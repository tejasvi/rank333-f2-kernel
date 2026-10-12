#!/usr/bin/env python3
"""pbworker.py: the worker of one machine ("box"; a long-running service, restart-safe). Configuration: env PB_STORE, PB_BUCKET,
PB_PREFIX (objstore.py), PB_ROOT (default ./pbroot), PB_LPATH (file: the closure's LEAN_PATH; the store is appended), PB_LEAN (the
lean binary; default PB_TOOLCHAIN/lean, else lean on PATH), PB_CLOSURE_ROOT (where a tarball package's root/ part is merged; default
ROOT/root), PB_NOTHP,
PB_SLOTS (default nproc - 2), PB_EMITTERS (concurrent emissions, default 2), PB_BACKLOG_S (target predicted work queued per slot,
default 1800), PB_SAMPLE (private-part sample rate, default 0.001), PB_BOX (default hostname), PB_ONCE=1 (exit when the queue has
nothing more to claim and everything is finished: dry runs).

Threads:
  claimer   while launching is allowed (queue CONTROL) and the queued predicted work per slot is under PB_BACKLOG_S: claim a
            package (pbq lease), emit it into ROOT/pkgs/<id> (spec "emit": {"type": "cmd", "argv": [...]} with {OUT}, {ID}, {SEED};
            or {"type": "tarball", "object": "<object name>", "manifest": "<path in the tarball>"} for pre-emitted packages;
            "//<namespace>/<name>" names an object of another store namespace),
            rewrite its manifest (pkg, absolute src/cwd, LEAN_PATH = closure + {STORE}) and rename it into ROOT/intake/<id>.jsonl;
  scheduler pbsched.py --intake ROOT/intake --forever (restarted if it dies; results.jsonl survives restarts);
  finalizer per package whose modules are all done: audit (each module's log: one KPUB, KAXSUM bad=0 local_axioms=0) -> .kman
            (kmod_build.sh's format) and modhash.py record (.mhash) per module -> one tarball (public .olean/.ilean/.kman/.mhash,
            manifest, logs, results) -> upload to PREFIX/tar/<shard>/<id>.tar.zst, verified (size + md5 against the object) ->
            done record + lease "done" -> delete the package's private parts (a seeded PB_SAMPLE share goes to PREFIX/sample/ first),
            emitted sources and data, and its store files; a package with a failed module (after sched's retry) is marked failed;
  renewer   every 300 s renews every held lease; a lost lease drops the package (no upload).
State: ROOT/inflight.json (claimed packages); on start every inflight package is adopted back (lease still ours) or dropped."""
import hashlib, json, os, random, shutil, socket, subprocess, sys, tarfile, threading, time, base64
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objstore, pbq

E = os.environ
B, P = objstore.BUCKET, objstore.PREFIX
ROOT = os.path.abspath(E.get('PB_ROOT', 'pbroot')); BOX = E.get('PB_BOX', socket.gethostname())
LEAN = E.get('PB_LEAN') or (os.path.join(E['PB_TOOLCHAIN'], 'lean') if E.get('PB_TOOLCHAIN') else (shutil.which('lean') or 'lean'))
CLOSURE_ROOT = E.get('PB_CLOSURE_ROOT', os.path.join(ROOT, 'root'))
NOTHP = E.get('PB_NOTHP', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'nothp.py'))
SLOTS = int(E.get('PB_SLOTS', max(1, (os.cpu_count() or 4) - 2))); NEMIT = int(E.get('PB_EMITTERS', 2))
BACKLOG = float(E.get('PB_BACKLOG_S', 1800)); SAMPLE = float(E.get('PB_SAMPLE', 0.001)); ONCE = E.get('PB_ONCE') == '1'
HERE = os.path.dirname(os.path.abspath(__file__))
D = {k: os.path.join(ROOT, k) for k in ('intake', 'pkgs', 'store', 'logs', 'work', 'out')}
for d in D.values(): os.makedirs(d, exist_ok=True)
LPATH_FILE = E.get('PB_LPATH', os.path.join(ROOT, 'lpath.txt'))
RESULTS = os.path.join(D['work'], 'results.jsonl'); INFL = os.path.join(ROOT, 'inflight.json')
lock = threading.Lock(); stop = threading.Event()
SCHED_FAIL = [0, 0.0]     # consecutive pbsched starts that ended within a minute, and when the run of them began
PINNED_SEEN = [None, []]    # (packages.jsonl generation last scanned, ids of the packages pinned to this box)
PIN_ONLY = os.environ.get('PB_PIN_ONLY') == '1'    # a dedicated box: claims only packages pinned to it
HEAVY_ONLY = os.environ.get('PB_HEAVY_ONLY') == '1'  # a memory-rich box for case II: claims only memory-heavy packages (and pinned ones)
SPLIT_ONLY = os.environ.get('PB_SPLIT_ONLY') == '1'  # a box dedicated to split builds: claims only split-build packages ("split_of") and pinned ones
EMIT_SEM = threading.Semaphore(int(E.get('PB_EMITTERS', 2))); EXCL = threading.Lock()
# emissions with a big memory footprint (spec emit "as_gb" >= 32: the caseII unit conversion peaks at 4-5 GB) are not seen by the
# scheduler's memory guard, and their units are memory-bound (several GB each): at most one such package IN FLIGHT per PB_HEAVY_EMIT_GB
# (60) GB of the box's memory; the claimer claims other (low-memory) packages instead, so a box mixes memory-bound and CPU-bound work
HEAVY_CAP = max(1, int((int(open('/proc/meminfo').read().split('MemTotal:')[1].split()[0]) / 2**20) // float(E.get('PB_HEAVY_EMIT_GB', 60))))
HEAVY = [0]
def is_heavy(x): return float((x.get('emit') or {}).get('as_gb') or 0) >= 32
def heavy_inflight():
    with lock: return sum(1 for v in inflight.values() if is_heavy(v.get('spec') or {}))   # an "exclusive" emission takes every emitter permit
MEM_GB = int(open('/proc/meminfo').read().split('MemTotal:')[1].split()[0]) / 2**20   # a package's "min_mem_gb" (big-memory units) must fit
AVOID = set()      # packages this box must not build (their module names collide with its scheduler's history)
# package families: a split build's group and final packages (line field "family" = the id of the package they split) share module
# names with each other and with that package, and this box's scheduler keys modules by name for its lifetime, so a second package
# of one family would collide only after its whole emission: a box claims at most one package of a family, ever (ROOT/families.txt
# keeps the families and ids of everything this box claimed, adopted or released on a collision)
FAM_F = os.path.join(ROOT, 'families.txt')
FAMILIES = set(l.strip() for l in open(FAM_F) if l.strip()) if os.path.exists(FAM_F) else set()
def add_family(f):
    if f and f not in FAMILIES:
        FAMILIES.add(f)
        with open(FAM_F, 'a') as fh: fh.write(f + '\n'); fh.flush(); os.fsync(fh.fileno())
def family_ok(x):
    f = x.get('family')
    if not f: return True
    with lock: cur = {(v.get('spec') or {}).get('family') or k for k, v in inflight.items()} | set(inflight)
    return f not in FAMILIES and f not in cur
lost = {}          # id -> inflight entry of a package whose lease was lost: cleaned up once none of its modules can still run
inflight = {}      # id -> {"spec":..., "state": "emitting"|"queued"|"finalizing", "t": ..., "modules": [...], "pred_s": ...}

def log(*a):
    print(time.strftime('%FT%TZ', time.gmtime()), *a, flush=True)

def save_inflight():
    with lock:
        t = INFL + '.tmp'; json.dump(inflight, open(t, 'w')); f = open(t); os.fsync(f.fileno()); f.close(); os.replace(t, INFL)

def sha256f(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''): h.update(b)
    return h.hexdigest()

def md5b64(p):
    h = hashlib.md5()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''): h.update(b)
    return base64.b64encode(h.digest()).decode()

Q = pbq.Queue(B, P, BOX, cache_dir=D['work'])

# ---------------------------------------------------------------- emission
def deps_dir(pid): return os.path.join(D['pkgs'], pid + '.deps')

def fetch_deps(spec):
    deps = spec.get('deps', [])
    if deps:
        import concurrent.futures as cf
        dd = deps_dir(spec['id']); os.makedirs(dd, exist_ok=True)
        with cf.ThreadPoolExecutor(int(E.get('PB_DEP_PAR', 24))) as ex:
            list(ex.map(lambda d: fetch_dep(d, bool(spec.get('deps_pubs')), dd), deps))

def emit(spec, tag):
    pid = spec['id']; out = os.path.join(D['pkgs'], pid); em = spec['emit']
    if os.path.exists(out): shutil.rmtree(out)
    os.makedirs(out)
    if em.get('deps_first'):
        # an emission that reads its dependencies (a class aggregation: kcagg reads each package's DONE and kext.txt): they come first,
        # their public modules into the store and their emitter records under {DEPS}/<dep>/
        fetch_deps(spec); spec = dict(spec, _deps_fetched=True)
        em = dict(em, argv=[x.replace('{DEPS}', deps_dir(pid)) for x in em.get('argv', [])], then=[x.replace('{DEPS}', deps_dir(pid)) for x in em.get('then', [])] or None)
    if em['type'] == 'tarball':
        t = os.path.join(D['work'], pid + '.pkg'); ob = em['object']
        bkt, name = ob[2:].split('/', 1) if ob.startswith('//') else (B, ob)
        objstore.download_file(bkt, name, t)
        if em.get('sha256') and sha256f(t) != em['sha256']: raise RuntimeError('package tarball sha256 differs from the package line')
        zstd = open(t, 'rb').read(4) == b'\x28\xb5\x2f\xfd'
        subprocess.run(['bash', '-c', ('zstd -dc %s | tar xf - -C %s' if zstd else 'tar xf %s -C %s') % (t, out)], check=True); os.remove(t)
        if em.get('merge_root') and os.path.isdir(os.path.join(out, 'root')):
            # the package's closure part (paths under root/) joins the worker's closure; files already present are kept (no-clobber)
            os.makedirs(CLOSURE_ROOT, exist_ok=True)
            subprocess.run(['cp', '-a', '-n', os.path.join(out, 'root', '.'), CLOSURE_ROOT + os.sep], check=True)
        if em.get('then'):
            # an emission step shipped in the tarball (e.g. the caseII ./emit.sh): runs in OUTDIR under the emission cap, writes the manifest
            run_emit(pid, out, [x.replace('{OUT}', out).replace('{ID}', pid) for x in em['then']], em)
        mf = os.path.join(out, em['manifest'])
    else:
        run_emit(pid, out, [x.replace('{OUT}', out).replace('{ID}', pid).replace('{SEED}', str(spec.get('seed', 1))) for x in em['argv']], em)
        mf = os.path.join(out, em.get('manifest', 'manifest.jsonl'))
    return emit_post(spec, tag, mf)

def install_store_files(srcroot, dep):
    """copy srcroot/<rel> into the store: an absent file is added, an identical one kept, and a DIFFERENT one (left by an earlier
    package under the same name) replaced atomically (running builds keep the old inode): the dependent package then builds
    against, and records the hash of, the dependency it named"""
    for r, _, fs in os.walk(srcroot):
        for f in fs:
            a = os.path.join(r, f); rel = os.path.relpath(a, srcroot); d = os.path.join(D['store'], rel)
            if os.path.exists(d):
                if sha256f(d) == sha256f(a): continue
                log('dependency', dep, 'replaces a different', rel)
            os.makedirs(os.path.dirname(d), exist_ok=True); shutil.copy2(a, d + '.dep%d' % os.getpid()); os.replace(d + '.dep%d' % os.getpid(), d)

def fetch_dep(dep, pubs_only, depdir=None):
    """a dependency package's results into the local store (no-clobber), verified against its done record: the whole store part,
    or with pubs_only just its public root modules (the small pubs object when the done record has one, else those files of the
    full tarball)"""
    dr = objstore.get(B, '%s/done/%s.json' % (P, dep))
    if dr is None: raise RuntimeError('dependency %s has no done record' % dep)
    dd = json.loads(dr[0]); x = os.path.join(D['work'], dep + '.dep'); shutil.rmtree(x, ignore_errors=True); os.makedirs(x)
    if pubs_only and dd.get('pubs_object'):
        t = os.path.join(D['work'], dep + '.pubs.tar'); objstore.download_file(B, dd['pubs_object'], t)
        if sha256f(t) != dd['pubs_sha256']: raise RuntimeError('dependency %s: pubs sha256 differs from its done record' % dep)
        cmd = 'tar xf %s -C %s && cd %s && sha256sum -c --quiet SHA256SUMS' % (t, x, x)
    else:
        t = os.path.join(D['work'], dep + '.dep.tar.zst'); objstore.download_file(B, dd['object'], t)
        if sha256f(t) != dd['sha256']: raise RuntimeError('dependency %s: tarball sha256 differs from its done record' % dep)
        if pubs_only:
            # the root modules' files only (streamed out of the full tarball), each checked against the tarball's SHA256SUMS
            pre = tuple('store/' + '/'.join(r.split('.')) + '.' for r in ((dd.get('audit') or {}).get('roots') or []))
            got = {}; sums = {}
            zp = subprocess.Popen(['zstd', '-dc', t], stdout=subprocess.PIPE)
            with tarfile.open(fileobj=zp.stdout, mode='r|') as tf:
                for mm in tf:
                    if mm.isfile() and (mm.name in ('SHA256SUMS', 'emit/DONE', 'emit/kext.txt') or mm.name.startswith(pre)):
                        b = tf.extractfile(mm).read()
                        if mm.name == 'SHA256SUMS': sums = {a: h for h, a in (l.split('  ', 1) for l in b.decode().splitlines() if l.strip())}
                        else: got[mm.name] = b
            zp.wait()
            if not any(a.startswith('store/') for a in got): raise RuntimeError('dependency %s: no root module files in its tarball' % dep)
            for a, b in got.items():
                if a.startswith('emit/'):
                    os.makedirs(os.path.join(x, 'emit'), exist_ok=True); open(os.path.join(x, a), 'wb').write(b); continue
                if sums.get(a) != hashlib.sha256(b).hexdigest(): raise RuntimeError('dependency %s: %s differs from SHA256SUMS' % (dep, a))
                f = os.path.join(x, a)
                os.makedirs(os.path.dirname(f), exist_ok=True); open(f, 'wb').write(b)
            cmd = 'true'
        else:
            cmd = 'zstd -dc %s | tar xf - -C %s && cd %s && sha256sum -c --quiet SHA256SUMS' % (t, x, x)
    subprocess.run(['bash', '-c', cmd], check=True)
    if os.path.isdir(os.path.join(x, 'store')): install_store_files(os.path.join(x, 'store'), dep)
    if depdir:
        os.makedirs(os.path.join(depdir, dep), exist_ok=True)
        for f in ('DONE', 'kext.txt'):
            if os.path.exists(os.path.join(x, 'emit', f)): shutil.copy2(os.path.join(x, 'emit', f), os.path.join(depdir, dep, f))
    shutil.rmtree(x, ignore_errors=True); os.remove(t)

def emit_post(spec, tag, mf):
    """after the emission: dependencies into the store, then the manifest rewritten into the scheduler's intake"""
    pid = spec['id']; out = os.path.join(D['pkgs'], pid); em = spec['emit']
    # packages this one builds on (a split case's leaves for its join): their public results go into the local store first
    if not spec.get('_deps_fetched'): fetch_deps(spec)
    base = os.path.dirname(mf); lp = open(LPATH_FILE).read().strip(); mods = []; ps = 0.0; lines = []
    own_lp = os.path.join(out, 'lpath_common.txt')
    if os.path.exists(own_lp) and em.get('own_lpath', True): lp = open(own_lp).read().strip()
    for l in open(mf):
        if not l.strip(): continue
        m = json.loads(l); m['pkg'] = pid
        if 'src' in m and not os.path.isabs(m['src']): m['src'] = os.path.join(base, m['src'])
        cwd = m.get('cwd') or '.'
        m['cwd'] = cwd if os.path.isabs(cwd) else os.path.normpath(os.path.join(base, cwd))
        # the store FIRST: Lean binds a package root (KJ, KMS, ...) to the first LEAN_PATH entry holding its directory, so the package's
        # own modules must resolve to the store even if a closure root happens to hold a directory of the same name
        env = m.setdefault('env', {}); env.setdefault('LEAN_PATH', '{STORE}:' + lp)
        if spec.get('tier') == 'caseII' and m.get('pred_gb'):
            # case-II units run up to ~1.25x their predicted memory and were OOM-killed on boxes with 2 GB per core; the scheduler's memory
            # guard admits by pred_gb, so give it headroom (fewer case-II units per box, the free slots go to co-tenants)
            m['pred_gb'] = round(float(m['pred_gb']) * float(E.get('PB_CASEII_GB_X', 1.0)) + 0.5, 2)
        mods.append(m['module']); ps += float(m.get('pred_s', 60)); lines.append(json.dumps(m))
    clash_old = sorted(set(mods) & scheduler_names())
    if clash_old: raise Collision('%d module names already known to this box\'s scheduler (e.g. %s)' % (len(clash_old), clash_old[0]))
    # a package root that also exists in the closure would shadow (or be shadowed by) the closure's modules of that root: warn
    roots = {mm.split('.')[0] for mm in mods}
    clash = sorted(r for r in roots for e in lp.split(':') if e and os.path.isdir(os.path.join(e, r)))
    if clash: log('package', pid, 'WARNING: package roots also present in the closure:', ' '.join(sorted(set(clash))))
    t = os.path.join(D['intake'], '.%s.tmp' % tag); open(t, 'w').write('\n'.join(lines) + '\n')
    f = open(t); os.fsync(f.fileno()); f.close(); os.replace(t, os.path.join(D['intake'], tag + '.jsonl'))
    return mods, ps

def run_emit(pid, out, argv, em):
    """one emission command in OUTDIR under an address-space cap (the package's emit "as_gb", else PB_EMIT_AS GiB, default 40): a
    runaway emission fails (MemoryError: the package is parked) instead of starving the box's builds"""
    cap = float(em.get('as_gb') or E.get('PB_EMIT_AS', 40))
    tf = os.path.join(D['logs'], pid + '.emit.time')
    argv = ['/usr/bin/time', '-f', '%e %M', '-o', tf, 'prlimit', '--as=%d' % int(cap * 2**30)] + argv
    el = os.path.join(D['logs'], pid + '.emit.log')
    with open(el, 'a') as lf:
        r = subprocess.run(argv, stdout=lf, stderr=subprocess.STDOUT, cwd=out)
    try:
        es, ek = open(tf).read().split()[-2:]
        inflight[pid]['emit_s'] = inflight[pid].get('emit_s', 0) + float(es); inflight[pid]['emit_maxrss_kb'] = max(inflight[pid].get('emit_maxrss_kb', 0), int(ek))
    except Exception: pass
    if r.returncode != 0:
        tail = open(el, errors='replace').read()[-20000:]
        if any(x in tail for x in ('bad_alloc', 'MemoryError', 'Cannot allocate memory', 'out of memory', 'std::length_error', 'maxrss')):
            raise MemoryError('emitter exit %d at the %s GiB cap' % (r.returncode, cap))
        raise RuntimeError('emitter exit %d' % r.returncode)

class Collision(Exception): pass
_seen = dict(pos=0, names=set())
def scheduler_names():
    """module names this box's pbsched already knows: it keys modules by name for its lifetime (results.jsonl, kept across its
    restarts) and keeps the first of two lines with one name, so a package reusing a name (a requeued package, a resubmitted
    _r2) would get the old record instead of a build"""
    if os.path.exists(RESULTS):
        with open(RESULTS) as f:
            f.seek(_seen['pos'])
            for l in f:
                if not l.endswith('\n'): break
                _seen['pos'] += len(l.encode())
                try: _seen['names'].add(json.loads(l)['module'])
                except Exception: pass
    n = set(_seen['names'])
    with lock:
        for v in inflight.values(): n.update(v.get('modules') or [])
    for f in os.listdir(D['intake']):
        if f.endswith('.jsonl'):
            try: n.update(json.loads(l)['module'] for l in open(os.path.join(D['intake'], f)) if l.strip())
            except Exception: pass
    return n

class _nullctx:
    def __enter__(self): return self
    def __exit__(self, *a): return False

def queued_work():
    """predicted seconds of claimed packages not yet finalized, minus what results.jsonl shows finished; a package still emitting
    counts at most a quarter of the backlog target (a huge one, e.g. a held heavy-split, emits for an hour: it must not stop the
    box from claiming work it can run meanwhile)"""
    cap = 0.25 * BACKLOG * SLOTS
    with lock:
        return (sum(v.get('pred_s', 0) for v in inflight.values() if v['state'] == 'queued')
                + sum(min(v.get('pred_s', 0), cap) for v in inflight.values() if v['state'] == 'emitting')
                - sum(v.get('done_s', 0) for v in inflight.values()))

def claimer():
    emitting = []
    def one(spec):
        pid = spec['id']; excl = bool(spec.get('emit', {}).get('exclusive')); n = int(E.get('PB_EMITTERS', 2)) if excl else 1
        heavy = is_heavy(spec)
        with EXCL if excl else _nullctx():
            for _ in range(n): EMIT_SEM.acquire()
        try:
            mods, ps = emit(spec, inflight[pid]['tag'])
            with lock: inflight[pid].update(state='queued', modules=mods, pred_s=ps)
            log('emitted', pid, len(mods), 'modules, pred %.0f s' % ps)
        except Collision as e:
            # another box builds it (this one would reuse old records); never claimed here again
            log('package', pid, 'released to another box:', e); AVOID.add(pid); add_family(spec.get('family'))
            with lock: inflight.pop(pid, None)
            shutil.rmtree(os.path.join(D['pkgs'], pid), ignore_errors=True)
            if Q.release(pid): log('released', pid)
        except MemoryError as e:
            # the emission hit the memory cap: park the package for other tools (no retry on the same tools)
            log('emit parked (needs-tools)', pid, e); Q.park(pid, 'needs-tools: %s' % e)
            with lock: inflight.pop(pid, None)
            shutil.rmtree(os.path.join(D['pkgs'], pid), ignore_errors=True)
        except Exception as e:
            if 'emitter exit 3' in str(e):
                # exit 3 = the emitter's closure check refused this box (installed closure != the package's): a box problem, not
                # the package's; another box builds it, this one never claims it again
                log('package', pid, 'released (closure check failed on this box):', e); AVOID.add(pid)
                with lock: inflight.pop(pid, None)
                shutil.rmtree(os.path.join(D['pkgs'], pid), ignore_errors=True)
                if Q.release(pid): log('released', pid)
            else:
                log('emit failed', pid, e); Q.fail(pid, 'emit: %s' % e)
            with lock: inflight.pop(pid, None)
            shutil.rmtree(os.path.join(D['pkgs'], pid), ignore_errors=True)
        finally:
            if heavy:
                with lock: HEAVY[0] -= 1
            for _ in range(n): EMIT_SEM.release()
        save_inflight()
    idle_since = None
    while not stop.is_set():
        emitting = [t for t in emitting if t.is_alive()]
        # a package pinned to this box (a join's item units needing this box's scheduler) is claimed past the backlog gate; the
        # package list is refreshed here too (claim() refreshes it only when called, and a full backlog stops the calls)
        if time.time() - Q.last_scan > 60:
            try: Q.rescan()
            except Exception: pass
        if PINNED_SEEN[0] != Q.pkgen: PINNED_SEEN[0], PINNED_SEEN[1] = Q.pkgen, [x['id'] for x in Q.pk if x.get('pin_box') == BOX]
        pinned = [i for i in PINNED_SEEN[1] if i not in inflight and i not in Q.taken and i not in AVOID]
        if (len(emitting) < NEMIT and (queued_work() < BACKLOG * SLOTS or pinned) and SCHED_FAIL[0] < 3 and Q.launch_allowed()):
            st = os.statvfs(ROOT); free_gb = st.f_bavail * st.f_frsize / 2**30
            with lock: reserved = sum(float(v['spec'].get('disk_gb') or 0) for v in inflight.values() if v['state'] in ('emitting', 'queued'))
            try: spec = Q.claim(skip=set(inflight) | AVOID, fits=lambda x: float(x.get('disk_gb') or 0) + 20 + reserved <= free_gb
                                and float(x.get('min_mem_gb') or 0) <= MEM_GB and (not is_heavy(x) or heavy_inflight() < HEAVY_CAP)
                                and x.get('pin_box') in ((BOX,) if (pinned or PIN_ONLY) else (None, BOX))
                                and (not HEAVY_ONLY or is_heavy(x) or x.get('pin_box') == BOX) and family_ok(x)
                                and (not SPLIT_ONLY or x.get('split_of') or x.get('pin_box') == BOX))
            except Exception as e:
                log('claim error (retried)', repr(e)[:160]); time.sleep(10); continue
            if spec is not None:
                idle_since = None
                with lock: inflight[spec['id']] = dict(spec=spec, state='emitting', t=time.time(), pred_s=float(spec.get('pred_s') or 3 * float(spec.get('pred_s_min') or 1200)),
                                                     tag='%s.%d' % (spec['id'], int(time.time())), tools=tools_id())
                if is_heavy(spec):
                    with lock: HEAVY[0] += 1
                add_family(spec['id']); add_family(spec.get('family'))
                save_inflight(); log('claimed', spec['id'])
                th = threading.Thread(target=one, args=(spec,), daemon=True); th.start(); emitting.append(th); continue
            idle_since = idle_since or time.time()
            if ONCE and not inflight and not emitting and time.time() - idle_since > 60:
                log('queue empty and nothing in flight: stopping'); open(os.path.join(D['intake'], 'STOP'), 'w').close(); stop.set(); return
        time.sleep(10)

# ---------------------------------------------------------------- finalization
KPAT = ('KUNITS', 'KLITS', 'KPUB', 'KDISPATCH', 'KKEY', 'KEXT', 'KAX', 'KAXSUM', 'KAXP')
PLAIN = set(E.get('PB_PLAIN_KINDS', 'table').split(','))   # manifest kinds without a public theorem (data tables): no KPUB required
def opath(mod): return os.path.join(D['store'], *mod.split('.'))

def kman(mod, rec):
    """kmod_build.sh's manifest for a module built by pbsched: K* lines of its log, KTIME, KDATA, KSHA; returns (clean, kext lines)"""
    o = opath(mod); lines = ['KMOD ' + mod]; kext = []
    for l in open(rec['log'], errors='replace'):
        w = l.split(' ', 1)[0].strip()
        if w in KPAT: lines.append(l.rstrip('\n'))
        if w == 'KEXT': kext.append(l.rstrip('\n'))
    lines.append('KTIME wall=%.2f user=%.2f sys=%.2f maxrss_kb=%d' % (rec['wall'], rec['user'], rec['sys'], rec['maxrss_kb']))
    for l in list(lines):
        if l.startswith(('KUNITS ', 'KLITS ')) and ' data=' in l:
            dp = l.split(' data=', 1)[1].split()[0]
            if os.path.exists(dp): lines.append('KDATA %s %s' % (dp, sha256f(dp)))
    for x in ('.olean', '.olean.private', '.ir'):
        if os.path.exists(o + x): lines.append('KSHA %s %s' % (os.path.basename(o + x), sha256f(o + x)))
    open(o + '.kman', 'w').write('\n'.join(lines) + '\n')
    npub = sum(1 for l in lines if l.startswith('KPUB ')); nclean = sum(1 for l in lines if l.startswith('KAXSUM ') and ' bad=0 local_axioms=0 ' in l + ' ')
    nbad = sum(1 for l in lines if l.startswith('KAX BAD'))
    if rec.get('kind') in PLAIN and npub == 0:
        # a data table: no public theorem, no audit of its own; its constants are obligations of its importers' audits (KAX OBL),
        # discharged by kmod_audit's external walk at aggregation, which imports it at the private level: so it gets no .kman
        # (kmod_audit would require a KPUB) but a .kplain record, and its .olean.private is kept and shipped
        os.replace(o + '.kman', o + '.kplain')
        with open(o + '.kplain', 'a') as f: f.write('KPLAIN %s\n' % rec.get('kind'))
        return nbad == 0, kext
    return (npub >= 1 and nclean >= npub and nbad == 0), kext

STD = {'propext', 'Classical.choice', 'Quot.sound'}
def audit_package(roots, lean_path=None):
    """the compositional axiom audit of the package from its public module(s) (the KMod library's kmod_audit.py walk, without its
    external step): every reached module has a .kman with a KPUB and, per KPUB, a KAXSUM bad=0 local_axioms=0, no KAX BAD;
    an obligation into a module with a .kman must name one of its KPUB theorems, or end in .EXT and occur in the statement of one of
    them (KModTyChk.lean, exported level); every
    other obligation (vocabulary, core, data tables) is returned for the external walk at aggregation (kmod_audit / KModExt over the
    union of all packages' lists).  Returns (errors, reached, external obligations)"""
    def parse(mod):
        f = opath(mod) + '.kman'
        if not os.path.exists(f): return None
        m = dict(pub=[], sum={}, obl=[], bad=[], kaxp={})
        for line in open(f, errors='replace'):
            w = line.split()
            if not w: continue
            if w[0] == 'KPUB': m['pub'].append(w[1])
            elif w[0] == 'KAXSUM': m['sum'][w[1]] = dict(x.split('=', 1) for x in w[2:] if '=' in x)
            elif w[0] == 'KAX' and len(w) > 3 and w[1] == 'OBL': m['obl'].append((w[2], w[3]))
            elif w[0] == 'KAX' and len(w) > 1 and w[1] == 'BAD': m['bad'].append(' '.join(w[2:]))
            elif w[0] == 'KAXP': m['kaxp'][w[1]] = set(w[2].split(',')) if len(w) > 2 and w[2] else set()
        return m
    errs = []; ext = set(); seen = set(); cache = {}; stack = list(roots); tycheck = set()
    def man(n):
        if n not in cache: cache[n] = parse(n)
        return cache[n]
    for r in roots:
        if man(r) is None: errs.append('root %s has no .kman' % r)
    while stack:
        mod = stack.pop()
        if mod in seen or man(mod) is None: continue
        seen.add(mod); m = man(mod)
        if not m['pub']: errs.append('%s: no KPUB' % mod)
        for t in m['pub']:
            sm = m['sum'].get(t)
            if sm is None: errs.append('%s: no KAXSUM for %s' % (mod, t))
            elif sm.get('bad') != '0' or sm.get('local_axioms') != '0': errs.append('%s: KAXSUM %s bad=%s local_axioms=%s' % (mod, t, sm.get('bad'), sm.get('local_axioms')))
        for b in m['bad']: errs.append('%s: KAX BAD %s' % (mod, b))
        for (n, c) in m['obl']:
            mn = man(n)
            if mn is not None:
                # as kmod_audit.py: accepted iff c is one of N's KPUB theorems, or c ends in .EXT and occurs as a
                # constant in the statement of one of N's KPUB theorems (checked in Lean at the exported level, KModTyChk.lean)
                if c not in mn['pub']:
                    if c.endswith('.EXT'): tycheck.add((n, c))
                    else: errs.append('%s: obligation %s of KMod module %s is not its public theorem' % (mod, c, n))
                stack.append(n)
            else: ext.add((n, c))
    if tycheck:
        tf = os.path.join(D['work'], 'tychk_%d.txt' % os.getpid())
        open(tf, 'w').write(''.join('%s %s %s\n' % (n, c, ' '.join(man(n)['pub'])) for n, c in sorted(tycheck)))
        env = dict(os.environ); env['LEAN_PATH'] = D['store'] + ':' + (lean_path or open(LPATH_FILE).read().strip())
        env['PATH'] = os.path.dirname(LEAN) + ':' + env.get('PATH', '')   # KModTyChk's findSysroot runs `lean --print-prefix` from PATH
        r = subprocess.run([LEAN, '--run', os.path.join(HERE, 'KModTyChk.lean'), tf], capture_output=True, text=True, env=env)
        okp = {tuple(l.split()[1:3]) for l in r.stdout.splitlines() if l.startswith('TYOK')}
        for n, c in sorted(tycheck):
            if (n, c) not in okp: errs.append('%s: obligation %s is not in the statement of a KPUB theorem of %s' % (n, c, n))
        if r.returncode not in (0, 2) and not okp: errs.append('statement check failed: %s' % r.stderr.strip()[-200:])
    for r in roots:
        for t, axs in (man(r) or {}).get('kaxp', {}).items():
            if not axs <= STD: errs.append('root KAXP %s: %s' % (t, ','.join(sorted(axs - STD))))
    return errs, seen, ext

def tools_id():
    """this worker's tools: the sha256 of the tools tarball the installer recorded (ROOT/provenance.json), else the md5 of TOOLS.md5"""
    t = (provenance().get('tools') or {}).get('sha256')
    if t: return t
    tm = os.path.join(HERE, 'TOOLS.md5')
    return 'md5:' + hashlib.md5(open(tm, 'rb').read()).hexdigest() if os.path.exists(tm) else None

PROV = {}
def provenance():
    """what regenerates this box's results: the tools tarball and closure tarballs (object + sha256, recorded by the installer in
    ROOT/provenance.json) and the worker files' md5s (TOOLS.md5)"""
    if not PROV:
        f = os.path.join(ROOT, 'provenance.json')
        if os.path.exists(f):
            try: PROV.update(json.load(open(f)))
            except Exception: pass
        tm = os.path.join(HERE, 'TOOLS.md5')
        if os.path.exists(tm): PROV['tools_md5'] = open(tm).read().split('\n')
    return PROV

def finalize(pid, recs):
    v = inflight[pid]; spec = v['spec']; mods = v['modules']; t0 = time.time()
    lp = open(LPATH_FILE).read().strip() + ':' + D['store']
    unclean = []; kext = []
    man = {}
    for l in open(os.path.join(D['intake'], v['tag'] + '.jsonl')):
        if l.strip(): mm = json.loads(l); man[mm['module']] = mm
    for m in mods:
        if 'cmd' in man.get(m, {}):
            # a unit built by its own command (the caseII kmod_build.sh): it wrote its .kman (and usually its .mhash) into the store
            kf = opath(m) + '.kman'
            if not os.path.exists(kf): unclean.append(m + ' (no .kman from its command)'); continue
            L = open(kf, errors='replace').read().splitlines()
            npub = sum(1 for x in L if x.startswith('KPUB ')); ncl = sum(1 for x in L if x.startswith('KAXSUM ') and ' bad=0 local_axioms=0 ' in x + ' ')
            if npub < 1 or ncl < npub or any(x.startswith('KAX BAD') for x in L): unclean.append(m + ' (its .kman is not clean)')
            kext += [x for x in L if x.startswith('KEXT ')]
            continue
        clean, kx = kman(m, recs[m]); kext += kx
        if not clean: unclean.append(m)
    # import-hash records (modhash), one header-reading process for the whole package; each module's own LEAN_PATH; units that
    # recorded themselves (.mhash present) are kept as they are
    def with_store(x):
        # the package's own modules live in the store: an explicit unit LEAN_PATH without {STORE} (caseII cmd units carry their
        # package's lpath_common.txt) still resolves them, from the store, first
        x = x.replace('{STORE}', D['store'])
        return x if D['store'] in x.split(':') else D['store'] + ':' + x
    lpm = {m: with_store(man.get(m, {}).get('env', {}).get('LEAN_PATH', lp)) for m in mods}
    todo = [m for m in mods if not ('cmd' in man.get(m, {}) and os.path.exists(opath(m) + '.mhash'))]
    lf = os.path.join(D['work'], pid + '.mh.txt')
    open(lf, 'w').write(''.join('%s\t%s\t%s\n' % (opath(m) + '.olean', m, lpm.get(m, lp)) for m in todo))
    if todo:
        r = subprocess.run([sys.executable, os.path.join(HERE, 'modhash.py'), 'record-many', lf, '--cache', os.path.join(D['work'], 'mh.json')],
                           capture_output=True, text=True, env=dict(os.environ, MH_TC=E.get('PB_TC', os.path.dirname(os.path.dirname(LEAN)))))
        if r.returncode != 0: unclean.append('modhash: %s' % r.stdout.strip()[-300:])
    roots = [m for m in mods if man.get(m, {}).get('pub')] or [m for m in mods if os.path.exists(opath(m) + '.kman')]
    lp0 = (man.get(roots[0], {}).get('env', {}).get('LEAN_PATH') if roots else None)
    aerr, reached, aext = audit_package(roots, with_store(lp0) if lp0 else None)
    if aerr: unclean += ['audit: ' + e for e in aerr[:20]]
    if unclean:
        log('package', pid, 'UNCLEAN:', unclean[:5]); Q.fail(pid, 'unclean audit: %s' % ' '.join(unclean[:20])); return False
    # tarball: public parts + manifest + logs + results lines
    tdir = os.path.join(D['out'], pid); shutil.rmtree(tdir, ignore_errors=True); os.makedirs(tdir)
    tp = os.path.join(D['out'], pid + '.tar'); files = []
    with tarfile.open(tp, 'w') as tf:
        for m in mods:
            for x in ('.olean', '.ilean', '.kman', '.kplain', '.mhash', '.olean.server') + (('.olean.private', '.ir') if os.path.exists(opath(m) + '.kplain') else ()):
                f = opath(m) + x
                if os.path.exists(f):
                    arc = 'store/' + os.path.relpath(f, D['store']); tf.add(f, arcname=arc); files.append((arc, sha256f(f)))
            lg = recs[m]['log']; tf.add(lg, arcname='logs/' + os.path.basename(lg))
        tf.add(os.path.join(D['intake'], v['tag'] + '.jsonl'), arcname='manifest.jsonl')
        el = os.path.join(D['logs'], pid + '.emit.log')
        if os.path.exists(el): tf.add(el, arcname='logs/emit.log')
        # the emitter's own records (DONE summary with pubs, kext.txt, inputs.sha256): aggregation (mkagg) reads DONE; kext.txt is
        # the authoritative external-leaf list of the emission that was built
        for x in ('DONE', 'kext.txt', 'inputs.sha256', 'emit.log') + tuple(spec.get('export') or ()):
            f = os.path.join(D['pkgs'], pid, x)
            if os.path.exists(f): tf.add(f, arcname='emit/' + x)
        rj = os.path.join(tdir, 'results.jsonl'); open(rj, 'w').write(''.join(json.dumps(recs[m]) + '\n' for m in mods)); tf.add(rj, arcname='results.jsonl')
        if kext: kf = os.path.join(tdir, 'kext.txt'); open(kf, 'w').write('\n'.join(kext) + '\n'); tf.add(kf, arcname='kext.txt')
        of = os.path.join(tdir, 'obl.txt'); open(of, 'w').write(''.join('%s %s\n' % x for x in sorted(aext))); tf.add(of, arcname='audit/obl.txt')
        sf = os.path.join(tdir, 'SHA256SUMS'); open(sf, 'w').write(''.join('%s  %s\n' % (h, a) for a, h in files)); tf.add(sf, arcname='SHA256SUMS')
    subprocess.run(['zstd', '-q', '-f', '-T4', '-10', tp, '-o', tp + '.zst'], check=True); os.remove(tp)
    sha = sha256f(tp + '.zst'); md5 = md5b64(tp + '.zst'); size = os.path.getsize(tp + '.zst')
    # unique per claim: a late upload of a swept lease can never overwrite another emission's tarball (re-emissions differ)
    name = '%s/tar/%s/%s.%s.tar.zst' % (P, pbq.shard(pid), v['tag'], BOX)
    if pid not in Q.gen: log('package', pid, 'lease lost before upload: dropped'); return False
    meta = objstore.upload_file(B, name, tp + '.zst')
    st = objstore.stat(B, name)
    if not st or int(st['size']) != size or st.get('md5Hash') != md5:
        log('package', pid, 'UPLOAD MISMATCH', st and st.get('md5Hash'), md5); Q.fail(pid, 'upload verification failed'); return False
    # the pubs object: just the public root modules (what a package listing this one in "deps" with "deps_pubs" needs, e.g. a join)
    pt = os.path.join(D['out'], pid + '.pubs.tar'); pf = []
    with tarfile.open(pt, 'w') as tf:
        for r in roots:
            for x in ('.olean', '.ilean', '.kman', '.mhash', '.olean.server'):
                f = opath(r) + x
                if os.path.exists(f): arc = 'store/' + os.path.relpath(f, D['store']); tf.add(f, arcname=arc); pf.append((arc, sha256f(f)))
        # with the emitter's DONE and kext.txt (a class aggregation reads each package's pubs and external leaves from them)
        for x in ('DONE', 'kext.txt') + tuple(spec.get('export') or ()):   # "export": emitter outputs others read (a class's ext.txt, ext_pl.txt)
            f = os.path.join(D['pkgs'], pid, x)
            if os.path.exists(f): tf.add(f, arcname='emit/' + x)
        sf = os.path.join(tdir, 'SHA256SUMS.pubs'); open(sf, 'w').write(''.join('%s  %s\n' % (h, a) for a, h in pf)); tf.add(sf, arcname='SHA256SUMS')
    psha = sha256f(pt); pmd5 = md5b64(pt); psize = os.path.getsize(pt)
    pname = '%s/pubs/%s/%s.%s.tar' % (P, pbq.shard(pid), v['tag'], BOX)
    objstore.upload_file(B, pname, pt); pst = objstore.stat(B, pname)
    if not pst or int(pst['size']) != psize or pst.get('md5Hash') != pmd5:
        log('package', pid, 'PUBS UPLOAD MISMATCH'); Q.fail(pid, 'pubs upload verification failed'); return False
    os.remove(pt)
    # private-part sample (seeded by module name), outside the store
    for m in mods:
        if int(hashlib.sha256(m.encode()).hexdigest()[:8], 16) / 2**32 < SAMPLE and os.path.exists(opath(m) + '.olean.private'):
            objstore.upload_file(B, '%s/sample/%s/%s.olean.private' % (P, pid, m), opath(m) + '.olean.private')
    rec = dict(id=pid, box=BOX, object=name, sha256=sha, md5=md5, size=size, modules=len(mods), kext=len(kext),
               pubs_object=pname, pubs_sha256=psha, pubs_size=psize,
               tools_claim=v.get('tools'), tools_finalize=tools_id(),
               wall_s=sum(recs[m]['wall'] for m in mods), pred_s=sum(recs[m]['pred_s'] for m in mods),
               cpu_s=sum(recs[m]['user'] + recs[m]['sys'] for m in mods), max_anon_gb=max(recs[m]['max_anon_gb'] for m in mods),
               retries=sum(1 for m in mods if recs[m]['attempt'] > 1), t_claim=v['t'], t_done=time.time(), finalize_s=time.time() - t0,
               emit_s=v.get('emit_s'), emit_maxrss_kb=v.get('emit_maxrss_kb'),
               kext_lines=(lambda f: open(f).read().splitlines()[:500] if os.path.exists(f) else [])(os.path.join(D['pkgs'], pid, 'kext.txt')),
               audit=dict(roots=roots, reached=len(reached), external_obligations=len(aext), result='PASS'),
               spec_sha256=hashlib.sha256(json.dumps(spec, sort_keys=True).encode()).hexdigest(), provenance=provenance(),
               spec=spec)
    Q.done(pid, rec); log('done', pid, '%d modules, %d bytes, sha256 %s' % (len(mods), size, sha[:16]))
    return True

def cleanup(pid, mods, tag=None):
    for m in mods or []:
        for x in ('.olean', '.ilean', '.kman', '.kplain', '.mhash', '.olean.private', '.olean.server', '.ir'):
            try: os.remove(opath(m) + x)
            except FileNotFoundError: pass
    shutil.rmtree(os.path.join(D['pkgs'], pid), ignore_errors=True); shutil.rmtree(os.path.join(D['out'], pid), ignore_errors=True)
    shutil.rmtree(deps_dir(pid), ignore_errors=True)
    for f in [os.path.join(D['out'], pid + '.tar.zst')] + ([os.path.join(D['intake'], tag + x) for x in ('.jsonl', '.cancel')] if tag else []):
        try: os.remove(f)
        except FileNotFoundError: pass

def classify_failure(recs, bad):
    """the failed modules of a package, classified from their exit and their last log's first error line: KERNEL (a kernel rejection:
    "(kernel)" in the error, a correctness signal: never requeued blindly), LEAN (another elaboration error), OOM (killed: exit 137/-9),
    SEGV (signal 11: exit 139/-11), OTHER; cancelled or blocked dependents (-2, -4) are skipped"""
    classes = set(); out = []
    for m in bad:
        r = recs.get(m) or {}; ex = r.get('exit')
        if ex in (-2, -4): continue
        line = ''
        try:
            for l in open(r.get('log') or '/nonexistent', errors='replace'):
                if 'error' in l: line = ' '.join(l.split())[:220]; break
        except Exception: pass
        c = ('KERNEL' if '(kernel)' in line else 'OOM' if ex in (137, -9) else 'SEGV' if ex in (139, -11) else 'LEAN' if line else 'OTHER')
        classes.add(c); out.append('%s[%s exit %s]: %s' % (m, c, ex, line))
    return sorted(classes), out

def finalizer():
    # nothing may end this thread (an exception, e.g. a KeyError on a package dropped meanwhile, would leave finished packages
    # unfinalized): an error is logged and the loop starts again (results.jsonl re-read from the start)
    while True:
        try: _finalizer_loop(); return
        except Exception as e:
            log('finalizer error (restarted)', repr(e)[:300]); time.sleep(15)

def _finalizer_loop():
    pos = 0; recs = {}
    while not stop.is_set() or inflight:
        if os.path.exists(RESULTS):
            with open(RESULTS) as f:
                f.seek(pos)
                for l in f:
                    if not l.endswith('\n'): break
                    pos += len(l.encode()); r = json.loads(l); recs[r['module']] = r
        for pid in [p for p, v in list(inflight.items()) if v['state'] == 'queued']:
            # the renewer drops a package whose lease was lost (released, moved, parked) at any moment: it may be gone already
            v = inflight.get(pid)
            if v is None: continue
            ms = v['modules']
            ok = [m for m in ms if recs.get(m, {}).get('exit') == 0]
            term = lambda r: r['exit'] == 0 or r['attempt'] >= 2 or r['exit'] in (-2, -3, -4)
            bad = [m for m in ms if m in recs and recs[m]['exit'] != 0 and term(recs[m])]
            with lock: v['done_s'] = sum(recs[m]['pred_s'] for m in ok)
            if bad and not all(m in recs and term(recs[m]) for m in ms):
                # cancel the package's modules that have not started; wait until every module has a terminal record
                cf = os.path.join(D['intake'], v['tag'] + '.cancel')
                if not os.path.exists(cf): open(cf, 'w').close(); log('package', pid, 'cancelling after failed modules', bad[:5])
                continue
            if len(ok) == len(ms):
                with lock: v['state'] = 'finalizing'
                try:
                    finalize(pid, recs)
                except Exception as e:
                    log('finalize error', pid, e); Q.fail(pid, 'finalize: %s' % e)
                cleanup(pid, ms, v['tag'])
                with lock: inflight.pop(pid, None)
                save_inflight()
            elif bad:
                cls, why = classify_failure(recs, bad)
                log('package', pid, 'failed modules', cls, why[:3]); Q.fail(pid, 'build failed [%s]: %s' % (','.join(cls), ' | '.join(why[:6])))
                cleanup(pid, ms, v['tag'])
                with lock: inflight.pop(pid, None)
                save_inflight()
        for pid, v in list(lost.items()):
            ms = v.get('modules') or []
            if all(m in recs and (recs[m]['exit'] == 0 or recs[m]['attempt'] >= 2 or recs[m]['exit'] in (-2, -3, -4)) for m in ms):
                cleanup(pid, ms, v.get('tag')); lost.pop(pid, None); log('lost package cleaned', pid)
        if stop.is_set() and not inflight: break
        time.sleep(15)

def renewer():
    # every held lease each RENEW s, in parallel: one slow or stalled request (a long round trip to the store) must not hold up
    # the others past the TTL; an error is not a loss (the lease is kept and renewed again next round), only a lease that is gone
    # or no longer ours is
    import concurrent.futures as cf
    ex = cf.ThreadPoolExecutor(int(E.get('PB_RENEW_PAR', 8)))
    def one(pid):
        try: return pid, Q.renew(pid)
        except Exception as e:
            log('renew error (kept, retried next round)', pid, repr(e)[:160]); return pid, None
    while not stop.is_set():
        for pid, ok in ex.map(one, list(inflight)):
            if ok is False:
                log('lease lost', pid)
                with lock:
                    v = inflight.pop(pid, None)
                save_inflight()
                if v:
                    # cancel its unstarted modules; the finalizer removes its files once every module has a terminal record
                    open(os.path.join(D['intake'], v['tag'] + '.cancel'), 'w').close(); lost[pid] = v
        stop.wait(pbq.RENEW)

def _cmdline(p):
    try: return open('/proc/%s/cmdline' % p, 'rb').read().split(b'\0')
    except OSError: return None

def running_sched():
    """a pbsched.py serving this box's intake that outlived the previous worker (unit KillMode=process: a tools push restarts only
    the worker; the scheduler and the modules it runs go on, untouched) -> its pid, else None"""
    me = D['intake'].encode()
    for p in os.listdir('/proc'):
        if p.isdigit() and int(p) != os.getpid():
            a = _cmdline(p)
            if a and any(x.endswith(b'pbsched.py') for x in a) and me in a: return int(p)
    return None

def scheduler():
    lpf = os.path.join(D['work'], 'lpath_empty.txt'); open(lpf, 'w').write('')
    while not stop.is_set() or inflight:
        old = running_sched()
        if old:
            # it reads the same intake and appends to the same results.jsonl: new packages go to it until it ends (box restart)
            log('attached to the running pbsched', old)
            while True:
                a = _cmdline(old)
                if not a or not any(x.endswith(b'pbsched.py') for x in a): break
                time.sleep(10)
            log('pbsched', old, 'ended')
            if os.path.exists(os.path.join(D['intake'], 'STOP')): return
            continue
        p = subprocess.Popen([sys.executable, os.path.join(HERE, 'pbsched.py'), '--intake', D['intake'], '--forever', '--out', D['store'],
                              '--lpath', lpf, '--lean', LEAN, '--nothp', NOTHP, '--slots', str(SLOTS), '--results', RESULTS,
                              '--logdir', D['logs'], '--timeline', os.path.join(D['work'], 'timeline.tsv'), '--as-gb', E.get('PB_AS_GB', '32'),
                              '--mem-frac', E.get('PB_MEMFRAC', '0.75')],
                             stdout=open(os.path.join(D['work'], 'pbsched.out'), 'a'), stderr=subprocess.STDOUT)
        t0 = time.time(); p.wait(); log('pbsched exited', p.returncode)
        if os.path.exists(os.path.join(D['intake'], 'STOP')): return
        # a scheduler that cannot start (it exits within a minute, again and again) builds nothing while the leases stay renewed:
        # after 3 such exits no more claims; after 10 minutes the held packages are given back (claimable by other boxes at once)
        if time.time() - t0 < 60:
            SCHED_FAIL[0] += 1; SCHED_FAIL[1] = SCHED_FAIL[1] or t0
        else:
            SCHED_FAIL[0] = 0; SCHED_FAIL[1] = 0.0
        if SCHED_FAIL[0] >= 3 and SCHED_FAIL[1] and time.time() - SCHED_FAIL[1] > 600 and inflight:
            with lock: drop = list(inflight.items())
            log('ALERT pbsched failed %d starts in a row since %s: releasing %d held packages' % (SCHED_FAIL[0], time.strftime('%H:%M:%SZ', time.gmtime(SCHED_FAIL[1])), len(drop)))
            try: objstore.put(B, '%s/alerts/%s.sched' % (P, BOX), json.dumps(dict(box=BOX, t=time.time(), fails=SCHED_FAIL[0], released=len(drop))))
            except Exception: pass
            for pid, v in drop:
                if v.get('state') == 'emitting': continue       # the claimer thread owns it until its emission ends
                with lock: inflight.pop(pid, None)
                cleanup(pid, v.get('modules'), v.get('tag'))
                if Q.release(pid): log('released', pid)
            save_inflight()
        time.sleep(5)

def emission_procs(pid):
    """live processes of a package's emission that the previous worker left running (KillMode=process): cwd in, or argv naming,
    the package's output dir"""
    out = os.path.join(D['pkgs'], pid); ob = out.encode(); r = []
    for p in os.listdir('/proc'):
        if not p.isdigit() or int(p) == os.getpid(): continue
        a = _cmdline(p)
        try: c = os.readlink('/proc/%s/cwd' % p)
        except OSError: continue
        if a is not None and (c == out or c.startswith(out + '/') or any(ob in x for x in a)): r.append(int(p))
    return r

def adopt_emission(pid, procs):
    """wait for an emission the previous worker started (it holds an emitter permit meanwhile), then finish it as emit() would:
    success = its /usr/bin/time record (run_emit) written after the claim with exit status 0, and its manifest present"""
    v = inflight[pid]; spec = v['spec']; em = spec['emit']; out = os.path.join(D['pkgs'], pid)
    EMIT_SEM.acquire()
    try:
        while any(_cmdline(p) for p in procs): time.sleep(10)
        tf = os.path.join(D['logs'], pid + '.emit.time'); mf = os.path.join(out, em.get('manifest', 'manifest.jsonl'))
        tt = open(tf).read() if os.path.exists(tf) and os.path.getmtime(tf) >= v.get('t', 0) else ''
        if not tt or 'non-zero status' in tt or 'terminated by signal' in tt or not os.path.exists(mf):
            raise RuntimeError('the emission ended without a clean record (time file %r)' % tt[-80:])
        try: es, ek = tt.split()[-2:]; v['emit_s'] = v.get('emit_s', 0) + float(es); v['emit_maxrss_kb'] = int(ek)
        except Exception: pass
        mods, ps = emit_post(spec, v['tag'], mf)
        with lock: v.update(state='queued', modules=mods, pred_s=ps)
        log('emitted (adopted)', pid, len(mods), 'modules, pred %.0f s' % ps)
    except Exception as e:
        log('adopted emission lost', pid, e)
        with lock: inflight.pop(pid, None)
        cleanup(pid, None, v.get('tag'))
        if Q.release(pid): log('released', pid)
    finally:
        EMIT_SEM.release()
    save_inflight()

def verify_after_boot():
    """after a new boot (boot_id changed): modules of in-flight packages that results.jsonl records as done but whose outputs did not
    survive the stop (an olean without its magic, an empty log: page-cache data lost by a machine stop or reset before pbsched
    fsynced outputs) are dropped from results.jsonl, with their files, so the scheduler builds them again"""
    bf = os.path.join(ROOT, 'boot_id'); cur = open('/proc/sys/kernel/random/boot_id').read().strip()
    prev = open(bf).read().strip() if os.path.exists(bf) else None
    open(bf, 'w').write(cur)
    if prev in (None, cur) or not os.path.exists(RESULTS): return
    mods = set(); cmdmods = set()
    with lock:
        for v in inflight.values():
            mods.update(v.get('modules') or [])
            try:
                for l in open(os.path.join(D['intake'], v['tag'] + '.jsonl')):
                    if l.strip() and '"cmd"' in l: cmdmods.add(json.loads(l)['module'])
            except Exception: pass
    def kman_ok(k):
        # a command-built unit (the caseII kmod_unit.sh) writes its own .kman: it must hold its KMOD line (a stop can leave it empty)
        if k not in cmdmods: return True
        f = opath(k) + '.kman'
        try: return any(l.startswith('KMOD ') for l in open(f, errors='replace'))
        except OSError: return False
    keep = []; bad = set(); nunread = 0
    for l in open(RESULTS, errors='replace'):
        if not l.strip(): continue
        try: r = json.loads(l)
        except ValueError: nunread += 1; continue      # a partial line cut by the stop: dropped (pbsched would refuse the file)
        k = r.get('module')
        if r.get('exit') == 0 and k in mods:
            o = opath(k) + '.olean'
            def tail_ok(k):
                # every olean-format output (.olean, .olean.private, .olean.server, .ir) present: its last 4 KiB not all zero (a stop
                # can leave the size right and the tail unwritten)
                for x in ('.olean', '.olean.private', '.olean.server', '.ir'):
                    f = opath(k) + x
                    try:
                        sz = os.path.getsize(f)
                        with open(f, 'rb') as fh:
                            fh.seek(max(0, sz - 4096)); t = fh.read(4096)
                        if sz == 0 or not t.strip(b'\0'): return False
                    except FileNotFoundError: continue
                return True
            # (a data table's log is empty by design: no K lines; its olean is the check)
            ok = os.path.exists(o) and open(o, 'rb').read(5) == b'olean' and (not r.get('log') or r.get('kind') in PLAIN or (os.path.exists(r['log']) and os.path.getsize(r['log']) > 0)) and kman_ok(k) and tail_ok(k)
            if not ok:
                bad.add(k); continue
        keep.append(l if l.endswith('\n') else l + '\n')
    if bad or nunread:
        t = RESULTS + '.tmp'
        with open(t, 'w') as f: f.write(''.join(keep)); f.flush(); os.fsync(f.fileno())
        os.replace(t, RESULTS)
        for k in bad:
            for x in ('.olean', '.ilean', '.kman', '.kplain', '.mhash', '.olean.private', '.olean.server', '.ir'):
                try: os.remove(opath(k) + x)
                except FileNotFoundError: pass
    log('new boot: %d done modules of in-flight packages failed the output check and will be rebuilt%s; %d unreadable results line(s) dropped' % (
        len(bad), (': ' + ' '.join(sorted(bad)[:5])) if bad else '', nunread))

def main():
    global inflight
    adopt = []
    try: prev_tools = (json.load(open(os.path.join(ROOT, 'provenance_prev.json'))).get('tools') or {}).get('sha256')
    except Exception: prev_tools = None
    if os.path.exists(INFL):
        old = json.load(open(INFL)); inflight = {}
        # the lease checks in parallel (one round trip each: sequential checks keep a restarted worker idle for minutes)
        import concurrent.futures as cf
        def own(pid):
            try: return pid, Q.adopt(pid)
            except Exception as e: log('adopt check failed', pid, e); return pid, False
        with cf.ThreadPoolExecutor(32) as ex: owned_by = dict(ex.map(own, list(old)))
        for pid, v in old.items():
            add_family(pid); add_family((v.get('spec') or {}).get('family'))
            owned = owned_by.get(pid, False); v.setdefault('tools', prev_tools)
            em = (v.get('spec') or {}).get('emit') or {}
            if owned and v['state'] in ('queued', 'finalizing') and os.path.exists(os.path.join(D['intake'], v['tag'] + '.jsonl')):
                v['state'] = 'queued'; inflight[pid] = v; log('adopted', pid)
            elif owned and v['state'] == 'emitting' and (em.get('type') == 'cmd' or em.get('then')) and emission_procs(pid):
                inflight[pid] = v; adopt.append(pid); log('adopting the running emission of', pid)
            else:
                log('dropped after restart', pid); cleanup(pid, v.get('modules'), v.get('tag'))
                # an emission cut off by the restart: give the lease back at once instead of letting it expire (TTL)
                if owned and Q.release(pid): log('released', pid)
        save_inflight()
    try: os.remove(os.path.join(D['intake'], 'STOP'))
    except FileNotFoundError: pass
    verify_after_boot()
    ths = [threading.Thread(target=f, daemon=True) for f in (scheduler, renewer, finalizer)]
    for t in ths: t.start()
    for pid in adopt: threading.Thread(target=adopt_emission, args=(pid, emission_procs(pid)), daemon=True).start()
    claimer()
    while inflight: time.sleep(10)
    open(os.path.join(D['intake'], 'STOP'), 'w').close()
    for t in ths: t.join(timeout=120)
    log('worker finished')

if __name__ == '__main__':
    main()
