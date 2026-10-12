#!/usr/bin/env python3
"""pbsched.py: the module scheduler of one worker (started by pbworker.py): the batch scheduler described below, plus:
  --intake DIR   every 15 s, every new DIR/*.jsonl (a package's manifest, renamed into place atomically by the worker) is merged
                 into the running DAG; each line may carry "pkg" (copied into the results); DIR/<tag>.cancel cancels a package's
                 modules that have not started (each gets a results line with exit -2); modules blocked by a failed dependency get
                 exit -4 lines; --forever keeps running when idle until DIR/STOP exists and nothing is left; --manifest becomes
                 optional; a module whose process cannot be started gets exit -3 instead of stopping the scheduler; a package claimed
                 again after a failure starts its failed modules over.

Batch scheduler: memory-aware, dependency-aware module scheduling.

  pbsched.py --manifest M1.jsonl [--manifest M2.jsonl ...] --out STORE --lpath LPATH_FILE --lean LEAN [--slots N] [--mem-frac 0.85]
           [--as-gb 32] [--nothp NOTHP_PY] [--guard-avail 0.08] [--results results.jsonl] [--logdir logs] [--timeline timeline.tsv]

Manifest lines (JSON, one module each; every tier's emitter writes them):
  module    dotted module name; its .olean/.ilean go to STORE/<A>/<B>/<C>.olean
  src       the module's .lean file (absolute, or relative to the manifest's directory); or
  cmd       a shell command instead of a Lean build (tests and non-Lean units)
  tier, kind   labels for the statistics (e.g. caseII/item, c436/leafrange, c436/agg, sat/part, top/final)
  deps      module names that must be built first (names not in any manifest are taken as prebuilt, in LEAN_PATH)
  pred_s    predicted kernel seconds, isolated (the emitter's model)
  pred_gb   predicted peak anonymous memory in GB (THP off)
  env, cwd  optional environment additions and working directory for the build ('{STORE}' in env values becomes the store path,
            so an emitter can ship its own LEAN_PATH, e.g. "<closure roots>:{STORE}")

Policy:
  - a module is ready when its in-manifest deps are done; the next launch comes from the tier whose share of running slots lags
    its share of remaining predicted work the most (all tiers progress together), longest module first, first fit by memory;
  - fill rule: the largest-memory module is preferred as long as the remaining free slots can still be filled with the smallest
    ready modules (their memory estimated from the ready queue's memory buckets) (heavy units run as fast as full slots allow, spread over the run instead of piling up at the end);
  - starvation guard: a ready module that others depend on, waiting over 900 s, gets its memory reserved until it fits;
  - admission: running sum of pred_gb + this module's pred_gb <= mem-frac x MemTotal, running < slots, and MemAvailable stays above
    guard-avail x MemTotal (a safety net against mispredictions);
  - every build is a fresh process: prlimit --as, THP off (prctl wrapper), lean -j1, LEAN_PATH = base + STORE;
  - a failed build is retried once with pred_gb x 2; a second failure marks the module (and everything depending on it) failed;
  - results.jsonl is appended and fsynced per module, so a restart skips finished modules (safe across machine stops).
Measured per module: wall, user, sys, ru_maxrss, sampled max RssAnon (every 2 s); timeline every 10 s: running, ready, sum pred_gb,
sum RssAnon, MemAvailable, load. Summary at the end: utilization (busy slot-s over slots x wall), per tier/kind: measured wall over
pred_s (the packing factor against the isolated prediction), memory prediction error, failures.
"""
import argparse, signal, heapq, json, os, resource, subprocess, sys, threading, time

def meminfo():
    d = {}
    for l in open('/proc/meminfo'):
        k, v = l.split(':', 1); d[k] = int(v.split()[0]) * 1024
    return d

def rss_anon(pid):
    try:
        for l in open('/proc/%d/status' % pid):
            if l.startswith('RssAnon:'): return int(l.split()[1]) * 1024
    except OSError:
        pass
    return 0

def session_anon(sids):
    # RssAnon summed over every process of each unit's session (a unit is started with start_new_session, so sid = its pid;
    # cmd units run lean as a grandchild, which the unit's own pid does not show)
    tot = {s: 0 for s in sids}
    for d in os.listdir('/proc'):
        if not d.isdigit(): continue
        try:
            st = open('/proc/%s/stat' % d).read(); sid = int(st[st.rindex(')') + 2:].split()[3])
        except (OSError, ValueError, IndexError):
            continue
        if sid in tot: tot[sid] += rss_anon(int(d))
    return tot

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest', action='append', default=[]); ap.add_argument('--intake', default=''); ap.add_argument('--forever', action='store_true')
    ap.add_argument('--out', required=True); ap.add_argument('--lpath', default=''); ap.add_argument('--lean', default='lean')
    ap.add_argument('--slots', type=int, default=os.cpu_count()); ap.add_argument('--mem-frac', type=float, default=0.85)
    ap.add_argument('--as-gb', type=float, default=32.0); ap.add_argument('--nothp', default='')
    ap.add_argument('--guard-avail', type=float, default=0.08)
    ap.add_argument('--wall-cap-x', type=float, default=20.0); ap.add_argument('--wall-cap-min', type=float, default=21600.0)   # 6 h: class modules' kernel decide legitimately runs 2-4 h on 25-58 s predictions
    ap.add_argument('--results', default='results.jsonl'); ap.add_argument('--logdir', default='logs')
    ap.add_argument('--timeline', default='timeline.tsv')
    ap.add_argument('--starve', type=float, default=900.0, help='seconds a ready aggregation-path module may wait before its memory is reserved')
    ap.add_argument('--post', default='', help="command run after each successful Lean module build, e.g. the modhash record: "
                    "'python3 modhash.py record {olean} {module} --lean-path {lean_path}'; a non-zero exit fails the module")
    a = ap.parse_args()
    for f in ('out', 'results', 'logdir', 'timeline', 'lpath', 'nothp', 'intake'):   # builds run in per-module cwd: make every path absolute
        if getattr(a, f): setattr(a, f, os.path.abspath(getattr(a, f)))
    os.makedirs(a.out, exist_ok=True); os.makedirs(a.logdir, exist_ok=True)
    M = {}
    def read_manifest(mf):
        base = os.path.dirname(os.path.abspath(mf)); out = []
        for l in open(mf):
            if not l.strip(): continue
            m = json.loads(l)
            if 'src' in m and not os.path.isabs(m['src']): m['src'] = os.path.join(base, m['src'])
            if m.get('cwd') and not os.path.isabs(m['cwd']): m['cwd'] = os.path.join(base, m['cwd'])
            m.setdefault('deps', []); m.setdefault('pred_s', 60.0); m.setdefault('pred_gb', 1.0)
            m.setdefault('tier', '?'); m.setdefault('kind', '?')
            out.append(m)
        return out
    for mf in a.manifest:
        for m in read_manifest(mf):
            if m['module'] in M: sys.exit('duplicate module ' + m['module'])
            M[m['module']] = m
    loaded = set(a.manifest); cancelled = set(); seen_cancel = set()
    done, failed = set(), set()
    if os.path.exists(a.results):
        # an abrupt stop (machine stop, reset) can leave a partial last line: an unreadable line is dropped (its module runs again)
        # and the file is rewritten without it, so the next appended record does not run into the fragment
        raw = open(a.results, 'rb').read(); good = []; nbad = 0
        for l in raw.decode('utf-8', 'replace').splitlines():
            if not l.strip(): continue
            try: r = json.loads(l)
            except ValueError: nbad += 1; continue
            good.append(l)
            if r.get('exit') == 0: done.add(r['module'])
        if nbad or (raw and not raw.endswith(b'\n')):
            with open(a.results + '.tmp', 'w') as f:
                f.write(''.join(x + '\n' for x in good)); f.flush(); os.fsync(f.fileno())
            os.replace(a.results + '.tmp', a.results)
            print('results: dropped %d unreadable line(s)' % nbad, flush=True)
    total_mem = meminfo()['MemTotal']; budget = a.mem_frac * total_mem
    base_lp = open(a.lpath).read().strip() if a.lpath else ''
    lp = (base_lp + ':' if base_lp else '') + os.path.abspath(a.out)
    children = {k: [] for k in M}; ndep = {}
    for k, m in M.items():
        ds = [d for d in m['deps'] if d in M]
        ndep[k] = sum(1 for d in ds if d not in done)
        for d in ds: children[d].append(k)
    ready = {}         # tier -> heap of (-pred_s, module): all tiers progress in proportion to their remaining work
    rem = {}           # tier -> remaining predicted seconds (not yet finished)
    rem_c = [0.0]; rem_m = [0.0]     # remaining predicted seconds and GB-seconds over all unfinished modules (memory-time balance)
    since = {}         # module -> time it became ready (starvation guard)
    for k in M:
        if k not in done:
            rem[M[k]['tier']] = rem.get(M[k]['tier'], 0.0) + M[k]['pred_s']
            rem_c[0] += M[k]['pred_s']; rem_m[0] += M[k]['pred_s'] * M[k]['pred_gb']
            if ndep[k] == 0: pass   # pushed below, once push() exists
    BUCK = [0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0, 4.0, 6.0, 8.0, 16.0, 1e9]     # predicted-GB bucket upper bounds
    def bucket(g): return next(i for i, u in enumerate(BUCK) if g <= u)
    def nready(): return len(live)
    attempts = {}
    live = set()          # modules currently ready (entries elsewhere are deleted lazily)
    crit = []             # heap (ready time, module) of ready modules others depend on: the starvation guard's candidates
    bypkg = {}            # package -> its module names (pkg_left walks one package, not the whole box)
    for k0, m0 in M.items(): bypkg.setdefault(m0.get("pkg"), set()).add(k0)
    def pkg_left(pk):
        # unfinished modules of package pk (an O(package) pass, made only for modules nothing depends on: a few per package)
        if not pk: return 99
        return sum(1 for kk in bypkg.get(pk, ()) if kk not in done and kk not in failed and kk not in cancelled)
    def push(k):
        since.setdefault(k, time.time()); live.add(k)
        # (a package's LAST unfinished module is protected too: otherwise a short final module can starve for hours behind a big
        # package of another tier on the same box; ordinary modules without dependents stay unprotected, see the guard's note below)
        if children.get(k) or pkg_left(M[k].get('pkg')) <= 1: heapq.heappush(crit, (since[k], k))   # (children first: no pass for them)
        g = M[k]['pred_gb'] * (2 if attempts.get(k, 0) >= 1 else 1)
        heapq.heappush(ready.setdefault(M[k]['tier'], {}).setdefault(bucket(g), []), (-M[k]['pred_s'], k))
    running = {}       # pid -> dict(module, start, gb, attempt, log, maxanon)
    for k in M:
        if k not in done and ndep[k] == 0: push(k)
    def record_terminal(k, ec, why):
        rec = dict(module=k, pkg=M[k].get('pkg'), tier=M[k]['tier'], kind=M[k]['kind'], attempt=2, exit=ec, start=time.time() - t0, wall=0.0,
                   user=0.0, sys=0.0, maxrss_kb=0, max_anon_gb=0.0, pred_s=M[k]['pred_s'], pred_gb=M[k]['pred_gb'], log='', why=why)
        rf.write(json.dumps(rec) + '\n'); rf.flush(); os.fsync(rf.fileno())
        failed.add(k); live.discard(k); rem[M[k]['tier']] -= M[k]['pred_s']; rem_c[0] -= M[k]['pred_s']; rem_m[0] -= M[k]['pred_s'] * M[k]['pred_gb']
    def intake():
        # merge new package manifests (their modules' deps are inside the package or prebuilt); process cancel markers
        if not a.intake: return 0
        new = 0
        for f in sorted(os.listdir(a.intake)):
            fp = os.path.join(a.intake, f)
            if f.endswith('.cancel') and f not in seen_cancel:
                seen_cancel.add(f); pk = f[:-len('.cancel')].rsplit('.', 1)[0]
                run_mods = {r['module'] for r in running.values()}
                for k, m in M.items():
                    if m.get('pkg') == pk and k not in done and k not in failed and k not in run_mods:
                        cancelled.add(k); record_terminal(k, -2, 'cancelled')
                continue
            if not f.endswith('.jsonl') or fp in loaded: continue
            loaded.add(fp); ms = read_manifest(fp)
            for m in ms:
                k0 = m['module']
                if k0 in M:
                    if k0 in failed and not any(r['module'] == k0 for r in running.values()):
                        # a package claimed again after a failure: its modules start over
                        failed.discard(k0); cancelled.discard(k0); attempts.pop(k0, None)
                    else:
                        print('pbsched: duplicate module %s in %s (kept the first)' % (k0, f), flush=True); continue
                M[k0] = m; children.setdefault(k0, []); bypkg.setdefault(m.get("pkg"), set()).add(k0)
            ready_new = []
            for m in ms:
                k = m['module']
                if M[k] is not m: continue
                ds = [d for d in m['deps'] if d in M]
                ndep[k] = sum(1 for d in ds if d not in done)
                for d in ds: children.setdefault(d, []).append(k)
                if k not in done:
                    rem[m['tier']] = rem.get(m['tier'], 0.0) + m['pred_s']; rem_c[0] += m['pred_s']; rem_m[0] += m['pred_s'] * m['pred_gb']
                    if ndep[k] == 0: ready_new.append(k)
            # pushed once the whole manifest's dependents are known: push() asks children.get(k), and a module listed before its
            # dependents would otherwise look like a package end (a giant's many tables would each be protected: minutes of stall)
            for k in ready_new: push(k); new += 1
        return new
    last_intake = [0.0]
    lock = threading.Lock(); stop = [False]
    rf = open(a.results, 'a'); tf = open(a.timeline, 'a')
    t0 = time.time(); busy_slot_s = [0.0]

    def sampler():
        last_tl = 0.0
        while not stop[0]:
            with lock:
                tot = 0
                sa = session_anon(list(running.keys()))
                now_ = time.time()
                for pid, r in running.items():
                    x = sa.get(pid, 0); r['maxanon'] = max(r['maxanon'], x); tot += x
                    # wall cap: a unit running past max(wall_cap_min, wall_cap_x x pred_s) is killed (its session) and retried once
                    # (a hang importing a damaged olean is otherwise never noticed)
                    cap = max(a.wall_cap_min, a.wall_cap_x * float(M[r['module']].get('pred_s') or 60))
                    if not r.get('walled') and now_ - r['start'] > cap:
                        r['walled'] = True
                        try: os.killpg(pid, signal.SIGKILL)
                        except OSError: pass
                        print('wall cap: killed %s after %.0f s (cap %.0f s)' % (r['module'], now_ - r['start'], cap), flush=True)
                n_run = len(running); n_ready = nready(); gb = sum(r['gb'] for r in running.values())
            now = time.time()
            if now - last_tl >= 10:
                mi = meminfo()
                tf.write('%.0f\t%d\t%d\t%d\t%d\t%.1f\t%.1f\t%.1f\t%s\n' % (now - t0, n_run, n_ready, len(done), len(failed), gb, tot / 2**30,
                         mi['MemAvailable'] / 2**30, open('/proc/loadavg').read().split()[0])); tf.flush(); last_tl = now
            time.sleep(2)
    th = threading.Thread(target=sampler, daemon=True); th.start()

    def launch(k):
        if k in cancelled or k in failed: return
        m = M[k]; att = attempts.get(k, 0) + 1; attempts[k] = att
        gb = m['pred_gb'] * (2 if att > 1 else 1)
        log = os.path.join(a.logdir, k.replace('/', '_') + ('.%d' % att) + '.log')
        env = dict(os.environ); env['LEAN_PATH'] = lp
        env.update({ek: ev.replace('{STORE}', os.path.abspath(a.out)) for ek, ev in m.get('env', {}).items()})   # per-unit LEAN_PATH with {STORE}
        if 'cmd' in m:
            argv = ['bash', '-c', m['cmd']]
        else:
            parts = k.split('.'); od = os.path.join(a.out, *parts[:-1]); os.makedirs(od, exist_ok=True)
            o = os.path.join(od, parts[-1])
            argv = [a.lean, '-j1', '-o', o + '.olean', '-i', o + '.ilean', m['src']]
            if a.nothp: argv = [sys.executable, a.nothp] + argv
        # address-space cap: the scheduler's default, raised for a unit predicted to need more (2 x its pred_gb + 16 GiB for the mapped
        # closure; pred_gb is doubled on a retry), so a big-memory unit (caseII join items: 36 GB anon) is not killed by the cap itself
        argv = ['prlimit', '--as=%d' % int(max(a.as_gb, 2 * gb + 16) * 2**30)] + argv
        lf = open(log, 'w')
        try:
            p = subprocess.Popen(argv, stdout=lf, stderr=subprocess.STDOUT, env=env, cwd=m.get('cwd') or None, start_new_session=True)
        except OSError as e:
            lf.write('pbsched: cannot start: %s\n' % e); lf.close(); record_terminal(k, -3, 'cannot start: %s' % e); block_dependents(k); return
        lf.close()
        running[p.pid] = dict(module=k, start=time.time(), gb=gb, attempt=att, log=log, maxanon=0, p=p)   # keep p: a dropped Popen gets reaped by subprocess._cleanup

    def fits(k):
        m = M[k]; gb = m['pred_gb'] * (2 if attempts.get(k, 0) >= 1 else 1)
        used = sum(r['gb'] for r in running.values())
        if (used + gb) * 2**30 > budget and running: return False
        if meminfo()['MemAvailable'] < a.guard_avail * total_mem and running: return False
        return True

    def block_dependents(k):
        st = [k]
        while st:
            x = st.pop()
            for c in children.get(x, []):
                if c not in failed:
                    failed.add(c); live.discard(c); st.append(c)
                    rec = dict(module=c, pkg=M[c].get('pkg'), tier=M[c]['tier'], kind=M[c]['kind'], attempt=2, exit=-4, start=time.time() - t0,
                               wall=0.0, user=0.0, sys=0.0, maxrss_kb=0, max_anon_gb=0.0, pred_s=M[c]['pred_s'], pred_gb=M[c]['pred_gb'], log='',
                               why='dependency %s failed' % k)
                    rf.write(json.dumps(rec) + '\n'); rf.flush(); os.fsync(rf.fileno())

    # live parameters (no restart, so no in-flight unit is lost): pbsched.params.json next to the results file, e.g.
    # {"mem_frac": 1.0, "slots": 170}, re-read every 30 s when it changes
    params_f = os.path.join(os.path.dirname(a.results), 'pbsched.params.json'); params_t = [0.0, None]
    while True:
        if time.time() - params_t[0] > 30:
            params_t[0] = time.time()
            try:
                st_ = os.stat(params_f)
                if st_.st_mtime != params_t[1]:
                    params_t[1] = st_.st_mtime; pp = json.load(open(params_f))
                    if 'mem_frac' in pp: budget = float(pp['mem_frac']) * total_mem
                    if 'slots' in pp: a.slots = int(pp['slots'])
                    if 'wall_cap_min' in pp: a.wall_cap_min = float(pp['wall_cap_min'])
                    if 'wall_cap_x' in pp: a.wall_cap_x = float(pp['wall_cap_x'])
                    print('params reloaded: mem_frac %s slots %d' % (pp.get('mem_frac'), a.slots), flush=True)
            except FileNotFoundError: pass
            except Exception as e: print('params file unreadable:', repr(e)[:120], flush=True)
        with lock:
            if a.intake and time.time() - last_intake[0] > 15:
                intake(); last_intake[0] = time.time()
            # launch as many ready modules as fit, longest first, first fit by memory
            while nready() and len(running) < a.slots:
                totrem = sum(rem.values()) or 1.0
                run_t = {}
                for r in running.values(): run_t[M[r['module']]['tier']] = run_t.get(M[r['module']]['tier'], 0) + 1
                order = sorted((t for t in ready if any(h for h in ready[t].values())), key=lambda t: -(rem.get(t, 0) / totrem - run_t.get(t, 0) / a.slots))
                launched = False
                free = a.slots - len(running)
                used = sum(r['gb'] for r in running.values()); bgb = budget / 2**30
                head = (bgb - used) / max(1, free)                                # GB per free slot
                # fill rule: smallest predicted memory among ready modules; a module may take memory only if the other free slots can
                # still be filled with modules that small (so heavy units run as fast as full slots allow, and never idle the CPUs)
                # memory the other free slots would need if filled with the smallest ready modules (bucket counts, bucket midpoints)
                need, left = 0.0, free - 1
                for b in range(len(BUCK)):
                    if left <= 0: break
                    n = sum(len(ready[t].get(b, ())) for t in ready)
                    take = min(left, n); left -= take
                    need += take * (0.5 * ((BUCK[b - 1] if b else 0.0) + min(BUCK[b], 32.0)))
                # starvation guard: the oldest ready module waiting > STARVE s that does not fit gets its memory reserved
                now = time.time(); reserve = 0.0; starved = None
                # only modules other modules wait on (aggregation path) are protected, after 900 s: reserving memory for ordinary heavy
                # units idles slots (a 300 s guard on every module kept a third of the slots idle)
                while crit and crit[0][1] not in live: heapq.heappop(crit)
                if crit and now - crit[0][0] > a.starve:
                    k0 = crit[0][1]; g0 = M[k0]['pred_gb'] * (2 if attempts.get(k0, 0) >= 1 else 1)
                    if fits(k0):
                        heapq.heappop(crit); live.discard(k0); launch(k0); continue
                    reserve = g0; starved = k0
                for dense in (True, False):
                    # pass 1: tier with the largest deficit first; within it the largest-memory module that keeps the fill rule, then
                    # the longest; pass 2: the longest module that fits the budget
                    for t in order:
                        for b, h in ready[t].items():
                            while h and h[0][1] not in live: heapq.heappop(h)
                        cand = sorted(((-b, h[0][0]) if dense else (h[0][0], -b), b) for b, h in ready[t].items() if h)
                        for _, b in cand:
                            k = ready[t][b][0][1]
                            g = M[k]['pred_gb'] * (2 if attempts.get(k, 0) >= 1 else 1)
                            if dense and used + g + need + reserve > bgb: continue
                            if (used + g + reserve) > bgb and running: continue
                            if fits(k):
                                heapq.heappop(ready[t][b]); live.discard(k); launch(k); launched = True; break
                        if launched: break
                    if launched: break
                if not launched: break
            if not running and not nready():
                if not a.forever or (a.intake and os.path.exists(os.path.join(a.intake, 'STOP'))): break
        if not running:
            time.sleep(2); continue
        try:
            pid, status, ru = os.wait4(-1, os.WNOHANG if a.intake else 0)   # with intake: poll, so new packages merge while long builds run
        except ChildProcessError:
            time.sleep(1); continue
        if pid == 0:
            time.sleep(0.5); continue
        with lock:
            r = running.pop(pid, None)
            if r is None: continue
            k = r['module']; end = time.time(); ec = os.waitstatus_to_exitcode(status)
            if 'cmd' not in M[k]:
                parts = k.split('.'); o = os.path.join(a.out, *parts) + '.olean'
                if ec == 0 and not os.path.exists(o): ec = 99
                if ec == 0 and a.post:
                    lpk = lp
                    for ek, ev in M[k].get('env', {}).items():
                        if ek == 'LEAN_PATH': lpk = ev.replace('{STORE}', os.path.abspath(a.out))
                    pc = a.post.replace('{olean}', o).replace('{module}', k).replace('{lean_path}', "'" + lpk + "'")
                    pr = subprocess.run(['bash', '-c', pc], capture_output=True, text=True)
                    with open(r['log'], 'a') as lf: lf.write('\nPOST rc=%d %s\n%s%s' % (pr.returncode, pc[:200], pr.stdout[-2000:], pr.stderr[-2000:]))
                    if pr.returncode != 0: ec = 98
            elif ec == 0 and not os.path.exists(os.path.join(a.out, *k.split('.')) + '.kman'):
                # a command unit (the caseII kmod_unit.sh) must leave its .kman in the store (the finalizer requires one from every
                # command unit): one that exits 0 without it (e.g. "built" in 0.0 s with an empty log) fails here and is retried once,
                # instead of failing the whole package's audit at its end
                with open(r['log'], 'a') as lf: lf.write('\npbsched: exit 0 but no %s.kman in the store: counted as a failure (98)\n' % k)
                ec = 98
            busy_slot_s[0] += end - r['start']
            rec = dict(module=k, pkg=M[k].get('pkg'), tier=M[k]['tier'], kind=M[k]['kind'], attempt=r['attempt'], exit=ec, start=r['start'] - t0, wall=end - r['start'],
                       user=ru.ru_utime, sys=ru.ru_stime, maxrss_kb=ru.ru_maxrss, max_anon_gb=r['maxanon'] / 2**30,
                       pred_s=M[k]['pred_s'], pred_gb=M[k]['pred_gb'], log=r['log'])
            if ec == 0:
                # the outputs reach the disk before the record says they exist: a box stopped abruptly (machine stop, reset) must
                # not leave a "done" module whose olean or log was still in the page cache
                ob = os.path.join(a.out, *k.split('.'))
                for f in [ob + x for x in ('.olean', '.ilean', '.olean.private', '.olean.server', '.ir', '.kman', '.mhash')] + [r['log']]:
                    try:
                        fd = os.open(f, os.O_RDONLY); os.fsync(fd); os.close(fd)
                    except OSError: pass
            rf.write(json.dumps(rec) + '\n'); rf.flush(); os.fsync(rf.fileno())
            if ec == 0:
                done.add(k); rem[M[k]['tier']] -= M[k]['pred_s']; rem_c[0] -= M[k]['pred_s']; rem_m[0] -= M[k]['pred_s'] * M[k]['pred_gb']
                for c in children[k]:
                    ndep[c] -= 1
                    if ndep[c] == 0 and c not in failed: push(c)
            elif attempts.get(k, 0) < 2:
                push(k)
            else:
                failed.add(k); rem[M[k]['tier']] -= M[k]['pred_s']; rem_c[0] -= M[k]['pred_s']; rem_m[0] -= M[k]['pred_s'] * M[k]['pred_gb']; block_dependents(k)
    stop[0] = True; wall = time.time() - t0
    # summary
    R = []
    for l in open(a.results):
        try: R.append(json.loads(l))
        except ValueError: pass
    ok = [r for r in R if r['exit'] == 0]
    by = {}
    for r in ok:
        g = by.setdefault((r['tier'], r['kind']), [0, 0.0, 0.0, 0.0, 0.0])
        g[0] += 1; g[1] += r['wall']; g[2] += r['pred_s']; g[3] = max(g[3], r['max_anon_gb'] - r['pred_gb']); g[4] += r['user'] + r['sys']
    out = dict(wall_s=wall, slots=a.slots, busy_slot_s=busy_slot_s[0], utilization=busy_slot_s[0] / (a.slots * wall) if wall else 0,
               modules_ok=len(ok), modules_failed=len(failed), retries=sum(1 for r in R if r['attempt'] > 1),
               per_tier={'%s/%s' % k: dict(n=v[0], wall_s=v[1], pred_s=v[2], factor=(v[1] / v[2] if v[2] else None),
                                          cpu_s=v[4], max_mem_underpred_gb=v[3]) for k, v in by.items()})
    json.dump(out, open(a.results + '.summary.json', 'w'), indent=1)
    print(json.dumps(out, indent=1))

if __name__ == '__main__':
    main()
