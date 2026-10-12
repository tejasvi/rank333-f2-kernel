#!/usr/bin/env python3
"""walk.py [--loop 900] [--par 6] [--batch-pkgs 150] [--once]: the private-level external walk (the KMod library's KModExt.lean,
md5 94d7a572, in queue/) over the union of every done package's external obligations (audit/obl.txt; per-tier unions in the verifier
db table obl), incremental.
An obligation `<module> <constant>` is walked in one of two kinds of batch:
  * env: the module lies on the final LEAN_PATH (FINAL_DIR/lpath_final.txt: vocabulary, the frozen port, Mathlib, core): batches of
    up to 150 modules, LEAN_PATH = FINAL_DIR/lpath_final.txt;
  * store: the module is produced by a done package (a data table, shipped with its .olean.private): the producing packages' store
    files are extracted from their tarballs (verified against the done record's sha256) into a scratch store for the batch, LEAN_PATH =
    scratch : FINAL_DIR/topstore/store : FINAL_DIR/lpath_final.txt; deleted after the batch.
Each batch: `lean --run KModExt.lean OBLFILE` under nice 10, THP off, 64 GiB address space; it must print EXTSUM ... bad=0 and every
`EXT STD` axiom must be propext / Classical.choice / Quot.sound.  Results: FINAL_DIR/walk/batches/<id>.{obl,out,json}; walked
obligations in the verifier db table walked (tier, module, const, batch); FINAL_DIR/walk/STATUS (one line).  A failed batch is recorded and retried
once; its obligations stay unwalked (V5 item C1 requires none)."""
import collections, concurrent.futures as cf, hashlib, io, json, os, shutil, sqlite3, subprocess, sys, tarfile, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = KE.FINAL
a = sys.argv[1:]
opt = lambda n, d, c=int: c(a[a.index(n) + 1]) if n in a else d
loop, par, bpk = opt('--loop', 900), opt('--par', 6), opt('--batch-pkgs', 150)
LEAN = KE.LEAN
EXT = os.path.join(KE.QUEUE, 'KModExt.lean'); NOTHP = KE.NOTHP
LPF = open(os.path.join(H, 'lpath_final.txt')).read().strip()
TOP = os.path.join(H, 'topstore', 'store')
W = os.path.join(H, 'walk'); os.makedirs(os.path.join(W, 'batches'), exist_ok=True); os.makedirs(os.path.join(W, 'tmp'), exist_ok=True)
STD = {'propext', 'Classical.choice', 'Quot.sound'}
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
assert hashlib.md5(open(EXT, 'rb').read()).hexdigest().startswith('94d7a572'), 'KModExt.lean is not the KMod library\'s 94d7a572'

def env_names():
    out = set()
    for root in LPF.split(':'):
        for dp, _, fs in os.walk(root):
            for f in fs:
                if f.endswith('.olean'): out.add(os.path.relpath(os.path.join(dp, f[:-6]), root).replace('/', '.'))
    return out

TYCHK = os.path.join(KE.QUEUE, 'KModTyChk.lean')
def lean_run(tool, arg, lp):
    ni = max(0, 10 - os.nice(0))
    env = dict(os.environ, LEAN_PATH=lp, PATH=os.path.dirname(LEAN) + ':' + os.environ.get('PATH', ''))   # findSysroot: `lean` on PATH
    return subprocess.run(['prlimit', '--as=%d' % (64 * 2**30), sys.executable, NOTHP, 'nice', '-n', str(ni), LEAN, '--run', tool, arg],
                          capture_output=True, text=True, env=env, timeout=7200)

def run_batch(bid, obl, pkgs):
    """obl: [(module, const)], pkgs: [(pid, tarball object, sha256)] whose store files the batch needs; returns the result dict.
    A store obligation into a module with a .kman (a KMod module of its producing package, whose audit PASS covers its walk) is
    resolved by its manifest: the constant is one of the module's KPUB theorems, or ends in .EXT and occurs in the statement of one
    (KModTyChk.lean, exported level); one into a data table (.kplain) or any other module is walked at the private level (KModExt)."""
    d = os.path.join(W, 'batches', bid); tmp = os.path.join(W, 'tmp', bid); res = dict(batch=bid, n=len(obl), pkgs=len(pkgs), t0=time.time())
    try:
        lp = LPF; walk = list(obl); kpub = {}; errs = []; tych = []
        if pkgs:
            st = os.path.join(tmp, 'store'); os.makedirs(st, exist_ok=True)
            def fetch(p3):
                pid, obj, sha = p3
                raw = objstore.fetch(B, obj, timeout=180, tries=6)
                if hashlib.sha256(raw).hexdigest() != sha: raise RuntimeError('%s: tarball sha256 differs from its done record' % pid)
                # zstd + tar in a subprocess (no GIL): only the module files
                subprocess.run(['bash', '-c', "zstd -dc | tar xf - -C %s --wildcards 'store/*.olean' 'store/*.olean.private' 'store/*.olean.server' 'store/*.ir' 'store/*.kman' 'store/*.kplain' 2>/dev/null; true" % tmp],
                               input=raw, check=True)
            with cf.ThreadPoolExecutor(16) as fx: list(fx.map(fetch, pkgs))
            lp = st + ':' + TOP + ':' + LPF
            walk = []
            for n, c in obl:
                base = os.path.join(st, *n.split('.'))
                if os.path.exists(base + '.kman'):
                    if n not in kpub: kpub[n] = [l.split()[1] for l in open(base + '.kman', errors='replace') if l.startswith('KPUB ')]
                    if c in kpub[n]: continue
                    if c.endswith('.EXT'): tych.append((n, c)); continue
                    errs.append('%s is not a KPUB theorem of KMod module %s' % (c, n))
                else: walk.append((n, c))
            res['manifest'] = len(obl) - len(walk) - len(tych) - len(errs); res['tycheck'] = len(tych)
        if tych:
            open(d + '.tychk', 'w').write(''.join('%s %s %s\n' % (n, c, ' '.join(kpub[n])) for n, c in tych))
            r = lean_run(TYCHK, d + '.tychk', lp)
            okp = {tuple(l.split()[1:3]) for l in r.stdout.splitlines() if l.startswith('TYOK')}
            errs += ['%s does not occur in a KPUB statement of %s' % (c, n) for n, c in tych if (n, c) not in okp]
        res['walked'] = len(walk); std = set(); bad = []; summ = None; kv = {'bad': '0', 'obligations': '0'}; rc = 0
        if walk:
            open(d + '.obl', 'w').write(''.join('%s %s\n' % x for x in walk))
            r = lean_run(EXT, d + '.obl', lp); rc = r.returncode
            open(d + '.out', 'w').write(r.stdout + r.stderr)
            sl = [l for l in r.stdout.splitlines() if l.startswith('EXTSUM ')]; summ = sl[-1] if sl else None
            std = {l.split()[2] for l in r.stdout.splitlines() if l.startswith('EXT STD ')}
            bad = [l for l in r.stdout.splitlines() if l.startswith('EXT BAD ')]
            kv = dict(x.split('=', 1) for x in summ.split()[1:]) if summ else {}
        res.update(rc=rc, extsum=summ, std=sorted(std), bad=bad[:20], errors=errs[:20],
                   ok=(rc == 0 and (summ is not None or not walk) and kv.get('bad') == '0' and std <= STD and not errs
                       and int(kv.get('obligations', -1)) == len(walk)))
    except Exception as e:
        res.update(ok=False, error=repr(e)[:400])
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    res['wall'] = time.time() - res['t0']; json.dump(res, open(d + '.json', 'w'))
    return res

def one_loop(ENV):
    db = sqlite3.connect(KE.VERIFIER_DB, timeout=600)
    db.execute('create table if not exists walked (tier text, module text, const text, batch text, primary key (tier, module, const)) without rowid')
    db.execute('create table if not exists walkfail (batch text primary key, tries int, detail text)')
    pend = db.execute('select o.tier, o.module, o.const from obl o left join walked w on o.tier=w.tier and o.module=w.module and o.const=w.const '
                      'where w.batch is null').fetchall()
    # one walk per (module, const) whatever the tier: obligations already walked under another tier are recorded as walked by that batch
    seen = dict(((m, c), b) for m, c, b in db.execute('select module, const, batch from walked'))
    todo = collections.defaultdict(list); reuse = []
    for t, m, c in pend:
        if (m, c) in seen: reuse.append((t, m, c, seen[(m, c)]))
        else: todo[(m, c)].append(t)
    if reuse: db.executemany('insert or ignore into walked values (?,?,?,?)', reuse); db.commit()
    prod = {}
    if todo:
        mods = {m for m, _ in todo}
        for m, pid in db.execute('select module, pid from produced'):
            if m in mods: prod[m] = pid
    envs = sorted(k for k in todo if k[0] in ENV and k[0] not in prod)
    store = collections.defaultdict(list); unknown = []
    for k in todo:
        if k[0] in prod: store[prod[k[0]]].append(k)
        elif k[0] not in ENV: unknown.append(k)
    batches = []
    # env batches: <= 150 modules each
    cur, mods = [], set()
    for k in envs:
        if k[0] not in mods and len(mods) >= 150: batches.append(('env', cur, [])); cur, mods = [], set()
        cur.append(k); mods.add(k[0])
    if cur: batches.append(('env', cur, []))
    # store batches: <= bpk producing packages each (their tarball objects from the done records)
    pids = sorted(store)
    # tarball objects from the verifier's record cache when its generation is the current done record's (a GET per package took
    # ~20 min for 30k packages); the others are read
    listing = {it['name'].rsplit('/', 1)[1][:-5]: str(it['generation']) for it in objstore.ls(B, P + '/done/', fields='name,generation') if it['name'].endswith('.json')}
    cache = {}
    cf_ = KE.DONE_RECORDS
    if os.path.exists(cf_):
        want = set(pids)
        for l in open(cf_):
            try: r = json.loads(l)
            except ValueError: continue
            if r['id'] in want and listing.get(r['id']) == r.get('_gen'): cache[r['id']] = (r['object'], r['sha256'])
    def rec(pid):
        if pid in cache: return (pid,) + cache[pid]
        try:
            g = objstore.get(B, P + '/done/%s.json' % pid, timeout=30, tries=4); d = json.loads(g[0]); return pid, d['object'], d['sha256']
        except Exception: return pid, None, None
    with cf.ThreadPoolExecutor(32) as ex: info = {pid: (o, s) for pid, o, s in ex.map(rec, pids) if o and pid in listing}
    for i in range(0, len(pids), bpk):
        grp = [p for p in pids[i:i + bpk] if p in info]
        if grp: batches.append(('store', [k for p in grp for k in store[p]], [(p, info[p][0], info[p][1]) for p in grp]))
    stamp = time.strftime('%H%M%S', time.gmtime())
    jobs = [('%s_%s_%03d' % (kind, stamp, j), obl, pk) for j, (kind, obl, pk) in enumerate(batches)]
    mb = opt('--max-batches', 0)
    if mb:      # a trial: the first env batch and the first store batches only
        jobs = [j for j in jobs if j[0].startswith('env')][:1] + [j for j in jobs if j[0].startswith('store')][:max(0, mb - 1)]
    log('pending: %d obligations (%d already walked under another tier); %d env, %d store in %d packages, %d unknown; %d batches' % (
        len(pend), len(reuse), len(envs), sum(len(v) for v in store.values()), len(store), len(unknown), len(jobs)))
    nok = nfail = 0
    with cf.ThreadPoolExecutor(par) as ex:
        for (bid, obl, pk), res in zip(jobs, ex.map(lambda j: run_batch(*j), jobs)):
            if res.get('ok'):
                db.executemany('insert or ignore into walked values (?,?,?,?)', [(t, m, c, bid) for m, c in obl for t in todo[(m, c)]]); nok += 1
            else:
                nfail += 1; db.execute('insert or replace into walkfail values (?, coalesce((select tries from walkfail where batch=?), 0) + 1, ?)',
                                       (bid, bid, json.dumps({k: res.get(k) for k in ('rc', 'extsum', 'bad', 'error')})[:2000]))
                log('BATCH FAILED', bid, json.dumps({k: res.get(k) for k in ('rc', 'extsum', 'bad', 'error')})[:400])
            db.commit()
    tot = db.execute('select count(*) from obl').fetchone()[0]; wk = db.execute('select count(*) from walked').fetchone()[0]
    nf = db.execute('select count(*) from walkfail').fetchone()[0]
    line = '%s walk: %d of %d obligation entries walked (std <= {propext, Classical.choice, Quot.sound}, bad=0); this pass %d batches ok, %d failed; unknown modules %d; failed batches recorded %d' % (
        time.strftime('%FT%TZ', time.gmtime()), wk, tot, nok, nfail, len(unknown), nf)
    if unknown: json.dump(unknown[:1000], open(os.path.join(W, 'UNKNOWN.json'), 'w'))
    open(os.path.join(W, 'STATUS'), 'w').write(line + '\n'); print(line, flush=True)

if __name__ == '__main__':
    ENV = env_names(); log('final LEAN_PATH modules: %d' % len(ENV))
    while True:
        try: one_loop(ENV)
        except Exception as e: log('loop error', repr(e)[:300])
        if '--once' in a: break
        time.sleep(loop)
