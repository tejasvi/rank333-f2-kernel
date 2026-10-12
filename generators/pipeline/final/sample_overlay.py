#!/usr/bin/env python3
"""sample_overlay.py [--par 8] [--in sample_check.jsonl] [--out sample_overlay.jsonl]: check again the samples that sample_check.py
marked "harness" ("object file <scratch>/store/KJ/X.olean ... does not exist": the scratch store holds only the sample's package under
KJ/ (or PLE/, NDX/, ...), and Lean binds a top-level package directory to the FIRST LEAN_PATH root that has it, so the scratch KJ/
hides the top store's KJ/).  Here each sample gets ONE merged root: the store-import closure of the sampled
module, walked through the .mhash KIMP records (each module's direct imports; a store import is the package's own file when the
package ships it, else the top store's, else its producer's full tarball, verified and cached in ovl_cache/), is hard-linked into overlay/<pkg dir>/..., the sample's own files beside them, and LEAN_PATH =
overlay : FINAL_DIR/lpath_final.txt.  Then the toolchain's leanchecker replays the module exactly as sample_check.py does (same
private part from the store, same KMH private-hash check).  One JSON line per sample in OUT, and a summary line.  Env: kitenv.py
(FINAL_DIR, PB_TOOLCHAIN, PB_STORE_PREFIX, VERIFIER_DB), objstore.py."""
import concurrent.futures as cf, hashlib, json, os, shutil, subprocess, sys, tempfile, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
F = KE.FINAL; H = os.path.join(F, 'recheck'); os.makedirs(H, exist_ok=True)
a = sys.argv[1:]; opt = lambda n, d, c=int: c(a[a.index(n) + 1]) if n in a else d
TC = KE.TOOLCHAIN
LPF = open(os.path.join(F, 'lpath_final.txt')).read().strip(); TOP = os.path.join(F, 'topstore', 'store')
IN = opt('--in', os.path.join(H, 'sample_check.jsonl'), str); OUT = opt('--out', os.path.join(H, 'sample_overlay.jsonl'), str)
todo = {}
for l in open(IN):
    try: r = json.loads(l)
    except Exception: continue
    if r.get('ok') is False and 'object file' in (r.get('tail') or '') and 'does not exist' in (r.get('tail') or ''):
        todo.setdefault(r['pkg'], []).append(r['object'])
done_before = set()
if os.path.exists(OUT):
    for l in open(OUT):
        try: done_before.add(json.loads(l)['object'])
        except Exception: pass
for k in list(todo):
    todo[k] = [o for o in todo[k] if o not in done_before]
    if not todo[k]: todo.pop(k)
STORE_PREFIX = KE.STORE_PREFIX
import sqlite3, threading
DB = sqlite3.connect(KE.VERIFIER_DB, timeout=600, check_same_thread=False); DBL = threading.Lock()
CACHE = os.path.join(H, 'ovl_cache'); os.makedirs(CACHE, exist_ok=True); CL = collections_lock = {}; CLL = threading.Lock()
def producer_store(m):
    # a store import that is neither the package's own file nor in the top store (an inner module of another package, e.g. a range
    # module an aggregation imports): its producer (verifier.db produced) and that producer's full tarball, verified, extracted once
    with DBL: row = DB.execute('select pid from produced where module = ?', (m,)).fetchone()
    if not row: return None
    pid = row[0]; d0 = os.path.join(CACHE, pid)
    with CLL: lk = CL.setdefault(pid, threading.Lock())
    with lk:
        if not os.path.exists(os.path.join(d0, '.ok')):
            g = objstore.get(B, P + '/done/%s.json' % pid)
            if not g: return None
            d = json.loads(g[0])
            raw = objstore.fetch(B, d['object'], timeout=180, tries=6)
            if hashlib.sha256(raw).hexdigest() != d['sha256']: return None
            os.makedirs(d0, exist_ok=True)
            subprocess.run(['bash', '-c', 'zstd -dc | tar xf - -C %s store 2>/dev/null; true' % d0], input=raw, check=True)
            open(os.path.join(d0, '.ok'), 'w').close()
    f = os.path.join(d0, 'store', *m.split('.'))
    return f if os.path.exists(f + '.olean') else None
EXTS = ('.olean', '.olean.server', '.ilean', '.olean.private', '.ir', '.mhash')
def kimps(mh):
    out = []
    try:
        for l in open(mh):
            if l.startswith('KIMP '):
                w = l.split()
                if len(w) >= 3 and w[2].startswith(STORE_PREFIX): out.append(w[1])
    except FileNotFoundError: pass
    return out
def one(pkg):
    out = []; tmp = tempfile.mkdtemp(prefix='ovl_', dir=H)
    try:
        g = objstore.get(B, P + '/done/%s.json' % pkg)
        if not g: return [dict(object=o, pkg=pkg, ok=None, note='package no longer done (superseded): skipped') for o in todo[pkg]]
        d = json.loads(g[0])
        raw = objstore.fetch(B, d['object'], timeout=180, tries=6)
        if hashlib.sha256(raw).hexdigest() != d['sha256']: return [dict(object=o, pkg=pkg, ok=False, note='tarball sha256 != done record') for o in todo[pkg]]
        os.makedirs(os.path.join(tmp, 'pkg'))
        subprocess.run(['bash', '-c', 'zstd -dc | tar xf - -C %s store 2>/dev/null; true' % os.path.join(tmp, 'pkg')], input=raw, check=True)
        own = os.path.join(tmp, 'pkg', 'store')
        def src(m):   # where module m's files are: the package's own copy first, else the top store
            o = os.path.join(own, *m.split('.'))
            if os.path.exists(o + '.olean'): return o
            t = os.path.join(TOP, *m.split('.'))
            return t if os.path.exists(t + '.olean') else producer_store(m)
        for o in todo[pkg]:
            mod = o.rsplit('/', 1)[1][:-len('.olean.private')]
            base = os.path.join(own, *mod.split('.'))
            pb = objstore.fetch(B, o, timeout=120, tries=6)
            psha = hashlib.sha256(pb).hexdigest(); kmh = None
            for l in (open(base + '.mhash') if os.path.exists(base + '.mhash') else []):
                if l.startswith('KMH '): kmh = dict(x.split('=', 1) for x in l.split()[2:] if '=' in x).get('private')
            open(base + '.olean.private', 'wb').write(pb)
            # the store-import closure through the .mhash records
            need = {}; stack = [mod]; missing = []
            while stack:
                m = stack.pop()
                if m in need: continue
                s = src(m)
                if s is None: missing.append(m); need[m] = None; continue
                need[m] = s; stack += [x for x in kimps(s + '.mhash') if x not in need]
            if missing:
                out.append(dict(object=o, pkg=pkg, module=mod, ok=False, note='store imports with no file: %s' % missing[:5])); continue
            ov = os.path.join(tmp, 'ovl_%s' % hashlib.md5(mod.encode()).hexdigest()[:8])
            for m, s in need.items():
                dst = os.path.join(ov, *m.split('.')); os.makedirs(os.path.dirname(dst), exist_ok=True)
                for x in EXTS:
                    if os.path.exists(s + x) and not os.path.exists(dst + x):
                        # hard links, not symlinks: leanchecker enumerates the search path's oleans and skips symlinked files
                        try: os.link(os.path.realpath(s + x), dst + x)
                        except OSError: shutil.copy2(s + x, dst + x)
            t0 = time.time()
            r = subprocess.run(['prlimit', '--as=%d' % (32 * 2**30), 'nice', '-n', str(max(0, 10 - os.nice(0))), os.path.join(TC, 'leanchecker'), mod],
                               capture_output=True, text=True, timeout=3600,
                               env=dict(os.environ, PATH=TC + ':' + os.environ.get('PATH', ''), LEAN_PATH=ov + ':' + LPF))
            txt = (r.stdout + r.stderr).strip()
            nc = r.returncode != 0 and 'missing data file for module' in txt
            out.append(dict(object=o, pkg=pkg, module=mod, private_sha=psha, kmh_private=kmh, kmh_match=(kmh == psha), rc=r.returncode,
                            wall=round(time.time() - t0, 1), overlay_modules=len(need), tail=txt[-300:], not_checkable=nc,
                            ok=(None if nc and kmh == psha else (r.returncode == 0 and kmh == psha))))
    except Exception as e:
        out.append(dict(pkg=pkg, ok=False, note='error %r' % e))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return out
n = ok = bad = skip = 0
with cf.ThreadPoolExecutor(opt('--par', 8)) as ex, open(OUT, 'a') as f:
    for res in ex.map(one, sorted(todo)):
        for x in res:
            f.write(json.dumps(x) + '\n'); f.flush(); n += 1
            if x.get('ok') is None: skip += 1
            elif x['ok']: ok += 1
            else: bad += 1
print('%s overlay re-check: %d samples in %d packages: %d PASS, %d FAIL, %d not checkable (import-all sibling private part deleted by policy) or superseded' % (
    time.strftime('%FT%TZ', time.gmtime()), n, len(todo), ok, bad, skip))
