#!/usr/bin/env python3
"""sample_check.py [--max N] [--par 32] [--out FILE]: V5 F1 on the seeded 0.1% private sample (PREFIX/sample/<pkg>/<module>.olean.private,
uploaded by each package's finalize before its private parts were deleted).  Per sampled module M of package Q:
  * Q's result tarball (sha256 = its done record) gives M's public .olean (+ .olean.server) and the package's other modules; M's
    recorded own private hash (KMH private= in M's .mhash) must equal the sample object's sha256 (it is that build's private part);
  * the toolchain's own leanchecker (Lean v4.30.0, bin/leanchecker) replays every declaration of M, private bodies included, into
    the environment of M's imports through the kernel; LEAN_PATH = scratch store : FINAL_DIR/topstore/store : FINAL_DIR/lpath_final.txt.
A sample whose module imports a sibling with `import all` whose private part is not sampled is "not checkable" (the KMod policy deletes
unsampled private parts); a "missing object file" (the scratch store's top-level package directory hides the top store's directory
of that name) is marked "harness" and checked again by sample_overlay.py with one merged root.
One JSON line per module in OUT (default FINAL_DIR/recheck/sample_check.jsonl); a summary line at the end.  Env: kitenv.py
(PB_TOOLCHAIN: the bin directory with leanchecker), objstore.py."""
import concurrent.futures as cf, hashlib, json, os, shutil, subprocess, sys, tempfile, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
F = KE.FINAL; H = os.path.join(F, 'recheck'); os.makedirs(H, exist_ok=True)
a = sys.argv[1:]; opt = lambda n, d, c=int: c(a[a.index(n) + 1]) if n in a else d
TC = KE.TOOLCHAIN
LPF = open(os.path.join(F, 'lpath_final.txt')).read().strip(); TOP = os.path.join(F, 'topstore', 'store')
OUT = opt('--out', os.path.join(H, 'sample_check.jsonl'), str)
done_before = set()
if os.path.exists(OUT):
    for l in open(OUT):
        try: done_before.add(json.loads(l)['object'])
        except Exception: pass
samples = {}
for it in objstore.ls(B, P + '/sample/', fields='name,size'):
    pkg = it['name'][len(P + '/sample/'):].split('/')[0]
    if it['name'] not in done_before: samples.setdefault(pkg, []).append(it['name'])
pkgs = sorted(samples)[:opt('--max', 10**9)]
def one(pkg):
    out = []; tmp = tempfile.mkdtemp(prefix='smp_', dir=H)
    try:
        g = objstore.get(B, P + '/done/%s.json' % pkg)
        if not g: return [dict(object=o, pkg=pkg, ok=None, note='package no longer done (superseded): skipped') for o in samples[pkg]]
        d = json.loads(g[0])
        raw = objstore.fetch(B, d['object'], timeout=180, tries=6)
        if hashlib.sha256(raw).hexdigest() != d['sha256']: return [dict(object=o, pkg=pkg, ok=False, note='tarball sha256 != done record') for o in samples[pkg]]
        subprocess.run(['bash', '-c', 'zstd -dc | tar xf - -C %s store 2>/dev/null; true' % tmp], input=raw, check=True)
        for o in samples[pkg]:
            mod = o.rsplit('/', 1)[1][:-len('.olean.private')]; base = os.path.join(tmp, 'store', *mod.split('.'))
            pb = objstore.fetch(B, o, timeout=120, tries=6)
            psha = hashlib.sha256(pb).hexdigest()
            kmh = None
            if os.path.exists(base + '.mhash'):
                for l in open(base + '.mhash'):
                    if l.startswith('KMH '): kmh = dict(x.split('=', 1) for x in l.split()[2:] if '=' in x).get('private')
            if not os.path.exists(base + '.olean'): out.append(dict(object=o, pkg=pkg, module=mod, ok=False, note='no .olean in the tarball')); continue
            open(base + '.olean.private', 'wb').write(pb)
            t0 = time.time()
            r = subprocess.run(['prlimit', '--as=%d' % (32 * 2**30), 'nice', '-n', str(max(0, 10 - os.nice(0))), os.path.join(TC, 'leanchecker'), mod],
                               capture_output=True, text=True, timeout=3600,
                               env=dict(os.environ, PATH=TC + ':' + os.environ.get('PATH', ''), LEAN_PATH=os.path.join(tmp, 'store') + ':' + TOP + ':' + LPF))
            txt = (r.stdout + r.stderr).strip()
            # a module that imports a sibling with `import all` needs that sibling's private part, deleted by policy unless sampled
            # too: not checkable here (reported apart, never as a pass)
            nc = r.returncode != 0 and 'missing data file for module' in txt
            # the scratch store's package dir hides the top store's (Lean binds a package dir to the first LEAN_PATH root that has
            # it): checked again with a merged root by sample_overlay.py; never a FAIL
            harness = r.returncode != 0 and 'object file' in txt and 'does not exist' in txt
            out.append(dict(object=o, pkg=pkg, module=mod, private_sha=psha, kmh_private=kmh, kmh_match=(kmh == psha), rc=r.returncode,
                            wall=round(time.time() - t0, 1), tail=txt[-300:], not_checkable=nc, harness=harness,
                            ok=(None if (nc or harness) and kmh == psha else (r.returncode == 0 and kmh == psha))))
    except Exception as e:
        out.append(dict(pkg=pkg, ok=False, note='error %r' % e))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return out
n = ok = bad = skip = 0
with cf.ThreadPoolExecutor(opt('--par', 32)) as ex, open(OUT, 'a') as f:
    for res in ex.map(one, pkgs):
        for x in res:
            f.write(json.dumps(x) + '\n'); n += 1
            if x.get('ok') is None: skip += 1
            elif x['ok']: ok += 1
            else: bad += 1
print('%s sample check: %d sampled private parts in %d packages: %d PASS, %d FAIL, %d not checkable (an import-all sibling private part deleted by policy) or superseded' % (
    time.strftime('%FT%TZ', time.gmtime()), n, len(pkgs), ok, bad, skip))
