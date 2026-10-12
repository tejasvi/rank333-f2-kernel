#!/usr/bin/env python3
"""envmanifest.py [--check] [--par 32]: V5 item B5, the pinned final environment.  Without --check: the sha256 of every .olean and
.olean.private under the roots of FINAL_DIR/lpath_final.txt, written to FINAL_DIR/env_manifest.sha256 ("<sha256>  <path>", sorted).
With --check: recomputes and reports every changed, added or removed file (exit 1 if any)."""
import concurrent.futures as cf, hashlib, os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'queue'))
import kitenv as KE
H = KE.FINAL
LP = open(os.path.join(H, 'lpath_final.txt')).read().strip().split(':')
OUT = os.path.join(H, 'env_manifest.sha256')
par = int(sys.argv[sys.argv.index('--par') + 1]) if '--par' in sys.argv else 32
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''): h.update(b)
    return h.hexdigest()
files = []
for root in LP:
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith(('.olean', '.olean.private')): files.append(os.path.join(dp, f))
t = time.time()
with cf.ThreadPoolExecutor(par) as ex: cur = dict(zip(files, ex.map(sha, files)))
if '--check' not in sys.argv:
    with open(OUT + '.tmp', 'w') as f:
        for p in sorted(cur): f.write('%s  %s\n' % (cur[p], p))
    os.replace(OUT + '.tmp', OUT)
    print('%s env manifest: %d files under %d roots in %.0f s -> %s' % (time.strftime('%FT%TZ', time.gmtime()), len(cur), len(LP), time.time() - t, OUT))
else:
    old = {}
    for l in open(OUT):
        h, p = l.rstrip('\n').split('  ', 1); old[p] = h
    ch = sorted(p for p in cur if p in old and cur[p] != old[p]); add = sorted(set(cur) - set(old)); rem = sorted(set(old) - set(cur))
    print('%s env check: %d files; changed %d, added %d, removed %d' % (time.strftime('%FT%TZ', time.gmtime()), len(cur), len(ch), len(add), len(rem)))
    for x in (ch[:20] + add[:20] + rem[:20]): print('  ', x)
    sys.exit(1 if (ch or add or rem) else 0)
