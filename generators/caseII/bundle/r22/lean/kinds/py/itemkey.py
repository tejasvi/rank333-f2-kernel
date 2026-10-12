#!/usr/bin/env python3
"""itemkey.py TEXT OUTDIR: the R22N.Glue key of an item, written to OUTDIR/key.txt (native/infra/lib/py/segkey.py's encoder):
root = (S, last) of the stream's #root line, the external children of OUTDIR/extL.txt (kitem.py: one "S u" line per DN / JB
reference, in stream order; none if the file is absent), and lo and the ranges of OUTDIR/rngL.txt ("lo L", then one "S last l"
line per RG reference in stream order; lo 0 and none if absent).  OUTDIR/key.sha256: the sha256 of the decimal string."""
import sys, os, hashlib
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.environ.get('KINDS_R22', '.') + '/lean/native/infra/lib/py')
import segkey
for ln in open(sys.argv[1]):
    if ln.startswith('#root'): root = [int(x) for x in ln.split()[3:]]; break
S = 0
for l in root: S |= 1 << l
ext = []
ef = os.path.join(sys.argv[2], 'extL.txt')
if os.path.exists(ef):
    for ln in open(ef):
        a = ln.split()
        if a: ext.append((int(a[0]), int(a[1])))
lo = 0; rng = []
rf = os.path.join(sys.argv[2], 'rngL.txt')
if os.path.exists(rf):
    for ln in open(rf):
        a = ln.split()
        if not a: continue
        if a[0] == 'lo': lo = int(a[1])
        else: rng.append(((int(a[0]), int(a[1])), int(a[2])))
k = segkey.encode((S, root[-1]), lo, ext, rng)
d = segkey.decode(k); assert d['root'] == (S, root[-1]) and d['lo'] == lo and d['ext'] == ext and d['rng'] == rng
ks = str(k)
open(os.path.join(sys.argv[2], 'key.txt'), 'w').write(ks + '\n')
open(os.path.join(sys.argv[2], 'key.sha256'), 'w').write(hashlib.sha256(ks.encode()).hexdigest() + '\n')
