#!/usr/bin/env python3
"""mkht3.py CAP [J...]: the sub-job tables of a context cap's heavy depth-6 jobs (all of them if no J is given), package KH
(prebuilt in the closure): KH.S<C>_<J> (KH/S<C>_<J>.lean, data KH_S<C>_<J>.bin); entry k is the mode-0 prefix header
of sub-job k of the native depth-10 split (frontier E1P/run/cap2/sub<C>/<J>.txt), what its module proves and glue0 reads."""
import sys, os, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kjlib as K
cap = sys.argv[1]; C = cap[1:] if cap.startswith('c') else cap; cap = 'c' + C
E = K.EMIT[cap]
toks = open(K.ipf(E['ip'])).read().split('\n')[1].split(); vecs = list(map(int, toks)); ordv = list(map(int, open(K.ipf(E['order'])).read().split()))
lab = {vecs[o]: i for i, o in enumerate(ordv)}
Js = [int(x) for x in sys.argv[2:]] or sorted(int(os.path.basename(f)[:-4]) for f in glob.glob(K.H + 'E1P/run/cap2/sub%s/*.txt' % C))
os.makedirs(K.H + 'mod/src/KH', exist_ok=True); mods = []
for J in Js:
    HT = []
    for ln in open(K.ipf('sub%s/%d.txt' % (C, J))):
        k, pre = ln.split(); assert int(k) == len(HT)
        pl = [lab[int(v)] for v in pre.split(',')]; d = len(pl)
        h = (d << 1) | (pl[-1] << 6)
        for i, l in enumerate(pl): h |= l << (13 + 7 * i)
        assert h < 1 << 128
        HT.append(h)
    with open(K.DD + 'KH_S%s_%d.bin' % (C, J), 'wb') as f:
        for h in HT: f.write(h.to_bytes(16, 'little'))
    open(K.H + 'mod/src/KH/S%s_%d.lean' % (C, J), 'w').write('\n'.join(['module', 'public import RT.Load',
        '/-! # The sub-job table of heavy job %d of c%s (%d depth-10 sub-jobs), public data: sub-job k\'s mode-0 prefix header -/' % (J, C, len(HT)),
        '#rttablew KH.S%s_%d "data/KH_S%s_%d.bin" 64 128' % (C, J, C, J), '']))
    mods.append('KH.S%s_%d' % (C, J))
open(K.H + 'mod/kh_%s_order.txt' % C, 'w').write('\n'.join(mods) + '\n')
print('%d sub-job tables of c%s' % (len(mods), C))
