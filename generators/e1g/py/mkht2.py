#!/usr/bin/env python3
"""mkht2.py CTX NAME: the production job table of a context cap (KH.<NAME>, package KH: prebuilt in the closure, outside the
store's package KJ): KH/<NAME>.lean, data data/KH_<NAME>.bin (-> E1P/data).  Entry k is the mode-0
prefix header of depth-6 job k (`[1] 0, [5] d, [7] pos, d × [7] labels`, labels = positions in the ordered IP, pos = the last
label): what job k's module proves (`JobOK C sl UB (L_0 % 2^(13 + 7 d))`) and what `glue0` reads.  Same entries as mkht.py's
rehearsal tables KJ.HT436 / KJ.HT422."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kjlib as K
ctx, name = sys.argv[1:3]
E = K.EMIT[ctx]
toks = open(K.ipf(E['ip'])).read().split('\n')[1].split(); vecs = list(map(int, toks)); ordv = list(map(int, open(K.ipf(E['order'])).read().split()))
lab = {vecs[o]: i for i, o in enumerate(ordv)}
HT = []
for ln in open(K.ipf(E['frontier'])):
    if not ln.strip(): continue
    k, pre = ln.split(); assert int(k) == len(HT)
    pl = [lab[int(v)] for v in pre.split(',')]; d = len(pl)
    h = (d << 1) | (pl[-1] << 6)
    for i, l in enumerate(pl): h |= l << (13 + 7 * i)
    HT.append(h)
with open(K.DD + 'KH_%s.bin' % name, 'wb') as f:
    for h in HT: f.write(h.to_bytes(16, 'little'))
os.makedirs(K.H + 'mod/src/KH', exist_ok=True)
open(K.H + 'mod/src/KH/%s.lean' % name, 'w').write('\n'.join(['module', 'public import RT.Load',
    '/-! # The job table of %s (%d depth-6 jobs of %s), public data: job k\'s mode-0 prefix header -/' % (ctx, len(HT), E['frontier']),
    '#rttablew KH.%s "data/KH_%s.bin" 64 128' % (name, name), '']))
print('KH.%s: %d headers' % (name, len(HT)))
