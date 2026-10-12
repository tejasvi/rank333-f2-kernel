#!/usr/bin/env python3
"""mkkch.py: for every counted giant (giants/h<c>_<J>/giant.json): the emitter inputs for its heavy packages
(ip/subh<c>/<J>.txt: its depth-D sub-job frontier, local indices; subtoph<c>/<J>.bin: the top trace of the same
DUMPONLY run) and its sub-job table module KCH.S<c>_<J> (public #rttablew of the sub-jobs' mode-0 prefix headers, 128- or 256-bit
entries; package KCH, never KC) with its data; writes manifest.jsonl (sched.py) for the tables not built yet."""
import sys, os, glob, json, shutil
sys.path.insert(0, os.environ['KC_PY'])   # kcagg_v3/py (kcgen.py)
import kcgen
K = kcgen.K; K.load_class_contexts()
I = os.environ.get('KC_INPUTS', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'inputs', 'classes'))
G = os.path.join(I, 'giants') + '/'
T = os.environ.get('KC_IPOUT', 'ip_out') + '/'   # ip/subh<c>, ip/subtoph<c> (as in the emitter tools tree's ip/)
S = os.environ.get('KC_KCHOUT', 'kch_out') + '/'
rows = []; LAB = {}
for gj in sorted(glob.glob(G + 'h*_*/giant.json')):
    g = json.load(open(gj)); c, J = g['class'], g['job']; ctx = 'h' + c; K.set_format(ctx); d = os.path.dirname(gj)
    os.makedirs(T + 'subh%s' % c, exist_ok=True); os.makedirs(T + 'subtoph%s' % c, exist_ok=True)
    shutil.copy(d + '/fr.txt', T + 'subh%s/%d.txt' % (c, J)); shutil.copy(glob.glob(d + '/top_*_top.bin')[0], T + 'subtoph%s/%d.bin' % (c, J))
    pre = [l.split()[1] for l in open(d + '/fr.txt') if l.strip()]
    if ctx not in LAB:
        E = K.EMIT[ctx]; vecs = list(map(int, open(K.ipf(E['ip'])).read().split('\n')[1].split())); ordv = list(map(int, open(K.ipf(E['order'])).read().split()))
        LAB[ctx] = {vecs[o]: i for i, o in enumerate(ordv)}
    lab = LAB[ctx]
    def hdr(p):
        pl = [lab[int(v)] for v in p.split(',')]; h = (len(pl) << 1) | (pl[-1] << 6)
        for i, l in enumerate(pl): h |= l << (13 + 7 * i)
        return h
    HT = [hdr(p) for p in pre]; W = 128 if max(h.bit_length() for h in HT) <= 128 else 256
    assert HT[0] == K.hdr_of_prefix(ctx, pre[0])
    with open(S + 'src/data/KCH_S%s_%d.bin' % (c, J), 'wb') as f:
        for h in HT: f.write(h.to_bytes(W // 8, 'little'))
    m = 'KCH.S%s_%d' % (c, J)
    open(S + 'src/KCH/S%s_%d.lean' % (c, J), 'w').write('\n'.join(['module', 'public import RT.Load',
        '/-! # The sub-job table of giant root job %d of class %s (%d depth-%d sub-jobs, leaf2/kc/giants), public data: sub-job k\'s mode-0 prefix header -/' % (J, c, len(pre), g['depth']),
        '#rttablew %s "data/KCH_S%s_%d.bin" 64 %d' % (m, c, J, W), '']))
    if not os.path.exists(S + 'build/KCH/S%s_%d.olean' % (c, J)):
        rows.append({'module': m, 'src': 'src/KCH/S%s_%d.lean' % (c, J), 'cwd': 'src', 'tier': 'kch', 'kind': 'table', 'deps': [], 'pred_s': 2.0, 'pred_gb': 1.0})
open(S + 'manifest.jsonl', 'w').write(''.join(json.dumps(r) + '\n' for r in rows))
print('giants', len(glob.glob(G + 'h*_*/giant.json')), 'tables to build', len(rows))
