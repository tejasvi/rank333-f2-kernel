#!/usr/bin/env python3
"""mkcut.py OUT.jsonl [TARGET_S]: the wave-1 package cut list of the context caps c436 and c422, from the native counts
(E1P/run/cap2/js<C>_1.txt "ix nodes leaves sec": depth-6 jobs; js<C>_2.txt "share ix nodes leaves sec": the depth-10 sub-jobs of
the heavy depth-6 jobs, whose prefixes are subfr<C>.txt, contiguous per parent).

Kernel cost per job (isolated, the tier totals of DESIGN §43.5 spread over the counts): c436 0.52 ms per st-node + 15.9 ms per
leaf; c422 0.61 ms + 22.4 ms.  Packages (one JSON line each):
  range      light depth-6 jobs [a, b) (each at most 600 s), cut at TARGET_S (default 5400 s) and at every heavy or split job;
             emitpkg.sh CAP a b OUT
  split      one depth-6 job over 600 s that the native run did not split: split at depth 8 directly (recursively deeper);
             emitpkg.sh CAP k k+1 OUT --split 8
  heavy-sub  sub-jobs [a, b) of heavy job J (local indices in its depth-10 frontier, each at most 600 s), cut at TARGET_S;
             emitpkg.sh CAP a b OUT --heavy J
  heavy-split one depth-10 sub-job over 600 s: split at depth 12 directly; emitpkg.sh CAP k k+1 OUT --heavy J --split 12
Every heavy job J also needs, in the aggregation phase, its sub-job table KH.S<C>_<J> (prebuilt), its top chain (emitted once,
--root P --frontier 10 --cert top) and the range [J, J+1) over KH.HT<C>; those are listed in OUT's companion heavy.jsonl."""
import sys, json
import os
R22 = os.environ.get('R22_ROOT', '.')   # the development layout's root (package mode does not use it)
RUN = R22 + '/e1g/E1P/run/cap2/'
PRICE = {'436': (0.52, 15.9), '422': (0.61, 22.4)}
LIMIT = 600.0
out = sys.argv[1]; TARGET = float(sys.argv[2]) if len(sys.argv) > 2 else 5400.0
pk = []; heavy_rows = []
def runs(items, C, kind_light, kind_split, extra, split_depth):
    """cut a sequence of (index, cost) into light ranges and split runs (consecutive jobs over LIMIT, all split directly), each
    up to TARGET; extra(...) adds the heavy job's fields and arguments"""
    cur, cs, sc, ss = [], 0.0, [], 0.0
    def flush_l():
        nonlocal cur, cs
        if cur: pk.append(dict(extra(kind_light, cur[0], cur[-1] + 1, None), pred_s=round(cs, 1))); cur, cs = [], 0.0
    def flush_s():
        nonlocal sc, ss
        if sc: pk.append(dict(extra(kind_split, sc[0], sc[-1] + 1, split_depth), pred_s=round(ss, 1))); sc, ss = [], 0.0
    prev = None
    for k, c in items:
        if prev is not None and k != prev + 1: flush_l(); flush_s()   # a gap (a heavy job): ranges must be contiguous
        prev = k
        if c > LIMIT:
            flush_l()
            if sc and ss + c > TARGET: flush_s()
            sc.append(k); ss += c
        else:
            flush_s()
            if cur and cs + c > TARGET: flush_l()
            cur.append(k); cs += c
    flush_l(); flush_s()
for C in ('436', '422'):
    mn, ml = PRICE[C]
    cost = lambda n, l: (mn * n + ml * l) / 1000.0
    d6 = {}
    for ln in open(RUN + 'fr%s_d6.txt' % C):
        k, p = ln.split(); d6[p] = int(k)
    nJ = len(d6)
    light = {}
    for ln in open(RUN + 'js%s_1.txt' % C):
        f = ln.split(); light[int(f[0])] = cost(int(f[1]), int(f[2]))
    heavy = sorted(set(range(nJ)) - set(light))
    def ex_light(kind, a, b, sd, C=C):
        return {'cap': C, 'kind': kind, 'a': a, 'b': b, 'args': [C, a, b] + (['--split', sd] if sd else [])}
    runs(sorted(light.items()), C, 'range', 'split', ex_light, 8)
    # heavy jobs: the emitter's own depth-10 frontiers (E1P/run/cap2/sub<C>/<J>.txt, mksubfr.py; a few nodes differ from the
    # native census's), each sub-job's cost from the native counts by prefix (a node the census did not have: 0, i.e. light;
    # if it is heavy, make_slice splits it)
    sub = {}
    for ln in open(RUN + 'js%s_2.txt' % C):
        f = ln.split(); sub[int(f[1])] = cost(int(f[2]), int(f[3]))
    pcost = {}
    for ln in open(RUN + 'subfr%s.txt' % C):
        k, p = ln.split(); pcost[p] = sub.get(int(k), 0.0)
    miss = 0
    for J in heavy:
        items = []
        for ln in open(RUN + 'sub%s/%d.txt' % (C, J)):
            t, p = ln.split()
            c = pcost.get(p)
            if c is None: miss += 1; c = 0.0
            items.append((int(t), c))
        def ex_heavy(kind, a, b, sd, C=C, J=J):
            return {'cap': C, 'kind': kind, 'job': J, 'a': a, 'b': b, 'args': [C, a, b, '--heavy', J] + (['--split', sd] if sd else [])}
        runs(items, C, 'heavy-sub', 'heavy-split', ex_heavy, 12)
        heavy_rows.append({'cap': C, 'job': J, 'subjobs': len(items), 'pred_s': round(sum(c for _, c in items), 1)})
    print('c%s: %d heavy jobs, %d sub-jobs not in the census (costed 0)' % (C, len(heavy), miss))
for i, p in enumerate(pk): p['id'] = 'w1_%05d' % i; p['pred_gb_max'] = 5.0
with open(out, 'w') as f:
    for p in pk: f.write(json.dumps(p) + '\n')
with open(out.replace('.jsonl', '') + '_heavy.jsonl', 'w') as f:
    for h in heavy_rows: f.write(json.dumps(h) + '\n')
from collections import defaultdict
st = defaultdict(lambda: [0, 0.0, 0.0])
for p in pk: s = st[(p['cap'], p['kind'])]; s[0] += 1; s[1] += p['pred_s']; s[2] = max(s[2], p['pred_s'])
for k in sorted(st): print('%s %-11s %6d packages, %9.0f vCPU-h predicted, max %.1f vCPU-h' % (k[0], k[1], st[k][0], st[k][1] / 3600, st[k][2] / 3600))
print('total %d packages, %.0f vCPU-h; heavy jobs %d' % (len(pk), sum(p['pred_s'] for p in pk) / 3600, len(heavy_rows)))
