#!/usr/bin/env python3
"""mkcut_pt.py COUNTDIR OUT.jsonl [TARGET_S]: the point tier's package cut list from a budgeted count pass (COUNTDIR: st.txt
"ix nodes leaves sec" of the jobs that finished under the budget; heavy.txt: the prefixes of the jobs over it, mapped to their
indices through the root-level frontier fr_Rptc.txt).
  range  light point jobs [a, b), cut at TARGET_S (default 5400 s) and at every heavy job: emitpkg.sh ptc a b OUT
  split  one heavy job (over the count pass's budget): split at depth 6 directly, recursively below: emitpkg.sh ptc k k+1 OUT
         --split 6; its pred_s is the budget's lower bound (the count pass stopped it)
Kernel price: 2.8 ms per st-node (the first point modules) and 20 ms per leaf (a guess; leaves are about 1% of the point tree's
st-nodes)."""
import sys, json
import os
R22 = os.environ.get('R22_ROOT', '.')   # the development layout's root (package mode does not use it)
HPT = R22 + '/hpt/'
cd, out = sys.argv[1], sys.argv[2]; TARGET = float(sys.argv[3]) if len(sys.argv) > 3 else 5400.0
fr = [ln.split()[1] for ln in open(HPT + 'data/fr_Rptc.txt')]; ix = {p: k for k, p in enumerate(fr)}
cost = {}
for ln in open(cd + '/st.txt'):
    f = ln.split()
    if len(f) >= 3: cost[int(f[0])] = (2.8 * int(f[1]) + 20.0 * int(f[2])) / 1000.0
heavy = sorted(ix[ln.strip()] for ln in open(cd + '/heavy.txt') if ln.strip())
budget_s = 2.8 * 200000 / 1000.0
missing = [k for k in range(len(fr)) if k not in cost and k not in set(heavy)]
assert not missing, 'jobs neither counted nor heavy: %d (first %s); is the count pass complete?' % (len(missing), missing[:5])
pk = []; cur, cs = [], 0.0
def flush():
    global cur, cs
    if cur: pk.append({'cap': 'ptc', 'kind': 'range', 'a': cur[0], 'b': cur[-1] + 1, 'pred_s': round(cs, 1), 'args': ['ptc', cur[0], cur[-1] + 1]})
    cur, cs = [], 0.0
hs = set(heavy)
for k in range(len(fr)):
    if k in hs:
        flush(); pk.append({'cap': 'ptc', 'kind': 'split', 'a': k, 'b': k + 1, 'pred_s_min': round(budget_s, 1), 'pred_s': None,
                            'args': ['ptc', k, k + 1, '--split', 6]}); continue
    c = cost[k]
    if cur and cs + c > TARGET: flush()
    cur.append(k); cs += c
flush()
for i, p in enumerate(pk): p['id'] = 'pt_%04d' % i; p['pred_gb_max'] = 5.0
with open(out, 'w') as f:
    for p in pk: f.write(json.dumps(p) + '\n')
nr = sum(1 for p in pk if p['kind'] == 'range')
print('%d packages: %d light ranges (%.1f vCPU-h), %d heavy jobs split directly (each over %.0f s of kernel)' % (
    len(pk), nr, sum(p['pred_s'] for p in pk if p['kind'] == 'range') / 3600, len(heavy), budget_s))
