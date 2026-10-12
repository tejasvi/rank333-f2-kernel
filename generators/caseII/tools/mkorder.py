#!/usr/bin/env python3
"""order/mkorder.py [ALPHA]: an order for the not-done KM2X packages (caseII/v2x), largest expected first.
A giant's estimate (expand.tsv; the native run1 count x 0.95, within about 1% on whole jobs) is shared among its sub-jobs in proportion
to (children at F+1)^ALPHA from p0x/probe.tsv (default ALPHA 1); a package's expectation is the sum over its sub-jobs. Done packages
(order/done_ids.txt) are left out; their records (done/summary.json) check the signal: rank correlation of the expectation, and of
the even split, with the measured records. Writes order/KM2X_order.txt (id, expected nodes) and prints the check."""
import os
import sys, json, collections
K = os.environ.get('KINDS_R22', '.') + '/lean/kinds/runs/'
A = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
X = [l.split() for l in open(K + 'caseII/jobs_x.txt') if l.strip()]
ch = {}
for l in open(K + 'p0x/probe.tsv'):
    a = l.split()
    if len(a) == 2: ch[int(a[0])] = int(a[1])
E = {}
for l in open(K + 'p0x/expand.tsv'):
    a = l.rstrip('\n').split('\t'); E['x_%s_%s' % (a[0], a[1])] = int(a[3])
byp = collections.defaultdict(list)
for n, a in enumerate(X, 1): byp[a[0]].append(n)
est = {}; probed = 0
for p, ns in byp.items():
    if all(n in ch for n in ns):
        probed += 1; w = [ch[n] ** A for n in ns]; s = sum(w)
        for n, x in zip(ns, w): est[n] = E[p] * (x / s if s else 1.0 / len(ns))
    else:
        for n in ns: est[n] = E[p] / len(ns)
P = [json.loads(l) for l in open(K + 'caseII/v2x/PACKAGES.jsonl')]
def pest(x): a, b = x['lines']; return sum(est[n] for n in range(a, b + 1))
done = {}
for r in json.load(open(K + 'caseII/done/summary.json')):
    if r['fam'] == 'KM2X': done[r['id']] = r['recs']
def rank(v):
    o = sorted(range(len(v)), key=lambda i: v[i]); r = [0] * len(v)
    for i, j in enumerate(o): r[j] = i
    return r
def spear(a, b):
    ra, rb = rank(a), rank(b); n = len(a); ma = sum(ra) / n; mb = sum(rb) / n
    num = sum((x - ma) * (y - mb) for x, y in zip(ra, rb)); den = (sum((x - ma) ** 2 for x in ra) * sum((y - mb) ** 2 for y in rb)) ** 0.5
    return num / den if den else 0.0
dp = [x for x in P if x['id'] in done]
if dp:
    act = [done[x['id']] for x in dp]
    print('check on %d done KM2X packages: rank correlation with records: probe-weighted %.3f, even split %.3f' % (
        len(dp), spear([pest(x) for x in dp], act), spear([x['est_nodes'] for x in dp], act)))
todo = sorted((x for x in P if x['id'] not in done), key=lambda x: -pest(x))
open(K + 'caseII/order/KM2X_order.txt', 'w').write(''.join('%s\t%.0f\n' % (x['id'], pest(x)) for x in todo))
tot = sum(pest(x) for x in todo)
cum = 0; marks = {}
for i, x in enumerate(todo, 1):
    cum += pest(x)
    for f in (0.5, 0.8, 0.95):
        if f not in marks and cum >= f * tot: marks[f] = i
print('%d giants probed of %d; %d not-done KM2X packages, expected %.3g nodes; top package %.3g; half the nodes in the first %d packages, 80%% in %d, 95%% in %d' % (
    probed, len(byp), len(todo), tot, pest(todo[0]), marks.get(0.5), marks.get(0.8), marks.get(0.95)))
