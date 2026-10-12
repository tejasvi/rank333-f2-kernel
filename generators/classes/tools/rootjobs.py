#!/usr/bin/env python3
"""rootjobs.py: per root job of the 21 classes: native st-nodes and leaves (craise_units.txt: per counted unit its class, root job, st-nodes and leaves),
and the predicted kernel s of the E1G layout: 0.5 ms per st-node + ms_leaf(c) per leaf, ms_leaf(c) = 1.6 x the class's leaf-weighted
BC7 price (a stratified sample of the units; 1.6 = h460's measured E1G layout over its BC7 price), floored at 6 ms.  Writes rootjobs.tsv."""
import collections, os, sys
I = os.environ.get('KC_INPUTS', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'inputs', 'classes'))
U = os.path.join(I, 'craise_units.txt')
TOOLS = os.environ['KC_TOOLS']   # the E1G emitter tools tree (ip/hcap/ana/roots_fixed.txt)
PRICE = {'485': 4.65, '487': 6.94, '490': 8.04, '454': 9.18, '470': 7.98, '473': 9.60, '476': 10.21, '465': 16.35, '455': 14.71, '456': 10.98,
         '471': 4.21, '475': 10.53, '458': 7.06, '464': 10.49, '472': 19.92, '450': 8.57, '451': 23.84, '469': 7.26, '463': 5.06, '420': 81.22, '460': 7.21}
roots = {l.split()[0]: int(l.split()[2]) for l in open(os.path.join(TOOLS, 'ip', 'hcap', 'ana', 'roots_fixed.txt')) if l.split() and not l.startswith('#')}
lv = collections.Counter(); nd = collections.Counter()
for l in open(U):
    g, c, node, fr, ix, nn, ll = l.split()
    k = int(node.split('_', 1)[1].split('.')[0]); lv[(c, k)] += int(ll); nd[(c, k)] += int(nn)
with open('rootjobs.tsv', 'w') as f:
    tot = collections.Counter()
    for c in sorted(PRICE):
        msl = max(6.0, 1.6 * PRICE[c])
        for k in range(roots[c]):
            p = (0.5 * nd[(c, k)] + msl * lv[(c, k)]) / 1000.0
            f.write('%s\t%d\t%d\t%d\t%.1f\n' % (c, k, nd[(c, k)], lv[(c, k)], p)); tot[c] += p
for c in sorted(tot, key=lambda c: -tot[c]): print(c, 'pred %.3e s = %.0f CPU-hours' % (tot[c], tot[c] / 3600))
print('tier pred %.3e s = %.0f CPU-hours' % (sum(tot.values()), sum(tot.values()) / 3600))
