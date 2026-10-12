#!/usr/bin/env python3
"""giants.py [PAR]: the class tier's giant root jobs (predicted over 3e5 s, rootjobs.tsv) split for packaging: per giant one DUMPONLY run
at depth D (9 for predicted over 1e6 s, else 7; kjlib.split_level: sub-job frontier fr.txt and top trace/top.bin from the same run)
and one search-only count pass over all its sub-jobs (kcgen.count_pass, budget 5e7 st-nodes), into giants/h<c>_<J>/.
PAR giants at a time (default 4, 16 threads each)."""
import sys, os, json
sys.path.insert(0, os.environ['KC_PY'])   # kcagg_v3/py (kcgen.py)
import kcgen
from concurrent.futures import ThreadPoolExecutor
K = kcgen.K
I = os.environ.get('KC_INPUTS', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'inputs', 'classes'))
G = os.path.join(I, 'giants') + '/'
PAR = int(sys.argv[1]) if len(sys.argv) > 1 else 4
K.load_class_contexts(); K.set_bsb_par(PAR)
rows = [l.split('\t') for l in open(os.path.join(I, 'rootjobs.tsv'))]
gi = [(r[0], int(r[1]), float(r[4])) for r in rows if float(r[4]) > 3e5]
gi.sort(key=lambda x: -x[2])
def one(g):
    c, J, p = g; ctx = 'h' + c; K.set_format(ctx)
    pre = [l.split()[1] for l in open(K.ipf(K.EMIT[ctx]['frontier'])) if l.strip()][J]
    D = 9 if p > 1e6 else 7
    rd = G + 'h%s_%d' % (c, J)
    K.split_level(ctx, pre, D, rd)
    fr, cnt, hv = kcgen.count_pass(ctx, rd, 50000000, 16)
    json.dump({'class': c, 'job': J, 'prefix': pre, 'depth': D, 'pred_s': p, 'subjobs': len(fr), 'over_budget': hv,
               'counts': {str(k): v for k, v in cnt.items()}}, open(rd + '/giant.json', 'w'))
    print('h%s/%d: depth %d, %d sub-jobs, %d over the count budget, %d leaves counted' % (c, J, D, len(fr), len(hv), sum(v[1] for v in cnt.values())), flush=True)
with ThreadPoolExecutor(PAR) as ex: list(ex.map(one, gi))
print('done', len(gi))
