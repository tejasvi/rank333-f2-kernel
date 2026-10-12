"""regiant.py c/J/D ...: re-split the counted giant h<c>_<J> at depth D (DUMPONLY run and count pass, as giants.py)."""
import sys, os, json, shutil
sys.path.insert(0, os.environ['KC_PY'])   # kcagg_v3/py (kcgen.py)
import kcgen
from concurrent.futures import ThreadPoolExecutor
K = kcgen.K; K.load_class_contexts(); K.set_bsb_par(5)
I = os.environ.get('KC_INPUTS', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'inputs', 'classes'))
G = os.path.join(I, 'giants') + '/'
todo = [(a.split('/')[0], int(a.split('/')[1]), int(a.split('/')[2])) for a in sys.argv[1:]]   # c/J/D
def one(t):
    c, J, D = t; ctx = 'h' + c; K.set_format(ctx)
    g0 = json.load(open(G + 'h%s_%d/giant.json' % (c, J)))
    rd = G + 'h%s_%d' % (c, J); shutil.rmtree(rd)
    K.split_level(ctx, g0['prefix'], D, rd)
    fr, cnt, hv = kcgen.count_pass(ctx, rd, 50000000, 16)
    json.dump({'class': c, 'job': J, 'prefix': g0['prefix'], 'depth': D, 'pred_s': g0['pred_s'], 'subjobs': len(fr), 'over_budget': hv,
               'counts': {str(k): v for k, v in cnt.items()}}, open(rd + '/giant.json', 'w'))
    print('h%s/%d: depth %d, %d sub-jobs, %d over the count budget' % (c, J, D, len(fr), len(hv)), flush=True)
with ThreadPoolExecutor(5) as ex: list(ex.map(one, todo))
