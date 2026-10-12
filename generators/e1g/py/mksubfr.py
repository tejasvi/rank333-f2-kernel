#!/usr/bin/env python3
"""mksubfr.py CAP [P]: the depth-10 sub-job frontiers of a context cap's heavy depth-6 jobs as the emitter itself produces them
(lineenum9qe_ld5 --root PREFIX --frontier 10 --cert top, DUMPFRONTIER/DUMPONLY: no job is run), into E1P/run/cap2/sub<C>/<J>.txt
(local indices) and the top-chain traces into E1P/run/cap2/subtop<C>/<J>.bin.  The native census's depth-10 frontiers
(subfr<C>.txt) differ in a few nodes (job 47 of c436: 17,159 against 17,161), so the sub-job tables KH.S<C>_<J> and the
heavy-job tops use these.  P parallel runs (default 12)."""
import sys, os, subprocess, glob, shutil
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kjlib as K
cap = sys.argv[1]; C = cap[1:] if cap.startswith('c') else cap; cap = 'c' + C
P = int(sys.argv[2]) if len(sys.argv) > 2 else 12
E = K.EMIT[cap]; RUN = K.H + 'E1P/run/cap2/'
d6 = {}
for ln in open(K.ipf(E['frontier'])):
    k, p = ln.split(); d6[int(k)] = p
heavy = sorted(int(os.path.basename(f)[:-4]) for f in glob.glob(RUN + 'sub%s/*.txt' % C))
os.makedirs(RUN + 'subtop%s' % C, exist_ok=True)
ni = max(0, 10 - os.nice(0))
def one(J):
    wd = '/tmp/mksubfr_%s_%d' % (C, J); shutil.rmtree(wd, ignore_errors=True); os.makedirs(wd)
    cmd = ('cd %s && DUMPFRONTIER=fr.txt DUMPONLY=1 nice -n %d %s %s --order %s %s --threads 1 --root "%s" --frontier 10 --cert top '
           '--state st.txt --out /dev/null > run.log 2>&1' % (wd, ni, K.BIN['lineenum'], K.ipf(E['ip']), K.ipf(E['order']), K.emit_opts(cap), d6[J]))
    subprocess.run(cmd, shell=True, check=True)
    n = 0
    with open(RUN + 'sub%s/%d.txt' % (C, J), 'w') as f:
        for ln in open(wd + '/fr.txt'):
            k, p = ln.split(); assert int(k) == n; f.write('%d %s\n' % (n, p)); n += 1
    shutil.copy(glob.glob(wd + '/top_*_top.bin')[0], RUN + 'subtop%s/%d.bin' % (C, J))
    shutil.rmtree(wd)
    return J, n
with ThreadPoolExecutor(P) as ex:
    res = list(ex.map(one, heavy))
print('%d heavy jobs of %s: %d sub-jobs' % (len(res), cap, sum(n for _, n in res)))
