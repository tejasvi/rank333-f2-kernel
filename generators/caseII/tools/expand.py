#!/usr/bin/env python3
"""p0x/expand.py JOBS T AVG PAR: case-II phase-0 extension. Every job of JOBS (py/mkjobscc.py's table) above T estimated nodes is
expanded like a phase-0 batch: prof7R3k14c with FLAGS_CCW of runs/xqcc/recipe_cc.txt (recipecheck must pass; its output in
recipecheck.txt) and `--pctop F pfile --pcert seg_x_<batch>_<idx>.r3 --dumpfrontier dump_x_<batch>_<idx>.txt --threads 1`, where
pfile is the job's prefix and F = depth + 2, deepened by one level (at most depth + 4) while the job's estimate over its frontier
count exceeds AVG. PAR runs at once, absolute nice 10, RLIMIT_AS 16 GiB each; a free-space guard stops new runs below 20 GB free.
Writes expand.tsv: batch idx depth est F frontier pcert_bytes seconds, and SHA256SUMS.txt over the kept pcerts and dumps."""
import sys, os, subprocess, time, threading, shutil
from concurrent.futures import ThreadPoolExecutor
R = os.environ.get('KINDS_R22', '.') + ''; K = R + '/lean/kinds'; O = K + '/runs/p0x'; BIN = R + '/lean/rerun/r3/prof7R3k14c'
jobs_f, T, AVG, PAR = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
rc = subprocess.run(['python3', K + '/py/recipecheck.py', K + '/runs/xqcc/recipe_cc.txt', 'FLAGS_CCW'], capture_output=True, text=True)
open(O + '/recipecheck.txt', 'w').write(rc.stdout + rc.stderr)
if rc.returncode: sys.exit('recipecheck failed: ' + (rc.stdout + rc.stderr)[-500:])
FL = [l.split(None, 1)[1].split() for l in open(K + '/runs/xqcc/recipe_cc.txt') if l.startswith('FLAGS_CCW ')][0]
NI = max(0, 10 - os.nice(0))
J = [l.split() for l in open(jobs_f) if l.strip()]
todo = [(a[0], a[1], int(a[2]), int(a[3]), a[4:]) for a in J if int(a[3]) > T]
lock = threading.Lock(); out = open(O + '/expand.tsv', 'a')
def one(j):
    b, ix, d, est, pre = j; n = 'x_%s_%s' % (b, ix); pf = '%s/pfile_%s.txt' % (O, n)
    open(pf, 'w').write('0 ' + ' '.join(pre) + '\n')
    for F in (d + 2, d + 3, d + 4):
        while shutil.disk_usage(O).free < 20e9: time.sleep(30)
        seg, dump, log = '%s/seg_%s.r3' % (O, n), '%s/dump_%s.txt' % (O, n), '%s/log_%s.txt' % (O, n)
        for f in (seg, dump):   # prof7R3 writes one pcert per launch: a deeper rerun starts from empty files
            if os.path.exists(f): os.remove(f)
        t0 = time.time()
        with open(log, 'w') as lg:
            r = subprocess.run(['prlimit', '--as=17179869184', 'nice', '-n', str(NI), BIN] + FL + ['--pctop', str(F), pf, '--pcert', seg,
                                '--dumpfrontier', dump, '--threads', '1'], stdout=lg, stderr=subprocess.STDOUT)
        dt = time.time() - t0
        if r.returncode: raise SystemExit('expand: %s F=%d exit %d' % (n, F, r.returncode))
        cnt = sum(1 for l in open(dump) if l.strip())
        if cnt == 0 or est / cnt <= AVG or F == d + 4: break
    with lock:
        out.write('%s\t%s\t%d\t%d\t%d\t%d\t%d\t%.1f\n' % (b, ix, d, est, F, cnt, os.path.getsize(seg), dt)); out.flush()
    return n
done = set()
if os.path.exists(O + '/expand.tsv'):
    for l in open(O + '/expand.tsv'):
        a = l.split('\t')
        if len(a) >= 8: done.add((a[0], a[1]))
todo = [j for j in todo if (j[0], j[1]) not in done]
print('expand: %d jobs to expand (%d done before)' % (len(todo), len(done)), flush=True)
with ThreadPoolExecutor(PAR) as ex: names = list(ex.map(one, sorted(todo, key=lambda j: -j[3])))
out.close()
subprocess.run('cd %s && sha256sum seg_x_*.r3 dump_x_*.txt > SHA256SUMS.txt' % O, shell=True, check=True)
print('expand: done', flush=True)
