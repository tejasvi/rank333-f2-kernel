#!/usr/bin/env python3
"""p0x/probe.py PAR: a size signal for the sub-jobs of caseII/jobs_x.txt. For each expanded job (expand.tsv, largest first) one
prof7R3k14c run with FLAGS_CCW and `--pctop F+1` over all of its sub-jobs (pfile = their prefixes) counts each sub-job's surviving
children one level down; the probe pcert is deleted at once. Appends probe.tsv: sub-job line (jobs_x.txt), children at F+1. PAR runs
at once, absolute nice 10, RLIMIT_AS 16 GiB; free-space guard 20 GB; resumable (parents already in probe_done.txt are skipped)."""
import sys, os, subprocess, threading, shutil, time, collections
from concurrent.futures import ThreadPoolExecutor
R = os.environ.get('KINDS_R22', '.') + ''; K = R + '/lean/kinds'; O = K + '/runs/p0x'; BIN = R + '/lean/rerun/r3/prof7R3k14c'
PAR = int(sys.argv[1])
FL = [l.split(None, 1)[1].split() for l in open(K + '/runs/xqcc/recipe_cc.txt') if l.startswith('FLAGS_CCW ')][0]
NI = max(0, 10 - os.nice(0))
X = [l.split() for l in open(K + '/runs/caseII/jobs_x.txt') if l.strip()]
byp = collections.OrderedDict()
for n, a in enumerate(X, 1): byp.setdefault(a[0], []).append(n)
E = {}
for l in open(O + '/expand.tsv'):
    a = l.rstrip('\n').split('\t'); E['x_%s_%s' % (a[0], a[1])] = int(a[3])
done = set(l.strip() for l in open(O + '/probe_done.txt')) if os.path.exists(O + '/probe_done.txt') else set()
todo = sorted((p for p in byp if p not in done), key=lambda p: -E[p])
lock = threading.Lock()
def one(p):
    ns = byp[p]; F = int(X[ns[0] - 1][2]); pf = '%s/probe/pf_%s.txt' % (O, p); seg = '%s/probe/seg_%s.r3' % (O, p); dump = '%s/probe/dump_%s.txt' % (O, p)
    open(pf, 'w').write(''.join('%d %s\n' % (i, ' '.join(X[n - 1][4:])) for i, n in enumerate(ns)))   # pctop wants indices 0, 1, ...
    for f in (seg, dump):
        if os.path.exists(f): os.remove(f)
    while shutil.disk_usage(O).free < 20e9: time.sleep(30)
    with open('%s/probe/log_%s.txt' % (O, p), 'w') as lg:
        r = subprocess.run(['prlimit', '--as=17179869184', 'nice', '-n', str(NI), BIN] + FL + ['--pctop', str(F + 1), pf, '--pcert', seg,
                            '--dumpfrontier', dump, '--threads', '1'], stdout=lg, stderr=subprocess.STDOUT)
    if r.returncode: return '%s exit %d' % (p, r.returncode)
    pre = {tuple(X[n - 1][4:]): n for n in ns}; c = collections.Counter()
    for l in open(dump):
        a = l.split()
        if a: c[pre[tuple(a[1:1 + F])]] += 1
    os.remove(seg); os.remove(dump); os.remove(pf)
    with lock:
        with open(O + '/probe.tsv', 'a') as o: o.write(''.join('%d\t%d\n' % (n, c[n]) for n in ns))
        with open(O + '/probe_done.txt', 'a') as o: o.write(p + '\n')
    return None
os.makedirs(O + '/probe', exist_ok=True)
print('probe: %d parents to probe' % len(todo), flush=True)
with ThreadPoolExecutor(PAR) as ex:
    for res in ex.map(one, todo):
        if res: print('probe: failed', res, flush=True)
print('probe: done', flush=True)
