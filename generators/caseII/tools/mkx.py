#!/usr/bin/env python3
"""p0x/mkx.py JOBS OUT: the sub-job table of the expanded jobs (expand.tsv, dump_x_<batch>_<idx>.txt) for py/mkpkgcc.py.
One line per frontier entry of an expanded job, in the order of JOBS and then of the dump: `x_<batch>_<idx> <dump index> <F> <est>
<labels>`, est = the parent's estimate over its frontier count (at least 1). Checks: every expanded job of expand.tsv is a job of JOBS
above the threshold, each dump prefix extends its parent's prefix and has length F, and no prefix occurs twice."""
import os
import sys
O = os.environ.get('KINDS_R22', '.') + '/lean/kinds/runs/p0x'
jobs_f, out = sys.argv[1], sys.argv[2]
J = {(a[0], a[1]): a for a in (l.split() for l in open(jobs_f)) if a}
order = [tuple(a[:2]) for a in (l.split() for l in open(jobs_f)) if a]
E = {}
for l in open(O + '/expand.tsv'):
    a = l.rstrip('\n').split('\t')
    if len(a) >= 8: E[(a[0], a[1])] = (int(a[2]), int(a[3]), int(a[4]), int(a[5]))
lines = []; seen = set(); nz = 0
for key in order:
    if key not in E: continue
    d, est, F, cnt = E[key]; par = J[key]; pre = par[4:]
    assert int(par[3]) == est and len(pre) == d, key
    n = 'x_%s_%s' % key; dump = [x.split() for x in open('%s/dump_%s.txt' % (O, n)) if x.strip()]
    assert len(dump) == cnt, (key, len(dump), cnt)
    if cnt == 0: nz += 1; continue
    e = max(1, round(est / cnt))
    for x in dump:
        lab = x[1:]
        assert len(lab) == F and lab[:d] == pre, (key, x[:3])
        t = tuple(lab); assert t not in seen, (key, x[:3]); seen.add(t)
        lines.append('%s %s %d %d %s\n' % (n, x[0], F, e, ' '.join(lab)))
open(out, 'w').write(''.join(lines))
print('%d expanded jobs, %d with an empty frontier; %d sub-jobs, est %.3g nodes' % (len(E), nz, len(lines), sum(int(l.split()[3]) for l in lines)))
