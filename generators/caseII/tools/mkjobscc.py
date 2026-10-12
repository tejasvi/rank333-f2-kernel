#!/usr/bin/env python3
"""mkjobscc.py OUT [CCDUMPDIR]: case-II job table on the CC route (table cc436_422) from phase 0.

- The native phase 1 (rerun/r3/p0/plan1/<batch>.jobs: indices into b10/dump_<batch>.txt, 150,707 job roots) is the job set wherever the
  CC phase 0 (runs/p0cc, FLAGS_CCW) dumped the same frontier: 59 of 61 batches, byte-identical DUMPs.
- In the two other batches the CC DUMP (CCDUMPDIR/dump_<batch>.txt, default runs/p0cc) decides: a CC entry is a job when its prefix is a
  native job of the batch or new on the CC table (not in the native DUMP: a node the native table killed). Native entries absent from the
  CC DUMP are dead above the frontier on the CC table (the CC top segment covers them) and are no jobs.
- Size: the native run's nodes (r22/xq/run1 state lines) x 0.95 (CC / native measured on 40 poolH jobs: 1.354M / 1.418M); new jobs 2,000.
Writes OUT: `batch idx depth est prefix…` per job (idx = the CC DUMP's index), and prints the totals."""
import sys, os, glob
out = sys.argv[1]; ccd = sys.argv[2] if len(sys.argv) > 2 else os.environ.get('KINDS_R22', '.') + '/lean/kinds/runs/p0cc'
P = os.environ.get('KINDS_R22', '.') + '/lean/rerun/r3/p0'; S = os.environ.get('KINDS_R22', '.') + '/xq/run1/gather/xq/'
batches = [l.split()[0] for l in open(P + '/b10n/batches.tsv') if l.strip()]
def dump(f): return [(int(a[0]), tuple(int(x) for x in a[1:])) for a in (l.split() for l in open(f)) if a]
rows = []; tot = 0; nnew = 0
for b in batches:
    jf = P + '/plan1/%s.jobs' % b
    if not os.path.exists(jf): continue
    nat = dump(P + '/b10/dump_%s.txt' % b); natp = dict(nat)
    jobs = [int(l) for l in open(jf) if l.strip()]
    size = {}
    sf = S + 'state_rerunH_%s_xq.txt' % b
    if os.path.exists(sf):
        for l in open(sf):
            a = l.split()
            if a: size[int(a[0])] = int(a[1])
    cf = os.path.join(ccd, 'dump_%s.txt' % b)
    if os.path.exists(cf) and open(cf, 'rb').read() != open(P + '/b10/dump_%s.txt' % b, 'rb').read():
        cc = dump(cf); jp = {natp[i]: i for i in jobs}; natset = set(natp.values())
        for i, pre in cc:
            if pre in jp: rows.append((b, i, len(pre), round(0.95 * size.get(jp[pre], 2000)), pre))
            elif pre not in natset: rows.append((b, i, len(pre), 2000, pre)); nnew += 1
    else:
        for i in jobs: rows.append((b, i, len(natp[i]), round(0.95 * size.get(i, 2000)), natp[i]))
with open(out, 'w') as f:
    for b, i, d, e, pre in rows: f.write('%s %d %d %d %s\n' % (b, i, d, e, ' '.join(map(str, pre)))); tot += e
print('%d jobs (%d new on the CC table) in %d batches, est %.3g CC nodes' % (len(rows), nnew, len(set(r[0] for r in rows)), tot))
