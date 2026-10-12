#!/usr/bin/env python3
"""blocks.py CLASS: G2 block modules of the E1 chain C<CLASS>X, in the E1 route's form (enum/e1asm.py with CH = 1, converted by
enum/e1bconv.py to the recursor walk of E1/AsmN.lean), written to l2/E1/C<CLASS>X_B<j>.lean.

The module ranges are read back from the existing chain module $E1ROOT/E1/C<CLASS>X.lean (okAll joins `okM<j>` over blocks
[ga, ga + gm)), so the chain module, the witness table C<CLASS>X_W and the length module C<CLASS>X_N stay valid as they are.
Module j proves okB<k> for every block k in its range (one literal each), okG<j> (glue of its range) and okM<j> (the join)."""
import sys, re
c = int(sys.argv[1])
import os
L2 = os.environ['E1ROOT'].rstrip('/') + '/'
G = os.path.dirname(os.path.abspath(__file__)) + '/l2/'
name, ipn = 'C%dX' % c, 'e%d' % c
src = open(L2 + 'E1/%s.lean' % name).read()
N = int(re.search(r'theorem len : lits.length = (\d+) := by decide', src).group(1))
m0 = re.search(r'have h0 : blkChk C E1\.SL_%s\.entry UB UBR lits 0 (\d+) = true := okM0' % ipn, src)
ranges = [(0, int(m0.group(1)))]
for m in re.finditer(r'have h(\d+) : blkChk C E1\.SL_%s\.entry UB UBR lits 0 (\d+) = true := blkChk_join _ _ _ _ _ 0 (\d+) (\d+) h(\d+) okM(\d+)' % ipn, src):
    t, end, start, ln, tp, j = map(int, m.groups())
    assert t == j == tp + 1 == len(ranges) and start == ranges[-1][0] + ranges[-1][1] and end == start + ln, m.group(0)
    ranges.append((start, ln))
assert ranges[-1][0] + ranges[-1][1] == N, (ranges[-1], N)
blk = 'blkChk E1.IP_%s.C E1.SL_%s.entry E1.IP_%s.UB E1.IP_%s.UBR' % (ipn, ipn, ipn, ipn)
hdr = ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0']
for j, (ga, gm) in enumerate(ranges):
    body = []
    for k in range(ga, ga + gm):
        body += ['theorem okB%d : %s lits %d 1 = true := by' % (k, blk, k), '  rw [← blkChkN_eq]; decide +kernel']
    body += ['theorem okG%d : glueChkR lits W %d %d = true := by' % (j, ga, gm),
             '  rw [← glueChkRN_eq lits W %d %d lenT]; decide +kernel' % (N, ga)]
    body.append('theorem okM%d : %s lits %d %d = true := by' % (j, blk, ga, gm))
    body.append('  have h0 : %s lits %d 1 = true := okB%d' % (blk, ga, ga))
    for t in range(1, gm):
        body.append('  have h%d : %s lits %d %d = true := blkChk_join _ _ _ _ _ %d %d 1 h%d okB%d' % (t, blk, ga, t + 1, ga, t, t - 1, ga + t))
    body.append('  exact h%d' % (gm - 1))
    open(G + 'E1/%s_B%d.lean' % (name, j), 'w').write('\n'.join(['import E1.%s_N' % name] + hdr +
        ['namespace E1.%s' % name, 'open E1S'] + body + ['end E1.%s' % name, '']))
print(name, 'literals', N, 'block modules', len(ranges))
