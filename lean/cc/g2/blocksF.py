#!/usr/bin/env python3
"""blocksF.py CLASS: module-form G2 block modules of the E1 chain C<CLASS>X through the O(log n) lookups of G2.C<CLASS>X_F
(G2.Asm2), written to mod/src/G2/C<CLASS>X_B<j>.lean; the manifest's block lines get the dependency on G2.C<CLASS>X_F.

Module j covers blocks [ga, ga + gm) (at most 48 blocks and 2 Mbit of literals); the chain module G2.C<CLASS>X is rewritten for these
ranges with the E1 chain's statements (okAll, len, okGAll, okGlue, no_start):
  okB<k>  : E1.block C sl UB UBR (F k) = true                              (one declaration per block, no list walk)
  okBF<j> : G2A.blkChkF C sl UB UBR F ga gm = true                         (from the okB, no evaluation)
  okM<j>  : E1S.blkChk C sl UB UBR lits ga gm = true                       (G2A.blkChk_of_F with hF)
  okGF<j> : G2A.glueChkRF F FW N ga gm = true                              (decide +kernel, lookups through F and FW)
  okG<j>  : E1S.glueChkR lits W ga gm = true                               (G2A.glueChkR_of_F with lenT, hF, hFW)"""
import sys, re, json
c = int(sys.argv[1])
import os
L2 = os.environ['E1ROOT'].rstrip('/') + '/'
G = os.path.dirname(os.path.abspath(__file__)) + '/'
name, ipn = 'C%dX' % c, 'e%d' % c
src = open(L2 + 'E1/%s.lean' % name).read()
N = int(re.search(r'theorem len : lits.length = (\d+) := by decide', src).group(1))
# module ranges: consecutive blocks, at most MAXB blocks and MAXBITS literal bits per module (the chain module below is written
# for these ranges; 11-block modules spend most of their time importing)
import struct
MAXB, MAXBITS = 48, 2000000
raw = open(G + 'data/%s.bin' % name, 'rb').read()
cnt = struct.unpack('<I', raw[:4])[0]; assert cnt == N
bits = []; off = 4
for i in range(N):
    nb = struct.unpack('<I', raw[off:off + 4])[0]; bits.append(8 * nb); off += 4 + nb
ranges = []; a = 0
while a < N:
    m = 0; tot = 0
    while a + m < N and (m == 0 or (m < MAXB and tot + bits[a + m] <= MAXBITS)): tot += bits[a + m]; m += 1
    ranges.append((a, m)); a += m
ctx = 'E1.IP_%s.C E1.SL_%s.entry E1.IP_%s.UB E1.IP_%s.UBR' % (ipn, ipn, ipn, ipn)
for j, (ga, gm) in enumerate(ranges):
    L = ['module', 'public import R22Port.U_d41d8cd98f00', 'public import G2.%s_F' % name, '@[expose] public section',
         'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'namespace G2.%s' % name, 'open E1S']
    for k in range(ga, ga + gm):
        L.append('theorem okB%d : E1.block %s (F %d) = true := by decide +kernel' % (k, ctx, k))
    L.append('theorem okBF%d : G2A.blkChkF %s F %d %d = true := by' % (j, ctx, ga, gm))
    L.append('  have h0 := G2A.blkChkF_zero %s F %d' % (ctx, ga))
    for t in range(gm):
        L.append('  have h%d := G2A.blkChkF_succ_of _ _ _ _ F %d %d h%d okB%d' % (t + 1, ga, t, t, ga + t))
    L.append('  exact h%d' % gm)
    L.append('theorem okM%d : blkChk %s lits %d %d = true :=' % (j, ctx, ga, gm))
    L.append('  G2A.blkChk_of_F _ _ _ _ lits F %d hF %d %d (by decide) okBF%d' % (N, ga, gm, j))
    L.append('theorem okGF%d : G2A.glueChkRF F FW %d %d %d = true := by decide +kernel' % (j, N, ga, gm))
    L.append('theorem okG%d : glueChkR lits W %d %d = true :=' % (j, ga, gm))
    L.append('  G2A.glueChkR_of_F lits W F FW %d lenT hF hFW %d %d (by decide) okGF%d' % (N, ga, gm, j))
    L += ['end G2.%s' % name, '']
    open(G + 'mod/src/G2/%s_B%d.lean' % (name, j), 'w').write('\n'.join(L))
import glob, os
for f in glob.glob(G + 'mod/src/G2/%s_B*.lean' % name):
    if int(re.search(r'_B(\d+)\.lean$', f).group(1)) >= len(ranges): os.remove(f)
blk = 'blkChk C E1.SL_%s.entry UB UBR lits' % ipn
L = ['module', 'public import R22Port.U_d41d8cd98f00'] + ['public import G2.%s_B%d' % (name, j) for j in range(len(ranges))] + \
    ['public import E1.OK_%s' % ipn, '@[expose] public section', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
     '/-! # The chain `%s`: every block accepted, every header record glued (witness table `W`), so no `x` satisfying' % name,
     'the global facts completes the chain\'s first start state (leaf2\'s E1/%s.lean, G2 block ranges) -/' % name,
     'namespace G2.%s' % name, 'open E1S E1.IP_%s' % ipn, 'theorem okAll : %s 0 %d = true := by' % (blk, N),
     '  have h0 : %s 0 %d = true := okM0' % (blk, ranges[0][1])]
for t in range(1, len(ranges)):
    a, m = ranges[t]
    L.append('  have h%d : %s 0 %d = true := blkChk_join _ _ _ _ _ 0 %d %d h%d okM%d' % (t, blk, a + m, a, m, t - 1, t))
L += ['  exact h%d' % (len(ranges) - 1), 'theorem len : lits.length = %d := lenT.symm' % N,
      'theorem okGAll : glueChkR lits W 0 %d = true := by' % N, '  have g0 : glueChkR lits W 0 %d = true := okG0' % ranges[0][1]]
for t in range(1, len(ranges)):
    a, m = ranges[t]
    L.append('  have g%d : glueChkR lits W 0 %d = true := glueChkR_join _ _ 0 %d %d g%d okG%d' % (t, a + m, a, m, t - 1, t))
L += ['  exact g%d' % (len(ranges) - 1),
      'theorem okGlue : glueChk lits W = true := glueChkR_full _ _ (len ▸ okGAll)',
      '/-- no `x` with the global facts completes the start state of the chain\'s first block -/',
      'theorem no_start (x : ℕ → ℕ) (hg : Glob C x) (hsl : ∀ i < 2 ^ 15, SlotV x (E1.SL_%s.entry i))' % ipn,
      '    (hxub : ∀ l < 127, x l ≤ E1.fld UB l) (hx : ∃ l < 127, 0 < x l) :',
      '    ¬ StartOK x (fun l => E1.fld UB l) (lits.getD 0 0) :=',
      '  chain_sound C E1.SL_%s.entry UB UBR (fun l => E1.fld UB l) x hg hsl E1.OK_%s.UB_eq E1.OK_%s.UBR_eq (by decide +kernel)' % (ipn, ipn, ipn),
      '    hxub hx lits (blkChk_spec _ _ _ _ _ _ (len ▸ okAll)) (glueChk_spec _ _ okGlue) 0 (by rw [len]; decide)',
      'end G2.%s' % name, '']
open(G + 'mod/src/G2/%s.lean' % name, 'w').write('\n'.join(L))
mf = G + 'mod/manifest_c%d.jsonl' % c
man = [json.loads(l) for l in open(mf)]
names = set(m['module'] for m in man)
man = [m for m in man if m['kind'] != 'block']
k0 = next(i for i, m in enumerate(man) if m['kind'] == 'chain')
man[k0:k0] = [dict(module='G2.%s_B%d' % (name, j), src='src/G2/%s_B%d.lean' % (name, j), cwd='src', tier='g2', kind='block',
                   deps=['G2.%s_F' % name], pred_s=5.0 + 1.5 * m, pred_gb=8.0) for j, (a, m) in enumerate(ranges)]
for m in man:
    if m['kind'] == 'chain': m['deps'] = ['G2.%s_B%d' % (name, j) for j in range(len(ranges))]
if 'G2.%s_F' % name not in names:
    man.insert(3, dict(module='G2.%s_F' % name, src='src/G2/%s_F.lean' % name, cwd='src', tier='g2', kind='lookup',
                       deps=['G2.%s_N' % name], pred_s=400.0, pred_gb=12.0))
open(mf, 'w').write(''.join(json.dumps(x) + '\n' for x in man))
print(name, 'literals', N, 'block modules', len(ranges))
