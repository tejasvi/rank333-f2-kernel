#!/usr/bin/env python3
"""mkinst.py --kII KEY [--ext CLASS ...] [--noext CAP ...] [--out FILE]: the final instance R22K/Final.lean (the final assembly).

`R22K.Final.rank_ge_23 : Top.RankGe23` is `R22K.FinalAll.rank_ge_23_of` applied to the published root theorems:
  G2.Crown303.crown, G2.Crown321.crown (lean/cc/g2);
  per raise class c: KC.h<c>.EXT, KC.h<c>.classLB (module KC.h<c>_Class), and NDX.h<c>.x<c> (module NDX.h<c>.Top) for the classes
    given with --ext, else R22K.FinalAll.x_nil (KC.h<c>.EXT is []);
  KJ.aggptc.point (KJ.aggptc_Point); R22B.GramCrown.* (port);
  per cap C in 436, 422: KJ.agg<C>.Root.EXT / .root (KJ.agg<C>_Root, `#e1groot`), PLE.c<C>.Ext.hext_of and PLE.c<C>.Sub.sub
    (the EXT top, mkexttop.py v4 --order KJ.agg<C>.Root.EXT --root-module KJ.agg<C>_Root: all<C> := PLE.c<C>.Ext.EXT, a tree
    of appends whose flattening is the root's list, same order, duplicates kept; `Sub.sub : ∀ pl ∈ KJ.agg<C>.Root.EXT, pl ∈
    PLE.c<C>.Ext.EXT`, the kernel's List.beq over both, 64 s / 17 GB at 300k entries); with --subdefeq C the subset is `fun _ h => h`
    (a v3 EXT top whose ALL is the root's list as a literal: fine at 50k entries, maximum recursion depth in the elaborator at 300k);
    with --subdecide C it is `decide +kernel` (an EXT top whose ALL is not the root's list); with --noext C (the cap has
    no external leaf: the root is stated over plain IP.C and has no EXT list, and there is no EXT top) ext = ALL = [];
  KM2.Top.segs with the case-II root key --kII (`kII ∈ keys`, root (1, 0) and lo 0 by `decide +kernel`); KMIA.Top.vI, KMJJ.Top.vI.
Then the corollaries R22B.Cor.* through R22K.Cor.  KMod form: each public theorem is a private theorem published by `#k1top` (KPUB,
KAX, KAXSUM, KAXP), so `kmod_audit.py --root R22K.Final` walks it.  Nothing is decided here that the kernel does not check.
`app_lines` is also used by mkinst_smoke.py (the same text over mock producers)."""
import argparse, os
CL = ['420', '450', '451', '454', '455', '456', '458', '460', '463', '464', '465', '469', '470', '471', '472', '473', '475', '476',
      '485', '487', '490']

def app_lines(kII, ext=(), noext=(), rn=lambda s: s, subdecide=(), subdefeq=()):
    """the application of R22K.FinalAll.rank_ge_23_of (lines); `rn` renames every producer constant (identity: the real names)"""
    ext = set(ext); noext = set(noext); subdecide = set(subdecide); subdefeq = set(subdefeq)
    assert ext <= set(CL), ext - set(CL)
    assert noext <= {'436', '422'} and subdecide <= {'436', '422'} and subdefeq <= {'436', '422'}, (noext, subdecide, subdefeq)
    assert not (noext & subdecide) and not (noext & subdefeq) and not (subdecide & subdefeq), (noext, subdecide, subdefeq)
    L = ['  R22K.FinalAll.rank_ge_23_of %s %s' % (rn('G2.Crown303.crown'), rn('G2.Crown321.crown'))]
    for c in CL:
        x = rn('NDX.h%s.x%s' % (c, c)) if c in ext else 'R22K.FinalAll.x_nil'
        L.append('    %s %s %s' % (rn('KC.h%s.EXT' % c), rn('KC.h%s.classLB' % c), x))
    L.append('    ' + rn('KJ.aggptc.point'))
    L.append('    ' + ' '.join(rn('R22B.GramCrown.' + g) for g in ('g175', 'g1903', 'g1822', 'g1741', 'g1732', 'g1813')))
    L.append('    ' + ' '.join(rn('R22B.GramCrown.' + g) for g in ('oc0', 'oc1', 'oc2')))
    for C in ('436', '422'):
        if C in noext:
            L.append('    [] %s [] (fun _ h pl hpl => absurd (h pl hpl) List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)'
                     % rn('KJ.agg%s.Root.root' % C))
        else:
            sub = '(by decide +kernel)' if C in subdecide else '(fun _ h => h)' if C in subdefeq else rn('PLE.c%s.Sub.sub' % C)
            L.append('    %s %s _ %s %s' % (rn('KJ.agg%s.Root.EXT' % C), rn('KJ.agg%s.Root.root' % C), rn('PLE.c%s.Ext.hext_of' % C), sub))
    L.append('    _ %s %s (by decide +kernel) (by decide +kernel) (by decide +kernel)' % (rn('KM2.Top.segs'), kII))
    L.append('    %s %s' % (rn('KMIA.Top.vI'), rn('KMJJ.Top.vI')))
    return L

def imports(ext=(), noext=(), subold=()):
    m = ['R22K.FinalAll', 'R22K.Cor', 'R22B.GramCrown', 'G2.Crown303', 'G2.Crown321', 'KJ.aggptc_Point', 'KM2.Top', 'KMIA.Top', 'KMJJ.Top']
    for C in ('436', '422'):
        m.append('KJ.agg%s_Root' % C)
        if C not in noext: m.append('PLE.c%s.Ext' % C)
        if C not in noext and C not in subold: m.append('PLE.c%s.Sub' % C)
    m += ['KC.h%s_Class' % c for c in CL] + ['NDX.h%s.Top' % c for c in CL if c in set(ext)]
    return m

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--kII', required=True, help='the key of the case-II root ((1, 0), lo 0) in KM2.Top.segs\'s key list')
    ap.add_argument('--ext', nargs='*', default=[], help='raise classes with external leaves (they have NDX.h<c>.x<c>)')
    ap.add_argument('--noext', nargs='*', default=[], help='caps (436, 422) without any external leaf')
    ap.add_argument('--subdecide', nargs='*', default=[], help='caps whose EXT ⊆ ALL is decided (ALL not the root list)')
    ap.add_argument('--subdefeq', nargs='*', default=[], help='caps whose EXT ⊆ ALL is `fun _ h => h` (a v3 EXT top: ALL the root list '
                    'as a literal; the elaborator fails on it at ~300k entries: maximum recursion depth)')
    ap.add_argument('--out', default=os.path.join(os.environ.get('FINAL_DIR', os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), 'src/R22K/Final.lean'))
    a = ap.parse_args()
    L = ['module', 'public import R22Port.U_d41d8cd98f00'] + ['public import ' + m for m in imports(a.ext, a.noext, set(a.subdecide) | set(a.subdefeq))] + ['meta import KMod.Audit',
        '/-! # R22K.Final: the kernel-only final theorem (generated by s443/ftop/py/mkinst.py; classes with external leaves: %s; caps without: %s; '
        'caps with a decided subset: %s)' % (' '.join(sorted(a.ext)) or 'none', ' '.join(sorted(a.noext)) or 'none', ' '.join(sorted(a.subdecide)) or 'none'),
        '',
        'KMod form: each public theorem is a private theorem published by `#k1top` (KPUB, KAX, KAXSUM, KAXP lines). -/',
        'set_option Elab.async false', '@[expose] public section', 'set_option maxHeartbeats 0', 'set_option maxRecDepth 100000',
        'open FullTable FullTable.WangLadder RootSound Matrix', 'namespace R22K.Final', '',
        '/-- **The theorem.** Every decomposition of the 3x3 matrix multiplication tensor over F2 into `n` rank-one terms has `n ≥ 23`. -/',
        'private theorem main : Top.RankGe23 :='] + app_lines(a.kII, a.ext, a.noext, subdecide=a.subdecide, subdefeq=a.subdefeq) + [
        '#k1top R22K.Final.rank_ge_23 [main]', '',
        '/-- with Laderman\'s decomposition: the F2-rank is exactly 23 -/',
        'private theorem rankEq23 :',
        '    (∃ (a b c : Fin 23 → M3), IsDecomp a b c) ∧ ∀ (n : ℕ) (a b c : Fin n → M3), IsDecomp a b c → 23 ≤ n :=',
        '  R22K.Cor.rank_eq_23 R22K.Final.rank_ge_23',
        '#k1top R22K.Final.rank_eq_23 [rankEq23]',
        '/-- the matrix-product convention (`C = AB`) -/',
        'private theorem mmEquiv : ∀ (n : ℕ) (a b c : Fin n → M3), R22B.Cor.IsDecompMM a b c → 23 ≤ n := R22K.Cor.mm_equiv R22K.Final.rank_ge_23',
        '#k1top R22K.Final.mm_equiv [mmEquiv]',
        '/-- Rudich-Rousseau\'s table statement at 23 for element 495 -/',
        'private theorem table23 : TableAtLeast ((table[495]!).map mask_matrix) 23 := R22K.Cor.table_23 R22K.Final.rank_ge_23',
        '#k1top R22K.Final.table_23 [table23]',
        '/-- Rudich-Rousseau\'s crown at 23 -/',
        'private theorem recursive23 : RecursiveAlgorithmMultiplicationsAtLeast 23 := R22K.Cor.recursive_23 R22K.Final.rank_ge_23',
        '#k1top R22K.Final.recursive_23 [recursive23]', '',
        'end R22K.Final', '']
    os.makedirs(os.path.dirname(a.out), exist_ok=True)
    open(a.out, 'w').write('\n'.join(L))
    print('wrote', a.out)

if __name__ == '__main__':
    main()
