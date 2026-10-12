module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.LoadItemR
public import KDK.ItemR2
public import KDK.LoadXB2
public meta import KB.LoadItemR
public meta import KDK.ItemR2
public meta import KDK.LoadXB2
/-! # KB.LoadItemR2: item batches with the X part's cheaper front end (`KD.itemXR2'`, packed trees)

`#kritemB2 I "dir" k0 k1`: as `#kritemB`, but each batch is checked by the kernel as `I.c<k> : KD.itemXR2' … I.m<k> … = true` on
packed records `I.m<k>`; then `I.n<k>` is the unpacked list (`List.map`, never evaluated) and `I.b<k> : KD.itemXR' … I.n<k> … = true`
is `KD.itemXR2'_imp` applied to `I.c<k>`.  `#kritemHead` and `#kritemEnd` are unchanged. -/
@[expose] public section
open Lean Elab Command L1Load KBLoad KBLoadR
namespace KBLoadR2

meta def mkTys2 : Tys :=
  let t2 := prodTy natTy natTy
  let t3 := prodTy natTy t2
  let t4 := prodTy natTy t3
  let t5 := prodTy natTy t4
  let xc := mkConst ``KD.XC2
  let ta3 := prodTy natTy lnatE
  let ta2 := prodTy natTy ta3
  let tAgg := prodTy natTy ta2
  let lagg := mkApp (mkConst ``List [Level.zero]) tAgg
  let tk5 := prodTy natTy t5
  let tk4 := prodTy xc tk5
  let tk3 := prodTy lnatE tk4
  let tk2 := prodTy natTy tk3
  let tKid := prodTy natTy tk2
  let lkid := mkApp (mkConst ``List [Level.zero]) tKid
  let tn16 := prodTy natTy lkid
  let tn15 := prodTy natTy tn16
  let tn14 := prodTy natTy tn15
  let tn13 := prodTy lnatE tn14
  let tn12 := prodTy lagg tn13
  let tn11 := prodTy lnatE tn12
  let tn10 := prodTy lnatE tn11
  let tn9 := prodTy lnatE tn10
  let tn8 := prodTy lnatE tn9
  let tn7 := prodTy lnatE tn8
  let tn6 := prodTy lnatE tn7
  let tn5 := prodTy lnatE tn6
  let tn4 := prodTy natTy tn5
  let tn3 := prodTy natTy tn4
  let tn2 := prodTy natTy tn3
  { ta3, ta2, tAgg, lagg, tk2, tk3, tk4, tk5, tKid, lkid,
    tn := #[natTy, natTy, tn2, tn3, tn4, tn5, tn6, tn7, tn8, tn9, tn10, tn11, tn12, tn13, tn14, tn15, tn16],
    tNode := prodTy natTy tn2 }


meta def parseRec2 (T : Tys) (cREPm cREP cDIAG : Nat) (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
  let mut q := q0
  let l := it[q]!; let hdr := it[q+1]!; q := q + 2
  let rd (q : Nat) : List Nat × Nat := let k := it[q]!; ((List.range k).map fun j => it[q + 1 + j]!, q + 1 + k)
  let (r2, q1) := rd q; let (r1, q2) := rd q1; let (r0, q3) := rd q2; let (x2, q4) := rd q3; let (x1, q5) := rd q4
  let (ks, q6) := rd q5; let (nr, q7) := rd q6
  q := q7
  let na := it[q]!; q := q + 1
  let mut aggs : Array Expr := #[]
  for _ in [0:na] do
    let x := it[q]!; let k := it[q+1]!
    let masks := (List.range k).map fun j => it[q + 2 + k + j]!
    let B := KDLoadXB.aggB cREPm cREP cDIAG x (← KDLoadXB.litOf (tabName x)) masks
    q := q + 2
    let rows := (List.range k).map fun j => it[q + j]!
    q := q + 2 * k
    aggs := aggs.push (mkPair natTy T.ta2 (mkRawNatLit x) (mkPair natTy T.ta3 (mkConst (tabName x)) (mkPair natTy lnatE (mkRawNatLit B) (mlE rows))))
  let (XL, q8) := rd q
  q := q8
  let HP := it[q]!; let DEFP := it[q+1]!; q := q + 2
  let nk := it[q]!; q := q + 1
  let mut kids : Array Expr := #[]
  for _ in [0:nk] do
    let u := it[q+2]!; let Fu := it[q+3]!; let ncr := it[q+4]!; q := q + 5
    let cr := (List.range ncr).map fun j => it[q + j]!
    q := q + ncr
    let (tr, q', _, _) := KDLoadXB2.mkXC2 it q
    q := q'
    kids := kids.push (mkPair natTy T.tk2 (mkRawNatLit u) (mkPair natTy T.tk3 (mkRawNatLit Fu) (mkPair lnatE T.tk4 (mlE cr)
      (mkPair (mkConst ``KD.XC2) T.tk5 tr (mkPair natTy t5E (mkConst (tabName u)) (KDLoadXB.tupleE (510 - u)))))))
  let tn := T.tn
  let node := mkPair natTy tn[2]! (mkConst (tabName l)) (mkPair natTy tn[3]! (mkConst (L1Load.hName "h" l))
    (mkPair natTy tn[4]! (mkConst (L1Load.hName "suf" l))
    (mkPair natTy tn[5]! (mkRawNatLit hdr) (mkPair lnatE tn[6]! (mlE r2) (mkPair lnatE tn[7]! (mlE r1) (mkPair lnatE tn[8]! (mlE r0)
      (mkPair lnatE tn[9]! (mlE x2) (mkPair lnatE tn[10]! (mlE x1) (mkPair lnatE tn[11]! (mlE ks) (mkPair lnatE tn[12]! (mlE nr)
        (mkPair T.lagg tn[13]! (mkList T.tAgg aggs.toList) (mkPair lnatE tn[14]! (mlE XL) (mkPair natTy tn[15]! (mkRawNatLit HP)
          (mkPair natTy tn[16]! (mkRawNatLit DEFP) (mkPair natTy T.lkid (mkRawNatLit XL.length) (mkList T.tKid kids.toList))))))))))))))))
  return (node, q)


meta def itemBatchesR2 (I : Name) (dir : String) (k0 k1 : Nat) : CommandElabM Nat := do
  let tab := mkConst (I ++ `T ++ `entry)
  let nb ← KDLoadXB.litOf (I ++ `nb)
  let T := mkTys
  let T2 := mkTys2
  let nodeE2 := prodTy T2.tNode extRTy
  let lnodeTy2 := mkApp (mkConst ``List [Level.zero]) nodeE2
  let (cREPm, cREP, cDIAG) := ((← KDLoadXB.litOf `KD.REPmF), (← KDLoadXB.litOf `KD.REPF), (← KDLoadXB.litOf `KD.DIAGF))
  let nodeE := prodTy T.tNode extRTy
  let lnodeTy := mkApp (mkConst ``List [Level.zero]) nodeE
  let lfrTy := mkApp (mkConst ``List [Level.zero]) frPTy
  let mut wsum := 0
  for k in [k0:min k1 nb] do
    let it := KDLoadXB.itemsF (← IO.FS.readBinFile (batchFile dir k))
    let (st, q1) := stackAt it 0
    let mut q := q1
    if k == 0 then
      let w ← thm (I ++ `s0_eq) (mkApp3 (mkConst ``Eq [Level.one]) lfrTy (mkConst (I ++ `s0)) st)
        (mkApp2 (mkConst ``Eq.refl [Level.one]) lfrTy (mkConst (I ++ `s0))) "first stack"
      wsum := wsum + w
    else if !(← getEnv).contains (sName I k) then
      liftCoreM <| defT (sName I k) lfrTy st
    let n := it[q]!; q := q + 1
    let mut recs : Array Expr := #[]
    for _ in [0:n] do
      let (x, q2) ← parseRec2 T2 cREPm cREP cDIAG it q
      let (e, q3) ← parseExtR it q2
      q := q3
      recs := recs.push (mkPair T2.tNode extRTy x e)
    if q != it.size then throwError "kritem: batch {k}: {it.size - q} items left over"
    let mN := I ++ Name.mkSimple s!"m{k}"
    liftCoreM <| defT mN lnodeTy2 (mkList nodeE2 recs.toList)
    let nxt := if k + 1 < nb then batchFile dir (k + 1) else dir ++ "/fin.bin"
    let (stn, _) := stackAt (KDLoadXB.itemsF (← IO.FS.readBinFile nxt)) 0
    liftCoreM <| defT (sName I (k + 1)) lfrTy stn
    -- the kernel check on the packed records, then the unpacked batch by KD.itemXR2'_imp (no evaluation)
    let ty2 := eqTrue (mkAppN (mkConst ``KD.itemXR2' []) ((chainArgsR I tab).push (mkConst (sName I k)) |>.push
      (mkConst mN) |>.push (mkConst (sName I (k + 1)))))
    let w ← thm (I ++ Name.mkSimple s!"c{k}") ty2 rflTrue s!"{I} batch {k}"
    let pf := mkAppN (mkConst ``KD.itemXR2'_imp []) ((chainArgsR I tab) ++ #[mkConst mN, mkConst (sName I k), mkConst (sName I (k + 1)),
      mkConst (I ++ Name.mkSimple s!"c{k}")])
    let pty ← liftTermElabM <| Meta.inferType pf
    -- pty = (itemXR' … s_k (List.map f m_k) s_{k+1} = true): name its record list I.n<k>, prove I.b<k>
    let some (_, lhs, _) := pty.eq? | throwError "kritemB2: unexpected type {pty}"
    let mapped := lhs.getAppArgs[14]!
    liftCoreM <| defT (I ++ Name.mkSimple s!"n{k}") lnodeTy mapped
    let ty := eqTrue (mkAppN (mkConst ``KD.itemXR' []) ((chainArgsR I tab).push (mkConst (sName I k)) |>.push
      (mkConst (I ++ Name.mkSimple s!"n{k}")) |>.push (mkConst (sName I (k + 1)))))
    let _ ← thm (I ++ Name.mkSimple s!"b{k}") ty pf s!"{I} batch {k} (unpacked)"
    logInfo m!"{I}.b{k}: {n} records, kernel {w} ms"
    wsum := wsum + w
  return wsum

elab "#kritemB2 " id:ident p:str k0:num k1:num : command => do
  let w ← itemBatchesR2 id.getId p.getString k0.getNat k1.getNat
  logInfo m!"{id.getId}: batches {k0.getNat}..{k1.getNat} (packed): kernel {w} ms"
end KBLoadR2
