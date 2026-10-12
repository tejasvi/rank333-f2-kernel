module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.LoadItem
public import KB.DefsR
public meta import KB.LoadItem
public meta import KB.DefsR
/-! # KB.LoadItemR: loaders for the kernel track's items with ranges (`KD.itemXR'`, `KB.CheckedR`)

`py/kitem.py`'s head (format 1) carries, after the external children, the root's bound `lo` and the item's ranges
`nR, nR x (S, last, l)` (the key's order); each extension datum ends with the record's range start (`511`: none).
* `#kritemHead I "dir" key`: as `#kditemHead`, plus `I.lo` and `I.rngL`;
* `#kritemB I "dir" k0 k1`: batches `k0 .. k1 - 1`, each a kernel check `I.b<k> : KD.itemXR' … = true`;
* `#kritemEnd I`: the chain `I.chain : KD.ChainR …`, `I.root`, `I.fin`, `I.hp0 : Nat.beq I.pend0 (1 <<< I.l0) = true`,
  `I.hrl` (every range above `lo`), and the key's facts `I.hloK`, `I.hrngK`, `I.hextK`, all checked by the kernel alone. -/
@[expose] public section
open Lean Elab Command L1Load KBLoad
namespace KBLoadR

meta def rngElTy : Expr := prodTy (prodTy natTy natTy) natTy
meta def lrngTy : Expr := mkApp (mkConst ``List [Level.zero]) rngElTy
meta def extRTy : Expr := prodTy extTy natTy

/-- one extension datum with the record's range start -/
meta def parseExtR (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
  let (e, q1) ← parseExt it q0
  return (mkPair extTy natTy e (mkRawNatLit it[q1]!), q1 + 1)

meta def extRE (tab : Expr) : Expr := mkAppN (mkConst ``KB.extIIR) #[mkConst ``R3RT.nperpL, mkConst `KI.c2T, mkConst `KI.hkT,
  mkConst `KI.cpT, tab]
meta def chainArgsR (I : Name) (tab : Expr) : Array Expr := #[extRTy, mkConst ``R3RT.nperpL, mkConst `KI.c2T, mkConst `KI.hkT,
  mkConst `KI.cpT, mkConst (I ++ `extL), mkConst (I ++ `lo), mkConst (I ++ `rngL), extRE tab, mkConst ``KB.accIIR,
  mkConst ``KB.xkIIR, mkConst ``KB.rgIIR, tab]

meta def itemHeadR (I : Name) (dir : String) (key : Nat) : CommandElabM Unit := do
  itemHead I dir key
  let it := KDLoadXB.itemsF (← IO.FS.readBinFile (dir ++ "/head.bin"))
  let npl := it[3]!
  let q := 4 + npl
  let nW := it[q+7]!
  let nE := it[q + 8 + nW]!
  let o := q + 9 + nW + 2 * nE
  let lo := it[o]!; let nR := it[o+1]!
  let rs := (List.range nR).map fun j => (it[o + 2 + 3 * j]!, it[o + 3 + 3 * j]!, it[o + 4 + 3 * j]!)
  if o + 2 + 3 * nR != it.size then throwError "kritemHead: {it.size - (o + 2 + 3 * nR)} items left over in the head"
  liftCoreM <| defT (I ++ `lo) natTy (mkRawNatLit lo)
  liftCoreM <| defT (I ++ `rngL) lrngTy (mkList rngElTy (rs.map fun (S, l, r) =>
    mkPair (prodTy natTy natTy) natTy (mkPair natTy natTy (mkRawNatLit S) (mkRawNatLit l)) (mkRawNatLit r)))
  logInfo m!"{I}: lower bound {lo}, {nR} ranges"

/-- batches `k0 .. k1 - 1` of an item with ranges -/
meta def itemBatchesR (I : Name) (dir : String) (k0 k1 : Nat) : CommandElabM Nat := do
  let tab := mkConst (I ++ `T ++ `entry)
  let nb ← KDLoadXB.litOf (I ++ `nb)
  let T := mkTys
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
      let (x, q2) ← parseRec T cREPm cREP cDIAG it q
      let (e, q3) ← parseExtR it q2
      q := q3
      recs := recs.push (mkPair T.tNode extRTy x e)
    if q != it.size then throwError "kritem: batch {k}: {it.size - q} items left over"
    liftCoreM <| defT (I ++ Name.mkSimple s!"n{k}") lnodeTy (mkList nodeE recs.toList)
    let nxt := if k + 1 < nb then batchFile dir (k + 1) else dir ++ "/fin.bin"
    let (stn, _) := stackAt (KDLoadXB.itemsF (← IO.FS.readBinFile nxt)) 0
    liftCoreM <| defT (sName I (k + 1)) lfrTy stn
    let ty := eqTrue (mkAppN (mkConst ``KD.itemXR' []) ((chainArgsR I tab).push (mkConst (sName I k)) |>.push
      (mkConst (I ++ Name.mkSimple s!"n{k}")) |>.push (mkConst (sName I (k + 1)))))
    let w ← thm (I ++ Name.mkSimple s!"b{k}") ty rflTrue s!"{I} batch {k}"
    logInfo m!"{I}.b{k}: {n} records, kernel {w} ms"
    wsum := wsum + w
  return wsum

/-- the end of an item with ranges: chain, root frame, final stack, root label, ranges above the bound, the key's facts -/
meta def itemEndR (I : Name) : CommandElabM Unit := do
  let tab := mkConst (I ++ `T ++ `entry)
  let nb ← KDLoadXB.litOf (I ++ `nb)
  let sN := mkConst (sName I nb)
  let cA := chainArgsR I tab
  let mut pf := mkAppN (mkConst ``KD.ChainR.nil) (cA.push sN)
  for j in [0:nb] do
    let k := nb - 1 - j
    pf := mkAppN (mkConst ``KD.ChainR.cons) (cA ++ #[mkConst (sName I k), mkConst (sName I (k + 1)), sN,
      mkConst (I ++ Name.mkSimple s!"n{k}"), mkConst (I ++ Name.mkSimple s!"b{k}"), pf])
  let w ← thm (I ++ `chain) (mkAppN (mkConst ``KD.ChainR) (cA ++ #[mkConst (I ++ `s0), sN])) pf s!"{I} chain"
  let lfrTy := mkApp (mkConst ``List [Level.zero]) frPTy
  liftCoreM <| defT (I ++ `sN) lfrTy sN
  let wr ← thm (I ++ `root) (eqTrue (mkAppN (mkConst ``KB.rootChk0) #[mkConst `KI.c1, mkConst `KI.c2T, mkConst `KI.hkT, tab,
    mkConst (I ++ `pl), mkConst (I ++ `W), mkConst (I ++ `lastP), mkConst (I ++ `f0)])) rflTrue s!"{I} root frame"
  let wf ← thm (I ++ `fin) (eqTrue (mkApp (mkConst ``KD.pendZ) (mkConst (I ++ `sN)))) rflTrue s!"{I} final stack"
  let wp ← thm (I ++ `hp0) (eqTrue (mkApp2 (mkConst ``Nat.beq) (mkConst (I ++ `pend0))
    (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkConst (I ++ `l0))))) rflTrue s!"{I} root label"
  let pB := mkLambda `p BinderInfo.default rngElTy (mkApp2 (mkConst ``Nat.blt) (mkConst (I ++ `lo))
    (mkApp3 (mkConst ``Prod.snd [Level.zero, Level.zero]) (prodTy natTy natTy) natTy (mkBVar 0)))
  let wl ← thm (I ++ `hrl) (eqTrue (mkApp3 (mkConst ``KD.allB) rngElTy pB (mkConst (I ++ `rngL)))) rflTrue
    s!"{I} ranges above the bound"
  let ofK := mkApp (mkConst ``R22N.SegI.ofKey) (mkConst (I ++ `key))
  let wlo ← thm (I ++ `hloK) (mkApp3 (mkConst ``Eq [Level.one]) natTy (mkApp (mkConst ``R22N.SegI.lo) ofK) (mkConst (I ++ `lo)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (mkConst (I ++ `lo))) s!"{I} bound"
  let wrng ← thm (I ++ `hrngK) (mkApp3 (mkConst ``Eq [Level.one]) lrngTy (mkApp (mkConst ``R22N.SegI.rng) ofK) (mkConst (I ++ `rngL)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) lrngTy (mkConst (I ++ `rngL))) s!"{I} ranges"
  let wext ← thm (I ++ `hextK) (mkApp3 (mkConst ``Eq [Level.one]) lpairE (mkApp (mkConst ``R22N.SegI.ext) ofK) (mkConst (I ++ `extL)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) lpairE (mkConst (I ++ `extL))) s!"{I} external children"
  logInfo m!"{I}: chain {w} ms, root frame {wr} ms, final {wf} ms, root label {wp} ms, ranges {wl} ms, key bound {wlo} ms, key ranges {wrng} ms, external children {wext} ms"

elab "#kritemHead " id:ident p:str key:num : command => itemHeadR id.getId p.getString key.getNat
elab "#kritemB " id:ident p:str k0:num k1:num : command => do
  let w ← itemBatchesR id.getId p.getString k0.getNat k1.getNat
  logInfo m!"{id.getId}: batches {k0.getNat}..{k1.getNat}: kernel {w} ms"
elab "#kritemEnd " id:ident : command => itemEndR id.getId

end KBLoadR
