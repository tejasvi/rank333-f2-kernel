module
public import R22Port.U_6050cb77ad13
public meta import Lean
public import Lean
public import KB.Defs
public import KDK.LoadXB
public import R3RT.LoadTD
public import R3RT.TabC3eD
public import L1.HypTables
public meta import KB.Defs
public meta import KDK.LoadXB
public meta import R3RT.LoadTD
public meta import R3RT.TabC3eD
public meta import L1.HypTables
/-! # KB.LoadItem: loaders for the kernel track's items

* `#kdstatII "c2t"`: the label tables of the item checker as functions of the label (balanced `Bool.rec` dispatchers over the
  bits of `l`): `KI.c2T l = L1.T.c2t_<l>` (the cap-2 tables, `R3RT.TabC3eD`; per label they equal case (II)'s `rt479/C3eDII.c2t`),
  `KI.hkT l = L1.T.h_<l>` (`L1.HypTables`), `KI.cpT u = (KD.XC.rep_n, repm_n, grd_n, lows_n, diag_n)` with `n = 510 - u`
  (`KD.XConstN`), and `KI.c1` = the cap-1 table of the given file (slot 511).
* `#kditem I "dir" key`: from `py/kitem.py`'s `dir/item.bin` and `dir/table_0.bin`: the item's row table `I.T` (R3's guarded
  table), its root data `I.pl`, `I.lastP`, `I.f0`, `I.l0`, `I.pend0`, the stacks `I.s<k>` and record lists `I.n<k>`, one kernel
  check per batch `I.b<k> : KD.itemXS' … I.s<k> I.n<k> I.s<k+1> = true`, the chain `I.chain : KD.ChainK … I.s0 I.sN`, and
  `I.root : KB.rootChk0 KI.c1 KI.c2T KI.hkT I.T.entry I.pl I.W I.lastP I.f0 = true` (`I.W`: the root frame's witness rows),
  `I.fin : KD.pendZ I.sN = true`, the external children `I.extL` (the key's order),
  `I.hp0 : I.pend0.testBit I.l0 = true`; with the key `I.key`, the interface facts `I.hkr`, `I.hlo`, `I.hrng`, `I.hext`.
  Every theorem is checked by the kernel when it is added (times logged). -/
@[expose] public section
open Lean Elab Command L1Load
namespace KBLoad

meta def lnatE : Expr := mkApp (mkConst ``List [Level.zero]) natTy
meta def lpairE : Expr := mkApp (mkConst ``List [Level.zero]) (prodTy natTy natTy)
meta def mlE (xs : List Nat) : Expr := mkList natTy (xs.map mkRawNatLit)
meta def t5E : Expr := prodTy natTy (prodTy natTy (prodTy natTy (prodTy natTy natTy)))
meta def frE (S D N U d : Nat) : Expr :=
  mkPair natTy (prodTy natTy (prodTy natTy (prodTy natTy natTy))) (mkRawNatLit S)
    (mkPair natTy (prodTy natTy (prodTy natTy natTy)) (mkRawNatLit D)
      (mkPair natTy (prodTy natTy natTy) (mkRawNatLit N) (mkPair natTy natTy (mkRawNatLit U) (mkRawNatLit d))))
meta def frPTy : Expr := mkConst ``KD.FrP
meta def frPE (S D N U d p : Nat) : Expr := mkPair t5E natTy (frE S D N U d) (mkRawNatLit p)

/-- balanced dispatcher `fun l => …` over 512 leaves (`Bool.rec` on bit `k` of `l`, high bits first) -/
meta def dispatch (ty : Expr) (leaf : Nat → Expr) : Expr :=
  let rec go (lo : Nat) : Nat → Expr
    | 0 => leaf lo
    | k + 1 =>
      mkApp4 (mkConst ``Bool.rec [Level.one]) (mkLambda `_ BinderInfo.default (mkConst ``Bool) ty)
        (go lo k) (go (lo + 2 ^ k) k) (RTLoad.bitE (mkBVar 0) k)
  mkLambda `l BinderInfo.default natTy (go 0 9)

meta def eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) e (mkConst ``Bool.true)
meta def rflTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def thm (n : Name) (ty pf : Expr) (what : String) : CommandElabM Nat := do
  let (w, _) ← R3RTAdd.addTimed (Declaration.thmDecl { name := n, levelParams := [], type := ty, value := pf }) what
  return w

meta def defT (n : Name) (ty v : Expr) : CoreM Unit := do
  let dv : DefinitionVal := { name := n, levelParams := [], type := ty, value := v, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv) (forceExpose := true)

elab "#kdstatII " p:str : command => do
  let fnTy := mkForall `l BinderInfo.default natTy natTy
  liftCoreM <| defT `KI.c2T fnTy (dispatch natTy fun l => if l < 511 then mkConst (tabName l) else mkRawNatLit 0)
  liftCoreM <| defT `KI.hkT fnTy (dispatch natTy fun l => if l < 511 then mkConst (L1Load.hName "h" l) else mkRawNatLit 0)
  liftCoreM <| defT `KI.cpT (mkForall `l BinderInfo.default natTy t5E) (dispatch t5E fun l => KDLoadXB.tupleE (510 - l))
  let b ← IO.FS.readBinFile p.getString
  liftCoreM <| defT `KI.c1 natTy (mkRawNatLit (natLE b (511 * 511 * 64) (512 * 511 * 64)))
  -- the binding's diagonal-clearing mask (R3's `#r3bindc2`)
  let mut DC := 2 ^ (511 * 512) - 1
  for u in [0:511] do DC := DC - 2 ^ (513 * u)
  liftCoreM <| defT `KI.DC natTy (mkRawNatLit DC)

meta def rowsTy : Expr := mkApp (mkConst ``List [Level.zero]) (prodTy natTy lnatE)
meta def rowsName (q : Nat) : Name := Name.mkStr `KI s!"rows_{q}"
meta def bqName (q : Nat) : Name := Name.mkStr `KI s!"bq_{q}"
meta def bindQE (q : Nat) (rows : Expr) : Expr :=
  let cap := if q < 511 then 2 else 1
  let stored := if q < 511 then mkApp (mkConst `KI.c2T) (mkRawNatLit q) else mkConst `KI.c1
  eqTrue (mkAppN (mkConst ``R3RT.bindQ) #[mkConst ``L5II.rowEII, mkRawNatLit q, mkRawNatLit cap, rows, stored, mkConst `KI.DC])

/-- `#kibind q "file"`: `KI.rows_<q>` (items: n, n x (id, k, k labels)) and the kernel check
`KI.bq_<q> : R3RT.bindQ L5II.rowEII q 2 KI.rows_<q> (KI.c2T q) KI.DC = true` (`q = 511`: cap 1, `KI.c1`) -/
elab "#kibind " qn:num p:str : command => do
  let q := qn.getNat
  let it := KDLoadXB.itemsF (← IO.FS.readBinFile p.getString)
  let n := it[0]!
  let mut rs : Array Expr := #[]
  let mut o := 1
  for _ in [0:n] do
    let id := it[o]!; let k := it[o+1]!
    rs := rs.push (mkPair natTy lnatE (mkRawNatLit id) (mlE ((List.range k).map fun j => it[o+2+j]!)))
    o := o + 2 + k
  liftCoreM <| defT (rowsName q) rowsTy (mkList (prodTy natTy lnatE) rs.toList)
  let w ← thm (bqName q) (bindQE q (mkConst (rowsName q))) rflTrue s!"KI.bq_{q}"
  logInfo m!"KI.bq_{q}: {n} rows, kernel {w} ms"

/-- `#kibindAll`: `KI.bindRows` (the rows of label `q`) and `KI.c2_all : KB.AllBelow (fun q => bindQ … q 2 (KI.bindRows q)
(KI.c2T q) KI.DC = true) 511` from the 511 checks `KI.bq_<q>` -/
elab "#kibindAll" : command => do
  liftCoreM <| defT `KI.bindRows (mkForall `q BinderInfo.default natTy rowsTy)
    (dispatch rowsTy fun q => if q < 511 then mkConst (rowsName q) else mkList (prodTy natTy lnatE) [])
  let P := mkLambda `q BinderInfo.default natTy (eqTrue (mkAppN (mkConst ``R3RT.bindQ) #[mkConst ``L5II.rowEII, mkBVar 0,
    mkRawNatLit 2, mkApp (mkConst `KI.bindRows) (mkBVar 0), mkApp (mkConst `KI.c2T) (mkBVar 0), mkConst `KI.DC]))
  let allB (k : Nat) : Expr := mkApp2 (mkConst ``KB.AllBelow) P (mkRawNatLit k)
  let mut pf := mkConst ``True.intro
  for k in [0:511] do
    pf := mkApp4 (mkConst ``And.intro) (allB k) (mkApp P (mkRawNatLit k)) pf (mkConst (bqName k))
  let w ← thm `KI.c2_all (allB 511) pf "KI.c2_all"
  logInfo m!"KI.c2_all: kernel {w} ms"

/-- the types of the record tuple (as `KD.LoadXB`) -/
structure Tys where
  ta3 : Expr
  ta2 : Expr
  tAgg : Expr
  lagg : Expr
  tk2 : Expr
  tk3 : Expr
  tk4 : Expr
  tk5 : Expr
  tKid : Expr
  lkid : Expr
  tn : Array Expr     -- tn[2..16]
  tNode : Expr

meta def mkTys : Tys :=
  let t2 := prodTy natTy natTy
  let t3 := prodTy natTy t2
  let t4 := prodTy natTy t3
  let t5 := prodTy natTy t4
  let xc := mkConst ``KD.XC
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

/-- one record in kx3.py's NOB layout at `q` (as `KD.LoadXB.batchCmd`): its `NodeX` term and the next position -/
meta def parseRec (T : Tys) (cREPm cREP cDIAG : Nat) (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
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
    let (tr, q', _, _) := KDLoadXB.mkXC it q
    q := q'
    kids := kids.push (mkPair natTy T.tk2 (mkRawNatLit u) (mkPair natTy T.tk3 (mkRawNatLit Fu) (mkPair lnatE T.tk4 (mlE cr)
      (mkPair (mkConst ``KD.XC) T.tk5 tr (mkPair natTy t5E (mkConst (tabName u)) (KDLoadXB.tupleE (510 - u)))))))
  let tn := T.tn
  let node := mkPair natTy tn[2]! (mkConst (tabName l)) (mkPair natTy tn[3]! (mkConst (L1Load.hName "h" l))
    (mkPair natTy tn[4]! (mkConst (L1Load.hName "suf" l))
    (mkPair natTy tn[5]! (mkRawNatLit hdr) (mkPair lnatE tn[6]! (mlE r2) (mkPair lnatE tn[7]! (mlE r1) (mkPair lnatE tn[8]! (mlE r0)
      (mkPair lnatE tn[9]! (mlE x2) (mkPair lnatE tn[10]! (mlE x1) (mkPair lnatE tn[11]! (mlE ks) (mkPair lnatE tn[12]! (mlE nr)
        (mkPair T.lagg tn[13]! (mkList T.tAgg aggs.toList) (mkPair lnatE tn[14]! (mlE XL) (mkPair natTy tn[15]! (mkRawNatLit HP)
          (mkPair natTy tn[16]! (mkRawNatLit DEFP) (mkPair natTy T.lkid (mkRawNatLit XL.length) (mkList T.tKid kids.toList))))))))))))))))
  return (node, q)

meta def dpayTy : Expr := mkConst ``KB.DPay
meta def dkTy : Expr :=
  prodTy natTy (prodTy natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy)))))
meta def extTy : Expr := prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy (mkApp (mkConst ``List [Level.zero]) dkTy) natTy)))

meta def dkPair (u hdr : Nat) (r0 : List Nat) (pay : Expr) : Expr :=
  mkPair natTy (prodTy natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy))))) (mkConst (tabName u))
    (mkPair natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy)))) (mkConst (L1Load.hName "h" u))
      (mkPair natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy))) (mkRawNatLit hdr)
        (mkPair lnatE (prodTy lnatE (prodTy lnatE dpayTy)) (mlE []) (mkPair lnatE (prodTy lnatE dpayTy) (mlE [])
          (mkPair lnatE dpayTy (mlE r0) pay)))))

/-- one dead child at `q`: `(u, hdr, nV, V idx, tag, payload)`, tag 0 cut `(kind, arg, row idx)`, 1 look-ahead
`(t, nT, h2, nTL, TL, TY, nSL, SL, SY)`, 2 profile leaf `(R)` -/
meta def parseDK (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
  let mut q := q0
  let rd (q : Nat) : List Nat × Nat := let k := it[q]!; ((List.range k).map fun j => it[q + 1 + j]!, q + 1 + k)
  let u := it[q]!; let hdr := it[q+1]!; q := q + 2
  let (r0, q') := rd q; q := q'
  let tag := it[q]!; q := q + 1
  if tag == 0 then
    let pay := mkAppN (mkConst ``KB.DPay.cut) #[mkRawNatLit it[q]!, mkRawNatLit it[q+1]!, mkRawNatLit it[q+2]!]
    return (dkPair u hdr r0 pay, q + 3)
  if tag == 2 then
    return (dkPair u hdr r0 (mkApp (mkConst ``KB.DPay.leaf) (mkRawNatLit it[q]!)), q + 1)
  if tag == 3 then
    -- a node cut 5 / 6 as an X part: x2, x1, node rows, aggregates (NOB layout), deficit table, one child
    let T := mkTys
    let (cREPm, cREP, cDIAG) := ((← KDLoadXB.litOf `KD.REPmF), (← KDLoadXB.litOf `KD.REPF), (← KDLoadXB.litOf `KD.DIAGF))
    let (x2, q1) := rd q; let (x1, q2) := rd q1; let (nr, q3) := rd q2; q := q3
    let na := it[q]!; q := q + 1
    let mut aggs : Array Expr := #[]
    for _ in [0:na] do
      let x := it[q]!; let k := it[q+1]!
      let masks := (List.range k).map fun j => it[q + 2 + k + j]!
      let B := KDLoadXB.aggB cREPm cREP cDIAG x (← KDLoadXB.litOf (tabName x)) masks
      let rows := (List.range k).map fun j => it[q + 2 + j]!
      q := q + 2 + 2 * k
      aggs := aggs.push (mkPair natTy T.ta2 (mkRawNatLit x) (mkPair natTy T.ta3 (mkConst (tabName x)) (mkPair natTy lnatE (mkRawNatLit B) (mlE rows))))
    let (XL, q4) := rd q; q := q4
    let HP := it[q]!; let DEFP := it[q+1]!; let J := it[q+2]!; q := q + 3
    let ku := it[q+2]!; let Fu := it[q+3]!; let ncr := it[q+4]!; q := q + 5
    let cr := (List.range ncr).map fun j => it[q + j]!
    q := q + ncr
    let (tr, q', _, _) := KDLoadXB.mkXC it q
    q := q'
    let kid := mkPair natTy T.tk2 (mkRawNatLit ku) (mkPair natTy T.tk3 (mkRawNatLit Fu) (mkPair lnatE T.tk4 (mlE cr)
      (mkPair (mkConst ``KD.XC) T.tk5 tr (mkPair natTy t5E (mkConst (tabName ku)) (KDLoadXB.tupleE (510 - ku))))))
    let pay := mkAppN (mkConst ``KB.DPay.xcut) #[mlE x2, mlE x1, mlE nr, mkList T.tAgg aggs.toList, mlE XL, mkRawNatLit HP,
      mkRawNatLit DEFP, mkRawNatLit J, kid]
    return (dkPair u hdr r0 pay, q)
  if tag != 1 then throwError "kditem: dead-child payload tag {tag} not supported"
  let t := it[q]!; let nT := it[q+1]!; let h2 := it[q+2]!; q := q + 3
  let nTL := it[q]!; q := q + 1
  let TL := (List.range nTL).map fun j => it[q + j]!; q := q + nTL
  let TY := (List.range nTL).map fun j => it[q + j]!; q := q + nTL
  let nSL := it[q]!; q := q + 1
  let SL := (List.range nSL).map fun j => it[q + j]!; q := q + nSL
  let SY := (List.range nSL).map fun j => it[q + j]!; q := q + nSL
  let pay := mkAppN (mkConst ``KB.DPay.flook) #[mkRawNatLit t, mkRawNatLit nT, mkRawNatLit h2, mlE TL, mlE TY, mlE SL, mlE SY]
  return (dkPair u hdr r0 pay, q)

/-- one extension datum at `q`: `(b, its, cs, dks, xm)` -/
meta def parseExt (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
  let mut q := q0
  let rd (q : Nat) : List Nat × Nat := let k := it[q]!; ((List.range k).map fun j => it[q + 1 + j]!, q + 1 + k)
  let b := it[q]!; q := q + 1
  let (its, q1) := rd q; let (cs, q2) := rd q1; q := q2
  let ndk := it[q]!; q := q + 1
  let mut dks : Array Expr := #[]
  for _ in [0:ndk] do
    let (dk, q') ← parseDK it q
    dks := dks.push dk; q := q'
  let xm := it[q]!; q := q + 1
  let e := mkPair natTy (prodTy lnatE (prodTy lnatE (prodTy (mkApp (mkConst ``List [Level.zero]) dkTy) natTy))) (mkRawNatLit b)
    (mkPair lnatE (prodTy lnatE (prodTy (mkApp (mkConst ``List [Level.zero]) dkTy) natTy)) (mlE its)
      (mkPair lnatE (prodTy (mkApp (mkConst ``List [Level.zero]) dkTy) natTy) (mlE cs)
        (mkPair (mkApp (mkConst ``List [Level.zero]) dkTy) natTy (mkList dkTy dks.toList) (mkRawNatLit xm))))
  return (e, q)

meta def stackAt (it : Array Nat) (q0 : Nat) : Expr × Nat := Id.run do
  let s := it[q0]!
  let mut fs : Array Expr := #[]
  let mut q := q0 + 1
  for _ in [0:s] do
    fs := fs.push (frPE it[q]! it[q+1]! it[q+2]! it[q+3]! it[q+4]! it[q+5]!); q := q + 6
  return (mkList frPTy fs.toList, q)


/-- the item's head: row table (`I.T`, its check `I.T.tab_ok` and shape `I.T.valid`), root data, key, first stack `I.s0` -/
meta def itemTable (I : Name) (dir : String) : CommandElabM Unit := do
  R3RTLoadTD.rttableG (I ++ `T) (dir ++ "/table_0.bin") 64 552
  let tab := mkConst (I ++ `T ++ `entry)
  let ntab := (← IO.FS.readBinFile (dir ++ "/table_0.bin")).size / 69
  let nch := (ntab + 63) / 64
  let dep := Nat.max 1 (Nat.log2 (nch - 1) + 1)
  let chunkE := mkConst (I ++ `T ++ `chunk)
  let wt ← thm (I ++ `T ++ `tab_ok) (eqTrue (mkAppN (mkConst ``R3RT.tabOKQ) #[mkConst ``L5II.rowEII, chunkE, mkRawNatLit 64,
    mkConst (I ++ `T ++ `N), mkRawNatLit nch])) rflTrue s!"{I} job table"
  let hent := mkLambda `i BinderInfo.default natTy (mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (mkApp tab (mkBVar 0)))
  let hch := mkLambda `q BinderInfo.default natTy (mkLambda `hq BinderInfo.default
    (mkApp2 (mkConst ``LE.le [Level.zero]) natTy (mkConst ``instLENat) |>.app (mkRawNatLit nch) |>.app (mkBVar 0))
    (mkAppN (mkConst ``KB.guard_zero) #[mkConst (I ++ `T ++ Name.mkSimple s!"D{dep}_0"), mkRawNatLit nch, mkBVar 1, mkBVar 0]))
  let wv ← thm (I ++ `T ++ `valid) (mkApp (mkConst ``KB.TabVII) tab)
    (mkAppN (mkConst ``KB.tabVII_of) #[chunkE, mkConst (I ++ `T ++ `N), mkRawNatLit nch, tab, hent, hch,
      mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (mkRawNatLit nch), rflTrue, mkConst (I ++ `T ++ `tab_ok)]) s!"{I} job table shape"
  logInfo m!"{I}.T: {ntab} rows, tab_ok kernel {wt} ms, shape {wv} ms"

meta def itemHead (I : Name) (dir : String) (key : Nat) : CommandElabM Unit := do
  itemTable I dir
  let it := KDLoadXB.itemsF (← IO.FS.readBinFile (dir ++ "/head.bin"))
  if it[0]! != 1 then throwError "kditem: item format {it[0]!}"
  let l0 := it[1]!; let pend0 := it[2]!; let npl := it[3]!
  let pl := (List.range npl).map fun j => it[4 + j]!
  let q := 4 + npl
  liftCoreM <| defT (I ++ `pl) lnatE (mlE pl)
  liftCoreM <| defT (I ++ `lastP) natTy (mkRawNatLit it[q]!)
  liftCoreM <| defT (I ++ `f0) t5E (frE it[q+1]! it[q+2]! it[q+3]! it[q+4]! it[q+5]!)
  liftCoreM <| defT (I ++ `l0) natTy (mkRawNatLit l0)
  liftCoreM <| defT (I ++ `pend0) natTy (mkRawNatLit pend0)
  liftCoreM <| defT (I ++ `nb) natTy (mkRawNatLit it[q+6]!)
  liftCoreM <| defT (I ++ `key) natTy (mkRawNatLit key)
  -- the root frame's witness rows (job-table indices) and the item's external children `(S, u)`, in the key's order
  let (W, extL) := if it.size > q + 7 then
      let nW := it[q+7]!
      let W := (List.range nW).map fun j => it[q + 8 + j]!
      let nE := it[q + 8 + nW]!
      let o := q + 9 + nW
      (W, (List.range nE).map fun j => (it[o + 2 * j]!, it[o + 2 * j + 1]!))
    else ([], [])
  liftCoreM <| defT (I ++ `W) lnatE (mlE W)
  liftCoreM <| defT (I ++ `extL) lpairE (mkList (prodTy natTy natTy) (extL.map fun (S, u) => mkPair natTy natTy (mkRawNatLit S) (mkRawNatLit u)))
  let lfrTy := mkApp (mkConst ``List [Level.zero]) frPTy
  liftCoreM <| defT (I ++ `s0) lfrTy (mkList frPTy [mkPair t5E natTy (mkConst (I ++ `f0)) (mkConst (I ++ `pend0))])
  logInfo m!"{I}: root depth {npl + 1}, {W.length} witness rows, {extL.length} external children"

meta def extE (tab : Expr) : Expr := mkAppN (mkConst ``KB.extII) #[mkConst ``R3RT.nperpL, mkConst `KI.c2T, mkConst `KI.hkT,
  mkConst `KI.cpT, tab]
/-- the item's external children: `I.extL` (`[]` for a head written before the list existed) -/
meta def extLE (I : Name) : CommandElabM Expr := do
  return if (← getEnv).contains (I ++ `extL) then mkConst (I ++ `extL) else mkList (prodTy natTy natTy) []
meta def chainArgs (extL tab : Expr) : Array Expr := #[extTy, mkConst ``R3RT.nperpL, mkConst `KI.c2T, mkConst `KI.hkT, mkConst `KI.cpT,
  extL, extE tab, mkConst ``KB.accII, mkConst ``KB.xkII, tab]
meta def sName (I : Name) (k : Nat) : Name := I ++ Name.mkSimple s!"s{k}"
meta def batchFile (dir : String) (k : Nat) : String := dir ++ "/b" ++ (String.mk (List.replicate (4 - (toString k).length) '0')) ++ toString k ++ ".bin"

/-- batches `k0 .. k1 - 1` of the item (each a kernel check `I.b<k>`), with the record lists `I.n<k>` and the next stacks -/
meta def itemBatches (I : Name) (dir : String) (k0 k1 : Nat) : CommandElabM Nat := do
  let tab := mkConst (I ++ `T ++ `entry)
  let extL ← extLE I
  let nb ← KDLoadXB.litOf (I ++ `nb)
  let T := mkTys
  let (cREPm, cREP, cDIAG) := ((← KDLoadXB.litOf `KD.REPmF), (← KDLoadXB.litOf `KD.REPF), (← KDLoadXB.litOf `KD.DIAGF))
  let nodeE := prodTy T.tNode extTy
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
      -- a part started at batch k without the previous part (tests): its input stack from the batch file
      liftCoreM <| defT (sName I k) lfrTy st
    let n := it[q]!; q := q + 1
    let mut recs : Array Expr := #[]
    for _ in [0:n] do
      let (x, q2) ← parseRec T cREPm cREP cDIAG it q
      let (e, q3) ← parseExt it q2
      q := q3
      recs := recs.push (mkPair T.tNode extTy x e)
    if q != it.size then throwError "kditem: batch {k}: {it.size - q} items left over"
    liftCoreM <| defT (I ++ Name.mkSimple s!"n{k}") lnodeTy (mkList nodeE recs.toList)
    let nxt := if k + 1 < nb then batchFile dir (k + 1) else dir ++ "/fin.bin"
    let (stn, _) := stackAt (KDLoadXB.itemsF (← IO.FS.readBinFile nxt)) 0
    liftCoreM <| defT (sName I (k + 1)) lfrTy stn
    let ty := eqTrue (mkAppN (mkConst ``KD.itemXS' []) ((chainArgs extL tab).push (mkConst (sName I k)) |>.push
      (mkConst (I ++ Name.mkSimple s!"n{k}")) |>.push (mkConst (sName I (k + 1)))))
    let w ← thm (I ++ Name.mkSimple s!"b{k}") ty rflTrue s!"{I} batch {k}"
    logInfo m!"{I}.b{k}: {n} records, kernel {w} ms"
    wsum := wsum + w
  return wsum

/-- the item's end: the chain `I.chain`, `I.sN`, the root frame `I.root`, the final stack `I.fin`, the root label `I.hp0` -/
meta def itemEnd (I : Name) : CommandElabM Unit := do
  let tab := mkConst (I ++ `T ++ `entry)
  let extL ← extLE I
  -- a head written before the witness rows / external children existed: both empty
  unless (← getEnv).contains (I ++ `W) do liftCoreM <| defT (I ++ `W) lnatE (mlE [])
  unless (← getEnv).contains (I ++ `extL) do liftCoreM <| defT (I ++ `extL) lpairE extL
  let nb ← KDLoadXB.litOf (I ++ `nb)
  let sN := mkConst (sName I nb)
  let mut pf := mkAppN (mkConst ``KD.ChainK.nil) ((chainArgs extL tab).push sN)
  for j in [0:nb] do
    let k := nb - 1 - j
    pf := mkAppN (mkConst ``KD.ChainK.cons) ((chainArgs extL tab) ++ #[mkConst (sName I k), mkConst (sName I (k + 1)), sN,
      mkConst (I ++ Name.mkSimple s!"n{k}"), mkConst (I ++ Name.mkSimple s!"b{k}"), pf])
  let w ← thm (I ++ `chain) (mkAppN (mkConst ``KD.ChainK) ((chainArgs extL tab) ++ #[mkConst (I ++ `s0), sN])) pf s!"{I} chain"
  let lfrTy := mkApp (mkConst ``List [Level.zero]) frPTy
  liftCoreM <| defT (I ++ `sN) lfrTy sN
  let wr ← thm (I ++ `root) (eqTrue (mkAppN (mkConst ``KB.rootChk0) #[mkConst `KI.c1, mkConst `KI.c2T, mkConst `KI.hkT, tab,
    mkConst (I ++ `pl), mkConst (I ++ `W), mkConst (I ++ `lastP), mkConst (I ++ `f0)])) rflTrue s!"{I} root frame"
  let wf ← thm (I ++ `fin) (eqTrue (mkApp (mkConst ``KD.pendZ) (mkConst (I ++ `sN)))) rflTrue s!"{I} final stack"
  -- the key's ranges and external children, checked by the kernel alone (a key with thousands of external children exceeds the
  -- elaborator's recursion and exponent limits)
  let ofK := mkApp (mkConst ``R22N.SegI.ofKey) (mkConst (I ++ `key))
  let rngTy := mkApp (mkConst ``List [Level.zero]) (prodTy (prodTy natTy natTy) natTy)
  let wrng ← thm (I ++ `hrngK) (mkApp3 (mkConst ``Eq [Level.one]) rngTy (mkApp (mkConst ``R22N.SegI.rng) ofK)
    (mkApp (mkConst ``List.nil [Level.zero]) (prodTy (prodTy natTy natTy) natTy)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) rngTy (mkApp (mkConst ``List.nil [Level.zero]) (prodTy (prodTy natTy natTy) natTy))) s!"{I} ranges"
  let wext ← thm (I ++ `hextK) (mkApp3 (mkConst ``Eq [Level.one]) lpairE (mkApp (mkConst ``R22N.SegI.ext) ofK) (mkConst (I ++ `extL)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) lpairE (mkConst (I ++ `extL))) s!"{I} external children"
  let wp ← thm (I ++ `hp0) (eqTrue (mkApp2 (mkConst ``Nat.testBit) (mkConst (I ++ `pend0)) (mkConst (I ++ `l0)))) rflTrue
    s!"{I} root label"
  logInfo m!"{I}: chain {w} ms, root frame {wr} ms, final {wf} ms, root label {wp} ms, key ranges {wrng} ms, external children {wext} ms"

/-- an item whose root is a dead node: table, root data, the root's record `I.dk`, `I.rootc : KD.rootChk …`,
`I.dkok : KB.dkidOK …` (from `py/kitem.py`'s `dead.bin`) -/
meta def itemDead (I : Name) (dir : String) (key : Nat) : CommandElabM Unit := do
  itemTable I dir
  let tab := mkConst (I ++ `T ++ `entry)
  let it := KDLoadXB.itemsF (← IO.FS.readBinFile (dir ++ "/dead.bin"))
  if it[0]! != 2 then throwError "kditemDead: format {it[0]!}"
  let npl := it[2]!
  let pl := (List.range npl).map fun j => it[3 + j]!
  let q := 3 + npl
  let (S0, D0, N0, U0, d0) := (it[q+1]!, it[q+2]!, it[q+3]!, it[q+4]!, it[q+5]!)
  liftCoreM <| defT (I ++ `pl) lnatE (mlE pl)
  liftCoreM <| defT (I ++ `lastP) natTy (mkRawNatLit it[q]!)
  liftCoreM <| defT (I ++ `f0) t5E (frE S0 D0 N0 U0 d0)
  liftCoreM <| defT (I ++ `key) natTy (mkRawNatLit key)
  let nW := it[q+6]!
  let W := (List.range nW).map fun j => it[q + 7 + j]!
  liftCoreM <| defT (I ++ `W) lnatE (mlE W)
  let (dk, qe) ← parseDK it (q + 7 + nW)
  if qe != it.size then throwError "kditemDead: {it.size - qe} items left over"
  liftCoreM <| defT (I ++ `dk) dkTy dk
  let wr ← thm (I ++ `rootc) (eqTrue (mkAppN (mkConst ``KB.rootChkW) #[mkConst `KI.c1, mkConst `KI.c2T, mkConst `KI.hkT, tab,
    mkConst (I ++ `pl), mkConst (I ++ `W), mkConst (I ++ `lastP), mkConst (I ++ `f0)])) rflTrue s!"{I} root frame"
  let wd ← thm (I ++ `dkok) (eqTrue (mkAppN (mkConst ``KB.dkidOK) #[mkConst ``R3RT.nperpL, mkConst `KI.c2T, mkConst `KI.hkT,
    mkConst `KI.cpT, tab, mkRawNatLit S0,
    mkRawNatLit D0, mkRawNatLit N0, mkRawNatLit U0, mkRawNatLit d0, mkConst (I ++ `lastP), mkConst (I ++ `dk)])) rflTrue
    s!"{I} dead root"
  logInfo m!"{I}: dead root, root frame {wr} ms, record {wd} ms"

elab "#kditemDead " id:ident p:str key:num : command => itemDead id.getId p.getString key.getNat
elab "#kditemHead " id:ident p:str key:num : command => itemHead id.getId p.getString key.getNat
elab "#kditemB " id:ident p:str k0:num k1:num : command => do
  let w ← itemBatches id.getId p.getString k0.getNat k1.getNat
  logInfo m!"{id.getId}: batches {k0.getNat}..{k1.getNat}: kernel {w} ms"
elab "#kditemEnd " id:ident : command => itemEnd id.getId
/-- the whole item in one process -/
elab "#kditem " id:ident p:str key:num : command => do
  let t0 ← IO.monoNanosNow
  itemHead id.getId p.getString key.getNat
  let nb ← KDLoadXB.litOf (id.getId ++ `nb)
  let w ← itemBatches id.getId p.getString 0 nb
  itemEnd id.getId
  let t1 ← IO.monoNanosNow
  logInfo m!"{id.getId}: {nb} batches, kernel {w} ms; total {(t1 - t0) / 1000000} ms"

end KBLoad
