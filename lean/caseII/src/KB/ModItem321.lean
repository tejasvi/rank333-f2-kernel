module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.LoadItem
public import KB.Agg321
public import KB.PcB
public import KMod.Units
public meta import KB.LoadItem
public meta import KB.Agg321
public meta import KB.PcB
public meta import KMod.Units
/-! # KB.ModItem321: the module-form item emitter for cases (I) / (I13) under `--rord 321`

From `py/kitem.py`'s files with `KI_ORD=321` (`dir/head.bin`, `b<k>.bin`, `fin.bin`, `table_0.bin`), as `KB.LoadItem`'s
`#kditem` with the 321 tables (`R22D.T321.c2t_<l>`, `h_<l>`, `suf_<l>`; `KI321.c2T`, `KI321.hkT`, `R22D.T321.CONF1T`), the
321 hyperplane masks `RT.O321.lpar511`, the job table over `L5O.rowE321` (`KB.TabV321`, `KB.tabV321_of`) and the 321 extension
`KB.ext321K lo hi` (dead children: tag 0 node cut 7, tag 1 look-ahead, tag 2 leaf). Every name is private (`mkPrivateName`):
* `#kmHead321 I "dir" key`: the job table `I.T` (`I.T.tab_ok`, `I.T.valid`), the root data, the key, `I.s0`;
* `#kmB321 I "dir" lo hi k0 k1`: batches `k0 .. k1 - 1`, each one kernel check `I.b<k> : KD.itemXR' … = true` (ranges: a range
  item's bound `I.lo`, its range children `I.rngL`);
* `#kmEnd321 I lo hi`: the chain `I.chain` (`KD.ChainR`), `I.sN`, `I.root` (`rootChk0`), `I.fin`, `I.hp0`, `I.hrl` (ranges above the
  bound), the key's facts `I.hloK`, `I.hrngK`, `I.hextK` (the generated source adds `I.hkr` by `rfl` and
  **`I.checked : KB.CheckedR321 lo hi I.key`**, `py/mkimod321.py`);
* `#kmDead321 I "dir" key`: a dead-root item (`dir/dead.bin`, a piece whose root is killed by a node cut 5 / 6): the job table, the
  root's parent frame `I.rootc` (`rootChkW`, through the fast check `I.rootcF` and `KB.rootChkWF_imp`), the root's record `I.dk`
  (`KB.DPay.xcut` with the 321 tables), `I.isx`, `I.dkok` (`KB.dkidOK` with `RT.O321.lpar511` and the 321 tables); the generated
  source adds the key facts and **`I.checked : KB.CheckedDead321 lo hi I.key`** (`py/mkimod321.py`);
* `#kmKeys321 thm lo hi I1 I2 …`: the module's one public theorem `thm : R22N.KeysOK (KB.CheckedAny321 lo hi) [keys]` (an item with
  `I.dkok` is a dead-root item). -/
public meta section
open Lean Elab Command L1Load KBLoad
namespace KBModItem321

def thmP (n : Name) (ty pf : Expr) (what : String) : CommandElabM Nat := do
  let t0 ← IO.monoNanosNow
  try liftCoreM <| addDecl (Declaration.thmDecl { name := n, levelParams := [], type := ty, value := pf })
  catch e => throwError m!"{what}: kernel rejects: {e.toMessageData}"
  return ((← IO.monoNanosNow) - t0) / 1000000

def tN (k : String) (l : Nat) : Name := Name.mkStr (Name.mkStr `R22D "T321") s!"{k}_{l}"
def c2N (l : Nat) : Name := tN "c2t" l

def dpayTy : Expr := mkConst ``KB.DPay321
def dkTy : Expr := prodTy natTy (prodTy natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy)))))
def ldkTy : Expr := mkApp (mkConst ``List [Level.zero]) dkTy
def extTy : Expr := prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy ldkTy natTy)))
def extRTy : Expr := prodTy extTy natTy
def rngElTy : Expr := prodTy (prodTy natTy natTy) natTy
def lrngTy : Expr := mkApp (mkConst ``List [Level.zero]) rngElTy

def dkPair (u hdr : Nat) (r0 : List Nat) (pay : Expr) : Expr :=
  mkPair natTy (prodTy natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy))))) (mkConst (c2N u))
    (mkPair natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy)))) (mkConst (tN "h" u))
      (mkPair natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayTy))) (mkRawNatLit hdr)
        (mkPair lnatE (prodTy lnatE (prodTy lnatE dpayTy)) (mlE []) (mkPair lnatE (prodTy lnatE dpayTy) (mlE [])
          (mkPair lnatE dpayTy (mlE r0) pay)))))

/-- one dead child at `q`: `(u, hdr, nV, V idx, tag, payload)`; tag 0 node cut `(kind, arg, row idx)` (kind 7 only), 1 look-ahead
`(t, nT, h2, nTL, TL, TY, nSL, SL, SY)`, 2 profile leaf `(R)` -/
def parseDK (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
  let mut q := q0
  let rd (q : Nat) : List Nat × Nat := let k := it[q]!; ((List.range k).map fun j => it[q + 1 + j]!, q + 1 + k)
  let u := it[q]!; let hdr := it[q+1]!; q := q + 2
  let (r0, q') := rd q; q := q'
  let tag := it[q]!; q := q + 1
  if tag == 0 then
    if it[q]! != 7 then throwError "k321item: node cut {it[q]!} (only 7 at --rord 321)"
    return (dkPair u hdr r0 (mkConst ``KB.DPay321.cut7), q + 3)
  if tag == 2 then
    return (dkPair u hdr r0 (mkApp (mkConst ``KB.DPay321.leaf) (mkRawNatLit it[q]!)), q + 1)
  if tag != 1 then throwError "k321item: dead-child payload tag {tag} not supported at --rord 321"
  let t := it[q]!; let nT := it[q+1]!; let h2 := it[q+2]!; q := q + 3
  let nTL := it[q]!; q := q + 1
  let TL := (List.range nTL).map fun j => it[q + j]!; q := q + nTL
  let TY := (List.range nTL).map fun j => it[q + j]!; q := q + nTL
  let nSL := it[q]!; q := q + 1
  let SL := (List.range nSL).map fun j => it[q + j]!; q := q + nSL
  let SY := (List.range nSL).map fun j => it[q + j]!; q := q + nSL
  let pay := mkAppN (mkConst ``KB.DPay321.flook) #[mkRawNatLit t, mkRawNatLit nT, mkRawNatLit h2, mlE TL, mlE TY, mlE SL, mlE SY]
  return (dkPair u hdr r0 pay, q)

def dpayXTy : Expr := mkConst ``KB.DPay
def dkXTy : Expr := prodTy natTy (prodTy natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayXTy)))))
/-- a dead root's record as `KB.DKid` (payload `KB.DPay`), with the 321 tables -/
def dkPairX (u hdr : Nat) (r0 : List Nat) (pay : Expr) : Expr :=
  mkPair natTy (prodTy natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayXTy))))) (mkConst (c2N u))
    (mkPair natTy (prodTy natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayXTy)))) (mkConst (tN "h" u))
      (mkPair natTy (prodTy lnatE (prodTy lnatE (prodTy lnatE dpayXTy))) (mkRawNatLit hdr)
        (mkPair lnatE (prodTy lnatE (prodTy lnatE dpayXTy)) (mlE []) (mkPair lnatE (prodTy lnatE dpayXTy) (mlE [])
          (mkPair lnatE dpayXTy (mlE r0) pay)))))

/-- a dead root's record at `q`: `(u, hdr, nV, V idx, 3, X part)`, a node cut 5 / 6 as `KB.DPay.xcut` (x2, x1, node rows, aggregates
in the NOB layout, deficit table, one child), with the 321 tables; no other kind is in the 321 dead-root contract -/
def parseDKX (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
  let mut q := q0
  let rd (q : Nat) : List Nat × Nat := let k := it[q]!; ((List.range k).map fun j => it[q + 1 + j]!, q + 1 + k)
  let u := it[q]!; let hdr := it[q+1]!; q := q + 2
  let (r0, q') := rd q; q := q'
  let tag := it[q]!; q := q + 1
  if tag != 3 then throwError "k321dead: the root's record has tag {tag}; only a node cut 5 / 6 (tag 3) is in the 321 dead-root contract"
  let T := mkTys
  let (cREPm, cREP, cDIAG) := ((← KDLoadXB.litOf `KD.REPmF), (← KDLoadXB.litOf `KD.REPF), (← KDLoadXB.litOf `KD.DIAGF))
  let (x2, q1) := rd q; let (x1, q2) := rd q1; let (nr, q3) := rd q2; q := q3
  let na := it[q]!; q := q + 1
  let mut aggs : Array Expr := #[]
  for _ in [0:na] do
    let x := it[q]!; let k := it[q+1]!
    let masks := (List.range k).map fun j => it[q + 2 + k + j]!
    let B := KDLoadXB.aggB cREPm cREP cDIAG x (← KDLoadXB.litOf (c2N x)) masks
    let rows := (List.range k).map fun j => it[q + 2 + j]!
    q := q + 2 + 2 * k
    aggs := aggs.push (mkPair natTy T.ta2 (mkRawNatLit x) (mkPair natTy T.ta3 (mkConst (c2N x)) (mkPair natTy lnatE (mkRawNatLit B) (mlE rows))))
  let (XL, q4) := rd q; q := q4
  let HP := it[q]!; let DEFP := it[q+1]!; let J := it[q+2]!; q := q + 3
  let ku := it[q+2]!; let Fu := it[q+3]!; let ncr := it[q+4]!; q := q + 5
  let cr := (List.range ncr).map fun j => it[q + j]!
  q := q + ncr
  let (tr, q', _, _) := KDLoadXB.mkXC it q
  q := q'
  let kid := mkPair natTy T.tk2 (mkRawNatLit ku) (mkPair natTy T.tk3 (mkRawNatLit Fu) (mkPair lnatE T.tk4 (mlE cr)
    (mkPair (mkConst ``KD.XC) T.tk5 tr (mkPair natTy t5E (mkConst (c2N ku)) (KDLoadXB.tupleE (510 - ku))))))
  let pay := mkAppN (mkConst ``KB.DPay.xcut) #[mlE x2, mlE x1, mlE nr, mkList T.tAgg aggs.toList, mlE XL, mkRawNatLit HP,
    mkRawNatLit DEFP, mkRawNatLit J, kid]
  return (dkPairX u hdr r0 pay, q)

/-- one extension datum at `q`: `((b, its, cs, dks, xm), range start)` (511: no range reference) -/
def parseExt (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
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
  -- py/kitem.py ends every datum with the record's range start (511: none)
  let rg := it[q]!; q := q + 1
  let e := mkPair natTy (prodTy lnatE (prodTy lnatE (prodTy ldkTy natTy))) (mkRawNatLit b)
    (mkPair lnatE (prodTy lnatE (prodTy ldkTy natTy)) (mlE its)
      (mkPair lnatE (prodTy ldkTy natTy) (mlE cs) (mkPair ldkTy natTy (mkList dkTy dks.toList) (mkRawNatLit xm))))
  return (mkPair extTy natTy e (mkRawNatLit rg), q)

/-- one record in kx3.py's NOB layout at `q`, with the 321 tables -/
def parseRec (T : Tys) (cREPm cREP cDIAG : Nat) (it : Array Nat) (q0 : Nat) : CommandElabM (Expr × Nat) := do
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
    let B := KDLoadXB.aggB cREPm cREP cDIAG x (← KDLoadXB.litOf (c2N x)) masks
    q := q + 2
    let rows := (List.range k).map fun j => it[q + j]!
    q := q + 2 * k
    aggs := aggs.push (mkPair natTy T.ta2 (mkRawNatLit x) (mkPair natTy T.ta3 (mkConst (c2N x)) (mkPair natTy lnatE (mkRawNatLit B) (mlE rows))))
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
      (mkPair (mkConst ``KD.XC) T.tk5 tr (mkPair natTy t5E (mkConst (c2N u)) (KDLoadXB.tupleE (510 - u)))))))
  let tn := T.tn
  let node := mkPair natTy tn[2]! (mkConst (c2N l)) (mkPair natTy tn[3]! (mkConst (tN "h" l))
    (mkPair natTy tn[4]! (mkConst (tN "suf" l))
    (mkPair natTy tn[5]! (mkRawNatLit hdr) (mkPair lnatE tn[6]! (mlE r2) (mkPair lnatE tn[7]! (mlE r1) (mkPair lnatE tn[8]! (mlE r0)
      (mkPair lnatE tn[9]! (mlE x2) (mkPair lnatE tn[10]! (mlE x1) (mkPair lnatE tn[11]! (mlE ks) (mkPair lnatE tn[12]! (mlE nr)
        (mkPair T.lagg tn[13]! (mkList T.tAgg aggs.toList) (mkPair lnatE tn[14]! (mlE XL) (mkPair natTy tn[15]! (mkRawNatLit HP)
          (mkPair natTy tn[16]! (mkRawNatLit DEFP) (mkPair natTy T.lkid (mkRawNatLit XL.length) (mkList T.tKid kids.toList))))))))))))))))
  return (node, q)

/-- the job table `I.T` over the 321 row interface, its check `I.T.tab_ok` and shape `I.T.valid : KB.TabV321 I.T.entry` -/
def itemTable (I : Name) (dir : String) : CommandElabM Unit := do
  R3RTLoadTD.rttableG (I ++ `T) (dir ++ "/table_0.bin") 64 552
  let tab := mkConst (I ++ `T ++ `entry)
  let ntab := (← IO.FS.readBinFile (dir ++ "/table_0.bin")).size / 69
  let nch := (ntab + 63) / 64
  let dep := Nat.max 1 (Nat.log2 (nch - 1) + 1)
  let chunkE := mkConst (I ++ `T ++ `chunk)
  let wt ← thmP (I ++ `T ++ `tab_ok) (eqTrue (mkAppN (mkConst ``R3RT.tabOKQ) #[mkConst ``L5O.rowE321, chunkE, mkRawNatLit 64,
    mkConst (I ++ `T ++ `N), mkRawNatLit nch])) rflTrue s!"{I} job table"
  let hent := mkLambda `i BinderInfo.default natTy (mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (mkApp tab (mkBVar 0)))
  let hch := mkLambda `q BinderInfo.default natTy (mkLambda `hq BinderInfo.default
    (mkApp2 (mkConst ``LE.le [Level.zero]) natTy (mkConst ``instLENat) |>.app (mkRawNatLit nch) |>.app (mkBVar 0))
    (mkAppN (mkConst ``KB.guard_zero) #[mkConst (I ++ `T ++ Name.mkSimple s!"D{dep}_0"), mkRawNatLit nch, mkBVar 1, mkBVar 0]))
  let wv ← thmP (I ++ `T ++ `valid) (mkApp (mkConst ``KB.TabV321) tab)
    (mkAppN (mkConst ``KB.tabV321_of) #[chunkE, mkConst (I ++ `T ++ `N), mkRawNatLit nch, tab, hent, hch,
      mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (mkRawNatLit nch), rflTrue, mkConst (I ++ `T ++ `tab_ok)]) s!"{I} job table shape"
  logInfo m!"{I}.T: {ntab} rows, tab_ok kernel {wt} ms, shape {wv} ms"

def itemHead (I : Name) (dir : String) (key : Nat) : CommandElabM Unit := do
  itemTable I dir
  let it := KDLoadXB.itemsF (← IO.FS.readBinFile (dir ++ "/head.bin"))
  if it[0]! != 1 then throwError "k321item: item format {it[0]!}"
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
  let nW := it[q+7]!
  let W := (List.range nW).map fun j => it[q + 8 + j]!
  let nE := it[q + 8 + nW]!
  let o := q + 9 + nW
  let extL := (List.range nE).map fun j => (it[o + 2 * j]!, it[o + 2 * j + 1]!)
  let o2 := o + 2 * nE
  let lo := it[o2]!; let nR := it[o2+1]!
  let rs := (List.range nR).map fun j => (it[o2 + 2 + 3 * j]!, it[o2 + 3 + 3 * j]!, it[o2 + 4 + 3 * j]!)
  if o2 + 2 + 3 * nR != it.size then throwError "k321item: {it.size - (o2 + 2 + 3 * nR)} items left over in the head"
  liftCoreM <| defT (I ++ `lo) natTy (mkRawNatLit lo)
  liftCoreM <| defT (I ++ `rngL) lrngTy (mkList rngElTy (rs.map fun (S, l, r) =>
    mkPair (prodTy natTy natTy) natTy (mkPair natTy natTy (mkRawNatLit S) (mkRawNatLit l)) (mkRawNatLit r)))
  liftCoreM <| defT (I ++ `W) lnatE (mlE W)
  liftCoreM <| defT (I ++ `extL) lpairE (mkList (prodTy natTy natTy) (extL.map fun (S, u) => mkPair natTy natTy (mkRawNatLit S) (mkRawNatLit u)))
  let lfrTy := mkApp (mkConst ``List [Level.zero]) frPTy
  liftCoreM <| defT (I ++ `s0) lfrTy (mkList frPTy [mkPair t5E natTy (mkConst (I ++ `f0)) (mkConst (I ++ `pend0))])
  logInfo m!"{I}: root depth {npl + 1}, {W.length} witness rows, {extL.length} external children, bound {lo}, {nR} ranges"

def extE (lo hi : Nat) (tab : Expr) : Expr :=
  mkAppN (mkConst ``KB.ext321KR) #[mkRawNatLit lo, mkRawNatLit hi, mkConst `KI321.c2T, mkConst `KI321.hkT, tab]
def chainArgs (lo hi : Nat) (I : Name) (tab : Expr) : Array Expr := #[extRTy, mkConst ``RT.O321.lpar511, mkConst `KI321.c2T,
  mkConst `KI321.hkT, mkConst `KI.cpT, mkConst (I ++ `extL), mkConst (I ++ `lo), mkConst (I ++ `rngL), extE lo hi tab,
  mkConst ``KB.acc321R, mkConst ``KB.xk321R, mkConst ``KB.rg321R, tab]

/-- batches `k0 .. k1 - 1` (each a kernel check `I.b<k>`), with the record lists `I.n<k>` and the next stacks -/
def itemBatches (I : Name) (dir : String) (lo hi k0 k1 : Nat) : CommandElabM Nat := do
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
      let w ← thmP (I ++ `s0_eq) (mkApp3 (mkConst ``Eq [Level.one]) lfrTy (mkConst (I ++ `s0)) st)
        (mkApp2 (mkConst ``Eq.refl [Level.one]) lfrTy (mkConst (I ++ `s0))) "first stack"
      wsum := wsum + w
    else if !(← getEnv).contains (sName I k) then
      liftCoreM <| defT (sName I k) lfrTy st
    let n := it[q]!; q := q + 1
    let mut recs : Array Expr := #[]
    for _ in [0:n] do
      let (x, q2) ← parseRec T cREPm cREP cDIAG it q
      let (e, q3) ← parseExt it q2
      q := q3
      recs := recs.push (mkPair T.tNode extRTy x e)
    if q != it.size then throwError "k321item: batch {k}: {it.size - q} items left over"
    liftCoreM <| defT (I ++ Name.mkSimple s!"n{k}") lnodeTy (mkList nodeE recs.toList)
    let nxt := if k + 1 < nb then batchFile dir (k + 1) else dir ++ "/fin.bin"
    let (stn, _) := stackAt (KDLoadXB.itemsF (← IO.FS.readBinFile nxt)) 0
    liftCoreM <| defT (sName I (k + 1)) lfrTy stn
    let ty := eqTrue (mkAppN (mkConst ``KD.itemXR' []) ((chainArgs lo hi I tab).push (mkConst (sName I k)) |>.push
      (mkConst (I ++ Name.mkSimple s!"n{k}")) |>.push (mkConst (sName I (k + 1)))))
    let w ← thmP (I ++ Name.mkSimple s!"b{k}") ty rflTrue s!"{I} batch {k}"
    logInfo m!"{I}.b{k}: {n} records, kernel {w} ms"
    wsum := wsum + w
  return wsum

/-- the item's end: chain, root frame, final stack, root label, the key's bound, ranges and external children -/
def itemEnd (I : Name) (lo hi : Nat) : CommandElabM Unit := do
  let tab := mkConst (I ++ `T ++ `entry)
  let nb ← KDLoadXB.litOf (I ++ `nb)
  let sN := mkConst (sName I nb)
  let cA := chainArgs lo hi I tab
  let mut pf := mkAppN (mkConst ``KD.ChainR.nil) (cA.push sN)
  for j in [0:nb] do
    let k := nb - 1 - j
    pf := mkAppN (mkConst ``KD.ChainR.cons) (cA ++ #[mkConst (sName I k), mkConst (sName I (k + 1)), sN,
      mkConst (I ++ Name.mkSimple s!"n{k}"), mkConst (I ++ Name.mkSimple s!"b{k}"), pf])
  let w ← thmP (I ++ `chain) (mkAppN (mkConst ``KD.ChainR) (cA ++ #[mkConst (I ++ `s0), sN])) pf s!"{I} chain"
  let lfrTy := mkApp (mkConst ``List [Level.zero]) frPTy
  liftCoreM <| defT (I ++ `sN) lfrTy sN
  -- the root frame: the fast check (byte popcounts, KB.PcB) is evaluated, rootChk0 follows by KB.rootChk0F_imp (no evaluation)
  let rArgs := #[mkConst ``R22D.T321.CONF1T, mkConst `KI321.c2T, mkConst `KI321.hkT, tab, mkConst (I ++ `pl), mkConst (I ++ `W),
    mkConst (I ++ `lastP), mkConst (I ++ `f0)]
  let wr ← thmP (I ++ `rootF) (eqTrue (mkAppN (mkConst ``KB.rootChk0F) rArgs)) rflTrue s!"{I} root frame"
  let _ ← thmP (I ++ `root) (eqTrue (mkAppN (mkConst ``KB.rootChk0) rArgs))
    (mkAppN (mkConst ``KB.rootChk0F_imp) (rArgs.push (mkConst (I ++ `rootF)))) s!"{I} root frame (rootChk0)"
  let wf ← thmP (I ++ `fin) (eqTrue (mkApp (mkConst ``KD.pendZ) (mkConst (I ++ `sN)))) rflTrue s!"{I} final stack"
  let wp ← thmP (I ++ `hp0) (eqTrue (mkApp2 (mkConst ``Nat.beq) (mkConst (I ++ `pend0))
    (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkConst (I ++ `l0))))) rflTrue s!"{I} root label"
  let pB := mkLambda `p BinderInfo.default rngElTy (mkApp2 (mkConst ``Nat.blt) (mkConst (I ++ `lo))
    (mkApp3 (mkConst ``Prod.snd [Level.zero, Level.zero]) (prodTy natTy natTy) natTy (mkBVar 0)))
  let wl ← thmP (I ++ `hrl) (eqTrue (mkApp3 (mkConst ``KD.allB) rngElTy pB (mkConst (I ++ `rngL)))) rflTrue
    s!"{I} ranges above the bound"
  let ofK := mkApp (mkConst ``R22N.SegI.ofKey) (mkConst (I ++ `key))
  let wlo ← thmP (I ++ `hloK) (mkApp3 (mkConst ``Eq [Level.one]) natTy (mkApp (mkConst ``R22N.SegI.lo) ofK) (mkConst (I ++ `lo)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (mkConst (I ++ `lo))) s!"{I} key bound"
  let wrng ← thmP (I ++ `hrngK) (mkApp3 (mkConst ``Eq [Level.one]) lrngTy (mkApp (mkConst ``R22N.SegI.rng) ofK) (mkConst (I ++ `rngL)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) lrngTy (mkConst (I ++ `rngL))) s!"{I} key ranges"
  let wext ← thmP (I ++ `hextK) (mkApp3 (mkConst ``Eq [Level.one]) lpairE (mkApp (mkConst ``R22N.SegI.ext) ofK) (mkConst (I ++ `extL)))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) lpairE (mkConst (I ++ `extL))) s!"{I} key external children"
  logInfo m!"{I}: chain {w} ms, root frame {wr} ms, final {wf} ms, root label {wp} ms, ranges {wl} ms, key bound {wlo} ms, key ranges {wrng} ms, external children {wext} ms"

def priv (n : Name) : CommandElabM Name := return mkPrivateName (← getEnv) n

elab "#kmHead321 " id:ident p:str key:num : command => do itemHead (← priv id.getId) p.getString key.getNat
elab "#kmB321 " id:ident p:str lo:num hi:num k0:num k1:num : command => do
  let w ← itemBatches (← priv id.getId) p.getString lo.getNat hi.getNat k0.getNat k1.getNat
  logInfo m!"{id.getId}: batches {k0.getNat}..{k1.getNat}: kernel {w} ms"
elab "#kmEnd321 " id:ident lo:num hi:num : command => do itemEnd (← priv id.getId) lo.getNat hi.getNat

/-- a dead-root item: job table, root data, the root's record `I.dk` (a node cut 5 / 6), `I.rootcF` / `I.rootc`, `I.isx`, `I.dkok` -/
def itemDead (I : Name) (dir : String) (key : Nat) : CommandElabM Unit := do
  itemTable I dir
  let tab := mkConst (I ++ `T ++ `entry)
  let it := KDLoadXB.itemsF (← IO.FS.readBinFile (dir ++ "/dead.bin"))
  if it[0]! != 2 then throwError "k321dead: format {it[0]!}"
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
  let (dk, qe) ← parseDKX it (q + 7 + nW)
  if qe != it.size then throwError "k321dead: {it.size - qe} items left over"
  liftCoreM <| defT (I ++ `dk) dkXTy dk
  -- the root's parent frame: the fast check (byte popcounts, KB.PcB) is evaluated; rootChkW follows by KB.rootChkWF_imp
  let rfA := #[mkConst ``R22D.T321.CONF1T, mkConst `KI321.c2T, mkConst `KI321.hkT, tab, mkConst (I ++ `pl), mkConst (I ++ `W),
    mkConst (I ++ `lastP), mkConst (I ++ `f0)]
  let wr ← thmP (I ++ `rootcF) (eqTrue (mkAppN (mkConst ``KB.rootChkWF) rfA)) rflTrue s!"{I} root frame"
  let _ ← thmP (I ++ `rootc) (eqTrue (mkAppN (mkConst ``KB.rootChkW) rfA))
    (mkAppN (mkConst ``KB.rootChkWF_imp) (rfA.push (mkConst (I ++ `rootcF)))) s!"{I} root frame (rootChkW)"
  let _ ← thmP (I ++ `isx) (eqTrue (mkApp (mkConst ``KB.isXcut) (mkConst (I ++ `dk)))) rflTrue s!"{I} node cut 5 / 6"
  let wd ← thmP (I ++ `dkok) (eqTrue (mkAppN (mkConst ``KB.dkidOK) #[mkConst ``RT.O321.lpar511, mkConst `KI321.c2T,
    mkConst `KI321.hkT, mkConst `KI.cpT, tab, mkRawNatLit S0, mkRawNatLit D0, mkRawNatLit N0, mkRawNatLit U0, mkRawNatLit d0,
    mkConst (I ++ `lastP), mkConst (I ++ `dk)])) rflTrue s!"{I} dead root"
  logInfo m!"{I}: dead root (node cut 5 / 6), root frame {wr} ms, record {wd} ms"

elab "#kmDead321 " id:ident p:str key:num : command => do itemDead (← priv id.getId) p.getString key.getNat

/-- the module's checked predicate `KB.CheckedAny321 lo hi` -/
def checkedE (lo hi : Nat) : Expr := mkApp2 (mkConst ``KB.CheckedAny321) (mkRawNatLit lo) (mkRawNatLit hi)

elab "#kmKeys321 " t:ident lo:num hi:num ids:ident* : command => do
  let env ← getEnv
  let (lo, hi) := (lo.getNat, hi.getNat)
  let mut keys : Array Nat := #[]
  let mut pfs : Array Expr := #[]
  for i in ids do
    let I := mkPrivateName env i.getId
    let k ← KDLoadXB.litOf (I ++ `key)
    keys := keys.push k
    let a := mkApp3 (mkConst ``KB.CheckedR321) (mkRawNatLit lo) (mkRawNatLit hi) (mkRawNatLit k)
    let b := mkApp3 (mkConst ``KB.CheckedRoot462) (mkRawNatLit lo) (mkRawNatLit hi) (mkRawNatLit k)
    let c := mkApp3 (mkConst ``KB.CheckedDead321) (mkRawNatLit lo) (mkRawNatLit hi) (mkRawNatLit k)
    let bc := mkApp2 (mkConst ``Or) b c
    -- CheckedAny321 lo hi k = CheckedR321 ∨ (CheckedRoot462 ∨ CheckedDead321); a dead-root item has `I.dkok`
    if env.contains (I ++ `dkok) then
      pfs := pfs.push (mkApp3 (mkConst ``Or.inr) a bc (mkApp3 (mkConst ``Or.inr) b c (mkConst (I ++ `checked))))
    else
      pfs := pfs.push (mkApp3 (mkConst ``Or.inl) a bc (mkConst (I ++ `checked)))
  let P (k : Nat) : Expr := mkApp (checkedE lo hi) (mkRawNatLit k)
  let mut ty := mkConst ``True
  let mut pf := mkConst ``True.intro
  for j in [0:keys.size] do
    let jj := keys.size - 1 - j
    pf := mkApp4 (mkConst ``And.intro) (P keys[jj]!) ty pfs[jj]! pf
    ty := mkApp2 (mkConst ``And) (P keys[jj]!) ty
  let natE := mkConst ``Nat
  let listE := keys.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) natE (mkRawNatLit x) acc) (mkApp (mkConst ``List.nil [.zero]) natE)
  let stmt := mkApp2 (mkConst ``R22N.KeysOK) (checkedE lo hi) listE
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: {keys.size} items of case ({lo}, {hi})"

end KBModItem321
