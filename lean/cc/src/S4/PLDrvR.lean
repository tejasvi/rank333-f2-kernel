module
public import S4.SplitR
public meta import Lean.Elab.Command
public meta import S4.PLDrv
public meta import S4.PLDrvM
public meta import KMod.Units
/-! # S4.PLDrvR: a split leaf with sibling ranges across modules (`gen7pc --split3`)

FILE: `HDR R Em pts k`, then for each part a line `PART path c hex nbits nsat nsub` (the part's item: the path to its first
child and the count `c`, 0 for a subtree; its record in hex) followed by its `SUB path c hex nbits nsat` lines (the part's items,
in record order). Paths as `gen7pc`: `;`-separated steps `t:sym:cdir:NT:SL:i`.
* `#plhdr3 Seg "file"` (header module, data only): public `Seg.R`, `Seg.Em` and the parts' items `Seg.item<j> : PL.Item`.
* `#plpart3 Seg Part "file" j` (imports the header): part `j`. PRIVATE item records, each its own `addDecl`: `PL.subOKL` for a
  subtree item, `PL.forestOK … []` for a range item; the part's own record (`PL.subMainOKR` for a subtree part, `PL.forestOK` for
  a range part) over the balanced tree (`PL.STR`) of its items; ONE PUBLIC theorem
  `Part.ok : PL.PathsOKR (PL.ltW3 pts k) (PL.QK (S5.leafN Seg.R) Seg.Em k) Seg.R [Seg.item<j>]` (`KMod.addPub`).
* `#plagg3 Seg "file" Part₀ … Partₘ₋₁` (the parts in file order): the private main-record theorem
  `PL.leafSXR (PL.ltW3 pts k) Seg.R ([Seg.item0] ++ …) = true` and ONE PUBLIC theorem
  `Seg.ok : L479.NoLiftK (S5.leafT Seg.R) (S5.leafN Seg.R) (S6.leafDom6 Seg.R) Seg.Em k` (`PL.noLiftK_of_items`). -/
public meta section
open Lean Elab Command Meta PL.Drv PL.DrvM
namespace PL.DrvR

def itemTy : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) pTy (mkConst ``Nat)
def itemsTy : Expr := mkApp (mkConst ``List [Level.zero]) itemTy
def mkItem (P c : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) pTy (mkConst ``Nat) P c
def nilItems : Expr := mkApp (mkConst ``List.nil [Level.zero]) itemTy
def singItem (a : Expr) : Expr := mkApp3 (mkConst ``List.cons [Level.zero]) itemTy a nilItems
def appendItems (a b : Expr) : Expr := mkApp6 (mkConst ``HAppend.hAppend [Level.zero, Level.zero, Level.zero]) itemsTy itemsTy
  itemsTy (mkApp2 (mkConst ``instHAppendOfAppend [Level.zero]) itemsTy (mkApp (mkConst ``List.instAppend [Level.zero]) itemTy)) a b

/-- balanced tree over `xs[lo:hi]` (hi > lo) of (STR expression, `ok` proof) -/
partial def treeR (ltE RE : Expr) (xs : Array (Expr × Expr)) (lo hi : Nat) : Expr × Expr :=
  if hi - lo == 1 then xs[lo]!
  else
    let mid := lo + (hi - lo) / 2
    let (ta, pa) := treeR ltE RE xs lo mid
    let (tb, pb) := treeR ltE RE xs mid hi
    (mkApp2 (mkConst ``PL.STR.node) ta tb,
     mkApp4 (mkConst ``And.intro) (mkApp3 (mkConst ``PL.STR.ok) ltE RE ta) (mkApp3 (mkConst ``PL.STR.ok) ltE RE tb) pa pb)

def addPriv (n : Name) (ty v : Expr) : CommandElabM Name := do
  let pn := mkPrivateName (← getEnv) n
  liftCoreM <| addDecl (.defnDecl { name := pn, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe })
  return pn

elab "#plhdr3 " id:ident p:str : command => do
  let (Rv, Emv, _, _, rest) ← hdrOf p.getString
  let seg := id.getId
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `R, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit Rv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `Em, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit Emv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  let mut j : Nat := 0
  for ln in rest do
    if ln.startsWith "PART " then
      let f := ln.splitOn " "
      let itemE := mkItem (toExpr (parsePath f[1]!)) (toExpr f[2]!.toNat!)
      liftCoreM <| addDecl (.defnDecl { name := seg ++ Name.mkSimple s!"item{j}", levelParams := [], type := itemTy, value := itemE, hints := .abbrev, safety := .safe }) (forceExpose := true)
      j := j + 1

elab "#plpart3 " sid:ident pid:ident p:str jn:num : command => do
  let t0 ← IO.monoNanosNow
  let (_, _, pts, k, rest) ← hdrOf p.getString
  let seg := sid.getId
  let part := pid.getId
  let j := jn.getNat
  let some (pl, subs) := partBlock rest j | throwError "no part {j}"
  let pf := pl.splitOn " "
  unless pf.length == 7 do throwError "bad PART line"
  let ptsE := toExpr pts
  let kE := mkRawNatLit k
  let ltE := mkApp2 (mkConst ``PL.ltW3) ptsE kE
  let RE := mkConst (seg ++ `R)
  let EmE := mkConst (seg ++ `Em)
  let natT := mkConst ``Nat
  let QE := mkApp3 (mkConst ``PL.QK) (mkApp (mkConst ``S5.leafN) RE) EmE kE
  let (hnd, hpts) ← planeFacts part ptsE EmE
  let mut xs : Array (Expr × Expr) := #[]
  let mut kern : Nat := 0
  let mut i : Nat := 0
  let mut nrng : Nat := 0
  for ln in subs do
    match ln.splitOn " " with
    | ["SUB", path, cs, hx, _nb, _ns] =>
      let P := parsePath path
      let c := cs.toNat!
      let cn ← addPriv (part ++ Name.mkSimple s!"c{i}") natT (mkRawNatLit (hexNat hx))
      let tn := mkPrivateName (← getEnv) (part ++ Name.mkSimple s!"t{i}")
      if c == 0 then
        let pn ← addPriv (part ++ Name.mkSimple s!"P{i}") pTy (toExpr P)
        let stmt := boolEq (mkApp4 (mkConst ``PL.subOKL) ltE RE (mkConst pn) (mkConst cn))
        let k0 ← IO.monoNanosNow
        liftCoreM <| addDecl (.thmDecl { name := tn, levelParams := [], type := stmt, value := rflTrue })
        kern := kern + ((← IO.monoNanosNow) - k0)
        xs := xs.push (mkApp2 (mkConst ``PL.STR.one) (mkConst pn) (mkConst cn), mkConst tn)
      else
        let (t, sym, cdir, nt, sl, i0) := P.getLast!
        let pn ← addPriv (part ++ Name.mkSimple s!"P{i}") pTy (toExpr P.dropLast)
        let args := #[ltE, RE, mkConst pn, toExpr t, toExpr sym, toExpr cdir, toExpr nt, toExpr sl, toExpr i0, toExpr c, nilItems,
          mkConst cn]
        let stmt := boolEq (mkAppN (mkConst ``PL.forestOK) args)
        let k0 ← IO.monoNanosNow
        liftCoreM <| addDecl (.thmDecl { name := tn, levelParams := [], type := stmt, value := rflTrue })
        kern := kern + ((← IO.monoNanosNow) - k0)
        xs := xs.push (mkAppN (mkConst ``PL.STR.rng) #[mkConst pn, toExpr t, toExpr sym, toExpr cdir, toExpr nt, toExpr sl, toExpr i0,
          toExpr c, mkConst cn], mkConst tn)
        nrng := nrng + 1
      i := i + 1
    | _ => throwError s!"bad SUB line {i}"
  let (psE, hsubE) :=
    if xs.isEmpty then (nilItems, mkAppN (mkConst ``PL.pathsOKR_nil) #[ltE, QE, RE])
    else
      let (t, okp) := treeR ltE RE xs 0 xs.size
      (mkApp (mkConst ``PL.STR.items) t, mkAppN (mkConst ``PL.pathsOKR_of_strW3) #[ptsE, kE, EmE, hnd, hpts, RE, t, okp])
  let P := parsePath pf[1]!
  let c := pf[2]!.toNat!
  let mcn ← addPriv (part ++ `cm) natT (mkRawNatLit (hexNat pf[3]!))
  let smn := mkPrivateName (← getEnv) (part ++ `tsm)
  let ty := mkApp4 (mkConst ``PL.PathsOKR) ltE QE RE (singItem (mkConst (seg ++ Name.mkSimple s!"item{j}")))
  let k1 ← IO.monoNanosNow
  let prf ← if c == 0 then do
      let ppn ← addPriv (part ++ `pP) pTy (toExpr P)
      let st := boolEq (mkAppN (mkConst ``PL.subMainOKR) #[ltE, RE, mkConst ppn, psE, mkConst mcn])
      liftCoreM <| addDecl (.thmDecl { name := smn, levelParams := [], type := st, value := rflTrue })
      pure (mkAppN (mkConst ``PL.pathsOKR_of_submainW3) #[ptsE, kE, EmE, hnd, hpts, RE, mkConst ppn, psE, mkConst mcn, mkConst smn, hsubE])
    else do
      let (t, sym, cdir, nt, sl, i0) := P.getLast!
      let ppn ← addPriv (part ++ `pP) pTy (toExpr P.dropLast)
      let args := #[mkConst ppn, toExpr t, toExpr sym, toExpr cdir, toExpr nt, toExpr sl, toExpr i0, toExpr c, psE, mkConst mcn]
      let st := boolEq (mkAppN (mkConst ``PL.forestOK) (#[ltE, RE] ++ args))
      liftCoreM <| addDecl (.thmDecl { name := smn, levelParams := [], type := st, value := rflTrue })
      pure (mkAppN (mkConst ``PL.pathsOKR_of_forestW3) (#[ptsE, kE, EmE, hnd, hpts, RE] ++ args ++ #[mkConst smn, hsubE]))
  let dsm := (← IO.monoNanosNow) - k1
  KMod.addPub (part ++ `ok) ty prf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plpart3 {part}: {xs.size} item records ({nrng} ranges); kernel {kern / 1000000} ms; part record {dsm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

elab "#plagg3 " sid:ident p:str parts:ident* : command => do
  let t0 ← IO.monoNanosNow
  let (_, _, pts, k, _) ← hdrOf p.getString
  let seg := sid.getId
  let ptsE := toExpr pts
  let kE := mkRawNatLit k
  let ltE := mkApp2 (mkConst ``PL.ltW3) ptsE kE
  let RE := mkConst (seg ++ `R)
  let EmE := mkConst (seg ++ `Em)
  let QE := mkApp3 (mkConst ``PL.QK) (mkApp (mkConst ``S5.leafN) RE) EmE kE
  let ps := parts.map (·.getId)
  let sing (j : Nat) : Expr := singItem (mkConst (seg ++ Name.mkSimple s!"item{j}"))
  let mut itemsE := if ps.isEmpty then nilItems else sing (ps.size - 1)
  let mut okE := if ps.isEmpty then mkAppN (mkConst ``PL.pathsOKR_nil) #[ltE, QE, RE] else mkConst (ps.back! ++ `ok)
  for j in (List.range (ps.size - 1)).reverse do
    okE := mkAppN (mkConst ``PL.pathsOKR_append) #[ltE, QE, RE, sing j, itemsE, mkConst (ps[j]! ++ `ok), okE]
    itemsE := appendItems (sing j) itemsE
  let tmn := mkPrivateName (← getEnv) (seg ++ `tm)
  let k0 ← IO.monoNanosNow
  liftCoreM <| addDecl (.thmDecl { name := tmn, levelParams := [], type := boolEq (mkApp3 (mkConst ``PL.leafSXR) ltE RE itemsE), value := rflTrue })
  let dm := (← IO.monoNanosNow) - k0
  let (hnd, hpts) ← planeFacts seg ptsE EmE
  let ty := mkApp5 (mkConst ``L479.NoLiftK) (mkApp (mkConst ``S5.leafT) RE) (mkApp (mkConst ``S5.leafN) RE)
    (mkApp (mkConst ``S6.leafDom6) RE) EmE kE
  let pf := mkAppN (mkConst ``PL.noLiftK_of_items) #[ptsE, kE, EmE, hnd, hpts, RE, itemsE, mkConst tmn, okE]
  KMod.addPub (seg ++ `ok) ty pf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plagg3 {seg}: {ps.size} parts; main {dm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

end PL.DrvR
