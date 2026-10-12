module
public import S4.EqF
public meta import Lean.Elab.Command
public meta import S4.PLDrv
public meta import S4.PLDrvM
public meta import S4.PLDrvR
public meta import KMod.Units
/-! # S4.PLDrvRE: split leaves of the reduced walk (`S4.EqF`, equal-first-factor ordering) across modules

`S4.PLDrvR` / `S4.PLDrvRN` for the reduced walk `PL.checkSXRE lt a0` (generator `gen7pc_eqf --eqf --split3`).
FILE (plane lift): `HDRE R Em pts k a0`; (NoDecomp): `HDRNE R a0`; then the PART/SUB lines as `gen7pc --split3`.
* `#plhdr3e Seg "file"` / `#plhdr3ne Seg "file"` (data only): public `Seg.R` (and `Seg.Em`) and the parts' items `Seg.item<j>`.
* `#plpart3e Seg Part "file" j` / `#plpart3ne …`: part `j`; private item records (`PL.subOKLE`, `PL.forestOKE … []`, each its own
  `addDecl`) and the part's own record (`PL.subMainOKRE` / `PL.forestOKE`) over their balanced tree (`PL.STR.okE`); ONE PUBLIC
  theorem `Part.ok : PL.PathsOKRE lt Q a0 Seg.R [Seg.item<j>]` (`KMod.addPub`), lt/Q = `ltW3 pts k`/`QK (leafN R) Em k` or `ltF`/`QT`.
* `#plagg3e Seg "file" Part₀ …` / `#plagg3ne …`: the private main-record theorem `PL.leafSXRE lt a0 Seg.R ([Seg.item0] ++ …) = true`
  and ONE PUBLIC theorem `Seg.ok`: `L479.NoLiftK (S5.leafT Seg.R) (S5.leafN Seg.R) (S6.leafDom6 Seg.R) Seg.Em k`
  (`PL.noLiftK_of_itemsE`) or `S5.NoDecomp (S5.leafT Seg.R) (S5.leafN Seg.R) (S6.leafDom6 Seg.R)` (`PL.noDecomp_of_itemsE`): the
  statements of `S4.PLDrvR` / `S4.PLDrvRN`, so the glue modules are unchanged. -/
public meta section
open Lean Elab Command Meta PL.Drv PL.DrvM PL.DrvR
namespace PL.DrvRE

/-- header: `HDRE R Em pts k a0` (plane) or `HDRNE R a0` (NoDecomp): (R, Em, pts, k, a0, rest) -/
def hdrE (path : String) : IO (Nat × Nat × List Nat × Nat × Nat × List String) := do
  let lines := (← IO.FS.lines path).toList.filter (fun l => !l.isEmpty)
  let h := lines.head!.splitOn " "
  if h.length == 6 && h[0]! == "HDRE" then
    return (hexNat h[1]!, hexNat h[2]!, parseList h[3]!, h[4]!.toNat!, h[5]!.toNat!, lines.tail!)
  else if h.length == 3 && h[0]! == "HDRNE" then
    return (hexNat h[1]!, 0, [], 0, h[2]!.toNat!, lines.tail!)
  else throw (IO.userError "bad header (HDRE R Em pts k a0 | HDRNE R a0)")

/-- balanced tree over `xs[lo:hi]` (hi > lo) of (STR expression, `okE` proof) -/
partial def treeRE (ltE a0E RE : Expr) (xs : Array (Expr × Expr)) (lo hi : Nat) : Expr × Expr :=
  if hi - lo == 1 then xs[lo]!
  else
    let mid := lo + (hi - lo) / 2
    let (ta, pa) := treeRE ltE a0E RE xs lo mid
    let (tb, pb) := treeRE ltE a0E RE xs mid hi
    (mkApp2 (mkConst ``PL.STR.node) ta tb,
     mkApp4 (mkConst ``And.intro) (mkApp4 (mkConst ``PL.STR.okE) ltE a0E RE ta) (mkApp4 (mkConst ``PL.STR.okE) ltE a0E RE tb) pa pb)

def hdrCmd (id : TSyntax `ident) (p : TSyntax `str) (withEm : Bool) : CommandElabM Unit := do
  let (Rv, Emv, _, _, _, rest) ← hdrE p.getString
  let seg := id.getId
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `R, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit Rv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  if withEm then
    liftCoreM <| addDecl (.defnDecl { name := seg ++ `Em, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit Emv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  let mut j : Nat := 0
  for ln in rest do
    if ln.startsWith "PART " then
      let f := ln.splitOn " "
      let itemE := mkItem (toExpr (parsePath f[1]!)) (toExpr f[2]!.toNat!)
      liftCoreM <| addDecl (.defnDecl { name := seg ++ Name.mkSimple s!"item{j}", levelParams := [], type := itemTy, value := itemE, hints := .abbrev, safety := .safe }) (forceExpose := true)
      j := j + 1

elab "#plhdr3e " id:ident p:str : command => hdrCmd id p true
elab "#plhdr3ne " id:ident p:str : command => hdrCmd id p false

/-- one part; `plane`: the plane-lift instance (`ltW3`, `QK`), else NoDecomp (`ltF`, `QT`) -/
def partCmd (sid pid : TSyntax `ident) (p : TSyntax `str) (jn : TSyntax `num) (plane : Bool) : CommandElabM Unit := do
  let t0 ← IO.monoNanosNow
  let (_, _, pts, k, a0, rest) ← hdrE p.getString
  let seg := sid.getId
  let part := pid.getId
  let j := jn.getNat
  let some (pl, subs) := partBlock rest j | throwError "no part {j}"
  let pf := pl.splitOn " "
  unless pf.length == 7 do throwError "bad PART line"
  let ptsE := toExpr pts
  let kE := mkRawNatLit k
  let a0E := mkRawNatLit a0
  let RE := mkConst (seg ++ `R)
  let natT := mkConst ``Nat
  let ltE := if plane then mkApp2 (mkConst ``PL.ltW3) ptsE kE else mkConst ``PL.ltF
  let QE := if plane then mkApp3 (mkConst ``PL.QK) (mkApp (mkConst ``S5.leafN) RE) (mkConst (seg ++ `Em)) kE else mkConst ``PL.QT
  let facts ← if plane then (do let (hnd, hpts) ← planeFacts part ptsE (mkConst (seg ++ `Em)); pure #[hnd, hpts]) else pure #[]
  let pre : Array Expr := if plane then #[ptsE, kE, mkConst (seg ++ `Em), a0E] ++ facts else #[a0E]
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
        let stmt := boolEq (mkAppN (mkConst ``PL.subOKLE) #[ltE, a0E, RE, mkConst pn, mkConst cn])
        let k0 ← IO.monoNanosNow
        liftCoreM <| addDecl (.thmDecl { name := tn, levelParams := [], type := stmt, value := rflTrue })
        kern := kern + ((← IO.monoNanosNow) - k0)
        xs := xs.push (mkApp2 (mkConst ``PL.STR.one) (mkConst pn) (mkConst cn), mkConst tn)
      else
        let (t, sym, cdir, nt, sl, i0) := P.getLast!
        let pn ← addPriv (part ++ Name.mkSimple s!"P{i}") pTy (toExpr P.dropLast)
        let args := #[ltE, a0E, RE, mkConst pn, toExpr t, toExpr sym, toExpr cdir, toExpr nt, toExpr sl, toExpr i0, toExpr c,
          nilItems, mkConst cn]
        let stmt := boolEq (mkAppN (mkConst ``PL.forestOKE) args)
        let k0 ← IO.monoNanosNow
        liftCoreM <| addDecl (.thmDecl { name := tn, levelParams := [], type := stmt, value := rflTrue })
        kern := kern + ((← IO.monoNanosNow) - k0)
        xs := xs.push (mkAppN (mkConst ``PL.STR.rng) #[mkConst pn, toExpr t, toExpr sym, toExpr cdir, toExpr nt, toExpr sl, toExpr i0,
          toExpr c, mkConst cn], mkConst tn)
        nrng := nrng + 1
      i := i + 1
    | _ => throwError s!"bad SUB line {i}"
  let (psE, hsubE) :=
    if xs.isEmpty then (nilItems, mkAppN (mkConst ``PL.pathsOKRE_nil) #[ltE, QE, a0E, RE])
    else
      let (t, okp) := treeRE ltE a0E RE xs 0 xs.size
      (mkApp (mkConst ``PL.STR.items) t,
       mkAppN (mkConst (if plane then ``PL.pathsOKRE_of_strW3 else ``PL.pathsOKRE_of_strF)) (pre ++ #[RE, t, okp]))
  let P := parsePath pf[1]!
  let c := pf[2]!.toNat!
  let mcn ← addPriv (part ++ `cm) natT (mkRawNatLit (hexNat pf[3]!))
  let smn := mkPrivateName (← getEnv) (part ++ `tsm)
  let ty := mkAppN (mkConst ``PL.PathsOKRE) #[ltE, QE, a0E, RE, singItem (mkConst (seg ++ Name.mkSimple s!"item{j}"))]
  let k1 ← IO.monoNanosNow
  let prf ← if c == 0 then do
      let ppn ← addPriv (part ++ `pP) pTy (toExpr P)
      let st := boolEq (mkAppN (mkConst ``PL.subMainOKRE) #[ltE, a0E, RE, mkConst ppn, psE, mkConst mcn])
      liftCoreM <| addDecl (.thmDecl { name := smn, levelParams := [], type := st, value := rflTrue })
      pure (mkAppN (mkConst (if plane then ``PL.pathsOKRE_of_submainW3 else ``PL.pathsOKRE_of_submainF))
        (pre ++ #[RE, mkConst ppn, psE, mkConst mcn, mkConst smn, hsubE]))
    else do
      let (t, sym, cdir, nt, sl, i0) := P.getLast!
      let ppn ← addPriv (part ++ `pP) pTy (toExpr P.dropLast)
      let args := #[mkConst ppn, toExpr t, toExpr sym, toExpr cdir, toExpr nt, toExpr sl, toExpr i0, toExpr c, psE, mkConst mcn]
      let st := boolEq (mkAppN (mkConst ``PL.forestOKE) (#[ltE, a0E, RE] ++ args))
      liftCoreM <| addDecl (.thmDecl { name := smn, levelParams := [], type := st, value := rflTrue })
      pure (mkAppN (mkConst (if plane then ``PL.pathsOKRE_of_forestW3 else ``PL.pathsOKRE_of_forestF))
        (pre ++ #[RE] ++ args ++ #[mkConst smn, hsubE]))
  let dsm := (← IO.monoNanosNow) - k1
  KMod.addPub (part ++ `ok) ty prf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plpart3e {part}: {xs.size} item records ({nrng} ranges); kernel {kern / 1000000} ms; part record {dsm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

elab "#plpart3e " sid:ident pid:ident p:str jn:num : command => partCmd sid pid p jn true
elab "#plpart3ne " sid:ident pid:ident p:str jn:num : command => partCmd sid pid p jn false

def aggCmd (sid : TSyntax `ident) (p : TSyntax `str) (parts : Array (TSyntax `ident)) (plane : Bool) : CommandElabM Unit := do
  let t0 ← IO.monoNanosNow
  let (_, _, pts, k, a0, _) ← hdrE p.getString
  let seg := sid.getId
  let ptsE := toExpr pts
  let kE := mkRawNatLit k
  let a0E := mkRawNatLit a0
  let RE := mkConst (seg ++ `R)
  let ltE := if plane then mkApp2 (mkConst ``PL.ltW3) ptsE kE else mkConst ``PL.ltF
  let QE := if plane then mkApp3 (mkConst ``PL.QK) (mkApp (mkConst ``S5.leafN) RE) (mkConst (seg ++ `Em)) kE else mkConst ``PL.QT
  let ps := parts.map (·.getId)
  let sing (j : Nat) : Expr := singItem (mkConst (seg ++ Name.mkSimple s!"item{j}"))
  let mut itemsE := if ps.isEmpty then nilItems else sing (ps.size - 1)
  let mut okE := if ps.isEmpty then mkAppN (mkConst ``PL.pathsOKRE_nil) #[ltE, QE, a0E, RE] else mkConst (ps.back! ++ `ok)
  for j in (List.range (ps.size - 1)).reverse do
    okE := mkAppN (mkConst ``PL.pathsOKRE_append) #[ltE, QE, a0E, RE, sing j, itemsE, mkConst (ps[j]! ++ `ok), okE]
    itemsE := appendItems (sing j) itemsE
  let tmn := mkPrivateName (← getEnv) (seg ++ `tm)
  let k0 ← IO.monoNanosNow
  liftCoreM <| addDecl (.thmDecl { name := tmn, levelParams := [], type := boolEq (mkAppN (mkConst ``PL.leafSXRE) #[ltE, a0E, RE, itemsE]), value := rflTrue })
  let dm := (← IO.monoNanosNow) - k0
  if plane then
    let EmE := mkConst (seg ++ `Em)
    let (hnd, hpts) ← planeFacts seg ptsE EmE
    let ty := mkApp5 (mkConst ``L479.NoLiftK) (mkApp (mkConst ``S5.leafT) RE) (mkApp (mkConst ``S5.leafN) RE)
      (mkApp (mkConst ``S6.leafDom6) RE) EmE kE
    let pf := mkAppN (mkConst ``PL.noLiftK_of_itemsE) #[ptsE, kE, EmE, a0E, hnd, hpts, RE, itemsE, mkConst tmn, okE]
    KMod.addPub (seg ++ `ok) ty pf
  else
    let ty := mkApp3 (mkConst ``S5.NoDecomp) (mkApp (mkConst ``S5.leafT) RE) (mkApp (mkConst ``S5.leafN) RE)
      (mkApp (mkConst ``S6.leafDom6) RE)
    let pf := mkAppN (mkConst ``PL.noDecomp_of_itemsE) #[a0E, RE, itemsE, mkConst tmn, okE]
    KMod.addPub (seg ++ `ok) ty pf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plagg3e {seg}: {ps.size} parts; main {dm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

elab "#plagg3e " sid:ident p:str parts:ident* : command => aggCmd sid p parts true
elab "#plagg3ne " sid:ident p:str parts:ident* : command => aggCmd sid p parts false

end PL.DrvRE
