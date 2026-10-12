module
public import S4.SplitRN
public meta import Lean.Elab.Command
public meta import S4.PLDrv
public meta import S4.PLDrvM
public meta import S4.PLDrvR
public meta import KMod.Units
/-! # S4.PLDrvRN: an UNSAT split leaf with sibling ranges across modules, `S5.NoDecomp` (`gen7pc --split3`, no `--plane`)

As `S4.PLDrvR`, with the leaf test `PL.ltF` (no SAT leaf) and the invariant `PL.QT` (`S4.SplitRN`).
FILE: `HDRN R` (the leaf record with the main certificate, hex), then for each part a line `PART path c hex nbits nsat nsub`
followed by its `SUB path c hex nbits nsat` lines (as `gen7pc --split3`).
* `#plhdr3n Seg "file"` (header module, data only): public `Seg.R` and the parts' items `Seg.item<j> : PL.Item`.
* `#plpart3n Seg Part "file" j` (imports the header): part `j`; private item records (`PL.subOKL` / `PL.forestOK … []`, each its
  own `addDecl`) and the part's own record (`PL.subMainOKR` / `PL.forestOK`) over their balanced tree; ONE PUBLIC theorem
  `Part.ok : PL.PathsOKR PL.ltF PL.QT Seg.R [Seg.item<j>]` (`KMod.addPub`).
* `#plagg3n Seg "file" Part₀ … Partₘ₋₁`: the private main-record theorem `PL.leafSXR PL.ltF Seg.R ([Seg.item0] ++ …) = true`
  and ONE PUBLIC theorem `Seg.ok : S5.NoDecomp (S5.leafT Seg.R) (S5.leafN Seg.R) (S6.leafDom6 Seg.R)`
  (`PL.noDecomp_of_items`). -/
public meta section
open Lean Elab Command Meta PL.Drv PL.DrvM PL.DrvR
namespace PL.DrvRN

def hdrN (path : String) : IO (Nat × List String) := do
  let lines := (← IO.FS.lines path).toList.filter (fun l => !l.isEmpty)
  let hdr := lines.head!.splitOn " "
  unless hdr.length == 2 && hdr[0]! == "HDRN" do throw (IO.userError "bad header (HDRN R)")
  return (hexNat hdr[1]!, lines.tail!)

elab "#plhdr3n " id:ident p:str : command => do
  let (Rv, rest) ← hdrN p.getString
  let seg := id.getId
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `R, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit Rv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  let mut j : Nat := 0
  for ln in rest do
    if ln.startsWith "PART " then
      let f := ln.splitOn " "
      let itemE := mkItem (toExpr (parsePath f[1]!)) (toExpr f[2]!.toNat!)
      liftCoreM <| addDecl (.defnDecl { name := seg ++ Name.mkSimple s!"item{j}", levelParams := [], type := itemTy, value := itemE, hints := .abbrev, safety := .safe }) (forceExpose := true)
      j := j + 1

elab "#plpart3n " sid:ident pid:ident p:str jn:num : command => do
  let t0 ← IO.monoNanosNow
  let (_, rest) ← hdrN p.getString
  let seg := sid.getId
  let part := pid.getId
  let j := jn.getNat
  let some (pl, subs) := partBlock rest j | throwError "no part {j}"
  let pf := pl.splitOn " "
  unless pf.length == 7 do throwError "bad PART line"
  let ltE := mkConst ``PL.ltF
  let QE := mkConst ``PL.QT
  let RE := mkConst (seg ++ `R)
  let natT := mkConst ``Nat
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
      (mkApp (mkConst ``PL.STR.items) t, mkAppN (mkConst ``PL.pathsOKR_of_strF) #[RE, t, okp])
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
      pure (mkAppN (mkConst ``PL.pathsOKR_of_submainF) #[RE, mkConst ppn, psE, mkConst mcn, mkConst smn, hsubE])
    else do
      let (t, sym, cdir, nt, sl, i0) := P.getLast!
      let ppn ← addPriv (part ++ `pP) pTy (toExpr P.dropLast)
      let args := #[mkConst ppn, toExpr t, toExpr sym, toExpr cdir, toExpr nt, toExpr sl, toExpr i0, toExpr c, psE, mkConst mcn]
      let st := boolEq (mkAppN (mkConst ``PL.forestOK) (#[ltE, RE] ++ args))
      liftCoreM <| addDecl (.thmDecl { name := smn, levelParams := [], type := st, value := rflTrue })
      pure (mkAppN (mkConst ``PL.pathsOKR_of_forestF) (#[RE] ++ args ++ #[mkConst smn, hsubE]))
  let dsm := (← IO.monoNanosNow) - k1
  KMod.addPub (part ++ `ok) ty prf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plpart3n {part}: {xs.size} item records ({nrng} ranges); kernel {kern / 1000000} ms; part record {dsm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

elab "#plagg3n " sid:ident p:str parts:ident* : command => do
  let t0 ← IO.monoNanosNow
  let _ ← hdrN p.getString
  let seg := sid.getId
  let ltE := mkConst ``PL.ltF
  let QE := mkConst ``PL.QT
  let RE := mkConst (seg ++ `R)
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
  let ty := mkApp3 (mkConst ``S5.NoDecomp) (mkApp (mkConst ``S5.leafT) RE) (mkApp (mkConst ``S5.leafN) RE)
    (mkApp (mkConst ``S6.leafDom6) RE)
  let pf := mkAppN (mkConst ``PL.noDecomp_of_items) #[RE, itemsE, mkConst tmn, okE]
  KMod.addPub (seg ++ `ok) ty pf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plagg3n {seg}: {ps.size} parts; main {dm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

end PL.DrvRN
