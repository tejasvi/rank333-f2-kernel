module
public import S4.SplitQ
public meta import Lean.Elab.Command
public meta import S4.PLDrv
public meta import KMod.Units
/-! # S4.PLDrvM: a giant split SAT leaf across modules (header, parts, aggregator)

* `#plhdr Seg "file"` (header module, data only): public `Seg.R` and `Seg.Em` from the `HDR` line, and the nested form's part
  paths `Seg.path<j>` (the file's PART lines, in order).
* `#plpart Seg Part "file" lo hi` (part module, imports the header): sub-records `lo ≤ k < hi` of the file. PUBLIC paths
  `Part.P_k` and `Part.paths`; PRIVATE certificates and theorems `subOKL … = true` (each its own `addDecl`); ONE PUBLIC theorem
  `Part.ok : PL.PathsOK (PL.ltW3 pts 3) (PL.QK (S5.leafN Seg.R) Seg.Em 3) Seg.R Part.paths` (`PL.pathsOK_of_treeW3`).
* `#plagg Seg "file" Part₁ … Partₘ` (aggregator, imports the parts): the private main-record theorem over
  `Part₁.paths ++ … ++ Partₘ.paths` and ONE PUBLIC theorem `Seg.ok : L479.NoLiftK (S5.leafT Seg.R) (S5.leafN Seg.R)
  (S6.leafDom6 Seg.R) Seg.Em 3` (`PL.noLiftK_of_paths`, `PL.pathsOK_append`).
* `#plpart2 Seg Part "file" j` / `#plagg2 Seg "file" Part₁ … Partₘ`: the nested form. Part j of the file has its own sub-main
  record (`PL.subMainOK`, private) over its sub-records and ONE PUBLIC theorem `Part.ok : PL.PathsOK … Seg.R [Seg.path<j>]`
  (`PL.pathsOK_of_submainW3`); the aggregator checks the small main record over `[Seg.path0, …]` (parts given in file order) and joins
  the parts into `Seg.ok` as above. Zero parts (a leaf without SAT leaves) give the empty path list (`PL.pathsOK_nil`).
Every public theorem is added by `KMod.addPub` (synchronous, logged as `KPUB`); run `#kax` on it (KMod.Audit) for the module's
manifest. A part or aggregator module exports only its theorem (all shared data is in the header), as `kmod_audit.py` requires;
the older `#plpart`/`#plagg` export their paths from the part and do not pass that rule. -/
public meta section
open Lean Elab Command Meta PL.Drv
namespace PL.DrvM

def hdrOf (path : String) : IO (Nat × Nat × List Nat × Nat × List String) := do
  let lines := (← IO.FS.lines path).toList.filter (fun l => !l.isEmpty)
  let hdr := lines.head!.splitOn " "
  unless hdr.length == 5 && hdr[0]! == "HDR" do throw (IO.userError "bad header")
  return (hexNat hdr[1]!, hexNat hdr[2]!, parseList hdr[3]!, hdr[4]!.toNat!, lines.tail!)

def stepTy : Expr := toTypeExpr (Nat × Bool × Bool × List Nat × List Nat × Nat)
def pTy : Expr := mkApp (mkConst ``List [Level.zero]) stepTy
def plistTy : Expr := mkApp (mkConst ``List [Level.zero]) pTy

elab "#plhdr " id:ident p:str : command => do
  let (Rv, Emv, _, _, rest) ← hdrOf p.getString
  let seg := id.getId
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `R, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit Rv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `Em, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit Emv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  -- the nested form's part paths (PART lines, in order): data of the header, so a part module exports only its theorem
  let mut j : Nat := 0
  for ln in rest do
    if ln.startsWith "PART " then
      let f := ln.splitOn " "
      liftCoreM <| addDecl (.defnDecl { name := seg ++ Name.mkSimple s!"path{j}", levelParams := [], type := pTy, value := toExpr (parsePath f[1]!), hints := .abbrev, safety := .safe }) (forceExpose := true)
      j := j + 1

def planeFacts (seg : Name) (ptsE EmE : Expr) : CommandElabM (Expr × Expr) := do
  let hn1 ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ `hnd) |> pure
  liftCoreM <| addDecl (.thmDecl { name := hn1, levelParams := [], type := boolEq (mkApp (mkConst ``PL.nodupB) ptsE), value := rflTrue })
  let hp1 ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ `hpts) |> pure
  liftCoreM <| addDecl (.thmDecl { name := hp1, levelParams := [], type := boolEq (mkApp2 (mkConst ``PL.ptsOKB) ptsE EmE), value := rflTrue })
  return (mkApp2 (mkConst ``PL.nodupB_spec) ptsE (mkConst hn1), mkApp3 (mkConst ``PL.ptsOKB_spec) ptsE EmE (mkConst hp1))

elab "#plpart " sid:ident pid:ident p:str lo:num hi:num : command => do
  let t0 ← IO.monoNanosNow
  let (_, _, pts, k, subs) ← hdrOf p.getString
  let seg := sid.getId
  let part := pid.getId
  let ptsE := toExpr pts
  let kE := mkRawNatLit k
  let ltE := mkApp2 (mkConst ``PL.ltW3) ptsE kE
  let RE := mkConst (seg ++ `R)
  let EmE := mkConst (seg ++ `Em)
  let natT := mkConst ``Nat
  let mut xs : Array (Expr × Expr × Expr) := #[]
  let mut kern : Nat := 0
  for i in [lo.getNat:hi.getNat] do
    match (subs[i]!).splitOn " " with
    | ["SUB", path, hx, _nb, _ns] =>
      let pn := part ++ Name.mkSimple s!"P{i}"
      liftCoreM <| addDecl (.defnDecl { name := pn, levelParams := [], type := pTy, value := toExpr (parsePath path), hints := .abbrev, safety := .safe }) (forceExpose := true)
      let cn ← liftCoreM <| mkPrivateName (← getEnv) (part ++ Name.mkSimple s!"c{i}") |> pure
      liftCoreM <| addDecl (.defnDecl { name := cn, levelParams := [], type := natT, value := mkRawNatLit (hexNat hx), hints := .abbrev, safety := .safe })
      let tn ← liftCoreM <| mkPrivateName (← getEnv) (part ++ Name.mkSimple s!"t{i}") |> pure
      let stmt := boolEq (mkApp4 (mkConst ``PL.subOKL) ltE RE (mkConst pn) (mkConst cn))
      let k0 ← IO.monoNanosNow
      liftCoreM <| addDecl (.thmDecl { name := tn, levelParams := [], type := stmt, value := rflTrue })
      kern := kern + ((← IO.monoNanosNow) - k0)
      xs := xs.push (mkConst pn, mkConst cn, mkConst tn)
    | _ => throwError s!"bad sub-record line {i}"
  if xs.isEmpty then throwError "no sub-records"
  let (t, okp) := tree ltE RE xs 0 xs.size
  let pathsV := xs.toList.map (·.1)
  liftCoreM <| addDecl (.defnDecl { name := part ++ `paths, levelParams := [], type := plistTy, value := (pathsV.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) pTy a acc) (mkApp (mkConst ``List.nil [Level.zero]) pTy)), hints := .abbrev, safety := .safe }) (forceExpose := true)
  let (hnd, hpts) ← planeFacts part ptsE EmE
  let QE := mkApp3 (mkConst ``PL.QK) (mkApp (mkConst ``S5.leafN) RE) EmE kE
  let ty := mkApp4 (mkConst ``PL.PathsOK) ltE QE RE (mkConst (part ++ `paths))
  let pf := mkAppN (mkConst ``PL.pathsOK_of_treeW3) #[ptsE, kE, EmE, hnd, hpts, RE, t, okp]
  KMod.addPub (part ++ `ok) ty pf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plpart {part}: {xs.size} sub-records; kernel {kern / 1000000} ms; total {(t1 - t0) / 1000000} ms"

elab "#plagg " sid:ident p:str parts:ident* : command => do
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
  let appendE (a b : Expr) : Expr := mkApp4 (mkConst ``HAppend.hAppend [Level.zero, Level.zero, Level.zero]) plistTy plistTy plistTy
    (mkApp2 (mkConst ``instHAppendOfAppend [Level.zero]) plistTy (mkApp (mkConst ``List.instAppend [Level.zero]) pTy)) |> fun f => mkApp2 f a b
  -- right-nested: p1 ++ (p2 ++ (… ++ pm)); no parts (a leaf without SAT leaves): the empty path list, `PL.pathsOK_nil`
  let mut pathsE := if ps.isEmpty then mkApp (mkConst ``List.nil [Level.zero]) pTy else mkConst (ps.back! ++ `paths)
  let mut okE := if ps.isEmpty then mkAppN (mkConst ``PL.pathsOK_nil) #[ltE, QE, RE] else mkConst (ps.back! ++ `ok)
  for j in (List.range (ps.size - 1)).reverse do
    let pj := ps[j]!
    okE := mkAppN (mkConst ``PL.pathsOK_append) #[ltE, QE, RE, mkConst (pj ++ `paths), pathsE, mkConst (pj ++ `ok), okE]
    pathsE := appendE (mkConst (pj ++ `paths)) pathsE
  let tmn ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ `tm) |> pure
  let k0 ← IO.monoNanosNow
  liftCoreM <| addDecl (.thmDecl { name := tmn, levelParams := [], type := boolEq (mkApp3 (mkConst ``PL.leafSXL) ltE RE pathsE), value := rflTrue })
  let dm := (← IO.monoNanosNow) - k0
  let (hnd, hpts) ← planeFacts seg ptsE EmE
  let ty := mkApp5 (mkConst ``L479.NoLiftK) (mkApp (mkConst ``S5.leafT) RE) (mkApp (mkConst ``S5.leafN) RE)
    (mkApp (mkConst ``S6.leafDom6) RE) EmE kE
  let pf := mkAppN (mkConst ``PL.noLiftK_of_paths) #[ptsE, kE, EmE, hnd, hpts, RE, pathsE, mkConst tmn, okE]
  KMod.addPub (seg ++ `ok) ty pf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plagg {seg}: {ps.size} parts; main {dm / 1000000} ms; total {(t1 - t0) / 1000000} ms"


/-- the lines of nested part `j`: its PART line and its SUB lines -/
def partBlock (lines : List String) (j : Nat) : Option (String × List String) := Id.run do
  let mut cur : Nat := 0
  let mut found : Option String := none
  let mut subs : Array String := #[]
  for ln in lines do
    if ln.startsWith "PART " then
      if found.isSome then break
      if cur == j then found := some ln
      cur := cur + 1
    else if ln.startsWith "SUB " && found.isSome then subs := subs.push ln
  return found.map (fun f => (f, subs.toList))

elab "#plpart2 " sid:ident pid:ident p:str jn:num : command => do
  let t0 ← IO.monoNanosNow
  let (_, _, pts, k, rest) ← hdrOf p.getString
  let seg := sid.getId
  let part := pid.getId
  let some (pl, subs) := partBlock rest jn.getNat | throwError "no part {jn.getNat}"
  let pf := pl.splitOn " "
  let ptsE := toExpr pts
  let kE := mkRawNatLit k
  let ltE := mkApp2 (mkConst ``PL.ltW3) ptsE kE
  let RE := mkConst (seg ++ `R)
  let EmE := mkConst (seg ++ `Em)
  let natT := mkConst ``Nat
  let pathC := mkConst (seg ++ Name.mkSimple s!"path{jn.getNat}")   -- the header's copy of this part's path
  let mcn ← liftCoreM <| mkPrivateName (← getEnv) (part ++ `cm) |> pure
  liftCoreM <| addDecl (.defnDecl { name := mcn, levelParams := [], type := natT, value := mkRawNatLit (hexNat pf[2]!), hints := .abbrev, safety := .safe })
  let mut xs : Array (Expr × Expr × Expr) := #[]
  let mut kern : Nat := 0
  let mut i : Nat := 0
  for ln in subs do
    match ln.splitOn " " with
    | ["SUB", path, hx, _nb, _ns] =>
      let pn ← liftCoreM <| mkPrivateName (← getEnv) (part ++ Name.mkSimple s!"P{i}") |> pure
      liftCoreM <| addDecl (.defnDecl { name := pn, levelParams := [], type := pTy, value := toExpr (parsePath path), hints := .abbrev, safety := .safe })
      let cn ← liftCoreM <| mkPrivateName (← getEnv) (part ++ Name.mkSimple s!"c{i}") |> pure
      liftCoreM <| addDecl (.defnDecl { name := cn, levelParams := [], type := natT, value := mkRawNatLit (hexNat hx), hints := .abbrev, safety := .safe })
      let tn ← liftCoreM <| mkPrivateName (← getEnv) (part ++ Name.mkSimple s!"t{i}") |> pure
      let stmt := boolEq (mkApp4 (mkConst ``PL.subOKL) ltE RE (mkConst pn) (mkConst cn))
      let k0 ← IO.monoNanosNow
      liftCoreM <| addDecl (.thmDecl { name := tn, levelParams := [], type := stmt, value := rflTrue })
      kern := kern + ((← IO.monoNanosNow) - k0)
      xs := xs.push (mkConst pn, mkConst cn, mkConst tn)
      i := i + 1
    | _ => throwError s!"bad sub-record line {i}"
  let (hnd, hpts) ← planeFacts part ptsE EmE
  let QE := mkApp3 (mkConst ``PL.QK) (mkApp (mkConst ``S5.leafN) RE) EmE kE
  let pathsMap (t : Expr) : Expr := mkApp3 (mkConst ``List.map [Level.zero, Level.zero])
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) pTy natT) pTy (mkApp2 (mkConst ``Prod.fst [Level.zero, Level.zero]) pTy natT) |> fun f => mkApp f (mkApp (mkConst ``PL.ST.list) t)
  let (psE, hsubE) :=
    if xs.isEmpty then (mkApp (mkConst ``List.nil [Level.zero]) pTy, mkApp3 (mkConst ``PL.pathsOK_nil) ltE QE RE)
    else
      let (t, okp) := tree ltE RE xs 0 xs.size
      (pathsMap t, mkAppN (mkConst ``PL.pathsOK_of_treeW3) #[ptsE, kE, EmE, hnd, hpts, RE, t, okp])
  let smn ← liftCoreM <| mkPrivateName (← getEnv) (part ++ `tsm) |> pure
  let k1 ← IO.monoNanosNow
  liftCoreM <| addDecl (.thmDecl { name := smn, levelParams := [], type := boolEq (mkApp5 (mkConst ``PL.subMainOK) ltE RE (pathC) psE (mkConst mcn)), value := rflTrue })
  let dsm := (← IO.monoNanosNow) - k1
  let singP := mkApp3 (mkConst ``List.cons [Level.zero]) pTy (pathC) (mkApp (mkConst ``List.nil [Level.zero]) pTy)
  let ty := mkApp4 (mkConst ``PL.PathsOK) ltE QE RE singP
  let prf := mkAppN (mkConst ``PL.pathsOK_of_submainW3) #[ptsE, kE, EmE, hnd, hpts, RE, pathC, psE, mkConst mcn, mkConst smn, hsubE]
  KMod.addPub (part ++ `ok) ty prf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plpart2 {part}: {xs.size} sub-records; kernel {kern / 1000000} ms; part main {dsm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

elab "#plagg2 " sid:ident p:str parts:ident* : command => do
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
  -- part j (the j-th name given, in the file's order) proves its PathsOK for the header's path j
  let sing (j : Nat) : Expr := mkApp3 (mkConst ``List.cons [Level.zero]) pTy (mkConst (seg ++ Name.mkSimple s!"path{j}")) (mkApp (mkConst ``List.nil [Level.zero]) pTy)
  let appendE (a b : Expr) : Expr := mkApp6 (mkConst ``HAppend.hAppend [Level.zero, Level.zero, Level.zero]) plistTy plistTy plistTy
    (mkApp2 (mkConst ``instHAppendOfAppend [Level.zero]) plistTy (mkApp (mkConst ``List.instAppend [Level.zero]) pTy)) a b
  -- no parts (a leaf without SAT leaves): the empty path list, `PL.pathsOK_nil`
  let mut pathsE := if ps.isEmpty then mkApp (mkConst ``List.nil [Level.zero]) pTy else sing (ps.size - 1)
  let mut okE := if ps.isEmpty then mkAppN (mkConst ``PL.pathsOK_nil) #[ltE, QE, RE] else mkConst (ps.back! ++ `ok)
  for j in (List.range (ps.size - 1)).reverse do
    let pj := ps[j]!
    okE := mkAppN (mkConst ``PL.pathsOK_append) #[ltE, QE, RE, sing j, pathsE, mkConst (pj ++ `ok), okE]
    pathsE := appendE (sing j) pathsE
  let tmn ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ `tm) |> pure
  let k0 ← IO.monoNanosNow
  liftCoreM <| addDecl (.thmDecl { name := tmn, levelParams := [], type := boolEq (mkApp3 (mkConst ``PL.leafSXL) ltE RE pathsE), value := rflTrue })
  let dm := (← IO.monoNanosNow) - k0
  let (hnd, hpts) ← planeFacts seg ptsE EmE
  let ty := mkApp5 (mkConst ``L479.NoLiftK) (mkApp (mkConst ``S5.leafT) RE) (mkApp (mkConst ``S5.leafN) RE)
    (mkApp (mkConst ``S6.leafDom6) RE) EmE kE
  let pf := mkAppN (mkConst ``PL.noLiftK_of_paths) #[ptsE, kE, EmE, hnd, hpts, RE, pathsE, mkConst tmn, okE]
  KMod.addPub (seg ++ `ok) ty pf
  let t1 ← IO.monoNanosNow
  logInfo m!"#plagg2 {seg}: {ps.size} parts; main {dm / 1000000} ms; total {(t1 - t0) / 1000000} ms"

end PL.DrvM
