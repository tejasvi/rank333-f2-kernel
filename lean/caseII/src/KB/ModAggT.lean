module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.AggT
public import KMod.Units
public meta import KB.AggT
public meta import KMod.Units
/-! # KB.ModAggT: `#kmAggF` and a concatenation over keys alone (scale tests; `KB.CovOfKeyT`, checked = `fun _ => True`)

* `#kmAggT thm "spec"`: as `KB.ModAggCC_cc436_422`'s `#kmAggF`, with item lines `I key` (the checked fact is `True.intro`);
  child lines `E|R childkey L` / `E|R childkey T <A>.cov idx`, export lines `X key`. Each item is a private `cov_<n>` by
  `R22N.Cov.mk'`; the public `thm : AllL CovOfKeyT [exported]`.
* `#kmCatT thm A1.cov A2.cov …`: the public `thm : AllL CovOfKeyT [all their keys]` by projection (a stand-in top over root chunks). -/
public meta section
open Lean Elab Command
namespace KBModAggT

def keysOf (n : Name) : CommandElabM (Array Nat) := do
  let some ci := (← getEnv).find? n | throwError "{n}: not found"
  let l ← match ci.type.getAppFnArgs with
    | (``R22N.AllL, #[_, _, l]) => pure l
    | _ => throwError "{n}: unexpected statement {ci.type}"
  let mut e := l
  let mut acc : Array Nat := #[]
  for _ in [0:10000000] do
    match e.getAppFnArgs with
    | (``List.cons, #[_, .lit (.natVal k), t]) => acc := acc.push k; e := t
    | (``List.nil, _) => return acc
    | _ => throwError "{n}: not a literal key list"
  return acc

def proj (h : Expr) (j : Nat) : Expr := Id.run do
  let mut e := h
  for _ in [0:j] do e := mkProj ``And 1 e
  return mkProj ``And 0 e

def natE : Expr := mkConst ``Nat
def listE (xs : Array Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) natE (mkRawNatLit x) acc) (mkApp (mkConst ``List.nil [.zero]) natE)

def allLPf (P : Expr) (keys : Array Nat) (pfs : Array Expr) : Expr := Id.run do
  let mut ty := mkConst ``True
  let mut pf := mkConst ``True.intro
  for j in [0:keys.size] do
    let jj := keys.size - 1 - j
    pf := mkApp4 (mkConst ``And.intro) (mkApp P (mkRawNatLit keys[jj]!)) ty pfs[jj]! pf
    ty := mkApp2 (mkConst ``And) (mkApp P (mkRawNatLit keys[jj]!)) ty
  return pf

def chainOf (xs : Array (Nat × Expr)) : Expr := Id.run do
  let mut pf := mkConst ``True.intro
  let mut ty := mkConst ``True
  for j in [0:xs.size] do
    let jj := xs.size - 1 - j
    let (kc, a) := xs[jj]!
    let cty := mkApp (mkConst ``KB.CovOfKeyT) (mkRawNatLit kc)
    pf := mkApp4 (mkConst ``And.intro) cty ty a pf
    ty := mkApp2 (mkConst ``And) cty ty
  return pf

elab "#kmAggT " t:ident p:str : command => do
  let t0 ← IO.monoNanosNow
  let lines := (← IO.FS.lines p.getString).toList.filter (· ≠ "")
  let mut items : Array (Nat × Array (Nat × Option Expr) × Array (Nat × Option Expr)) := #[]
  let mut exported : Array Nat := #[]
  for l in lines do
    match l.splitOn " " with
    | ["I", k] => items := items.push (k.toNat!, #[], #[])
    | [c, kc, "L"] =>
      let some last := items.back? | throwError "#kmAggT: child before any item"
      items := items.pop.push (if c == "E" then (last.1, last.2.1.push (kc.toNat!, none), last.2.2)
        else (last.1, last.2.1, last.2.2.push (kc.toNat!, none)))
    | [c, kc, "T", th, i] =>
      let some last := items.back? | throwError "#kmAggT: child before any item"
      let ref := some (proj (mkConst th.toName) i.toNat!)
      items := items.pop.push (if c == "E" then (last.1, last.2.1.push (kc.toNat!, ref), last.2.2)
        else (last.1, last.2.1, last.2.2.push (kc.toNat!, ref)))
    | ["X", k] => exported := exported.push k.toNat!
    | _ => throwError m!"#kmAggT: bad spec line {l}"
  let checked := mkLambda `k .default natE (mkConst ``True)
  let mut covName : Std.HashMap Nat Name := {}
  let mut n := 0
  let mut kms := 0
  for (k, ext, rng) in items do
    let res (xs : Array (Nat × Option Expr)) : CommandElabM (Array (Nat × Expr)) := xs.mapM fun (kc, a) => do
      match a with
      | some e => pure (kc, e)
      | none => match covName.get? kc with
        | some c => pure (kc, mkConst c)
        | none => throwError "#kmAggT: local child {kc} not covered before its parent"
    let pf := mkAppN (mkConst ``R22N.Cov.mk') #[checked, mkRawNatLit k, mkConst ``True.intro, chainOf (← res ext), chainOf (← res rng)]
    let nm := mkPrivateName (← getEnv) (Name.mkSimple s!"cov_{n}")
    let k0 ← IO.monoNanosNow
    liftCoreM <| addDecl (Declaration.thmDecl { name := nm, levelParams := [], type := mkApp (mkConst ``KB.CovOfKeyT) (mkRawNatLit k), value := pf })
    kms := kms + ((← IO.monoNanosNow) - k0) / 1000000
    covName := covName.insert k nm
    n := n + 1
  let mut pfs : Array Expr := #[]
  for k in exported do
    match covName.get? k with
    | some c => pfs := pfs.push (mkConst c)
    | none => throwError "#kmAggT: exported key {k} not covered here"
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (mkConst ``KB.CovOfKeyT) (listE exported)
  KMod.addPub t.getId stmt (allLPf (mkConst ``KB.CovOfKeyT) exported pfs)
  logInfo m!"{t.getId}: Cov over {n} items ({exported.size} exported); private theorems kernel {kms} ms; command {((← IO.monoNanosNow) - t0) / 1000000} ms"

elab "#kmCatT " t:ident srcs:ident* : command => do
  let t0 ← IO.monoNanosNow
  let mut keys : Array Nat := #[]
  let mut pfs : Array Expr := #[]
  for s in srcs do
    let ks ← keysOf s.getId
    for j in [0:ks.size] do
      keys := keys.push ks[j]!; pfs := pfs.push (proj (mkConst s.getId) j)
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (mkConst ``KB.CovOfKeyT) (listE keys)
  KMod.addPub t.getId stmt (allLPf (mkConst ``KB.CovOfKeyT) keys pfs)
  logInfo m!"{t.getId}: {keys.size} keys from {srcs.size} aggregators; command {((← IO.monoNanosNow) - t0) / 1000000} ms"

end KBModAggT
