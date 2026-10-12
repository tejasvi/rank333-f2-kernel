module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.AggCC_cc436_422
public import KMod.Units
public meta import KB.AggCC_cc436_422
public meta import KMod.Units
/-! # KB.ModAggCC_cc436_422: the module-form `Cov` aggregators and a stand-in top on the CC route's table cc436_422

* `#kmAgg thm M1.keysOK M2.keysOK …` (item modules without children: whole jobs): the public theorem
  `thm : R22N.AllL (fun k => R22N.Cov KB.CheckedAnyCC_cc436_422 ((SegI.ofKey k).root, (SegI.ofKey k).lo)) [keys]`, each item by
  `Cov.mk'` with its `checked` fact projected from its module's `KeysOK` (an item with external children or ranges is refused here);
* `#kmTop thm A1.cov A2.cov …`: `thm : R22N.AllL (fun k => ∃ segs …, (HCC L → SegOKO …) ∧ GlueOK segs ∧ root and lo of k) [keys]`
  by `KB.segs_of_covKCC_cc436_422` over the aggregators' facts (`allL_imp`). -/
@[expose] public section
open Lean Elab Command


namespace KBModAggCC
/-- the key list of a theorem `R22N.KeysOK _ [k…]` or `R22N.AllL _ [k…]` -/
meta def keysOf (n : Name) : CommandElabM (Array Nat) := do
  let some ci := (← getEnv).find? n | throwError "{n}: not found"
  let l ← match ci.type.getAppFnArgs with
    | (``R22N.KeysOK, #[_, l]) => pure l
    | (``R22N.AllL, #[_, _, l]) => pure l
    | _ => throwError "{n}: unexpected statement {ci.type}"
  let mut e := l
  let mut acc : Array Nat := #[]
  for _ in [0:1000000] do
    match e.getAppFnArgs with
    | (``List.cons, #[_, .lit (.natVal k), t]) => acc := acc.push k; e := t
    | (``List.nil, _) => return acc
    | _ => throwError "{n}: not a literal key list: {e}"
  return acc

/-- projection `j` of an `AllL` proof (`.2` `j` times, then `.1`) -/
meta def proj (h : Expr) (j : Nat) : Expr := Id.run do
  let mut e := h
  for _ in [0:j] do e := mkProj ``And 1 e
  return mkProj ``And 0 e

meta def natE : Expr := mkConst ``Nat
meta def listE (xs : Array Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) natE (mkRawNatLit x) acc) (mkApp (mkConst ``List.nil [.zero]) natE)

/-- `AllL P [k…]` from per-key proofs -/
meta def allLE (P : Expr) (keys : Array Nat) (pfs : Array Expr) : Expr × Expr := Id.run do
  let mut ty := mkConst ``True
  let mut pf := mkConst ``True.intro
  for j in [0:keys.size] do
    let jj := keys.size - 1 - j
    pf := mkApp4 (mkConst ``And.intro) (mkApp P (mkRawNatLit keys[jj]!)) ty pfs[jj]! pf
    ty := mkApp2 (mkConst ``And) (mkApp P (mkRawNatLit keys[jj]!)) ty
  return (ty, pf)

meta def addThm (n : Name) (ty pf : Expr) : CommandElabM Nat := do
  let t0 ← IO.monoNanosNow
  liftCoreM <| addDecl (Declaration.thmDecl { name := n, levelParams := [], type := ty, value := pf })
  return ((← IO.monoNanosNow) - t0) / 1000000

elab "#kmAgg " t:ident srcs:ident* : command => do
  let mut keys : Array Nat := #[]
  let mut pfs : Array Expr := #[]
  let eqL (f : Name) (k : Nat) : Expr :=
    let ty := mkApp (mkConst ``List [.zero]) (if f == ``R22N.SegI.ext then mkApp2 (mkConst ``Prod [.zero, .zero]) natE natE
      else mkApp2 (mkConst ``Prod [.zero, .zero]) (mkApp2 (mkConst ``Prod [.zero, .zero]) natE natE) natE)
    let nil := mkApp (mkConst ``List.nil [.zero]) (ty.appArg!)
    mkApp2 (mkConst ``Eq.refl [.one]) ty nil
  for s in srcs do
    let ks ← keysOf s.getId
    for j in [0:ks.size] do
      let k := ks[j]!
      let hk := proj (mkConst s.getId) j
      pfs := pfs.push (mkAppN (mkConst ``KB.covOfKey_leaf) #[mkRawNatLit k, hk, eqL ``R22N.SegI.ext k, eqL ``R22N.SegI.rng k])
      keys := keys.push k
  let (ty, pf) := allLE (mkConst ``KB.CovOfKeyCC) keys pfs
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (mkConst ``KB.CovOfKeyCC) (listE keys)
  -- the statement is `AllL CovOfKeyCC [k…]`; `ty` is its unfolding (the kernel checks the two equal)
  let _ := ty
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: Cov over {keys.size} items from {srcs.size} item modules"

elab "#kmTop " t:ident aggs:ident* : command => do
  let mut keys : Array Nat := #[]
  let mut pfs : Array Expr := #[]
  for a in aggs do
    let ks ← keysOf a.getId
    for j in [0:ks.size] do
      pfs := pfs.push (mkApp2 (mkConst ``KB.segsOfKey_of_cov) (mkRawNatLit ks[j]!) (proj (mkConst a.getId) j))
      keys := keys.push ks[j]!
  let (_, pf) := allLE (mkConst ``KB.SegsOfKeyCC) keys pfs
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (mkConst ``KB.SegsOfKeyCC) (listE keys)
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: segments for {keys.size} roots from {aggs.size} aggregators"

/-- `#kmAggF thm "spec"`: a `Cov` aggregator over items with external children and ranges.  Spec lines, children before their
parents: `I key thm idx` (an item: its `checked` fact is conjunct `idx` of theorem `thm`, a `KeysOK`), then its children in its
key's order: `E childkey L` / `R childkey L` (covered earlier in this file) or `E childkey T thm idx` / `R childkey T thm idx`
(conjunct `idx` of an imported aggregator's `cov`); `X key` exports a covered key.  Each item's `Cov` is a private theorem
`cov_<n>` (`Cov.mk'`; the kernel matches each child's `CovOfKeyCC childkey` with the decoded ext / rng entry); the public
`thm : AllL CovOfKeyCC [exported keys]`. -/
elab "#kmAggF " t:ident p:str : command => do
  let lines := (← IO.FS.lines p.getString).toList.filter (· ≠ "")
  let mut covName : Std.HashMap Nat Name := {}
  let mut exported : Array Nat := #[]
  let mut items : Array (Nat × Expr × Array (Nat × Expr) × Array (Nat × Expr)) := #[]
  -- parse
  for l in lines do
    match l.splitOn " " with
    | ["I", k, th, i] => items := items.push (k.toNat!, proj (mkConst th.toName) i.toNat!, #[], #[])
    | [c, kc, "L"] =>
      let some last := items.back? | throwError "#kmAggF: child before any item"
      let ref := mkConst (Name.mkSimple s!"__local_{kc}")
      items := items.pop.push (if c == "E" then (last.1, last.2.1, last.2.2.1.push (kc.toNat!, ref), last.2.2.2)
        else (last.1, last.2.1, last.2.2.1, last.2.2.2.push (kc.toNat!, ref)))
    | [c, kc, "T", th, i] =>
      let some last := items.back? | throwError "#kmAggF: child before any item"
      let ref := proj (mkConst th.toName) i.toNat!
      items := items.pop.push (if c == "E" then (last.1, last.2.1, last.2.2.1.push (kc.toNat!, ref), last.2.2.2)
        else (last.1, last.2.1, last.2.2.1, last.2.2.2.push (kc.toNat!, ref)))
    | ["X", k] => exported := exported.push k.toNat!
    | _ => throwError m!"#kmAggF: bad spec line {l}"
  let chainOf (xs : Array (Nat × Expr)) : Expr := Id.run do
    let mut pf := mkConst ``True.intro
    let mut ty := mkConst ``True
    for j in [0:xs.size] do
      let jj := xs.size - 1 - j
      let (kc, a) := xs[jj]!
      let cty := mkApp (mkConst ``KB.CovOfKeyCC) (mkRawNatLit kc)
      pf := mkApp4 (mkConst ``And.intro) cty ty a pf
      ty := mkApp2 (mkConst ``And) cty ty
    return pf
  let checked := mkConst ``KB.CheckedAnyCC_cc436_422
  let mut n := 0
  let mut wsum := 0
  for (k, hk, ext, rng) in items do
    -- local children: the private theorems already added
    let res (xs : Array (Nat × Expr)) : CommandElabM (Array (Nat × Expr)) := xs.mapM fun (kc, a) => do
      match a with
      | .const nm _ =>
        if nm.toString.startsWith "__local_" then
          match covName.get? kc with
          | some c => pure (kc, mkConst c)
          | none => throwError "#kmAggF: local child {kc} not covered before its parent"
        else pure (kc, a)
      | _ => pure (kc, a)
    let ext' ← res ext; let rng' ← res rng
    let pf := mkAppN (mkConst ``R22N.Cov.mk') #[checked, mkRawNatLit k, hk, chainOf ext', chainOf rng']
    let nm := mkPrivateName (← getEnv) (Name.mkSimple s!"cov_{n}")
    let w ← addThm nm (mkApp (mkConst ``KB.CovOfKeyCC) (mkRawNatLit k)) pf
    wsum := wsum + w
    covName := covName.insert k nm
    n := n + 1
  let mut pfs : Array Expr := #[]
  for k in exported do
    match covName.get? k with
    | some c => pfs := pfs.push (mkConst c)
    | none => throwError "#kmAggF: exported key {k} not covered here"
  let (_, pf) := allLE (mkConst ``KB.CovOfKeyCC) exported pfs
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (mkConst ``KB.CovOfKeyCC) (listE exported)
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: Cov over {n} items ({exported.size} exported), private theorems kernel {wsum} ms"
end KBModAggCC
