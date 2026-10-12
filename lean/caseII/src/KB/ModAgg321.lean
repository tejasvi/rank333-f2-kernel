module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.Agg321
public import KMod.Units
public meta import KB.Agg321
public meta import KMod.Units
/-! # KB.ModAgg321: the module-form `Cov` aggregators and the stand-in top of cases (I) / (I13) under `--rord 321`

As `KB.ModAggCC_cc436_422`, with the checked predicate `KB.CheckedAny321 lo hi` and the per-key statements `KB.CovOfKey321 lo hi`,
`KB.SegsOfKey321 lo hi`:
* `#kmAggF321 thm lo hi "spec"` (spec lines as `#kmAggF`: `I key thm idx`, `E|R childkey L`, `E|R childkey T thm idx`, `X key`);
* `#kmTop321 thm lo hi A1.cov A2.cov …`: `thm : R22N.AllL (KB.SegsOfKey321 lo hi) [keys]`;
* `#kmVI321 thm lo hi A1.cov …`: `thm : ∀ l ∈ [0, 168, 462], R22N.Cov (KB.CheckedAny321 lo hi) ((2 ^ l, l), 0)`, `R22B.Final`'s
  `vI` / `vI13`;
* `#kmRoot462 thm lo hi`: the dead job root 462 as an item module's public theorem
  `thm : R22N.KeysOK (KB.CheckedAny321 lo hi) [key of ((2^462, 462), lo 0)]` (`KB.root462_I` / `KB.root462_I13`). -/
public meta section
open Lean Elab Command
namespace KBModAgg321

def natE : Expr := mkConst ``Nat
def listE (xs : Array Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) natE (mkRawNatLit x) acc) (mkApp (mkConst ``List.nil [.zero]) natE)

def keysOf (n : Name) : CommandElabM (Array Nat) := do
  let some ci := (← getEnv).find? n | throwError "{n}: not found"
  let l ← match ci.type.getAppFnArgs with
    | (``R22N.KeysOK, #[_, l]) => pure l
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

def allLPf (P : Expr) (keys : Array Nat) (pfs : Array Expr) : Expr := Id.run do
  let mut ty := mkConst ``True
  let mut pf := mkConst ``True.intro
  for j in [0:keys.size] do
    let jj := keys.size - 1 - j
    pf := mkApp4 (mkConst ``And.intro) (mkApp P (mkRawNatLit keys[jj]!)) ty pfs[jj]! pf
    ty := mkApp2 (mkConst ``And) (mkApp P (mkRawNatLit keys[jj]!)) ty
  return pf

def covP (lo hi : Nat) : Expr := mkApp2 (mkConst ``KB.CovOfKey321) (mkRawNatLit lo) (mkRawNatLit hi)
def segsP (lo hi : Nat) : Expr := mkApp2 (mkConst ``KB.SegsOfKey321) (mkRawNatLit lo) (mkRawNatLit hi)
def checkedE (lo hi : Nat) : Expr := mkApp2 (mkConst ``KB.CheckedAny321) (mkRawNatLit lo) (mkRawNatLit hi)

elab "#kmAggF321 " t:ident lo:num hi:num p:str : command => do
  let (lo, hi) := (lo.getNat, hi.getNat)
  let lines := (← IO.FS.lines p.getString).toList.filter (· ≠ "")
  let mut items : Array (Nat × Expr × Array (Nat × Option Expr) × Array (Nat × Option Expr)) := #[]
  let mut exported : Array Nat := #[]
  for l in lines do
    match l.splitOn " " with
    | ["I", k, th, i] => items := items.push (k.toNat!, proj (mkConst th.toName) i.toNat!, #[], #[])
    | [c, kc, "L"] =>
      let some last := items.back? | throwError "#kmAggF321: child before any item"
      items := items.pop.push (if c == "E" then (last.1, last.2.1, last.2.2.1.push (kc.toNat!, none), last.2.2.2)
        else (last.1, last.2.1, last.2.2.1, last.2.2.2.push (kc.toNat!, none)))
    | [c, kc, "T", th, i] =>
      let some last := items.back? | throwError "#kmAggF321: child before any item"
      let ref := some (proj (mkConst th.toName) i.toNat!)
      items := items.pop.push (if c == "E" then (last.1, last.2.1, last.2.2.1.push (kc.toNat!, ref), last.2.2.2)
        else (last.1, last.2.1, last.2.2.1, last.2.2.2.push (kc.toNat!, ref)))
    | ["X", k] => exported := exported.push k.toNat!
    | _ => throwError m!"#kmAggF321: bad spec line {l}"
  let chainOf (xs : Array (Nat × Expr)) : Expr := Id.run do
    let mut pf := mkConst ``True.intro
    let mut ty := mkConst ``True
    for j in [0:xs.size] do
      let jj := xs.size - 1 - j
      let (kc, a) := xs[jj]!
      let cty := mkApp (covP lo hi) (mkRawNatLit kc)
      pf := mkApp4 (mkConst ``And.intro) cty ty a pf
      ty := mkApp2 (mkConst ``And) cty ty
    return pf
  let mut covName : Std.HashMap Nat Name := {}
  let mut n := 0
  let mut kms := 0
  for (k, hk, ext, rng) in items do
    let res (xs : Array (Nat × Option Expr)) : CommandElabM (Array (Nat × Expr)) := xs.mapM fun (kc, a) => do
      match a with
      | some e => pure (kc, e)
      | none => match covName.get? kc with
        | some c => pure (kc, mkConst c)
        | none => throwError "#kmAggF321: local child {kc} not covered before its parent"
    let pf := mkAppN (mkConst ``R22N.Cov.mk') #[checkedE lo hi, mkRawNatLit k, hk, chainOf (← res ext), chainOf (← res rng)]
    let nm := mkPrivateName (← getEnv) (Name.mkSimple s!"cov_{n}")
    let k0 ← IO.monoNanosNow
    liftCoreM <| addDecl (Declaration.thmDecl { name := nm, levelParams := [], type := mkApp (covP lo hi) (mkRawNatLit k), value := pf })
    kms := kms + ((← IO.monoNanosNow) - k0) / 1000000
    covName := covName.insert k nm
    n := n + 1
  let mut pfs : Array Expr := #[]
  for k in exported do
    match covName.get? k with
    | some c => pfs := pfs.push (mkConst c)
    | none => throwError "#kmAggF321: exported key {k} not covered here"
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (covP lo hi) (listE exported)
  KMod.addPub t.getId stmt (allLPf (covP lo hi) exported pfs)
  logInfo m!"{t.getId}: Cov over {n} items ({exported.size} exported) of case ({lo}, {hi}); private theorems kernel {kms} ms"

elab "#kmTop321 " t:ident lo:num hi:num aggs:ident* : command => do
  let (lo, hi) := (lo.getNat, hi.getNat)
  let mut keys : Array Nat := #[]
  let mut pfs : Array Expr := #[]
  for a in aggs do
    let ks ← keysOf a.getId
    for j in [0:ks.size] do
      pfs := pfs.push (mkAppN (mkConst ``KB.segsOfKey321_of_cov) #[mkRawNatLit lo, mkRawNatLit hi, mkRawNatLit ks[j]!, proj (mkConst a.getId) j])
      keys := keys.push ks[j]!
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (segsP lo hi) (listE keys)
  KMod.addPub t.getId stmt (allLPf (segsP lo hi) keys pfs)
  logInfo m!"{t.getId}: segments of case ({lo}, {hi}) for {keys.size} roots from {aggs.size} aggregators"

/-- `#kmVI321 thm lo hi A1.cov …`: from aggregators exporting the three job roots' keys, the public theorem
`thm : ∀ l ∈ ([0, 168, 462] : List ℕ), R22N.Cov (KB.CheckedAny321 lo hi) ((2 ^ l, l), 0)`, `R22B.Final`'s `vI` / `vI13` (by
`KB.vI_of`; the kernel matches each root's key with `((2^l, l), 0)`) -/
elab "#kmVI321 " t:ident lo:num hi:num aggs:ident* : command => do
  let (lo, hi) := (lo.getNat, hi.getNat)
  -- the exported keys and their proofs, by the root they decode to
  let mut found : Std.HashMap Nat Expr := {}
  for a in aggs do
    let ks ← keysOf a.getId
    for j in [0:ks.size] do
      let k := ks[j]!
      -- root (S, last) and lo of the key: R22N.Glue's byte layout
      let S := k % 2 ^ (8 * 64); let last := (k / 2 ^ (8 * 64)) % 2 ^ 16; let klo := (k / 2 ^ (8 * 66)) % 2 ^ 16
      if klo == 0 && (last == 0 || last == 168 || last == 462) && S == 2 ^ last then
        found := found.insert last (proj (mkConst a.getId) j)
  let c := checkedE lo hi
  let get (l : Nat) : CommandElabM Expr := do
    match found.get? l with
    | some e => pure e
    | none => throwError "#kmVI321: no exported key of the root ({l}) with lo 0"
  let pf := mkAppN (mkConst ``KB.vI_of) #[c, (← get 0), (← get 168), (← get 462)]
  let stmt ← liftTermElabM do
    let e ← Meta.inferType pf
    instantiateMVars e
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: the roots 0, 168, 462 of case ({lo}, {hi}) covered (R22B.Final's vI form)"

/-- the key of the dead job root 462: root `(2^462, 462)`, `lo = 0`, no external children, no ranges (`R22N.Glue`'s format) -/
def key462 : Nat := (2 ^ 462) + 2 ^ (8 * 64) * 462

elab "#kmRoot462 " t:ident lo:num hi:num : command => do
  let (lo, hi) := (lo.getNat, hi.getNat)
  let emp ← if lo == 0 && hi == 12 then pure (mkConst ``KB.root462_I)
    else if lo == 13 && hi == 13 then pure (mkConst ``KB.root462_I13)
    else throwError "#kmRoot462: case ({lo}, {hi}) is neither (0, 12) nor (13, 13)"
  let k := key462
  let kE := mkRawNatLit k
  let ofK := mkApp (mkConst ``R22N.SegI.ofKey) kE
  let pairNN := mkApp2 (mkConst ``Prod [.zero, .zero]) natE natE
  let rootV := mkApp4 (mkConst ``Prod.mk [.zero, .zero]) natE natE (mkRawNatLit (2 ^ 462)) (mkRawNatLit 462)
  let eqR := mkApp2 (mkConst ``Eq.refl [.one]) pairNN rootV
  let eq0 := mkApp2 (mkConst ``Eq.refl [.one]) natE (mkRawNatLit 0)
  let lE := mkApp (mkConst ``List [.zero]) pairNN
  let nilE := mkApp (mkConst ``List.nil [.zero]) pairNN
  let rT := mkApp2 (mkConst ``Prod [.zero, .zero]) pairNN natE
  let lR := mkApp (mkConst ``List [.zero]) rT
  let nilR := mkApp (mkConst ``List.nil [.zero]) rT
  let a := mkApp3 (mkConst ``KB.CheckedR321) (mkRawNatLit lo) (mkRawNatLit hi) kE
  let b := mkApp3 (mkConst ``KB.CheckedRoot462) (mkRawNatLit lo) (mkRawNatLit hi) kE
  -- CheckedRoot462: emptiness ∧ root ∧ lo ∧ ext ∧ rng (the kernel decodes the key)
  let hEmp := mkForall `A .default (mkConst ``R3RT.Spec.Dec22) (mkForall `h .default
    (mkApp3 (mkConst ``R3RT.SpecO.CaseK) (mkRawNatLit lo) (mkRawNatLit hi) (mkBVar 0))
    (mkApp (mkConst ``Not) (mkAppN (mkConst ``R3RT.SpecO.Below) #[mkConst ``Top321.O, mkBVar 1, mkRawNatLit (2 ^ 462), mkRawNatLit 462])))
  let tR := mkApp3 (mkConst ``Eq [.one]) pairNN (mkApp (mkConst ``R22N.SegI.root) ofK) rootV
  let tL := mkApp3 (mkConst ``Eq [.one]) natE (mkApp (mkConst ``R22N.SegI.lo) ofK) (mkRawNatLit 0)
  let tE := mkApp3 (mkConst ``Eq [.one]) lE (mkApp (mkConst ``R22N.SegI.ext) ofK) nilE
  let tG := mkApp3 (mkConst ``Eq [.one]) lR (mkApp (mkConst ``R22N.SegI.rng) ofK) nilR
  let and2 (p q : Expr) (hp hq : Expr) : Expr := mkApp4 (mkConst ``And.intro) p q hp hq
  let pfB := and2 hEmp (mkApp2 (mkConst ``And) tR (mkApp2 (mkConst ``And) tL (mkApp2 (mkConst ``And) tE tG))) emp
    (and2 tR (mkApp2 (mkConst ``And) tL (mkApp2 (mkConst ``And) tE tG)) eqR
      (and2 tL (mkApp2 (mkConst ``And) tE tG) eq0
        (and2 tE tG (mkApp2 (mkConst ``Eq.refl [.one]) lE nilE) (mkApp2 (mkConst ``Eq.refl [.one]) lR nilR))))
  -- CheckedAny321 lo hi k = CheckedR321 ∨ (CheckedRoot462 ∨ CheckedDead321)
  let c := mkApp3 (mkConst ``KB.CheckedDead321) (mkRawNatLit lo) (mkRawNatLit hi) kE
  let pfAny := mkApp3 (mkConst ``Or.inr) a (mkApp2 (mkConst ``Or) b c) (mkApp3 (mkConst ``Or.inl) b c pfB)
  let pf := mkApp4 (mkConst ``And.intro) (mkApp (checkedE lo hi) kE) (mkConst ``True) pfAny (mkConst ``True.intro)
  let stmt := mkApp2 (mkConst ``R22N.KeysOK) (checkedE lo hi) (listE #[k])
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: the dead job root 462 of case ({lo}, {hi})"

end KBModAgg321
