module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.AggCC_cc436_422
public import KMod.Units
public meta import KB.AggCC_cc436_422
public meta import KMod.Units
/-! # KB.ModRekeyCC: a split-independent statement for a case-II package's covered roots (CC route, table cc436_422)

`#kmRekeyCC thm A.cov`: from an aggregator's `A.cov : R22N.AllL KB.CovOfKeyCC [k₁, …]`, the public theorem
`thm : R22N.AllL KB.CovOfKeyCC [m₁, …]` (sorted ascending) where the `m` are the minimal keys `kᵢ % 2^544`: R22N.Glue's root `S` (64 bytes), `last` and `lo`
(2 bytes each), with no external children and no ranges. `KB.CovOfKeyCC k` reads only `(SegI.ofKey k).root` and `.lo`, so each
`A.cov` component is a proof of the new one by definitional unfolding (the kernel decodes both keys). A queue run may split a job
differently each time (dynamic donation), which changes the job item's external children and ranges, hence its key; the minimal
keys, sorted, and so this statement, depend only on the covered job roots: a join can state its children's indices from the job list
alone. -/
@[expose] public section
open Lean Elab Command

namespace KBModRekeyCC

/-- the key list of a theorem `R22N.AllL _ [k…]` -/
meta def keysOf (n : Name) : CommandElabM (Array Nat) := do
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
    | _ => throwError "{n}: not a literal key list: {e}"
  return acc

meta def natE : Expr := mkConst ``Nat
meta def listE (xs : Array Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) natE (mkRawNatLit x) acc) (mkApp (mkConst ``List.nil [.zero]) natE)

elab "#kmRekeyCC " t:ident a:ident : command => do
  let ks ← keysOf a.getId
  -- (minimal key, index in A.cov), sorted by the minimal key
  let ord := ((List.range ks.size).map (fun i => (ks[i]! % 2 ^ 544, i))).toArray.qsort (fun x y => x.1 < y.1)
  for j in [1:ord.size] do
    if ord[j]!.1 == ord[j-1]!.1 then throwError "#kmRekeyCC: two roots with the same minimal key"
  let ms := ord.map (·.1)
  -- the proof: the AllL tree of A.cov's components in sorted order, each stated over its minimal key (the kernel unfolds CovOfKeyCC on
  -- both keys)
  let mut ty := mkConst ``True
  let mut pf := mkConst ``True.intro
  for j in [0:ord.size] do
    let jj := ord.size - 1 - j
    let src := ord[jj]!.2
    let mut e := mkConst a.getId
    for _ in [0:src] do e := mkProj ``And 1 e
    let pj := mkProj ``And 0 e
    let pm := mkApp (mkConst ``KB.CovOfKeyCC) (mkRawNatLit ms[jj]!)
    pf := mkApp4 (mkConst ``And.intro) pm ty pj pf
    ty := mkApp2 (mkConst ``And) pm ty
  let stmt := mkApp3 (mkConst ``R22N.AllL []) natE (mkConst ``KB.CovOfKeyCC) (listE ms)
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: {ms.size} roots restated over their minimal keys (root, lo)"

end KBModRekeyCC
