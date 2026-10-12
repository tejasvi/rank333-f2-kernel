module
public meta import KMod.Units
/-! # KMod.Comb: generic pieces for emitters' combinators (plan §7a)

* `dispatch n lits`: adds the private definition `n : Nat → Nat`, a balanced `Bool.rec`/`Nat.ble` tree with `n j ⇝ lits[j]`
  for `j < lits.size` (O(log size) kernel steps per evaluation).  Returns the constant.
* `forallLt f Lf gs`: for groups `gs` whose checker is `f`, a proof of `∀ i, i < N → f (Lf i) = true` where `N` is the total
  literal count and `Lf` maps index `j` of the concatenation of the groups' literals to that literal (e.g. `dispatch` of
  `gs.flatMap (·.lits)`).  A balanced `KMod.rng_split` tree over the units, `KMod.and_l`/`KMod.and_r` inside units of arity
  > 1, `KMod.rng_one` at the literals (each a kernel evaluation of `Lf` at a numeral).  The module must import `KMod.Vocab`.
* `balanced base join xs`: fold `xs` with `join` as a balanced tree.
The kernel cost of `forallLt` is O(N log N) small steps; measured in §7a. -/
public meta section
open Lean Meta
namespace KMod.Comb

def natE : Expr := mkConst ``Nat

/-- add the dispatch `n : Nat → Nat` over the literal definitions `lits` (give `n` as a private name) -/
def dispatch (n : Name) (lits : Array Name) : MetaM Expr := addDispatch n lits

partial def balanced [Inhabited α] (join : α → α → MetaM α) (xs : Array α) (lo hi : Nat) : MetaM α := do
  if hi - lo ≤ 1 then return xs[lo]!
  let mid := (lo + hi) / 2
  join (← balanced join xs lo mid) (← balanced join xs mid hi)

/-- the facts `F lᵢ = true` of a right-nested unit proof `h : (F l₀ && (F l₁ && …)) = true` -/
partial def unitFacts (f : Expr) (ls : List Expr) (h : Expr) : Array Expr :=
  match ls with
  | [] => #[]
  | [_] => #[h]
  | l :: rest =>
    let a := (mkApp f l).headBeta
    let b := andChain f rest
    #[mkApp3 (mkConst `KMod.and_l) a b h] ++ unitFacts f rest (mkApp3 (mkConst `KMod.and_r) a b h)

/-- `∀ i, i < N → f (Lf i) = true` from the units of `gs` (all with checker `f`), `N` the total literal count -/
def forallLt (f Lf : Expr) (gs : Array Group) : MetaM Expr := do
  unless (← getEnv).contains `KMod.rng_split do throwError "KMod.Comb.forallLt: the module must import KMod.Vocab"
  for g in gs do
    unless g.checker == f do throwError "KMod.Comb.forallLt: group {g.name} has a different checker"
  let P := mkLambda `i .default natE (boolEqTrue (mkApp f (mkApp Lf (mkBVar 0))).headBeta)
  -- per-literal pieces `∀ i, j ≤ i → i < j+1 → P i` (as `rng_one`), in global index order
  let mut pieces : Array (Nat × Nat × Expr) := #[]
  let mut off := 0
  for g in gs do
    for i in [0:g.units.size] do
      let ls := (g.unitLits i).toList.map mkConst
      let facts := unitFacts f ls (mkConst g.units[i]!)
      for t in [0:facts.size] do
        let j := off + g.arity * i + t
        pieces := pieces.push (j, j + 1, mkApp3 (mkConst `KMod.rng_one) P (mkRawNatLit j) facts[t]!)
    off := off + g.lits.size
  let join (a b : Nat × Nat × Expr) : MetaM (Nat × Nat × Expr) :=
    pure (a.1, b.2.1, mkApp6 (mkConst `KMod.rng_split) P (mkRawNatLit a.1) (mkRawNatLit b.1) (mkRawNatLit b.2.1) a.2.2 b.2.2)
  let (_, n, t) ← balanced join pieces 0 pieces.size
  return mkApp3 (mkConst `KMod.rng_zero) P (mkRawNatLit n) t

end KMod.Comb
