module
public meta import KMod.Comb
/-! # KModT.Comb: the test combinator: every literal fact `BC7.leafS L = true` gives `Good 1` (`good_one`), joined by a balanced
`good_add` tree; the statement is `KModT.Good n` with n the literal count. -/
public meta section
open Lean Meta
namespace KModT

def goodComb : KMod.Combinator := fun _ gs => do
  let mut items : Array (Nat × Expr) := #[]
  for g in gs do
    for i in [0:g.units.size] do
      let ls := (g.unitLits i).toList.map mkConst
      let facts := KMod.Comb.unitFacts g.checker ls (mkConst g.units[i]!)
      for t in [0:facts.size] do
        items := items.push (1, mkApp2 (mkConst `KModT.good_one) ls[t]! facts[t]!)
  let join (a b : Nat × Expr) : MetaM (Nat × Expr) :=
    pure (a.1 + b.1, mkApp4 (mkConst `KModT.good_add) (mkRawNatLit a.1) (mkRawNatLit b.1) a.2 b.2)
  return (← KMod.Comb.balanced join items 0 items.size).2

end KModT
