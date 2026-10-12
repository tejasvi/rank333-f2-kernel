module
public meta import KMod.Comb
/-! # KModT.E1Comb: test combinator for E1G block groups: the statement `∃ Lf : Nat → Nat, ∀ i, i < N → F (Lf i) = true`,
proved with the module's `#kdispatch Lf …` (over all literals of the groups, in order) and `KMod.Comb.forallLt`. -/
public meta section
open Lean Meta
namespace KModT

def e1Comb : KMod.Combinator := fun stmt gs => do
  let Lf ← KMod.privConst `Lf
  let pf ← KMod.Comb.forallLt gs[0]!.checker Lf gs
  let .app (.app (.const ``Exists [u]) α) p := stmt | throwError "e1Comb: the statement is not an ∃"
  return mkApp4 (mkConst ``Exists.intro [u]) α p Lf pf

end KModT
