module
public import BranchCheck7
/-! # KModT.Good: the test vocabulary of the KMod library (as K1Mod.Good: `Good n` = some tree of n BC7-checked leaves) -/
@[expose] public section
namespace KModT
inductive LT where | leaf (R : Nat) | node (a b : LT)
def LT.ok : LT → Prop | .leaf R => BC7.leafS R = true | .node a b => a.ok ∧ b.ok
def LT.size : LT → Nat | .leaf _ => 1 | .node a b => a.size + b.size
def Good (n : Nat) : Prop := ∃ t : LT, t.size = n ∧ t.ok
theorem good_one {R : Nat} (h : BC7.leafS R = true) : Good 1 := ⟨.leaf R, rfl, h⟩
theorem good_add {a b : Nat} (ha : Good a) (hb : Good b) : Good (a + b) := by
  obtain ⟨t1, h1, p1⟩ := ha; obtain ⟨t2, h2, p2⟩ := hb
  exact ⟨.node t1 t2, by simp [LT.size, h1, h2], p1, p2⟩
end KModT
