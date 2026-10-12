module
/-! # KMod.Vocab: the public lemmas the KMod combinators use (core only, no Mathlib)

Range facts for index families (`rng_one`, `rng_split`, `rng_zero`: a balanced range-split tree turns per-index facts into
`∀ i, i < n → P i`) and the two projections of a unit of arity k > 1 (`(f L₀ && (f L₁ && …)) = true`). -/
@[expose] public section
namespace KMod

theorem rng_one {P : Nat → Prop} {lo : Nat} (h : P lo) : ∀ i, lo ≤ i → i < Nat.succ lo → P i := by
  intro i h1 h2
  have e : i = lo := Nat.le_antisymm (Nat.le_of_lt_succ h2) h1
  subst e; exact h

theorem rng_split {P : Nat → Prop} {lo mid hi : Nat} (h1 : ∀ i, lo ≤ i → i < mid → P i)
    (h2 : ∀ i, mid ≤ i → i < hi → P i) : ∀ i, lo ≤ i → i < hi → P i := by
  intro i a b
  by_cases c : i < mid
  · exact h1 i a c
  · exact h2 i (Nat.le_of_not_lt c) b

theorem rng_zero {P : Nat → Prop} {n : Nat} (h : ∀ i, 0 ≤ i → i < n → P i) : ∀ i, i < n → P i :=
  fun i hi => h i (Nat.zero_le i) hi

theorem and_l {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => rfl

theorem and_r {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => exact h

end KMod
