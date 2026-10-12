module
public import R22Port.U_d41d8cd98f00
public import KD.Tree
/-! # KDK.Frame (kinds-only name of KD.Frame): valid frames at job roots and at batch boundaries

* **`rootFrame_ok`**: a job root (prefix `S`, top label `last`, no dead labels) has a valid L1 frame `(S, 0, N, U, d)` when
  `U = packU S` and every conflict bit of `N` comes from the cap-1 table (`Conf1OK`) or from the cap-2 table of a prefix label
  (`C2OK`), i.e. `N = CONF1 ∪ ⋃_{p ∈ S} c2t_p`, the frame `node5` would build along the prefix.  The static tables' semantics
  are `BindQSpec`'s conclusions.
* **`frames_chain`**: batch-boundary frames by chaining.  If every batch, from valid input frames, yields valid output frames,
  and each batch's input stack is the previous batch's output stack (the same literal), then every batch's input frames are
  valid, starting from the job root's.  So `Batch5TDSpec`'s stack hypothesis is discharged by one comparison per batch (the
  computed final stack against the next batch's input literal), no recomputation. -/
@[expose] public section
set_option exponentiation.threshold 1024
noncomputable section
namespace KD
open R3RT R3RT.Spec RootSound BC4 BC5 Classical

theorem card_three_le (s : Finset ℕ) (a b c : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : 3 ≤ s.card := by
  have : ({a, b, c} : Finset ℕ) ⊆ s := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> assumption
  have h := Finset.card_le_card this
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_insert_of_notMem (by simp [hbc]),
    Finset.card_singleton] at h
  exact h

theorem card_two_le (s : Finset ℕ) (a b : ℕ) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : 2 ≤ s.card := by
  have : ({a, b} : Finset ℕ) ⊆ s := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
  have h := Finset.card_le_card this
  rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton] at h
  exact h

/-- **Job roots.** -/
theorem rootFrame_ok {S last N U : ℕ} (hS : S >>> last = 1) (hS511 : S < 2 ^ 511) (c1 : ℕ) (hc1 : Conf1OK c1)
    (c2 : ℕ → ℕ) (hc2 : ∀ p, p < 511 → S.testBit p = true → C2OK p (c2 p))
    (hN : ∀ v w, (N >>> (512 * v)).testBit w = true →
      (c1 >>> (512 * v)).testBit w = true ∨ ∃ p, p < 511 ∧ S.testBit p = true ∧ (c2 p >>> (512 * v)).testBit w = true)
    (hU : U = packU S) :
    FrameOK S 0 N U ((Finset.range 511).filter (fun l => S.testBit l = true)).card := by
  have hlast := shr_one_lastOf hS
  have hpos : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · rw [h, Nat.zero_shiftRight] at hS; exact absurd hS (by decide)
    · exact h
  refine ⟨hpos, hS511, rfl, hU, fun A hA => ⟨fun l _ _ h0 => by simp at h0, ?_⟩⟩
  intro v w hv hw hSv hSw hvw hbit hAv hAw
  rcases hN v w hbit with h1 | ⟨p, hp, hSp, h2⟩
  · obtain ⟨m, hm, hmv, hmw⟩ := hc1 v w hv hw (Ne.symm hvw) h1
    have hc := card_two_le (inMask A m) v w
      (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
      (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩) hvw
    have := hm A; omega
  · have hpw : w ≠ p := by intro e; rw [e, hSp] at hSw; exact absurd hSw (by decide)
    have hpv : v ≠ p := by intro e; rw [e, hSp] at hSv; exact absurd hSv (by decide)
    obtain ⟨m, hm, hmp, hmv, hmw⟩ := hc2 p hp hSp v w hv hw hpw (Ne.symm hvw) h2
    have hpl : p ≤ lastOf S := by
      rw [hlast]; by_contra hc; push Not at hc; rw [shr_one_bit hS p (by omega)] at hSp; simp at hSp; omega
    have hAp : A.Has p := (hA p hp hpl).2 hSp
    have hc := card_three_le (inMask A m) p v w
      (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hp, hmp, hAp⟩)
      (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
      (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩)
      (Ne.symm hpv) (Ne.symm hpw) hvw
    have := hm A; omega

/-! ## Batch boundaries -/

/-- all frames of a stack are valid -/
def StackOK (st : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop := ∀ f ∈ st, FrameOK f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2

/-- **Chaining.**  `stk k` is batch `k`'s input stack; batch `k` maps valid input frames to valid output frames, and its
output stack is batch `k+1`'s input (`hstep`).  From a valid root stack every batch starts from valid frames. -/
theorem frames_chain (stk : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)) (h0 : StackOK (stk 0))
    (hstep : ∀ k, StackOK (stk k) → StackOK (stk (k + 1))) : ∀ k, StackOK (stk k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => exact hstep k ih

end KD

namespace KD
open R3RT R3RT.Spec

/-- **Segments (queue pieces) chained by prefix.**  Segment `i > 0` starts from the stack its donor `don i < i` exported at the
hand-off (`exp (don i) i`); every segment maps a valid input stack to valid exports.  Then every segment's input stack is
valid, from segment 0's (the job root's).  Batches inside a segment are `frames_chain`. -/
theorem segments_chain (stk : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)) (exp : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)) (don : ℕ → ℕ)
    (h0 : StackOK (stk 0)) (hdon : ∀ i, 0 < i → don i < i) (hlink : ∀ i, 0 < i → stk i = exp (don i) i)
    (hseg : ∀ j, StackOK (stk j) → ∀ i, StackOK (exp j i)) : ∀ i, StackOK (stk i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact h0
    · rw [hlink i hi]; exact hseg _ (ih _ (hdon i hi)) i

end KD
