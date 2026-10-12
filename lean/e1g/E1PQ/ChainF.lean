module
public import E1P.Hdr
/-! # Chains indexed by a function (E1P): composition for jobs of 1e4-1e6 blocks (E1PQ.ChainF: E1GK.ChainF at E1P's widths, over the port's own E1P.Hdr; replacing E1PK.ChainF, which imported a copy of E1P/Hdr.lean)

`Hdr.lean`'s chain lemmas take the blocks as a `List ℕ`, and a block is reached by `Ss.getD i 0` in `O(i)` kernel steps.  Here
the blocks are a function `Lf : ℕ → ℕ` with `n` entries (e.g. a balanced dispatch over private block literals: `O(log n)`
steps), and the hypotheses are per block, so that they can be proved one declaration at a time (one block, or `k` packed
leaf blocks, per declaration) and assembled by `RangeOK` joins:
* `RangeOK P a m`, `range_one`, `range_join`, `range_and`, `range_all`: `∀ i < n, P i` from per-index facts in a balanced tree.
* `glueRowW n Lf nJ Jf Wf i`: every header record of block `i` is glued (`glue` / `glue0`) to its witness, a later block or
  a job; `glueF_of_rows` turns the rows into the chain's glue hypothesis `GlueF`.
* `chain_sound_fn`, `jobOK_of_chain_fn`, `enum_of_chain_fn`: `chain_sound_f`, `jobOK_of_chain_w`, `enum_of_chain_w` over
  `Lf`.  The proofs are those of `Hdr.lean` with `Ss.getD i 0` replaced by `Lf i`. -/
@[expose] public section

set_option maxRecDepth 20000
namespace E1PS

/-! ## Per-index facts in a balanced tree -/

/-- `P i` for every `i` in `[a, a + m)` -/
def RangeOK (P : ℕ → Prop) (a m : ℕ) : Prop := ∀ i, a ≤ i → i < a + m → P i

theorem range_one (P : ℕ → Prop) (a : ℕ) (h : P a) : RangeOK P a 1 := by
  intro i h1 h2; have : i = a := by omega
  subst this; exact h

theorem range_join (P : ℕ → Prop) (a m k : ℕ) (h1 : RangeOK P a m) (h2 : RangeOK P (a + m) k) : RangeOK P a (m + k) := by
  intro i hi1 hi2
  by_cases h : i < a + m
  · exact h1 i hi1 h
  · exact h2 i (by omega) (by omega)

theorem range_zero (P : ℕ → Prop) (a : ℕ) : RangeOK P a 0 := by intro i h1 h2; omega

/-- two facts from one declaration (a conjunction of packed checks) -/
theorem range_and (P : ℕ → Prop) (a : ℕ) (b c : Bool) (hb : b = true → P a) (hc : c = true → RangeOK P (a + 1) m)
    (h : (b && c) = true) : RangeOK P a (m + 1) := by
  rw [Bool.and_eq_true] at h
  have := range_join P a 1 m (range_one P a (hb h.1)) (hc h.2)
  rwa [Nat.add_comm 1 m] at this

theorem range_all (P : ℕ → Prop) (n : ℕ) (h : RangeOK P 0 n) : ∀ i < n, P i := fun i hi => h i (Nat.zero_le i) (by omega)

/-! ## Glue rows -/

/-- record `j` of block `i` is glued to `w`: a later block (`w < n`) or job `w - n` of `Jf` -/
noncomputable def glue1Fn (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (i j w : ℕ) : Bool :=
  cond (Nat.blt w n)
    (Nat.blt i w && (E1P.glue (recOf (Lf i) j) (Lf w) || E1P.glue0 (recOf (Lf i) j) (Lf w)))
    (Nat.blt (w - n) nJ && (E1P.glue (recOf (Lf i) j) (Jf (w - n)) || E1P.glue0 (recOf (Lf i) j) (Jf (w - n))))

/-- every header record of block `i` is glued to its witness `Wf i j` -/
noncomputable def glueRowW (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (Wf : ℕ → ℕ → ℕ) (i : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1Fn n Lf nJ Jf i j (Wf i j)) (E1P.rd 8 (E1P.bS2 (Lf i)))

/-- the chain's glue hypothesis: every record of every block is glued to a later block or to a job -/
def GlueF (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) : Prop :=
  ∀ i < n, ∀ j < E1P.rd 8 (E1P.bS2 (Lf i)),
    (∃ i', i < i' ∧ i' < n ∧ (E1P.glue (recOf (Lf i) j) (Lf i') = true ∨ E1P.glue0 (recOf (Lf i) j) (Lf i') = true)) ∨
    (∃ k < nJ, E1P.glue (recOf (Lf i) j) (Jf k) = true ∨ E1P.glue0 (recOf (Lf i) j) (Jf k) = true)

theorem glueRowW_spec (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (Wf : ℕ → ℕ → ℕ) (i : ℕ)
    (h : glueRowW n Lf nJ Jf Wf i = true) : ∀ j < E1P.rd 8 (E1P.bS2 (Lf i)),
    (∃ i', i < i' ∧ i' < n ∧ (E1P.glue (recOf (Lf i) j) (Lf i') = true ∨ E1P.glue0 (recOf (Lf i) j) (Lf i') = true)) ∨
    (∃ k < nJ, E1P.glue (recOf (Lf i) j) (Jf k) = true ∨ E1P.glue0 (recOf (Lf i) j) (Jf k) = true) := by
  unfold glueRowW at h
  intro j hj
  generalize E1P.rd 8 (E1P.bS2 (Lf i)) = K at h hj
  induction K with
  | zero => omega
  | succ K ih =>
    have h' := h
    simp only [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact ih h'.1 hlt
    · have hw := h'.2
      unfold glue1Fn at hw
      generalize Wf i j = w at hw
      cases hb : Nat.blt w n
      · rw [hb, cond_false] at hw
        simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hw
        exact Or.inr ⟨w - n, hw.1, hw.2⟩
      · rw [hb, cond_true] at hw
        simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hw hb
        exact Or.inl ⟨w, hw.1, hb, hw.2⟩

theorem glueF_of_rows (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (Wf : ℕ → ℕ → ℕ)
    (h : ∀ i < n, glueRowW n Lf nJ Jf Wf i = true) : GlueF n Lf nJ Jf :=
  fun i hi => glueRowW_spec n Lf nJ Jf Wf i (h i hi)

/-! ## Chain soundness over `Lf` -/

theorem chain_sound_fn (C : E1P.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (ub x : ℕ → ℕ) (hg : Glob C x)
    (hsl : ∀ i < 2 ^ 19, SlotV x (sl i)) (hUB : UB = V ub) (hUBR : UBR = VR ub) (hubb : ∀ l < 255, ub l ≤ 2 ^ 32)
    (hxub : ∀ l < 255, x l ≤ ub l) (hx : ∃ l < 255, 0 < x l) (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ)
    (hJ : ∀ k < nJ, ¬ StartOK x ub (Jf k))
    (hblk : ∀ i < n, E1P.block C sl UB UBR (Lf i) = true) (hglue : GlueF n Lf nJ Jf) :
    ∀ i < n, ¬ StartOK x ub (Lf i) := by
  suffices hk : ∀ k, ∀ i < n, n - i ≤ k → ¬ StartOK x ub (Lf i) from fun i hi => hk n i hi (by omega)
  intro k
  induction k with
  | zero => intro i hi hk; omega
  | succ k ih =>
    intro i hi hk hs
    obtain ⟨j, hj⟩ := block_sound C sl UB UBR ub x hg hsl hUB hUBR hubb hxub _ (hblk i hi) hs
    by_cases hjn : j < E1P.rd 8 (E1P.bS2 (Lf i))
    · rcases hglue i hi j hjn with ⟨i', hii', hi', hgl⟩ | ⟨k', hk', hgl⟩
      · rcases hgl with hgl | hgl
        · exact ih i' hi' (by omega) (glue_start x ub _ _ hgl hj)
        · exact ih i' hi' (by omega) (glue0_start x ub hxub _ _ hgl hj)
      · rcases hgl with hgl | hgl
        · exact hJ k' hk' (glue_start x ub _ _ hgl hj)
        · exact hJ k' hk' (glue0_start x ub hxub _ _ hgl hj)
    · rw [hdr_rec _ j (by omega)] at hj
      exact recV_zero x hx hj

/-- **A function-indexed chain glued to jobs proves `JobOK` of its first block** -/
theorem jobOK_of_chain_fn (C : E1P.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (hUB : UB = V (fun l => E1P.fld UB l))
    (hUBR : UBR = VR (fun l => E1P.fld UB l)) (hubb : ∀ l < 255, E1P.fld UB l ≤ 2 ^ 32)
    (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (hne : 0 < n)
    (hblk : ∀ i < n, E1P.block C sl UB UBR (Lf i) = true) (hglue : GlueF n Lf nJ Jf)
    (hjobs : ∀ k < nJ, JobOK C sl UB (Jf k)) : JobOK C sl UB (Lf 0) :=
  fun x hg hsl hxub hx => chain_sound_fn C sl UB UBR (fun l => E1P.fld UB l) x hg hsl hUB hUBR hubb hxub hx n Lf nJ Jf
    (fun k hk => hjobs k hk x hg hsl hxub hx) hblk hglue 0 hne

/-- **A function-indexed chain from the root, glued to jobs, proves the canonical-point statement** (`L479.EnumOK`'s
shape) -/
theorem enum_of_chain_fn (C : E1P.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (hUB : UB = V (fun l => E1P.fld UB l))
    (hUBR : UBR = VR (fun l => E1P.fld UB l)) (hubb : ∀ l < 255, E1P.fld UB l ≤ 2 ^ 32)
    (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (hne : 0 < n) (hroot : Lf 0 % 2 ^ 14 = 0)
    (hblk : ∀ i < n, E1P.block C sl UB UBR (Lf i) = true) (hglue : GlueF n Lf nJ Jf)
    (hjobs : ∀ k < nJ, JobOK C sl UB (Jf k)) :
    ∀ x : ℕ → ℕ, Glob C x → (∀ i < 2 ^ 19, SlotV x (sl i)) → (∀ l < 255, x l ≤ E1P.fld UB l) →
      (∃ l < 255, 0 < x l) → False := by
  intro x hg hsl hxub hx
  apply jobOK_of_chain_fn C sl UB UBR hUB hUBR hubb n Lf nJ Jf hne hblk hglue hjobs x hg hsl hxub hx
  have h0 : Lf 0 % 2 = 0 := by
    have := Nat.mod_mod_of_dvd (Lf 0) (show 2 ∣ 2 ^ 14 by norm_num); rw [hroot] at this; omega
  have hd0 : Lf 0 / 2 % 2 ^ 5 = 0 := by
    have a := mod_div_mod (Lf 0) 14 1 5 (by omega)
    rw [hroot] at a; simpa using a.symm
  have hp0 : Lf 0 / 2 ^ 6 % 2 ^ 8 = 0 := by
    have a := mod_div_mod (Lf 0) 14 6 8 (by omega)
    rw [hroot] at a; simpa using a.symm
  unfold StartOK
  rw [hd0, hp0, if_neg (by omega)]
  refine ⟨fun l => by simp [multR], fun l hl => by omega, fun l _ => by simp [multR], fun l hl => ?_⟩
  simp only [multR, Nat.zero_add, Nat.sub_zero]
  exact hxub l hl

end E1PS

namespace E1PS
/-- a decided range unit `∀ t < m, P (a + t)` as a `RangeOK` -/
theorem range_of_forall (P : ℕ → Prop) (a m : ℕ) (h : ∀ t < m, P (a + t)) : RangeOK P a m := by
  intro i h1 h2
  have := h (i - a) (by omega)
  rwa [show a + (i - a) = i by omega] at this
end E1PS

namespace E1PS
/-- glue rows `a .. a + m - 1` (one `Bool` for a decided unit) -/
noncomputable def glueRange (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (Wf : ℕ → ℕ → ℕ) (a m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t b => b && glueRowW n Lf nJ Jf Wf (a + t)) m

theorem glueRange_spec (n : ℕ) (Lf : ℕ → ℕ) (nJ : ℕ) (Jf : ℕ → ℕ) (Wf : ℕ → ℕ → ℕ) (a m : ℕ)
    (h : glueRange n Lf nJ Jf Wf a m = true) : RangeOK (fun i => glueRowW n Lf nJ Jf Wf i = true) a m := by
  apply range_of_forall
  induction m with
  | zero => intro t ht; omega
  | succ m ih =>
    intro t ht
    have h' : (glueRange n Lf nJ Jf Wf a m && glueRowW n Lf nJ Jf Wf (a + m)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
    · exact ih h'.1 t hlt
    · exact h'.2
end E1PS

