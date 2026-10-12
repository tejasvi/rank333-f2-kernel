module
public import R22Port.U_d41d8cd98f00
public import KDK.XComp
public import KDK.Frame
/-! # KDK.FrameU (kinds-only name of KD.FrameU): job-root frames over a universe, with the prefix's conflicts as dead labels

`rootFrame_okU`: a job root (prefix `S`, top label `last`) has the valid frame `(S, D, N, U, |S|)` over `Ω` when `N` is built from
the cap-1 table and the prefix labels' cap-2 tables (as `KD.rootFrame_ok`), `U = packU S`, and every dead label of `D` conflicts in
`N` with a prefix label.  Recipe batch 10 (L479: 441 cap-1 rows) kills such labels at the root, so its bulk-peel `F_u` equals
`(above(u) \ D') \ Anode[u]` only with this `D` (converter `py/kx3.py`, `KX2_ROOTDEAD`).  The cap-2 tables' self slots are empty
(`hc2self`; checked on `rt/C3eD.c2t` and `rt479/C3eDII.c2t`). -/
@[expose] public section
set_option exponentiation.threshold 1024
noncomputable section
namespace KD
open R3RT R3RT.Spec RootSound BC4 BC5 Classical

theorem rootFrame_okU {Ω : Dec22 → Prop} {S last N U D : ℕ} (hS : S >>> last = 1) (hS511 : S < 2 ^ 511) (c1 : ℕ)
    (hc1 : R3RT.SpecO.Conf1OK R3RT.SpecO.LO123 Ω c1) (c2 : ℕ → ℕ)
    (hc2 : ∀ p, p < 511 → S.testBit p = true → C2OKU Ω p (c2 p))
    (hc2self : ∀ p, p < 511 → S.testBit p = true → ∀ w, (c2 p >>> (512 * p)).testBit w = false)
    (hN : ∀ v w, (N >>> (512 * v)).testBit w = true →
      (c1 >>> (512 * v)).testBit w = true ∨ ∃ p, p < 511 ∧ S.testBit p = true ∧ (c2 p >>> (512 * v)).testBit w = true)
    (hD : ∀ l, D.testBit l = true → ∃ q, q < 511 ∧ S.testBit q = true ∧ (N >>> (512 * q)).testBit l = true)
    (hU : U = packU S) :
    FrameOKU Ω S D N U ((Finset.range 511).filter (fun l => S.testBit l = true)).card := by
  have hlast := shr_one_lastOf hS
  have hpos : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · rw [h, Nat.zero_shiftRight] at hS; exact absurd hS (by decide)
    · exact h
  -- a decomposition below the prefix has every prefix label
  have hpre : ∀ A : Dec22, Below A S (lastOf S) → ∀ p, p < 511 → S.testBit p = true → A.Has p := by
    intro A hA p hp hSp
    have hpl : p ≤ lastOf S := by
      rw [hlast]; by_contra hc; push Not at hc; rw [shr_one_bit hS p (by omega)] at hSp; simp at hSp; omega
    exact (hA p hp hpl).2 hSp
  -- conflicts of `N` between a label `v` that `A` has and a label `w` outside the prefix, `w ≠ v`
  have hconf : ∀ A : Dec22, Ω A → Below A S (lastOf S) → ∀ v w, v < 511 → w < 511 → S.testBit w = false → v ≠ w →
      (N >>> (512 * v)).testBit w = true → A.Has v → ¬ A.Has w := by
    intro A hΩ hA v w hv hw hSw hvw hbit hAv hAw
    rcases hN v w hbit with h1 | ⟨p, hp, hSp, h2⟩
    · obtain ⟨m, hm, hmv, hmw⟩ := hc1 v w hv hw (Ne.symm hvw) h1
      have hc := card_two_le (inMask A m) v w
        (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
        (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩) hvw
      have := rowOKU_apply hm A hΩ; omega
    · have hpw : w ≠ p := by intro e; rw [e, hSp] at hSw; exact absurd hSw (by decide)
      by_cases hpv : v = p
      · subst hpv; rw [hc2self v hp hSp w] at h2; exact absurd h2 (by decide)
      · obtain ⟨m, hm, hmp, hmv, hmw⟩ := hc2 p hp hSp v w hv hw hpw (Ne.symm hvw) h2
        have hAp : A.Has p := hpre A hA p hp hSp
        have hc := card_three_le (inMask A m) p v w
          (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hp, hmp, hAp⟩)
          (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
          (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩)
          (Ne.symm hpv) (Ne.symm hpw) hvw
        have := rowOKU_apply hm A hΩ; omega
  refine ⟨hpos, hS511, rfl, hU, fun A hΩ hA => ⟨?_, ?_⟩⟩
  · intro l hl hl5 hDl hAl
    obtain ⟨q, hq, hSq, hbit⟩ := hD l hDl
    have hql : q ≠ l := by
      intro e; subst e
      have : q ≤ lastOf S := by
        rw [hlast]; by_contra hc; push Not at hc; rw [shr_one_bit hS q (by omega)] at hSq; simp at hSq; omega
      omega
    have hSl : S.testBit l = false := by rw [shr_one_bit hS l (by omega)]; simp; rw [← hlast]; omega
    exact hconf A hΩ hA q l hq hl5 hSl hql hbit (hpre A hA q hq hSq) hAl
  · intro v w hv hw _ hSw hvw hbit hAv hAw
    exact hconf A hΩ hA v w hv hw hSw hvw hbit hAv hAw

end KD
