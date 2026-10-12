module
public import R22Port.U_d41d8cd98f00
public import KDK321.Flook
/-! # KB.Flook321: the look-ahead record over a label order with any tight list, for nonzero `b`, `c`

`KD321.flookRecO_sound` needs a nonempty tight list (`KD.core_sound_le'`). The 321 converter also writes look-ahead certificates
whose tight list is empty (58 in case (I) job 1, as in case (II)); with nonzero `b`, `c` (RR's tables, `Top.dec22_bc`) they are sound
through `KD.core_sound_le`, as case (II)'s `KB.flookOK_soundU_nz`. **`flookOKO_sound_nz`**: an accepted `KD321.flookOKO` on a valid
frame leaves no decomposition of `Ω` with nonzero `b`, `c` below the node. -/
@[expose] public section
noncomputable section
namespace KD321
open RootSound R3RT R3RT.SpecO BC4 BC5 Finset Classical

theorem flookOKO_sound_nz {O : LabelOrder} {vf npf : ℕ → ℕ} (hV : VecOK O vf npf) {Ω : Spec.Dec22 → Prop}
    {S D N U d last t nT h2 : ℕ} {TL TY SL SY : List ℕ} (hF : FrameOK O Ω S D N U d)
    (h : flookOKO vf npf S D U d last t nT h2 TL TY SL SY = true) :
    ∀ A : Spec.Dec22, Ω A → (∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) → ¬ Below O A S last := by
  intro A hΩ hnz hA
  unfold flookOKO at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hS, hd⟩, ht⟩, ht5⟩, hTL⟩, hSL⟩, hw⟩ := h
  replace hS := KD.beq_true hS
  have htl : t ≤ last := by
    by_contra hc; push Not at hc; rw [KD.shr_one_bit hS t (by omega)] at ht; simp at ht; omega
  obtain ⟨_, s, has⟩ := (hA t ht5 htl).2 ht
  have hvt : vf t = O.vec t := hV.vf_eq t ht5
  have hpair : ∀ X, X < 512 → RootCheck.hitsOne X (vf t) = true → pair (toM3 X) ((fun s => toM3 (A.av s)) s) = 1 := by
    intro X hX hh; simp only; rw [has, pair_eq_one_iff X _ hX (O.vec_lt t ht5), ← hvt]; exact hh
  refine KD.core_sound_le A.dec s (hnz s).1 (hnz s).2 nT TL SL h2 ?_ ?_ ?_ ?_ hw
  · intro X hX; obtain ⟨_, h0, h1, _, _⟩ := fbAllO_mem _ _ hTL X hX; exact ⟨h1, by omega⟩
  · intro X hX; obtain ⟨_, h0, h1, _, _⟩ := fbAllO_mem _ _ hSL X hX; exact ⟨h1, by omega⟩
  · intro X hX
    obtain ⟨Y, h0, h1, h2', h3⟩ := fbAllO_mem _ _ hTL X hX
    have hge : 3 * rkOf X ≤ (hitSet (fun s => toM3 (A.av s)) (toM3 X)).card := by
      rw [hitSet_cardO O A X h1]; exact deficit_labO O A X h0 h1
    refine ⟨hpair X h1 h2', le_antisymm ?_ hge⟩
    rw [hitSet_cardO O A X h1]; simpa using fbO_sound hV hF hS hd h0 h1 h3 A hΩ hA
  · intro X hX
    obtain ⟨Y, h0, h1, h2', h3⟩ := fbAllO_mem _ _ hSL X hX
    refine ⟨hpair X h1 h2', ?_⟩
    rw [hitSet_cardO O A X h1]; exact fbO_sound hV hF hS hd h0 h1 h3 A hΩ hA

end KD321
