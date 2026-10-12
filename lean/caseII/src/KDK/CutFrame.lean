module
public import R22Port.U_d41d8cd98f00
public import KD.Leaf
public import KD.Flook
/-! # KDK.CutFrame (kinds-only name of KD.CutFrame): cut nodes and leaves on the frame `frame5` computes (spec revision 5, G4)

A node without a child loop (cut node or leaf) is checked from its parent's frame: R3's `frame5` (`node5` without kills and
hyperplane tests; contract `Frame5Spec`) builds the node's frame `(S', D', N', U')`, and the record's checker runs on it:
* `cutNode`: node cuts 1 / 2 / 4 / 7 / 8 / 9 / 10 (`KD.cutOK`), **`cutNode_sound`**;
* `flookNode`: node cut 3 and leaf code 4 (`KD.flookRec`), **`flookNode_sound`**;
* `leafNode`: a leaf with its v7 record (`KD.leafBind`), **`leafNode_sound`** (nonzero `b`, `c`, as `KD.leaf_node_dead`).
Each gives emptiness of the node `(S ||| 2^last, last)` for canonical-or-not case-(II) decompositions, hence `ChildDead` of
the parent's child `last` (`childDead_of_empty`). -/
@[expose] public section
set_option exponentiation.threshold 1024
noncomputable section
namespace KD
open R3RT R3RT.Spec RootSound BC4 BC5 Classical

def cutNode (S D N U dP c2 h rec kind arg m cap : ℕ) : Bool :=
  R3RT.frame5 S D N U dP c2 h rec
    (fun S' D' _ U' => cutOK S' D' U' 0 (Nat.succ dP) (Nat.land (Nat.shiftRight rec 8) 511) kind arg m cap)

def flookNode (S D N U dP c2 h rec t nT h2 : ℕ) (TL TY SL SY : List ℕ) : Bool :=
  R3RT.frame5 S D N U dP c2 h rec
    (fun S' D' _ U' => flookRec S' D' U' 0 (Nat.succ dP) (Nat.land (Nat.shiftRight rec 8) 511) t nT h2 TL TY SL SY)

def leafNode (S D N U dP c2 h rec R : ℕ) : Bool :=
  R3RT.frame5 S D N U dP c2 h rec (fun S' _ _ _ => Nat.beq (Nat.succ dP) 22 && leafBind R S')

theorem last_eq (rec : ℕ) : Nat.land (Nat.shiftRight rec 8) 511 = (rec >>> 8) % 512 := by
  show (rec >>> 8) &&& (2 ^ 9 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- the node `(S ||| 2^u, u)` empty ⇒ the parent's child `u` is dead -/
theorem childDead_of_empty {S last u : ℕ} (h : ∀ A : Dec22, R3RT.Spec.CaseII A → ¬ Below A (S ||| 2 ^ u) u) :
    ChildDead S last u := fun A _ hII hc => h A hII hc.2.2

theorem testBit_one' (i : ℕ) : (1 : ℕ).testBit i = decide (i = 0) := by
  have := @Nat.testBit_two_pow 0 i; rw [pow_zero] at this; rw [this]; simp [eq_comm]

/-- the node frame `frame5` yields has its top bit at `last` -/
theorem top_of_frame5 {S D N U dP c2 h rec : ℕ} {k : ℕ → ℕ → ℕ → ℕ → Bool}
    (h5 : R3RT.frame5 S D N U dP c2 h rec k = true) :
    ((S ||| 2 ^ ((rec >>> 8) % 512)) >>> ((rec >>> 8) % 512)) = 1 := by
  unfold R3RT.frame5 at h5
  simp only [Bool.and_eq_true, Nat.blt_eq] at h5
  obtain ⟨⟨⟨⟨⟨hl, hS⟩, _⟩, _⟩, _⟩, _⟩ := h5
  replace hS := Nat.eq_of_beq_eq_true hS
  rw [last_eq] at hl hS
  set l := (rec >>> 8) % 512
  have hS' : S >>> l = 0 := hS
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_two_pow]
  have hSi : S.testBit (l + i) = false := by
    have := congrArg (fun x => x.testBit i) hS'
    simp only [Nat.testBit_shiftRight, Nat.zero_testBit] at this; exact this
  rw [hSi, testBit_one']
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have : l ≠ l + i := by omega
    simp [this]

theorem cutNode_soundU {Ω : Dec22 → Prop} (hF5 : R3RT.SpecO.Frame5Spec R3RT.SpecO.LO123 Ω)
    {S D N U dP c2 h rec kind arg m cap : ℕ} (hF : FrameOKU Ω S D N U dP)
    (hc2 : C2OKU Ω ((rec >>> 8) % 512) c2) (hh : HOK ((rec >>> 8) % 512) h)
    (hrec : R3RT.SpecO.RecRowsOK R3RT.SpecO.LO123 Ω rec) (hT : TypeFacts)
    (hrow : RowOKU Ω m cap) (hc : cutNode S D N U dP c2 h rec kind arg m cap = true) :
    ∀ A : Dec22, Ω A → R3RT.Spec.CaseII A → ¬ Below A (S ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) := by
  intro A hΩ hII
  obtain ⟨D', hF', hk⟩ := hF5 S D N U dP c2 h rec _ hF hc2 hh hrec hc
  rw [last_eq] at hk
  exact cut_soundU hF' (blockOKU_zero Ω _) hT hrow hk A hΩ ((caseII_iff A).1 hII)

theorem flookNode_soundU {Ω : Dec22 → Prop} (hF5 : R3RT.SpecO.Frame5Spec R3RT.SpecO.LO123 Ω)
    {S D N U dP c2 h rec t nT h2 : ℕ} {TL TY SL SY : List ℕ}
    (hF : FrameOKU Ω S D N U dP) (hc2 : C2OKU Ω ((rec >>> 8) % 512) c2) (hh : HOK ((rec >>> 8) % 512) h)
    (hrec : R3RT.SpecO.RecRowsOK R3RT.SpecO.LO123 Ω rec)
    (hc : flookNode S D N U dP c2 h rec t nT h2 TL TY SL SY = true) :
    ∀ A : Dec22, Ω A → ¬ Below A (S ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) := by
  obtain ⟨D', hF', hk⟩ := hF5 S D N U dP c2 h rec _ hF hc2 hh hrec hc
  rw [last_eq] at hk
  exact flookRec_soundU hF' (blockOKU_zero Ω _) hk

theorem leafNode_soundU {Ω : Dec22 → Prop} (hF5 : R3RT.SpecO.Frame5Spec R3RT.SpecO.LO123 Ω) {S D N U dP c2 h rec R : ℕ}
    (hF : FrameOKU Ω S D N U dP) (hc2 : C2OKU Ω ((rec >>> 8) % 512) c2) (hh : HOK ((rec >>> 8) % 512) h)
    (hrec : R3RT.SpecO.RecRowsOK R3RT.SpecO.LO123 Ω rec)
    (hR : BC7s.leafS R = true) (hc : leafNode S D N U dP c2 h rec R = true) :
    ∀ A : Dec22, (∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) → ¬ Below A (S ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) := by
  have htop := top_of_frame5 hc
  obtain ⟨D', hF', hk⟩ := hF5 S D N U dP c2 h rec _ hF hc2 hh hrec hc
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hd, hb⟩ := hk
  replace hd := Nat.eq_of_beq_eq_true hd
  obtain ⟨_, hS511, hcard, _⟩ := frameOKU_basic hF'
  rw [show dP + 1 = 22 from hd] at hcard
  exact leaf_node_dead hR hb htop hS511 hcard

/-! ### Revision 5's statements (the trivial universe) -/

theorem frame5Spec_U5 (hF5 : Frame5Spec) : R3RT.SpecO.Frame5Spec R3RT.SpecO.LO123 R3RT.SpecO.ΩT :=
  R3RT.SpecO.frame5Spec_123.mpr hF5

theorem recRowsOKU_of5 {rec : ℕ} (h : RecRowsOK rec) : R3RT.SpecO.RecRowsOK R3RT.SpecO.LO123 R3RT.SpecO.ΩT rec :=
  (R3RT.SpecO.recRowsOK_123 rec).mpr h

theorem cutNode_sound (hF5 : Frame5Spec) {S D N U dP c2 h rec kind arg m cap : ℕ} (hF : FrameOK S D N U dP)
    (hc2 : C2OK ((rec >>> 8) % 512) c2) (hh : HOK ((rec >>> 8) % 512) h) (hrec : RecRowsOK rec) (hT : TypeFacts)
    (hrow : RowOK m cap) (hc : cutNode S D N U dP c2 h rec kind arg m cap = true) :
    ∀ A : Dec22, R3RT.Spec.CaseII A → ¬ Below A (S ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) :=
  fun A => cutNode_soundU (frame5Spec_U5 hF5) (frameOKU_of5 hF) (c2OKU_of5 hc2) hh (recRowsOKU_of5 hrec) hT
    (rowOKU_of5 hrow) hc A trivial

theorem flookNode_sound (hF5 : Frame5Spec) {S D N U dP c2 h rec t nT h2 : ℕ} {TL TY SL SY : List ℕ}
    (hF : FrameOK S D N U dP) (hc2 : C2OK ((rec >>> 8) % 512) c2) (hh : HOK ((rec >>> 8) % 512) h) (hrec : RecRowsOK rec)
    (hc : flookNode S D N U dP c2 h rec t nT h2 TL TY SL SY = true) :
    ∀ A : Dec22, ¬ Below A (S ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) :=
  fun A => flookNode_soundU (frame5Spec_U5 hF5) (frameOKU_of5 hF) (c2OKU_of5 hc2) hh (recRowsOKU_of5 hrec) hc A trivial

theorem leafNode_sound (hF5 : Frame5Spec) {S D N U dP c2 h rec R : ℕ} (hF : FrameOK S D N U dP)
    (hc2 : C2OK ((rec >>> 8) % 512) c2) (hh : HOK ((rec >>> 8) % 512) h) (hrec : RecRowsOK rec)
    (hR : BC7s.leafS R = true) (hc : leafNode S D N U dP c2 h rec R = true) :
    ∀ A : Dec22, (∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) → ¬ Below A (S ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) :=
  leafNode_soundU (frame5Spec_U5 hF5) (frameOKU_of5 hF) (c2OKU_of5 hc2) hh (recRowsOKU_of5 hrec) hR hc

end KD
