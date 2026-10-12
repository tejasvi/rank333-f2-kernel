module
public import R22Port.U_d41d8cd98f00
public import KD321.Kinds
public import KD.Flook
/-! # KDK321.Flook (kinds-only name of KD321.Flook): the look-ahead cut (node cut 3) and leaf code 4 over a label order

`KD.Flook` with the order's code table `vf` and odd-pairing masks `npf` (`VecOK`).  At a leaf (`d = 22`, `need = 0`) the bounds
are exact, so the same record certifies leaf code 4 (`--rootcut`).
* `fbOKO`: the bound of one functional; `flookOKO`: one record (dead prefix term `t`, tight list `TL` with deficit hyperplanes
  `TY`, slack list `SL` with `SY`, RootCheck's walk hint `h2`);
* **`flookO_sound`**, **`flookRecO_sound`**: no decomposition lies below the node. -/
@[expose] public section
set_option exponentiation.threshold 1024
noncomputable section
namespace KD321
open RootSound R3RT R3RT.SpecO BC4 BC5 Finset Classical

/-- final hits of `X` at most `3 rk X + c` (as `KD.fbOK`, with the order's masks `npf`) -/
def fbOKO (npf : ℕ → ℕ) (U d F X c Y : ℕ) : Bool :=
  Nat.ble (KD.fld7 U X) (Nat.add (Nat.mul 3 (rkOf X)) c) &&
  (Nat.ble (Nat.add (KD.fld7 U X) (Nat.sub 22 d)) (Nat.add (Nat.mul 3 (rkOf X)) c) ||
   Nat.beq (K2.remB (Nat.land F (npf X)) (Nat.sub (Nat.add (Nat.mul 3 (rkOf X)) c) (KD.fld7 U X))) 0 ||
   (Nat.blt 0 Y && Nat.blt Y 512 && Nat.blt (KD.fld7 U Y) (Nat.mul 3 (rkOf Y)) &&
    Nat.ble (Nat.sub 22 d) (Nat.add (Nat.sub (Nat.add (Nat.mul 3 (rkOf X)) c) (KD.fld7 U X)) (Nat.sub (Nat.mul 3 (rkOf Y)) (KD.fld7 U Y))) &&
    Nat.beq (K2.remB (Nat.land (Nat.land F (npf X)) (npf Y))
      (Nat.sub (Nat.add (Nat.sub (Nat.add (Nat.mul 3 (rkOf X)) c) (KD.fld7 U X)) (Nat.sub (Nat.mul 3 (rkOf Y)) (KD.fld7 U Y))) (Nat.sub 22 d))) 0))

section fb
variable {O : LabelOrder} {vf npf : ℕ → ℕ}

theorem fbO_sound (hV : VecOK O vf npf) {Ω : Spec.Dec22 → Prop} {S D N U d last X c Y : ℕ} (hF : FrameOK O Ω S D N U d)
    (hS : S >>> last = 1) (hd : d ≤ 22) (hX0 : 0 < X) (hX : X < 512)
    (h : fbOKO npf U d (Nat.land (KD.avM D 0) (KD.abv last)) X c Y = true) (A : Spec.Dec22) (hΩ : Ω A)
    (hA : Below O A S last) :
    ((range 511).filter (fun l => Has O A l ∧ par (O.vec l &&& X) = true)).card ≤ 3 * rkOf X + c := by
  have hF' := hF
  obtain ⟨_, _, hcard, hU, _⟩ := hF'
  have hfl : ∀ Z, Z < 512 → KD.fld7 U Z = hits O S Z := fun Z hZ => by
    rw [hU]; exact fld7_packUO O S Z d hZ hcard (by omega)
  have hinF : ∀ l, last < l → l < 511 → Has O A l → (Nat.land (KD.avM D 0) (KD.abv last)).testBit l = true := by
    intro l hll hl5 hAl
    have hD := frame_notD O hF hS hΩ hA l hll hl5 hAl
    rw [show Nat.land (KD.avM D 0) (KD.abv last) = KD.avM D 0 &&& KD.abv last from rfl, Nat.testBit_and, KD.testBit_avM,
      KD.testBit_abv, hD]
    simp [hl5, hll]
  have hsp := below_splitO O hS hA (fun l => par (O.vec l &&& X) = true)
  have hT1 := below_le_tailO O hS hA d hcard (fun l => par (O.vec l &&& X) = true)
  have hFlt : Nat.land (KD.avM D 0) (KD.abv last) < 2 ^ 511 := lt_of_le_of_lt Nat.and_le_left (KD.avM_lt D 0)
  have hhX := hfl X hX
  unfold hits at hhX
  unfold fbOKO at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨h0, h⟩ := h
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at h0 h
  rw [hhX] at h0 h
  rw [hsp]
  rcases h with (h1 | h1) | ⟨⟨⟨⟨hY0, hY⟩, hdY⟩, hge⟩, h1⟩
  · omega
  · replace h1 := KD.beq_true h1
    have hx : Nat.land (Nat.land (KD.avM D 0) (KD.abv last)) (npf X) < 2 ^ 511 := lt_of_le_of_lt Nat.and_le_left hFlt
    have hc := KD.remB_card_le hx h1
    have hsub : ((range 511).filter (fun l => last < l ∧ Has O A l ∧ (par (O.vec l &&& X) = true))).card ≤
        (K2.bitsB 511 (Nat.land (Nat.land (KD.avM D 0) (KD.abv last)) (npf X))).card := by
      apply KD.card_le_bits; intro l hl
      simp only [mem_filter, mem_range] at hl
      obtain ⟨hl5, hll, hAl, hp⟩ := hl
      refine ⟨hl5, ?_⟩
      rw [show Nat.land (Nat.land (KD.avM D 0) (KD.abv last)) (npf X) = Nat.land (KD.avM D 0) (KD.abv last) &&& npf X from rfl,
        Nat.testBit_and, hinF l hll hl5 hAl, hV.np_bit X hX l hl5, hp]; rfl
    omega
  · replace h1 := KD.beq_true h1
    have hhY := hfl Y hY
    unfold hits at hhY
    rw [hhY] at hdY hge h1
    have hFXY : Nat.land (Nat.land (Nat.land (KD.avM D 0) (KD.abv last)) (npf X)) (npf Y) < 2 ^ 511 :=
      lt_of_le_of_lt Nat.and_le_left (lt_of_le_of_lt Nat.and_le_left hFlt)
    have hc := KD.remB_card_le hFXY h1
    have hdefY := deficit_labO O A Y hY0 hY
    have hspY := below_splitO O hS hA (fun l => par (O.vec l &&& Y) = true)
    rw [hspY] at hdefY
    have hY2 : ((range 511).filter (fun l => last < l ∧ Has O A l ∧ (par (O.vec l &&& Y) = true))).card =
        ((range 511).filter (fun l => last < l ∧ Has O A l ∧ (par (O.vec l &&& Y) = true ∧ par (O.vec l &&& X) = true))).card +
        ((range 511).filter (fun l => last < l ∧ Has O A l ∧ (par (O.vec l &&& Y) = true ∧ ¬ par (O.vec l &&& X) = true))).card := by
      rw [← card_union_of_disjoint]
      · apply congrArg Finset.card; ext l; simp only [mem_filter, mem_union, mem_range]
        constructor
        · rintro ⟨hl, h1, h2, h3⟩
          by_cases hx : par (O.vec l &&& X) = true
          · exact Or.inl ⟨hl, h1, h2, h3, hx⟩
          · exact Or.inr ⟨hl, h1, h2, h3, hx⟩
        · rintro (⟨hl, h1, h2, h3, _⟩ | ⟨hl, h1, h2, h3, _⟩) <;> exact ⟨hl, h1, h2, h3⟩
      · rw [disjoint_filter]; rintro l _ ⟨_, _, _, hx⟩ ⟨_, _, _, hx'⟩; exact hx' hx
    have hXY : ((range 511).filter (fun l => last < l ∧ Has O A l ∧ (par (O.vec l &&& Y) = true ∧ par (O.vec l &&& X) = true))).card ≤
        (K2.bitsB 511 (Nat.land (Nat.land (Nat.land (KD.avM D 0) (KD.abv last)) (npf X)) (npf Y))).card := by
      apply KD.card_le_bits; intro l hl
      simp only [mem_filter, mem_range] at hl
      obtain ⟨hl5, hll, hAl, hpY, hpX⟩ := hl
      refine ⟨hl5, ?_⟩
      rw [show Nat.land (Nat.land (Nat.land (KD.avM D 0) (KD.abv last)) (npf X)) (npf Y) =
          Nat.land (KD.avM D 0) (KD.abv last) &&& npf X &&& npf Y from rfl,
        Nat.testBit_and, Nat.testBit_and, hinF l hll hl5 hAl, hV.np_bit X hX l hl5, hV.np_bit Y hY l hl5, hpX, hpY]; rfl
    have hdisj : ((range 511).filter (fun l => last < l ∧ Has O A l ∧ (par (O.vec l &&& X) = true))).card +
        ((range 511).filter (fun l => last < l ∧ Has O A l ∧ (par (O.vec l &&& Y) = true ∧ ¬ par (O.vec l &&& X) = true))).card ≤ 22 - d := by
      rw [← below_above_cardO O hS hA d hcard]
      rw [← card_union_of_disjoint]
      · apply card_le_card; intro l hl
        simp only [mem_union, mem_filter, mem_range] at hl ⊢
        rcases hl with ⟨hl, h1, h2, _⟩ | ⟨hl, h1, h2, _⟩
        · exact ⟨hl, h1, h2⟩
        · exact ⟨hl, h1, h2⟩
      · rw [disjoint_filter]; rintro l _ ⟨_, _, hx⟩ ⟨_, _, _, hx'⟩; exact hx' hx
    omega

end fb

/-! ## The cut record -/

def fbAllO (npf : ℕ → ℕ) (U d F a c : ℕ) : List ℕ → List ℕ → Bool :=
  -- nested `List.rec` (no overlapping match: no splitter with unexported `_sparseCasesOn` auxiliaries; the ExposeCheck rule)
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun Ys => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Ys)
    (fun X _ ih Ys => List.rec (motive := fun _ => Bool) false
      (fun Y Ys' _ => Nat.blt 0 X && Nat.blt X 512 && RootCheck.hitsOne X a && fbOKO npf U d F X c Y && ih Ys') Ys)

/-- node cut 3 / leaf code 4: dead prefix term `t` (a label of `S`), tight list `TL` (deficits `TY`), slack list `SL` (`SY`),
walk hint `h2` -/
def flookOKO (vf npf : ℕ → ℕ) (S D U d last t nT h2 : ℕ) (TL TY SL SY : List ℕ) : Bool :=
  Nat.beq (Nat.shiftRight S last) 1 && Nat.ble d 22 && S.testBit t && Nat.blt t 511 &&
  fbAllO npf U d (Nat.land (KD.avM D 0) (KD.abv last)) (vf t) 0 TL TY &&
  fbAllO npf U d (Nat.land (KD.avM D 0) (KD.abv last)) (vf t) 1 SL SY &&
  RootCheck.walk nT TL SL 64 h2 (RootCheck.q0 TL) (RootCheck.p0 TL) 0

theorem fbAllO_mem {npf : ℕ → ℕ} {U d F a c : ℕ} : ∀ (Xs Ys : List ℕ), fbAllO npf U d F a c Xs Ys = true →
    ∀ X ∈ Xs, ∃ Y, 0 < X ∧ X < 512 ∧ RootCheck.hitsOne X a = true ∧ fbOKO npf U d F X c Y = true
  | [], [], _, X, hX => absurd hX List.not_mem_nil
  | [], _ :: _, h, _, _ => absurd h Bool.false_ne_true
  | _ :: _, [], h, _, _ => absurd h Bool.false_ne_true
  | X' :: Xs, Y' :: Ys, h, X, hX => by
    have h' : (Nat.blt 0 X' && Nat.blt X' 512 && RootCheck.hitsOne X' a && fbOKO npf U d F X' c Y' &&
        fbAllO npf U d F a c Xs Ys) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h'
    rcases List.mem_cons.mp hX with rfl | hm
    · exact ⟨Y', h0, h1, h2, h3⟩
    · exact fbAllO_mem Xs Ys h4 X hm

theorem hitSet_cardO (O : LabelOrder) (A : Spec.Dec22) (X : ℕ) (hX : X < 512) :
    (hitSet (fun s => toM3 (A.av s)) (toM3 X)).card = ((range 511).filter (fun l => Has O A l ∧ par (O.vec l &&& X) = true)).card := by
  unfold hitSet
  rw [card_termsO O A (fun v => pair (toM3 X) (toM3 v) = 1)]
  apply KD.card_filter_congr; intro l hl; rw [mem_range] at hl
  rw [pair_eq_one_iff X _ hX (O.vec_lt l hl), KD.par_eq_hitsOne]

section flook
variable {O : LabelOrder} {vf npf : ℕ → ℕ}

/-- **The look-ahead cut over an order.**  An accepted record with a nonempty tight list: no decomposition of `Ω` lies below
the node. -/
theorem flookO_sound (hV : VecOK O vf npf) {Ω : Spec.Dec22 → Prop} {S D N U d last t nT h2 : ℕ} {X0 : ℕ}
    {TL TY SL SY : List ℕ} (hF : FrameOK O Ω S D N U d) (h : flookOKO vf npf S D U d last t nT h2 (X0 :: TL) TY SL SY = true) :
    ∀ A : Spec.Dec22, Ω A → ¬ Below O A S last := by
  intro A hΩ hA
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
  refine KD.core_sound_le' A.dec s nT X0 TL SL h2 ?_ ?_ ?_ ?_ hw
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

end flook

/-- a cut-3 / leaf-4 record with a nonempty tight list -/
def flookRecO (vf npf : ℕ → ℕ) (S D U d last t nT h2 : ℕ) (TL TY SL SY : List ℕ) : Bool :=
  match TL with
  | [] => false
  | X0 :: TL' => flookOKO vf npf S D U d last t nT h2 (X0 :: TL') TY SL SY

theorem flookRecO_sound {O : LabelOrder} {vf npf : ℕ → ℕ} (hV : VecOK O vf npf) {Ω : Spec.Dec22 → Prop}
    {S D N U d last t nT h2 : ℕ} {TL TY SL SY : List ℕ} (hF : FrameOK O Ω S D N U d)
    (h : flookRecO vf npf S D U d last t nT h2 TL TY SL SY = true) : ∀ A : Spec.Dec22, Ω A → ¬ Below O A S last := by
  cases TL with
  | nil => simp [flookRecO] at h
  | cons X0 TL' => exact flookO_sound hV hF h

end KD321
