module
public import R22Port.U_d41d8cd98f00
public import KB.Defs
public import KDK321.Batch321
public import Top.TopL479
/-! # KB.ItemII: the kernel track's items in the segment contract of `Top.rank_ge_23_L479`

The contract (native/infra PROOF_OBJECT.md §3.2a, `R22B.SegRefH`): every checked item key has a segment with exactly the key's
interface (`R22N.SegI.ofKey`: root, `lo`, external children, ranges), certified (`Top.SegOKO`) under the facts `H`.  The segment
comes first: its OPEN nodes are chosen only under `H` (`segRef_of_cov`), as `Top.rank_ge_23_L479` fixes `segII` before `hsegII`.

* `segOKO_of_cov`: a covered tree (`KD.ItemCovK`) with the key's root and external children is a certified segment (`lo = 0`,
  no ranges, no dead nodes).
* `rootChk0`: the root's parent frame, the empty prefix's `(0, 0, c1, 0, 0)` for a depth-1 root (KD321's `FrameOK0`), else
  `KD.rootChk`.
* **`itemK_segRef`**: an accepted item (root frame, chain of accepted batches `KD.ChainK`, no pending labels at the end, the key's
  interface) gives the contract's `∃ g` statement, for any order, universe and extension with their soundness facts.
* **`CheckedK`** (the kernel track's item predicate) and **`segRefHK_K`**: `SegRefHK H O C (CheckedK …)`, which is
  `R22B.SegRefH`'s body, so `R22B.segs_of_covH` and `R22B.final_generic` take it as the kernel track's checker contract. -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
noncomputable section
namespace KB
open R3RT.SpecO KD

/-- `R22B.SegRefH H O C checked` (native/infra/lib/bridge/R22B/Segs.lean), with the same body -/
def SegRefHK (H : Prop) (O : LabelOrder) (C : R3RT.Spec.Dec22 → Prop) (checked : ℕ → Prop) : Prop :=
  ∀ k, checked k → ∃ g : Top.Seg, g.root = (R22N.SegI.ofKey k).root ∧ g.lo = (R22N.SegI.ofKey k).lo ∧
    g.ext = {e | e ∈ (R22N.SegI.ofKey k).ext} ∧ g.rng = {p | p ∈ (R22N.SegI.ofKey k).rng} ∧ (H → Top.SegOKO O C g)

/-- the segment of a covered tree: the key's interface, OPEN nodes `K`, no dead nodes -/
def segK (key : ℕ) (K : Set (ℕ × ℕ)) : Top.Seg where
  root := (R22N.SegI.ofKey key).root
  lo := (R22N.SegI.ofKey key).lo
  opens := K
  dead := ∅
  ext := {e | e ∈ (R22N.SegI.ofKey key).ext}
  rng := {p | p ∈ (R22N.SegI.ofKey key).rng}

/-- **a covered tree is a certified segment** -/
theorem segOKO_of_cov {O : LabelOrder} {C : R3RT.Spec.Dec22 → Prop} {key : ℕ} {K : Set (ℕ × ℕ)}
    (hlo : (R22N.SegI.ofKey key).lo = 0) (hrng : (R22N.SegI.ofKey key).rng = [])
    (h : ItemCovK O C (R22N.SegI.ofKey key).root K {e | e ∈ (R22N.SegI.ofKey key).ext}) : Top.SegOKO O C (segK key K) := by
  obtain ⟨hr, hK⟩ := h
  refine ⟨Or.inl hr, fun h0 => by simp [segK, hlo] at h0, fun p hp => by simp [segK, hrng] at hp,
    fun n hn => by simp [segK] at hn, fun n hn => ?_⟩
  obtain ⟨htop, hc, hcov⟩ := hK n hn
  refine ⟨htop, hc, fun u hu1 hu2 => ?_⟩
  rcases hcov u hu1 hu2 with h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- **from covered trees to the contract**: the segment exists unconditionally; its OPEN nodes are chosen under the facts -/
theorem segRef_of_cov {O : LabelOrder} {C : R3RT.Spec.Dec22 → Prop} (H : Prop) (key : ℕ)
    (hlo : (R22N.SegI.ofKey key).lo = 0) (hrng : (R22N.SegI.ofKey key).rng = [])
    (hK : H → ∃ K, ItemCovK O C (R22N.SegI.ofKey key).root K {e | e ∈ (R22N.SegI.ofKey key).ext}) :
    ∃ g : Top.Seg, g.root = (R22N.SegI.ofKey key).root ∧ g.lo = (R22N.SegI.ofKey key).lo ∧
      g.ext = {e | e ∈ (R22N.SegI.ofKey key).ext} ∧ g.rng = {p | p ∈ (R22N.SegI.ofKey key).rng} ∧
      (H → Top.SegOKO O C g) := by
  by_cases hH : H
  · obtain ⟨K, hc⟩ := hK hH
    exact ⟨segK key K, rfl, rfl, rfl, rfl, fun _ => segOKO_of_cov hlo hrng hc⟩
  · exact ⟨segK key ∅, rfl, rfl, rfl, rfl, fun h => absurd h hH⟩

/-! ## The root's parent frame, including the empty prefix -/

/-! ## Root frames with witness rows -/

/-- `KD.rootFrame_okO` with a second kind of dead label: a label of a row full at the prefix (a witness row) -/
theorem rootFrame_okOW {O : LabelOrder} {Ω : R3RT.Spec.Dec22 → Prop} {S last N U D : ℕ} (hS : S >>> last = 1)
    (hS511 : S < 2 ^ 511) (c1 : ℕ) (hc1 : Conf1OK O Ω c1) (c2 : ℕ → ℕ)
    (hc2 : ∀ p, p < 511 → S.testBit p = true → C2OKO O Ω p (c2 p))
    (hc2self : ∀ p, p < 511 → S.testBit p = true → ∀ w, w < 511 → (c2 p >>> (512 * p)).testBit w = false)
    (hN : ∀ v w, (N >>> (512 * v)).testBit w = true →
      (c1 >>> (512 * v)).testBit w = true ∨ ∃ p, p < 511 ∧ S.testBit p = true ∧ (c2 p >>> (512 * v)).testBit w = true)
    (hD : ∀ l, D.testBit l = true → (∃ q, q < 511 ∧ S.testBit q = true ∧ (N >>> (512 * q)).testBit l = true) ∨
      ∃ m cap, RowOKO O Ω m cap ∧ m.testBit l = true ∧
        ((Finset.range 511).filter (fun p => S.testBit p = true ∧ m.testBit p = true)).card = cap)
    (hU : U = packU O S) :
    FrameOKO O Ω S D N U (pcnt511 S) := by
  classical
  have hlast := shr_one_lastOf hS
  have hpos : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · rw [h, Nat.zero_shiftRight] at hS; exact absurd hS (by decide)
    · exact h
  have hpre : ∀ A : R3RT.Spec.Dec22, Below O A S (R3RT.Spec.lastOf S) → ∀ p, p < 511 → S.testBit p = true → Has O A p := by
    intro A hA p hp hSp
    have hpl : p ≤ R3RT.Spec.lastOf S := by
      rw [hlast]; by_contra hc; push Not at hc; rw [shr_one_bit hS p (by omega)] at hSp; simp at hSp; omega
    exact (hA p hp hpl).2 hSp
  have hconf : ∀ A : R3RT.Spec.Dec22, Ω A → Below O A S (R3RT.Spec.lastOf S) → ∀ v w, v < 511 → w < 511 → S.testBit w = false →
      v ≠ w → (N >>> (512 * v)).testBit w = true → Has O A v → ¬ Has O A w := by
    intro A hΩ hA v w hv hw hSw hvw hbit hAv hAw
    rcases hN v w hbit with h1 | ⟨p, hp, hSp, h2⟩
    · obtain ⟨m, hm, hmv, hmw⟩ := hc1 v w hv hw (Ne.symm hvw) h1
      have hc := card_two_le (inMask O A m) v w
        (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
        (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩) hvw
      have := rowOKO_apply hm A hΩ; omega
    · have hpw : w ≠ p := by intro e; rw [e, hSp] at hSw; exact absurd hSw (by decide)
      by_cases hpv : v = p
      · subst hpv; rw [hc2self v hp hSp w hw] at h2; exact absurd h2 (by decide)
      · obtain ⟨m, hm, hmp, hmv, hmw⟩ := hc2 p hp hSp v w hv hw hpw (Ne.symm hvw) h2
        have hAp := hpre A hA p hp hSp
        have hc := card_three_le (inMask O A m) p v w
          (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hp, hmp, hAp⟩)
          (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
          (by simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩)
          (Ne.symm hpv) (Ne.symm hpw) hvw
        have := rowOKO_apply hm A hΩ; omega
  refine ⟨hpos, hS511, rfl, hU, fun A hΩ hA => ⟨?_, ?_⟩⟩
  · intro l hl hl5 hDl hAl
    have hSl : S.testBit l = false := by rw [shr_one_bit hS l (by omega)]; simp; rw [← hlast]; omega
    rcases hD l hDl with ⟨q, hq, hSq, hbit⟩ | ⟨m, cap, hm, hml, hcard⟩
    · have hql : q ≠ l := by intro e; subst e; rw [hSq] at hSl; exact absurd hSl (by decide)
      exact hconf A hΩ hA q l hq hl5 hSl hql hbit (hpre A hA q hq hSq) hAl
    · -- a full witness row: the prefix holds `cap` of its labels, so `l` would be one too many
      have hsub : insert l ((Finset.range 511).filter (fun p => S.testBit p = true ∧ m.testBit p = true)) ⊆ inMask O A m := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hl5, hml, hAl⟩
        · simp only [Finset.mem_filter, Finset.mem_range] at hp
          simp only [inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hp.1, hp.2.2, hpre A hA p hp.1 hp.2.1⟩
      have hnot : l ∉ (Finset.range 511).filter (fun p => S.testBit p = true ∧ m.testBit p = true) := by
        simp only [Finset.mem_filter, Finset.mem_range, not_and]; intro _ h; rw [hSl] at h; exact absurd h (by decide)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot, hcard] at h1
      have := rowOKO_apply hm A hΩ; omega
  · intro v w hv hw _ hSw hvw hbit hAv hAw
    exact hconf A hΩ hA v w hv hw hSw hvw hbit hAv hAw

theorem rootDW_testBit {tab : ℕ → ℕ} {N l : ℕ} {pl W : List ℕ} (h : (rootDW tab N pl W).testBit l = true) :
    l < 511 ∧ ((∃ q ∈ pl, (N >>> (512 * q)).testBit l = true) ∨ ∃ w ∈ W, (tab w).testBit l = true) := by
  unfold rootDW at h
  rw [L5.land_eq, Nat.testBit_and, Bool.and_eq_true, R3RT.m511_bit, decide_eq_true_eq, L5.lor_eq, Nat.testBit_or,
    Bool.or_eq_true] at h
  refine ⟨h.2, ?_⟩
  rcases h.1 with h1 | h1
  · exact Or.inl (rootD_aux N l pl h1)
  · right
    clear h
    induction W with
    | nil => simp at h1
    | cons w t ih =>
      change (Nat.lor (tab w) (List.rec (motive := fun _ => ℕ) 0 (fun w _ acc => Nat.lor (tab w) acc) t)).testBit l = true at h1
      rw [L5.lor_eq, Nat.testBit_or, Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · exact ⟨w, List.mem_cons_self .., h1⟩
      · obtain ⟨w', hw', h'⟩ := ih h1; exact ⟨w', List.mem_cons_of_mem _ hw', h'⟩

/-- **an accepted root frame with witness rows is valid** -/
theorem rootChkW_sound {O : LabelOrder} {Ω : R3RT.Spec.Dec22 → Prop} {c1 : ℕ} {c2T hkT tab : ℕ → ℕ} {pl W : List ℕ}
    {lastP : ℕ} {f : ℕ × ℕ × ℕ × ℕ × ℕ} (hc1 : Conf1OK O Ω c1) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → HOK O l (hkT l)) (hT : TabOKO O Ω tab) (h : rootChkW c1 c2T hkT tab pl W lastP f = true) :
    FrameOKO O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2 := by
  obtain ⟨S, D, N, U, d⟩ := f
  unfold rootChkW at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hinc, hS⟩, hS511⟩, hlast⟩, hself⟩, hN⟩, hD⟩, hU⟩, hd⟩, hW⟩ := h
  have hS511' : S < 2 ^ 511 := by rwa [L5.shl_eq, Nat.shiftLeft_eq, one_mul] at hS511
  have hbit : ∀ q, S.testBit q = true ↔ q ∈ pl := by
    intro q; rw [hS, maskL_testBit]; simp
  have hpl511 : ∀ p ∈ pl, p < 511 := by
    intro p hp
    have := (hbit p).mpr hp
    by_contra hc; push Not at hc
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hS511' (Nat.pow_le_pow_right (by norm_num) hc))] at this
    exact absurd this (by decide)
  have hd' : d = pcnt511 S := by rw [hd, L5.pcnt_eq_card]; rfl
  subst hd'
  refine rootFrame_okOW (by rwa [L5.shr_eq] at hlast) hS511' c1 hc1 c2T (fun p hp _ => hc2 p hp) ?_ ?_ ?_ ?_
  · intro p _ hSp w hw
    have := allB_spec hself p ((hbit p).mp hSp)
    simp only [Nat.beq_eq] at this
    have h2 : (Nat.land (Nat.shiftRight (c2T p) (Nat.mul 512 p)) R3RT.M511).testBit w = false := by rw [this]; simp
    rw [L5.land_eq, Nat.testBit_and, R3RT.m511_bit, decide_eq_true hw, Bool.and_true, L5.shr_eq] at h2
    exact h2
  · intro v w hb
    rw [hN, Nat.testBit_shiftRight] at hb
    rcases rootN_testBit c1 c2T _ pl hb with h1 | ⟨p, hp, h1⟩
    · left; rw [Nat.testBit_shiftRight]; exact h1
    · right; exact ⟨p, hpl511 p hp, (hbit p).mpr hp, by rw [Nat.testBit_shiftRight]; exact h1⟩
  · intro l hl
    rw [hD] at hl
    obtain ⟨hl5, h1 | ⟨w, hw, h1⟩⟩ := rootDW_testBit hl
    · obtain ⟨q, hq, h2⟩ := h1
      exact Or.inl ⟨q, hpl511 q hq, (hbit q).mpr hq, h2⟩
    · right
      refine ⟨tab w % 2 ^ 511, (tab w >>> 511) % 512, (hT w).2, ?_, ?_⟩
      · rw [Nat.testBit_mod_two_pow]; simp [hl5, h1]
      · have hf := allB_spec hW w hw
        simp only [Nat.beq_eq] at hf
        have hf' : ((Finset.range 511).filter (fun p => (tab w &&& S).testBit p = true)).card = (tab w >>> 511) % 512 := by
          rw [← L5.pcnt_eq_card]; exact hf
        rw [← hf']
        show ((Finset.range 511).filter (fun p => S.testBit p = true ∧ (tab w % 2 ^ 511).testBit p = true)).card = _
        apply congrArg Finset.card
        ext p
        simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_and, Nat.testBit_mod_two_pow, Bool.and_eq_true,
          decide_eq_true_eq]
        constructor
        · rintro ⟨hp, hS, -, hw'⟩; exact ⟨hp, hw', hS⟩
        · rintro ⟨hp, hw', hS⟩; exact ⟨hp, hS, hp, hw'⟩
  · rw [hU, hS]; exact rootU_eq hh pl hinc hpl511

theorem rootChkW_top {c1 : ℕ} {c2T hkT tab : ℕ → ℕ} {pl W : List ℕ} {lastP : ℕ} {f : ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : rootChkW c1 c2T hkT tab pl W lastP f = true) : f.1 >>> lastP = 1 := by
  unfold rootChkW at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  rw [← L5.shr_eq]; exact h.1.1.1.1.1.1.2

theorem rootChk0_sound {O : LabelOrder} {Ω : R3RT.Spec.Dec22 → Prop} {c1 : ℕ} {c2T hkT tab : ℕ → ℕ} {pl W : List ℕ}
    {lastP : ℕ} {f : ℕ × ℕ × ℕ × ℕ × ℕ} (hc1 : Conf1OK O Ω c1) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → HOK O l (hkT l)) (hT : TabOKO O Ω tab) (h : rootChk0 c1 c2T hkT tab pl W lastP f = true) :
    KD321.FrameOK0 O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2 := by
  obtain ⟨S, D, N, U, d⟩ := f
  cases pl with
  | nil =>
    simp only [rootChk0, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    subst h1 h2 h3 h4 h5
    exact Or.inr ⟨rfl, rfl, rfl, rfl, hc1⟩
  | cons p t => exact Or.inl (rootChkW_sound hc1 hc2 hh hT h)

/-! ## The item theorem in the contract's form -/

/-- **an accepted item gives the contract's segment**: root frame `f0` (`rootChk0`), a chain of accepted batches from
`[(f0, pend0)]` (the root's label `l0` pending) to a stack without pending labels, and the key's interface: root
`(f0.1 ||| 2^l0, l0)`, `lo = 0`, no ranges, external children `extL` -/
theorem itemK_segRef {E : Type} {O : LabelOrder} {Ω C : R3RT.Spec.Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk : E → ℕ}
    (H : Prop) (hnp : NpOK O np) (hh : ∀ l, l < 511 → HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (c1 : ℕ) (hc1 : H → Conf1OK O Ω c1) (hc2 : H → ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hExt : H → ExtSound O Ω C ext acc) (key : ℕ) (tab : ℕ → ℕ) (hT : H → TabOKO O Ω tab)
    (pl W : List ℕ) (lastP : ℕ) (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (hroot : rootChk0 c1 c2T hkT tab pl W lastP f0 = true)
    (l0 pend0 : ℕ) (hp0 : pend0.testBit l0 = true) (extL : List (ℕ × ℕ)) (out : List FrP)
    (hch : ChainK np c2T hkT cpT extL ext acc xk tab [(f0, pend0)] out) (hfin : pendZ out = true)
    (hkr : (R22N.SegI.ofKey key).root = (f0.1 ||| 2 ^ l0, l0)) (hlo : (R22N.SegI.ofKey key).lo = 0)
    (hrng : (R22N.SegI.ofKey key).rng = []) (hext : (R22N.SegI.ofKey key).ext = extL) :
    ∃ g : Top.Seg, g.root = (R22N.SegI.ofKey key).root ∧ g.lo = (R22N.SegI.ofKey key).lo ∧
      g.ext = {e | e ∈ (R22N.SegI.ofKey key).ext} ∧ g.rng = {p | p ∈ (R22N.SegI.ofKey key).rng} ∧
      (H → Top.SegOKO O C g) := by
  refine segRef_of_cov H key hlo hrng (fun hH => ?_)
  rw [hkr, hext]
  exact itemK_cov (Fr := fun f => KD321.FrameOK0 O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2) hnp
    (KD321.n5contract0 O Ω) (fun S D N U d hF => KD321.frameOK0_of S D N U d hF) tab (hT hH) (hc2 hH) hh hcp hCΩ
    (hExt hH) f0 (rootChk0_sound (hc1 hH) (hc2 hH) hh (hT hH) hroot) l0 pend0 hp0 out hch hfin

/-- **the kernel track's checker contract**: `R22B.SegRefH H O C (CheckedK …)` -/
theorem segRefHK_K {E : Type} {O : LabelOrder} {Ω C : R3RT.Spec.Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {ext : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk : E → ℕ}
    (H : Prop) (hnp : NpOK O np) (hh : ∀ l, l < 511 → HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (c1 : ℕ) (hc1 : H → Conf1OK O Ω c1) (hc2 : H → ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hExt : H → ∀ tab, TabOKO O Ω tab → ExtSound O Ω C (ext tab) acc) (TabV : (ℕ → ℕ) → Prop)
    (hTV : ∀ tab, TabV tab → H → TabOKO O Ω tab) :
    SegRefHK H O C (CheckedK np c2T hkT cpT ext acc xk c1 TabV) := by
  intro key ⟨tab, pl, W, lastP, f0, l0, pend0, extL, out, htv, hroot, hp0, hch, hfin, hkr, hlo, hrng, hext⟩
  exact itemK_segRef H hnp hh hcp hCΩ c1 hc1 hc2 (fun hH => hExt hH tab (hTV tab htv hH)) key tab (hTV tab htv) pl W lastP
    f0 hroot l0 pend0 hp0 extL out hch hfin hkr hlo hrng hext

end KB
