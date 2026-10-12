module
public import R22Port.U_d41d8cd98f00
public import KB.ItemII
/-! # KB.ExtII: the case-(II) extension of an OPEN node (kinds records, CANON, cut / look-ahead / leaf children)

The hook `KD.itemXS'` calls on an OPEN node's own frame `(S, D, N, U, d)` (top label `last`), datum `e = (b, its, cs, dks, xm)`:
* `KD.kindsNode S D U 0 d last b its`: the suffix break `b` (every child `≥ b` dead for `Ω`) and the PREFF / DOOM / TYPE records
  `its` (`tag | u << 2 | X << 11`; child `u` dead for `Ω ∩ CaseII`; TYPE needs `KD.TypeFacts`);
* `KD321.canonNode C3.LABT Sc S` for each L3 node record `Sc ∈ cs` (the order's key table at `--rord 123` is L3's own `C3.LABT`,
  `labO123`): every child in `canonKids C3.LABT Sc` dead for canonical decompositions;
* `dkidOK` for each dead child `k ∈ dks` (a node without child loop): its frame5 record's rows fetched from the job table by
  index (`withRec`, as `KD.nodeXO`), its cap-2 table and hit vector compared with the label tables, and its kind:
  `KD.cutNode` (node cuts 1 / 2 / 4 / 7 / 8 / 9 / 10; the row of cuts 2 / 10 is a job-table row), `KD.flookNode` (node cut 3,
  leaf code 4), `KD.leafNode` with the v7 record accepted by `BC7s.leafS` (leaf code 0).
`accII e` is the label mask of the children so accounted for.  **`extII_sound`**: `KD.ExtSound LO123 Ω C (extII c2T hkT tab)
accII` for a valid job table, valid label tables, `TypeFacts`, `C ⊆ Ω`, `C ⊆ CaseII` (leaves: nonzero `b`, `c` by RR's
`Top.dec22_bc HC.rr_all`). -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
noncomputable section
namespace KB
open R3RT.SpecO KD
open R3RT (M511 foldR mkD)

/-! ## The order's L3 key table -/

/-- at `--rord 123` the order's key is L3's own (`C3.LABT`) -/
theorem labO123 : KD321.LabO LO123 C3.LABT where
  key_eq := rfl
  lab_vec := fun l hl => KD.labN_vecL l hl
  inj := fun _ _ hu hv h => KD.labN_inj hu hv h

/-! ## Dead children -/

/-! ## Soundness -/

theorem withRec_sound {O : LabelOrder} {Ω : R3RT.Spec.Dec22 → Prop} (tab : ℕ → ℕ) (hT : TabOKO O Ω tab)
    (hdr : ℕ) (r2 r1 r0 : List ℕ) (k : ℕ → Bool) (h : withRec tab hdr r2 r1 r0 k = true) :
    ∃ rec, RecRowsOK O Ω rec ∧ (rec >>> 8) % 512 = (hdr >>> 8) % 512 ∧ k rec = true := by
  unfold withRec at h
  have hcap : ∀ y, L5O.capT tab y < 256 := fun y => (hT y).1
  obtain ⟨b2, hk2, hb2⟩ := L5O.foldR_sem tab 2 _ r2 0 0 0 0 (fun y _ => hcap y) h
  obtain ⟨b1, hk1, hb1⟩ := L5O.foldR_sem tab 1 _ r1 _ _ _ 0 (fun y _ => hcap y) hk2
  obtain ⟨b0, hk0, hb0⟩ := L5O.foldR_sem tab 0 _ r0 _ _ _ 0 (fun y _ => hcap y) hk1
  simp only [Bool.and_eq_true, Nat.beq_eq] at hk0
  obtain ⟨⟨⟨⟨hbad, hc2'⟩, hc1'⟩, hc0'⟩, hk⟩ := hk0
  obtain ⟨hb1z, _⟩ := hb0 hbad
  obtain ⟨hb2z, hcap1⟩ := hb1 hb1z
  obtain ⟨_, hcap2⟩ := hb2 hb2z
  simp only [Nat.zero_add] at hc2' hc1' hc0' hk
  have hn2 : r2.length = (hdr >>> 52) % 1024 := by rw [hc2', ← L5O.n5n2_eq]; rfl
  have hn1 : r1.length = (hdr >>> 32) % 1024 := by rw [hc1', ← L5O.n5n1_eq]; rfl
  have hnV : r0.length = (hdr >>> 22) % 1024 := by rw [hc0', ← L5O.n5nV_eq]; rfl
  have hm : Nat.add r0.length (Nat.add r1.length r2.length) = r0.length + r1.length + r2.length := by
    rw [L5.nadd_eq, L5.nadd_eq]; ring
  rw [hm] at hk
  set MB := ((0 * 2 ^ (512 * r2.length) + L5O.PK tab r2) * 2 ^ (512 * r1.length) + L5O.PK tab r1) * 2 ^ (512 * r0.length) +
    L5O.PK tab r0 with hMB
  set E := ((0 * 2 ^ (8 * r2.length) + L5O.QK tab 2 r2) * 2 ^ (8 * r1.length) + L5O.QK tab 1 r1) * 2 ^ (8 * r0.length) +
    L5O.QK tab 0 r0 with hE
  have hrecok := L5O.rec_ok tab hT hdr r2 r1 r0 hn2 hn1 hnV hcap2 hcap1 MB E rfl rfl
  have hMBlt : MB < 2 ^ (512 * (r0.length + r1.length + r2.length)) := by
    rw [hMB]; exact pack3_lt 512 _ _ _ _ _ _ (PK_lt tab r0) (PK_lt tab r1) (PK_lt tab r2)
  have hlo := L5O.rec_lo hdr MB E (r0.length + r1.length + r2.length) hMBlt
  exact ⟨_, hrecok, L5O.low_field _ _ 8 9 hlo (by norm_num), hk⟩

/-- the static data of an aggregate and of a child, from the tables' facts (`KD.statX_sound`'s parts) -/
theorem aggStat_sound {O : LabelOrder} {Ω : R3RT.Spec.Dec22 → Prop} {c2T : ℕ → ℕ} (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    {ag : Agg} (h : aggStat c2T ag = true) : C2OKO O Ω ag.1 ag.2.1 := by
  simp only [aggStat, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  rw [h.2]; exact hc2 _ h.1

theorem kidStat_sound {O : LabelOrder} {Ω : R3RT.Spec.Dec22 → Prop} {c2T : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ}
    (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) {c : KidX}
    (h : kidStat c2T cpT c = true) : KidXOKO O Ω c := by
  simp only [kidStat, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [h2]; exact hc2 _ h1, ?_⟩
  rw [tupBeq_spec h3]; exact hcp _ h1

/-- **a node cut 5 / 6 checked as an X part kills its child** (over any order and universe) -/
theorem xcutOK_sound {O : LabelOrder} {Ω : R3RT.Spec.Dec22 → Prop} {np c2T : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ}
    (hnp : NpOK O np) (tab : ℕ → ℕ) (hT : TabOKO O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) {S D N U d last : ℕ} (hF : FrameOKO O Ω S D N U d) (hS : S >>> last = 1)
    {x2 x1 nrows : List ℕ} {aggs : List Agg} {XL : List ℕ} {HP DEFP J : ℕ} {kid : KidX}
    (h : xcutOK np c2T cpT tab S D N U d last x2 x1 nrows aggs XL HP DEFP J kid = true) :
    ∀ A : R3RT.Spec.Dec22, Ω A → ¬ Continues O A S last kid.1 := by
  classical
  unfold xcutOK at h
  have hcap : ∀ y, L5O.capT tab y < 256 := fun y => (hT y).1
  obtain ⟨bx2, hkx2, hbx2⟩ := L5O.foldR_sem tab 2 _ x2 0 0 0 0 (fun y _ => hcap y) h
  obtain ⟨bx1, hkx1, hbx1⟩ := L5O.foldR_sem tab 1 _ x1 _ _ bx2 0 (fun y _ => hcap y) hkx2
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hkx1
  obtain ⟨⟨⟨⟨⟨hbad, hd⟩, hblkx⟩, hag⟩, hks⟩, hxp⟩ := hkx1
  obtain ⟨hbx2z, hcapx1⟩ := hbx1 hbad
  obtain ⟨_, hcapx2⟩ := hbx2 hbx2z
  simp only [Nat.zero_add] at hblkx hxp
  have hS511 : S < 2 ^ 511 := hF.2.1
  have hpc : L5.pcnt 512 S ≤ 127 := by
    have e := L5O.pcnt_and_eq S S hS511
    rw [Nat.and_self] at e
    rw [e, show ((Finset.range 511).filter (fun l => S.testBit l = true ∧ S.testBit l = true)) =
      ((Finset.range 511).filter (fun l => S.testBit l = true)) by ext l; simp, hF.2.2.1]
    exact hd
  set MBx := (0 * 2 ^ (512 * x2.length) + L5O.PK tab x2) * 2 ^ (512 * x1.length) + L5O.PK tab x1 with hMBx
  set Ex := (0 * 2 ^ (8 * x2.length) + L5O.QK tab 2 x2) * 2 ^ (8 * x1.length) + L5O.QK tab 1 x1 with hEx
  have hblkx' : L1.blocks MBx Ex (Nat.mul S L1.REP63) (Nat.div (Nat.add (x1.length + x2.length) 62) 63) = true := hblkx
  have hrowsx : ∀ q, q < x1.length + x2.length → RowOKO O Ω (E1S.dig 512 MBx q % 2 ^ 511)
      (L5.pcnt 512 (E1S.dig 512 MBx q &&& S) + (if q < x1.length then 1 else 2)) := by
    intro q hq
    have hb := L5.blocks_sound S hS511 hpc _ _ _ hblkx' q (by rw [L5.ndiv_eq, L5.nadd_eq]; omega)
    obtain ⟨hdm, hde⟩ := pack2_slot tab hT x2 x1 2 1 q hq
    rw [hdm]; rw [hde, hdm] at hb
    by_cases hq1 : q < x1.length
    · simp only [hq1, if_true] at hb ⊢
      have hc := hcapx1 _ (L5O.getD_rev_mem x1 q hq1)
      rw [Nat.mod_mod, ← hb, Nat.sub_add_cancel hc]
      exact (hT (x1.reverse.getD q 0)).2
    · simp only [hq1, if_false] at hb ⊢
      have hc := hcapx2 _ (L5O.getD_rev_mem x2 (q - x1.length) (by omega))
      rw [Nat.mod_mod, ← hb, Nat.sub_add_cancel hc]
      exact (hT (x2.reverse.getD (q - x1.length) 0)).2
  have hMBxlt : MBx < 2 ^ (512 * (x1.length + x2.length)) := by
    have := pack3_lt 512 _ _ _ _ _ _ (PK_lt tab []) (PK_lt tab x1) (PK_lt tab x2)
    rw [hMBx]; simpa [L5O.PK, E1S.pk] using this
  have hD : DictSemXO O Ω S last (mkD 0 MBx 0) (rposB 0 0 x1.length) := by
    intro p A hΩ hA
    by_cases hqn : p < x1.length + x2.length
    · have hr := hrowsx p hqn
      refine le_trans (row_aboveO hS hS511 A hΩ hA _ _ hr _ (fun l hl => by
        rw [testBit_mkD_hi _ _ _ p l (Nat.zero_le p) hl, Nat.sub_zero])) ?_
      unfold rposB
      split_ifs <;> omega
    · have hz : ∀ l, l < 511 → (mkD 0 MBx 0 p).testBit l = false := by
        intro l hl
        rw [testBit_mkD_hi _ _ _ p l (Nat.zero_le p) hl, Nat.sub_zero, E1S.testBit_dig 512 MBx p l (by omega)]
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le hMBxlt (Nat.pow_le_pow_right (by norm_num) (by push Not at hqn; nlinarith))
      have : ((Finset.range 511).filter (fun l => last < l ∧ R3RT.SpecO.Has O A l ∧
          (mkD 0 MBx 0 p).testBit l = true)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro l hl ⟨_, _, h3⟩
        rw [hz l (Finset.mem_range.mp hl)] at h3; exact absurd h3 (by decide)
      omega
  intro A hΩ
  exact xpartC_soundO hF hS hD (fun p => mkD_lt _ _ _ p) (fun ag hag' => aggStat_sound hc2 (allB_spec hag ag hag'))
    (fun c hc => by rw [List.mem_singleton] at hc; rw [hc]; exact kidStat_sound hc2 hcp hks) hnp hxp kid
    (List.mem_singleton_self _) A hΩ

/-- **the look-ahead cut with any tight list** (`KD.flook_soundU` needs a tight functional for `b_t, c_t ≠ 0`; here nonzero `b`, `c`
are a hypothesis, so `KD.core_sound_le` applies also when every functional through the term is slack-1) -/
theorem flookOK_soundU_nz {Ω : R3RT.Spec.Dec22 → Prop} {S D N U W d last t nT h2 : ℕ} {TL TY SL SY : List ℕ}
    (hF : FrameOKU Ω S D N U d) (hW : BlockOKU Ω S W) (h : flookOK S D U W d last t nT h2 TL TY SL SY = true) :
    ∀ A : R3RT.Spec.Dec22, Ω A → (∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) → ¬ R3RT.Spec.Below A S last := by
  intro A hΩ hnz hA
  unfold flookOK at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hS, hd⟩, ht⟩, ht5⟩, hTL⟩, hSL⟩, hw⟩ := h
  replace hS := beq_true hS
  have htl : t ≤ last := by
    by_contra hc; push Not at hc; rw [shr_one_bit hS t (by omega)] at ht; simp at ht; omega
  obtain ⟨s, hs⟩ := (has_iff A t).1 ((hA t ht5 htl).2 ht)
  have has : A.av s = R3RT.vecL t := by rw [← (labT_spec A s).2, hs]
  have hpair : ∀ X, X < 512 → RootCheck.hitsOne X (R3RT.vecL t) = true →
      RootSound.pair (RootSound.toM3 X) ((fun s => RootSound.toM3 (A.av s)) s) = 1 := by
    intro X hX hh; simp only; rw [has, RootSound.pair_eq_one_iff X _ hX (R3RT.vecL_lt t)]; exact hh
  refine core_sound_le A.dec s (hnz s).1 (hnz s).2 nT TL SL h2 ?_ ?_ ?_ ?_ hw
  · intro X hX; obtain ⟨_, h0, h1, _, _⟩ := fbAll_mem _ _ hTL X hX; exact ⟨h1, by omega⟩
  · intro X hX; obtain ⟨_, h0, h1, _, _⟩ := fbAll_mem _ _ hSL X hX; exact ⟨h1, by omega⟩
  · intro X hX
    obtain ⟨Y, h0, h1, h2', h3⟩ := fbAll_mem _ _ hTL X hX
    refine ⟨hpair X h1 h2', le_antisymm ?_ (hitSet_ge A X h0 h1)⟩
    rw [hitSet_card A X h1]; simpa using fb_soundU hF hW hS hd h0 h1 h3 A hΩ hA
  · intro X hX
    obtain ⟨Y, h0, h1, h2', h3⟩ := fbAll_mem _ _ hSL X hX
    refine ⟨hpair X h1 h2', ?_⟩
    rw [hitSet_card A X h1]; exact fb_soundU hF hW hS hd h0 h1 h3 A hΩ hA

/-- **a dead child is dead**: the node `(S ||| 2^u, u)` is empty for case-(II) decompositions of `Ω` with nonzero `b`, `c` -/
theorem dkidOK_sound {Ω : R3RT.Spec.Dec22 → Prop} {np c2T hkT tab : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ}
    (hnp : NpOK LO123 np) (hT : TabOKU Ω tab) (hc2 : ∀ l, l < 511 → C2OKU Ω l (c2T l))
    (hh : ∀ l, l < 511 → HOK LO123 l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (hTF : TypeFacts)
    {S D N U d last : ℕ} (hF : FrameOKU Ω S D N U d) (hS : S >>> last = 1) (k : DKid)
    (h : dkidOK np c2T hkT cpT tab S D N U d last k = true) :
    last < dkLab k ∧ dkLab k < 511 ∧ ∀ A : R3RT.Spec.Dec22, Ω A → R3RT.Spec.CaseII A → (∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) →
      ¬ R3RT.Spec.Below A (S ||| 2 ^ dkLab k) (dkLab k) := by
  obtain ⟨c2, h', hdr, r2, r1, r0, pay⟩ := k
  cases pay with
  | xcut x2 x1 nrows aggs XL HP DEFP J kid =>
    unfold dkidOK at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨hlu, hu5⟩, _⟩, _⟩, hkl, hx⟩ := h
    refine ⟨hlu, hu5, fun A hΩ _ _ hB => ?_⟩
    have := xcutOK_sound hnp tab hT hc2 hcp hF hS hx A hΩ
    rw [hkl] at this
    exact this ⟨hlu, hu5, hB⟩
  | cut kind arg i =>
    unfold dkidOK at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨hlu, hu5⟩, hc2e⟩, hhe⟩, hw⟩ := h
    obtain ⟨rec, hrec, hlr, hk⟩ := withRec_sound tab hT hdr r2 r1 r0 _ hw
    have hlab : dkLab (c2, h', hdr, r2, r1, r0, DPay.cut kind arg i) = (rec >>> 8) % 512 := by
      show Nat.land (Nat.shiftRight hdr 8) 511 = _; rw [land511, L5.shr_eq, hlr]
    rw [hlab] at hlu hu5 hc2e hhe ⊢
    refine ⟨hlu, hu5, fun A hΩ hII _ => ?_⟩
    have hc2' : C2OKU Ω ((rec >>> 8) % 512) c2 := by rw [hc2e]; exact hc2 _ hu5
    have hh' : HOK LO123 ((rec >>> 8) % 512) h' := by rw [hhe]; exact hh _ hu5
    have hrow : RowOKU Ω (Nat.mod (tab i) (Nat.shiftLeft 1 511)) (Nat.mod (Nat.shiftRight (tab i) 511) 512) := by
      rw [show Nat.shiftLeft 1 511 = 2 ^ 511 by rw [L5.shl_eq, Nat.shiftLeft_eq, one_mul], L5.shr_eq]
      exact (hT i).2
    exact cutNode_soundU L5O.frame5_spec hF hc2' hh' hrec hTF hrow hk A hΩ hII
  | flook t nT h2 TL TY SL SY =>
    unfold dkidOK at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨hlu, hu5⟩, hc2e⟩, hhe⟩, hw⟩ := h
    obtain ⟨rec, hrec, hlr, hk⟩ := withRec_sound tab hT hdr r2 r1 r0 _ hw
    have hlab : dkLab (c2, h', hdr, r2, r1, r0, DPay.flook t nT h2 TL TY SL SY) = (rec >>> 8) % 512 := by
      show Nat.land (Nat.shiftRight hdr 8) 511 = _; rw [land511, L5.shr_eq, hlr]
    rw [hlab] at hlu hu5 hc2e hhe ⊢
    refine ⟨hlu, hu5, fun A hΩ _ hnz => ?_⟩
    have hc2' : C2OKU Ω ((rec >>> 8) % 512) c2 := by rw [hc2e]; exact hc2 _ hu5
    have hh' : HOK LO123 ((rec >>> 8) % 512) h' := by rw [hhe]; exact hh _ hu5
    have hk5 : R3RT.frame5 S D N U d c2 h' rec (fun S' D' _ U' =>
        flookOK S' D' U' 0 (Nat.succ d) (Nat.land (Nat.shiftRight rec 8) 511) t nT h2 TL TY SL SY) = true := hk
    obtain ⟨D', hF', hk'⟩ := (L5O.frame5_spec : Frame5Spec LO123 Ω) S D N U d c2 h' rec _ hF hc2' hh' hrec hk5
    rw [last_eq] at hk'
    exact flookOK_soundU_nz hF' (blockOKU_zero Ω _) hk' A hΩ hnz
  | leaf R =>
    unfold dkidOK at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨⟨hlu, hu5⟩, hc2e⟩, hhe⟩, hw⟩ := h
    obtain ⟨rec, hrec, hlr, hk⟩ := withRec_sound tab hT hdr r2 r1 r0 _ hw
    have hlab : dkLab (c2, h', hdr, r2, r1, r0, DPay.leaf R) = (rec >>> 8) % 512 := by
      show Nat.land (Nat.shiftRight hdr 8) 511 = _; rw [land511, L5.shr_eq, hlr]
    rw [hlab] at hlu hu5 hc2e hhe ⊢
    refine ⟨hlu, hu5, fun A _ _ hnz => ?_⟩
    have hc2' : C2OKU Ω ((rec >>> 8) % 512) c2 := by rw [hc2e]; exact hc2 _ hu5
    have hh' : HOK LO123 ((rec >>> 8) % 512) h' := by rw [hhe]; exact hh _ hu5
    simp only [dpayOK, Bool.and_eq_true] at hk
    exact leafNode_soundU L5O.frame5_spec hF hc2' hh' hrec hk.1 hk.2 A hnz

theorem canonM_testBit {u : ℕ} : ∀ (cs : List ℕ), (canonM cs).testBit u = true →
    ∃ Sc ∈ cs, (KD321.canonKids C3.LABT Sc).testBit u = true
  | [], h => by simp [canonM] at h
  | Sc :: t, h => by
    change (Nat.lor (KD321.canonKids C3.LABT Sc) (canonM t)).testBit u = true at h
    rw [L5.lor_eq, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨Sc, List.mem_cons_self .., h⟩
    · obtain ⟨Sc', hm, h'⟩ := canonM_testBit t h
      exact ⟨Sc', List.mem_cons_of_mem _ hm, h'⟩

/-- **the case-(II) extension is sound** (`KD.ExtSound`) -/
theorem extII_sound {Ω C : R3RT.Spec.Dec22 → Prop} {np c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} (tab : ℕ → ℕ)
    (hnp : NpOK LO123 np) (hT : TabOKU Ω tab) (hc2 : ∀ l, l < 511 → C2OKU Ω l (c2T l))
    (hh : ∀ l, l < 511 → HOK LO123 l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (hTF : TypeFacts)
    (hCΩ : ∀ A, C A → Ω A) (hCII : ∀ A, C A → R3RT.Spec.CaseII A)
    (hnz : ∀ A : R3RT.Spec.Dec22, C A → ∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) :
    ExtSound LO123 Ω C (extII np c2T hkT cpT tab) accII := by
  intro S D N U d last e hF hS hl511 hd h u hu1 hu2 hacc
  obtain ⟨b, its, cs, dks, xm⟩ := e
  unfold extII at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hkn, hcn⟩, hdk⟩ := h
  obtain ⟨hsuf, hits⟩ := kindsNode_soundU hF (blockOKU_zero Ω S) hTF hkn
  have hS511 : S < 2 ^ 511 := (frameOKO_basic hF).2.1
  unfold accII at hacc
  simp only [L5.lor_eq, Nat.testBit_or, Bool.or_eq_true] at hacc
  rcases hacc with (hb | hi) | (hc | hk)
  · -- the suffix break
    rw [testBit_geM, decide_eq_true_eq] at hb
    exact fun A _ hC => hsuf u hb.1 A (hCΩ A hC)
  · -- PREFF / DOOM / TYPE
    obtain ⟨it, hit, hiu⟩ := (maskL_testBit _ u its).mp hi
    intro A _ hC
    have := hits it hit A (hCΩ A hC) ((caseII_iff A).1 (hCII A hC))
    rwa [hiu] at this
  · -- CANON
    obtain ⟨Sc, hSc, hk⟩ := canonM_testBit cs hc
    intro A hcan _
    exact KD321.canonNode_sound labO123 hS hS511 (allB_spec hcn Sc hSc) u hk A hcan
  · -- dead children
    obtain ⟨k, hkm, hku⟩ := (maskL_testBit _ u dks).mp hk
    obtain ⟨_, _, hdead⟩ := dkidOK_sound hnp hT hc2 hh hcp hTF hF hS k (allB_spec hdk k hkm)
    intro A _ hC hcont
    rw [← hku] at hcont
    exact hdead A (hCΩ A hC) (hCII A hC) (hnz A hC) hcont.2.2

/-! ## Case (II) -/

/-- **the case-(II) extension under the case's facts**: `Ω = C = CaseK 14 22`, nonzero `b`, `c` from RR's tables -/
theorem extII_soundII {np c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} (tab : ℕ → ℕ) (hnp : NpOK LO123 np)
    (hT : TabOKU (CaseK 14 22) tab) (hc2 : ∀ l, l < 511 → C2OKU (CaseK 14 22) l (c2T l))
    (hh : ∀ l, l < 511 → HOK LO123 l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (hTF : TypeFacts) :
    ExtSound LO123 (CaseK 14 22) (CaseK 14 22) (extII np c2T hkT cpT tab) accII :=
  extII_sound tab hnp hT hc2 hh hcp hTF (fun _ h => h) (fun _ h => h.1) (fun A _ => Top.dec22_bc HC.rr_all A)

/-! ## The contract of case (II) -/

/-- an accepted job table has valid rows under the class facts of case (II) (`L5II.table_specII`) -/
theorem tabVII_sound (tab : ℕ → ℕ) (h : TabVII tab) (hcf : ClassFactsC (CaseK 14 22) HC.cLBII) :
    TabOKO LO123 (CaseK 14 22) tab := by
  obtain ⟨chunk, N, nch, hent, hch, hN, hok⟩ := h
  exact L5II.table_specII HC.cLBII (by simp [HC.cLBII]) (fun c hc => if_neg hc) chunk tab N nch hent hch hN hcf hok

/-- the facts of case (II), as `Top.rank_ge_23_L479`'s `hsegII` takes them -/
abbrev HII : Prop := ClassFactsC (CaseK 14 22) HC.cLBII ∧ KD.TypeFacts

/-- **the kernel track's checker contract for case (II)** (`R22B.SegRefH HII LO123 (CaseK 14 22)`): items checked with
`KD.batchX`'s node check, the case-(II) extension (`extII`: kinds records, CANON, cut / look-ahead / leaf children), R3's per-job
table, the root frame and the key's interface.  The static facts left: the label tables' hit vectors and window constants
(unconditional) and the cap-1 / cap-2 tables (under the class facts, e.g. by `L5II.bindQ_specII`) -/
theorem segRefII {c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {c1 : ℕ} (hh : ∀ l, l < 511 → HOK LO123 l (hkT l))
    (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (hc1 : HII → Conf1OK LO123 (CaseK 14 22) c1)
    (hc2 : HII → ∀ l, l < 511 → C2OKU (CaseK 14 22) l (c2T l)) :
    SegRefHK HII LO123 (CaseK 14 22)
      (CheckedK R3RT.nperpL c2T hkT cpT (fun tab => extII R3RT.nperpL c2T hkT cpT tab) accII xkII c1 TabVII) :=
  segRefHK_K HII npOK_123 hh hcp (fun _ h => h) c1 hc1 hc2
    (fun hH tab hT => extII_soundII tab npOK_123 hT (hc2 hH) hh hcp hH.2) TabVII (fun tab h hH => tabVII_sound tab h hH.1)


/-! ## Items with a dead root -/

theorem rootChk_top {c1 : ℕ} {c2T hkT : ℕ → ℕ} {pl : List ℕ} {lastP : ℕ} {f : ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : rootChk c1 c2T hkT pl lastP f = true) : f.1 >>> lastP = 1 := by
  unfold rootChk at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  rw [← L5.shr_eq]; exact h.1.1.1.1.1.2

/-- **an item with a dead root is a certified segment**: its only node is the root, dead (`EmptyO`) by its record -/
theorem segRefDeadII {c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {c1 : ℕ} (hh : ∀ l, l < 511 → HOK LO123 l (hkT l))
    (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hc1 : HII → Conf1OK LO123 (CaseK 14 22) c1) (hc2 : HII → ∀ l, l < 511 → KD.C2OKU (CaseK 14 22) l (c2T l)) :
    SegRefHK HII LO123 (CaseK 14 22) (CheckedDeadK R3RT.nperpL c2T hkT cpT c1 TabVII) := by
  intro key ⟨tab, pl, W, lastP, f0, k, htv, hroot, hdk, hkr, hlo, hrng, hext⟩
  refine ⟨⟨(R22N.SegI.ofKey key).root, (R22N.SegI.ofKey key).lo, ∅, {(R22N.SegI.ofKey key).root},
    {e | e ∈ (R22N.SegI.ofKey key).ext}, {p | p ∈ (R22N.SegI.ofKey key).rng}⟩, rfl, rfl, rfl, rfl, fun hH => ?_⟩
  have hT : TabOKO LO123 (CaseK 14 22) tab := tabVII_sound tab htv hH.1
  have hF := rootChkW_sound (hc1 hH) (hc2 hH) hh hT hroot
  obtain ⟨_, _, hdead⟩ := dkidOK_sound npOK_123 hT (hc2 hH) hh hcp hH.2 hF (rootChkW_top hroot) k hdk
  refine ⟨Or.inr rfl, fun h0 => by simp [hlo] at h0, fun p hp => by simp [hrng] at hp, fun n hn => ?_,
    fun n hn => absurd hn (Set.notMem_empty n)⟩
  rw [Set.mem_singleton_iff] at hn
  subst hn
  rw [hkr]
  intro A _ hC hB
  exact hdead A hC hC.1 (Top.dec22_bc HC.rr_all A) hB

end KB
