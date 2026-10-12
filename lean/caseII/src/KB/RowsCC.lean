module
public import R22Port.U_d41d8cd98f00
public import L5.Bind5II
public import S4.TopCC
/-! # KB.RowsCC: case (II)'s row interface and table facts for the CC route (`L479.cLBW L`, s443/S4/TopCC.lean)

The CC route's case-(II) table is C3eD with the context caps `L`: `(c, R) ∈ L` puts class `c` at `R + 1` (the first entry for a
class counts). Its kept rows are C3eD's (`RT.K3eD`, ids `< 3781613`) with every row of a class `c` of `L` whose cap is
`22 - R` lowered to `21 - R`, in place (py/mkcc.py writes the search's files the same way; RT's class field selects exactly
the rows the data lowers, checked on 443 and 436 + 422).
* `KCC.rowECC L`: the row interface (`R3RT.tabOKQ`'s `rowE`): RT's label-form entry, minus `2^511` (cap one less) when the row is
  lowered (`lowB`), 0 beyond the table.
* `KCC.entry_soundΩk`: RT's entry theorem at any bound `k` of the class fact (the transport does not use the bound).
* `KCC.rowECC_ok`: every value is a valid row, under the class facts of `cLBW L` (`hL`: `cLB c ≤ R + 1` for the caps of `L`).
* **`KCC.table_specCC`**, **`KCC.bindQ_specCC`**: `R3RT.SpecO.TableSpec` / `BindQSpec` for `rowECC L` at the bounds `cLBW L`,
  the forms `KB`'s job tables and label-table bindings consume. -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
noncomputable section
namespace KCC
open E1S Finset R3RT.Spec RootSound BC4 BC5 Classical L5 L5O L5W L5II
variable {O : R3RT.SpecO.LabelOrder} {Ω : Dec22 → Prop}

/-! ## The row interface -/

/-- the row `e` is lowered: the first entry `(c, R)` of `L` with `c = eCls e` has `eCap e = 22 - R` -/
def lowB (L : List (ℕ × ℕ)) (e : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ acc => cond (Nat.beq (_root_.RT.eCls e) p.1) (Nat.beq (_root_.RT.eCap e) (Nat.sub 22 p.2)) acc) L

/-- **the CC route's row interface**: RT's rows, the lowered ones with cap one less, 0 beyond -/
def rowECC (L : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  Bool.rec 0 (Bool.rec (RT.K3eDL.entry i) (Nat.sub (RT.K3eDL.entry i) (Nat.shiftLeft 1 511)) (lowB L (RT.K3eD.entry i)))
    (Nat.blt i 3781613)

theorem lowB_spec (L : List (ℕ × ℕ)) (e : ℕ) (h : lowB L e = true) :
    ∃ p, L.find? (fun p => p.1 == _root_.RT.eCls e) = some p ∧ _root_.RT.eCap e = 22 - p.2 := by
  induction L with
  | nil => exact absurd h (by simp [lowB])
  | cons p t ih =>
    change cond (Nat.beq (_root_.RT.eCls e) p.1) (Nat.beq (_root_.RT.eCap e) (Nat.sub 22 p.2)) (lowB t e) = true at h
    cases hc : Nat.beq (_root_.RT.eCls e) p.1
    · rw [hc, cond_false] at h
      obtain ⟨p', hp', hc'⟩ := ih h
      refine ⟨p', ?_, hc'⟩
      rw [List.find?_cons]
      have : (p.1 == _root_.RT.eCls e) = false := by
        rw [beq_eq_false_iff_ne]; intro h'
        rw [← h', show Nat.beq p.1 p.1 = true from Nat.beq_refl p.1] at hc; exact absurd hc (by decide)
      rw [this]; exact hp'
    · rw [hc, cond_true, Nat.beq_eq] at h
      refine ⟨p, ?_, by simpa using h⟩
      rw [List.find?_cons]
      have : (p.1 == _root_.RT.eCls e) = true := by
        rw [Nat.beq_eq] at hc; simp [hc]
      rw [this]

/-- a lowered row's class has the bound `R + 1` in `cLBW L` -/
theorem cLBW_of_lowB (L : List (ℕ × ℕ)) (e : ℕ) (h : lowB L e = true) :
    ∃ R, L479.cLBW L (_root_.RT.eCls e) = R + 1 ∧ _root_.RT.eCap e = 22 - R ∧ (_root_.RT.eCls e, R) ∈ L := by
  obtain ⟨p, hf, hc⟩ := lowB_spec L e h
  have hp1 : p.1 = _root_.RT.eCls e := by have := List.find?_some hf; simpa using this
  refine ⟨p.2, ?_, hc, ?_⟩
  · unfold L479.cLBW; rw [hf]
  · rw [← hp1]; exact List.mem_of_find?_eq_some hf

/-- `cLBW L` is at least C3eD's bound, when every cap of `L` is at least its class's bound -/
theorem cLB_le_cLBW (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) (c : ℕ) :
    _root_.RT.cLB _root_.RT.K3eD_Cls.CL c ≤ L479.cLBW L c := by
  unfold L479.cLBW
  cases hf : L.find? (fun p => p.1 == c) with
  | some p =>
    have hp1 : p.1 = c := by have := List.find?_some hf; simpa using this
    simp only
    have := hL p (List.mem_of_find?_eq_some hf); rw [hp1] at this; exact this
  | none =>
    simp only
    split_ifs with h18
    · subst h18; rw [show _root_.RT.cLB _root_.RT.K3eD_Cls.CL 18 = 9 by decide +kernel]; omega
    · exact le_refl _

/-! ## Entries at any bound -/

/-- **RT's entry theorem at any bound**: the class fact at `k` gives the entry's dual the fact at `k` -/
theorem entry_soundΩk (hΩ : RT.Om.RankInv Ω) (CL e k : ℕ) (hcls : ∀ A, Ω A → RT.Om.FactD (_root_.RT.kM CL (_root_.RT.eCls e)) k A)
    (h : _root_.RT.entryOK 22 CL e = true) : ∀ A, Ω A → RT.Om.FactD (_root_.RT.dualM e) k A := by
  unfold _root_.RT.entryOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hsd⟩, hP⟩, hQ⟩, hmap⟩, _⟩ := h
  have hgen := _root_.RT.mapsIn_spec CL e hmap
  intro A hA
  have hA' : Ω (RT.Om.move A (_root_.RT.eT e) hP hQ) := hΩ A _ (RT.Om.move_rk A (_root_.RT.eT e) hP hQ) hA
  have hk := hcls _ hA'
  unfold RT.Om.FactD at hk ⊢
  refine le_trans hk (Finset.card_le_card ?_)
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  cases e2 : (_root_.RT.dualM e).testBit (A.av s)
  · rfl
  · exfalso
    rw [← hsd] at e2
    obtain ⟨_, hin⟩ := _root_.RT.spanM_ind e
      (fun w => _root_.RT.inK CL (_root_.RT.eCls e) (C3.actN (_root_.RT.eT e) (_root_.RT.eP e) (_root_.RT.eQ e) w) = true)
      (by show _root_.RT.inK CL (_root_.RT.eCls e) (C3.actN (_root_.RT.eT e) (_root_.RT.eP e) (_root_.RT.eQ e) 0) = true
          rw [_root_.RT.actN_zero]; exact _root_.RT.inK_zero _ _) hgen
      (fun x y hx hy h1 h2 => by
        show _root_.RT.inK CL (_root_.RT.eCls e) (C3.actN (_root_.RT.eT e) (_root_.RT.eP e) (_root_.RT.eQ e) (x ^^^ y)) = true
        rw [_root_.RT.actN_xor _ _ _ _ _ hx hy]; exact _root_.RT.inK_xor (C3.actN_lt _ _ _ _) (C3.actN_lt _ _ _ _) h1 h2)
      (A.av s) e2
    have hin' : _root_.RT.inK CL (_root_.RT.eCls e) (C3.actN (_root_.RT.eT e) (_root_.RT.eP e) (_root_.RT.eQ e) (A.av s)) = true := hin
    have hs' : (_root_.RT.kM CL (_root_.RT.eCls e)).testBit ((RT.Om.move A (_root_.RT.eT e) hP hQ).av s) = false := hs
    simp only [RT.Om.move] at hs'
    rw [_root_.RT.kM_testBit _ _ _ (C3.actN_lt _ _ _ _), hin'] at hs'
    exact absurd hs' (by decide)

/-! ## Rows -/

/-- a kept row with the fact `22 - k` on its dual is a valid row of cap `k` (labels by `--rord 123`) -/
theorem rowOK_of_fact (hO : Is123 O) (i : ℕ) (hi : i < 3781613) (k : ℕ)
    (hf : ∀ A, Ω A → RT.Om.FactD (_root_.RT.dualM (RT.K3eD.entry i)) (22 - k) A) :
    R3RT.SpecO.RowOK O Ω (RT.K3eDL.entry i % 2 ^ 511) k := by
  intro A hA
  have hf1 := hf A hA
  unfold RT.Om.FactD at hf1
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 22)))
    (p := fun s => (_root_.RT.dualM (RT.K3eD.entry i)).testBit (A.av s) = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at hsplit
  have hPc : (Finset.univ.filter (fun s : Fin 22 => (_root_.RT.dualM (RT.K3eD.entry i)).testBit (A.av s) = true)).card ≤ k := by
    omega
  refine le_trans ?_ hPc
  apply Finset.card_le_card_of_injOn (fun l => if h : R3RT.SpecO.Has O A l then Classical.choose h.2 else 0)
  · intro l hl
    beta_reduce
    simp only [R3RT.SpecO.inMask, Finset.coe_filter, mem_filter, mem_range] at hl
    obtain ⟨hl1, hbit, hH⟩ := hl
    rw [dif_pos hH]
    have hs := Classical.choose_spec hH.2
    simp only [Finset.coe_filter, Finset.mem_coe, mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [hs, hO l hl1, ← _root_.RT.K3eDL.labMask_spec i hi l hl1]
    rw [Nat.testBit_mod_two_pow] at hbit; simpa [hl1] using hbit
  · intro l hl l' hl' heq
    simp only [R3RT.SpecO.inMask, Finset.coe_filter, Finset.mem_coe, mem_filter, mem_range] at hl hl'
    beta_reduce at heq
    simp only [dif_pos hl.2.2, dif_pos hl'.2.2] at heq
    have h1 := Classical.choose_spec hl.2.2.2
    have h2 := Classical.choose_spec hl'.2.2.2
    rw [heq] at h1
    exact O.vec_inj l l' hl.1 hl'.1 (h1.symm.trans h2)

/-- the class facts of the CC table -/
def HclsCC (L : List (ℕ × ℕ)) (Ω : Dec22 → Prop) : Prop :=
  ∀ c, c < 496 → ∀ A, Ω A → RT.Om.FactD (_root_.RT.kM _root_.RT.K3eD_Cls.CL c) (L479.cLBW L c) A

theorem K3eDL_split (i : ℕ) (hi : i < 3781613) :
    RT.K3eDL.entry i = RT.K3eDL.entry i % 2 ^ 511 + _root_.RT.eCap (RT.K3eD.entry i) * 2 ^ 511 := by
  have h := _root_.RT.K3eDL.capL_spec i hi
  rw [Nat.shiftRight_eq_div_pow] at h
  have := Nat.mod_add_div (RT.K3eDL.entry i) (2 ^ 511)
  rw [h] at this; linarith

/-- **every value of the CC row interface is a valid row** with cap `< 32` -/
theorem rowECC_ok (hO : Is123 O) (hΩ : RT.Om.RankInv Ω) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) (hL5 : ∀ p ∈ L, p.1 < 496)
    (hcls : HclsCC L Ω) (i : ℕ) :
    (rowECC L i >>> 511) % 512 < 32 ∧ R3RT.SpecO.RowOK O Ω (rowECC L i % 2 ^ 511) ((rowECC L i >>> 511) % 512) := by
  have hcls0 : HclsΩ Ω := fun c hc A hA => le_trans (cLB_le_cLBW L hL c) (hcls c hc A hA)
  unfold rowECC
  cases hi : Nat.blt i 3781613
  · simp only [Nat.zero_shiftRight, Nat.zero_mod]; exact ⟨by norm_num, L5II.rowOK_zero⟩
  · have hi' : i < 3781613 := Nat.blt_eq.mp hi
    have hsp := K3eDL_split i hi'
    have hm := Nat.mod_lt (RT.K3eDL.entry i) (show 0 < 2 ^ 511 by positivity)
    have hcap : _root_.RT.eCap (RT.K3eD.entry i) < 32 := Nat.mod_lt _ (by norm_num)
    cases hl : lowB L (RT.K3eD.entry i)
    · -- not lowered: RT's row
      simp only
      refine ⟨?_, L5II.rowOK_K3eDL hO hΩ hcls0 i hi'⟩
      rw [_root_.RT.K3eDL.capL_spec i hi']; omega
    · -- lowered: cap one less, from the class fact at R + 1
      simp only
      obtain ⟨R, hR, hcR, hmem⟩ := cLBW_of_lowB L _ hl
      set e := RT.K3eD.entry i with he
      set m := RT.K3eDL.entry i % 2 ^ 511 with hmdef
      rcases Nat.eq_zero_or_pos (_root_.RT.eCap e) with h0 | hpos
      · -- a lowered row of cap 0 becomes the 0 entry
        have hz : Nat.sub (RT.K3eDL.entry i) (Nat.shiftLeft 1 511) = 0 := by
          rw [hsp, h0]; simp only [Nat.zero_mul, Nat.add_zero]
          rw [show Nat.shiftLeft 1 511 = 2 ^ 511 by rw [show Nat.shiftLeft 1 511 = 1 <<< 511 from rfl, Nat.one_shiftLeft]]
          exact Nat.sub_eq_zero_of_le hm.le
        rw [hz]; simp only [Nat.zero_shiftRight, Nat.zero_mod]; exact ⟨by norm_num, L5II.rowOK_zero⟩
      · have hP : Nat.shiftLeft 1 511 = 2 ^ 511 := by rw [show Nat.shiftLeft 1 511 = 1 <<< 511 from rfl, Nat.one_shiftLeft]
        have hc1 : _root_.RT.eCap e = (_root_.RT.eCap e - 1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
        have hsp' : RT.K3eDL.entry i = (m + (_root_.RT.eCap e - 1) * 2 ^ 511) + 2 ^ 511 := by
          rw [hsp]; conv_lhs => rw [hc1]
          rw [Nat.add_mul, one_mul, Nat.add_assoc]
        have hv : Nat.sub (RT.K3eDL.entry i) (Nat.shiftLeft 1 511) = m + (_root_.RT.eCap e - 1) * 2 ^ 511 := by
          rw [hP, Nat.sub_eq, hsp', Nat.add_sub_cancel]
        have hlo : (m + (_root_.RT.eCap e - 1) * 2 ^ 511) % 2 ^ 511 = m := by
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
        have hhi : ((m + (_root_.RT.eCap e - 1) * 2 ^ 511) >>> 511) % 512 = _root_.RT.eCap e - 1 := by
          rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hm,
            Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [hv, hlo, hhi]
        refine ⟨by omega, rowOK_of_fact hO i hi' _ ?_⟩
        have hN : _root_.RT.K3eD.N = 3781613 := by decide +kernel
        have hc5 : _root_.RT.eCls e < 496 := by have := hL5 _ hmem; simpa using this
        have hk : 22 - (_root_.RT.eCap e - 1) = R + 1 := by omega
        rw [hk]
        refine entry_soundΩk hΩ _root_.RT.K3eD_Cls.CL e (R + 1) (fun A hA => ?_) (RT.K3eD.entry_ok i (by rw [hN]; exact hi'))
        have := hcls _ hc5 A hA
        rwa [hR] at this

theorem rowECC_lt (L : List (ℕ × ℕ)) (i : ℕ) : rowECC L i < 2 ^ 516 := by
  unfold rowECC
  cases hi : Nat.blt i 3781613
  · simp only; positivity
  · have hi' : i < 3781613 := Nat.blt_eq.mp hi
    have hc := L5II.K3eDL_cap i hi'
    cases lowB L (RT.K3eD.entry i)
    · exact L5II.entry_lt516 _ hc
    · simp only
      exact lt_of_le_of_lt (Nat.sub_le _ _) (L5II.entry_lt516 _ hc)

/-! ## The per-job table -/

/-- **the per-job table check for the CC route** -/
theorem table_specCCN (hO : Is123 O) (hΩ : RT.Om.RankInv Ω) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) (hL5 : ∀ p ∈ L, p.1 < 496) (hcls : HclsCC L Ω)
    (chunk entry : ℕ → ℕ) (N nch : ℕ)
    (hent : ∀ i, entry i = (chunk (i / 64) >>> (552 * (i % 64))) % 2 ^ 552) (hch : ∀ q, nch ≤ q → chunk q = 0)
    (hN : ∀ i, N ≤ i → entry i = 0) (hok : R3RT.tabOKQ (rowECC L) chunk 64 N nch = true) :
    R3RT.SpecO.TabOK O Ω entry := by
  have hM552 : R3RT.M552Q = 2 ^ 552 - 1 := by decide +kernel
  have hM520 : R3RT.M520 = 2 ^ 520 - 1 := by decide +kernel
  have hspec := L5II.tabOKQ_spec _ _ _ _ _ hok
  intro i
  have hz : entry i = 0 → (entry i >>> 511) % 512 < 256 ∧ R3RT.SpecO.RowOK O Ω (entry i % 2 ^ 511) ((entry i >>> 511) % 512) := by
    intro h0; rw [h0]; simp only [Nat.zero_shiftRight, Nat.zero_mod]; exact ⟨by norm_num, L5II.rowOK_zero⟩
  by_cases hiN : N ≤ i
  · exact hz (hN i hiN)
  by_cases hq : nch ≤ i / 64
  · apply hz; rw [hent i, hch _ hq]; simp
  have h1 := hspec (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num))
  rcases h1 with h1 | h1
  · exfalso; rw [Nat.ble_eq, nadd_eq, nmul_eq] at h1; omega
  · have ht : Nat.land (Nat.shiftRight (chunk (i / 64)) (Nat.mul 552 (i % 64))) R3RT.M552Q = entry i := by
      rw [hent i, land_eq, shr_eq, nmul_eq, hM552, Nat.and_two_pow_sub_one_eq_mod]
    rw [ht, Nat.beq_eq, land_eq, shr_eq, hM520, Nat.and_two_pow_sub_one_eq_mod] at h1
    obtain ⟨hcap, hrow⟩ := rowECC_ok hO hΩ L hL hL5 hcls (entry i >>> 520)
    rw [h1] at hcap hrow
    have e1 : entry i % 2 ^ 520 % 2 ^ 511 = entry i % 2 ^ 511 := by
      rw [show (2 : ℕ) ^ 520 = 2 ^ 511 * 2 ^ 9 by norm_num, Nat.mod_mul_right_mod]
    have e2 : ((entry i % 2 ^ 520) >>> 511) % 512 = (entry i >>> 511) % 512 := by
      apply Nat.eq_of_testBit_eq; intro j
      rw [show (512 : ℕ) = 2 ^ 9 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
        Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
      by_cases hj : j < 9
      · simp [hj, show 511 + j < 520 by omega]
      · simp [hj]
    rw [e1, e2] at hrow; rw [e2] at hcap
    exact ⟨by omega, hrow⟩

/-! ## The static exclusion tables -/

theorem row_of_bindCC (hO : Is123 O) (hΩ : RT.Om.RankInv Ω) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) (hL5 : ∀ p ∈ L, p.1 < 496) (hcls : HclsCC L Ω)
    (cap : ℕ) (hcap : cap < 32) (id m : ℕ) (hm : m >>> 511 = 0)
    (hrow : rowECC L id = m ||| (cap <<< 511)) (hc0 : 0 < cap) : R3RT.SpecO.RowOK O Ω m cap := by
  have hm' : m < 2 ^ 511 := by
    rw [Nat.shiftRight_eq_div_pow] at hm
    by_contra hc
    have := Nat.div_pos (by omega : 2 ^ 511 ≤ m) (by positivity : 0 < 2 ^ 511)
    omega
  have hsum : m ||| (cap <<< 511) = cap * 2 ^ 511 + m := by
    rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hm', Nat.shiftLeft_eq]
  obtain ⟨_, hR⟩ := rowECC_ok hO hΩ L hL hL5 hcls id
  rw [hrow, hsum] at hR
  have e1 : (cap * 2 ^ 511 + m) % 2 ^ 511 = m := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm']
  have e2 : ((cap * 2 ^ 511 + m) >>> 511) % 512 = cap := by
    rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hm',
      Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at hR
  exact hR

/-- **the static-table binding for the CC route** -/
theorem bindQ_specCCN (hO : Is123 O) (hΩ : RT.Om.RankInv Ω) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) (hL5 : ∀ p ∈ L, p.1 < 496) (hcls : HclsCC L Ω)
    (q : ℕ) (rows : List (ℕ × List ℕ)) (stored DC : ℕ) :
    (q < 511 → R3RT.bindQ (rowECC L) q 2 rows stored DC = true → R3RT.SpecO.C2OK O Ω q stored) ∧
    (R3RT.bindQ (rowECC L) 511 1 rows stored DC = true → R3RT.SpecO.Conf1OK O Ω stored) := by
  have core : ∀ (q' cap : ℕ), 0 < cap → cap < 32 → R3RT.bindQ (rowECC L) q' cap rows stored DC = true →
      ∀ v w, v < 511 → w < 511 → (stored >>> (512 * v)).testBit w = true →
        ∃ r ∈ rows, v ∈ r.2 ∧ v ≠ q' ∧ R3RT.SpecO.RowOK O Ω (R3RT.ptsMask r.2) cap ∧ (R3RT.ptsMask r.2).testBit w = true ∧
          (q' = 511 ∨ (R3RT.ptsMask r.2).testBit q' = true) := by
    intro q' cap hc0 hc32 hb v w hv hw hbit
    unfold R3RT.bindQ at hb
    obtain ⟨Tf, hk, hrows, hbits⟩ := L5II.rowsFold_sem _ _ _ _ rows 0 hb
    rw [Nat.beq_eq, land_eq] at hk
    rw [Nat.testBit_shiftRight, ← hk, Nat.testBit_and, Bool.and_eq_true] at hbit
    rcases hbits _ hbit.1 with h0 | ⟨r, hr, u, hu, huq, hb'⟩
    · simp at h0
    · obtain ⟨hm, hrowE, hq⟩ := hrows r hr
      have hm' : R3RT.ptsMask r.2 < 2 ^ 511 := by
        rw [Nat.shiftRight_eq_div_pow] at hm
        by_contra hc
        have := Nat.div_pos (by omega : 2 ^ 511 ≤ R3RT.ptsMask r.2) (by positivity : 0 < 2 ^ 511)
        omega
      obtain ⟨rfl, hwb⟩ := L5II.slot_bit _ _ _ _ hm' hw hb'
      exact ⟨r, hr, hu, huq, row_of_bindCC hO hΩ L hL hL5 hcls cap hc32 r.1 _ hm hrowE hc0, hwb, hq⟩
  constructor
  · intro hq hb v w hv hw hwq hwv hbit
    obtain ⟨r, _, hvr, hvq, hR, hwb, hqb⟩ := core q 2 (by norm_num) (by norm_num) hb v w hv hw hbit
    refine ⟨R3RT.ptsMask r.2, hR, ?_, (L5II.ptsMask_testBit _ _).mpr hvr, hwb⟩
    rcases hqb with h | h
    · omega
    · exact h
  · intro hb v w hv hw hwv hbit
    obtain ⟨r, _, hvr, _, hR, hwb, _⟩ := core 511 1 (by norm_num) (by norm_num) hb v w hv hw hbit
    exact ⟨R3RT.ptsMask r.2, hR, (L5II.ptsMask_testBit _ _).mpr hvr, hwb⟩

/-- the CC table's class facts from `ClassFactsC Ω (cLBW L)` -/
theorem hclsCC_of (L : List (ℕ × ℕ)) (h : R3RT.SpecO.ClassFactsC Ω (L479.cLBW L)) : HclsCC L Ω :=
  fun c hc A hA => h A hA c hc

/-- **`TableSpec` for the CC route** (`rowECC L`, rank-invariant `Ω`, the bounds `cLBW L`) -/
theorem table_specCC (hO : Is123 O) (hΩ : RT.Om.RankInv Ω) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) (hL5 : ∀ p ∈ L, p.1 < 496) :
    R3RT.SpecO.TableSpec O Ω (rowECC L) (L479.cLBW L) :=
  fun chunk entry N nch hent hch hN hcls hok =>
    table_specCCN hO hΩ L hL hL5 (hclsCC_of L hcls) chunk entry N nch hent hch hN hok

/-- **`BindQSpec` for the CC route** -/
theorem bindQ_specCC (hO : Is123 O) (hΩ : RT.Om.RankInv Ω) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) (hL5 : ∀ p ∈ L, p.1 < 496) :
    R3RT.SpecO.BindQSpec O Ω (rowECC L) (L479.cLBW L) :=
  fun q rows stored DC hcls => bindQ_specCCN hO hΩ L hL hL5 (hclsCC_of L hcls) q rows stored DC

end KCC
#print axioms KCC.table_specCC
#print axioms KCC.bindQ_specCC
