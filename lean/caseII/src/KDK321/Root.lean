module
public import R22Port.U_d41d8cd98f00
public import KD321.Kinds
public import L5.Frame5O
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
/-! # KDK321.Root (kinds-only name of KD321.Root): frames at depth-1 roots (the empty prefix as parent)

The parent of a depth-1 node `(2^l, l)` is the empty prefix.  The converters build its frame as `(0, 0, CONF1, 0, 0)`, which
is not `FrameOK` (`0 < S`), so `L5O.node5_spec` / `L5O.frame5_spec` do not apply to the depth-1 record itself.  Here:
* **`node5_spec_empty`**: `node5` from `(0, 0, c1, 0, 0)` with `Conf1OK c1` gives `Node5Spec`'s conclusion at the child
  `(0 ||| 2^last, D', c1 ||| c2, 0 + h, 0 + 1)`: a valid child frame, the kills, and the continuation;
* **`frame5_spec_empty`**: the same for `frame5` (a depth-1 cut node or leaf);
* `FrameOK0` (a valid frame or the empty one) and **`node5_spec0`**, **`frame5_spec0`**: `Node5Spec` / `Frame5Spec` with
  `FrameOK0` input, for batch checkers whose bottom frame is the empty prefix;
* `frame_root`: `(2^l, 0, 0, packU (2^l), 1)` is a valid frame (no dead labels, no conflicts), e.g. for a depth-1 cut node
  checked on its own (`root_cut7`; job 2 of case (I), `root462_empty`).
The proofs follow `L5O.node5_spec` / `frame5_spec`, with the parent's semantics replaced by `Conf1OK` (no `Below` needed). -/
noncomputable section
namespace KD321
open E1S Finset R3RT.Spec RootSound BC4 BC5 Classical L5 L5O
variable {O : R3RT.SpecO.LabelOrder} {Ω : Dec22 → Prop}

theorem packU_zeroO (O : R3RT.SpecO.LabelOrder) : R3RT.SpecO.packU O 0 = 0 := by
  unfold R3RT.SpecO.packU R3RT.SpecO.hits; simp

/-- the dead mask of the child of the empty frame -/
theorem dead_ok0 (N rec : ℕ) (A : Dec22) (hΩ : Ω A) (hlast : n5last rec < 511) (hc1 : R3RT.SpecO.Conf1OK O Ω N)
    (hrows : ∀ i < n5m rec, R3RT.SpecO.RowOK O Ω (dig 512 (n5MB rec) i % 2 ^ 511)
      (pcnt 512 (dig 512 (n5MB rec) i &&& (0 ||| 2 ^ n5last rec)) +
        (if i < n5nV rec then 0 else if i < n5nV rec + n5n1 rec then 1 else 2)))
    (hB : R3RT.SpecO.Below O A (0 ||| 2 ^ n5last rec) (n5last rec)) :
    ∀ l, n5last rec < l → l < 511 → (n5D' 0 N rec).testBit l = true → ¬ R3RT.SpecO.Has O A l := by
  intro l hl1 hl2 hD hA
  have hS'lt : 0 ||| 2 ^ n5last rec < 2 ^ 511 := by rw [Nat.zero_or]; exact Nat.pow_lt_pow_right (by norm_num) hlast
  have hbits : ∀ l', (0 ||| 2 ^ n5last rec).testBit l' = true → l' ≤ n5last rec := by
    intro l' h'; rw [Nat.zero_or, Nat.testBit_two_pow] at h'; simp at h'; omega
  unfold n5D' at hD
  rw [lor_eq, lor_eq, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true] at hD
  rcases hD with (hD | hD) | hD
  · simp at hD
  · rw [dig_eq_ops, dig_testBit] at hD
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
    obtain ⟨m, hm, hmv, hmw⟩ := hc1 (n5last rec) l hlast hl2 (by omega) (by rw [Nat.testBit_shiftRight]; exact hD.2)
    have hAl := below_has_last A 0 _ hB hlast
    have hsub : ({n5last rec, l} : Finset ℕ) ⊆ R3RT.SpecO.inMask O A m := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      simp only [R3RT.SpecO.inMask, mem_filter, mem_range]
      rcases hx with rfl | rfl
      · exact ⟨hlast, hmv, hAl⟩
      · exact ⟨hl2, hmw, hA⟩
    have hc := le_trans (card_le_card hsub) (hm A hΩ)
    rw [card_pair (by omega)] at hc
    omega
  · have hnV : n5nV rec ≤ 1024 := by
      rw [n5nV_eq]; have := Nat.mod_lt (rec >>> 22) (show 0 < 1024 by norm_num); omega
    obtain ⟨i, hi, hbit⟩ := orFold_bit (n5MB rec) (n5nV rec) hnV l hD
    have him : i < n5m rec := by unfold n5m; rw [nadd_eq, nadd_eq]; omega
    have hR := hrows i him
    rw [if_pos hi, Nat.add_zero] at hR
    have := row_count A hΩ _ (n5last rec) _ _ hS'lt hbits hB hR {l} (by
      intro x hx; rw [mem_singleton] at hx; subst hx
      refine ⟨hA, hbit, ?_⟩
      cases h' : (0 ||| 2 ^ n5last rec).testBit x
      · rfl
      · have := hbits x h'; omega)
    simp at this

/-- the conflict table of the child of the empty frame -/
theorem conf_ok0 (N c2 last : ℕ) (A : Dec22) (hΩ : Ω A) (hlast : last < 511) (hc1 : R3RT.SpecO.Conf1OK O Ω N)
    (hC2 : R3RT.SpecO.C2OK O Ω last c2) (hB : R3RT.SpecO.Below O A (0 ||| 2 ^ last) last) :
    ∀ v w, v < 511 → w < 511 → (0 ||| 2 ^ last).testBit v = false → (0 ||| 2 ^ last).testBit w = false → v ≠ w →
      ((N ||| c2) >>> (512 * v)).testBit w = true → R3RT.SpecO.Has O A v → ¬ R3RT.SpecO.Has O A w := by
  intro v w hv hw hSv hSw hvw hbit hAv hAw
  rw [testBit_or_pow, Bool.or_eq_false_iff] at hSv hSw
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Bool.or_eq_true] at hbit
  rcases hbit with hb | hb
  · obtain ⟨m, hm, hmv, hmw⟩ := hc1 v w hv hw (Ne.symm hvw) (by rw [Nat.testBit_shiftRight]; exact hb)
    have hsub : ({v, w} : Finset ℕ) ⊆ R3RT.SpecO.inMask O A m := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      simp only [R3RT.SpecO.inMask, mem_filter, mem_range]
      rcases hx with rfl | rfl
      · exact ⟨hv, hmv, hAv⟩
      · exact ⟨hw, hmw, hAw⟩
    have hc := le_trans (card_le_card hsub) (hm A hΩ)
    rw [card_pair hvw] at hc
    omega
  · have hwl : w ≠ last := by intro h; rw [h] at hSw; simp at hSw
    have hvl : v ≠ last := by intro h; rw [h] at hSv; simp at hSv
    obtain ⟨m, hm, hml, hmv, hmw⟩ := hC2 v w hv hw hwl (Ne.symm hvw) (by rw [Nat.testBit_shiftRight]; exact hb)
    have hAl := below_has_last A 0 last hB hlast
    have hsub : ({last, v, w} : Finset ℕ) ⊆ R3RT.SpecO.inMask O A m := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      simp only [R3RT.SpecO.inMask, mem_filter, mem_range]
      rcases hx with rfl | rfl | rfl
      · exact ⟨hlast, hml, hAl⟩
      · exact ⟨hv, hmv, hAv⟩
      · exact ⟨hw, hmw, hAw⟩
    have hc := le_trans (card_le_card hsub) (hm A hΩ)
    rw [card_insert_of_notMem (by simp [Ne.symm hvl, Ne.symm hwl]), card_pair hvw] at hc
    omega

/-- **`node5` from the empty prefix.** -/
theorem node5_spec_empty (N c2 h suf rec : ℕ) (ks : List ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool)
    (hc1 : R3RT.SpecO.Conf1OK O Ω N) (hC2 : R3RT.SpecO.C2OK O Ω ((rec >>> 8) % 512) c2)
    (hH : R3RT.SpecO.HOK O ((rec >>> 8) % 512) h) (hR : R3RT.SpecO.RecRowsOK O Ω rec)
    (hn : R3RT.node5 0 0 N 0 0 c2 h suf rec ks k = true) :
    ∃ D', R3RT.SpecO.FrameOK O Ω (0 ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (0 + h) (0 + 1) ∧
      R3RT.SpecO.KillsOK O Ω (0 ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) ks ∧
      k (0 ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (0 + h) = true := by
  set last := (rec >>> 8) % 512 with hlastdef
  rw [node5_eq] at hn
  simp only [Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hl1, _⟩, hd⟩, _⟩, _⟩, _⟩, hblk⟩, hkill⟩, hk⟩ := hn
  have hlast_eq : n5last rec = last := n5last_eq rec
  have hl : last < 511 := by rw [← hlast_eq]; exact Nat.blt_eq.mp hl1
  have hSlt : (0 : ℕ) < 2 ^ last := Nat.two_pow_pos _
  have hd' : n5d rec = 0 + 1 := by rw [Nat.beq_eq] at hd; exact hd
  have hS'eq : Nat.lor 0 (Nat.shiftLeft 1 (n5last rec)) = 0 ||| 2 ^ last := by
    rw [lor_eq, shl_eq, Nat.shiftLeft_eq, Nat.one_mul, hlast_eq]
  have hS'lt : 0 ||| 2 ^ last < 2 ^ 511 := by rw [Nat.zero_or]; exact Nat.pow_lt_pow_right (by norm_num) hl
  have hbits : ∀ l', (0 ||| 2 ^ last).testBit l' = true → l' ≤ last := by
    intro l' h'; rw [Nat.zero_or, Nat.testBit_two_pow] at h'; simp at h'; omega
  have hcard : ((range 511).filter (fun l => (0 ||| 2 ^ last).testBit l = true)).card = 0 + 1 := by
    rw [card_or_pow 0 last hSlt hl]; simp
  have hpc : pcnt 512 (0 ||| 2 ^ last) ≤ 127 := by rw [pcnt_eq_card511 _ hS'lt, hcard]; omega
  rw [hS'eq] at hblk hk
  have hrows := rows_ok rec (0 ||| 2 ^ last) hS'lt hpc hR hblk
  have hSl : (0 : ℕ).testBit last = false := Nat.zero_testBit last
  have hlastOf : lastOf (0 ||| 2 ^ last) = last := lastOf_or 0 last hSlt
  have hdead : ∀ A : Dec22, Ω A → R3RT.SpecO.Below O A (0 ||| 2 ^ last) last →
      ∀ l, last < l → l < 511 → (n5D' 0 N rec).testBit l = true → ¬ R3RT.SpecO.Has O A l := by
    intro A hΩ hB
    have := dead_ok0 N rec A hΩ (by rw [hlast_eq]; exact hl) hc1 (by rw [hlast_eq]; exact hrows) (by rw [hlast_eq]; exact hB)
    rw [hlast_eq] at this; exact this
  have hconf : ∀ A : Dec22, Ω A → R3RT.SpecO.Below O A (0 ||| 2 ^ last) last →
      ∀ v w, v < 511 → w < 511 → (0 ||| 2 ^ last).testBit v = false → (0 ||| 2 ^ last).testBit w = false → v ≠ w →
        ((N ||| c2) >>> (512 * v)).testBit w = true → R3RT.SpecO.Has O A v → ¬ R3RT.SpecO.Has O A w :=
    fun A hΩ hB => conf_ok0 N c2 last A hΩ hl hc1 hC2 hB
  refine ⟨n5D' 0 N rec, ⟨by rw [Nat.zero_or]; positivity, hS'lt, hcard,
    by rw [packU_or 0 last h hSl hl hH, packU_zeroO], fun A hΩ hB => ?_⟩, ?_, ?_⟩
  · rw [hlastOf] at hB ⊢
    exact ⟨hdead A hΩ hB, hconf A hΩ hB⟩
  · -- the kills, as in `L5O.node5_spec`
    intro kr hkr A hΩ hCont
    have hnu : Nat.sub 21 (n5d rec) ≤ 32768 := by rw [nsub_eq]; omega
    obtain ⟨Y, hKF, hcnt⟩ := kills5_sem _ _ _ _ _ _ ks hnu hkill kr hkr
    obtain ⟨hw0, hu511, hexu, hcvu, hY⟩ := hKF
    set u := kr % 512 with hu
    have hBl := cont_below A _ _ _ hCont
    have hlu : last < u := hCont.1
    rw [hlast_eq] at hw0
    set X1 := dig 512 (winXS (n5last rec) (n5D' 0 N rec) (Nat.lor N c2)) (u - Nat.succ (n5last rec)) with hX1
    have hX1b : ∀ l, u < l → R3RT.SpecO.Has O A l → X1.testBit l = true := by
      intro l hul hAl
      rw [hX1, winXS_bit _ _ _ (by rw [hlast_eq]; exact hl) _ (by rw [hlast_eq]; omega), hlast_eq]
      rw [show last + 1 + (u - Nat.succ last) = u by omega]
      have h1 : decide (u < l ∧ l < 511) = true := decide_eq_true ⟨hul, hAl.1⟩
      have h2 : (n5D' 0 N rec).testBit l = false := by
        cases hb : (n5D' 0 N rec).testBit l
        · rfl
        · exact absurd hAl (hdead A hΩ hBl l (by omega) hAl.1 hb)
      have h3 : (dig 512 (Nat.lor N c2) u).testBit l = false := by
        cases hb : (dig 512 (Nat.lor N c2) u).testBit l
        · rfl
        · exfalso
          rw [dig_testBit, Bool.and_eq_true] at hb
          have hSu : (0 ||| 2 ^ last).testBit u = false := by
            cases h' : (0 ||| 2 ^ last).testBit u
            · rfl
            · have := hbits u h'; omega
          have hSw : (0 ||| 2 ^ last).testBit l = false := by
            cases h' : (0 ||| 2 ^ last).testBit l
            · rfl
            · have := hbits l h'; omega
          exact hconf A hΩ hBl u l hu511 hAl.1 hSu hSw (by omega)
            (by rw [Nat.testBit_shiftRight, ← lor_eq]; exact hb.2) (cont_has A _ _ _ hCont) hAl
      rw [h1, h2, h3]; rfl
    have hMC : ∀ i, dig 512 (n5MC rec) i = dig 512 (n5MB rec) (n5nV rec + i) := by
      intro i; unfold n5MC; rw [shr_eq, shl_eq, Nat.shiftLeft_eq, show n5nV rec * 2 ^ 9 = 512 * n5nV rec by ring, dig_shr]
    have hME : ∀ i, dig 512 (n5ME rec) i = if i < n5n1 rec then dig 512 (n5MC rec) i else 0 := by
      intro i; unfold n5ME; rw [mask_ops, dig_mod_pow]
    have hMBz : ∀ j, n5m rec ≤ j → dig 512 (n5MB rec) j = 0 := by
      intro j hj; rw [n5MB_eq, dig_mod_pow, if_neg (by omega)]
    have hmsum : n5m rec = n5nV rec + n5n1 rec + n5n2 rec := by unfold n5m; rw [nadd_eq, nadd_eq]; ring
    apply kill_dead A hΩ (0 ||| 2 ^ last) last u (0 + 1) hS'lt hbits hcard hCont X1 Y
      ((kr >>> 9) % 32) ((kr >>> 14) % 32)
      (fun i => dig 512 (n5ME rec) ((kr >>> 19 >>> (10 * i)) % 1024))
      (fun i => dig 512 (n5MC rec) ((kr >>> 19 >>> (10 * ((kr >>> 9) % 32 + i))) % 1024)) hX1b
    · intro i hi
      have hb := hexu i hi
      refine ⟨hb, ?_⟩
      rw [hME] at hb ⊢
      split at hb
      · rename_i hlt
        rw [if_pos hlt, hMC]
        rw [hMC] at hb
        have := hrows (n5nV rec + (kr >>> 19 >>> (10 * i)) % 1024) (by omega)
        rw [if_neg (by omega), if_pos (by omega)] at this
        exact this
      · simp at hb
    · intro i hi
      have hb := hcvu i hi
      rw [hMC] at hb ⊢
      set c := (kr >>> 19 >>> (10 * ((kr >>> 9) % 32 + i))) % 1024 with hc
      by_cases hc1' : c < n5n1 rec
      · rw [decide_eq_true hc1'] at hb
        have := hrows (n5nV rec + c) (by omega)
        rw [if_neg (by omega), if_pos (by omega)] at this
        simp only [Bool.not_true] at hb
        rw [hb]; simpa using this
      · rw [decide_eq_false hc1'] at hb
        simp only [Bool.not_false] at hb
        by_cases hcm : n5nV rec + c < n5m rec
        · have := hrows (n5nV rec + c) hcm
          rw [if_neg (by omega), if_neg (by omega)] at this
          rw [hb]; simpa [Nat.add_assoc] using this
        · rw [hMBz _ (by omega)] at hb; simp at hb
    · intro l
      rw [hY l]
    · rw [← hd']; exact hcnt
  · rw [lor_eq, nadd_eq] at hk; exact hk

/-- **`frame5` from the empty prefix** (a depth-1 cut node or leaf). -/
theorem frame5_spec_empty (N c2 h rec : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool)
    (hc1 : R3RT.SpecO.Conf1OK O Ω N) (hC2 : R3RT.SpecO.C2OK O Ω ((rec >>> 8) % 512) c2)
    (hH : R3RT.SpecO.HOK O ((rec >>> 8) % 512) h) (hR : R3RT.SpecO.RecRowsOK O Ω rec)
    (hn : R3RT.frame5 0 0 N 0 0 c2 h rec k = true) :
    ∃ D', R3RT.SpecO.FrameOK O Ω (0 ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (0 + h) (0 + 1) ∧
      k (0 ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (0 + h) = true := by
  set last := (rec >>> 8) % 512 with hlastdef
  rw [frame5_eq] at hn
  simp only [Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨hl1, _⟩, hd⟩, h30⟩, hblk⟩, hk⟩ := hn
  have h30' : (rec >>> 32) % 2 ^ 30 = 0 := by
    rw [Nat.beq_eq, land_eq, shr_eq, show (1073741823 : ℕ) = 2 ^ 30 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h30
    exact h30
  have hn1 : n5n1 rec = 0 := by
    rw [n5n1_eq]
    have : (rec >>> 32) % 1024 = ((rec >>> 32) % 2 ^ 30) % 1024 := by
      rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num))]
    rw [this, h30', Nat.zero_mod]
  have hn2 : n5n2 rec = 0 := by
    rw [n5n2_eq]
    have e : rec >>> 52 = (rec >>> 32) >>> 20 := by rw [← Nat.shiftRight_add]
    have : (rec >>> 32 >>> 20) % 1024 = ((rec >>> 32) % 2 ^ 30) >>> 20 % 1024 := by
      apply Nat.eq_of_testBit_eq; intro j
      simp only [show (1024 : ℕ) = 2 ^ 10 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      by_cases hj : j < 10
      · simp [hj, show 20 + j < 30 by omega]
      · simp [hj]
    rw [e, this, h30', Nat.zero_shiftRight, Nat.zero_mod]
  have hm : n5m rec = n5nV rec := by unfold n5m; rw [hn1, hn2]; rfl
  have hMB : f5MB rec = n5MB rec := by
    unfold f5MB; rw [mask_ops, n5MB_eq, hm, shr_eq]
  have hE : f5E rec = n5E rec := by
    rw [n5E_eq, hm]; unfold f5E
    rw [land_eq, shr_eq, shr_eq, nsub_eq, shl_eq, shl_eq, shl_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
      Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, mul_comm (n5nV rec) (2 ^ 9), mul_comm (n5nV rec) (2 ^ 3)]
  have hD : f5D' 0 N rec = n5D' 0 N rec := by
    unfold f5D' n5D'
    rw [hMB, mask_ops (n5MB rec) (n5nV rec), n5MB_eq, hm, Nat.mod_mod]
  have hblk' : L1.blocks (n5MB rec) (n5E rec) (Nat.mul (Nat.lor 0 (Nat.shiftLeft 1 (n5last rec))) L1.REP63)
      (Nat.div (Nat.add (n5m rec) 62) 63) = true := by rw [← hMB, ← hE, hm]; exact hblk
  have hlast_eq : n5last rec = last := n5last_eq rec
  have hl : last < 511 := by rw [← hlast_eq]; exact Nat.blt_eq.mp hl1
  have hSlt : (0 : ℕ) < 2 ^ last := Nat.two_pow_pos _
  have hd' : n5d rec = 0 + 1 := by rw [Nat.beq_eq] at hd; exact hd
  have hS'eq : Nat.lor 0 (Nat.shiftLeft 1 (n5last rec)) = 0 ||| 2 ^ last := by
    rw [lor_eq, shl_eq, Nat.shiftLeft_eq, Nat.one_mul, hlast_eq]
  have hS'lt : 0 ||| 2 ^ last < 2 ^ 511 := by rw [Nat.zero_or]; exact Nat.pow_lt_pow_right (by norm_num) hl
  have hcard : ((range 511).filter (fun l => (0 ||| 2 ^ last).testBit l = true)).card = 0 + 1 := by
    rw [card_or_pow 0 last hSlt hl]; simp
  have hpc : pcnt 512 (0 ||| 2 ^ last) ≤ 127 := by rw [pcnt_eq_card511 _ hS'lt, hcard]; omega
  rw [hS'eq] at hblk' hk
  have hrows := rows_ok rec (0 ||| 2 ^ last) hS'lt hpc hR hblk'
  have hSl : (0 : ℕ).testBit last = false := Nat.zero_testBit last
  have hlastOf : lastOf (0 ||| 2 ^ last) = last := lastOf_or 0 last hSlt
  refine ⟨f5D' 0 N rec, ⟨by rw [Nat.zero_or]; positivity, hS'lt, hcard,
    by rw [packU_or 0 last h hSl hl hH, packU_zeroO], fun A hΩ hB => ?_⟩, ?_⟩
  · rw [hlastOf] at hB ⊢
    refine ⟨?_, conf_ok0 N c2 last A hΩ hl hc1 hC2 hB⟩
    have := dead_ok0 N rec A hΩ (by rw [hlast_eq]; exact hl) hc1 (by rw [hlast_eq]; exact hrows) (by rw [hlast_eq]; exact hB)
    rw [hlast_eq, ← hD] at this; exact this
  · rw [lor_eq, nadd_eq] at hk; exact hk

/-! ## Valid or empty frames -/

/-- a valid frame, or the empty prefix's frame `(0, 0, N, 0, 0)` with `Conf1OK N` -/
def FrameOK0 (O : R3RT.SpecO.LabelOrder) (Ω : Dec22 → Prop) (S D N U d : ℕ) : Prop :=
  R3RT.SpecO.FrameOK O Ω S D N U d ∨ (S = 0 ∧ D = 0 ∧ U = 0 ∧ d = 0 ∧ R3RT.SpecO.Conf1OK O Ω N)

theorem frameOK0_of (S D N U d : ℕ) (h : R3RT.SpecO.FrameOK O Ω S D N U d) : FrameOK0 O Ω S D N U d := Or.inl h

/-- **`Node5Spec` with a valid-or-empty input frame.** -/
theorem node5_spec0 (S D N U dP c2 h suf rec : ℕ) (ks : List ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool)
    (hF : FrameOK0 O Ω S D N U dP) (hC2 : R3RT.SpecO.C2OK O Ω ((rec >>> 8) % 512) c2)
    (hH : R3RT.SpecO.HOK O ((rec >>> 8) % 512) h) (hR : R3RT.SpecO.RecRowsOK O Ω rec)
    (hn : R3RT.node5 S D N U dP c2 h suf rec ks k = true) :
    ∃ D', R3RT.SpecO.FrameOK O Ω (S ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (U + h) (dP + 1) ∧
      R3RT.SpecO.KillsOK O Ω (S ||| 2 ^ ((rec >>> 8) % 512)) ((rec >>> 8) % 512) ks ∧
      k (S ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (U + h) = true := by
  rcases hF with hF | ⟨rfl, rfl, rfl, rfl, hc1⟩
  · exact L5O.node5_spec S D N U dP c2 h suf rec ks k hF hC2 hH hR hn
  · exact node5_spec_empty N c2 h suf rec ks k hc1 hC2 hH hR hn

/-- **`Frame5Spec` with a valid-or-empty input frame.** -/
theorem frame5_spec0 (S D N U dP c2 h rec : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Bool)
    (hF : FrameOK0 O Ω S D N U dP) (hC2 : R3RT.SpecO.C2OK O Ω ((rec >>> 8) % 512) c2)
    (hH : R3RT.SpecO.HOK O ((rec >>> 8) % 512) h) (hR : R3RT.SpecO.RecRowsOK O Ω rec)
    (hn : R3RT.frame5 S D N U dP c2 h rec k = true) :
    ∃ D', R3RT.SpecO.FrameOK O Ω (S ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (U + h) (dP + 1) ∧
      k (S ||| 2 ^ ((rec >>> 8) % 512)) D' (N ||| c2) (U + h) = true := by
  rcases hF with hF | ⟨rfl, rfl, rfl, rfl, hc1⟩
  · exact L5O.frame5_spec S D N U dP c2 h rec k hF hC2 hH hR hn
  · exact frame5_spec_empty N c2 h rec k hc1 hC2 hH hR hn

/-! ## A depth-1 node on its own -/

/-- `(2^l, 0, 0, packU (2^l), 1)` is a valid frame: no dead labels, no conflicts -/
theorem frame_root (O : R3RT.SpecO.LabelOrder) (Ω : Dec22 → Prop) (l : ℕ) (hl : l < 511) :
    R3RT.SpecO.FrameOK O Ω (2 ^ l) 0 0 (R3RT.SpecO.packU O (2 ^ l)) 1 := by
  refine ⟨Nat.two_pow_pos l, Nat.pow_lt_pow_right (by norm_num) hl, ?_, rfl, fun A _ _ => ⟨fun _ _ _ h => by simp at h,
    fun _ _ _ _ _ _ _ h => by simp at h⟩⟩
  have := card_or_pow 0 l (Nat.two_pow_pos l) hl
  rw [Nat.zero_or] at this; rw [this]; simp

/-- a depth-1 node cut by the rank-1 window with no dead labels -/
theorem root_cut7 {r1m nr1m : ℕ} (hR : KD321.R1OK O r1m nr1m) (l lo hi : ℕ) (hl : l < 511)
    (h : KD321.winOKO r1m nr1m (2 ^ l) 0 1 l lo hi = true) :
    ∀ A : Dec22, Ω A → R3RT.SpecO.CaseK lo hi A → ¬ R3RT.SpecO.Below O A (2 ^ l) l :=
  KD321.winO_sound hR (frame_root O Ω l hl) (by rw [Nat.shiftRight_eq_div_pow, Nat.div_self (Nat.two_pow_pos l)]) (by norm_num) h

/-- **job 2 of case (I)**: the depth-1 node of label 462 (code 1, the first rank-1 label) has no decomposition with at most 12
rank-1 first factors (all 22 labels would be rank-1) -/
theorem root462_empty : ∀ A : Dec22, R3RT.SpecO.CaseK 0 12 A → ¬ R3RT.SpecO.Below Top321.O A (2 ^ 462) 462 :=
  fun A hC => root_cut7 (Ω := fun _ => True) KD321.r1OK321 462 0 12 (by norm_num) (by decide +kernel) A trivial hC

/-- **job 2 of case (I13)**: the same for exactly 13 rank-1 first factors -/
theorem root462_empty13 : ∀ A : Dec22, R3RT.SpecO.CaseK 13 13 A → ¬ R3RT.SpecO.Below Top321.O A (2 ^ 462) 462 :=
  fun A hC => root_cut7 (Ω := fun _ => True) KD321.r1OK321 462 13 13 (by norm_num) (by decide +kernel) A trivial hC

end KD321
