module
public import R22Port.U_d41d8cd98f00
public import S7.SatCheck
public import S7.LiftTest
public import LG.LiftK
/-! # The lifting test of SAT leaves for any subspace `E` and inside count `k` (planes: `m = 3`, `k = 3`)

A SAT leaf of the coset IP is a complete assignment `asg` (a decomposition `(a_e, b_e, c_e)` of `T mod E`). It is refuted
when it does not lift to a decomposition of `T` with `k` inside terms at distinct nonzero points `P ⊆ E`
(`LiftKL asg Em k`, the leaf-level form of `L479.LiftK`). A lift gives, for every functional `X`,
`T(X) + Σ_{e ∈ l} b_e c_eᵀ = Σ_{p ∈ P, X(p) = 1} u_p v_pᵀ` for a sublist `l` of `asg`: the right side has rank at most
`m = #{p ∈ P : X(p) = 1}`.

**Rank facts.** A fact `(X, r, F, G)` (`1 ≤ r ≤ 3`; `F = (f_0, f_1, f_2)` on the `b` side, `G = (g_0, g_1, g_2)` on the
`c` side) says that every matrix `T(X) + Σ_{e ∈ l} b_e c_eᵀ` has a 3×3 block `[f_iᵀ M g_j]` of rank `≥ r`. The checker
computes the block code of `T(X)` (`blkT`) and of every term (`blkN`, the outer product of `F b_e` and `G c_e`), closes
the singleton `{blkT}` under XOR with the term blocks (`clo`, a 512-bit set of 3×3 codes), and checks that the closure
misses `LOW (r - 1)`, a set containing every sum of at most `r - 1` outer products (`low_outer`, by `decide`). A
`V`-free block (every term killed) keeps the closure a singleton.

**Cover.** `coverOK pts k facts`: every `k`-sublist `S` of the points `pts` of `E \ {0}` has a fact with
`#{p ∈ S : X(p) = 1} < r`. Planes, `k = 3`: an independent triple needs `r ≥ 2` on a functional that is 1 on exactly one
point (a dual basis element), a collinear triple needs `r ≥ 1` on the line's annihilator or `r ≥ 3` on a functional
nonzero on the line (the lifting criterion, cases (i) and (ii)).

`ltP_sound`: an accepted certificate refutes `LiftKL asg Em k` whenever `pts` lists the nonzero points of `E` without
repetition. -/
@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PL
open BC4 BC5 S5 RootSound Matrix S7L Finset

/-! ## The leaf-level lift -/

/-- **a lift of the decomposition listed in `asg`** with `k` inside terms at distinct nonzero points of `E` -/
def LiftKL (asg : Asg) (Em k : Nat) : Prop :=
  ∃ P : Finset ℕ, P.card = k ∧ (∀ p ∈ P, p < 512 ∧ p ≠ 0 ∧ Em.testBit p = true) ∧
    ∃ u v : ℕ → Fin 9 → F2, (∀ p ∈ P, u p ≠ 0 ∧ v p ≠ 0) ∧
      ∀ X, X < 512 → ∃ l : Asg, l.Sublist asg ∧
        TX (toM3 X) + (l.map (fun e => vecMulVec (nv e.2.1) (nv e.2.2))).sum =
          ∑ p ∈ P.filter (fun p => par (p &&& X) = true), vecMulVec (u p) (v p)

/-- at a complete assignment a lift of the decomposition is a leaf-level lift -/
theorem liftKL_of_complete {T n : Nat} {b c : Nat → Nat} {asg : Asg} (h : AsgOK T n b c 0 asg) {Em k : Nat}
    (hl : L479.LiftK n b c Em k) : LiftKL asg Em k := by
  classical
  obtain ⟨ts, hnd, hmem, he⟩ := h
  obtain ⟨P, hP, hPp, u, v, huv, hX⟩ := hl
  refine ⟨P, hP, hPp, u, v, huv, fun X hXl => ?_⟩
  obtain ⟨S, hS, hsum⟩ := hX X hXl
  refine ⟨(ts.filter (fun t => decide (t ∈ S))).map (fun t => (aT T t, b t, c t)), ?_, ?_⟩
  · rw [he]; exact List.Sublist.map _ List.filter_sublist
  · rw [← hsum, List.map_map, ← List.sum_toFinset _ (hnd.filter _)]
    congr 1
    apply Finset.sum_congr _ (fun x _ => rfl)
    ext t
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, hmem, Nat.zero_testBit, and_true]
    exact ⟨fun h => h.2, fun ht => ⟨Finset.mem_range.mp (hS ht), ht⟩⟩

/-- **a lift moves with the GL3 move of the root** `(b, c) ↦ (b S, S⁻¹ c)` -/
theorem liftK_move1 (n : Nat) (b c : Nat → Nat) (Em k : Nat) (p : Nat × Nat) (hinv : mul3 p.1 p.2 = 273)
    (h : L479.LiftK n b c Em k) : L479.LiftK n (fun u => mul3 (b u) p.1) (fun u => mul3 p.2 (c u)) Em k := by
  have hSS : toM3 p.1 * toM3 p.2 = 1 := by rw [← toM3_mul3, hinv, toM3_273]
  have hSS' : toM3 p.2 * toM3 p.1 = 1 := mul_eq_one_comm.mp hSS
  obtain ⟨P, hP, hPp, u, v, huv, hX⟩ := h
  refine ⟨P, hP, hPp, fun q => lu p.1 (u q), fun q => rv p.2 (v q), fun q hq => ⟨fun h0 => (huv q hq).1 ?_,
    fun h0 => (huv q hq).2 ?_⟩, fun X hXl => ?_⟩
  · have h0' : lu p.1 (u q) = 0 := h0
    rw [← lu_lu p.1 p.2 hSS (u q), h0', lu_zero]
  · have h0' : rv p.2 (v q) = 0 := h0
    rw [← rv_rv p.1 p.2 hSS (v q), h0', rv_zero]
  · obtain ⟨S, hS, e⟩ := hX X hXl
    refine ⟨S, hS, ?_⟩
    have e' := congrArg (phi p.1 p.2) e
    rw [phi_add, phi_TX p.1 p.2 hSS', phi_sum, phi_sum] at e'
    simp only [phi_N] at e'
    simp only [phi_vmv] at e'
    exact e'

theorem liftK_move (n : Nat) (Em k : Nat) (b c : Nat → Nat) (p q : Nat × Nat) (hp : mul3 p.1 p.2 = 273)
    (hq : mul3 q.1 q.2 = 273) (h : L479.LiftK n b c Em k) :
    L479.LiftK n (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))) Em k :=
  liftK_move1 n _ _ Em k q hq (liftK_move1 n b c Em k p hp h)

/-! ## Bilinear evaluation `fᵀ M g` and 3×3 block codes -/

/-- `fᵀ M g` -/
def bil (f g : Nat) (M : Matrix (Fin 9) (Fin 9) F2) : F2 := ∑ y : Fin 9, ∑ z : Fin 9, nv f y * M y z * nv g z

theorem bil_add (f g : Nat) (M N : Matrix (Fin 9) (Fin 9) F2) : bil f g (M + N) = bil f g M + bil f g N := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Matrix.add_apply]; ring

theorem bil_zero (f g : Nat) : bil f g 0 = 0 := by
  unfold bil; simp

theorem bil_vmv (f g : Nat) (u v : Fin 9 → F2) : bil f g (vecMulVec u v) = (nv f ⬝ᵥ u) * (nv g ⬝ᵥ v) := by
  unfold bil dotProduct
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
  rw [vecMulVec_apply]; ring

/-- `fᵀ T(X) g` from the rows of `T(X)` (`S7L.txrow`). The rows depend only on `(X, y)`, so the kernel computes each
once per certificate (a single product `tr(F G X)` per pair measured 1.3-1.4× slower and 1.5× the memory). -/
def bilTXK (f g X k : Nat) : Bool :=
  @Nat.rec (fun _ => Bool) false (fun y acc => xor acc (f.testBit y && par (txrow X y &&& g))) k

def bilTX (f g X : Nat) : Bool := bilTXK f g X 9

theorem txrow_lt (X y : Nat) : txrow X y < 512 := by
  unfold txrow; exact lt_of_lt_of_eq (mkB_lt _ 9) (by norm_num)

theorem bilTXK_bf (f g X : Nat) (hg : g < 512) : ∀ k, bf (bilTXK f g X k) =
    ∑ y ∈ Finset.range k, bf (f.testBit y) * bf (par (txrow X y &&& g)) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    show bf (xor (bilTXK f g X k) (f.testBit k && par (txrow X k &&& g))) = _
    rw [bf_xor]
    cases f.testBit k <;> cases par (txrow X k &&& g) <;> simp [bf]

theorem bil_TX (f g X : Nat) (hg : g < 512) : bil f g (TX (toM3 X)) = bf (bilTX f g X) := by
  unfold bilTX
  rw [bilTXK_bf f g X hg, ← Fin.sum_univ_eq_sum_range]
  unfold bil
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hrow : ∀ z : Fin 9, TX (toM3 X) y z = nv (txrow X y.val) z := by
    intro z; rw [nv_txrow X y]
  have e1 : ∑ z : Fin 9, nv f y * TX (toM3 X) y z * nv g z = nv f y * (nv (txrow X y.val) ⬝ᵥ nv g) := by
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hrow z]; ring
  rw [e1, dot_nv _ _ (txrow_lt X y.val)]
  rfl

/-- the 3-bit code of `(f_iᵀ u)_{i < 3}` -/
def vc (F : Nat → Nat) (u : Fin 9 → F2) : Nat := mkB (fun i => decide (nv (F i) ⬝ᵥ u = 1)) 3

/-- the 9-bit code of the outer product of two 3-bit codes: bit `3i + j` is `x_i y_j` -/
def outerC (x y : Nat) : Nat := mkB (fun k => x.testBit (k / 3) && y.testBit (k % 3)) 9

/-- **the block code** of `M` on `F × G`: bit `3i + j` is `f_iᵀ M g_j` -/
def blkCode (F G : Nat → Nat) (M : Matrix (Fin 9) (Fin 9) F2) : Nat :=
  mkB (fun k => decide (bil (F (k / 3)) (G (k % 3)) M = 1)) 9

theorem f2_add_one (a b : F2) : decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  revert a b; decide

theorem f2_mul_one (a b : F2) : decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  revert a b; decide

theorem blkCode_lt (F G : Nat → Nat) (M : Matrix (Fin 9) (Fin 9) F2) : blkCode F G M < 512 :=
  lt_of_lt_of_eq (mkB_lt _ 9) (by norm_num)

theorem blkCode_add (F G : Nat → Nat) (M N : Matrix (Fin 9) (Fin 9) F2) :
    blkCode F G (M + N) = blkCode F G M ^^^ blkCode F G N := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor]
  unfold blkCode
  rw [mkB_bit, mkB_bit, mkB_bit, bil_add, f2_add_one]
  cases decide (k < 9) <;> simp

theorem blkCode_zero (F G : Nat → Nat) : blkCode F G 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro k
  unfold blkCode
  rw [mkB_bit, bil_zero, Nat.zero_testBit]
  simp

theorem blkCode_vmv (F G : Nat → Nat) (u v : Fin 9 → F2) :
    blkCode F G (vecMulVec u v) = outerC (vc F u) (vc G v) := by
  apply Nat.eq_of_testBit_eq; intro k
  unfold blkCode outerC vc
  rw [mkB_bit, mkB_bit, bil_vmv, f2_mul_one, mkB_bit, mkB_bit]
  by_cases hk : k < 9
  · have h1 : k / 3 < 3 := by omega
    have h2 : k % 3 < 3 := by omega
    simp [hk, h1, h2]
  · simp [hk]

theorem blkCode_list (F G : Nat → Nat) (l : List (Matrix (Fin 9) (Fin 9) F2)) :
    blkCode F G l.sum = l.foldr (fun M acc => blkCode F G M ^^^ acc) 0 := by
  induction l with
  | nil => rw [List.sum_nil, blkCode_zero]; rfl
  | cons M l ih => rw [List.sum_cons, blkCode_add, ih]; rfl

/-! ## The checker -/

/-- `(f_iᵀ b)_{i<3}` as a 3-bit code -/
def vcB (F : Nat → Nat) (b : Nat) : Nat := mkB (fun i => par (F i &&& b)) 3

/-- the block code of a term `b cᵀ` -/
def blkN (F G : Nat → Nat) (e : Nat × Nat × Nat) : Nat := outerC (vcB F e.2.1) (vcB G e.2.2)

/-- the block code of `T(X)` -/
def blkT (F G : Nat → Nat) (X : Nat) : Nat := mkB (fun k => bilTX (F (k / 3)) (G (k % 3)) X) 9

/-- a 512-bit set of 9-bit codes translated by XOR with `v` -/
def xorT (m v : Nat) : Nat := mkB (fun w => m.testBit (w ^^^ v)) 512

/-- the closure of the code set `m` under XOR with the term blocks of `asg` -/
def clo (F G : Nat → Nat) (asg : Asg) (m : Nat) : Nat :=
  @List.rec (Nat × Nat × Nat) (fun _ => Nat → Nat) (fun m => m)
    (fun e _ ih m => ih (let v := blkN F G e; cond (Nat.beq v 0) m (m ||| xorT m v))) asg m

/-- 3×3 codes of rank `≤ 1` (512-bit mask; checked superset: `low_outer`) -/
def L1M : Nat := 0x810000000000008100410000000000410000210000000021000000110000001100000000090000090000000000050005000000000000030381412111090503ff
/-- 3×3 codes of rank `≤ 2` -/
def L2M : Nat := 0xffc3a59999a5c3ffc3ff69556955c3ffa569ff3369a533ff995533ff995533ff99696999ff0f0fffa555a5550fff0fffc3c333330f0fffffffffffffffffffff
/-- the codes of rank `≤ r` (`r ≤ 2`) -/
def LOW (r : Nat) : Nat := cond (Nat.beq r 0) 1 (cond (Nat.beq r 1) L1M L2M)

/-! ## Semantics of the checker -/

theorem outerC_lt (x y : Nat) : outerC x y < 512 := lt_of_lt_of_eq (mkB_lt _ 9) (by norm_num)

theorem blkN_lt (F G : Nat → Nat) (e : Nat × Nat × Nat) : blkN F G e < 512 := outerC_lt _ _

theorem vc_nv (F : Nat → Nat) (hF : ∀ i, F i < 512) (b : Nat) : vc F (nv b) = vcB F b := by
  apply Nat.eq_of_testBit_eq; intro i
  unfold vc vcB
  rw [mkB_bit, mkB_bit, dot_nv _ _ (hF i)]
  cases par (F i &&& b) <;> simp [bf]

/-- the block of a term is `blkN` -/
theorem blkCode_N (F G : Nat → Nat) (hF : ∀ i, F i < 512) (hG : ∀ i, G i < 512) (e : Nat × Nat × Nat) :
    blkCode F G (vecMulVec (nv e.2.1) (nv e.2.2)) = blkN F G e := by
  rw [blkCode_vmv, vc_nv F hF, vc_nv G hG]; rfl

/-- the block of `T(X)` is `blkT` -/
theorem blkCode_TX (F G : Nat → Nat) (hG : ∀ i, G i < 512) (X : Nat) :
    blkCode F G (TX (toM3 X)) = blkT F G X := by
  apply Nat.eq_of_testBit_eq; intro k
  unfold blkCode blkT
  rw [mkB_bit, mkB_bit, bil_TX _ _ _ (hG _)]
  cases bilTX (F (k / 3)) (G (k % 3)) X <;> simp [bf]

/-- the XOR of the term blocks of a list -/
def xorL (F G : Nat → Nat) (l : Asg) : Nat := l.foldr (fun e acc => blkN F G e ^^^ acc) 0

theorem xorL_lt (F G : Nat → Nat) : ∀ l : Asg, xorL F G l < 512 := by
  intro l
  induction l with
  | nil => show (0 : Nat) < 512; norm_num
  | cons e l ih =>
    show blkN F G e ^^^ xorL F G l < 512
    have e1 : (512 : Nat) = 2 ^ 9 := by norm_num
    rw [e1] at ih ⊢
    exact Nat.xor_lt_two_pow (lt_of_lt_of_eq (blkN_lt F G e) e1) ih

theorem blkCode_terms (F G : Nat → Nat) (hF : ∀ i, F i < 512) (hG : ∀ i, G i < 512) (l : Asg) :
    blkCode F G ((l.map (fun e => vecMulVec (nv e.2.1) (nv e.2.2))).sum) = xorL F G l := by
  induction l with
  | nil => rw [List.map_nil, List.sum_nil, blkCode_zero]; rfl
  | cons e l ih =>
    rw [List.map_cons, List.sum_cons, blkCode_add, ih, blkCode_N F G hF hG]; rfl

theorem xorT_bit (m v w : Nat) : (xorT m v).testBit w = (decide (w < 512) && m.testBit (w ^^^ v)) := by
  unfold xorT; rw [mkB_bit]

theorem xor_lt512 {a b : Nat} (ha : a < 512) (hb : b < 512) : a ^^^ b < 512 := by
  have e1 : (512 : Nat) = 2 ^ 9 := by norm_num
  rw [e1] at ha hb ⊢; exact Nat.xor_lt_two_pow ha hb

/-- **the closure contains every reachable block** -/
theorem clo_mem (F G : Nat → Nat) : ∀ (asg : Asg) (m : Nat) (l : Asg), l.Sublist asg → ∀ w, w < 512 →
    m.testBit w = true → (clo F G asg m).testBit (w ^^^ xorL F G l) = true := by
  intro asg
  induction asg with
  | nil =>
    intro m l hl w _ hw
    rw [List.sublist_nil.mp hl]
    show m.testBit (w ^^^ 0) = true
    rw [Nat.xor_zero]; exact hw
  | cons e rest ih =>
    intro m l hl w hw512 hw
    have e1 : clo F G (e :: rest) m =
        clo F G rest (cond (Nat.beq (blkN F G e) 0) m (m ||| xorT m (blkN F G e))) := rfl
    rw [e1]
    have hm1 : (cond (Nat.beq (blkN F G e) 0) m (m ||| xorT m (blkN F G e))).testBit w = true := by
      cases Nat.beq (blkN F G e) 0
      · simp [Nat.testBit_or, hw]
      · simpa using hw
    have hm2 : (cond (Nat.beq (blkN F G e) 0) m (m ||| xorT m (blkN F G e))).testBit (w ^^^ blkN F G e) = true := by
      cases hb : Nat.beq (blkN F G e) 0
      · simp only [cond_false, Nat.testBit_or, xorT_bit]
        have : (w ^^^ blkN F G e) ^^^ blkN F G e = w := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [this, hw]
        simp [xor_lt512 hw512 (blkN_lt F G e)]
      · have h0 : blkN F G e = 0 := Nat.eq_of_beq_eq_true hb
        simp only [cond_true]; rw [h0, Nat.xor_zero]; exact hw
    cases hl with
    | cons _ hl' => exact ih _ l hl' w hw512 hm1
    | cons_cons _ hl' =>
      rename_i l'
      have ex : xorL F G (e :: l') = blkN F G e ^^^ xorL F G l' := rfl
      rw [ex, ← Nat.xor_assoc]
      exact ih _ l' hl' _ (xor_lt512 hw512 (blkN_lt F G e)) hm2

/-! ## Sums of few rank-1 matrices have low-rank blocks (finite facts, by `decide`) -/

theorem low0 : (LOW 0).testBit 0 = true := by decide

theorem low_step_all : allLT 2 (fun r => allLT 512 (fun c => !(LOW r).testBit c ||
    allLT 8 (fun x => allLT 8 (fun y => (LOW (r + 1)).testBit (c ^^^ outerC x y))))) = true := by decide +kernel

theorem low_mono_all : allLT 2 (fun r => allLT 512 (fun c => !(LOW r).testBit c || (LOW (r + 1)).testBit c)) = true := by
  decide +kernel

theorem low_step (r : Nat) (hr : r < 2) (c : Nat) (hc : c < 512) (h : (LOW r).testBit c = true) (x y : Nat)
    (hx : x < 8) (hy : y < 8) : (LOW (r + 1)).testBit (c ^^^ outerC x y) = true := by
  have h1 : (!(LOW r).testBit c ||
      allLT 8 (fun x => allLT 8 (fun y => (LOW (r + 1)).testBit (c ^^^ outerC x y)))) = true :=
    allLT_spec (allLT_spec low_step_all r hr) c hc
  rw [h, Bool.not_true, Bool.false_or] at h1
  exact allLT_spec (allLT_spec h1 x hx) y hy

theorem low_mono (r : Nat) (hr : r < 2) (c : Nat) (hc : c < 512) (h : (LOW r).testBit c = true) :
    (LOW (r + 1)).testBit c = true := by
  have h1 : (!(LOW r).testBit c || (LOW (r + 1)).testBit c) = true := allLT_spec (allLT_spec low_mono_all r hr) c hc
  rw [h, Bool.not_true, Bool.false_or] at h1
  exact h1

theorem low_mono' (r r' : Nat) (hrr : r ≤ r') (hr' : r' ≤ 2) (c : Nat) (hc : c < 512) (h : (LOW r).testBit c = true) :
    (LOW r').testBit c = true := by
  induction r' with
  | zero => have : r = 0 := by omega
            subst this; exact h
  | succ r' ih =>
    rcases Nat.lt_or_ge r (r' + 1) with h1 | h1
    · exact low_mono r' (by omega) c hc (ih (by omega) (by omega))
    · have : r = r' + 1 := by omega
      subst this; exact h

theorem vc_lt (F : Nat → Nat) (u : Fin 9 → F2) : vc F u < 8 := lt_of_lt_of_eq (mkB_lt _ 3) (by norm_num)

/-- **the block of a sum of `m ≤ 2` rank-1 matrices has rank `≤ m`** -/
theorem low_sum (F G : Nat → Nat) (u v : ℕ → Fin 9 → F2) :
    ∀ s : Finset ℕ, s.card ≤ 2 → (LOW s.card).testBit (blkCode F G (∑ p ∈ s, vecMulVec (u p) (v p))) = true := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; rw [Finset.sum_empty, blkCode_zero, Finset.card_empty]; exact low0
  | insert a s ha ih =>
    intro hc
    rw [Finset.card_insert_of_notMem ha] at hc ⊢
    rw [Finset.sum_insert ha, blkCode_add, blkCode_vmv, Nat.xor_comm]
    exact low_step s.card (by omega) _ (blkCode_lt F G _) (ih (by omega)) _ _ (vc_lt F (u a)) (vc_lt G (v a))

/-! ## The leaf test -/

/-- fields of a 65-bit fact record: `X` (9), `r` (2), `f_0 f_1 f_2` (9 each), `g_0 g_1 g_2` (9 each) -/
def fX (f : Nat) : Nat := rd 9 f
def fR (f : Nat) : Nat := rd 2 (sk 9 f)
def fF (f : Nat) (i : Nat) : Nat := rd 9 (sk (11 + 9 * i) f)
def fG (f : Nat) (j : Nat) : Nat := rd 9 (sk (38 + 9 * j) f)

/-- **a rank fact holds for the decomposition `asg`**: `1 ≤ r` and the closure of the block of `T(X)` under the term blocks
misses the codes of rank `≤ r - 1` -/
def factOK (asg : Asg) (f : Nat) : Bool :=
  Nat.ble 1 (fR f) &&
    Nat.beq (Nat.land (clo (fF f) (fG f) asg (2 ^ blkT (fF f) (fG f) (fX f))) (LOW (fR f - 1))) 0

/-- the number of points of `S` where `X` is 1 -/
def cntX (X : Nat) (S : List Nat) : Nat := (S.filter (fun p => par (p &&& X))).length

/-- **the lifting test**: `w` = 5 bits `nf`, then `nf` fact records of 65 bits; every fact holds and every `k`-sublist of
`pts` has a fact `(X, r)` with fewer than `r` of its points where `X` is 1 -/
def ltP (pts : List Nat) (k : Nat) (asg : Asg) (w : Nat) : Bool :=
  (rdLst 65 (rd 5 w) (sk 5 w)).all (factOK asg) &&
    (pts.sublistsLen k).all (fun S => (rdLst 65 (rd 5 w) (sk 5 w)).any (fun f => Nat.blt (cntX (fX f) S) (fR f)))

theorem rd9_lt (S : Nat) : rd 9 S < 512 := lt_of_lt_of_eq (rd_lt 9 S) (by norm_num)

/-- the sublist of `pts` listing a set `P ⊆ pts` -/
theorem cnt_eq (pts : List Nat) (hnd : pts.Nodup) (P : Finset ℕ) (hP : ∀ p ∈ P, p ∈ pts) (X : Nat) :
    cntX X (pts.filter (fun p => decide (p ∈ P))) = (P.filter (fun p => par (p &&& X) = true)).card := by
  unfold cntX
  rw [List.filter_filter]
  have hnd' := hnd.filter (fun p => (par (p &&& X) && decide (p ∈ P)))
  rw [← List.toFinset_card_of_nodup hnd']
  congr 1
  ext p
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨hP p h2, h1, h2⟩

theorem len_eq (pts : List Nat) (hnd : pts.Nodup) (P : Finset ℕ) (hP : ∀ p ∈ P, p ∈ pts) :
    (pts.filter (fun p => decide (p ∈ P))).length = P.card := by
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext p
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hP p h, h⟩⟩

/-- **soundness of the lifting test**: if `pts` lists the nonzero points of `E` without repetition, an accepted
certificate refutes every lift of `asg` with `k` inside terms -/
theorem ltP_sound (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts)
    (asg : Asg) (w : Nat) (h : ltP pts k asg w = true) : ¬ LiftKL asg Em k := by
  rintro ⟨P, hcard, hPp, u, v, huv, hX⟩
  have hPpts : ∀ p ∈ P, p ∈ pts := fun p hp => hpts p (hPp p hp).1 (hPp p hp).2.1 (hPp p hp).2.2
  unfold ltP at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hall, hcov⟩ := h
  set S := pts.filter (fun p => decide (p ∈ P)) with hS
  have hSmem : S ∈ pts.sublistsLen k := by
    rw [List.mem_sublistsLen]
    exact ⟨List.filter_sublist, by rw [hS, len_eq pts hnd P hPpts, hcard]⟩
  have h1 := List.all_eq_true.mp hcov S hSmem
  obtain ⟨f, hf, hlt⟩ := List.any_eq_true.mp h1
  have hok := List.all_eq_true.mp hall f hf
  unfold factOK at hok
  rw [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨hr1, hcl⟩ := hok
  have hr3 : fR f < 4 := lt_of_lt_of_eq (rd_lt 2 _) (by norm_num)
  rw [Nat.blt_eq, hS, cnt_eq pts hnd P hPpts] at hlt
  -- the lift at `X`
  obtain ⟨l, hl, heq⟩ := hX (fX f) (rd9_lt f)
  have hF : ∀ i, fF f i < 512 := fun i => rd9_lt _
  have hG : ∀ j, fG f j < 512 := fun j => rd9_lt _
  have hb := congrArg (blkCode (fF f) (fG f)) heq
  rw [blkCode_add, blkCode_TX _ _ hG, blkCode_terms _ _ hF hG] at hb
  -- the reachable block is in the closure
  have hin := clo_mem (fF f) (fG f) asg (2 ^ blkT (fF f) (fG f) (fX f)) l hl (blkT (fF f) (fG f) (fX f))
    (lt_of_lt_of_eq (mkB_lt _ 9) (by norm_num)) (by rw [Nat.testBit_two_pow_self])
  rw [hb] at hin
  -- and has rank `≤ m ≤ r - 1`
  set P' := P.filter (fun p => par (p &&& fX f) = true) with hP'
  have hm2 : P'.card ≤ 2 := by omega
  have hlow := low_mono' P'.card (fR f - 1) (by omega) (by omega) _ (blkCode_lt (fF f) (fG f) _)
    (low_sum (fF f) (fG f) u v P' hm2)
  have hz := congrArg (fun x => Nat.testBit x (blkCode (fF f) (fG f) (∑ p ∈ P', vecMulVec (u p) (v p)))) (Nat.eq_of_beq_eq_true hcl)
  simp only [Nat.testBit_and, Nat.zero_testBit] at hz
  rw [Nat.land_eq, Nat.testBit_and] at hz
  rw [hin, hlow] at hz
  exact absurd hz (by decide)

end PL

#print axioms PL.liftK_move
#print axioms PL.liftKL_of_complete
#print axioms PL.clo_mem
#print axioms PL.low_sum
#print axioms PL.ltP_sound
