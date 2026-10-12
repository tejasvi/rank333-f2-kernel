module
public import R22Port.U_d41d8cd98f00
public import S4.SatQ
/-! # The lifting test with witness facts (`PL.ltW`): rank lower bounds by row (or column) witnesses

A **witness fact** `(X, r, side, B, Q)` (`1 ≤ r ≤ 3`; base vectors `B_0, B_1, B_2`; witnesses `Q_1, …, Q_7`) says: for every
nonzero `λ < 2^r`, with `c_λ = ⊕_{i : λ_i = 1} B_i` and `(w, z) = (c_λ, Q_λ)` (side 0) or `(Q_λ, c_λ)` (side 1),
* every term is killed by the pair: `(w · b_e)(z · c_e) = 0` for every `e ∈ asg`;
* `wᵀ T(X) z = 1`.
Then `wᵀ M z = 1` for every `M = T(X) + Σ_{e ∈ l} b_e c_eᵀ`. Side 0: the `r × 9` matrix `[c_λᵀ M]` never has a nonzero
`λ` with `c_λᵀ M = 0`, so `rank M ≥ r` (side 1: columns). The check is exact for "`c_λᵀ M ≠ 0` on the whole coset":
`c_λᵀ M` ranges over `c_λᵀ T(X) + span{c_e : c_λ · b_e = 1}`, and a witness exists iff `c_λᵀ T(X)` is outside that span.
A V-free `r × r` block gives a witness fact of rank `r`.

A lift with `m < r` points where `X` is 1 has right side `Σ_{p} u_p v_pᵀ` (`m` terms): some nonzero `λ < 2^r` is
orthogonal to the `m` codes `(B_i · u_p)_i` (`fin1`, `fin2`, by `decide`), so `c_λᵀ (Σ_p u_p v_pᵀ) z = 0`, a contradiction.

`ltW pts k asg w`: every fact holds, and every `k`-sublist of `pts` has a fact with `#{p ∈ S : X(p) = 1} < r`
(as `PL.ltP`). `ltW_sound`, `leafSLW_noLiftK`, `leafNoExt_of_leafSLW`: as for `ltP`. -/
@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PL
open BC4 BC5 S5 RootSound Matrix S7L Finset

/-- fields of a 102-bit witness fact: `X` (9), `r` (2), side (1), `B_0 B_1 B_2` (9 each), `Q_1 … Q_7` (9 each) -/
def gX (f : Nat) : Nat := rd 9 f
def gR (f : Nat) : Nat := rd 2 (sk 9 f)
def gS (f : Nat) : Nat := rd 1 (sk 11 f)
def gB (f i : Nat) : Nat := rd 9 (sk (12 + 9 * i) f)
def gQ (f l : Nat) : Nat := rd 9 (sk (39 + 9 * (l - 1)) f)

/-- `⊕_{i < 3, λ_i = 1} B_i` -/
def combB (B : Nat → Nat) (l : Nat) : Nat :=
  (bif l.testBit 0 then B 0 else 0) ^^^ (bif l.testBit 1 then B 1 else 0) ^^^ (bif l.testBit 2 then B 2 else 0)

/-- the pair `(w, z)` kills every term of `asg` -/
def killAll (asg : Asg) (w z : Nat) : Bool :=
  @List.rec (Nat × Nat × Nat) (fun _ => Bool) true (fun e _ ih => !(par (w &&& e.2.1) && par (z &&& e.2.2)) && ih) asg

/-- the pair `(w, z)` kills every term of `asg` and `wᵀ T(X) z = 1` -/
def pairOK (asg : Asg) (X w z : Nat) : Bool := killAll asg w z && bilTX w z X

/-- **a witness fact holds** -/
def wfactOK (asg : Asg) (f : Nat) : Bool :=
  Nat.ble 1 (gR f) &&
    allLT (2 ^ gR f) (fun l => Nat.beq l 0 ||
      bif Nat.beq (gS f) 0 then pairOK asg (gX f) (combB (gB f) l) (gQ f l)
      else pairOK asg (gX f) (gQ f l) (combB (gB f) l))

/-- **the lifting test with witness facts**: `w` = 5 bits `nf`, then `nf` facts of 102 bits -/
def ltW (pts : List Nat) (k : Nat) (asg : Asg) (w : Nat) : Bool :=
  (rdLst 102 (rd 5 w) (sk 5 w)).all (wfactOK asg) &&
    (pts.sublistsLen k).all (fun S => (rdLst 102 (rd 5 w) (sk 5 w)).any (fun f => Nat.blt (cntX (gX f) S) (gR f)))

/-! ## Semantics -/

/-- the 3-bit inner product -/
def pdot (l x : Nat) : Bool :=
  xor (xor (l.testBit 0 && x.testBit 0) (l.testBit 1 && x.testBit 1)) (l.testBit 2 && x.testBit 2)

/-- the code of `(B_i · u)_{i < 3}` -/
def cd (B : Nat → Nat) (u : Fin 9 → F2) : Nat := mkB (fun i => decide (nv (B i) ⬝ᵥ u = 1)) 3

theorem f2_eq_bf (a : F2) : a = bf (decide (a = 1)) := by
  revert a; decide

theorem dot_add_left (a b u : Fin 9 → F2) : (a + b) ⬝ᵥ u = a ⬝ᵥ u + b ⬝ᵥ u := add_dotProduct a b u

theorem nv_cond (c : Bool) (B : Nat) : nv (bif c then B else 0) = bif c then nv B else 0 := by
  cases c
  · exact nv_zero'
  · rfl

theorem nv_xor' (x y : Nat) : nv (x ^^^ y) = nv x + nv y := nv_xor x y

theorem combB_dot (B : Nat → Nat) (l : Nat) (u : Fin 9 → F2) : nv (combB B l) ⬝ᵥ u = bf (pdot l (cd B u)) := by
  unfold combB
  rw [nv_xor', nv_xor', nv_cond, nv_cond, nv_cond, dot_add_left, dot_add_left]
  have hc : ∀ i, i < 3 → (cd B u).testBit i = decide (nv (B i) ⬝ᵥ u = 1) := by
    intro i hi; unfold cd; rw [mkB_bit]; simp [hi]
  unfold pdot
  rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), bf_xor, bf_xor, bf_and, bf_and, bf_and,
    ← f2_eq_bf, ← f2_eq_bf, ← f2_eq_bf]
  cases l.testBit 0 <;> cases l.testBit 1 <;> cases l.testBit 2 <;> simp [bf]

theorem killAll_spec (w z : Nat) : ∀ asg : Asg, killAll asg w z = true →
    ∀ e ∈ asg, (par (w &&& e.2.1) && par (z &&& e.2.2)) = false := by
  intro asg
  induction asg with
  | nil => intro _ e he; exact absurd he List.not_mem_nil
  | cons e0 rest ih =>
    intro h e he
    have e1 : killAll (e0 :: rest) w z = (!(par (w &&& e0.2.1) && par (z &&& e0.2.2)) && killAll rest w z) := rfl
    rw [e1, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases List.mem_cons.mp he with rfl | he'
    · exact h.1
    · exact ih h.2 e he'

theorem bil_list (f g : Nat) (F : Nat × Nat × Nat → Matrix (Fin 9) (Fin 9) F2) :
    ∀ l : Asg, bil f g ((l.map F).sum) = (l.map (fun e => bil f g (F e))).sum := by
  intro l
  induction l with
  | nil => rw [List.map_nil, List.sum_nil, bil_zero]; rfl
  | cons e l ih => rw [List.map_cons, List.sum_cons, bil_add, ih]; rfl

theorem bil_fsum (f g : Nat) (F : ℕ → Matrix (Fin 9) (Fin 9) F2) (s : Finset ℕ) :
    bil f g (∑ p ∈ s, F p) = ∑ p ∈ s, bil f g (F p) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bil_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bil_add, ih]

/-- the pair check gives `wᵀ M z = 1` on the whole coset -/
theorem pairOK_bil (asg : Asg) (X w z : Nat) (hw : w < 512) (hz : z < 512) (h : pairOK asg X w z = true) (l : Asg)
    (hl : l.Sublist asg) :
    bil w z (TX (toM3 X) + (l.map (fun e => vecMulVec (nv e.2.1) (nv e.2.2))).sum) = 1 := by
  unfold pairOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hall, hT⟩ := h
  have hk := killAll_spec w z asg hall
  rw [bil_add, bil_TX _ _ _ hz, hT, bil_list]
  have h0 : (l.map (fun e => bil w z (vecMulVec (nv e.2.1) (nv e.2.2)))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [bil_vmv, dot_nv _ _ hw, dot_nv _ _ hz, ← bf_and, hk e (hl.subset he)]
    rfl
  rw [h0, add_zero]; rfl

theorem combB_lt (B : Nat → Nat) (hB : ∀ i, B i < 512) (l : Nat) : combB B l < 512 := by
  unfold combB
  have hc : ∀ (c : Bool) (i : Nat), (bif c then B i else 0) < 512 := by
    intro c i; cases c
    · show (0 : Nat) < 512; norm_num
    · exact hB i
  exact xor_lt512 (xor_lt512 (hc _ _) (hc _ _)) (hc _ _)

/-- finite facts: one or two codes in `F2^3` are orthogonal to some nonzero `λ` (below 4 for one code) -/
theorem fin1_all : allLT 8 (fun x => ([1, 2, 3] : List Nat).any (fun l => !pdot l x)) = true := by decide

theorem fin2_all : allLT 8 (fun x => allLT 8 (fun y =>
    ([1, 2, 3, 4, 5, 6, 7] : List Nat).any (fun l => !pdot l x && !pdot l y))) = true := by decide

theorem cd_lt (B : Nat → Nat) (u : Fin 9 → F2) : cd B u < 8 := lt_of_lt_of_eq (mkB_lt _ 3) (by norm_num)

/-- **a nonzero `λ < 2^r` orthogonal to the codes of fewer than `r` vectors** -/
theorem orth_exists (B : Nat → Nat) (u : ℕ → Fin 9 → F2) (s : Finset ℕ) (r : Nat) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hs : s.card < r) : ∃ l, 0 < l ∧ l < 2 ^ r ∧ ∀ p ∈ s, pdot l (cd B (u p)) = false := by
  rcases Nat.lt_or_ge s.card 1 with h0 | h1
  · have : s = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    have h2 : 2 ≤ 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1
    exact ⟨1, by norm_num, by omega, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  · rcases Nat.lt_or_ge s.card 2 with h1' | h2
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
      have hr2 : 2 ≤ r := by simp at hs; omega
      have hf := allLT_spec fin1_all (cd B (u p)) (cd_lt B (u p))
      obtain ⟨l, hl, hlx⟩ := List.any_eq_true.mp hf
      have h4 : 4 ≤ 2 ^ r := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
      refine ⟨l, ?_, ?_, fun q hq => ?_⟩
      · simp at hl; omega
      · simp at hl; omega
      · rw [Finset.mem_singleton.mp hq]; simpa using hlx
    · have hc2 : s.card = 2 := by omega
      obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hc2
      have hr : r = 3 := by omega
      subst hr
      have hf := allLT_spec (allLT_spec fin2_all (cd B (u p)) (cd_lt B (u p))) (cd B (u q)) (cd_lt B (u q))
      obtain ⟨l, hl, hlx⟩ := List.any_eq_true.mp hf
      rw [Bool.and_eq_true] at hlx
      refine ⟨l, ?_, ?_, fun x hx => ?_⟩
      · simp at hl; omega
      · simp at hl; omega
      · rcases Finset.mem_insert.mp hx with rfl | hx'
        · simpa using hlx.1
        · rw [Finset.mem_singleton.mp hx']; simpa using hlx.2

theorem gB_lt (f i : Nat) : gB f i < 512 := rd9_lt _
theorem gQ_lt (f l : Nat) : gQ f l < 512 := rd9_lt _

/-- **soundness of the witness test** -/
theorem ltW_sound (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts)
    (asg : Asg) (w : Nat) (h : ltW pts k asg w = true) : ¬ LiftKL asg Em k := by
  rintro ⟨P, hcard, hPp, u, v, huv, hX⟩
  have hPpts : ∀ p ∈ P, p ∈ pts := fun p hp => hpts p (hPp p hp).1 (hPp p hp).2.1 (hPp p hp).2.2
  unfold ltW at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hall, hcov⟩ := h
  set S := pts.filter (fun p => decide (p ∈ P)) with hS
  have hSmem : S ∈ pts.sublistsLen k := by
    rw [List.mem_sublistsLen]
    exact ⟨List.filter_sublist, by rw [hS, len_eq pts hnd P hPpts, hcard]⟩
  obtain ⟨f, hf, hlt⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcov S hSmem)
  have hok := List.all_eq_true.mp hall f hf
  unfold wfactOK at hok
  rw [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨hr1, hcl⟩ := hok
  have hr3 : gR f ≤ 3 := by have := rd_lt 2 (sk 9 f); unfold gR; omega
  rw [Nat.blt_eq, hS, cnt_eq pts hnd P hPpts] at hlt
  obtain ⟨l, hl, heq⟩ := hX (gX f) (rd9_lt f)
  set P' := P.filter (fun p => par (p &&& gX f) = true) with hP'
  have hB : ∀ i, gB f i < 512 := fun i => gB_lt f i
  -- the side: rows (u) or columns (v)
  cases hside : Nat.beq (gS f) 0
  · -- side 1: z = c_λ, w = Q_λ; λ orthogonal to the codes of the v_p
    obtain ⟨lam, hl0, hl2, horth⟩ := orth_exists (gB f) v P' (gR f) hr1 hr3 hlt
    have hpair := allLT_spec hcl lam hl2
    have hb0 : Nat.beq lam 0 = false := by
      cases hb : Nat.beq lam 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
    rw [hb0, Bool.false_or, hside] at hpair
    simp only [cond_false] at hpair
    have h1 := pairOK_bil asg (gX f) (gQ f lam) (combB (gB f) lam) (gQ_lt f lam) (combB_lt _ hB lam) hpair l hl
    rw [heq, bil_fsum] at h1
    have h0 : ∑ p ∈ P', bil (gQ f lam) (combB (gB f) lam) (vecMulVec (u p) (v p)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [bil_vmv, combB_dot, horth p hp]; simp [bf]
    rw [h0] at h1
    exact absurd h1 (by decide)
  · -- side 0: w = c_λ, z = Q_λ; λ orthogonal to the codes of the u_p
    obtain ⟨lam, hl0, hl2, horth⟩ := orth_exists (gB f) u P' (gR f) hr1 hr3 hlt
    have hpair := allLT_spec hcl lam hl2
    have hb0 : Nat.beq lam 0 = false := by
      cases hb : Nat.beq lam 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
    rw [hb0, Bool.false_or, hside] at hpair
    simp only [cond_true] at hpair
    have h1 := pairOK_bil asg (gX f) (combB (gB f) lam) (gQ f lam) (combB_lt _ hB lam) (gQ_lt f lam) hpair l hl
    rw [heq, bil_fsum] at h1
    have h0 : ∑ p ∈ P', bil (combB (gB f) lam) (gQ f lam) (vecMulVec (u p) (v p)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [bil_vmv, combB_dot, horth p hp]; simp [bf]
    rw [h0] at h1
    exact absurd h1 (by decide)

/-- **SAT leaves with `k` inside terms, witness facts** -/
theorem leafSLW_noLiftK (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (h : BC7L.leafSL (ltW pts k) R = true) :
    L479.NoLiftK (leafT R) (leafN R) (S6.leafDom6 R) Em k := by
  intro b c hbc hd hl
  exact leafSLQ (ltW pts k) (fun b c => L479.LiftK (leafN R) b c Em k)
    (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) h b c hbc hd hl

/-- **the external leaf of a coset IP, refuted by the witness test** (`k = 22 - R`; any `E`, `R`, `lo`) -/
theorem leafNoExt_of_leafSLW {C : E1G.Ctx} {Em lo pl : ℕ} (pts : List Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (cert : ℕ)
    (hN : C.N ≤ 127) (hR : C.R ≤ 31) (hC : E1GS.Cosets Em C.VT C.N) (hD : E1GS.DomPerp C.DOM Em)
    (hDOM : C.DOM < 2 ^ 512)
    (hok : BC7L.leafSL (ltW pts (22 - C.R)) (E1G.leafRec C.R C.VT C.DOM pl cert) = true) :
    L479.LeafNoExt C Em lo pl := by
  have h := leafSLW_noLiftK pts (22 - C.R) Em hnd hpts _ hok
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM] at h
  apply L479.leafNoExt_of_noLiftK hN hR hC hD hDOM
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM]
  exact h

end PL

#print axioms PL.combB_dot
#print axioms PL.orth_exists
#print axioms PL.ltW_sound
#print axioms PL.leafSLW_noLiftK
#print axioms PL.leafNoExt_of_leafSLW
