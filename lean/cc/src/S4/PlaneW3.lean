module
public import R22Port.U_d41d8cd98f00
public import S4.PlaneW
/-! # The lifting test with guessed terms (`PL.ltW3`): witness facts plus lift3 entries

`PL.ltW` refutes a `k`-subset `S` of the points of `E` with a rank fact at a functional `X` that is 1 on fewer than `r`
points of `S`. When no such fact exists (planes: a collinear `S` whose line has `δ(φ_ℓ) = 0` and rank-2 elements in all
three classes), a **lift3 entry** for `S` guesses the inside term `N_c = u vᵀ` at a point `pc ∈ S`:
* at a functional `X` with `X(pc) = 1`, the lift reads `T(X) + Σ_{e ∈ l} N_e + N_c = Σ_{p ∈ S \ pc, X(p) = 1} N_p`, a sum
  of `m = #{p ∈ S \ pc : X(p) = 1}` rank-1 matrices;
* so a fact of rank `r > m` on the shifted coset `T(X) + u vᵀ + span{N_e}` refutes the lift with that guess: every pair
  `(w, z)` of the fact kills the terms and has `wᵀ (T(X) + u vᵀ) z = 1`.
An entry `(S, pc, ufs, svs)` covers every guess: every nonzero `u` has a **u-free** fact (`ufs`: every pair's `w` is
orthogonal to `u`, so the shift does not matter), or is a **survivor** `(u, gs) ∈ svs` with, for every nonzero `v`, a
shifted fact `g ∈ gs` valid at `(u, v)`. A shifted fact record carries the bits `b_λ = wᵀ T(X) z` (checked once), so the
`v` loop only adds `(w · u)(z · v)`.

`ltW3_sound`, `leafSLW3_noLiftK`, `leafNoExt_of_leafSLW3`: as for `ltW`. This is the exact m = 2, k = 3 lifting condition
(no rank-1 `N_3` with `δ(χ_1) + [N_3]` and `δ(χ_2) + [N_3]` both rank-1 classes), certified by rank facts. -/
@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PL
open BC4 BC5 S5 RootSound Matrix S7L Finset

/-- the pair vectors of a witness fact -/
def wvec (f l : Nat) : Nat := bif Nat.beq (gS f) 0 then combB (gB f) l else gQ f l
def zvec (f l : Nat) : Nat := bif Nat.beq (gS f) 0 then gQ f l else combB (gB f) l

/-- a shifted fact record (105 bits): a witness fact (102 bits) and the bits `b_λ` (`λ = 1, 2, 3`) -/
def sbit (g l : Nat) : Bool := (sk (101 + l) g).testBit 0

/-- a u-free fact for the entry: the fact holds, `X(pc) = 1`, fewer than `r` other points of `S` -/
def uPre (asg : Asg) (pc : Nat) (others : List Nat) (f : Nat) : Bool :=
  wfactOK asg f && par (pc &&& gX f) && Nat.blt (cntX (gX f) others) (gR f)

/-- every pair's `w` is orthogonal to `u` -/
def uFree (f u : Nat) : Bool := allLT (2 ^ gR f) (fun l => Nat.beq l 0 || !par (wvec f l &&& u))

/-- the `v`-independent part of a shifted fact: `r ≥ 1`, `X(pc) = 1`, fewer than `r` other points, every pair kills the
terms, and the recorded bits are `wᵀ T(X) z` -/
def sPre (asg : Asg) (pc : Nat) (others : List Nat) (g : Nat) : Bool :=
  Nat.ble 1 (gR (rd 102 g)) && par (pc &&& gX (rd 102 g)) && Nat.blt (cntX (gX (rd 102 g)) others) (gR (rd 102 g)) &&
    allLT (2 ^ gR (rd 102 g)) (fun l => Nat.beq l 0 ||
      (killAll asg (wvec (rd 102 g) l) (zvec (rd 102 g) l) &&
        (sbit g l == bilTX (wvec (rd 102 g) l) (zvec (rd 102 g) l) (gX (rd 102 g)))))

/-- the shifted fact at the guess `(u, v)` -/
def sAt (g u v : Nat) : Bool :=
  allLT (2 ^ gR (rd 102 g)) (fun l => Nat.beq l 0 ||
    xor (sbit g l) (par (wvec (rd 102 g) l &&& u) && par (zvec (rd 102 g) l &&& v)))

/-- an entry: the subset `S`, the point `pc`, the u-free facts, the survivors `(u, shifted facts)` -/
abbrev Entry := List Nat × Nat × List Nat × List (Nat × List Nat)

/-- **a lift3 entry for `S` holds** -/
def entryOK (asg : Asg) (S : List Nat) (E : Entry) : Bool :=
  (E.1 == S) && S.contains E.2.1 &&
    E.2.2.1.all (uPre asg E.2.1 (S.filter (fun p => p != E.2.1))) &&
    E.2.2.2.all (fun sv => sv.2.all (sPre asg E.2.1 (S.filter (fun p => p != E.2.1)))) &&
    allLT 512 (fun u => Nat.beq u 0 || E.2.2.1.any (fun f => uFree f u) ||
      E.2.2.2.any (fun sv => Nat.beq sv.1 u && allLT 512 (fun v => Nat.beq v 0 || sv.2.any (fun g => sAt g u v))))

/-! ## Parsing (any parse is sound; the parser only has to be total) -/

/-- a survivor: `[9] u`, `[6] nv`, `nv` shifted facts of 105 bits -/
def rdSurv (S : Nat) : (Nat × List Nat) × Nat :=
  ((rd 9 S, rdLst 105 (rd 6 (sk 9 S)) (sk 15 S)), sk (15 + 105 * rd 6 (sk 9 S)) S)

def rdSurvs (n S : Nat) : List (Nat × List Nat) × Nat :=
  @Nat.rec (fun _ => Nat → List (Nat × List Nat) × Nat) (fun S => ([], S))
    (fun _ ih S => let a := rdSurv S; let r := ih a.2; (a.1 :: r.1, r.2)) n S

/-- an entry: `[2] k'`, `k'` points of 9 bits, `[9] pc`, `[6] nu`, `nu` facts of 102 bits, `[4] ns`, `ns` survivors -/
def rdEntry (S : Nat) : Entry × Nat :=
  let k' := rd 2 S
  let S1 := sk (2 + 9 * k') S
  let pc := rd 9 S1
  let nu := rd 6 (sk 9 S1)
  let S2 := sk (15 + 102 * nu) S1
  let svs := rdSurvs (rd 4 S2) (sk 4 S2)
  ((rdLst 9 k' (sk 2 S), pc, rdLst 102 nu (sk 15 S1), svs.1), svs.2)

def rdEntries (n S : Nat) : List Entry :=
  @Nat.rec (fun _ => Nat → List Entry) (fun _ => []) (fun _ ih S => let a := rdEntry S; a.1 :: ih a.2) n S

/-- the end of the fact list (`[5] nf` and `nf` facts) -/
def factsEnd (w : Nat) : Nat := sk (5 + 102 * rd 5 w) w

/-- **the lifting test with guessed terms**: `w` = the facts of `ltW`, then `[5] ne` and `ne` lift3 entries; every
`k`-sublist of `pts` has a fact with fewer than `r` active points or an entry -/
def ltW3 (pts : List Nat) (k : Nat) (asg : Asg) (w : Nat) : Bool :=
  (rdLst 102 (rd 5 w) (sk 5 w)).all (wfactOK asg) &&
    (pts.sublistsLen k).all (fun S => (rdLst 102 (rd 5 w) (sk 5 w)).any (fun f => Nat.blt (cntX (gX f) S) (gR f)) ||
      (rdEntries (rd 5 (factsEnd w)) (sk 5 (factsEnd w))).any (fun E => entryOK asg S E))

/-! ## Semantics -/

theorem wvec_lt (f l : Nat) : wvec f l < 512 := by
  unfold wvec; cases Nat.beq (gS f) 0
  · exact gQ_lt f l
  · exact combB_lt _ (fun i => gB_lt f i) l

theorem zvec_lt (f l : Nat) : zvec f l < 512 := by
  unfold zvec; cases Nat.beq (gS f) 0
  · exact combB_lt _ (fun i => gB_lt f i) l
  · exact gQ_lt f l

/-- for the fact's pairs, the right side of a lift with fewer than `r` points has a vanishing pair -/
theorem pair_vanish (f : Nat) (u v : ℕ → Fin 9 → F2) (s : Finset ℕ) (hr1 : 1 ≤ gR f) (hr3 : gR f ≤ 3)
    (hs : s.card < gR f) : ∃ l, 0 < l ∧ l < 2 ^ gR f ∧
      bil (wvec f l) (zvec f l) (∑ p ∈ s, vecMulVec (u p) (v p)) = 0 := by
  cases hside : Nat.beq (gS f) 0
  · obtain ⟨l, hl0, hl2, horth⟩ := orth_exists (gB f) v s (gR f) hr1 hr3 hs
    refine ⟨l, hl0, hl2, ?_⟩
    unfold wvec zvec; rw [hside]; simp only [cond_false]
    rw [bil_fsum]; apply Finset.sum_eq_zero; intro p hp
    rw [bil_vmv, combB_dot, horth p hp]; simp [bf]
  · obtain ⟨l, hl0, hl2, horth⟩ := orth_exists (gB f) u s (gR f) hr1 hr3 hs
    refine ⟨l, hl0, hl2, ?_⟩
    unfold wvec zvec; rw [hside]; simp only [cond_true]
    rw [bil_fsum]; apply Finset.sum_eq_zero; intro p hp
    rw [bil_vmv, combB_dot, horth p hp]; simp [bf]

theorem gR_le3 (f : Nat) : gR f ≤ 3 := by have := rd_lt 2 (sk 9 f); unfold gR; omega

theorem beq_false_of_ne {a : Nat} (h : a ≠ 0) : Nat.beq a 0 = false := by
  cases hb : Nat.beq a 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- the lift at `X` with the guess `N_c` added: the right side loses `N_c` -/
theorem rhs_shift (P : Finset ℕ) (u v : ℕ → Fin 9 → F2) (X pc : Nat) (hpc : pc ∈ P) (hX : par (pc &&& X) = true) :
    (∑ p ∈ P.filter (fun p => par (p &&& X) = true), vecMulVec (u p) (v p)) + vecMulVec (u pc) (v pc) =
      ∑ p ∈ (P.filter (fun p => par (p &&& X) = true)).erase pc, vecMulVec (u p) (v p) := by
  have hmem : pc ∈ P.filter (fun p => par (p &&& X) = true) := Finset.mem_filter.mpr ⟨hpc, hX⟩
  rw [← Finset.add_sum_erase _ _ hmem, add_comm, ← add_assoc]
  have h2 : ∀ M : Matrix (Fin 9) (Fin 9) F2, M + M = 0 := by
    intro M; funext i j; simp only [Matrix.add_apply, Matrix.zero_apply]; exact CharTwo.add_self_eq_zero (M i j)
  rw [h2, zero_add]

theorem cnt_erase (S : List Nat) (hnd : S.Nodup) (P : Finset ℕ) (hSP : ∀ p, p ∈ S ↔ p ∈ P) (X pc : Nat) :
    cntX X (S.filter (fun p => p != pc)) = ((P.filter (fun p => par (p &&& X) = true)).erase pc).card := by
  unfold cntX
  rw [List.filter_filter]
  have hnd' := hnd.filter (fun p => (par (p &&& X) && (p != pc)))
  rw [← List.toFinset_card_of_nodup hnd']
  congr 1
  ext p
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Finset.mem_erase,
    Finset.mem_filter, hSP]
  tauto

/-- the pair check without the value: every term killed gives `wᵀ (T(X) + Σ_l N_e) z = wᵀ T(X) z` -/
theorem killAll_bil (asg : Asg) (X w z : Nat) (hw : w < 512) (hz : z < 512) (hk : killAll asg w z = true) (l : Asg)
    (hl : l.Sublist asg) :
    bil w z (TX (toM3 X) + (l.map (fun e => vecMulVec (nv e.2.1) (nv e.2.2))).sum) = bf (bilTX w z X) := by
  have hk' := killAll_spec w z asg hk
  rw [bil_add, bil_TX _ _ _ hz, bil_list]
  have h0 : (l.map (fun e => bil w z (vecMulVec (nv e.2.1) (nv e.2.2)))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [bil_vmv, dot_nv _ _ hw, dot_nv _ _ hz, ← bf_and, hk' e (hl.subset he)]
    rfl
  rw [h0, add_zero]

theorem wfact_pair (asg : Asg) (f l : Nat) (h : wfactOK asg f = true) (hl0 : 0 < l) (hl : l < 2 ^ gR f) :
    pairOK asg (gX f) (wvec f l) (zvec f l) = true := by
  unfold wfactOK at h
  rw [Bool.and_eq_true] at h
  have h1 := allLT_spec h.2 l hl
  rw [beq_false_of_ne (by omega), Bool.false_or] at h1
  unfold wvec zvec
  cases hs : Nat.beq (gS f) 0
  · rw [hs] at h1; simpa using h1
  · rw [hs] at h1; simpa using h1

theorem bil_guess (w z : Nat) (hw : w < 512) (hz : z < 512) (a b : Fin 9 → F2) :
    bil w z (vecMulVec a b) = bf (par (w &&& natOf a) && par (z &&& natOf b)) := by
  rw [bil_vmv, ← nv_natOf a, ← nv_natOf b, dot_nv _ _ hw, dot_nv _ _ hz, bf_and, nv_natOf, nv_natOf]

/-- **an accepted entry refutes every lift on its subset** -/
theorem entry_sound (asg : Asg) (S : List Nat) (E : Entry) (h : entryOK asg S E = true) (hnd : S.Nodup)
    (P : Finset ℕ) (hSP : ∀ p, p ∈ S ↔ p ∈ P) (u v : ℕ → Fin 9 → F2) (huv : ∀ p ∈ P, u p ≠ 0 ∧ v p ≠ 0)
    (hX : ∀ X, X < 512 → ∃ l : Asg, l.Sublist asg ∧
        TX (toM3 X) + (l.map (fun e => vecMulVec (nv e.2.1) (nv e.2.2))).sum =
          ∑ p ∈ P.filter (fun p => par (p &&& X) = true), vecMulVec (u p) (v p)) : False := by
  unfold entryOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, hpcS⟩, hufs⟩, hsvs⟩, hcov⟩ := h
  have hpcP : E.2.1 ∈ P := (hSP E.2.1).mp (List.contains_iff_mem.mp hpcS)
  obtain ⟨hu0, hv0⟩ := huv E.2.1 hpcP
  have hUlt : natOf (u E.2.1) < 512 := natOf_lt _
  have hVlt : natOf (v E.2.1) < 512 := natOf_lt _
  have hUne : natOf (u E.2.1) ≠ 0 := fun e => hu0 (by rw [← nv_natOf (u E.2.1), e, nv_zero'])
  have hVne : natOf (v E.2.1) ≠ 0 := fun e => hv0 (by rw [← nv_natOf (v E.2.1), e, nv_zero'])
  -- the common argument for a fact with pair vectors `wv`, `zv` at `X`
  have key : ∀ (X r : Nat) (wv zv : Nat → Nat), X < 512 → par (E.2.1 &&& X) = true →
      ((P.filter (fun p => par (p &&& X) = true)).erase E.2.1).card < r →
      (∀ l, 0 < l → l < 2 ^ r → ∀ la : Asg, la.Sublist asg →
        bil (wv l) (zv l) (TX (toM3 X) + (la.map (fun e => vecMulVec (nv e.2.1) (nv e.2.2))).sum +
          vecMulVec (u E.2.1) (v E.2.1)) = 1) →
      (∀ s : Finset ℕ, s.card < r → ∃ l, 0 < l ∧ l < 2 ^ r ∧
          bil (wv l) (zv l) (∑ p ∈ s, vecMulVec (u p) (v p)) = 0) → False := by
    intro X r wv zv hXlt hpX hcnt hpair hvan
    obtain ⟨la, hla, heq⟩ := hX X hXlt
    obtain ⟨l, hl0, hl2, hz⟩ := hvan _ hcnt
    have h1 := hpair l hl0 hl2 la hla
    rw [heq, rhs_shift P u v X E.2.1 hpcP hpX, hz] at h1
    exact absurd h1 (by decide)
  have hcU := allLT_spec hcov (natOf (u E.2.1)) hUlt
  rw [beq_false_of_ne hUne, Bool.false_or, Bool.or_eq_true] at hcU
  rcases hcU with hfree | hsurv
  · -- a u-free fact
    obtain ⟨f, hf, hfu⟩ := List.any_eq_true.mp hfree
    have hpre := List.all_eq_true.mp hufs f hf
    unfold uPre at hpre
    simp only [Bool.and_eq_true] at hpre
    obtain ⟨⟨hwf, hpX⟩, hcnt⟩ := hpre
    have hr1 : 1 ≤ gR f := by
      unfold wfactOK at hwf; rw [Bool.and_eq_true, Nat.ble_eq] at hwf; exact hwf.1
    rw [Nat.blt_eq, cnt_erase S hnd P hSP] at hcnt
    refine key (gX f) (gR f) (wvec f) (zvec f) (rd9_lt f) hpX hcnt (fun l hl0 hl2 la hla => ?_)
      (fun s hs => pair_vanish f u v s hr1 (gR_le3 f) hs)
    rw [bil_add, pairOK_bil asg (gX f) _ _ (wvec_lt f l) (zvec_lt f l) (wfact_pair asg f l hwf hl0 hl2) la hla,
      bil_guess _ _ (wvec_lt f l) (zvec_lt f l)]
    have hfr := allLT_spec hfu l hl2
    rw [beq_false_of_ne (by omega), Bool.false_or, Bool.not_eq_true'] at hfr
    rw [hfr, Bool.false_and]; rfl
  · -- a survivor
    obtain ⟨sv, hsv, hsvc⟩ := List.any_eq_true.mp hsurv
    rw [Bool.and_eq_true] at hsvc
    obtain ⟨hsu, hvloop⟩ := hsvc
    have hsu' : sv.1 = natOf (u E.2.1) := Nat.eq_of_beq_eq_true hsu
    have hcV := allLT_spec hvloop (natOf (v E.2.1)) hVlt
    rw [beq_false_of_ne hVne, Bool.false_or] at hcV
    obtain ⟨g, hg, hgat⟩ := List.any_eq_true.mp hcV
    have hpre := List.all_eq_true.mp (List.all_eq_true.mp hsvs sv hsv) g hg
    unfold sPre at hpre
    simp only [Bool.and_eq_true, Nat.ble_eq] at hpre
    obtain ⟨⟨⟨hr1, hpX⟩, hcnt⟩, hpairs⟩ := hpre
    rw [Nat.blt_eq, cnt_erase S hnd P hSP] at hcnt
    refine key (gX (rd 102 g)) (gR (rd 102 g)) (wvec (rd 102 g)) (zvec (rd 102 g)) (rd9_lt _) hpX hcnt
      (fun l hl0 hl2 la hla => ?_) (fun s hs => pair_vanish (rd 102 g) u v s hr1 (gR_le3 _) hs)
    have hp := allLT_spec hpairs l hl2
    rw [beq_false_of_ne (by omega), Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hk, hb⟩ := hp
    rw [bil_add, killAll_bil asg _ _ _ (wvec_lt _ l) (zvec_lt _ l) hk la hla, ← hb,
      bil_guess _ _ (wvec_lt _ l) (zvec_lt _ l), ← bf_xor]
    have ha := allLT_spec hgat l hl2
    rw [beq_false_of_ne (by omega), Bool.false_or] at ha
    rw [ha]; rfl

/-- **a witness fact with fewer than `r` active points refutes the lift** -/
theorem fact_refutes (asg : Asg) (f : Nat) (hok : wfactOK asg f = true) (P : Finset ℕ) (u v : ℕ → Fin 9 → F2)
    (hlt : (P.filter (fun p => par (p &&& gX f) = true)).card < gR f)
    (hX : ∀ X, X < 512 → ∃ l : Asg, l.Sublist asg ∧
        TX (toM3 X) + (l.map (fun e => vecMulVec (nv e.2.1) (nv e.2.2))).sum =
          ∑ p ∈ P.filter (fun p => par (p &&& X) = true), vecMulVec (u p) (v p)) : False := by
  have hr1 : 1 ≤ gR f := by
    have h := hok; unfold wfactOK at h; rw [Bool.and_eq_true, Nat.ble_eq] at h; exact h.1
  obtain ⟨la, hla, heq⟩ := hX (gX f) (rd9_lt f)
  obtain ⟨l, hl0, hl2, hz⟩ := pair_vanish f u v _ hr1 (gR_le3 f) hlt
  have h1 := pairOK_bil asg (gX f) _ _ (wvec_lt f l) (zvec_lt f l) (wfact_pair asg f l hok hl0 hl2) la hla
  rw [heq, hz] at h1
  exact absurd h1 (by decide)

/-- **soundness of the test with guessed terms** -/
theorem ltW3_sound (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts)
    (asg : Asg) (w : Nat) (h : ltW3 pts k asg w = true) : ¬ LiftKL asg Em k := by
  rintro ⟨P, hcard, hPp, u, v, huv, hX⟩
  have hPpts : ∀ p ∈ P, p ∈ pts := fun p hp => hpts p (hPp p hp).1 (hPp p hp).2.1 (hPp p hp).2.2
  unfold ltW3 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hall, hcov⟩ := h
  set S := pts.filter (fun p => decide (p ∈ P)) with hS
  have hSmem : S ∈ pts.sublistsLen k := by
    rw [List.mem_sublistsLen]
    exact ⟨List.filter_sublist, by rw [hS, len_eq pts hnd P hPpts, hcard]⟩
  have hc := List.all_eq_true.mp hcov S hSmem
  rw [Bool.or_eq_true] at hc
  rcases hc with hfact | hentry
  · obtain ⟨f, hf, hlt⟩ := List.any_eq_true.mp hfact
    rw [Nat.blt_eq, hS, cnt_eq pts hnd P hPpts] at hlt
    exact fact_refutes asg f (List.all_eq_true.mp hall f hf) P u v hlt hX
  · obtain ⟨E, _, hE⟩ := List.any_eq_true.mp hentry
    have hSnd : S.Nodup := hnd.filter _
    have hSP : ∀ p, p ∈ S ↔ p ∈ P := by
      intro p; rw [hS, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hPpts p h, h⟩⟩
    exact entry_sound asg S E hE hSnd P hSP u v huv hX

/-- **SAT leaves with `k` inside terms, the test with guessed terms** -/
theorem leafSLW3_noLiftK (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (h : BC7L.leafSL (ltW3 pts k) R = true) :
    L479.NoLiftK (leafT R) (leafN R) (S6.leafDom6 R) Em k := by
  intro b c hbc hd hl
  exact leafSLQ (ltW3 pts k) (fun b c => L479.LiftK (leafN R) b c Em k)
    (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) h b c hbc hd hl

/-- **the external leaf of a coset IP, refuted by the test with guessed terms** (`k = 22 - R`; any `E`, `R`, `lo`) -/
theorem leafNoExt_of_leafSLW3 {C : E1G.Ctx} {Em lo pl : ℕ} (pts : List Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (cert : ℕ)
    (hN : C.N ≤ 127) (hR : C.R ≤ 31) (hC : E1GS.Cosets Em C.VT C.N) (hD : E1GS.DomPerp C.DOM Em)
    (hDOM : C.DOM < 2 ^ 512)
    (hok : BC7L.leafSL (ltW3 pts (22 - C.R)) (E1G.leafRec C.R C.VT C.DOM pl cert) = true) :
    L479.LeafNoExt C Em lo pl := by
  have h := leafSLW3_noLiftK pts (22 - C.R) Em hnd hpts _ hok
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM] at h
  apply L479.leafNoExt_of_noLiftK hN hR hC hD hDOM
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM]
  exact h

end PL

#print axioms PL.entry_sound
#print axioms PL.fact_refutes
#print axioms PL.ltW3_sound
#print axioms PL.leafSLW3_noLiftK
#print axioms PL.leafNoExt_of_leafSLW3
