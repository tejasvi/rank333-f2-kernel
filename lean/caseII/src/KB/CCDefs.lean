module
public import R22Port.U_d41d8cd98f00
public import KB.ItemRII
public import KB.RowsCC
/-! # KB.CCDefs: the kernel track's case (II) on the CC route (`L479.cLBW L`, s443/S4/TopCC.lean)

* `KB.TabVCC L`: R3's guarded per-job table over the CC route's row interface `KCC.rowECC L`; `tabVCC_of` builds it from the
  loader's definitions, `tabVCC_sound` gives valid rows under the class facts of `cLBW L` (`KCC.table_specCC`).
* `KB.HCC L`: the facts `Top.rank_ge_23_CC`'s `hsegII` takes, `ClassFactsC (CaseK 14 22) (cLBW L) ∧ KD.TypeFacts`.
* **`KB.segRefRCC`**: case (II)'s contract on the CC route for any label tables with their facts (instances: `KB.CC_<name>_F`). -/
@[expose] public section
set_option maxHeartbeats 4000000
noncomputable section
namespace KB
open R3RT.SpecO KD

/-- the per-job table of a CC-route item -/
def TabVCC (L : List (ℕ × ℕ)) (tab : ℕ → ℕ) : Prop :=
  ∃ (chunk : ℕ → ℕ) (N nch : ℕ), (∀ i, tab i = (chunk (i / 64) >>> (552 * (i % 64))) % 2 ^ 552) ∧
    (∀ q, nch ≤ q → chunk q = 0) ∧ (∀ i, N ≤ i → tab i = 0) ∧ R3RT.tabOKQ (KCC.rowECC L) chunk 64 N nch = true

theorem tabVCC_of (L : List (ℕ × ℕ)) (chunk : ℕ → ℕ) (N nch : ℕ) (entry : ℕ → ℕ)
    (hent : ∀ i, entry i = Nat.land (Nat.shiftRight (chunk (Nat.div i 64)) (Nat.mul 552 (Nat.mod i 64))) (2 ^ 552 - 1))
    (hch : ∀ q, nch ≤ q → chunk q = 0) (hnch : nch = (N + 63) / 64)
    (hlast : Nat.blt (chunk (nch - 1)) (2 ^ (552 * (N - 64 * (nch - 1)))) = true)
    (hok : R3RT.tabOKQ (KCC.rowECC L) chunk 64 N nch = true) : TabVCC L entry := by
  have hent' : ∀ i, entry i = (chunk (i / 64) >>> (552 * (i % 64))) % 2 ^ 552 := by
    intro i; rw [hent i, L5.land_eq, L5.shr_eq, Nat.and_two_pow_sub_one_eq_mod]; rfl
  refine ⟨chunk, N, nch, hent', hch, fun i hi => ?_, hok⟩
  rw [hent' i]
  by_cases hq : nch ≤ i / 64
  · rw [hch _ hq, Nat.zero_shiftRight, Nat.zero_mod]
  · push Not at hq
    have h1 : 64 * nch ≤ N + 63 := by rw [hnch]; exact Nat.mul_div_le (N + 63) 64
    have hlo : 64 * (nch - 1) < N := by omega
    have hi64 : i / 64 = nch - 1 := by omega
    have hmod : N - 64 * (nch - 1) ≤ i % 64 := by omega
    rw [hi64]
    have hb := Nat.blt_eq.mp hlast
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by
      exact Nat.mul_le_mul_left 552 hmod))), Nat.zero_mod]

/-- the facts of case (II) on the CC route -/
abbrev HCC (L : List (ℕ × ℕ)) : Prop := ClassFactsC (CaseK 14 22) (L479.cLBW L) ∧ KD.TypeFacts

theorem tabVCC_sound (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1)
    (hL5 : ∀ p ∈ L, p.1 < 496) (tab : ℕ → ℕ) (h : TabVCC L tab) (hcf : ClassFactsC (CaseK 14 22) (L479.cLBW L)) :
    TabOKO LO123 (CaseK 14 22) tab := by
  obtain ⟨chunk, N, nch, hent, hch, hN, hok⟩ := h
  exact KCC.table_specCC L5W.is123_LO123 (RT.Om.caseK_rankInv 14 22) L hL hL5 chunk tab N nch hent hch hN hcf hok

/-- the CC route's label-table facts from bindings over `rowECC L` -/
theorem c2_of_bindCC (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1)
    (hL5 : ∀ p ∈ L, p.1 < 496) (q : ℕ) (rows : List (ℕ × List ℕ)) (stored DC : ℕ)
    (hcf : ClassFactsC (CaseK 14 22) (L479.cLBW L)) :
    (q < 511 → R3RT.bindQ (KCC.rowECC L) q 2 rows stored DC = true → R3RT.SpecO.C2OK LO123 (CaseK 14 22) q stored) ∧
    (R3RT.bindQ (KCC.rowECC L) 511 1 rows stored DC = true → R3RT.SpecO.Conf1OK LO123 (CaseK 14 22) stored) :=
  KCC.bindQ_specCC L5W.is123_LO123 (RT.Om.caseK_rankInv 14 22) L hL hL5 q rows stored DC hcf

/-- **case (II)'s contract on the CC route**, for label tables `c2T` / `c1` with their facts under `HCC L` -/
theorem segRefRCC (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1)
    (hL5 : ∀ p ∈ L, p.1 < 496) {c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {c1 : ℕ}
    (hh : ∀ l, l < 511 → HOK LO123 l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hc1 : HCC L → Conf1OK LO123 (CaseK 14 22) c1) (hc2 : HCC L → ∀ l, l < 511 → C2OKU (CaseK 14 22) l (c2T l)) :
    SegRefHK (HCC L) LO123 (CaseK 14 22)
      (CheckedR R3RT.nperpL c2T hkT cpT (fun tab => extIIR R3RT.nperpL c2T hkT cpT tab) accIIR xkIIR rgIIR c1 (TabVCC L)) :=
  segRefHR (HCC L) npOK_123 hh hcp (fun _ h => h) c1 hc1 hc2
    (fun hH tab hT => extIIR_soundII tab npOK_123 hT (hc2 hH) hh hcp hH.2) (TabVCC L)
    (fun tab h hH => tabVCC_sound L hL hL5 tab h hH.1)

/-- **an item with a dead root on the CC route is a certified segment** (`segRefDeadII` with `TabVCC L` and `HCC L`) -/
theorem segRefDeadCC (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1)
    (hL5 : ∀ p ∈ L, p.1 < 496) {c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {c1 : ℕ}
    (hh : ∀ l, l < 511 → HOK LO123 l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hc1 : HCC L → Conf1OK LO123 (CaseK 14 22) c1) (hc2 : HCC L → ∀ l, l < 511 → KD.C2OKU (CaseK 14 22) l (c2T l)) :
    SegRefHK (HCC L) LO123 (CaseK 14 22) (CheckedDeadK R3RT.nperpL c2T hkT cpT c1 (TabVCC L)) := by
  intro key ⟨tab, pl, W, lastP, f0, k, htv, hroot, hdk, hkr, hlo, hrng, hext⟩
  refine ⟨⟨(R22N.SegI.ofKey key).root, (R22N.SegI.ofKey key).lo, ∅, {(R22N.SegI.ofKey key).root},
    {e | e ∈ (R22N.SegI.ofKey key).ext}, {p | p ∈ (R22N.SegI.ofKey key).rng}⟩, rfl, rfl, rfl, rfl, fun hH => ?_⟩
  have hT : TabOKO LO123 (CaseK 14 22) tab := tabVCC_sound L hL hL5 tab htv hH.1
  have hF := rootChkW_sound (hc1 hH) (hc2 hH) hh hT hroot
  obtain ⟨_, _, hdead⟩ := dkidOK_sound npOK_123 hT (hc2 hH) hh hcp hH.2 hF (rootChkW_top hroot) k hdk
  refine ⟨Or.inr rfl, fun h0 => by simp [hlo] at h0, fun p hp => by simp [hrng] at hp, fun n hn => ?_,
    fun n hn => absurd hn (Set.notMem_empty n)⟩
  rw [Set.mem_singleton_iff] at hn
  subst hn
  rw [hkr]
  intro A _ hC hB
  exact hdead A hC hC.1 (Top.dec22_bc HC.rr_all A) hB

/-- the cap list's side conditions as one decided fact -/
theorem capL_of_all (L : List (ℕ × ℕ))
    (h : L.all (fun p => Nat.ble (_root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1) (p.2 + 1) && Nat.blt p.1 496) = true) :
    (∀ p ∈ L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) ∧ (∀ p ∈ L, p.1 < 496) := by
  rw [List.all_eq_true] at h
  exact ⟨fun p hp => by have := h p hp; simp only [Bool.and_eq_true, Nat.ble_eq] at this; exact this.1,
    fun p hp => by have := h p hp; simp only [Bool.and_eq_true, Nat.blt_eq] at this; exact this.2⟩

end KB
#print axioms KB.segRefRCC
#print axioms KB.segRefDeadCC
