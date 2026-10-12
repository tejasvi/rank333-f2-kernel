module
public import R22Port.U_d41d8cd98f00
public import Top.TopL479
public import LG.CapT
public import LG.RR495
/-! # Context caps in case (II) as data: `Top.rank_ge_23_CC` (and `Top.rank_ge_23_P443`, its 443 instance)

The L479 route's case-(II) table is C3eD with class 479 raised (`HC.cLBII`). The CC route replaces it by C3eD, Lemma W(a)
and any list `L` of context caps: `(c, R) ∈ L` says that when at least 14 first factors are rank 1, at least `R + 1` first
factors lie outside `K_c` (at most `21 - R` on `K_c`), i.e. class `c` at `R + 1`.

* `L479.cLBW L`: the table of case (II): `(c, R) ∈ L` puts class `c` at `R + 1` (the first entry for a class counts);
  otherwise class 18 (`{row 2 = 0}`, `K_18 = 2^64 - 1`) at 11 (Lemma W(a), `L479.lemmaWa`), every other class at C3eD's
  bound.
* `L479.CCInst c R lo`: one context-cap instance CC(E, 22 - R, lo) for class `c`: a coset IP on a representative `E` of
  class `c` with its facts (`IPG` on the C3eD table), `C.R = R`, its enumeration (`EnumOK`), its external leaves
  (`LeafNoExt`, by `leafNoExt_of_nd` for UNSAT leaves and the plane NoLift checker for SAT leaves), `R ≤` the class's C3eD
  bound, and the two symmetries between `E` and `K_c` (`HC.mapsTo`, decided per instance).
* `L479.capG_of_inst`: `CCInst c R lo` gives `CapG K_c R lo` (`capG_of`, `factN_transport`, `capG_transport`).
* `L479.classFactsW_of`: the caps of `L` give `ClassFactsC (CaseK lo hi) (cLBW L)`.
* `Top.rank_ge_23_CC`: `RankGe23` from the L479 route's hypotheses with `hIPL`/`hEnum`/`hExt` replaced by
  `hCC : ∀ p ∈ L, L479.CCInst p.1 p.2 14` and `hsegII` stated against `cLBW L`.
* `Top.rank_ge_23_P443`: the instance `L = [(443, 19)]`. -/
@[expose] public section

set_option linter.unusedVariables false

namespace L479
open Finset

/-- **the case-(II) table of the CC route**: the context caps `L` (`(c, R) ∈ L`: class `c` at `R + 1`; the first entry for a
class counts), Lemma W(a) (class 18 at 11), C3eD elsewhere -/
def cLBW (L : List (ℕ × ℕ)) (c : ℕ) : ℕ :=
  match L.find? (fun p => p.1 == c) with
  | some p => p.2 + 1
  | none => if c = 18 then 11 else RT.cLB RT.K3eD_Cls.CL c

/-- class 18 is `{row 2 = 0}` -/
theorem kM18 : RT.kM RT.K3eD_Cls.CL 18 = 2 ^ 64 - 1 := by decide +kernel

/-- **Lemma W(a) as a class fact**: every `Dec22` has at least 11 first factors outside `K_18` -/
theorem fact18 (A : R3RT.Spec.Dec22) :
    11 ≤ (univ.filter (fun s => (RT.kM RT.K3eD_Cls.CL 18).testBit (A.av s) = false)).card := by
  have h := (lemmaWa A.av A.b A.c A.lt A.dec (le_refl 22)).1
  refine le_trans h (le_of_eq (congrArg Finset.card (Finset.filter_congr (fun s _ => ?_))))
  rw [kM18, Nat.testBit_two_pow_sub_one]
  simp

/-- **the class facts of `CaseK lo hi` under the CC table** -/
theorem classFactsW_of (L : List (ℕ × ℕ)) (lo hi : ℕ)
    (hcap : ∀ p ∈ L, CapG (RT.kM RT.K3eD_Cls.CL p.1) p.2 lo)
    (hclsN : ∀ c, c < 496 → RT.FactN 22 (RT.kM RT.K3eD_Cls.CL c) (RT.cLB RT.K3eD_Cls.CL c)) :
    R3RT.SpecO.ClassFactsC (R3RT.SpecO.CaseK lo hi) (cLBW L) := by
  intro A hΩ c hc
  unfold cLBW
  cases hf : L.find? (fun p => p.1 == c) with
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpc : p.1 = c := by have := List.find?_some hf; simpa using this
    have := hcap p hp A (by rw [← KD.nType_eq]; exact hΩ.1)
    rw [hpc] at this
    exact this
  | none =>
    simp only
    split_ifs with h18
    · subst h18; exact fact18 A
    · exact hclsN c hc A.av A.b A.c A.lt A.ne A.inj A.dec

/-- **weakening**: class facts for `lb` give class facts for every pointwise smaller `lb'` (a case-(II) table that does not use
W(a) or a cap of `L` checks against its own bounds) -/
theorem classFactsC_mono {Ω : R3RT.Spec.Dec22 → Prop} {lb lb' : ℕ → ℕ} (hle : ∀ c, c < 496 → lb' c ≤ lb c)
    (h : R3RT.SpecO.ClassFactsC Ω lb) : R3RT.SpecO.ClassFactsC Ω lb' :=
  fun A hA c hc => le_trans (hle c hc) (h A hA c hc)

theorem cLBW_443 : cLBW [(443, 19)] 443 = 20 ∧ cLBW [(443, 19)] 18 = 11 := by decide
theorem cLBW_436_422 : cLBW [(436, 19), (422, 19)] 436 = 20 ∧ cLBW [(436, 19), (422, 19)] 422 = 20 := by decide

theorem cLBW_nil_le (c : ℕ) : RT.cLB RT.K3eD_Cls.CL c ≤ cLBW [] c := by
  unfold cLBW; simp only [List.find?_nil]
  split_ifs with h
  · subst h; rw [show RT.cLB RT.K3eD_Cls.CL 18 = 9 by decide +kernel]; omega
  · exact le_refl _

/-- **a context-cap instance** CC(E, 22 - R, lo) for class `c`: the facts of a coset IP on a representative `E` of class `c`
(`IPG` on the C3eD table, `R` outside first factors), its enumeration, its external leaves, `R ≤` the class's C3eD bound,
and symmetries mapping `K_c` into `E` and `E` into `K_c` (`HC.mapsTo t P Q m m'`: every point of `m'` goes into `m`) -/
def CCInst (c R lo : ℕ) : Prop :=
  ∃ (C : E1G.Ctx) (Em LB LBR UB Ntab nrows i2 : ℕ) (sl tab : ℕ → ℕ) (GE : ℕ → Bool × ℕ × ℕ),
    IPG C RT.K3eD_Cls.CL Em lo LB LBR UB Ntab nrows i2 sl tab GE ∧ C.R = R ∧ EnumOK C sl UB ∧
    (∀ pl ∈ C.EXT, LeafNoExt C Em lo pl) ∧ R ≤ RT.cLB RT.K3eD_Cls.CL c ∧
    (∃ (t : Bool) (P Q : ℕ), C3.isGL P = true ∧ C3.isGL Q = true ∧
      HC.mapsTo t P Q Em (RT.kM RT.K3eD_Cls.CL c) = true) ∧
    (∃ (t : Bool) (P Q : ℕ), C3.isGL P = true ∧ C3.isGL Q = true ∧
      HC.mapsTo t P Q (RT.kM RT.K3eD_Cls.CL c) Em = true)

/-- **the context cap of an instance** -/
theorem capG_of_inst {c R lo : ℕ} (h : CCInst c R lo)
    (hclsN : ∀ c, c < 496 → RT.FactN 22 (RT.kM RT.K3eD_Cls.CL c) (RT.cLB RT.K3eD_Cls.CL c))
    (h495 : RT.Fact (RT.kM RT.K3eD_Cls.CL 495) 22) (hc : c < 496) : CapG (RT.kM RT.K3eD_Cls.CL c) R lo := by
  obtain ⟨C, Em, LB, LBR, UB, Ntab, nrows, i2, sl, tab, GE, hip, hR, henum, hext, hRc, ⟨t, P, Q, hP, hQ, hK⟩,
    ⟨t', P', Q', hP', hQ', hE⟩⟩ := h
  have hb : RT.FactN 22 Em C.R := by
    have h1 := factN_transport hP' hQ' hE (hclsN c hc)
    intro av b c' hav hnz hinj hd
    have := h1 av b c' hav hnz hinj hd
    omega
  have h2 := capG_of C RT.K3eD_Cls.CL Em lo LB LBR UB Ntab nrows i2 sl tab GE hip henum hext hclsN hb h495
  rw [hR] at h2
  exact capG_transport hP hQ hK h2

end L479

noncomputable section
namespace Top
open RootSound R3RT R3RT.SpecO Finset Classical

/-- **`R_F2(<3,3,3>) ≥ 23` on the CC route**: the L479 route with the l479cw hypotheses replaced by context-cap instances
`hCC` for the list `L` (class, outside count), and case (II) checked under the table `L479.cLBW L` (C3eD, W(a), `L`).
Classes of `L` must be `< 496`. -/
theorem rank_ge_23_CC
    -- the point lemma (E1P)
    (hPoint : HC.ClassLB 492 21)
    -- dims 4-5, lines, planes and dim 3: the 110 raised classes
    (hCap : ∀ p ∈ HC.T_K3eD_Cls.RL, p.1 ≠ 492 → HC.ClassLB p.1 p.2)
    -- the Gram-state checkers (`G/Main.lean`)
    (g175 : G.NoFam_17_5_0) (g1903 : G.NoFam_19_0_3) (g1822 : G.NoFam_18_2_2) (g1741 : G.NoFam_17_4_1)
    (g1732 : G.NoFam_17_3_2) (g1813 : G.NoFam_18_1_3)
    (oc0 : G.OrbitComplete2) (oc1 : G.OrbitComplete3 1) (oc2 : G.OrbitComplete3 2)
    -- the context caps of case (II): one CC instance per entry (class, R) of `L` (coset IP facts, enumeration, leaves)
    (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 < 496) (hCC : ∀ p ∈ L, L479.CCInst p.1 p.2 14)
    -- case (II) under the table `cLBW L`, every segment checked at Ω = case (II)
    (ιII : Type) (segII : ιII → Seg)
    (hsegII : ClassFactsC (CaseK 14 22) (L479.cLBW L) → KD.TypeFacts → ∀ k, SegOKO LO123 (CaseK 14 22) (segII k))
    -- the case-(II) manifest
    (hglueII : GlueOK segII) (hrootII : ∃ k, (segII k).root = (1, 0) ∧ (segII k).lo = 0)
    -- cases (I) and (I13) under `--rord 321`, with their manifests
    (ιI : Type) (segI : ιI → Seg) (hsegI : Spec.ClassFacts → ∀ k, SegOKO Top321.O (CaseK 0 12) (segI k))
    (hglueI : GlueOK segI)
    (hrootI : ∀ l ∈ ([0, 168, 462] : List ℕ), ∃ k, (segI k).root = (2 ^ l, l) ∧ (segI k).lo = 0)
    (ιI13 : Type) (segI13 : ιI13 → Seg) (hsegI13 : Spec.ClassFacts → ∀ k, SegOKO Top321.O (CaseK 13 13) (segI13 k))
    (hglueI13 : GlueOK segI13)
    (hrootI13 : ∀ l ∈ ([0, 168, 462] : List ℕ), ∃ k, (segI13 k).root = (2 ^ l, l) ∧ (segI13 k).lo = 0) :
    RankGe23 := by
  have hcf : Spec.ClassFacts := classFacts_of hCap
  have hty : KD.TypeFacts := G.Br.typeFacts g175 g1903 g1822 g1741 g1732 g1813 oc0 oc1 oc2
  have hcaps : ∀ p ∈ L, L479.CapG (RT.kM RT.K3eD_Cls.CL p.1) p.2 14 :=
    fun p hp => L479.capG_of_inst (hCC p hp) hcf L479.h495 (hL p hp)
  have hcfII : ClassFactsC (CaseK 14 22) (L479.cLBW L) := L479.classFactsW_of L 14 22 hcaps hcf
  have hI : CaseIEmpty := fun A _ hA =>
    caseK321_of_segs 0 12 segI (hsegI hcf) hglueI hrootI A ⟨Nat.zero_le _, hA⟩
  have hI13 : CaseI13Empty := fun A _ hA =>
    caseK321_of_segs 13 13 segI13 (hsegI13 hcf) hglueI13 hrootI13 A ⟨le_of_eq hA.symm, le_of_eq hA⟩
  exact rank_ge_23_of_cases HC.rr_all hPoint hI hI13 (caseII_of_segs segII (hsegII hcfII hty) hglueII hrootII)

/-- **the 443 instance**: the plane cap CC(P443, 3, 14) (class 443 at 20) in place of L479 -/
theorem rank_ge_23_P443
    (hPoint : HC.ClassLB 492 21)
    (hCap : ∀ p ∈ HC.T_K3eD_Cls.RL, p.1 ≠ 492 → HC.ClassLB p.1 p.2)
    (g175 : G.NoFam_17_5_0) (g1903 : G.NoFam_19_0_3) (g1822 : G.NoFam_18_2_2) (g1741 : G.NoFam_17_4_1)
    (g1732 : G.NoFam_17_3_2) (g1813 : G.NoFam_18_1_3)
    (oc0 : G.OrbitComplete2) (oc1 : G.OrbitComplete3 1) (oc2 : G.OrbitComplete3 2)
    -- E1G instance, chains, IP facts and leaves: CC(P443, 3, 14)
    (hCC443 : L479.CCInst 443 19 14)
    (ιII : Type) (segII : ιII → Seg)
    (hsegII : ClassFactsC (CaseK 14 22) (L479.cLBW [(443, 19)]) → KD.TypeFacts →
      ∀ k, SegOKO LO123 (CaseK 14 22) (segII k))
    (hglueII : GlueOK segII) (hrootII : ∃ k, (segII k).root = (1, 0) ∧ (segII k).lo = 0)
    (ιI : Type) (segI : ιI → Seg) (hsegI : Spec.ClassFacts → ∀ k, SegOKO Top321.O (CaseK 0 12) (segI k))
    (hglueI : GlueOK segI)
    (hrootI : ∀ l ∈ ([0, 168, 462] : List ℕ), ∃ k, (segI k).root = (2 ^ l, l) ∧ (segI k).lo = 0)
    (ιI13 : Type) (segI13 : ιI13 → Seg) (hsegI13 : Spec.ClassFacts → ∀ k, SegOKO Top321.O (CaseK 13 13) (segI13 k))
    (hglueI13 : GlueOK segI13)
    (hrootI13 : ∀ l ∈ ([0, 168, 462] : List ℕ), ∃ k, (segI13 k).root = (2 ^ l, l) ∧ (segI13 k).lo = 0) :
    RankGe23 :=
  rank_ge_23_CC hPoint hCap g175 g1903 g1822 g1741 g1732 g1813 oc0 oc1 oc2 [(443, 19)]
    (fun p hp => by simp at hp; rw [hp]; norm_num) (fun p hp => by simp at hp; rw [hp]; exact hCC443)
    ιII segII hsegII hglueII hrootII ιI segI hsegI hglueI hrootI ιI13 segI13 hsegI13 hglueI13 hrootI13

end Top
end

#print axioms L479.fact18
#print axioms L479.classFactsW_of
#print axioms L479.capG_of_inst
#print axioms L479.classFactsC_mono
#print axioms Top.rank_ge_23_CC
#print axioms Top.rank_ge_23_P443
