module
public import R22Port.U_d41d8cd98f00
public import S4.CC422
public import S4.CC436
/-! # `Top.rank_ge_23_436_422`: the CC route with the plane caps 436 and 422 

`Top.rank_ge_23_CC` at `L = [(436, 19), (422, 19)]`, with each instance given by its enumeration and leaf certificates. -/
@[expose] public section

noncomputable section
namespace Top
open RootSound R3RT R3RT.SpecO Finset Classical

theorem rank_ge_23_436_422
    (hPoint : HC.ClassLB 492 21)
    (hCap : ∀ p ∈ HC.T_K3eD_Cls.RL, p.1 ≠ 492 → HC.ClassLB p.1 p.2)
    (g175 : G.NoFam_17_5_0) (g1903 : G.NoFam_19_0_3) (g1822 : G.NoFam_18_2_2) (g1741 : G.NoFam_17_4_1)
    (g1732 : G.NoFam_17_3_2) (g1813 : G.NoFam_18_1_3)
    (oc0 : G.OrbitComplete2) (oc1 : G.OrbitComplete3 1) (oc2 : G.OrbitComplete3 2)
    -- the E1G chains on c436 / c422 and the external-leaf certificates
    (ext436 : List ℕ) (henum436 : L479.EnumOK (E1G.OK_c436.Cx ext436) E1G.OK_c436.sl E1G.IP_c436.UB)
    (hext436 : ∀ pl ∈ ext436, L479.LeafNoExt (E1G.OK_c436.Cx ext436) E1G.IP_c436.Em 14 pl)
    (ext422 : List ℕ) (henum422 : L479.EnumOK (E1G.OK_c422.Cx ext422) E1G.OK_c422.sl E1G.IP_c422.UB)
    (hext422 : ∀ pl ∈ ext422, L479.LeafNoExt (E1G.OK_c422.Cx ext422) E1G.IP_c422.Em 14 pl)
    (ιII : Type) (segII : ιII → Seg)
    (hsegII : ClassFactsC (CaseK 14 22) (L479.cLBW [(436, 19), (422, 19)]) → KD.TypeFacts →
      ∀ k, SegOKO LO123 (CaseK 14 22) (segII k))
    (hglueII : GlueOK segII) (hrootII : ∃ k, (segII k).root = (1, 0) ∧ (segII k).lo = 0)
    (ιI : Type) (segI : ιI → Seg) (hsegI : Spec.ClassFacts → ∀ k, SegOKO Top321.O (CaseK 0 12) (segI k))
    (hglueI : GlueOK segI)
    (hrootI : ∀ l ∈ ([0, 168, 462] : List ℕ), ∃ k, (segI k).root = (2 ^ l, l) ∧ (segI k).lo = 0)
    (ιI13 : Type) (segI13 : ιI13 → Seg) (hsegI13 : Spec.ClassFacts → ∀ k, SegOKO Top321.O (CaseK 13 13) (segI13 k))
    (hglueI13 : GlueOK segI13)
    (hrootI13 : ∀ l ∈ ([0, 168, 462] : List ℕ), ∃ k, (segI13 k).root = (2 ^ l, l) ∧ (segI13 k).lo = 0) :
    RankGe23 :=
  rank_ge_23_CC hPoint hCap g175 g1903 g1822 g1741 g1732 g1813 oc0 oc1 oc2 [(436, 19), (422, 19)]
    (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> norm_num)
    (fun p hp => by
      simp at hp
      rcases hp with rfl | rfl
      · exact L479.CC436.inst ext436 henum436 hext436
      · exact L479.CC422.inst ext422 henum422 hext422)
    ιII segII hsegII hglueII hrootII ιI segI hsegI hglueI hrootI ιI13 segI13 hsegI13 hglueI13 hrootI13

end Top
end

#print axioms Top.rank_ge_23_436_422
