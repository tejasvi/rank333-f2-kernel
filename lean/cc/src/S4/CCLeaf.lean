module
public import R22Port.U_d41d8cd98f00
public import S4.PlaneW3
public import S4.TopCC
/-! # External leaves of a CC instance from their certificates

`PL.leafNoExt_of_cert`: an external leaf `pl` of a coset IP with record `E1G.leafRec C.R C.VT C.DOM pl cert` is refuted for
the parametric glue (`L479.LeafNoExt C Em lo pl`) when its record is UNSAT (`S5.NoDecomp`, the v7 certificate) or
passes the lifting test with guessed terms (`BC7L.leafSL (PL.ltW3 pts (22 - C.R))`, SAT leaves). `PL.leaves_of_cert`: the same for
every leaf of a list, from the IP facts (`L479.IPG`). -/
@[expose] public section

namespace PL

theorem leafNoExt_of_cert {C : E1G.Ctx} {Em lo pl : ℕ} (pts : List Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (cert : ℕ)
    (hN : C.N ≤ 127) (hR : C.R ≤ 31) (hC : E1GS.Cosets Em C.VT C.N) (hD : E1GS.DomPerp C.DOM Em)
    (hDOM : C.DOM < 2 ^ 512)
    (h : S5.NoDecomp (S5.leafT (E1G.leafRec C.R C.VT C.DOM pl cert)) (S5.leafN (E1G.leafRec C.R C.VT C.DOM pl cert))
        (S6.leafDom6 (E1G.leafRec C.R C.VT C.DOM pl cert)) ∨
      BC7L.leafSL (ltW3 pts (22 - C.R)) (E1G.leafRec C.R C.VT C.DOM pl cert) = true) :
    L479.LeafNoExt C Em lo pl := by
  rcases h with hnd' | hsl
  · apply L479.leafNoExt_of_nd hN hR hC hD hDOM
    rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
      E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM]
    rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
      E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM] at hnd'
    exact hnd'
  · exact leafNoExt_of_leafSLW3 pts hnd hpts cert hN hR hC hD hDOM hsl

/-- every external leaf of an IP from its certificate (UNSAT or the witness lifting test) -/
theorem leaves_of_cert {C : E1G.Ctx} {CL Em lo LB LBR UB Ntab nrows i2 : ℕ} {sl tab : ℕ → ℕ} {GE : ℕ → Bool × ℕ × ℕ}
    (hip : L479.IPG C CL Em lo LB LBR UB Ntab nrows i2 sl tab GE) (pts : List Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (cert : ℕ → ℕ)
    (h : ∀ pl ∈ C.EXT,
      S5.NoDecomp (S5.leafT (E1G.leafRec C.R C.VT C.DOM pl (cert pl))) (S5.leafN (E1G.leafRec C.R C.VT C.DOM pl (cert pl)))
        (S6.leafDom6 (E1G.leafRec C.R C.VT C.DOM pl (cert pl))) ∨
      BC7L.leafSL (ltW3 pts (22 - C.R)) (E1G.leafRec C.R C.VT C.DOM pl (cert pl)) = true) :
    ∀ pl ∈ C.EXT, L479.LeafNoExt C Em lo pl :=
  fun pl hpl => leafNoExt_of_cert pts hnd hpts (cert pl) hip.N_le (by have := hip.R_le; omega) hip.cosets hip.domperp
    hip.DOM_lt (h pl hpl)

/-- **an external leaf from a split SAT-leaf module**: the module's public `NoLiftK` for its record literal `R`, once `R` is
the IP's `E1G.leafRec` of the leaf (by `rfl` or `decide`), gives `LeafNoExt` -/
theorem leafNoExt_of_noLiftK_rec {C : E1G.Ctx} {Em lo pl : ℕ} (cert R : ℕ) (hR : R = E1G.leafRec C.R C.VT C.DOM pl cert)
    (hN : C.N ≤ 127) (hR31 : C.R ≤ 31) (hC : E1GS.Cosets Em C.VT C.N) (hD : E1GS.DomPerp C.DOM Em)
    (hDOM : C.DOM < 2 ^ 512) (h : L479.NoLiftK (S5.leafT R) (S5.leafN R) (S6.leafDom6 R) Em (22 - C.R)) :
    L479.LeafNoExt C Em lo pl := by
  subst hR
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM] at h
  apply L479.leafNoExt_of_noLiftK hN hR31 hC hD hDOM
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM]
  exact h

/-- the points of `E` listed: a decidable check over the 512 vectors -/
def ptsOK (pts : List Nat) (Em : Nat) : Bool :=
  S5.allLT 512 (fun p => Nat.beq p 0 || !Em.testBit p || pts.contains p)

theorem ptsOK_spec {pts : List Nat} {Em : Nat} (h : ptsOK pts Em = true) :
    ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts := by
  intro p hp h0 he
  have h1 := S5.allLT_spec h p hp
  have hb : Nat.beq p 0 = false := by
    cases hq : Nat.beq p 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hq) h0
  rw [hb, he] at h1
  simpa using h1

end PL

#print axioms PL.leafNoExt_of_cert
#print axioms PL.leaves_of_cert
#print axioms PL.leafNoExt_of_noLiftK_rec
#print axioms PL.ptsOK_spec
