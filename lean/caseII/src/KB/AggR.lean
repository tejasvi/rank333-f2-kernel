module
public import R22Port.U_d41d8cd98f00
public import KB.Agg
public import KB.StatFactsR
/-! # KB.AggR: `KB.Agg` for the kernel track's items with ranges

`KB.CheckedAnyRII` (an item with an OPEN root and possibly ranges, `KB.CheckedRII`, or a dead root), its contract in the bridge's
form `KB.segRefH_allR`, and **`KB.segs_of_covKR`**: a `R22N.Cov` derivation over such items (ranges included: `Cov.mk'` takes the
range children's proofs) gives the glued, certified segment family `Top.rank_ge_23_L479` consumes. -/
@[expose] public section
noncomputable section
namespace KB
open R3RT.SpecO

abbrev CheckedAnyRII (k : ℕ) : Prop := CheckedRII k ∨ CheckedDeadII k

theorem segRefH_allR : R22B.SegRefH HII LO123 (CaseK 14 22) CheckedAnyRII := segRefAllRII

theorem segs_of_covKR (x : (ℕ × ℕ) × ℕ) (hx : R22N.Cov CheckedAnyRII x) :
    ∃ (ι : Type) (segs : ι → Top.Seg), (HII → ∀ i, Top.SegOKO LO123 (CaseK 14 22) (segs i)) ∧ Top.GlueOK segs ∧
      ∃ i, (segs i).root = x.1 ∧ (segs i).lo = x.2 :=
  R22B.segs_of_covH HII LO123 (CaseK 14 22) CheckedAnyRII segRefH_allR x hx

end KB
#print axioms KB.segs_of_covKR
