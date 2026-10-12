module
public import R22Port.U_d41d8cd98f00
public import KB.CC_cc436_422_F
public import KB.AggR
/-! # KB.AggCC_cc436_422: `KB.AggR` on the CC route's table cc436_422

`KB.CheckedAnyCC_cc436_422` (an OPEN-root item with possibly ranges, `KB.CheckedRCC_cc436_422`, or a dead root), and
**`KB.segs_of_covKCC_cc436_422`**: a `R22N.Cov` derivation over such items gives the glued, certified segment family under
`KB.HCC KCC_cc436_422.L`. -/
@[expose] public section
noncomputable section
namespace KB
open R3RT.SpecO

abbrev CheckedAnyCC_cc436_422 (k : ℕ) : Prop := CheckedRCC_cc436_422 k ∨ CheckedDeadCC_cc436_422 k

theorem segs_of_covKCC_cc436_422 (x : (ℕ × ℕ) × ℕ) (hx : R22N.Cov CheckedAnyCC_cc436_422 x) :
    ∃ (ι : Type) (segs : ι → Top.Seg), (HCC KCC_cc436_422.L → ∀ i, Top.SegOKO LO123 (CaseK 14 22) (segs i)) ∧ Top.GlueOK segs ∧
      ∃ i, (segs i).root = x.1 ∧ (segs i).lo = x.2 :=
  R22B.segs_of_covH (HCC KCC_cc436_422.L) LO123 (CaseK 14 22) CheckedAnyCC_cc436_422 segRefAllRCC_cc436_422 x hx

theorem allL_imp {α : Type} {P Q : α → Prop} (h : ∀ x, P x → Q x) : ∀ {l : List α}, R22N.AllL P l → R22N.AllL Q l
  | [], _ => trivial
  | a :: l, hl => ⟨h a hl.1, allL_imp h hl.2⟩

/-- the stand-in top's per-key statement -/
def SegsOfKeyCC (k : ℕ) : Prop :=
  ∃ (ι : Type) (segs : ι → Top.Seg), (HCC KCC_cc436_422.L → ∀ i, Top.SegOKO R3RT.SpecO.LO123 (R3RT.SpecO.CaseK 14 22) (segs i)) ∧
    Top.GlueOK segs ∧ ∃ i, (segs i).root = (R22N.SegI.ofKey k).root ∧ (segs i).lo = (R22N.SegI.ofKey k).lo

def CovOfKeyCC (k : ℕ) : Prop := R22N.Cov CheckedAnyCC_cc436_422 ((R22N.SegI.ofKey k).root, (R22N.SegI.ofKey k).lo)

theorem segsOfKey_of_cov (k : ℕ) (h : CovOfKeyCC k) : SegsOfKeyCC k :=
  segs_of_covKCC_cc436_422 _ h

/-- an item without external children or ranges covers its interface -/
theorem covOfKey_leaf (k : ℕ) (hk : CheckedAnyCC_cc436_422 k) (he : (R22N.SegI.ofKey k).ext = [])
    (hr : (R22N.SegI.ofKey k).rng = []) : CovOfKeyCC k :=
  R22N.Cov.mk k hk (fun e h => by rw [he] at h; cases h) (fun p h => by rw [hr] at h; cases h)

end KB
#print axioms KB.segs_of_covKCC_cc436_422
