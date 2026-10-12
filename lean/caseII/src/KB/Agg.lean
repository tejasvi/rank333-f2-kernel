module
public import R22Port.U_d41d8cd98f00
public import KB.StatFactsII
public import R22B.Segs
/-! # KB.Agg: kernel-checked items glued by `R22N.Cov` into the segment hypotheses

`KB.CheckedAnyII`: the kernel track's item predicate (an OPEN-root item, `KB.CheckedII`, or a dead-root item, `KB.CheckedDeadII`).
`KB.segRefH_all`: its refinement contract in the bridge's form (`R22B.SegRefH`; `KB.segRefAllII` by `Iff.rfl`).
**`KB.segs_of_covK`**: a `Cov` derivation over kernel-checked items (an aggregator module: `R22N.Cov.mk'` per item, children first)
gives what `Top.rank_ge_23_L479` consumes per case: a family of segments, each certified under the facts, glued, with the covered
interface as a root (the bridge's `R22B.segs_of_covH`). -/
@[expose] public section
noncomputable section
namespace KB
open R3RT.SpecO

/-- the kernel track's item predicate: an item whose root is OPEN or dead -/
abbrev CheckedAnyII (k : ℕ) : Prop := CheckedII k ∨ CheckedDeadII k

/-- the kernel track's contract in the bridge's form -/
theorem segRefH_all : R22B.SegRefH HII LO123 (CaseK 14 22) CheckedAnyII := segRefAllII

/-- **a covered interface is the root of a glued family of certified segments** -/
theorem segs_of_covK (x : (ℕ × ℕ) × ℕ) (hx : R22N.Cov CheckedAnyII x) :
    ∃ (ι : Type) (segs : ι → Top.Seg), (HII → ∀ i, Top.SegOKO LO123 (CaseK 14 22) (segs i)) ∧ Top.GlueOK segs ∧
      ∃ i, (segs i).root = x.1 ∧ (segs i).lo = x.2 :=
  R22B.segs_of_covH HII LO123 (CaseK 14 22) CheckedAnyII segRefH_all x hx

end KB
#print axioms KB.segs_of_covK
