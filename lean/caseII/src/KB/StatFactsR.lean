module
public import R22Port.U_d41d8cd98f00
public import KB.StatFactsII
public import KB.ItemRII
public import KB.StatR
/-! # KB.StatFactsR: case (II)'s contract for items with ranges, without hypotheses

`KB.segRefRII_full : SegRefHK HII LO123 (CaseK 14 22) CheckedRII` (the static facts of `KB.StatFactsII`), and
`KB.segRefAllRII` for the kernel track's item predicate with ranges (an item whose root is OPEN, with ranges, or dead). -/
@[expose] public section
noncomputable section
namespace KB
open R3RT.SpecO

theorem segRefRII_full : SegRefHK HII LO123 (CaseK 14 22) CheckedRII := segRefRII hhII hcpII hc1II hc2II

theorem segRefAllRII : SegRefHK HII LO123 (CaseK 14 22) (fun k => CheckedRII k ∨ CheckedDeadII k) :=
  fun k h => h.elim (segRefRII_full k) (segRefDeadII_full k)

end KB
#print axioms KB.segRefRII_full
#print axioms KB.segRefAllRII
