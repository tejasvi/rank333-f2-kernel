module
public import R22Port.U_d41d8cd98f00
public import R22B.Corollaries
meta import KMod.Audit
/-! # R22K.Cor: the corollaries of `Top.RankGe23` for the final file (R22B.Cor.*, as R22B.FinalTop states them) -/
set_option Elab.async false
@[expose] public section
open FullTable FullTable.WangLadder RootSound Matrix
namespace R22K.Cor
/-- with Laderman's decomposition: the F2-rank is exactly 23 -/
private theorem rankEq23 (h : Top.RankGe23) :
    (∃ (a b c : Fin 23 → M3), IsDecomp a b c) ∧ ∀ (n : ℕ) (a b c : Fin n → M3), IsDecomp a b c → 23 ≤ n :=
  R22B.Cor.rank_eq_23 h
/-- the matrix-product convention (`C = AB`) -/
private theorem mmEquiv (h : Top.RankGe23) : ∀ (n : ℕ) (a b c : Fin n → M3), R22B.Cor.IsDecompMM a b c → 23 ≤ n :=
  R22B.Cor.mm_equiv.mp h
/-- Rudich-Rousseau's table statement at 23 for element 495 -/
private theorem table23 (h : Top.RankGe23) : TableAtLeast ((table[495]!).map mask_matrix) 23 := R22B.Cor.table_23 h
/-- Rudich-Rousseau's crown at 23 -/
private theorem recursive23 (h : Top.RankGe23) : RecursiveAlgorithmMultiplicationsAtLeast 23 := R22B.Cor.recursive_23 h
#k1top R22K.Cor.rank_eq_23 [rankEq23]
#k1top R22K.Cor.mm_equiv [mmEquiv]
#k1top R22K.Cor.table_23 [table23]
#k1top R22K.Cor.recursive_23 [recursive23]
end R22K.Cor
