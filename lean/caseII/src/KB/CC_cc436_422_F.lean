module
public import R22Port.U_d41d8cd98f00
public import KB.StatFactsR
public import KB.CC_cc436_422_B00
public import KB.CC_cc436_422_B01
public import KB.CC_cc436_422_B02
public import KB.CC_cc436_422_B03
public import KB.CC_cc436_422_B04
public import KB.CC_cc436_422_B05
public import KB.CC_cc436_422_B06
public import KB.CC_cc436_422_B07
public import KB.CC_cc436_422_B08
public import KB.CC_cc436_422_B09
public import KB.CC_cc436_422_B10
public import KB.CC_cc436_422_B11
public import KB.CC_cc436_422_B12
public import KB.CC_cc436_422_B13
public import KB.CC_cc436_422_B14
public import KB.CC_cc436_422_B15
public import KB.CC_cc436_422_Bc1
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000000
#kccbindAll KCC_cc436_422
noncomputable section
namespace KB
open R3RT.SpecO KD
/-- the cap list `436:19,422:19` meets `KB.segRefRCC`'s side conditions -/
theorem capL_cc436_422 : (∀ p ∈ KCC_cc436_422.L, _root_.RT.cLB _root_.RT.K3eD_Cls.CL p.1 ≤ p.2 + 1) ∧ (∀ p ∈ KCC_cc436_422.L, p.1 < 496) :=
  capL_of_all _ (by decide +kernel)
theorem hc2_cc436_422 : HCC KCC_cc436_422.L → ∀ l, l < 511 → KD.C2OKU (CaseK 14 22) l (KCC_cc436_422.c2T l) := fun hH l hl =>
  (c2_of_bindCC KCC_cc436_422.L capL_cc436_422.1 capL_cc436_422.2 l (KCC_cc436_422.bindRows l) (KCC_cc436_422.c2T l) KI.DC hH.1).1 hl (allBelow_spec KCC_cc436_422.c2_all l hl)
theorem hc1_cc436_422 : HCC KCC_cc436_422.L → Conf1OK LO123 (CaseK 14 22) KCC_cc436_422.c1 := fun hH =>
  (c2_of_bindCC KCC_cc436_422.L capL_cc436_422.1 capL_cc436_422.2 511 KCC_cc436_422.rows_511 KCC_cc436_422.c1 KI.DC hH.1).2 KCC_cc436_422.bq_511
abbrev CheckedRCC_cc436_422 := CheckedR R3RT.nperpL KCC_cc436_422.c2T KI.hkT KI.cpT (fun tab => extIIR R3RT.nperpL KCC_cc436_422.c2T KI.hkT KI.cpT tab) accIIR
  xkIIR rgIIR KCC_cc436_422.c1 (TabVCC KCC_cc436_422.L)
abbrev CheckedDeadCC_cc436_422 := CheckedDeadK R3RT.nperpL KCC_cc436_422.c2T KI.hkT KI.cpT KCC_cc436_422.c1 (TabVCC KCC_cc436_422.L)
/-- **case (II) on the CC route `436:19,422:19`**: every accepted item (OPEN root with ranges, or dead root) is a certified segment with its key's interface -/
theorem segRefAllRCC_cc436_422 : SegRefHK (HCC KCC_cc436_422.L) LO123 (CaseK 14 22) (fun k => CheckedRCC_cc436_422 k ∨ CheckedDeadCC_cc436_422 k) :=
  fun k h => h.elim (segRefRCC KCC_cc436_422.L capL_cc436_422.1 capL_cc436_422.2 hhII hcpII hc1_cc436_422 hc2_cc436_422 k)
    (segRefDeadCC KCC_cc436_422.L capL_cc436_422.1 capL_cc436_422.2 hhII hcpII hc1_cc436_422 hc2_cc436_422 k)
end KB
#print axioms KB.segRefAllRCC_cc436_422
