module
public import R22Port.U_d41d8cd98f00
public import G2.C321X_W
public import E1.AsmN
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! # The length of the chain `C321X`, for the recursor-walk block modules (`E1/AsmN.lean`) -/
namespace G2.C321X
open E1S
theorem lenT : 146626 = lits.length := len_of_lenR lits 146626 (by decide +kernel)
end G2.C321X
