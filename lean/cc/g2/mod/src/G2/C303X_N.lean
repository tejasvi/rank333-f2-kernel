module
public import R22Port.U_d41d8cd98f00
public import G2.C303X_W
public import E1.AsmN
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! # The length of the chain `C303X`, for the recursor-walk block modules (`E1/AsmN.lean`) -/
namespace G2.C303X
open E1S
theorem lenT : 182520 = lits.length := len_of_lenR lits 182520 (by decide +kernel)
end G2.C303X
