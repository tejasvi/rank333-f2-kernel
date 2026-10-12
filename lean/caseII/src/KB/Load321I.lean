module
public import R22Port.U_6050cb77ad13
public meta import Lean
public import Lean
public import KB.LoadItem
public import R22D.T321
public meta import KB.LoadItem
public meta import R22D.T321
/-! # KB.Load321I: `#kdstat321`, the label tables of the `--rord 321` item checker (cases (I) / (I13))

`KI321.c2T l = R22D.T321.c2t_<l>` (cap-2 tables of `C3eD_321.c2t`) and `KI321.hkT l = R22D.T321.h_<l>` (hit vectors of
`hyp7_321.bin`) as balanced `Bool.rec` dispatchers over the bits of `l` (`KBLoad.dispatch`, as `#kdstatII`); 0 at `l = 511`.
The cap-1 table is `R22D.T321.CONF1T` and the window constants are `KI.cpT` (order-free). -/
public meta section
open Lean Elab Command L1Load
namespace KBLoad321I

def nm (k : String) (l : Nat) : Name := Name.mkStr (Name.mkStr `R22D "T321") s!"{k}_{l}"

elab "#kdstat321" : command => do
  let fnTy := mkForall `l BinderInfo.default natTy natTy
  liftCoreM <| KBLoad.defT `KI321.c2T fnTy (KBLoad.dispatch natTy fun l => if l < 511 then mkConst (nm "c2t" l) else mkRawNatLit 0)
  liftCoreM <| KBLoad.defT `KI321.hkT fnTy (KBLoad.dispatch natTy fun l => if l < 511 then mkConst (nm "h" l) else mkRawNatLit 0)

end KBLoad321I
