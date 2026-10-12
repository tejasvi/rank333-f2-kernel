module
/-! synthetic test vocabulary: a cheap regular checker, to time `#kdispatch` + `forallLt` at scale -/
@[expose] public section
namespace KModT
def chkS (x : Nat) : Bool := Nat.ble 1 x
end KModT
