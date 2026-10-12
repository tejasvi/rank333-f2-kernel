module
public import R22Port.U_d41d8cd98f00
public import KB.Defs
public import KDK.ItemR
/-! # KB.DefsR: the kernel track's item predicate with range segments (definitions only)

* `ExtR := ExtD × ℕ`: the case-(II) extension datum and the record's range start (`511`: no range reference);
  `extIIR` / `accIIR` / `xkIIR` are `extII` / `accII` / `xkII` on the first component, `rgIIR` the second.
* **`CheckedR`**: an accepted job table, the root's parent frame (`rootChk0`), a chain of accepted batches of `KD.itemXR'` from
  `[(f0, pend0)]` with `pend0 = 2^l0` to a stack without pending labels, every range of the list above the root's bound
  (`lo < l`), and the key's interface: root `(f0.1 ||| 2^l0, l0)`, `lo`, the ranges `rngL` and the external children `extL`. -/
@[expose] public section
set_option maxHeartbeats 4000000
noncomputable section
namespace KB
open R3RT.SpecO KD

/-- the extension datum with the record's range start (`511`: none) -/
abbrev ExtR := ExtD × ℕ

def extIIR (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (tab : ℕ → ℕ) (S D N U d last : ℕ) (e : ExtR) : Bool :=
  extII np c2T hkT cpT tab S D N U d last e.1
def accIIR (e : ExtR) : ℕ := accII e.1
def xkIIR (e : ExtR) : ℕ := xkII e.1
def rgIIR (e : ExtR) : ℕ := e.2

/-- **the item predicate of the kernel track with ranges** -/
def CheckedR {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ)
    (ext : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk rg : E → ℕ) (c1 : ℕ) (TabV : (ℕ → ℕ) → Prop) (key : ℕ) :
    Prop :=
  ∃ (tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (l0 pend0 lo : ℕ) (extL : List (ℕ × ℕ))
    (rngL : List ((ℕ × ℕ) × ℕ)) (out : List FrP),
    TabV tab ∧ rootChk0 c1 c2T hkT tab pl W lastP f0 = true ∧ Nat.beq pend0 (Nat.shiftLeft 1 l0) = true ∧
    ChainR np c2T hkT cpT extL lo rngL (ext tab) acc xk rg tab [(f0, pend0)] out ∧ pendZ out = true ∧
    allB (fun p => Nat.blt lo p.2) rngL = true ∧
    (R22N.SegI.ofKey key).root = (f0.1 ||| 2 ^ l0, l0) ∧ (R22N.SegI.ofKey key).lo = lo ∧
    (R22N.SegI.ofKey key).rng = rngL ∧ (R22N.SegI.ofKey key).ext = extL

end KB
