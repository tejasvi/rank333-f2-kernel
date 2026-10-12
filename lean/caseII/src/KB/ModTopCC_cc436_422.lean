module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.AggCC_cc436_422
public import KMod.Units
public meta import KB.AggCC_cc436_422
public meta import KMod.Units
/-! # KB.ModTopCC_cc436_422: the case-(II) root in `R22B.Final`'s form, on the CC route's table cc436_422

`#kmVII thm A1.cov A2.cov …`: from Cov aggregators (`KB.ModAggCC_cc436_422`'s `#kmAgg` / `#kmAggF`) that export the key of the
case-(II) root `((1, 0), 0)` (the top segment of label 0, R3's `--pctop`), the public theorem
`thm : R22N.Cov KB.CheckedAnyCC_cc436_422 ((1, 0), 0)`, the form of `R22B.Final`'s `vII` (with `rII` the route's contract,
`KB.segRefAllRCC_cc436_422` / `KB.CheckedAnyCC_cc436_422`). The kernel matches the key's root and bound with `((1, 0), 0)`. -/
public meta section
open Lean Elab Command
namespace KBModTopCC

def keysOf (n : Name) : CommandElabM (Array Nat) := do
  let some ci := (← getEnv).find? n | throwError "{n}: not found"
  let l ← match ci.type.getAppFnArgs with
    | (``R22N.AllL, #[_, _, l]) => pure l
    | _ => throwError "{n}: unexpected statement {ci.type}"
  let mut e := l
  let mut acc : Array Nat := #[]
  for _ in [0:10000000] do
    match e.getAppFnArgs with
    | (``List.cons, #[_, .lit (.natVal k), t]) => acc := acc.push k; e := t
    | (``List.nil, _) => return acc
    | _ => throwError "{n}: not a literal key list"
  return acc

def proj (h : Expr) (j : Nat) : Expr := Id.run do
  let mut e := h
  for _ in [0:j] do e := mkProj ``And 1 e
  return mkProj ``And 0 e

elab "#kmVII " t:ident aggs:ident* : command => do
  let mut found : Option Expr := none
  for a in aggs do
    let ks ← keysOf a.getId
    for j in [0:ks.size] do
      let k := ks[j]!
      let S := k % 2 ^ (8 * 64); let last := (k / 2 ^ (8 * 64)) % 2 ^ 16; let klo := (k / 2 ^ (8 * 66)) % 2 ^ 16
      if S == 1 && last == 0 && klo == 0 then found := some (proj (mkConst a.getId) j)
  let some pf := found | throwError "#kmVII: no exported key of the root ((1, 0), 0)"
  let natE := mkConst ``Nat
  let pairT := mkApp2 (mkConst ``Prod [.zero, .zero]) natE natE
  let x := mkApp4 (mkConst ``Prod.mk [.zero, .zero]) pairT natE
    (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) natE natE (mkRawNatLit 1) (mkRawNatLit 0)) (mkRawNatLit 0)
  let stmt := mkApp2 (mkConst ``R22N.Cov) (mkConst ``KB.CheckedAnyCC_cc436_422) x
  KMod.addPub t.getId stmt pf
  logInfo m!"{t.getId}: the case-(II) root ((1, 0), 0) covered (R22B.Final's vII form)"

end KBModTopCC
