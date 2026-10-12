module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import Lean
public import RT.Load
/-! # G2.Disp: O(log n) dispatchers over a chain's blocks and witness rows (for G2.Asm2)

* `#g2f Pfx N`: `Pfx.F : ℕ → ℕ` with `Pfx.F k = Pfx.L<k>` for `k < N` (the block literals of `#e1lits Pfx`) and `0` above, as
  a binary dispatch: `Pfx.FD<l>_<i>` chooses by bit `l-1` of `k` between its two children (`RTLoad.bitE`), one `Bool.rec` per
  level, so `Pfx.F k` reduces in `log₂ N` steps.
* `#g2fw Pfx "file"`: `Pfx.FW : ℕ → List ℕ`, the witness rows of the file (as G2.WLoad's `#g2w`) at the leaves, `[]` above.
Every definition is checked by the kernel as usual (one `addDecl` each). -/
@[expose] public section
open Lean Elab Command

namespace G2Disp

meta def u32 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + 256 * (b.get! (i + 1)).toNat + 65536 * (b.get! (i + 2)).toNat + 16777216 * (b.get! (i + 3)).toNat

/-- the dispatch tree over `n` leaves (`leaf c` for leaf `c < n`, `dflt` above): definitions `pfx.<tag><l>_<i>`, root returned -/
meta def disp (pfx : Name) (tag : String) (ty : Expr) (n : Nat) (leaf : Nat → Expr) (dflt : Expr) : CommandElabM Name := do
  let natTy := mkConst ``Nat
  let fnTy := mkForall `k BinderInfo.default natTy ty
  let dep := Nat.max 1 (Nat.log2 (n - 1) + 1)
  for lvl in [1:dep + 1] do
    let cnt := (n + 2 ^ lvl - 1) / 2 ^ lvl
    for idx in [0:cnt] do
      let kv := mkBVar 0
      let child (c : Nat) : Expr :=
        if lvl == 1 then (if c < n then leaf c else dflt)
        else (if c * 2 ^ (lvl - 1) < n then mkApp (mkConst (pfx ++ Name.mkSimple s!"{tag}{lvl-1}_{c}")) kv else dflt)
      let body := mkApp4 (mkConst ``Bool.rec [Level.one]) (mkLambda `_ BinderInfo.default (mkConst ``Bool) ty)
        (child (2 * idx)) (child (2 * idx + 1)) (RTLoad.bitE kv (lvl - 1))
      liftCoreM <| RTLoad.defN (pfx ++ Name.mkSimple s!"{tag}{lvl}_{idx}") fnTy (mkLambda `k BinderInfo.default natTy body)
  return pfx ++ Name.mkSimple s!"{tag}{dep}_0"

elab "#g2f " pfx:ident n:num : command => do
  let p := pfx.getId
  let natTy := mkConst ``Nat
  let root ← disp p "FD" natTy n.getNat (fun c => mkConst (p ++ Name.mkSimple s!"L{c}")) (mkRawNatLit 0)
  liftCoreM <| RTLoad.defN (p ++ `F) (mkForall `k BinderInfo.default natTy natTy)
    (mkLambda `k BinderInfo.default natTy (mkApp (mkConst root) (mkBVar 0)))
  logInfo m!"#g2f {p}: {n.getNat} leaves"

elab "#g2fw " pfx:ident path:str : command => do
  let p := pfx.getId
  let b ← IO.FS.readBinFile path.getString
  let cnt := u32 b 0
  let natTy := mkConst ``Nat
  let rowTy := mkApp (mkConst ``List [Level.zero]) natTy
  let mut off := 4
  let mut rows : Array Expr := #[]
  for _ in [0:cnt] do
    let len := u32 b off
    off := off + 4
    let mut es : Array Nat := #[]
    for j in [0:len] do
      es := es.push (u32 b (off + 4 * j))
    off := off + 4 * len
    let mut r : Expr := mkApp (mkConst ``List.nil [Level.zero]) natTy
    for v in es.reverse do
      r := mkApp3 (mkConst ``List.cons [Level.zero]) natTy (mkRawNatLit v) r
    rows := rows.push r
  let root ← disp p "FWD" rowTy cnt (fun c => rows[c]!) (mkApp (mkConst ``List.nil [Level.zero]) natTy)
  liftCoreM <| RTLoad.defN (p ++ `FW) (mkForall `k BinderInfo.default natTy rowTy)
    (mkLambda `k BinderInfo.default natTy (mkApp (mkConst root) (mkBVar 0)))
  logInfo m!"#g2fw {p}: {cnt} rows"

end G2Disp
