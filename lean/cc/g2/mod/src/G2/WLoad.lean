module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import Lean
public import RT.Load
/-! # G2.WLoad: a chain's glue witness table from a binary file (no list-literal elaboration)

`#g2w Pfx "file"`: the file holds `u32 count`, then per row `u32 len` and `len` entries `u32`. Defines
`Pfx.W : List (List Nat)` (the rows in file order, entries as raw literals), by one `addDecl` (`RTLoad.defN`), checked by the
kernel as usual. This replaces leaf2's `def W : List (List Nat) := [[…], …]` literal (E1/<chain>_W.lean), whose elaboration
does not finish in reasonable time for the 182,520-row table of class 303; the value is the same list. -/
@[expose] public section
open Lean Elab Command

namespace G2WLoad

meta def u32 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + 256 * (b.get! (i + 1)).toNat + 65536 * (b.get! (i + 2)).toNat + 16777216 * (b.get! (i + 3)).toNat

meta def g2w (pfx : Name) (path : String) : CommandElabM Unit := do
  let b ← IO.FS.readBinFile path
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
  let mut w : Expr := mkApp (mkConst ``List.nil [Level.zero]) rowTy
  for r in rows.reverse do
    w := mkApp3 (mkConst ``List.cons [Level.zero]) rowTy r w
  liftCoreM <| RTLoad.defN (pfx ++ `W) (mkApp (mkConst ``List [Level.zero]) rowTy) w
  logInfo m!"#g2w {pfx}: {cnt} rows"

elab "#g2w " pfx:ident p:str : command => g2w pfx.getId p.getString

end G2WLoad
