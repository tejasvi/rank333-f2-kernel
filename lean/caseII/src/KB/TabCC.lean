module
public import R22Port.U_d41d8cd98f00
public meta import Lean
public import KB.StatR
public import KB.CCDefs
public import KB.LoadItem
public meta import KB.LoadItem
/-! # KB.TabCC: the CC route's label tables and their binding to `KCC.rowECC L` (commands)

* `#kccstat N "c:R,…" "file.c2t"`: `N.L` (the cap list), `N.c2t_<l>` (label `l`'s cap-2 table from the file, py/mkcc.py's
  layout), the dispatcher `N.c2T`, and `N.c1` (the cap-1 table, slot 511). The hit vectors, window constants and the diagonal
  mask are case (II)'s (`KI.hkT`, `KI.cpT`, `KI.DC`): they do not depend on the kept rows.
* `#kccbind N q "file"`: `N.rows_<q>` and the kernel check `N.bq_<q> : R3RT.bindQ (KCC.rowECC N.L) q 2 N.rows_<q> (N.c2T q) KI.DC =
  true` (`q = 511`: cap 1 and `N.c1`), from py/mkcc.py's `bind/q<q>.bin` (`bind/c1.bin`).
* `#kccbindAll N`: `N.bindRows` and `N.c2_all : KB.AllBelow (fun q => bindQ … q 2 (N.bindRows q) (N.c2T q) KI.DC = true) 511`. -/
@[expose] public section
open Lean Elab Command L1Load KBLoad
namespace KBCC

meta def lpE (L : List (Nat × Nat)) : Expr :=
  mkList (prodTy natTy natTy) (L.map fun (c, r) => mkPair natTy natTy (mkRawNatLit c) (mkRawNatLit r))
meta def ccTab (N : Name) (l : Nat) : Name := N ++ Name.mkSimple s!"c2t_{l}"
meta def ccRows (N : Name) (q : Nat) : Name := N ++ Name.mkSimple s!"rows_{q}"
meta def ccBq (N : Name) (q : Nat) : Name := N ++ Name.mkSimple s!"bq_{q}"
meta def rowECCE (N : Name) : Expr := mkApp (mkConst ``KCC.rowECC) (mkConst (N ++ `L))

elab "#kccstat " id:ident ls:str p:str : command => do
  let N := id.getId
  let L := ((ls.getString.splitOn ",").filter (· ≠ "")).map fun s =>
    match s.splitOn ":" with | [a, b] => (a.toNat!, b.toNat!) | _ => (0, 0)
  liftCoreM <| defT (N ++ `L) (mkApp (mkConst ``List [Level.zero]) (prodTy natTy natTy)) (lpE L)
  let b ← IO.FS.readBinFile p.getString
  if b.size != 512 * 511 * 64 then throwError "kccstat: {p.getString} has {b.size} bytes"
  for l in [0:511] do
    liftCoreM <| defT (ccTab N l) natTy (mkRawNatLit (natLE b (l * 511 * 64) ((l + 1) * 511 * 64)))
  let fnTy := mkForall `l BinderInfo.default natTy natTy
  liftCoreM <| defT (N ++ `c2T) fnTy (dispatch natTy fun l => if l < 511 then mkConst (ccTab N l) else mkRawNatLit 0)
  liftCoreM <| defT (N ++ `c1) natTy (mkRawNatLit (natLE b (511 * 511 * 64) (512 * 511 * 64)))
  logInfo m!"{N}: cap list {L}, 511 cap-2 tables and the cap-1 table from {p.getString}"

meta def bindQCC (N : Name) (q : Nat) (rows : Expr) : Expr :=
  let cap := if q < 511 then 2 else 1
  let stored := if q < 511 then mkApp (mkConst (N ++ `c2T)) (mkRawNatLit q) else mkConst (N ++ `c1)
  eqTrue (mkAppN (mkConst ``R3RT.bindQ) #[rowECCE N, mkRawNatLit q, mkRawNatLit cap, rows, stored, mkConst `KI.DC])

elab "#kccbind " id:ident qn:num p:str : command => do
  let N := id.getId; let q := qn.getNat
  let it := KDLoadXB.itemsF (← IO.FS.readBinFile p.getString)
  let n := it[0]!
  let mut rs : Array Expr := #[]
  let mut o := 1
  for _ in [0:n] do
    let id := it[o]!; let k := it[o+1]!
    rs := rs.push (mkPair natTy lnatE (mkRawNatLit id) (mlE ((List.range k).map fun j => it[o+2+j]!)))
    o := o + 2 + k
  liftCoreM <| defT (ccRows N q) rowsTy (mkList (prodTy natTy lnatE) rs.toList)
  let w ← thm (ccBq N q) (bindQCC N q (mkConst (ccRows N q))) rflTrue s!"{N}.bq_{q}"
  logInfo m!"{N}.bq_{q}: {n} rows, kernel {w} ms"

elab "#kccbindAll " id:ident : command => do
  let N := id.getId
  liftCoreM <| defT (N ++ `bindRows) (mkForall `q BinderInfo.default natTy rowsTy)
    (dispatch rowsTy fun q => if q < 511 then mkConst (ccRows N q) else mkList (prodTy natTy lnatE) [])
  let P := mkLambda `q BinderInfo.default natTy (eqTrue (mkAppN (mkConst ``R3RT.bindQ) #[rowECCE N, mkBVar 0,
    mkRawNatLit 2, mkApp (mkConst (N ++ `bindRows)) (mkBVar 0), mkApp (mkConst (N ++ `c2T)) (mkBVar 0), mkConst `KI.DC]))
  let allB (k : Nat) : Expr := mkApp2 (mkConst ``KB.AllBelow) P (mkRawNatLit k)
  let mut pf := mkConst ``True.intro
  for k in [0:511] do
    pf := mkApp4 (mkConst ``And.intro) (allB k) (mkApp P (mkRawNatLit k)) pf (mkConst (ccBq N k))
  let w ← thm (N ++ `c2_all) (allB 511) pf s!"{N}.c2_all"
  logInfo m!"{N}.c2_all: kernel {w} ms"

end KBCC
