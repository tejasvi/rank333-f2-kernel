module
public import S4.SplitQ
public meta import Lean.Elab.Command
public meta import KMod.Units
/-! # S4.PLDrv: `#plsplit Seg "file"`, a split SAT leaf as one module (K1's layout)

FILE: `HDR R Em pts k` (R and Em in hex, pts comma-separated), then one `SUB path cert nbits nsat` line per sub-record in
DFS order (path as `gen7pc --split`: `;`-separated steps `t:sym:cdir:NT:SL:i`, or `-`).

The command adds the PUBLIC definitions `Seg.R` (the leaf record with the main certificate) and `Seg.Em`; PRIVATE definitions
`P_k`, `c_k` and PRIVATE theorems `t_k : PL.subOKL (PL.ltW3 pts k) Seg.R P_k c_k = true` (each its own `addDecl`, so the kernel
checks each sub-record alone and drops its caches); the private main-record theorem
`PL.leafSXL (PL.ltW3 pts k) Seg.R (t.list.map Prod.fst) = true` for the balanced tree `t` of the sub-records; and ONE PUBLIC
theorem `Seg.ok : L479.NoLiftK (S5.leafT Seg.R) (S5.leafN Seg.R) (S6.leafDom6 Seg.R) Seg.Em k` (`PL.noLiftK_of_tree`).
Logs the kernel time of every sub-record and the totals. -/
public meta section
open Lean Elab Command Meta
namespace PL.Drv

def parseList (s : String) : List Nat := if s.isEmpty then [] else (s.splitOn ",").map String.toNat!

def parseStep (s : String) : Nat × Bool × Bool × List Nat × List Nat × Nat :=
  match s.splitOn ":" with
  | [t, sym, cdir, nt, sl, i] => (t.toNat!, sym == "1", cdir == "1", parseList nt, parseList sl, i.toNat!)
  | _ => (0, false, false, [], [], 0)

def parsePath (s : String) : List (Nat × Bool × Bool × List Nat × List Nat × Nat) :=
  if s == "-" then [] else (s.splitOn ";").map parseStep

def hexNat (s : String) : Nat := s.foldl (fun acc ch =>
  acc * 16 + (if ch.isDigit then ch.toNat - '0'.toNat else ch.toNat - 'a'.toNat + 10)) 0

def boolEq (lhs : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
def rflTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- balanced tree over `xs[lo:hi]` (hi > lo): (ST expression, `ok` proof) given `ok`'s parameters -/
partial def tree (ltE RE : Expr) (xs : Array (Expr × Expr × Expr)) (lo hi : Nat) : Expr × Expr :=
  if hi - lo == 1 then
    (mkApp2 (mkConst ``PL.ST.leaf) xs[lo]!.1 xs[lo]!.2.1, xs[lo]!.2.2)
  else
    let mid := lo + (hi - lo) / 2
    let (ta, pa) := tree ltE RE xs lo mid
    let (tb, pb) := tree ltE RE xs mid hi
    (mkApp2 (mkConst ``PL.ST.node) ta tb,
     mkApp4 (mkConst ``And.intro) (mkApp3 (mkConst ``PL.ST.ok) ltE RE ta) (mkApp3 (mkConst ``PL.ST.ok) ltE RE tb) pa pb)

elab "#plsplit " id:ident p:str : command => do
  let t0 ← IO.monoNanosNow
  let lines := (← IO.FS.lines p.getString).toList.filter (fun l => !l.isEmpty)
  let seg := id.getId
  let hdr := (lines.head!.splitOn " ")
  unless hdr.length == 5 && hdr[0]! == "HDR" do throwError "bad header"
  let Rv := hexNat hdr[1]!
  let Emv := hexNat hdr[2]!
  let pts := parseList hdr[3]!
  let k := hdr[4]!.toNat!
  let ptsE := toExpr pts
  let kE := mkRawNatLit k
  let ltE := mkApp2 (mkConst ``PL.ltW3) ptsE kE
  let natT := mkConst ``Nat
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `R, levelParams := [], type := natT, value := mkRawNatLit Rv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  liftCoreM <| addDecl (.defnDecl { name := seg ++ `Em, levelParams := [], type := natT, value := mkRawNatLit Emv, hints := .abbrev, safety := .safe }) (forceExpose := true)
  let RE := mkConst (seg ++ `R)
  let EmE := mkConst (seg ++ `Em)
  let stepTy := toTypeExpr (Nat × Bool × Bool × List Nat × List Nat × Nat)
  let pTy := mkApp (mkConst ``List [Level.zero]) stepTy
  let mut xs : Array (Expr × Expr × Expr) := #[]
  let mut kern : Nat := 0
  let mut times : Array String := #[]
  let mut i : Nat := 0
  for ln in lines.tail! do
    match ln.splitOn " " with
    | ["SUB", path, hx, _nb, ns] =>
      let pn ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ Name.mkSimple s!"P{i}") |> pure
      let cn ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ Name.mkSimple s!"c{i}") |> pure
      liftCoreM <| addDecl (.defnDecl { name := pn, levelParams := [], type := pTy, value := toExpr (parsePath path), hints := .abbrev, safety := .safe })
      liftCoreM <| addDecl (.defnDecl { name := cn, levelParams := [], type := natT, value := mkRawNatLit (hexNat hx), hints := .abbrev, safety := .safe })
      let tn ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ Name.mkSimple s!"t{i}") |> pure
      let stmt := boolEq (mkApp4 (mkConst ``PL.subOKL) ltE RE (mkConst pn) (mkConst cn))
      let k0 ← IO.monoNanosNow
      liftCoreM <| addDecl (.thmDecl { name := tn, levelParams := [], type := stmt, value := rflTrue })
      let dk := (← IO.monoNanosNow) - k0
      kern := kern + dk
      times := times.push s!"{i} {ns} {dk / 1000}"
      xs := xs.push (mkConst pn, mkConst cn, mkConst tn)
      i := i + 1
    | _ => throwError s!"bad line: {ln}"
  if xs.isEmpty then throwError "no sub-records"
  let t1 ← IO.monoNanosNow
  let (t, okp) := tree ltE RE xs 0 xs.size
  -- the main record
  let tmn ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ `tm) |> pure
  let pathsE := mkApp3 (mkConst ``List.map [Level.zero, Level.zero])
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) pTy natT) pTy
    (mkApp2 (mkConst ``Prod.fst [Level.zero, Level.zero]) pTy natT)
  let mstmt := boolEq (mkApp3 (mkConst ``PL.leafSXL) ltE RE (mkApp pathsE (mkApp (mkConst ``PL.ST.list) t)))
  let k1 ← IO.monoNanosNow
  liftCoreM <| addDecl (.thmDecl { name := tmn, levelParams := [], type := mstmt, value := rflTrue })
  let dm := (← IO.monoNanosNow) - k1
  -- the plane facts
  let hn1 ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ `hnd) |> pure
  liftCoreM <| addDecl (.thmDecl { name := hn1, levelParams := [], type := boolEq (mkApp (mkConst ``PL.nodupB) ptsE), value := rflTrue })
  let hp1 ← liftCoreM <| mkPrivateName (← getEnv) (seg ++ `hpts) |> pure
  liftCoreM <| addDecl (.thmDecl { name := hp1, levelParams := [], type := boolEq (mkApp2 (mkConst ``PL.ptsOKB) ptsE EmE), value := rflTrue })
  -- the public theorem
  let ty := mkApp5 (mkConst ``L479.NoLiftK) (mkApp (mkConst ``S5.leafT) RE) (mkApp (mkConst ``S5.leafN) RE)
    (mkApp (mkConst ``S6.leafDom6) RE) EmE kE
  let pf := mkAppN (mkConst ``PL.noLiftK_of_tree) #[ptsE, kE, EmE, mkApp2 (mkConst ``PL.nodupB_spec) ptsE (mkConst hn1),
    mkApp3 (mkConst ``PL.ptsOKB_spec) ptsE EmE (mkConst hp1), RE, t, mkConst tmn, okp]
  KMod.addPub (seg ++ `ok) ty pf
  let t2 ← IO.monoNanosNow
  IO.FS.writeFile (p.getString ++ ".times") (String.intercalate "\n" times.toList ++ "\n")
  logInfo m!"#plsplit {seg}: {xs.size} sub-records; sub-record kernel {kern / 1000000} ms; main {dm / 1000000} ms; public theorem {(t2 - t1) / 1000000} ms; total {(t2 - t0) / 1000000} ms"

end PL.Drv
