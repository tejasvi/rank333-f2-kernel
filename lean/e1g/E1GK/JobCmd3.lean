module
public meta import Lean
public import E1GK.ChainF
public import E1GK.ExtMono
public import RT.Load
public meta import KMod.Units
/-! # `#e1gjob` (E1GK.JobCmd3: E1GK.JobCmd2 with every `NS.EXT` a literal list, so that an importer can evaluate it): an E1G job module, built as terms (module form)

`#e1gjob NS "blocks.bin" "of.bin" "wt.bin" "units.txt" IP SL OK` adds, every declaration through `addDecl` (checked by the
kernel only; set `Elab.async false`), with private names (`mkPrivateName`) except the last:
* the job's block literals `L<i>`, the glue witness tables (`OF`, `WT`: 32-bit entries, the `#rttablew` layout), `n`, `Jf`,
  `Wf i j`, and `Lf i`: a balanced dispatch over the literals as one small definition per level;
* the units `u<k>`, one per line of `units.txt` (block indices): `(E1G.block C sl UB UBR L_a && …) = true` by evaluation;
* the glue ranges `g<a>`: `glueRange n Lf 0 Jf Wf a m = true` (256 blocks each) by evaluation;
* `r<a>`: `RangeOK P a m` from the units (packed units split by `Bool.and_eq_true`), joined in balanced trees, and the
  private chain theorem `jobL : JobOK C sl UB (Lf 0)` (`jobOK_of_chain_fn`);
* public: `NS.job : JobOK C sl UB H` with `H` the job's header numeral (a job root, mode 0: `S % 2 ^ (13 + 7 d)` by `jobOK_hdr0`; mode 1: `S % 2 ^ 611`): the only constant an
  importer sees.
`IP.C`, `SL.chunk`, `IP.UB`, `IP.UBR`, `OK.UB_eq`, `OK.UBR_eq`, `OK.UB_le` come from the context's IP modules.

**External leaves** (certificate 0, accepted by `E1G.leafOK` through `C.EXT`): a job line may end with `X=p1,p2,…` (the packed
prefixes `Σ l_i 2^(7 i)` of its external leaves), and an `@THM` line may name a lifted theorem.  A module with any of them
defines the public list `NS.EXT` (the jobs' lists and the lifted children's lists, in order, as one literal list: the
children's lists are evaluated at build time, so an importer that does not load them can still evaluate `NS.EXT`),
checks its chains against `withExt IP.C NS.EXT`, and exports the lifted form
`∀ E, ExtSub NS.EXT E → RangeOK (fun k => JobOK (withExt IP.C E) sl UB (TBL.entry k)) a m` (`E1GK.ExtMono`); aggregators and
tops over lifted children are lifted the same way.  Modules without external leaves are unchanged (over `IP.C`). -/
@[expose] public section
open Lean Elab Command Meta

namespace E1GJob3

meta def natTy : Expr := mkConst ``Nat
meta def boolTy : Expr := mkConst ``Bool
meta def tru : Expr := mkConst ``Bool.true
meta def eqTrue (b : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) boolTy b tru
meta def timing : IO Bool := return (← IO.getEnv "E1GJOB_TIMES").isSome
meta def addThm (n : Name) (ty val : Expr) : CoreM Nat := do
  let t0 ← IO.monoNanosNow
  KMod.addDeclSync (Declaration.thmDecl { name := n, levelParams := [], type := ty, value := val })
  let t1 ← IO.monoNanosNow
  if ← timing then IO.eprintln s!"  {n}: {(t1 - t0) / 1000000} ms"
  return t1 - t0
/-- per-group kernel statistics for the KMod manifest: (units, sum ns, max ns, slowest index) -/
structure GStat where
  units : Nat := 0
  sum : Nat := 0
  mx : Nat := 0
  slow : Nat := 0
meta def GStat.add (g : GStat) (i t : Nat) : GStat :=
  { units := g.units + 1, sum := g.sum + t, mx := max g.mx t, slow := if t > g.mx then i else g.slow }
/-- the KMod `KUNITS` manifest line of a group -/
meta def kunits (grp : String) (lits arity : Nat) (g : GStat) (path : String) : CommandElabM Unit := do
  let bytes ← IO.FS.readBinFile path
  logInfo m!"KUNITS {grp} lits={lits} arity={arity} units={g.units} kernel_ms={g.sum / 1000000} max_unit_ms={g.mx / 1000000} slowest={g.slow} data={path} bytes={bytes.size} hash={hash bytes}"
meta def klits (grp : String) (path : String) : CommandElabM Unit := do
  let bytes ← IO.FS.readBinFile path
  logInfo m!"KLITS {grp} lits={KMod.u32 bytes 0} data={path} bytes={bytes.size} hash={hash bytes}"
/-- a private (unexported) definition, abbrev hints -/
meta def defP (n : Name) (ty v : Expr) : CoreM Unit := do
  let dv : DefinitionVal := { name := n, levelParams := [], type := ty, value := v, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv)
meta def decideProof (b : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) (eqTrue b) (mkApp2 (mkConst ``instDecidableEqBool) b tru)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) boolTy tru)
meta def u32 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + 256 * (b.get! (i + 1)).toNat + 65536 * (b.get! (i + 2)).toNat + 16777216 * (b.get! (i + 3)).toNat
/-- the literals of an `#e1lits` file, as private definitions `pfx.L<i>`; returns their count and the values -/
meta def litsP (pfx : Name) (path : String) : CoreM (Array Nat) := do
  let b ← IO.FS.readBinFile path
  let cnt := u32 b 0
  let mut off := 4
  let mut vs : Array Nat := #[]
  for i in [0:cnt] do
    let nb := u32 b off
    off := off + 4
    let v := RTLoad.natLE b off (off + nb)
    off := off + nb
    defP (pfx ++ Name.mkSimple s!"L{i}") natTy (mkRawNatLit v)
    vs := vs.push v
  return vs
/-- a table of 32-bit entries (`#rttablew … 64 32` layout) as private definitions: chunks, per-level dispatch, `entry` -/
meta def tableP (pf : Name) (path : String) : CoreM Unit := do
  let b ← IO.FS.readBinFile path
  let ch := 64; let wb := 32; let wB := 4
  let n := b.size / wB
  let nch := (n + ch - 1) / ch
  for k in [0:nch] do
    defP (pf ++ Name.mkSimple s!"C{k}") natTy (mkRawNatLit (RTLoad.natLE b (wB * ch * k) (min b.size (wB * ch * (k + 1)))))
  let dep := Nat.max 1 (Nat.log2 (nch - 1) + 1)
  let fnTy := mkForall `k BinderInfo.default natTy natTy
  for lvl in [1:dep + 1] do
    let cnt := (nch + 2 ^ lvl - 1) / 2 ^ lvl
    for idx in [0:cnt] do
      let kv := mkBVar 0
      let child (c : Nat) : Expr :=
        if lvl == 1 then (if c < nch then mkConst (pf ++ Name.mkSimple s!"C{c}") else mkRawNatLit 0)
        else (if c * 2 ^ (lvl - 1) < nch then mkApp (mkConst (pf ++ Name.mkSimple s!"D{lvl-1}_{c}")) kv else mkRawNatLit 0)
      let body := mkApp4 (mkConst ``Bool.rec [Level.one]) (mkLambda `_ BinderInfo.default (mkConst ``Bool) natTy)
        (child (2 * idx)) (child (2 * idx + 1)) (RTLoad.bitE kv (lvl - 1))
      defP (pf ++ Name.mkSimple s!"D{lvl}_{idx}") fnTy (mkLambda `k BinderInfo.default natTy body)
  defP (pf ++ `chunk) fnTy (mkLambda `k BinderInfo.default natTy (mkApp (mkConst (pf ++ Name.mkSimple s!"D{dep}_0")) (mkBVar 0)))
  let iv := mkBVar 0
  let ent := mkApp2 (mkConst ``Nat.land)
    (mkApp2 (mkConst ``Nat.shiftRight) (mkApp (mkConst (pf ++ `chunk)) (mkApp2 (mkConst ``Nat.div) iv (mkRawNatLit ch)))
      (mkApp2 (mkConst ``Nat.mul) (mkRawNatLit wb) (mkApp2 (mkConst ``Nat.mod) iv (mkRawNatLit ch))))
    (mkRawNatLit (2 ^ wb - 1))
  defP (pf ++ `entry) fnTy (mkLambda `i BinderInfo.default natTy ent)
/-- balanced dispatch over `lit a .. lit (a + m - 1)`, one private definition per level -/
meta partial def mkDisp (ns : Name) (lit : Nat → Expr) (a m : Nat) : CoreM (Expr → Expr) := do
  if m ≤ 1 then return fun _ => lit a
  let h := m / 2
  let lo ← mkDisp ns lit a h
  let hi ← mkDisp ns lit (a + h) (m - h)
  let nm := ns ++ Name.mkSimple s!"D_{a}_{m}"
  let body := mkApp4 (mkConst ``cond [Level.one]) natTy (mkApp2 (mkConst ``Nat.blt) (mkBVar 0) (mkRawNatLit (a + h)))
    (lo (mkBVar 0)) (hi (mkBVar 0))
  defP nm (mkForall `i BinderInfo.default natTy natTy) (mkLambda `i BinderInfo.default natTy body)
  return fun iv => mkApp (mkConst nm) iv

/-- the chain of one block file: private literals `pv.B.L<i>`, tables, `Lf`, `Wf`, units, glue ranges and RangeOK trees, with
the jobs `nJ`, `JfE` (`fun _ => 0` when `nJ = 0`); returns the values of the literals and the terms `hblk`, `hglue` of
`jobOK_of_chain_fn` -/
meta def chainCore (ns pv : Name) (pb po pw pu : String) (ip sl : Name) (cE : Expr) (nJ : Nat) (JfE? : Option Expr) :
    CommandElabM (Array Nat × Expr × Expr) := do
  let mut sN : GStat := {}; let mut sL : GStat := {}; let mut sG : GStat := {}; let mut sR : GStat := {}
  let mut arityL := 1
  let vs ← liftCoreM <| litsP (pv ++ `B) pb
  liftCoreM <| tableP (pv ++ `OF) po
  liftCoreM <| tableP (pv ++ `WT) pw
  let units : Array (Array Nat) := ((← IO.FS.lines pu).filter (· ≠ "")).map fun l =>
    (l.splitOn " " |>.filter (· ≠ "") |>.map String.toNat!).toArray
  let n : Nat := units.foldl (fun acc u => acc + u.size) 0
  if n != vs.size then throwError "#e1gjob: units cover {n} blocks, the file has {vs.size}"
  let lit (k : Nat) : Expr := mkConst (pv ++ `B ++ Name.mkSimple s!"L{k}")
  let fnTy := mkForall `i BinderInfo.default natTy natTy
  liftCoreM <| defP (pv ++ `n) natTy (mkRawNatLit n)
  let disp ← liftCoreM <| mkDisp (pv ++ `Lf) lit 0 n
  liftCoreM <| defP (pv ++ `Lf) fnTy (mkLambda `i BinderInfo.default natTy (disp (mkBVar 0)))
  let wfTy := mkForall `i BinderInfo.default natTy (mkForall `j BinderInfo.default natTy natTy)
  liftCoreM <| defP (pv ++ `Wf) wfTy (mkLambda `i BinderInfo.default natTy (mkLambda `j BinderInfo.default natTy
    (mkApp (mkConst (pv ++ `WT ++ `entry)) (mkApp2 (mkConst ``Nat.add) (mkApp (mkConst (pv ++ `OF ++ `entry)) (mkBVar 1)) (mkBVar 0)))))
  match JfE? with
  | some e => liftCoreM <| defP (pv ++ `Jf) fnTy e
  | none => liftCoreM <| defP (pv ++ `Jf) fnTy (mkLambda `i BinderInfo.default natTy (mkRawNatLit 0))
  let C := cE; let slE := mkApp (mkConst ``E1G.slc) (mkConst (sl ++ `chunk))
  let UB := mkConst (ip ++ `UB); let UBR := mkConst (ip ++ `UBR)
  let blk (L : Expr) : Expr := mkAppN (mkConst ``E1G.block) #[C, slE, UB, UBR, L]
  let LfE := mkConst (pv ++ `Lf); let nE := mkConst (pv ++ `n); let WfE := mkConst (pv ++ `Wf); let JfE := mkConst (pv ++ `Jf)
  let P := mkLambda `i BinderInfo.default natTy (eqTrue (blk (mkApp LfE (mkBVar 0))))
  let mut pf : Array Expr := Array.replicate n (mkConst ``True.intro)
  for ui in [0:units.size] do
    let ks := units[ui]!
    let bs := ks.map (fun k => blk (lit k))
    let b := (bs.extract 1 bs.size).foldl (fun acc x => mkApp2 (mkConst ``Bool.and) acc x) bs[0]!
    let un := pv ++ Name.mkSimple s!"u{ui}"
    let tu ← liftCoreM <| addThm un (eqTrue b) (decideProof b)
    if ks.size == 1 then sN := sN.add ui tu else { sL := sL.add ui tu; arityL := max arityL ks.size }
    let mut T : Array Expr := #[bs[0]!]
    for r in [1:bs.size] do T := T.push (mkApp2 (mkConst ``Bool.and) T[r-1]! bs[r]!)
    let split (r : Nat) (h : Expr) : Expr :=
      mkApp4 (mkConst ``Eq.mp [Level.zero]) (eqTrue T[r]!) (mkApp2 (mkConst ``And) (eqTrue T[r-1]!) (eqTrue bs[r]!))
        (mkApp2 (mkConst ``Bool.and_eq_true) T[r-1]! bs[r]!) h
    for t in [0:ks.size] do
      let mut h := mkConst un
      let mut r := ks.size - 1
      while r > t do
        h := mkApp3 (mkConst ``And.left) (eqTrue T[r-1]!) (eqTrue bs[r]!) (split r h)
        r := r - 1
      let p := if t == 0 then h else mkApp3 (mkConst ``And.right) (eqTrue T[t-1]!) (eqTrue bs[t]!) (split t h)
      pf := pf.set! ks[t]! p
  let GB := 256
  let G := mkLambda `i BinderInfo.default natTy (eqTrue (mkAppN (mkConst ``E1GS.glueRowW) #[nE, LfE, mkRawNatLit nJ, JfE, WfE, mkBVar 0]))
  let rangeTy (Q : Expr) (a m : Nat) : Expr := mkAppN (mkConst ``E1GS.RangeOK) #[Q, mkRawNatLit a, mkRawNatLit m]
  let rec tree (Q : Expr) (leaf : Nat → Expr) (lo cnt : Nat) (step : Nat) (sizeOf : Nat → Nat) : Expr :=
    if cnt ≤ 1 then leaf lo else
    let h := cnt / 2
    let a := lo * step; let m1 := (List.range h).foldl (fun s t => s + sizeOf (lo + t)) 0
    let m2 := (List.range (cnt - h)).foldl (fun s t => s + sizeOf (lo + h + t)) 0
    mkAppN (mkConst ``E1GS.range_join) #[Q, mkRawNatLit a, mkRawNatLit m1, mkRawNatLit m2,
      tree Q leaf lo h step sizeOf, tree Q leaf (lo + h) (cnt - h) step sizeOf]
  let nch := (n + GB - 1) / GB
  let csize (c : Nat) : Nat := min GB (n - c * GB)
  for c in [0:nch] do
    let a := c * GB; let m := csize c
    let bt := tree P (fun k => mkAppN (mkConst ``E1GS.range_one) #[P, mkRawNatLit k, pf[k]!]) a m 1 (fun _ => 1)
    let tr ← liftCoreM <| addThm (pv ++ Name.mkSimple s!"r{a}") (rangeTy P a m) bt
    sR := sR.add c tr
    let gb := mkAppN (mkConst ``E1GS.glueRange) #[nE, LfE, mkRawNatLit nJ, JfE, WfE, mkRawNatLit a, mkRawNatLit m]
    let tg ← liftCoreM <| addThm (pv ++ Name.mkSimple s!"g{a}") (eqTrue gb) (decideProof gb)
    sG := sG.add c tg
  let topB := tree P (fun c => mkConst (pv ++ Name.mkSimple s!"r{c * GB}")) 0 nch GB csize
  let t1 ← liftCoreM <| addThm (pv ++ `hblkR) (rangeTy P 0 n) topB
  let topG := tree G (fun c => mkAppN (mkConst ``E1GS.glueRange_spec)
      #[nE, LfE, mkRawNatLit nJ, JfE, WfE, mkRawNatLit (c * GB), mkRawNatLit (csize c), mkConst (pv ++ Name.mkSimple s!"g{c * GB}")])
    0 nch GB csize
  let t2 ← liftCoreM <| addThm (pv ++ `hglR) (rangeTy G 0 n) topG
  sR := sR.add nch (t1 + t2)
  let gn := (pv.componentsRev.headD `j).toString
  let base := ns.toString
  kunits s!"{base}.{gn}.nodes" n 1 sN pb
  if sL.units > 0 then kunits s!"{base}.{gn}.leaves" n arityL sL pb
  kunits s!"{base}.{gn}.glue" n 256 sG pw
  kunits s!"{base}.{gn}.ranges" n 256 sR pu
  klits s!"{base}.{gn}.OF" po
  let hblk := mkAppN (mkConst ``E1GS.range_all) #[P, nE, mkConst (pv ++ `hblkR)]
  let hgl := mkAppN (mkConst ``E1GS.glueF_of_rows) #[nE, LfE, mkRawNatLit nJ, JfE, WfE,
    mkAppN (mkConst ``E1GS.range_all) #[G, nE, mkConst (pv ++ `hglR)]]
  return (vs, hblk, hgl)

meta def ctxE (ip sl : Name) (cE : Expr) : Expr × Expr × Expr × Expr :=
  (cE, mkApp (mkConst ``E1G.slc) (mkConst (sl ++ `chunk)), mkConst (ip ++ `UB), mkConst (ip ++ `UBR))
meta def ltE (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [Level.zero]) natTy (mkConst ``instLTNat) a b
meta def jobOKE (ip sl : Name) (cE S : Expr) : Expr :=
  let (C, slE, UB, _) := ctxE ip sl cE; mkAppN (mkConst ``E1GS.JobOK) #[C, slE, UB, S]
/-- `hne : 0 < n` by evaluation -/
meta def hneE (nE : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) (ltE (mkRawNatLit 0) nE) (mkApp2 (mkConst ``Nat.decLt) (mkRawNatLit 0) nE)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) boolTy tru)
/-- the private chain theorem `jobL : JobOK C sl UB (Lf 0)` from `hjobs : ∀ k < nJ, JobOK C sl UB (Jf k)` -/
meta def jobLE (pv : Name) (ip sl ok : Name) (cE : Expr) (nJ : Nat) (hblk hgl hjobs : Expr) : Expr :=
  let (C, slE, UB, UBR) := ctxE ip sl cE
  mkAppN (mkConst ``E1GS.jobOK_of_chain_fn) #[C, slE, UB, UBR, mkConst (ok ++ `UB_eq), mkConst (ok ++ `UBR_eq),
    mkConst (ok ++ `UB_le), mkConst (pv ++ `n), mkConst (pv ++ `Lf), mkRawNatLit nJ, mkConst (pv ++ `Jf),
    hneE (mkConst (pv ++ `n)), hblk, hgl, hjobs]
/-- `JobOK C sl UB (S % 2 ^ 611)` from `JobOK C sl UB S` (`jobOK_hdr`), as the term and its type -/
meta def hdrE (ip sl : Name) (cE S h : Expr) : TermElabM Expr := do
  let (C, slE, UB, _) := ctxE ip sl cE
  let iffPf := mkAppN (mkConst ``E1GS.jobOK_hdr) #[C, slE, UB, S]
  let iffTy ← inferType iffPf
  match iffTy.getAppFnArgs with
  | (``Iff, #[a, bb]) => return mkApp4 (mkConst ``Iff.mpr) a bb iffPf h
  | _ => throwError "unexpected type of jobOK_hdr: {iffTy}"
/-- the public header of a chain whose first block is `S` (value `L0`): a mode-0 block (a job root) by its prefix,
`L0 % 2 ^ (13 + 7 d)` (`jobOK_hdr0`; what `glue0` and a frontier header table hold), a mode-1 block by `L0 % 2 ^ 611`
(`jobOK_hdr`); returns the numeral and the proof of `JobOK C sl UB H` from `h : JobOK C sl UB S` -/
meta def pubHdr (ip sl : Name) (cE S : Expr) (L0 : Nat) (h : Expr) : TermElabM (Nat × Expr) := do
  let (C, slE, UB, _) := ctxE ip sl cE
  if L0 % 2 == 1 then
    return (L0 % 2 ^ 611, ← hdrE ip sl cE S h)
  let d := L0 / 2 % 32
  let H := L0 % 2 ^ (13 + 7 * d)
  let f := mkAppN (mkConst ``E1GS.jobOK_hdr0) #[C, slE, UB, S]
  let fty ← whnf (← inferType f)
  let .forallE _ h0ty _ _ := fty | throwError "unexpected type of jobOK_hdr0: {fty}"
  let inst ← synthInstance (mkApp (mkConst ``Decidable) h0ty)
  let h0 := mkApp3 (mkConst ``of_decide_eq_true) h0ty inst (mkApp2 (mkConst ``Eq.refl [Level.one]) boolTy tru)
  let iffPf := mkApp f h0
  match (← inferType iffPf).getAppFnArgs with
  | (``Iff, #[a, bb]) => return (H, mkApp4 (mkConst ``Iff.mpr) a bb iffPf h)
  | _ => throwError "unexpected type of jobOK_hdr0 application"

/-- `∀ k < 0, P k` -/
meta def noJobsE (ip sl : Name) (cE JfE : Expr) : Expr :=
  let kv := mkBVar 1; let hkv := mkBVar 0
  mkLambda `k BinderInfo.default natTy (mkLambda `hk BinderInfo.default (ltE (mkBVar 0) (mkRawNatLit 0))
    (mkApp4 (mkConst ``absurd [Level.zero]) (ltE kv (mkRawNatLit 0)) (jobOKE ip sl cE (mkApp JfE (mkBVar 1))) hkv
      (mkApp (mkConst ``Nat.not_lt_zero) kv)))

/-! ## External-leaf lists and lifted statements -/

meta def listNatTy : Expr := mkApp (mkConst ``List [Level.zero]) natTy
meta def listLit (vs : Array Nat) : Expr :=
  vs.foldr (fun v acc => mkApp3 (mkConst ``List.cons [Level.zero]) natTy (mkRawNatLit v) acc) (mkApp (mkConst ``List.nil [Level.zero]) natTy)
meta def baseC (ip : Name) : Expr := mkConst (ip ++ `C)
meta def withExtE (ip : Name) (E : Expr) : Expr := mkApp2 (mkConst ``E1GS.withExt) (baseC ip) E
meta def extSubE (X E : Expr) : Expr := mkApp2 (mkConst ``E1GS.ExtSub) X E
/-- `IP.C.EXT = []` by evaluation -/
meta def baseNilE (ip : Name) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) listNatTy (mkApp (mkConst ``List.nil [Level.zero]) natTy)
/-- the lifted form of a statement: `∀ E, ExtSub X E → stmt (withExt IP.C E)` -/
meta def liftedStmt (ip : Name) (X : Expr) (stmt : Expr → Expr) : MetaM Expr :=
  withLocalDeclD `E listNatTy fun E => withLocalDeclD `hE (extSubE X E) fun hE =>
    mkForallFVars #[E, hE] (stmt (withExtE ip E))
/-- an imported theorem's form: `none` (over `IP.C`), or `some X` (lifted, `∀ E, ExtSub X E → …`) -/
meta def liftedX? (thm : Name) : CoreM (Option Expr) := do
  let ty := (← getConstInfo thm).type
  match ty with
  | .forallE _ _ (.forallE _ hty _ _) _ =>
    match hty.getAppFnArgs with
    | (``E1GS.ExtSub, #[X, _]) => return some X
    | _ => return none
  | _ => return none
/-- a public list `name : List ℕ` (exposed: importers unfold it) -/
meta def addExtList (name : Name) (v : Expr) : CoreM Unit :=
  addDecl (.defnDecl { name := name, levelParams := [], type := listNatTy, value := v, hints := .abbrev, safety := .safe })
    (forceExpose := true)
/-- the members of a list term: literals, `List.cons`/`List.nil`, appends, and constants with (exposed) values -/
meta partial def evalList (e : Expr) : MetaM (Array Nat) := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``List.nil, _) => return #[]
  | (``List.cons, #[_, h, t]) =>
    match h.rawNatLit? <|> h.nat? with
    | some v => return #[v] ++ (← evalList t)
    | none => throwError "evalList: not a numeral: {h}"
  | (``HAppend.hAppend, #[_, _, _, _, a, b]) => return (← evalList a) ++ (← evalList b)
  | (``List.append, #[_, a, b]) => return (← evalList a) ++ (← evalList b)
  | _ =>
    match e with
    | .const n _ =>
      match (← getConstInfo n).value? with
      | some v => evalList v
      | none => throwError "evalList: {n} has no value here"
    | _ => throwError "evalList: cannot evaluate {e}"
/-- the right-nested append `s_0 ++ (s_1 ++ (… ++ s_k))` of segments, and for each segment `i` a function from
`ExtSub (whole) E` to `ExtSub s_i E` -/
meta def appendSegs (segs : Array Expr) : MetaM (Expr × Array (Expr → Expr → Expr)) := do
  let k := segs.size
  -- tails: tail_i = s_i ++ (… ++ s_{k-1}); tail_{k-1} = s_{k-1}
  let mut tails : Array Expr := Array.replicate k (mkConst ``Nat.zero)
  tails := tails.set! (k - 1) segs[k - 1]!
  let mut i := k - 1
  while i > 0 do
    i := i - 1
    tails := tails.set! i (← mkAppM ``HAppend.hAppend #[segs[i]!, tails[i + 1]!])
  let mut subs : Array (Expr → Expr → Expr) := #[]
  for j in [0:k] do
    let tl := tails
    subs := subs.push fun E h => Id.run do
      -- from ExtSub tail_0 E to ExtSub tail_j E, then (unless last) to ExtSub s_j E
      let mut hh := h
      for t in [0:j] do
        hh := mkAppN (mkConst ``E1GS.extSub_append_right) #[segs[t]!, tl[t + 1]!, E, hh]
      if j + 1 < k then hh := mkAppN (mkConst ``E1GS.extSub_append_left) #[segs[j]!, tl[j + 1]!, E, hh]
      return hh
  return (tails[0]!, subs)

meta def run (ns : Name) (pb po pw pu : String) (ip sl ok : Name) : CommandElabM Unit := do
  let pv := mkPrivateName (← getEnv) ns
  let cE := baseC ip
  let (vs, hblk, hgl) ← chainCore ns pv pb po pw pu ip sl cE 0 none
  let JfE := mkConst (pv ++ `Jf)
  discard <| liftCoreM <| addThm (pv ++ `jobL) (jobOKE ip sl cE (mkApp (mkConst (pv ++ `Lf)) (mkRawNatLit 0)))
    (jobLE pv ip sl ok cE 0 hblk hgl (noJobsE ip sl cE JfE))
  let (H, pf) ← liftTermElabM <| pubHdr ip sl cE (mkApp (mkConst (pv ++ `Lf)) (mkRawNatLit 0)) vs[0]! (mkConst (pv ++ `jobL))
  KMod.addPub (ns ++ `job) (jobOKE ip sl cE (mkRawNatLit H)) pf
  logInfo m!"#e1gjob {ns}: {vs.size} blocks; public {ns ++ `job} : JobOK … {H}"

/-- `RangeOK (fun k => JobOK C sl UB (T k)) a m` -/
meta def rangeQ (ip sl : Name) (cE T : Expr) (a m : Nat) : Expr :=
  mkAppN (mkConst ``E1GS.RangeOK) #[mkLambda `k BinderInfo.default natTy (jobOKE ip sl cE (mkApp T (mkBVar 0))), mkRawNatLit a, mkRawNatLit m]
meta partial def joinTree (ip sl : Name) (cE T : Expr) (leaves : Array (Nat × Nat × Expr)) (lo cnt : Nat) : Expr :=
  if cnt ≤ 1 then leaves[lo]!.2.2 else
  let h := cnt / 2
  let a := leaves[lo]!.1
  let m1 := (List.range h).foldl (fun s t => s + leaves[lo + t]!.2.1) 0
  let m2 := (List.range (cnt - h)).foldl (fun s t => s + leaves[lo + h + t]!.2.1) 0
  mkAppN (mkConst ``E1GS.range_join) #[mkLambda `k BinderInfo.default natTy (jobOKE ip sl cE (mkApp T (mkBVar 0))),
    mkRawNatLit a, mkRawNatLit m1, mkRawNatLit m2, joinTree ip sl cE T leaves lo h, joinTree ip sl cE T leaves (lo + h) (cnt - h)]

/-- the header `H` of an imported `JobOK _ _ _ H` (or its lifted form) -/
meta def thmHdr (thm : Name) : CoreM Expr := do
  let rec go (e : Expr) : Expr := match e with | .forallE _ _ b _ => go b | _ => e
  match (go (← getConstInfo thm).type).getAppFnArgs with
  | (``E1GS.JobOK, #[_, _, _, H]) => return H
  | _ => throwError "#e1gjobs: {thm} is not a JobOK theorem"

/-- several jobs `a .. a + m - 1` of the header table `TBL` (lines of `jobs.lst`: four paths per job, as `#e1gjob`, optionally
`X=p1,…` (its external leaves), each a private chain; or `@THM`, an imported `THM : JobOK C sl UB H` or its lifted form, e.g.
a split job's top); public `NS.ok : RangeOK (fun k => JobOK C sl UB (TBL.entry k)) a m` (each job's header meets
`TBL.entry k` by evaluation), lifted over `NS.EXT` when the module has external leaves or lifted children -/
meta def runJobs (ns : Name) (pl : String) (ip sl ok tbl : Name) (a : Nat) : CommandElabM Unit := do
  let pv := mkPrivateName (← getEnv) ns
  let jobs := ((← IO.FS.lines pl).filter (· ≠ "")).map (fun l => (l.splitOn " ").filter (· ≠ "") |>.toArray)
  let T := mkConst (tbl ++ `entry)
  -- segments of NS.EXT: per job, its own external leaves or a lifted child's list
  let mut segs : Array Expr := #[]
  let mut segOf : Array (Option Nat) := #[]
  for f in jobs do
    if f.size == 1 && f[0]!.startsWith "@" then
      match ← liftCoreM <| liftedX? (f[0]!.drop 1).toName with
      | some X => segOf := segOf.push (some segs.size); segs := segs.push X
      | none => segOf := segOf.push none
    else
      let xs := (f.extract 4 f.size).filter (·.startsWith "X=")
      let vals : Array Nat := xs.foldl (fun acc x => acc ++ ((((x.drop 2).toString).splitOn ",").filter (· ≠ "") |>.map String.toNat! |>.toArray)) #[]
      if vals.isEmpty then segOf := segOf.push none
      else segOf := segOf.push (some segs.size); segs := segs.push (listLit vals)
  let lifted := !segs.isEmpty
  let (cE, subs) ← if lifted then do
      let (whole, subs) ← liftTermElabM <| appendSegs segs
      let vals ← liftTermElabM <| evalList whole
      liftCoreM <| addExtList (ns ++ `EXT) (listLit vals)
      pure (withExtE ip (mkConst (ns ++ `EXT)), subs)
    else pure (baseC ip, #[])
  let extC := mkConst (ns ++ `EXT)
  let hrefl := mkApp (mkConst ``E1GS.extSub_refl) extC
  let mut leaves : Array (Nat × Nat × Expr) := #[]
  for j in [0:jobs.size] do
    let f := jobs[j]!
    let k := a + j
    let Q := mkLambda `k BinderInfo.default natTy (jobOKE ip sl cE (mkApp T (mkBVar 0)))
    let pj := pv ++ Name.mkSimple s!"J{j}"
    if f.size == 1 && f[0]!.startsWith "@" then
      -- "@THM": job k is an imported theorem `THM : JobOK C sl UB H` (or lifted), H = T k by evaluation
      let thm := (f[0]!.drop 1).toName
      let pf : Expr ← do
        if let some i := segOf[j]! then
          pure (mkAppN (mkConst thm) #[extC, subs[i]! extC hrefl])
        else if lifted then
          let H ← liftCoreM <| thmHdr thm
          let (_, slE, UB, _) := ctxE ip sl cE
          pure (mkAppN (mkConst ``E1GS.jobOK_lift_base) #[baseC ip, baseNilE ip, slE, UB, H, mkConst thm, extC])
        else
          pure (mkConst thm)
      discard <| liftCoreM <| addThm (pj ++ `jobT) (jobOKE ip sl cE (mkApp T (mkRawNatLit k))) pf
      leaves := leaves.push (k, 1, mkAppN (mkConst ``E1GS.range_one) #[Q, mkRawNatLit k, mkConst (pj ++ `jobT)])
      continue
    let (vsj, hblk, hgl) ← chainCore ns pj f[0]! f[1]! f[2]! f[3]! ip sl cE 0 none
    let Lf0 := mkApp (mkConst (pj ++ `Lf)) (mkRawNatLit 0)
    discard <| liftCoreM <| addThm (pj ++ `jobL) (jobOKE ip sl cE Lf0) (jobLE pj ip sl ok cE 0 hblk hgl (noJobsE ip sl cE (mkConst (pj ++ `Jf))))
    let (_, pf) ← liftTermElabM <| pubHdr ip sl cE Lf0 vsj[0]! (mkConst (pj ++ `jobL))
    -- JobOK … (the header of Lf 0) is JobOK … (T k) by evaluation
    discard <| liftCoreM <| addThm (pj ++ `jobT) (jobOKE ip sl cE (mkApp T (mkRawNatLit k))) pf
    leaves := leaves.push (k, 1, mkAppN (mkConst ``E1GS.range_one) #[Q, mkRawNatLit k, mkConst (pj ++ `jobT)])
  let tree := joinTree ip sl cE T leaves 0 leaves.size
  if lifted then
    discard <| liftCoreM <| addThm (pv ++ `range) (rangeQ ip sl cE T a jobs.size) tree
    let (_, slE, UB, _) := ctxE ip sl cE
    let stmt ← liftTermElabM <| liftedStmt ip extC (fun c => rangeQ ip sl c T a jobs.size)
    KMod.addPub (ns ++ `ok) stmt (mkAppN (mkConst ``E1GS.rangeOK_lift) #[baseC ip, extC, slE, UB, T, mkRawNatLit a,
      mkRawNatLit jobs.size, mkConst (pv ++ `range)])
    logInfo m!"#e1gjobs {ns}: jobs {a} .. {a + jobs.size - 1} of {tbl}, lifted over {ns ++ `EXT} ({segs.size} segments)"
  else
    KMod.addPub (ns ++ `ok) (rangeQ ip sl cE T a jobs.size) tree
    logInfo m!"#e1gjobs {ns}: jobs {a} .. {a + jobs.size - 1} of {tbl}"

/-- an aggregator: the imported range theorems listed in `children.lst` ("name a m", consecutive ranges), joined; public
`NS.ok : RangeOK (fun k => JobOK C sl UB (TBL.entry k)) a M`, lifted over `NS.EXT` (the append of the lifted children's lists)
when any child is lifted (a child over `IP.C` is lifted by `rangeOK_lift_base`) -/
meta def runAgg (ns : Name) (pc : String) (ip sl tbl : Name) : CommandElabM Unit := do
  let rows := ((← IO.FS.lines pc).filter (· ≠ "")).map (fun l => (l.splitOn " ").filter (· ≠ "") |>.toArray)
  let T := mkConst (tbl ++ `entry)
  let names := rows.map (fun r => r[0]!.toName)
  let ams : Array (Nat × Nat) := rows.map (fun r => (r[1]!.toNat!, r[2]!.toNat!))
  for i in [1:ams.size] do
    if ams[i]!.1 != ams[i-1]!.1 + ams[i-1]!.2 then throwError "#e1gagg: ranges not consecutive at {i}"
  let a := ams[0]!.1; let M := ams.foldl (fun s l => s + l.2) 0
  let xs ← liftCoreM <| names.mapM liftedX?
  if xs.all Option.isNone then
    let cE := baseC ip
    let leaves : Array (Nat × Nat × Expr) := (List.range names.size).toArray.map fun i => (ams[i]!.1, ams[i]!.2, mkConst names[i]!)
    KMod.addPub (ns ++ `ok) (rangeQ ip sl cE T a M) (joinTree ip sl cE T leaves 0 leaves.size)
    logInfo m!"#e1gagg {ns}: {leaves.size} children, jobs {a} .. {a + M - 1} of {tbl}"
    return
  let segs := xs.filterMap id
  let (whole, subs) ← liftTermElabM <| appendSegs segs
  let vals ← liftTermElabM <| evalList whole
  liftCoreM <| addExtList (ns ++ `EXT) (listLit vals)
  let extC := mkConst (ns ++ `EXT)
  let (_, slE, UB, _) := ctxE ip sl (baseC ip)
  let segIx : Array (Option Nat) := Id.run do
    let mut out := #[]; let mut c := 0
    for x in xs do
      if x.isSome then out := out.push (some c); c := c + 1 else out := out.push none
    return out
  let stmt ← liftTermElabM <| liftedStmt ip extC (fun c => rangeQ ip sl c T a M)
  let pf ← liftTermElabM <| withLocalDeclD `E listNatTy fun E => withLocalDeclD `hE (extSubE extC E) fun hE => do
    let cE := withExtE ip E
    let leaves : Array (Nat × Nat × Expr) := (List.range names.size).toArray.map fun i =>
      let p := match segIx[i]! with
        | some s => mkAppN (mkConst names[i]!) #[E, subs[s]! E hE]
        | none => mkAppN (mkConst ``E1GS.rangeOK_lift_base) #[baseC ip, baseNilE ip, slE, UB, T, mkRawNatLit ams[i]!.1,
            mkRawNatLit ams[i]!.2, mkConst names[i]!, E]
      (ams[i]!.1, ams[i]!.2, p)
    mkLambdaFVars #[E, hE] (joinTree ip sl cE T leaves 0 leaves.size)
  KMod.addPub (ns ++ `ok) stmt pf
  logInfo m!"#e1gagg {ns}: {names.size} children ({segs.size} lifted), jobs {a} .. {a + M - 1} of {tbl}, lifted over {ns ++ `EXT}"

/-- a chain whose records are glued to later blocks or to the jobs `0 .. nJ - 1` of `TBL` (witness `n + k`), with the jobs
from the imported `CHILD : RangeOK (fun k => JobOK C sl UB (TBL.entry k)) 0 nJ` (or its lifted form); public
`NS.job : JobOK C sl UB H`, lifted over `NS.EXT` (its own external leaves `ext`, then the child's list) when either is present -/
meta def runTop (ns : Name) (pb po pw pu : String) (ip sl ok tbl : Name) (nJ : Nat) (child : Name) (ext : Array Nat) :
    CommandElabM Unit := do
  let pv := mkPrivateName (← getEnv) ns
  let T := mkConst (tbl ++ `entry)
  let cx ← liftCoreM <| liftedX? child
  let segs : Array Expr := (if ext.isEmpty then #[] else #[listLit ext]) ++ (match cx with | some X => #[X] | none => #[])
  let lifted := !segs.isEmpty
  let (cE, subs) ← if lifted then do
      let (whole, subs) ← liftTermElabM <| appendSegs segs
      let vals ← liftTermElabM <| evalList whole
      liftCoreM <| addExtList (ns ++ `EXT) (listLit vals)
      pure (withExtE ip (mkConst (ns ++ `EXT)), subs)
    else pure (baseC ip, #[])
  let extC := mkConst (ns ++ `EXT)
  let (_, slE, UB, _) := ctxE ip sl cE
  let (vs, hblk, hgl) ← chainCore ns pv pb po pw pu ip sl cE nJ (some T)
  let Q := mkLambda `k BinderInfo.default natTy (jobOKE ip sl cE (mkApp T (mkBVar 0)))
  let childR : Expr := match cx with
    | some _ => mkAppN (mkConst child) #[extC, subs[segs.size - 1]! extC (mkApp (mkConst ``E1GS.extSub_refl) extC)]
    | none => if lifted then mkAppN (mkConst ``E1GS.rangeOK_lift_base) #[baseC ip, baseNilE ip, slE, UB, T, mkRawNatLit 0,
        mkRawNatLit nJ, mkConst child, extC] else mkConst child
  let hjobs := mkAppN (mkConst ``E1GS.range_all) #[Q, mkRawNatLit nJ, childR]
  let Lf0 := mkApp (mkConst (pv ++ `Lf)) (mkRawNatLit 0)
  discard <| liftCoreM <| addThm (pv ++ `jobL) (jobOKE ip sl cE Lf0) (jobLE pv ip sl ok cE nJ hblk hgl hjobs)
  let (H, pf) ← liftTermElabM <| pubHdr ip sl cE Lf0 vs[0]! (mkConst (pv ++ `jobL))
  if lifted then
    discard <| liftCoreM <| addThm (pv ++ `jobH) (jobOKE ip sl cE (mkRawNatLit H)) pf
    let stmt ← liftTermElabM <| liftedStmt ip extC (fun c => jobOKE ip sl c (mkRawNatLit H))
    KMod.addPub (ns ++ `job) stmt (mkAppN (mkConst ``E1GS.jobOK_lift) #[baseC ip, extC, slE, UB, mkRawNatLit H, mkConst (pv ++ `jobH)])
    logInfo m!"#e1gtop {ns}: {vs.size} blocks over {nJ} jobs of {tbl}; public {ns ++ `job} (lifted over {ns ++ `EXT}) : JobOK … {H}"
  else
    KMod.addPub (ns ++ `job) (jobOKE ip sl cE (mkRawNatLit H)) pf
    logInfo m!"#e1gtop {ns}: {vs.size} blocks over {nJ} jobs of {tbl}; public {ns ++ `job} : JobOK … {H}"

meta def parseExt (s : String) : Array Nat :=
  ((s.splitOn ",").filter (· ≠ "") |>.map String.toNat!).toArray

elab "#e1gjob " ns:ident pb:str po:str pw:str pu:str ip:ident sl:ident ok:ident : command =>
  run ns.getId pb.getString po.getString pw.getString pu.getString ip.getId sl.getId ok.getId
elab "#e1gjobs " ns:ident pl:str ip:ident sl:ident ok:ident tbl:ident a:num : command =>
  runJobs ns.getId pl.getString ip.getId sl.getId ok.getId tbl.getId a.getNat
elab "#e1gagg " ns:ident pc:str ip:ident sl:ident tbl:ident : command =>
  runAgg ns.getId pc.getString ip.getId sl.getId tbl.getId
elab "#e1gtop " ns:ident pb:str po:str pw:str pu:str ip:ident sl:ident ok:ident tbl:ident nJ:num child:ident ext:(str)? : command =>
  runTop ns.getId pb.getString po.getString pw.getString pu.getString ip.getId sl.getId ok.getId tbl.getId nJ.getNat child.getId
    (match ext with | some e => parseExt e.getString | none => #[])

end E1GJob3
