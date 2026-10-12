module
public meta import Lean
public import E1PQ.ChainF
public import RT.Load
public meta import KMod.Units
/-! # `#e1pjob`, `#e1pjobs`, `#e1pagg`, `#e1ptop` (E1PQ.JobCmd, the rule-1 successor of E1PK.JobCmd): E1GK.JobCmd for the E1P checker (255 labels; mode-1 headers of
1027 bits, mode-0 prefix headers of `14 + 8 d` bits).  E1GK.JobCmd's documentation, with E1G read as E1P:

`#e1gjob`: an E1G job module, built as terms (module form)

`#e1gjob NS "blocks.bin" "of.bin" "wt.bin" "units.txt" IP SL OK` adds, every declaration through `addDecl` (checked by the
kernel only; set `Elab.async false`), with private names (`mkPrivateName`) except the last:
* the job's block literals `L<i>`, the glue witness tables (`OF`, `WT`: 32-bit entries, the `#rttablew` layout), `n`, `Jf`,
  `Wf i j`, and `Lf i`: a balanced dispatch over the literals as one small definition per level;
* the units `u<k>`, one per line of `units.txt` (block indices): `(E1G.block C sl UB UBR L_a && …) = true` by evaluation;
* the glue ranges `g<a>`: `glueRange n Lf 0 Jf Wf a m = true` (256 blocks each) by evaluation;
* `r<a>`: `RangeOK P a m` from the units (packed units split by `Bool.and_eq_true`), joined in balanced trees, and the
  private chain theorem `jobL : JobOK C sl UB (Lf 0)` (`jobOK_of_chain_fn`);
* public: `NS.job : JobOK C sl UB H` with `H` the job's header numeral (a job root, mode 0: `S % 2 ^ (14 + 8 d)` by `jobOK_hdr0`; mode 1: `S % 2 ^ 1027`): the only constant an
  importer sees.
`IP.C`, `SL.chunk`, `IP.UB`, `IP.UBR`, `OK.UB_eq`, `OK.UBR_eq`, `OK.UB_le` come from the context's IP modules. -/
@[expose] public section
open Lean Elab Command Meta

namespace E1PJob

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
meta def chainCore (ns pv : Name) (pb po pw pu : String) (ip sl : Name) (nJ : Nat) (JfE? : Option Expr) :
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
  let C := mkConst (ip ++ `C); let slE := mkApp (mkConst ``E1P.slc) (mkConst (sl ++ `chunk))
  let UB := mkConst (ip ++ `UB); let UBR := mkConst (ip ++ `UBR)
  let blk (L : Expr) : Expr := mkAppN (mkConst ``E1P.block) #[C, slE, UB, UBR, L]
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
  let G := mkLambda `i BinderInfo.default natTy (eqTrue (mkAppN (mkConst ``E1PS.glueRowW) #[nE, LfE, mkRawNatLit nJ, JfE, WfE, mkBVar 0]))
  let rangeTy (Q : Expr) (a m : Nat) : Expr := mkAppN (mkConst ``E1PS.RangeOK) #[Q, mkRawNatLit a, mkRawNatLit m]
  let rec tree (Q : Expr) (leaf : Nat → Expr) (lo cnt : Nat) (step : Nat) (sizeOf : Nat → Nat) : Expr :=
    if cnt ≤ 1 then leaf lo else
    let h := cnt / 2
    let a := lo * step; let m1 := (List.range h).foldl (fun s t => s + sizeOf (lo + t)) 0
    let m2 := (List.range (cnt - h)).foldl (fun s t => s + sizeOf (lo + h + t)) 0
    mkAppN (mkConst ``E1PS.range_join) #[Q, mkRawNatLit a, mkRawNatLit m1, mkRawNatLit m2,
      tree Q leaf lo h step sizeOf, tree Q leaf (lo + h) (cnt - h) step sizeOf]
  let nch := (n + GB - 1) / GB
  let csize (c : Nat) : Nat := min GB (n - c * GB)
  for c in [0:nch] do
    let a := c * GB; let m := csize c
    let bt := tree P (fun k => mkAppN (mkConst ``E1PS.range_one) #[P, mkRawNatLit k, pf[k]!]) a m 1 (fun _ => 1)
    let tr ← liftCoreM <| addThm (pv ++ Name.mkSimple s!"r{a}") (rangeTy P a m) bt
    sR := sR.add c tr
    let gb := mkAppN (mkConst ``E1PS.glueRange) #[nE, LfE, mkRawNatLit nJ, JfE, WfE, mkRawNatLit a, mkRawNatLit m]
    let tg ← liftCoreM <| addThm (pv ++ Name.mkSimple s!"g{a}") (eqTrue gb) (decideProof gb)
    sG := sG.add c tg
  let topB := tree P (fun c => mkConst (pv ++ Name.mkSimple s!"r{c * GB}")) 0 nch GB csize
  let t1 ← liftCoreM <| addThm (pv ++ `hblkR) (rangeTy P 0 n) topB
  let topG := tree G (fun c => mkAppN (mkConst ``E1PS.glueRange_spec)
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
  let hblk := mkAppN (mkConst ``E1PS.range_all) #[P, nE, mkConst (pv ++ `hblkR)]
  let hgl := mkAppN (mkConst ``E1PS.glueF_of_rows) #[nE, LfE, mkRawNatLit nJ, JfE, WfE,
    mkAppN (mkConst ``E1PS.range_all) #[G, nE, mkConst (pv ++ `hglR)]]
  return (vs, hblk, hgl)

meta def ctxE (ip sl : Name) : Expr × Expr × Expr × Expr :=
  (mkConst (ip ++ `C), mkApp (mkConst ``E1P.slc) (mkConst (sl ++ `chunk)), mkConst (ip ++ `UB), mkConst (ip ++ `UBR))
meta def ltE (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [Level.zero]) natTy (mkConst ``instLTNat) a b
meta def jobOKE (ip sl : Name) (S : Expr) : Expr :=
  let (C, slE, UB, _) := ctxE ip sl; mkAppN (mkConst ``E1PS.JobOK) #[C, slE, UB, S]
/-- `hne : 0 < n` by evaluation -/
meta def hneE (nE : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) (ltE (mkRawNatLit 0) nE) (mkApp2 (mkConst ``Nat.decLt) (mkRawNatLit 0) nE)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) boolTy tru)
/-- the private chain theorem `jobL : JobOK C sl UB (Lf 0)` from `hjobs : ∀ k < nJ, JobOK C sl UB (Jf k)` -/
meta def jobLE (pv : Name) (ip sl ok : Name) (nJ : Nat) (hblk hgl hjobs : Expr) : Expr :=
  let (C, slE, UB, UBR) := ctxE ip sl
  mkAppN (mkConst ``E1PS.jobOK_of_chain_fn) #[C, slE, UB, UBR, mkConst (ok ++ `UB_eq), mkConst (ok ++ `UBR_eq),
    mkConst (ok ++ `UB_le), mkConst (pv ++ `n), mkConst (pv ++ `Lf), mkRawNatLit nJ, mkConst (pv ++ `Jf),
    hneE (mkConst (pv ++ `n)), hblk, hgl, hjobs]
/-- `JobOK C sl UB (S % 2 ^ 1027)` from `JobOK C sl UB S` (`jobOK_hdr`), as the term and its type -/
meta def hdrE (ip sl : Name) (S h : Expr) : TermElabM Expr := do
  let (C, slE, UB, _) := ctxE ip sl
  let iffPf := mkAppN (mkConst ``E1PS.jobOK_hdr) #[C, slE, UB, S]
  let iffTy ← inferType iffPf
  match iffTy.getAppFnArgs with
  | (``Iff, #[a, bb]) => return mkApp4 (mkConst ``Iff.mpr) a bb iffPf h
  | _ => throwError "unexpected type of jobOK_hdr: {iffTy}"
/-- the public header of a chain whose first block is `S` (value `L0`): a mode-0 block (a job root) by its prefix,
`L0 % 2 ^ (14 + 8 d)` (`jobOK_hdr0`; what `glue0` and a frontier header table hold), a mode-1 block by `L0 % 2 ^ 1027`
(`jobOK_hdr`); returns the numeral and the proof of `JobOK C sl UB H` from `h : JobOK C sl UB S` -/
meta def pubHdr (ip sl : Name) (S : Expr) (L0 : Nat) (h : Expr) : TermElabM (Nat × Expr) := do
  let (C, slE, UB, _) := ctxE ip sl
  if L0 % 2 == 1 then
    return (L0 % 2 ^ 1027, ← hdrE ip sl S h)
  let d := L0 / 2 % 32
  let H := L0 % 2 ^ (14 + 8 * d)
  let f := mkAppN (mkConst ``E1PS.jobOK_hdr0) #[C, slE, UB, S]
  let fty ← whnf (← inferType f)
  let .forallE _ h0ty _ _ := fty | throwError "unexpected type of jobOK_hdr0: {fty}"
  let inst ← synthInstance (mkApp (mkConst ``Decidable) h0ty)
  let h0 := mkApp3 (mkConst ``of_decide_eq_true) h0ty inst (mkApp2 (mkConst ``Eq.refl [Level.one]) boolTy tru)
  let iffPf := mkApp f h0
  match (← inferType iffPf).getAppFnArgs with
  | (``Iff, #[a, bb]) => return (H, mkApp4 (mkConst ``Iff.mpr) a bb iffPf h)
  | _ => throwError "unexpected type of jobOK_hdr0 application"

/-- `∀ k < 0, P k` -/
meta def noJobsE (ip sl : Name) (JfE : Expr) : Expr :=
  let kv := mkBVar 1; let hkv := mkBVar 0
  mkLambda `k BinderInfo.default natTy (mkLambda `hk BinderInfo.default (ltE (mkBVar 0) (mkRawNatLit 0))
    (mkApp4 (mkConst ``absurd [Level.zero]) (ltE kv (mkRawNatLit 0)) (jobOKE ip sl (mkApp JfE (mkBVar 1))) hkv
      (mkApp (mkConst ``Nat.not_lt_zero) kv)))

meta def run (ns : Name) (pb po pw pu : String) (ip sl ok : Name) : CommandElabM Unit := do
  let pv := mkPrivateName (← getEnv) ns
  let (vs, hblk, hgl) ← chainCore ns pv pb po pw pu ip sl 0 none
  let JfE := mkConst (pv ++ `Jf)
  discard <| liftCoreM <| addThm (pv ++ `jobL) (jobOKE ip sl (mkApp (mkConst (pv ++ `Lf)) (mkRawNatLit 0)))
    (jobLE pv ip sl ok 0 hblk hgl (noJobsE ip sl JfE))
  let (H, pf) ← liftTermElabM <| pubHdr ip sl (mkApp (mkConst (pv ++ `Lf)) (mkRawNatLit 0)) vs[0]! (mkConst (pv ++ `jobL))
  KMod.addPub (ns ++ `job) (jobOKE ip sl (mkRawNatLit H)) pf
  logInfo m!"#e1gjob {ns}: {vs.size} blocks; public {ns ++ `job} : JobOK … {H}"

/-- `RangeOK (fun k => JobOK C sl UB (T k)) a m` -/
meta def rangeQ (ip sl : Name) (T : Expr) (a m : Nat) : Expr :=
  mkAppN (mkConst ``E1PS.RangeOK) #[mkLambda `k BinderInfo.default natTy (jobOKE ip sl (mkApp T (mkBVar 0))), mkRawNatLit a, mkRawNatLit m]
meta partial def joinTree (ip sl : Name) (T : Expr) (leaves : Array (Nat × Nat × Expr)) (lo cnt : Nat) : Expr :=
  if cnt ≤ 1 then leaves[lo]!.2.2 else
  let h := cnt / 2
  let a := leaves[lo]!.1
  let m1 := (List.range h).foldl (fun s t => s + leaves[lo + t]!.2.1) 0
  let m2 := (List.range (cnt - h)).foldl (fun s t => s + leaves[lo + h + t]!.2.1) 0
  mkAppN (mkConst ``E1PS.range_join) #[mkLambda `k BinderInfo.default natTy (jobOKE ip sl (mkApp T (mkBVar 0))),
    mkRawNatLit a, mkRawNatLit m1, mkRawNatLit m2, joinTree ip sl T leaves lo h, joinTree ip sl T leaves (lo + h) (cnt - h)]

/-- several jobs `a .. a + m - 1` of the header table `TBL` (lines of `jobs.lst`: four paths per job, as `#e1gjob`, each a
private chain; or `@THM`, an imported `THM : JobOK C sl UB H`, e.g. a split job's top); public `NS.ok : RangeOK (fun k => JobOK C sl UB (TBL.entry k)) a m` (each job's header `L_0 % 2 ^ 1027` meets
`TBL.entry k` by evaluation) -/
meta def runJobs (ns : Name) (pl : String) (ip sl ok tbl : Name) (a : Nat) : CommandElabM Unit := do
  let pv := mkPrivateName (← getEnv) ns
  let jobs := ((← IO.FS.lines pl).filter (· ≠ "")).map (fun l => (l.splitOn " ").filter (· ≠ "") |>.toArray)
  let T := mkConst (tbl ++ `entry)
  let mut leaves : Array (Nat × Nat × Expr) := #[]
  for j in [0:jobs.size] do
    let f := jobs[j]!
    let k := a + j
    let Q := mkLambda `k BinderInfo.default natTy (jobOKE ip sl (mkApp T (mkBVar 0)))
    -- "@THM": job k is an imported theorem `THM : JobOK C sl UB H` (a split job's top), H = T k by evaluation
    if f.size == 1 && f[0]!.startsWith "@" then
      let thm := (f[0]!.drop 1).toName
      let pj := pv ++ Name.mkSimple s!"J{j}"
      discard <| liftCoreM <| addThm (pj ++ `jobT) (jobOKE ip sl (mkApp T (mkRawNatLit k))) (mkConst thm)
      leaves := leaves.push (k, 1, mkAppN (mkConst ``E1PS.range_one) #[Q, mkRawNatLit k, mkConst (pj ++ `jobT)])
      continue
    let pj := pv ++ Name.mkSimple s!"J{j}"
    let (vsj, hblk, hgl) ← chainCore ns pj f[0]! f[1]! f[2]! f[3]! ip sl 0 none
    let Lf0 := mkApp (mkConst (pj ++ `Lf)) (mkRawNatLit 0)
    discard <| liftCoreM <| addThm (pj ++ `jobL) (jobOKE ip sl Lf0) (jobLE pj ip sl ok 0 hblk hgl (noJobsE ip sl (mkConst (pj ++ `Jf))))
    let (_, pf) ← liftTermElabM <| pubHdr ip sl Lf0 vsj[0]! (mkConst (pj ++ `jobL))
    -- JobOK … (the header of Lf 0) is JobOK … (T k) by evaluation
    discard <| liftCoreM <| addThm (pj ++ `jobT) (jobOKE ip sl (mkApp T (mkRawNatLit k))) pf
    leaves := leaves.push (k, 1, mkAppN (mkConst ``E1PS.range_one) #[Q, mkRawNatLit k, mkConst (pj ++ `jobT)])
  KMod.addPub (ns ++ `ok) (rangeQ ip sl T a jobs.size) (joinTree ip sl T leaves 0 leaves.size)
  logInfo m!"#e1gjobs {ns}: jobs {a} .. {a + jobs.size - 1} of {tbl}"

/-- an aggregator: the imported range theorems listed in `children.lst` ("name a m", consecutive ranges), joined; public
`NS.ok : RangeOK (fun k => JobOK C sl UB (TBL.entry k)) a M` -/
meta def runAgg (ns : Name) (pc : String) (ip sl tbl : Name) : CommandElabM Unit := do
  let rows := ((← IO.FS.lines pc).filter (· ≠ "")).map (fun l => (l.splitOn " ").filter (· ≠ "") |>.toArray)
  let T := mkConst (tbl ++ `entry)
  let leaves : Array (Nat × Nat × Expr) := rows.map (fun r => (r[1]!.toNat!, r[2]!.toNat!, mkConst r[0]!.toName))
  for i in [1:leaves.size] do
    if leaves[i]!.1 != leaves[i-1]!.1 + leaves[i-1]!.2.1 then throwError "#e1gagg: ranges not consecutive at {i}"
  let a := leaves[0]!.1; let M := leaves.foldl (fun s l => s + l.2.1) 0
  KMod.addPub (ns ++ `ok) (rangeQ ip sl T a M) (joinTree ip sl T leaves 0 leaves.size)
  logInfo m!"#e1gagg {ns}: {leaves.size} children, jobs {a} .. {a + M - 1} of {tbl}"

/-- a chain whose records are glued to later blocks or to the jobs `0 .. nJ - 1` of `TBL` (witness `n + k`), with the jobs
from the imported `CHILD : RangeOK (fun k => JobOK C sl UB (TBL.entry k)) 0 nJ`; public `NS.job : JobOK C sl UB H` -/
meta def runTop (ns : Name) (pb po pw pu : String) (ip sl ok tbl : Name) (nJ : Nat) (child : Name) : CommandElabM Unit := do
  let pv := mkPrivateName (← getEnv) ns
  let T := mkConst (tbl ++ `entry)
  let (vs, hblk, hgl) ← chainCore ns pv pb po pw pu ip sl nJ (some T)
  let Q := mkLambda `k BinderInfo.default natTy (jobOKE ip sl (mkApp T (mkBVar 0)))
  let hjobs := mkAppN (mkConst ``E1PS.range_all) #[Q, mkRawNatLit nJ, mkConst child]
  let Lf0 := mkApp (mkConst (pv ++ `Lf)) (mkRawNatLit 0)
  discard <| liftCoreM <| addThm (pv ++ `jobL) (jobOKE ip sl Lf0) (jobLE pv ip sl ok nJ hblk hgl hjobs)
  let (H, pf) ← liftTermElabM <| pubHdr ip sl Lf0 vs[0]! (mkConst (pv ++ `jobL))
  KMod.addPub (ns ++ `job) (jobOKE ip sl (mkRawNatLit H)) pf
  logInfo m!"#e1gtop {ns}: {vs.size} blocks over {nJ} jobs of {tbl}; public {ns ++ `job} : JobOK … {H}"

elab "#e1pjob " ns:ident pb:str po:str pw:str pu:str ip:ident sl:ident ok:ident : command =>
  run ns.getId pb.getString po.getString pw.getString pu.getString ip.getId sl.getId ok.getId
elab "#e1pjobs " ns:ident pl:str ip:ident sl:ident ok:ident tbl:ident a:num : command =>
  runJobs ns.getId pl.getString ip.getId sl.getId ok.getId tbl.getId a.getNat
elab "#e1pagg " ns:ident pc:str ip:ident sl:ident tbl:ident : command =>
  runAgg ns.getId pc.getString ip.getId sl.getId tbl.getId
elab "#e1ptop " ns:ident pb:str po:str pw:str pu:str ip:ident sl:ident ok:ident tbl:ident nJ:num child:ident : command =>
  runTop ns.getId pb.getString po.getString pw.getString pu.getString ip.getId sl.getId ok.getId tbl.getId nJ.getNat child.getId

end E1PJob
