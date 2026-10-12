module
public meta import Lean
public import E1GK.ChainF
public import E1GK.ExtMono
public import RT.Load
public meta import E1GK.JobCmd3
public meta import KMod.Units
/-! # `#e1groot`: a context cap's root level (module form)

`#e1groot NS "blocks.bin" "of.bin" "wt.bin" "units.txt" IP SL OK TBL nJ CHILD`: the top chain from the IP's root (depth 0, so
`Lf 0 % 2 ^ 13 = 0`) to the job frontier, glued to the `nJ` jobs of the job table `TBL` (witness `n + k`), with the jobs from
the imported `CHILD : RangeOK (fun k => JobOK C sl UB (TBL.entry k)) 0 nJ` (the cap's root range), or its lifted form
`∀ E, ExtSub X E → …`.  `E1GS.enum_of_chain_fn` gives the canonical-point statement, public as

  `NS.root : ∀ x, Glob C x → (∀ i < 2 ^ 15, SlotV x (sl i)) → (∀ l < 127, x l ≤ E1G.fld UB l) → (∃ l < 127, 0 < x l) → False`

(`L479.EnumOK C sl UB` unfolded), over `C = IP.C`, or, when the child is lifted, over `withExt IP.C NS.EXT` with `NS.EXT` the
child's list (a literal copy: the cap's census list `EXT436`; `withExt IP.C E` is `{IP.C with EXT := E}`, the external-leaf tier's
`Cx E`).  The chain's blocks, glue and ranges are built as `E1GK.JobCmd3`'s chains (private declarations, KMod lines). -/
@[expose] public section
open Lean Elab Command Meta

namespace E1GRoot
open E1GJob3

meta def runRoot (ns : Name) (pb po pw pu : String) (ip sl ok tbl : Name) (nJ : Nat) (child : Name) : CommandElabM Unit := do
  let pv := mkPrivateName (← getEnv) ns
  let T := mkConst (tbl ++ `entry)
  let cx ← liftCoreM <| liftedX? child
  let cE ← match cx with
    | some X => do
        let vals ← liftTermElabM <| evalList X
        liftCoreM <| addExtList (ns ++ `EXT) (listLit vals)
        pure (withExtE ip (mkConst (ns ++ `EXT)))
    | none => pure (baseC ip)
  let (_, slE, UB, UBR) := ctxE ip sl cE
  let (vs, hblk, hgl) ← chainCore ns pv pb po pw pu ip sl cE nJ (some T)
  if vs[0]! % 2 ^ 13 != 0 then throwError "#e1groot: the chain's first block is not the IP's root"
  let Q := mkLambda `k BinderInfo.default natTy (jobOKE ip sl cE (mkApp T (mkBVar 0)))
  -- the child's range at this context (a lifted child at E := NS.EXT, the literal copy of its own list)
  let childR : Expr := match cx with
    | some X => mkAppN (mkConst child) #[mkConst (ns ++ `EXT), mkApp (mkConst ``E1GS.extSub_refl) X]
    | none => mkConst child
  let hjobs := mkAppN (mkConst ``E1GS.range_all) #[Q, mkRawNatLit nJ, childR]
  let nE := mkConst (pv ++ `n); let Lf := mkConst (pv ++ `Lf); let Jf := mkConst (pv ++ `Jf)
  -- `Lf 0 % 2 ^ 13 = 0` by evaluation (stated with `Nat.mod … 8192`; the kernel unfolds `%` and `2 ^ 13` to match)
  let lhs := mkApp2 (mkConst ``Nat.mod) (mkApp Lf (mkRawNatLit 0)) (mkRawNatLit 8192)
  let eq0 := mkApp3 (mkConst ``Eq [Level.one]) natTy lhs (mkRawNatLit 0)
  let hroot := mkApp3 (mkConst ``of_decide_eq_true) eq0 (mkApp2 (mkConst ``instDecidableEqNat) lhs (mkRawNatLit 0))
    (mkApp2 (mkConst ``Eq.refl [Level.one]) boolTy tru)
  let pf := mkAppN (mkConst ``E1GS.enum_of_chain_fn) #[cE, slE, UB, UBR, mkConst (ok ++ `UB_eq), mkConst (ok ++ `UBR_eq),
    mkConst (ok ++ `UB_le), nE, Lf, mkRawNatLit nJ, Jf, hneE nE, hroot, hblk, hgl, hjobs]
  let ty ← liftTermElabM do
    let t ← inferType pf
    instantiateMVars t
  KMod.addPub (ns ++ `root) ty pf
  logInfo m!"#e1groot {ns}: {vs.size} blocks over {nJ} jobs of {tbl}{if cx.isSome then m!", lifted over {ns ++ `EXT}" else m!""}; public {ns ++ `root}"

elab "#e1groot " ns:ident pb:str po:str pw:str pu:str ip:ident sl:ident ok:ident tbl:ident nJ:num child:ident : command =>
  runRoot ns.getId pb.getString po.getString pw.getString pu.getString ip.getId sl.getId ok.getId tbl.getId nJ.getNat child.getId

end E1GRoot
