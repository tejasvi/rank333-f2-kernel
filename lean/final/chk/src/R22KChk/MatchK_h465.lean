module
public import R22K.FinalAll
public import KC.h465_Class
public import NDX.h465.Top
public meta import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 100000   -- as R22K.Final (mkinst.py)
/-! CHECK ONLY (py/mkmatchk.py): class h465's root against R22K.FinalAll -/
/-- the type of binder `bn` of `R22K.FinalAll.rank_ge_23_of`, the binders in `subst` replaced (chk/Match.lean's binderTy) -/
meta def binderTy (bn : Name) (subst : List (Name × Expr)) : MetaM Expr := do
  let ci ← getConstInfo `R22K.FinalAll.rank_ge_23_of
  forallTelescope ci.type fun xs _ => do
    let decls ← xs.mapM (fun x => x.fvarId!.getDecl)
    let some i := decls.findIdx? (·.userName == bn) | throwError "no binder {bn}"
    let mut t := decls[i]!.type
    for (n, v) in subst do
      let some j := decls.findIdx? (·.userName == n) | throwError "no binder {n}"
      t := t.replaceFVar xs[j]! v
    if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then throwError "binder {bn}: type depends on binders not substituted"
    return t
meta def report (label : String) (a b : Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  let r ← if a == b then pure "EXPR-EQUAL" else do
    if (← withTransparency .all (isDefEq a b)) then pure "DEFEQ" else pure "MISMATCH"
  logInfo m!"FTCHK {label} {r}"

elab "#ftmatchk" : command => liftTermElabM do
  let e := mkConst `KC.h465.EXT
  report "kc465 ← KC.h465.classLB (e465 := KC.h465.EXT)" (← binderTy `kc465 [(`e465, e)]) (← inferType (mkConst `KC.h465.classLB))
  report "x465 ← NDX.h465.x465 (e465 := KC.h465.EXT)" (← binderTy `x465 [(`e465, e)]) (← inferType (mkConst `NDX.h465.x465))
#ftmatchk
#check (R22K.FinalAll.rank_ge_23_of (e465 := KC.h465.EXT) (kc465 := KC.h465.classLB) (x465 := NDX.h465.x465))
