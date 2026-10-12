module
public import R22K.FinalAll
public import KC.h473_Class
public import NDX.h473.Top
public meta import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 100000   -- as R22K.Final (mkinst.py)
/-! CHECK ONLY (py/mkmatchk.py): class h473's root against R22K.FinalAll -/
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
  let e := mkConst `KC.h473.EXT
  report "kc473 ← KC.h473.classLB (e473 := KC.h473.EXT)" (← binderTy `kc473 [(`e473, e)]) (← inferType (mkConst `KC.h473.classLB))
  report "x473 ← NDX.h473.x473 (e473 := KC.h473.EXT)" (← binderTy `x473 [(`e473, e)]) (← inferType (mkConst `NDX.h473.x473))
#ftmatchk
#check (R22K.FinalAll.rank_ge_23_of (e473 := KC.h473.EXT) (kc473 := KC.h473.classLB) (x473 := NDX.h473.x473))
