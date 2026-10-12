module
public import G2.Crown303
public import G2.Crown321
public import R1.Crown303
public import R1.Crown321
public meta import Lean
/-! # Statement check: `G2.Crown<c>.crown` is `E1NR1.Crown<c>.crown g<c>` (R22B.CapLeaf2 lines 247 and 253) without `g<c>`

`#g2stmt a b`: the type of `b` equals the type of `a` with its first binder dropped (`Expr` equality, binder names aside;
the first hypothesis must not occur in the rest), and the constants of `b`'s type with the modules they come from (one
environment, so one module per name). The `example`s check the drop-in with the kernel: with `g<c>` given, the two proofs
have the same type. -/
open Lean Elab Command Meta

elab "#g2stmt " a:ident b:ident : command => do
  let env ← getEnv
  let some ia := env.find? a.getId | throwError "unknown {a.getId}"
  let some ib := env.find? b.getId | throwError "unknown {b.getId}"
  match ia.type with
  | .forallE _ _ body _ =>
    if body.hasLooseBVars then throwError "the first binder of {a.getId} occurs in the rest"
    logInfo m!"G2STMT {a.getId} (first binder dropped) vs {b.getId}: equal={body == ib.type}"
    for c in ib.type.getUsedConstants do
      let m := (env.getModuleIdxFor? c).map (fun i => env.header.moduleNames[i.toNat]!)
      logInfo m!"G2CONST {c} {m}"
  | _ => throwError "{a.getId} is not a ∀"

#g2stmt E1NR1.Crown303.crown G2.Crown303.crown
#g2stmt E1NR1.Crown321.crown G2.Crown321.crown

example (g303 : R22N.CovG (E1N.keySW 640) (E1N.keyExtW 640) (E1N.CheckedW E1N.IP_e303.D 640) 0) :
    E1NR1.Crown303.crown g303 = G2.Crown303.crown := rfl
example (g321 : R22N.CovG (E1N.keySW 640) (E1N.keyExtW 640) (E1N.CheckedW E1N.IP_e321.D 640) 0) :
    E1NR1.Crown321.crown g321 = G2.Crown321.crown := rfl
