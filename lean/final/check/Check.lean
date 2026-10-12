module
public import R22K.Final
public meta import Lean

#check @R22K.Final.rank_ge_23
#print Top.RankGe23
#print RootSound.IsDecomp
#print RootSound.M3
#print RootSound.F2
#print axioms R22K.Final.rank_ge_23
#print axioms R22K.Final.rank_eq_23
#print axioms R22K.Final.mm_equiv
#print axioms R22K.Final.table_23
#print axioms R22K.Final.recursive_23

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  IO.println s!"imported modules: {env.header.moduleNames.size}; imported constants: {env.constants.map₁.size}"
