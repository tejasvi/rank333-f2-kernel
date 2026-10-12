import Lean
open Lean
/-! `lean --run Closure.lean ROOT OUT`: the transitive import closure of module ROOT as Lean loads it at the exported level
(importModules, level exported, no extensions): one module name per line in OUT, plus the number of constants in the environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let root := args[0]!.toName
  let env ← importModules #[{ module := root }] {} (loadExts := false) (level := .exported)
  let mods := env.header.moduleNames
  IO.FS.writeFile args[1]! (String.intercalate "\n" (mods.toList.map toString) ++ "\n")
  IO.println s!"closure {mods.size} modules, {env.constants.fold (fun n _ _ => n + 1) 0} constants"
  return 0
