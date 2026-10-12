import Lean
/-! `lean --run KModExt.lean OBLFILE`: the external walk of the KMod audit (plan §7a).  OBLFILE has one obligation per line,
`<module> <constant>`: the constants that KMod modules use from non-KMod modules (vocabulary, Mathlib, core).  Imports all
those modules at the PRIVATE level (every body present) and walks each constant through types, values and constructors.  Every
axiom reached is `STD` (propext, Classical.choice, Quot.sound) or `BAD`; a constant missing from the environment is `BAD`.
Prints `EXT BAD <axiom> via <obligation>` lines, `EXT STD <axiom>` lines and
`EXTSUM obligations=<n> modules=<m> visited=<v> std=<s> bad=<b>`; exit status 0 iff bad = 0. -/
open Lean

partial def walk (env : Environment) (c : Name) (vis : IO.Ref NameSet) (axs : IO.Ref NameSet) (bad : IO.Ref (Array Name)) :
    IO Unit := do
  if (← vis.get).contains c then return
  vis.modify (·.insert c)
  match env.find? c with
  | none => bad.modify (·.push c)
  | some ci =>
    match ci with
    | .axiomInfo _ =>
      if c == ``propext || c == ``Classical.choice || c == ``Quot.sound then axs.modify (·.insert c)
      else bad.modify (·.push c)
    | .inductInfo v =>
      for n in ci.type.getUsedConstants do walk env n vis axs bad
      for n in v.ctors do walk env n vis axs bad
    | _ =>
      for n in ci.type.getUsedConstants do walk env n vis axs bad
      match ci.value? (allowOpaque := true) with
      | some v => for n in v.getUsedConstants do walk env n vis axs bad
      | none => pure ()

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let lines := (← IO.FS.lines args[0]!).filter (· ≠ "")
  let obl := lines.map fun l => match l.splitOn " " with
    | [m, c] => (m.toName, c.toName)
    | _ => (Name.anonymous, Name.anonymous)
  let mods := (obl.map (·.1)).foldl (fun (s : NameSet) m => s.insert m) {}
  let env ← importModules (mods.toArray.map fun m => { module := m }) {} (loadExts := true) (level := .private)
  let vis ← IO.mkRef ({} : NameSet); let axs ← IO.mkRef ({} : NameSet); let bad ← IO.mkRef (#[] : Array Name)
  let mut nbad := 0
  for (m, c) in obl do
    let b0 := (← bad.get).size
    walk env c vis axs bad
    let b := (← bad.get)
    for i in [b0:b.size] do IO.println s!"EXT BAD {b[i]!} via {m} {c}"
    nbad := b.size
  for a in (← axs.get).toArray.qsort Name.lt do IO.println s!"EXT STD {a}"
  IO.println s!"EXTSUM obligations={obl.size} modules={mods.size} visited={(← vis.get).size} std={(← axs.get).size} bad={nbad}"
  return if nbad == 0 then 0 else 2
