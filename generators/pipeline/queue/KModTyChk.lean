import Lean
/-! `lean --run KModTyChk.lean FILE`: the statement check of the KMod audit (kmod_audit.py).  FILE has lines `<module> <constant>
<theorem> …`: a KMod module, a constant of it that another module uses (e.g. a lifted range's external-leaf list `NS.EXT`), and the
module's public (KPUB) theorems.  Imports all the modules at the EXPORTED level (their private parts may be deleted; a theorem's
statement is public) and prints `TYOK <module> <constant> <theorem>` when the constant occurs in the statement (type) of one of
the theorems, else `TYFAIL <module> <constant>`.  Exit status 0 iff every line is TYOK. -/
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let lines := ((← IO.FS.lines args[0]!).filter (· ≠ "")).map (fun l => ((l.splitOn " ").filter (· ≠ "")).toArray)
  let mods := lines.foldl (fun (s : NameSet) l => s.insert l[0]!.toName) {}
  let env ← importModules (mods.toArray.map fun m => { module := m }) {} (loadExts := false) (level := .exported)
  let mut bad := 0
  for l in lines do
    let c := l[1]!.toName
    let mut hit : Option Name := none
    for t in l.extract 2 l.size do
      match env.find? t.toName with
      | some ci => if ci.type.getUsedConstants.contains c then hit := some t.toName
      | none => pure ()
    match hit with
    | some t => IO.println s!"TYOK {l[0]!} {c} {t}"
    | none => IO.println s!"TYFAIL {l[0]!} {c}"; bad := bad + 1
  return if bad == 0 then 0 else 2
