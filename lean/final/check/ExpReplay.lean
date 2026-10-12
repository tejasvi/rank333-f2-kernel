/-
ExpReplay.lean: kernel replay of a module's own constants against its imports at the exported level.

  PATH=<toolchain>/bin:$PATH LEAN_PATH=<roots> lean --run ExpReplay.lean MODULE...

`leanchecker` (the toolchain's LeanChecker.lean, `replayFromImports`) loads a module's whole import closure at the private level, so
it needs the private part of every imported module. This tool loads the imports at the exported level, the level at which the
module system elaborated the module (public parts of ordinary imports; private parts only of `import all` imports), and then replays
the module's own constants, read from its private part, with `Environment.replay`, which sends each of them to the kernel. It needs
the module's own private part. VERIFICATION.md says where it is used and how it was cross-validated against `leanchecker`.
-/
import Lean
open Lean

/-- Kernel replay of one module's own constants (from its most private part) into the environment of its imports at the
exported level, the level at which the module system elaborated it: public parts of ordinary imports, private parts only for
`import all`. -/
unsafe def replayExported (module : Name) : IO Nat := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  let some (mod, _) := parts[0]? | throw <| IO.userError "failed to read module data"
  let some (last, _) := parts[parts.size - 1]? | throw <| IO.userError "failed to read module data"
  unless parts.size = 3 do throw <| IO.userError s!"private part of {module} not found"
  let (_, s) ← (importModulesCore mod.imports (globalLevel := .exported)).run
  let env ← finalizeImport s mod.imports {} 0 false false (level := .exported) (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for name in last.constNames, ci in last.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions
  return newConstants.size

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut rc : UInt32 := 0
  for a in args do
    let m := a.toName
    try
      let n ← replayExported m
      IO.println s!"{m}\tPASS\t{n} constants"
    catch e =>
      IO.println s!"{m}\tFAIL\t{e}"
      rc := 1
  return rc
