/-
OleanCmp.lean: compare one module's files from two build trees, part by part (.olean, .olean.server, .olean.private, as far as
both trees have them).

  lean --run OleanCmp.lean TMPDIR MODULE PRODUCTION_ROOT RELEASE_ROOT

For each part it reports whether the constant names, the constants (each ConstantInfo: name, level parameters, type, value and the
rest of the declaration, compared through Lean's canonical serialization), the imports and the extra constant names are identical,
and which environment-extension entries differ. VERIFICATION.md ("Library sources edited for release") gives the results for the
22 library modules whose shipped sources differ from the production sources in comments and docstrings.
-/
import Lean
open Lean

/-- The canonical serialization of `d`: Lean's own `.olean` writer applied to `d` alone. Two values serialize to the same bytes
exactly when their object graphs are equal. -/
def digestOf (tmp : System.FilePath) (d : ModuleData) : IO ByteArray := do
  saveModuleData tmp `Cmp d
  IO.FS.readBinFile tmp

def partNames : Array String := #["olean", "olean.server", "olean.private"]

def main (args : List String) : IO Unit := do
  -- args: TMPDIR MODULE PRODROOT RELROOT
  let tmp : System.FilePath := args[0]!
  let mod := args[1]!
  let prodRoot : System.FilePath := args[2]!
  let relRoot : System.FilePath := args[3]!
  let rel := (mod.replace "." "/")
  -- the parts present in both trees (a production private part may have been deleted after its audit)
  let mut nparts := 0
  for x in partNames do
    if (← (prodRoot / (rel ++ "." ++ x)).pathExists) && (← (relRoot / (rel ++ "." ++ x)).pathExists) then nparts := nparts + 1 else break
  let files (root : System.FilePath) : Array System.FilePath :=
    (partNames.extract 0 nparts).map fun x => root / (rel ++ "." ++ x)
  let p ← readModuleDataParts (files prodRoot)
  let r ← readModuleDataParts (files relRoot)
  for i in [0:nparts] do
    let some pp := p[i]? | continue
    let some rr := r[i]? | continue
    let dp := pp.1
    let dr := rr.1
    let sameNames := dp.constNames == dr.constNames
    let cP ← digestOf (tmp / "cp") { dp with imports := #[], extraConstNames := #[], entries := #[] }
    let cR ← digestOf (tmp / "cr") { dr with imports := #[], extraConstNames := #[], entries := #[] }
    let sameConsts := cP == cR
    let sameImports := dp.imports == dr.imports
    let sameExtra := dp.extraConstNames == dr.extraConstNames
    let extP := dp.entries.map (·.1)
    let extR := dr.entries.map (·.1)
    let mut diffs : Array String := #[]
    let mut nsame := 0
    for (n, es) in dp.entries do
      match dr.entries.find? (·.1 == n) with
      | none => diffs := diffs.push s!"{n}(only in production)"
      | some (_, es2) =>
        let a ← digestOf (tmp / "ep") { dp with imports := #[], constNames := #[], constants := #[], extraConstNames := #[], entries := #[(n, es)] }
        let b ← digestOf (tmp / "er") { dr with imports := #[], constNames := #[], constants := #[], extraConstNames := #[], entries := #[(n, es2)] }
        if a == b then nsame := nsame + 1 else diffs := diffs.push s!"{n}({es.size}/{es2.size} entries)"
    for n in extR do
      unless extP.contains n do diffs := diffs.push s!"{n}(only in release)"
    IO.println s!"{mod}\t{partNames.getD i ""}\tconstants={dp.constants.size}\tnames_equal={sameNames}\tconstants_identical={sameConsts}\timports_equal={sameImports}\textra_equal={sameExtra}\textensions={dp.entries.size}\textensions_identical={nsame}\textensions_differing={diffs.toList}"
