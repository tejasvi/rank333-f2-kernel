import Lean
/-! `lean --run OleanImports.lean LISTFILE OUT`: the import headers of built `.olean` files, read with `Lean.readModuleData` (the
header the importing `lean` process itself reads; nothing is taken from sources).  LISTFILE: one olean path per line.  OUT, per file:
`OLEAN <path> <isModule 0|1> <number of imports>` then one `IMP <module> <importAll 0|1> <isExported 0|1> <isMeta 0|1>` per import,
in header order; an unreadable file gives `ERR <path> <message>`.  Each file's compacted region is freed before the next one is read.
Used by modhash.py (one name, one content). -/
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [lf, out] := args | IO.eprintln "usage: lean --run OleanImports.lean LISTFILE OUT"; return 2
  let h ← IO.FS.Handle.mk out .write
  let mut nerr := 0
  for p in (← IO.FS.lines lf) do
    if p.isEmpty then continue
    try
      let (md, region) ← readModuleData p
      let b (x : Bool) : String := if x then "1" else "0"
      h.putStrLn s!"OLEAN {p} {b md.isModule} {md.imports.size}"
      for i in md.imports do
        h.putStrLn s!"IMP {i.module.toString false} {b i.importAll} {b i.isExported} {b i.isMeta}"
      region.free
    catch e =>
      nerr := nerr + 1
      h.putStrLn s!"ERR {p} {(toString e).replace "\n" " "}"
  h.flush
  return (if nerr == 0 then 0 else 1)
