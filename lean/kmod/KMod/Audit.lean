module
public meta import Lean.Elab.Command
public meta import Lean.OriginalConstKind
public meta import Lean.Util.CollectAxioms
/-! # KMod.Audit: `#kax THM` (the per-module step of the compositional axiom audit) and `#kaxp THM` (plan §7a)

`#kax THM` runs inside the module that declares THM, at build time, while the module's private declarations are present.  It
walks THM's type and value through every constant OF THIS MODULE, following definition and theorem bodies (private ones
included).  Constants of other modules are not entered:
* `propext`, `Classical.choice`, `Quot.sound`: `KAX STD <c>`;
* an imported constant that was declared as an axiom (`getOriginalConstKind?`; e.g. `sorryAx`, `Lean.ofReduceBool`): `KAX BAD
  <c> <module>`;
* any other imported constant (a theorem, which importers see as an axiom, or a definition): `KAX OBL <module> <c>`, an
  obligation discharged by that module's own audit (a KMod child: its public theorem) or by the external walk of
  `kmod_audit.py` (vocabulary and core: `tools/KModExt.lean`, at the private level, through every body);
* an axiom of this module, or a missing constant: `KAX BAD <c>`.
Summary line: `KAXSUM THM visited=<n> std=<a> obl=<b> bad=<c> local_axioms=<d> ms=<t>`, where `local_axioms` counts every axiom
declared in this module, reachable or not.  Independent of Lean's axiom table.

`#k1top NAME [C₁, …]` (alias `#ktop`): the stand-in top: a public conjunction of the given theorems, then `#kax` and
`#print axioms` on it.

`#kaxp THM` is the second check: Lean's own `collectAxioms` (as `#print axioms`; imported declarations through the exported axiom
table), logged as `KAXP THM <axioms, comma-separated>`. -/
public meta section
open Lean Elab Command
namespace KMod

def stdAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

structure AuditOut where
  vis : NameSet := {}
  std : NameSet := {}
  obl : Std.HashMap Name Name := {}
  bad : Array String := #[]

def modName (env : Environment) (i : ModuleIdx) : Name := env.allImportedModuleNames[i.toNat]!

partial def walkMod (env : Environment) (c : Name) (st : IO.Ref AuditOut) : IO Unit := do
  if (← st.get).vis.contains c then return
  st.modify fun s => { s with vis := s.vis.insert c }
  match env.getModuleIdxFor? c with
  | some i =>
    if stdAxioms.contains c then st.modify fun s => { s with std := s.std.insert c }
    else
      let isAx : Bool := (match env.find? c with
        | some (.axiomInfo _) => (getOriginalConstKind? env c matches some .axiom)
        | _ => false)
      if isAx then st.modify fun s => { s with bad := s.bad.push s!"{c} {modName env i}" }
      else st.modify fun s => { s with obl := s.obl.insert c (modName env i) }
  | none =>
    match env.find? c with
    | none => st.modify fun s => { s with bad := s.bad.push s!"{c} missing" }
    | some (.axiomInfo _) => st.modify fun s => { s with bad := s.bad.push s!"{c} local" }
    | some ci =>
      for n in ci.type.getUsedConstants do walkMod env n st
      match ci.value? (allowOpaque := true) with
      | some v => for n in v.getUsedConstants do walkMod env n st
      | none => pure ()

/-- the per-module walk of THM, logged as `KAX` lines and the `KAXSUM` line -/
def runKAx (thm : Name) : CommandElabM Unit := do
  let env ← getEnv
  let st ← IO.mkRef ({} : AuditOut)
  let t0 ← IO.monoNanosNow
  walkMod env thm st
  let o ← st.get
  let loc : Nat := env.constants.map₂.foldl (fun (acc : Nat) _ ci => if ci matches .axiomInfo _ then acc + 1 else acc) 0
  let obl := o.obl.toArray.qsort (fun a b => a.2.lt b.2 || (a.2 == b.2 && a.1.lt b.1))
  let lines := (o.std.toArray.qsort Name.lt).map (fun c => s!"KAX STD {c}") ++ obl.map (fun (c, m) => s!"KAX OBL {m} {c}") ++
    o.bad.map (fun c => s!"KAX BAD {c}")
  let dt := ((← IO.monoNanosNow) - t0) / 1000000
  logInfo m!"{String.intercalate "\n" lines.toList}\nKAXSUM {thm} visited={o.vis.size} std={o.std.size} obl={obl.size} bad={o.bad.size} local_axioms={loc} ms={dt}"

/-- Lean's own axiom collection for THM (as `#print axioms`), logged as the `KAXP` line; with `printStyle` also the
`#print axioms` sentence -/
def runKAxP (thm : Name) (printStyle := false) : CommandElabM Unit := do
  let axs := (← collectAxioms thm).qsort Name.lt
  if printStyle then
    if axs.isEmpty then logInfo m!"'{thm}' does not depend on any axioms"
    else logInfo m!"'{thm}' depends on axioms: {axs.toList}"
  logInfo m!"KAXP {thm} {String.intercalate "," (axs.toList.map toString)}"

syntax (name := kaxCmd) "#kax " ident : command

@[command_elab kaxCmd] def elabKAx : CommandElab := fun stx => do
  runKAx (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1])

syntax (name := kaxpCmd) "#kaxp " ident : command

@[command_elab kaxpCmd] def elabKAxP : CommandElab := fun stx => do
  runKAxP (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1])

/-- `#k1top NAME [C₁, …, Cₙ]` (alias `#ktop`): the stand-in top of a slice.  In a module that imports the slice's top-level
modules: the PUBLIC theorem `NAME : T₁ ∧ (T₂ ∧ … Tₙ)` (Tᵢ the type of Cᵢ, each a Prop, right-nested) proved by `And.intro`, added
by a synchronous addDecl and logged as `KPUB`; then `#kax NAME` and `#print axioms NAME` (also as `KAXP`).  The name is taken
as written (no namespace prefix). -/
syntax (name := k1topCmd) ("#k1top " <|> "#ktop ") ident " [" ident,+ "]" : command

@[command_elab k1topCmd] def elabK1Top : CommandElab := fun stx => do
  let name := stx[1].getId
  let cs ← liftCoreM <| stx[3].getSepArgs.mapM realizeGlobalConstNoOverloadWithInfo
  let env ← getEnv
  let mut tys : Array Expr := #[]
  for c in cs do
    let some ci := env.find? c | throwError "#k1top: unknown constant {c}"
    unless ci.levelParams.isEmpty do throwError "#k1top: {c} is universe polymorphic"
    unless ← liftTermElabM (Meta.isProp ci.type) do throwError "#k1top: the type of {c} is not a proposition"
    tys := tys.push ci.type
  let n := cs.size
  let mut ty := tys[n - 1]!
  let mut pf := mkConst cs[n - 1]!
  for k in [0:n - 1] do
    let i := n - 2 - k
    pf := mkApp4 (mkConst ``And.intro) tys[i]! ty (mkConst cs[i]!) pf
    ty := mkApp2 (mkConst ``And) tys[i]! ty
  let t0 ← IO.monoNanosNow
  liftCoreM <| withOptions (Elab.async.set · false) <|
    addDecl (.thmDecl { name := name, levelParams := [], type := ty, value := pf })
  logInfo m!"KPUB {name} ms={((← IO.monoNanosNow) - t0) / 1000000} stmt_hash={ty.hash} conjuncts={n}"
  runKAx name
  runKAxP name (printStyle := true)

end KMod
