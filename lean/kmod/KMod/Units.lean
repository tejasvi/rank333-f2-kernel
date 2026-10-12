module
public meta import Lean.Elab.Command
/-! # KMod.Units: unit groups, the public theorem, and the manifest lines of a KMod module (plan §7a)

A KMod module checks a group of units privately and exports ONE public theorem:

* `#kunits G "FILE" [K] (F)`: FILE is an `#e1lits`-format literal file (`u32 count`, then per literal `u32 nbytes` and the
  little-endian bytes); K is the arity (default 1); F : Nat → Bool is the checker, elaborated once.  For literal j a PRIVATE
  definition `G.L<j> : Nat` (the literal, `abbrev` hints) and for unit i a PRIVATE theorem
  `G.u<i> : (F G.L<Ki> && (F G.L<Ki+1> && … F G.L<Ki+K-1>)) = true` (right-nested; one conjunct when K = 1; the last unit takes
  the remaining literals), proved by `of_decide_eq_true _ _ rfl`, each its own synchronous `addDecl`, so the kernel checks
  every unit alone (measured +3% per unit against one declaration).  Records the group as private definitions `G.n` (the
  literal count), `G.k` (the arity) and `G.chk` (the checker).
* `#kpub THM : STMT := COMB G₁ … Gₘ`: the PUBLIC theorem `THM : STMT`, proved by the term `COMB STMT #[group G₁, …]`.  COMB is
  a constant of type `KMod.Combinator` from a `meta import`ed module (the emitter's: it turns the units into the statement,
  and may add private auxiliary declarations; `KMod.Comb` has generic pieces).  STMT is elaborated in exporting mode, so it
  can use only the public vocabulary; the proof may use everything.
* `#kpubterm THM : STMT := TERM`: the same with the proof as a term (aggregators, small modules).
* `#klits G "FILE"`: a data group: the PRIVATE literal definitions `G.L<j>` only, no units (arity 0), e.g. witness rows for a
  `#kdispatch`.  Manifest line `KLITS G lits=<n> data=<FILE> bytes=<b> hash=<h>`.
* `#kdispatch D G₁ … Gₘ`: the PRIVATE definition `D : Nat → Nat` with `D j ⇝` literal j of the concatenation of the groups'
  literals (a balanced `Bool.rec`/`Nat.ble` tree, O(log n) kernel steps per evaluation at a numeral).  Later commands can
  name `D` (a checker of a further group, e.g. glue checks `fun x => … D …`); combinators get it with `KMod.privConst \`D`.
* `#kkey FIRST LAST`, `#kext LABEL…`: manifest lines `KKEY FIRST LAST` (the key range the module covers) and `KEXT LABEL`
  (one per external leaf); bookkeeping only.

Manifest lines, one `logInfo` each (the build wrapper collects the `K…` lines of the build log into `<module>.kman`):
`KUNITS G lits=<n> arity=<K> units=<u> kernel_ms=<sum> max_unit_ms=<max> slowest=<i> data=<FILE> bytes=<b> hash=<h>`,
`KPUB THM ms=<kernel ms> stmt_hash=<h>`, `KDISPATCH D lits=<n> ms=<t>`, `KKEY …`, `KEXT …`.  With the environment variable `KMOD_UNIT_TIMES=<dir>`,
`#kunits` also writes the per-unit kernel times (µs, one per line) to `<dir>/<module>.<G>.utimes`.
All `addDecl` calls of this library are synchronous (`Elab.async` off locally); put `set_option Elab.async false` in the
module header anyway. -/
public meta section
open Lean Elab Command Meta
namespace KMod

def u32 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + 256 * (b.get! (i + 1)).toNat + 65536 * (b.get! (i + 2)).toNat + 16777216 * (b.get! (i + 3)).toNat

partial def natLE (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi - lo ≤ 64 then Id.run do
    let mut acc := 0
    let mut i := hi
    while i > lo do
      i := i - 1
      acc := acc * 256 + (b.get! i).toNat
    return acc
  else
    let mid := lo + (hi - lo) / 2
    natLE b lo mid + (natLE b mid hi <<< (8 * (mid - lo)))

/-- the literals of an `#e1lits`-format byte array -/
def parseLits (b : ByteArray) : Array Nat := Id.run do
  let cnt := u32 b 0
  let mut off := 4
  let mut out : Array Nat := Array.mkEmpty cnt
  for _ in [0:cnt] do
    let nb := u32 b off
    off := off + 4
    out := out.push (natLE b off (off + nb))
    off := off + nb
  return out

/-- a unit group of the current module -/
structure Group where
  name : Name
  arity : Nat
  /-- the private literal definitions `G.L<j>`, in file order -/
  lits : Array Name
  /-- the private unit theorems: `units[i] : (chk lits[K i] && (… && chk lits[K i + K - 1])) = true` -/
  units : Array Name
  /-- the checker `F : Nat → Bool` -/
  checker : Expr
  deriving Inhabited

/-- the units of literal range `[K i, min (K i + K) n)` -/
def Group.unitLits (g : Group) (i : Nat) : Array Name := g.lits.extract (g.arity * i) (g.arity * i + g.arity)

/-- an emitter's proof builder: the statement and the groups named in `#kpub` ↦ a proof of the statement -/
@[expose] abbrev Combinator := Expr → Array Group → MetaM Expr

def pname (env : Environment) (g : Name) (s : String) : Name := mkPrivateName env (g ++ Name.mkSimple s)

/-- add a declaration synchronously (kernel-checked before returning) -/
def addDeclSync (d : Declaration) : CoreM Unit := withOptions (Elab.async.set · false) (addDecl d)

/-- add a private `abbrev`-hinted definition -/
def addPrivDef (n : Name) (type value : Expr) : CoreM Unit :=
  addDeclSync (.defnDecl { name := n, levelParams := [], type := type, value := value, hints := .abbrev, safety := .safe })

/-- the group G of the current module, from its private record -/
def getGroup (g : Name) : CoreM Group := do
  let env ← getEnv
  let val (s : String) : CoreM Expr := do
    match env.find? (pname env g s) with
    | some (.defnInfo d) => pure d.value
    | _ => throwError "KMod: no unit group {g} in this module"
  let natv (s : String) : CoreM Nat := do
    match ← val s with
    | .lit (.natVal n) => pure n
    | _ => throwError "KMod: group {g}: {s} is not a literal"
  let n ← natv "n"
  let k ← natv "k"
  let chk ← val "chk"
  let nu := if k == 0 then 0 else (n + k - 1) / k
  return { name := g, arity := k, checker := chk,
           lits := (Array.range n).map (fun j => pname env g s!"L{j}"),
           units := (Array.range nu).map (fun i => pname env g s!"u{i}") }

/-- `F a && (F b && …)`, right-nested -/
def andChain (f : Expr) (ls : List Expr) : Expr :=
  match ls with
  | [] => mkConst ``Bool.true
  | [l] => (mkApp f l).headBeta
  | l :: rest => mkApp2 (mkConst ``and) (mkApp f l).headBeta (andChain f rest)

def boolEqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) e (mkConst ``Bool.true)

/-- the proof of `e = true` by evaluation: `of_decide_eq_true (instDecidableEqBool e true) rfl` -/
def decideProof (e : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) (boolEqTrue e) (mkApp2 (mkConst ``instDecidableEqBool) e (mkConst ``Bool.true))
    (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- ranges of at most this many literals are dispatched inline (a `Bool.rec` tree inside one definition) -/
def dispatchChunk : Nat := 8

/-- the inline dispatch over `lits[lo, hi)` on the bound variable #0 -/
partial def dispatchInline (lits : Array Expr) (lo hi : Nat) : Expr :=
  if hi - lo ≤ 1 then lits[lo]!
  else
    let mid := (lo + hi) / 2
    mkApp4 (mkConst ``Bool.rec [levelOne]) (mkLambda `_ .default (mkConst ``Bool) (mkConst ``Nat))
      (dispatchInline lits lo mid) (dispatchInline lits mid hi) (mkApp2 (mkConst ``Nat.ble) (mkRawNatLit mid) (mkBVar 0))

/-- the dispatch over `lits[lo, hi)` on #0: inline for at most `dispatchChunk` literals, else an application `n.d<lo>_<hi> #0` of a
new definition (added here, children first) whose body splits at the midpoint -/
partial def dispatchRange (n : Name) (lits : Array Expr) (lo hi : Nat) : CoreM Expr := do
  if hi - lo ≤ dispatchChunk then return dispatchInline lits lo hi
  let mid := (lo + hi) / 2
  let l ← dispatchRange n lits lo mid
  let r ← dispatchRange n lits mid hi
  let natTy := mkConst ``Nat
  let body := mkApp4 (mkConst ``Bool.rec [levelOne]) (mkLambda `_ .default (mkConst ``Bool) natTy) l r
    (mkApp2 (mkConst ``Nat.ble) (mkRawNatLit mid) (mkBVar 0))
  let m := n ++ Name.mkSimple s!"d{lo}_{hi}"
  let ty ← mkArrow natTy natTy
  addDeclSync (.defnDecl { name := m, levelParams := [], type := ty, value := mkLambda `i .default natTy body, hints := .abbrev, safety := .safe })
  return mkApp (mkConst m) (mkBVar 0)

/-- add the definition `n : Nat → Nat` with `n j ⇝ lits[j]` for `j < lits.size`: a balanced `Bool.rec`/`Nat.ble` tree, one small
definition per node above `dispatchChunk` literals (so one evaluation at a numeral costs O(log size) kernel steps; a single
lambda over the whole tree would cost O(size) per evaluation, as unfolding instantiates the whole body) -/
def addDispatch (n : Name) (lits : Array Name) : CoreM Expr := do
  if lits.isEmpty then throwError "KMod: dispatch {n} over no literals"
  let natTy := mkConst ``Nat
  let body ← dispatchRange n (lits.map mkConst) 0 lits.size
  let ty ← mkArrow natTy natTy
  addDeclSync (.defnDecl { name := n, levelParams := [], type := ty, value := mkLambda `i .default natTy body, hints := .abbrev, safety := .safe })
  return mkConst n

/-- the private constant `n` of this module (e.g. a `#kdispatch` function) -/
def privConst (n : Name) : CoreM Expr := do
  let pn := mkPrivateName (← getEnv) n
  unless (← getEnv).contains pn do throwError "KMod: no private constant {n} in this module"
  return mkConst pn

syntax (name := kunitsCmd) "#kunits " ident str (num)? term : command

@[command_elab kunitsCmd] def elabKUnits : CommandElab := fun stx => do
  let grp := stx[1].getId
  let path := stx[2].isStrLit?.getD ""
  let k := if stx[3].isNone then 1 else stx[3][0].isNatLit?.getD 1
  if k == 0 then throwError "#kunits: the arity must be positive"
  let bytes ← IO.FS.readBinFile path
  let lits := parseLits bytes
  if lits.isEmpty then throwError "#kunits: {path} has no literals"
  let f ← liftTermElabM do
    let e ← Term.elabTerm stx[4] (some (← mkArrow (mkConst ``Nat) (mkConst ``Bool)))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  if f.hasMVar || f.hasFVar then throwError "#kunits: the checker term has metavariables or free variables"
  let env0 ← getEnv
  for j in [0:lits.size] do
    liftCoreM <| addPrivDef (pname env0 grp s!"L{j}") (mkConst ``Nat) (mkRawNatLit lits[j]!)
  let nu := (lits.size + k - 1) / k
  let mut kern : Nat := 0
  let mut mx : Nat := 0
  let mut slow : Nat := 0
  let mut times : Array Nat := Array.mkEmpty nu
  for i in [0:nu] do
    let ls := ((List.range k).map (k * i + ·)).filter (· < lits.size) |>.map (fun j => mkConst (pname env0 grp s!"L{j}"))
    let e := andChain f ls
    let t0 ← IO.monoNanosNow
    liftCoreM <| addDeclSync (.thmDecl { name := pname env0 grp s!"u{i}", levelParams := [], type := boolEqTrue e,
                                         value := decideProof e })
    let dt := (← IO.monoNanosNow) - t0
    kern := kern + dt
    if dt > mx then mx := dt; slow := i
    times := times.push (dt / 1000)
  let natTy := mkConst ``Nat
  liftCoreM do
    addPrivDef (pname env0 grp "n") natTy (mkRawNatLit lits.size)
    addPrivDef (pname env0 grp "k") natTy (mkRawNatLit k)
    addPrivDef (pname env0 grp "chk") (← mkArrow natTy (mkConst ``Bool)) f
  if let some dir ← IO.getEnv "KMOD_UNIT_TIMES" then
    IO.FS.writeFile s!"{dir}/{env0.mainModule}.{grp}.utimes" (String.intercalate "\n" (times.toList.map toString) ++ "\n")
  logInfo m!"KUNITS {grp} lits={lits.size} arity={k} units={nu} kernel_ms={kern / 1000000} max_unit_ms={mx / 1000000} slowest={slow} data={path} bytes={bytes.size} hash={hash bytes}"

/-- add the public theorem `thm : stmt := pf` (synchronously kernel-checked) and log its manifest line -/
def addPub (thm : Name) (stmt pf : Expr) : CommandElabM Unit := do
  let t0 ← IO.monoNanosNow
  liftCoreM <| addDeclSync (.thmDecl { name := thm, levelParams := [], type := stmt, value := pf })
  logInfo m!"KPUB {thm} ms={((← IO.monoNanosNow) - t0) / 1000000} stmt_hash={stmt.hash}"

/-- elaborate a public statement: exporting mode, so private names are rejected -/
def elabStmt (s : Syntax) : CommandElabM Expr := liftTermElabM <| withExporting do
  let e ← Term.elabType s
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "#kpub: the statement has metavariables"
  return e

syntax (name := kpubCmd) "#kpub " ident " : " term " := " ident (ppSpace ident)* : command

@[command_elab kpubCmd] def elabKPub : CommandElab := fun stx => do
  let thm := stx[1].getId
  let stmt ← elabStmt stx[3]
  let cn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[5]
  let groups ← liftCoreM <| stx[6].getArgs.mapM (fun g => getGroup g.getId)
  let comb ← unsafe evalConstCheck Combinator ``KMod.Combinator cn
  let pf ← liftTermElabM <| withOptions (Elab.async.set · false) do
    let p ← comb stmt groups
    instantiateMVars p
  if pf.hasMVar || pf.hasFVar then throwError "#kpub: the combinator's proof has metavariables or free variables"
  addPub thm stmt pf

syntax (name := kpubtermCmd) "#kpubterm " ident " : " term " := " term : command

@[command_elab kpubtermCmd] def elabKPubTerm : CommandElab := fun stx => do
  let thm := stx[1].getId
  let stmt ← elabStmt stx[3]
  let pf ← liftTermElabM do
    let e ← Term.elabTermEnsuringType stx[5] (some stmt)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  if pf.hasMVar || pf.hasFVar then throwError "#kpubterm: the proof has metavariables or free variables"
  addPub thm stmt pf

syntax (name := klitsCmd) "#klits " ident str : command

@[command_elab klitsCmd] def elabKLits : CommandElab := fun stx => do
  let grp := stx[1].getId
  let path := stx[2].isStrLit?.getD ""
  let bytes ← IO.FS.readBinFile path
  let lits := parseLits bytes
  if lits.isEmpty then throwError "#klits: {path} has no literals"
  let env0 ← getEnv
  let natTy := mkConst ``Nat
  liftCoreM do
    for j in [0:lits.size] do
      addPrivDef (pname env0 grp s!"L{j}") natTy (mkRawNatLit lits[j]!)
    addPrivDef (pname env0 grp "n") natTy (mkRawNatLit lits.size)
    addPrivDef (pname env0 grp "k") natTy (mkRawNatLit 0)
    addPrivDef (pname env0 grp "chk") (← mkArrow natTy (mkConst ``Bool)) (mkLambda `_ .default natTy (mkConst ``Bool.true))
  logInfo m!"KLITS {grp} lits={lits.size} data={path} bytes={bytes.size} hash={hash bytes}"

syntax (name := kdispatchCmd) "#kdispatch " ident (ppSpace ident)+ : command

@[command_elab kdispatchCmd] def elabKDispatch : CommandElab := fun stx => do
  let n := stx[1].getId
  let groups ← liftCoreM <| stx[2].getArgs.mapM (fun g => getGroup g.getId)
  let lits := groups.flatMap (·.lits)
  let t0 ← IO.monoNanosNow
  discard <| liftCoreM <| addDispatch (mkPrivateName (← getEnv) n) lits
  logInfo m!"KDISPATCH {n} lits={lits.size} ms={((← IO.monoNanosNow) - t0) / 1000000}"

syntax (name := kkeyCmd) "#kkey " str str : command
@[command_elab kkeyCmd] def elabKKey : CommandElab := fun stx => do
  logInfo m!"KKEY {stx[1].isStrLit?.getD ""} {stx[2].isStrLit?.getD ""}"

syntax (name := kextCmd) "#kext " (str)+ : command
@[command_elab kextCmd] def elabKExt : CommandElab := fun stx => do
  let ls := stx[1].getArgs.map (fun s => s!"KEXT {s.isStrLit?.getD ""}")
  logInfo m!"{String.intercalate "\n" ls.toList}"

end KMod
