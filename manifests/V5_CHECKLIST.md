# V5: final census of the kernel-only build

Snapshot: snap-20261011T2103Z-f674b4e775a4 (`snapshot.json`).

Each item states a claim, the check that establishes it, and the pass criterion. The census command is `generators/pipeline/final/v5.py
--snapshot <dir>`. It reads one frozen snapshot of the queue (`snapshot.py`: the done listing with generations, the spec lines, the
superseded and parked ids, the gate lines) and the verification artifacts. It prints one PASS/FAIL line per item into
`V5_RESULT.txt`, whose first line names the snapshot. All counts in `V5_RESULT.txt`, `compute.tsv`, `census/` and `sample_check/`
come from that one snapshot (`snapshot.json`).

## A. The package set

- **A0. Sets.**
  - (a) The final set is R22K.Final's dependency DAG: the producers of the top-store modules in R22K.Final's exported import closure
    (`census/producers.tsv`), and, through the spec lines' `deps`, everything they build on.
  - (b) The done set is every done record that is not superseded. An id that has both a done record and a superseded record was
    rebuilt in place: the superseded record is its earlier build (another tarball), and the done record is the rebuild.
  - (c) The difference (b) − (a) is listed in `V5_SETS.tsv` with ids and reasons.
  - Pass: every package of (a) is done, and (b) equals the done listing.
- **A1. Completeness.** Every spec line is done or parked (a superseded or retired alternative). Every dependency of every gate line
  that is not itself parked is done.
- **A2. Per-package audit.** Every done record of (a) and of (b) has `audit.result == "PASS"`. A few packages finalized before the
  audit step was part of the worker; they pass the offline re-audit instead (the worker's own audit code and `kmod_audit.py`, plus
  the external walk with std = 3, bad = 0). The worker writes PASS only when both conditions hold:
  - every module has its manifest checks (`KPUB` ≥ 1, `KAXSUM bad=0 local_axioms=0` for each, no `KAX BAD`) or is a data table;
  - the compositional walk from the package roots finds no error.

## B. Integrity, one name one content, the modhash gate (`verify/verifier.py`)

- **B1. Integrity.** Each package's tarball sha256 equals its done record. Every `.olean`, `.olean.private`, `.olean.server` and `.ir`
  file is non-empty, carries the olean header of toolchain 4.30.0, and matches the package's `SHA256SUMS`. Every module built has
  its `.olean`.
- **B2. Own hashes.** Each module's recorded hash (`KMH` in its `.mhash`) equals the sha256 of the shipped `.olean`, and of the
  `.olean.private` when one is shipped.
- **B3. One name, one content.** No module name is produced by two packages with different content. No package module shadows a module
  on the final LEAN_PATH. The top store's conflict list is empty, or each entry is the same package built twice with byte-identical
  public parts (`resolve_conflicts.py`).
- **B4. Modhash gate.** Every recorded import (`KIMP`) resolves to its producing package (store import) or, through the final
  LEAN_PATH, to a file (closure import), with the same `.olean` hash. For `import all` imports it also has the same private hash.
- **B5. Pinned environment.** A sha256 manifest of every `.olean` and `.olean.private` under the final LEAN_PATH roots
  (`envmanifest.py`) is taken before the final build and re-checked after it: 0 changed, added or removed files.

## C. Axioms

- **C1. External walk at the private level.** The union of every package's external obligations is walked in batches with
  `KModExt.lean`, each batch importing its modules at the private level (`final/walk.py`). Every batch passes. The union of the
  standard axioms reported is a subset of {propext, Classical.choice, Quot.sound}. An obligation entry whose module has no current
  producer and is not on the final LEAN_PATH comes from a retired package's audit; it is excluded and listed
  (`audit/C1_excluded_retired.tsv`).
- **C2. Compositional audit of the top.** `kmod_audit.py --root R22K.Final` passes over the top store and the final LEAN_PATH: every
  reached module has `KPUB` and `KAXSUM bad=0 local_axioms=0`, and every lifted `NS.EXT` obligation occurs in a public statement.
  R22K.Final's own external obligations pass the private-level walk (`final_ext.py`). Summaries: `audit/kmod_audit_final.txt`,
  `audit/external_walk.txt`.
- **C3. Lean's axiom print.** `#print axioms` of the 5 public theorems of R22K.Final lists exactly propext, Classical.choice and
  Quot.sound. It runs in a module file that imports R22K.Final at the exported level, so it traverses R22K.Final's own declarations
  and the public parts of everything it imports. Proofs in the producers' private parts, which the storage policy deletes, are covered
  by C1, C2 and A2.
- **C4. No sorry, no compiler trust.** No file a package ships contains the names `sorryAx`, `ofReduceBool` or `trustCompiler`. The
  packages ship public parts only; their private parts are deleted after finalize, except the seeded sample. Private parts are covered
  by each module's build-time axiom census (A2) and by C1-C3, which report any such use as a non-standard axiom.
- **C5. One kernel.** Every done record with provenance names the same toolchain closure (one sha256).

## D. The final instance

- **D1.** The sha256 of `R22K/Final.lean` as built.
