# Verification

Each check below states its claim, how it is established, and its result; the result files are in `manifests/`.

## The final set

The final set is every package in the dependency graph of `R22K.Final`: 150,678 packages with 14,185,917 modules. All numbers in this file come from one snapshot of the package records, taken after the last build (`snap-20261011T2103Z-f674b4e775a4`). `manifests/packages.tsv.zst` has one row per package (id, tier, spec hash, generator and library hashes, module count, root modules with their `.olean` sha256, audit result). The per-module hashes are in the Zenodo record.

## Per-module and per-package checks

Every module is checked by the Lean kernel when it is built. Every module of this release runs `#kax` on its public theorem: the generated packages and the libraries under `lean/`. The resulting manifest records:
- the public theorems (`KPUB`);
- the leaf units with their kernel times (`KUNITS`);
- the audit summary (`KAXSUM`: bad constants and local axioms; both must be 0);
- the axioms (`KAXP`);
- the obligations into other modules (`OBL`).

A package passes its audit when all of the following hold:
- every module has its manifest checks, or is a data table whose private part is shipped for the external walk;
- the walk from the package's public theorems finds no error;
- every obligation into a module of the final set names a public theorem of that module, or an `NS.EXT` list that occurs in such a theorem's statement.

## The gate (V5)

| item | claim | result |
|---|---|---|
| A0 | the sets: the final set (the dependency graph of `R22K.Final`, 150,678 packages) and every finished, current package record (150,688); the 10 records outside the final set belong to an earlier split of one job that a later split replaces, and no package of the final set depends on them | PASS |
| A1 | the final set is complete: every dependency of every aggregation and of the final module is a package of the set | PASS: 0 missing |
| A2 | every package passed its audit | PASS: 150,678 of 150,678 in the final set (150,688 of 150,688 records), including 67 audited after their build with the same code |
| B1 | integrity: each package's archive matches its record; every `.olean`, `.olean.private`, `.olean.server` and `.ir` file is non-empty, has the Lean 4.30.0 header and no zero-filled tail, and matches the package's checksum list | PASS: 0 problems |
| B2 | each module's recorded own hash equals its shipped `.olean` (and `.olean.private` where shipped) | PASS: 0 problems |
| B3 | one name, one content: no module name is produced by two packages of the set with different content, and no package module shadows a module of the final environment | PASS: 0 problems |
| B4 | import hashes: every import recorded at build time resolves to its producer in the set (or to the final environment) with the same `.olean` hash; for `import all` imports the private part's hash agrees too | PASS: 0 problems |
| B5 | the final environment (frozen port, libraries, Mathlib, toolchain) is unchanged between its snapshot and the final build | PASS: 198,234 files, 0 changed |
| C1 | the private-level external walk over the union of all packages' external obligations finds only standard axioms | PASS: 5,008,518 of 5,010,509 obligation entries walked, no bad constant; axioms ⊆ {propext, Classical.choice, Quot.sound}. The 1,991 entries not walked point into modules that no package of the set produces and that are not in the final environment |
| C2 | the audit walk from `R22K.Final` passes | PASS: 20,470 modules reached; 979,280 external obligations; 707 of 707 `NS.EXT` obligations occur in a public statement |
| C3 | `#print axioms` on the five final theorems | PASS: each depends on exactly [propext, Classical.choice, Quot.sound]. `lean/final/check/check_closure.sh` reproduces this from the archived public `.olean` files |
| C4 | no `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` or `native_decide` auxiliary in any module | PASS: 0 hits over the modules of every package |
| C5 | one kernel: every package and the final module were checked by the same Lean 4.30.0 toolchain | PASS |
| D1 | the final module is the generated instance (sha256 `330f8a7b…`) | PASS |

**C3 and the census.**
- `#print axioms` reads the exported environment. That environment holds the final module's own proofs and the public parts of its imports; the package modules' private proof bodies are not archived (see below).
- The transitive statement is the composed census. Its parts:
  - the import closure of `R22K.Final`: 17,017 modules, each either the root of an audited package of the set or a module of the final environment (Lean, Mathlib, the frozen port, the libraries under `lean/`), with none uncovered;
  - the per-package audits (A2) below each root;
  - the import-hash gate (B4);
  - the private-level external walk (C1).
- The census, C2, C3 and C4 agree on {propext, Classical.choice, Quot.sound}.

## Negative controls

Each control ran through the production build and audit path, and each was rejected as required:

| planted defect | rejected by |
|---|---|
| a module whose public theorem rests on a private axiom | the module manifest check and the audit walk |
| a module built against a different import hash | the import-hash check (STALE) |
| a private body changed under an `import all` import, with the public part unchanged | the import-hash check (STALE and PRIVATE-CONFLICT) |
| a skipped canonical child in an equal-first-factor certificate | the kernel (type mismatch) |
| an `NS.EXT` obligation not in any public statement | the audit walk |

## Library sources edited for release

The shipped sources of 22 library modules differ from the production sources in comments and docstrings only; the edits remove absolute paths and process vocabulary:
- `lean/caseII`: KB.Agg, KB.AggR, KDK321.Batch321, KDK321.Flook and KDK.ItemK (`lean/caseII/DOCSTRING_EDITS.tsv`);
- `lean/cc` and `lean/final`: HC436.IP_c436, HC436.OK_c436_Base, G2.C303X_Lits, G2.C321X_Lits, R22K.FinalTop, R22K.FinalAll, R22K.Cap and eight S4 modules (CC422, CC436, CCLeaf, EqF, PlaneLift, PlaneW3, SatQ, SplitQ) (`lean/DOCSTRING_EDITS.tsv`);
- `lean/e1g`: E1GK.RootCmd and E1PQ.ChainF (`lean/e1g/OLEAN_SHA256_RELEASE`).

Rebuilt from the shipped sources, each of these modules has a public `.olean` and `.ir` equal to the production file, so no hash of the import closure changes. `lean/final/check/OleanCmp.lean` compares each rebuilt module with the production module part by part: `.olean`, `.olean.server` and `.olean.private`, 63 parts in all, since the production private parts of the three R22K modules are not kept.
- In every part, the constant names, the constants, the imports and the extra constant names are identical. Each constant (989,925 constant entries over the 63 parts) is compared through Lean's canonical serialization: name, level parameters, type, value and the rest of the declaration.
- The only data that differ are module docstrings (`moduleDocExt`, all 22 modules) and declaration docstrings (`docStringExt`, KB.Agg and S4.SatQ).

The per-part results are in `manifests/docstring_edits_check.tsv`.

## Independent re-check

When a package finalizes, a seeded 0.1% share of its modules' private parts (chosen by a hash of the module name) is archived before the private parts are deleted. Each sampled module was replayed by the Lean v4.30.0 toolchain's `leanchecker`, private bodies included, and its private part's sha256 was compared with the hash recorded at its build.

| sampled private parts | pass | fail | not checkable | in replaced packages (not replayed) |
|---|---|---|---|---|
| all 9,538 | 5,914 | 0 | 3,258 | 366 |
| the 9,165 in packages of the final set | 5,912 | 0 | 3,253 | 0 |

- **Pass:** the kernel replay succeeds and the hash matches.
- **Not checkable:** the module imports a sibling with `import all` whose private part was not kept.
- The pass and not-checkable counts of the two rows differ by the 7 sampled parts of the 10 records outside the final set (2 pass, 5 not checkable).

**Coverage.** The sample covers the tiers whose modules the scheduler builds directly: the E1 chains (c436, c422, held jobs and point), the class packages and the EXT packages, 9,136,832 modules of the final set. The packages of cases II, I and I13 (5,049,085 modules) build their modules with the case-II unit script. It deletes each module's private part as soon as the module's manifest is clean, before the package's finalize step draws the sample, so the sample holds no module of these packages. Like every module, they are covered by their kernel checks at build time, their audit records and the census (C1, C2, C4). In addition, they are re-checked by regeneration (below).

The per-sample results, with tiers, are in `manifests/sample_check/`; the passing private parts are in the Zenodo record (`private_sample_pass_01` to `_06`).

### Re-check of cases II, I and I13 by regeneration

The re-check is pre-registered in `manifests/sample_check/SAMPLE_CII.md`. The selection, procedure and criteria were fixed before any regeneration ran. Amendment 1 (before the runs) supplies three inputs; Amendment 2 records a stop and its resolution.
- **Selection:** a fixed seed picked 24 packages: 20 of the 18,110 case-II packages, the case-I package `I.321`, and 3 of the 80 case-I13 packages. In production they have 6,840 modules.
- **Regeneration:** the packages were regenerated from this repository and the Zenodo record, with every private part kept. Two further inputs: the case I/I13 search tables, which are files of the native release's Zenodo record; and, for the three I13 leaves, the production queue run's plan and segments, which are privately archived and not in this release (their sha256 are in `I13_RUN_ARCHIVE.sha256`).
- **Checks:**
  - every regenerated module was replayed by `leanchecker`, against a closure that holds every private part of the port, S4 and KMod builds;
  - its public `.olean` was compared with the production hash;
  - each package top's statement (KMod `KPUB` hash) was compared with production's.

| case | packages | regenerated modules | leanchecker pass / fail / not checkable | (a) byte-identical replay of production modules | (b) independent re-derivation of the same top statement (kernel-replayed) | (b), aggregation modules replayed at the exported level | top statement equal |
|---|---|---|---|---|---|---|---|
| II | 20 | 6,171 | 6,128 / 0 / 43 | 3 packages | 4 packages | 13 packages | 20 of 20 |
| I | 1 | 149 | 149 / 0 / 0 | 0 | 1 package | 0 | 1 of 1 |
| I13 | 3 | 113 | 113 / 0 / 0 | 3 packages | 0 | 0 | 3 of 3 |
| all | 24 | 6,433 | 6,390 / 0 / 43 | 6 packages, 503 modules | 5 packages, 576 modules | 13 packages, 5,354 modules | 24 of 24 |

- **(a) Byte-identical replay of production modules:** every regenerated public `.olean` equals the production file, and every module passes `leanchecker`. For the three I13 leaves this holds with the tool version recorded for them (below).
- **(b) Independent re-derivation of the same top statement, kernel-replayed:** every regenerated module, chunks and tops included, passes `leanchecker`, and the top's statement equals production's. The item modules differ in bytes, because a multi-item search package splits its items according to how the search distributes work.
- **(b), with the aggregation modules replayed at the exported level:** the 43 aggregation modules (chunks and tops) of the 13 large packages are not checkable by `leanchecker`. Its replay imports the private part of every item module of the package at once, 35 to 345 GB per package. For these packages:
  - every item module passes `leanchecker`;
  - each aggregation module was kernel-checked at its own build, with a clean audit record;
  - each aggregation module passes the kernel replay at the exported level (`lean/final/check/ExpReplay.lean`). This replays the module's own constants in the kernel against the public parts of its imports, the level at which the module system elaborated it.
  - The exported-level replay agrees with `leanchecker` on all 32 chunks and tops of the other packages. Every module kind of the large packages (items, chunks, tops) has instances that `leanchecker` replays in full in the other packages (`kinds.tsv`).
- **Byte identity overall:** 771 regenerated public `.olean` files equal production, 5,648 differ, and 14 have no production module of the same name.
- **Audit records:** bad constants and local axioms are 0 everywhere, and every axiom set lies within {propext, Classical.choice, Quot.sound}. The 53 harness retries (reruns after a process ran out of memory) are listed in the results and are not counted as results.
- **The I13 leaves:**
  - Their leaf-level comparison used the production queue run's plan, which is privately archived and not in this release. A fresh regeneration reproduces the I13 top statement `KMJJ.Top.vI` with its own item split, the same split-dependence as case II.
  - With the production plan, the 106 item modules are byte-identical to production.
  - The 7 chunks built with this repository's `mkaggf.py` differ by one deny-list line (Amendment 2). Built with the earlier `mkaggf.py` that produced them in production (`generators/caseII/CASE321_TOOLS.tsv`), they are byte-identical.
  - `OleanCmp.lean` finds all constants identical between the two builds; the files are in the Zenodo file `recheck_cii_i13_chunks.tar.zst`.
- **Results:** `manifests/sample_check/recheck_cii/` (`SUMMARY.md`, `modules.tsv.zst`, `packages.tsv`, `kinds.tsv`, `totals.json`).

`lean4checker`, `nanoda` and `lean4lean` were not run on the final closure. Replaying a module needs the private parts of all its imports, and the private parts of the package modules are not archived. A full independent replay regenerates them (REGENERATE.md).
