# Pre-registered re-check of the case II, I and I13 packages: results

Pre-registration: `manifests/sample_check/SAMPLE_CII.md`, registered 2026-10-11 23:59Z (sha256 `9d108df2b80727a09ffe7a084144e287340724a9efe45f810ee354ba15a043f5`), with Amendment 1 (00:12Z, before any regeneration ran: gen7c, the case-I/I13 tables, the I13 split; file sha256 `0915d56c9efa0d939c83be2a7aabaa11849f8f8b385ac65bd530cfe020938c5f`) and Amendment 2 (02:34Z: the stop on the I13 chunks and its resolution; file sha256 `fbdb60543d336a0a529bc0ab873c060aef28158e463d9ed3aab26ef99aadc999`). Selection as registered: 24 packages, 6,840 production modules.

## Outcome

- One failure condition fired, and was resolved before the run resumed (Amendment 2): the 7 chunks of the three same-split I13 leaves differ in bytes from production. They differ by one source line that this repository's `py/mkaggf.py` writes; built from the production chunk sources they are byte-identical to production (see "The I13 chunks and the deny-list line").
- No other failure condition is met. No module is rejected by the kernel replay: 6,390 replays of the counting runs pass and 0 fail, and the 14 replays of the I13 confirmation rebuilds (7 chunks, two builds) pass too. Every KMod audit record has bad 0 and local_axioms 0. Every recorded axiom set is within {propext, Classical.choice, Quot.sound}. All 24 package tops have the production statement (KPUB statement hash).
- Replay coverage: 6,390 of 6,433 regenerated modules are replayed by the toolchain's `leanchecker` with every private part present. 43 are not checkable, all of them aggregation modules (chunks and tops) of the 13 large packages, whose replay needs the private parts of every item module of the package at once (see "Not checkable, per package"). 43 of these 43 pass the kernel replay at the exported level.
- Byte identity: 771 regenerated public `.olean` files equal the production files, 5,648 differ and 14 have no production module of the same name. The differing modules are item modules of multi-item search packages, whose item split depends on how the search hands out work, and the aggregation modules above them; and the 7 chunks of the three I13 leaves, which are byte-identical to production when built from the production chunk sources (see "The I13 chunks and the deny-list line").
- Evidence per package: (a) byte-identical replay of production modules for 6 packages, (b) independent re-derivation of the same top statement, kernel-replayed, for 5, and (b) with the aggregation modules not replayed by `leanchecker` for 13.

## Results per package

| case | package | production modules | regenerated modules | leanchecker pass / fail / not checkable | exported-level replay pass (aggregation modules) | .olean identical / differs / no production module | top statement equal | evidence |
|---|---|---|---|---|---|---|---|---|
| II | `II.KM2P000181` | 226 | 175 | 172 / 0 / 3 | 3 | 5 / 170 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P000195` | 238 | 237 | 234 / 0 / 3 | 3 | 25 / 212 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P001217` | 1,505 | 1,464 | 1,461 / 0 / 3 | 3 | 152 / 1,312 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P001917` | 132 | 126 | 126 / 0 / 0 | 3 | 2 / 124 / 0 | yes | (b) |
| II | `II.KM2P002742` | 484 | 454 | 450 / 0 / 4 | 4 | 1 / 453 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P002866` | 304 | 261 | 258 / 0 / 3 | 3 | 0 / 261 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P005680` | 338 | 234 | 231 / 0 / 3 | 3 | 0 / 234 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P005847` | 253 | 236 | 233 / 0 / 3 | 3 | 11 / 225 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P006552` | 230 | 204 | 201 / 0 / 3 | 3 | 5 / 199 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P006811` | 188 | 183 | 180 / 0 / 3 | 3 | 5 / 178 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P007638` | 202 | 176 | 173 / 0 / 3 | 3 | 3 / 173 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2P009791` | 90 | 90 | 90 / 0 / 0 | 3 | 90 / 0 / 0 | yes | (a) |
| II | `II.KM2P010636` | 282 | 282 | 282 / 0 / 0 | 3 | 282 / 0 / 0 | yes | (a) |
| II | `II.KM2P010915` | 18 | 18 | 18 / 0 / 0 | 2 | 18 / 0 / 0 | yes | (a) |
| II | `II.KM2X001188` | 751 | 743 | 738 / 0 / 5 | 5 | 10 / 733 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2X003814` | 50 | 52 | 52 / 0 / 0 | 3 | 5 / 45 / 2 | yes | (b) |
| II | `II.KM2X004859` | 102 | 108 | 108 / 0 / 0 | 3 | 24 / 78 / 6 | yes | (b) |
| II | `II.KM2X006668` | 706 | 672 | 668 / 0 / 4 | 4 | 9 / 663 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| II | `II.KM2X007307` | 151 | 141 | 141 / 0 / 0 | 3 | 2 / 139 / 0 | yes | (b) |
| II | `II.KM2X007552` | 328 | 315 | 312 / 0 / 3 | 3 | 14 / 301 / 0 | yes | (b), aggregation modules not replayed by leanchecker |
| I | `I.321` | 149 | 149 | 149 / 0 / 0 | 5 | 2 / 141 / 6 | yes | (b) |
| I13 | `I13.L028` | 68 | 68 | 68 / 0 / 0 | 3 | 65 / 3 / 0 | yes | (a) (I13 chunks: see below) |
| I13 | `I13.L034` | 18 | 18 | 18 / 0 / 0 | 2 | 16 / 2 / 0 | yes | (a) (I13 chunks: see below) |
| I13 | `I13.L048` | 27 | 27 | 27 / 0 / 0 | 2 | 25 / 2 / 0 | yes | (a) (I13 chunks: see below) |
| II | **total (20 packages)** | 6,578 | 6,171 | 6,128 / 0 / 43 | 63 | 663 / 5,500 / 8 | 20 of 20 | (a) 3, (b) 4, (b) with aggregation modules not replayed 13 |
| I | **total (1 packages)** | 149 | 149 | 149 / 0 / 0 | 5 | 2 / 141 / 6 | 1 of 1 | (a) 0, (b) 1, (b) with aggregation modules not replayed 0 |
| I13 | **total (3 packages)** | 113 | 113 | 113 / 0 / 0 | 7 | 106 / 7 / 0 | 3 of 3 | (a) 3, (b) 0, (b) with aggregation modules not replayed 0 |
| all | **total (24 packages)** | 6,840 | 6,433 | 6,390 / 0 / 43 | 75 | 771 / 5,648 / 14 | 24 of 24 | (a) 6, (b) 5, (b) with aggregation modules not replayed 13 |

The exported-level column counts every chunk and top replayed by `ExpReplay.lean`: in the re-run packages these replays cross-validate the tool against `leanchecker` (all 32 chunk and top modules of the re-run packages pass both); in the large packages they are the replay of the aggregation modules that `leanchecker` cannot check.

## The kinds of evidence

- **(a) Byte-identical replay of production modules:** 6 packages, 503 modules: every regenerated public `.olean` equals the production file (for the three I13 leaves, with the chunks built from the production chunk sources), and every module is replayed by `leanchecker` with every private part present. `II.KM2P009791`, `II.KM2P010636`, `II.KM2P010915`, `I13.L028`, `I13.L034`, `I13.L048`.
- **(b) Independent re-derivation of the same top statement, kernel-replayed:** 5 packages, 576 modules: every regenerated module, chunks and tops included, passes `leanchecker`, and the top's KPUB statement hash equals production's, while item modules differ in bytes. `II.KM2P001917`, `II.KM2X003814`, `II.KM2X004859`, `II.KM2X007307`, `I.321`.
- **(b) with the aggregation modules not replayed by `leanchecker` (the large packages):** 13 packages, 5,354 modules: every item module passes `leanchecker`; the top's KPUB statement hash equals production's; the 43 chunk and top modules are not checkable by `leanchecker` (reason below), each was kernel-checked at its own build (lean exit 0) with a clean KMod audit record, and 43 of them pass the kernel replay at the exported level. `II.KM2P000181`, `II.KM2P000195`, `II.KM2P001217`, `II.KM2P002742`, `II.KM2P002866`, `II.KM2P005680`, `II.KM2P005847`, `II.KM2P006552`, `II.KM2P006811`, `II.KM2P007638`, `II.KM2X001188`, `II.KM2X006668`, `II.KM2X007552`.

## The I13 chunks and the deny-list line

In the counting run all 106 item modules of the three I13 leaves are byte-identical to production, and their 7 chunks differ. The chunk sources that this repository's `py/mkaggf.py` writes differ from the production chunk sources by one line,

```
run_cmd Lean.modifyEnv (Lean.LibrarySuggestions.typePrefixDenyListExt.addEntry · `R22N.AllL)
```

which adds an entry to the library-suggestion deny list (an environment extension) and adds no constant. The production I13 packages were emitted by the earlier `mkaggf.py`, which does not write this line (PART.md, Tool versions). With the line left out, the release's chunk sources are byte-identical to the production chunk sources (`i13_chunks/sources/`, `i13_chunks/sources.sha256`).

The chunks were rebuilt twice against the regenerated item modules, every private part kept. Built from the production chunk sources, all 7 are byte-identical to production (`.olean` and `.olean.server`) and pass `leanchecker`. Built from the release's chunk sources, all 7 are byte-identical to the counting run's chunks (`.olean` and `.olean.private`) and pass `leanchecker`. The three leaves therefore count as evidence (a), with the tool version recorded for them: the earlier `mkaggf.py` (`generators/caseII/CASE321_TOOLS.tsv`).

`i13_chunks/oleancmp_prod_vs_release.tsv` compares each production chunk with the chunk built from the release's chunk sources (`lean/final/check/OleanCmp.lean`). In both the `.olean` and the `.olean.server` part, the constants, their names, the imports and the extra data are identical. The differing environment-extension entries are the deny-list entry (`typePrefixDenyListExt`, present only in the release build), the two library-suggestion indexes computed from the module (`symbolFrequency`, `sineQueNon`), and in the server part the module-docstring entry (`moduleDocExt`).

| chunk | counting run (release chunk sources) vs production | production chunk sources vs production | leanchecker, both builds |
|---|---|---|---|
| `KMJL028.A0` | differs | identical | pass, pass |
| `KMJL028.A1` | differs | identical | pass, pass |
| `KMJL028.A2` | differs | identical | pass, pass |
| `KMJL034.A0` | differs | identical | pass, pass |
| `KMJL034.A1` | differs | identical | pass, pass |
| `KMJL048.A0` | differs | identical | pass, pass |
| `KMJL048.A1` | differs | identical | pass, pass |

Files: `i13_chunks/prod/` holds the production chunk files (`.olean`, `.olean.server`, `.kman`; production keeps no `.olean.private`), `i13_chunks/regen_prodsrc/` the chunks built from the production chunk sources, and `i13_chunks/regen_release/` those built from the release's chunk sources (`.olean`, `.olean.server`, `.olean.private`, `.kman`), each tree with its own sha256 list. In `modules.tsv` the chunks built from the production chunk sources are the rows of run "production chunk sources".

## Module kinds

Every module kind that occurs in the large packages has instances in the re-run packages that `leanchecker` replays in full:

| module kind | in the large packages | replayed by leanchecker there | replayed at the exported level there | in the re-run packages | replayed by leanchecker there |
|---|---|---|---|---|---|
| item | 5,311 | 5,311 | 0 | 1,046 | 1,046 |
| dead-root item | 0 | 0 | 0 | 1 | 1 |
| aggregation (chunk) | 30 | 0 | 30 | 24 | 24 |
| top | 13 | 0 | 13 | 8 | 8 |

## Not checkable, per package

- `II.KM2P000181`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 48 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P000195`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 54 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P001217`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 345 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P002742`: 4 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 98 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 4 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P002866`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 56 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P005680`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 122 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P005847`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 37 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P006552`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 61 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P006811`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 45 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2P007638`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 44 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.
- `II.KM2X001188`: 5 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 89 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 5 pass, 0 fail; top statement equal to production: yes.
- `II.KM2X006668`: 4 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 100 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 4 pass, 0 fail; top statement equal to production: yes.
- `II.KM2X007552`: 3 aggregation modules (chunks and top) not checkable: imported item private parts not kept: package total 35 GB. Each was kernel-checked at its build (lean exit 0) with a clean KMod audit record; exported-level kernel replay: 3 pass, 0 fail; top statement equal to production: yes.

`leanchecker` (the toolchain's `LeanChecker.lean`, `replayFromImports`) imports the module's whole import closure at the private level and needs every imported module's private part. A chunk or top imports every item module of its package, whose private parts total the figure given per package; they could not be held at once on the machines' disks, so each item module's private part was deleted after its own replay passed (its sha256 is recorded in `modules.tsv`). The exported-level replay (`ExpReplay.lean`) loads the imports at the exported level, the level at which the module system elaborated the module, and replays the module's own constants from its private part; it was cross-validated against `leanchecker` on the re-run packages' chunks and tops (all 32 chunk and top modules of the re-run packages pass both).

## Harness incidents (not results)

Harness retries are reruns after a build or replay process failed for want of memory; they are listed in `modules.tsv` (column harness_retries, 53 in all) and are never counted as replay results. m1 to m5 are the five build machines (column machine of `modules.tsv`).

| time (UTC, 2026-10-12) | machine | what happened | what was rerun |
|---|---|---|---|
| 00:23-00:42 | m1 | Replays under a 32 GiB address-space cap stopped with "INTERNAL PANIC: out of memory" (18 replays); a launch burst under the 128 GiB cap stopped 33 replays with "GNU MP: Cannot allocate memory". | All 51 replays, with the 128 GiB cap and paced launches. |
| 00:36-00:42 | m1 | Scheduler restarts ended unit builds whose output went to the scheduler (KM2P005680.I229, KM2P006552.I53 and others in flight). | The units; job output goes to files since. |
| 01:03-01:06 | m2 | After a memory-budget increase the machine ran out of memory; the kernel killed sshd and Lean processes, among them the replay of KM2P001217.I5 (rc -9). | The killed builds and replays. |
| 01:20-01:24 | m4 | Out of memory after a budget increase: the kernel killed builds (KM2P001217.I30, KM2P001217.I62, rc 137), sshd, and then the remaining jobs. | All jobs of the machine. |
| 01:22-01:31 | m3 | Out of memory after a budget increase; the machine was reset at 01:30:38 (disk kept). | All jobs of the machine. |
| 01:24 | m2 | The out-of-memory handler killed the scheduler process; its running jobs were adopted or rerun. | The jobs without a recorded result. |
| 01:30-01:37 | m1 | KM2P005680.A0 aborted at build with std::bad_alloc under the 64 GiB address-space cap while its items' private parts were present (kept for their replays). | The build, after the items' replays (aggregation builds wait for them since). |
| 02:23 | m1 | The confirmation rebuild of the I13 chunks failed at its first build attempt (lean: "object file … does not exist"): each variant's store held only the chunk directory, and Lean resolves a module root to the first search-path entry that has its directory. | The 14 chunk builds, with the item modules and the chunks in one store per variant. |
| 02:26 | m1 | The confirmation run's first leanchecker step did not start a replay ("could not execute external process 'lean'": the toolchain's bin directory was not on PATH). | The 14 replays. |

## Inputs and harness

- This repository: `lean/caseII` (library sources, build script, build order), `generators/caseII` (search sources and `build.sh`, the emitter bundle, the tools, `case321`), `inputs/caseII` (job tables, package specs, the case-I frontier), `generators/e1g/cpp/gen7.h`.
- This record (Zenodo): `caseII_lib_data.tar.zst` (the library's data), `caseII_cc436_422.tar.zst` (the CC tables), `packages_modules.tsv.zst` (the production public `.olean` hashes).
- The native release's Zenodo record (10.5281/zenodo.23236154), files checked by sha256: `data/tables/tab_C3eD.bin` 349056a0…, `data/tables/kept_C3eDc4d.txt` e424ea8d…, `data/tables/C3eD_321.c2t` ce58f101…, `data/tables/kept3eD_lab321.bin` f55cb1a4…, `data/tables/frontier_d1_321.txt` 4d41cbf5…, `data/lean/46cc737594e4597c5185c50c1513fb11/kept3eD.bin` a43a3aa3…; `hyp7_321.bin` is a file byte-identical to the record's `data/lean/057c18088377951db54aaf82089d3d6e/hyp7_321.bin` (sha256 47c3e483…).
- The frozen port: `src/Top/Root321.lean` (md5 e90210e5…, listed in its `MANIFEST_FULL.md5`), from which `py/kitem.py` reads the 321 key table for cases I and I13.
- The production closure for what it provides (port, S4, KMod, Mathlib and the v4.30.0 toolchain), including every private part of the port, S4 and KMod builds. The closure tree is the same on all five machines: 25,655 files, sha256 of its file manifest `18d9bf9fda61f288c4345fa6ac1b7783878aa0699a96dc320180d14800b3d995`; its public `.olean` files equal the production closure's (4,333 port files and the S4 and KMod files compared).
- For the three I13 leaves: the production I13 queue run's plan (`plan.txt`, sha256 b9fec4f5907e3ea7c8d985cfdc1cb9a424f9145a2ef403ad517d40f8d3e1ad7d), header (`hdr_I13W.r3`, 0f2dd25a…) and 48 segment files, privately archived; the sha256 of every file is in `I13_RUN_ARCHIVE.sha256`.
- Binaries built from this repository's sources: `prof7R3q_b12d` from `src_b12/` (sha256 b90cc247…), `prof7R3q_b14` (0fba0f33…), `r3qglue` (5d82fdcc…, byte-identical to the production binary), `gen7c` from `src/gen7c/gen7c.cc` with `generators/e1g/cpp/gen7.h` (a19c4072…).
- Every module is built by the package's own `kmod_unit.sh` with `KMOD_KEEP_PRIVATE=1` (RLIMIT_AS 64 GiB, nice 10) and replayed by `leanchecker <module>` (Lean v4.30.0 toolchain) with the module's private part present (RLIMIT_AS 128 GiB). After a passing replay the private part's sha256 is recorded and the file is deleted (disk); no package module imports a sibling with `import all`.
- For the confirmation rebuild of the three I13 leaves' chunks: the production chunk sources (`i13_chunks/sources/production/`), which equal the chunk sources written by this repository's `py/mkaggf.py` with its deny-list line left out (`i13_chunks/sources/release/`).

## Checks before the runs

- Library: the 89 modules rebuilt from `lean/caseII` and the Zenodo data match `OLEANS.sha256` in 351 of 356 files; the 5 others are exactly the `DOCSTRING_EDITS.tsv` rows, and their hashes equal the table's 'new' column.
- Package specs: the 20 case-II kits regenerated by `tools/mkpkgcc.py` (`8e4 1e30` for `jobs_cc.txt`, `PKG_PREFIX=KM2X` and `3e5` for `jobs_x.txt`) have `spec.json` equal to `PACKAGES_KM2`'s `spec_json_sha256`.
- gen7c: on the 834 profile leaves of 124 calls made while converting `KM2P010915.I0`, the release-built `gen7c` and the production `gen7c` (sha256 a2777304…) give identical certificates, bit counts and node counts (the 4th output field, the generator's run time in µs, excluded).
- I13: `tools/case321/splitrun.py` on the production plan gives the production leaf partition: `parts.json` identical (80 parts), and the plans of L028, L034 and L048 identical; the three leaves have 68, 18 and 27 units, as in production.
- I.321: a fresh case-I queue run (`w321.sh FLAGS_IW`, jobs 0 and 1, `prof7R3q_b14` from this repository; plan sha256 d4209b4d15e292d3ebb057bf2908b779ecfa6875fd0229f2bb95ffc4c71a76ec): AUDIT OK, 1,080 items (production: 864), 0 conversion failures, 0 key mismatches; `mkstage321.sh KMIA 0 12` with MAXS 60 and FANIN 400, and `mkpkg2.py`, give 149 units with 4 chunks (production: 149 units with 10 chunks; the production package was staged with FANIN 100).

## Notes

- Search packages split their items by how the queue search hands out work; the regenerated packages have their own unit counts (production modules vs regenerated modules in the table above).
- A replay that stops on a missing private part counts as 'not checkable', never as a pass. With the complete closure (every private part of the port, S4 and KMod builds), the only such replays are those of the large packages' aggregation modules (see "Not checkable, per package").
- Harness retries are reruns after the replay or build process itself failed to get memory (an address-space cap of the first launches, or the machine's memory exhausted after a scheduling change, process killed by the kernel); they are listed in `modules.tsv` (column harness_retries) and are not replay results.
- After the incidents the memory budgets were lowered, every job runs as the kernel's preferred out-of-memory victim (oom_score_adj 800), and a watchdog stops the youngest replay when available memory drops below 90 GB; there was no further incident.
- The re-run packages (KM2P010915, KM2P009791, KM2X003814, KM2P001917, KM2X004859, KM2P010636, KM2X007307, I13.L028, I13.L034, I13.L048, I.321) count with their re-run, in which every private part was kept; their earlier runs are listed in `modules.tsv` as superseded.
- KM2P001217 (1,464 regenerated units) was built on m2, m3 and m4: its item modules in three shares, then its aggregation modules on m2 with the other shares' module files and records merged in. 207 of its item modules were also copied, with their private parts, to m1 and replayed there: 185 of them pass on both machines with the same private-part sha256, 2 (I1346 and I1361) were replayed on m1 only, and 20 had been replayed on m2 (and their private parts deleted) before the copy.
- The I13 chunks rebuilt from this repository's chunk sources against the same item modules are byte-identical to the counting run's chunks (`.olean` and `.olean.private`), so the counting run reproduces.

## Files

- `modules.tsv`: one row per regenerated module. Column run is "counting" for the runs counted above, "superseded" for the earlier runs of the re-run packages, and "production chunk sources" for the I13 confirmation rebuild. The columns give the build exit status, the `leanchecker` result (with the reason when not checkable), the exported-level replay, harness retries, the KMod audit (KAXSUM bad and local_axioms, KAXP axioms), the public `.olean` sha256 with the production one and their comparison, the private part's sha256 and size, and the machine.
- `packages.tsv`: one row per package with the counts above, the top, its regenerated and production statement hashes, and the evidence.
- `kinds.tsv`: the module-kind coverage table. `totals.json`: the totals per case.
- `I13_RUN_ARCHIVE.sha256`: the sha256 of every file of the production I13 queue run used for the I13 regeneration.
- `i13_chunks/`: the I13 chunk files and sources described above, with sha256 lists.
