# Pre-registered re-check of the case II, I and I13 packages

Registered 2026-10-11 23:59Z, before any regeneration ran. This file fixes the selection, the procedure and the criteria; the results are added to VERIFICATION.md.

## Why

The seeded 0.1% private sample (VERIFICATION.md) holds no module of the packages of cases II, I and I13: their unit script deletes each private part as soon as the module's manifest is clean, before the package's finalize step draws the sample. This re-check covers them by regeneration: selected packages are regenerated from this repository and the Zenodo record with every private part kept, and every regenerated module is replayed by the kernel.

## Selection

- **Seed:** `02759a712c3a9354f69f2ce72c427b4f0b0517101420a876c7e6d2292cbe9bd8`, the sha256 of this repository's `SHA256SUMS` as of 2026-10-11 23:46Z. It was fixed, and sent to the release team, before this re-check was decided.
- **Rule:** within a population, packages are ranked by the hex string sha256("<seed>:<package id>"), ascending, and the first k are taken.
- **Case II:** the 18,110 case-II packages of the final set (the 18,108 search packages `II.KM2P*` and `II.KM2X*`, and `II.JOIN4I`, `II.JOIN4C`); k = 20, about 0.1% of case II's modules, the rate of the existing sample.
- **Case I:** its one package, `I.321`.
- **Case I13:** the 80 packages `I13.L000` to `I13.L078` and `I13.J`; k = 3.

The selected packages, with their production module counts and module-build CPU-hours (`manifests/packages.tsv.zst`):

| case | package | modules | CPU-hours | rank key (first 12 hex) |
|---|---|---|---|---|
| case II | `II.KM2P000195` | 238 | 7.0 | `000246a16ac6` |
| case II | `II.KM2X007307` | 151 | 7.0 | `000330fc8e25` |
| case II | `II.KM2X001188` | 751 | 12.8 | `000630eb2831` |
| case II | `II.KM2P005847` | 253 | 10.0 | `00082f0f7877` |
| case II | `II.KM2X007552` | 328 | 7.6 | `0008c6d16d2c` |
| case II | `II.KM2P001917` | 132 | 2.1 | `000c338850f0` |
| case II | `II.KM2P001217` | 1505 | 34.3 | `000f6377fd7f` |
| case II | `II.KM2P007638` | 202 | 6.8 | `0017cdf0b13d` |
| case II | `II.KM2X003814` | 50 | 2.3 | `001aa68d5f3c` |
| case II | `II.KM2P009791` | 90 | 1.9 | `001ae9e96cc2` |
| case II | `II.KM2X006668` | 706 | 33.3 | `001bc76fa20e` |
| case II | `II.KM2P005680` | 338 | 13.1 | `001eb1855a10` |
| case II | `II.KM2P006811` | 188 | 6.4 | `0022a7083c0e` |
| case II | `II.KM2P006552` | 230 | 8.2 | `002890fe26ca` |
| case II | `II.KM2P002866` | 304 | 7.7 | `002b5b185f59` |
| case II | `II.KM2P002742` | 484 | 13.1 | `002b801e2cfe` |
| case II | `II.KM2P000181` | 226 | 8.7 | `002f42161a55` |
| case II | `II.KM2P010636` | 282 | 3.5 | `00310c727281` |
| case II | `II.KM2P010915` | 18 | 0.3 | `00334edff5d1` |
| case II | `II.KM2X004859` | 102 | 2.6 | `0034d41b583f` |
| case I | `I.321` | 149 | 6.1 | `6608c35fc5eb` |
| case I13 | `I13.L028` | 68 | 2.8 | `03d54c8eb94a` |
| case I13 | `I13.L034` | 18 | 1.0 | `0893620cbf7f` |
| case I13 | `I13.L048` | 27 | 0.8 | `0a6903fc9c70` |

In all: 24 packages, 6,840 modules and 199.3 CPU-hours in production.

## Procedure

1. From this repository and the Zenodo record only, build the case-II library (`lean/caseII`, compared with `OLEANS.sha256`), the search binaries and `r3qglue` (`generators/caseII/search/build.sh`), and the emitter bundle copy (`docs/caseII.md`).
2. Regenerate each selected package from its spec: `inputs/caseII/PACKAGES_KM2.jsonl.zst` and `bundle/emitcc.sh` for case II; the `case321` tools for cases I and I13. Build every module with `KMOD_KEEP_PRIVATE=1`, so that every private part is kept.
3. For every regenerated module: replay it with the Lean v4.30.0 toolchain's `leanchecker`, private bodies included; and compare the sha256 of its public `.olean` with the production hash in `packages_modules.tsv.zst` (Zenodo) where a production module of the same name exists.
4. For every package top (`<P>.Top`, and the tops of cases I and I13): compare its public statement, as recorded by KMod (`KPUB` with its statement hash), with the production top's.

## Criteria

- **Failure (the re-check stops and is reported):** a module that the kernel replay rejects; a KMod audit record with a bad constant or a local axiom; an axiom outside {propext, Classical.choice, Quot.sound}; a package top whose statement differs from production's.
- **Reported per case:** modules replayed, with pass / fail / not checkable (a module is not checkable if a private part it needs is missing).
- **Byte identity, reported:** the numbers of regenerated modules whose public `.olean` equals the production file, differs from it, or has no production module of the same name. A multi-item search package splits its items according to how the search distributes work (`docs/caseII.md`), so its item modules, and its top's imports, need not reproduce byte for byte; its top's statement must. A difference in a package that has a single item, or in a module that does not depend on the item split, counts as a failure.

## Amendment 1 (2026-10-12 00:12Z, before any regeneration ran)

The selection is unchanged. A check of the procedure's inputs found three that are not in this repository or its Zenodo record. They are supplied as follows:
- **`gen7c`.** The item conversion (`py/kitem.py`) calls `gen7c --lg` for profile leaves whose stream carries no v7 record. Its command-line source `gen7c.cc` is added to `generators/caseII/search/src/gen7c/` and built with `generators/e1g/cpp/gen7.h`; the re-check uses that build. An informational probe compares its output with the production binary's on about 100 profile leaves.
- **Tables of cases I and I13.** `tab_C3eD.bin`, `kept_C3eDc4d.txt`, `C3eD_321.c2t`, `kept3eD_lab321.bin` and `hyp7_321.bin` are files of the native release's Zenodo record (https://doi.org/10.5281/zenodo.23236154: `data/tables/`, `data/lean/`), checked against their sha256 there. `docs/caseII.md` names them.
- **The I13 leaf split.** The root-chunk statement of an I13 leaf package depends on how its queue run split the items. A fresh queue run splits differently, so a leaf regenerated from it covers other roots. The three I13 leaves are therefore regenerated with the released `case321` tools from the production I13 queue run's plan and segments (not archived, 27 GB); the sha256 of each of these files is recorded with the results. `I.321` comes from a fresh case-I queue run: the statement of its top `KMIA.Top.vI` depends only on the job roots.

Evidence is reported in two kinds, with counts for each:
- **(a) byte-identical replay of production modules:** the regenerated public `.olean` equals the production file, and the module passes the kernel replay;
- **(b) independent re-derivation of the same top statement (kernel-replayed):** every regenerated module of the package passes the kernel replay and the package top's statement equals production's, while item modules differ in bytes because the item split depends on how the search distributes work.

## Amendment 2 (2026-10-12 02:34Z, during the run)

**Stop.** At 02:05Z a failure condition of the criteria fired, and the run stopped for review.
- In the three same-split I13 leaves (I13.L028, I13.L034, I13.L048), every item module's public `.olean` equals the production file: 65 of 65, 16 of 16 and 25 of 25.
- The 7 aggregation chunks (KMJL028.A0 to A2, KMJL034.A0 and A1, KMJL048.A0 and A1) differ in bytes, and these chunks do not depend on the item split.

**Cause.** The chunk specs equal production's. The chunk sources differ in one line, which the shipped `py/mkaggf.py` writes and the earlier version that produced the production I13 packages did not:
``run_cmd Lean.modifyEnv (Lean.LibrarySuggestions.typePrefixDenyListExt.addEntry · `R22N.AllL)``
It adds an entry to the library-suggestion deny list and no constant.

**Resolution, approved before the run resumed:**
1. The 7 chunks were rebuilt from the production chunk sources (without the line) against the regenerated items. All 7 are byte-identical to production (`.olean` and `.olean.server`), and so are the 106 item modules.
2. `lean/final/check/OleanCmp.lean` compares the chunks built with the shipped `mkaggf.py` with the production chunks. In every part:
   - all constants are identical;
   - the differing data are the deny-list entry (`typePrefixDenyListExt`), the two library-suggestion indexes computed from the module (`symbolFrequency`, `sineQueNon`), and the module-docstring entry (`moduleDocExt`).
   - Both variants of all 7 chunks pass `leanchecker` with every private part present.
3. The earlier `mkaggf.py` (or a switch that omits the line) ships with the case321 tools, and `docs/caseII.md` says which packages each version produced. `generators/caseII/CASE321_TOOLS.tsv` maps every case I/I13 package to its tool versions.
4. The three I13 leaves count as evidence (a), byte-identical replay of production modules, with the tool version recorded for the package. Their 7 chunks built with the shipped `mkaggf.py` are reported separately, as a byte difference whose cause is verified.
