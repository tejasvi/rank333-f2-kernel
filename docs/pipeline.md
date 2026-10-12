# Build pipeline, manifests, verification records

This document covers the build pipeline, the manifests of the final package set and of R22K.Final's import closure, the V5 census, the
audit and sample-check records, and three large archives. Every count below comes from one frozen snapshot of the build queue,
`snap-20261011T2103Z-f674b4e775a4` (`manifests/snapshot.json`), and from a file in this repository.

## Contents

### generators/pipeline/ (the build pipeline)

The pipeline's own `README.md` describes the components, data flow, queue layout, environment variables, winner rules and
determinism. Its files are listed with sha256 in `SHA256SUMS.pipeline`.

- `queue/`: the object-store client (local directory or HTTP JSON API), the package queue, the per-machine worker, the module
  scheduler, import-hash records, queue operations.
- `verify/`: the incremental verifier and the done-record cache.
- `final/`: the top store, the union walk, the final build of R22K.Final and its audit, the closure census, V5, the queue snapshot,
  and the private-sample check.
- `winners/`: the first-finisher-wins rules for packages with several attempts.

A scheduler outside this kit ran the queue: it started and stopped the workers and installed the Lean closure on them.

### manifests/

| file | contents |
|---|---|
| `packages.tsv.zst` | One row per package of the final set (150,678). Columns: id, tier, group, kind, spec sha256, generator and its sha256, generator inputs, the manifest's `bundle` / `closure` values, installed closure parts with sha256, pipeline kit sha256, module count, module-build CPU seconds, tarball sha256 and bytes, root modules with their public `.olean` sha256, audit result. |
| `closure.tsv.zst` | The 17,017-module exported import closure of R22K.Final: module, origin, `.olean` sha256, `.olean` bytes, producing package (top-store modules). |
| `V5_RESULT.txt`, `V5_CHECKLIST.md`, `V5_SETS.tsv` | The V5 census against the snapshot: 15 items, all PASS. Also the checklist, and the sets: (a) the final set, (b) the done set, (c) = (b) − (a). |
| `census/SUMMARY.txt`, `census/producers.tsv` | Closure modules and `.olean` bytes per origin; the 50 producing packages of its 757 top-store modules; 0 uncovered. |
| `audit/kmod_audit_final.txt` | `kmod_audit.py --root R22K.Final`: PASS (20,470 modules reached, 707 `NS.EXT` statement checks). |
| `audit/external_walk.txt` | The private-level external walk: 5,008,518 of 5,010,509 obligation entries walked in 890 passed batches, 1,991 excluded; standard axioms {propext, Classical.choice, Quot.sound}. Also R22K.Final's own external step. |
| `audit/C1_excluded_retired.tsv` | The 1,991 excluded entries: modules of retired packages, with no current producer and not on the final LEAN_PATH. |
| `sample_check/census.txt`, `sample_check/samples.tsv.zst` | The private-sample re-check: per-class counts, and one row per sample (package, module, set, class, sample sha256, build-time private sha256). |
| `negative_controls.md` | Each planted defect, the check that catches it, and the outcome. |
| `compute.tsv` | Module-build CPU-hours, modules and tarball bytes of the final set, by group (sums of `packages.tsv.zst`). |
| `topstore.tsv` | Size of the top store by file type. |
| `snapshot.json` | The snapshot's id, time, counts and the sha256 of its files. |

### Zenodo record

| file | bytes | contents |
|---|---|---|
| `packages_modules.tsv.zst` | 834,641,897 | Every module of every final-set package (14,185,917 rows): package, module, public `.olean` sha256, private sha256 as built (`-` where none is recorded). |
| `r22k_oleans_ours.tar.zst` | 263,003,893 | The public `.olean` of this project's modules in R22K.Final's import closure: caseII, cc, e1g, hcapk, the 757 top-store modules and R22K (1,043 modules, 1,211,785,480 bytes raw). Members: `<Module/Path>.olean` (one LEAN_PATH root) and `MANIFEST_r22k_oleans_ours.tsv`. Upstream oleans are not archived (the toolchain and Mathlib's cache provide them); the port's are in `r22k_oleans_port_ir.tar.zst`. |
| `r22k_oleans_port_ir.tar.zst` | 782,524,986 | The public `.olean` of the frozen port's 5,373 modules in R22K.Final's import closure (3,311,083,568 bytes raw), and the 406 `.ir` files that the Lean loader reads when it imports R22K.Final (394 of port modules, 12 of caseII modules; 69,005,808 bytes raw). Members: `<Module/Path>.olean`, `<Module/Path>.ir` and `MANIFEST_r22k_oleans_port_ir.tsv` (module, file, origin, sha256, bytes). With `r22k_oleans_ours.tar.zst` and Mathlib's cache it completes the closure; `lean/final/check/check_closure.sh` loads R22K.Final from them. |
| `private_sample_pass_01.tar.zst` … `_06.tar.zst` | 1,148,319,340; 1,253,171,019; 1,062,171,762; 1,069,705,855; 1,091,017,334; 534,731,953 (total 6,159,117,263) | The sampled private parts of the final set that pass the replay: 5,912 files, 21,920,507,760 bytes raw. Each part holds whole packages (1,611 / 598 / 1,177 / 1,403 / 653 / 470 files). Members: `<package id>/<module>.olean.private` and `MANIFEST_<part>.tsv`. Every file's sha256 equals the private hash recorded at its build. |

These archives total 8,039,288,039 bytes.

## The sets (V5 A0)

- **(a) Final set** = R22K.Final's dependency DAG: 150,678 packages, all done, all with audit PASS. It consists of the 50 producers of
  the closure's 757 top-store modules and, through the spec lines' `deps`, everything they build on.
- **(b) Done set:** every done record that is not superseded: 150,688 records. Four ids were rebuilt in place (II.KM2X003078,
  II.KM2X003089, II.KM2X006581, ext_436_303fa8312a1f): each has a superseded record of its earlier build, and its done record is the
  rebuild.
- **(c) = (b) − (a):** 10 packages, w1_29428.re.sb1_0 to w1_29428.re.sb1_9. They are the groups of an earlier split level of
  w1_29428.re, replaced by the re-cut final w1_29428.re.sb2 (spec field `replaces`). No final-set package depends on them.

## Sizes (each figure is in the file named)

- **Final set** (`compute.tsv`): 150,678 packages, 14,185,917 modules, 529,503.8 module-build CPU-hours (user+sys, elaboration plus
  kernel). The package archives of the final set total 40,061,006,833 bytes.
- **Closure public oleans** (`census/SUMMARY.txt`, `closure.tsv.zst`): 17,017 modules, 6,666,843,176 bytes.
  - Upstream (Lean toolchain, Mathlib, batteries, aesop, Qq, plausible, proofwidgets, importGraph, LeanSearchClient): 10,601
    modules, 2,143,974,128 bytes.
  - Port: 5,373 modules, 3,311,083,568 bytes.
  - This project: 1,043 modules, 1,211,785,480 bytes. That is caseII 953,466,976; store 221,670,040; hcapk 22,873,624; e1g
    11,824,264; cc 1,774,512; R22K 176,064.
- **Top store** (`topstore.tsv`): 3,474,400 files, 18,134,537,991 bytes (sum of file sizes), 27,920,805,888 bytes on disk. These are
  the public parts (`.olean`, `.ilean`, `.olean.server`, `.kman`, `.mhash`) of 694,880 exported modules. The top store is not
  shipped: its `.kman` and `.mhash` records hold absolute paths.
- **Archives:** listed in the Zenodo table above; byte counts and sha256 are in `ZENODO.md`.

## How to build, run and regenerate

- **Requirements:** Python 3.10 or later, zstd, GNU tar, and the Lean v4.30.0 toolchain for the build and replay steps. Nothing is
  compiled; there are no binaries.
- **One package:**
  - The pipeline README's "Building one package locally" section builds one package from its spec line with the file-backed
    store.
  - Compare each module's `.olean` sha256 with the package's rows in `zenodo/packages_modules.tsv.zst`, and the root modules with
    `packages.tsv.zst`.
  - The generator and its sha256 come from the package's row in `packages.tsv.zst`. The generator sources are under
    `generators/<tier>/`.
- **The census and V5:** `snapshot.py` freezes the queue state. Then `classify.py --snapshot`, `v5.py --snapshot` and
  `sample_census.py --snapshot` reproduce `census/`, `V5_RESULT.txt` and `sample_check/census.txt` from it and the verification
  artifacts.
- **Replaying a private sample:**
  - Put the sample's `.olean.private` beside its package's public files (the package tarball's `store/`), with its store imports
    and the closure on `LEAN_PATH`.
  - Then run the toolchain's `leanchecker <module>`, as `final/sample_check.py` and `final/sample_overlay.py` do.
  - A sample is checkable only if every `import all` sibling's private part is present. The storage policy deletes those after
    audit, so 3,253 of the final set's 9,165 samples are not checkable.

## Determinism

- **Reproducible: a module's `.olean` bytes.** Given the same toolchain, closure files, sources and module names, a module's `.olean`
  is the same file. All hash comparisons (own hashes, imports, one name one content, the module lists) use `.olean` sha256.
- **Not reproducible:** tarball bytes (they carry file mtimes and owners, and are compressed with multi-threaded zstd), logs,
  timings, and the `.kman` / `.mhash` records (timings and the building machine's paths).
- **The archives listed here** are written deterministically (sorted names, fixed owner and mtime).

## Tool versions

- **Pipeline kit.** The production workers ran successive versions of this kit. Each done record names the version that finalized
  it, and `packages.tsv.zst` (column `pipeline_kit_sha256`) gives the version per package: 26 versions; the largest covers 67,048
  packages (3625d99b…). 67 early packages, finalized before kit provenance was recorded, have none.
- **What is shipped.** The kit in `generators/pipeline/` is the final version, with storage, paths and machine names turned into
  environment variables. `final_build.sh` also performs, with a sha256 check, the copy of the four R22K top-build files (FinalTop,
  Cap, FinalAll, Cor) into its build directory.
- **Generators per package** (`packages.tsv.zst`, columns `generator`, `generator_sha256`):
  - e1g tools v3 (035f661f): 15,355
  - e1g tools v7.1: 18,672
  - e1g tools v8: 75
  - e1g tools v8.2: 76,266, plus 451 aggregations (mkagg)
  - e1g tools v8.3: 7
  - e1g tools v8.5: 2
  - ext extpkg v3 / v5 / v6 / v7 / v8 / v9 / v10 / v11: 1,222 / 500 / 3,112 / 9,304 / 1,649 / 2,674 / 117 / 384
    (the versions of the `extpkg.py` script; `docs/cc.md` and `generators/ext/package_tools.tsv.zst` number the EXT tools versions that
    bundle it: extpkg v3 and v5 are tools v3 and v5, extpkg v6 and v7 are tools v6, and extpkg v8 to v11 are tools v7 to v10)
  - ext tools v1 / v2: 242 / 868
  - classes kcagg v2 / v3: 19 / 2
  - split builds (the parent's emitted tarball): 1,542
  - pre-emitted tarballs: 18,191 caseII, 23 ext tops, 1 ext leaf
