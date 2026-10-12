# Regenerating packages and replaying the proof

Every generated module of the final set can be produced again from the files in this repository and the Zenodo record. This file says how, tier by tier, and what a regeneration reproduces. The documents in `docs/` give the commands in full.

## Prerequisites

1. **Toolchain and dependencies:** Lean v4.30.0, Mathlib v4.30.0, Rudich and Rousseau's development, and the frozen port, as in `lean/TOOLCHAIN.md`.
2. **Libraries:** build the libraries under `lean/` with the build script in each directory: `kmod/`, `e1g/`, `caseII/`, `cc/`, `hcapk/`.
   - The HCapK sources are derived from the frozen port's sources by `lean/hcapk/derive_hcapk.py`.
   - Each directory lists the sha256 of every module file it builds, so a rebuild can be compared module by module.
3. **Generators:** build them from `generators/<tier>/` with the build script in each directory.
   - The `build.sh` scripts of `generators/e1g/` and `generators/ext/` reproduce the production binaries byte for byte (`BINARIES.sha256`).
   - The case-II search binaries depend on the build's paths and CPU (`-march=native`), so a rebuild with `generators/caseII/search/build.sh` differs in bytes. It gives the same pcerts, frontier dumps and package tops, as `docs/caseII.md` describes.

## Package records

- `manifests/packages.tsv.zst` has one row per package of the final set. Each row gives:
  - the tier;
  - the sha256 of the spec (the generator command as run);
  - the generator and its version;
  - the module count;
  - the root modules with the sha256 of their public `.olean`;
  - the audit result.
- The spec lines themselves are in `inputs/<tier>/`.
- The Zenodo file `packages_modules.tsv.zst` lists every module of every package of the final set with the sha256 of its public `.olean` and, as recorded at its build, of its `.olean.private`.

## Tool versions

Every package of the final set records the generator that produced it: `manifests/packages.tsv.zst`, columns `generator` and `generator_sha256`, and for case II also `manifest_bundle`. Every recorded version is in this repository:
- **E1 chains and class packages:** the E1 tools version named in the package's spec line: v3, v7.1, v8, v8.2, v8.3 or v8.5. The tarball sha256 of each version is in `generators/e1g/TOOLS.md`, and its tree is under `generators/e1g/tools/<version>/`.
- **EXT:** the tools version per package is in `generators/ext/package_tools.tsv.zst`, with the scripts of every version under `generators/ext/versions/` and their hashes in `TOOLS_VERSIONS.tsv`.
- **Class aggregations:** kcagg v2 or v3 (`generators/classes/`).
- **Case II:** the emitter bundle version recorded in each package's manifest (`generators/caseII/BUNDLES.tsv`; files in `generators/caseII/bundle/`). **Cases I and I13:** `generators/caseII/CASE321_TOOLS.tsv`.

**How the versions are pinned.**
- A package's spec line, whose sha256 is in `packages.tsv.zst`, names its tools version.
- Over all build records that carry provenance, each tools version's install directory held exactly one tools tarball.
- The build records also name the toolchain closure:
  - 106,014 records give its sha256 (`582f0654…`);
  - 44,596 earlier records give only its object name, `kclosure_v1`, the only toolchain closure ever published;
  - 68 records predate provenance altogether: 67 E1 packages of tools v3 and 1 EXT package. For these, the spec line names the tools version, and `kclosure_v1` was the only toolchain closure.

## What a regeneration reproduces

| tier | regenerate with | reproduces byte for byte, with the tool version recorded for the package | compare |
|---|---|---|---|
| c436, c422, held jobs, point (E1 chains) | `generators/e1g/sh/mktools.sh <version>` assembles the tools tree; then the package's line in `inputs/e1g/spec_lines.jsonl.zst` (`docs/e1g.md`) | Lean sources, `manifest.jsonl`, the emitter's record, and the public `.olean` of every module. The certificate data depend on the order in which emitter threads take jobs (LP warm starts). The production emissions ran multithreaded, so a regeneration's certificate data and `.olean.private` can differ from production; single-threaded emission is reproducible from run to run. | public `.olean` |
| split builds of held jobs | emit the family's source package, then build the group manifests in `inputs/e1g/splitplans.tar.zst` | the same module files as the single-package build | public `.olean` |
| cap roots, point root, heavy-job aggregations | `mkagg.py` (tools v8.2) over the dependencies | module sources | public `.olean` |
| class packages | the E1 tools tree v7.1 with the package's line in `inputs/classes/kc_packages_*.jsonl.zst` (`docs/classes.md`) | Lean sources, manifests and public `.olean`; certificate data as for the E1 chains (the same emitter) | public `.olean` |
| class roots | `generators/classes/kcagg_v2/kcagg.sh` (19 classes) or `kcagg_v3/kcagg.sh` (454, 485) | sources and module files | public `.olean` |
| leaf tier (EXT packages, giant leaves, leaf tops) | `generators/ext/regen_ext.sh` with the tools version recorded for the package in `generators/ext/package_tools.tsv.zst`; leaf tops with `mkexttop.py` (`docs/cc.md`) | module sources, manifests and module files, for every tools version. The parallel generators give the same output for any worker count. | `.olean` |
| case II packages | the CC tables (`mkcc.py`), phase 0, the job tables (`mkjobscc.py`, `mkx.py`) and the package specs (`mkpkgcc.py`), then each package's `emit.sh`, which runs the queue search `prof7R3q_b12d` (source in `generators/caseII/search/src_b12/`; `docs/caseII.md`) | the tables, job tables and all 18,108 package specs. A package's items depend on how the in-package search distributes work, so its item modules can differ between runs. | the public statement of each package top, `<P>.Top.cov : R22N.AllL KB.CovOfKeyCC [<the minimal keys of its job roots>]`, which depends only on its job lines |
| case-II join | `joinemit.py`, `mkpkgw.py`, `mkjoinpkg.py` (`docs/caseII.md`) | the item lists, chunk sources and `KM2.Top` source; the item modules' `.olean` | item lists and chunk sources; the statement `KM2.Top.segs : R22N.AllL KB.SegsOfKeyCC [1]` |
| cases I and I13 | the queue runs and the case-I/I13 package tools (`docs/caseII.md`) | the specs. Items depend on the search's work distribution. | the statements of `KMIA.Top.vI`, `KMJJ.Top.vI` and the leaves' root chunks |
| G2 crowns | `lean/cc/g2/` generators (`docs/cc.md`) | 31,444 of the 36,953 generated sources. The others differ only in a data directory name or a docstring line. The generated sources as built are in the Zenodo record. | `.olean` |
| final module | `lean/final/py/mkinst.py --kII 1 --ext <21 classes>` | `R22K/Final.lean` (sha256 in THEOREM.md) | `.olean` |

**Two points apply to every tier.**
- The comparison uses the public `.olean`, whose bytes are reproducible: for the same toolchain, closure, sources and module names, a module's `.olean` is the same file. Package archives, logs, timings and build records carry machine paths and times, so they are not compared.
- A regenerated package is checked by the kernel when it is built, whatever its certificate bytes are.

**Building and comparing:**
- `generators/pipeline/` builds a package from its spec with a local file store (`docs/pipeline.md`).
- It also runs the audit (`kmod_audit`), writes the import-hash records (`modhash.py record`), and compares each module's `.olean` sha256 with the package's rows in `packages_modules.tsv.zst` and its roots with `packages.tsv.zst`.

## Replaying the whole proof

The private parts of the package modules are deleted after their audit, and only a seeded 0.1% sample is archived. So an independent kernel replay of the whole closure (`lean4checker` over `R22K.Final`) first rebuilds the packages with their private parts kept:

1. Regenerate and build every package of the final set as above, keeping each module's `.olean.private`.
2. Build the class roots, the aggregations, the joins and `R22K.Final`.
3. Compare as in the table above.
4. Run `lean4checker R22K.Final`, or any other independent checker, over the rebuilt closure.

**Cost:** the module builds of the final set take about 530,000 vCPU-hours (529,504 CPU-hours of elaboration and kernel checking). Generating the packages comes on top. Its CPU time was not recorded, because the emitters run multithreaded.
