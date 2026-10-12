# The context caps c436 and c422, the point tier, and their generators

This document covers the E1G/E1P job tier of the kernel-only proof:
- the context caps c436 and c422 (E1G format);
- the point tier ptc (E1P format);
- the aggregation of both to their roots;
- the split builds of the largest emitted packages.

It holds the Lean modules built outside the frozen port that this tier imports, the generator sources with their build, the
inputs, and the spec line of every e1g package in the final set.

## Contents

| path | what | size |
|---|---|---|
| `lean/e1g/` | Lean sources (see below), `KH_data.tar.zst`, `build_e1g.sh`, `OLEAN_SHA256`, `OLEAN_SHA256_RELEASE`, `PORT_DEPS.md` | 461 files, 7.8 MB |
| `generators/e1g/` | `cpp/`, `build.sh`, `BINARIES.sha256`, `TOOLS.md`, `tools/<version>/`, `tools/FILES.tsv`, `py/`, `py/qorder/`, `sh/` | 57 files, 0.7 MB |
| `inputs/e1g/` | `ip_core`, `ip_heavy`, `ip_classes` (`.tar.zst`), `IP_SHA256`, `spec_lines.jsonl.zst`, `packages.tsv.zst`, `splitplans.tar.zst`, `cut.tar.zst` | 8 files, 65.6 MB |
| `zenodo/e1g_binaries.tar.zst` | the production binaries `lineenum9qe_ld5` and `e1pconv` (`BINARIES.sha256`; `libhighs.so.1` is the highspy 1.15.1 wheel's file) | 1.0 MB |
| `zenodo/e1g_cut_inputs.tar.zst` | the inputs of the wave-1 cut list (`py/mkcut.py`): the native census's depth-10 sub-job counts and frontiers | 54.6 MB |

No file of this tier exceeds 50 MB (the largest is `ip_heavy.tar.zst`, 35.9 MB).

### Inputs (`inputs/e1g/`)

The three `ip_*` archives extract to `ip/`, the 1,081 input files of the tools trees: IP, order and frontier files of c436,
c422 and the point IP (`ip_core`); the heavy jobs' depth-10 frontiers and top traces (`ip_heavy`); and the class contexts
and class giants' frontiers and top traces (`ip_classes`, which `docs/classes.md` references).

The files are byte-identical to the production tools trees' `ip/`, with one exception, `ip/hcap/ana/roots_fixed.txt`. Its
frontier column is written relative to `ip/` (`hcap/run/c<c>/root5/fr.txt`). The production file (sha256 `bb9ae128717e…`)
gives the same names under the absolute development root, and `kjlib.load_class_contexts` strips that root, so both forms
name the same input file.

### Lean modules (`lean/e1g/`)

- **`E1GK.ChainF`, `E1GK.ExtMono`:** chains indexed by a function and monotonicity in the external-leaf list, over `E1G.Hdr`.
  Both are in the final theorem's import closure.
- **`E1GK.JobCmd3`, `E1GK.RootCmd`, `E1PQ.ChainF`, `E1PQ.JobCmd`:** the KJ command library. `#e1gjob` builds an E1G job
  module, `#e1groot` the root of a range or of a heavy job, and `#e1pjob`, `#e1pjobs`, `#e1ptop` and `#e1pagg` do the
  same for the point tier. The generated KJ modules run them.
- **`KH.HT436`, `KH.HT422`:** the job tables of the two caps.
- **`KH.S<C>_<J>`:** the sub-job tables of the 448 heavy jobs (343 of c436, 105 of c422).
- **The tables' data:** 450 modules in all. They read their data through `#rttablew` from `data/KH_<name>.bin`, which is in
  `KH_data.tar.zst`. `py/mkht2.py` and `py/mkht3.py` regenerate the data from the inputs.

`PORT_DEPS.md` lists every import from outside this directory: the frozen port is referenced, not copied; KMod is in
`lean/kmod`.

## Build

1. **Binaries:** `generators/e1g/build.sh OUTDIR` needs g++ 15.2, an AVX-512 x86-64 CPU, zlib and highspy 1.15.1.
   - On the production build host it reproduces `BINARIES.sha256` byte for byte.
   - On another CPU model the bytes differ (`-march=native`). The exact binaries are in `zenodo/e1g_binaries.tar.zst`;
     `libhighs.so.1` is the file of the highspy 1.15.1 wheel (`pip install highspy==1.15.1`), sha256 in `BINARIES.sha256`.
2. **A tools tree:** `generators/e1g/sh/mktools.sh VERSION $TOOLS_ROOT/VERSION [BINDIR]` builds the tree of one tools version.
   - It takes `py/` and `emitpkg.sh` from `tools/VERSION`, the binaries from BINDIR (a `build.sh` output directory, or the
     extracted zenodo archive; without BINDIR it runs `build.sh`), and `ip/` from `inputs/e1g`.
   - It checks every input against `IP_SHA256` and the binaries against `BINARIES.sha256`.
   - The versions are v3, v7.1, v8, v8.2, v8.3 and v8.5. `TOOLS.md` gives their tarball sha256 values, the settings each used
     and the packages each produced.
3. **The Lean modules:** run `lean/e1g/build_e1g.sh` with these variables set:
   - `KMOD_BUILD`: the KMod build;
   - `PORT_FULL`: the frozen full port build;
   - `LP_BASE`: Mathlib and core as a LEAN_PATH;
   - optionally `E1G_BUILD` and `LEAN`.

   It extracts the KH data and compiles all 456 modules (`-j1`, cwd = `lean/e1g`).
   - The output equals `OLEAN_SHA256`, which lists the production module files.
   - One exception: `E1GK.RootCmd` and `E1PQ.ChainF` have doc comments edited for release. For those two, `.olean.private`
     and `.olean.server` equal `OLEAN_SHA256_RELEASE`, and their `.olean`, `.ilean` and `.ir` equal production.

## Regenerate a package

`inputs/e1g/spec_lines.jsonl.zst` has one JSON line per package, as the queue ran it. It includes:
- placeholders: `{OUT}` (the package directory), `{DEPS}` (a directory of the dependencies' package directories);
- variables: `$TOOLS_ROOT` (the directory holding the tools trees by version), `$STORE` and `$FETCH` (the object store
  holding emitted packages and split manifests, and its copy command).

The fields are: `id`, `kind`, `cap`, `a`, `b`, `job`, `args`, `deps`, `deps_pubs`, `export`, `family`, `emit` (with `argv`),
`role` and `tools`. `inputs/e1g/packages.tsv.zst` summarises the same lines, with the production spec sha256, tarball sha256
and module count of each final package (as in `manifests/packages.tsv.zst`).

The roles are as follows.
- **Role `final`, kinds `range`, `split`, `heavy-sub`, `heavy-split` (93,811 packages):** run `emit.argv` with `{OUT}` set.
  - Its `env` prefix sets the `KJ_*` options.
  - The result is the package directory: `DONE`, `manifest.jsonl`, `kext.txt`, `src/KJ/*.lean`, `src/data/`.
- **Kinds `agg-heavy`, `agg-root`, `agg-point` (451):** `mkagg.py` (v8.2) over `{DEPS}`, which holds the `deps` packages'
  directories.
- **Kinds `splitbuild`, `splitbuild-final` (1,497):** the build of one emitted package is spread over group packages.
  - `inputs/e1g/splitplans.tar.zst` has, per family, every group manifest that a final package used (1,497 of them),
    `FAMILIES.tsv` (family, emitted-package sha256, groups, final package) and `PACKAGES.tsv` (package -> manifest).
  - To regenerate: emit the family's `split-source` line (25 lines, role `split-source`), then build the modules of each group
    manifest from that tree. The production line's sha256 check names the production emission; a regenerated emission
    replaces it.
  - `py/splitbuild.py` (`sh/sbrun.sh`) computes the groups from an emitted package. `py/sbtables.py` adds the tables that
    the lifted ranges of a final package import publicly.

Every package is built by the package worker (generators/pipeline) from its `manifest.jsonl`. The LEAN_PATH is the store of
built packages, then the e1g build, KMod, HC436, the port, and Mathlib. Compare with production as described under
Determinism.

The other planning tools are in `py/`:
- `mkcut.py`: the c436/c422 wave-1 cut list, from `inputs/e1g/cut.tar.zst` and `zenodo/e1g_cut_inputs.tar.zst`;
- `mkcut_pt.py` (in the tools trees): the point cut list;
- `mksubfr.py`: the heavy jobs' depth-10 frontiers and top traces in `ip_heavy`;
- `mkaggplan.py`: the aggregation lines;
- `py/qorder/`: the queue-order predictor.

They read the development layout under `$R22_ROOT/e1g/` (`E1P/run/cap2/`, `pkg/`). Package mode, which every production
package used, reads only the tools tree.

## Determinism

**Binaries and module builds are byte-reproducible.**
- `build.sh` gives the production binaries on the production build host.
- The Lean builds are byte-reproducible. A rebuild of the six e1g library modules and three KH tables from this directory
  gives the production module files (all five per module), except the doc-comment parts of the two edited modules. Those are
  listed in `OLEAN_SHA256_RELEASE`.
- A module built inside a split-build group is byte-identical to the same module built in the single package build
  (6 modules of one heavy job checked).

**The tools here behave as the production tools.** The production v8.2 tarball tree and the v8.2 tree assembled here both
emitted `w1_03785` at `--threads 1`, and the two package trees are byte-identical: every source and data file, the manifest,
and `DONE`. The class contexts of v7.1 load identically from both trees, for all 21 classes: emitter settings, tables, and
the resolved frontier files with their sha256.

**Emission reproduces the package exactly, except for certificate data bytes when the emitter runs multithreaded.** Production
package `w1_03785` (c436 range 208746-209453, tools v8.2, `--threads 4`, 16 modules, 707 jobs) was regenerated with the tools
built here (`mktools.sh v8.2` and the production binaries):
- `manifest.jsonl` (module names, dependencies, kinds, predicted costs), `DONE` (all fields but the timing) and `kext.txt` are
  identical to production.
- Two regenerations have identical `.lean` sources (16 of 16).
- Two modules built from the regeneration (`L4`, `L9`) have `.olean`, `.ilean` and `.olean.server` byte-identical to
  production.

**Certificate data vary across multithreaded runs.** The leaf-certificate data (`src/data/*_j<k>.bin`) are not byte-stable
when the emitter runs with more than one thread. The LP warm starts follow the order in which the threads take jobs, and that
order depends on timing.
- Two `--threads 4` regenerations of `w1_03785` differ in 85 of 2,844 data files, and a `--threads 1` run differs from the first in
  145.
- So the built modules' `.olean.private` (the proofs, which carry the certificates) differ from production's, while their
  public files agree.

**Single-threaded emission is byte-reproducible.** Two `--threads 1` runs gave identical trees, sources and data, for
`w1_03785` and for the point range ptc 21-40. The `.lean` sources do not depend on the thread count (1 against 4 threads on
both packages), nor on thread against process fan-out (a 661-module heavy split, sources identical).

**Consequences.**
- A regenerated package has the same modules, statements and public module files as production (measured above). The public
  `.olean` of the root modules is what `manifests/packages.tsv.zst` records.
- The kernel checks every certificate in it when the package is built.
- Compare `.lean` sources, `manifest.jsonl`, `DONE` (without `secs`) and public `.olean` files.
- `.olean.private`, data files and package tarballs match production only where the certificate data do.
- `inputs.sha256` and `emit.log` record the local tools paths and times, so they differ by construction.
