# Case II, and the tops of cases I and I13

This document covers the case-II library, the case-II generators and inputs, and the sources of the tops of cases I and I13. The final
theorem uses three tops from it:

| package | top module | public statement |
|---|---|---|
| II.JOIN4C | `KM2.Top` | `KM2.Top.segs : R22N.AllL KB.SegsOfKeyCC [1]` (case II: the segments over the case-II root's minimal key 1) |
| I.321 | `KMIA.Top` | `KMIA.Top.vI` (`#kmVI321 KMIA.Top.vI 0 12`: `∀ l ∈ [0, 168, 462], R22N.Cov (KB.CheckedAny321 0 12) ((2^l, l), 0)`) |
| I13.J | `KMJJ.Top` | `KMJJ.Top.vI` (`#kmVI321 KMJJ.Top.vI 13 13`, the same form for lo = hi = 13) |

Case II is 18,108 search packages (`II.KM2P*`: 10,181 on `jobs_cc.txt`; `II.KM2X*`: 7,927 on `jobs_x.txt`) and the join: `II.JOIN4I`
(4,596 item modules with 7,878 phase-0 segments, 51,900 records) and `II.JOIN4C` (80 Cov chunks and `KM2.Top`, over the 295,982
job roots of the packages). Case I is the package `I.321`; case I13 is 79 leaf packages `I13.L000`-`I13.L078` and the join `I13.J`.

## Layout

### lean/caseII/

- `src/`: the case-II library, 89 modules (`KB.*`, `KDK.*`, `KDK321.*`). Build order: `build_order.txt` (76 modules), then
  `build_order_ext.txt` (13). `checkorder.py` checks that this order is topological.
- `build.sh`: builds modules in order, one `lean` call per module (Lean v4.30.0, `-DElab.async=false`, RLIMIT_AS 64 GiB, nice 10).
- `SOURCES.sha256`: the 89 sources here and the build files (93 files).
- `OLEANS.sha256`: the module files of the 89 modules as built (`.olean`, `.olean.private`, `.olean.server`, `.ir`; 356 files).
- `DOCSTRING_EDITS.tsv`: five sources (`KB.Agg`, `KB.AggR`, `KDK321.Batch321`, `KDK321.Flook`, `KDK.ItemK`) differ from the
  production sources in comment and docstring wording only.
  - Rebuilt from them, every `.olean` and `.ir` file is identical to the production file.
  - Five `.olean.private` / `.olean.server` files of three of these modules differ. The table gives both sha256 for each.
- `DATA.sha256`: the 1,026 data files that the library reads under `data/`. They are in `zenodo/caseII_lib_data.tar.zst`:
  - `data/cc436_422/`: the CC-route binding rows and peel tables (`bind/q*.bin`, `bind/c1.bin`, `cc436_422.c2t`);
  - `data/bindII_in/`, `data/bindII/`: the binding rows of the native table;
  - `data/rt479/C3eDII.c2t`.
- `tops/KMIA/`: `KMIA.Top` and its aggregator chunks `KMIA.A0`-`KMIA.A9`.
  - Each chunk reads a `.spec` (`py/mkaggf.py`'s format):
    - `I key <item module>.keysOK idx`: an item;
    - `E|R key T <chunk>.cov`: an external or range child that another chunk covers (`E` lines name a leaf package's root chunk);
    - `X key`: the keys that the chunk exports.
  - The spec is untrusted input. The chunk's proof, one `R22N.Cov` step per item with children first, is checked by the kernel.
- `tops/KMJJ/`: `KMJJ.Top`, `KMJJ.A0` and `KMJJ.A1`.

The other modules of these packages are not in this repository:
- the item modules of the case-I and case-I13 packages, generated from the queue runs;
- the 18,108 search packages, generated per package;
- the case-II join, whose sources are in `zenodo/caseII_join_src.tar.zst`.

### generators/caseII/

- `search/`: the C++ searches and `build.sh` (needs `HIGHS_LIB`, the directory of `libhighs.so.1`, HiGHS 1.15.1):
  - `src/rerun/r3/prof7R3_b14.cc`: the phase-0 search. Production binary `prof7R3k14c`.
  - `src/xq/r3q/prof7R3q.cc`: the queue search, production binary `prof7R3q_b14` (cases I and I13). This source is the merge of
    `prof7R3_b14.cc` with the queue client:
    `python3 r3q_block.py L92_block.txt prof7R3_b14.cc BLOCK.cc; python3 r3q_patch.py prof7R3_b14.cc BLOCK.cc prof7R3q.cc`
    regenerates it byte for byte.
  - `src_b12/prof7R3q.cc` (md5 `e6bd66cf3d9b06969b9ced0049186326`): the source of `prof7R3q_b12d`, the queue search that emitted all
    18,108 case-II search packages. Every bundle version carries this same binary.
    - It is the merge of the batch-12 search `src/rerun/r3/prof7R3_b12.cc` with the queue client, by the merge scripts' batch-12
      revisions in `b12/`:
      `python3 b12/r3q_block.py L92_block.txt src/rerun/r3/prof7R3_b12.cc BLOCK.cc; python3 b12/r3q_patch.py src/rerun/r3/prof7R3_b12.cc BLOCK.cc OUT.cc`
      regenerates it byte for byte.
    - `src_b12/xq_r3.h` and `src_b12/r3rec.h` are the headers of that build. They sit next to the source, so the compiler finds them
      before the batch-14 versions.
    - Built with the production command (`g++ -O3 -march=native -std=c++17 -pthread`, dynamic HiGHS, the production tree's include
      paths), it gives the production binary byte for byte (sha256 `164e19ea…`).
    - Built with `build.sh` here (`build.sh src_b12/prof7R3q.cc OUT -march=native`), the binary differs in bytes: static libstdc++,
      `$ORIGIN` RPATH, and other include paths.
    - That rebuilt binary gives the same pcert and DUMP as the production binary on phase-0 batch `poolC_poolE_d12_000`, with the same
      header and records hashes.
    - It also regenerates package `II.KM2P000188` (see Determinism).
  - `src/rerun/r3/prof7R3_b12.cc`: the batch-12 search, the base of `prof7R3q_b12d`.
  - `SOURCE_EDITS.tsv`: `r3qglue.cc` differs from the production file in one comment line, and builds to the same binary.
    - The merge inputs and outputs (`prof7R3_b12.cc`, `prof7R3_b14.cc`, `prof7R3q.cc`, `src_b12/*`) are byte-identical to the
      production files.
    - The merge writes the base's md5 into the queue fingerprint (`R3Q_BASE`), so editing a base would change that fingerprint.
  - `src/xq/r3q/r3qglue.cc`: the item-key and glue tool. `build.sh` on this source gives the production binary byte for byte
    (sha256 `5d82fdcc…`).
- `bundle/`: the case-II emitter bundle, version `77b5632621a1563c`, with path placeholders:
  - `emitcc.sh`, the emission of one package:
    - a local queue server (`r22/xq/xqd.py`) and queue-search helpers with `FLAGS_CCW` from `r22/lean/kinds/runs/xqcc/recipe_cc.txt`;
    - `xqaudit.py --plan`, which must report AUDIT OK;
    - the lazy emission `py/emitlazy.py`: item keys, stub item modules with item lists, Cov chunks (`py/mkaggf.py`), and the top
      `<P>.Top` (`#kmRekeyCC`);
  - `mkpkgw.py`: the package manifest and `kmod_unit.sh`. Each item-module unit converts its items at build time
    (`py/unitconv.py`: `pcseg`, `kitem`, `itemkey`), then runs `kmod_build.sh`;
  - `CLOSURE`: the library closure that `emitcc.sh` and every unit check before they run: name `kinds_v4` and three `.olean` sha256;
  - `lpath_common.txt`: the LEAN_PATH, with `@CLOSURE_ROOT@` and `@LEAN_TOOLCHAIN@`;
  - `r22/lean/kinds/py/joinemit.py`: the join emitter.
  - Data: `canon/tab.json`, `kernel/root/zx.txt`, `l1/hyp7.bin`. The CC tables are in `zenodo/caseII_cc436_422.tar.zst`.
  - `BUNDLE_77b5632621a1563c.sha256`: the `sha256sum` listing of the production bundle, binaries and tables included. The first 16
    hex digits of its sha256 are the version.
  - `BUNDLE_77b5632621a1563c.tsv`: for each file, its production sha256, the sha256 of the copy here, and how they differ (path
    placeholders and comments). `joinemit.py` and `mkaggf.py` here also carry the join's options (`SKIPSEG`, `AGG_LEVELS`).
    Package emission sets neither option, so these two copies give the bundle copies' output.
  - `versions/<version>/`: for each of the five earlier bundle versions, its files that differ from `77b5632621a1563c`, with path
    placeholders and comment edits as above, and `BUNDLE_<version>.tsv` (production sha256, sha256 here, difference). To emit with an
    earlier version, copy `bundle/` and put the version's files over it at the same paths (see Tool versions).
- `tools/`:
  - phase 0: `phase0_run.sh`, `expand.py`, `recut.py`, `probe.py`;
  - job tables: `mkjobscc.py`, `mkx.py`, `mkorder.py`;
  - packages: `mkpkgcc.py`;
  - join: `mkjoinpkg.py`;
  - table data: `mkcc.py`;
  - comparison hashes of pcerts: `pcrec.py`;
  - library generators: `mkloadcc.py`, `mkmodcc.py`, `tomod.py`, `rename.py`;
  - cases I and I13 (`case321/`): `w321.sh` with `recipe_321.txt` (the queue run), `splitpkg.py` and `splitrun.py` (the split
    packages), `mkstage321.sh`, `mkimod321.py`, `mkpkg2.py`, and `mkaggf.py`, the aggregation emitter that wrote the chunks and tops
    of the cases I and I13 packages. It is the version before `34b2a0f7` (the same file as
    `bundle/versions/d4258187d500b0d1/r22/lean/kinds/py/mkaggf.py`): it writes no deny-list line. `splittest.sh` (in `tools/`)
    tests the split packages.
- `BINARIES.sha256`: the production binaries: `prof7R3q_b12d`, `prof7R3q_b14`, `prof7R3k14c`, `r3qglue`, `libhighs.so.1`, and
  `gen7c`, the v7 leaf-certificate generator that `py/kitem.py` calls.
  - `search/src/gen7c/gen7c.cc` is gen7c's source. `build.sh src/gen7c/gen7c.cc OUT` compiles it with `generators/e1g/cpp/gen7.h`.
  - That build (sha256 `a19c4072…`) and the production binary (`a2777304…`) give identical certificates, bit counts and node counts
    on 834 profile leaves. These are the leaves of one item module of a selected package in the pre-registered re-check.
- `BUNDLES.tsv`: the emitter bundle version of each package. `BUNDLE_FILES.tsv`: the files and sha256 of every bundle version.
- `CASE321_TOOLS.tsv`: the tool versions of each cases I and I13 package (`I.321`, `I13.L000`-`I13.L078`, `I13.J`), with the
  `mkstage321.sh` arguments and how each mapping was verified.

### inputs/caseII/

- `jobs_cc.txt.zst`: the 151,993 case-II jobs. Format: `batch idx depth est labels…`.
- `jobs_x.txt.zst`: the 144,855 sub-jobs of the 866 expanded jobs. Format: `x_<batch>_<idx> idx F est labels…`.
- `phase0_inputs.tar.zst`:
  - `phase0/`: `batches.tsv` (the 61 phase-0 batches: name, depth F, …); the PFILEs `pfile_<batch>.txt`; the frontier DUMPs
    `dump_<batch>.txt`. In 59 batches the native table gives the same DUMP. `phase0/native/` holds the native DUMPs of the other
    two batches (`topB_00`, `poolG_poolI_d16_000`).
  - `plan1/`: the native job selection, `<batch>.jobs` (indices into the native DUMPs), `jobs.tsv`, `ratios.tsv`, `summary.txt`.
  - `run1_sizes/`: the per-job node counts that `mkjobscc.py` scales into `est`.
  - `expand/`: `expand.tsv` (the 866 expanded jobs: batch, idx, depth, est, F, frontier size, pcert bytes, seconds), `probe.tsv`,
    `pfile_x_*.txt`, `dump_x_*.txt`.
  - `recut/`: `recut.tsv`, `recut_ids.txt` (the 54 join segments re-cut in two levels), `pf1_*`, `pf2_*`, `dump_r1_*`, `dump_r2_*`.
- `PCERTS.tsv`: the 1,035 phase-0 pcerts of the join (61 batches, 866 expansions, 108 re-cut runs, 42.1 GB). Columns: name, bytes,
  sha256 as produced, header sha256, records sha256 (see Determinism).
- `PACKAGES_KM2.jsonl.zst`: the 18,108 package specs, in the join's order (the `jobs_cc.txt` packages, then the `jobs_x.txt` ones).
  Fields:
  - `jobfile` and `lines`: the package's job lines;
  - `sha256`: the production kit tarball, which holds `spec.json` and `emit.sh`;
  - `spec_json_sha256`: the kit's `spec.json`;
  - `emit.object`: the kit name.
- `PACKAGES_JOIN.jsonl`: the specs of `II.JOIN4I` and `II.JOIN4C`.
- `join.json`: the join emission's counts, roots and pcert sha256 list. `emit_join.json`: its emission record (bundle, binary and
  table sha256, recipe checks).
- `recipecheck.txt`: the output of `recipecheck.py recipe_cc.txt FLAGS_CCW`.
- `MKCC_INPUTS.sha256`: the data inputs of `mkcc.py`, at their tree paths.
  - From the native release's Zenodo record (10.5281/zenodo.23236154):
    - `data/tables/tab_C3eD.bin` and `data/tables/kept_C3eDc4d.txt`;
    - `data/lean/48752ee91aa3a82f686338f91f508896/C3eD.c2t`;
    - `data/lean/c2624c174a573a8334132808166253b2/kept3eD_lab.bin`;
    - `data/lean/46cc737594e4597c5185c50c1513fb11/kept3eD.bin`.
  - In `zenodo/caseII_mkcc_inputs.tar.zst`: `rows3eD.npz` (the kept rows' masks and caps) and `mm3_table.npz` (the table's class
    labels, read by `m2lib.Table`).
- `mkcc/`: the two code inputs of `mkcc.py`, with path placeholders: `m2lib.py` (table helpers; placed at `$KINDS_R22/math2/m2lib.py`)
  and `FLAGS_NATIVE14.txt` (the FLAGS template, placed at `lean/rerun/r3/rt479/`).
- `case321/frontier_d1_321.txt`: the depth-1 jobs of cases I and I13. Job 0 is root 0, job 1 is root 168, job 2 is the dead root 462.

### Zenodo record

| archive | bytes | sha256 | contents |
|---|---|---|---|
| `caseII_cc436_422.tar.zst` | 181,959,935 | `34fb4b6efa2f37644fb9fae7027d2ab4bb132516250a02f2f5ebc821e5af7371` | `data/cc/cc436_422/`: the CC route's table data (table, kept rows, label rows, RT entries, peel tables, binding rows, lowered rows, FLAGS line, pcert headers `hdr_*.r3`), 522 files, 1.12 GB unpacked |
| `caseII_lib_data.tar.zst` | 41,220,887 | `f9cca15b6597aaa05e22f19d6359b81ef334ac2983ae9909989e2ba7671d04aa` | `data/`: the library's 1,026 data files (`DATA.sha256`), 328 MB unpacked |
| `caseII_mkcc_inputs.tar.zst` | 62,544,452 | `714072b212d681a77242400360dcd335d4ff20e4e300059de0b8ca3a94f8c83c` | `mkcc/rows3eD.npz` and `mkcc/mm3_table.npz`, the two inputs of `tools/mkcc.py` that are not in the native release's record (468 MB unpacked) |
| `caseII_join_src.tar.zst` | 82,419,235 | `62f849cf964b9ac1c29c451420fe6ec554c5a2cb68c037fbd2d5563b255b566e` | `JOIN4I/`: the item stubs and item lists `KM2.I*` (`id seg:p0/<pcert>:<segment> 0 0 key dead`), `manifest.tsv`, `KM2_waves.txt`, `pkgs.exports`, the manifest; `JOIN4C/`: the chunks `KM2.A0`-`KM2.A79` with their `.spec`, `KM2.Top`, `manifest.jsonl`, `emit.json`, `join.json` |

The phase-0 pcerts (42.1 GB) are not archived. Phase 0 regenerates them (see Determinism), and `PCERTS.tsv` holds their hashes.

## Build the library

```
zstd -dc caseII_lib_data.tar.zst | tar xf -      # in lean/caseII: creates data/
LEAN=<toolchain>/bin/lean DEPS=<S4 build>:<KMod build>:<port build>:<Mathlib and its packages> \
  ./build.sh $(cat build_order.txt build_order_ext.txt)
sha256sum -c OLEANS.sha256     # reports exactly the five files of DOCSTRING_EDITS.tsv, whose new sha256 it lists
```

## Regenerate

The tools read their inputs at the tree paths that the production run used, under `KINDS_R22`, or `R22` for the shell scripts.
`emitcc.sh` also needs `KINDS_BUNDLE`, `CLOSURE_ROOT` and `LEAN_TOOLCHAIN`. Placeholders `@R22@`, `@BASE@` and `@SHM@` stand for
the tree root and the base-table directory.

1. **CC table data.**
   - Place the inputs of `MKCC_INPUTS.sha256` and `mkcc/` at their tree paths under `KINDS_R22`. Put `tab_C3eD.bin`,
     `kept_C3eDc4d.txt` and `mm3_table.npz` in `MKCC_BASE`.
   - `KINDS_R22=<tree> MKCC_BASE=<dir> python3 tools/mkcc.py cc436_422 "436:19,422:19"` writes `data/cc/cc436_422/`.
   - From the released inputs alone, its 518 data files are byte-identical to the archive. The FLAGS file differs only in the
     paths it names.
2. **Phase 0.**
   - `tools/phase0_run.sh`: the 61 batches;
   - `tools/expand.py jobs_cc.txt 5e5 1e5 PAR`: the 866 jobs above 500,000 estimated nodes. Each starts at F = depth + 2 and is
     deepened while its estimate per frontier entry exceeds 1e5;
   - `tools/recut.py recut_ids.txt PAR`: the 54 re-cuts.
   Each run is `prof7R3k14c FLAGS_CCW --pctop F PFILE --pcert … --dumpfrontier … --threads 1`.
3. **Job tables.**
   - `tools/mkjobscc.py jobs_cc.txt` (from `plan1/`, the DUMPs and `run1_sizes/`) regenerates `jobs_cc.txt` byte for byte.
   - `tools/mkx.py jobs_cc.txt jobs_x.txt` (from `expand.tsv` and the expansion DUMPs) regenerates `jobs_x.txt` byte for byte.
4. **Packages.**
   - `tools/mkpkgcc.py JOBS OUTDIR STOREDIR [TARGET] [HEAVY]` writes the package kits (`spec.json` and `emit.sh`, packed with fixed
     tar metadata) and their PACKAGES lines. Two runs give the production splits and `spec.json` files byte for byte:
     - `mkpkgcc.py jobs_cc.txt OUT STORE 8e4 1e30` gives 11,047 packages. The 10,181 without an expanded job are the `KM2P` packages
       of the final set.
     - `PKG_PREFIX=KM2X mkpkgcc.py jobs_x.txt OUT STORE 3e5` gives the 7,927 `KM2X` packages.
   - Per package, `emit.sh` runs `bundle/emitcc.sh`, then the manifest's units run `./kmod_unit.sh <module>`.
5. **Join.**
   - Run `bundle/r22/lean/kinds/py/joinemit.py P0DIR jobs_cc.txt,jobs_x.txt PACKAGES OUT KM2 PAR` with `SKIPSEG=recut_ids.txt` and
     `AGG_LEVELS=1`. Here P0DIR holds the 1,035 pcerts and the phase-0 records.
   - Then run `bundle/mkpkgw.py OUT KM2 BUNDLE TIMES`, and `tools/mkjoinpkg.py OUT PACKAGES OUTDIR STOREDIR`:
     - `JNAME=JOIN4` writes the item package `II.JOIN4I`;
     - `JNAME=JOIN4C JITEMS=II.JOIN4I JSKIPI=1` writes only the chunk package `II.JOIN4C`, over the built `II.JOIN4I`.
6. **Cases I and I13.** Inputs:
   - From the native release's Zenodo record (10.5281/zenodo.23236154):
     - `data/tables/tab_C3eD.bin`, `data/tables/kept_C3eDc4d.txt`, `data/tables/C3eD_321.c2t` (`ce58f101…`),
       `data/tables/kept3eD_lab321.bin` (`f55cb1a4…`) and `data/tables/frontier_d1_321.txt` (`4d41cbf5…`);
     - `data/lean/057c18088377951db54aaf82089d3d6e/hyp7_321.bin` (`47c3e483…`) and
       `data/lean/46cc737594e4597c5185c50c1513fb11/kept3eD.bin` (`a43a3aa3…`).
   - From the frozen port: the 321 key table, which `py/kitem.py` reads with `XQ_ORD=321` from `src/Top/Root321.lean` (md5
     `e90210e5…`, listed in `MANIFEST_FULL.md5`).
   - Paths: `py/xqitems.py` hands kitem the kept rows at `/dev/shm/r22/kept_C3eDc4d.txt`, so that path must hold the released
     file, for example as a link. Every table goes at its tree path under `KINDS_R22`.
   - The `case321` scripts run at their tree paths too: `mkimod321.py`, `splitpkg.py` and `mkaggf.py` in `lean/kinds/py/` (this
     `mkaggf.py` replaces the bundle's), `mkstage321.sh` and `mkpkg2.py` in `lean/kinds/runs/reh/`. With the bundle's `mkaggf.py`
     instead, every chunk and top source carries one deny-list line more.
   Steps:
   - The queue runs: `tools/case321/w321.sh FLAGS_IW QD 0 1` and `w321.sh FLAGS_I13W QD 0 1`. They use `prof7R3q_b14`, the 321-order
     tables of the native tier, `BASE_TABLES` and `FRONTIER`.
   - Case I: `py/xqitems.py` (`XQ_ORD=321`), then `tools/case321/mkstage321.sh KMIA 0 12 ITEMDIR 60 100` (MAXS 60, FANIN 100, as in
     production), then `mkpkg2.py`.
   - Case I13: `tools/case321/splitrun.py PLAN WORK KMJ 13 13`, which writes the 79 leaf packages and the join package (its defaults:
     MAXS 60, FANIN 400, BUDGET 4e8, MAXROOTS 400).

## Determinism

- **CC table data.** `mkcc.py` regenerates all 518 data files byte for byte from the released inputs (`MKCC_INPUTS.sha256`, `mkcc/`).
- **Library.** The library sources and `data/` determine the module files.
  - Rebuilding the six modules that read data files reproduces all four files of each module, as listed in `OLEANS.sha256`:
    `KB.TabC_cc436_422`, `KB.CC_cc436_422_S`, `KB.CC_cc436_422_Bc1`, `KB.BindII_00`, `KB.BindII_c1` and `KB.StatII`.
  - Rebuilding the five modules of `DOCSTRING_EDITS.tsv` from the sources here gives the production `.olean` and `.ir` files.
  - Readers compare `.olean` hashes.
- **Phase 0 (pcerts and DUMPs).** The same command on the same tables gives the same pcert, apart from three run-specific header
  lines: `#R3PC 1 fp=…`, the per-run fingerprint; and `#table …` and `#kept …`, the table paths.
  - `tools/pcrec.py` hashes the header without these lines, and the records.
  - Readers compare these two hashes with `PCERTS.tsv`, and the DUMPs byte for byte.
  - Two batches were rerun, `poolC_poolE_d12_000` and `topB_03`, once with the production binary and once with a binary built
    from `prof7R3_b14.cc` here. Both runs gave the same header hash, records hash, length and DUMP.
- **Job tables and package specs.** `jobs_cc.txt` and `jobs_x.txt` regenerate byte for byte.
  - So do the package splits and all 18,108 `spec.json` files (the two `mkpkgcc.py` runs above).
  - The kit tarballs also hold `emit.sh`, whose bundle location differs here, so readers compare `spec_json_sha256`.
- **Search packages.** The queue search hands out work dynamically: helpers donate subtrees, and the item-size cap splits work.
  - So a package's items, their modules, and its module files vary from run to run.
  - Each package's public statement does not vary: `<P>.Top.cov : R22N.AllL KB.CovOfKeyCC [the minimal keys of its job roots,
    sorted]` (`#kmRekeyCC`, `KB.ModRekeyCC`), which depends only on the package's job lines.
  - Readers compare this statement and its axioms, not `.olean` hashes.
  - The join imports the packages' tops by name and uses only these statements.
  - The package `II.KM2P000188` was regenerated end to end from the files here. The steps were `mkpkgcc.py`, `emit.sh` with the
    bundle copy here (1 job, 1 item, 140 records, 3 units) and `kmod_unit.sh`.
    - This was done twice: once with the production `prof7R3q_b12d` binary, and once with `prof7R3q_b12d` and `r3qglue` built by
      `build.sh` from `src_b12/prof7R3q.cc` and `src/xq/r3q/r3qglue.cc`.
    - Both times, `KM2P000188.Top.olean` and `.olean.server` are byte-identical to the production files.
    - Both times, every unit's KAXSUM reports bad 0 and local_axioms 0.
    - A one-item package has no split to vary.
- **Join.**
  - The item lists of `KM2.I*` depend only on the pcerts' records and the bundle tools. Two separate emissions gave identical item
    lists.
  - The item modules' sources are written at build time from the item lists and the pcerts. They import only library modules.
  - The chunks `KM2.A*` and `KM2.Top` depend on the item lists, the job tables and the package list (`AGG_LEVELS=1`).
  - The join was re-emitted with the tools and inputs here: the bundle copy with placeholders, `jobs_cc.txt`, `jobs_x.txt`,
    `PACKAGES_KM2.jsonl` and `recut_ids.txt`. It used the production pcerts and the production per-segment feature cache.
    - All 9,353 source files came out byte for byte the same: item stubs, item lists, chunks, `.spec` files, `KM2.Top`,
      `manifest.tsv`, `KM2_waves.txt` and `pkgs.exports`.
    - `join.json` came out the same too.
  - Readers compare the item lists and chunk sources with `caseII_join_src.tar.zst`, and the public statement of `KM2.Top.segs`:
    `R22N.AllL KB.SegsOfKeyCC [1]`.
- **Cases I and I13.** The same holds as for the search packages.
  - Item splits vary. The public statements of `KMIA.Top.vI` and `KMJJ.Top.vI` depend only on the job roots.
  - A leaf's root chunk `<leaf>.A<j>.cov` covers the roots of its subtrees, so it depends on the queue run's item split as well.
  - The re-check's leaf-level comparison of I13 uses the production queue run's plan and segments. Those are privately archived and
    are not in this release.
  - A fresh regeneration reproduces the I13 top statement `KMJJ.Top.vI` with its own item split. This is the same split-dependence as
    in case II.
  - Given a package's items, its sources do not vary. The staging step of `mkstage321.sh` (`mkimod321.py` for the root 462,
    `mkslice2.py`, and `tools/case321/mkaggf.py`) was re-run on the item dirs of each of the 81 production packages
    (`data/q/*.d`). For every package it gives every module source, spec, export map and wave byte for byte: 4,756 modules (149 of
    `I.321`, 4,607 of I13) from their 43,258 item dirs.
    - `manifest.tsv` comes out identical for `I.321`. For the I13 packages, its column 6 (the item modules' predicted peak GB)
      differs: the production I13 emission predicted with the peak model of `mkimod321.py` before its widening, and the packages'
      `manifest.jsonl` were updated to the widened model before the production build.
    - With the bundle's `mkaggf.py` instead, the 225 chunk and top sources each carry one deny-list line more, and are otherwise
      identical.
- **Binaries.** `BINARIES.sha256` lists the production binaries.
  - `r3qglue` rebuilds byte for byte from `r3qglue.cc`.
  - The case-II package emissions ran `prof7R3q_b12d`, built from `src_b12/prof7R3q.cc` (md5 `e6bd66cf3d9b06969b9ced0049186326`).
    The `b12/` merge scripts regenerate that source from `prof7R3_b12.cc`.
    - A build with the production flags and paths gives the production binary byte for byte (sha256 `164e19eaca7b564d…`).
    - The build with `build.sh` here differs in bytes. It gives the same pcert and DUMP, and regenerates `II.KM2P000188` end to end.
  - The search binaries embed their build paths, so a rebuild with `build.sh` here differs in bytes but gives the same pcerts, as
    checked above.
  - No proof step depends on a binary: the kernel checks every item and every aggregation step.

## Tool versions

The case-II packages were emitted by six versions of the emitter bundle. Each package used one version; `BUNDLES.tsv` lists them.

| bundle | tarball sha256 | packages | change from the previous version |
|---|---|---|---|
| `2160bb66c4a52525` | `af3dd754b64923517ab6c6d144f2ecd82c85fc774168aedbd630f63234814646` | 1 (`II.KM2P008803`) | first version |
| `d4258187d500b0d1` | `9bce645c2338f007365b54385668af96e37a0f8567878031089c7182edb9cc1c` | 1,570 | closure check (`CLOSURE`) in `emitcc.sh` and in every unit; manifests record `closure`; memory prediction `max(1.6, peak − 0.5)` GB |
| `34b2a0f77dbb18b7` | `c5fbd7c324a1ca7f915ef90628847ed3488c810b12c58aa9c23049865c5bb370` | 1,877 | deny-list lines in item modules (`R22N.KeysOK`), chunks and tops (`R22N.AllL`); `kmod_unit.sh` written atomically |
| `9c9a9612e5319b30` | `d48d5b64f5379450e7436a7477d348e28a68dd483880eb3a333a6b9a6f5c4433` | 13,727 (with JOIN4I and JOIN4C) | jobs are added once a helper is connected |
| `57a95ac68fd635ce` | `a416a810245e1847a1921bdfa3ad79992279cd4addb015a8832acff37f14c1db` | 908 | default helper threads: half the cores, at most 128; units exit 5 without a source, and 4 on a build without a `.kman` |
| `77b5632621a1563c` | `22ae7e2b5956e1783446aebc7cc942474dc52c581cecbb23061a2d5b11e4d292` | 27 | the emission stops its queue server and helpers on exit |

- Every case-II package is built against the library closure `kinds_v4`, the one in `OLEANS.sha256`.
  - The versions from `d4258187` on check this closure before they emit or build.
  - The final environment's modhash gate passes for every package, the `2160bb66` package included.
- Every version uses the same binaries and tables (`BUNDLE_FILES.tsv`).
- `bundle/versions/<version>/` holds each earlier version's files that differ from `77b5632621a1563c`, edited in the same way
  (path placeholders, comments). `BUNDLE_<version>.tsv` gives each file's production sha256, its sha256 here and the difference.
  To emit with an earlier version, copy `bundle/` and put the version's files over it at the same paths. `2160bb66` has no `CLOSURE`
  file, and its scripts do not read one.
- What each version emits, compared with `77b5632621a1563c`:
  - `2160bb66`: item modules, chunks and tops without the deny-list lines; manifests without `closure` and with the earlier
    memory prediction; `kmod_unit.sh` without the closure check and without the exit codes 5 and 4.
  - `d4258187`: item modules, chunks and tops without the deny-list lines; `kmod_unit.sh` without the exit codes 5 and 4.
  - `34b2a0f7`, `9c9a9612`: the same module sources; `kmod_unit.sh` without the exit codes 5 and 4.
  - `57a95ac6`: the same module sources and package files.
  - Every version writes its own version string into the manifests and the emission record.
- The versions before `34b2a0f7` write item modules, chunks and tops without the deny-list lines. Those lines change no statement.
- **Cases I and I13.** Their packages were not emitted by a bundle version. They come from the `case321` tools and the queue search
  `prof7R3q_b14`. `CASE321_TOOLS.tsv` maps each of the 81 packages to the versions of the 21 tools involved and to the
  `mkstage321.sh` arguments used.
  - Their chunks and tops were written by the `mkaggf.py` before `34b2a0f7`, without deny-list lines: `tools/case321/mkaggf.py`, whose
    production version (sha256 `298a682196fe773c…`) differs from it only in a default path. Run on the production item modules, it
    reproduces the chunk and top sources, specs, export maps, its `manifest.tsv` rows and the waves of all 81 packages byte for byte.
  - The production copies of the other scripts were not archived with the packages. The versions here reproduce every module
    source of all 81 packages from their item dirs (Determinism). The whole I13 pipeline from the production queue run gives the
    item dirs and item module sources of the three leaves of the pre-registered re-check byte for byte; their chunks, written there
    with the bundle's `mkaggf.py`, differ by the deny-list line only.

## Sizes

- In this repository: 15.6 MB in 248 files. Largest file: `lean/caseII/tops/KMJJ/A0.spec`, 3.7 MB.
- In the Zenodo record: 368 MB in four archives.
