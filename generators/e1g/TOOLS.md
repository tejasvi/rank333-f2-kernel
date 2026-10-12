# e1g generator tools: versions, binaries, settings, and the packages each produced

## The tools tree

Every e1g package was emitted by `emitpkg.sh CAP A B PKGDIR [options]` from a tools tree:

```
TOOLS/emitpkg.sh      runs py/emitpkg.py with --tools TOOLS (package mode: every input from TOOLS/ip, binaries from TOOLS/bin)
TOOLS/py/             emitpkg.py, kjlib.py, mkslice.py, mkagg.py, mkcut_pt.py (mkcut_pt.py from v7.1 on)
TOOLS/bin/            lineenum9qe_ld5, e1pconv
TOOLS/lib/            libhighs.so.1
TOOLS/ip/             the IP, order and frontier files (inputs/e1g)
```

The aggregation packages ran `python3 TOOLS/py/mkagg.py CAP {OUT} {DEPS} --tools TOOLS [--heavy-only]`.

`sh/mktools.sh VERSION OUTDIR [BINDIR]` assembles the tree of one version from this directory and `inputs/e1g`.

## Binaries

All six versions ship the same three binaries (`BINARIES.sha256`):

| file | sha256 | source |
|---|---|---|
| `bin/lineenum9qe_ld5` | `83e50eb462e343b5a18d27c80c66dbb15732245e949d004aca30f3e1362724f2` | `cpp/lineenum9qe.cc` + `packlp_avx.h`, `e1pleaf.h`, `e1pemit.h`, `gen7.h` |
| `bin/e1pconv` | `f00fa1ea04a7bf992564fa71878898c00107d0fe73adfad70846f2518f4b94eb` | `cpp/e1pconv.cc` + `e1pleaf.h`, `e1pemit.h`, `gen7.h` |
| `lib/libhighs.so.1` | `4964579253b67b4525fbe4985725560732dac3b8f178356e6699f9411e64d93a` | the highspy 1.15.1 wheel (HiGHS 1.15.1) |

`build.sh` compiles the two binaries with g++ 15.2.0 (`-O3 -march=native -std=c++17 -pthread -static-libstdc++ -static-libgcc`).
On the production build host it reproduces both sha256 values exactly from the sources in `cpp/`. Because of `-march=native`, a
build on another CPU model gives different bytes; such binaries are functionally equivalent, but regenerated certificates
can then differ in their bytes (see PART.md, determinism).

## Versions

Each version is a tarball of the tree above. Its sha256 is the production identity of the version, recorded in every
package's provenance. `tools/<version>/` holds that version's `py/` and `emitpkg.sh`.
`tools/FILES.tsv` lists, for each file, the sha256 in the production tarball and the sha256 of the copy here. The copies
differ only in comments and in the development-layout defaults of `kjlib.py`, `emitpkg.py`, `mkagg.py` and `mkcut_pt.py`,
which package mode overrides (`configure(out, tools)`). The binaries are the same in every version, and so is every input
file: v3 reads 906 of the 1,081 files in `inputs/e1g` and lacks the class contexts. One input file is written for release:
`ip/hcap/ana/roots_fixed.txt` names the class frontiers relative to `ip/`, where production gave them under the absolute
development root, which `kjlib.load_class_contexts` strips.

| version | tarball sha256 | adds (package mode) |
|---|---|---|
| v3 | `035f661f4d3c3cad5d614e7e4709a7949958b0a87fdba1a82d3ae812c6ad1a93` | the c436 / c422 production emitter: ranges, splits, heavy sub-jobs and heavy splits; mkagg |
| v7.1 | `f0718c2d3fffa48b7b5625ce8070624a8248d6d88f4eb4ba8194f39b9538bd09` | `--budget`; the batched split (`KJ_BSB_PAR`, `KJ_BSB_BUDGET`); the class contexts h<c> (package KC, contexts looked up after `configure`); mkcut_pt.py |
| v8 | `ac2d3a4624bd10a5c32d00c8dc2c4e5c1da27bcd42f2a3f32c6ee010cb762d5f` | the point tier over the frozen port's `E1P.Hdr` and `HPt`, with `E1PQ` |
| v8.2 | `5594aa9af67549916feed9aa8fe483e0ef8dbf70f307e79d0c5a85deec0a4b0d` | mkagg over `{DEPS}` (a directory of package directories), heavy-only DONE ranges, the root's external-leaf export `Root<C>.ext.txt`; kjlib and emitpkg as in v8 |
| v8.3 | `26557633e8175fd95594a67158155054fe5f15aad30be7fe1f59271e186c8f19` | `KJ_PROC_PAR`: sub-splits of the batched split in forked processes (a semaphore of N slots shared by the process tree) |
| v8.5 | `0ab0f15919fded6775a5ae21c8ee422d784ce7c36f4054cbe5bae3b8effd2d80` | failed sub-jobs re-emitted alone with a raised gen7 budget (`GEN7_BOOST`), then split deeper; per-split data directories `data/j/<split>/`; `E1P_EXTBITS` only for contexts with external leaves (0 for the point tier, whose leaf certificates stay inline) |

## The packages each version produced

The final package set has 95,759 e1g packages (`inputs/e1g/packages.tsv.zst`, role `final`). The split builds build the
emitted trees of 25 packages (role `split-source`) without re-emitting them.

| version | settings | final packages | split sources |
|---|---|---|---|
| v3 | `--threads 4` | 15,355: heavy-split 13,554; split 1,305; heavy-sub 488; range 8 | 0 |
| v7.1 | `--threads 4 --budget 300000` | 2,106: heavy-split 1,695; split 411 | 10 heavy-split |
| v8 | `--threads 4` | 72 point packages: split 54 (`pt_*.v8`); range 18 | 1 (`pt_0011.v8`) |
| v8 | `KJ_BSB_PAR=7 KJ_BSB_BUDGET=20000 --threads 24` | 3 point splits (`pt_*.v9`) | 0 |
| v8.2 | `--threads 4` | 76,266: heavy-split 39,848; heavy-sub 32,000; split 2,510; range 1,908 | 4 heavy-split |
| v8.2 | `KJ_BSB_PAR=5 KJ_BSB_BUDGET=100000 --threads 32` (ids `.re`) | 0 | 7 heavy-split |
| v8.2 | mkagg | 451 aggregation packages: agg-heavy 448 (`--heavy-only`), agg-root 2 (c436, c422), agg-point 1 | |
| v8.3 | `KJ_PROC_PAR=24 KJ_BSB_PAR=2 KJ_BSB_BUDGET=100000 --threads 4` (ids `.r2`) | 1 heavy-split | 3 heavy-split |
| v8.3 | `KJ_PROC_PAR=32 KJ_BSB_PAR=2 KJ_BSB_BUDGET=20000 --threads 3` | 6 point splits (`pt_*.v10`) | 0 |
| v8.5 | `KJ_PROC_PAR=8 KJ_BSB_PAR=2 KJ_BSB_BUDGET=20000 --threads 16` | 2 point splits (`pt_0001.v13`, `pt_0010.v13b`) | 0 |
| split build | `py/splitbuild.py` groups over a split source's emitted tree | 1,497: 1,472 groups and 25 finals | |

The class tier's 16,566 class packages were emitted with v7.1 as well (generators/classes); they are not counted above.

## Settings

- `--threads T`: lineenum9qe_ld5's worker threads per emission.
- `--budget B`: the node budget of a split level's DUMPONLY pass.
- `KJ_BSB_PAR`, `KJ_BSB_BUDGET`: concurrent batches and the node budget per batch of the batched split.
- `KJ_PROC_PAR`: the number of forked-process slots for sub-splits.
- `--name NAME` (`.re`, `.r2` ids): module names distinct from those of the original package of the same job.

Every option is recorded in the package's spec line (`inputs/e1g/spec_lines.jsonl.zst`).
