# The CC route, the EXT tier, the G2 crowns and the final top

This document covers:
- the Lean sources of the final theorem (`R22K`);
- the CC route in case (II) (`S4`, `HC436`);
- the kernel crowns of classes 303 and 321 (`G2`);
- the generators and inputs of the EXT tier: the external leaves of the two plane caps and of the 21 class-raise classes.

`README.md` summarizes two topics of this document: the CC route, and the equal-first-factor reduction.

| path | size | contents |
|---|---|---|
| `lean/DOCSTRING_EDITS.tsv` | 6 KB | production and shipped sha256 of the outputs of the 15 docstring-edited modules (Section 9) |
| `lean/final/` | 1.0 MB | `R22K` sources, their generators, match checks, olean hashes |
| `lean/cc/` | 13.9 MB | `S4` (18 modules), `HC436` (6 modules) and their data, `g2/` (G2 hand-written sources, generators, manifests, checks), olean hashes |
| `generators/ext/` | 1.0 MB | C++ sources of the five EXT generators, `build.sh`, `BINARIES.sha256`, the emitter scripts of every tools version used, the package-to-tools table |
| `inputs/ext/` | 44.4 MB | the EXT leaf lists, the leaf-list objects, the top inputs, the cut specs, the IP constants |
| Zenodo record | 777.4 MB | `g2_src_generated.tar.zst`, `g2_data.tar.zst`, `g2_split.tar.zst` |

## 1. `lean/final/`: the final theorem

| path | what it is |
|---|---|
| `src/R22K/FinalTop.lean` | `R22K.FinalTop.rank_ge_23 : Top.RankGe23`, from each tier's published root statement, through `Top.rank_ge_23_436_422` |
| `src/R22K/Cap.lean` | `R22K.Cap.hCap`. This is `R22B.CapLeaf2` of the frozen port, renamed. The CovG facts of classes 303 and 321 are replaced by the statements of the G2 crowns, and the job facts of the 21 raise classes by class certificates. It is the output of `py/mkcap.py`. |
| `src/R22K/FinalAll.lean` | `R22K.FinalAll.rank_ge_23_of`. It is FinalTop with `hrr := HC.rr_all` and `hCap := R22K.Cap.hCap …`. Its 93 hypotheses are each a published root statement. It also holds `x_nil`. It is the output of `py/mkftall.py`. |
| `src/R22K/Cor.lean` | `R22K.Cor.rank_eq_23`, `mm_equiv`, `table_23`, `recursive_23` (output of `py/mkftall.py`) |
| `src/R22K/Final.lean` | `R22K.Final.rank_ge_23` and four corollaries: `rank_ge_23_of` applied to the producers' theorems. It is the output of `py/mkinst.py --kII 1 --ext <21 classes>`. sha256 `330f8a7baad895d088afba4423673bd13b9e1b5a83d8baa74495d2f7f3436737` |
| `src/R22KChk/Axioms.lean` | `#print axioms` of the five public theorems of `R22K.Final` |
| `py/mkinst.py`, `py/mkftall.py`, `py/mkcap.py` | the generators of Final.lean, of FinalAll.lean and Cor.lean, and of Cap.lean |
| `py/mkmatchk.py`, `chk/src/R22KChk/MatchK_h<c>.lean` (21), `chk/MatchK.out`, `chk/log/` | For each raise class, the class root `KC.h<c>.classLB` and its EXT top `NDX.h<c>.x<c>` are checked against the binders of `rank_ge_23_of`. Result: 21 of 21 apply; each `kc<c>` is `Expr`-equal and each `x<c>` defeq. |
| `chk/src/R22KChk/MatchCC436.lean`, `chk/log/MatchCC436.out` | the cap producers `KJ.agg436/422.Root.{EXT,root}`, `PLE.c436/c422.Ext.{EXT,hext_of}` and `PLE.c436/c422.Sub.sub` applied to `rank_ge_23_of` (type-checks) |
| `build_final.sh` | builds the five `R22K` modules in KMod form, prints the axioms, compares with `OLEANS.sha256` |
| `OLEANS.sha256` | sha256 of `R22K/{Final,FinalAll,FinalTop,Cap,Cor}.olean`, `R22K/Final.olean.private`, and the `.olean.server` of the docstring-edited modules (Section 9) |

## 2. `lean/cc/`: the CC route and the c436 context IP

| path | what it is |
|---|---|
| `src/S4/TopCC.lean` | `L479.cLBW`, `L479.fact18`, `L479.classFactsW_of`, `L479.CCInst`, `L479.capG_of_inst`, `Top.rank_ge_23_CC` |
| `src/S4/Top436.lean` | `Top.rank_ge_23_436_422` (`rank_ge_23_CC` at `L = [(436,19),(422,19)]`) |
| `src/S4/CC436.lean`, `src/S4/CC422.lean` | `L479.CC436.inst`, `L479.CC422.inst` (`L479.CCInst c 19 14`), `inst_cert` |
| `src/S4/CCLeaf.lean` | `PL.leafNoExt_of_cert`, `PL.leaves_of_cert`, `PL.leafNoExt_of_noLiftK_rec` |
| `src/S4/PlaneLift.lean`, `SatQ.lean`, `PlaneW.lean`, `PlaneW3.lean` | the lifting test for planes (`PL.liftK_move`, `PL.leafSLQ`, `PL.ltW_sound`, `PL.entry_sound`, `PL.ltW3_sound`) |
| `src/S4/SplitQ.lean`, `SplitR.lean`, `SplitRN.lean` | split certificates (main record, sub-records, sibling ranges), `PL.noLiftK_of_items`, `PL.noDecomp_of_items` |
| `src/S4/EqF.lean` | the equal-first-factor reduction (`PL.Canon`, `PL.canon_exists`, `PL.skipOK_canon`, `PL.checkSXRE_sound`, `PL.leafSXRE_sound_paths`, `PL.noLiftK_of_itemsE`, `PL.noDecomp_of_itemsE`) |
| `src/S4/PLDrv.lean`, `PLDrvM.lean`, `PLDrvR.lean`, `PLDrvRE.lean`, `PLDrvRN.lean` | the commands that the generated package modules use: `#plsplit`, `#plhdr`/`#plpart`/`#plagg`, `#plhdr3`/`#plpart3`/`#plagg3`, `#plhdr3e`/`#plpart3e`/`#plagg3e` (and `…ne`), `#plhdr3n`/`#plpart3n`/`#plagg3n` |
| `src/HC436/{IP_c436,SL_c436,OK_c436_Base,OK_c436_S0,OK_c436_F,OK_c436}.lean` | the coset IP `c436` (`E1G.IP_c436`, `E1G.OK_c436`) |
| `data/hc436/{c436_g_gp,c436_g_sl,tab_c436}.bin`, `data/hc436/SHA256` | the tables these modules load (815 KB) |
| `build_cc.sh` | builds the 24 modules in dependency order and compares with `OLEANS.sha256` |
| `OLEANS.sha256` | sha256 of the 24 `.olean` and 24 `.olean.private` files, and the `.olean.server` of the docstring-edited modules (Section 9) |

The exported import closure of `R22K.Final` contains:
- the S4 modules TopCC, Top436, CC436, CC422, CCLeaf, PlaneLift, SatQ, PlaneW, PlaneW3, SplitQ, SplitR and SplitRN;
- the six HC436 modules.

`S4.EqF` and the five driver modules are imported privately, by generated package modules only. The generated modules (`PLE.*`, `PLX.*`, `NDL.*`, `NDX.*`) are written per package by `generators/ext/` and sit in the package archives.

## 3. `lean/cc/g2/`: kernel crowns of classes 303 and 321

`G2.Crown<c>.crown : ∀ (hcls : ∀ c, RT.Fact (RT.kM RT.Cls_e<c>.CL c) (RT.cLB RT.Cls_e<c>.CL c)), HC.E1Concl E1.IP_e<c>.Em 18`, for c = 303 and 321. Its type equals the type of the native crown `E1NR1.Crown<c>.crown` with the CovG hypothesis `g<c>` removed. That hypothesis rests on the 23 `#ndbool` facts of the port's `R1.Ext303` and `R1.Ext321`.

| path | what it is |
|---|---|
| `mod/src/G2/` (19 sources) | `G2.Crown303`, `G2.Crown321`, `G2.Disp`, `G2.Asm2`, `G2.WLoad`. For each class: the chain `C<c>X`, `C<c>X_N`, the lookups `C<c>X_F`, the witness loader `C<c>X_W`, the literal loaders `C<c>X_Lits` and `E<c>M_Lits`, and the class theorem `E<c>` |
| `tomod_g2.py`, `blocksF.py`, `mkF.py`, `blocks.py`, `splitgen.py`, `w2bin.py`, `tools/mknest.py` | the generators: module form, block modules, lookups, split leaves, witness table |
| `mod/manifest_c303.jsonl`, `mod/manifest_c321.jsonl` | the module lists (19,331 and 17,622 modules: module, G2 dependencies, source) |
| `build_g2.py`, `lean_g2.sh` | parallel build of the 36,956 modules in dependency order (`-DElab.async=false -j1 -R mod/src`, run from `g2/`) |
| `chk/StmtCrown.lean`, `.out` | each crown's type is `Expr`-equal to the type of `E1NR1.Crown<c>.crown` with its first binder dropped |
| `chk/AxAsm2.lean`, `.out`, `.tsv` | the 22 lemmas of `G2.Asm2` use only `propext` and `Quot.sound` |
| `OLEANS.sha256.zst` | sha256 of the 36,956 `.olean` and 36,956 `.olean.private` files, and the `.olean.server` of the two Lits modules (Section 9), 73,914 lines |
| zenodo `g2_src_generated.tar.zst` | the other 36,937 sources: 6,998 block modules `C<c>X_B<j>`, 1,621 chunks `E<c>M_C<j>`, and 5,507 split leaves `E<c>S<k>` with 5,507 `_Data` and 17,304 `_C<j>` modules |
| zenodo `g2_data.tar.zst` | `data/{C303X,C303X_W,C321X,C321X_W,e303_mono,e321_mono}.bin` (1.52 GB unpacked), sha256 in `data/SHA256` |
| zenodo `g2_split.tar.zst` | `l2/split/E<c>S<k>.bin`, 5,507 files (346 MB unpacked), sha256 in `l2/split.sha256.zst` |

## 4. `generators/ext/`: the EXT generators

The EXT tier proves the external leaves of the two cap instances and of the 21 class-raise classes:
- for the caps `L479.CCInst 436 19 14` and `L479.CCInst 422 19 14`, the statement `L479.LeafNoExt` for each leaf;
- for the classes h<c>, the statement `S5.NoDecomp` for each leaf.

The final set has 20,141 EXT packages:

| kind | cap | packages | modules |
|---|---|---|---|
| ext | 436 | 16,412 | 1,479,123 |
| ext | 422 | 3,287 | 293,254 |
| ext | 21 classes h<c> | 374 | 22,831 |
| splitbuild, splitbuild-final (the parts of 9 giant leaves of 436) | 436 | 36 + 9 | the modules of the 9 emissions |
| ext-top (`PLE.c436.Sub.sub`, `PLE.c422.Sub.sub`, `NDX.h<c>.x<c>`) | 436, 422, 21 classes | 23 | |

| path | what it is |
|---|---|
| `src/planecert.h` | the plane lifting certificate (rank facts, guessed terms), shared by all five generators |
| `src/gen7pc.cc`, `src/gen7p.h` | `gen7pc`: the v7 certificate walk with the plane lifting test (`--plane BASIS --pk 3 --split3`) |
| `src/gen7pc_eqf.cc`, `src/gen7p_eqf.h` | `gen7pc_eqf`: the equal-first-factor walk (`--eqf`; `S4.EqF`, `S4.PLDrvRE`) |
| `src/gen7pd.cc`, `src/gen7pd.h` | `gen7pd`: the top and subtree generator of parallel generation |
| `src/gen7pd_eqf.h` with `src/v9/gen7pd_eqf.cc` | `gen7pd_eqf_v9` (tools v9 and v10) |
| `src/gen7pd_eqf.h` with `src/gen7pd_eqf.cc` | `gen7pd_eqf` (tools v12: `--sub --dump`, `--top --assemble`) |
| `build.sh`, `BINARIES.sha256` | `build.sh` compiles the five binaries into `bin/` with g++ 15.2.0 and `-O2 -march=x86-64-v3 -std=c++17 -static -Isrc`. It checks them against the sha256 of the binaries of the production run. All five are bit-identical to them. |
| `scripts/` | the emitter scripts of tools v12: `extpkg.py` (one EXT package), `gensplit.py` (parallel generation), `mkndprod.py` (the class route), `mkexttop.py` v4b (EXT tops) |
| `versions/v1` … `versions/v10`, `versions/mkexttop_v3` | `extpkg.py`, `mkndprod.py` and `gensplit.py` of every earlier tools version that produced packages of the final set, and mkexttop v3 |
| `pipeline/` | the queue drivers, for reference: `extscan.py` (leaf discovery and grouping into packages), `aggext.py`, `aggauto.py` (aggregation), `cutgiant.py` (cut packages of giant leaves). Regeneration does not need them, because their outputs are in `inputs/ext/` and `package_tools.tsv.zst`. |
| `TOOLS_VERSIONS.tsv` | one row per tools version: the bootstrap sha256, the bundle sha256, the production and shipped sha256 of each script, the binaries in the bundle, and the packages of the final set that the version produced |
| `package_tools.tsv.zst` | one row per package (20,141 rows): id, kind, cap, tools, bootstrap, generators, env, leaves, nleaves, modules |
| `regen_ext.sh VERSION CAP LEAVES OUT` | regenerates one EXT package with the scripts of VERSION and the binaries in `bin/` |

| tools | packages of the final set | generators used |
|---|---|---|
| v1 | ext 242 | gen7pc |
| v2 | ext 868 | gen7pc |
| v3 | ext 1,222 | gen7pc |
| v5 | ext 500 | gen7pc, gen7pc_eqf |
| v6 | ext 12,416 | gen7pc, gen7pc_eqf |
| v7 | ext 1,649 | gen7pc, gen7pc_eqf |
| v8 | ext 2,675 | gen7pc, gen7pc_eqf |
| v9 | ext 117 | gen7pc, gen7pc_eqf, gen7pd_eqf_v9 |
| v10 | ext 384, splitbuild 28 + splitbuild-final 7 | gen7pc, gen7pc_eqf, gen7pd_eqf_v9 |
| v12 | splitbuild 8 + splitbuild-final 2 | gen7pd_eqf |
| mkexttop v4b | ext-top 9 (436, 422, h420, h454, h455, h470, h485, h487, h490) | |
| mkexttop v3 | ext-top 14 (h450, h451, h456, h458, h460, h463, h464, h465, h469, h471, h472, h473, h475, h476) | |

`gen7pd` is in every bundle from v5 on. It handles S, B and E leaves without repeated terms, and no package of the final set has such a leaf. 19 single-leaf packages of tools v10 and 6 of the 9 cut families run with `EXTPKG_NOSPLIT=1`. This makes `extpkg.py` use `gen7pc_eqf` for EqF leaves with flag S, B or E.

The shipped scripts differ from the production files in three ways:
- leaf-list objects are read from `$EXT_LEAVES/<object>`;
- the paths of the build environment are environment variables;
- comments are reworded.

The text they emit is unchanged. The C++ sources differ from the production sources in three comment lines, which keep their line numbers. The binaries are unchanged.

## 5. `inputs/ext/`: the EXT inputs

| path | contents |
|---|---|
| `leaves/ext_c436.tsv.zst`, `ext_c422.tsv.zst`, `ext_h<c>.tsv.zst` (23 files) | the deduplicated external leaves per cap, one line `key labels flag pl` each. The union of the leaves of the final packages is exactly these lists. |
| `extleaves/<object>.zst` (88 files) | the leaf-list objects. A package with leaves `@gs:<object>:<sha256>:<a>:<b>` takes lines a..b-1 of `<object>`, which is sha256-checked. |
| `inline_leaves.tsv.zst` | the leaves of the 1,110 packages whose spec carries them inline (tools v1, v2): id, key, labels, flag, pl |
| `tops/<cap>/chunks.txt.zst`, `order.txt.zst` (23 caps) | the inputs of the EXT tops. `chunks.txt` lists each chunk module with its pl list. `order.txt` is the root list (`KJ.agg436.Root.EXT`, `KJ.agg422.Root.EXT`, `KC.h<c>.EXT`), one pl per line, duplicates kept. |
| `cut/<family>/emission.tsv`, `g0_<k>.jsonl`, `final.jsonl` (9 families) | the giant emission (tools, env, leaves, modules, SAT leaves, parts, main-record bits) and the module lists of its cut packages. `g0_<k>` holds H and a quarter of the parts, balanced by predicted time. `final` holds H, A and the chunk. |
| `ip/IP_<cap>.lean` (23 files) | the constants R, VT, DOM and Em of each IP: the only part of the IP sources that the generators read |

| list | leaves | U | S | B |
|---|---|---|---|---|
| ext_c436 | 392,525 | 388,935 | 3,382 | 208 |
| ext_c422 | 96,469 | 96,383 | 27 | 59 |
| 21 classes | 7,446 | 7,446 | 0 | 0 |

The flags have these meanings:
- U: the enumeration's certificate exceeds 200 kbit;
- S: the residual problem has decompositions;
- B: the leaf is beyond the enumeration's search budget.

No leaf has flag E. The class lists are h420 1,196; h450 45; h451 55; h454 1,243; h455 766; h456 427; h458 295; h460 1; h463 2; h464 265; h465 148; h469 12; h470 737; h471 228; h472 134; h473 21; h475 297; h476 97; h485 1,399; h487 44; h490 34.

## 6. Build

Environment:
- `LEAN`: Lean v4.30.0;
- `LEAN_PATH_ENV`: the `.olean` roots listed in `lean/TOOLCHAIN.md`;
- `KMOD_BUILD_SH`: `lean/kmod/kmod_build.sh`, for the final top.

Steps:
1. `generators/ext/build.sh` builds the five generators and checks them against `BINARIES.sha256`.
2. `lean/cc/build_cc.sh` builds the 24 modules in a few minutes.
3. For G2, unpack the three zenodo archives into `lean/cc/` (their members start with `g2/`). Then run `python3 build_g2.py -j N --check` from `lean/cc/g2`. This builds 36,956 modules in about 565 CPU-hours of module builds, and a block module needs up to about 6 GB.
4. `lean/final/build_final.sh` needs every producer's package store and the other libraries under `lean/` on `LEAN_PATH_ENV`.

Data files are read by paths relative to the build directory: `lean/cc` for HC436, `lean/cc/g2` for G2.

## 7. Regenerate

**EXT packages.** First unpack the leaf-list objects and look up the package row:

```
mkdir -p $X && for f in inputs/ext/extleaves/*.zst; do zstd -dc $f > $X/$(basename $f .zst); done; export EXT_LEAVES=$X
row=$(zstdcat generators/ext/package_tools.tsv.zst | awk -F'\t' -v id=$ID '$1==id')
```

- **ext** (CC caps and classes): run `[EXTPKG_NOSPLIT=1] generators/ext/regen_ext.sh <tools> <cap> '<leaves>' OUT`, with tools, env and leaves from the row.
  - For a package with inline leaves, write its rows of `inline_leaves.tsv` as lines `key labels flag pl` to a file F, and pass `@F`.
  - The output is `OUT/src` (module sources), `OUT/manifest.jsonl` (modules, kinds, dependencies) and `OUT/DONE` (published theorems, leaves, per-leaf certificate sizes).
- **Module names depend only on the leaves.**
  - Leaf modules: `PLX.c<cap>.x<16 hex of sha256("c<cap>:<pl>")>.{H,P<j>,A}`.
  - The chunk: `PLE.c<cap>.X<16 hex of the sha256 of the sorted pl list>`.
  - Classes: `NDL.h<c>.*` and `NDX.h<c>.X*`.
  - A multi-leaf package id is `ext_<cap>_` plus 12 hex of the sha256 of its leaf text. A single-leaf package id is `ext_c<cap>_x` plus 16 hex of sha256(`c<cap>:<pl>`). Either kind of id can carry a suffix `_r<n>`.
- **splitbuild**: regenerate the family's emission from `cut/<family>/emission.tsv` in the same way. The cut packages build the modules of `g0_<k>.jsonl` and `final.jsonl` from that emission's sources.
- **ext-top**: run `python3 <mkexttop> <cap> chunks.txt OUT --order order.txt <args>`, with mkexttop and args from the row:
  - 436: v4b `--root-module KJ.agg436_Root --fan 25 --fan-auto`;
  - 422: v4b `--root-module KJ.agg422_Root`;
  - classes: v4b or v3, with no args.

**R22K sources.**
- `mkinst.py --kII 1 --ext <21 classes>` regenerates Final.lean.
- From FinalTop.lean, `mkftall.py` regenerates FinalAll.lean and Cor.lean.
- `mkcap.py` (with `PORT_SRC` and `HCAPK_BUILD`) regenerates Cap.lean.
- FinalTop.lean is written by hand.

**G2 sources.** `tomod_g2.py`, then `blocksF.py` and `mkF.py` regenerate the 36,953 generated modules. Their inputs are the E1 route's source tree for classes 303 and 321 (`E1ROOT`). `blocksF.py` and `mkF.py` alone, from `data/C<c>X.bin`, regenerate the 6,998 block modules, the two chains and the two lookup modules. `G2.Disp`, `G2.Asm2` and `G2.WLoad` are written by hand.

## 8. Determinism

**Generators.** `build.sh` reproduces the five production binaries bit for bit.

**EXT packages.**
- Regeneration with the tools version recorded for a package gives byte-identical module sources, `manifest.jsonl` and DONE record (generation times aside), for every package kind.
- The oleans built from these sources with Lean 4.30.0 are byte-identical to the production oleans.
- This holds for the parallel generators too, because the number of workers does not change the output:
  - each generator process is single-threaded and deterministic;
  - `gensplit.py` generates the items of the top's item list independently;
  - it writes them, or splices them (`--assemble`), in the order of that list.
- Different tools versions can give different certificates for the same leaf. For one B leaf the main record has 549 bits under gen7pc_eqf and 567 bits under gen7pd_eqf of tools v12. Module names and public statements are the same, because they depend only on the leaves.

| check | package and route | result |
|---|---|---|
| binaries | the five generators | `build.sh` output equals `BINARIES.sha256` |
| gen7pc, tools v6 | `ext_436_0007bbed9f6e` (32 U leaves) | the leaf slice's sha256 is the package id. DONE and manifest equal production. 97 of 97 oleans equal production. |
| gen7pd_eqf_v9 with gensplit, tools v10 | `ext_c436_x55480f8c91804ec5` (EqF S leaf, 54 SAT leaves, 74 parts) | 4 and 12 workers give identical sources. DONE equals production. 77 of 77 oleans equal production. |
| gen7pc_eqf with `EXTPKG_NOSPLIT=1`, tools v10 | `ext_c436_xf0657888c1c76c58_r2` (cut family, B leaf) | sources, generator output and manifest equal the production emission |
| gen7pd_eqf, tools v12 | `ext_c436_x719558292535fb27_r5` (cut family, 1,632,960 SAT leaves, 1,296 parts) | two independent production emissions of the leaf (`_r5`, `_r6`) have identical 1,299 module sources, manifest and DONE. 4 and 12 workers give identical sources. |
| one package per version | v1, v2 (inline), v3, v5, v6 (CC and class h450), v7, v8, v9, v10 | DONE equals production for all ten. `ext_h450_ab23070c82ea` (class route) and `ext_436_6df0dcf8199f` (v2) each have 7 of 7 oleans equal to production. |
| EXT tops | all 23 | sources equal the production sources |

**Lean modules.** Rebuilds from unchanged sources give byte-identical `.olean`, `.olean.private`, `.olean.server` and `.ilean` files (`S4.EqF`, `S4.Top436`). The R22K generators regenerate Final.lean, FinalAll.lean, Cor.lean and Cap.lean byte-identically.

**G2.** Regeneration gives byte-identical sources for 31,444 of the 36,953 generated modules. The other modules differ as follows:
- the 5,507 `_Data` modules differ only in the directory of their data file, which the intermediate split modules record;
- `C303X_Lits` and `C321X_Lits` differ only in the docstring line of Section 9.

The regenerated manifests equal the shipped ones in modules, dependencies and sources. They differ only in the scheduler hints `pred_s` and `pred_gb`. The generated sources are in `zenodo/g2_src_generated.tar.zst`, exactly as built.

## 9. Shipped sources that differ from the built ones

Every difference is checked by a rebuild against the production outputs.
- **Data-path literals.** In the arguments of `#rttable`, `#rttablew`, `#e1lits`, `#g2w` and `#g2fw`, 3 lines in HC436 and 5,515 lines in G2 name their file relative to the build directory.
  - HC436.IP_c436, HC436.SL_c436, HC436.OK_c436_Base, G2.E303S0_Data, G2.C303X_W and G2.E303M_Lits rebuild with byte-identical `.olean`, `.olean.private`, `.olean.server` and `.ilean`.
  - No `.olean` contains a path.
- **`--` comment lines** (same lines, same columns): R22K.FinalTop (4 lines), R22K.FinalAll (4), S4.Top436 (1), S4.TopCC (7).
  - All four rebuild with byte-identical `.olean`, `.olean.server` and `.ilean`.
  - The two S4 modules also rebuild with a byte-identical `.olean.private`.
- **Docstrings** of 15 modules name files by relative paths and use no process vocabulary. They also have no stale section titles.
  - The modules are HC436.IP_c436, HC436.OK_c436_Base, G2.C303X_Lits, G2.C321X_Lits, R22K.FinalTop, R22K.FinalAll, R22K.Cap, S4.EqF, S4.CC422, S4.CC436, S4.CCLeaf, S4.SatQ, S4.SplitQ, S4.PlaneLift and S4.PlaneW3.
  - All 15 rebuild with a `.olean` byte-identical to production, so the closure hashes and the theorem's hashes are unchanged.
  - Their `.olean.server` differs from production, and their `.olean.private` differs too, except for S4.CCLeaf.
  - `lean/DOCSTRING_EDITS.tsv` lists, per module, the production and shipped sha256 of `.olean`, `.olean.private` and `.olean.server`. The production build keeps no `.olean.private` for the three R22K modules among them.
  - The OLEANS lists give the hashes for the shipped sources.
  - `mkcap.py` and `mkftall.py` emit the edited docstrings, and they regenerate the shipped Cap.lean, FinalAll.lean and Cor.lean byte-identically.

## 10. Hash lists

- `lean/final/OLEANS.sha256` holds the R22K oleans of the final run. FinalAll, FinalTop, Cap and Cor equal the import records of `R22K.Final`.
- `lean/cc/OLEANS.sha256` has 58 lines. All equal the final environment manifest, except the `.olean.private` and `.olean.server` lines of the docstring-edited modules in Section 9.
- `lean/cc/g2/OLEANS.sha256.zst` has 73,914 lines, taken from the module hash records of the build. All equal the final environment manifest, except the `.olean.private` and `.olean.server` lines of the two Lits modules in Section 9. 46 files are recomputed and all equal: a random sample, the crowns and the class theorems.
- `generators/ext/BINARIES.sha256` lists the five production binaries.
- `generators/ext/TOOLS_VERSIONS.tsv` lists the bundles, bootstraps and scripts of each tools version.

## 11. Zenodo record

| archive | size (bytes) | sha256 | contents |
|---|---|---|---|
| `g2_src_generated.tar.zst` | 5,662,703 | `2065a1a23a726f1c5c37d18d95c0036ff580dade74e31547b0931030c65e495f` | `g2/mod/src/G2/`: the 36,937 generated sources |
| `g2_data.tar.zst` | 651,400,672 | `0dc1d1c4a2874f6bc3427b6ac5fb2c72e6458c6abd0fee0ed511d449cef10306` | `g2/data/`: the 6 literal files |
| `g2_split.tar.zst` | 120,321,155 | `b940253ab00b459884beda6149e3f93fcae0132b2f294d9f56c6c27428b24a56` | `g2/l2/split/`: the 5,507 split literal files |

The archives are written with `tar --sort=name --owner=0 --group=0 --numeric-owner --mtime=2026-10-11T00:00:00Z --format=gnu`. Their binary members are literal tables of random-looking bytes.

## 12. Sizes

| subtree | files | size |
|---|---|---|
| `lean/DOCSTRING_EDITS.tsv` | 1 | 0.007 MB |
| `lean/final` | 57 | 1.0 MB |
| `lean/cc` (with `g2/`) | 68 | 13.9 MB |
| `generators/ext` | 48 | 1.0 MB |
| `inputs/ext` | 235 | 44.4 MB |
| all of the above | 409 | 60.3 MB |
| Zenodo record | 3 | 777.4 MB |

The largest repo file is `inputs/ext/leaves/ext_c436.tsv.zst` (8.3 MB). The largest zenodo file is `g2_data.tar.zst` (651.4 MB).
