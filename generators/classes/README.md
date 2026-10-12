# Class tier generators

The class tier proves `ClassLB c LB` for 21 hcap classes: 420, 450, 451, 454, 455, 456, 458, 460, 463, 464, 465, 469, 470,
471, 472, 473, 475, 476, 485, 487, 490. It has two package kinds: 16,566 class packages (`kc_*`) and 21 class aggregations
(`kcagg_h<c>`).

## Class packages (`kc_*`)

Each class package covers a range of root jobs, or of sub-jobs of a giant root job, of one class. It is produced by the
E1G emitter from its spec line. The emitter is `emitpkg.sh` of the E1G emitter tools tree v7.1 (tarball sha256
`f0718c2d3fffa48b7b5625ce8070624a8248d6d88f4eb4ba8194f39b9538bd09`): its sources are in `generators/e1g/tools/v7.1/`, and
`generators/e1g/sh/mktools.sh v7.1 OUT` assembles the full tools tree. The class contexts it reads are in
`inputs/e1g/ip_classes.tar.zst` (sha256 list `inputs/e1g/IP_SHA256`): `ip/hcap/` for the 21 classes, `ip/subh<c>/` and
`ip/subtoph<c>/`. The spec
lines are in `inputs/classes/kc_packages_{A1,A2,B}.jsonl.zst`. Each line has `id`, `cap` (`h<c>`), `kind`, `args` and
`pred_s`. The emitter command is

```
emitpkg.sh <args...> OUT --threads 4
```

| kind | args | content |
|---|---|---|
| `range` | `h<c> a b` | root jobs [a, b), each predicted at most 600 s |
| `split` | `h<c> k k+1 --split 7` | one root job, split at depth 7 (batched split, recursively) |
| `heavy-sub` | `h<c> a b --heavy J` | sub-jobs [a, b) of giant root job J (its depth-D frontier) |
| `heavy-split` | `h<c> s s+1 --heavy J --split D+2` | one sub-job of giant J, split at depth D+2 |

For the heavy kinds, the emitter reads `ip/subh<c>/<J>.txt` (the giant's sub-job frontier) and `ip/subtoph<c>/<J>.bin`
(its top trace) from the tools tree. These files ship in `inputs/e1g/ip_classes.tar.zst`. They are byte-identical to
`fr.txt` and `top_*_top.bin` of the same giant in `inputs/classes/giants.tar.zst`, which is where `tools/mkkch.py` derives
them from.

The lists:
- A1: 1,533 `range` and `split` packages of 14 classes, whose job modules build on the frozen port alone;
- A2: 2,799 `range` and `split` packages of the 7 classes 456, 472, 473, 476, 485, 487 and 490, whose job modules import
  `HCapK.OK_h<c>` and `HCapK.R<c>_HT`;
- B: 12,234 `heavy-sub` and `heavy-split` packages of the 45 giant root jobs (`inputs/classes/kc_heavy.jsonl`).

A1 and A2 split, by class, the lines of the list that `tools/kccut.py A.jsonl 5400 --no-giants` writes (ids
`kc_00000`–`kc_04331`). `tools/kccut.py B.jsonl 5400 --giants-only --id0=4332` writes B (ids `kc_04332`–`kc_16565`) and
`kc_heavy.jsonl`. Run on the shipped `rootjobs.tsv` and giants, both commands reproduce the shipped lists byte for byte.

Cut tools, in order:
1. `rootjobs.py`: per root job, the native st-node and leaf counts and the predicted kernel seconds of the E1G layout. It
   reads the classes' root counts from `ip/hcap/ana/roots_fixed.txt` (in `inputs/e1g/ip_classes.tar.zst`). Its output is
   `inputs/classes/rootjobs.tsv`.
2. `giants.py`: for the root jobs predicted over 3e5 s, a DUMPONLY split at depth D (7, or 9 above 1e6 s) and a count pass
   over the sub-jobs. Its output is `giants/h<c>_<J>/{fr.txt, top.bin, top_*_top.bin, giant.json}`.
3. `regiant.py c/J/D`: re-splits a giant at a different depth.
4. `kccut.py`: the cut lists above.
5. `mkkch.py`: the emitter inputs `ip/subh*`/`ip/subtoph*` and the KCH tables `KCH.S<c>_<J>` (sources in `lean/hcapk/KCH/`).

`rootjobs.tsv` and the giants' files are shipped, so the cut lists can be recomputed from them with `kccut.py`. The tools read
them from `KC_INPUTS`, a directory with the decompressed inputs.
`rootjobs.py` documents how `rootjobs.tsv` was computed from the native per-unit counts; that count table is not shipped.

## Class aggregations (`kcagg_h<c>`)

`kcagg_vN/kcagg.sh C OUT DEPS` writes the aggregation package of class c. `DEPS/<id>/DONE` and `DEPS/<id>/kext.txt` are the
emitter's records of each class package of the class. The package roots' public `.olean` files must be in the build store.
The package contains:
- per giant: aggregators over its heavy packages' ranges of `KCH.S<c>_<J>`, its top chain (`#e1gtop` over
  `giants/h<c>_<J>/top.bin`), and the range [J, J+1) of `E1G.R<c>_HT` over that top;
- per class: fan-in-100 aggregators over all ranges of `E1G.R<c>_HT`, then the class module `KC.h<c>_Class`, written by
  `mkclass_root.py`. It publishes `KC.h<c>.EXT` (the class's external leaves, a literal list), `KC.h<c>.jobs` and
  `KC.h<c>.classLB`.

It also writes `ext.txt` and `ext_pl.txt` (`KC.h<c>.EXT`, one packed prefix per line, in list order). These are the input of
the EXT tier's tops.

Environment: `KC_TOOLS` (the E1G emitter tools tree), `KC_INPUTS` (a directory with the decompressed `inputs/classes`:
`zstd -d` the `.jsonl.zst` files and extract `giants.tar.zst`) and
`KC_LPATH_COMMON` (a file listing the closure roots in LEAN_PATH form; the build store comes first).

### Versions

| version | tarball sha256 | classes |
|---|---|---|
| v2 | `de4b1aa73e8c93efc2922bb068a0e9eec5dc94cf451637f16cfc99e2a01cb129` | 420, 450, 451, 455, 456, 458, 460, 463, 464, 465, 469, 470, 471, 472, 473, 475, 476, 487, 490 |
| v3 | `2159c8a6c0cd4e32dfe9d427e4e2b8624b7ef9784ac6d6b279b605ee37c2cfa8` | 454, 485 |

v2 and v3 differ only in `mkclass_root.py`, in the private proof `extSub` of the class module:
- v2 decides the inclusion of the root range's external-leaf list in `KC.h<c>.EXT` with `E1GS.subset_of_all`
  (`List.all` / `List.elem`);
- v3 decides it with a direct `List.rec` membership test (`memN` / `allMemN`), whose soundness lemmas are proved in the
  module.

The public statements are the same in both. `PRODUCTION_TREE.sha256` in each directory lists the per-file sha256 of the
production tarball. The released trees differ from the production trees in two ways only:
- the input files (cut lists, `kc_heavy.jsonl`, giants) are read from `inputs/classes`;
- environment defaults that named machine paths, and comments, are replaced.

The generated Lean sources are unchanged.

## Other tools

- `tools/zscan.py STORE`: lists `.olean`, `.olean.private`, `.olean.server` and `.ir` files whose last 64 bytes are all
  zero.
