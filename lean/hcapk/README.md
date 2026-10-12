# HCapK and KCH

## HCapK (183 modules)

HCapK holds 183 modules. Each `HCapK.X` is the frozen port's `HCap.X` source, built under the module name `HCapK.X`.
Imports among the 183 modules are renamed the same way. Declaration names, namespaces and statements are unchanged.
In the class modules `C<c>`, the two auto-generated equation lemmas `E1G.IP_h<c>.EXT.eq_1` and `E1G.OK_h<c>.Cx.eq_1` have the
same statements as in the port; their proof terms differ.

The 183 modules are listed in `need.txt`. They are:
- the class module `C<c>` and the root-level modules under it, for 11 classes: 454, 456, 465, 469, 471, 472, 473, 476, 485,
  487, 490;
- for 7 of these (456, 472, 473, 476, 485, 487, 490), also the instance facts `OK_h<c>` and the job table `R<c>_HT`, with
  their dependencies.

Who imports HCapK:
- `R22K.Cap` imports `HCapK.C<c>`, in place of `HCap.C<c>`, for the 11 classes above;
- the class modules `KC.h<c>_Class` of the same 11 classes import `HCapK.C<c>` and `HCapK.R<c>`;
- the job and aggregation modules (`KC.*`) of the 7 classes import `HCapK.OK_h<c>` and `HCapK.R<c>_HT`.

No module imports both `HCap.X` and `HCapK.X`. The import closure of `R22K.Final` contains the 183 HCapK modules and none of
the 183 corresponding `HCap` modules.

### Sources

The sources are derived from the frozen port's sources by `derive_hcapk.py PORT_SRC OUT`. Its inputs are the 183 files
listed, with their md5, in `PORT_INPUTS.md5`; these are the md5 values of the port's `MANIFEST_FULL.md5`. For each module, the
derivation:
- adds one comment line at the top;
- renames the imports of the 183 modules;
- replaces the absolute data path of the seven `#rttable` commands (in `OK_h<c>_Base`) by `data/<dir>/<file>`, relative to
  the build's working directory, which links the port's `snap/data` as `./data`.

The sha256 of the derived sources are in `HCAPK_SOURCES.sha256`.

Neither the comment line nor the data path enters the build outputs. For `C454` and `OK_h456_Base`, rebuilding from the
derived sources gives `.olean`, `.olean.private`, `.olean.server`, `.ilean` and `.ir` byte-identical to the production
outputs listed in `OLEANS.sha256`.

### Build

```
LIB_PATH=<frozen port build>:<Mathlib and dependency roots>:<toolchain lib/lean> \
  ./build_hcapk.sh <frozen port root> <out>
```

The script derives the sources, builds the 183 modules in dependency order into `<out>/build`, then builds the KCH tables.

## KCH (45 tables)

`KCH.S<c>_<J>` is the sub-job table of giant root job J of class c. It is a public `#rttablew` table of the sub-jobs' mode-0
prefix headers, with 128-bit or 256-bit entries.
- Sources: `KCH/`.
- Data: `inputs/classes/kch_data.tar.zst`. The tables read `data/KCH_S<c>_<J>.bin` from the working directory.
- Generator: `generators/classes/tools/mkkch.py`, which works from `inputs/classes/giants.tar.zst`.

The heavy-sub and heavy-split class packages and the class aggregations import these tables. The tables are needed to build
those modules, but they are not in the import closure of `R22K.Final`.

## Olean hashes

`OLEANS.sha256` lists `.olean` and `.olean.private` for the 183 HCapK modules and the 45 KCH tables, as the production
builds and the final build used them.
