# Sizes

## This repository

Files: 1438; total 208.9 MB.

| top-level path | MB |
|---|---|
| `inputs` | 125.7 |
| `manifests` | 42.1 |
| `lean` | 35.4 |
| `generators` | 5.4 |
| `SHA256SUMS` | 0.1 |
| `docs` | 0.1 |
| `README.md` | 0.0 |
| `VERIFICATION.md` | 0.0 |
| `REGENERATE.md` | 0.0 |
| `THEOREM.md` | 0.0 |
| `ZENODO.md` | 0.0 |
| `SIZES.md` | 0.0 |

Files over 50 MB (GitHub warns above 50 MB and rejects above 100 MB; the limit applied here is 95 MB):

- none

## The Zenodo record

Files: 19; total 8.61 GB (limit 50 GB).

| file | bytes | GB |
|---|---|---|
| `caseII_cc436_422.tar.zst` | 181959935 | 0.17 |
| `caseII_join_src.tar.zst` | 82419235 | 0.08 |
| `caseII_lib_data.tar.zst` | 41220887 | 0.04 |
| `caseII_mkcc_inputs.tar.zst` | 62544452 | 0.06 |
| `e1g_binaries.tar.zst` | 951735 | 0.00 |
| `e1g_cut_inputs.tar.zst` | 54647790 | 0.05 |
| `g2_data.tar.zst` | 651400672 | 0.61 |
| `g2_split.tar.zst` | 120321155 | 0.11 |
| `g2_src_generated.tar.zst` | 5662703 | 0.01 |
| `packages_modules.tsv.zst` | 834641897 | 0.78 |
| `private_sample_pass_01.tar.zst` | 1148319340 | 1.07 |
| `private_sample_pass_02.tar.zst` | 1253171019 | 1.17 |
| `private_sample_pass_03.tar.zst` | 1062171762 | 0.99 |
| `private_sample_pass_04.tar.zst` | 1069705855 | 1.00 |
| `private_sample_pass_05.tar.zst` | 1091017334 | 1.02 |
| `private_sample_pass_06.tar.zst` | 534731953 | 0.50 |
| `r22k_oleans_ours.tar.zst` | 263003893 | 0.24 |
| `r22k_oleans_port_ir.tar.zst` | 782524986 | 0.73 |
| `recheck_cii_i13_chunks.tar.zst` | 238964 | 0.00 |

## The public `.olean` files of the import closure

The import closure of `R22K.Final` has 17,017 modules, whose public `.olean` files total 6,666,843,176 bytes. `manifests/closure.tsv.zst` lists each module with its origin, `.olean` sha256 and size.

| origin | modules | `.olean` bytes | where the files are |
|---|---|---|---|
| Lean, and Mathlib with its dependencies (Batteries, Aesop, Qq, ProofWidgets, Plausible, ImportGraph, LeanSearchClient) | 10,601 | 2,143,974,128 | the toolchain and Mathlib's cache |
| the frozen port | 5,373 | 3,311,083,568 | `r22k_oleans_port_ir.tar.zst`, 782,524,986 bytes, which also holds the 406 `.ir` files that the loader reads (394 port, 12 caseII) |
| this project: the libraries under `lean/` (caseII 73, cc 20, e1g 5 and hcapk 183 modules), 757 modules of 50 generated packages, and the 5 `R22K` modules | 1,043 | 1,211,785,480 | `r22k_oleans_ours.tar.zst`, 263,003,893 bytes |

All of them fit. The files that the toolchain and Mathlib's cache do not provide take 1,045,528,879 bytes compressed in the Zenodo record, and `lean/final/check/check_closure.sh` loads `R22K.Final` from them (THEOREM.md).
