# Class tier inputs

| file | content |
|---|---|
| `kc_packages_A1.jsonl.zst` | spec lines of 1,533 `range`/`split` class packages (14 classes) |
| `kc_packages_A2.jsonl.zst` | spec lines of 2,799 `range`/`split` class packages (classes 456, 472, 473, 476, 485, 487, 490) |
| `kc_packages_B.jsonl.zst` | spec lines of 12,234 `heavy-sub`/`heavy-split` class packages (45 giant root jobs) |
| `kc_heavy.jsonl` | the 45 giant root jobs: class, job, prefix, split depth, sub-job count |
| `rootjobs.tsv.zst` | per root job of the 21 classes: class, job, native st-nodes, leaves, predicted kernel seconds |
| `giants.tar.zst` | per giant `giants/h<c>_<J>/`: `fr.txt` (sub-job frontier), `top.bin` and `top_*_top.bin` (top trace of the same DUMPONLY run), `giant.json` (depth, per-sub-job counts) |
| `kch_data.tar.zst` | the 45 KCH table data files `kch_data/KCH_S<c>_<J>.bin` |

The three spec lists together are the 16,566 class packages of the final package set. `kc_heavy.jsonl` and the three lists
are reproduced byte for byte by `generators/classes/tools/kccut.py` from `rootjobs.tsv.zst` and `giants.tar.zst` (see
`generators/classes/README.md`).
