# e1g modules: what they import from outside this directory

The frozen port is referenced, not copied (lean/TOOLCHAIN.md gives its manifest hash and DOI). The KMod library is in lean/kmod,
HC436 in lean/cc.

## The modules in this directory

| module | imports (outside e1g) |
|---|---|
| `E1GK.ChainF` | `E1G.Hdr` (port) |
| `E1GK.ExtMono` | `E1G.Hdr` (port) |
| `E1GK.JobCmd3` | `RT.Load` (port); meta: `Lean`, `KMod.Units` (lean/kmod) |
| `E1GK.RootCmd` | `RT.Load` (port); meta: `Lean`, `KMod.Units` (lean/kmod) |
| `E1PQ.ChainF` | `E1P.Hdr` (port) |
| `E1PQ.JobCmd` | `RT.Load` (port); meta: `Lean`, `KMod.Units` (lean/kmod) |
| `KH.HT436`, `KH.HT422`, `KH.S<C>_<J>` (450 in all) | `RT.Load` (port) |

Inside e1g: `E1GK.ExtMono` imports `E1GK.ChainF`; `E1GK.JobCmd3` imports `E1GK.ChainF` and `E1GK.ExtMono`; `E1GK.RootCmd`
imports those and meta-imports `E1GK.JobCmd3`; `E1PQ.JobCmd` imports `E1PQ.ChainF`.

## The generated job modules (package KJ, built by the e1g packages)

Besides the e1g modules above, the generated modules import:

| context | imports |
|---|---|
| c436 | `HC436.IP_c436`, `HC436.SL_c436`, `HC436.OK_c436` (lean/cc); `E1G.Hdr`, `RT.Load` (port); `KH.HT436`, `KH.S436_<J>` (heavy jobs); `KMod.Units`, `KMod.Audit` (lean/kmod) |
| c422 | `HCap.IP_c422`, `HCap.SL_c422`, `HCap.OK_c422`, `E1G.Hdr`, `RT.Load` (port); `KH.HT422`, `KH.S422_<J>`; `KMod.Units`, `KMod.Audit` |
| point (ptc) | `HPt.IP_ptc`, `HPt.SL_ptc`, `HPt.OK_ptc_F`, `HPt.Rptc_HT`, `E1P.Hdr`, `RT.Load` (port); `E1PQ.ChainF`, `E1PQ.JobCmd`; `KMod.Units`, `KMod.Audit` |

The aggregation modules (mkagg.py) also meta-import `E1GK.RootCmd`. The class packages (KC, lean/hcapk and generators/classes)
are emitted by the same tools (v7.1) and import `HCapK`/`KCH` instead of `HC436`/`KH`.

The full import closure of the final theorem, with the origin and `.olean` sha256 of every module, is
`manifests/closure.tsv.zst`.
