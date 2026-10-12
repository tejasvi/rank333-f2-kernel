# Toolchain and dependencies

| dependency | version | how to obtain |
|---|---|---|
| Lean | v4.30.0 (`leanprover/lean4:v4.30.0`) | elan |
| Mathlib | v4.30.0 (commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`) | `lake` from the Mathlib repository |
| Rudich and Rousseau's Lean proof of R ≥ 22 | archive `lb22_zenodo.zip`, 82,480,696 bytes, md5 `c72def5ec5a272b3a60f6a43b2f99066` | https://doi.org/10.5281/zenodo.23047901 |
| The frozen port (the module-form Lean development of the native release) | `MANIFEST_FULL.md5`: 315,565 files, md5 `7c5a67484a5335c4d4c4b5b69ac3ddb1`, sha256 `1818978d19fc1bfd3c192c8ac1a4f40b0d61be209b9d0f13fc0c3ed96b5f779b` | sources in the native release repository (https://github.com/tejasvi/rank333-f2, `lean/`) and its Zenodo record (https://doi.org/10.5281/zenodo.23236154, data archive); the manifest itself is `lean/port/MANIFEST_FULL.md5.zst` |

**What this repository adds.** It does not copy the frozen port. It adds:
- the frozen port's manifest, `lean/port/MANIFEST_FULL.md5.zst` (zstd-compressed; it lists the port's sources under `src/`, its data under `snap/` and its build files under `build/`). Every port file in the Zenodo archive `r22k_oleans_port_ir.tar.zst` is listed in it with the same md5;
- the Lean libraries under `lean/`;
- the generators under `generators/`;
- the inputs under `inputs/`, from which every generated package of the final set is produced.

**Build order.**
1. Lean core, Mathlib and Rudich–Rousseau.
2. The frozen port.
3. The libraries under `lean/`, in the build orders given in each directory.
4. The generated packages (REGENERATE.md).
5. `lean/final`.

Every module of the final import closure is listed with its `.olean` sha256 in `manifests/closure.tsv.zst`. This lets a rebuild be compared module by module.
