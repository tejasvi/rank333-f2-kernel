# KMod: module form and axiom audit

KMod is the module form used by the job modules, aggregation modules and class modules. Each KMod module checks its own
units and exports exactly one public theorem. The axiom audit is compositional: each module audits its own theorem when it
is built, and a top-level walk joins the per-module results.

KMod is imported with `meta import`. It is needed to build these modules, but it is not part of the import closure of the
final theorem.

## Library modules

| module | contents |
|---|---|
| `KMod.Vocab` | shared names and helpers |
| `KMod.Units` | unit groups and combinators: `#kunits`, `#klits`, `#kdispatch` (a balanced dispatch tree, one definition per node), `#kpub`, `#kpubterm`, `#kkey`, `#kext` |
| `KMod.Audit` | `#kax THM`, `#kaxp THM`, `#k1top NAME [C, ...]` (alias `#ktop`) |
| `KMod.Comb` | generic pieces for combinators (`forallLt`) |

The `.olean` and `.olean.private` sha256 of these modules, as the production builds and the final build used them, are in
`OLEANS.sha256`.

## Manifest lines

Building a module writes manifest lines to its build log. `tools/kmod_build.sh` collects them into `<module>.kman`:

- `KUNITS`, `KLITS`: unit groups and literal tables, with the name, size and sha256 of each data file;
- `KPUB`: the module's public theorem and a hash of its statement;
- `KDISPATCH`, `KKEY`, `KEXT`: dispatch sizes, the key range the module covers, and its external-leaf labels;
- `KAX STD | OBL | BAD`: the result of `#kax`;
- `KAXSUM <thm> visited=… std=… obl=… bad=… local_axioms=…`;
- `KAXP <thm> <axioms>`: Lean's `collectAxioms`;
- `KTIME`, `KDATA`, `KSHA`: build time, and the sha256 of data files and outputs.

The `.kman` records contain machine paths, so they are not part of the release. The manifests in `manifests/` carry the
names and hashes.

## Audit rules

1. **Per module (`#kax THM`).** Walks the theorem through types, values and constructors, within the module. Each
   constant reached is classified as:
   - `STD`: one of `propext`, `Classical.choice`, `Quot.sound`;
   - `OBL <module> <constant>`: a constant from another module, recorded as an obligation;
   - `BAD`: any other axiom, including `sorryAx`, the auxiliary axioms of `native_decide`, and axioms declared in the module.

   `kmod_build.sh` rejects a module unless its manifest has a `KPUB` line, and every `KPUB` theorem has a `KAXSUM` with
   `bad=0` and `local_axioms=0`.

2. **Top-level walk (`tools/kmod_audit.py --root MOD --build DIR ...`).** Starts at the root module's manifest and follows
   the obligations.
   - Every module reached must satisfy rule 1.
   - An obligation into a KMod module N must name one of N's `KPUB` theorems. The one other accepted target is an
     external-leaf list `NS.EXT` that occurs in the statement of one of N's `KPUB` theorems. `tools/KModTyChk.lean` checks
     this at the exported level; a statement is public.
   - Obligations into other modules (the frozen port, Mathlib, Lean core) go to `tools/KModExt.lean`. It imports those
     modules at the private level, so every body is present, and walks each constant. It must report `bad=0`.
   - If the root has a `KAXP` line, it must list only the three standard axioms.
   - Optional: `--keys FILE` checks that the reached modules' `KKEY` ranges partition the key list exactly.

3. **Lean's own check.** `#kaxp THM` prints `collectAxioms` for the theorem. `#k1top NAME [C, ...]` publishes the
   conjunction of the listed theorems as one public theorem.

## Tests (`KModT`)

Positive tests: `Good`, `Comb`, `Syn`, `E1Comb`, `E1/*`, `T1/*`, `T4/*` (staged builds: `test/T1.plan`, `test/T4.plan`
with `tools/kmod_plan.sh`) and `Top/S1`.

Negative controls. Each must fail the audit:

| test | content | expected |
|---|---|---|
| `Neg/Ax` | a private axiom proves the public theorem | `KAX BAD` (local axiom); `kmod_build.sh` rejects the module |
| `Neg/Sorry` | `sorry` | `KAX BAD sorryAx` |
| `Neg/Native` | `native_decide` | `KAX BAD` (the auxiliary axiom of `native_decide`, local to the module) |
| `Neg/Voc` | the theorem uses a vocabulary lemma proved by `sorry` (`BadVocab`) | the external walk reports `bad>0` |
| `Neg/Top` | an aggregation over a module with a bad axiom | `kmod_audit.py` FAIL |
| `NegE/A`, `NegE/B` | B uses A's `EXT` list, which is not in A's public statement | `kmod_audit.py` FAIL (statement check) |

The E1 tests read the frozen port's `snap/data` through `./port_data`.
