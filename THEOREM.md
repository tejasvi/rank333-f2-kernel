# The final theorem

## Statement

Module `R22K.Final`, source `lean/final/src/R22K/Final.lean` (sha256 `330f8a7baad895d088afba4423673bd13b9e1b5a83d8baa74495d2f7f3436737`).

```lean
R22K.Final.rank_ge_23 : Top.RankGe23
```

with

```lean
@[expose] def Top.RankGe23 : Prop :=
  ∀ (n : ℕ) (a b c : Fin n → RootSound.M3), RootSound.IsDecomp a b c → 23 ≤ n

@[expose] def RootSound.IsDecomp {n : ℕ} (a b c : Fin n → RootSound.M3) : Prop :=
  ∀ (i j j' k k' i' : Fin 3),
    ∑ s, a s i j * b s j' k * c s k' i' = if j = j' ∧ k = k' ∧ i = i' then 1 else 0

@[reducible, expose] def RootSound.M3 : Type := Matrix (Fin 3) (Fin 3) RootSound.F2   -- RootSound.F2 := ZMod 2
```

In words, every decomposition of the 3×3 matrix multiplication tensor over F2 into `n` rank-one terms has `n ≥ 23`.

The same module proves four corollaries:

| theorem | statement |
|---|---|
| `R22K.Final.rank_eq_23` | `(∃ a b c, RootSound.IsDecomp a b c) ∧ ∀ (n : ℕ) (a b c : Fin n → RootSound.M3), RootSound.IsDecomp a b c → 23 ≤ n`: with Laderman's decomposition, the rank is exactly 23 |
| `R22K.Final.mm_equiv` | `∀ (n : ℕ) (a b c : Fin n → RootSound.M3), R22B.Cor.IsDecompMM a b c → 23 ≤ n`: the matrix-product convention `C = AB` |
| `R22K.Final.table_23` | `FullTable.TableAtLeast (List.map FullTable.mask_matrix FullTable.table[495]!) 23`: Rudich and Rousseau's table statement at 23 |
| `R22K.Final.recursive_23` | `FullTable.RecursiveAlgorithmMultiplicationsAtLeast 23`: Rudich and Rousseau's statement on recursive algorithms with 23 |

## Axioms

`#print axioms` on the five theorems, in the final environment:

```
'R22K.Final.rank_ge_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'R22K.Final.rank_eq_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'R22K.Final.mm_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'R22K.Final.table_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'R22K.Final.recursive_23' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Coverage.**
- `#print axioms` reads the constants of the exported environment.
- The private proof bodies of the package modules are not loaded there. Their axioms are certified by the composed census: each module's build-time axiom record, the audit walk from `R22K.Final`, and the private-level external walk over every obligation (VERIFICATION.md).
- The census, the walk and a name scan of every module for `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` and `native_decide` auxiliaries all give the same set, `{propext, Classical.choice, Quot.sound}`.

## Loading the theorem without building

The public `.olean` files of the whole import closure are available, so `R22K.Final` can be loaded without building anything:
- Lean, Mathlib and Mathlib's dependencies (10,601 modules) come with the toolchain and Mathlib's cache;
- the other 6,416 modules are in two archives of the Zenodo record: `r22k_oleans_ours.tar.zst` (this project's 1,043 modules) and `r22k_oleans_port_ir.tar.zst` (the frozen port's 5,373 modules, and the 406 `.ir` files that the loader reads: 394 of port modules and 12 of case-II library modules).

`lean/final/check/check_closure.sh` unpacks the two archives and checks every file against the archive's manifest. It then runs `lean/final/check/Check.lean`, a module file that imports `R22K.Final` at the exported level and prints the statement of `R22K.Final.rank_ge_23`, the definitions it uses, the axioms of the five theorems, and the size of the loaded environment (17,017 modules, 1,576,388 constants). The expected output is `lean/final/check/Check.out`. The run takes a few seconds and about 7 GB of memory.

The port's files in the archive are the frozen port's build files: each is listed with the same md5 in its manifest, `lean/port/MANIFEST_FULL.md5.zst`.

This shows the statement and its definitions as Lean loads them, from files whose sha256 are in `manifests/closure.tsv.zst`, and it reproduces C3 of VERIFICATION.md. It re-checks no proof: Lean does not re-run the kernel on imported modules, and the private parts are not loaded (see Coverage above).

## How the proof is assembled

`R22K.Final.rank_ge_23` is `R22K.FinalAll.rank_ge_23_of` applied to these published theorems, each the root of a tier:

| hypothesis | producer | tier |
|---|---|---|
| `G2.Crown303.crown`, `G2.Crown321.crown` | G2 | the two crowns that replace the native run's 23 facts |
| `KC.h<c>.EXT`, `KC.h<c>.classLB`, `NDX.h<c>.x<c>` for the 21 classes 420, 450, 451, 454, 455, 456, 458, 460, 463, 464, 465, 469, 470, 471, 472, 473, 475, 476, 485, 487, 490 | class roots and their leaf tops | class raises |
| `KJ.aggptc.point` | point root | point lemma |
| `R22B.GramCrown.*` (9) | frozen port | Gram crowns |
| `KJ.agg436.Root.EXT`, `KJ.agg436.Root.root`, `PLE.c436.Ext.hext_of`, `PLE.c436.Sub.sub` | cap root 436 and its leaf top | context cap CC(436,3,14) |
| `KJ.agg422.Root.EXT`, `KJ.agg422.Root.root`, `PLE.c422.Ext.hext_of`, `PLE.c422.Sub.sub` | cap root 422 and its leaf top | context cap CC(422,3,14) |
| `KM2.Top.segs` with key 1 | case-II join | case II |
| `KMIA.Top.vI`, `KMJJ.Top.vI` | case I and case I13 tops | cases I and I13 |

Each hypothesis's type is Expr-equal or definitionally equal to the statement its producer publishes; the checks are in `lean/final/chk/`. Elaborating `R22K.Final` checks the application itself.

## Environment

- **Lean and dependencies:** Lean v4.30.0, Mathlib v4.30.0, and the frozen port of the native release; lean/TOOLCHAIN.md gives the versions and hashes.
- **Import closure** of `R22K.Final` at the exported level: 17,017 modules with 1,576,388 constants. `manifests/closure.tsv.zst` lists each module with its origin and `.olean` sha256.
