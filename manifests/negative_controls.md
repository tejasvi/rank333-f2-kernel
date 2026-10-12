# Negative controls

Release snapshot: snap-20261011T2103Z-f674b4e775a4. The controls test the checks themselves: the per-package audit, the statement
check of external obligations, the modhash gate and the EqF route. The production run used the same checks.

Each control plants one defect and runs the production check that must catch it. Each one comes with an unmodified (positive)
counterpart that must pass. Every control below gave the expected result.

## Per-package audit (the worker's finalize audit; `pkgaudit.py` runs the worker's own audit code)

| control | planted | expected | result |
|---|---|---|---|
| pos_clean | nothing (a clean package) | PASS | PASS |
| a_local_axioms | a module that declares a local axiom | FAIL | FAIL |
| a_kax_bad | a module whose axiom census reports a non-standard axiom (`KAX BAD`) | FAIL | FAIL |
| b_no_kpub | a module without a public-theorem record (`KPUB`) | FAIL | FAIL |
| b_root_no_kman | a root module without its `.kman` record | FAIL | FAIL |
| c_non_kpub_obligation | an external obligation that no public theorem's statement contains | FAIL | FAIL |
| d_kaxsum_bad | a module whose axiom summary reports `KAXSUM bad=1` | FAIL | FAIL |

## External obligations must occur in a public statement

- **Planted:** the obligation `KAX OBL KJ.c436h209_12170_12171_s12170_Top KJ.c436h209_12170_12171_s12170_Top.Fake.EXT`, added to a
  copy of package w1_08507.
- **Result:** the worker's compositional walk fails ("not in the statement of a KPUB theorem"). `kmod_audit.py` (md5 c7594ac1, with
  `KModTyChk.lean` md5 9f0ec98c) also fails ("not in the statement of any of its public theorems").
- **Positive counterparts:** the six unmodified packages with `NS.EXT` obligations (w1_08507, w1_32229, w1_09158, w1_87071, w1_87218,
  w1_07658) pass in both checkers, with identical obligation sets. Each of their 2 to 8 `NS.EXT` obligations occurs in a public
  statement.

## Through the production worker path (claim, emit, build, finalize, on a separate test queue)

1. **Planted private axiom** in module `KJ.l422_L2` of a test package.
   - The module's audit records `KAX BAD` and `KAXSUM bad=1 local_axioms=1`.
   - The package ends FAILED ("unclean audit"), with no done record and no tarball.
   - The positive control (the same package without the axiom) passes.
2. **Mismatched import hash:** package A is built against `KJ.nceB` version 1, while the store holds version 2.
   - `modhash.py check` reports STALE (and NAME-CONFLICT with `--universe`) and exits 1.
   - The consistent pair gives 0 violations.
   - The worker records what each build saw, so the mismatch is caught at aggregation.
3. **Private-level import mismatch:** importer A uses `import all KJ.nceB` and proves `hid = 1` by `rfl`. B is rebuilt with the same
   public `.olean` but `hid = 3` in its private part.
   - `modhash.py check` reports STALE (private part) and PRIVATE-CONFLICT, and exits 1.
   - `modhash.py` compares the recorded `.olean.private` hash for every `import all` import: STALE if it differs, PRIVATE-MISSING if
     it is absent.
   - A module whose own private part differs from its record is rebuilt.
   - The counterparts behave as required: an exported-level importer with a private-only change gives 0 violations; an exported
     mismatch gives STALE.
4. **EqF route:** a generator switch makes the EqF generator skip one canonical child of a node.
   - The package fails in the kernel ("declaration type mismatch"), and its aggregation and chunk are blocked.
   - The same leaf without the switch passes.
   - An independent EqF validation passes: byte-identical rebuild, axioms {propext, Classical.choice, Quot.sound}, 0 modhash
     violations.

## Related gates

These run over the whole final set, not over planted defects: V5 items B1-B4 and C1-C4 (`V5_RESULT.txt`), and the private-sample
re-check (`sample_check/`).
