# Build pipeline: queue, workers, verification, final build, winner selection

This kit turns package spec lines into verified Lean module packages and checks the final theorem's whole dependency set. It covers:
- the package queue and the per-machine worker that builds packages;
- the verifier, the union walk, the final build and the V5 checklist;
- the private-part sample check;
- the rules that pick one winner when a package has several attempts.

A scheduler outside this kit ran the queue during the production run: it started and stopped the workers and installed the Lean closure (toolchain, Mathlib, the frozen port, the libraries) on them. Everything that decides what is built, what is accepted, and what the final theorem rests on is in this kit.

All paths and stores come from environment variables (table below). Nothing in the kit names a machine, a store, or an account.

## Layout

```
queue/    objstore.py   object-store client (local directory or HTTP JSON API), generation preconditions
          kitenv.py     shared paths and settings (environment)
          pbq.py        the package queue: leases, done records, sweep, snapshots
          pbworker.py   the worker of one machine: claim, emit, schedule, finalize (audit, records, tarball, done record)
          pbsched.py    the module scheduler a worker runs (memory- and dependency-aware)
          modhash.py    import-hash records (.mhash) and the "one module name, one content" check
          nothp.py      runs a command with transparent huge pages disabled
          OleanImports.lean  reads .olean import headers (for modhash.py)
          KModTyChk.lean     statement check of the KMod audit (byte-identical to the KMod library's copy)
          KModExt.lean       private-level external walk of the KMod audit (byte-identical to the KMod library's copy)
          appendpk.py, front.py, gateappend.py, requeue.py, supersede.py, unsupersede.py   queue operations
verify/   verifier.py   incremental verifier of every done package (integrity, own hashes, imports, one name one content)
          records.py    local cache of the done records
final/    topstore.py   the top store: the public parts of every done package
          walk.py       the union walk: external obligations of every package, at the private level
          final_build.sh, kmod_audit_obl.py, final_ext.py, envmanifest.py   the final top R22K.Final and its audit
          Closure.lean, classify.py   the census of R22K.Final's import closure
          v5.py         the V5 checklist; snapshot.py freezes the queue state the census runs read
          sample_check.py, sample_overlay.py, sample_census.py   the private-part sample check
          resolve_conflicts.py, backfill_pubs.py, pkgaudit.py, crosscheck.sh   maintenance and the offline re-audit
winners/  race.py, ptc_resolve.py, pairrace.py, multirace.py, extcut_race.py   first-finisher-wins resolution
```

## Data flow

1. **Spec line.** Each package is one JSON line of `packages.jsonl`. It gives the id, the emitter (`emit`: a command, or a pre-emitted tarball), the dependencies on other packages (`deps`), and predictions (`pred_s`, `pred_gb_max`, `min_mem_gb`).
2. **Claim.** A worker claims the package with a lease, `lease/<id>`. The lease is created with `if_generation=0`, so only one worker can hold it, and the holder renews it every 300 s. A package becomes claimable only when all its `deps` have done records.
3. **Emit.** The emitter writes the package's Lean sources and a manifest, one JSON line per module (module, src or cmd, deps, pred_s, pred_gb, env). The worker rewrites the manifest's paths for its own machine. The package's store comes first on `LEAN_PATH`, then the closure.
4. **Build.** `pbsched.py` builds every module in a fresh `lean -j1` process, with THP off and an address-space cap. It respects module dependencies, the machine's memory and a starvation guard. Each result goes to `results.jsonl`, which is fsynced.
5. **Finalize.** For each package, `pbworker.py`:
   - audits it: every reached module's `.kman` has a `KPUB` and a `KAXSUM bad=0 local_axioms=0` per public theorem, and no `KAX BAD`. An obligation into a KMod module must name one of that module's public theorems, or an `.EXT` list in a public statement (checked by `KModTyChk.lean`). Every other obligation goes to `audit/obl.txt`.
   - writes the `.mhash` records (`modhash.py record`): the module's own `.olean` and `.olean.private` sha256, plus every import as resolved, with its hashes.
   - packs the public parts, manifest, logs, results and `SHA256SUMS` into `tar/<shard>/<id>.<t>.<box>.tar.zst`, and the root modules into `pubs/...tar`. Both uploads are checked by size and md5.
   - writes `done/<id>.json` (tarball sha256, modules, CPU and wall times, audit result, spec sha256, provenance), then sets the lease to `done`.
   - sends a seeded share of the private parts (`PB_SAMPLE`, 0.001) to `sample/<id>/`, then deletes the package's private parts.
6. **Verify.** `verify/verifier.py` reads every done tarball. It checks:
   - the tarball sha256 against the done record, every olean-format file (magic, toolchain version, non-zero tail) against `SHA256SUMS`;
   - each module's own hashes (its `KMH` line);
   - store imports, which must be produced by a done package with the same hash;
   - closure imports, which must resolve through the final `LEAN_PATH` to the same hash;
   - one name, one content across all done packages.
   It also indexes each module's producer and collects the obligation union.
7. **Union walk.** `final/walk.py` walks every package's external obligations with `KModExt.lean` at the private level. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
8. **Final build.** `final/final_build.sh` builds `R22K.Final` against the top store. It runs `#print axioms` (5 theorems) and the top-level KMod audit (`kmod_audit_obl.py --no-ext`), then the external step for the leftover obligations (`final_ext.py`, which reuses obligations the union walk already passed). Last, it checks that the environment is unchanged since its manifest (`envmanifest.py --check`).
9. **V5.** `final/v5.py --snapshot SNAPDIR` writes one PASS/FAIL line per checklist item to `V5_RESULT.txt`, from a frozen queue snapshot (`snapshot.py`). It also defines the sets:
   - (a) the final set: R22K.Final's dependency DAG, i.e. the producers of its top-store modules closed under spec `deps`;
   - (b) every done, non-superseded record;
   - (c) (b) − (a).
   `classify.py --snapshot` and `sample_census.py --snapshot` read the same snapshot.

## Queue layout (under `PB_PREFIX` in namespace `PB_BUCKET`)

| object | meaning |
|---|---|
| `packages.jsonl` | the spec lines; claim order = file order (`front.py`, `pbq.py add --front` reorder) |
| `lease/<id>` | `held` / `done` / `failed` / `parked`, holder, time, attempts |
| `done/<id>.json` | the result record of the current build |
| `superseded/<id>.json` | a retired package's former done record (`superseded_by`, reason, time); `unsuperseded/<id>` audits a restore |
| `parked/<id>`, `failed/<id>`, `attempts/<id>`, `requeued/<id>` | markers and audit trail of the sweep and of operator actions |
| `tar/<shard>/...tar.zst`, `pubs/<shard>/...tar` | result tarballs and public-part tarballs |
| `sample/<id>/<module>.olean.private` | the seeded private-part sample |
| `taken.json.gz`, `done.json.gz` | snapshots of the leased and done ids (`pbq.py snapshot --loop`) |
| `CONTROL` | `{"launch": false}` stops claiming |

## Environment

| variable | used by | meaning (default) |
|---|---|---|
| `PB_STORE` | all | `file:///ABS/DIR` (local directory) or `http(s)://...` (JSON object API) (`file://$PWD/pbstore`) |
| `PB_STORE_API`, `PB_STORE_UPLOAD`, `PB_STORE_TOKEN_CMD` | objstore.py (http) | URL templates with `%s` for the namespace; command printing a bearer token |
| `PB_BUCKET`, `PB_PREFIX` | all | store namespace and queue prefix (`kp`, `pb/run`) |
| `PB_ROOT` | worker | the worker's root: intake/, pkgs/, store/, logs/, work/ (`./pbroot`) |
| `PB_LPATH` | worker | file holding the closure's LEAN_PATH (`PB_ROOT/lpath.txt`) |
| `PB_TOOLCHAIN`, `PB_LEAN` | worker, final, sample | Lean bin directory; lean binary (`lean` on PATH) |
| `PB_CLOSURE_ROOT` | worker | where a tarball package's `root/` part is merged (`PB_ROOT/root`) |
| `PB_SLOTS`, `PB_EMITTERS`, `PB_BACKLOG_S`, `PB_SAMPLE`, `PB_BOX`, `PB_ONCE`, `PB_PIN_ONLY`, `PB_HEAVY_ONLY`, `PB_SPLIT_ONLY` | worker | build slots (nproc − 2), concurrent emissions (2), queued work per slot (1800 s), private sample rate (0.001), worker name (hostname), exit when idle (`1`), claim filters |
| `PBQ_TTL`, `PBQ_RESCAN`, `PBQ_WINDOW`, `PBQ_MAX_MISSES`, `PBQ_WORKERS_FILE` | pbq.py | lease expiry (1200 s), claim tuning, optional list of live workers for the sweep |
| `PB_WORK` | verify, final, winners | the verification workspace (`./pbwork`) |
| `SCAN_DIR`, `FINAL_DIR`, `VERIFIER_DB` | verify, final | verifier state (`PB_WORK/scan`), final workspace (`PB_WORK/final`), verifier db (`SCAN_DIR/verifier.db`) |
| `PB_STORE_PREFIX` | verifier, sample_overlay | the worker store path recorded in the `.mhash` KIMP lines being checked (`PB_ROOT/store/`) |
| `REAUDIT_FILE`, `GATES_FILE` | v5, classify, snapshot | offline re-audit results (`PB_WORK/audit/reaudit.out`); list of gate files (`PB_WORK/gates.txt`) |
| `MKINST`, `KMOD_BUILD`, `FTOP_BUILD` | final_build.sh | mkinst.py, kmod_build.sh, the build dir of R22K.FinalTop/Cap/FinalAll/Cor |
| `KMOD_LEAN`, `KMOD_LEAN_PATH` | kmod_audit_obl.py, pkgaudit.py, crosscheck.sh | lean binary, closure LEAN_PATH for the audit tools |
| `RACE_DIR`, `PT_DIR`, `AGG_PLAN`, `EXTCUT_IDS`, `EXTCUT_STATE` | winners | alternative-attempt spec files, aggregation lines, cut ids and state |
| `V5_TOOLCHAIN_CLOSURE` | v5.py | file name of the toolchain closure in the provenance records (`kclosure_v1.tar.zst`) |

## Building one package locally and comparing hashes

```
export PB_STORE=file://$PWD/store PB_PREFIX=pb/one PB_ROOT=$PWD/root PB_LPATH=$PWD/lpath.txt PB_TOOLCHAIN=<lean v4.30.0 bin> PB_ONCE=1
# lpath.txt: the closure's LEAN_PATH (Mathlib, the frozen port, the libraries), one line, ':'-separated
# pkg.jsonl: the package's spec line (and, for a package with deps, the spec lines of its dependencies)
python3 queue/pbq.py init kp pb/one pkg.jsonl
python3 queue/pbworker.py          # claims, emits, builds, audits, finalizes; exits when nothing is left (PB_ONCE=1)
```

The done record lands in `store/kp/pb/one/done/<id>.json` and the tarball in `store/kp/pb/one/tar/...`.
- **Compare:** each module's `.olean` sha256 (its `KMH` line in `store/<module path>.mhash` inside the tarball) against the module list of that package (zenodo `packages_modules`), and the root modules against `manifests/packages.tsv.zst`.
- **Do not compare tarball sha256s.** Those differ by construction (see below).

## Winner selection (first finisher wins)

Some packages had several attempts: parallel re-emissions, split builds of one package (groups plus a final), cut builds of a giant EXT leaf, or race copies. Exactly one attempt per slot is ever a dependency and enters the top store. The losers are retired with `supersede.py`: the done record moves to `superseded/`, and the lease is parked, so a worker still building it drops it. A retired package whose done record reappears (a finalize racing the park) is retired again.
- **race.py.** A slot is a dependency X of an aggregation line, with its alternatives: re-emissions X.re and X.r2 (spec `replaces`: X), and split finals of each (family X: X.sb, or a re-cut final of kind `splitbuild-final`).
  - When one alternative is done, it becomes the aggregation line's dependency. If several are done, the current dependency stays if it is one of them, otherwise the earliest `t_done` wins.
  - All other alternatives, and the group packages of each losing family, are retired.
- **ptc_resolve.py.** Each point range's v8 package races its replacements (`PT_DIR/pt_v*.jsonl`, `parent` = the v8 id).
  - The first done attempt becomes `agg_ptc`'s dependency for that range.
  - The other attempts are retired, together with their split packages that are not done.
- **pairrace.py.** Packages that build the same thing race each other (a race copy).
  - The gated line's dependency becomes the first done copy. If two finish together, the copy the top store installed wins, otherwise the earliest `t_done`.
  - The other copies are retired.
- **multirace.py.** The attempts of one giant EXT leaf race each other, each attempt counting together with its split packages.
  - When any id of an attempt is done, every package of every other attempt is retired.
  - An attempt whose lease failed outright is parked.
- **extcut_race.py.** A giant EXT package ID races its cut build (groups ID.sb0_k and final ID.sb).
  - If ID.sb finishes first, ID is retired. If ID finishes first, the cut's packages that are not done are retired.
  - The winner's own split packages are never retired: when ID.sb wins, its groups are its dependencies.

## Determinism

- **Reproducible: `.olean` bytes.** Given the same toolchain, the same closure files, the same sources and the same module names, a module's `.olean` is the same file.
  - This is what the hashes compare. The `KMH` line, the verifier's own-hash check and the one-name-one-content check all work on `.olean` sha256.
  - A package built twice (a lease that expired on a loaded worker, rebuilt elsewhere) is accepted only if its `.olean`, `.ilean` and `.olean.server` files are byte-identical to the first build's (`resolve_conflicts.py`). V5 B3 counts every unresolved difference.
- **Not reproducible:** logs, timings, `results.jsonl`, the `.kman` and `.mhash` records (they hold timings and the absolute paths of the building machine), and the tarballs.
  - Tarballs are written with the files' modification times and owners and compressed with multi-threaded zstd, so their sha256 identifies one build, not its content.
  - Done records name the tarball by sha256. Content is compared per module.

## Tool versions

- The production run's workers ran successive versions of this kit. Each done record names its version: `tools_claim` and `tools_finalize` hold the kit tarball's sha256.
- The files here are the final version, with storage, paths and machine names replaced by the environment variables above.
- The decision rules are those of the final version: the audit, the hashes, the verifier checks, the winner rules and V5.
- Shared with the KMod library:
  - `KModTyChk.lean` (sha256 b8f84d6dcc73e4c82ca27cec440ede392dbbf35cc3f82d9f73af85c081420bf5) and `KModExt.lean` (sha256 7523a74fb0a70e0a98b11c0bbf7bb32aad4d08c94b02afd4f2f559233f646acb) are byte-identical copies.
  - `kmod_audit_obl.py` is the library's `kmod_audit.py` (md5 c7594ac1) with one change: `--obl-out` is also written under `--no-ext`.
