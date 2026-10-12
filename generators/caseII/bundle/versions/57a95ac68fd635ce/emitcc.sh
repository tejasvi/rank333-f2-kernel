#!/bin/bash
# emitcc.sh [OUT]: case-II package emission on a build machine (CC route, table cc436_422), the `then` step of the worker, run in the
# extracted package dir OUT (default .). The package holds spec.json: {"prefix": P, "jobs": [[batch, idx, [labels…]], …]}.
#  1. A local queue: xqd on 127.0.0.1 (a free port) and prof7R3q_b12d helpers on the build machine (EMIT_THREADS, default all cores; 8 threads
#     each) with FLAGS_CCW of the bundle's recipe (table paths rewritten to the bundle; py/recipecheck.py must pass), --xqcap 1000
#     --xqcapd 15 --donate_depth 15 --agedonate 10 --pcwit (in FLAGS_CCW). Jobs: one addjobs per batch, from mini frontier files.
#  2. When every job is complete: xqaudit --plan (AUDIT OK required), then py/emitlazy.py (lazy: nothing converted here): the items'
#     keys (r3qglue --itemkey) and dead roots, stub item modules with their item lists, the Cov chunks (py/mkaggf.py, AGG_LEAF=1,
#     one root chunk), and the top <P>.Top: #kmRekeyCC over the root chunk (the job roots' minimal keys: a statement that does not
#     depend on how the jobs were split). Each item-module unit converts its own items (py/unitconv.py, from kmod_unit.sh) just
#     before its build and deletes them after; the segments stay until the package is done (about 25 KB per node).
#  3. (folded into 2)
#  4. mkpkgw.py: manifest.jsonl (cmd units ./kmod_unit.sh <module>, env KMOD_OUT={STORE}, deps, pred_s, pred_gb, pub on <P>.Top),
#     kmod_unit.sh, tools/, lpath_common.txt (the library closure's), emit.json (the run's hashes, counts and times).
# Absolute nice 10 throughout. Env: KINDS_BUNDLE (this script's dir), KPY (python3 with numpy), EMIT_THREADS, EMIT_TIMEOUT (14400 s).
# Closure check: the bundle's CLOSURE names the library closure it emits for (line 1) and the sha256 of three of its oleans; the first
# lpath_common.txt entry with a KB/ directory (placeholders @CLOSURE_ROOT@ and @LEAN_TOOLCHAIN@ substituted from the environment) must hold exactly those
# files, else exit 3 (a machine with another closure must not emit). The package's units check the same before they build.
set -e
OUT=$(readlink -f ${1:-.}); B=$(cd $(dirname $(readlink -f $0)); pwd)
export KINDS_R22=$B/r22 LD_LIBRARY_PATH=$B/bin${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
R=$KINDS_R22; K=$R/lean/kinds; PY=${KPY:-python3}; NI=$((10-$(nice))); [ $NI -lt 0 ] && NI=0
T0=$(date +%s); cd $OUT; mkdir -p q data/q src
log(){ echo "$(date -u +%T) $*" | tee -a emit.log; }
PFX=$($PY -c 'import json; print(json.load(open("spec.json"))["prefix"])')
CLD=""; for e in $(sed "s|@CLOSURE_ROOT@|${CLOSURE_ROOT:?set CLOSURE_ROOT}|g; s|@LEAN_TOOLCHAIN@|${LEAN_TOOLCHAIN:-}|g" $B/lpath_common.txt | tr ':' ' '); do for d in "$e"; do [ -d "$d/KB" ] && { CLD=$d; break 2; }; done; done
[ -n "$CLD" ] && (cd "$CLD" && tail -n +2 $B/CLOSURE | sha256sum -c --quiet --status) || { log "closure check failed: $(head -1 $B/CLOSURE) not installed (KB in ${CLD:-none})"; exit 3; }
sed "s|@R22@|$R|g" $K/runs/xqcc/recipe_cc.txt > q/recipe_cc.txt
$PY $K/py/recipecheck.py q/recipe_cc.txt FLAGS_CCW > q/recipecheck.txt 2>&1 || { cat q/recipecheck.txt; exit 2; }
FLAGS=$(sed -n 's/^FLAGS_CCW //p' q/recipe_cc.txt)
PORT=$($PY -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])')
setsid -f nice -n $NI $PY $R/xq/xqd.py --base $OUT/q/srv --port $PORT --lease 120 > q/srv.out 2>&1 < /dev/null; sleep 2
# helpers: EMIT_THREADS, default half the cores and at most 128 threads (16 helpers); every helper loads the CC tables, so more helpers
# per machine cost memory and start-up time
TH=8; NC=$(nproc); DT=$(( NC / 2 )); [ $DT -gt 128 ] && DT=128; NT=${EMIT_THREADS:-$DT}; NH=$(( NT / TH )); [ $NH -lt 1 ] && NH=1
for h in $(seq 1 $NH); do mkdir -p q/h$h
  nice -n $NI $R/xq/r3q/bin/prof7R3q_b12d $FLAGS --xqrecipe q/recipe_cc.txt:FLAGS_CCW --agedonate 10 --donate_depth 15 --xqhelper \
    --xqlinger 600 --threads $TH --xqcap 1000 --xqcapd 15 --out q/h$h/F.prof --pcert q/h$h/pc.r3 --xq 127.0.0.1:$PORT > q/h$h/log.txt 2>&1 &
  echo $! > q/h$h/pid; done
sleep 8
X="$PY $R/xq/xqctl.py --addr 127.0.0.1:$PORT"
NB=$($PY - <<'PY'
import json, collections
s = json.load(open('spec.json')); g = collections.OrderedDict()
for b, ix, pre in s['jobs']: g.setdefault(b, []).append((ix, pre))
for b, js in g.items():
    open('q/fr_%s.txt' % b, 'w').write(''.join('%d %s\n' % (ix, ' '.join(map(str, pre))) for ix, pre in js))
    open('q/jobs_%s.txt' % b, 'w').write(''.join('%d\n' % ix for ix, _ in js))
open('q/batches.txt', 'w').write(''.join(b + '\n' for b in g))
print(len(g))
PY
)
NJ=$($PY -c 'import json; print(len(json.load(open("spec.json"))["jobs"]))')
# addjobs compat=auto needs a connected helper: wait for one (EMIT_CONNECT_TIMEOUT s, default 1800; helpers load the tables first, which
# is slow on a busy machine), and fail at once with the helpers' log tails if none is alive
CT=${EMIT_CONNECT_TIMEOUT:-1800}; t0c=$(date +%s)
until [ "$($X status 2>/dev/null | $PY -c 'import json,sys; d=json.load(sys.stdin); print(sum(1 for r in d["runs"] if r["connected"]))' 2>/dev/null || echo 0)" -ge 1 ]; do
  alive=0; for h in $(seq 1 $NH); do kill -0 $(cat q/h$h/pid) 2>/dev/null && alive=1; done
  [ $alive = 1 ] || { log "no helper alive before addjobs; h1: $(tail -3 q/h1/log.txt | tr '\n' ' ')"; exit 1; }
  [ $(($(date +%s) - t0c)) -gt $CT ] && { log "no helper connected after $CT s; h1: $(tail -3 q/h1/log.txt | tr '\n' ' ')"; exit 1; }
  sleep 3; done
log "helpers connected after $(($(date +%s) - t0c)) s"
while read b; do
  for t in $(seq 1 120); do r=$($X addjobs pool=$b space=cc_$b compat=auto statedir=$OUT/q frontier=$OUT/q/fr_$b.txt jobs=$OUT/q/jobs_$b.txt rord=123 2>&1) && case "$r" in OK*) break;; esac; sleep 2; done
  case "$r" in OK*) ;; *) log "addjobs failed for $b: $r"; exit 1;; esac
done < q/batches.txt
log "queued $NJ jobs in $NB batches; $NH helpers x $TH threads"
TO=${EMIT_TIMEOUT:-14400}
until [ "$(cat q/gather/xq/state_*_xq.txt 2>/dev/null | wc -l)" -ge $NJ ]; do sleep 5
  [ $(($(date +%s) - T0)) -gt $TO ] && { log "timeout"; $X exit "*" > /dev/null 2>&1; exit 1; }
  alive=0; for h in $(seq 1 $NH); do kill -0 $(cat q/h$h/pid) 2>/dev/null && alive=1; done; [ $alive = 1 ] || { log "no helper alive"; exit 1; }
done
T1=$(date +%s); $X exit "*" > /dev/null 2>&1 || true; wait
p=$(awk '{print $1}' q/srv/xqd.pid 2>/dev/null); [ -n "$p" ] && grep -qa "$OUT/q/srv" /proc/$p/cmdline 2>/dev/null && kill $p
$PY $R/xq/xqaudit.py q/srv/manifest.log --plan q/plan.txt > q/audit.txt 2>&1; grep -q "AUDIT OK" q/audit.txt || { tail -5 q/audit.txt; exit 1; }
nice -n $NI $PY $K/py/emitlazy.py $OUT $PFX $NT > q/emitlazy.txt 2>&1 || { tail -5 q/emitlazy.txt; exit 1; }
T2=$(date +%s); A=$(tail -1 src/${PFX}_waves.txt)
mkdir -p src/$PFX; printf '%s\n' module 'meta import KMod.Units' 'meta import KMod.Audit' 'public import KB.AggCC_cc436_422' \
  'meta import KB.ModRekeyCC' "import $A" 'set_option Elab.async false' 'set_option maxRecDepth 100000' \
  'set_option exponentiation.threshold 100000000' 'run_cmd Lean.modifyEnv (Lean.LibrarySuggestions.typePrefixDenyListExt.addEntry · `R22N.AllL)' \
  "#kmRekeyCC $PFX.Top.cov $A.cov" "#kax $PFX.Top.cov" > src/$PFX/Top.lean
echo "$PFX.Top" >> src/${PFX}_waves.txt
printf '%s\ttop\t1\t0\t0.30\t0.90\t0\t%s\n' "$PFX.Top" "$A" >> src/manifest.tsv
nice -n $NI $PY $B/mkpkgw.py $OUT $PFX $B "$T0 $T1 $T2" > q/mkpkgw.txt 2>&1
log "emitted: $(tail -1 q/mkpkgw.txt)"
