#!/bin/bash
# w321.sh RL QD JOBS...: cases (I) / (I13) queue run (prof7R3q_b14, recipe_321.txt line RL = FLAGS_IW or FLAGS_I13W, both with
# --pcwit) on the depth-1 jobs of rt321/frontier_d1_321.txt (0: root 0, 1: root 168; 2 is the dead root 462, not queued): helpers
# with --xqcap ${CAP:-10000} --xqcapd ${CAPD:-19}, so split units leave range items and piece items of at most about CAP nodes.
# Output in runs/xqcc/QD: srv/manifest.log, plan.txt (xqaudit --plan), the helpers' pc_*.r3.xq item segments. Absolute nice 10.
# env LINGER: helper linger seconds (default 60; many helpers on few initial jobs: longer, the run ends with xqctl exit).
# env FRONTIER: the depth-1 job table (inputs/caseII/case321/frontier_d1_321.txt).
# env PY: the Python for xqd / xqctl / xqaudit (stdlib only; default the build machine's venv; a machine without it: PY=python3).
D=$(cd $(dirname $0); pwd); RL=$1; Q=$D/$2; shift 2; PORT=${PORT:-7988}; B=${R22:?set R22 to the tree root}/xq/r3q/bin/prof7R3q_b14
R=${R22:?set R22 to the tree root}; PY=${PY:-python3}; X="$PY $R/xq/xqctl.py --addr 127.0.0.1:$PORT"
# recipe_321.txt names its table files with placeholders: @BASE@ (env BASE_TABLES: the directory of tab_C3eD.bin and kept_C3eDc4d.txt)
# and @R22@ (the tree root); the run uses a substituted copy next to the run directory
RF=$Q.recipe_321.txt; sed "s|@BASE@|${BASE_TABLES:?set BASE_TABLES}|g; s|@R22@|$R|g" $D/recipe_321.txt > $RF
FLAGS=$(sed -n "s/^$RL //p" $RF); log(){ echo "$(date -u +%T) $*"; }
case " $FLAGS " in *" --pcwit "*) ;; *) echo "w321: recipe line $RL without --pcwit"; exit 2;; esac
NI=$((10-$(nice))); [ $NI -lt 0 ] && NI=0; NH=${NH:-6}
hrun(){ local n=$1 th=$2; shift 2; mkdir -p $Q/$n; nice -n $NI $B $FLAGS --xqrecipe $RF:$RL --agedonate 10 --donate_depth 15 --xqhelper --xqlinger ${LINGER:-60} --threads $th --xqcap ${CAP:-10000} --xqcapd ${CAPD:-19} --out $Q/$n/F_$n.prof --pcert $Q/$n/pc_$n.r3 --xq 127.0.0.1:$PORT "$@" > $Q/$n/log.txt 2>&1 & echo $! > $Q/$n/pid; }
rm -rf $Q; mkdir -p $Q; printf '%s\n' "$@" > $Q/j.txt
setsid -f nice -n $NI $PY $R/xq/xqd.py --base $Q/srv --port $PORT --lease 120 > $Q/srv.out 2>&1 < /dev/null; sleep 2
for h in $(seq 1 $NH); do hrun h$h ${TH:-4}; done; sleep 15
until $X addjobs pool=X space=k321$RL compat=auto statedir=$Q frontier=${FRONTIER:-$R/lean/rerun/r3/rt321/frontier_d1_321.txt} jobs=$Q/j.txt rord=321 | grep -q "^OK"; do sleep 5
  alive=0; for h in $(seq 1 $NH); do kill -0 $(cat $Q/h$h/pid) 2>/dev/null && alive=1; done
  [ $alive = 0 ] && { log "no helper alive: $(tail -1 $Q/h1/log.txt)"; p=$(awk '{print $1}' $Q/srv/xqd.pid); grep -qa "xqcc/$(basename $Q)/srv" /proc/$p/cmdline && kill $p; exit 1; }
done
log "jobs queued: $*"
until [ "$(wc -l < $Q/gather/xq/state_X_xq.txt 2>/dev/null || echo 0)" -ge $# ]; do sleep 10; [ $SECONDS -gt 14400 ] && { log timeout; break; }; done 2>/dev/null; log "jobs complete"
$X exit "*"; wait
grep -h "item-size cap.*reached" $Q/h*/log.txt | cut -c1-200 | head -20
$PY $R/xq/xqaudit.py $Q/srv/manifest.log --plan $Q/plan.txt | tail -3
awk '$1=="I"{k[$4]++} END{for(x in k) printf "kind %s: %d items  ", x, k[x]; print ""}' $Q/plan.txt
p=$(awk '{print $1}' $Q/srv/xqd.pid); grep -qa "xqcc/$(basename $Q)/srv" /proc/$p/cmdline && kill $p; log done
