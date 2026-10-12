#!/bin/bash
# p0cc/run.sh [PAR]: phase 0 on the CC route's table (case II): the 61 batches of the native phase 0 (rerun/r3/p0/b10's PFILEs and
# batch table) with FLAGS_CCW + --pctop F PFILE --pcert --dumpfrontier --threads 1 (prof7R3k14c, as rerun/r3/p0/b10n/run.sh), PAR at
# once (default 61), absolute nice 10, prlimit 16 GiB each. Outputs runs/p0cc/{seg,dump,log}_<name>.*; then check.txt: every log EXIT 0,
# each DUMP compared with b10's (identical or not), header #pcwit. A free-space guard stops the run below 15 GB free.
R=${R22:?set R22 to the tree root}; K=$R/lean/kinds; P=$R/lean/rerun/r3/p0; O=$K/runs/p0cc; B=$R/lean/rerun/r3/prof7R3k14c
FL=$(sed -n 's/^FLAGS_CCW //p' $K/runs/xqcc/recipe_cc.txt); PAR=${1:-61}
NI=$((10-$(nice))); [ $NI -lt 0 ] && NI=0
python3 $K/py/recipecheck.py $K/runs/xqcc/recipe_cc.txt FLAGS_CCW > $O/recipecheck.txt 2>&1 || { cat $O/recipecheck.txt; exit 2; }
run(){ n=$1; F=$2; rm -f $O/seg_$n.r3 $O/dump_$n.txt
  /usr/bin/time -v prlimit --as=17179869184 nice -n $NI $B $FL --pctop $F $P/b10/pfile_$n.txt --pcert $O/seg_$n.r3 --dumpfrontier $O/dump_$n.txt --threads 1 > $O/log_$n.txt 2>&1
  echo "EXIT $?" >> $O/log_$n.txt; }
cat $P/b10/batches_s*.tsv > $O/batches.tsv
# free-space guard: below 15 GB free, stop this run's searches (processes named prof7R3k14c of this user; the machine runs only this phase)
( while sleep 30; do f=$(df -BG --output=avail $O | tail -1 | tr -dc 0-9); [ "$f" -lt 15 ] && { echo "$(date -u +%T) FREE SPACE ALARM: ${f} GB" >> $O/alarm.txt
    for p in $(pgrep -u $(id -u) -x prof7R3k14c); do kill $p; done; }; [ -f $O/done ] && break; done ) &
PIDS=()
while read n F np dr; do
  while [ $(jobs -rp | wc -l) -ge $((PAR + 1)) ]; do sleep 2; done
  run $n $F < /dev/null & PIDS+=($!)
done < $O/batches.tsv
wait "${PIDS[@]}"
{ bad=0; nd=0; nseg=0; ndiff=0
  while read n F np dr; do
    grep -q '^EXIT 0$' $O/log_$n.txt || { echo "FAIL $n: no EXIT 0"; bad=1; }
    if cmp -s $P/b10/dump_$n.txt $O/dump_$n.txt; then nd=$((nd+1)); else echo "DUMP DIFFERS $n ($(wc -l < $P/b10/dump_$n.txt) vs $(wc -l < $O/dump_$n.txt) lines)"; ndiff=$((ndiff+1)); fi
    head -c 4000 $O/seg_$n.r3 | grep -aq "^#pcwit 1" || { echo "NO #pcwit in $n"; bad=1; }
    nseg=$((nseg+1)); done < $O/batches.tsv
  echo "batches $nseg, DUMPs byte-identical to b10: $nd, differing: $ndiff, problems: $bad"; } > $O/check.txt
( cd $O && sha256sum seg_*.r3 dump_*.txt > SHA256SUMS.txt )
touch $O/done
