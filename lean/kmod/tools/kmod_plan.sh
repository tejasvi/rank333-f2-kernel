#!/bin/bash
# kmod_plan.sh PLAN [P]: build the stages of PLAN (one line per stage, module names) in order with kmod_build.sh, P modules in
# parallel (default 32); stops after a stage with a failure.  The kmod_build.sh environment (KMOD_*) passes through.
PLAN=$1; P=${2:-32}; B=$(dirname "$(readlink -f "$0")")/kmod_build.sh; LOG=${KMOD_LOG:-$PWD/log}; mkdir -p "$LOG"
tag=$(basename "$PLAN" .plan); s=0
while read -r line; do
  t0=$(date +%s.%N)
  echo $line | tr ' ' '\n' | xargs -P $P -n 1 "$B" > "$LOG/${tag}_stage$s.out" 2>&1
  bad=$(/usr/bin/grep -c -E 'rc=[1-9]|UNCLEAN' "$LOG/${tag}_stage$s.out")
  echo "stage $s: $(echo $line | wc -w) modules, $(awk "BEGIN{print $(date +%s.%N) - $t0}") s wall, failures $bad"
  [ "$bad" -ne 0 ] && { /usr/bin/grep -E 'rc=[1-9]|UNCLEAN' "$LOG/${tag}_stage$s.out" | head; exit 1; }
  s=$((s+1))
done < "$PLAN"
