#!/bin/bash
# build_cc.sh [MODULE...]: build the CC-route modules (HC436.*, S4.*) into build/ in dependency order (default: all 24), then compare
# the .olean and .olean.private files with OLEANS.sha256. Each module: lean -j1 -R src src/<path>.lean, run from this directory: the
# data files of HC436 (#rttable, #rttablew) are read from data/hc436/ by relative paths.
#
# Environment:
#   LEAN           the Lean v4.30.0 `lean` binary
#   LEAN_PATH_ENV  the .olean roots: the KMod build (lean/kmod), the frozen port build, Mathlib and its dependencies, the Lean
#                  toolchain (lean/TOOLCHAIN.md)
set -eu
cd "$(dirname "$0")"
ORDER="HC436.IP_c436 HC436.SL_c436 HC436.OK_c436_Base HC436.OK_c436_S0 HC436.OK_c436_F HC436.OK_c436
S4.PlaneLift S4.SatQ S4.PlaneW S4.PlaneW3 S4.TopCC S4.CCLeaf S4.CC422 S4.CC436 S4.SplitQ S4.SplitR S4.SplitRN S4.EqF S4.PLDrv
S4.PLDrvM S4.PLDrvR S4.PLDrvRE S4.PLDrvRN S4.Top436"
if [ $# -gt 0 ]; then MODS="$*"; else MODS=$ORDER; fi
export LEAN_PATH="$PWD/build:$LEAN_PATH_ENV"
NI=$((10-$(nice))); [ $NI -lt 0 ] && NI=0
mkdir -p build log
for m in $MODS; do
  f=src/$(echo $m | tr . /).lean; o=build/$(echo $m | tr . /); mkdir -p "$(dirname $o)"
  nice -n $NI "$LEAN" -j1 -R src $f -o $o.olean -i $o.ilean > log/$m.log 2>&1 || { echo "FAIL $m"; tail -20 log/$m.log; exit 1; }
  echo "ok $m"
done
[ $# -gt 0 ] || (cd build && sha256sum -c ../OLEANS.sha256)
