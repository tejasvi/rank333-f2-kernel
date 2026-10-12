#!/bin/bash
# build.sh MOD...: compile src/<MOD as path>.lean into build/ as Lean 4.30 module files, one module per lean call
# (Elab.async off, RLIMIT_AS 64 GiB, nice 10), stopping at the first failure; "wall user sys maxRSS_KB" goes to log/<MOD>.time.
# Build the whole library in order:  ./build.sh $(cat build_order.txt build_order_ext.txt)
# Environment:
#   LEAN     the lean binary of toolchain leanprover/lean4 v4.30.0 (default: lean on PATH)
#   DEPS     colon-separated LEAN_PATH entries of the dependency builds, in this order: the S4 module build,
#            the KMod build, the frozen port build, then Mathlib and its packages
#   NOTHP    optional: path of nothp.py (runs lean with transparent huge pages off)
#   MODHASH  optional: path of modhash.py; after each module, `modhash.py record` writes build/<path>.mhash (resolved imports
#            and their hashes)
# The library reads its data files by relative paths under data/ (see DATA.sha256): run this script from this directory.
cd "$(dirname "$(readlink -f "$0")")"
export LEAN_PATH=$PWD/build${DEPS:+:$DEPS}
LEAN=${LEAN:-lean}; mkdir -p build log
for m in "$@"; do
  f=src/$(echo $m | tr . /).lean; o=build/$(echo $m | tr . /); mkdir -p "$(dirname $o)"
  rm -f $o.olean $o.ilean $o.olean.private $o.olean.server $o.ir
  run=(nice -n 10 "$LEAN" -j1 -DElab.async=false -R src $f -o $o.olean -i $o.ilean)
  [ -n "${NOTHP:-}" ] && run=(python3 "$NOTHP" "${run[@]}")
  /usr/bin/time -f "%e %U %S %M" -o log/$m.time prlimit --as=68719476736 "${run[@]}" > log/$m.log 2>&1; rc=$?
  echo "== $m rc=$rc $(cat log/$m.time)"; [ $rc -ne 0 ] && { grep -A8 error log/$m.log | head -30; exit $rc; }
  if [ -n "${MODHASH:-}" ]; then python3 "$MODHASH" record $o.olean $m --lean-path "$LEAN_PATH" > log/$m.mhash.log 2>&1 || { echo "== $m modhash record failed"; exit 3; }; fi
done
exit 0
