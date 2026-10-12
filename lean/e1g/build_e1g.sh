#!/bin/bash
# build_e1g.sh [MOD...]: compile the e1g modules (this directory: E1GK.*, E1PQ.*, KH.*) into $E1G_BUILD (default ./build) as
# Lean v4.30.0 module files (.olean, .olean.server, .olean.private, .ir, .ilean).  Without arguments: every module, in dependency
# order (E1GK.ChainF, E1GK.ExtMono, E1GK.JobCmd3, E1GK.RootCmd, E1PQ.ChainF, E1PQ.JobCmd, then the 450 independent KH.*).
# LEAN_PATH: $E1G_BUILD, then
#   KMOD_BUILD  the KMod library's build (lean/kmod; E1GK.JobCmd3, E1GK.RootCmd and E1PQ.JobCmd meta-import KMod.Units),
#   PORT_FULL   the frozen full port build (E1G.Hdr, E1P.Hdr, RT.Load and their closure; see lean/TOOLCHAIN.md),
#   LP_BASE     Mathlib, its dependencies and core, as a LEAN_PATH string.
# Modules compile with cwd = this directory and no -R: the module name is the path relative to cwd, and KH.<name> reads its
# table as data/KH_<name>.bin, so KH_data.tar.zst is extracted here first (it creates data/).  LEAN: the lean binary of the
# toolchain (default: lean on PATH).
set -e
D=$(cd "$(dirname "$0")" && pwd); B=${E1G_BUILD:-$D/build}; cd "$D"
[ -d data ] || zstd -dc KH_data.tar.zst | tar xf -
export LEAN_PATH=$B:${KMOD_BUILD:?set KMOD_BUILD}:${PORT_FULL:?set PORT_FULL}:${LP_BASE:?set LP_BASE}
LEAN=${LEAN:-lean}
MODS="$*"
[ -n "$MODS" ] || MODS="E1GK.ChainF E1GK.ExtMono E1GK.JobCmd3 E1GK.RootCmd E1PQ.ChainF E1PQ.JobCmd $(ls KH/*.lean | sed 's|/|.|; s|\.lean$||' | sort)"
for m in $MODS; do
  f=$(echo $m | tr . /).lean; o=$B/$(echo $m | tr . /); mkdir -p "$(dirname "$o")"
  "$LEAN" -j1 "$f" -o "$o.olean" -i "$o.ilean" || { echo "FAILED $m"; exit 1; }
  echo "ok $m"
done
# compare with the production module files: (cd $E1G_BUILD && sha256sum -c ../OLEAN_SHA256) (see PART.md for the 3 modules whose
# .olean.server/.olean.private differ because their doc comments were edited for release)
