#!/bin/bash
# build.sh MOD...: build KMod library or test modules with tools/kmod_build.sh.
# Environment: KMOD_LEAN_PATH = the frozen port build directory followed by its library roots (Mathlib and dependencies,
# the Lean toolchain's lib/lean); KMOD_LEAN = the lean binary (default: lean on PATH).
# Library modules:  KMOD_PLAIN=1 ./build.sh KMod.Vocab KMod.Units KMod.Audit KMod.Comb
# Tests:            ./build.sh KModT.Good ...  (the E1 tests read the frozen port's snap/data through ./port_data)
set -e
cd "$(dirname "$(readlink -f "$0")")"
: "${KMOD_LEAN_PATH:?set KMOD_LEAN_PATH to the frozen port build and its library roots}"
export KMOD_SRC=$PWD KMOD_OUT=${KMOD_OUT:-$PWD/build} KMOD_LOG=${KMOD_LOG:-$PWD/log}
exec ./tools/kmod_build.sh "$@"
