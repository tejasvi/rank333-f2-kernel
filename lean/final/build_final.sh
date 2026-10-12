#!/bin/bash
# build_final.sh: build R22K.FinalTop, R22K.Cap, R22K.FinalAll, R22K.Cor and R22K.Final in KMod form into build/, print the axioms of
# the five public theorems of R22K.Final (src/R22KChk/Axioms.lean), and compare the .olean files with OLEANS.sha256.
#
# Environment:
#   LEAN           the Lean v4.30.0 `lean` binary
#   KMOD_BUILD_SH  the KMod build script (lean/kmod/kmod_build.sh): one KPUB/KAX/KAXSUM/KAXP manifest per module; it deletes a module's
#                  .olean.private once its manifest is clean, unless KMOD_KEEP_PRIVATE=1
#   LEAN_PATH_ENV  the .olean roots of everything R22K imports: the producers' package store, lean/cc, lean/cc/g2, lean/e1g, lean/caseII,
#                  lean/hcapk, lean/kmod, the frozen port build, Mathlib and its dependencies, the Lean toolchain (lean/TOOLCHAIN.md)
#
# src/R22K/Final.lean is the output of
#   python3 py/mkinst.py --kII 1 --ext 420 450 451 454 455 456 458 460 463 464 465 469 470 471 472 473 475 476 485 487 490
# src/R22K/FinalAll.lean and Cor.lean are the output of py/mkftall.py, src/R22K/Cap.lean of py/mkcap.py (PORT_SRC, HCAPK_BUILD).
set -eu
cd "$(dirname "$0")"; T=$PWD
mkdir -p build log
export PATH="$(dirname "$LEAN"):$PATH"
export KMOD_SRC=$T/src KMOD_OUT=$T/build KMOD_LOG=$T/log KMOD_LEAN_PATH="$LEAN_PATH_ENV"
bash "$KMOD_BUILD_SH" R22K.FinalTop R22K.Cap R22K.FinalAll R22K.Cor
KMOD_KEEP_PRIVATE=1 bash "$KMOD_BUILD_SH" R22K.Final
LEAN_PATH="$T/build:$LEAN_PATH_ENV" nice -n $((10-$(nice))) "$LEAN" -R src src/R22KChk/Axioms.lean > log/Axioms.log 2>&1
cat log/Axioms.log
n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" log/Axioms.log || true)
[ "$n" = 5 ] || { echo "FAIL #print axioms ($n of 5)"; exit 1; }
echo "PASS #print axioms: 5 of 5 theorems use exactly [propext, Classical.choice, Quot.sound]"
(cd build && sha256sum -c ../OLEANS.sha256)
