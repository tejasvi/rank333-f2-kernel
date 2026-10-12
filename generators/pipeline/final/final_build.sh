#!/bin/bash
# final_build.sh [CLASS ...]: the final top R22K.Final and its audit (V5 D1, C2, C3, B5), run once every top-level producer is done.
#  1. mkinst.py writes src/R22K/Final.lean with --kII 1 and the classes whose NDX.h<c>.Top exists in the top store (or the CLASS list
#     given);
#  2. the KMod library's kmod_build.sh builds R22K.Final in KMod form (KMOD_KEEP_PRIVATE=1: its .olean.private stays, for
#     #print axioms and leanchecker; KPUB/KAXSUM/KAXP manifest, THP off, 64 GiB AS, nice 10, -j1) with
#     LEAN_PATH = build : FINAL_DIR/topstore/store : FINAL_DIR/lpath_final.txt; then modhash.py record (.mhash);
#  3. src/R22KChk/Axioms.lean (`#print axioms` of the five public theorems), a module file importing R22K.Final at the exported level
#     (the producers' private parts are deleted by policy, so a plain import cannot load them): log/Axioms.log;
#  4. kmod_audit_obl.py (the KMod library's kmod_audit.py c7594ac1 + --obl-out under --no-ext) --root R22K.Final over build, the top
#     store and the R22K top build (FinalTop, Cap, FinalAll, Cor);
#  5. final_ext.py walks the external obligations it leaves (env: KModExt; package modules: manifests / tables);
#  6. envmanifest.py --check (the final environment unchanged since its manifest).
# Env: FINAL_DIR (the final workspace: lpath_final.txt, topstore/; this step works in FINAL_DIR/top), PB_TOOLCHAIN (Lean bin dir),
#      MKINST (mkinst.py), KMOD_BUILD (kmod_build.sh), FTOP_BUILD (the build dir holding R22K.FinalTop, Cap, FinalAll, Cor).
# Everything is logged under FINAL_DIR/top/log/; prints one line per step; exit status 0 iff every step passed.
set -u
K=$(cd "$(dirname "$0")/.."; pwd)
: "${FINAL_DIR:?set FINAL_DIR}" "${PB_TOOLCHAIN:?set PB_TOOLCHAIN}" "${MKINST:?set MKINST}" "${KMOD_BUILD:?set KMOD_BUILD}" "${FTOP_BUILD:?set FTOP_BUILD}"
F=$(cd "$FINAL_DIR"; pwd); T=$F/top; mkdir -p "$T"; cd "$T"
TC=$PB_TOOLCHAIN; export PATH=$TC:$PATH
mkdir -p src/R22K src/R22KChk build log
EXT=("$@")
if [ ${#EXT[@]} -eq 0 ]; then
  for c in 420 450 451 454 455 456 458 460 463 464 465 469 470 471 472 473 475 476 485 487 490; do
    [ -f $F/topstore/store/NDX/h$c/Top.olean ] && EXT+=("$c")
  done
fi
python3 "$MKINST" --kII 1 --ext "${EXT[@]}" --out $T/src/R22K/Final.lean || { echo "FAIL mkinst"; exit 1; }
sha256sum src/R22K/Final.lean | tee log/Final.lean.sha256
# R22K must resolve in ONE root (Lean binds a top-level package directory to the first LEAN_PATH root that has it, and build/ holds
# R22K/Final): the top build's R22K files (FinalTop, Cap, FinalAll, Cor) are copied byte-identically into build/R22K first
mkdir -p build/R22K
(cd "$FTOP_BUILD/R22K" && find . -maxdepth 1 -type f -printf '%f\n' | sort | xargs sha256sum) > log/COPIED_R22K.sha256
(cd "$FTOP_BUILD/R22K" && find . -maxdepth 1 -type f -exec cp -p {} "$T/build/R22K/" \;)
(cd build/R22K && sha256sum -c --quiet ../../log/COPIED_R22K.sha256) || { echo "FAIL R22K copy"; exit 1; }
export KMOD_KEEP_PRIVATE=1 KMOD_SRC=$T/src KMOD_OUT=$T/build KMOD_LOG=$T/log KMOD_LEAN_PATH="$F/topstore/store:$(cat $F/lpath_final.txt)"
bash "$KMOD_BUILD" R22K.Final > log/build.out 2>&1; rc=$?
tail -2 log/build.out; [ $rc -eq 0 ] || { echo "FAIL build rc=$rc"; exit 1; }
python3 $K/queue/modhash.py record build/R22K/Final.olean R22K.Final --lean-path "$T/build:$KMOD_LEAN_PATH" | tail -1
cat > src/R22KChk/Axioms.lean <<'EOF'
module
public import R22K.Final
#print axioms R22K.Final.rank_ge_23
#print axioms R22K.Final.rank_eq_23
#print axioms R22K.Final.mm_equiv
#print axioms R22K.Final.table_23
#print axioms R22K.Final.recursive_23
EOF
LEAN_PATH="$T/build:$KMOD_LEAN_PATH" nice -n $((10-$(nice))) $TC/lean -R src src/R22KChk/Axioms.lean > log/Axioms.log 2>&1 || { echo "FAIL axioms build"; head log/Axioms.log; exit 1; }
cat log/Axioms.log
n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" log/Axioms.log)
[ "$n" = 5 ] && echo "PASS #print axioms: 5 of 5 theorems use exactly [propext, Classical.choice, Quot.sound]" || { echo "FAIL #print axioms ($n of 5)"; exit 1; }
KMOD_LEAN_PATH="$(cat $F/lpath_final.txt)" python3 $K/final/kmod_audit_obl.py --root R22K.Final --build $T/build --build $F/topstore/store \
  --build "$FTOP_BUILD" --no-ext --obl-out log/final_obl.txt > log/audit.txt 2>&1; rc=$?
tail -3 log/audit.txt; [ $rc -eq 0 ] || { echo "FAIL kmod_audit"; exit 1; }
python3 $K/final/final_ext.py log/final_obl.txt --tag top --par 8 | tee log/final_ext.txt | tail -3
[ ${PIPESTATUS[0]} -eq 0 ] || { echo "FAIL external step"; exit 1; }
python3 $K/final/envmanifest.py --check | tee log/envcheck.txt | head -3; [ ${PIPESTATUS[0]} -eq 0 ] || { echo "FAIL environment changed"; exit 1; }
echo "PASS final top: R22K.Final built, manifest + audit + external step + axioms + environment"
