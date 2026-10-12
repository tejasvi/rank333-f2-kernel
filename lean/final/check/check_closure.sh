#!/bin/bash
# check_closure.sh: load R22K.Final from the archived public .olean files, without building anything, and print the statement of
# R22K.Final.rank_ge_23 with its definitions, the axioms of the five public theorems, and the numbers of imported modules and
# constants (Check.lean; expected output Check.out).
#
# Environment:
#   LEAN     the Lean v4.30.0 `lean` binary (it finds its own core library)
#   MATHLIB  a Lake workspace with Mathlib v4.30.0 built or fetched (`lake exe cache get`), such as a Mathlib checkout
#            (lean/TOOLCHAIN.md): it supplies the .olean and .ir files of Mathlib and its dependencies
#   ZENODO   the directory holding r22k_oleans_ours.tar.zst and r22k_oleans_port_ir.tar.zst
#
# The two archives hold the public .olean files of the other 6,416 modules of the import closure (this project's 1,043 and the frozen
# port's 5,373) and the 406 .ir files that the loader reads for them. Each file is checked against the archive's manifest. Loading
# takes a few seconds and about 7 GB of memory.
set -eu
cd "$(dirname "$0")"
rm -rf lib; mkdir lib
tar --zstd -xf "$ZENODO/r22k_oleans_ours.tar.zst" -C lib
tar --zstd -xf "$ZENODO/r22k_oleans_port_ir.tar.zst" -C lib
(cd lib && awk -F'\t' 'NR>2 {m=$1; gsub(/\./, "/", m); print $3 "  " m ".olean"}' MANIFEST_r22k_oleans_ours.tsv | sha256sum -c --quiet)
(cd lib && awk -F'\t' 'NR>2 {m=$1; gsub(/\./, "/", m); print $4 "  " m "." $2}' MANIFEST_r22k_oleans_port_ir.tsv | sha256sum -c --quiet)
echo "archive members match their manifests"
LP="$PWD/lib"
for d in "$MATHLIB/.lake/build/lib/lean" "$MATHLIB"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
LEAN_PATH="$LP" "$LEAN" Check.lean | tee Check.log
n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" Check.log || true)
[ "$n" = 5 ] || { echo "FAIL #print axioms ($n of 5)"; exit 1; }
echo "PASS: 5 of 5 theorems use exactly [propext, Classical.choice, Quot.sound]"
