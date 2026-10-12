#!/bin/bash
# build.sh [OUTDIR]: builds the five EXT generators from src/ and checks them against BINARIES.sha256.
# The production binaries are static x86-64-v3 builds made with g++ 15.2.0 (Ubuntu 15.2.0-16ubuntu1):
#   g++ -O2 -march=x86-64-v3 -std=c++17 -static -Isrc -o BIN SRC
# With that compiler the builds are bit-identical to the production binaries (checked below). Each generator is a single-threaded
# process with integer arithmetic only and no randomness; the parallel generation of tools v9-v12 runs several such processes
# (scripts/gensplit.py) and merges their outputs in tree order.
set -e
cd "$(dirname "$0")"
OUT=${1:-bin}
mkdir -p "$OUT"
build() { g++ -O2 -march=x86-64-v3 -std=c++17 -static -Isrc -o "$OUT/$1" "src/$2"; }
build gen7pc         gen7pc.cc          # gen7p.h, planecert.h
build gen7pc_eqf     gen7pc_eqf.cc      # gen7p_eqf.h, planecert.h
build gen7pd         gen7pd.cc          # gen7pd.h, planecert.h
build gen7pd_eqf_v9  v9/gen7pd_eqf.cc   # gen7pd_eqf.h, planecert.h (tools v9, v10); the source keeps its name, which the binary records
build gen7pd_eqf     gen7pd_eqf.cc      # gen7pd_eqf.h, planecert.h (tools v12)
SUMS="$(pwd)/BINARIES.sha256"
( cd "$OUT" && sed 's#  bin/#  #' "$SUMS" | sha256sum -c - ) || echo "binaries differ from the production builds (compiler version?)"
