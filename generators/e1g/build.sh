#!/bin/bash
# build.sh [OUTDIR]: the two emitter binaries from cpp/, as used in production:
#   OUTDIR/bin/lineenum9qe_ld5   the enumeration and certificate emitter (lineenum9qe.cc + packlp_avx.h, e1pleaf.h, e1pemit.h, gen7.h)
#   OUTDIR/bin/e1pconv           trace -> block-literal converter (e1pconv.cc + e1pleaf.h, e1pemit.h, gen7.h)
#   OUTDIR/lib/libhighs.so.1     the HiGHS shared library of the highspy 1.15.1 wheel (lineenum9qe_ld5 finds it via $ORIGIN/../lib)
# Requirements: g++ 15.2 (C++17), an x86-64 CPU with AVX-512, zlib, and highspy 1.15.1 (pip install highspy==1.15.1).
# HIGHSPY_LIB: the directory holding libhighs.so.1 (default: the installed highspy package's directory).
# The production binaries (BINARIES.sha256) were built with exactly these commands; -march=native makes the bytes depend on the
# build CPU, so a build on another CPU model gives different, functionally equivalent binaries.
set -e
D=$(cd "$(dirname "$0")" && pwd); O=${1:-$D/build}; mkdir -p "$O/bin" "$O/lib"
HP=${HIGHSPY_LIB:-$(python3 -c 'import highspy, os; print(os.path.dirname(highspy.__file__))')}
cp "$HP/libhighs.so.1" "$O/lib/"
cd "$D/cpp"
g++ -O3 -march=native -std=c++17 -pthread -static-libstdc++ -static-libgcc -o "$O/bin/lineenum9qe_ld5" lineenum9qe.cc \
    -L"$HP" -l:libhighs.so.1 -Wl,-rpath,'$ORIGIN/../lib' -lz
g++ -O3 -march=native -std=c++17 -pthread -static-libstdc++ -static-libgcc -o "$O/bin/e1pconv" e1pconv.cc
cd "$O" && sha256sum bin/lineenum9qe_ld5 bin/e1pconv lib/libhighs.so.1
