#!/bin/bash
# build.sh SOURCE OUT [ARCH]: build the queue search (src/xq/r3q/prof7R3q.cc, i.e. prof7R3q_b14; or src_b12/prof7R3q.cc, i.e.
# prof7R3q_b12d, whose own xq_r3.h and r3rec.h sit next to it and are found first), the phase-0 search (src/rerun/r3/prof7R3_b14.cc) or the
# glue tool (src/xq/r3q/r3qglue.cc; built alone, with -lcrypto), or the v7 leaf-certificate generator (src/gen7c/gen7c.cc). The bulk-peel generator src/rerun/r3/xp2/xpeel.cc and xpeel2.cc are compiled as objects first and
# linked in. ARCH defaults to -march=native; production used "-march=x86-64-v4 -mavx512vpopcntdq -mtune=generic".
# HIGHS_LIB: directory holding libhighs.so.1 (HiGHS 1.x, e.g. the highspy wheel's package directory). The binary's RPATH is $ORIGIN,
# so libhighs.so.1 is found next to the binary (or through LD_LIBRARY_PATH).
set -e
SRC=$1; OUT=$2; ARCH=${3:--march=native}; D=$(cd "$(dirname "$0")/src" && pwd)
if [ "$(basename $SRC)" = gen7c.cc ]; then   # the v7 leaf-certificate generator (py/kitem.py): gen7c.cc with generators/e1g/cpp/gen7.h
  g++ -O3 $ARCH -std=c++17 -I$D/../../../e1g/cpp $SRC -o $OUT; echo "$OUT $(sha256sum < $OUT | cut -c1-16)"; exit 0; fi
if [ "$(basename $SRC)" = r3qglue.cc ]; then   # the glue tool: no search objects, OpenSSL's MD5
  g++ -O2 -std=c++17 -I$D/xq/r3q -I$D/rerun/r3 $SRC -o $OUT -lcrypto; echo "$OUT $(sha256sum < $OUT | cut -c1-16)"; exit 0; fi
: ${HIGHS_LIB:?set HIGHS_LIB to the directory holding libhighs.so.1}
T=$(mktemp -d)
g++ -O3 $ARCH -std=c++17 -c $D/rerun/r3/xp2/xpeel.cc -o $T/xpeel.o & g++ -O3 $ARCH -std=c++17 -I$D/rerun/r3/xp2 -c $D/rerun/r3/xp2/xpeel2.cc -o $T/xpeel2.o & wait
g++ -O3 $ARCH -std=c++17 -pthread -I$D/cpp -I$D/rerun/r3/xp2 -I$D/rerun/r3 -I$D/xq/r3q $SRC $T/xpeel.o $T/xpeel2.o -o $OUT \
  -static-libstdc++ -static-libgcc -L$HIGHS_LIB -l:libhighs.so.1 -Wl,-rpath,\$ORIGIN
rm -rf $T; echo "$OUT $(sha256sum < $OUT | cut -c1-16)"
