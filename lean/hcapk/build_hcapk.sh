#!/bin/bash
# build_hcapk.sh PORT_ROOT OUT: derive the HCapK sources from the frozen port (PORT_ROOT/src, PORT_ROOT/snap/data) and build them
# in dependency order into OUT/build, then the 45 KCH tables (sources in ./KCH, data in inputs/classes/kch_data.tar.zst).
# Environment: LEAN (default lean), LIB_PATH = the frozen port build directory followed by its library roots (Mathlib and
# dependencies, the toolchain's lib/lean), KCH_DATA = the extracted kch_data directory (default OUT/kch_data).
set -e
HERE=$(dirname "$(readlink -f "$0")"); PORT=$1; OUT=$(readlink -f -m "$2"); LEAN=${LEAN:-lean}
: "${LIB_PATH:?set LIB_PATH to the frozen port build and its library roots}"
mkdir -p "$OUT/src" "$OUT/build"
python3 "$HERE/derive_hcapk.py" "$PORT/src" "$OUT/src"
ln -sfn "$PORT/snap/data" "$OUT/src/data"
python3 - "$OUT" <<'EOF'
import json, sys
out = sys.argv[1]; rows = [json.loads(l) for l in open(out + '/src/manifest.jsonl')]
dep = {r['module']: r['deps'] for r in rows}; seen = set(); order = []
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in dep.get(m, []): visit(d)
    order.append(m)
for r in rows: visit(r['module'])
open(out + '/order.txt', 'w').write('\n'.join(order) + '\n')
EOF
export LEAN_PATH=$OUT/build:$LIB_PATH
cd "$OUT/src"
while read -r m; do
  rel=$(echo "$m" | tr . /); mkdir -p "$OUT/build/$(dirname "$rel")"
  "$LEAN" -j1 "$rel.lean" -o "$OUT/build/$rel.olean" -i "$OUT/build/$rel.ilean" > "$OUT/build/$rel.log" 2>&1 || { echo "FAILED $m"; exit 1; }
done < "$OUT/order.txt"
# KCH tables: data files under ./data relative to the working directory
mkdir -p "$OUT/kch/data"; cp "$HERE"/KCH/*.lean "$OUT/kch/" 2>/dev/null || true
KD=${KCH_DATA:-$OUT/kch_data}; cp "$KD"/*.bin "$OUT/kch/data/"
mkdir -p "$OUT/build/KCH"; cd "$OUT/kch"
for f in "$HERE"/KCH/*.lean; do
  b=$(basename "$f" .lean); mkdir -p KCH; cp "$f" KCH/
  "$LEAN" -j1 "KCH/$b.lean" -o "$OUT/build/KCH/$b.olean" -i "$OUT/build/KCH/$b.ilean" > "$OUT/build/KCH/$b.log" 2>&1 || { echo "FAILED KCH.$b"; exit 1; }
done
echo "built $(wc -l < "$OUT/order.txt") HCapK modules and $(ls "$HERE"/KCH/*.lean | wc -l) KCH tables into $OUT/build"
