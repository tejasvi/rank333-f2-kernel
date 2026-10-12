#!/bin/bash
# regen_ext.sh VERSION CAP LEAVES OUT: regenerate one EXT package (module sources, manifest.jsonl, DONE) with the tools version
# that produced it (column tools of package_tools.tsv.zst).
#   VERSION  v1 v2 v3 v5 v6 v7 v8 v9 v10 v12
#   CAP      436, 422 or h<c>
#   LEAVES   the package's leaf argument: '@gs:<object>:<sha256>:<a>:<b>' (lines a..b-1 of a leaf-list object; the objects are
#            inputs/ext/extleaves/<object>.zst, decompressed into $EXT_LEAVES), or '@<file>' (inline leaves, inputs/ext/inline_leaves.tsv.zst)
# Packages whose row has env EXTPKG_NOSPLIT=1 must be run with that variable set. Needs bin/ from build.sh.
set -e
H="$(cd "$(dirname "$0")" && pwd)"; V=$1; CAP=$2; L=$3; OUT=$4
[ -n "$OUT" ] || { echo "usage: regen_ext.sh VERSION CAP LEAVES OUT"; exit 2; }
T=$(mktemp -d)
if [ "$V" = v12 ]; then cp "$H"/scripts/extpkg.py "$H"/scripts/gensplit.py "$H"/scripts/mkndprod.py "$T"/; else cp "$H"/versions/"$V"/*.py "$T"/; fi
cp "$H"/bin/gen7pc "$T"/
case $V in v1|v2|v3) ;; *) cp "$H"/bin/gen7pc_eqf "$H"/bin/gen7pd "$T"/;; esac
case $V in v9|v10) cp "$H"/bin/gen7pd_eqf_v9 "$T"/gen7pd_eqf;; v12) cp "$H"/bin/gen7pd_eqf "$T"/gen7pd_eqf;; esac
cp -r "$H"/../../inputs/ext/ip "$T"/ip
PLANE_TOOLS="$T" python3 "$T"/extpkg.py "$CAP" "$L" "$OUT"
rm -rf "$T"
