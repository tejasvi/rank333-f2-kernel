#!/bin/bash
# mktools.sh VERSION OUTDIR [BINDIR]: assemble the tools tree of one tools version (TOOLS.md) as the production package commands
# used it (OUTDIR/emitpkg.sh CAP A B PKGDIR ...):
#   OUTDIR/py/, OUTDIR/emitpkg.sh  from tools/VERSION/
#   OUTDIR/bin/, OUTDIR/lib/       from BINDIR (a build.sh output directory, or the extracted zenodo e1g_binaries archive,
#                                  with libhighs.so.1 from the highspy 1.15.1 wheel: HIGHSPY_LIB); default: build.sh into OUTDIR
#   OUTDIR/ip/                     from ../../inputs/e1g/ip_*.tar.zst, checked against ../../inputs/e1g/IP_SHA256
# Every tools version reads the same input files (v3 reads a subset: it has no class contexts).
set -e
G=$(cd "$(dirname "$0")/.." && pwd); I=$G/../../inputs/e1g
V=$1; O=$2; BD=$3
[ -d "$G/tools/$V" ] || { echo "no tools version $V"; exit 1; }
mkdir -p "$O"; O=$(cd "$O" && pwd)
cp -r "$G/tools/$V/py" "$G/tools/$V/emitpkg.sh" "$O/"
if [ -n "$BD" ]; then
  mkdir -p "$O/bin" "$O/lib"; cp "$BD/bin/lineenum9qe_ld5" "$BD/bin/e1pconv" "$O/bin/"
  HL=$BD/lib/libhighs.so.1   # (the zenodo archive has bin/ only: libhighs.so.1 then comes from the highspy 1.15.1 wheel)
  [ -f "$HL" ] || HL=${HIGHSPY_LIB:-$(python3 -c 'import highspy, os; print(os.path.dirname(highspy.__file__))')}/libhighs.so.1
  cp "$HL" "$O/lib/"
else "$G/build.sh" "$O"; fi
for t in "$I"/ip_*.tar.zst; do zstd -dc "$t" | tar xf - -C "$O"; done
( cd "$O" && sha256sum -c --quiet "$I/IP_SHA256" ) && echo "inputs ok"
( cd "$O" && sha256sum bin/lineenum9qe_ld5 bin/e1pconv lib/libhighs.so.1 ) | diff - <(cd "$G" && grep -v '^#' BINARIES.sha256) > /dev/null \
  && echo "binaries: the production hashes" || echo "binaries: built here, hashes differ from BINARIES.sha256 (a different build CPU or compiler)"
