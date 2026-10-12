#!/bin/bash
# kmod_build.sh MOD...: build KMod modules one by one (each: THP off, RLIMIT_AS, nice 10 absolute, /usr/bin/time), then write the
# module's manifest <build>/<path>.kman: `KMOD <module>`, the K* lines of the build log (KUNITS, KPUB, KKEY, KEXT, KAX, KAXSUM,
# KAXP), `KTIME wall=… user=… sys=… maxrss_kb=…`, `KDATA <path> <sha256>` per data file named in KUNITS lines, `KSHA <file> <sha256>`
# per output.  Then, unless KMOD_KEEP_PRIVATE=1, deletes the module's .olean.private if the manifest is clean (one KPUB, a KAXSUM
# with bad=0 and local_axioms=0, for every KPUB theorem).  Exit status: the first failing lean's status (2 = unclean manifest).
# Environment: KMOD_SRC (source root, default ./src), KMOD_OUT (build dir, default ./build), KMOD_LOG (default ./log),
# KMOD_LEAN_PATH (extra LEAN_PATH entries, prepended after KMOD_OUT), KMOD_AS (bytes, default 64 GiB), KMOD_LEAN (lean binary),
# KMOD_PLAIN=1 (library modules: build only, no manifest, keep everything).
set -u
SRC=${KMOD_SRC:-$PWD/src}; OUT=${KMOD_OUT:-$PWD/build}; LOG=${KMOD_LOG:-$PWD/log}
LEAN=${KMOD_LEAN:-lean}
AS=${KMOD_AS:-68719476736}
NOTHP=$(dirname "$(readlink -f "$0")")/nothp.py
export LEAN_PATH=$OUT${KMOD_LEAN_PATH:+:$KMOD_LEAN_PATH}
NI=$((10-$(nice))); [ $NI -lt 0 ] && NI=0
mkdir -p "$LOG"
for m in "$@"; do
  rel=$(echo $m | tr . /); f=$SRC/$rel.lean; o=$OUT/$rel; mkdir -p "$(dirname $o)"
  /usr/bin/time -f "%e %U %S %M" -o "$LOG/$m.time" prlimit --as=$AS python3 "$NOTHP" \
    nice -n $NI "$LEAN" -j1 -R "$SRC" "$f" -o "$o.olean" -i "$o.ilean" > "$LOG/$m.log" 2>&1; rc=$?
  read -r w u s r < "$LOG/$m.time" 2>/dev/null || { w=0; u=0; s=0; r=0; }
  if [ $rc -ne 0 ]; then echo "== $m rc=$rc wall=$w"; /usr/bin/grep -m8 -A4 "error" "$LOG/$m.log"; exit $rc; fi
  if [ "${KMOD_PLAIN:-0}" = 1 ]; then echo "== $m built (plain) wall=$w maxrss_kb=$r"; continue; fi
  {
    echo "KMOD $m"
    /usr/bin/grep -E '^K(UNITS|LITS|PUB|DISPATCH|KEY|EXT|AX|AXSUM|AXP) ' "$LOG/$m.log"
    echo "KTIME wall=$w user=$u sys=$s maxrss_kb=$r"
    /usr/bin/grep -E '^K(UNITS|LITS) ' "$LOG/$m.log" | sed -n 's/.* data=\([^ ]*\) .*/\1/p' | sort -u | while read -r d; do echo "KDATA $d $(sha256sum < "$d" | cut -c1-64)"; done
    for x in "$o.olean" "$o.olean.private" "$o.ir"; do [ -f "$x" ] && echo "KSHA $(basename $x) $(sha256sum < "$x" | cut -c1-64)"; done
  } > "$o.kman"
  npub=$(/usr/bin/grep -c '^KPUB ' "$o.kman"); nclean=$(/usr/bin/grep -c '^KAXSUM .* bad=0 local_axioms=0 ' "$o.kman")
  if [ "$npub" -lt 1 ] || [ "$nclean" -lt "$npub" ]; then echo "== $m UNCLEAN manifest (KPUB $npub, clean KAXSUM $nclean)"; exit 2; fi
  [ "${KMOD_KEEP_PRIVATE:-0}" = 1 ] || rm -f "$o.olean.private"
  echo "== $m ok wall=$w maxrss_kb=$r"
done
exit 0
