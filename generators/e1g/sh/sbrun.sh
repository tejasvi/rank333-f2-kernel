#!/bin/bash
# sbrun.sh ID PKGTAR OUTDIR [GROUP_S]: split the BUILD of one emitted package into group packages (splitbuild.py).
#   ID      the emitting package's id (e.g. w1_34300.r2)
#   PKGTAR  its emitted package as a tar.zst of the emitter's OUT directory (DONE, emit.log, inputs.sha256, kext.txt,
#           manifest.jsonl, run/, src/), stored as $STORE/emitted/ID.tar.zst for the package worker
#   OUTDIR  receives pkg/ (the files splitbuild reads), plan/ID/g<w>_<i>.jsonl (the group manifests, stored as
#           $STORE/splitbuild/ID/ for the package worker) and plan/ID.lines.jsonl (the queue lines)
# The queue lines fetch with $FETCH (the package worker's copy command for the store).  GROUP_S: predicted kernel s per group
# (default 40000).
set -e
ID=$1; T=$(readlink -f "$2"); O=$3; GS=${4:-40000}
G=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$O" && cd "$O"
SHA=$(sha256sum "$T" | cut -c1-64)
RAW=$(zstd -dc "$T" | tar tvf - | awk '$6 !~ /^(\.\/)?run(\/|$)/ && $6 !~ /^(\.\/)?emit\.log$/ {s+=$3} END {printf "%.2f", s/1e9}')
rm -rf pkg && mkdir -p pkg && zstd -dc "$T" | tar xf - -C pkg --wildcards './manifest.jsonl' './DONE' './kext.txt' './inputs.sha256' './src/KJ/*'
rm -rf plan; python3 "$G/py/splitbuild.py" pkg "$ID" '$STORE/emitted/'"$ID"'.tar.zst' "$SHA" plan --manpfx '$STORE/splitbuild' --group-s "$GS" --raw-gb "$RAW"
echo "$ID: raw $RAW GB; $(wc -l < plan/$ID.lines.jsonl) packages in $O/plan/$ID.lines.jsonl"
