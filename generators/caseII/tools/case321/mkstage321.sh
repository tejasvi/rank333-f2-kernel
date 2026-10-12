#!/bin/bash
# mkstage321.sh PREFIX LO HI ITEMDIR MAXS FANIN: a staging dir runs/reh/stage321_<PREFIX> for a cases (I) / (I13) slice under --rord 321:
# - data/q/<id>.d: hard links of ITEMDIR's py/xqitems.py items (XQ_ORD=321, a queue run's plan);
# - src/<PREFIX>/: py/mkslice2.py with CCN 321:LO:HI run inside the staging dir (relative item dirs, SPECROOT=src), plus the dead job root
#   462 as the item module <PREFIX>.R462 (py/mkimod321.py ... root462; EXTRA_MODS).
# Then runs/reh/mkpkg2.py-style packaging (manifest, tools, closure, lpath).
# Split cases (py/splitpkg.py): env STAGE_R462=0 leaves the root 462 out (leaf packages; the join package has it); AGG_LEAF / AGG_EXT
# pass through to py/mkaggf.py. env KPY: the Python (default python3; the scripts need only the standard library).
set -e
PY=${KPY:-python3}
K=${KINDS_R22:?set KINDS_R22 to the tree root}/lean/kinds; P=$1; LO=$2; HI=$3; SRC=$(readlink -f $4); MAXS=$5; FAN=$6
S=$K/runs/reh/stage321_$P; rm -rf $S; mkdir -p $S/data/q $S/src
for d in $SRC/*.d; do [ -f $d/key.txt ] && cp -al $d $S/data/q/; done
cd $S
EM=
if [ "${STAGE_R462:-1}" = 1 ]; then $PY $K/py/mkimod321.py src $P.R462 $LO $HI root462 > /dev/null; EM=$P.R462; fi
SPECROOT=src EXTRA_MODS=$EM $PY $K/py/mkslice2.py src $P 321:$LO:$HI $MAXS $FAN $(ls -d data/q/*.d)
