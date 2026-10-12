#!/bin/bash
# kcagg.sh C OUT DEPS (kcagg v2): the aggregation package of hcap class h<C>, once every package
# of the class is done.  DEPS/<id>/DONE and DEPS/<id>/kext.txt for every package id of class h<C> in cut/kc_packages_{A1,A2,B}.jsonl
# (the build scheduler fetches them; their root modules are in the store).  Writes into OUT: src/KC/*.lean, src/data/*, manifest.jsonl (the
# scheduler's fields), lpath_common.txt ({STORE} first, then the roots listed in KC_LPATH_COMMON), order.txt, ext.txt and ext_pl.txt (KC.h<C>.EXT literally, one decimal per line) (the class's external
# leaves, the EXT tier's input format), internal.jsonl.  Environment: KC_TOOLS = the E1G emitter tools tree (its py/kjlib.py is the library:
# KC_KJLIB_DIR), KC_INPUTS = inputs/classes of this repository, KC_LPATH_COMMON = a file with the closure roots (LEAN_PATH form).
set -e
D=$(dirname "$(readlink -f "$0")")
C=$1; OUT=$(readlink -f -m "$2"); DEPS=$(readlink -f "$3")
: "${KC_TOOLS:?set KC_TOOLS to the E1G emitter tools tree}"
export KC_TOOLS KC_KJLIB_DIR=${KC_KJLIB_DIR:-$KC_TOOLS/py}
KC_INPUTS=${KC_INPUTS:-$D/../../../inputs/classes}
export KC_GIANTS=${KC_GIANTS:-$KC_INPUTS/giants} KC_HEAVY=${KC_HEAVY:-$KC_INPUTS/kc_heavy.jsonl} KC_EXTDIR=$OUT/ext KC_LPATH_COMMON
mkdir -p "$OUT"
exec python3 $D/py/kcagg.py "$C" "$OUT" "$DEPS" $KC_INPUTS/kc_packages_A1.jsonl $KC_INPUTS/kc_packages_A2.jsonl $KC_INPUTS/kc_packages_B.jsonl
