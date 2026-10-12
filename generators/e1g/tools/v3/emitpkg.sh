#!/bin/bash
# emitpkg.sh CAP A B OUTDIR [--threads T] [--name NAME] [--seed S]: one production package (py/emitpkg.py) with this tools tree
T=$(dirname $(readlink -f $0))
exec python3 $T/py/emitpkg.py "$@" --tools $T
