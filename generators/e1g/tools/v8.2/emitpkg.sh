#!/bin/bash
# emitpkg.sh CAP A B OUTDIR [--threads T] [--name NAME] [--seed S]: one production package (py/emitpkg.py) with this tools tree
T=$(dirname $(readlink -f $0))
export PYTHONDONTWRITEBYTECODE=1   # (keeps the tree as shipped: no __pycache__ in py/)
exec python3 $T/py/emitpkg.py "$@" --tools $T
