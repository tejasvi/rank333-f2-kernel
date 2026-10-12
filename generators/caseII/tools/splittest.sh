#!/bin/bash
# splittest.sh TESTDIR SLOTS STAGE...: build a split case's package stage dirs on the build machine as a build machine would, in the order given (the leaves,
# then the join), into ONE store TESTDIR/store, at absolute nice 10.
# - The packages carry no root/ (mkpkg2 PKG_ROOT=0): the shared closure stands in, i.e. each lpath_common.txt entry @CLOSURE_ROOT@/<orig>
#   is mapped to <orig> (the build machine's own file).
# - Each stage's manifest is rewritten as stage1_setup.sh does (absolute cwd, env LEAN_PATH = that path + store, KMOD_LEAN = the build machine's
#   toolchain), and konly/reh/sched.py builds it into the shared store, so the join's imports of the leaves' root chunks resolve there.
# - Then kmod_audit.py --root <the last stage's pub module> over the store: --no-ext, and the full audit with the external walk.
set -e
D=$(readlink -f $1); S=$2; shift 2; mkdir -p $D/store $D/logs
LEAN=lean
NI=$((10-$(nice))); [ $NI -lt 0 ] && NI=0
for st in "$@"; do
  st=$(readlink -f $st); n=$(basename $st)
  sed 's|@CLOSURE_ROOT@||g' $st/lpath_common.txt > $D/lpath.$n
  python3 - "$st" "$D" "$n" "$LEAN" << 'PY'
import json, sys
st, D, n, lean = sys.argv[1:5]; lp = open('%s/lpath.%s' % (D, n)).read().strip(); out = []
for l in open(st + '/manifest.jsonl'):
    m = json.loads(l); m['cwd'] = st; m.setdefault('env', {})['LEAN_PATH'] = lp + ':{STORE}'; m['env']['KMOD_LEAN'] = lean
    out.append(json.dumps(m))
open('%s/manifest.%s.jsonl' % (D, n), 'w').write('\n'.join(out) + '\n'); print(n, len(out), 'units')
PY
  nice -n $NI python3 ${R22:?set R22 to the tree root}/lean/konly/reh/sched.py --manifest $D/manifest.$n.jsonl --out $D/store \
    --lpath $D/lpath.$n --lean $LEAN --slots $S --mem-frac 0.10 --as-gb 64 \
    --nothp ${NOTHP:-${REPO:?set REPO to the repository root}/lean/kmod/tools/nothp.py} --results $D/results.$n.jsonl --logdir $D/logs \
    --timeline $D/timeline.$n.tsv > $D/sched.$n.out 2>&1 || { echo "sched rc=$? on $n"; exit 1; }
  tail -1 $D/sched.$n.out
done
TOP=$(python3 -c "import json; print([json.loads(l)['module'] for l in open('$st/manifest.jsonl') if 'pub' in json.loads(l)][0])")
KMOD_LEAN_PATH=$(cat $D/lpath.$n) nice -n $NI python3 ${R22:?set R22 to the tree root}/lean/leaf2/kmod/tools/kmod_audit.py \
  --root $TOP --build $D/store --no-ext > $D/audit.out 2>&1 || true
tail -2 $D/audit.out
KMOD_LEAN_PATH=$(cat $D/lpath.$n) nice -n $NI python3 ${R22:?set R22 to the tree root}/lean/leaf2/kmod/tools/kmod_audit.py \
  --root $TOP --build $D/store > $D/audit_full.out 2>&1 || true
tail -2 $D/audit_full.out
