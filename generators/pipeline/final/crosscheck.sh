#!/bin/bash
# crosscheck.sh PKGDIR...: the offline re-audit of extracted package tarball dirs: for each, the worker's walk (pkgaudit.py =
# pbworker.py's audit_package) vs the KMod library's kmod_audit.py (kmod_audit_obl.py: md5 c7594ac1 plus --obl-out, with
# KModTyChk.lean for NS.EXT obligations) with its external walk (KModExt at the private level over the closure): verdicts and
# obligation sets, one line per package ("<id> mine=PASS kmod_audit=PASS obligations=same ... ext=EXTSUM ... bad=0"), the format
# kitenv.py's REAUDIT_FILE holds.  Env: KMOD_LEAN (the lean binary), KMOD_LEAN_PATH (the closure's LEAN_PATH).
A=$(cd "$(dirname "$0")"; pwd)
: "${KMOD_LEAN:?set KMOD_LEAN to the lean binary}" "${KMOD_LEAN_PATH:?set KMOD_LEAN_PATH to the closure LEAN_PATH}"
export KMOD_LEAN KMOD_LEAN_PATH
for d in "$@"; do
  id=$(basename $d); roots=$(python3 -c "
import json
ms=[json.loads(l) for l in open('$d/manifest.jsonl') if l.strip()]
r=[m['module'] for m in ms if m.get('pub')]; print(' '.join(r))")
  python3 $A/pkgaudit.py $d/store $roots --obl-out $d/obl_mine.txt > $d/audit_mine.txt 2>&1; m=$?
  k=0; for r in $roots; do python3 $A/kmod_audit_obl.py --root $r --build $d/store --obl-out $d/obl_kmod_$r.txt > $d/audit_kmod_$r.txt 2>&1 || k=1; done
  cat $d/obl_kmod_*.txt 2>/dev/null | sort -u > $d/obl_kmod.txt
  same=$(cmp -s <(sort -u $d/obl_mine.txt) $d/obl_kmod.txt && echo same || echo DIFFER)
  shipped=$( [ -f $d/audit/obl.txt ] && (cmp -s <(sort -u $d/audit/obl.txt) <(sort -u $d/obl_mine.txt) && echo shipped=same || echo shipped=DIFFER) || echo shipped=none)
  echo "$id mine=$([ $m = 0 ] && echo PASS || echo FAIL) kmod_audit=$([ $k = 0 ] && echo PASS || echo FAIL) obligations=$same $shipped ext=$(tail -3 $d/audit_kmod_*.txt | grep -o 'EXTSUM[^;]*' | head -1) stmt=[$(cat $d/audit_kmod_*.txt | grep -o 'statement check: .*' | tr '\n' ';')]"
done
