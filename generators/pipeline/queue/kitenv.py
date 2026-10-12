#!/usr/bin/env python3
"""kitenv.py: the paths and settings every pipeline script shares, from the environment (defaults relative to the current directory).
  PB_WORK        the verification workspace (default ./pbwork)
  SCAN_DIR       verifier state: verifier.db, done_records.jsonl, done_ids.json, verifier.status (default PB_WORK/scan)
  FINAL_DIR      the final workspace: lpath_final.txt, top/ (final build), topstore/ (the public parts of every done package),
                 walk/ (external-walk batches), census/, recheck/, V5_RESULT.txt (default PB_WORK/final)
  VERIFIER_DB    default SCAN_DIR/verifier.db
  REAUDIT_FILE   offline re-audit results ("<id> mine=PASS kmod_audit=PASS ... bad=0" lines) for packages finalized before the
                 worker ran the audit itself (default PB_WORK/audit/reaudit.out; absent = none)
  GATES_FILE     the list of gate files (aggregation lines appended when their deps are done; default PB_WORK/gates.txt);
                 a relative gate path is relative to its directory, "//<namespace>/<name>" is a store object
  PB_TOOLCHAIN   the Lean toolchain's bin directory (lean, leanchecker; default: the directory of the lean on PATH)
  PB_LEAN        the lean binary (default PB_TOOLCHAIN/lean)
  PB_ROOT        a worker's root (default ./pbroot); PB_STORE_PREFIX, the worker store path recorded in the .mhash KIMP lines of
                 the packages being checked (default PB_ROOT/store/)
  PB_NOTHP       nothp.py (default: the one in queue/)"""
import os, shutil
K = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))          # the pipeline kit
QUEUE = os.path.join(K, 'queue')
WORK = os.path.abspath(os.environ.get('PB_WORK', 'pbwork'))
SCAN = os.path.abspath(os.environ.get('SCAN_DIR', os.path.join(WORK, 'scan')))
FINAL = os.path.abspath(os.environ.get('FINAL_DIR', os.path.join(WORK, 'final')))
VERIFIER_DB = os.environ.get('VERIFIER_DB', os.path.join(SCAN, 'verifier.db'))
DONE_RECORDS = os.path.join(SCAN, 'done_records.jsonl')
REAUDIT = os.environ.get('REAUDIT_FILE', os.path.join(WORK, 'audit', 'reaudit.out'))
GATES = os.environ.get('GATES_FILE', os.path.join(WORK, 'gates.txt'))
TOOLCHAIN = os.environ.get('PB_TOOLCHAIN') or os.path.dirname(shutil.which('lean') or '/usr/local/bin/lean')
LEAN = os.environ.get('PB_LEAN') or os.path.join(TOOLCHAIN, 'lean')
ROOT = os.path.abspath(os.environ.get('PB_ROOT', 'pbroot'))
STORE_PREFIX = os.environ.get('PB_STORE_PREFIX') or os.path.join(ROOT, 'store') + '/'
NOTHP = os.environ.get('PB_NOTHP', os.path.join(QUEUE, 'nothp.py'))
def reaudit_ok():
    """ids the offline re-audit passed (empty when there is no re-audit file)"""
    if not os.path.exists(REAUDIT): return set()
    return {l.split()[0] for l in open(REAUDIT) if 'mine=PASS kmod_audit=PASS' in l and ' bad=0' in l}
def gate_files():
    """the gate files listed in GATES_FILE ('#' comments), relative ones resolved against its directory"""
    if not os.path.exists(GATES): return []
    d = os.path.dirname(os.path.abspath(GATES)); out = []
    for l in open(GATES):
        f = l.split('#')[0].strip()
        if f: out.append(f if f.startswith('//') or os.path.isabs(f) else os.path.join(d, f))
    return out
