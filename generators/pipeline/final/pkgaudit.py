#!/usr/bin/env python3
"""pkgaudit.py STORE ROOT... [--obl-out F] [--lean-path LP] [--worker PBWORKER.py]: the worker's per-package compositional audit run
offline over an extracted store.  It is the SAME code: `opath`, `STD` and `audit_package` are taken from pbworker.py (default:
queue/pbworker.py) by AST and executed here, without the worker's import side effects (queue, directories).  Rule = the KMod
library's kmod_audit.py, md5 c7594ac1 (an obligation into a KMod module N names one of N's KPUB theorems, or ends in .EXT and occurs in the
statement of one of them: KModTyChk.lean, exported level, LEAN_PATH = STORE + --lean-path or $KMOD_LEAN_PATH).
Prints PASS/FAIL, the modules reached and the external obligations; exit 1 on FAIL."""
import ast, hashlib, os, subprocess, sys, tempfile

def load_audit(worker, store, lean_path):
    src = open(worker).read(); tree = ast.parse(src)
    want = {'opath', 'audit_package', 'STD'}
    body = [n for n in tree.body if (isinstance(n, ast.FunctionDef) and n.name in want) or
            (isinstance(n, ast.Assign) and any(getattr(t, 'id', None) in want for t in n.targets))]
    assert {getattr(n, 'name', None) or n.targets[0].id for n in body} == want, 'pbworker.py lacks one of %s' % want
    work = tempfile.mkdtemp(prefix='pkgaudit_')
    lpf = os.path.join(work, 'lpath.txt'); open(lpf, 'w').write(lean_path or '')
    ns = dict(os=os, subprocess=subprocess, D={'store': os.path.abspath(store), 'work': work}, HERE=os.path.dirname(os.path.abspath(worker)),
              LEAN=os.environ.get('KMOD_LEAN') or os.environ.get('PB_LEAN') or os.path.join(os.environ.get('PB_TOOLCHAIN', ''), 'lean'),
              LPATH_FILE=lpf)
    exec(compile(ast.Module(body=body, type_ignores=[]), worker, 'exec'), ns)
    return ns['audit_package'], hashlib.md5(src.encode()).hexdigest()

if __name__ == '__main__':
    a = sys.argv[1:]
    opt = lambda n, d=None: a[a.index(n) + 1] if n in a else d
    flags = {'--obl-out', '--lean-path', '--worker'}
    pos = [x for i, x in enumerate(a) if x not in flags and (i == 0 or a[i - 1] not in flags)]
    store, roots = pos[0], pos[1:]
    worker = opt('--worker', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'queue', 'pbworker.py'))
    audit_package, wmd5 = load_audit(worker, store, opt('--lean-path', os.environ.get('KMOD_LEAN_PATH', '')))
    errs, seen, ext = audit_package(roots, opt('--lean-path', os.environ.get('KMOD_LEAN_PATH', '')) or None)
    of = opt('--obl-out')
    if of: open(of, 'w').write(''.join('%s %s\n' % x for x in sorted(ext)))
    for e in errs[:20]: print('ERROR', e)
    print('pbworker.py %s: reached %d, external obligations %d: %s' % (wmd5[:8], len(seen), len(ext), 'PASS' if not errs else 'FAIL (%d errors)' % len(errs)))
    sys.exit(0 if not errs else 1)
