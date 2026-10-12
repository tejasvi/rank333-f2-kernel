#!/usr/bin/env python3
"""mkmatchk.py [--store DIR] [--classes h454,h456,...] [--jobs N]: CHECK ONLY, the per-class import + statement check of the class
roots against R22K.FinalAll (R22K.Cap imports HCapK.C<c> for the 11 HCapK classes).

For every class h<c> whose root KC.h<c>_Class is in the top store (default: $TOPSTORE),
writes chk/src/R22KChk/MatchK_h<c>.lean (imports R22K.FinalAll, KC.h<c>_Class and, if present, NDX.h<c>.Top) and builds it
alone (absolute nice 10, -j1, THP off, 64 GiB AS; LEAN_PATH = the store, build/, then $LEAN_PATH_REST), so a clash is
isolated to its class. The file
  * imports cleanly: no constant is declared twice (Lean refuses the import otherwise; for an HCapK class this is the clash);
  * FTCHK kc<c> <- KC.h<c>.classLB (e<c> := KC.h<c>.EXT): the binder type of R22K.FinalAll.rank_ge_23_of against the class
    root's statement (EXPR-EQUAL / DEFEQ / MISMATCH, as chk/Match.lean);
  * FTCHK x<c> <- NDX.h<c>.x<c> (the class EXT top), or <- R22K.FinalAll.x_nil when KC.h<c>.EXT is `[]`, or
    "x<c> pending" when the list is not empty and the top has not landed;
  * the application `R22K.FinalAll.rank_ge_23_of (e<c> := ...) (kc<c> := ...) [(x<c> := ...)]` type-checks (#check).
Results: chk/MatchK.out (one block per class, the FTCHK lines and the build's rc) and chk/log/MatchK_h<c>.log."""
import os, sys, subprocess, re, concurrent.futures as cf
F = os.environ.get('FINAL_DIR', os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN = os.environ.get('LEAN', 'lean')                      # Lean v4.30.0
NOTHP = os.environ['NOTHP']                              # the THP-off wrapper (generators/pipeline)
def opt(n, d): return sys.argv[sys.argv.index(n) + 1] if n in sys.argv else d
store = os.path.abspath(opt('--store', os.environ.get('TOPSTORE', 'store')))
jobs = int(opt('--jobs', '2'))
avail = sorted(m.group(1) for f in os.listdir(os.path.join(store, 'KC')) for m in [re.fullmatch(r'(h\d+)_Class\.olean', f)] if m)
ALL21 = ['h420', 'h450', 'h451', 'h454', 'h455', 'h456', 'h458', 'h460', 'h463', 'h464', 'h465', 'h469', 'h470', 'h471', 'h472',
         'h473', 'h475', 'h476', 'h485', 'h487', 'h490']
want = opt('--classes', '').split(',') if '--classes' in sys.argv else ALL21
classes = [c for c in want if c in avail]
lp = ':'.join([store, os.path.join(F, 'build')] + os.environ['LEAN_PATH_REST'].split(':'))
os.makedirs(os.path.join(F, 'chk/src/R22KChk'), exist_ok=True); os.makedirs(os.path.join(F, 'chk/log'), exist_ok=True)
HEAD = '''/-- the type of binder `bn` of `R22K.FinalAll.rank_ge_23_of`, the binders in `subst` replaced (chk/Match.lean's binderTy) -/
meta def binderTy (bn : Name) (subst : List (Name × Expr)) : MetaM Expr := do
  let ci ← getConstInfo `R22K.FinalAll.rank_ge_23_of
  forallTelescope ci.type fun xs _ => do
    let decls ← xs.mapM (fun x => x.fvarId!.getDecl)
    let some i := decls.findIdx? (·.userName == bn) | throwError "no binder {bn}"
    let mut t := decls[i]!.type
    for (n, v) in subst do
      let some j := decls.findIdx? (·.userName == n) | throwError "no binder {n}"
      t := t.replaceFVar xs[j]! v
    if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then throwError "binder {bn}: type depends on binders not substituted"
    return t
meta def report (label : String) (a b : Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  let r ← if a == b then pure "EXPR-EQUAL" else do
    if (← withTransparency .all (isDefEq a b)) then pure "DEFEQ" else pure "MISMATCH"
  logInfo m!"FTCHK {label} {r}"
'''
def gen(c):
    n = c[1:]
    top = os.path.exists(os.path.join(store, 'NDX', c, 'Top.olean'))
    L = ['module', 'public import R22K.FinalAll', 'public import KC.%s_Class' % c] + (['public import NDX.%s.Top' % c] if top else []) + [
        'public meta import Lean', 'open Lean Elab Command Meta', 'set_option maxHeartbeats 0', 'set_option maxRecDepth 100000   -- as R22K.Final (mkinst.py)',
        '/-! CHECK ONLY (py/mkmatchk.py): class %s\'s root against R22K.FinalAll -/' % c, HEAD,
        'elab "#ftmatchk" : command => liftTermElabM do',
        '  let e := mkConst `KC.%s.EXT' % c,
        '  report "kc%s ← KC.%s.classLB (e%s := KC.%s.EXT)" (← binderTy `kc%s [(`e%s, e)]) (← inferType (mkConst `KC.%s.classLB))' % (n, c, n, c, n, n, c)]
    if top:
        L += ['  report "x%s ← NDX.%s.x%s (e%s := KC.%s.EXT)" (← binderTy `x%s [(`e%s, e)]) (← inferType (mkConst `NDX.%s.x%s))' % (n, c, n, n, c, n, n, c, n)]
    else:
        L += ['  let some v := (← getConstInfo `KC.%s.EXT).value? | throwError "KC.%s.EXT has no value"' % (c, c),
              '  if v.isAppOfArity ``List.nil 1 then',
              '    let t ← binderTy `x%s [(`e%s, e)]' % (n, n),
              '    let x ← mkAppOptM ``R22K.FinalAll.x_nil #[none]',
              '    let ok ← withTransparency .all (isDefEq (← inferType x) t)',
              '    logInfo m!"FTCHK x%s ← R22K.FinalAll.x_nil (KC.%s.EXT = []) {if ok then "DEFEQ" else "MISMATCH"}"' % (n, c),
              '  else',
              '    logInfo m!"FTCHK x%s pending: KC.%s.EXT is not [] and NDX.%s.Top has not landed"' % (n, c, c)]
    L += ['#ftmatchk']
    if top:
        L += ['#check (R22K.FinalAll.rank_ge_23_of (e%s := KC.%s.EXT) (kc%s := KC.%s.classLB) (x%s := NDX.%s.x%s))' % (n, c, n, c, n, c, n)]
    else:
        L += ['#check (R22K.FinalAll.rank_ge_23_of (e%s := KC.%s.EXT) (kc%s := KC.%s.classLB))' % (n, c, n, c)]
    p = os.path.join(F, 'chk/src/R22KChk/MatchK_%s.lean' % c)
    open(p, 'w').write('\n'.join(L) + '\n')
    return p, top
def run(c):
    p, top = gen(c)
    log = os.path.join(F, 'chk/log/MatchK_%s.log' % c)
    ni = max(0, 10 - os.nice(0))
    env = dict(os.environ, LEAN_PATH=lp)
    with open(log, 'w') as fo:
        r = subprocess.run(['prlimit', '--as=68719476736', sys.executable, NOTHP, 'nice', '-n', str(ni), LEAN, '-j1', p],
                           stdout=fo, stderr=subprocess.STDOUT, env=env, cwd=F)
    txt = open(log).read()
    fl = [l for l in txt.splitlines() if 'FTCHK' in l]
    err = [l for l in txt.splitlines() if 'error' in l][:3]
    chk = 'rank_ge_23_of' in txt and r.returncode == 0
    return c, r.returncode, top, fl, err, chk
out = []
with cf.ThreadPoolExecutor(jobs) as ex:
    for c, rc, top, fl, err, chk in ex.map(run, classes):
        hk = os.path.exists(os.path.join(os.environ['HCAPK_BUILD'], 'HCapK/C%s.olean' % c[1:]))
        out.append('== %s rc=%d %s top=%s application=%s' % (c, rc, 'HCapK' if hk else 'port', 'yes' if top else 'no', 'OK' if chk else 'FAIL'))
        out += ['   ' + l.strip() for l in fl] + ['   ERR ' + l.strip()[:300] for l in err]
missing = [c for c in want if c not in avail]
out.append('classes without a root in the store yet: %s' % (' '.join(missing) or '-'))
open(os.path.join(F, 'chk/MatchK.out'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
