#!/usr/bin/env python3
"""tomod.py MOD...: kinds/lean/<MOD as path>.lean -> kinds/mod/src/<path>.lean as a Lean 4.30 module, by the port's rules
(the port's README, §3): `module` first; the umbrella R22Port.U_6050cb77ad13 (Init and Lean) for a file that imports
`Lean`, else R22Port.U_d41d8cd98f00 (Init); every `import X` -> `public import X`; the body in `@[expose] public section` after the
module docstring.  Loader files (they define `elab` commands): `public meta import Lean` and `public meta import X` for each import X, every top-level `def` / `partial def`
becomes `meta` (R-c), and `addDecl (Declaration.defnDecl dv)` gets `(forceExpose := true)` (R-d).  An import line ending in `-- nometa`
stays data-only (`public import X`, no `public meta import X`): the loader's compile-time code only names that module's constants and
never runs its definitions, so a module that meta-imports the loader does not load the IR of that module's whole closure (the item
modules' import base, the design notes).  `--copy-port MOD`: the port's
own ported source (port/out/src) instead (modules rebuilt only because a dependency changed).  `--dst DIR` (default kinds/mod/src):
the output root; with it, mod/rename.py's RENAME applies to the output path and to every import line (kinds-only module names, so
that each module name maps to one file; kinds/mod2)."""
import sys, re, os, shutil
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rename import RENAME
K = os.environ.get('KINDS_R22', '.') + '/lean/kinds'
P = os.environ.get('KINDS_R22', '.') + '/lean/native/infra/port/out/src'
args = sys.argv[1:]; copy = False; droot = os.path.join(K, 'mod/src'); ren = {}
if args and args[0] == '--dst': droot = os.path.abspath(args[1]); args = args[2:]; ren = RENAME
if args and args[0] == '--copy-port': copy = True; args = args[1:]
def rimp(t): return re.sub(r'^((?:public )?(?:meta )?import )(\S+)', lambda x: x.group(1) + ren.get(x.group(2), x.group(2)), t, flags=re.M)
for m in args:
    rel = m.replace('.', '/') + '.lean'
    dst = os.path.join(droot, ren.get(m, m).replace('.', '/') + '.lean'); os.makedirs(os.path.dirname(dst), exist_ok=True)
    if copy:
        open(dst, 'w').write(rimp(open(os.path.join(P, rel)).read())); print('copied', m); continue
    src = open(os.path.join(K, 'lean', rel)).read().split('\n')
    imps = [l.split()[1] for l in src if l.startswith('import ')]
    nometa = {l.split()[1] for l in src if l.startswith('import ') and re.search(r'--\s*nometa\b', l)}
    rest = '\n'.join(l for l in src if not l.startswith('import '))
    loader = re.search(r'^elab "', rest, re.M) is not None
    umb = 'R22Port.U_6050cb77ad13' if 'Lean' in imps else 'R22Port.U_d41d8cd98f00'
    head = ['module', 'public import ' + umb] + (['public meta import Lean'] if loader else []) + ['public import ' + x for x in imps]
    if loader: head += ['public meta import ' + x for x in imps if x != 'Lean' and x not in nometa]   # R-c: compile-time code uses their definitions
    if loader:
        rest = re.sub(r'^(private )?def ', lambda mm: (mm.group(1) or '') + 'meta def ', rest, flags=re.M)
        rest = re.sub(r'^(private )?partial def ', lambda mm: (mm.group(1) or '') + 'meta partial def ', rest, flags=re.M)
        rest = rest.replace('addDecl (Declaration.defnDecl dv)', 'addDecl (Declaration.defnDecl dv) (forceExpose := true)')
    t = rest.lstrip('\n')
    if t.startswith('/-!'):
        j = t.find('-/') + 2
        t = t[:j] + '\n@[expose] public section' + t[j:]
    else:
        t = '@[expose] public section\n' + t
    open(dst, 'w').write(rimp('\n'.join(head) + '\n' + t))
    print('ported', m, '(loader)' if loader else '')
