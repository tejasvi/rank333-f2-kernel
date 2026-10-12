#!/usr/bin/env python3
"""derive_hcapk.py PORT_SRC OUT: the 183 HCapK sources from the frozen port's sources.

For every module HCap.X in need.txt, OUT/HCapK/X.lean is PORT_SRC/HCap/X.lean with
  - one comment line added at the top,
  - every import of a module in need.txt renamed HCap.Y -> HCapK.Y,
  - the absolute data path of an `#rttable` command replaced by the relative path data/<dir>/<file> (resolved from the build's
    working directory, which then holds the port's snap/data as ./data).
Declarations, their names and their namespaces are unchanged.  The added comment and the data path do not enter the build outputs:
.olean, .olean.private, .olean.server, .ilean and .ir are byte-identical to those of the production sources.
Also writes OUT/manifest.jsonl (module, source, HCapK dependencies) for build_hcapk.sh."""
import os, re, sys, json
PS, OUT = sys.argv[1], sys.argv[2]
HERE = os.path.dirname(os.path.abspath(__file__))
need = [l.strip() for l in open(os.path.join(HERE, 'need.txt')) if l.strip()]; N = set(need)
os.makedirs(os.path.join(OUT, 'HCapK'), exist_ok=True)
rows = []
for m in need:
    nm = m.split('.', 1)[1]
    t = open(os.path.join(PS, *m.split('.')) + '.lean').read()
    deps = []
    def rep(mo):
        imp = mo.group(2)
        if imp in N:
            deps.append('HCapK.' + imp.split('.', 1)[1]); return mo.group(1) + 'HCapK.' + imp.split('.', 1)[1]
        return mo.group(0)
    t = re.sub(r'^((?:public |meta )*import )(\S+)', rep, t, flags=re.M)
    t = re.sub(r'^(#rttable \S+ ")/[^"]*/snap/data/', r'\1data/', t, flags=re.M)
    t = ("-- HCapK.%s: the frozen port's HCap/%s.lean with the module renamed HCap -> HCapK (imports of the 183 HCapK modules likewise); "
         "declarations unchanged\n" % (nm, nm.replace('.', '/'))) + t
    open(os.path.join(OUT, 'HCapK', nm + '.lean'), 'w').write(t)
    rows.append({'module': 'HCapK.' + nm, 'src': 'HCapK/%s.lean' % nm, 'deps': deps})
open(os.path.join(OUT, 'manifest.jsonl'), 'w').write(''.join(json.dumps(r) + '\n' for r in rows))
print(len(rows), 'modules')
