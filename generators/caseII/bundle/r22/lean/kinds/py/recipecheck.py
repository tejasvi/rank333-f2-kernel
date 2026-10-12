#!/usr/bin/env python3
"""recipecheck.py RECIPE LINE | --flags "OPTIONS": the kernel track's assert on a prof7R3 / prof7R3q recipe line . Exit 0
when the line is usable for kernel-checked queue items, 1 with the reasons otherwise. A launcher or emission wrapper calls it
before starting a run.

Rules:
- a run on a CC route table (`--table .../data/cc/<NAME>/tab_<NAME>.bin`) must have `--pcwit`. Without witness rows the kernel
  cannot justify the dead labels R3 hands to range items and deep pieces, and it rejects them;
- its `--lpkept` and `--pcxp` files must be the same route's (`kept_<NAME>.txt`, `<NAME>.c2t`, `kept<NAME>_lab.bin`), as
  runs/runu12cc.sh substitutes them.
Repeated options are allowed (later values win, as R3's own FLAGS_NATIVE repeats --xp2psteps)."""
import sys, re, collections
if sys.argv[1] == '--flags': toks = sys.argv[2].split()
else:
    line = [l for l in open(sys.argv[1]) if l.startswith(sys.argv[2] + ' ')]
    if len(line) != 1: sys.exit('recipecheck: line %s found %d times in %s' % (sys.argv[2], len(line), sys.argv[1]))
    toks = line[0].split()[1:]
bad = []
def arg(o, n=1):
    v = [toks[i + 1:i + 1 + n] for i, t in enumerate(toks) if t == o]
    return v
tab = arg('--table')
if len(tab) != 1: bad.append('--table appears %d times' % len(tab))
else:
    m = re.search(r'/data/cc/([^/]+)/tab_\1\.bin$', tab[0][0])
    if m:
        name = m.group(1)
        if '--pcwit' not in toks: bad.append('CC table %s without --pcwit (range items and deep pieces would carry dead labels the kernel cannot justify)' % name)
        kept = arg('--lpkept')[-1:]
        if not kept or not kept[0][0].endswith('/kept_%s.txt' % name): bad.append('--lpkept is not the route\'s kept_%s.txt' % name)
        px = arg('--pcxp', 2)[-1:]
        if not px or not px[0][0].endswith('/%s.c2t' % name) or not px[0][1].endswith('/kept%s_lab.bin' % name):
            bad.append('--pcxp is not the route\'s %s.c2t / kept%s_lab.bin' % (name, name))
if bad:
    print('recipecheck: REFUSE: ' + '; '.join(bad)); sys.exit(1)
print('recipecheck: OK')
