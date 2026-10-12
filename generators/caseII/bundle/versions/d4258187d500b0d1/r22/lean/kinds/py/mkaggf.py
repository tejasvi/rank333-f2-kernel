#!/usr/bin/env python3
"""mkaggf.py OUTDIR PREFIX CCN FANIN ITEMMOD...: the module-form Cov aggregators over item modules whose items may have external
children and ranges (KB.ModAggCC_<CCN>'s #kmAggF), and a stand-in top.

Reads each item module OUTDIR/<M>.lean (py/mkimod.py: `#kmHead|#kmDead Ij "dir" key`, `#kmKeys <M>.keysOK I0 I1 ...`), decodes every
key (R22N.Glue format), and checks the closure: every external child (e, 0) and every range (node, l) must be the interface of exactly
one listed item. This check is untrusted; the kernel re-checks every reference. The items are then ordered children first (post-order
from the roots, i.e. the items that are nobody's child). The non-root items are cut into chunks of at most FANIN items, and the roots
go into their own final chunks.

Chunk j is OUTDIR/<PREFIX>/A<j>.lean, with spec OUTDIR/<PREFIX>/A<j>.spec:
- per item, `I key <M>.keysOK idx`;
- then its children in key order: `E|R childkey L` (same chunk) or `E|R childkey T <PREFIX>.A<c>.cov idx` (exported by an earlier chunk);
- `X key` for the keys that a later chunk needs, and for the roots.
The top is OUTDIR/<PREFIX>/Top.lean: `#kmTop <PREFIX>.Top.segs` over the root chunks, so its statement covers exactly the roots.

The spec path written into the sources is SPECROOT/<PREFIX as path>/A<j>.spec (env SPECROOT, default OUTDIR).
Prints the build order, one wave per line: chunks whose imported chunks are all in earlier waves, then the top.
Appends manifest lines (kind agg / top) to OUTDIR/manifest.tsv.

Split slices (one big case cut into packages, py/splitpkg.py):
- env AGG_LEAF=1: a leaf package, i.e. complete subtrees. There is no top module: the roots must fit in one root chunk, whose
  `<A>.cov` (AllL CovOfKey.. [root keys]) is the package's public theorem. The export map OUTDIR/<PREFIX as path>.exports gets one line
  per root: `key <A>.cov idx`.
- env AGG_EXT=FILE...: children covered by other packages (their .exports lines). Such a child is written `E|R key T <A>.cov idx`
  and its module is imported. It is a dependency on another package, not a wave of this one."""
import sys, os, re
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.environ.get('KINDS_R22', '.') + '/lean/native/infra/lib/py')
import segkey
out, pfx, ccn, fan = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]); mods = sys.argv[5:]
# CCN = '321:LO:HI': cases (I) / (I13) under --rord 321 (KB.ModItem321's item modules, KB.ModAgg321's #kmAggF321 / #kmTop321)
O321 = ccn.startswith('321:')
if O321: LO321, HI321 = (int(x) for x in ccn.split(':')[1:3])
KEY462 = (1 << 462) + (1 << (8 * 64)) * 462   # the dead job root 462 (KB.ModAgg321's #kmRoot462)
specroot = os.environ.get('SPECROOT', out)
LEAF = os.environ.get('AGG_LEAF') == '1'
ext = {}              # interface -> (key, theorem, idx): children covered by other packages (env AGG_EXT)
for f in os.environ.get('AGG_EXT', '').split():
    for ln in open(f):
        a = ln.split()
        if not a: continue
        dk = segkey.decode(int(a[0])); iface = (dk['root'], dk['lo'])
        if iface in ext and ext[iface][0] != a[0]: sys.exit('mkaggf: external interface %s exported twice with different keys' % (iface,))
        ext[iface] = (a[0], a[1], int(a[2]))
items = {}            # interface -> item
for m in mods:
    txt = open(os.path.join(out, m.replace('.', '/') + '.lean')).read()
    if O321 and re.search(r'^#kmRoot462 ', txt, re.M):
        thm = re.search(r'^#kmRoot462 (\S+) ', txt, re.M).group(1)
        dk = segkey.decode(KEY462); iface = (dk['root'], dk['lo'])
        if iface in items: sys.exit('mkaggf: the root 462 covered twice')
        items[iface] = dict(key=str(KEY462), thm=thm, idx=0, mod=m, dir='root462', ext=[], rng=[])
        continue
    km = re.search(r'^#kmKeys321 (\S+) \d+ \d+ (.*)$' if O321 else r'^#kmKeys (\S+) (.*)$', txt, re.M)
    thm, names = km.group(1), km.group(2).split()
    for kind, I, d, key in re.findall(r'^#km(Head321|Head|Dead321|Dead) (I\d+) "([^"]+)" (\d+)', txt, re.M):
        k = int(key); dk = segkey.decode(k)
        iface = (dk['root'], dk['lo'])
        if iface in items: sys.exit('mkaggf: interface of %s %s covered twice' % (m, I))
        items[iface] = dict(key=key, thm=thm, idx=names.index(I), mod=m, dir=d,
                            ext=[(e, 0) for e in dk['ext']], rng=[tuple(r) for r in dk['rng']])
parents = {}
for i, it in items.items():
    for c in it['ext'] + it['rng']:
        if c in items: parents.setdefault(c, []).append(i)
        elif c not in ext: sys.exit('mkaggf: child %s of item %s (%s) is not covered' % (c, it['dir'], it['mod']))
roots = [i for i in items if i not in parents]
# post-order from the roots (iterative), children in key order
order, seen = [], set()
for r in roots:
    stack = [(r, 0)]
    while stack:
        i, j = stack.pop()
        if j == 0:
            if i in seen: continue
            seen.add(i)
        ch = [c for c in items[i]['ext'] + items[i]['rng'] if c in items]
        if j < len(ch):
            stack.append((i, j + 1))
            if ch[j] not in seen: stack.append((ch[j], 0))
        else:
            order.append(i)
if len(order) != len(items): sys.exit('mkaggf: %d items are not below any root (a cycle)' % (len(items) - len(order)))
rootset = set(roots)
if LEAF and len(roots) > fan: sys.exit('mkaggf: a leaf package needs its %d roots in one root chunk (FANIN %d)' % (len(roots), fan))
if ext and set(ext) & set(items): sys.exit('mkaggf: %d interfaces are both items here and external' % len(set(ext) & set(items)))
nonroot = [i for i in order if i not in rootset]; rootl = [i for i in order if i in rootset]
chunks = [nonroot[j:j + fan] for j in range(0, len(nonroot), fan)]
nroot0 = len(chunks)
chunks += [rootl[j:j + fan] for j in range(0, len(rootl), fan)]
cof = {i: c for c, ch in enumerate(chunks) for i in ch}
exp = []; eidx = {}
for c, ch in enumerate(chunks):
    e = [i for i in ch if i in rootset or any(cof[p] > c for p in parents[i])]
    exp.append(e)
    for j, i in enumerate(e): eidx[i] = j
H = ['set_option Elab.async false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option exponentiation.threshold 100000000']
def write(name, lines):
    p = os.path.join(out, name.replace('.', '/') + '.lean'); os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w').write('\n'.join(lines) + '\n')
man = open(os.path.join(out, 'manifest.tsv'), 'a')
names = ['%s.A%d' % (pfx, c) for c in range(len(chunks))]
deps = []
for c, ch in enumerate(chunks):
    spec = []; imods = []; iaggs = []; iext = []
    for i in ch:
        it = items[i]
        spec.append('I %s %s %d' % (it['key'], it['thm'], it['idx']))
        if it['mod'] not in imods: imods.append(it['mod'])
        for tag, lst in (('E', it['ext']), ('R', it['rng'])):
            for cc in lst:
                if cc in ext:
                    ek, et, ei = ext[cc]; spec.append('%s %s T %s %d' % (tag, ek, et, ei))
                    em = et[:-len('.cov')] if et.endswith('.cov') else sys.exit('mkaggf: external theorem %s is not a .cov' % et)
                    if em not in iext: iext.append(em)
                    continue
                ck = items[cc]['key']
                if cof[cc] == c: spec.append('%s %s L' % (tag, ck))
                else:
                    a = names[cof[cc]]; spec.append('%s %s T %s.cov %d' % (tag, ck, a, eidx[cc]))
                    if a not in iaggs: iaggs.append(a)
    spec += ['X %s' % items[i]['key'] for i in exp[c]]
    sp = os.path.join(out, pfx.replace('.', '/'), 'A%d.spec' % c); os.makedirs(os.path.dirname(sp), exist_ok=True)
    open(sp, 'w').write('\n'.join(spec) + '\n')
    spb = os.path.join(specroot, pfx.replace('.', '/'), 'A%d.spec' % c)
    hdr = (['public import KB.Agg321', 'meta import KB.ModAgg321'] if O321 else
           ['public import KB.AggCC_%s' % ccn, 'meta import KB.ModAggCC_%s' % ccn])
    cmd = ('#kmAggF321 %s.cov %d %d "%s"' % (names[c], LO321, HI321, spb)) if O321 else ('#kmAggF %s.cov "%s"' % (names[c], spb))
    write(names[c], ['module', 'meta import KMod.Units', 'meta import KMod.Audit'] + hdr + ['import %s' % m for m in imods + iaggs + iext] + H +
          ['/-! Cov aggregator %s over %d items (%d exported; py/mkaggf.py) -/' % (names[c], len(ch), len(exp[c])),
           cmd, '#kax %s.cov' % names[c]])
    deps.append(iaggs)
    man.write('%s\tagg\t%d\t0\t%.2f\t%.2f\t0\t%s\n' % (names[c], len(ch), 0.5 + 0.02 * len(ch), 0.9, ','.join(imods + iaggs + iext)))
T = '%s.Top' % pfx; tops = names[nroot0:]
if LEAF:
    assert len(tops) == 1
    with open(os.path.join(out, pfx.replace('.', '/') + '.exports'), 'w') as f:
        for i in exp[nroot0]:
            if i in rootset: f.write('%s %s.cov %d\n' % (items[i]['key'], tops[0], eidx[i]))
hdrT = (['public import KB.Agg321', 'meta import KB.ModAgg321'] if O321 else
        ['public import KB.AggCC_%s' % ccn, 'meta import KB.ModAggCC_%s' % ccn])
cmdT = ('#kmTop321 %s.segs %d %d %s' % (T, LO321, HI321, ' '.join('%s.cov' % a for a in tops))) if O321 else \
       ('#kmTop %s.segs %s' % (T, ' '.join('%s.cov' % a for a in tops)))
pubT = '%s.segs' % T
if O321 and set(rootl) >= {((1 << l, l), 0) for l in (0, 168, 462)}:
    # the three job roots of case (LO, HI): the top states R22B.Final's vI / vI13 form (KB.ModAgg321's #kmVI321)
    cmdT = '#kmVI321 %s.vI %d %d %s' % (T, LO321, HI321, ' '.join('%s.cov' % a for a in tops)); pubT = '%s.vI' % T
if not LEAF: write(T, ['module', 'meta import KMod.Units', 'meta import KMod.Audit'] + hdrT +
      ['import %s' % a for a in tops] + H + ['/-! stand-in top %s over the %d roots of %d items (py/mkaggf.py) -/' % (T, len(rootl), len(items)),
      cmdT, '#kax %s' % pubT, '#kaxp %s' % pubT])
if not LEAF: man.write('%s\ttop\t%d\t0\t%.2f\t%.2f\t0\t%s\n' % (T, len(tops), 0.3, 0.9, ','.join(tops)))
# waves: a chunk's wave is one more than the largest wave of the chunks it imports
wv = []
for c in range(len(chunks)): wv.append(1 + max([wv[names.index(a)] for a in deps[c]] or [-1]))
for w in range(max(wv) + 1): print(' '.join(names[c] for c in range(len(chunks)) if wv[c] == w))
if not LEAF: print(T)
hgt = {}
for i in order: hgt[i] = 1 + max([hgt[c] for c in items[i]['ext'] + items[i]['rng'] if c in items] or [0])
sys.stderr.write('mkaggf: %d items (%d roots, %d with children), %d chunks (%d root chunks), %d waves; item tree height %d; %d external children%s\n' % (
    len(items), len(rootl), sum(1 for i in items if items[i]['ext'] or items[i]['rng']), len(chunks), len(chunks) - nroot0, max(wv) + 1,
    max(hgt.values()), sum(1 for i in items for c in items[i]['ext'] + items[i]['rng'] if c in ext), ' (leaf: no top)' if LEAF else ''))
