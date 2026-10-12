#!/usr/bin/env python3
"""mkslice2.py OUTDIR PREFIX CCN MAXS FANIN ITEMDIR...: py/mkslice.py for items that may have external children and ranges.

Items are kitem.py dirs with key.txt. They are grouped into item modules by the models of the design notes A process's anonymous memory
ratchets to its high-water mark, and the kernel cache is per declaration, so a module's peak is its largest batch, not a sum:
- items are sorted by predicted peak, largest first; an item over MAXS predicted kernel s goes alone;
- the others fill a module up to 100 items or MAXS s, as long as each item's peak is within max(25%, 0.3 GB) of the module's first
  (largest) one, so no item holds much more memory than it needs;
- and up to MAXIN input bytes (env MAXIN, default 30 MB). A module's environment keeps every item's data until the olean is written,
  at about 35 times the binary size (the design notes: anon = 1.2 + largest batch + 35 x input GB), so 30 MB of input costs about 1 GB.
py/mkimod.py writes each module as OUTDIR/<PREFIX>/I<j>.lean. py/mkaggf.py then writes the Cov aggregators (#kmAggF, at most
FANIN items per chunk; the roots in their own final chunks) and the stand-in top over the roots.

CCN '321:LO:HI' builds a slice of case (LO, HI) under --rord 321 (py/mkimod321.py, KB.ModAgg321).
Item dirs are written into the sources as given, so pass them relative to the build's working directory to get a relocatable
slice. The spec paths come from env SPECROOT (default OUTDIR). The manifest is OUTDIR/manifest.tsv. Build waves go to
OUTDIR/<PREFIX>_waves.txt: the item modules, then mkaggf's chunk waves, then the top."""
import sys, os, subprocess
out, pfx, ccn, maxs, fan = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4]), sys.argv[5]; idirs = sys.argv[6:]
K = os.environ.get('KINDS_R22', '.') + '/lean/kinds'
sys.argv = ['x', out, 'X', ccn]
src = open(K + '/py/mkimod.py').read().split("L = ['module'")[0]
exec(src)
maxin = float(os.environ.get('MAXIN', '30e6'))
def inb(d): return sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d) if f.endswith('.bin'))
items_ = []
for d in idirs:
    if os.path.exists(d + '/dead.bin'): items_.append((d, 0.05, 0.0, 1, inb(d))); continue
    h = items(open(d + '/head.bin', 'rb').read()); nb = h[3 + h[3] + 1 + 6]
    ks = 0.0; pk = 0.0; n = 0
    for k in range(nb):
        bs = 0.0
        for a in recfeats(os.path.join(d, 'b%04d.bin' % k)):
            n += 1
            if a is None: ks += 0.1; continue
            ks += kms(a) / 1000.0; bs += inc(a)
        pk = max(pk, bs)
    items_.append((d, ks, pk, n, inb(d)))
items_.sort(key=lambda x: (-x[2], -x[1]))
groups = []; cur = []; t = 0.0; ib = 0
for it in items_:
    if it[1] > maxs or it[4] > maxin: groups.append([it]); continue
    if cur and (len(cur) >= 100 or t + it[1] > maxs or ib + it[4] > maxin or cur[0][2] - it[2] > max(0.25 * cur[0][2], 0.3)):
        groups.append(cur); cur = []; t = 0.0; ib = 0
    cur.append(it); t += it[1]; ib += it[4]
if cur: groups.append(cur)
mods = []
for j, g in enumerate(groups):
    m = '%s.I%d' % (pfx, j); mods.append(m)
    if ccn.startswith('321:'):   # cases (I) / (I13) under --rord 321: KB.ModItem321's modules (py/mkimod321.py)
        lo_, hi_ = ccn.split(':')[1:3]
        subprocess.run([sys.executable, K + '/py/mkimod321.py', out, m, lo_, hi_] + [x[0] for x in g], check=True, stdout=subprocess.DEVNULL)
    else:
        subprocess.run([sys.executable, K + '/py/mkimod.py', out, m, ccn] + [x[0] for x in g], check=True, stdout=subprocess.DEVNULL)
# env EXTRA_MODS: item modules written elsewhere (e.g. the dead root 462 of cases (I) / (I13), py/mkimod321.py ... root462), added to the
# aggregation and to the first wave
mods += [m for m in os.environ.get('EXTRA_MODS', '').split() if m]
agg = subprocess.run([sys.executable, K + '/py/mkaggf.py', out, pfx, ccn, fan] + mods, check=True, capture_output=True, text=True)
sys.stderr.write(agg.stderr)
open(os.path.join(out, pfx.replace('.', '/') + '_waves.txt'), 'w').write(' '.join(mods) + '\n' + agg.stdout)
print('items %d (records %d), item modules %d (heavy, peak > 2 GB: %d), aggregator waves %d; predicted kernel %.0f s' % (
    len(items_), sum(x[3] for x in items_), len(mods), sum(1 for g in groups if 0.42 + g[0][2] > 2.0),
    len(agg.stdout.split('\n')) - 2, sum(x[1] for x in items_)))
