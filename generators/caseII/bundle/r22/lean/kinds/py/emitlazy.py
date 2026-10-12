#!/usr/bin/env python3
"""emitlazy.py OUT PREFIX PAR: the lazy part of case-II package emission (emitcc.sh), after the local queue run (OUT/q/plan.txt).

No item is converted here. For every plan item:
- its R22N.Glue key from `r3qglue --itemkey` (root, lo, external children and ranges in stream order, encoded by segkey.encode: the
  same integer py/itemkey.py writes after conversion; py/unitconv.py checks the two equal);
- whether its root is a dead node (pieces and jobs whose first O / C / L record is a C or an L: py/xqdead.py's rule; #kmDead);
- its segment (file, offset, length).
Items are cut into item modules (with EMIT_FEATURES=1, the default: py/mkslice2.py's peak-class grouping on each item's mkimod CC
features, from one scratch kitem run per item; else in plan order): an item over SEGMAX bytes of segment (default 4e6, about 13 MB
converted; about the GB-s optimum per record with the ~2.3 GB unit floor) alone, the others up to SEGMAX in total or 100 items. Each module gets a stub source OUT/src/<PREFIX>/I<j>.lean (its #kmHead / #kmDead lines with the
keys and its #kmKeys line: what py/mkaggf.py reads) and its item list OUT/src/<PREFIX>/I<j>.items (`id file off len key dead`), from
which the unit converts the items and writes the real source (py/unitconv.py, run by kmod_unit.sh). OUT/src/manifest.tsv gets one row
per module with estimates from the segment bytes (records about 35 KB of segment each; the unit's wall 10 s + 10 s per MB and peak
3.5 GB + 0.35 GB per MB, measured on the first package with the unit's conversion; mkpkgw takes them as pred_s / pred_gb). Then py/mkaggf.py (AGG_LEAF=1) writes the Cov chunks with one root chunk, and the waves go to
OUT/src/<PREFIX>_waves.txt (item modules, then the chunks)."""
import sys, os, json, subprocess, collections
from concurrent.futures import ThreadPoolExecutor
sys.set_int_max_str_digits(0)
R22 = os.environ.get('KINDS_R22', '.')
sys.path.insert(0, R22 + '/lean/native/infra/lib/py')
import segkey
GLUE = R22 + '/xq/r3q/bin/r3qglue'; K = R22 + '/lean/kinds'; C = K + '/data/cc/cc436_422'
out, pfx, par = sys.argv[1], sys.argv[2], int(sys.argv[3])
SEGMAX = float(os.environ.get('SEGMAX', '4e6'))   # about the GB-s optimum per record with the ~2.3 GB unit floor
FEAT = os.environ.get('EMIT_FEATURES', '1') == '1'   # emit-time features (default): accurate pred_gb / pred_s per unit
MAXS = float(os.environ.get('MAXS', '60')); MAXIN = float(os.environ.get('MAXIN', '30e6'))
_argv = sys.argv; sys.argv = ['x', out + '/q/mkimod_ns', 'X', 'cc436_422']; MK = {'__name__': 'mkimod_ns'}
exec(open(K + '/py/mkimod.py').read().split("L = ['module'")[0], MK)   # its items(), recfeats(), kms(), inc() in their own namespace
sys.argv = _argv
def feats(it):
    """mkimod's CC features of one item (as py/mkslice2.py): kitem once into a scratch dir, read, delete (no disk peak)"""
    d = '%s/q/feat/%s.d' % (out, it['id']); b = d[:-2] + '.bin'; t = d[:-2] + '.txt'
    os.makedirs(out + '/q/feat', exist_ok=True)
    env = dict(os.environ, KI_MEMB='1.2', KI_PERMISSIVE='1', PCSEG_HDR=C + '/hdr_ccw.r3')
    subprocess.run([GLUE, '--itembin', it['file'], it['off'], str(it['len']), b], check=True, capture_output=True)
    with open(t, 'w') as o: subprocess.run([sys.executable, K + '/py/pcseg.py', b, '0'], stdout=o, check=True, env=env)
    subprocess.run([sys.executable, K + '/py/kitem.py', t, C + '/kept_cc436_422.txt', C + '/cc436_422.c2t', C + '/kept_rt.bin', d, '20'],
                   capture_output=True, env=env)
    inb = sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d) if f.endswith('.bin')) if os.path.isdir(d) else 0
    if os.path.exists(d + '/dead.bin'): r = (0.05, 0.0, 1, inb)
    elif os.path.exists(d + '/head.bin'):
        h = MK['items'](open(d + '/head.bin', 'rb').read()); nb = h[3 + h[3] + 1 + 6]; ks = 0.0; pk = 0.0; n = 0
        for k in range(nb):
            bs = 0.0
            for a in MK['recfeats'](os.path.join(d, 'b%04d.bin' % k)):
                n += 1
                if a is None: ks += 0.1; continue
                ks += MK['kms'](a) / 1000.0; bs += MK['inc'](a)
            pk = max(pk, bs)
        r = (ks, pk, n, inb)
    else: r = None
    subprocess.run(['rm', '-rf', d, b, t])
    if r is None: raise SystemExit('emitlazy: item %s does not convert' % it['id'])
    return r
items = []
for ln in open(out + '/q/plan.txt'):
    a = ln.split()
    if not a or a[0] != 'I': continue
    seg = [x for x in a if x.startswith('seg=')][0][4:].split(':')
    items.append(dict(id=a[1], parent=a[2], kind=a[3], file=seg[1], off=seg[2], len=int(seg[3])))
def one(it):
    q = {'ext': [], 'rng': []}
    for ln in subprocess.run([GLUE, '--itemkey', it['file'], it['off'], str(it['len'])], capture_output=True, text=True, check=True).stdout.split('\n'):
        a = ln.split()
        if not a: continue
        if a[0] == 'root': labs = [int(x) for x in a[1:a.index('lo')]]; q['root'] = (sum(1 << l for l in labs), labs[-1]); q['lo'] = int(a[a.index('lo') + 1])
        elif a[0] == 'ext': labs = [int(x) for x in a[1:]]; q['ext'].append((sum(1 << l for l in labs), labs[-1]))
        elif a[0] == 'rng': labs = [int(x) for x in a[1:-1]]; q['rng'].append(((sum(1 << l for l in labs), labs[-1]), int(a[-1])))
    it['key'] = segkey.encode(q['root'], q['lo'], q['ext'], q['rng'])
    dead = False
    if it['kind'] in ('P', 'J'):
        p = subprocess.Popen([GLUE, '--itemtext', it['file'], it['off'], str(it['len'])], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
        for ln in p.stdout:
            a = ln.split()
            if not a or a[0][0] == '#' or a[0] == 'N': continue
            if a[0] == 'O': break
            if a[0] in ('C', 'L'): dead = True; break
        p.stdout.close(); p.kill(); p.wait()
    it['dead'] = dead
    if FEAT: it['ks'], it['pk'], it['nrec'], it['inb'] = feats(it)
    return it
with ThreadPoolExecutor(par) as ex: items = list(ex.map(one, items))
groups = []; cur = []; cs = 0
if FEAT:   # py/mkslice2.py's grouping: largest predicted batch peak first; MAXS s, 100 items, MAXIN bytes, SEGMAX segment bytes, peaks within max(25%, 0.3 GB)
    srt = sorted(items, key=lambda x: (-x['pk'], -x['ks'])); t = 0.0; ib = 0
    for it in srt:
        if it['ks'] > MAXS or it['inb'] > MAXIN or it['len'] > SEGMAX: groups.append([it]); continue
        if cur and (len(cur) >= 100 or t + it['ks'] > MAXS or ib + it['inb'] > MAXIN or cs + it['len'] > SEGMAX or
                    cur[0]['pk'] - it['pk'] > max(0.25 * cur[0]['pk'], 0.3)):
            groups.append(cur); cur = []; t = 0.0; ib = 0; cs = 0
        cur.append(it); t += it['ks']; ib += it['inb']; cs += it['len']
else:
    for it in items:
        if it['len'] > SEGMAX: groups.append([it]); continue
        if cur and (cs + it['len'] > SEGMAX or len(cur) >= 100): groups.append(cur); cur = []; cs = 0
        cur.append(it); cs += it['len']
if cur: groups.append(cur)
os.makedirs('%s/src/%s' % (out, pfx), exist_ok=True)
H = ['module', 'meta import KMod.Units', 'meta import KMod.Audit', 'public import KB.CC_cc436_422_F', 'import KDK.ItemR2',
     'meta import KB.ModItemCC_cc436_422', 'set_option Elab.async false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
     'set_option exponentiation.threshold 100000000']
mods = []; man = open(out + '/src/manifest.tsv', 'a')
for j, g in enumerate(groups):
    m = '%s.I%d' % (pfx, j); mods.append(m); L = list(H); names = []
    for k, it in enumerate(g):
        I = 'I%d' % k; names.append(I)
        L.append('#km%s %s "data/q/%s.d" %d' % ('Dead' if it['dead'] else 'Head', I, it['id'], it['key']))
    L += ['#kmKeys %s.keysOK %s' % (m, ' '.join(names)), '#kax %s.keysOK' % m]
    open('%s/src/%s/I%d.lean' % (out, pfx, j), 'w').write('-- stub (py/emitlazy.py): py/unitconv.py writes the real source before the build\n' + '\n'.join(L) + '\n')
    open('%s/src/%s/I%d.items' % (out, pfx, j), 'w').write(''.join('%s %s %s %d %d %d\n' % (it['id'], it['file'], it['off'], it['len'], it['key'], it['dead']) for it in g))
    # lazy units (measured on the first package, main, 12 slots: 9.3 s and at most 0.35 GB per MB of segment above a 3.5 GB base, with
    # the unit's conversion): column 5 is the unit's predicted wall s, column 6 its peak GB less mkpkgw's 0.5 margin
    sb = sum(it['len'] for it in g); mb = sb / 1e6
    if FEAT:   # mkimod's CC models; the unit's wall: runs/reh/mkpkg2.py's fit + 16 ms per record of lazy conversion
        recs = sum(it['nrec'] for it in g); ks = sum(it['ks'] for it in g); inb = sum(it['inb'] for it in g)
        pk = 1.2 + max(it['pk'] for it in g) + 35.0 * inb / 1e9
        ps = max(8.0, 11.8 + 0.586 * ks + 1.433 * recs / 1000 + 2773.0 * inb / 1e9 - 47.0 * len(g) / 100) + 0.016 * recs
        # closure kinds_v4  lowers every unit's import base by 0.25-1.04 GB: over 110 units of two test packages mkimod's
        # model + mkpkgw's 0.5 exceeded the measured RssAnon peak by 0.84-2.27 GB (median 1.35), so mkpkgw's margin is dropped here:
        # pred_gb = max(2.1, mkimod's peak) (column 6 is pred_gb less mkpkgw's 0.5)
        pg = max(1.6, pk - 0.5)
    else: recs = max(1, round(sb / 35e3)); ps = 10.0 + 10.0 * mb; pg = 3.0 + 0.35 * mb
    man.write('%s\titems\t%d\t%d\t%.2f\t%.2f\t%d\t%s\n' % (m, len(g), recs, ps, pg, 0,
              'KMod.Units,KMod.Audit,KB.CC_cc436_422_F,KDK.ItemR2,KB.ModItemCC_cc436_422'))
man.close()
env = dict(os.environ, AGG_LEAF='1', SPECROOT='src')
ids = {x['id'] for x in items}; nroots = sum(1 for it in items if it['parent'] not in ids)
agg = subprocess.run([sys.executable, K + '/py/mkaggf.py', out + '/src', pfx, 'cc436_422', str(max(400, nroots + 10))] + mods,
                     capture_output=True, text=True, env=env)
if agg.returncode: sys.exit('emitlazy: mkaggf failed: ' + agg.stderr[-2000:])
open('%s/src/%s_waves.txt' % (out, pfx), 'w').write(' '.join(mods) + '\n' + agg.stdout)
nd = sum(1 for it in items if it['dead'])
print('emitlazy: %d items (%d dead roots) in %d item modules; %s' % (len(items), nd, len(mods), agg.stderr.strip().split('\n')[-1]))
