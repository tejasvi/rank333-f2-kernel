#!/usr/bin/env python3
"""joinemit.py P0DIR JOBS PACKAGES OUT PREFIX PAR: case-II join (the global Cov above the packages), emitted lazily like a package.

Items: every kind-4 segment of the CC phase-0 pcerts P0DIR/seg_<batch>.r3 (py/pcseg.py list), i.e. the top segment of the case-II root
(topA) and every top / split segment below it, each with its JOB children. The pcerts are hard-linked into OUT/p0/ and named relative to
the package dir (py/unitconv.py resolves them against it). Their #lab tables must equal the bundle header's (data/cc/cc436_422/hdr_ccw.r3).
Per segment: its key (py/itemkey.py after one scratch conversion: py/pcseg.py SEGID, py/kitem.py on the CC route's files, deleted at
once), mkimod's CC features, and whether its root is dead; cached in OUT/q/feat.jsonl (a rerun converts only the missing segments).
Item modules: py/emitlazy.py's grouping (largest predicted batch peak first; MAXS predicted kernel s, MAXIN converted bytes, SEGMAX
segment bytes (default 4e6), 100 items, peaks within max(25%, 0.3 GB)); stub sources OUT/src/<PREFIX>/I<j>.lean plus item lists
I<j>.items whose lines are `id seg:p0/<file>:<segid> 0 0 key dead` (py/unitconv.py converts them at unit time).
External children: the job roots, covered by the packages' tops `<pkg>.Top.cov : AllL CovOfKeyCC [their jobs' minimal keys, sorted]`
(KB.ModRekeyCC): the export map OUT/src/pkgs.exports (`minimal key <pkg>.Top.cov idx`) comes from the job tables and PACKAGES.jsonl
(py/mkpkgcc.py's line ranges) alone. JOBS may be a comma-separated list of job tables; each package line's "jobfile" (a basename)
selects its table. PACKAGES may likewise be a comma-separated list of package lists. A job's prefix holds labels (matrices); the key's root S has bit i for the label at
index i of the #lab table, last = the last label's index. Then py/mkaggf.py (AGG_EXT) writes the Cov chunks; the roots (items that are
nobody's child) must include the case-II root, root (1, 0) and lo 0 (minimal key 1). The top <PREFIX>.Top restates each root chunk over
its roots' minimal keys (#kmRekeyCC <PREFIX>.Top.cov<j>) and states #kmTop <PREFIX>.Top.segs over them: AllL SegsOfKeyCC [1] when the
case-II root is the only root. Writes OUT/join.json (counts, roots, the pcerts' sha256). Env SKIPSEG=FILE: item ids (`<batch>_<segid>`) left out, i.e. fat segments
re-cut into smaller ones whose pcerts (runs/p0r: seg_r1_<id>.r3, seg_r2_<id>.r3) are in P0DIR."""
import sys, os, json, subprocess, threading, hashlib
from concurrent.futures import ThreadPoolExecutor
sys.set_int_max_str_digits(0)
R22 = os.environ.get('KINDS_R22', '.')
sys.path.insert(0, R22 + '/lean/native/infra/lib/py')
import segkey
K = R22 + '/lean/kinds'; C = K + '/data/cc/cc436_422'
p0, jobs_f, pk_f, out, pfx, par = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], int(sys.argv[6])
SKIP = set(x.strip() for x in open(os.environ['SKIPSEG']) if x.strip()) if os.environ.get('SKIPSEG') else set()   # re-cut segments (runs/p0r)
MAXS = float(os.environ.get('MAXS', '60')); MAXIN = float(os.environ.get('MAXIN', '30e6')); SEGMAX = float(os.environ.get('SEGMAX', '4e6'))
out = os.path.abspath(out)
os.makedirs(out + '/src/' + pfx, exist_ok=True); os.makedirs(out + '/q/feat', exist_ok=True); os.makedirs(out + '/p0', exist_ok=True)
_argv = sys.argv; sys.argv = ['x', out + '/q/mkimod_ns', 'X', 'cc436_422']; MK = {'__name__': 'mkimod_ns'}
exec(open(K + '/py/mkimod.py').read().split("L = ['module'")[0], MK)
sys.argv = _argv
def hdrlab(f):
    with open(f, 'rb') as h:
        for ln in h:
            if ln.startswith(b'#lab '): a = ln.split(); return [int(x) for x in a[2:2 + int(a[1])]]
            if ln.startswith(b'#end'): break
    sys.exit('joinemit: no #lab line in %s' % f)
LAB = hdrlab(C + '/hdr_ccw.r3'); LIX = {v: i for i, v in enumerate(LAB)}
for f in ('recipecheck.txt', 'check.txt', 'SHA256SUMS.txt', 'batches.tsv'):   # phase 0's own records go with the pcerts
    if os.path.exists(os.path.join(p0, f)): subprocess.run(['cp', '-p', os.path.join(p0, f), os.path.join(out, 'p0', f)], check=True)
segs = []; pcerts = {}
for f in sorted(x for x in os.listdir(p0) if x.startswith('seg_') and x.endswith('.r3')):
    path = os.path.join(p0, f); dst = os.path.join(out, 'p0', f)
    if not os.path.exists(dst):
        try: os.link(path, dst)
        except OSError: subprocess.run(['cp', path, dst], check=True)
    if os.path.getsize(dst) != os.path.getsize(path): sys.exit('joinemit: %s differs from %s' % (dst, path))
    if hdrlab(dst) != LAB: sys.exit('joinemit: the #lab table of %s differs from hdr_ccw.r3' % f)
    pcerts[f] = dst
    for ln in subprocess.run([sys.executable, K + '/py/pcseg.py', dst, 'list'], capture_output=True, text=True, check=True).stdout.split('\n'):
        a = ln.split()
        if len(a) > 8 and a[3] == 'kind' and a[4] == '4' and '%s_%s' % (f[4:-3], a[0]) not in SKIP:
            segs.append(dict(id='%s_%s' % (f[4:-3], a[0]), file='p0/' + f, sid=a[0], len=int(a[8])))
FF = out + '/q/feat.jsonl'; cache = {}
if os.path.exists(FF):
    for l in open(FF):
        try: x = json.loads(l)
        except ValueError: continue   # a torn last line
        cache[x['id']] = x
lock = threading.Lock(); ff = open(FF, 'a')
def feat(it):
    if it['id'] in cache and cache[it['id']]['file'] == it['file'] and cache[it['id']]['sid'] == it['sid']:
        x = cache[it['id']]; it.update(key=int(x['key']), dead=x['dead'], ks=x['ks'], pk=x['pk'], nrec=x['nrec'], inb=x['inb']); return it
    d = '%s/q/feat/%s.d' % (out, it['id']); t = d[:-2] + '.txt'
    env = dict(os.environ, KI_MEMB='1.2', KI_PERMISSIVE='1', PCSEG_HDR=C + '/hdr_ccw.r3')   # as py/unitconv.py
    with open(t, 'w') as o: subprocess.run([sys.executable, K + '/py/pcseg.py', os.path.join(out, it['file']), it['sid']], stdout=o, check=True, env=env)
    r = subprocess.run([sys.executable, K + '/py/kitem.py', t, C + '/kept_cc436_422.txt', C + '/cc436_422.c2t', C + '/kept_rt.bin', d, '20'],
                       capture_output=True, text=True, env=env)
    if not os.path.exists(d + '/table_0.bin') and not os.path.exists(d + '/dead.bin'):
        raise SystemExit('joinemit: %s does not convert: %s' % (it['id'], (r.stdout + r.stderr).strip().split('\n')[-1][:200]))
    subprocess.run([sys.executable, K + '/py/itemkey.py', t, d], check=True, env=env)
    it['key'] = int(open(d + '/key.txt').read().split()[0]); it['dead'] = os.path.exists(d + '/dead.bin')
    inb = sum(os.path.getsize(os.path.join(d, x)) for x in os.listdir(d) if x.endswith('.bin'))
    if it['dead']: it.update(ks=0.05, pk=0.0, nrec=1, inb=inb)
    else:
        h = MK['items'](open(d + '/head.bin', 'rb').read()); nb = h[3 + h[3] + 1 + 6]; ks = 0.0; pk = 0.0; n = 0
        for k in range(nb):
            bs = 0.0
            for a in MK['recfeats'](os.path.join(d, 'b%04d.bin' % k)):
                n += 1
                if a is None: ks += 0.1; continue
                ks += MK['kms'](a) / 1000.0; bs += MK['inc'](a)
            pk = max(pk, bs)
        it.update(ks=ks, pk=pk, nrec=n, inb=inb)
    subprocess.run(['rm', '-rf', d, t])
    with lock:
        ff.write(json.dumps(dict(id=it['id'], file=it['file'], sid=it['sid'], key=str(it['key']), dead=it['dead'], ks=it['ks'], pk=it['pk'],
                                 nrec=it['nrec'], inb=it['inb'])) + '\n'); ff.flush()
    return it
with ThreadPoolExecutor(par) as ex: segs = list(ex.map(feat, segs))
ff.close()
# the packages' exports: per package its jobs' minimal keys, sorted (KB.ModRekeyCC)
JT = {os.path.basename(f): [l.split() for l in open(f) if l.strip()] for f in jobs_f.split(',')}
def mkey(pre):
    ix = [LIX[v] for v in pre]
    return segkey.encode((sum(1 << i for i in ix), ix[-1]), 0, [], [])
njobs = 0; npk = 0
with open(out + '/src/pkgs.exports', 'w') as f:
    for l in (ln for f in pk_f.split(',') for ln in open(f) if ln.strip()):
        x = json.loads(l); a, b = x['lines']; pk = x['id'].split('.', 1)[1]; npk += 1; J = JT[x['jobfile']]
        ks = sorted(mkey([int(v) for v in J[i - 1][4:]]) for i in range(a, b + 1))
        for i, k in enumerate(ks): f.write('%d %s.Top.cov %d\n' % (k, pk, i))
        njobs += len(ks)
# the roots: items that are nobody's child (the case-II root must be one)
iface = {}; child = set()
for it in segs:
    dk = segkey.decode(it['key']); iface[(dk['root'], dk['lo'])] = it['id']
    child.update((e, 0) for e in dk['ext']); child.update(tuple(r) for r in dk['rng'])
roots = sorted(i for i in iface if i not in child)
CASE2 = ((1, 0), 0)
if CASE2 not in roots: sys.exit('joinemit: the case-II root (S 1, last 0, lo 0) is not a root of the join; roots: %s' % roots[:10])
# item modules: emitlazy's grouping on the features
srt = sorted(segs, key=lambda x: (-x['pk'], -x['ks'])); groups = []; cur = []; t = 0.0; ib = 0; cs = 0
for it in srt:
    if it['ks'] > MAXS or it['inb'] > MAXIN or it['len'] > SEGMAX: groups.append([it]); continue
    if cur and (len(cur) >= 100 or t + it['ks'] > MAXS or ib + it['inb'] > MAXIN or cs + it['len'] > SEGMAX or
                cur[0]['pk'] - it['pk'] > max(0.25 * cur[0]['pk'], 0.3)):
        groups.append(cur); cur = []; t = 0.0; ib = 0; cs = 0
    cur.append(it); t += it['ks']; ib += it['inb']; cs += it['len']
if cur: groups.append(cur)
H = ['module', 'meta import KMod.Units', 'meta import KMod.Audit', 'public import KB.CC_cc436_422_F', 'import KDK.ItemR2',
     'meta import KB.ModItemCC_cc436_422', 'set_option Elab.async false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
     'set_option exponentiation.threshold 100000000']
mods = []
if os.path.exists(out + '/src/manifest.tsv'): os.remove(out + '/src/manifest.tsv')
man = open(out + '/src/manifest.tsv', 'a')
for j, g in enumerate(groups):
    m = '%s.I%d' % (pfx, j); mods.append(m); L = list(H); names = []
    for k, it in enumerate(g):
        names.append('I%d' % k); L.append('#km%s I%d "data/q/%s.d" %d' % ('Dead' if it['dead'] else 'Head', k, it['id'], it['key']))
    L += ['#kmKeys %s.keysOK %s' % (m, ' '.join(names)), '#kax %s.keysOK' % m]
    open('%s/src/%s/I%d.lean' % (out, pfx, j), 'w').write('-- stub (py/joinemit.py): py/unitconv.py writes the real source before the build\n' + '\n'.join(L) + '\n')
    open('%s/src/%s/I%d.items' % (out, pfx, j), 'w').write(''.join('%s seg:%s:%s 0 0 %d %d\n' % (it['id'], it['file'], it['sid'], it['key'], it['dead']) for it in g))
    recs = sum(it['nrec'] for it in g); ks = sum(it['ks'] for it in g); inb = sum(it['inb'] for it in g)
    pk = 1.2 + max(it['pk'] for it in g) + 35.0 * inb / 1e9
    ps = max(8.0, 11.8 + 0.586 * ks + 1.433 * recs / 1000 + 2773.0 * inb / 1e9 - 47.0 * len(g) / 100) + 0.016 * recs; pg = max(2.1, pk)
    man.write('%s\titems\t%d\t%d\t%.2f\t%.2f\t%d\t%s\n' % (m, len(g), recs, ps, pg, 0, 'KMod.Units,KMod.Audit,KB.CC_cc436_422_F,KDK.ItemR2,KB.ModItemCC_cc436_422'))
man.close()
env = dict(os.environ, AGG_EXT=out + '/src/pkgs.exports', SPECROOT='src')
agg = subprocess.run([sys.executable, K + '/py/mkaggf.py', out + '/src', pfx, 'cc436_422', '100'] + mods, capture_output=True, text=True, env=env)
if agg.returncode: sys.exit('joinemit: mkaggf failed: ' + agg.stderr[-3000:])
# the top: each root chunk restated over its roots' minimal keys, then #kmTop over the restatements
T = '%s.Top' % pfx; tl = open('%s/src/%s/Top.lean' % (out, pfx)).read().split('\n')
kt = [l for l in tl if l.startswith('#kmTop ')]
if len(kt) != 1: sys.exit('joinemit: unexpected top from mkaggf')
rch = [a[:-len('.cov')] for a in kt[0].split()[2:]]
open('%s/src/%s/Top.lean' % (out, pfx), 'w').write('\n'.join(
    ['module', 'meta import KMod.Units', 'meta import KMod.Audit', 'public import KB.AggCC_cc436_422', 'meta import KB.ModAggCC_cc436_422',
     'meta import KB.ModRekeyCC'] + ['import %s' % a for a in rch] +
    ['set_option Elab.async false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option exponentiation.threshold 100000000',
     'run_cmd Lean.modifyEnv (Lean.LibrarySuggestions.typePrefixDenyListExt.addEntry · `R22N.AllL)',
     '/-! the case-II join\'s top (py/joinemit.py): the root chunks restated over their roots\' minimal keys (root, lo), then the segments -/'] +
    ['#kmRekeyCC %s.cov%d %s.cov' % (T, j, a) for j, a in enumerate(rch)] +
    ['#kmTop %s.segs %s' % (T, ' '.join('%s.cov%d' % (T, j) for j in range(len(rch))))] +
    ['#kax %s.cov%d' % (T, j) for j in range(len(rch))] +   # every KPUB needs its clean KAXSUM (kmod_build's manifest rule)
    ['#kax %s.segs' % T, '#kaxp %s.segs' % T]) + '\n')
open('%s/src/%s_waves.txt' % (out, pfx), 'w').write(' '.join(mods) + '\n' + agg.stdout)
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''): h.update(b)
    return h.hexdigest()
minroots = sorted(segkey.encode(r, lo, [], []) for r, lo in roots)
info = dict(prefix=pfx, segments=len(segs), dead=sum(1 for s in segs if s['dead']), records=sum(s['nrec'] for s in segs), item_modules=len(mods),
            packages=npk, jobs=njobs, roots=[str(k) for k in minroots], root_chunks=rch, segbytes=sum(s['len'] for s in segs),
            pcerts={f: sha(p) for f, p in sorted(pcerts.items())}, mkaggf=agg.stderr.strip().split('\n')[-1])
json.dump(info, open(out + '/join.json', 'w'), indent=1)
print('joinemit: %d segments (%d dead roots, %d records) in %d item modules; %d roots (minimal keys %s); %d packages, %d jobs; %s' % (
    len(segs), info['dead'], info['records'], len(mods), len(roots), ' '.join(info['roots'][:5]), npk, njobs, info['mkaggf']))
