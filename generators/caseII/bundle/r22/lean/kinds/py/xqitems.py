#!/usr/bin/env python3
"""xqitems.py PLAN OUTDIR [PAR]: the items of a prof7R3q queue run (xqaudit.py --plan PLAN) as kernel items on the CC route's table
cc436_422.

For every plan line `I id parent kind ... seg=HOST:FILE:OFF:LEN:SHA`:
- `r3qglue --itembin FILE OFF LEN` writes the item's verified block, and py/pcseg.py turns it into OUTDIR/<id>.txt. pcseg takes the
  header lines of the recipe's pcert header (env XQ_HDR, default data/cc/cc436_422/hdr_published.r3 for FLAGS_CC; hdr_ccn.r3
  for FLAGS_CCN, with #xpvar and #pcwit) and writes a range item's root as
  NODE + OPEN of S. `r3qglue --itemtext` has the same records, but without that NODE/OPEN, which kitem.py needs;
- `r3qglue --itemkey` writes OUTDIR/<id>.qkey: the queue's interface, i.e. root labels and lo, ext prefixes, rng nodes and starts;
- py/kitem.py (CC data files, KI_MEMB batch budget, default 1.2 GB) and py/itemkey.py write the item dir OUTDIR/<id>.d with key.txt.
It then compares every item key (segkey decode) with the queue's interface: root (S, last), lo, ext in order, and rng in order.
PAR conversions run at once (default 8). Absolute nice 10 for the children.
Prints per-kind counts, conversion failures and key mismatches."""
import sys, os, subprocess, collections
from concurrent.futures import ThreadPoolExecutor
sys.set_int_max_str_digits(0)
R22 = os.environ.get('KINDS_R22', '.')   # env KINDS_R22: a relocated tree (emitter bundle on a build machine)
sys.path.insert(0, R22 + '/lean/native/infra/lib/py')
import segkey
K = R22 + '/lean/kinds'; C = K + '/data/cc/cc436_422'
# env XQ_ORD=321 (with XQ_LO / XQ_HI): a cases (I) / (I13) run under --rord 321 (kitem.py KI_ORD=321; the C3eD kept rows, the 321
# c2t, RT's kept entries); XQ_HDR must then be the run's pcert header (with #pcwit)
ORD321 = os.environ.get('XQ_ORD') == '321'
LR = R22 + '/lean'
ROWS, C2T, RTB = ((('/dev/shm/r22/kept_C3eDc4d.txt', LR + '/rerun/r3/rt321/C3eD_321.c2t', LR + '/leaf2/rt/kept3eD.bin')) if ORD321 else
                  (C + '/kept_cc436_422.txt', C + '/cc436_422.c2t', C + '/kept_rt.bin'))
GLUE = R22 + '/xq/r3q/bin/r3qglue'
PY = os.environ.get('KPY', 'python3')   # env KPY: the Python with numpy for kitem.py
plan, out = sys.argv[1], sys.argv[2]; par = int(sys.argv[3]) if len(sys.argv) > 3 else 8
NI = str(max(0, 10 - os.nice(0)))
os.makedirs(out, exist_ok=True)
items = []
for ln in open(plan):
    a = ln.split()
    if not a or a[0] != 'I': continue
    seg = [x for x in a if x.startswith('seg=')][0][4:].split(':')
    items.append((a[1], a[3], seg[1], seg[2], seg[3]))
def conv(it):
    iid, kind, f, off, n = it
    t = os.path.join(out, iid + '.txt'); d = os.path.join(out, iid + '.d')
    b = os.path.join(out, iid + '.bin')
    r = subprocess.run(['nice', '-n', NI, GLUE, '--itembin', f, off, n, b], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if r.returncode: return (iid, kind, 'itembin: ' + r.stderr.strip()[:120])
    with open(t, 'w') as o:
        r = subprocess.run([PY, K + '/py/pcseg.py', b, '0'], stdout=o, stderr=subprocess.PIPE, text=True,
                           env=dict(os.environ, PCSEG_HDR=os.environ.get('XQ_HDR', C + '/hdr_published.r3')))
    if r.returncode: return (iid, kind, 'pcseg: ' + r.stderr.strip()[:120])
    os.remove(b)
    with open(os.path.join(out, iid + '.qkey'), 'w') as o:
        subprocess.run([GLUE, '--itemkey', f, off, n], stdout=o, check=True)
    env = dict(os.environ, KI_MEMB=os.environ.get('KI_MEMB', '1.2'), KI_PERMISSIVE='1')
    if ORD321: env.update(KI_ORD='321', KI_LO=os.environ['XQ_LO'], KI_HI=os.environ['XQ_HI'])
    subprocess.run(['rm', '-rf', d])
    with open(d + '.conv.log', 'w') as o:
        subprocess.run(['nice', '-n', NI, PY, K + '/py/kitem.py', t, ROWS, C2T, RTB, d, '20'],
                       stdout=o, stderr=subprocess.STDOUT, env=env)
    if not os.path.exists(d + '/table_0.bin') and not os.path.exists(d + '/dead.bin'):
        return (iid, kind, 'kitem: ' + open(d + '.conv.log').read().strip().split('\n')[-1][:120])
    subprocess.run([PY, K + '/py/itemkey.py', t, d], check=True)
    return (iid, kind, None)
with ThreadPoolExecutor(par) as ex: res = list(ex.map(conv, items))
bad = [r for r in res if r[2]]
cnt = collections.Counter(r[1] for r in res)
print('items %d %s; conversion failures %d' % (len(res), dict(cnt), len(bad)))
for r in bad[:10]: print('  FAIL', r)
# keys against the queue's interface
mism = 0
for iid, kind, err in res:
    if err: continue
    d = segkey.decode(int(open(os.path.join(out, iid + '.d', 'key.txt')).read().split()[0]))
    q = {'ext': [], 'rng': []}
    for ln in open(os.path.join(out, iid + '.qkey')):
        a = ln.split()
        if not a: continue
        if a[0] == 'root': labs = [int(x) for x in a[1:a.index('lo')]]; q['root'] = (sum(1 << l for l in labs), labs[-1]); q['lo'] = int(a[a.index('lo') + 1])
        elif a[0] == 'ext': labs = [int(x) for x in a[1:]]; q['ext'].append((sum(1 << l for l in labs), labs[-1]))
        elif a[0] == 'rng': labs = [int(x) for x in a[1:-1]]; q['rng'].append(((sum(1 << l for l in labs), labs[-1]), int(a[-1])))
    ok = d['root'] == q['root'] and d['lo'] == q['lo'] and d['ext'] == q['ext'] and [tuple(x) for x in d['rng']] == q['rng']
    if not ok:
        mism += 1
        if mism <= 5: print('  KEY MISMATCH item', iid, kind, 'kinds', (d['root'][1], d['lo'], len(d['ext']), len(d['rng'])), 'queue', (q['root'][1], q['lo'], len(q['ext']), len(q['rng'])))
print('key mismatches %d of %d' % (mism, len(res) - len(bad)))
nr = sum(1 for iid, kind, err in res if not err and segkey.decode(int(open(os.path.join(out, iid + '.d', 'key.txt')).read().split()[0]))['rng'])
nl = sum(1 for iid, kind, err in res if not err and segkey.decode(int(open(os.path.join(out, iid + '.d', 'key.txt')).read().split()[0]))['lo'] > 0)
print('items with range children %d, range items (lo > 0) %d' % (nr, nl))
