#!/usr/bin/env python3
"""splitgen.py CLASS [P] [--certs-only]: G2 data for the split external leaves of the E1 route's class CLASS (303 or 321).

Everything is written under l2/ (the E1 route's layout); $E1ROOT is only read.
1. The leaves to split are the first plan['s'] lines of $E1ROOT/litsE1/c<C>x.lit.extord (C.EXT order, as E1.IP_e<C>.C.EXT).
2. Their v7 certificates and tree shapes with the E1 route's C++ generator (split/g7c.py run_c / shapes_c, P processes; batches cached
   in l2/litsE1/c<C>x.split.g7c, so a killed run resumes).
3. Leaf k: split7.parse7, split7.nest_split(tree, 6000) as split/extasm.py; files l2/split/E<C>S<k>.{bin,recs,sizes};
   Lean modules l2/L5/t/E<C>S<k>{_Data,_C<j>,} by tools/mknest.py, a copy of split/mknest.py (P workers).
4. Checks every leaf against the E1 route's plan: tree nodes and record count (plan['splits'][k]), and the chunk count line.
Prints a summary; failures are listed and the run exits non-zero."""
import sys, os, re, ast, pickle, struct, subprocess
from multiprocessing import Pool
sys.set_int_max_str_digits(0); sys.setrecursionlimit(1000000)
L2 = os.environ['E1ROOT'].rstrip('/') + '/'
G = os.path.dirname(os.path.abspath(__file__)) + '/l2/'
sys.path.insert(0, L2 + 'split'); sys.path.insert(0, L2 + 'enum')
import split7, g7c
from ipload import IP
c = int(sys.argv[1]); P = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 12
ipn = 'e%d' % c; IPU = ipn.upper(); W = L2 + 'cls/c%d/' % c
E = [int(x) for x in re.search(r'E = \[([0-9, ]+)\]', open(L2 + 'E1/IP_%s.lean' % ipn).read()).group(1).split(',')]
ip = IP(W + 'ipns', W + 'o_tighta')
VT = sum(v << (9 * l) for l, v in enumerate(ip.vecs)); R = ip.R
DOM = sum(1 << X for X in range(1, 512) if all(bin(X & e).count('1') % 2 == 0 for e in E))
plan = ast.literal_eval(open(L2 + 'litsE1/c%dx.lit.plan' % c).read())
ext = [tuple(int(x) for x in l.split(',')) for l in open(L2 + 'litsE1/c%dx.lit.extord' % c) if l.strip()]
big = ext[:plan['s']]
assert len(big) == len(plan['splits'])
if os.environ.get('G2_LIMIT'): big = big[:int(os.environ['G2_LIMIT'])]   # test runs
terms_of = lambda pl: [ip.vecs[l] for l in pl]
wdir = G + 'litsE1/c%dx.split.g7c%s' % (c, '_t' + os.environ['G2_LIMIT'] if os.environ.get('G2_LIMIT') else '')
cf, sf = wdir + '/certs.pkl', wdir + '/shapes.pkl'
if os.path.exists(cf): certs = pickle.load(open(cf, 'rb'))
else:
    certs = g7c.run_c(big, terms_of, E, P, 30000000, wdir)
    pickle.dump(certs, open(cf, 'wb'))
if os.path.exists(sf): shapes = pickle.load(open(sf, 'rb'))
else:
    shapes = g7c.shapes_c(big, terms_of, E, P, 30000000, wdir, certs)
    pickle.dump(shapes, open(sf, 'wb'))
print('class', c, 'E', E, 'split leaves', len(big), 'certificates', len(certs), 'shapes', len(shapes), flush=True)
if '--certs-only' in sys.argv: sys.exit(0)

def wlits(path, L):
    with open(path, 'wb') as f:
        f.write(struct.pack('<I', len(L)))
        for x in L:
            b = x.to_bytes(max(1, (x.bit_length() + 7) // 8), 'little'); f.write(struct.pack('<I', len(b))); f.write(b)
def lstep(st):
    t, sym, cdir, NT, SL, i = st
    return '(%d, %s, %s, [%s], [%s], %d)' % (t, 'true' if sym else 'false', 'true' if cdir else 'false',
                                            ', '.join(map(str, NT)), ', '.join(map(str, SL)), i)
def leafrec(pl, cert):
    tm = sum(((VT >> (9 * l)) & 511) << (9 * i) for i, l in enumerate(pl))
    return R | (tm << 6) | ((1 | (DOM << 2) | (cert << 514)) << (6 + 9 * R))

def one(k):
    pl = big[k]
    v, n = certs[pl]
    if pl in shapes: t, used = split7.parse7(v, shapes[pl])
    else: t, used = split7.decode7(terms_of(pl), DOM, v)
    if used != n: return (k, 'FAIL used %d != %d' % (used, n))
    nodes = split7.size(t, {})
    main, m0, recs = split7.nest_split(t, 6000)
    nm = '%sS%d' % (IPU, k)
    out = G + 'split/' + nm
    wlits(out + '.bin', [leafrec(pl, split7.enc(main).v)] + [split7.enc(q).v for _, q, _, _ in recs])
    open(out + '.recs', 'w').write('%d\n' % m0 + ''.join('[%s]|%d|%d\n' % (', '.join(lstep(st) for st in p), a, m)
                                                         for p, _, a, m in recs))
    open(out + '.sizes', 'w').write(''.join('%d\n' % split7.size(q, {}) for _, q, _, _ in recs))
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tools/mknest.py'), nm, out, '6000'], capture_output=True, text=True)
    if r.returncode != 0: return (k, 'FAIL mknest ' + r.stderr[-300:])
    pn, prec, pnodes, pline = plan['splits'][k]
    if (pn, prec, pnodes, pline) != (nm, len(recs), nodes, r.stdout.strip()):   # informational: another generator version
        return (k, 'DIFF plan %s got %s' % ((pn, prec, pnodes, pline), (nm, len(recs), nodes, r.stdout.strip())))
    return (k, 'OK %d nodes %d records' % (nodes, len(recs)))

bad, diff = [], []
with Pool(P) as pool:
    for k, msg in pool.imap_unordered(one, range(len(big)), chunksize=4):
        if msg.startswith('FAIL'): bad.append((k, msg)); print(k, msg, flush=True)
        elif msg.startswith('DIFF'): diff.append((k, msg))
print('class', c, 'split leaves', len(big), 'failed', len(bad), 'differing from the plan (informational)', len(diff), flush=True)
open(G + 'split/c%d.check' % c, 'w').write('%d leaves %d failed %d differ\n' % (len(big), len(bad), len(diff)) +
                                          ''.join('%d %s\n' % b for b in sorted(bad + diff)))
sys.exit(1 if bad else 0)
