#!/usr/bin/env python3
"""mkndprod.py IP EXTFILE PKGDIR [--par P] [--chunk C] [--maxnodes M] [--subbits B2] [--minbits BMIN] [--partbits B1] [--sperbit S]
                [--name X]

The external leaves of a class-raise class (MODULES.md row 12a: certificates over E1P_EXTBITS, gen7 cap/ABORT) as one
sched.py package whose top module proves exactly the class root's hypothesis
    x<c> : ∀ pl ∈ [pl₁, …, plₙ], S5.NoDecomp (S5.leafT (E1G.leafRec E1G.IP_<IP>.R E1G.IP_<IP>.VT E1G.IP_<IP>.DOM pl 0))
             (S5.leafN (E1G.leafRec …)) (S6.leafDom6 (E1G.leafRec …))
over the literal list of EXTFILE's prefixes, in file order (the class route's `KC.<IP>.EXT` is the same literal, so
`KC.<IP>.classLB hrr hcert x<c>` typechecks by unfolding; no import of KC.*).

IP: a class of the port's HCap tree (HCap/IP_<IP>.lean, namespace E1G.IP_<IP>; R, VT, DOM read
from it). EXTFILE: one leaf per line, "<key> <l1,...,lR> <flag> <pl>" (pl = Σ l_i 2^(7i) is checked).
Per leaf (P at a time, absolute nice 10): gen7pc --split3 1 1 --splitB B2 BMIN B1 without --plane (plain v7 search: no SAT
leaf; a decomposition prints SAT) on "terms M:<DOM>" -> PKGDIR/gen/<ID>.txt. Sibling-range records of at most B2 bits
(default 24,000; a0-a2: 1.3-2.1 GB at 24-40 kbit), parts of at most B1 bits (default 3,000,000). A leaf whose generator output is
not a MAIN record (SAT, BIG, ENC) is listed in PKGDIR/failed.tsv and stops the top (the statement needs every leaf).
Modules (S4.SplitRN / S4.PLDrvRN, KMod: one KPUB + #kax each, except the data-only headers):
  src/data/<IP>_e<ID>.pln          HDRN <record hex>, then the PART/SUB lines
  src/NDL/<IP>/e<ID>/H.lean         #plhdr3n (exposed R and items)
  src/NDL/<IP>/e<ID>/P<j>.lean      #plpart3n: `ok : PL.PathsOKR PL.ltF PL.QT R [item<j>]`
  src/NDL/<IP>/e<ID>/A.lean         #plagg3n: `ok : S5.NoDecomp (leafT R) (leafN R) (leafDom6 R)`
  src/NDX/<IP>/X<k>.lean            chunk of at most C leaves (default 100): private `hr<i> : SEG.R = E1G.leafRec R VT DOM pl cert`
                                    (decide +kernel) and `ok : ∀ pl ∈ [chunk literal], NoDecomp (… pl 0 …)` (PL.noDecomp_of_rec)
  src/NDX/<IP>/Top.lean             `NDX.<IP>.<X>` (default X = x<c>, c = IP's digits): the statement above, from the chunks
  manifest.jsonl, leaves.tsv, failed.tsv
ID = key with non-alphanumerics replaced by '_'. Leaf modules are imported privately by the chunks, chunks by the top."""
import sys, os, re, json, subprocess, time
from concurrent.futures import ThreadPoolExecutor
sys.set_int_max_str_digits(0)
S = os.environ.get('S443_DIR', '.') + '/'
PORT = os.environ.get('PORT_SRC', 'port/src') + '/'

def opt(name, default):
    return type(default)(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default

ip, extf, pk = sys.argv[1], sys.argv[2], os.path.abspath(sys.argv[3])
PAR, CH, MAXN = opt('--par', 4), opt('--chunk', 100), opt('--maxnodes', 2000000000)
B2, BMIN, B1 = opt('--subbits', 24000), opt('--minbits', 2000), opt('--partbits', 3000000)
SPB = opt('--sperbit', 0.0003)                 # kernel s per record bit (a0-a2: 0.14-0.43 ms)
XN = opt('--name', 'x' + re.sub(r'\D', '', ip))
NS = 'E1G.IP_' + ip
TOOLS = os.environ.get('PLANE_TOOLS')          # build machines: the plane tools dir (gen7pc, ip/IP_<IP>.lean); otherwise the s443 tree
GEN = os.path.join(TOOLS, 'gen7pc') if TOOLS else S + 'cpp/gen7pc'
txt = open(os.path.join(TOOLS, 'ip', 'IP_%s.lean' % ip) if TOOLS else PORT + 'HCap/IP_%s.lean' % ip).read()
cfg = {n: int(re.search(r'def %s : Nat := (0x[0-9a-f]+|\d+)' % n, txt).group(1), 0) for n in ('R', 'VT', 'DOM')}
R, VT, DOM = cfg['R'], cfg['VT'], cfg['DOM']
assert R < 64 and DOM < 2 ** 512
NI = str(max(0, 10 - os.nice(0)))

def leafrec(pl, cert):
    terms = 0
    for i in range(R):
        terms |= ((VT >> (9 * ((pl >> (7 * i)) & 127))) & 511) << (9 * i)
    return R | (terms << 6) | ((1 | (DOM << 2) | (cert << 514)) << (6 + 9 * R))

leaves = []
for ln in open(extf):
    t = ln.split()
    if len(t) < 2 or t[0].startswith('#'): continue
    labs = list(map(int, t[1].split(',')))
    assert len(labs) == R and all(0 <= l < 128 for l in labs), (t[0], len(labs))
    pl = sum(l << (7 * i) for i, l in enumerate(labs))
    if len(t) > 3: assert int(t[3]) == pl, ('packed prefix differs from the labels', t[0])
    leaves.append((re.sub(r'[^A-Za-z0-9]', '_', t[0]), labs, t[2] if len(t) > 2 else 'U', pl))
assert len(set(x[0] for x in leaves)) == len(leaves), 'duplicate ID'
assert len(set(x[3] for x in leaves)) == len(leaves), 'duplicate pl'
for d in ('gen', 'src/data', 'src/NDX/' + ip):
    os.makedirs(os.path.join(pk, d), exist_ok=True)

def gen(item):
    lid, labs, flag, pl = item
    out = os.path.join(pk, 'gen', lid + '.txt')
    if os.path.exists(out) and open(out).read().rstrip().endswith('END'):
        return lid, 0.0
    inp = ','.join(str((VT >> (9 * l)) & 511) for l in labs) + ' M:%x\n' % DOM
    t0 = time.time()
    with open(out, 'w') as f:
        subprocess.run(['nice', '-n', NI, GEN, '--maxnodes', str(MAXN), '--split3', '1', '1',
                        '--splitB', str(B2), str(BMIN), str(B1)], input=inp, stdout=f, stderr=subprocess.DEVNULL, text=True)
    return lid, time.time() - t0

with ThreadPoolExecutor(PAR) as ex:
    gtime = dict(ex.map(gen, leaves))

OPTS = ['meta import KMod.Units', 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
        'set_option maxRecDepth 100000']
man, rows, failed, ents = [], [], [], []
def mod(name, rel, kind, deps, ps, gb, lines):
    open(os.path.join(pk, rel), 'w').write('\n'.join(lines) + '\n')
    man.append(dict(module=name, src=rel, cwd='src', tier='nd', kind=kind, deps=deps, pred_s=round(ps, 1), pred_gb=round(gb, 2)))

for lid, labs, flag, pl in leaves:
    lines = [l for l in open(os.path.join(pk, 'gen', lid + '.txt')).read().split('\n') if l]
    mains = [i for i, l in enumerate(lines) if l.startswith('MAIN ')]      # after a fit-fallback retry gen7pc reprints everything
    if mains: lines = lines[mains[-1]:]
    m = lines[0].split() if lines else ['EMPTY']
    if m[0] != 'MAIN':
        failed.append((lid, m[0])); continue
    assert int(m[3]) == 0, ('SAT leaves in a plain certificate', lid)
    cert = int(m[1], 16)
    rec = leafrec(pl, cert)
    seg = 'NDL.%s.e%s' % (ip, lid)
    body = [l for l in lines[1:] if l.startswith('PART ') or l.startswith('SUB ')]
    dpath = 'data/%s_e%s.pln' % (ip, lid)
    open(os.path.join(pk, 'src', dpath), 'w').write('HDRN %x\n' % rec + '\n'.join(body) + ('\n' if body else ''))
    parts, cur = [], None            # [bits of the part's records, largest record's bits]
    for l in body:
        f = l.split()
        if f[0] == 'PART': cur = [int(f[4]), int(f[4])]; parts.append(cur)
        else: cur[0] += int(f[4]); cur[1] = max(cur[1], int(f[4]))
    md = 'src/NDL/%s/e%s/' % (ip, lid)
    os.makedirs(os.path.join(pk, md), exist_ok=True)
    mod(seg + '.H', md + 'H.lean', 'hdr', [], 5.0, 0.6,
        ['module', 'public import S4.SplitRN', 'meta import S4.PLDrvRN', 'set_option Elab.async false', '#plhdr3n %s "%s"' % (seg, dpath)])
    for j, (pb, mb) in enumerate(parts):
        mod('%s.P%d' % (seg, j), md + 'P%d.lean' % j, 'part', [seg + '.H'], 4.0 + SPB * pb, max(0.9, 0.9 + 0.000028 * mb),
            ['module', 'public import %s.H' % seg, 'meta import S4.PLDrvRN', 'meta import KMod.Audit', 'set_option Elab.async false',
             '#plpart3n %s %s.P%d "%s" %d' % (seg, seg, j, dpath, j), '#kax %s.P%d.ok' % (seg, j)])
    pj = ['%s.P%d' % (seg, j) for j in range(len(parts))]
    mbits = int(m[2])
    mod(seg + '.A', md + 'A.lean', 'agg', [seg + '.H'] + pj, 5.0 + SPB * mbits, max(0.6, 0.9 + 0.000028 * mbits),
        ['module', 'public import %s.H' % seg] + ['import ' + p for p in pj] +
        ['meta import S4.PLDrvRN', 'meta import KMod.Audit', 'set_option Elab.async false',
         '#plagg3n %s "%s"%s' % (seg, dpath, ''.join(' ' + p for p in pj)), '#kax %s.ok' % seg])
    rows.append((lid, pl, mbits, len(parts), sum(1 for l in body if l.startswith('SUB ')), max([p[1] for p in parts] or [0]),
                 sum(p[0] for p in parts) + mbits, round(gtime.get(lid, 0.0), 2)))
    ents.append((seg, pl, cert))

def stmt(lst):
    r = 'E1G.leafRec %s.R %s.VT %s.DOM pl 0' % (NS, NS, NS)
    return '∀ pl ∈ %s, S5.NoDecomp (S5.leafT (%s)) (S5.leafN (%s)) (S6.leafDom6 (%s))' % (lst, r, r, r)
def lit(pls): return '[%s]' % ', '.join(map(str, pls))
HEAD = ['module', 'public import R22Port.U_d41d8cd98f00', 'public import HCap.IP_' + ip, 'public import S4.SplitRN']

if ents and not failed:
    chunks = [ents[i:i + CH] for i in range(0, len(ents), CH)]
    if len(chunks) > CH: sys.exit('more than %d chunks: a middle level is needed' % CH)
    xs = []
    for k, ch in enumerate(chunks):
        name = 'NDX.%s.X%d' % (ip, k)
        L = HEAD + ['import %s.A' % s for s, _, _ in ch] + OPTS + [
            '/-! External leaves of %s, chunk %d (%d leaves): `NoDecomp` of the cert-0 leaf records, from the split leaf modules'
            ' (generated by s443/py/mkndprod.py) -/' % (ip, k, len(ch)), 'namespace ' + name]
        for i, (seg, pl, cert) in enumerate(ch):
            L.append('theorem hr%d : %s.R = E1G.leafRec %s.R %s.VT %s.DOM %d %d := by decide +kernel' % (i, seg, NS, NS, NS, pl, cert))
        L += ['theorem hR : %s.R < 64 := by decide +kernel' % NS, 'theorem hD : %s.DOM < 2 ^ 512 := by decide +kernel' % NS,
              '#kpubterm %s.ok : %s := by' % (name, stmt(lit([p for _, p, _ in ch]))), '  intro pl hpl',
              '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpl', '  rcases hpl with ' + ' | '.join(['rfl'] * len(ch))]
        for i, (seg, pl, cert) in enumerate(ch):
            L.append('  · exact PL.noDecomp_of_rec _ _ _ _ %d _ hr%d hR hD %s.ok' % (cert, i, seg))
        L += ['end ' + name, '#kax %s.ok' % name, '']
        mod(name, 'src/NDX/%s/X%d.lean' % (ip, k), 'glue', [s + '.A' for s, _, _ in ch], 5.0 + 0.3 * len(ch), 0.8, L)
        xs.append((name, [p for _, p, _ in ch]))
    allpl = [x[3] for x in leaves]
    assert allpl == [p for _, ps in xs for p in ps]
    top = 'NDX.%s.Top' % ip
    L = HEAD + ['import ' + x for x, _ in xs] + OPTS + [
        '/-! The external leaves of %s (%d leaves, %d chunks): the class root\'s hypothesis `%s` over the literal list of the leaf'
        ' agent\'s `KC.%s.EXT` (EXTFILE order; generated by s443/py/mkndprod.py). The chunks are imported privately. -/'
        % (ip, len(allpl), len(xs), XN, ip), 'namespace NDX.%s' % ip]
    if len(xs) == 1:
        L += ['#kpubterm NDX.%s.%s : %s := %s.ok' % (ip, XN, stmt(lit(allpl)), xs[0][0])]
    else:
        L += ['theorem hALL : %s = %s := by decide +kernel' % (lit(allpl), ' ++ '.join(lit(ps) for _, ps in xs)),
              '#kpubterm NDX.%s.%s : %s := by' % (ip, XN, stmt(lit(allpl))), '  intro pl hpl', '  rw [hALL] at hpl',
              '  simp only [List.mem_append] at hpl', '  rcases hpl with ' + ' | '.join(['h'] * len(xs))]
        L += ['  · exact %s.ok pl h' % x for x, _ in xs]
    L += ['end NDX.%s' % ip, '#kax NDX.%s.%s' % (ip, XN), '#print axioms NDX.%s.%s' % (ip, XN), '']
    mod(top, 'src/NDX/%s/Top.lean' % ip, 'top', [x for x, _ in xs], 5.0 + 0.02 * len(allpl), 0.8, L)
open(os.path.join(pk, 'manifest.jsonl'), 'w').write(''.join(json.dumps(x) + '\n' for x in man))
open(os.path.join(pk, 'leaves.tsv'), 'w').write('id\tpl\tmain_bits\tparts\tsub_records\tmax_sub_bits\ttotal_bits\tgen_s\n' +
                                                ''.join('\t'.join(map(str, r)) + '\n' for r in rows))
open(os.path.join(pk, 'failed.tsv'), 'w').write(''.join('%s\t%s\n' % f for f in failed))
tot = sum(x['pred_s'] for x in man)
print('%s: %d leaves, %d certified, %d failed%s; %d modules, predicted %.0f kernel-s (%.2f CPU-h)'
      % (ip, len(leaves), len(ents), len(failed), ' (NO TOP)' if failed else '', len(man), tot, tot / 3600))
