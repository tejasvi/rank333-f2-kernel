#!/usr/bin/env python3
"""extpkg.py CAP LEAVES OUT [--maxnodes M]: one EXT package of the build queue (package kind "ext").

CAP 436 or 422: the CC route. Every leaf (flag S, U, B or E) is certified by `gen7pc --plane BASIS --pk 3 --split3` (sibling
ranges; S4.SplitR / S4.PLDrvR: header, parts, aggregator with `SEG.ok : L479.NoLiftK (leafT R) (leafN R) (leafDom6 R) Em 3`),
and the package's one chunk module gives
    PLE.c<CAP>.X<key>.ok : ∀ (ext : List ℕ), ∀ pl ∈ [pl₁, …], L479.LeafNoExt (E1G.OK_c<CAP>.Cx ext) E1G.IP_c<CAP>.Em 14 pl
(a literal list, no shared data module; PL.leafNoExt_of_noLiftK_rec with `hr : SEG.R = E1G.leafRec R VT DOM pl cert` by
`decide +kernel`, the IP facts from `ipg ext`). The cap's EXT top (fan-in-100 middle level and `PLE.c<CAP>.Ext.hext_of`) is built
at aggregation from the chunks (mkexttop.py).
CAP h<c>: the class route (`mkndprod.py`, NoDecomp): leaf modules, chunks and the top `NDX.h<c>.Top` with `NDX.h<c>.x<c>`.

LEAVES: base64 of lines "<key> <l1,…,lR> <flag> [<pl>]" (the E1G emitter's kext.txt order: key = the job key; pl checked against the
labels), or "@<file>" for a file of such lines.
OUT: the package directory (the worker's {OUT}): src/ (modules, cwd), src/data/, manifest.jsonl (sched.py lines; "pub"
on the package's top-level theorem; header modules kind "table", so the worker ships them as .kplain), DONE (JSON: pubs, leaves,
modules, predictions), inputs.sha256, gen/ (generator outputs).
Module names are deterministic: leaf modules PLX.c<CAP>.x<16 hex of sha256("c<CAP>:<pl>")>, chunk PLE.c<CAP>.X<16 hex of
sha256 over the sorted pl list>. A leaf whose generator output is not a MAIN record (SAT: a decomposition that lifts; BIG; ENC)
fails the package (exit 1 since v10, reason in DONE.failed): every EXT leaf must be certified."""
import sys, os, re, json, base64, hashlib, subprocess, time
sys.set_int_max_str_digits(0)
TOOLS = os.environ.get('PLANE_TOOLS') or os.path.dirname(os.path.abspath(__file__))
HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(TOOLS, 'gen7pc') if os.path.exists(os.path.join(TOOLS, 'gen7pc')) else os.path.join(HERE, 'gen7pc_v3')
IPDIR = os.path.join(TOOLS, 'ip') if os.path.isdir(os.path.join(TOOLS, 'ip')) else os.path.join(HERE, 'ip')
GENPD = os.path.join(TOOLS, 'gen7pd') if os.path.exists(os.path.join(TOOLS, 'gen7pd')) else os.path.join(HERE, '..', 'cpp', 'gen7pd')
GENW = int(os.environ.get('EXTPKG_GENW', '8'))      # parallel subtree generators per leaf (v4)
# v9: gen7pd over the EqF walk (s443/cpp/eqfpd/gen7pd_eqf.cc = gen7pd.cc + gen7p_eqf.h): EqF S/B/E leaves are generated in parallel
GENPDE = os.path.join(TOOLS, 'gen7pd_eqf') if os.path.exists(os.path.join(TOOLS, 'gen7pd_eqf')) else os.path.join(HERE, '..', 'cpp', 'eqfpd', 'gen7pd_eqf')
GENWE = int(os.environ.get('EXTPKG_GENWE', '16'))   # its parallel subtree generators per leaf 
GENE = os.path.join(TOOLS, 'gen7pc_eqf') if os.path.exists(os.path.join(TOOLS, 'gen7pc_eqf')) else os.path.join(HERE, '..', 'cpp', 'gen7pc_eqf_v3')
CC = {
    '436': dict(ip='IP_c436.lean', imps=['S4.CCLeaf', 'S4.CC436'], ipg='L479.CC436.ipg', cx='E1G.OK_c436.Cx', ns='E1G.IP_c436',
                basis='1,34,80', pts=[1, 34, 35, 80, 81, 114, 115]),
    '422': dict(ip='IP_c422.lean', imps=['S4.CCLeaf', 'LG.IPC422'], ipg='L479.IPC422.ipg', cx='E1G.OK_c422.Cx', ns='E1G.IP_c422',
                basis='1,20,66', pts=[1, 20, 21, 66, 67, 86, 87]),
}
OPTS = ['meta import KMod.Units', 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
        'set_option maxRecDepth 100000']
# records: sub-records of at most B2 bits (U/B/E leaves: UB2) and 72 SAT leaves, parts of at most B1 bits and 10,368 SAT leaves
# v6: parts of at most 1 Mbit (B1), so a part's kernel time stays under about 450 s even at 0.43 ms/bit (Lean 4.30's write crash past
# about 2,000 s of kernel work per module; SAT parts are bounded by NPART: about 10,368 x 45-49 ms)
NPART, NSUB, B2, UB2, BMIN, B1 = 10368, 72, 40000, 24000, 2000, 1000000
TOOLS_VERSION = 'v12'  # v12: parallel EqF generation assembled and encoded as gen7pc_eqf (gen7pd_eqf --dump/--assemble); v10: exit 1   # v9: EqF S/B/E leaves through gen7pd_eqf + gensplit (parallel generation)   # v8: maxHeartbeats 0 in the header, part and aggregator modules (x53bef413ee8f2c87's A: '(kernel)
#                         deterministic timeout' at the default 200000; its main-record check takes 256 s)
def agg_gb(mbits):
    """the aggregator A's predicted memory (v7): the kernel's main-record walk keeps its big-Nat intermediates; measured 30.1 GB RSS
    locally at 533,277 main bits (ext_c436_x79030781b541af39, 216 parts; v6 predicted 15.8 GB, so the scheduler's first-attempt
    address-space cap 2 x pred + 16 GB was too small and A aborted: exit -6, or `INTERNAL PANIC: out of memory`, exit 1)"""
    # the pipeline's A logs (2026-10-10): out of memory also under the retry's 79 GB cap (the cap covers every mmapped closure and
    # store file), so 3 + 0.0001 x main_bits: 56 GB at 533k bits, first-attempt cap 2 x 56 + 16 = 128 GB (lines: min_mem_gb 128)
    return round(max(0.6, 3.0 + 0.0001 * mbits), 2)
SPB = 0.0003                 # kernel s per record bit without SAT leaves (a0-a2: 0.14-0.43 ms)

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()

def fetch_gs(spec):
    """'@gs:OBJECT:SHA256:A:B': lines A..B-1 of the leaf-list object OBJECT, read from $EXT_LEAVES/<basename of OBJECT> (sha256-checked)"""
    obj, sha_, a, b = spec[4:].rsplit(':', 3)
    data = open(os.path.join(os.environ.get('EXT_LEAVES', 'extleaves'), os.path.basename(obj)), 'rb').read()
    assert hashlib.sha256(data).hexdigest() == sha_, 'leaf list %s: sha256 differs' % obj
    return ''.join(data.decode().splitlines(True)[int(a):int(b)])

def leaves_of(arg):
    txt = fetch_gs(arg) if arg.startswith('@gs:') else open(arg[1:]).read() if arg.startswith('@') else base64.b64decode(arg).decode()
    out = []
    for ln in txt.splitlines():
        t = ln.split()
        if len(t) < 2 or t[0].startswith('#'): continue
        labs = list(map(int, t[1].split(',')))
        pl = sum(l << (7 * i) for i, l in enumerate(labs))
        if len(t) > 3: assert int(t[3]) == pl, ('packed prefix differs from the labels', t[0])
        out.append((t[0], labs, t[2] if len(t) > 2 else 'S', pl))
    return out

def cc_package(cap, leaves, out, maxn):
    cfg = dict(CC[cap]); txt = open(os.path.join(IPDIR, cfg['ip'])).read()
    for n in ('R', 'VT', 'DOM', 'Em'):
        cfg[n] = int(re.search(r'def %s : Nat := (0x[0-9a-f]+|\d+)' % n, txt).group(1), 0)
    R, VT, DOM = cfg['R'], cfg['VT'], cfg['DOM']
    for d in ('gen', 'src/data'): os.makedirs(os.path.join(out, d), exist_ok=True)
    uniq = {}
    for k, labs, flag, pl in leaves:
        assert len(labs) == R and all(0 <= l < 128 for l in labs), (k, len(labs), R)
        uniq.setdefault(pl, (k, labs, flag, pl))
    leaves = [uniq[p] for p in sorted(uniq)]
    man, rows, failed, ents = [], [], [], []
    def mod(name, rel, kind, deps, ps, gb, lines, pub=None):
        p = os.path.join(out, rel); os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w').write('\n'.join(lines) + '\n')
        m = dict(module=name, src=rel, cwd='src', tier='ext', kind=kind, deps=deps, pred_s=round(ps, 1), pred_gb=round(gb, 2))
        if pub: m['pub'] = pub
        man.append(m)
    for key, labs, flag, pl in leaves:
        lid = 'x' + hashlib.sha256(('c%s:%d' % (cap, pl)).encode()).hexdigest()[:16]
        g = os.path.join(out, 'gen', lid + '.txt')
        terms = [(VT >> (9 * l)) & 511 for l in labs]
        t0 = time.time()
        b2 = UB2 if flag in ('U', 'B', 'E') else B2
        inp = ','.join(map(str, terms)) + ' E:' + cfg['basis'] + '\n'
        eqf = len(set(terms)) < len(terms) and os.path.exists(GENE) and os.environ.get('EXTPKG_NOEQF') != '1'
        if eqf and flag in ('S', 'B', 'E') and os.path.exists(GENPDE) and os.environ.get('EXTPKG_NOSPLIT') != '1':
            # v9: the EqF walk generated in parallel (gen7pd_eqf --top / --sub, gensplit; MAIN keeps a0): same SAT leaves as
            # gen7pc_eqf (217,728 on ext_c436_xffeb7cfb27eaeb25), a much smaller main record (10k vs 95k bits)
            sys.path.insert(0, HERE); import gensplit
            # v12: the items generated in parallel and dumped, then assembled into the whole tree and encoded as gen7pc_eqf --split3
            # (grouped parts, a small main record): ext_c436_xffeb7cfb27eaeb25: 217,728 SAT leaves, 108 parts, main 95,169 bits
            # (gen7pc_eqf: 108 parts, 95,124 bits), 86 s with 12 workers (343 s)
            gensplit.gen_split_asm(GENPDE, inp, ['--eqf', '--plane', cfg['basis'], '--pk', '3', '--maxnodes', str(maxn)], g, workers=GENWE,
                                   d0=2, L1s=300000, B1s=100000000, NPART=NPART, NSUB=NSUB, B2=b2, BM=BMIN, B1=B1, kexp=1,
                                   log=lambda m: print('gensplit-asm %s: %s' % (key, m), flush=True))
        elif eqf:
            # v5: the equal-first-factor walk (S4.EqF / S4.PLDrvRE; gen7pc_eqf --eqf): 8-192x fewer SAT leaves on repeated terms
            with open(g, 'w') as f:
                subprocess.run([GENE, '--eqf', '--plane', cfg['basis'], '--pk', '3', '--maxnodes', str(maxn), '--split3', str(NPART), str(NSUB),
                                '--splitB', str(b2), str(BMIN), str(B1)], input=inp, stdout=f, stderr=subprocess.DEVNULL, text=True)
        elif flag in ('S', 'B', 'E') and os.path.exists(GENPD) and os.environ.get('EXTPKG_NOSPLIT') != '1':
            # v4: distributed generation (gen7pd --top / --sub in parallel, items within the part budgets), same output format
            sys.path.insert(0, HERE); import gensplit
            gensplit.gen_split(GENPD, inp, ['--plane', cfg['basis'], '--pk', '3', '--maxnodes', str(maxn)], g, workers=GENW,
                               d0=3, L1=NPART, B1=B1, L2=NSUB, B2=b2, BM=BMIN, log=lambda m: print('gensplit %s: %s' % (key, m), flush=True))
        else:
            with open(g, 'w') as f:
                subprocess.run([GEN, '--plane', cfg['basis'], '--pk', '3', '--maxnodes', str(maxn), '--split3', str(NPART), str(NSUB),
                                '--splitB', str(b2), str(BMIN), str(B1)], input=inp, stdout=f, stderr=subprocess.DEVNULL, text=True)
        gs = time.time() - t0
        lines = [l for l in open(g).read().split('\n') if l]
        # gen7pc prints a partial output before an encoding overflow and then the whole output again with the fit fallback:
        # only the last MAIN block counts
        mains = [i for i, l in enumerate(lines) if l.startswith('MAIN ')]
        if mains: lines = lines[mains[-1]:]
        m = lines[0].split() if lines else ['EMPTY']
        if m[0] != 'MAIN' or lines[-1] != 'END':
            failed.append((key, pl, m[0])); continue
        cert = int(m[1], 16)
        T = sum(t << (9 * i) for i, t in enumerate(terms))
        rec = R | (T << 6) | ((1 | (DOM << 2) | (cert << 514)) << (6 + 9 * R))
        seg = 'PLX.c%s.%s' % (cap, lid)
        body = [l for l in lines[1:] if l.startswith('PART ') or l.startswith('SUB ')]
        dpath = 'data/c%s_%s.pls' % (cap, lid)
        if eqf:
            a0 = int(m[5])
            hdr = 'HDRE %x %x %s 3 %d\n' % (rec, cfg['Em'], ','.join(map(str, cfg['pts'])), a0)
            base, drv, sfx = 'S4.EqF', 'S4.PLDrvRE', '3e'
        else:
            hdr = 'HDR %x %x %s 3\n' % (rec, cfg['Em'], ','.join(map(str, cfg['pts'])))
            base, drv, sfx = 'S4.SplitR', 'S4.PLDrvR', '3'
        open(os.path.join(out, 'src', dpath), 'w').write(hdr + '\n'.join(body) + ('\n' if body else ''))
        parts, cur = [], None          # [SAT leaves, largest sub-record's SAT leaves, bits without SAT leaves, largest sub's bits]
        for l in body:
            f = l.split()
            if f[0] == 'PART': cur = [int(f[5]), 0, int(f[4]), 0]; parts.append(cur)
            else:
                cur[1] = max(cur[1], int(f[5])); cur[3] = max(cur[3], int(f[4]))
                if int(f[5]) == 0: cur[2] += int(f[4])
        md = 'src/PLX/c%s/%s/' % (cap, lid)
        mod(seg + '.H', md + 'H.lean', 'table', [], 5.0, 0.6,
            ['module', 'public import ' + base, 'meta import ' + drv, 'set_option Elab.async false', 'set_option maxHeartbeats 0', '#plhdr%s %s "%s"' % (sfx, seg, dpath)])
        for j, (ns, mx, ub, mb) in enumerate(parts):
            mod('%s.P%d' % (seg, j), md + 'P%d.lean' % j, 'part', [seg + '.H'], 4.0 + 0.0445 * ns + SPB * ub,
                (0.58 + 0.0070 * mx) if ub == 0 else max(0.58 + 0.0070 * mx, 0.9 + 0.000028 * mb),
                ['module', 'public import %s.H' % seg, 'meta import ' + drv, 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
                 '#plpart%s %s %s.P%d "%s" %d' % (sfx, seg, seg, j, dpath, j), '#kax %s.P%d.ok' % (seg, j)])
        pj = ['%s.P%d' % (seg, j) for j in range(len(parts))]
        mod(seg + '.A', md + 'A.lean', 'agg', [seg + '.H'] + pj, 5.0 + SPB * int(m[2]), agg_gb(int(m[2])),
            ['module', 'public import %s.H' % seg] + ['import ' + p for p in pj] +
            ['meta import ' + drv, 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
             '#plagg%s %s "%s"%s' % (sfx, seg, dpath, ''.join(' ' + p for p in pj)), '#kax %s.ok' % seg])
        nsat = int(m[3])
        rows.append(dict(key=key, pl=str(pl), flag=flag, seg=seg, eqf=eqf, sat_leaves=nsat, parts=len(parts), main_bits=int(m[2]),
                         sub_records=sum(1 for l in body if l.startswith('SUB ')), gen_s=round(gs, 2)))
        ents.append((seg, pl, cert))
    if failed:
        return man, rows, failed, None
    pls = [p for _, p, _ in ents]
    pkey = 'X' + hashlib.sha256(('c%s:' % cap + ','.join(map(str, pls))).encode()).hexdigest()[:16]
    name = 'PLE.c%s.%s' % (cap, pkey)
    g = cfg['ipg']
    L = ['module'] + ['public import ' + x for x in cfg['imps']] + ['import %s.A' % s for s, _, _ in ents] + OPTS + [
        '/-! External leaves of c%s (%d): `LeafNoExt` from the split leaf modules (generated by s443/extpkg/extpkg.py) -/'
        % (cap, len(ents)), 'namespace ' + name]
    for k, (seg, pl, cert) in enumerate(ents):
        L.append('theorem hr%d : %s.R = E1G.leafRec %s.R %s.VT %s.DOM %d %d := by decide +kernel' % (k, seg, cfg['ns'], cfg['ns'], cfg['ns'], pl, cert))
    L += ['#kpubterm %s.ok : ∀ (ext : List ℕ), ∀ pl ∈ [%s], L479.LeafNoExt (%s ext) %s.Em 14 pl := by'
          % (name, ', '.join(map(str, pls)), cfg['cx'], cfg['ns']),
          '  intro ext pl hpl', '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpl',
          '  rcases hpl with ' + ' | '.join(['rfl'] * len(ents))]
    for k, (seg, pl, cert) in enumerate(ents):
        L.append('  · exact PL.leafNoExt_of_noLiftK_rec %d %s.R hr%d (%s ext).N_le (by have := (%s ext).R_le; omega)'
                 ' (%s ext).cosets (%s ext).domperp (%s ext).DOM_lt %s.ok' % (cert, seg, k, g, g, g, g, g, seg))
    L += ['end ' + name, '#kax %s.ok' % name, '']
    mod(name, 'src/PLE/c%s/%s.lean' % (cap, pkey), 'glue', [s + '.A' for s, _, _ in ents], 5.0 + 0.3 * len(ents), 0.8, L,
        pub=name + '.ok')
    return man, rows, failed, (name, name + '.ok', pls)

def nd_package(cap, leaves, out, maxn):
    """the class route (class-raise EXT leaves, NoDecomp), incremental: per-leaf modules NDL.<cap>.x<16 hex>.{H,P<j>,A} (S4.PLDrvRN,
    or S4.PLDrvRE when the terms repeat a value) and one chunk per package,
        NDX.<cap>.X<16 hex>.ok : ∀ pl ∈ [pl₁, …], S5.NoDecomp (S5.leafT (E1G.leafRec E1G.IP_<cap>.R … pl 0)) (S5.leafN …) (S6.leafDom6 …)
    (PL.noDecomp_of_rec). The class's top `NDX.<cap>.x<c>` over KC.<cap>.EXT's literal is built at aggregation from the chunks."""
    ns = 'E1G.IP_' + cap
    txt = open(os.path.join(IPDIR, 'IP_%s.lean' % cap)).read()
    cfg = {n: int(re.search(r'def %s : Nat := (0x[0-9a-f]+|\d+)' % n, txt).group(1), 0) for n in ('R', 'VT', 'DOM')}
    R, VT, DOM = cfg['R'], cfg['VT'], cfg['DOM']
    for d in ('gen', 'src/data'): os.makedirs(os.path.join(out, d), exist_ok=True)
    uniq = {}
    for k, labs, flag, pl in leaves:
        assert len(labs) == R and all(0 <= l < 128 for l in labs), (k, len(labs), R)
        uniq.setdefault(pl, (k, labs, flag, pl))
    leaves = [uniq[p] for p in sorted(uniq)]
    man, rows, failed, ents = [], [], [], []
    def mod(name, rel, kind, deps, ps, gb, lines, pub=None):
        p = os.path.join(out, rel); os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w').write('\n'.join(lines) + '\n')
        m = dict(module=name, src=rel, cwd='src', tier='ext', kind=kind, deps=deps, pred_s=round(ps, 1), pred_gb=round(gb, 2))
        if pub: m['pub'] = pub
        man.append(m)
    for key, labs, flag, pl in leaves:
        lid = 'x' + hashlib.sha256(('%s:%d' % (cap, pl)).encode()).hexdigest()[:16]
        g = os.path.join(out, 'gen', lid + '.txt')
        terms = [(VT >> (9 * l)) & 511 for l in labs]
        eqf = len(set(terms)) < len(terms) and os.path.exists(GENE) and os.environ.get('EXTPKG_NOEQF') != '1'
        t0 = time.time()
        with open(g, 'w') as f:
            subprocess.run(([GENE, '--eqf'] if eqf else [GEN]) + ['--maxnodes', str(maxn), '--split3', '1', '1', '--splitB', str(UB2), str(BMIN), str(B1)],
                           input=','.join(map(str, terms)) + ' M:%x\n' % DOM, stdout=f, stderr=subprocess.DEVNULL, text=True)
        gs = time.time() - t0
        lines = [l for l in open(g).read().split('\n') if l]
        mains = [i for i, l in enumerate(lines) if l.startswith('MAIN ')]
        if mains: lines = lines[mains[-1]:]
        m = lines[0].split() if lines else ['EMPTY']
        if m[0] != 'MAIN' or lines[-1] != 'END' or int(m[3]) != 0:
            failed.append((key, pl, m[0] if m[0] != 'MAIN' else 'SAT leaves')); continue
        cert = int(m[1], 16)
        T = sum(t << (9 * i) for i, t in enumerate(terms))
        rec = R | (T << 6) | ((1 | (DOM << 2) | (cert << 514)) << (6 + 9 * R))
        seg = 'NDL.%s.%s' % (cap, lid)
        body = [l for l in lines[1:] if l.startswith('PART ') or l.startswith('SUB ')]
        dpath = 'data/%s_%s.pln' % (cap, lid)
        if eqf: hdr, base, drv, sfx = 'HDRNE %x %d\n' % (rec, int(m[5])), 'S4.EqF', 'S4.PLDrvRE', '3ne'
        else: hdr, base, drv, sfx = 'HDRN %x\n' % rec, 'S4.SplitRN', 'S4.PLDrvRN', '3n'
        open(os.path.join(out, 'src', dpath), 'w').write(hdr + '\n'.join(body) + ('\n' if body else ''))
        parts, cur = [], None
        for l in body:
            f = l.split()
            if f[0] == 'PART': cur = [int(f[4]), int(f[4])]; parts.append(cur)
            else: cur[0] += int(f[4]); cur[1] = max(cur[1], int(f[4]))
        md = 'src/NDL/%s/%s/' % (cap, lid)
        mod(seg + '.H', md + 'H.lean', 'table', [], 5.0, 0.6,
            ['module', 'public import ' + base, 'meta import ' + drv, 'set_option Elab.async false', 'set_option maxHeartbeats 0', '#plhdr%s %s "%s"' % (sfx, seg, dpath)])
        for j, (pb, mb) in enumerate(parts):
            mod('%s.P%d' % (seg, j), md + 'P%d.lean' % j, 'part', [seg + '.H'], 4.0 + SPB * pb, max(0.9, 0.9 + 0.000028 * mb),
                ['module', 'public import %s.H' % seg, 'meta import ' + drv, 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
                 '#plpart%s %s %s.P%d "%s" %d' % (sfx, seg, seg, j, dpath, j), '#kax %s.P%d.ok' % (seg, j)])
        pj = ['%s.P%d' % (seg, j) for j in range(len(parts))]
        mbits = int(m[2])
        mod(seg + '.A', md + 'A.lean', 'agg', [seg + '.H'] + pj, 5.0 + SPB * mbits, agg_gb(mbits),
            ['module', 'public import %s.H' % seg] + ['import ' + p for p in pj] +
            ['meta import ' + drv, 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
             '#plagg%s %s "%s"%s' % (sfx, seg, dpath, ''.join(' ' + p for p in pj)), '#kax %s.ok' % seg])
        rows.append(dict(key=key, pl=str(pl), flag=flag, seg=seg, eqf=eqf, parts=len(parts), main_bits=mbits,
                         sub_records=sum(1 for l in body if l.startswith('SUB ')), gen_s=round(gs, 2)))
        ents.append((seg, pl, cert))
    if failed:
        return man, rows, failed, None
    pls = [p for _, p, _ in ents]
    pkey = 'X' + hashlib.sha256(('%s:' % cap + ','.join(map(str, pls))).encode()).hexdigest()[:16]
    name = 'NDX.%s.%s' % (cap, pkey)
    r0 = 'E1G.leafRec %s.R %s.VT %s.DOM pl 0' % (ns, ns, ns)
    L = ['module', 'public import R22Port.U_d41d8cd98f00', 'public import HCap.IP_' + cap, 'public import S4.SplitRN'] + \
        ['import %s.A' % s_ for s_, _, _ in ents] + OPTS + [
        '/-! External leaves of %s (%d): `NoDecomp` of the cert-0 leaf records (generated by s443/extpkg/extpkg.py) -/' % (cap, len(ents)),
        'namespace ' + name]
    for i, (seg, pl, cert) in enumerate(ents):
        L.append('theorem hr%d : %s.R = E1G.leafRec %s.R %s.VT %s.DOM %d %d := by decide +kernel' % (i, seg, ns, ns, ns, pl, cert))
    L += ['theorem hR : %s.R < 64 := by decide +kernel' % ns, 'theorem hD : %s.DOM < 2 ^ 512 := by decide +kernel' % ns,
          '#kpubterm %s.ok : ∀ pl ∈ [%s], S5.NoDecomp (S5.leafT (%s)) (S5.leafN (%s)) (S6.leafDom6 (%s)) := by'
          % (name, ', '.join(map(str, pls)), r0, r0, r0),
          '  intro pl hpl', '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpl',
          '  rcases hpl with ' + ' | '.join(['rfl'] * len(ents))]
    for i, (seg, pl, cert) in enumerate(ents):
        L.append('  · exact PL.noDecomp_of_rec _ _ _ _ %d _ hr%d hR hD %s.ok' % (cert, i, seg))
    L += ['end ' + name, '#kax %s.ok' % name, '']
    mod(name, 'src/NDX/%s/%s.lean' % (cap, pkey), 'glue', [s_ + '.A' for s_, _, _ in ents], 5.0 + 0.3 * len(ents), 0.8, L, pub=name + '.ok')
    return man, rows, failed, (name, name + '.ok', pls)

def main():
    cap, arg, out = sys.argv[1], sys.argv[2], os.path.abspath(sys.argv[3])
    maxn = int(sys.argv[sys.argv.index('--maxnodes') + 1]) if '--maxnodes' in sys.argv else 2000000000
    os.makedirs(out, exist_ok=True)
    if os.path.exists(out + '/DONE'): os.remove(out + '/DONE')
    t0 = time.time(); leaves = leaves_of(arg)
    open(os.path.join(out, 'leaves.in'), 'w').write(''.join('%s %s %s %d\n' % (k, ','.join(map(str, labs)), flag, pl) for k, labs, flag, pl in leaves))
    if cap in CC: man, rows, failed, top = cc_package(cap, leaves, out, maxn)
    elif re.fullmatch(r'h\d+', cap): man, rows, failed, top = nd_package(cap, leaves, out, maxn)
    else: sys.exit('unknown cap %s' % cap)
    open(os.path.join(out, 'manifest.jsonl'), 'w').write(''.join(json.dumps(x) + '\n' for x in man))
    # inputs: the leaf records, every tools file (generators, scripts, IP sources) and the plane closure parts installed on this machine
    ins = [os.path.join(out, 'leaves.in')]
    for d, _, fs in sorted(os.walk(TOOLS)):
        ins += [os.path.join(d, f) for f in sorted(fs)]
    for x in (GEN, GENE, GENPD, GENPDE, os.path.join(HERE, 'gensplit.py'), os.path.join(HERE, 'mkndprod.py')):
        if x not in ins: ins.append(x)
    marks = sorted(f for f in os.listdir(os.environ.get('KP_MARKS', 'marks')) if 'plane' in f) if os.path.isdir(os.environ.get('KP_MARKS', 'marks')) else []
    open(os.path.join(out, 'inputs.sha256'), 'w').write(''.join('%s  %s\n' % (sha(p), p) for p in ins if os.path.isfile(p)) +
                                                         ''.join('installed  %s\n' % m for m in marks))
    done = dict(cap=cap, kind='ext', tools=TOOLS_VERSION, tools_dir=TOOLS, leaves=len(leaves), modules=len(man), pred_s=round(sum(m['pred_s'] for m in man), 1),
                pred_gb_max=max([m['pred_gb'] for m in man] or [0]), pubs=[[top[0], top[1]]] if top else [],
                pls=[str(p) for p in (top[2] if top else [])], rows=rows, failed=[list(map(str, f)) for f in failed], kext=0,
                secs=round(time.time() - t0, 1))
    open(os.path.join(out, 'DONE'), 'w').write(json.dumps(done) + '\n')
    print('extpkg %s: %d leaves, %d modules, pred %.0f s%s' % (cap, len(leaves), len(man), done['pred_s'],
          '' if not failed else ', FAILED %s' % failed))
    if failed or not top: sys.exit(1)     # v10: exit 1 (the worker reads exit 3 as "closure check refused this machine")

main()
