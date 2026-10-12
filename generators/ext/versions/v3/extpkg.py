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
fails the package (exit 3, reason in DONE.failed): every EXT leaf must be certified."""
import sys, os, re, json, base64, hashlib, subprocess, time
sys.set_int_max_str_digits(0)
TOOLS = os.environ.get('PLANE_TOOLS') or os.path.dirname(os.path.abspath(__file__))
HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(TOOLS, 'gen7pc') if os.path.exists(os.path.join(TOOLS, 'gen7pc')) else os.path.join(HERE, 'gen7pc_v3')
IPDIR = os.path.join(TOOLS, 'ip') if os.path.isdir(os.path.join(TOOLS, 'ip')) else os.path.join(HERE, 'ip')
CC = {
    '436': dict(ip='IP_c436.lean', imps=['S4.CCLeaf', 'S4.CC436'], ipg='L479.CC436.ipg', cx='E1G.OK_c436.Cx', ns='E1G.IP_c436',
                basis='1,34,80', pts=[1, 34, 35, 80, 81, 114, 115]),
    '422': dict(ip='IP_c422.lean', imps=['S4.CCLeaf', 'LG.IPC422'], ipg='L479.IPC422.ipg', cx='E1G.OK_c422.Cx', ns='E1G.IP_c422',
                basis='1,20,66', pts=[1, 20, 21, 66, 67, 86, 87]),
}
OPTS = ['meta import KMod.Units', 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
        'set_option maxRecDepth 100000']
# records: sub-records of at most B2 bits (U/B/E leaves: UB2) and 72 SAT leaves, parts of at most B1 bits and 10,368 SAT leaves
NPART, NSUB, B2, UB2, BMIN, B1 = 10368, 72, 40000, 24000, 2000, 3000000
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
        with open(g, 'w') as f:
            subprocess.run([GEN, '--plane', cfg['basis'], '--pk', '3', '--maxnodes', str(maxn), '--split3', str(NPART), str(NSUB),
                            '--splitB', str(b2), str(BMIN), str(B1)], input=','.join(map(str, terms)) + ' E:' + cfg['basis'] + '\n',
                           stdout=f, stderr=subprocess.DEVNULL, text=True)
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
        open(os.path.join(out, 'src', dpath), 'w').write('HDR %x %x %s 3\n' % (rec, cfg['Em'], ','.join(map(str, cfg['pts'])))
                                                        + '\n'.join(body) + ('\n' if body else ''))
        parts, cur = [], None          # [SAT leaves, largest sub-record's SAT leaves, bits without SAT leaves, largest sub's bits]
        for l in body:
            f = l.split()
            if f[0] == 'PART': cur = [int(f[5]), 0, int(f[4]), 0]; parts.append(cur)
            else:
                cur[1] = max(cur[1], int(f[5])); cur[3] = max(cur[3], int(f[4]))
                if int(f[5]) == 0: cur[2] += int(f[4])
        md = 'src/PLX/c%s/%s/' % (cap, lid)
        mod(seg + '.H', md + 'H.lean', 'table', [], 5.0, 0.6,
            ['module', 'public import S4.SplitR', 'meta import S4.PLDrvR', 'set_option Elab.async false', '#plhdr3 %s "%s"' % (seg, dpath)])
        for j, (ns, mx, ub, mb) in enumerate(parts):
            mod('%s.P%d' % (seg, j), md + 'P%d.lean' % j, 'part', [seg + '.H'], 4.0 + 0.0445 * ns + SPB * ub,
                (0.58 + 0.0070 * mx) if ub == 0 else max(0.58 + 0.0070 * mx, 0.9 + 0.000028 * mb),
                ['module', 'public import %s.H' % seg, 'meta import S4.PLDrvR', 'meta import KMod.Audit', 'set_option Elab.async false',
                 '#plpart3 %s %s.P%d "%s" %d' % (seg, seg, j, dpath, j), '#kax %s.P%d.ok' % (seg, j)])
        pj = ['%s.P%d' % (seg, j) for j in range(len(parts))]
        mod(seg + '.A', md + 'A.lean', 'agg', [seg + '.H'] + pj, 5.0 + SPB * int(m[2]), max(0.6, 0.9 + 0.000028 * int(m[2])),
            ['module', 'public import %s.H' % seg] + ['import ' + p for p in pj] +
            ['meta import S4.PLDrvR', 'meta import KMod.Audit', 'set_option Elab.async false',
             '#plagg3 %s "%s"%s' % (seg, dpath, ''.join(' ' + p for p in pj)), '#kax %s.ok' % seg])
        nsat = int(m[3])
        rows.append(dict(key=key, pl=str(pl), flag=flag, seg=seg, sat_leaves=nsat, parts=len(parts), main_bits=int(m[2]),
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
    """the class route: mkndprod.py (same module names and texts as locally); the manifest's header kind becomes table, and the
    top gets its pub"""
    f = os.path.join(out, 'leaves.txt')
    open(f, 'w').write(''.join('%s %s %s %d\n' % (k, ','.join(map(str, labs)), flag, pl) for k, labs, flag, pl in leaves))
    env = dict(os.environ, PLANE_TOOLS=TOOLS if os.path.isdir(os.path.join(TOOLS, 'ip')) else '')
    if not env['PLANE_TOOLS']: env.pop('PLANE_TOOLS')
    r = subprocess.run([sys.executable, os.path.join(HERE, 'mkndprod.py'), cap, f, out, '--par', '4', '--maxnodes', str(maxn)],
                       env=env, capture_output=True, text=True)
    sys.stdout.write(r.stdout); sys.stderr.write(r.stderr)
    failed = [tuple(l.rstrip('\n').split('\t')) for l in open(os.path.join(out, 'failed.tsv')) if l.strip()]
    man = [json.loads(l) for l in open(os.path.join(out, 'manifest.jsonl')) if l.strip()]
    top = None
    xn = 'x' + re.sub(r'\D', '', cap)
    for m in man:
        if m['kind'] == 'hdr': m['kind'] = 'table'
        if m['kind'] == 'top': m['pub'] = 'NDX.%s.%s' % (cap, xn); top = (m['module'], m['pub'], [x[3] for x in leaves])
    rows = [dict(key=k, pl=str(pl), flag=flag) for k, labs, flag, pl in leaves]
    return man, rows, failed, top

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
    ins = [os.path.join(out, 'leaves.in'), GEN, os.path.abspath(__file__), os.path.join(HERE, 'mkndprod.py')]
    ins += [os.path.join(IPDIR, CC[cap]['ip'])] if cap in CC else [os.path.join(IPDIR, 'IP_%s.lean' % cap)]
    open(os.path.join(out, 'inputs.sha256'), 'w').write(''.join('%s  %s\n' % (sha(p), p) for p in ins if os.path.exists(p)))
    done = dict(cap=cap, kind='ext', leaves=len(leaves), modules=len(man), pred_s=round(sum(m['pred_s'] for m in man), 1),
                pred_gb_max=max([m['pred_gb'] for m in man] or [0]), pubs=[[top[0], top[1]]] if top else [],
                pls=[str(p) for p in (top[2] if top else [])], rows=rows, failed=[list(map(str, f)) for f in failed], kext=0,
                secs=round(time.time() - t0, 1))
    open(os.path.join(out, 'DONE'), 'w').write(json.dumps(done) + '\n')
    print('extpkg %s: %d leaves, %d modules, pred %.0f s%s' % (cap, len(leaves), len(man), done['pred_s'],
          '' if not failed else ', FAILED %s' % failed))
    if failed or not top: sys.exit(3)

main()
