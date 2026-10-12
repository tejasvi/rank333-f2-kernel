#!/usr/bin/env python3
"""mkagg.py CAP OUTDIR PKGDIR... [--tools DIR] [--heavy-only] [--threads T]: the aggregation phase of a context cap over its
built packages (their DONE summaries: cap, a, b, heavy, pubs; every pub a RangeOK over the package's job table), as KJ modules
in OUTDIR (sources, data, sched.py manifest; they import the packages' pub modules, prebuilt in the store):
  * per heavy job J whose packages cover its sub-jobs [0, n):
      KJ.agg<C>h<J>_A…   fan-in-100 #e1gagg over the packages' ranges (over KH.S<C>_<J>), lifted if any child is;
      KJ.agg<C>h<J>_Top  #e1gtop: J's top chain (depth 6 to 10, the emitter's own trace, mksubfr.py / DUMPONLY) glued to its
                         sub-jobs through KH.S<C>_<J>: JobOK of J's header;
      KJ.agg<C>h<J>_R    #e1gjobs over KH.HT<C> at J with the line @top: RangeOK [J, J+1)
  * unless --heavy-only, when the light packages' ranges and the heavy jobs' [J, J+1) cover [0, N) of the cap's depth-6 jobs:
      KJ.agg<C>_A…       fan-in-100 aggregators over KH.HT<C>: the cap's root range RangeOK 0 N;
      KJ.agg<C>_Root     #e1groot (E1GK.RootCmd): the chain from the IP's root to depth 6 (DUMPONLY trace), glued to the N jobs:
                         the canonical-point statement over IP.C, or over withExt IP.C EXT (the census list) when lifted.
The pub of OUTDIR is the root (or, with --heavy-only, each heavy job's range)."""
import sys, os, re, json, glob, argparse, struct, subprocess, shutil
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kjlib as K

def agg_tree(ctx, name, tbl, tbl_mod, children, man, key):
    """fan-in-100 #e1gagg modules over consecutive children (theorem, a, m, module); returns the root (theorem, module), order"""
    IPN, SLN, OKN, IMPS = K.CFG[ctx]; order = []; lvl = 0
    while len(children) > 1:
        nxt = []
        for i in range(0, len(children), 100):
            ch = children[i:i + 100]
            nm = '%s_A%d_%d' % (name, lvl, i // 100) if len(children) > 100 else '%s_A' % name
            open(K.DD + K.PK + '_%s.lst' % nm, 'w').write('\n'.join('%s %d %d' % (c[0], c[1], c[2]) for c in ch) + '\n')
            a = ch[0][1]; M = sum(c[2] for c in ch)
            open(K.MD + '%s.lean' % nm, 'w').write('\n'.join(K.header(ctx, extra_pub=[tbl_mod], priv=[c[3] for c in ch]) + [
                '#%sagg %s.%s "%s" %s %s %s' % (K.F['cmd'], K.PK, nm, K.R(K.DD + K.PK + '_%s.lst' % nm), IPN, SLN, tbl),
                '#kax ' + K.PK + '.%s.ok' % nm, '#kkey "%s/%d" "%s/%d"' % (key, a, key, a + M - 1), '']))
            K.manifest([{'module': K.PK + '.%s' % nm, 'tier': ctx, 'kind': 'agg', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45, 'input_bytes': 0}], man)
            order.append(K.PK + '.%s' % nm); nxt.append((K.PK + '.%s.ok' % nm, a, M, K.PK + '.%s' % nm))
        children = nxt; lvl += 1
    return children[0], order

def chain_files(ctx, name, trace, HT):
    """the block literals of a DUMPONLY top trace (e1pconv) and their glue witnesses against the job headers HT; one unit per
    block; returns the file prefix (relative) and the block count"""
    rd = K.RUNDIR[ctx] + 'top_%s' % name; os.makedirs(rd, exist_ok=True)
    shutil.copy(trace, rd + '/top_0_top.bin')
    if not os.path.exists(rd + '/top.bin'): K.conv_top(ctx, rd)
    b = open(rd + '/top.bin', 'rb').read(); n = struct.unpack('<I', b[:4])[0]; i = 4; top = []
    for _ in range(n):
        ln = struct.unpack('<I', b[i:i + 4])[0]; i += 4; top.append(int.from_bytes(b[i:i + ln], 'little')); i += ln
    pfx = K.DD + K.PK + '_%s_top' % name
    K.wrlits(pfx + '.bin', top); K.wrW(pfx, K.witnesses(top, HT))
    with open(pfx + '_units.txt', 'w') as f:
        for k in range(len(top)): f.write('%d\n' % k)
    return K.R(pfx), top

def headers(frontier, ctx):
    E = K.EMIT[ctx]
    toks = open(K.ipf(E['ip'])).read().split('\n')[1].split(); vecs = list(map(int, toks)); ordv = list(map(int, open(K.ipf(E['order'])).read().split()))
    lab = {vecs[o]: i for i, o in enumerate(ordv)}; HT = []
    for ln in open(frontier):
        k, pre = ln.split(); pl = [lab[int(v)] for v in pre.split(',')]
        h = (len(pl) << 1) | (pl[-1] << 6)
        for i, l in enumerate(pl): h |= l << (13 + 7 * i)
        HT.append(h)
    return HT

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cap'); ap.add_argument('out'); ap.add_argument('pkgs', nargs='+')
    ap.add_argument('--tools'); ap.add_argument('--heavy-only', action='store_true'); ap.add_argument('--threads', type=int, default=14)
    ap.add_argument('--range-only', action='store_true', help='stop at the root range (no #e1groot): the classes h<c>, whose class modules are the class tier\'s')
    ap.add_argument('--root-only', action='store_true', help='the heavy jobs\' ranges were built by earlier --heavy-only runs (deterministic names); '
                    'only the light ranges, the root range and the root are generated')
    ap.add_argument('--heavy-jobs', help='with --root-only: the cap\'s heavy jobs (wave1_packages_heavy.jsonl)')
    a = ap.parse_args()
    out = os.path.abspath(a.out); os.makedirs(out, exist_ok=True)
    K.configure(out=out, tools=a.tools)   # first: with --tools every input comes from TOOLS/ip (kjlib's defaults are the development trees)
    if a.cap.startswith('h'): K.load_class_contexts()
    cap = a.cap if a.cap in K.EMIT else 'c' + a.cap; C = cap[1:]
    K.set_format(cap)
    K.set_package('KC' if cap.startswith('h') else 'KJ')   # (creates OUTDIR/src/<package>: configure() no longer does)
    man = out + '/agg_manifest.jsonl'; open(man, 'w').close()
    light, heavy = [], {}
    for d in a.pkgs:
        s = json.load(open(os.path.join(d, 'DONE')))
        if s['cap'] not in (cap, C): continue
        J = s.get('heavy', -1)
        assert len(s['pubs']) == 1, (d, s['pubs'])
        mod, thm = s['pubs'][0]
        (heavy.setdefault(J, []) if J >= 0 else light).append((thm, s['a'], s['b'] - s['a'], mod))
    order = []; tops = []
    IPN, SLN, OKN, IMPS = K.CFG[cap]
    if a.root_only:   # the heavy jobs' [J, J+1) ranges exist (agg<C>h<J>_R); take their names, generate nothing for them
        Js = [json.loads(l)['job'] for l in open(a.heavy_jobs) if l.strip() and json.loads(l)['cap'] in (C, cap)]
        tops = [(K.PK + '.agg%sh%d.R.ok' % (C, J), J, 1, K.PK + '.agg%sh%d_R' % (C, J)) for J in Js]
        heavy = {}
    for J, ch in sorted(heavy.items()):
        ch.sort(key=lambda c: c[1]); hctx = K.heavy_context(cap, J)
        fr = K.ipf(K.EMIT[hctx]['frontier']); n = sum(1 for _ in open(fr))
        cov = 0
        for c in ch: assert c[1] == cov, ('heavy job %d: sub-jobs not contiguous at %d' % (J, cov)); cov += c[2]
        if cov != n: print('heavy job %d: packages cover %d of %d sub-jobs; skipped' % (J, cov, n)); continue
        # the giant's sub-job table and top trace, by heavy_context (c436/c422: KH.S<C>_<J>, subtop<C>/; classes: KCH.S<c>_<J>, subtoph<c>/)
        name = 'agg%sh%d' % (C, J); tbl = K.EMIT[hctx]['tbl']; tblm = K.EMIT[hctx]['tblmod']
        (rthm, ra, rm, rmod), o = agg_tree(hctx, name, tbl, tblm, ch, man, '%s/h%d' % (cap, J)) if len(ch) > 1 else ((ch[0][0], 0, n, ch[0][3]), [])
        order += o
        trace = K.ipf(K.EMIT[hctx]['subtop'])
        pfx, top = chain_files(cap, name, trace, headers(fr, cap))
        open(K.MD + '%s_Top.lean' % name, 'w').write('\n'.join(K.header(cap, priv=[tblm, rmod]) + [
            '/-! # heavy job %d of %s: its top chain (depth 6 to 10, %d blocks) glued to its %d sub-jobs -/' % (J, cap, len(top), n),
            '#%stop %s.%s.Top "%s.bin" "%s_OF.bin" "%s_WT.bin" "%s_units.txt" %s %s %s %s %d %s' % (K.F['cmd'], K.PK, name, pfx, pfx, pfx, pfx, IPN, SLN, OKN, tbl, n, rthm),
            '#kax ' + K.PK + '.%s.Top.job' % name, '#kkey "%s/%d" "%s/%d"' % (cap, J, cap, J), '']))
        K.manifest([{'module': K.PK + '.%s_Top' % name, 'tier': cap, 'kind': 'top', 'pred_kernel_s': round(K.F['MS_NODE'] * 150 * len(top) / 1000.0, 1),
                     'pred_anon_gb': 1.0, 'input_bytes': 0}], man)
        tbl6 = K.EMIT[cap]['tbl']; tbl6m = K.EMIT[cap]['tblmod']   # the cap's job table: namespace (command) and module (import)
        open(K.DD + K.PK + '_%s_R.lst' % name, 'w').write('@' + K.PK + '.%s.Top.job\n' % name)
        open(K.MD + '%s_R.lean' % name, 'w').write('\n'.join(K.header(cap, extra_pub=[tbl6m], priv=[K.PK + '.%s_Top' % name]) + [
            '#%sjobs %s.%s.R "%s" %s %s %s %s %d' % (K.F['cmd'], K.PK, name, K.R(K.DD + K.PK + '_%s_R.lst' % name), IPN, SLN, OKN, tbl6, J),
            '#kax ' + K.PK + '.%s.R.ok' % name, '#kkey "%s/%d" "%s/%d"' % (cap, J, cap, J), '']))
        K.manifest([{'module': K.PK + '.%s_R' % name, 'tier': cap, 'kind': 'leaf-range', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.5, 'input_bytes': 0}], man)
        order += [K.PK + '.%s_Top' % name, K.PK + '.%s_R' % name]; tops.append((K.PK + '.%s.R.ok' % name, J, 1, K.PK + '.%s_R' % name))
    if not a.heavy_only and cap == 'ptc':
        # the point tier: the root range over E1P.Rptc_HT (2352 jobs), then the point lemma from HPt.C492 (HPt build)
        allr = sorted(light, key=lambda c: c[1]); cov = 0
        for c in allr: assert c[1] == cov, 'ptc: ranges not contiguous at %d' % cov; cov += c[2]
        N = sum(1 for _ in open(K.ipf(K.EMIT[cap]['frontier'])))
        assert cov == N, 'ptc: the ranges cover %d of %d jobs' % (cov, N)
        tbl = K.EMIT[cap]['tbl']; tmod = K.EMIT[cap]['tblmod']
        (rthm, _, _, rmod), o = agg_tree(cap, 'aggptc', tbl, tmod, allr, man, cap) if len(allr) > 1 else ((allr[0][0], 0, N, allr[0][3]), [])
        order += o
        open(K.MD + 'aggptc_Point.lean', 'w').write('\n'.join(['module', 'public import HPt.C492', 'public import E1PK.ChainF', 'import %s' % rmod,
            'meta import KMod.Units', 'meta import KMod.Audit',
            '/-! # The point lemma `ClassLB 492 21` from the point tier\'s %d jobs (their root range %s) and `HPt.C492.classLB_K` -/' % (N, rthm),
            'open E1PS RT HC',
            '#kpubterm KJ.aggptc.point : ∀ (_ : RRAll) (_ : ∀ p ∈ T_K3eD_Cls.RL, p.1 ≠ 492 → ClassLB p.1 p.2), ClassLB 492 21 :=',
            '  fun hrr hCap => HPt.C492.classLB_K hrr hCap (E1PS.range_all _ %d %s)' % (N, rthm),
            '#kax ' + K.PK + '.aggptc.point', '#kkey "ptc" "ptc"', '']))
        K.manifest([{'module': K.PK + '.aggptc_Point', 'tier': cap, 'kind': 'root', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.6, 'input_bytes': 0}], man)
        order.append(K.PK + '.aggptc_Point')
    elif not a.heavy_only:
        allr = sorted(light + tops, key=lambda c: c[1]); cov = 0
        for c in allr: assert c[1] == cov, 'cap %s: ranges not contiguous at %d' % (cap, cov); cov += c[2]
        N = sum(1 for _ in open(K.ipf(K.EMIT[cap]['frontier'])))
        assert cov == N, 'cap %s: the ranges cover %d of %d jobs' % (cap, cov, N)
        tbl6 = K.EMIT[cap]['tbl']
        tbl6m = K.EMIT[cap]['tblmod']
        (rthm, _, _, rmod), o = agg_tree(cap, 'agg%s' % C, tbl6, tbl6m, allr, man, cap) if len(allr) > 1 else ((allr[0][0], 0, N, allr[0][3]), [])
        order += o
    if not a.heavy_only and cap != 'ptc' and not a.range_only:
        # the root chain: DUMPONLY from the IP's root to depth 6
        rd = K.RUNDIR[cap] + 'roottrace_%s' % C; os.makedirs(rd, exist_ok=True)
        if not glob.glob(rd + '/top_*_top.bin'):
            E = K.EMIT[cap]; lp = ('LD_LIBRARY_PATH=%s ' % K.LIBPATH) if K.LIBPATH else ''
            subprocess.run('cd %s && %sDUMPFRONTIER=fr.txt DUMPONLY=1 %s %s --order %s %s --threads 1 --frontier 6 --cert top --state st.txt --out /dev/null > run.log 2>&1'
                           % (rd, lp, K.BIN['lineenum'], K.ipf(E['ip']), K.ipf(E['order']), K.emit_opts(cap)), shell=True, check=True)
        pfx, top = chain_files(cap, 'agg%s_root' % C, glob.glob(rd + '/top_*_top.bin')[0], headers(K.ipf(K.EMIT[cap]['frontier']), cap))
        hdr = K.header(cap, extra_pub=[tbl6m], priv=[rmod]); hdr.insert(hdr.index('meta import KMod.Units'), 'meta import E1GK.RootCmd')
        open(K.MD + 'agg%s_Root.lean' % C, 'w').write('\n'.join(hdr + [
            '/-! # the root level of %s: the chain from the IP\'s root to depth 6 (%d blocks), glued to its %d jobs -/' % (cap, len(top), N),
            '#e1groot ' + K.PK + '.agg%s.Root "%s.bin" "%s_OF.bin" "%s_WT.bin" "%s_units.txt" %s %s %s %s %d %s' % (C, pfx, pfx, pfx, pfx, IPN, SLN, OKN, tbl6, N, rthm),
            '#kax ' + K.PK + '.agg%s.Root.root' % C, '#kkey "%s" "%s"' % (cap, cap), '']))
        K.manifest([{'module': K.PK + '.agg%s_Root' % C, 'tier': cap, 'kind': 'root', 'pred_kernel_s': round(0.5 * 150 * len(top) / 1000.0 + 0.001 * N, 1),
                     'pred_anon_gb': 1.5, 'input_bytes': 0}], man)
        order.append(K.PK + '.agg%s_Root' % C)
    # sched.py manifest
    internal = {json.loads(l)['module']: json.loads(l) for l in open(man) if l.strip()}
    inpkg = set(order); rows = []
    KIND = {'table': 'table', 'leaf-range': 'leafrange', 'agg': 'agg', 'top': 'top', 'root': 'root'}
    for m in order:
        src = 'src/' + m.replace('.', '/') + '.lean'; text = open(os.path.join(out, src)).read()
        imps = re.findall(r'^(?:public |meta )*import (\S+)', text, re.M)
        pub = re.findall(r'^#kax (\S+)', text, re.M); r = internal[m]
        # deps: every KJ module it imports (here or a package's pub: built first when in the same scheduler run, else prebuilt)
        rows.append({'module': m, 'src': src, 'cwd': 'src', 'tier': cap, 'kind': KIND[r['kind']], 'deps': [i for i in imps if i.startswith(K.PK + '.')],
                     'pred_s': r['pred_kernel_s'], 'pred_gb': r['pred_anon_gb'], '_pub': pub[0] if pub else None})
    imported = set(d for r in rows for d in r['deps'])
    for r in rows:
        p = r.pop('_pub')
        if r['module'] not in imported: r['pub'] = p
    with open(out + '/manifest.jsonl', 'w') as f:
        for r in rows: f.write(json.dumps(r) + '\n')
    summ = {'cap': cap, 'modules': len(rows), 'heavy_jobs': len(tops), 'pubs': [(r['module'], r['pub']) for r in rows if 'pub' in r]}
    open(out + '/DONE', 'w').write(json.dumps(summ) + '\n'); print(json.dumps(summ))

if __name__ == '__main__':
    main()
