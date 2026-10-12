#!/usr/bin/env python3
"""kcagg.py C OUTDIR PKGROOT CUT.jsonl... (env KC_KJLIB_DIR (the E1G library kjlib.py), KC_GIANTS, KC_HEAVY, KC_EXTDIR): the aggregation-phase package of class h<C>, once all its packages are done.
PKGROOT/<id>/DONE (emitpkg's JSON: pubs) and PKGROOT/<id>/kext.txt per package of the cut lists.  Writes OUTDIR/src/KC/*.lean,
OUTDIR/src/data/*, OUTDIR/manifest.jsonl (sched.py: deps in this package; the package roots are prebuilt in the store) and
OUTDIR/order.txt, OUTDIR/ext.txt (the class's external leaves, the EXT tier's input format):
  per giant J (kc_heavy.jsonl): fan-in-100 aggregators over its heavy packages' ranges of KCH.S<C>_<J> (#e1gagg), its top chain
    (#e1gtop over giants/h<C>_<J>/top.bin glued to its sub-jobs), and the range [J, J+1) of E1G.R<C>_HT over that top;
  per class: fan-in-100 aggregators over all ranges of E1G.R<C>_HT (range/split packages and giant ranges), then the class module
    KC.h<C>_Class (mkclass_root: KC.h<C>.EXT, KC.h<C>.jobs, KC.h<C>.classLB)."""
import sys, os, json, struct, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kcgen, mkclass_root
K = kcgen.K
c, out, proot = sys.argv[1], os.path.abspath(sys.argv[2]), sys.argv[3]; cuts = sys.argv[4:]
ctx = 'h' + c
if os.environ.get('KC_TOOLS'): K.configure(tools=os.environ['KC_TOOLS'])   # inputs (ip/) from the E1G emitter tools tree
K.set_package('KC', src=out + '/src', data=out + '/src/data'); os.makedirs(out + '/src/data', exist_ok=True); K.load_class_contexts(); K.set_format(ctx)
E = K.EMIT[ctx]; nJ = E['nJ']; IPN, SLN, OKN, IMPS = K.CFG[ctx]; TBL, TBLMOD = E['tbl'], E['tblmod']
rows = [json.loads(l) for f in cuts for l in open(f) if l.strip()]; rows = [r for r in rows if r['cap'] == ctx]
HJ = os.environ['KC_HEAVY']
heavy = {r['job']: r for r in (json.loads(l) for l in (open(HJ) if os.path.exists(HJ) else [])) if r['cap'] == ctx}
G = os.environ['KC_GIANTS'] + '/'
man = out + '/internal.jsonl'; open(man, 'w').close(); order = []; ext = []   # kjlib rows; the scheduler's manifest is manifest.jsonl
def pub_of(r):
    d = json.load(open('%s/%s/DONE' % (proot, r['id'])))
    assert len(d['pubs']) == 1, ('package with several pubs', r['id']); return d['pubs'][0]   # [module, theorem]
def kext_of(r):
    f = '%s/%s/kext.txt' % (proot, r['id'])
    return [l.split() for l in open(f) if l.strip()] if os.path.exists(f) else []
def agg(name, children, tbl, tblmod):
    """fan-in-100 #e1gagg over consecutive children (theorem, a, m, module); returns the root (theorem, a, m, module)"""
    lvl = 0
    while len(children) > 1:
        nxt = []
        for i in range(0, len(children), 100):
            ch = children[i:i + 100]; nm = '%s_C%d_%d' % (name, lvl, i // 100)
            open(K.DD + 'KC_%s.lst' % nm, 'w').write('\n'.join('%s %d %d' % (x[0], x[1], x[2]) for x in ch) + '\n')
            a = ch[0][1]; M = sum(x[2] for x in ch)
            open(K.MD + '%s.lean' % nm, 'w').write('\n'.join(K.header(ctx, extra_pub=[tblmod], priv=[x[3] for x in ch]) + [
                '#%sagg KC.%s "%s" %s %s %s' % (K.F['cmd'], nm, K.R(K.DD + 'KC_%s.lst' % nm), IPN, SLN, tbl),
                '#kax KC.%s.ok' % nm, '#kkey "%s/%d" "%s/%d"' % (name, a, name, a + M - 1), '']))
            K.manifest([{'module': 'KC.%s' % nm, 'tier': ctx, 'kind': 'agg', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45, 'input_bytes': 0,
                         'imports': IMPS + [K.F['hdr'], tblmod] + [x[3] for x in ch]}], man)
            order.append('KC.%s' % nm); nxt.append(('KC.%s.ok' % nm, a, M, 'KC.%s' % nm))
        children = nxt; lvl += 1
    return children[0]
ranges = []
for r in sorted([r for r in rows if r['kind'] in ('range', 'split')], key=lambda r: r['a']):
    m, t = pub_of(r); ranges.append((t, r['a'], r['b'] - r['a'], m))
    for x in kext_of(r): ext.append((r['a'], x))
for J in sorted(heavy):
    hr = sorted([r for r in rows if r['kind'] in ('heavy-sub', 'heavy-split') and r['job'] == J], key=lambda r: r['a'])
    nS = heavy[J]['subjobs']; assert hr[0]['a'] == 0 and hr[-1]['b'] == nS and all(hr[i]['a'] == hr[i - 1]['b'] for i in range(1, len(hr))), ('giant coverage', J)
    ktbl = 'KCH.S%s_%d' % (c, J)
    ch = []
    for r in hr:
        m, t = pub_of(r); ch.append((t, r['a'], r['b'] - r['a'], m))
        for x in kext_of(r): ext.append((J, x))
    gname = '%s_g%d' % (ctx, J)
    rt = agg(gname, ch, ktbl, ktbl)
    # the giant's top chain glued to its sub-jobs (the table's headers), from the DUMPONLY run of giants/
    pre = [l.split()[1] for l in open(G + '%s_%d/fr.txt' % (ctx, J)) if l.strip()]; HTs = [K.hdr_of_prefix(ctx, p) for p in pre]
    b = open(G + '%s_%d/top.bin' % (ctx, J), 'rb').read(); n = struct.unpack('<I', b[:4])[0]; i = 4; top = []
    for _ in range(n):
        ln = struct.unpack('<I', b[i:i + 4])[0]; i += 4; top.append(int.from_bytes(b[i:i + ln], 'little')); i += ln
    pfx = K.DD + 'KC_%s_top' % gname
    K.wrlits(pfx + '.bin', top); K.wrW(pfx, K.witnesses(top, HTs))
    with open(pfx + '_units.txt', 'w') as f:
        for k in range(len(top)): f.write('%d\n' % k)
    tmod = 'KC.%s_Top' % gname
    open(K.MD + '%s_Top.lean' % gname, 'w').write('\n'.join(K.header(ctx, priv=[ktbl, rt[3]]) + [
        '/-! # giant root job %d of class %s: its top chain (depth %d), glued to its %d sub-jobs (KCH.S%s_%d) -/' % (J, c, heavy[J]['depth'], nS, c, J),
        '#%stop KC.%s.Top "%s.bin" "%s_OF.bin" "%s_WT.bin" "%s_units.txt" %s %s %s %s %d %s' % (K.F['cmd'], gname, K.R(pfx), K.R(pfx), K.R(pfx), K.R(pfx), IPN, SLN, OKN, ktbl, nS, rt[0]),
        '#kax KC.%s.Top.job' % gname, '#kkey "%s/%d" "%s/%d"' % (ctx, J, ctx, J), '']))
    K.manifest([{'module': tmod, 'tier': ctx, 'kind': 'top', 'pred_kernel_s': round(sum(K.F['MS_NODE'] * 150 for _ in top) / 1000.0, 1), 'pred_anon_gb': 1.0,
                 'input_bytes': os.path.getsize(pfx + '.bin'), 'imports': IMPS + [K.F['hdr'], ktbl, rt[3]]}], man)
    order.append(tmod)
    # the range [J, J+1) of the class table over the top
    lname = '%s_gr%d' % (ctx, J)
    open(K.DD + 'KC_%s.lst' % lname, 'w').write('@KC.%s.Top.job\n' % gname)
    open(K.MD + '%s.lean' % lname, 'w').write('\n'.join(K.header(ctx, extra_pub=[TBLMOD], priv=[tmod]) + [
        '#%sjobs KC.%s "%s" %s %s %s %s %d' % (K.F['cmd'], lname, K.R(K.DD + 'KC_%s.lst' % lname), IPN, SLN, OKN, TBL, J),
        '#kax KC.%s.ok' % lname, '#kkey "%s/%d" "%s/%d"' % (ctx, J, ctx, J), '']))
    K.manifest([{'module': 'KC.%s' % lname, 'tier': ctx, 'kind': 'leaf-range', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45, 'input_bytes': 0,
                 'imports': IMPS + [K.F['hdr'], TBLMOD, tmod]}], man)
    order.append('KC.%s' % lname); ranges.append(('KC.%s.ok' % lname, J, 1, 'KC.%s' % lname))
ranges.sort(key=lambda x: x[1])
assert ranges[0][1] == 0 and all(ranges[i][1] == ranges[i - 1][1] + ranges[i - 1][2] for i in range(1, len(ranges))) and ranges[-1][1] + ranges[-1][2] == nJ, 'class coverage'
root = agg(ctx, ranges, TBL, TBLMOD)
ext.sort(key=lambda x: x[0]); pls = [K.plpack(list(map(int, x[1][2].split(',')))) for x in ext]
open(out + '/ext.txt', 'w').write(''.join('%s %s %s %d\n' % (x[1][1], x[1][2], x[1][3] if len(x[1]) > 3 else '?', p) for x, p in zip(ext, pls)))
# KC.h<C>.EXT's literal exactly (one decimal packed prefix per line, in the list's order), for the EXT top x<c> (mkexttop.py --order)
open(out + '/ext_pl.txt', 'w').write(''.join('%d\n' % p for p in pls))
lifted = [root[3]] if pls else []
order.append(mkclass_root.write(c, root[0], root[3], lifted, pls, man))
open(out + '/order.txt', 'w').write('\n'.join(order) + '\n')
# the sched.py manifest of the aggregation package (deps from the sources; the class's package roots are prebuilt in the store)
import re
mrows = {}
for l in open(man):
    if l.strip(): r = json.loads(l); mrows[r['module']] = r
inpkg = set(order)
KIND = {'table': 'table', 'leaf-range': 'leafrange', 'agg': 'agg', 'top': 'top', 'class': 'class'}
with open(out + '/manifest.jsonl', 'w') as f:   # the scheduler's fields, as emitpkg writes them
    for m in order:
        src = 'src/' + m.replace('.', '/') + '.lean'; text = open(out + '/' + src).read()
        imps = re.findall(r'^(?:public |meta )*import (\S+)', text, re.M); r = mrows[m]
        u = {'module': m, 'src': src, 'cwd': 'src', 'tier': ctx, 'kind': KIND[r['kind']], 'deps': [i for i in imps if i in inpkg],
             'pred_s': r['pred_kernel_s'], 'pred_gb': max(0.45, r['pred_anon_gb'])}
        if r['kind'] == 'class': u['pub'] = 'KC.%s.classLB' % ctx
        f.write(json.dumps(u) + '\n')
# the build LEAN_PATH: the store first, then the closure roots (HCapK, KCH, port, E1GK, KMod, Mathlib, toolchain) from KC_LPATH_COMMON
LPC = os.environ.get('KC_LPATH_COMMON')
if LPC and os.path.exists(LPC): open(out + '/lpath_common.txt', 'w').write('{STORE}:' + open(LPC).read().strip() + '\n')
XD = os.environ.get('KC_EXTDIR', os.path.join(out, 'ext'))
try:
    os.makedirs(XD, exist_ok=True); open(XD + '/%s.txt' % ctx, 'w').write(open(out + '/ext.txt').read())
    open(XD + '/%s_pl.txt' % ctx, 'w').write(open(out + '/ext_pl.txt').read())
except OSError: pass
print('h%s aggregation: %d ranges (%d giants), %d modules, %d external leaves, class module KC.h%s_Class' % (c, len(ranges), len(heavy), len(order), len(pls), c))
