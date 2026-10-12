"""kcgen.py: plan-then-emit generation of big (sub)jobs for the class tier, on the E1G library kjlib.py (with build_split_batched).

build_split_planned(ctx, prefix, name, man, depth, threads, …) has build_split's interface and return value, but
  1. PLANS first, by search only (cheap: lineenum without E1P emission runs ~100k st-nodes/s per thread): each split level is one
     DUMPONLY run (sub-job frontier + top trace, kjlib.split_level) and one count pass over all its sub-jobs (`--state` gives
     exact st-nodes and leaves per sub-job; `--budget count_budget --heavy` stops giants early); a sub-job over the count budget,
     or estimated over `limit` from its counts, is planned as a split `step` levels deeper (recursively), the rest as jobs;
  2. EMITS the planned jobs in batches sized by their exact leaves (<= batch_leaves) and estimated seconds (<= batch_s), with
     E1P emission (gen7), each batch's records streamed in a worker process (a process pool: the per-job module writing is
     Python, so threads would serialise on the GIL); a job whose bit-model prediction after emission exceeds over_factor x limit
     is split after all (build_split_batched); heavy leaves apart (heavy_split), as kjlib;
  3. writes, bottom-up, each split node's sub-job table, range tree (300 s cuts, fan-in 100) and top (#e1gtop).
Emitter runs at once: kjlib.BSB_PAR (semaphore); Python workers: `workers`.  No wasted E1P work on giants (only cheap count passes
are stopped by the budget), no oversized batch, and Python and lineenum memory stay bounded."""
import os, sys, glob, json, struct, subprocess, threading, math
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor
# the E1G library kjlib.py: KC_KJLIB_DIR (e.g. the emitter tools tree's py/)
sys.path.insert(0, os.environ['KC_KJLIB_DIR'])
import kjlib as K

def count_pass(ctx, rd, budget, threads):
    """search only over all sub-jobs of rd/fr.txt: {k: (st-nodes, leaves)} for those finished, and the list of those over budget"""
    E = K.EMIT[ctx]; ni = max(0, 10 - os.nice(0)); lp = ('LD_LIBRARY_PATH=%s ' % K.LIBPATH) if K.LIBPATH else ''
    if not os.path.exists(rd + '/count.ok'):
        for f in ('st_count.txt', 'heavy_count.txt'):
            if os.path.exists(rd + '/' + f): os.remove(rd + '/' + f)
        with K._BSB_SEM:
            subprocess.run('cd %s && %snice -n %d %s %s --order %s %s --threads %d --frontierfile fr.txt --state st_count.txt --out /dev/null '
                           '--budget %d --heavy heavy_count.txt > count.log 2>&1' % (rd, lp, ni, K.BIN['lineenum'], K.ipf(E['ip']), K.ipf(E['order']),
                                                                                    K.emit_opts(ctx), threads, budget), shell=True, check=True)
        open(rd + '/count.ok', 'w').write('ok\n')
    cnt = {}
    for l in open(rd + '/st_count.txt'):
        a = l.split()
        if len(a) >= 3: cnt[int(a[0])] = (int(a[1]), int(a[2]))
    pre = [l.split()[1] for l in open(rd + '/fr.txt') if l.strip()]; kof = {p: k for k, p in enumerate(pre)}
    hv = [kof[l.strip()] for l in open(rd + '/heavy_count.txt') if l.strip()] if os.path.exists(rd + '/heavy_count.txt') else []
    return pre, cnt, hv

def plan(ctx, prefix, depth, name, threads, limit, count_budget, step, ms_leaf, log=None):
    """the planned split tree under prefix: {name, prefix, depth, rd, pre, kind: [('job', nodes, leaves) | ('split', node)]}"""
    rd = K.RUNDIR[ctx] + 'split_%s' % name
    K.split_level(ctx, prefix, depth, rd)
    pre, cnt, hv = count_pass(ctx, rd, count_budget, threads)
    assert sorted(list(cnt) + hv) == list(range(len(pre))), ('count pass', name, len(pre), len(cnt), len(hv))
    kinds = [None] * len(pre); subs = []
    for k in range(len(pre)):
        if k in cnt:
            n, l = cnt[k]
            if (K.F['MS_NODE'] * n + ms_leaf * l) / 1000.0 <= limit: kinds[k] = ('job', n, l); continue
        subs.append(k)
    # children planned concurrently (each is DUMPONLY + count passes, under the emitter semaphore)
    res = {}
    def one(k): res[k] = plan(ctx, pre[k], depth + step, '%s_s%d' % (name, k), threads, limit, count_budget, step, ms_leaf, log)
    with ThreadPoolExecutor(max(1, min(len(subs), 2 * K.BSB_PAR))) as ex: list(ex.map(one, subs))
    for k in subs: kinds[k] = ('split', res[k])
    if log: log('  plan %s (depth %d): %d sub-jobs, %d jobs (%d leaves), %d split' % (name, depth, len(pre), sum(1 for x in kinds if x[0] == 'job'),
                                                                                  sum(x[2] for x in kinds if x[0] == 'job'), len(subs)))
    return dict(name=name, prefix=prefix, depth=depth, rd=rd, pre=pre, kinds=kinds)

def walk(node):
    yield node
    for x in node['kinds']:
        if x[0] == 'split': yield from walk(x[1])

def plan_stats(node, ms_leaf):
    J = [(x[1], x[2]) for nd in walk(node) for x in nd['kinds'] if x[0] == 'job']
    return dict(splits=sum(1 for _ in walk(node)), jobs=len(J), nodes=sum(n for n, _ in J), leaves=sum(l for _, l in J),
                est_s=sum(K.F['MS_NODE'] * n + ms_leaf * l for n, l in J) / 1000.0)

# ---- worker side (a process pool: kjlib's state is re-established in each worker) ----
_W = {}
def winit(cfg):
    K.set_package(cfg['PK'], src=cfg['SRC'], data=cfg['DATA']); K.load_class_contexts()
    for c, d in cfg['RUNDIR'].items(): K.RUNDIR[c] = d
    K.set_format(cfg['ctx']); _W.update(cfg)
def wbatch(args):
    """process one emitted batch: per job (streamed) a job chain, a heavy-leaf split, or 'over' (to be split after all);
    manifest rows of heavy splits go to the batch's own manifest part; returns (results, lifted modules added, ext by job)"""
    brd, name, ks, HT, K_, hi, limit, over_factor = args
    ctx = _W['ctx']; man = brd + '/manifest.part'; open(man, 'w').close()
    before = set(K.LIFTED); cs = K.job_costs(brd); ex = K.read_ext(brd); out = {}
    for k, lits in K.iter_e1p(sorted(glob.glob(brd + '/e_*_t*.e1p')), skip=lambda ix: cs.get(ix, (0,))[0] > over_factor * limit):
        c = cs[k][0]
        if lits is None: out[k] = ('over', c); continue
        assert K.mode0_header(lits[0]) == HT[k], ('header', name, k)
        if K.heavy_leaves(lits):
            thm, tmod, so, (hc, mx, nb, n) = K.heavy_split(ctx, '%s_x%d' % (name, k), lits, man, K_, hi, ext=ex.get(k))
            IMPS = K.CFG[ctx][3]
            K.manifest([{'module': tmod, 'tier': ctx, 'kind': 'top', 'lifted': tmod in K.LIFTED, 'pred_kernel_s': round(max(c - hc, 1.0), 1),
                         'pred_anon_gb': K.pred_gb_s(mx), 'input_bytes': nb, 'imports': IMPS + ['E1G.Hdr']}], man)
            out[k] = ('heavy', '@' + thm, tmod, so + [tmod]); continue
        line, nb, n, mx = K.write_job(K.DD + K.PK + '_%s_j%d' % (name, k), lits, K_, ext=ex.get(k))
        out[k] = ('job', line, nb, mx, c)
    missing = [k for k in ks if k not in out]
    assert not missing, ('batch records missing', name, missing[:5])
    for f in glob.glob(brd + '/e_*_t*.e1p') + glob.glob(brd + '/leaves*_t*.txt') + glob.glob(brd + '/e_*_leafjobs_t*.bin'): os.remove(f)
    return out, sorted(set(K.LIFTED) - before), {k: v for k, v in ex.items() if k in out and out[k][0] != 'over'}

def build_split_planned(ctx, prefix, name, man, depth=None, threads=14, hi=300.0, K_=4, limit=600.0, batch_leaves=2.0e6, batch_s=20000.0,
                        count_budget=5000000, step=2, ms_leaf=5.0, over_factor=2.0, workers=6, log=None):
    """plan (search only), emit in batches by exact counts (process pool), write the tree bottom-up; returns as build_split"""
    IPN, SLN, OKN, IMPS = K.CFG[ctx]
    depth = depth or len(prefix.split(',')) + step
    root = plan(ctx, prefix, depth, name, threads, limit, count_budget, step, ms_leaf, log)
    if log: log('  planned %s: %s' % (name, plan_stats(root, ms_leaf)))
    # batches over every node's planned jobs
    batches = []
    for nd in walk(root):
        nd['HT'] = [K.hdr_of_prefix(ctx, p) for p in nd['pre']]
        js = [k for k, x in enumerate(nd['kinds']) if x[0] == 'job']; i = 0
        while i < len(js):
            b, L, S = [], 0, 0.0
            while i < len(js):
                n, l = nd['kinds'][js[i]][1:3]; s = (K.F['MS_NODE'] * n + ms_leaf * l) / 1000.0
                if b and (L + l > batch_leaves or S + s > batch_s or len(b) >= 4096): break
                b.append(js[i]); L += l; S += s; i += 1
            batches.append((nd, b))
    cfg = dict(PK=K.PK, SRC=os.path.dirname(K.MD.rstrip('/')), DATA=K.DD, RUNDIR=dict(K.RUNDIR), ctx=ctx)
    results = {}; errs = []
    with ProcessPoolExecutor(workers, initializer=winit, initargs=(cfg,)) as pp:
        def run(nb):
            nd, ks = nb; brd = nd['rd'] + '/b%d' % ks[0]
            try:
                if not K.emission_done(brd):
                    K.reset_emission(brd)
                    open(brd + '/jobs.txt', 'w').write('\n'.join(map(str, ks)) + '\n')
                    mxn = max(nd['kinds'][k][1] for k in ks)
                    with K._BSB_SEM: K.emit(ctx, brd, '--frontierfile %s/fr.txt --jobs jobs.txt --budget %d --heavy heavy.txt' % (nd['rd'], max(2 * mxn, 100000)), threads)
                hv = [l.strip() for l in open(brd + '/heavy.txt') if l.strip()] if os.path.exists(brd + '/heavy.txt') else []
                assert not hv, ('emission budget hit despite the plan', nd['name'], hv[:3])
                out, lifted, ex = pp.submit(wbatch, (brd, nd['name'], ks, nd['HT'], K_, hi, limit, over_factor)).result()
                results[(nd['name'], ks[0])] = (out, lifted, ex, brd)
                if log: log('  emitted %s b%d: %d jobs' % (nd['name'], ks[0], len(ks)))
            except BaseException as e:
                errs.append((nd['name'], ks[0], repr(e)))
        with ThreadPoolExecutor(max(1, 2 * K.BSB_PAR)) as tp: list(tp.map(run, batches))
    if errs: raise RuntimeError('build_split_planned %s: %s' % (name, errs[:3]))
    # merge the workers' state
    per = {}
    for (nm, k0), (out, lifted, ex, brd) in results.items():
        K.LIFTED.update(lifted); per.setdefault(nm, ({}, {}))
        per[nm][0].update(out); per[nm][1].update(ex)
        part = brd + '/manifest.part'
        if os.path.exists(part):
            with K._MAN_LOCK_G:
                with open(man, 'a') as f: f.write(open(part).read())
    # bottom-up: tables, ranges, tops
    def finish(nd):
        out, EXT = per.get(nd['name'], ({}, {}))
        nJ = len(nd['pre']); HT = nd['HT']; order = []
        W = 128 if max(h.bit_length() for h in HT) <= 128 else 256
        with open(K.DD + K.PK + '_%s_SHT.bin' % nd['name'], 'wb') as f:
            for h in HT: f.write(h.to_bytes(W // 8, 'little'))
        tbl = K.PK + '.%s.SHT' % nd['name']; tmod_s = K.PK + '.%s_SHT' % nd['name']
        open(K.MD + '%s_SHT.lean' % nd['name'], 'w').write('\n'.join(['module', 'public import RT.Load',
            '/-! # Sub-job header table of split job %s (%d sub-jobs, mode-0 prefix headers), public data -/' % (nd['name'], nJ),
            '#rttablew %s "%s" 64 %d' % (tbl, K.R(K.DD + K.PK + '_%s_SHT.bin' % nd['name']), W), '']))
        order.append(tmod_s)
        K.manifest([{'module': tmod_s, 'tier': ctx, 'kind': 'table', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45, 'input_bytes': W // 8 * nJ,
                     'imports': ['RT.Load']}], man)
        lst, costs, inb, mxs, imp = [], [], [], [], []
        for k in range(nJ):
            x = nd['kinds'][k]
            if x[0] == 'split':
                thm, tmod, so, st = finish(x[1]); order += so
                lst.append('@' + thm); inb.append(0); mxs.append(0.0); costs.append(1.0); imp.append(tmod); continue
            r = out[k]
            if r[0] == 'over':   # predicted over over_factor x limit after emission: split after all (budget-based)
                thm, tmod, so, st = K.build_split_batched(ctx, nd['pre'][k], '%s_s%d' % (nd['name'], k), man, nd['depth'] + step, threads, hi, K_, limit, log=log)
                order += so; lst.append('@' + thm); inb.append(0); mxs.append(0.0); costs.append(1.0); imp.append(tmod); continue
            if r[0] == 'heavy':
                order += r[3]; lst.append(r[1]); inb.append(0); mxs.append(0.0); costs.append(1.0); imp.append(r[2]); continue
            lst.append(r[1]); inb.append(r[2]); mxs.append(r[3]); costs.append(r[4]); imp.append(None)
        exts = {k: EXT[k] for k in EXT if not lst[k].startswith('@')}
        root_child, root_mod, ro, ng = K.range_tree(ctx, nd['name'], tbl, tmod_s, 0, lst, costs, inb, mxs, imp, man, hi, what='sub-jobs', exts=exts)
        order += ro
        b = open(nd['rd'] + '/top.bin', 'rb').read(); n = struct.unpack('<I', b[:4])[0]; i = 4; top = []
        for _ in range(n):
            ln = struct.unpack('<I', b[i:i + 4])[0]; i += 4; top.append(int.from_bytes(b[i:i + ln], 'little')); i += ln
        pfx = K.DD + K.PK + '_%s_top' % nd['name']
        K.wrlits(pfx + '.bin', top); K.wrW(pfx, K.witnesses(top, HT))
        with open(pfx + '_units.txt', 'w') as f:
            for k in range(len(top)): f.write('%d\n' % k)
        tcost = sum(K.F['MS_NODE'] * 150 for _ in top) / 1000.0
        isl = [False] * len(top)
        open(K.MD + '%s_Top.lean' % nd['name'], 'w').write('\n'.join(K.header(ctx, priv=[tmod_s, root_mod]) + [
            '/-! # the top chain of split job %s (root %s, cut at depth %d), glued to its %d sub-jobs (planned) -/' % (nd['name'], nd['prefix'], nd['depth'], nJ),
            '#%stop %s.%s.Top "%s.bin" "%s_OF.bin" "%s_WT.bin" "%s_units.txt" %s %s %s %s %d %s' % (K.F['cmd'], K.PK, nd['name'], K.R(pfx), K.R(pfx), K.R(pfx), K.R(pfx),
                                                                                              IPN, SLN, OKN, tbl, nJ, root_child),
            '#kax ' + K.PK + '.%s.Top.job' % nd['name'], '#kkey "%s" "%s"' % (nd['name'], nd['name']), '']))
        K.manifest([{'module': K.PK + '.%s_Top' % nd['name'], 'tier': ctx, 'kind': 'top', 'pred_kernel_s': round(tcost, 1),
                     'pred_anon_gb': K.pred_gb_s(max(K.unit_s(top, [k], isl) for k in range(len(top)))),
                     'input_bytes': os.path.getsize(pfx + '.bin'), 'imports': IMPS + [K.F['hdr'], tmod_s, root_mod]}], man)
        order.append(K.PK + '.%s_Top' % nd['name'])
        if root_mod in K.LIFTED: K.LIFTED.add(K.PK + '.%s_Top' % nd['name'])
        return K.PK + '.%s.Top.job' % nd['name'], K.PK + '.%s_Top' % nd['name'], order, (sum(costs) + tcost, nJ, ng, max(costs))
    return finish(root)
