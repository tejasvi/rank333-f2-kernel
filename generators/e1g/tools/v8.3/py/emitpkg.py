#!/usr/bin/env python3
"""emitpkg.py CAP A B OUTDIR [--threads T] [--tools DIR] [--name NAME] [--seed S] [--split D] [--heavy J] [--budget B]: one production package of the E1G context caps
(CAP 436 or 422; ptc for the point IP): jobs A .. B-1 of the cap's depth-6 frontier (the point IP's root-level frontier) as KJ
modules, emitted and generated in OUTDIR (kjlib.make_slice in package mode):
  OUTDIR/src/KJ/*.lean      the modules (E1GK.JobCmd3 / E1PQ.JobCmd; every public statement's vocabulary publicly imported)
  OUTDIR/src/data/*         their data (block literals, glue witnesses, units, job lists; read as "data/..." with cwd = src)
  OUTDIR/manifest.jsonl     konly/reh/sched.py lines: module, src, cwd, tier, kind, deps (in-package), pred_s (bit model,
                            isolated), pred_gb (DESIGN §43.6 memory model); "pub" on the package's top-level theorem(s)
  OUTDIR/kext.txt           one line per external leaf: "cap jobkey l1,..,lR F" (F: U certificate over 200 kbit, B over gen7's
                            budget, S SAT, E), in job order
  OUTDIR/inputs.sha256      sha256 of the inputs: IP, order and frontier files, binaries, this generator, and the package spec
  OUTDIR/run/               the emissions (lineenum9qe_ld5 + gen7, E1P_LEAFDELEG=66, E1P_EXTBITS=200000; leaf dumps)
  OUTDIR/DONE               written last (JSON summary)
--heavy J: A, B index the native depth-10 sub-jobs of heavy depth-6 job J (frontier ip/sub<C>/<J>.txt, table KH.S<C>_<J>).
--budget B: the range is emitted under lineenum's node budget B; a job over it stops early and is split directly with the
batched split (bounded memory), so no range emission holds a giant job whole (the un-park path: same A, B, same pub).
--split D: the range's jobs are known to be heavy (from the native counts): each is split at depth D directly, without first
emitting it whole (a 4M-leaf job takes about 13 min to emit whole).
Restart-safe: an emission that did not finish (its log does not end in DONE) is redone from scratch; the module texts are always
regenerated (they depend only on the emissions).  Deterministic: the modules depend only on the job set (jobs are sorted; the
emitter's thread order does not matter); --seed is recorded and changes nothing.  The job tables (KH.HT436, KH.HT422; the
point IP's HPt.Rptc_HT) and E1GK/E1PQ are prebuilt in the closure; HPt and E1P.Hdr are the frozen port's."""
import sys, os, re, json, hashlib, argparse, time
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kjlib as K
KIND = {'table': 'table', 'leaf-range': 'leafrange', 'agg': 'agg', 'top': 'top', 'root': 'root'}

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cap'); ap.add_argument('a', type=int); ap.add_argument('b', type=int); ap.add_argument('out')
    ap.add_argument('--threads', type=int, default=14); ap.add_argument('--tools'); ap.add_argument('--name')
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--split', type=int, default=0, help='known heavy jobs: split every job of the range at this depth directly')
    ap.add_argument('--heavy', type=int, default=-1, help='A, B are sub-job indices of this heavy depth-6 job (its native depth-10 split)')
    ap.add_argument('--budget', type=int, default=0, help='node budget of the range emission: a job over it is split directly (batched)')
    a = ap.parse_args()
    out = os.path.abspath(a.out); os.makedirs(out, exist_ok=True)
    if os.path.exists(out + '/DONE'): os.remove(out + '/DONE')
    # first the package and the tools tree: with --tools every input comes from TOOLS/ip (kjlib's defaults are the
    # development trees, which a package build does not have; a lookup before this would see them on the development host only)
    K.configure(out=out, tools=a.tools)
    if a.cap.startswith('h'): K.load_class_contexts(); K.set_package('KC')   # the class tier's hcap classes h<c>: modules KC.*, data KC_*
    ctx = a.cap if a.cap in K.EMIT else 'c' + a.cap
    assert ctx in K.EMIT, a.cap
    if a.heavy >= 0: ctx = K.heavy_context(ctx, a.heavy)
    if os.environ.get('KJ_BSB_PAR'): K.set_bsb_par(int(os.environ['KJ_BSB_PAR']))   # batched splits: emitter runs at once (each --threads)
    if os.environ.get('KJ_BSB_BUDGET'): K.BSB_BUDGET = int(os.environ['KJ_BSB_BUDGET'])   # batched splits: lineenum's node budget
    if os.environ.get('KJ_PROC_PAR'): K.set_proc_par(int(os.environ['KJ_PROC_PAR']))   # batched splits: sub-splits in up to N child processes
    name = a.name or '%s_%d_%d' % (ctx, a.a, a.b)   # e.g. c436_135500_135550, c436h47_0_120
    logf = open(out + '/emit.log', 'a')
    def log(s): logf.write(s + '\n'); logf.flush()
    t0 = time.time()
    log('== emitpkg %s %d %d (name %s, threads %d, seed %d) %s' % (ctx, a.a, a.b, name, a.threads, a.seed, time.strftime('%Y-%m-%d %H:%M:%S')))
    order, root_thm, root_mod, rd = K.make_slice(ctx, a.a, a.b - a.a, name, a.threads, FS=a.split, log=log, budget=a.budget)
    internal = {}
    for l in open(rd + '/manifest.jsonl'):
        if l.strip(): r = json.loads(l); internal[r['module']] = r
    mods = [m for m in order if m.startswith(K.PK + '.')]
    inpkg = set(mods); rows = []; kext = []
    for m in mods:
        src = 'src/' + m.replace('.', '/') + '.lean'
        text = open(os.path.join(out, src)).read()
        imps = re.findall(r'^(?:public |meta )*import (\S+)', text, re.M)
        r = internal[m]
        pub = re.findall(r'^#kax (\S+)', text, re.M)
        rows.append({'module': m, 'src': src, 'cwd': 'src', 'tier': ctx, 'kind': KIND[r['kind']], 'deps': [i for i in imps if i in inpkg],
                     'pred_s': r['pred_kernel_s'], 'pred_gb': r['pred_anon_gb'], '_pub': pub[0] if pub else None})
        for ln in re.findall(r'^#kext (.*)$', text, re.M): kext += re.findall(r'"([^"]*)"', ln)
    imported = set(d for r in rows for d in r['deps'])
    for r in rows:
        p = r.pop('_pub')
        if r['module'] not in imported: assert p, r['module']; r['pub'] = p
    with open(out + '/manifest.jsonl', 'w') as f:
        for r in rows: f.write(json.dumps(r) + '\n')
    open(out + '/kext.txt', 'w').write(''.join(l + '\n' for l in kext))
    E = K.EMIT[ctx]
    ins = [K.ipf(E['ip']), K.ipf(E['order']), K.ipf(E['frontier'])] + [K.ipf(t[1:]) for t in E['opts'].split() if t.startswith('@')]
    ins += [K.BIN['lineenum'], K.BIN['e1pconv'], os.path.abspath(K.__file__), os.path.abspath(__file__)]
    with open(out + '/inputs.sha256', 'w') as f:
        for p in ins: f.write('%s  %s\n' % (sha(p), p))
        f.write('# spec %s %d %d name=%s seed=%d split=%d heavy=%d budget=%d bsb_budget=%d extbits=%d heavy_s=%.1f\n' % (ctx, a.a, a.b, name, a.seed, a.split, a.heavy, a.budget, K.BSB_BUDGET, K.EXTBITS, K.HEAVY_S))
    pubs = [(r['module'], r['pub']) for r in rows if 'pub' in r]
    summ = {'cap': ctx if a.heavy < 0 else (a.cap if a.cap in K.EMIT else 'c' + a.cap), 'heavy': a.heavy, 'split': a.split, 'budget': a.budget, 'a': a.a, 'b': a.b, 'name': name, 'modules': len(rows), 'pred_s': round(sum(r['pred_s'] for r in rows), 1),
            'pred_gb_max': max(r['pred_gb'] for r in rows), 'pubs': pubs, 'kext': len(kext), 'secs': round(time.time() - t0, 1)}
    open(out + '/DONE', 'w').write(json.dumps(summ) + '\n')
    log('== done: ' + json.dumps(summ))
    print(json.dumps(summ))

if __name__ == '__main__':
    main()
