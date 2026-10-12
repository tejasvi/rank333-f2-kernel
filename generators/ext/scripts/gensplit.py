#!/usr/bin/env python3
"""gensplit.py: distributed generation of one leaf certificate with gen7pd (EXT tools v4), in gen7pc --split3's output format.

  gen_split(gen7pd, inp, args, out, workers=8, d0=2, L1=10368, B1=3000000, L2=72, B2=40000, BM=2000, maxdepth=19)

inp: the leaf line ("terms DOM"); args: generator options (--plane Q --pk 3 ...). The top (gen7pd --top d0) gives the main record
with one subtree item per unexpanded node; the items' subtrees are generated in parallel (gen7pd --sub PATH, at most L1 SAT leaves
and B1 bits each, parts split into sub-records of L2 SAT leaves / B2 bits). An item over budget (TOOBIG) is expanded: its path
joins the top's expand set and the top is regenerated (the top's nodes, and so every other item's path and state, do not change:
no hoist across the cut); only new items are generated. Writes MAIN + the PART/SUB blocks in item order + END to out. With gen7pd_eqf --eqf the MAIN line keeps the top's a0 (5th field)."""
import os, sys, subprocess, json, time
from concurrent.futures import ThreadPoolExecutor

def run(cmd, inp):
    r = subprocess.run(cmd, input=inp, capture_output=True, text=True)
    return r.stdout

def group_items(exts, cache, L1, B1):
    """runs of consecutive sibling items (same parent and step prefix, consecutive kid indices: no skip kid between) within the part
    budget (L1 SAT leaves, B1 bits, at most 32767 kids): [(first path, [paths])]"""
    runs = []
    for p in exts:
        h = cache[p].split('\n', 1)[0].split()      # PART <path> 0 <hex> <nbits> <nsat> <nsub>
        nb, ns = int(h[4]), int(h[5])
        k = p.rfind(':'); key, idx = p[:k + 1], int(p[k + 1:])
        if runs:
            r = runs[-1]
            if r['key'] == key and r['last'] + 1 == idx and r['ns'] + ns <= L1 and r['nb'] + nb <= B1 and len(r['ps']) < 32767:
                r['ps'].append(p); r['last'] = idx; r['ns'] += ns; r['nb'] += nb; continue
        runs.append(dict(key=key, last=idx, ns=ns, nb=nb, ps=[p]))
    return [(r['ps'][0], r['ps']) for r in runs]

def merge_parts(ps, cache):
    """the PART block of a range item over the single-subtree PARTs of ps (in order): their records' bits in turn, their SUB lines in turn"""
    val = 0; off = 0; ns = 0; nsub = 0; subs = []
    for p in ps:
        lines = cache[p].rstrip('\n').split('\n')
        h = lines[0].split()
        assert h[0] == 'PART' and h[1] == p and h[2] == '0', h[:3]
        val |= int(h[3], 16) << off; off += int(h[4]); ns += int(h[5]); nsub += int(h[6])
        body = [l for l in lines[1:] if l != 'END']
        assert len(body) == int(h[6]) and all(l.startswith('SUB ') for l in body)
        subs += body
    if len(ps) == 1: return cache[ps[0]].rstrip('\n').rsplit('\n', 1)[0] + '\n'
    return 'PART %s %d %x %d %d %d\n' % (ps[0], len(ps), val, off, ns, nsub) + ''.join(l + '\n' for l in subs)

def gen_split(gen, inp, args, out, workers=8, d0=3, L1=10368, B1=3000000, L2=72, B2=40000, BM=2000, maxrounds=16, log=None, kexp=2, group=False):
    t0 = time.time(); expand = []; cache = {}; rounds = 0; ef = out + '.expand'
    while True:
        rounds += 1
        open(ef, 'w').write(''.join(p + '\n' for p in expand))
        top = run([gen] + args + ['--top', str(d0), '--expand', ef, '--kexpand', str(kexp)], inp).splitlines()
        if not top or not top[0].startswith('MAIN ') or top[-1] != 'END': raise RuntimeError('top: %s' % (top[:1],))
        exts = [l[4:] for l in top[1:-1] if l.startswith('EXT ')]
        todo = [p for p in exts if p not in cache]
        def sub(p):
            return p, run([gen] + args + ['--sub', p, '--maxsat', str(L1), '--maxbits', str(B1), '--split3part', str(L2), str(B2), str(BM)], inp)
        with ThreadPoolExecutor(workers) as ex:
            for p, o in ex.map(sub, todo): cache[p] = o
        big = [p for p in exts if cache[p].startswith('TOOBIG')]
        bad = [p for p in exts if not cache[p].startswith('TOOBIG') and not cache[p].startswith('PART ')]
        if bad: raise RuntimeError('sub %s: %s' % (bad[0], cache[bad[0]][:200]))
        if log: log('round %d: %d items, %d generated, %d over budget, %.0f s' % (rounds, len(exts), len(todo), len(big), time.time() - t0))
        if not big: break
        if rounds >= maxrounds: raise RuntimeError('still %d items over budget after %d rounds' % (len(big), rounds))
        expand += big
    m = top[0].split()
    nsat = int(m[3]) + sum(int(cache[p].split('\n', 1)[0].split()[5]) for p in exts)
    if group:
        # v10: runs of consecutive sibling items become range items (gen7pd_eqf --top --group): far fewer parts
        runs = group_items(exts, cache, L1, B1)
        gf = out + '.group'
        open(gf, 'w').write(''.join('%s %d\n' % (p0, len(ps)) for p0, ps in runs if len(ps) > 1))
        top = run([gen] + args + ['--top', str(d0), '--expand', ef, '--kexpand', str(kexp), '--group', gf], inp).splitlines()
        if not top or not top[0].startswith('MAIN ') or top[-1] != 'END': raise RuntimeError('grouped top: %s' % (top[:1],))
        gx = [l.split()[1:] for l in top[1:-1] if l.startswith('EXT ')]
        if [(p, int(n)) for p, n in gx] != [(p0, len(ps)) for p0, ps in runs]: raise RuntimeError('grouped top: EXT runs differ from the groups')
        m = top[0].split()
        if int(m[4]) != len(runs): raise RuntimeError('grouped top: item count')
        with open(out, 'w') as f:
            f.write('MAIN %s %s %d %d%s\n' % (m[1], m[2], nsat, len(runs), (' ' + m[5]) if len(m) > 5 else ''))
            for p0, ps in runs: f.write(merge_parts(ps, cache))
            f.write('END\n')
        if log: log('grouped: %d items -> %d range items' % (len(exts), len(runs)))
        return dict(items=len(runs), singles=len(exts), rounds=rounds, nsat=nsat, secs=time.time() - t0)
    with open(out, 'w') as f:
        f.write('MAIN %s %s %d %d%s\n' % (m[1], m[2], nsat, len(exts), (' ' + m[5]) if len(m) > 5 else ''))   # eqf: a0 (gen7pd_eqf --top)
        for p in exts: f.write(cache[p].rstrip('\n').rsplit('\n', 1)[0] + '\n')   # the PART block without its END
        f.write('END\n')
    return dict(items=len(exts), rounds=rounds, nsat=nsat, secs=time.time() - t0)

if __name__ == '__main__':
    gen, inp, out = sys.argv[1], sys.argv[2], sys.argv[3]
    args = sys.argv[4:]
    r = gen_split(gen, inp + '\n', args, out, log=lambda s: print(s, flush=True))
    print(json.dumps(r))


def gen_split_asm(gen, inp, args, out, workers=16, d0=3, L1s=300000, B1s=100000000, NPART=10368, NSUB=72, B2=40000, BM=2000, B1=1000000,
                  maxrounds=24, log=None, kexp=1):
    """(21:3x UTC) parallel generation, gen7pc's encoding: the items (subtrees within L1s SAT leaves / B1s bits, over-budget ones expanded)
    are generated in parallel and dumped (gen7pd_eqf --sub --dump); then gen7pd_eqf --top --assemble splices them into the whole tree and
    writes gen7pc_eqf's --split3 output (grouped parts, a small main record) to out"""
    import hashlib, shutil
    t0 = time.time(); expand = []; cache = {}; rounds = 0; ef = out + '.expand'; dd = out + '.dumps'
    os.makedirs(dd, exist_ok=True)
    key = lambda p: hashlib.sha256(p.encode()).hexdigest()[:24]
    while True:
        rounds += 1
        open(ef, 'w').write(''.join(p + '\n' for p in expand))
        top = run([gen] + args + ['--top', str(d0), '--expand', ef, '--kexpand', str(kexp)], inp).splitlines()
        if not top or not top[0].startswith('MAIN ') or top[-1] != 'END': raise RuntimeError('top: %s' % (top[:1],))
        exts = [l[4:] for l in top[1:-1] if l.startswith('EXT ')]
        todo = [p for p in exts if p not in cache]
        def sub(p):
            return p, run([gen] + args + ['--sub', p, '--maxsat', str(L1s), '--maxbits', str(B1s), '--dump', os.path.join(dd, key(p))], inp)
        with ThreadPoolExecutor(workers) as ex:
            for p, o in ex.map(sub, todo): cache[p] = o.strip()
        big = [p for p in exts if cache[p].startswith('TOOBIG')]
        bad = [p for p in exts if not cache[p].startswith('TOOBIG') and not cache[p].startswith('DUMPED')]
        if bad: raise RuntimeError('sub %s: %s' % (bad[0], cache[bad[0]][:200]))
        if log: log('asm round %d: %d items, %d generated, %d over budget, %.0f s' % (rounds, len(exts), len(todo), len(big), time.time() - t0))
        if not big: break
        if rounds >= maxrounds: raise RuntimeError('still %d items over budget after %d rounds' % (len(big), rounds))
        expand += big
    ad = out + '.asm'
    shutil.rmtree(ad, ignore_errors=True); os.makedirs(ad)
    for i, p in enumerate(exts): os.link(os.path.join(dd, key(p)), os.path.join(ad, '%d.dump' % i))
    o = run([gen] + args + ['--top', str(d0), '--expand', ef, '--kexpand', str(kexp), '--assemble', ad, '--split3', str(NPART), str(NSUB),
                            '--splitB', str(B2), str(BM), str(B1)], inp)
    if not o.startswith('MAIN ') or not o.rstrip().endswith('END'): raise RuntimeError('assemble: %s' % o[:200])
    open(out, 'w').write(o)
    shutil.rmtree(ad, ignore_errors=True); shutil.rmtree(dd, ignore_errors=True)
    m = o.split('\n', 1)[0].split()
    if log: log('assembled: %s SAT leaves, %s parts, main record %s bits, %.0f s' % (m[3], m[4], m[2], time.time() - t0))
    return dict(items=len(exts), rounds=rounds, nsat=int(m[3]), parts=int(m[4]), main_bits=int(m[2]), secs=time.time() - t0)
