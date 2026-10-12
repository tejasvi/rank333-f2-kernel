#!/usr/bin/env python3
"""gensplit.py: distributed generation of one leaf certificate with gen7pd (EXT tools v4), in gen7pc --split3's output format.

  gen_split(gen7pd, inp, args, out, workers=8, d0=2, L1=10368, B1=3000000, L2=72, B2=40000, BM=2000, maxdepth=19)

inp: the leaf line ("terms DOM"); args: generator options (--plane Q --pk 3 ...). The top (gen7pd --top d0) gives the main record
with one subtree item per unexpanded node; the items' subtrees are generated in parallel (gen7pd --sub PATH, at most L1 SAT leaves
and B1 bits each, parts split into sub-records of L2 SAT leaves / B2 bits). An item over budget (TOOBIG) is expanded: its path
joins the top's expand set and the top is regenerated (the top's nodes, and so every other item's path and state, do not change:
no hoist across the cut); only new items are generated. Writes MAIN + the PART/SUB blocks in item order + END to out."""
import os, sys, subprocess, json, time
from concurrent.futures import ThreadPoolExecutor

def run(cmd, inp):
    r = subprocess.run(cmd, input=inp, capture_output=True, text=True)
    return r.stdout

def gen_split(gen, inp, args, out, workers=8, d0=3, L1=10368, B1=3000000, L2=72, B2=40000, BM=2000, maxrounds=16, log=None, kexp=2):
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
    with open(out, 'w') as f:
        f.write('MAIN %s %s %d %d\n' % (m[1], m[2], nsat, len(exts)))
        for p in exts: f.write(cache[p].rstrip('\n').rsplit('\n', 1)[0] + '\n')   # the PART block without its END
        f.write('END\n')
    return dict(items=len(exts), rounds=rounds, nsat=nsat, secs=time.time() - t0)

if __name__ == '__main__':
    gen, inp, out = sys.argv[1], sys.argv[2], sys.argv[3]
    args = sys.argv[4:]
    r = gen_split(gen, inp + '\n', args, out, log=lambda s: print(s, flush=True))
    print(json.dumps(r))
