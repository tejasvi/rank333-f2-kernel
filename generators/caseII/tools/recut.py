#!/usr/bin/env python3
"""p0r/recut.py IDS PAR: re-cut fat join segments (py/joinemit.py item ids `<batch>_<segid>` of runs/join/p0all) into smaller segments,
phase-0 style. For a segment rooted at prefix P (depth d0) in a batch with frontier F: (1) prof7R3k14c FLAGS_CCW `--pctop F1` on P
(F1 = d0 + 2, at most F - 1) gives the top segment seg_r1_<id>.r3 and its frontier at F1; (2) `--pctop F` on those frontier prefixes
gives one segment per prefix, seg_r2_<id>.r3, whose JOB children are at depth F. Check: (2)'s frontier equals the batch DUMP's entries
under P (the original segment's JOB children). recut.tsv: id d0 F1 F frontier1 frontier2 ok. PAR at once, nice 10, 16 GiB each."""
import sys, os, subprocess, threading
from concurrent.futures import ThreadPoolExecutor
R = os.environ.get('KINDS_R22', '.') + ''; K = R + '/lean/kinds'; O = K + '/runs/p0r'; BIN = R + '/lean/rerun/r3/prof7R3k14c'
P0 = K + '/runs/join/p0all'; B10 = R + '/lean/rerun/r3/p0/b10'; C = K + '/data/cc/cc436_422'
ids = [l.strip() for l in open(sys.argv[1]) if l.strip()]; PAR = int(sys.argv[2])
FL = [l.split(None, 1)[1].split() for l in open(K + '/runs/xqcc/recipe_cc.txt') if l.startswith('FLAGS_CCW ')][0]
NI = max(0, 10 - os.nice(0))
def hdrlab(f):
    with open(f, 'rb') as h:
        for ln in h:
            if ln.startswith(b'#lab '): a = ln.split(); return [int(x) for x in a[2:2 + int(a[1])]]
LAB = hdrlab(C + '/hdr_ccw.r3')
BF = {l.split()[0]: int(l.split()[1]) for l in open(P0 + '/batches.tsv') if l.strip()}
for l in open(K + '/runs/p0x/expand.tsv'):   # the expansion tops (runs/p0x): batch x_<batch>_<idx>, frontier F of expand.tsv
    a = l.rstrip('\n').split('\t'); BF['x_%s_%s' % (a[0], a[1])] = int(a[4])
def dump_of(b):
    if b.startswith('x_'): return [tuple(int(v) for v in l.split()[1:]) for l in open(K + '/runs/p0x/dump_%s.txt' % b) if l.strip()]
    f = K + '/runs/p0cc/dump_%s.txt' % b
    if not os.path.exists(f): f = B10 + '/dump_%s.txt' % b   # byte-identical to the CC DUMP in 59 of 61 batches (runs/p0cc/check.txt)
    return [tuple(int(v) for v in l.split()[1:]) for l in open(f) if l.strip()]
lock = threading.Lock()
def run(pf, F, seg, dump, log):
    for f in (seg, dump):
        if os.path.exists(f): os.remove(f)
    with open(log, 'w') as lg:
        r = subprocess.run(['prlimit', '--as=17179869184', 'nice', '-n', str(NI), BIN] + FL + ['--pctop', str(F), pf, '--pcert', seg,
                            '--dumpfrontier', dump, '--threads', '1'], stdout=lg, stderr=subprocess.STDOUT)
    if r.returncode: raise SystemExit('recut: %s exit %d' % (seg, r.returncode))
    return [tuple(int(v) for v in l.split()[1:]) for l in open(dump) if l.strip()]
def one(i):
    b, sid = i.rsplit('_', 1)
    txt = subprocess.run([sys.executable, K + '/py/pcseg.py', '%s/seg_%s.r3' % (P0, b), sid], capture_output=True, text=True, check=True).stdout
    root = [int(x) for x in next(l for l in txt.split('\n') if l.startswith('#root')).split()[3:]]
    pre = tuple(LAB[x] for x in root); d0 = len(pre); F = BF[b]; F1 = min(d0 + 2, F - 1)
    if F1 <= d0: return '%s\t%d\t-\t%d\t-\t-\tskip (no room)\n' % (i, d0, F)
    pf1 = '%s/pf1_%s.txt' % (O, i); open(pf1, 'w').write('0 %s\n' % ' '.join(map(str, pre)))
    fr1 = run(pf1, F1, '%s/seg_r1_%s.r3' % (O, i), '%s/dump_r1_%s.txt' % (O, i), '%s/log_r1_%s.txt' % (O, i))
    pf2 = '%s/pf2_%s.txt' % (O, i); open(pf2, 'w').write(''.join('%d %s\n' % (j, ' '.join(map(str, p))) for j, p in enumerate(fr1)))
    fr2 = run(pf2, F, '%s/seg_r2_%s.r3' % (O, i), '%s/dump_r2_%s.txt' % (O, i), '%s/log_r2_%s.txt' % (O, i))
    want = sorted(p for p in dump_of(b) if p[:d0] == pre)
    ok = sorted(fr2) == want
    return '%s\t%d\t%d\t%d\t%d\t%d\t%s\n' % (i, d0, F1, F, len(fr1), len(fr2), 'ok' if ok else 'MISMATCH (%d expected)' % len(want))
with ThreadPoolExecutor(PAR) as ex:
    for line in ex.map(one, ids):
        with lock: open(O + '/recut.tsv', 'a').write(line)
subprocess.run('cd %s && sha256sum seg_r1_*.r3 seg_r2_*.r3 > SHA256SUMS.txt' % O, shell=True, check=True)
print('recut: done')
