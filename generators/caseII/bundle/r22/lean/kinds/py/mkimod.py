#!/usr/bin/env python3
"""mkimod.py OUTDIR MODNAME CCN DIR...: one module-form case-(II) item module over the kitem.py item directories DIR... (each with
head.bin or dead.bin, b<k>.bin, fin.bin, table_0.bin, key.txt) on the CC route's table CCN (KB.ModItemCC_<CCN>), written as
OUTDIR/<MODNAME as path>.lean: private items I0, I1, … (#kmHead / #kmB / #kmEnd and the private `Ij.checked`, or #kmDead), the
module's one public theorem `<MODNAME>.keysOK : R22N.KeysOK checked [keys]` (#kmKeys) and its audit (#k1ax).  Imports KDK.ItemR2 (env KDK=KD for the old tree kinds/mod). Appends the module's
manifest line to OUTDIR/manifest.tsv: module, kind, items, records, predicted isolated kernel s, predicted peak anonymous GB, input
bytes, imports (models: DESIGN.md 44.5, 44.9). The memory model is the module path's fit on the stage-2 local test (45 item modules,
residual sd 0.27 GB): 1.2 + the largest batch's summed record increments + 35 x the input GB. A module's environment keeps every
item's data as expressions until the olean is written, at about 35 times the binary size."""
import sys, os, struct
out, mod, ccn = sys.argv[1], sys.argv[2], sys.argv[3]; dirs = sys.argv[4:]
def items(b):
    o = 0; v = []
    while o + 8 <= len(b):
        n = struct.unpack_from('<Q', b, o)[0]; v.append(int.from_bytes(b[o + 8:o + 8 + n], 'little')); o += 8 + n
    return v
def tree(it, q, acc):
    tag, ns = it[q], it[q + 1]
    if tag == 2: return q + 2
    acc['st'] += ns; q += 2 + 2 * ns
    if tag == 0: acc['st'] += 1; return q + 2
    acc['br'] += 1; q += 2; q = tree(it, q, acc); return tree(it, q, acc)
def recfeats(path):
    """per record of a kitem batch: children, steps, in-branches, dictionary rows, child rows, steps x window"""
    it = items(open(path, 'rb').read()); out_ = []
    s = it[0]; q = 1 + 6 * s; n = it[q]; q += 1
    for _ in range(n):
        q += 2
        lens = []
        for _ in range(7):
            k = it[q]; lens.append(k); q += 1 + k
        dc = sum(lens[:5])
        na = it[q]; q += 1
        for _ in range(na):
            k = it[q + 1]; q += 2 + 2 * k
        k = it[q]; q += 1 + k; q += 2
        nk = it[q]; q += 1
        acc = dict(ch=nk, st=0, br=0, cr=0, sw=0)
        for _ in range(nk):
            u, ncr = it[q + 2], it[q + 4]; acc['cr'] += ncr; q += 5 + ncr
            a = dict(st=0, br=0); q = tree(it, q, a); acc['st'] += a['st']; acc['br'] += a['br']; acc['sw'] += a['st'] * (510 - u)
        # the extension datum: b, its, cs, dks (skipped by length), xm, rg
        q += 1
        for _ in range(2):
            k = it[q]; q += 1 + k
        ndk = it[q]; q += 1
        stop = False
        for _ in range(ndk):   # dead children: skipped by their layout (tags 0 cut, 1 look-ahead, 2 leaf); tag 3 stops the walk
            q += 2; k = it[q]; q += 1 + k; tag = it[q]; q += 1
            if tag == 0: q += 3
            elif tag == 2: q += 1
            elif tag == 1:
                q += 3; k = it[q]; q += 1 + 2 * k; k = it[q]; q += 1 + 2 * k
            else: stop = True; break
        if stop: return out_ + [None]   # a node cut 5 / 6 (rare): stop the feature walk; the module still checks it
        q += 2
        acc['dc'] = dc; out_.append(acc)
    return out_
DENYK = 'run_cmd Lean.modifyEnv (Lean.LibrarySuggestions.typePrefixDenyListExt.addEntry · `R22N.KeysOK)'
def kms(a): return 17.03 + 0.01919 * a['ch'] + 0.08317 * a['st'] + 0.6416 * a['br'] + 0.01799 * a['dc'] + 0.08388 * a['cr'] + 1.732e-05 * a['sw']
def inc(a): return 1.004e-3 * a['br'] + 1.315e-4 * a['dc'] + 5.21e-5 * a['cr'] + 2.248e-7 * a['sw']
L = ['module', 'meta import KMod.Units', 'meta import KMod.Audit', 'public import KB.CC_%s_F' % ccn, 'import %s.ItemR2' % os.environ.get('KDK', 'KDK'), 'meta import KB.ModItemCC_%s' % ccn,
     'set_option Elab.async false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
     'set_option exponentiation.threshold 100000000',
     # Lean 4.30's library-suggestion extensions (symbolFrequency, sineQuaNon) fold over the module's public theorems at writeModule in
     # a MetaM whose heartbeat budget counts from 0 (not from the command's start): after ~2,000 s of kernel work the first whnf of that
     # fold panics and lean segfaults (KM2.I7, the design notes). Denying KeysOK-typed premises leaves them nothing to fold.
     '%s' % DENYK,
     '/-! case-(II) item module %s: %d items on the CC route %s (py/mkimod.py) -/' % (mod, len(dirs), ccn)]
names = []; nrec = 0; ksum = 0.0; peak = 0.0; nbytes = 0
for j, d in enumerate(dirs):
    I = 'I%d' % j; names.append(I)
    key = open(d + '/key.txt').read().split()[0]
    nbytes += sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d) if f.endswith('.bin'))
    if os.path.exists(d + '/dead.bin'):
        L += ['#kmDead %s "%s" %s' % (I, d, key),
              'private theorem %s.hkr : (R22N.SegI.ofKey %s.key).root = (%s.f0.1 ||| 2 ^ KB.dkLab %s.dk, KB.dkLab %s.dk) := rfl' % (I, I, I, I, I),
              'private theorem %s.hlo : (R22N.SegI.ofKey %s.key).lo = 0 := rfl' % (I, I),
              'private theorem %s.hrng : (R22N.SegI.ofKey %s.key).rng = [] := rfl' % (I, I),
              'private theorem %s.hext : (R22N.SegI.ofKey %s.key).ext = [] := rfl' % (I, I),
              'private theorem %s.checked : KB.CheckedDeadCC_%s %s.key :=' % (I, ccn, I),
              '  ⟨%s.T.entry, %s.pl, %s.W, %s.lastP, %s.f0, %s.dk, %s.T.valid, %s.rootc, %s.dkok, %s.hkr, %s.hlo, %s.hrng, %s.hext⟩' % tuple([I] * 13)]
        nrec += 1; ksum += 0.05; peak = max(peak, 0.45)
        continue
    h = items(open(d + '/head.bin', 'rb').read()); nb = h[3 + h[3] + 1 + 6]
    L += ['#kmHead %s "%s" %s' % (I, d, key), '#kmB %s "%s" 0 %d' % (I, d, nb), '#kmEnd %s' % I,
          'private theorem %s.hkr : (R22N.SegI.ofKey %s.key).root = (%s.f0.1 ||| 2 ^ %s.l0, %s.l0) := rfl' % (I, I, I, I, I),
          'private theorem %s.checked : KB.CheckedRCC_%s %s.key :=' % (I, ccn, I),
          '  ⟨%s.T.entry, %s.pl, %s.W, %s.lastP, %s.f0, %s.l0, %s.pend0, %s.lo, %s.extL, %s.rngL, %s.sN, %s.T.valid,' % tuple([I] * 12),
          '    %s.root, %s.hp0, %s.chain, %s.fin, %s.hrl, %s.hkr, %s.hloK, %s.hrngK, %s.hextK⟩' % tuple([I] * 9)]
    for k in range(nb):
        bsum = 0.0   # one batch is one declaration: the kernel caches every record's intermediates, so the batch's increments add up
        for a in recfeats(os.path.join(d, 'b%04d.bin' % k)):
            nrec += 1
            if a is None: ksum += 0.1; continue
            ksum += kms(a) / 1000.0; bsum += inc(a)
        peak = max(peak, bsum)
L += ['#kmKeys %s.keysOK %s' % (mod, ' '.join(names)), '#kax %s.keysOK' % mod]
path = os.path.join(out, mod.replace('.', '/') + '.lean'); os.makedirs(os.path.dirname(path), exist_ok=True)
open(path, 'w').write('\n'.join(L) + '\n')
pk = 1.2 + peak + 35.0 * nbytes / 1e9
with open(os.path.join(out, 'manifest.tsv'), 'a') as f:
    f.write('%s\titems\t%d\t%d\t%.2f\t%.2f\t%d\t%s\n' % (mod, len(dirs), nrec, ksum, pk, nbytes, 'KMod.Units,KMod.Audit,KB.CC_%s_F,%s.ItemR2,KB.ModItemCC_%s' % (ccn, os.environ.get('KDK', 'KDK'), ccn)))
print('%s: %d items, %d records, predicted %.1f kernel s, peak %.2f GB' % (mod, len(dirs), nrec, ksum, pk))
