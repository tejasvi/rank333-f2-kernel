#!/usr/bin/env python3
"""mkimod321.py OUTDIR MODNAME LO HI DIR...: one module-form item module of case (LO, HI) under --rord 321 (cases (I) / (I13)) over
py/kitem.py's item directories (KI_ORD=321: head.bin, b<k>.bin, fin.bin, table_0.bin, key.txt), written as OUTDIR/<MODNAME as path>.lean:
private items I0, I1, … (KB.ModItem321's #kmHead321 / #kmB321 / #kmEnd321, the key root `Ij.hkr` by `rfl`, and
`Ij.checked : KB.CheckedR321 LO HI Ij.key`: items may be range items or have range children), the module's one public theorem `<MODNAME>.keysOK : R22N.KeysOK (KB.CheckedAny321 LO HI)
[keys]` (#kmKeys321) and its audit (#kax). With DIR = `root462`, the module is the dead job root 462 alone (#kmRoot462). An item
dir with dead.bin is a dead-root item (a piece whose root is killed by a node cut 5 / 6): #kmDead321, the key facts by `rfl`, and
`Ij.checked : KB.CheckedDead321 LO HI Ij.key` (KB.Dead321).
Appends the module's manifest line to OUTDIR/manifest.tsv (as py/mkimod.py: module, kind, items, records, predicted kernel s,
predicted peak GB, input bytes, imports), with the 321 models of the design notes / 44.12: 17 ms per record plus 0.5 ms per root-frame
witness row (the fast root check); peak 1.2 x (2.6 GB + 0.1 GB per 1,000 records + 0.1 GB per 1,000 records above 5,000)."""
import sys, os
ARGS = sys.argv[1:]
K = os.environ.get('KINDS_R22', '.') + '/lean/kinds'
sys.argv = ['x', ARGS[0], 'X', 'cc436_422']
exec(open(K + '/py/mkimod.py').read().split("L = ['module'")[0])   # items(), recfeats(), kms(), inc() (it also sets out, mod, dirs)
out, mod, lo, hi = ARGS[0], ARGS[1], int(ARGS[2]), int(ARGS[3]); dirs = ARGS[4:]
L = ['module', 'meta import KMod.Units', 'meta import KMod.Audit', 'public import KB.Agg321', 'meta import KB.ModItem321',
     'meta import KB.ModAgg321', 'set_option Elab.async false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
     'set_option exponentiation.threshold 100000000',
     '/-! case-(%d, %d) item module %s under --rord 321: %d items (py/mkimod321.py) -/' % (lo, hi, mod, len(dirs))]
names = []; nrec = 0; ksum = 0.0; peak = 0.0; nbytes = 0
if dirs == ['root462']:
    L += ['#kmRoot462 %s.keysOK %d %d' % (mod, lo, hi), '#kax %s.keysOK' % mod]
    nrec = 1; ksum = 0.1
else:
    for j, d in enumerate(dirs):
        I = 'I%d' % j; names.append(I)
        key = open(d + '/key.txt').read().split()[0]
        nbytes += sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d) if f.endswith('.bin'))
        if os.path.exists(d + '/dead.bin'):
            # the 321 dead-root contract (KB.Dead321) takes a node cut 5 / 6 only (#kmDead321 refuses other tags at build time): check here
            dv = items(open(d + '/dead.bin', 'rb').read())
            if dv[0] != 2: sys.exit('mkimod321: %s: dead.bin format %d' % (d, dv[0]))
            q = 3 + dv[2] + 6; q += 1 + dv[q]          # skip pl, lastP, f0, then the witness rows
            q += 2; q += 1 + dv[q]                     # the root's record: u, hdr, then its V rows
            if dv[q] != 3: sys.exit('mkimod321: %s: a dead root of payload tag %d; KB.Dead321 takes a node cut 5 / 6 (tag 3) only' % (d, dv[q]))
            L += ['#kmDead321 %s "%s" %s' % (I, d, key),
                  'private theorem %s.hkr : (R22N.SegI.ofKey %s.key).root = (%s.f0.1 ||| 2 ^ KB.dkLab %s.dk, KB.dkLab %s.dk) := rfl' % (I, I, I, I, I),
                  'private theorem %s.hlo : (R22N.SegI.ofKey %s.key).lo = 0 := rfl' % (I, I),
                  'private theorem %s.hrng : (R22N.SegI.ofKey %s.key).rng = [] := rfl' % (I, I),
                  'private theorem %s.hext : (R22N.SegI.ofKey %s.key).ext = [] := rfl' % (I, I),
                  'private theorem %s.checked : KB.CheckedDead321 %d %d %s.key :=' % (I, lo, hi, I),
                  '  ⟨%s.T.entry, %s.pl, %s.W, %s.lastP, %s.f0, %s.dk, %s.T.valid, %s.rootc, %s.isx, %s.dkok, %s.hkr, %s.hlo, %s.hrng, %s.hext⟩'
                  % tuple([I] * 14)]
            nrec += 1; ksum += 0.5   # the root frame (fast check) and the X part of the node cut
            continue
        h = items(open(d + '/head.bin', 'rb').read()); nb = h[3 + h[3] + 1 + 6]
        L += ['#kmHead321 %s "%s" %s' % (I, d, key), '#kmB321 %s "%s" %d %d 0 %d' % (I, d, lo, hi, nb), '#kmEnd321 %s %d %d' % (I, lo, hi),
              'private theorem %s.hkr : (R22N.SegI.ofKey %s.key).root = (%s.f0.1 ||| 2 ^ %s.l0, %s.l0) := rfl' % (I, I, I, I, I),
              'private theorem %s.checked : KB.CheckedR321 %d %d %s.key :=' % (I, lo, hi, I),
              '  ⟨%s.T.entry, %s.pl, %s.W, %s.lastP, %s.f0, %s.l0, %s.pend0, %s.lo, %s.extL, %s.rngL, %s.sN, %s.T.valid, %s.root, %s.hp0,'
              % tuple([I] * 14),
              '    %s.chain, %s.fin, %s.hrl, %s.hkr, %s.hloK, %s.hrngK, %s.hextK⟩' % tuple([I] * 7)]
        nW = h[3 + h[3] + 1 + 7] if len(h) > 3 + h[3] + 1 + 7 else 0   # the root frame's witness rows
        ksum += 0.0005 * nW   # the fast root check (KB.PcB): 0.45 ms per witness row (it was 44 ms with L5.pcnt)
        for k in range(nb):
            bsum = 0.0
            for a in recfeats(os.path.join(d, 'b%04d.bin' % k)):
                nrec += 1
                ksum += 0.017   # the 321 sample : about 17 ms per record
                if a is None: continue
                bsum += inc(a)
            peak = max(peak, bsum)
    L += ['#kmKeys321 %s.keysOK %d %d %s' % (mod, lo, hi, ' '.join(names)), '#kax %s.keysOK' % mod]
path = os.path.join(out, mod.replace('.', '/') + '.lean'); os.makedirs(os.path.dirname(path), exist_ok=True)
open(path, 'w').write('\n'.join(L) + '\n')
# peak RssAnon: the case-(I) sample (2.5 GB at 113 records to 3.4 GB at 9,299) fits 2.6 + 0.1 GB per 1,000 records, but an I13 module of
# 9,951 records peaked at 5.75 GB : +0.1 GB per 1,000 records above 5,000, and 1.2x (mkpkg2 adds 0.5 GB)
krec = nrec / 1000.0
pk = 1.2 * (2.6 + 0.1 * krec + 0.1 * max(0.0, krec - 5.0))
with open(os.path.join(out, 'manifest.tsv'), 'a') as f:
    f.write('%s\titems\t%d\t%d\t%.2f\t%.2f\t%d\t%s\n' % (mod, max(1, len(dirs) if dirs != ['root462'] else 1), nrec, ksum, pk, nbytes,
            'KMod.Units,KMod.Audit,KB.Agg321,KB.ModItem321,KB.ModAgg321'))
print('%s: %d items, %d records, predicted %.1f kernel s, peak %.2f GB' % (mod, len(dirs), nrec, ksum, pk))
