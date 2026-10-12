#!/usr/bin/env python3
"""mkcc.py NAME L [--verify]: case (II)'s table data for the CC route (s443/S4/TopCC.lean, `L479.cLBW L`) on the C3eD base, without L479.

L = "c:R,c:R,...": context cap (c, R) puts class c at lb R + 1; its kept rows (dims KDIMS, default 3) whose kept cap is the base
table's cap 22 - lb(c) are lowered to 22 - (R + 1), in place (row ids unchanged).  Writes data/cc/NAME/:
  tab_NAME.bin       the base table ($MKCC_BASE/tab_C3eD.bin) with lb R + 1 on every entry of class c
  kept_NAME.txt      the base kept rows ($MKCC_BASE/kept_C3eDc4d.txt) with the lowered caps
  NAME.c2t           the bulk peel's tables derived from the new caps (r3c2t.cc's layout, as rerun/r3/bind/mkbind.py derives them):
                     table q < 511, slot u = OR of the cap-2 rows through q and u (u != q), the diagonal bit cleared; table 511
                     (CONF1), slot u = OR of the cap-1 rows through u, diagonal cleared
  keptNAME_lab.bin   leaf2/rt/kept3eD_lab.bin with the new caps (label mask | cap << 511, 65 bytes per row)
  lowered.txt        "row class oldcap newcap" per lowered row
  kept_rt.bin        RT's raw kept entries (leaf2/rt/kept3eD.bin) with the new caps (py/kitem.py's RTBIN)
  bind/q<q>.bin, bind/c1.bin   KB's binding inputs (items: n, n x (row id, k, k labels)): the cap-2 rows through q; the cap-1 rows
  FLAGS_NAME.txt     RECIPE's batch-14 FLAGS_NATIVE line with these files in place of the C3eD479 ones
--verify: with L empty, the derived tables must equal rerun/r3/rt/C3eD.c2t byte for byte (the generator's check)."""
import sys, os, struct, numpy as np
R22 = os.environ.get('KINDS_R22', '.'); sys.path.insert(0, R22 + '/math2'); import m2lib as M2
R = R22 + '/lean'; MB = os.environ.get('MKCC_BASE', R22 + '/base')   # MKCC_BASE: the directory of tab_C3eD.bin and kept_C3eDc4d.txt
name = sys.argv[1]; L = [tuple(int(x) for x in p.split(':')) for p in sys.argv[2].split(',') if p]; VERIFY = '--verify' in sys.argv
DIMS = set(os.environ.get('KDIMS', '3').split(','))
od = '%s/kinds/data/cc/%s' % (R, name); os.makedirs(od + '/bind', exist_ok=True)
BT, BK = MB + '/tab_C3eD.bin', MB + '/kept_C3eDc4d.txt'
T = M2.Table(BT)
raise_ = {c: r + 1 for (c, r) in L}
# --- table
t = np.fromfile(BT, dtype=np.uint8).reshape(-1, 24).copy()
for c, nl in raise_.items():
    m = T.orb == c
    olds = set(np.unique(t[m, 16]).tolist()); assert len(olds) == 1, (c, olds); old = olds.pop()
    assert nl >= old, (c, old, nl)
    t[m, 16] = nl
    print('class %d: lb %d -> %d (%d entries)' % (c, old, nl, int(m.sum())), flush=True)
t.tofile('%s/tab_%s.bin' % (od, name))
# --- kept rows
low = []
with open(BK) as fi, open('%s/kept_%s.txt' % (od, name), 'w') as fo:
    for i, line in enumerate(fi):
        p = line.split()
        if raise_ and p[0] in DIMS:
            info = T.info(M2.reduce_basis([int(x) for x in p[2:]]))
            if info and info[0] in raise_ and int(p[1]) == 22 - info[1]:
                nc = 22 - raise_[info[0]]
                fo.write('%s %d %s\n' % (p[0], nc, ' '.join(p[2:]))); low.append((i, info[0], int(p[1]), nc)); continue
        fo.write(line)
with open(od + '/lowered.txt', 'w') as f:
    for x in low: f.write('%d %d %d %d\n' % x)
cnt = {}
for (_, c, oc, nc) in low: cnt[(c, oc, nc)] = cnt.get((c, oc, nc), 0) + 1
print('lowered rows %d: %s' % (len(low), cnt), flush=True)
# --- label masks and caps (rows3eD.npz: base kept rows in --rord 123 label coordinates)
z = np.load(R + '/rerun/r3/k6/rows3eD.npz'); MK = z['M']; CAP = z['cap'].astype(np.int64).copy()
assert MK.shape[0] == 3781613
for (i, c, oc, nc) in low:
    assert CAP[i] == oc, (i, CAP[i], oc); CAP[i] = nc
def pts_of(rows):
    """label lists of the given rows"""
    out = []
    for i in rows:
        r = []
        for k in range(8):
            w = int(MK[i, k])
            while w: b = w & -w; r.append(64 * k + b.bit_length() - 1); w ^= b
        out.append(r)
    return out
# cap-2 tables: (q, u, row) triples
c2 = np.nonzero(CAP == 2)[0]; c1 = np.nonzero(CAP == 1)[0]
P2 = pts_of(c2); P1 = pts_of(c1)
print('cap-2 rows %d, cap-1 rows %d' % (len(c2), len(c1)), flush=True)
qs = []; us = []; rs = []
for j, p in enumerate(P2):
    k = len(p); a = np.array(p, dtype=np.int32)
    qq = np.repeat(a, k); uu = np.tile(a, k); keep = qq != uu
    qs.append(qq[keep]); us.append(uu[keep]); rs.append(np.full(int(keep.sum()), j, dtype=np.int32))
qs = np.concatenate(qs); us = np.concatenate(us); rs = np.concatenate(rs)
key = qs.astype(np.int64) * 511 + us
order = np.argsort(key, kind='stable'); key = key[order]; rs = rs[order]
vals = MK[c2[rs]]                                    # (n, 8) uint64
starts = np.concatenate(([0], np.nonzero(np.diff(key))[0] + 1))
red = np.bitwise_or.reduceat(vals, starts, axis=0)
tab = np.zeros((512, 511, 8), dtype=np.uint64)
ukeys = key[starts]; tab[ukeys // 511, ukeys % 511] = red
# CONF1: slot u = OR of the cap-1 rows through u
for j, p in enumerate(P1):
    for u in p: tab[511, u] |= MK[c1[j]]
# clear the diagonal bit u of slot u (every table)
for u in range(511): tab[:, u, u // 64] &= ~np.uint64(1 << (u % 64))
raw = tab.tobytes()
assert len(raw) == 512 * 511 * 64
open('%s/%s.c2t' % (od, name), 'wb').write(raw)
if VERIFY:
    base = open(R + '/rerun/r3/rt/C3eD.c2t', 'rb').read()
    ok = raw == base
    print('verify against rt/C3eD.c2t: %s' % ('IDENTICAL' if ok else 'DIFFERENT'), flush=True)
    if not ok: sys.exit(1)
# --- the peel's label file
lab = np.fromfile(R + '/leaf2/rt/kept3eD_lab.bin', dtype=np.uint8).reshape(-1, 65).copy()
for (i, c, oc, nc) in low:
    e = lab[i]; cap = ((int(e[63]) >> 7) & 1) | (int(e[64]) << 1); assert cap == oc, (i, cap, oc)
    e[63] = (e[63] & 0x7F) | ((nc & 1) << 7); e[64] = nc >> 1
lab.tofile('%s/kept%s_lab.bin' % (od, name))
# --- RT's raw entries with the new caps (bits 85..89), for py/kitem.py's check of the rows against RT
rt = np.fromfile(R + '/leaf2/rt/kept3eD.bin', dtype=np.uint8).reshape(-1, 16).copy()
for (i, c, oc, nc) in low:
    e = int.from_bytes(rt[i].tobytes(), 'little')
    assert (e >> 85) % 32 == oc and (e >> 90) % 512 == c, (i, (e >> 85) % 32, (e >> 90) % 512)
    e = e - (oc << 85) + (nc << 85)
    rt[i] = np.frombuffer(e.to_bytes(16, 'little'), dtype=np.uint8)
rt.tofile('%s/kept_rt.bin' % od)
# --- KB binding inputs (R3's bind/in layout)
def items(vals):
    b = bytearray()
    for v in vals:
        bs = int(v).to_bytes(max(1, (int(v).bit_length() + 7) // 8), 'little'); b += struct.pack('<Q', len(bs)); b += bs
    return bytes(b)
byq = [[] for _ in range(511)]
for j, p in enumerate(P2):
    for q in p: byq[q].append(j)
for q in range(511):
    v = [len(byq[q])]
    for j in byq[q]: v += [int(c2[j]), len(P2[j])] + P2[j]
    open('%s/bind/q%03d.bin' % (od, q), 'wb').write(items(v))
v = [len(c1)]
for j, p in enumerate(P1): v += [int(c1[j]), len(p)] + p
open('%s/bind/c1.bin' % od, 'wb').write(items(v))
# --- recipe line
fl = open(R + '/rerun/r3/rt479/FLAGS_NATIVE14.txt').read().replace('@SHM@', MB).replace('@R22@', R22).split()   # the template's placeholders
rep = {MB + '/tab_C3eD479.bin': '%s/tab_%s.bin' % (od, name), MB + '/kept_C3eD479c4d.txt': '%s/kept_%s.txt' % (od, name),
       R + '/rerun/r3/rt479/C3eDII.c2t': '%s/%s.c2t' % (od, name), R + '/rerun/r3/rt479/kept3eDII_lab.bin': '%s/kept%s_lab.bin' % (od, name)}
fl = [rep.get(x, x) for x in fl]
open('%s/FLAGS_%s.txt' % (od, name), 'w').write(' '.join(fl) + '\n')
print('wrote %s' % od)
