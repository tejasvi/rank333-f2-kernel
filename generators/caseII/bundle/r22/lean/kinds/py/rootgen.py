"""rootgen.py: the matrix-form root certificate of Lemma R (r22/wtight/ROOT.md), as r22/lean/kernel/root/gencert.py builds it for
RootCheck (tables RK, QX, PX, Z_X from its cache zx.txt, FZ, outer, the odd-set elimination, the slack-choice tree and its
encoding), for KD.flookOK.  Copied here so the generator runs from this directory."""
import os
import numpy as np
def bits(v): return [(v >> i) & 1 for i in range(9)]
def mat(v): return np.array(bits(v), dtype=np.int64).reshape(3, 3)
def vec3(r): return int(r[0]) | (int(r[1]) << 1) | (int(r[2]) << 2)
def span(vs):
    s = {0}
    for v in vs: s |= {x ^ v for x in s}
    return frozenset(s)
RK = [0] * 512; QX = [frozenset([0])] * 512; PX = [frozenset([0])] * 512
for X in range(1, 512):
    Xm = mat(X); QX[X] = span([vec3(Xm[i]) for i in range(3)]); PX[X] = span([vec3(Xm[:, j]) for j in range(3)]); RK[X] = len(QX[X]).bit_length() - 1
ZX = [int(x) for x in open(os.environ.get('KINDS_R22', '.') + '/lean/kernel/root/zx.txt').read().split()]
def mask8(S): return sum(1 << v for v in S)
def fzmask(Z):
    Zm = mat(Z); m = 0
    for p in range(8):
        pv = np.array([(p >> k) & 1 for k in range(3)])
        for q in range(8):
            qv = np.array([(q >> k) & 1 for k in range(3)])
            if int(pv @ Zm @ qv) % 2: m |= 1 << (8 * p + q)
    return m
FZ = [fzmask(Z) for Z in ZX]
QXM = [mask8(QX[X]) for X in range(512)]; PXM = [mask8(PX[X]) for X in range(512)]
def spread(P): return sum(0xFF << (8 * p) for p in range(8) if (P >> p) & 1)
def outer(P, Q): return (Q * 0x0101010101010101) & spread(P)
def oddset(tight, Qm, Pm):
    o = outer(Pm, Qm); piv = {}
    for j, X in enumerate(tight):
        v = FZ[X] & o; s = 1 << j; par = 1
        while v:
            h = v.bit_length() - 1
            if h in piv: pv, ps, pp = piv[h]; v ^= pv; s ^= ps; par ^= pp
            else: piv[h] = (v, s, par); break
        if not v and par: return s
    return None
def build(tight, slack, Qm, Pm, i):
    if Qm == 1 or Pm == 1: return ('Z',)
    S = oddset(tight, Qm, Pm)
    if S is not None: return ('S', S)
    if i == len(slack): return None
    X = slack[i]
    l = build(tight, slack, Qm & QXM[X], Pm, i + 1)
    if l is None: return None
    r = build(tight, slack, Qm, Pm & PXM[X], i + 1)
    if r is None: return None
    return ('N', l, r)
def enc_tree(tr, nT):
    if tr[0] == 'Z': return (0, 2)
    if tr[0] == 'S': return (2 | (tr[1] << 2), 2 + nT)
    lv, ll = enc_tree(tr[1], nT); rv, rl = enc_tree(tr[2], nT)
    assert ll < 4096
    return (1 | (ll << 1) | (lv << 13) | (rv << (13 + ll)), 13 + ll + rl)
def q0p0(tight):
    Q0 = 255; P0 = 255
    for X in tight:
        if RK[X] < 3: Q0 &= QXM[X]; P0 &= PXM[X]
    return Q0, P0
def walk(nT, tight, slack, hh, Q, P, i, fuel=64):
    """model of RootCheck.walk"""
    if fuel == 0: return False
    if hh & 1:
        if i >= len(slack): return False
        L = (hh >> 1) & 4095; X = slack[i]
        return walk(nT, tight, slack, hh >> 13, Q & QXM[X], P, i + 1, fuel - 1) and walk(nT, tight, slack, hh >> (13 + L), Q, P & PXM[X], i + 1, fuel - 1)
    if (hh >> 1) & 1:
        S = (hh >> 2) & ((1 << nT) - 1)
        if bin(S).count('1') % 2 == 0: return False
        z = 0
        for j in range(nT):
            if (S >> j) & 1: z ^= FZ[tight[j]]
        return (outer(P, Q) & z) == 0
    return Q == 1 or P == 1
