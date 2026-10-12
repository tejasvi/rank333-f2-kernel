#!/usr/bin/env python3
"""pcseg.py PCERT list | PCERT SEGID | PCERT dump OUTDIR [SEGID...]: one segment (PCERT may also be an R3XI item block, as segment 0) of a prof7R3 --pcert file as r3cat text (segment-level items of the kernel track).

`list`: one line per complete segment: id, job, kind (0 job root, 1 piece, 2 replay cut, 4 top), depth d0, record bytes, number of
DON / JOB / RNG records, witness rows (#pcwit).
SEGID: the segment's records in r3cat_k13's text format (absolute labels, one record per line), without inlining: a DON stays a line
"DN <label>" (an external child: the piece segment with prefix + label), a JOB a line "JB <label> <ix>", a RNG a line "RG <l>" (it
also ends the node: its children from l on are the range item's).
Header: the pcert's "#..." lines (#lab, #kept, #table, #typecut, #xpvar, #pcwit, #leafv7, ...), then "#root <job> <kind> <prefix>"
(the prefix includes the segment root's label, as r3cat's #root line), "#seg <id>", "#wit <row ids>" (the witness rows of the
inherited dead mask, ascending; with #pcwit 1) and "#dinh <hex>" (the inherited dead mask; bit l = label l).  "#lab" without the
count, as r3cat's text.  Record layouts: prof7R3.cc's header comment, r3cat.cc's toText."""
import sys, struct
P = sys.argv[1]
data = open(P, 'rb').read()
if data[:4] == b'R3XI':
    # an item block (QUEUE.md section 3: [u32 'R3XI'][u32 hlen][header][u64 n][records][sha256]; r3qglue --itembin) as segment 0, with
    # FLAGS_NATIVE's header lines (or PCSEG_HDR's) (the block carries no flags; the witness rows are present iff hlen exceeds the fixed part + 4)
    hl = struct.unpack('<I', data[4:8])[0]; h = data[8:8 + hl]; n = struct.unpack('<Q', data[8 + hl:16 + hl])[0]
    recs_ = data[16 + hl:16 + hl + n]
    import hashlib
    hz = data[16 + hl + n:16 + hl + n + 32]   # all zero in the native extractor's blocks (t/mkitems2): not checked then
    if hz != bytes(32) and hashlib.sha256(recs_).digest() != hz: raise SystemExit('pcseg: R3XI sha256 mismatch')
    # PCSEG_HDR: a pcert of the same recipe whose header lines (#lab, #table, #kept and the format flags) the block takes; default
    # FLAGS_NATIVE's (pc_nt_H3.r3). The CC route's published recipe has no #xpvar / #pcwit / #leafv7 (e.g. runs/pc_don_H0.r3).
    import os
    LABH = open(os.environ.get('PCSEG_HDR', os.environ.get('KINDS_R22', '.') + '/lean/kinds/runs/pc_nt_H3.r3'), 'rb').read(8192)
    hdr = LABH[:LABH.index(b'#end\n') + 5].decode()
    XI = (h, recs_)
    data = b''; he = 0
else:
    XI = None
    he = data.index(b'#end\n') + 5
    hdr = data[:he].decode()
HL = [ln for ln in hdr.split('\n') if ln.startswith('#') and not ln.startswith('#end') and not ln.startswith('#R3PC')]
# '#lab N l1 .. lN' in the pcert; r3cat's text (and kitem.py) has '#lab l1 .. lN'
HL = [('#lab ' + ' '.join(ln.split()[2:])) if ln.startswith('#lab ') else ln for ln in HL]
FL = {ln.split()[0]: ln for ln in HL}
LEAFX, CUTX, LEAFV7, PCWIT = '#leafx' in FL, '#cutx' in FL, '#leafv7' in FL, '#pcwit' in FL
def var(b, i):
    x = 0; sh = 0
    while True:
        c = b[i]; i += 1; x |= (c & 127) << sh
        if not c & 128: return x, i
        sh += 7
segs = {}
if XI is not None:
    h, recs_ = XI; q = 0
    S = segs.setdefault(0, dict(chunks=[(0, recs_)], last=True))
    S['item'], q = var(h, q); S['job'], q = var(h, q); S['kind'] = h[q]; d0 = h[q + 1]; q += 2
    S['pre'] = [int.from_bytes(h[q + 2 * k:q + 2 * k + 2], 'little') for k in range(d0)]; q += 2 * d0
    S['dinh'] = h[q:q + 64]; q += 64; S['win'] = []
    if len(h) > q + 4:
        nw, q = var(h, q); p_ = 0
        for _ in range(nw): dl, q = var(h, q); p_ += dl; S['win'].append(p_)
    S['rl'], S['rp'] = struct.unpack('<HH', h[q:q + 4]); q += 4
    if q != len(h): raise SystemExit('pcseg: R3XI header length')
o = he
while o + 12 <= len(data):
    magic, ln, crc = struct.unpack('<III', data[o:o + 12])
    if magic != 0x31423352: raise SystemExit('pcseg: bad block magic at %d' % o)
    pay = data[o + 12:o + 12 + ln]
    segid, ci = struct.unpack('<QI', pay[:12]); fl = pay[12]; q = 13
    S = segs.setdefault(segid, dict(chunks=[], last=False))
    if fl & 1:
        S['job'], q = var(pay, q); S['kind'] = pay[q]; q += 1; d0 = pay[q]; q += 1
        S['pre'] = [int.from_bytes(pay[q + 2 * k:q + 2 * k + 2], 'little') for k in range(d0)]; q += 2 * d0
        S['dinh'] = pay[q:q + 64]; q += 64
        S['win'] = []
        if PCWIT:
            n, q = var(pay, q); p_ = 0
            for _ in range(n): dl, q = var(pay, q); p_ += dl; S['win'].append(p_)
    if fl & 2: S['last'] = True
    S['chunks'].append((ci, pay[q:]))
    o += 12 + ln
def records(S):
    return b''.join(c for _, c in sorted(S['chunks']))
def totext(b, out, st0=None):
    st = [list(x) for x in (st0 or [])]; pend = None
    i = 0; nref = [0, 0, 0]
    def child():
        nonlocal i
        if not st: raise SystemExit('pcseg: child record outside a node')
        dl, i = var(b, i); st[-1][2] += dl; return st[-1][2]
    while i < len(b):
        t = b[i]; i += 1
        if t == 0x01:
            x = b[i] | (b[i + 1] << 8); i += 2; d, l = x >> 9, x & 511
            if st: st[-1][2] = l
            pend = [d, l, l]; out.append('N %d %d' % (d, l))
        elif t == 0x02:
            c = b[i]; i += 1; s = 'L %d' % c
            if LEAFX:
                if c == 5: v, i = var(b, i); s += ' row %d' % v
                elif c in (6, 7):
                    n = b[i]; i += 1; s += ' wl' + ''.join(' %d' % (b[i + 2 * k] | (b[i + 2 * k + 1] << 8)) for k in range(n)); i += 2 * n
                    s += ' cap %d' % (b[i] - 1); i += 1
            if LEAFV7 and c == 0:
                nb, i = var(b, i); nby = (nb + 7) // 8; s += ' v7 %d %s' % (nb, b[i:i + nby].hex()); i += nby
            out.append(s); pend = None
        elif t == 0x03:
            k = b[i]; i += 1; s = 'C %d' % k
            if k == 1: s += ' %d' % (b[i] | (b[i + 1] << 8)); i += 2
            elif k in (2, 4, 5, 6, 10):
                v, i = var(b, i); s += ' %d' % v
                if CUTX and k in (5, 6):
                    ok = b[i]; i += 1; s += ' xp %d' % ok
                    if ok:
                        ne, i = var(b, i); s += ' ex'
                        for _ in range(ne): v, i = var(b, i); s += ' %d' % v
                        L1, i = var(b, i); s += ' node ' + b[i:i + L1].hex(); i += L1
                        L2, i = var(b, i); s += ' cert ' + b[i:i + L2].hex(); i += L2
            elif k == 3: s += ' %d' % b[i]; i += 1
            elif k == 11:
                p_, ak = b[i], b[i + 1]; i += 2; s += ' %d %d' % (p_, ak)
                if ak in (1, 2):
                    dm = b[i]; i += 1; s += ' %d' % dm + ''.join(' %d' % (b[i + 2 * j] | (b[i + 2 * j + 1] << 8)) for j in range(dm)); i += 2 * dm
                else: s += ' %d' % b[i]; i += 1
            out.append(s); pend = None
        elif t == 0x04:
            if pend is None: raise SystemExit('pcseg: OPEN without NODE')
            st.append(pend); pend = None; out.append('O')
        elif t == 0x05: st.pop(); out.append('E')
        elif t == 0x06: out.append('A')
        elif t == 0x10:
            n, i = var(b, i); p_ = 0; s = 'V'
            for _ in range(n): dl, i = var(b, i); p_ += dl; s += ' %d' % p_
            out.append(s)
        elif t == 0x11:
            v = []
            for _ in range(4): x, i = var(b, i); v.append(x)
            s = 'XR %d %d %d %d :' % tuple(v)
            for _ in range(sum(v)): x, i = var(b, i); s += ' %d' % x
            out.append(s)
        elif t == 0x12:
            n, i = var(b, i); pl = st[-1][1] if st else 0; s = 'WB'
            for _ in range(n): dl, i = var(b, i); pl += dl; s += ' %d:%d' % (pl, b[i]); i += 1
            out.append(s)
        elif t == 0x13:
            n, i = var(b, i); pl = st[-1][1] if st else 0; s = 'BK'
            for _ in range(n):
                dl, i = var(b, i); pl += dl; dm = b[i]; i += 1; s += ' %d:%d' % (pl, dm)
                for k in range(dm): s += ',%d' % (b[i + 2 * k] | (b[i + 2 * k + 1] << 8))
                i += 2 * dm
            out.append(s)
        elif t == 0x20:
            l = child(); x = b[i]; i += 1; s = 'T %d :' % l
            for _ in range(x): v, i = var(b, i); s += ' %d' % v
            out.append(s)
        elif t == 0x21:
            l = child(); x, c = b[i], b[i + 1]; i += 2; s = 'CV %d %d %d :' % (l, x, c)
            for _ in range(x + c): v, i = var(b, i); s += ' %d' % v
            out.append(s)
        elif t == 0x22:
            l = child(); k = b[i]; i += 1; bb, i = var(b, i); ch = b[i]; i += 1; s = 'X %d %d %d %d' % (l, k, bb, ch)
            if ch in (1, 3): raise SystemExit('pcseg: Farkas X records are not printed by this tool')
            if ch == 5:
                ne, i = var(b, i); s += ' ex'
                for _ in range(ne): v, i = var(b, i); s += ' %d' % v
                L, i = var(b, i); s += ' cert ' + b[i:i + L].hex(); i += L
            out.append(s)
        elif t == 0x23:
            l = child(); ty = b[i]; g = b[i + 1] | (b[i + 2] << 8) | (b[i + 3] << 16); i += 4
            out.append('CN %d %d %d %d %d' % (l, ty, g >> 18, (g >> 9) & 511, g & 511))
        elif t == 0x24: l = child(); out.append('P %d %d' % (l, b[i] | (b[i + 1] << 8))); i += 2
        elif t == 0x25: out.append('TY %d' % child())
        elif t == 0x26: out.append('DM %d' % child())
        elif t == 0x28: out.append('DN %d' % child()); nref[0] += 1
        elif t == 0x27:
            l = child(); ak = b[i]; i += 1; s = 'AF %d %d' % (l, ak)
            if ak in (1, 2):
                dm = b[i]; i += 1; s += ' %d' % dm + ''.join(' %d' % (b[i + 2 * j] | (b[i + 2 * j + 1] << 8)) for j in range(dm)); i += 2 * dm
            else: s += ' %d' % b[i]; i += 1
            out.append(s)
        elif t == 0x2B: L, i = var(b, i); out.append('XPN ' + b[i:i + L].hex()); i += L
        elif t == 0x2C:
            # a range reference ends the node's child records (the children from l on are the range item's; r3qglue --itemkey)
            l = b[i] | (b[i + 1] << 8); i += 2; out.append('RG %d' % l); nref[2] += 1
            if not st: raise SystemExit('pcseg: RG outside a node')
            st.pop()
        elif t == 0x2D: l = child(); ix, i = var(b, i); out.append('JB %d %d' % (l, ix)); nref[1] += 1
        elif t in (0x29, 0x2A): raise SystemExit('pcseg: skip references (resumed runs) are not supported')
        else: raise SystemExit('pcseg: unknown tag %d' % t)
    return nref
if sys.argv[2] == 'list':
    for sid in sorted(segs):
        S = segs[sid]
        if not S['last'] or 'job' not in S: continue
        b = records(S); out = []
        try: nref = totext(b, out, [(len(S['pre']), S['pre'][-1], S['rp'])] if S['kind'] == 3 else None)
        except SystemExit as e: nref = ['?', '?', '?']
        print('%d job %d kind %d d0 %d bytes %d DN %s JB %s RG %s wit %d' % (sid, S['job'], S['kind'], len(S['pre']), len(b), nref[0], nref[1], nref[2], len(S['win'])))
def segtext(sid):
    S = segs[sid]
    if not S['last']: raise SystemExit('pcseg: segment incomplete')
    out = list(HL)
    out.append('#root %d %d %s' % (S['job'], S['kind'], ' '.join(map(str, S['pre']))))
    out.append('#seg %d' % sid)
    if PCWIT: out.append('#wit ' + ' '.join(map(str, S['win'])))
    out.append('#dinh ' + S['dinh'][::-1].hex())   # the inherited dead mask, as a big-endian hex number (label l = bit l)
    st0 = None
    if S['kind'] == 3:
        # a range item (queue only): its records continue node S (the prefix's last label) from child S['rl'] on, deltas based at
        # S['rp']; written as NODE + OPEN of S so that the text reads as S's subtree (children below the range start are absent)
        out.append('#range %d %d' % (S['rl'], S['rp']))
        out.append('N %d %d' % (len(S['pre']), S['pre'][-1])); out.append('O')
        st0 = [(len(S['pre']), S['pre'][-1], S['rp'])]
    totext(records(S), out, st0)
    return '\n'.join(out) + '\n'
if sys.argv[2] == 'dump':   # dump OUTDIR [ids]: every complete segment (or the given ones) to OUTDIR/<id>.txt
    import os
    os.makedirs(sys.argv[3], exist_ok=True)
    ids = [int(x) for x in sys.argv[4:]] or [sid for sid in sorted(segs) if segs[sid]['last'] and 'job' in segs[sid]]
    for sid in ids:
        try: t = segtext(sid)
        except SystemExit as e: print('%d %s' % (sid, e)); continue
        open(os.path.join(sys.argv[3], '%d.txt' % sid), 'w').write(t)
elif sys.argv[2] != 'list':
    sys.stdout.write(segtext(int(sys.argv[2])))
