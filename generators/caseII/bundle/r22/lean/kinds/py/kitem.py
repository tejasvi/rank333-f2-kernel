#!/usr/bin/env python3
"""kitem.py TEXT ROWS C2T RTBIN OUTDIR [B]: one item (a piece or a job of the case-(II) run) for the kernel track's item checker
KD.itemXS' (kinds/lean/KD/ItemK.lean) with the case-(II) extension KB.extII (kinds/lean/KB/ExtII.lean), from its r3cat text stream.

Every OPEN record of the stream, in DFS pre-order, with
* its composed node record (KD.nodeXO: L1 v5 + the bound bulk-peel part), built exactly as py/kx3.py builds it (KX2_NOB layout);
* its extension datum (b, its, cs, dks, xm): the suffix break b (smallest label above last with at most 21 - d labels outside D'
  from b on), the PREFF records (tag 0 | u << 2 | X << 11), the L3 node records of its CANON children (C3 records with the order's
  key table C3.LABT: k321.py's canon_records with the 123 labels), its dead children (flook cut children "C 3 pos": the cut node's
  V rows (cap >= 3) by job-table index and kflook's certificate for the dead term on the frame frame5 builds), its external children
  xm (DN pieces and JB jobs: the segments rooted at those children; the item key lists them, in stream order);
* its pending mask (KD.pendOf: above last, minus T/C kill labels, bulk-peel children, the extension's children, D'), the frame
  stack simulated as KD.itemXS' does (a record's label pending in its parent frame, popped frames without pending labels).
profile leaves (code 0, depth 22) with their v7 records from the pinned generator (hcls/E1P/cpp/gen7c --lg, full domain:
R = [6] 22, 22 x [9] codes in increasing label order, [1] dm 0, [1] lg 1, certificate bits; as batch 13's --leafv7).
rootcut leaves (code 4, depth 22) as look-ahead children (the first term with a certificate, as k321.py).
Items with other dead children (node cuts other than 3) are refused (not in this checker yet).
Python models: kx3.py's node5 / bulk-peel models, the kernel track's models (PREFF), C3T's node check, kflook's fbOK / RootCheck walk.

Root frame (KB.rootChk0): the empty frame (0, 0, c1, 0, 0) for a depth-1 root (a top segment); else the prefix's frame with the
witness rows W (KB.rootChkW): a piece's header rows (#wit, #pcwit) and, for a dead root, its own V rows full at the prefix.
Input: r3cat_k13's job text or py/pcseg.py's segment text (#root, #wit, #dinh, #range). Ranges (KD.itemXR', KB.CheckedR): a range
item (kind 3, "#range l p") excuses its root's children below l; a node's "RG l" hands its children from l on to the range
segment ((S, last), l), listed in the key's rng in stream order; each extension datum ends with the record's range start (511: none).
Order (env KI_ORD, default 123): KI_ORD=321 converts a --rord 321 stream (cases (I) / (I13), env KI_LO / KI_HI = the case's
rank-1 window, 0 12 or 13 13) for KB.CheckedK321 (KB.Defs321's ext321K): the 321 hyp tables (rt321/hyp7_321.bin), the 321 CANON
key table (Top321.LABT321), the 321 models of DOOM and node cut 7 (k321.py: the rank-1 window [lo, hi], rank-1 labels 462-510);
TYPE records and node cuts other than 3 (look-ahead) and 7 are refused there. ROWS / C2T / RTBIN: the C3eD kept rows
(/dev/shm/r22/kept_C3eDc4d.txt), rt321/C3eD_321.c2t, leaf2/rt/kept3eD.bin.
Writes (items [u64 len][len bytes LE]) OUTDIR/head.bin: version 1, l0, pend0, npl, pl..., lastP, S0 D0 N0 U0 d0, nbatch, nW, W (job-table
  indices), nE, nE x (S, u) (the external children's keys, stream order), lo, nR, nR x (S, last, l) (the ranges); OUTDIR/extL.txt
  and rngL.txt the same (py/itemkey.py's ext, lo and rng);
  OUTDIR/b<k>.bin (k < nbatch, 4 digits): the batch's input stack s, s x (S D N U d pend), then n, n x (record, ext);
  OUTDIR/fin.bin: the final stack s, s x (S D N U d pend)
  record = l, hdr, r2 / r1 / r0 / x2 / x1 / ks lists (count + table indices, reversed as kx3.py), then kx3.py's bulk-peel part
  ext = b, nits, its, ncs, cs, ndk, per dead child (u, hdr, nV, V idx reversed, then tag 1 (flook): t, nT, h2, nTL, TL, TY, nSL,
  SL, SY, or tag 2 (leaf): R), xm
and OUTDIR/table_0.bin (the item's row table, 69-byte entries as kx3.py) and OUTDIR/stats.txt."""
import sys, os, struct, json, collections
R22 = os.environ.get('KINDS_R22', '.')   # env KINDS_R22: a relocated tree (emitter bundle on a build machine)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rootgen as RG
sys.set_int_max_str_digits(0)
txt, rowsf, c2tf, rtbin, outdir = sys.argv[1:6]
B = int(sys.argv[6]) if len(sys.argv) > 6 else 20
os.makedirs(outdir, exist_ok=True)
M511 = (1 << 511) - 1; M512 = (1 << 512) - 1
def par(x): return bin(x).count('1') & 1
def pc(x): return bin(x).count('1')
def die(msg): raise SystemExit('kitem: ' + msg)
PERMISSIVE = os.environ.get('KI_PERMISSIVE', '0') == '1'   # corruption tests: a failed Python model is reported, the records are still
SOFT = []                                                  # written, and the kernel decides
def soft(msg):
    if not PERMISSIVE: die(msg)
    if len(SOFT) < 20: print('kitem (permissive): ' + msg, flush=True)
    SOFT.append(msg)
def span9(basis):
    sp = {0}
    for v in basis: sp |= {x ^ v for x in sp}
    return tuple(sorted(sp - {0}))

# ---------------- parse ----------------
HDR = {}
lines = [ln.rstrip('\n') for ln in open(txt)]
for ln in lines:
    if ln.startswith('#'): HDR[ln.split()[0]] = ln
labv = [int(x) for x in HDR['#lab'].split()[1:]]; lab = {v: i for i, v in enumerate(labv)}
ORD = os.environ.get('KI_ORD', '123')
if ORD not in ('123', '321'): die('KI_ORD must be 123 or 321')
if ORD == '321':
    KLO, KHI = int(os.environ['KI_LO']), int(os.environ['KI_HI'])
    R1M321 = ((1 << 511) - 1) ^ ((1 << 462) - 1); NR1M321 = (1 << 462) - 1
root = [int(x) for x in HDR['#root'].split()[3:]]
recs = []          # OPEN records in pre-order
EXTSEQ = []        # external children (OPEN record, label) in stream order
RNGSEQ = []        # range references (OPEN record, range start) in stream order
LO = int(HDR['#range'].split()[1]) if '#range' in HDR else 0   # a range item (kind 3): its root's children start at LO
if '#range' in HDR:
    # guard : a range item's records continue node S, so the text must open S (NODE + OPEN) before them, as py/pcseg.py
    # writes it from `r3qglue --itembin`; `r3qglue --itemtext` leaves that line out and must not be used for range items
    body = [ln for ln in lines if ln and ln[0] != '#']
    if len(body) < 2 or body[0].split()[0] != 'N' or body[1].split()[0] != 'O':
        die('range item without its root NODE/OPEN (the r3qglue --itemtext form): extract it with r3qglue --itembin and py/pcseg.py '
            '(PCSEG_HDR = the recipe\'s pcert header; py/xqitems.py)')
WIT = [int(x) for x in HDR['#wit'].split()[1:]] if '#wit' in HDR else []        # the root's witness rows (pcseg.py, #pcwit)
DINH = int(HDR['#dinh'].split()[1], 16) if '#dinh' in HDR and len(HDR['#dinh'].split()) > 1 else None   # R3's inherited mask
root_dead = None   # the root's record when the root is a dead node
stack = []         # OPEN contexts
pend = None; pend_V = None; opened = False
for ln in lines:
    if not ln or ln[0] == '#': continue
    a = ln.split(); t = a[0]
    if t == 'N':
        pend = (int(a[1]), int(a[2])); pend_V = []; opened = False
        continue
    if t == 'O':
        cur = dict(d=pend[0], l=pend[1], V=[], XR=([], [], []), K=[], XPN=None, XC=[], P=[], CN=[], DK=[], XM=[], kids_nodes=[], parent=stack[-1] if stack else None)
        if stack: stack[-1]['kids_nodes'].append(pend[1])
        recs.append(cur); stack.append(cur); opened = True
        continue
    if t == 'E': stack.pop(); continue
    if t == 'V' and not opened:
        pend_V = [int(x) for x in a[1:]]; continue
    if t == 'C' or t == 'L':
        if not stack:   # the item root is a dead node (a replay-cut segment has no NODE record: the root is #root's last label)
            if pend is None: pend = (len(root), root[-1]); pend_V = []
            root_dead = dict(kind=None, u=pend[1], d=pend[0], V=list(pend_V or []), a=a)
            continue
        P = stack[-1]; u = pend[1]
        if t == 'L':
            if pend[0] != 22 or a[1] not in ('0', '4'): die('leaf code %s at depth %d: only codes 0 (profile) and 4 (rootcut) at depth 22' % (a[1], pend[0]))
            if a[1] == '0':
                dk_ = dict(kind='leaf', u=u, d=pend[0], V=list(pend_V or []))
                if len(a) > 4 and a[2] == 'v7': dk_['Rs'] = (int(a[3]), int.from_bytes(bytes.fromhex(a[4]), 'little'))
                P['DK'].append(dk_)
            else: P['DK'].append(dict(kind='flook', u=u, d=pend[0], pos=None, V=list(pend_V or [])))   # leaf code 4: Lemma R at d = 22
            continue
        ck = int(a[1])
        if ck in (5, 6):
            # node cut 5 / 6 with its 27.11-format bulk-peel certificate (#cutx 1): converted into a hybrid X-part child of the
            # parent (the X tier's XT/Cut.lean conversion); the cut node is the parent's killed child
            if not ('xp' in a and a[a.index('xp') + 1] == '1'): die('node cut %d without a certificate' % ck)
            ie, inode, icert = a.index('ex'), a.index('node'), a.index('cert')
            P.setdefault('CUTS', []).append(dict(u=u, kind=ck, bb=int(a[2]), ex=[int(x) for x in a[ie + 1:inode]],
                                                 nd=bytes.fromhex(a[inode + 1]), ce=bytes.fromhex(a[icert + 1])))
            continue
        if ck == 3: P['DK'].append(dict(kind='flook', u=u, d=pend[0], pos=int(a[2]), V=list(pend_V or [])))
        elif ck in (1, 2, 4, 7, 8, 9, 10):
            arg = int(a[2]) if ck == 1 else 0
            if ck == 1 and not 0 < arg < 512: die('node cut 1 with split / wlook (arg %d)' % arg)
            rid = int(a[2]) if ck in (2, 10) else None
            P['DK'].append(dict(kind='cut', ck=ck, arg=arg, rid=rid, u=u, d=pend[0], V=list(pend_V or [])))
        elif ck == 11 and int(a[3]) in (1, 2):
            # replay cut: an add failure, the subspace spanned by the basis overflows; checked as node cut 2 with its kept row
            dim = int(a[4]); basis = [int(x) for x in a[5:5 + dim]]
            P['DK'].append(dict(kind='cut', ck=2, arg=0, rid=None, sub=span9(basis), u=u, d=pend[0], V=list(pend_V or [])))
        else: die('node cut %d at depth %d: not in this checker' % (ck, pend[0]))
        continue
    if not stack: continue
    cur = stack[-1]
    if t == 'V': cur['V'] = [int(x) for x in a[1:]]
    elif t == 'XR':
        ne, n1, n2, n3 = int(a[1]), int(a[2]), int(a[3]), int(a[4]); r = [int(x) for x in a[6:]]
        cur['XR'] = (r[:ne], r[ne:ne + n1], r[ne + n1:ne + n1 + n2])
    elif t == 'T': cur['K'].append((int(a[1]), 'T', [int(x) for x in a[3:]], []))
    elif t == 'CV':
        nx, nc = int(a[2]), int(a[3]); r = [int(x) for x in a[5:]]
        cur['K'].append((int(a[1]), 'C', r[:nx], r[nx:]))
    elif t == 'XPN': cur['XPN'] = bytes.fromhex(a[1])
    elif t == 'X':
        ch = a[4]
        if ch == '5': cur['XC'].append(bytes.fromhex(a[a.index('cert') + 1]))
        elif ch != '2': die('X kill with choice %s (only 5, certificate, and 2, expanded)' % ch)
    elif t == 'P': cur['P'].append((0, int(a[1]), int(a[2])))
    elif t == 'DM': cur['P'].append((1, int(a[1]), 0))
    elif t == 'TY': cur['P'].append((2, int(a[1]), 0))
    elif t == 'CN': cur['CN'].append((int(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5])))
    elif t in ('DN', 'JB'):
        # an external child: the piece (DN) or job (JB) segment rooted at this node's child u; the item's key lists it (ext), in
        # stream order (r3qglue --itemkey's order)
        u = int(a[1]); cur['XM'].append(u); EXTSEQ.append((cur, u))
    elif t == 'RG':
        # a range reference: the node's children from l on are a range segment's ((S, last), l); it ends the node's records
        l_ = int(a[1]); cur['RG'] = l_; RNGSEQ.append((cur, l_)); stack.pop()
    elif t in ('WB', 'BLK', 'AF', 'SR', 'SK'): die('record %s not in this checker' % t)
if root_dead is not None:
    if recs: die('a dead root with OPEN records')
    a = root_dead['a']; t = a[0]; dkr = dict(u=root_dead['u'], d=root_dead['d'], V=root_dead['V'])
    if t == 'L':
        if root_dead['d'] != 22 or a[1] not in ('0', '4'): die('root leaf code %s' % a[1])
        dkr.update(kind='leaf') if a[1] == '0' else dkr.update(kind='flook', pos=None)
        if a[1] == '0' and len(a) > 4 and a[2] == 'v7': dkr['Rs'] = (int(a[3]), int.from_bytes(bytes.fromhex(a[4]), 'little'))
    else:
        ck = int(a[1])
        if ck == 3: dkr.update(kind='flook', pos=int(a[2]))
        elif ck in (1, 2, 4, 7, 8, 9, 10):
            arg = int(a[2]) if ck == 1 else 0
            if ck == 1 and not 0 < arg < 512: die('root node cut 1 with split / wlook')
            dkr.update(kind='cut', ck=ck, arg=arg, rid=int(a[2]) if ck in (2, 10) else None)
        elif ck == 11 and int(a[3]) in (1, 2):
            dim = int(a[4]); basis = [int(x) for x in a[5:5 + dim]]
            dkr.update(kind='cut', ck=2, arg=0, rid=None, sub=span9(basis))
        elif ck in (5, 6):
            if not ('xp' in a and a[a.index('xp') + 1] == '1'): die('root node cut %d without a certificate' % ck)
            ie, inode, icert = a.index('ex'), a.index('node'), a.index('cert')
            dkr.update(kind='xcut', cu=dict(u=dkr['u'], kind=ck, bb=int(a[2]), ex=[int(x) for x in a[ie + 1:inode]],
                                            nd=bytes.fromhex(a[inode + 1]), ce=bytes.fromhex(a[icert + 1])))
        else: die('root node cut %d: not in this checker' % ck)
    root_dead = dkr
print('item: %d OPEN records, %d dead children, %d kinds records, %d CANON' % (len(recs), sum(len(r['DK']) for r in recs),
      sum(len(r['P']) for r in recs), sum(len(r['CN']) for r in recs)), flush=True)

# ---------------- v7 leaf records (the pinned generator, as batch 13's --leafv7) ----------------
import subprocess
GEN7C = R22 + '/lean/hcls/E1P/cpp/gen7c'
stats = collections.Counter()
leafq = []
def leaf_labels(r, u):
    labs = []; q = r
    while q is not None: labs.append(q['l']); q = q['parent']
    return sorted(list(root[:-1]) + labs + [u])
def v7_from_stream(dk):
    """the stream's v7 record (FLAGS_NATIVE --leafv7), checked against the layout and the leaf's codes"""
    nb_, R_ = dk['Rs']
    if R_ >> nb_: die('v7 record longer than its bit count')
    if (R_ & 63) != 22 or [(R_ >> (6 + 9 * i)) & 511 for i in range(22)] != [labv[l] for l in dk['labs']]:
        die('v7 record does not match the leaf')
    if (R_ >> (6 + 9 * 22)) & 3 != 2: die('v7 record dm / lg bits')
    dk['R'] = R_; stats['v7stream'] += 1
for r in recs:
    for dk in r['DK']:
        if dk['kind'] == 'leaf':
            dk['labs'] = leaf_labels(r, dk['u'])
            if 'Rs' in dk: v7_from_stream(dk)
            else: leafq.append(dk)
if root_dead is not None and root_dead['kind'] == 'leaf':
    root_dead['labs'] = sorted(list(root[:-1]) + [root_dead['u']])
    if 'Rs' in root_dead: v7_from_stream(root_dead)
    else: leafq.append(root_dead)
if leafq:
    inp = ''.join(','.join(str(labv[l]) for l in dk['labs']) + ' all\n' for dk in leafq)
    outl = subprocess.run([GEN7C, '--lg'], input=inp, capture_output=True, text=True).stdout.split('\n')
    for dk, o in zip(leafq, outl):
        f = o.split()
        if not f: die('gen7c: no output')
        n = len(dk['labs']); assert n == 22
        if f[0] == 'NONE': cert, nb = 0, 0
        else: cert, nb = int(f[0], 16), int(f[1])
        R = n
        for i, l in enumerate(dk['labs']): R |= labv[l] << (6 + 9 * i)
        pp = 6 + 9 * n
        R |= (0 << pp) | (1 << (pp + 1)) | (cert << (pp + 2))
        dk['R'] = R; dk['nbits'] = pp + 2 + nb
    print('v7 leaf records: %d (gen7c --lg, full domain)' % len(leafq), flush=True)

# ---------------- rows (kx3.py) ----------------
def compact(r):
    ex, c1, c2l = r['XR']
    ue = sorted({i for (u, t, ei, cr) in r['K'] for i in ei})
    u1 = sorted({c >> 1 for (u, t, ei, cr) in r['K'] for c in cr if not c & 1})
    u2 = sorted({c >> 1 for (u, t, ei, cr) in r['K'] for c in cr if c & 1})
    me = {i: k for k, i in enumerate(ue)}; m1 = {i: k for k, i in enumerate(u1)}; m2 = {i: k for k, i in enumerate(u2)}
    r['XR'] = ([ex[i] for i in ue], [c1[i] for i in u1], [c2l[i] for i in u2])
    r['K'] = [(u, t, [me[i] for i in ei], [((m2[c >> 1] << 1) | 1) if c & 1 else (m1[c >> 1] << 1) for c in cr]) for (u, t, ei, cr) in r['K']]
for r in recs: compact(r)
XPVAR = HDR.get('#xpvar', '#xpvar 0').split()[1] == '1'   # FLAGS_NATIVE streams: bulk-peel blobs as LEB128 varint item lists
def kitems(b):
    if XPVAR:
        out = []; x = 0; sh = 0
        for c in b:
            x |= (c & 127) << sh; sh += 7
            if not c & 128: out.append(x); x = 0; sh = 0
        if sh != 0: die('truncated varint blob')
        return out
    out = []; o = 0
    while o + 8 <= len(b):
        n = int.from_bytes(b[o:o + 8], 'little'); out.append(int.from_bytes(b[o + 8:o + 8 + n], 'little')); o += 8 + n
    return out
need_rows = {0}   # row 0 always: an item without rows (a top segment in collection mode) writes it as its one table row
for r in recs:
    if r['XPN'] is not None:
        it = kitems(r['XPN']); q = 0; nQ = it[q]; q += 1 + nQ; nd = it[q]; q += 1
        r['XD'] = [(it[q + 2 * j], it[q + 2 * j + 1]) for j in range(nd)]; q += 2 * nd
        nn = it[q]; q += 1; r['XNR'] = it[q:q + nn]; q += nn
        nB = it[q]; q += 1; r['XAG'] = []
        for _ in range(nB):
            x, nr_ = it[q], it[q + 1]; q += 2; r['XAG'].append((x, it[q:q + nr_])); q += nr_
    else: r['XD'] = []; r['XNR'] = []; r['XAG'] = []
    need_rows.update(r['V']); need_rows.update(r['XR'][0]); need_rows.update(r['XR'][1]); need_rows.update(r['XR'][2])
    need_rows.update(i for i, _ in r['XD'])
    for cu in r.get('CUTS', []):
        it = kitems(cu['nd']); q = 0; nQ = it[q]; q += 1 + nQ; nd_ = it[q]; q += 1
        cu['D'] = [(it[q + 2 * j], it[q + 2 * j + 1]) for j in range(nd_)]; q += 2 * nd_
        nn = it[q]; q += 1; cu['NR'] = it[q:q + nn]; q += nn
        if q != len(it): die('cut node record bytes left over')
        need_rows.update(i for i, _ in cu['D']); need_rows.update(cu['ex'])
    for dk in r['DK']:
        need_rows.update(dk['V'])
        if dk.get('rid') is not None: need_rows.add(dk['rid'])
subs = [dk for r in recs for dk in r['DK'] if dk.get('sub')] + ([root_dead] if root_dead is not None and root_dead.get('sub') else [])
if subs:
    want = {dk['sub'] for dk in subs}; found = {}
    with open(rowsf) as f:
        for i, line in enumerate(f):
            a = line.split(); pts = tuple(sorted(int(x) for x in a[2:]))
            if pts in want and (pts not in found or int(a[1]) < found[pts][1]): found[pts] = (i, int(a[1]))
    for dk in subs:
        if dk['sub'] not in found: die('replay cut: subspace %s is not a kept row' % (dk['sub'],))
        dk['rid'] = found[dk['sub']][0]; need_rows.add(dk['rid'])
    stats_replay = len(subs)
else: stats_replay = 0
if root_dead is not None:
    need_rows.update(root_dead['V'])
    if root_dead.get('rid') is not None: need_rows.add(root_dead['rid'])
    if root_dead['kind'] == 'xcut':
        cu = root_dead['cu']; it = kitems(cu['nd']); q = 0; nQ = it[q]; q += 1 + nQ; nd_ = it[q]; q += 1
        cu['D'] = [(it[q + 2 * j], it[q + 2 * j + 1]) for j in range(nd_)]; q += 2 * nd_
        nn = it[q]; q += 1; cu['NR'] = it[q:q + nn]; q += nn
        if q != len(it): die('cut node record bytes left over')
        need_rows.update(i for i, _ in cu['D']); need_rows.update(cu['ex'])
need_rows.update(WIT)
rows = {}
with open(rowsf) as f:
    for i, line in enumerate(f):
        if i in need_rows:
            a = line.split(); m = 0
            for v in a[2:]: m |= 1 << lab[int(v)]
            rows[i] = (int(a[1]), m)
if len(rows) != len(need_rows): die('missing rows')
import mmap
rtf = open(rtbin, 'rb'); rtm = mmap.mmap(rtf.fileno(), 0, access=mmap.ACCESS_READ)
for i in need_rows:
    e = int.from_bytes(rtm[16 * i:16 * i + 16], 'little'); d = e % 16; V = [(e >> (4 + 9 * j)) % 512 for j in range(9)]; cap = (e >> 85) % 32
    dual = V[d:]; lm = 0
    for l, v in enumerate(labv):
        if all(par(v & w) == 0 for w in dual): lm |= 1 << l
    if lm != rows[i][1] or cap != rows[i][0]: die('row %d differs between the kept-row file and the RT entries' % i)
for r in recs:
    ex, c1, c2l = r['XR']
    r['V5'] = [x for x in r['V'] if rows[x][0] >= 3]
    exs = set(ex); R1 = list(ex) + [x for x in c1 if x not in exs]; R1i = {x: k for k, x in enumerate(R1)}
    r['R1'] = R1; r['R2'] = list(c2l)
    r['K5'] = [(u, t, [R1i[ex[i]] for i in ei], [((R1i[c1[c >> 1]], 1) if not c & 1 else (c >> 1, 2)) for c in cr]) for (u, t, ei, cr) in r['K']]
def kdecode_tree27(it, q):
    """kill2's 27.11 tree (node cuts 5 / 6): leaf 0, ns, (X, d)*, finX, finD; node 1, ns, (X, d)*, v, c2flag, nb, row idx*, left,
    right (the in-branch's rows become its own aggregate); budget cut 2, 0"""
    tag = it[q]; ns = it[q + 1]; q += 2; sts = [(it[q + 2 * j], it[q + 2 * j + 1]) for j in range(ns)]; q += 2 * ns
    if tag == 2:
        if ns != 0: die('cut with steps')
        return ('C',), q
    if tag == 0:
        return ('L', sts, (it[q], it[q + 1])), q + 2
    if tag != 1: die('27.11 tree tag %d' % tag)
    v = it[q]; nb = it[q + 2]; ri = it[q + 3:q + 3 + nb]; q += 3 + nb
    l, q = kdecode_tree27(it, q); rr, q = kdecode_tree27(it, q)
    return ('N27', sts, v, ri, l, rr), q
def kdecode_tree(it, q):
    tag = it[q]; ns = it[q + 1]; q += 2; sts = [(it[q + 2 * j], it[q + 2 * j + 1]) for j in range(ns)]; q += 2 * ns
    if tag == 2:
        assert ns == 0, 'cut with steps'
        return ('C',), q
    if tag == 0:
        fin = (it[q], it[q + 1]); return ('L', sts, fin), q + 2
    v = it[q]; q += 1
    l, q = kdecode_tree(it, q); rr, q = kdecode_tree(it, q)
    return ('N', sts, v, l, rr), q
for r in recs:
    # a node without dictionary rows can still have X kills (choice 5) whose certificates use no rows (counting alone)
    if not r['XD'] and not r.get('CUTS') and not r['XC']: r['KIDS'] = []; r['X1'] = []; r['X2'] = []; r['XPOS'] = []; continue
    R1 = r['R1']; R2 = r['R2']; i1 = {x: k for k, x in enumerate(R1)}; i2 = {x: k for k, x in enumerate(R2)}
    X1 = []; X2 = []; j1 = {}; j2 = {}; xpos = []
    for (rid, res) in r['XD']:
        if res == 1:
            if rid in i1: xpos.append(('1', i1[rid]))
            else:
                if rid not in j1: j1[rid] = len(X1); X1.append(rid)
                xpos.append(('x1', j1[rid]))
        elif res == 2:
            if rid in i2: xpos.append(('2', i2[rid]))
            else:
                if rid not in j2: j2[rid] = len(X2); X2.append(rid)
                xpos.append(('x2', j2[rid]))
        else: die('bulk-peel row with residual %d' % res)
    def place(rid, res):
        if res == 1:
            if rid in i1: return ('1', i1[rid])
            if rid not in j1: j1[rid] = len(X1); X1.append(rid)
            return ('x1', j1[rid])
        if res == 2:
            if rid in i2: return ('2', i2[rid])
            if rid not in j2: j2[rid] = len(X2); X2.append(rid)
            return ('x2', j2[rid])
        die('cut row with residual %d' % res)
    for cu in r.get('CUTS', []):
        cu['CPOS'] = [place(rid, res) for (rid, res) in cu['D']]; cu['EXPOS'] = [place(rid, 1) for rid in cu['ex']]
        it = kitems(cu['ce']); kind, bb, u, tt, Fu, ncr = it[:6]; cr = it[6:6 + ncr]; tree, q = kdecode_tree27(it, 6 + ncr)
        if q != len(it): die('cut certificate bytes left over')
        if u != cu['u']: die('cut certificate for child %d, node %d' % (u, cu['u']))
        cu['KID'] = (kind, bb, u, Fu, cr, tree)
    r['XPOS'] = xpos; r['X1'] = X1; r['X2'] = X2
    kids = []
    for cb in r['XC']:
        it = kitems(cb); kind, bb, u, tt, Fu, ncr = it[:6]; cr = it[6:6 + ncr]; tree, q = kdecode_tree(it, 6 + ncr)
        assert q == len(it), 'certificate bytes left over'
        kids.append((kind, bb, u, Fu, cr, tree))
    r['KIDS'] = kids

# ---------------- static tables ----------------
c2raw = open(c2tf, 'rb').read(); TAB = 511 * 64
c2t = {}
def c2(l):
    if l not in c2t: c2t[l] = int.from_bytes(c2raw[l * TAB:(l + 1) * TAB], 'little')
    return c2t[l]
CONF1T = int.from_bytes(c2raw[511 * TAB:512 * TAB], 'little')
hyp = open(R22 + '/lean/rerun/r3/rt321/hyp7_321.bin' if ORD == '321' else R22 + '/lean/l1/hyp7.bin', 'rb').read()
HT = [int.from_bytes(hyp[l * 448:(l + 1) * 448], 'little') for l in range(511)]
SUFT = [int.from_bytes(hyp[(511 + l) * 448:(512 + l) * 448], 'little') for l in range(511)]
ONES7 = sum(1 << (7 * X) for X in range(512))
RKT = RG.RK
OFFN7 = sum((64 - 3 * RKT[X]) << (7 * X) for X in range(512)); G7 = sum(64 << (7 * X) for X in range(512))
def slot(N, u): return (N >> (512 * u)) & M512
def above(u): return (M511 >> (u + 1)) << (u + 1)
def geM(b): return (M511 >> b) << b
def fld7(U, X): return (U >> (7 * X)) & 127
NPERP = [sum(1 << l for l, v in enumerate(labv) if par(v & X)) for X in range(512)]
REPL = sum(1 << (512 * i) for i in range(511)); DIAGL = sum(1 << (513 * i) for i in range(511))

# ---------------- node records (kx3.py's mkrec / model / xpart, KX2_NOB layout) ----------------
def mkrec(r, P, pops):
    S = 0
    for l in P: S |= 1 << l
    def resid(x): cap, mask = rows[x]; return cap - pc(S & mask)
    V5, R1, R2 = r['V5'], r['R1'], r['R2']
    for x in V5:
        if not resid(x) == 0: soft('row residual: %s %d' % ('V row not full', x))
    for x in R1:
        if not resid(x) == 1: soft('row residual: %s %d' % ('R1 row', x))
    for x in r.get('X1', []):
        if not resid(x) == 1: soft('row residual: %s %d' % ('X1', x))
    for x in r.get('X2', []):
        if not resid(x) == 2: soft('row residual: %s %d' % ('X2', x))
    for x in R2:
        if not resid(x) == 2: soft('row residual: %s %d' % ('R2 row', x))
    kills = []
    for (u, typ, ei, cv) in r['K5']:
        for i in ei:
            if not (rows[R1[i]][1] >> u) & 1: soft('ex row without u: %d' % R1[i])
        idx = []
        for (jj, cls) in cv:
            if cls == 1:
                if (rows[R1[jj]][1] >> u) & 1: soft('R1 cover row with u')
                idx.append(jj)
            else:
                if not (rows[R2[jj]][1] >> u) & 1: soft('R2 cover row without u')
                idx.append(len(R1) + jj)
        assert len(ei) < 32 and len(idx) < 32 and len(R1) + len(R2) < 1024 and len(V5) < 1024
        v = u | (len(ei) << 9) | (len(idx) << 14); sh = 19
        for i in ei: v |= i << sh; sh += 10
        for i in idx: v |= i << sh; sh += 10
        kills.append(v)
    mrows = list(V5) + list(R1) + list(R2)
    E = [pc(S & rows[x][1]) for x in mrows]
    MB = 0
    for i, x in enumerate(mrows): MB |= rows[x][1] << (512 * i)
    Eb = sum(e << (8 * i) for i, e in enumerate(E))
    body = MB | (Eb << (512 * len(mrows)))
    rec = pops | (P[-1] << 8) | (len(P) << 17) | (len(V5) << 22) | (len(R1) << 32) | (len(R2) << 52) | (body << 64)
    return rec, kills, mrows

def model(st, r, rec, kills):
    S, D, N, U, dP = st
    V5, R1, R2 = r['V5'], r['R1'], r['R2']
    last = (rec >> 8) & 511; d = (rec >> 17) & 31
    S2 = S | (1 << last); N2 = N | c2(last); U2 = U + HT[last]
    if (S >> last) != 0 or d != dP + 1: return None, 'depth/prefix'
    if ((U2 + (22 - d) * ONES7 + OFFN7) & G7) != G7: return None, 'hyperplane rem test'
    if ((U2 + SUFT[last] + OFFN7) & G7) != G7: return None, 'hyperplane suffix test'
    D2 = D | slot(N, last)
    for x in V5: D2 |= rows[x][1]
    w0 = last + 1; CH = (M511 >> w0) << w0; Fn = CH & ~D2
    nu = 21 - d; cl = list(R1) + list(R2)
    for kr in kills:
        u = kr & 511; nX = (kr >> 9) & 31; nC = (kr >> 14) & 31; rr = kr >> 19
        if u < w0: return None, 'kill label'
        X = Fn & above(u) & ~slot(N2, u); A = (1 << 512) - 1
        for _ in range(nX):
            i = rr & 1023; rr >>= 10
            mask = rows[R1[i]][1] if i < len(R1) else 0
            X &= ~mask; A &= mask
        if not (A >> u) & 1: return None, 'ex row without u'
        C = 0; nc = 0
        for _ in range(nC):
            i = rr & 1023; rr >>= 10; mask = rows[cl[i]][1]
            if ((mask >> u) & 1) != (0 if i < len(R1) else 1): return None, 'cover row side'
            C |= mask; nc += 1
        if not (nc + pc(X & ~C) < nu): return None, 'kill count'
    return (S2, D2, N2, U2, d), None

def xpart(r, nV, n1, n2, X1, X2):
    r"""the node's bulk-peel part in KD.batchX's layout (kx3.py), with its node cuts 5 / 6 merged in as further children: each cut's
    rows join the dictionary (extras), its node rows and ex rows join the node rows, every in-branch of its 27.11 tree becomes its
    own aggregate {x = u + 1 + v, rows}, its steps join the deficit table, and its F_u is the hybrid (above(u) \ D') \ Anode[u]
    (the X tier's XT/Cut.lean conversion).  With cuts, the other children's F_u become the hybrid set too (KD.fuX is exact; the
    certificate's own F_u contains it, and its counts only drop on the smaller set)."""
    S2, D2, N2, U2, d = r['FR']
    m = nV + n1 + n2; b1 = nV + n1; e1 = m + len(X1)
    off = {'1': nV, '2': nV + n1, 'x1': m, 'x2': m + len(X1)}
    pos = [off[c] + k for (c, k) in r['XPOS']]
    cuts = r.get('CUTS', [])
    for cu in cuts:
        cu['cpos'] = [off[c] + k for (c, k) in cu['CPOS']]; cu['expos'] = [off[c] + k for (c, k) in cu['EXPOS']]
    def pmask(p):
        if p < nV: return rows[r['V5'][p]][1]
        if p < nV + n1: return rows[r['R1'][p - nV]][1]
        if p < m: return rows[r['R2'][p - nV - n1]][1]
        if p < e1: return rows[X1[p - m]][1]
        return rows[X2[p - e1]][1]
    def r1pos(p): return p < b1 or (m <= p < e1)
    nr = [pos[i] for i in r['XNR']]
    for cu in cuts: nr += [cu['cpos'][i] for i in cu['NR']] + cu['expos']
    seen = set(); nr = [p for p in nr if not (p in seen or seen.add(p))]
    for p in nr:
        if not r1pos(p): die('node row of residual 2')
    use = {}
    def picks(t, u):
        if t[0] in ('L', 'C'): return
        use[u + 1 + t[2]] = use.get(u + 1 + t[2], 0) + 1
        picks(t[3], u); picks(t[4], u)
    for (kind, bb, u, Fu, cr, tree) in r['KIDS']: picks(tree, u)
    aggs_sorted = sorted(r['XAG'], key=lambda a: (-use.get(a[0], 0), a[0]))
    aggi = {}; aggv = []
    for k, (x, idxs) in enumerate(aggs_sorted):
        ps = [pos[i] for i in idxs]
        aggv += [x, len(ps)] + ps + [rows[r['XD'][i][0]][1] for i in idxs]
        aggi[x] = k
    nag = len(aggs_sorted)
    # the cuts' in-branches: one aggregate each, in tree preorder
    def cut_aggs(t, u, cpos):
        nonlocal nag, aggv
        if t[0] in ('L', 'C'): return t
        if t[0] != 'N27': die('cut tree node %s' % t[0])
        x = u + 1 + t[2]
        if not x < 511: die('cut in-branch pick %d outside the window' % x)
        ps = [cpos[i] for i in t[3]]
        k = nag; nag += 1
        aggv += [x, len(ps)] + ps + [pmask(p_) for p_ in ps]
        return ('N', t[1], t[2], cut_aggs(t[4], u, cpos), cut_aggs(t[5], u, cpos), k)
    cutkids = []
    for cu in cuts:
        kind, bb, u, Fu, cr, tree = cu['KID']
        cutkids.append((kind, bb, u, Fu, [cu['cpos'][i] for i in cr], cut_aggs(tree, u, cu['cpos'])))
    out = [len(nr)] + nr + [nag] + aggv
    nrm = [pmask(p) for p in nr]
    def anode_slot(u):
        a = slot(N2, u)
        for mk in nrm:
            if (mk >> u) & 1: a |= mk
        return a & ~(1 << u) & M511
    Xs = set()
    def scan(t):
        if t[0] == 'C': return
        for (X, dd) in t[1]: Xs.add(X)
        if t[0] == 'L': Xs.add(t[2][0])
        else: scan(t[3]); scan(t[4])
    for (kind, bb, u, Fu, cr, tree) in r['KIDS']: scan(tree)
    for (kind, bb, u, Fu, crp, tree) in cutkids: scan(tree)
    XL = sorted(Xs); jx = {X: j for j, X in enumerate(XL)}
    HP = 0; DEFP = 0
    for j, X in enumerate(XL):
        if X == 0: H = M511; dv = 22 - d
        else: H = NPERP[X]; dv = 3 * RKT[X] - fld7(U2, X)
        if dv < 0: dv = 0
        assert dv < 256
        HP |= H << (512 * j); DEFP |= dv << (8 * j)
    out += [len(XL)] + XL + [HP, DEFP, len(r['KIDS']) + len(cutkids)]
    TB = 21 - d
    def conv(t, u, pk=frozenset()):
        res = []
        if t[0] == 'C':
            if not len(pk) > TB: soft('cut with %d picks at u=%d, budget %d' % (len(pk), u, TB))
            return [2, 0]
        def st_ok(X, dd):
            j = jx[X]; H = (HP >> (512 * j)) & M511; dv = (DEFP >> (8 * j)) & 255
            if not (dd >= 1 and dd + ((H >> u) & 1) <= dv): soft('step (%d,%d) at u=%d: bound %d' % (X, dd, u, dv))
            return [j, dd]
        if t[0] == 'L':
            res += [0, len(t[1])]
            for (X, dd) in t[1]: res += st_ok(X, dd)
            res += st_ok(t[2][0], t[2][1])
            return res
        res += [1, len(t[1])]
        for (X, dd) in t[1]: res += st_ok(X, dd)
        v = t[2]
        if len(t) > 5: k = t[5]   # a cut's in-branch: its own aggregate
        else:
            x = u + 1 + v
            if x not in aggi: die('no aggregate for pick %d' % x)
            k = aggi[x]
            AGGWALK[0] += k + 1
        res += [v, k] + conv(t[3], u, pk | {v}) + conv(t[4], u, pk)
        return res
    for (kind, bb, u, Fu, cr, tree) in r['KIDS']:
        Fc = (M511 >> (u + 1) << (u + 1)) & ~D2 & ~anode_slot(u) & M511
        if cuts:
            # the cuts' node rows join Anode, so F_u can only shrink; KD.fuX wants F_u exactly (above(u) \ D') \ Anode[u], and the
            # child's certificate stays valid on the smaller set (its counts only drop): the hybrid set is written
            if Fc & ~Fu: soft("F_u does not contain (above(u) \\ D') \\ Anode[u] at u=%d" % u)
            if Fc != Fu: stats['kid_fu_hybrid'] += 1
            Fu = Fc
        elif Fc != Fu: soft("F_u differs from (above(u) \\ D') \\ Anode[u] at u=%d" % u)
        crp = [pos[i] for i in cr]
        for p_ in crp:
            if not (r1pos(p_) or (pmask(p_) >> u) & 1): die('child row of residual 2 not through u')
            CRSEEN.add(p_)
            if not r1pos(p_): CR2[0] += 1
            if KI_FEAT: CRPOS.append(p_)
        out += [kind, bb, u, Fu, len(crp)] + crp + conv(tree, u)
    for (kind, bb, u, Fu0, crp, tree) in cutkids:
        Fu = (M511 >> (u + 1) << (u + 1)) & ~D2 & ~anode_slot(u) & M511   # the hybrid F_u (XT.fixFu)
        if Fu & ~Fu0: stats['cut_fu_outside'] += 1   # the hybrid set should lie inside the certificate's own F_u (monotonicity)
        for p_ in crp:
            if not (r1pos(p_) or (pmask(p_) >> u) & 1): die('cut child row of residual 2 not through u')
        out += [kind, bb, u, Fu, len(crp)] + crp + conv(tree, u)
        stats['xcut'] += 1
    return out

# ---------------- the extension: PREFF, CANON (C3 node records with C3.LABT), flook cut children ----------------
def preff_ok(U, d, u, X):
    if not (0 < X < 512): return False
    r = 3 * RKT[X]; h = fld7(U, X) + par(labv[u] & X)
    if not h < r: return False
    return h + (21 - d) < r or pc(NPERP[X] >> (u + 1)) <= r - h - 1
R1M = (1 << 49) - 1; R12M = (1 << 343) - 1; R2M = R12M ^ R1M; R3M = M511 ^ R12M
def cut_model(S, D, U, W, d, last, kind, arg, m, cap):   # model of KD.cutOK (kcut.py)
    if (S >> last) != 1 or d > 22: return False
    AV = M511 & ~(D | W)
    need = 22 - d
    if kind == 1:
        X = arg
        if not (0 < X < 512): return False
        h = fld7(U, X); r = 3 * RKT[X]
        return h < r and (h + need < r or pc(NPERP[X] >> (last + 1)) <= r - h - 1)
    if kind in (4, 9): return d <= 21 and pc(AV & above(last)) <= 21 - d
    if kind == 7:
        if d > 21: return False
        s1 = S & R1M_
        return pc(s1 | (R1M_ & above(last) & AV)) <= 13 or (need <= 13 and pc(s1) <= 13 - need)
    if kind == 8:
        R12 = (1 << 343) - 1; R2 = R12 ^ R1M_; R3 = M511 ^ R12
        c1, c2_, c3 = pc(S & R1M_), pc(S & R2), pc(S & R3)
        for y in range((need if last < 49 else 0) + 1):
            for x in range(((need - y) if last < 343 else 0) + 1):
                if typeOK(c1 + y, c2_ + x, c3 + (need - y - x)): return False
        return True
    if kind in (2, 10): return pc(S & m) > cap
    return False
R1M_ = (1 << 49) - 1
def doom_ok(S, AV, d, u):   # model of KD's DOOM record (kconv.py)
    s1 = S & R1M; nn = 21 - d
    if u < 49: return pc(s1 | (R1M & above(u) & AV)) <= 12 or (nn <= 12 and pc(s1) <= 12 - nn)
    return pc(s1) <= 13
def typeOK(n1, n2, n3):
    if n1 + n2 + n3 != 22: return True
    return (n2 + 2 * n3 >= 7 or (n2, n3) == (6, 0)) and (n1, n2, n3) not in ((17, 3, 2), (18, 1, 3))   # --typecut 95 (KD.typeOK)
def wintest321(r, ra, rb, n, lo, hi):   # k321.py's window test (KD321.winTest)
    return r + min(ra, n) < lo or hi < r or rb + min(ra, max(0, hi - r)) < n
def doom321(S, D, d, u):   # k321.py's model of KD321.doomOKO at the case's window
    av = above(u) & (M511 & ~D)
    r12 = min(22, pc(S & R1M321)) + ((R1M321 >> u) & 1)
    return wintest321(r12, min(22, pc(av & R1M321)), min(22, pc(av & NR1M321)), 21 - d, KLO, KHI)
def win321(S, D, d, last):   # k321.py's model of KD321.cut7O (winOKO) at the case's window
    if (S >> last) != 1 or d > 22: return False
    av = above(last) & (M511 & ~D)
    return wintest321(min(22, pc(S & R1M321)), min(23, pc(av & R1M321)), min(23, pc(av & NR1M321)), 22 - d, KLO, KHI)
def ty_ok(S, d, u):   # model of KD's TYPE record (kconv.py)
    c1 = pc(S & R1M) + (1 if u < 49 else 0); c2_ = pc(S & R2M) + (0 if u < 49 else (1 if u < 343 else 0)); c3 = pc(S & R3M) + (0 if u < 343 else 1)
    nd = 21 - d
    for y in range((nd if u < 49 else 0) + 1):
        for x in range(((nd - y) if u < 343 else 0) + 1):
            if typeOK(c1 + y, c2_ + x, c3 + (nd - y - x)): return False
    return True
R = R22 + '/lean'
CT = json.load(open(R + '/canon/tab.json')); GL = set(CT['gl']); LAB = CT['lab']
if ORD == '321':
    # the 321 key table Top321.LABT321 (code -> label + 1), as k321.py reads it; it must agree with the stream's #lab
    _src = open(R + '/native/infra/port/out/src/Top/Root321.lean').read()
    _LT = int(_src.split('def LABT321 : ℕ := ')[1].split()[0], 16)
    LAB = [(_LT >> (9 * v)) & 511 for v in range(512)]
    if any(LAB[labv[l]] != l + 1 for l in range(511)): die('the 321 key table disagrees with the stream\'s #lab')
def mulF(u, v): return (((u & 73) * (v & 7)) ^ (((u >> 1) & 73) * ((v >> 3) & 7)) ^ (((u >> 2) & 73) * ((v >> 6) & 7)))
def trN(v): return (v & 273) | ((v & 34) << 2) | ((v & 136) >> 2) | ((v & 4) << 4) | ((v & 64) >> 4)
def gF(t, P, Q, v): return mulF(mulF(P, trN(v) if t else v), Q)
def fld9(S, i): return (S >> (9 * i)) & 511
def chk_node(S, o):   # Python mirror of C3T.nodeOK with LAB
    k = fld9(S, o); seq = [fld9(S, o + 1 + i) for i in range(k)]; Tb = 0
    for v in seq: Tb |= 1 << LAB[v]
    r = fld9(S, o + k + 1); st = []
    for i in range(r):
        t, P, Q = fld9(S, o + k + 2 + 3 * i), fld9(S, o + k + 3 + 3 * i), fld9(S, o + k + 4 + 3 * i)
        if P not in GL or Q not in GL: return False, 0
        Ib = 0
        for v in seq: Ib |= 1 << LAB[gF(t, P, Q, v)]
        if Ib != Tb: return False, 0
        st.append((t, P, Q))
    nW = fld9(S, o + k + 2 + 3 * r); w = o + k + 3 + 3 * r
    for _ in range(nW):
        l = fld9(S, w); kind = fld9(S, w + 1)
        if kind == 0:
            i = fld9(S, w + 2)
            if i >= r: return False, 0
            m = LAB[gF(*st[i], l)]
            if not (m < LAB[l] and not (Tb >> m) & 1): return False, 0
            w += 3
        else:
            t, P, Q, j = fld9(S, w + 2), fld9(S, w + 3), fld9(S, w + 4), fld9(S, w + 5); T1 = Tb | (1 << LAB[l])
            if P not in GL or Q not in GL: return False, 0
            hs = [fld9(S, w + 6 + i) for i in range(j + 1)]
            if any(not (T1 >> LAB[h]) & 1 for h in hs): return False, 0
            m = LAB[gF(t, P, Q, hs[0])]
            if (T1 >> m) & 1: return False, 0
            Ib = 0
            for h in hs[1:]: Ib |= 1 << LAB[gF(t, P, Q, h)]
            low = T1 & ((1 << m) - 1)
            if low & Ib != low: return False, 0
            w += 7 + j
    return True, w
def canon_records(seq, cns):
    Tvs = [labv[x] for x in seq]; k = len(seq)
    ws = []
    for (l, typ, t, P, Q) in cns:
        Tl = seq + [l]; Tv = Tvs + [labv[l]]
        img = [LAB[gF(t, P, Q, v)] - 1 for v in Tv]; simg = sorted(img)
        j = 0
        while j <= k and simg[j] == Tl[j]: j += 1
        if not (j <= k and simg[j] < Tl[j]): soft('CANON record is not a witness'); continue
        stab = int(sorted(img[:k]) == seq)
        H = [Tv[img.index(simg[q])] for q in range(j + 1)]
        ws.append((labv[l], typ, j, stab, t, P, Q, H))
    grp = collections.OrderedDict()
    for w in ws:
        if w[3]: grp.setdefault((w[4], w[5], w[6]), []).append(w)
    use = [g for g, L in grp.items() if k + len(L) < sum(x[2] + 1 for x in L)]
    idx = {g: i for i, g in enumerate(use)}
    W = []
    for (l, typ, j, stab, t, P, Q, H) in ws:
        g = (t, P, Q)
        if stab and g in idx: W.append([l, 0, idx[g]])
        else: W.append([l, 1, t, P, Q, j, H[j]] + H[:j])
    out = []
    for s in range(0, len(W), 511):
        part = W[s:s + 511]; used = sorted(set(x[2] for x in part if x[1] == 0)); remap = {u: i for i, u in enumerate(used)}
        f = [k] + Tvs + [len(used)]
        for u in used: f += list(use[u])
        f.append(len(part))
        for x in part: f += ([x[0], 0, remap[x[2]]] if x[1] == 0 else x)
        Sc = 0
        for i, x in enumerate(f): Sc |= x << (9 * i)
        ok, o2 = chk_node(Sc, 0)
        if not (ok and o2 == len(f)): die('python C3T check failed')
        out.append(Sc)
    return out
def canon_kids(Sc):   # model of KD321.canonKids
    k = fld9(Sc, 0); r = fld9(Sc, k + 1); nW = fld9(Sc, k + 2 + 3 * r); w = k + 3 + 3 * r; m = 0
    for _ in range(nW):
        lt = LAB[fld9(Sc, w)]
        if lt >= 1: m |= 1 << (lt - 1)
        w = w + 3 if fld9(Sc, w + 1) == 0 else w + 7 + fld9(Sc, w + 5)
    return m
def abv(u): return (M511 >> (u + 1)) << (u + 1)
def fb_ok(U, d, F, X, c, Y):
    h = fld7(U, X); r = 3 * RKT[X] + c; need = 22 - d
    if not h <= r: return False
    if h + need <= r or pc(F & NPERP[X]) <= r - h: return True
    if 0 < Y < 512 and fld7(U, Y) < 3 * RKT[Y]:
        dY = 3 * RKT[Y] - fld7(U, Y)
        if need <= (r - h) + dY and pc(F & NPERP[X] & NPERP[Y]) <= (r - h) + dY - need: return True
    return False
def greedy_slack(TL, SL, SY, Q0, P0):
    """the slack functionals (with their SY) reordered greedily: at each depth the one leaving the fewest open (Q, P) states, counted
    with multiplicity; a state closes when Q = 1, P = 1, or the tight list has an odd set on it (RG.build's leaves)"""
    def closed(Q, P): return Q == 1 or P == 1 or RG.oddset(TL, Q, P) is not None
    states = [] if closed(Q0, P0) else [(Q0, P0)]
    rest = list(range(len(SL))); order = []
    while rest and states:
        best = None
        for j in rest:
            X = SL[j]; nxt = []
            for (Q, P) in states:
                for (q2, p2) in ((Q & RG.QXM[X], P), (Q, P & RG.PXM[X])):
                    if not closed(q2, p2): nxt.append((q2, p2))
            if best is None or len(nxt) < best[0]: best = (len(nxt), j, nxt)
        order.append(best[1]); rest.remove(best[1]); states = best[2]
    order += rest
    return [SL[j] for j in order], [SY[j] for j in order]

def flook_rec(S, D, U, d, last, tl):
    """kflook.py's certificate for the dead term tl at the cut node (S, D, U, d, last); None if not certified"""
    av = labv[tl]; need = 22 - d; F = (M511 & ~D) & abv(last)
    hits = [fld7(U, X) for X in range(512)]
    defY = [Y for Y in range(1, 512) if hits[Y] < 3 * RKT[Y]]
    TL, TY, SL, SY = [], [], [], []
    for X in range(1, 512):
        if not par(av & X): continue
        cF = pc(F & NPERP[X]); add = min(need, cF); s0 = hits[X] - 3 * RKT[X]; Yb = 0
        if s0 + add < 2 and defY:
            m = 0
            for Y in defY:
                mi = (3 * RKT[Y] - hits[Y]) - pc(F & NPERP[Y] & NPERP[X])
                if mi > m: m = mi; Yb = Y
            if need - m < add: add = max(0, need - m)
            else: Yb = 0
        sh = s0 + add
        if sh == 0: TL.append(X); TY.append(Yb)
        elif sh == 1 and RKT[X] < 3: SL.append(X); SY.append(Yb)
    if not TL and not SL: return None
    # an empty tight list is allowed (prof7 refutes some terms by slack-1 functionals only: q0 [] = p0 [] = 255; KB's flook check is
    # sound for nonzero b, c, i.e. KD.core_sound_le with Top.dec22_bc)
    if not TL: stats['flook_tl0'] += 1
    Q0, P0 = RG.q0p0(TL)
    # the slack order is free (fbOK checks each listed functional on its own; the walk takes slack[i] at depth i): the listed order
    # first, then a greedy order when the listed one gives no tree or a left subtree of 4096 bits or more (RootCheck's 12-bit field)
    enc = None
    for attempt in (0, 1):
        if attempt == 1:
            SL, SY = greedy_slack(TL, SL, SY, Q0, P0)
            stats['flook_greedy'] += 1
        tr = RG.build(TL, SL, Q0, P0, 0)
        if tr is None: continue
        try: enc = RG.enc_tree(tr, len(TL)); break
        except AssertionError: enc = None
    if enc is None: return None
    tv, _ = enc
    if not (all(fb_ok(U, d, F, X, 0, Y) for X, Y in zip(TL, TY)) and all(fb_ok(U, d, F, X, 1, Y) for X, Y in zip(SL, SY))
            and RG.walk(len(TL), TL, SL, tv, Q0, P0, 0)): return None
    return (tl, len(TL), tv, TL, TY, SL, SY)

def emit_xcut(cu, S2, D2, N2, U2, d2):
    """a node cut 5 / 6 of child cu['u'] of the node with frame (S2, D2, N2, U2, d2), as KB.DPay.xcut: its own dictionary (x1 =
    residual-1 rows and ex rows, x2 = residual-2 rows; positions x1 first), node rows = its node rows and the ex rows, one aggregate
    per in-branch, the deficit table of its steps, the child with the hybrid F_u (the X tier's XT/Cut.lean conversion)"""
    u = cu['u']
    X1 = []; X2 = []; j1 = {}; j2 = {}
    def place(rid, res):
        cap, mask = rows[rid]
        if cap - pc(S2 & mask) != res: die('xcut row %d: residual %d, record says %d' % (rid, cap - pc(S2 & mask), res))
        if res == 1:
            if rid not in j1: j1[rid] = len(X1); X1.append(rid)
            return ('x1', j1[rid])
        if res == 2:
            if rid not in j2: j2[rid] = len(X2); X2.append(rid)
            return ('x2', j2[rid])
        die('xcut row with residual %d' % res)
    cpl = [place(rid, res) for (rid, res) in cu['D']]; exl = [place(rid, 1) for rid in cu['ex']]
    def P_(t): return t[1] if t[0] == 'x1' else len(X1) + t[1]
    cpos = [P_(t) for t in cpl]; expos = [P_(t) for t in exl]
    def pmask(p_): return rows[X1[p_]][1] if p_ < len(X1) else rows[X2[p_ - len(X1)]][1]
    nr = [cpos[i] for i in cu['NR']] + expos
    seen = set(); nr = [p_ for p_ in nr if not (p_ in seen or seen.add(p_))]
    for p_ in nr:
        if not p_ < len(X1): die('xcut node row of residual 2')
    it = kitems(cu['ce']); kind, bb, ku, tt, Fu0, ncr = it[:6]; cr = it[6:6 + ncr]; tree, q = kdecode_tree27(it, 6 + ncr)
    if q != len(it) or ku != u: die('xcut certificate')
    aggv = []; nag = [0]
    def cut_aggs(t):
        if t[0] in ('L', 'C'): return t
        x = u + 1 + t[2]
        if not x < 511: die('xcut in-branch pick outside the window')
        ps = [cpos[i] for i in t[3]]
        k = nag[0]; nag[0] += 1
        aggv.extend([x, len(ps)] + ps + [pmask(p_) for p_ in ps])
        return ('N', t[1], t[2], cut_aggs(t[4]), cut_aggs(t[5]), k)
    tree = cut_aggs(tree)
    nrm = [pmask(p_) for p_ in nr]
    an = slot(N2, u)
    for mk in nrm:
        if (mk >> u) & 1: an |= mk
    an &= ~(1 << u) & M511
    Fu = (M511 >> (u + 1) << (u + 1)) & ~D2 & ~an & M511
    if Fu & ~Fu0: stats['cut_fu_outside'] += 1
    Xs = set()
    def scan(t):
        if t[0] == 'C': return
        for (X, dd) in t[1]: Xs.add(X)
        if t[0] == 'L': Xs.add(t[2][0])
        else: scan(t[3]); scan(t[4])
    scan(tree)
    XL = sorted(Xs); jx = {X: j for j, X in enumerate(XL)}
    HP = 0; DEFP = 0
    for j, X in enumerate(XL):
        if X == 0: H = M511; dv = 22 - d2
        else: H = NPERP[X]; dv = 3 * RKT[X] - fld7(U2, X)
        if dv < 0: dv = 0
        assert dv < 256
        HP |= H << (512 * j); DEFP |= dv << (8 * j)
    TB = 21 - d2
    def conv(t, pk=frozenset()):
        if t[0] == 'C':
            if not len(pk) > TB: die('xcut budget cut with %d picks, budget %d' % (len(pk), TB))
            return [2, 0]
        def st_ok(X, dd):
            j = jx[X]; H = (HP >> (512 * j)) & M511; dv = (DEFP >> (8 * j)) & 255
            if not (dd >= 1 and dd + ((H >> u) & 1) <= dv): soft('xcut step (%d,%d) at u=%d: bound %d' % (X, dd, u, dv))
            return [j, dd]
        res = []
        if t[0] == 'L':
            res += [0, len(t[1])]
            for (X, dd) in t[1]: res += st_ok(X, dd)
            return res + st_ok(t[2][0], t[2][1])
        res += [1, len(t[1])]
        for (X, dd) in t[1]: res += st_ok(X, dd)
        return res + [t[2], t[5]] + conv(t[3], pk | {t[2]}) + conv(t[4], pk)
    crp = [cpos[i] for i in cr]
    for p_ in crp:
        if not (p_ < len(X1) or (pmask(p_) >> u) & 1): die('xcut child row of residual 2 not through u')
    kidv = [kind, bb, u, Fu, len(crp)] + crp + conv(tree)
    if d2 > 127: die('xcut depth')
    stats['xcut'] += 1
    hdrc = u << 8
    return ([u, hdrc, 0, 3] + [len(X2)] + [jt(x) for x in reversed(X2)] + [len(X1)] + [jt(x) for x in reversed(X1)]
            + [len(nr)] + nr + [nag[0]] + aggv + [len(XL)] + XL + [HP, DEFP, len(XL)] + kidv)

def emit_dk(dk, S2, D2, N2, U2, d2, P):
    """a dead child of the node with frame (S2, D2, N2, U2, d2) and labels P: its ext encoding and its label bit"""
    u = dk['u']; V5c = [x for x in dk['V'] if rows[x][0] >= 3]
    Sc_ = S2 | (1 << u); Dc = D2 | slot(N2, u)
    for x in V5c:
        Dc |= rows[x][1]
        if pc(Sc_ & rows[x][1]) != rows[x][0]: die('dead node V row not full')
    Uc = U2 + HT[u]; dc = d2 + 1
    hdrc = (u << 8) | (dc << 17) | (len(V5c) << 22)
    head = [u, hdrc, len(V5c)] + [jt(x) for x in reversed(V5c)]
    if dk['kind'] == 'xcut':
        # --rord 321: a node cut 5 / 6 only as a dead ROOT (KB.Dead321's #kmDead321); a record's node cuts 5 / 6 are its X part's cut
        # children (CUTS), never dead children, and KB.ext321K has no xcut payload
        if ORD == '321' and not dk.get('root'): die('node cut 5 / 6 as a dead child in a --rord 321 item (only a dead root)')
        return emit_xcut(dk['cu'], S2, D2, N2, U2, d2), 1 << u
    if ORD == '321' and dk['kind'] == 'cut':
        if dk['ck'] != 7: die('node cut %d in a --rord 321 item (KB.ext321K takes cut 7, look-ahead and leaves)' % dk['ck'])
        if not win321(Sc_, Dc, dc, u): soft('321 cut-7 model rejects child %d' % u)
        stats['cut7'] += 1
        return head + [0, 7, 0, 0], 1 << u
    if dk['kind'] == 'cut':
        ckind = dk['ck']
        m, cap = (rows[dk['rid']][1], rows[dk['rid']][0]) if dk['rid'] is not None else (0, 0)
        if not cut_model(Sc_, Dc, Uc, 0, dc, u, ckind, dk['arg'], m, cap): soft('cut model rejects kind %d at child %d' % (ckind, u))
        stats['cut%d' % ckind] += 1
        return head + [0, ckind, dk['arg'], jt(dk['rid']) if dk['rid'] is not None else 0], 1 << u
    if dk['kind'] == 'leaf':
        if dc != 22: die('leaf not at depth 22')
        stats['leaf'] += 1
        return head + [2, dk['R']], 1 << u
    seq = P + [u]
    if dk['pos'] is not None: fr = flook_rec(Sc_, Dc, Uc, dc, u, seq[dk['pos']])
    else:   # leaf code 4: the dead term is not in the record; the first term with a certificate (k321.py's leaf-4 search)
        fr = None
        for tl in seq:
            fr = flook_rec(Sc_, Dc, Uc, dc, u, tl)
            if fr is not None: break
        stats['leaf4'] += 1
    if fr is None: die('flook certificate not found for the dead child %d' % u)
    tl_, nT, tv, TL, TY, SL, SY = fr
    stats['flook'] += 1
    return head + [1, tl_, nT, tv, len(TL)] + TL + TY + [len(SL)] + SL + SY, 1 << u

# ---------------- walk: frames, records, extensions, pending masks ----------------
JT = {}; JTL = []
def jt(x):
    if x not in JT: JT[x] = len(JTL); JTL.append(x)
    return JT[x]
S0 = 0; N0 = CONF1T; U0 = 0
pl = list(root[:-1]); l0 = root[-1]
for l in pl: S0 |= 1 << l; N0 |= c2(l); U0 += HT[l]
D0 = 0
for l in pl: D0 |= slot(N0, l)
D0 &= M511
# witness rows of the root frame (KB.rootChkW): rows full at the prefix whose labels are dead at the root's parent.  A piece's
# header carries them (#pcwit: the VROWS rows of the donor node and its ancestors); a dead root adds its own V rows (cap >= 3)
# without its label.  A depth-1 root (pl = []) has the empty frame (0, 0, c1, 0, 0) and no witness rows (KB.rootChk0).
W = []
if pl:
    for x in WIT:
        if x not in rows: die('witness row %d not in the kept rows' % x)
        if pc(S0 & rows[x][1]) != rows[x][0]: soft('witness row %d not full at the prefix (%d of %d)' % (x, pc(S0 & rows[x][1]), rows[x][0]))
        W.append(x)
    if root_dead is not None:
        u_ = root_dead['u']
        W += [x for x in root_dead['V'] if rows[x][0] >= 3 and not (rows[x][1] >> u_) & 1 and pc(S0 & rows[x][1]) == rows[x][0] and x not in W]
    for x in W: D0 |= rows[x][1]
    D0 &= M511
elif WIT: soft('a depth-1 root with witness rows')
f0 = (S0, D0, N0, U0, len(pl))
lastP = pl[-1] if pl else 0
if DINH is not None:
    stats['dinh_outside'] = pc(DINH & ~D0 & M511); stats['d0_outside_dinh'] = pc(D0 & ~DINH)
    if DINH & ~D0 & M511:
        # guard : R3 holds dead labels at this root that the root frame (prefix conflicts and witness rows) cannot
        # justify; the item's checks would then run on a weaker frame than R3's certificates assume, and the kernel rejects such items
        # (range items of a run without --pcwit). KI_ALLOW_DINH=1 keeps the old note for experiments.
        msg = '%d labels of the header mask are not dead in the root frame%s' % (pc(DINH & ~D0 & M511), '' if WIT else ' (no witness rows: was the run made without --pcwit?)')
        if os.environ.get('KI_ALLOW_DINH') == '1': print('kitem: note: ' + msg)
        else: die(msg)
if root_dead is not None:
    if not pl: die('a dead depth-1 root')
    root_dead['root'] = True
    dv, _ = emit_dk(root_dead, S0, D0, N0, U0, len(pl), list(pl))
    def items0(vs):
        o = bytearray()
        for v in vs:
            bb = v.to_bytes(max(1, (v.bit_length() + 7) // 8), 'little'); o += struct.pack('<Q', len(bb)); o += bb
        return bytes(o)
    open(os.path.join(outdir, 'dead.bin'), 'wb').write(items0([2, l0, len(pl)] + pl + [lastP] + list(f0) + [len(W)] + [jt(x) for x in W] + dv))
    with open(os.path.join(outdir, 'table_0.bin'), 'wb') as f:
        for x in JTL: f.write((rows[x][1] | (rows[x][0] << 511) | (x << 520)).to_bytes(69, 'little'))
        if not JTL: f.write((rows[0][1] | (rows[0][0] << 511)).to_bytes(69, 'little'))   # the real row 0 (tabOKQ checks it)
    msg = 'kitem: root %s (depth %d) is a dead node (%s); %d witness rows; item table %d rows; the record passed the Python models' % (root, len(root), dict(stats), len(W), len(JTL))
    print(msg); open(os.path.join(outdir, 'stats.txt'), 'w').write(msg + '\n'); sys.exit(0)
stack = [[f0, 1 << l0]]   # frames (S, D, N, U, d) with pending masks, top first
KI_FRAMES = os.environ.get('KI_FRAMES', '0') == '1'   # diagnostics: OUTDIR/frames.txt, per record "batch index label parent(5) child(5)"
FRAMES = []
KI_FEAT = os.environ.get('KI_FEAT', '0') == '1'       # OUTDIR/feat.txt, per record the cost model's features
FEAT = []
AGGWALK = [0]   # the aggregate indices' sum + count over a record's in-branches (aggAt's walk length)
CRSEEN = set(); CR2 = [0]   # a record's distinct child-row positions, and its residual-2 child rows
CRPOS = []; DICTL = [0, 0, 0, 0, 0]   # a record's child-row positions; nV, n1, n2, |X1|, |X2|
path = list(pl)
out_recs = []              # (record vals, ext vals, pops, stack before)
batches = []; cur = []; cur_in = None
def stk_vals(st): return [len(st)] + [x for (f, p) in st for x in (f + (p,))]
MEMB = float(os.environ.get('KI_MEMB', '0'))   # GB: a batch closes before a record that would push its predicted kernel cache over this
cur_sum = 0.0                                   # (one declaration caches every record's intermediates; the design notes's per-record model)
def rec_inc(r):
    def tf(t):
        if t[0] == 'C': return (0, 0, 0)
        if t[0] == 'L': return (len(t[1]) + 1, 0, 0)
        a = tf(t[3]); c_ = tf(t[4]); return (len(t[1]) + a[0] + c_[0], 1 + a[1] + c_[1], 0)
    ni = ncr = sw = 0
    for (kind, bb, u, Fu, cr, tree) in r['KIDS']:
        a = tf(tree); ni += a[1]; ncr += len(cr); sw += a[0] * (510 - u)
    dc = len(r['V5']) + len(r['R1']) + len(r['R2']) + len(r.get('X1', [])) + len(r.get('X2', []))
    return 1.004e-3 * ni + 1.315e-4 * dc + 5.21e-5 * ncr + 2.248e-7 * sw
for r in recs:
    d = r['d']; u0 = r['l']
    st_before = [(tuple(f), p) for (f, p) in stack] if MEMB > 0 else None
    top = stack[0][0][4]; pops = top - (d - 1)
    if pops < 0 or pops >= len(stack): die('stack')
    for (f, p) in stack[:pops]:
        if p != 0: soft('a popped frame has pending labels: %s (frame depth %d, node label %d, prefix %s)' % ([l for l in range(511) if (p >> l) & 1][:10], f[4], f[0].bit_length() - 1, [l for l in range(511) if (f[0] >> l) & 1]))
    parf, parp = stack[pops]
    if not (parp >> u0) & 1: soft('record label %d not pending in its parent frame' % u0)
    if not d <= 21: die('depth')
    if len(cur) >= B:
        batches.append((cur_in, cur)); cur = []; cur_sum = 0.0
    if not cur: cur_in = [(tuple(f), p) for (f, p) in stack]
    P = path[:d - 1] + [u0]
    rec, kills, mr = mkrec(r, P, pops)
    res, why = model(parf, r, rec, kills)
    if res is None:
        soft('node5 model rejects node depth %d label %d: %s' % (d, u0, why))
        S_, D_, N_, U_, dP_ = parf; D2_ = D_ | slot(N_, u0)
        for x in r['V5']: D2_ |= rows[x][1]
        res = (S_ | (1 << u0), D2_, N_ | c2(u0), U_ + HT[u0], d)
    r['FR'] = res
    S2, D2, N2, U2, d2 = res; last = u0
    # record vals (kx3.py's flush layout)
    nV, n1, n2 = len(r['V5']), len(r['R1']), len(r['R2'])
    hdr = rec & ((1 << 64) - 1)
    vals = [u0, hdr, n2] + [jt(x) for x in reversed(r['R2'])] + [n1] + [jt(x) for x in reversed(r['R1'])] + [nV] + [jt(x) for x in reversed(r['V5'])]
    X1 = r.get('X1', []); X2 = r.get('X2', [])
    vals += [len(X2)] + [jt(x) for x in reversed(X2)] + [len(X1)] + [jt(x) for x in reversed(X1)]
    vals += [len(kills)] + kills
    AGGWALK[0] = 0; CRSEEN.clear(); CR2[0] = 0; CRPOS.clear(); DICTL[:] = [nV, n1, n2, len(X1), len(X2)]
    vals += xpart(r, nV, n1, n2, X1, X2) if (r['XD'] or r.get('CUTS') or r['KIDS']) else [0, 0, 0, 0, 0, 0]
    # extension
    AV = M511 & ~D2; nn = 21 - d2; b = last + 1
    while pc(AV & geM(b)) > nn: b += 1
    its = []
    for (tg, u, X) in r['P']:
        if ORD == '321':
            if tg == 2: die('TYPE record in a --rord 321 item')
            ok = last < u < 511 and ((tg == 0 and preff_ok(U2, d2, u, X)) or (tg == 1 and doom321(S2, D2, d2, u)))
        else:
            ok = last < u < 511 and ((tg == 0 and preff_ok(U2, d2, u, X)) or (tg == 1 and doom_ok(S2, AV, d2, u)) or (tg == 2 and ty_ok(S2, d2, u)))
        if not ok: soft('kinds model rejects tag %d u=%d X=%d' % (tg, u, X))
        its.append(tg | (u << 2) | (X << 11)); stats['kind%d' % tg] += 1
    cs = canon_records(sorted(P), r['CN']) if r['CN'] else []
    ck = 0
    for Sc in cs: ck |= canon_kids(Sc)
    for (u, typ, t, Pp, Q) in r['CN']:
        if not (ck >> u) & 1: soft('CANON child %d not in the node records' % u)
    dkv = []; dkm = 0
    for dk in r['DK']:
        v_, bit_ = emit_dk(dk, S2, D2, N2, U2, d2, P)
        dkv += v_; dkm |= bit_
    xmE = 0
    for u in r['XM']:
        if not (last < u < 511): soft('external child %d not above the node label %d' % (u, last))
        xmE |= 1 << u
    stats['ext'] += len(r['XM'])
    rgl = r.get('RG', 511)
    if rgl != 511: stats['rg'] += 1
    ext = [b, len(its)] + its + [len(cs)] + cs + [len(r['DK'])] + dkv + [xmE, rgl]
    # pending mask (KD.pendOf)
    km = 0
    for kr in kills: km |= 1 << (kr & 511)
    xm_ = 0
    for (kind, bb, u, Fu, cr, tree) in r['KIDS']: xm_ |= 1 << u
    for cu in r.get('CUTS', []): xm_ |= 1 << cu['u']
    accm = geM(b)
    for it_ in its: accm |= 1 << ((it_ >> 2) & 511)
    accm |= ck | dkm
    pnew = above(last) & ~km & ~xm_ & ~accm & ~xmE & ~D2 & M511
    if pops + 1 == len(stack): pnew &= ~((1 << LO) - 1)          # the root (parent frame last on the stack): children >= LO only
    if rgl != 511: pnew &= ~(M511 >> rgl << rgl) if rgl < 511 else ~0   # children >= rgl are the range segment's
    stack = [[res, pnew], [parf, parp & ~(1 << last)]] + stack[pops + 1:]
    path = P
    if KI_FRAMES: FRAMES.append((len(batches), len(cur), u0, tuple(parf), tuple(res)))
    if KI_FEAT:
        # the cost model's features : children, X-steps, in-branches, aggregates, child rows; plus dictionary rows
        def tf(t):
            if t[0] == 'C': return (0, 0)
            if t[0] == 'L': return (len(t[1]) + 1, 0)
            a, b_ = tf(t[3]); c_, d_ = tf(t[4]); return (len(t[1]) + a + c_, 1 + b_ + d_)
        ns = ni = ncr = 0
        for (kind, bb, u, Fu, cr, tree) in r['KIDS']:
            a, b_ = tf(tree); ns += a; ni += b_; ncr += len(cr)
        FEAT.append((len(batches), len(cur), u0, d, len(r['KIDS']) + len(r.get('CUTS', [])), ns, ni, len(r['XAG']), ncr,
                     len(r['XD']), len(r['DK']), len(r['P']), len(r['CN']), AGGWALK[0], len(CRSEEN), CR2[0],
                     '/'.join(map(str, DICTL)), sum(1 for q_ in CRPOS if q_ < sum(DICTL[:3]))))
    if MEMB > 0:
        ri = rec_inc(r)
        if len(cur) > 0 and cur_sum + ri > MEMB:
            batches.append((cur_in, cur)); cur = []; cur_in = st_before; cur_sum = 0.0
        cur_sum += ri
    cur.append((vals, ext)); stats['open'] += 1; stats['kills'] += len(kills); stats['xkids'] += len(r['KIDS'])
    stats['preff'] += len(its); stats['canon_rec'] += len(cs); stats['canon'] += len(r['CN'])
if cur: batches.append((cur_in, cur))
final = [(tuple(f), p) for (f, p) in stack]
for (f, p) in final:
    if p != 0:
        soft('pending labels at the end: frame of depth %d, labels %s' % (f[4], [l for l in range(511) if (p >> l) & 1][:20]))

def items(vs):
    o = bytearray()
    for v in vs:
        bb = v.to_bytes(max(1, (v.bit_length() + 7) // 8), 'little'); o += struct.pack('<Q', len(bb)); o += bb
    return bytes(o)
extL = [(r['FR'][0] | (1 << u), u) for (r, u) in EXTSEQ]
rngL = [(r['FR'][0], r['l'], l_) for (r, l_) in RNGSEQ]
for (S_, l_, r_) in rngL:
    if not LO < r_: soft('range start %d not above the bound %d' % (r_, LO))
vals = [1, l0, 1 << l0, len(pl)] + pl + [lastP] + list(f0) + [len(batches)]
vals += [len(W)] + [jt(x) for x in W] + [len(extL)] + [x for e in extL for x in e]
vals += [LO, len(rngL)] + [x for e in rngL for x in e]
open(os.path.join(outdir, 'head.bin'), 'wb').write(items(vals))
with open(os.path.join(outdir, 'extL.txt'), 'w') as f:
    for (S_, u_) in extL: f.write('%d %d\n' % (S_, u_))
with open(os.path.join(outdir, 'rngL.txt'), 'w') as f:
    f.write('lo %d\n' % LO)
    for (S_, l_, r_) in rngL: f.write('%d %d %d\n' % (S_, l_, r_))
if KI_FEAT:
    with open(os.path.join(outdir, 'feat.txt'), 'w') as f:
        f.write('batch idx label depth children xsteps inbranches aggs childrows dictrows deadkids kinds canon aggwalk crdistinct cr2 nV/n1/n2/x1/x2 crInMB\n')
        for t_ in FEAT: f.write(' '.join(str(v) for v in t_) + '\n')
if KI_FRAMES:
    with open(os.path.join(outdir, 'frames.txt'), 'w') as f:
        for (bk, ix, u_, pf, cf) in FRAMES: f.write(' '.join(str(v) for v in (bk, ix, u_) + pf + cf) + '\n')
for k, (sin, bl) in enumerate(batches):
    vals = stk_vals(sin) + [len(bl)]
    for (rv, ev) in bl: vals += rv + ev
    open(os.path.join(outdir, 'b%04d.bin' % k), 'wb').write(items(vals))
open(os.path.join(outdir, 'fin.bin'), 'wb').write(items(stk_vals(final)))
with open(os.path.join(outdir, 'table_0.bin'), 'wb') as f:
    for x in JTL: f.write((rows[x][1] | (rows[x][0] << 511) | (x << 520)).to_bytes(69, 'little'))
    if not JTL: f.write((rows[0][1] | (rows[0][0] << 511)).to_bytes(69, 'little'))   # the real row 0 (tabOKQ checks it)
msg = ('kitem: root %s (depth %d), bound %d, %d ranges, %d witness rows, %d external children, %d OPEN records in %d batches of <= %d, %d T/C kills, %d bulk-peel children, %d PREFF, '
       '%d CANON children in %d node records, %d look-ahead children (%d rootcut leaves), %d profile leaves, DOOM %d, TYPE %d, node cuts 5/6 %d (hybrid F_u outside the certificate\'s: %d), look-ahead certificates with an empty tight list %d (greedy slack order %d), header-mask labels not dead in the root frame %s, item table %d rows; every record passed the Python models, '
       'no pending label at the end') % (root, len(root), LO, len(rngL), len(W), len(extL), stats['open'], len(batches), B, stats['kills'], stats['xkids'], stats['preff'],
       stats['canon'], stats['canon_rec'], stats['flook'], stats['leaf4'], stats['leaf'], stats['kind1'], stats['kind2'], stats['xcut'], stats['cut_fu_outside'], stats['flook_tl0'], stats['flook_greedy'], stats.get('dinh_outside', '-'), len(JTL))
if SOFT: msg += '; PERMISSIVE: %d failed Python-model checks (first: %s)' % (len(SOFT), SOFT[0])
print(msg); open(os.path.join(outdir, 'stats.txt'), 'w').write(msg + '\n')
