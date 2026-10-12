"""kjlib.py: shared pieces of the KJ module generators (mkslice.py, mksplit2.py): reading lineenum9qe --e1p job
records and the E1P_LEAFDUMP dumps, glue witnesses, units, the bit-model kernel-time prediction, and the module texts."""
import os, glob, struct, json, threading as _thr
R22 = os.environ.get('R22_ROOT', '.')   # the development layout's root (package mode does not use it)
_MAN_LOCK_G = _thr.Lock()   # (build_split_batched: manifest rows from several threads)
H = R22 + '/e1g/'
MD = H + 'mod/src/KJ/'; DD = H + 'E1P/data/'; PK = 'KJ'   # the generated modules' package (set_package)
OUT = None
LIFTED = set()   # generated modules whose public statement is lifted (external leaves below them): range_tree, tops
# where the emitter's inputs live (IP, order and frontier files, by name) and its binaries; where emissions run.  On the development host these
# are the development trees; `configure(out, tools)` points everything into a package directory and a tools tree (emitpkg.py).
IPDIRS = [H + 'E1P/run/cap2/', R22 + '/hpt/run/', R22 + '/hpt/data/',
          R22 + '/']
BIN = {'lineenum': H + 'E1P/cpp/lineenum9qe_ld5', 'e1pconv': H + 'E1P/cpp/e1pconv'}
RUNDIR = {'c436': H + 'E1P/run/cap2/', 'c422': H + 'E1P/run/cap2/', 'ptc': H + 'E1P/run/pt/'}
LIBPATH = ''
def configure(out=None, tools=None):
    """package mode: sources in OUT/src/KJ, data in OUT/src/data, emissions in OUT/run; inputs and binaries from TOOLS
    (TOOLS/ip, TOOLS/bin, TOOLS/lib)"""
    global MD, DD, LIBPATH, OUT
    if out:
        out = os.path.abspath(out); OUT = out
        MD = out + '/src/%s/' % PK; DD = out + '/src/data/'
        for c in RUNDIR: RUNDIR[c] = out + '/run/'
        os.makedirs(DD, exist_ok=True); os.makedirs(out + '/run', exist_ok=True)
    if tools:
        tools = os.path.abspath(tools)
        IPDIRS[:] = [tools + '/ip/']; BIN['lineenum'] = tools + '/bin/lineenum9qe_ld5'; BIN['e1pconv'] = tools + '/bin/e1pconv'
        LIBPATH = tools + '/lib'
def set_package(pk, src=None, data=None):
    """the generated modules' package (KJ: the context caps' jobs and the point tier; KC: the class tier's class jobs) and,
    optionally, the source root and data directory (default: as configured)"""
    global PK, MD, DD
    PK = pk
    if src: MD = os.path.abspath(src) + '/%s/' % pk
    elif OUT: MD = OUT + '/src/%s/' % pk
    else: MD = H + 'mod/src/%s/' % pk
    if data: DD = os.path.abspath(data) + '/'
    os.makedirs(MD, exist_ok=True)
def ipf(name):
    """an input file by name, from the first input directory holding it"""
    if os.path.isabs(name) and os.path.exists(name): return name
    for d in IPDIRS:
        if os.path.exists(d + name): return d + name
    raise FileNotFoundError(name)
def R(p):
    """how a generated source or .lst refers to a data file: relative to the source root (builds run with cwd = mod/src, where
    data -> ../../E1P/data; in a package build cwd = <pkg>/src with the files in src/data)"""
    return 'data/' + p[len(DD):] if p.startswith(DD) else p
# contexts: (IP, SL, OK namespaces, the IP modules to import publicly), and the block format
CFG = {'c436': ('E1G.IP_c436', 'E1G.SL_c436', 'E1G.OK_c436', ['HC436.IP_c436', 'HC436.SL_c436', 'HC436.OK_c436']),
       'c422': ('E1G.IP_c422', 'E1G.SL_c422', 'E1G.OK_c422', ['HCap.IP_c422', 'HCap.SL_c422', 'HCap.OK_c422']),
       'ptc': ('E1P.IP_ptc', 'E1P.SL_ptc', 'E1P.OK_ptc', ['HPt.IP_ptc', 'HPt.SL_ptc', 'HPt.OK_ptc_F'])}
# block formats: labels LB bits (positions), NL budget fields of 3 bits, delegated records of RW bits, row-table entries of RTW
# bits; a state key is HB + 3 NL + LB d bits (mode 1) or HB + LB d (mode 0); mode-1 headers H1 bits (jobOK_hdr); heavy-leaf
# tables of HHTW-bit entries; the Lean side (Hdr, ChainF, job commands)
# kernel prices per format: ms per st-node (bit model) and the slowest node unit's ms per literal bit (E1P: first estimates from
# the first point modules: 19 jobs, 26,205 st-nodes in 73 s, i.e. 2.8 ms per st-node; the node unit: hpt's job 1204)
FMT = {'e1g': dict(name='e1g', LB=7, NL=127, RW=540, RTW=15, HB=12, H1=611, HHTW=640, hdr='E1G.Hdr', chain='E1GK.ChainF',
                   vocab=['E1GK.ChainF', 'E1GK.ExtMono'], jobcmd='E1GK.JobCmd3', cmd='e1g', MS_NODE=0.5, MS_UNIT_NODE_BIT=0.0078),
       'e1p': dict(name='e1p', LB=8, NL=255, RW=946, RTW=19, HB=13, H1=1027, HHTW=1032, hdr='E1PK.Hdr', chain='E1PK.ChainF',
                   vocab=['E1PK.ChainF'], jobcmd='E1PK.JobCmd', cmd='e1p', MS_NODE=2.8, MS_UNIT_NODE_BIT=0.0126)}
CTXFMT = {'c436': 'e1g', 'c422': 'e1g', 'ptc': 'e1p'}
F = dict(FMT['e1g'])
def set_format(ctx):
    """the block format of a context (E1G for the context caps, E1P for the point IP)"""
    F.clear(); F.update(FMT[CTXFMT.get(ctx, ctx)])
# bit model (isolated, DESIGN §43): node part per st-node, an in-block leaf, a delegated leaf (1.9 ms + 60 µs/bit)
MS_NODE, MS_LEAF_IN, MS_LEAF0, MS_LEAF_BIT = 0.5, 2.0, 1.9, 0.06
# the slowest declaration of a module (DESIGN §43.6, fitted on the rehearsal slice's 137 leaf ranges): a leaf unit takes up to
# 0.15 ms per certificate bit, a node block up to 7.8 µs per literal bit; peak RssAnon = 0.51 GB + 0.148 GB per second of
# the slowest declaration
MS_UNIT_LEAF_BIT, MS_UNIT_NODE_BIT, GB0, GB_PER_S = 0.15, 0.0078, 0.51, 0.148
EXTBITS = 200000   # a certificate over this many bits makes its leaf external (the external-leaf tier)
HEAVY_S = 5.0     # a leaf predicted over this many seconds goes to a heavy-leaf module of its own job (heavy_split)
LEAF_UNIT_S = 2.0  # leaf blocks are packed up to K per declaration while the unit stays under this many predicted seconds
class Rdr:
    def __init__(s, v): s.v = v
    def get(s, k): x = s.v & ((1 << k) - 1); s.v >>= k; return x
def _head(s):
    mode = s.get(1); d = s.get(5); s.get(F['LB']); [s.get(F['LB']) for _ in range(d)]
    if mode == 1: [s.get(3) for _ in range(F['NL'])]
    return mode, d
def records(S):
    s = Rdr(S); mode, d = _head(s)
    nd = s.get(8); return [s.get(F['RW']) for _ in range(nd)]
def _leaf_rest(S):
    """the stream after a block's header, records, row table and mode-0 caps: (no records?, tag, the bits after the tag)"""
    s = Rdr(S); mode, d = _head(s)
    nd = s.get(8); [s.get(F['RW']) for _ in range(nd)]; k = s.get(12); [s.get(F['RTW']) for _ in range(k)]
    if mode == 0: n0 = s.get(8); [s.get(12) for _ in range(n0)]
    tag = s.get(2); return nd == 0, tag, s.v
def is_leafblock(S):
    nd0, tag, _ = _leaf_rest(S); return nd0 and tag == 0
def certbits(S):
    """the certificate bits of a leaf block (what follows its leaf tag)"""
    nd0, tag, v = _leaf_rest(S); return v.bit_length() if (nd0 and tag == 0) else 0
def glue(r, Sc):
    d = r & 31; return (Sc & 1) == 1 and ((Sc >> 1) & ((1 << (F['HB'] + 3 * F['NL'] + F['LB'] * d)) - 1)) == r
def glue0(r, Sc):
    d = r & 31; Wd = F['HB'] + F['LB'] * d; return (Sc & 1) == 0 and ((Sc >> 1) & ((1 << Wd) - 1)) == (r & ((1 << Wd) - 1))
def mode0_header(S): return S % (1 << (1 + F['HB'] + F['LB'] * ((S >> 1) & 31)))
def unit_s(lits, u, isl):
    if all(isl[i] for i in u): return MS_UNIT_LEAF_BIT * sum(certbits(lits[i]) for i in u) / 1000.0
    return F['MS_UNIT_NODE_BIT'] * max(lits[i].bit_length() for i in u) / 1000.0
def pred_gb_s(s): return round(GB0 + GB_PER_S * s, 2)
def read_e1p(paths):
    jobs = {}
    for f in paths:
        b = open(f, 'rb').read(); i = 0
        while i < len(b):
            mg, ix, n = struct.unpack('<III', b[i:i + 12]); i += 12; assert mg == 0x4A503145
            ls = []
            for _ in range(n):
                ln = struct.unpack('<I', b[i:i + 4])[0]; i += 4; ls.append(int.from_bytes(b[i:i + ln], 'little')); i += ln
            jobs[ix] = ls
    return jobs
def read_dumps(rd):
    """per job: st-nodes of its blocks and the bit length of every leaf certificate"""
    nodes, bits = {}, {}
    for f in glob.glob(rd + '/leaves_blocks_t*.txt'):
        for ln in open(f):
            a = ln.split(); nodes[int(a[0])] = nodes.get(int(a[0]), 0) + int(a[2])
    for f in glob.glob(rd + '/leaves_t*.txt'):
        for ln in open(f):
            a = ln.split()
            if len(a) < 4: continue   # an external leaf (no certificate): a membership test in the kernel
            h = a[3]; bits.setdefault(int(a[0]), []).append(4 * len(h) - (4 - int(h[0], 16).bit_length()))
    return nodes, bits
def read_ext(rd):
    """external leaves of an emission (lineenum9qe --e1pext): job -> [(labels, flag)], from the "job l1,..,lR [F]" lines
    (F: S satisfiable, B over gen7's budget, U certificate over E1P_EXTBITS, E, ?)"""
    out = {}
    for f in glob.glob(rd + '/e_*_ext_t*.txt'):
        for ln in open(f):
            a = ln.split()
            if len(a) < 2: continue
            out.setdefault(int(a[0]), []).append((list(map(int, a[1].split(','))), a[2] if len(a) > 2 else '?'))
    return out
def plpack(labels):
    """E1G's packed prefix of a leaf: label i in bits [7 i, 7 i + 7) (what E1G.leafOK looks up in C.EXT)"""
    return sum(l << (7 * i) for i, l in enumerate(labels))
def kext_lines(tier, key, ext):
    return ['#kext ' + ' '.join('"%s %s %s %s"' % (tier, key, ','.join(map(str, labs)), fl) for labs, fl in ext)] if ext else []
def predict_s(nodes, bits, deleg=64):
    t = F['MS_NODE'] * nodes
    for b in bits: t += MS_LEAF0 + MS_LEAF_BIT * b if b >= deleg else MS_LEAF_IN
    return t / 1000.0
def witnesses(lits, jobs=None):
    key = {}
    HB, LB = F['HB'], F['LB']
    for k, S in enumerate(lits): key.setdefault((S >> 1) & ((1 << (HB + LB * ((S >> 1) & 31))) - 1), []).append(k)
    jkey = {}
    if jobs:
        for k, Hj in enumerate(jobs): jkey.setdefault((Hj >> 1) & ((1 << (HB + LB * ((Hj >> 1) & 31))) - 1), []).append(k)
    W = []
    for k, S in enumerate(lits):
        row = []
        for r in records(S):
            kk = r & ((1 << (HB + LB * (r & 31))) - 1)
            c = [i for i in key.get(kk, []) if i > k and (glue(r, lits[i]) or glue0(r, lits[i]))]
            if c: row.append(c[0]); continue
            c = [j for j in jkey.get(kk, []) if glue(r, jobs[j]) or glue0(r, jobs[j])]
            assert c, ('no witness', k, len(row)); row.append(len(lits) + c[0])
        W.append(row)
    return W
def wrlits(fn, lits):
    with open(fn, 'wb') as f:
        f.write(struct.pack('<I', len(lits)))
        for v in lits:
            bb = v.to_bytes((v.bit_length() + 7) // 8, 'little'); f.write(struct.pack('<I', len(bb))); f.write(bb)
def wrW(pfx, W):
    offs, flat = [], []
    for r in W: offs.append(len(flat)); flat.extend(r)
    for nm, arr in (('OF', offs), ('WT', flat or [0])):
        with open('%s_%s.bin' % (pfx, nm), 'wb') as f:
            for v in arr: f.write(v.to_bytes(4, 'little'))
def write_job(pfx, lits, K=4, jobsHT=None, ext=None):
    """the four input files of a chain (#e1gjob / #e1gjobs line / #e1gtop): returns the .lst line and the input bytes"""
    wrlits(pfx + '.bin', lits); wrW(pfx, witnesses(lits, jobsHT))
    isl = [i > 0 and is_leafblock(S) for i, S in enumerate(lits)]
    leafb = [i for i in range(len(lits)) if isl[i]]
    U = [[i] for i in range(len(lits)) if not isl[i]]
    cur, t = [], 0.0
    for i in leafb:   # packs of up to K leaf blocks while the declaration stays under LEAF_UNIT_S predicted
        ti = MS_UNIT_LEAF_BIT * certbits(lits[i]) / 1000.0
        if cur and (len(cur) == K or t + ti > LEAF_UNIT_S): U.append(cur); cur, t = [], 0.0
        cur.append(i); t += ti
    if cur: U.append(cur)
    with open(pfx + '_units.txt', 'w') as f:
        for u in U: f.write(' '.join(map(str, u)) + '\n')
    nb = sum(os.path.getsize(pfx + s) for s in ('.bin', '_OF.bin', '_WT.bin', '_units.txt'))
    ist = [is_leafblock(S) for S in lits]   # for the timing, block 0 too (a heavy leaf's 1-block job)
    mx = max(unit_s(lits, u, ist) for u in U)
    rp = R(pfx); xs = (' X=' + ','.join(str(plpack(l)) for l, _ in ext)) if ext else ''
    return '%s.bin %s_OF.bin %s_WT.bin %s_units.txt%s' % (rp, rp, rp, rp, xs), nb, len(lits), mx
def cut(costs, lo=120.0, hi=300.0):
    """consecutive groups with predicted cost up to hi (a single job over hi alone)"""
    G, cur, s = [], [], 0.0
    for i, c in enumerate(costs):
        if cur and s + c > hi: G.append(cur); cur, s = [], 0.0
        cur.append(i); s += c
    if cur: G.append(cur)
    return G
def header(ctx, extra_pub=(), priv=()):
    IPN, SLN, OKN, IMPS = CFG[ctx]
    return (['module'] + ['public import %s' % m for m in IMPS] + ['public import %s' % F['hdr']] + ['public import %s' % m for m in extra_pub] +
            ['import %s' % m for m in priv] + ['public import %s' % m for m in F['vocab']] + ['meta import %s' % F['jobcmd'], 'meta import KMod.Units', 'meta import KMod.Audit',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false'])
def manifest(rows, path):
    with _MAN_LOCK_G:
        with open(path, 'a') as f:
            for r in rows: f.write(json.dumps(r) + '\n')
def pred_anon_gb(nblocks): return round(0.45 + 2.0e-5 * nblocks, 2)

# per context: IP and order files, search options, the stream format option, the leaf basis (gen7), the external-leaf option,
# the depth-6 (or root-level) frontier, the job header table (its constants' prefix and module); file names resolve by ipf().
# The c436/c422 tables are the production ones, KH.HT436 / KH.HT422 (prebuilt in the closure, outside package KJ, which the
# scheduler's store holds); the rehearsal slices used per-slice KJ.HT436.
EMIT = {
  'c436': dict(ip='ipc2_436.txt', order='o436_tighta', opts='--lp 1 18 --sepmode 1 --inherit 0 --lpadd 50',
               fmt='--e1g', eb='1,34,80', ext='--e1pext', frontier='fr436_d6.txt', tbl='KH.HT436', tblmod='KH.HT436'),
  'c422': dict(ip='ipc2_422.txt', order='o422_tighta', opts='--lp 1 18 --sepmode 1 --inherit 0 --lpadd 50',
               fmt='--e1g', eb='1,20,66', ext='--e1pext', frontier='fr422_d6.txt', tbl='KH.HT422', tblmod='KH.HT422'),
  # the point IP (hpt/ana/roots_pt.txt): E1P stream (no --e1g), no external leaves (E1P.Ctx has no EXT), inherited rows
  'ptc': dict(ip='ipns', order='oP1_tighta', opts='--lp 1 19 --sepmode 1 --inherit 1 --inhmax 800 --lpadd 50 --sepskip @skip_P1.txt',
              fmt='', eb='1', ext='', frontier='fr_Rptc.txt', tbl='E1P.Rptc_HT', tblmod='HPt.Rptc_HT')}
# the class tier's hcap-native raise classes (the class tier): contexts h<c> over the port's IP facts and root
# tables E1G.R<c>_HT (HCap.R<c>_HT), root5 frontiers; file names relative to the lean tree (IPDIRS on the development host; the tools tree's
# ip/ mirrors them)
LEAN = R22 + '/'
CLASS_D2 = ['485', '487', '490']
CLASS_D3 = ['420', '450', '451', '454', '455', '456', '458', '460', '463', '464', '465', '469', '470', '471', '472', '473', '475', '476']
CLASS_HCAPK = {'456', '472', '473', '476', '485', '487', '490'}   # OK_h<c> and R<c>_HT from package HCapK (port sources, renamed modules)
def load_class_contexts(roots='hcap/ana/roots_fixed.txt', required=True):
    """the classes' contexts from the roots file in the input directories (call configure(tools=…) first in package mode);
    a missing file raises unless required=False"""
    try: rf = ipf(roots)
    except FileNotFoundError:
        if required: raise FileNotFoundError('%s in none of %s (in package mode, configure(tools=...) first)' % (roots, IPDIRS))
        return
    for l in open(rf):
        a = l.split()
        if not a or a[0].startswith('#') or a[0] not in CLASS_D2 + CLASS_D3: continue
        c = a[0]; ctx = 'h' + c
        eb, R_ = open(ipf('hcap/run/c%s/eb' % c)).read().split()[:2]
        okp = 'HCapK' if c in CLASS_HCAPK else 'HCap'   # the frozen port lacks OK/R_HT of these: the class tier's HCapK copies
        CFG[ctx] = ('E1G.IP_' + ctx, 'E1G.SL_' + ctx, 'E1G.OK_' + ctx, ['HCap.IP_' + ctx, 'HCap.SL_' + ctx, okp + '.OK_' + ctx])
        CTXFMT[ctx] = 'e1g'
        fr = a[3][len(LEAN):] if a[3].startswith(LEAN) else a[3]
        EMIT[ctx] = dict(ip='hcap/run/c%s/ipns' % c, order='hcap/run/c%s/o_tighta' % c,
                         opts='--lp 1 %d --sepmode 1 --inherit 0 --lpadd 50' % (int(R_) - 1), fmt='--e1g', eb=eb, ext='--e1pext',
                         frontier=fr, tbl='E1G.R%s_HT' % c, tblmod='%s.R%s_HT' % (okp, c), nJ=int(a[2]), R=int(R_))
        RUNDIR.setdefault(ctx, OUT + '/run/' if OUT else H + 'E1P/run/hcap/')
def heavy_context(cap, J):
    """the context of heavy job J of a context cap (c436, c422): its depth-10 sub-jobs (native split), frontier sub<C>/<J>.txt
    (local indices), job table KH.S<C>_<J> (prebuilt); search as the cap"""
    C = cap[1:]; ctx = '%sh%d' % (cap, J)
    if ctx not in EMIT:
        E = dict(EMIT[cap])
        if cap.startswith('h'):   # a class giant (the class tier's): frontier subh<c>/<J>.txt, table KCH.S<c>_<J> (prebuilt; not KC)
            E['frontier'] = 'sub%s/%d.txt' % (cap, J); E['tbl'] = E['tblmod'] = 'KCH.S%s_%d' % (C, J); E['subtop'] = 'subtop%s/%d.bin' % (cap, J)
        else:
            E['frontier'] = 'sub%s/%d.txt' % (C, J); E['tbl'] = E['tblmod'] = 'KH.S%s_%d' % (C, J); E['subtop'] = 'subtop%s/%d.bin' % (C, J)
        EMIT[ctx] = E; CFG[ctx] = CFG[cap]; CTXFMT[ctx] = CTXFMT[cap]; RUNDIR[ctx] = RUNDIR[cap]
    return ctx
def emit_opts(ctx):
    return ' '.join(ipf(t[1:]) if t.startswith('@') else t for t in EMIT[ctx]['opts'].split())
def prefix_of(ctx, S):
    """the prefix (coset representatives as in the frontier files) of a job's first block S"""
    E = EMIT[ctx]
    toks = open(ipf(E['ip'])).read().split('\n')[1].split(); vecs = list(map(int, toks))
    ordv = list(map(int, open(ipf(E['order'])).read().split()))
    d = (S >> 1) & 31; LB = F['LB']
    return ','.join(str(vecs[ordv[(S >> (1 + F['HB'] + LB * i)) & ((1 << LB) - 1)]]) for i in range(d))

def emit(ctx, rd, args, threads=14, extra_env=''):
    """run lineenum9qe_ld5 (delegated layout, leaf dumps, certificates over EXTBITS external) in rd with the given job/root
    arguments"""
    import subprocess
    E = EMIT[ctx]
    os.makedirs(rd, exist_ok=True)
    ni = max(0, 10 - os.nice(0))
    lp = ('LD_LIBRARY_PATH=%s ' % LIBPATH) if LIBPATH else ''
    cmd = ('cd %s && %s %sE1P_LEAFDELEG=66 E1P_EXTBITS=%d E1P_LEAFDUMP=%s/leaves nice -n %d %s %s --order %s '
           '%s --threads %d --donate 16 %s --state st.txt --out /dev/null %s --e1p e --e1pE %s %s --e1plimit 16384 --maxrss 120 '
           '> run.log 2>&1' % (rd, extra_env, lp, EXTBITS, rd, ni, BIN['lineenum'], ipf(E['ip']), ipf(E['order']), emit_opts(ctx), threads,
                               args, E['fmt'], E['eb'], E['ext']))
    subprocess.run(cmd, shell=True, check=True)

def emission_done(rd):
    """an emission finished (lineenum9qe ends with "DONE frontier run …"): its outputs are complete and can be reused"""
    try: return 'DONE frontier run' in open(rd + '/run.log').read()[-4000:]
    except OSError: return False
def reset_emission(rd):
    """an unfinished emission is redone from scratch (its e1p records, dumps and ext lines may be partial)"""
    import shutil
    if os.path.isdir(rd): shutil.rmtree(rd)
    os.makedirs(rd)
def conv_top(ctx, rd):
    """the top chain of a split emission (lineenum9qe --cert top) as block literals (e1pconv)"""
    import subprocess
    E = EMIT[ctx]
    lp = ('LD_LIBRARY_PATH=%s ' % LIBPATH) if LIBPATH else ''
    subprocess.run('%s%s %s %s %s --out %s/top.bin %s --ebasis %s > %s/conv.log 2>&1'
                   % (lp, BIN['e1pconv'], ipf(E['ip']), ipf(E['order']), glob.glob(rd + '/top_*_top.bin')[0], rd, E['fmt'], E['eb'], rd),
                   shell=True, check=True)

def range_tree(ctx, name, tbl, tbl_mod, a0, lst, costs, inb, mxs, imp, man, hi=300.0, key=None, what='jobs', exts=None):
    """leaf-range modules KJ.<name>_L<g> (`#e1gjobs` over the public table `tbl`, jobs a0 + i) cut at `hi` predicted seconds,
    and fan-in-100 aggregators; returns (theorem of the root range, its module, build order, number of leaf modules)"""
    IPN, SLN, OKN, IMPS = CFG[ctx]; key = key or name
    groups = cut(costs, hi=hi); children = []; order = []
    for g, G in enumerate(groups):
        a = a0 + G[0]; b = a0 + G[-1] + 1; mod = PK + '.%s_L%d' % (name, g)
        open(DD + PK + '_%s_L%d.lst' % (name, g), 'w').write('\n'.join(lst[i] for i in G) + '\n')
        open(MD + '%s_L%d.lean' % (name, g), 'w').write('\n'.join(header(ctx, extra_pub=[tbl_mod], priv=[imp[i] for i in G if imp[i]]) + [
            '/-! # %s %d .. %d of %s: predicted %.0f s -/' % (what, a, b - 1, name, sum(costs[i] for i in G)),
            '#%sjobs %s.%s.L%d "%s" %s %s %s %s %d' % (F['cmd'], PK, name, g, R(DD + '%s_%s_L%d.lst' % (PK, name, g)), IPN, SLN, OKN, tbl, a),
            '#kax ' + PK + '.%s.L%d.ok' % (name, g), '#kkey "%s/%d" "%s/%d"' % (key, a, key, b - 1)] +
            [l for i in G for l in kext_lines(ctx, '%s/%d' % (key, a0 + i), (exts or {}).get(i))] + ['']))
        lifted = any((exts or {}).get(i) for i in G) or any(imp[i] in LIFTED for i in G if imp[i])
        if lifted: LIFTED.add(mod)
        manifest([{'module': mod, 'tier': ctx, 'kind': 'leaf-range', 'lifted': lifted, 'jobs': ['%s/%d' % (key, a), '%s/%d' % (key, b - 1)],
                   'pred_kernel_s': round(sum(costs[i] for i in G), 1), 'pred_anon_gb': pred_gb_s(max(mxs[i] for i in G)),
                   'input_bytes': sum(inb[i] for i in G), 'imports': IMPS + [F['hdr'], tbl_mod] + [imp[i] for i in G if imp[i]]}], man)
        order.append(mod); children.append((PK + '.%s.L%d.ok' % (name, g), a, b - a, mod))
    lvl = 0
    while len(children) > 1:   # fan-in-100 aggregators
        nxt = []
        for i in range(0, len(children), 100):
            ch = children[i:i + 100]
            nm = '%s_A%d_%d' % (name, lvl, i // 100) if len(children) > 100 else '%s_A' % name
            open(DD + PK + '_%s.lst' % nm, 'w').write('\n'.join('%s %d %d' % (c[0], c[1], c[2]) for c in ch) + '\n')
            a = ch[0][1]; M = sum(c[2] for c in ch)
            open(MD + '%s.lean' % nm, 'w').write('\n'.join(header(ctx, extra_pub=[tbl_mod], priv=[c[3] for c in ch]) + [
                '#%sagg %s.%s "%s" %s %s %s' % (F['cmd'], PK, nm, R(DD + '%s_%s.lst' % (PK, nm)), IPN, SLN, tbl),
                '#kax ' + PK + '.%s.ok' % nm, '#kkey "%s/%d" "%s/%d"' % (key, a, key, a + M - 1), '']))
            lifted = any(c[3] in LIFTED for c in ch)
            if lifted: LIFTED.add(PK + '.%s' % nm)
            manifest([{'module': PK + '.%s' % nm, 'tier': ctx, 'kind': 'agg', 'lifted': lifted, 'jobs': ['%s/%d' % (key, a), '%s/%d' % (key, a + M - 1)],
                       'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45, 'input_bytes': 0,
                       'imports': IMPS + [F['hdr'], tbl_mod] + [c[3] for c in ch]}], man)
            order.append(PK + '.%s' % nm); nxt.append((PK + '.%s.ok' % nm, a, M, PK + '.%s' % nm))
        children = nxt; lvl += 1
    return children[0][0], children[0][3], order, len(groups)

def hdr_of(S):
    """what a job made of block S proves: `JobOK C sl UB (S % 2^H1)` (mode 1, `jobOK_hdr`; 611 bits in E1G, 1027 in E1P) or its
    mode-0 prefix header"""
    return S % (1 << F['H1']) if S & 1 else mode0_header(S)

def heavy_leaves(lits):
    return [i for i, S in enumerate(lits) if i > 0 and is_leafblock(S) and MS_UNIT_LEAF_BIT * certbits(S) / 1000.0 > HEAVY_S]

def heavy_split(ctx, name, lits, man, K_=4, hi=300.0, ext=None):
    """a job with heavy leaves (predicted over HEAVY_S, i.e. above about 33k certificate bits): each heavy leaf block becomes a
    1-block job over the table KJ.<name>_HHT of their headers (640-bit entries), proved in heavy-leaf range modules, so that a
    long leaf check (and its peak memory: 0.51 GB + 0.148 GB/s) sits in a short module of its own; the rest of the job is a chain
    glued to them (`#e1gtop`), with the job's own header.  Returns (theorem, top module, order, (kernel s, slowest unit s))."""
    IPN, SLN, OKN, IMPS = CFG[ctx]
    hv = heavy_leaves(lits); hs = set(hv)
    main = [S for i, S in enumerate(lits) if i not in hs]; heavy = [lits[i] for i in hv]
    HH = [hdr_of(S) for S in heavy]
    with open(DD + PK + '_%s_HHT.bin' % name, 'wb') as f:
        for h in HH: f.write(h.to_bytes(F['HHTW'] // 8, 'little'))
    tbl = PK + '.%s.HHT' % name; tmod = PK + '.%s_HHT' % name
    open(MD + '%s_HHT.lean' % name, 'w').write('\n'.join(['module', 'public import RT.Load',
        '/-! # Heavy-leaf header table of job %s (%d leaf blocks, their headers), public data -/' % (name, len(heavy)),
        '#rttablew %s "%s" 64 %d' % (tbl, R(DD + PK + '_%s_HHT.bin' % name), F['HHTW']), '']))
    manifest([{'module': tmod, 'tier': ctx, 'kind': 'table', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45,
               'input_bytes': F['HHTW'] // 8 * len(heavy), 'imports': ['RT.Load']}], man)
    order = [tmod]
    lst, costs, inb, mxs = [], [], [], []
    for k, S in enumerate(heavy):
        line, nb, n, mx = write_job(DD + PK + '_%s_h%d' % (name, k), [S], K_)
        lst.append(line); costs.append(max(mx, (MS_LEAF0 + MS_LEAF_BIT * certbits(S)) / 1000.0)); inb.append(nb); mxs.append(mx)   # heavy leaves run near the upper rate
    root_child, root_mod, ro, ng = range_tree(ctx, name + '_H', tbl, tmod, 0, lst, costs, inb, mxs, [None] * len(heavy), man, hi,
                                              key=name + '/h', what='heavy leaves')
    order += ro
    line, nb, n, mx = write_job(DD + PK + '_%s_m' % name, main, K_, jobsHT=HH)
    pfx = R(DD + PK + '_%s_m' % name)
    xarg = (' "%s"' % ','.join(str(plpack(l)) for l, _ in ext)) if ext else ''
    open(MD + '%s_Top.lean' % name, 'w').write('\n'.join(header(ctx, priv=[tmod, root_mod]) + [
        '/-! # job %s without its %d heavy leaves, glued to them (heavy-leaf modules %s.%s_H…) -/' % (name, len(heavy), PK, name),
        '#%stop %s.%s.Top "%s.bin" "%s_OF.bin" "%s_WT.bin" "%s_units.txt" %s %s %s %s %d %s%s' % (F['cmd'], PK, name, pfx, pfx, pfx, pfx, IPN, SLN, OKN, tbl, len(heavy), root_child, xarg),
        '#kax ' + PK + '.%s.Top.job' % name, '#kkey "%s" "%s"' % (name, name)] + kext_lines(ctx, name, ext) + ['']))
    if ext or root_mod in LIFTED: LIFTED.add(PK + '.%s_Top' % name)
    return PK + '.%s.Top.job' % name, PK + '.%s_Top' % name, order, (sum(costs), mx, nb, n)

def build_split(ctx, prefix, name, man, depth=10, threads=14, hi=300.0, K_=4, limit=600.0):
    """a split job (its depth-d0 root `prefix`, cut at depth `depth`) as a KJ module tree: sub-job header table, leaf ranges,
    fan-in-100 aggregators, the top; returns (public theorem of the top, top module, build order)"""
    IPN, SLN, OKN, IMPS = CFG[ctx]
    rd = RUNDIR[ctx] + 'split_%s' % name
    if not emission_done(rd):
        reset_emission(rd)
        emit(ctx, rd, '--root "%s" --frontier %d --cert top' % (prefix, depth), threads)
    if not os.path.exists(rd + '/top.bin'): conv_top(ctx, rd)
    jobs = read_e1p(sorted(glob.glob(rd + '/e_*_t*.e1p')))
    nJ = max(jobs) + 1; assert sorted(jobs) == list(range(nJ))
    EXT = read_ext(rd)
    HT = [mode0_header(jobs[k][0]) for k in range(nJ)]
    W = 128 if max(h.bit_length() for h in HT) <= 128 else 256   # mode-0 headers of 1 + HB + LB d bits: deep splits need 256
    with open(DD + PK + '_%s_SHT.bin' % name, 'wb') as f:
        for h in HT: f.write(h.to_bytes(W // 8, 'little'))
    tbl = PK + '.%s.SHT' % name
    open(MD + '%s_SHT.lean' % name, 'w').write('\n'.join(['module', 'public import RT.Load',
        '/-! # Sub-job header table of split job %s (%d sub-jobs, mode-0 prefix headers), public data -/' % (name, nJ),
        '#rttablew %s "%s" 64 %d' % (tbl, R(DD + PK + '_%s_SHT.bin' % name), W), '']))
    order = [PK + '.%s_SHT' % name]
    manifest([{'module': PK + '.%s_SHT' % name, 'tier': ctx, 'kind': 'table', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45,
               'input_bytes': 16 * nJ, 'imports': ['RT.Load']}], man)
    nodes, bits = read_dumps(rd)
    costs, lst, inb, mxs, imp = [], [], [], [], []
    sub_order = []
    for k in range(nJ):
        c = predict_s(nodes.get(k, 0), bits.get(k, []))
        if c > limit:   # an oversize sub-job: split it further (2 levels deeper), recursively
            thm, tmod, so, _ = build_split(ctx, prefix_of(ctx, jobs[k][0]), '%s_s%d' % (name, k), man, depth + 2, threads, hi, K_, limit)
            sub_order += so; lst.append('@' + thm); inb.append(0); mxs.append(0.0); costs.append(1.0); imp.append(tmod)
            continue
        if heavy_leaves(jobs[k]):   # heavy leaves: the sub-job's chain in a top module of its own, its heavy leaves apart
            thm, tmod, so, (hc, mx, nb, n) = heavy_split(ctx, '%s_x%d' % (name, k), jobs[k], man, K_, hi, ext=EXT.get(k))
            manifest([{'module': tmod, 'tier': ctx, 'kind': 'top', 'pred_kernel_s': round(max(c - hc, 1.0), 1), 'pred_anon_gb': pred_gb_s(mx),
                       'input_bytes': nb, 'imports': IMPS + ['E1G.Hdr']}], man)
            sub_order += so + [tmod]; lst.append('@' + thm); inb.append(0); mxs.append(0.0); costs.append(1.0); imp.append(tmod)
            continue
        line, nb, n, mx = write_job(DD + PK + '_%s_j%d' % (name, k), jobs[k], K_, ext=EXT.get(k))
        lst.append(line); inb.append(nb); mxs.append(mx); costs.append(c); imp.append(None)
    order += sub_order
    exts = {k: EXT[k] for k in EXT if k < nJ and not lst[k].startswith('@')}
    root_child, root_mod, ro, ng = range_tree(ctx, name, tbl, PK + '.%s_SHT' % name, 0, lst, costs, inb, mxs, imp, man, hi, what='sub-jobs', exts=exts)
    order += ro
    # the top chain glued to the sub-jobs
    b = open(rd + '/top.bin', 'rb').read(); n = struct.unpack('<I', b[:4])[0]; i = 4; top = []
    for _ in range(n):
        ln = struct.unpack('<I', b[i:i + 4])[0]; i += 4; top.append(int.from_bytes(b[i:i + ln], 'little')); i += ln
    pfx = DD + PK + '_%s_top' % name
    wrlits(pfx + '.bin', top); wrW(pfx, witnesses(top, HT))
    with open(pfx + '_units.txt', 'w') as f:
        for k in range(len(top)): f.write('%d\n' % k)
    tcost = sum(F['MS_NODE'] * 150 for _ in top) / 1000.0
    isl = [False] * len(top)
    open(MD + '%s_Top.lean' % name, 'w').write('\n'.join(header(ctx, priv=[PK + '.%s_SHT' % name, root_mod]) + [
        '/-! # the top chain of split job %s (root %s, cut at depth %d), glued to its %d sub-jobs -/' % (name, prefix, depth, nJ),
        '#%stop %s.%s.Top "%s.bin" "%s_OF.bin" "%s_WT.bin" "%s_units.txt" %s %s %s %s %d %s' % (F['cmd'], PK, name, R(pfx), R(pfx), R(pfx), R(pfx), IPN, SLN, OKN, tbl, nJ, root_child),
        '#kax ' + PK + '.%s.Top.job' % name, '#kkey "%s" "%s"' % (name, name), '']))
    manifest([{'module': PK + '.%s_Top' % name, 'tier': ctx, 'kind': 'top', 'pred_kernel_s': round(tcost, 1),
               'pred_anon_gb': pred_gb_s(max(unit_s(top, [k], isl) for k in range(len(top)))),
               'input_bytes': os.path.getsize(pfx + '.bin'), 'imports': IMPS + [F['hdr'], PK + '.%s_SHT' % name, root_mod]}], man)
    order.append(PK + '.%s_Top' % name)
    if root_mod in LIFTED: LIFTED.add(PK + '.%s_Top' % name)
    return PK + '.%s.Top.job' % name, PK + '.%s_Top' % name, order, (sum(costs) + tcost, nJ, ng, max(costs))

def make_slice(ctx, start, count, name, TH=14, FS=0, log=print, budget=0):
    """jobs start .. start + count - 1 of a context as KJ modules (mkslice.py; emitpkg.py): emission, the bit-model cuts, oversize
    jobs split (600 s, recursive), heavy leaves apart, leaf ranges (300 s) over the context's job table, fan-in-100 aggregators;
    writes RUN/slice_<name>/{manifest.jsonl, order.txt}; returns (order, root theorem, root module, slice directory)"""
    set_format(ctx); E = EMIT[ctx]
    IPN, SLN, OKN, IMPS = CFG[ctx]
    RUN = RUNDIR[ctx]; rd = RUN + 'slice_%s' % name; os.makedirs(rd, exist_ok=True); os.makedirs(MD, exist_ok=True)
    TBL, TBLMOD = E['tbl'], E['tblmod']
    if not FS and not emission_done(rd):
        reset_emission(rd)
        open(rd + '/jobs.txt', 'w').write('\n'.join(str(k) for k in range(start, start + count)) + '\n')
        # with a node budget, a job over it stops early and is listed (heavy.txt): it is then split directly (batched), so no
        # emission of the range ever holds a giant job whole
        emit(ctx, rd, '--frontierfile %s --jobs jobs.txt' % ipf(E['frontier']) + (' --budget %d --heavy heavy.txt' % budget if budget else ''), TH)
    if FS:
        nodes, bits = {}, {}
    else:
        jobs = read_e1p(sorted(glob.glob(rd + '/e_*_t*.e1p')))
        overb = set()
        if budget and os.path.exists(rd + '/heavy.txt'):
            fidx = {}
            for ln in open(ipf(E['frontier'])):
                a_, p_ = ln.split(); fidx[p_] = int(a_)
            overb = set(fidx[l.strip()] for l in open(rd + '/heavy.txt') if l.strip())
        assert sorted(set(jobs) | overb) == list(range(start, start + count)), ('missing jobs', sorted(set(range(start, start + count)) - set(jobs) - overb)[:5])
        nodes, bits = read_dumps(rd)
    EXT = {} if FS else read_ext(rd)
    man = rd + '/manifest.jsonl'; open(man, 'w').close(); order = [TBLMOD] if TBLMOD.startswith(PK + '.') else []
    pre = {}
    for ln in open(ipf(E['frontier'])):
        a_, p_ = ln.split()
        if start <= int(a_) < start + count: pre[int(a_)] = p_
    costs, lst, inb, mxs, imp = [], [], [], [], []
    LIMIT = 600.0
    if FS: overb = set(range(start, start + count))
    for k in range(start, start + count):
        c = float('inf') if k in overb else predict_s(nodes.get(k, 0), bits.get(k, []))
        if c > LIMIT:   # an oversize job: split 2 levels deeper into its own module tree; the range refers to its top theorem
            # known heavy jobs (FS: direct split) go through the batched split (bounded memory: lineenum's node budget, batches of
            # sub-jobs, streamed records); a job found oversize after its whole emission through the plain one
            bs = build_split_batched if k in overb else build_split
            kw = dict(log=log, budget=BSB_BUDGET) if k in overb else {}
            thm, tmod, sorder, (sc, nJ, ng, mx) = bs(ctx, pre[k], '%s_s%d' % (name, k), man,
                                                     depth=FS or len(pre[k].split(',')) + 2, threads=TH, **kw)
            log('  job %d (predicted %.0f s) split: %d sub-jobs in %d leaf modules (sub-job max %.0f s), top %s' % (k, c, nJ, ng, mx, tmod))
            order += sorder; lst.append('@' + thm); inb.append(0); mxs.append(0.0); costs.append(1.0); imp.append(tmod)
            continue
        if heavy_leaves(jobs[k]):   # heavy leaves apart: the job's chain in a top module, each heavy leaf in a short module
            thm, tmod, sorder, (hc, mx, nb, n) = heavy_split(ctx, '%s_x%d' % (name, k), jobs[k], man, ext=EXT.get(k))
            manifest([{'module': tmod, 'tier': ctx, 'kind': 'top', 'pred_kernel_s': round(max(c - hc, 1.0), 1), 'pred_anon_gb': pred_gb_s(mx),
                         'input_bytes': nb, 'imports': IMPS + ['E1G.Hdr']}], man)
            log('  job %d: %d heavy leaves apart (%.0f s of %.0f s), top %s' % (k, len(heavy_leaves(jobs[k])), hc, c, tmod))
            order += sorder + [tmod]; lst.append('@' + thm); inb.append(0); mxs.append(0.0); costs.append(1.0); imp.append(tmod)
            continue
        line, nb, n, mx = write_job(DD + PK + '_%s_j%d' % (name, k), jobs[k], ext=EXT.get(k))
        lst.append(line); inb.append(nb); mxs.append(mx); costs.append(c); imp.append(None)
    exts = {k - start: EXT[k] for k in EXT if not lst[k - start].startswith('@')}
    root_child, root_mod, ro, ng = range_tree(ctx, name, TBL, TBLMOD, start, lst, costs, inb, mxs, imp, man, key=ctx, what='%s jobs' % ctx, exts=exts)
    order += ro
    open(rd + '/order.txt', 'w').write('\n'.join(order) + '\n')
    log('%s: %d jobs (%d st-nodes, %d leaves), %d leaf modules (predicted %.0f s total), %d modules in all; root range %s (%s)' % (
        name, count, sum(nodes.values()), sum(len(v) for v in bits.values()), ng, sum(costs), len(order), root_child, root_mod))
    return order, root_child, root_mod, rd

# ---- batched splits (class tier): build_split with bounded memory and disk, for jobs of 1e7 .. 1e9 st-nodes ----
import threading
BSB_PAR = 6                                  # emitter runs at once (each with `threads` threads): the recursion's subtrees run concurrently
BSB_BUDGET = 2000000                         # lineenum's node budget in batched splits (make_slice passes it; emitpkg: KJ_BSB_BUDGET)
_BSB_SEM = threading.Semaphore(BSB_PAR)
_MAN_LOCK = threading.Lock()
def set_bsb_par(n):
    global BSB_PAR, _BSB_SEM
    BSB_PAR = n; _BSB_SEM = threading.Semaphore(n)
def iter_e1p(paths, skip=lambda ix: False):
    """the job records of lineenum9qe --e1p files one at a time, (job index, block literals); a job with skip(ix) is passed over
    without reading its literals (None)"""
    for f in paths:
        with open(f, 'rb') as fh:
            while True:
                h = fh.read(12)
                if len(h) < 12: break
                mg, ix, n = struct.unpack('<III', h); assert mg == 0x4A503145
                if skip(ix):
                    for _ in range(n): fh.seek(struct.unpack('<I', fh.read(4))[0], 1)
                    yield ix, None; continue
                ls = []
                for _ in range(n):
                    ln = struct.unpack('<I', fh.read(4))[0]; ls.append(int.from_bytes(fh.read(ln), 'little'))
                yield ix, ls
def job_costs(rd, deleg=64):
    """per job of an emission: (predicted kernel s of the bit model, leaves, st-nodes), streamed from the dumps (predict_s without
    the per-leaf lists)"""
    nodes, ms, lv = {}, {}, {}
    for f in glob.glob(rd + '/leaves_blocks_t*.txt'):
        for ln in open(f):
            a = ln.split(); j = int(a[0]); nodes[j] = nodes.get(j, 0) + int(a[2])
    for f in glob.glob(rd + '/leaves_t*.txt'):
        for ln in open(f):
            a = ln.split(); j = int(a[0])
            b = 0 if len(a) < 4 else 4 * len(a[3]) - (4 - int(a[3][0], 16).bit_length())
            ms[j] = ms.get(j, 0.0) + ((MS_LEAF0 + MS_LEAF_BIT * b) if b >= deleg else MS_LEAF_IN); lv[j] = lv.get(j, 0) + 1
    return {j: ((F['MS_NODE'] * nodes.get(j, 0) + ms.get(j, 0.0)) / 1000.0, lv.get(j, 0), nodes.get(j, 0)) for j in set(nodes) | set(ms)}
def hdr_of_prefix(ctx, prefix):
    """the mode-0 header of a frontier node (mkht.py: [1] 0, [5] d, [7] pos = the last label, d x [7] labels = positions in the
    ordered IP), as the emitted job's first block carries it"""
    E = EMIT[ctx]
    vecs = list(map(int, open(ipf(E['ip'])).read().split('\n')[1].split())); ordv = list(map(int, open(ipf(E['order'])).read().split()))
    lab = {vecs[o]: i for i, o in enumerate(ordv)}
    pl = [lab[int(v)] for v in prefix.split(',')]; d = len(pl)
    h = (d << 1) | (pl[-1] << (1 + F['HB'] - F['LB']))
    for i, l in enumerate(pl): h |= l << (1 + F['HB'] + F['LB'] * i)
    return h
def split_level(ctx, prefix, depth, rd):
    """the sub-job frontier and the top trace of one split level from ONE DUMPONLY run (mksubfr.py; no job is run), then the top
    chain (e1pconv); idempotent (rd/level.ok)"""
    import subprocess, shutil
    if os.path.exists(rd + '/level.ok'): return
    if os.path.isdir(rd): shutil.rmtree(rd)
    os.makedirs(rd)
    E = EMIT[ctx]; ni = max(0, 10 - os.nice(0)); lp = ('LD_LIBRARY_PATH=%s ' % LIBPATH) if LIBPATH else ''
    with _BSB_SEM: subprocess.run('cd %s && DUMPFRONTIER=fr.txt DUMPONLY=1 %snice -n %d %s %s --order %s %s --threads 1 --root "%s" --frontier %d --cert top '
                   '--state st0.txt --out /dev/null > level.log 2>&1' % (rd, lp, ni, BIN['lineenum'], ipf(E['ip']), ipf(E['order']),
                                                                       emit_opts(ctx), prefix, depth), shell=True, check=True)
    conv_top(ctx, rd)
    open(rd + '/level.ok', 'w').write('ok\n')
def build_split_batched(ctx, prefix, name, man, depth=10, threads=14, hi=300.0, K_=4, limit=600.0, batch_leaves=2.0e6, batch_s=20000.0,
                        b0=64, budget=2000000, log=None):
    """build_split for big jobs with bounded memory and disk: the level's sub-job frontier and top trace from one DUMPONLY run
    (split_level; tables and top from the same run), the sub-jobs emitted in batches of consecutive sub-jobs (sized from the jobs
    seen so far: at most batch_leaves leaves and batch_s predicted kernel s, first batch b0 sub-jobs) with lineenum's node budget
    (`--budget budget --heavy`: a sub-job over it stops early and is listed, so no process emits a giant), each batch's records
    streamed one job at a time; a sub-job over the budget, or predicted over `limit` (then not read), recurses 2 levels deeper on
    its own frontier prefix; the batch's emission files are deleted after use; then one range tree over all sub-jobs (SHT) and the
    top, as build_split.  Same interface and
    return value as build_split: (public theorem of the top, top module, build order, (predicted s, sub-jobs, leaf modules, max s))."""
    IPN, SLN, OKN, IMPS = CFG[ctx]
    rd = RUNDIR[ctx] + 'split_%s' % name
    split_level(ctx, prefix, depth, rd)
    pre = []
    for ln in open(rd + '/fr.txt'):
        if ln.strip(): k, p = ln.split(); assert int(k) == len(pre); pre.append(p)
    nJ = len(pre); HT = [hdr_of_prefix(ctx, p) for p in pre]; kof = {p: k for k, p in enumerate(pre)}
    W = 128 if max(h.bit_length() for h in HT) <= 128 else 256   # as build_split: deep splits need 256-bit entries
    with open(DD + PK + '_%s_SHT.bin' % name, 'wb') as f:
        for h in HT: f.write(h.to_bytes(W // 8, 'little'))
    tbl = PK + '.%s.SHT' % name
    open(MD + '%s_SHT.lean' % name, 'w').write('\n'.join(['module', 'public import RT.Load',
        '/-! # Sub-job header table of split job %s (%d sub-jobs, mode-0 prefix headers), public data -/' % (name, nJ),
        '#rttablew %s "%s" 64 %d' % (tbl, R(DD + PK + '_%s_SHT.bin' % name), W), '']))
    order = [PK + '.%s_SHT' % name]
    manifest([{'module': PK + '.%s_SHT' % name, 'tier': ctx, 'kind': 'table', 'pred_kernel_s': 1.0, 'pred_anon_gb': 0.45,
               'input_bytes': W // 8 * nJ, 'imports': ['RT.Load']}], man)
    res = {}; sub_order = []; EXT = {}; a = 0; seen_l = seen_s = seen_j = 0; nb_ = 0; kids = []; errs = []
    while a < nJ:
        if seen_j: per_l, per_s = seen_l / seen_j, seen_s / seen_j; B = int(min(batch_leaves / max(per_l, 1.0), batch_s / max(per_s, 1e-3)))
        else: B = b0
        B = max(1, min(B, 4096, nJ - a)); b = a + B
        brd = rd + '/b%d' % a
        if not emission_done(brd):
            reset_emission(brd)
            open(brd + '/jobs.txt', 'w').write('\n'.join(str(k) for k in range(a, b)) + '\n')
            with _BSB_SEM: emit(ctx, brd, '--frontierfile %s/fr.txt --jobs jobs.txt --budget %d --heavy heavy.txt' % (rd, budget), threads)
        cs = job_costs(brd); ex = read_ext(brd)
        hv = [kof[l.strip()] for l in open(brd + '/heavy.txt') if l.strip()] if os.path.exists(brd + '/heavy.txt') else []
        assert sorted(list(cs) + hv) == list(range(a, b)), ('batch jobs', a, b, sorted(set(range(a, b)) - set(cs) - set(hv))[:5])
        big = set(hv) | set(k for k in cs if cs[k][0] > limit)
        EXT.update({k: v for k, v in ex.items() if k not in big})
        for k in sorted(big):   # over the budget or predicted over the limit: its own split, 2 levels deeper (records not read), in a thread
            def sub(k=k):
                try:
                    thm, tmod, so, _ = build_split_batched(ctx, pre[k], '%s_s%d' % (name, k), man, depth + 2, threads, hi, K_, limit, batch_leaves, batch_s, b0, budget, log)
                    res[k] = ('@' + thm, 0, 0.0, 1.0, tmod, so)
                except BaseException as e:
                    errs.append((k, repr(e)))
            th = threading.Thread(target=sub); th.start(); kids.append(th)
        for k, lits in iter_e1p(sorted(glob.glob(brd + '/e_*_t*.e1p')), skip=lambda ix: ix in big):
            if lits is None: continue
            c = cs[k][0]
            assert mode0_header(lits[0]) == HT[k], ('header', name, k)
            if heavy_leaves(lits):
                thm, tmod, so, (hc, mx, nb, n) = heavy_split(ctx, '%s_x%d' % (name, k), lits, man, K_, hi, ext=ex.get(k))
                manifest([{'module': tmod, 'tier': ctx, 'kind': 'top', 'lifted': tmod in LIFTED, 'pred_kernel_s': round(max(c - hc, 1.0), 1),
                           'pred_anon_gb': pred_gb_s(mx), 'input_bytes': nb, 'imports': IMPS + ['E1G.Hdr']}], man)
                res[k] = ('@' + thm, 0, 0.0, 1.0, tmod, so + [tmod]); continue
            line, nb, n, mx = write_job(DD + PK + '_%s_j%d' % (name, k), lits, K_, ext=ex.get(k))
            res[k] = (line, nb, mx, c, None, [])
        for f in glob.glob(brd + '/e_*_t*.e1p') + glob.glob(brd + '/leaves*_t*.txt') + glob.glob(brd + '/e_*_leafjobs_t*.bin'): os.remove(f)
        seen_j += len(cs); seen_l += sum(v[1] for v in cs.values()); seen_s += sum(v[0] for v in cs.values()); nb_ += 1
        if log: log('  %s: sub-jobs %d .. %d of %d (batch %d: %d leaves, %.0f s predicted; %d over the budget, %d split)' % (
            name, a, b - 1, nJ, nb_, sum(v[1] for v in cs.values()), sum(v[0] for v in cs.values()), len(hv), len(big)))
        a = b
    for th in kids: th.join()
    if errs: raise RuntimeError('build_split_batched %s: sub-splits failed: %s' % (name, errs[:3]))
    lst = [res[k][0] for k in range(nJ)]; inb = [res[k][1] for k in range(nJ)]; mxs = [res[k][2] for k in range(nJ)]
    costs = [res[k][3] for k in range(nJ)]; imp = [res[k][4] for k in range(nJ)]
    for k in range(nJ): sub_order += res[k][5]
    order += sub_order
    exts = {k: EXT[k] for k in EXT if k < nJ and not lst[k].startswith('@')}
    root_child, root_mod, ro, ng = range_tree(ctx, name, tbl, PK + '.%s_SHT' % name, 0, lst, costs, inb, mxs, imp, man, hi, what='sub-jobs', exts=exts)
    order += ro
    b = open(rd + '/top.bin', 'rb').read(); n = struct.unpack('<I', b[:4])[0]; i = 4; top = []
    for _ in range(n):
        ln = struct.unpack('<I', b[i:i + 4])[0]; i += 4; top.append(int.from_bytes(b[i:i + ln], 'little')); i += ln
    pfx = DD + PK + '_%s_top' % name
    wrlits(pfx + '.bin', top); wrW(pfx, witnesses(top, HT))
    with open(pfx + '_units.txt', 'w') as f:
        for k in range(len(top)): f.write('%d\n' % k)
    tcost = sum(F['MS_NODE'] * 150 for _ in top) / 1000.0
    isl = [False] * len(top)
    open(MD + '%s_Top.lean' % name, 'w').write('\n'.join(header(ctx, priv=[PK + '.%s_SHT' % name, root_mod]) + [
        '/-! # the top chain of split job %s (root %s, cut at depth %d), glued to its %d sub-jobs (batched) -/' % (name, prefix, depth, nJ),
        '#%stop %s.%s.Top "%s.bin" "%s_OF.bin" "%s_WT.bin" "%s_units.txt" %s %s %s %s %d %s' % (F['cmd'], PK, name, R(pfx), R(pfx), R(pfx), R(pfx), IPN, SLN, OKN, tbl, nJ, root_child),
        '#kax ' + PK + '.%s.Top.job' % name, '#kkey "%s" "%s"' % (name, name), '']))
    manifest([{'module': PK + '.%s_Top' % name, 'tier': ctx, 'kind': 'top', 'pred_kernel_s': round(tcost, 1),
               'pred_anon_gb': pred_gb_s(max(unit_s(top, [k], isl) for k in range(len(top)))),
               'input_bytes': os.path.getsize(pfx + '.bin'), 'imports': IMPS + [F['hdr'], PK + '.%s_SHT' % name, root_mod]}], man)
    order.append(PK + '.%s_Top' % name)
    if root_mod in LIFTED: LIFTED.add(PK + '.%s_Top' % name)
    return PK + '.%s.Top.job' % name, PK + '.%s_Top' % name, order, (sum(costs) + tcost, nJ, ng, max(costs))
