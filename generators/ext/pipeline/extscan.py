#!/usr/bin/env python3
# extscan.py (reference copy): reads the EXT leaves that finished packages report, groups them into EXT packages and writes their queue lines.
# Regeneration does not need it: its outputs are shipped (inputs/ext/, generators/ext/package_tools.tsv.zst).
# Reads $STORE (object store), $QUEUE_PREFIX (queue prefix), $PIPELINE_DIR (objstore.py, the store client), $KP_ROOT, $PIN_POOL, $EXT_IP, $EXT_ARCHIVE.
"""extscan.py: discovery of EXT leaves in the build queue and their EXT packages.

  extscan.py scan  [--bucket B] [--prefix P] [--state DIR] [--loop S] [--submit]
  extscan.py class FILE CAP [--state DIR] [--submit]       (a class list file: one package for the class)
  extscan.py chunks CAP [--state DIR]                       (the done EXT packages' chunks of CAP: input of mkexttop.py)

scan: every S seconds (once without --loop) the done records of PREFIX not seen before are read; for each with "kext" > 0 its
tarball's emit/kext.txt (the emitter's authoritative list, "c<cap> <jobkey> <l1,…,lR> <flag>") is read. New leaves (dedup by cap and
pl = Σ l_i 2^(7i)) are appended to STATE/ext_c<cap>.tsv ("key labels flag pl source") and each becomes one package line
    {"id": "ext_c<cap>_<x…>", "cap", "kind": "ext", "leaves": [...], "pred_s", "pred_gb_max", "tools": {...},
     "emit": {"type": "cmd", "argv": ["bash", "-c", <extpkg.sh>, "extpkg", "<cap>", "<base64 leaf line>", "{OUT}"]}}
in STATE/pending.jsonl. With --submit the pending lines are inserted at the HEAD of PREFIX/packages.jsonl (generation-matched
read-modify-write; workers rescan the queue, so they are claimed before the packages behind them), recorded in
STATE/submitted.jsonl. The deduped lists are archived to $EXT_ARCHIVE in the store (with SHA256SUMS) after each change.
Package ids, leaf module names and emissions are deterministic, so a resubmitted leaf rebuilds byte-identical modules."""
import sys, os, re, json, time, base64, hashlib, subprocess, argparse, collections, math
sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get('PIPELINE_DIR', '.'))
import objstore

EO, ES = open(os.path.join(HERE, 'extpkg_v13.obj')).read().split()       # the bootstrap script object (bootstrap v13: tools v12) and its sha256
EXTPKG_SH = open(os.path.join(HERE, 'extpkg_v13.sh')).read()
assert hashlib.sha256(EXTPKG_SH.encode()).hexdigest() == ES
LSCRIPT = '${KP_ROOT}/plane/' + os.path.basename(EO)
# the inline loader: fetch the versioned bootstrap script once per machine (sha256-checked), then run it
LOADER = ('set -e; S=%s; if [ ! -f $S ]; then mkdir -p ${KP_ROOT}/plane; T=$S.$$; python3 -c \'import sys; sys.path.insert(0, "${KP_ROOT}/tools"); '
          'import objstore; objstore.download_file(sys.argv[1], sys.argv[2], sys.argv[3])\' "$STORE" %s $T; '
          'echo "%s  $T" | sha256sum -c --quiet; mv $T $S; fi; exec bash $S "$@"') % (LSCRIPT, EO, ES)
TOOLS = dict(bootstrap=[EO, ES],
             plane=re.findall(r'^inst (\S+) (\S+)$', EXTPKG_SH, re.M),       # [(object, sha256)]: closure part, tools
             extpkg_py=hashlib.sha256(open(os.path.join(HERE, '..', 'scripts', 'extpkg.py'), 'rb').read()).hexdigest(),
             gen7pc=hashlib.sha256(open(os.path.join(HERE, '..', 'bin', 'gen7pc'), 'rb').read()).hexdigest())

GROUP = 16           # UNSAT-type EXT leaves per package

def log(*a): print(time.strftime('%FT%TZ', time.gmtime()), *a, flush=True)

def pl_of(labs): return sum(l << (7 * i) for i, l in enumerate(labs))

def leafline(k, labs, f, pl): return '%s %s %s %d\n' % (k, ','.join(map(str, labs)), f, pl)
# giant-like single leaves: a CC S/B/E leaf whose terms repeat a lot (<= 12 distinct values of 19, or an EqF factor >= 96) can have
# a 500k-800k-bit main record, and its aggregator then needs 30-50 GB at once; such leaves go to the pin pool (state/pin_pool.txt,
# one machine per line, else $PIN_POOL) with min_mem_gb 128
_VT = {}
def _vt(cap):
    if cap not in _VT:
        import glob
        p = (glob.glob(os.path.join(os.environ.get('EXT_IP', os.path.join(HERE, '..', '..', '..', 'inputs', 'ext', 'ip')), 'IP_c%s.lean' % cap)) or [None])[0]
        _VT[cap] = int(re.search(r'def VT : Nat := (0x[0-9a-f]+|\d+)', open(p).read()).group(1), 0) if p else None
    return _VT[cap]
def giant_like(cap, leaves):
    if cap not in ('436', '422') or len(leaves) != 1 or leaves[0][2] not in ('S', 'B', 'E'): return False
    vt = _vt(cap)
    if vt is None: return False
    terms = [(vt >> (9 * l)) & 511 for l in leaves[0][1]]
    fac = 1
    for v in collections.Counter(terms).values(): fac *= math.factorial(v)
    return len(set(terms)) <= 12 or fac >= 96      # ext_c436_x79030781b541af39 (533k main bits): 13 distinct values, factor 96
def pin_pool():
    p = os.path.join(HERE, 'state', 'pin_pool.txt')
    if os.path.exists(p):
        b = [l.strip() for l in open(p) if l.strip() and not l.startswith('#')]
        if b: return b
    return os.environ.get('PIN_POOL', '').split()
def pin_for(pid):
    pool = pin_pool(); return pool[int(hashlib.sha256(pid.encode()).hexdigest(), 16) % len(pool)] if pool else None
def nosplit(sp):
    """the emit settings of a giant: a 200 GB address-space cap (tools v12 holds the assembled tree in one process). The tools-v10
    giants of the final set ran with EXTPKG_NOSPLIT=1 (single-threaded gen7pc_eqf: grouped parts, a small main record), because the
    tools-v9/v10 parallel split puts the whole upper tree in the main record and one part per item (package_tools.tsv, column env)"""
    sp['emit']['as_gb'] = 200
    return sp

def spec(cap, leaves, pid=None, ref=None, min_mem_gb=None, pin_box=None):
    """the package line of leaves [(key, labels, flag, pl)] of cap ('436', '422' or 'h<c>'); ref = (object, sha256, a, b): the
    leaves are lines a..b-1 of that leaf-list object (v3 lines), else they are inlined (base64, v2 lines)"""
    txt = ''.join(leafline(*x) for x in leaves)
    if pid is None:
        pid = 'ext_c%s_x%s' % (cap, hashlib.sha256(('c%s:%d' % (cap, leaves[0][3])).encode()).hexdigest()[:16]) if len(leaves) == 1 \
            else 'ext_%s_%s' % (cap, hashlib.sha256(txt.encode()).hexdigest()[:12])
    if ref is not None:
        pred = sum(1800.0 if f == 'S' else 7200.0 if f in ('B', 'E') else 120.0 for _, _, f, _ in leaves)
        return dict(id=pid, cap=cap, kind='ext', pred_s=pred, pred_gb_max=2.5 if any(f in ('B', 'E') for _, _, f, _ in leaves) else 2.0,
                    nleaves=len(leaves), leaves_ref=dict(object=ref[0], sha256=ref[1], a=ref[2], b=ref[3]), tools=dict(bootstrap=[EO, ES]),
                    emit=dict(type='cmd', argv=['bash', '-c', LOADER, 'extpkg', cap, '@gs:%s:%s:%d:%d' % ref, '{OUT}']),
                    _leaves=[dict(key=k, labels=','.join(map(str, labs)), flag=f, pl=str(pl)) for k, labs, f, pl in leaves],
                    **({'min_mem_gb': min_mem_gb} if min_mem_gb else {}), **({'pin_box': pin_box} if pin_box else {}))
    # predicted seconds before emission (the emitter's manifest refines them): UNSAT-type leaves (U, B, E) ~1-5 min, SAT leaves ~30 min
    return dict(id=pid, cap=cap, kind='ext', pred_s=sum(1800.0 if f == 'S' else 300.0 for _, _, f, _ in leaves), pred_gb_max=2.0,
                leaves=[dict(key=k, labels=','.join(map(str, labs)), flag=f, pl=str(pl)) for k, labs, f, pl in leaves],
                tools=TOOLS, emit=dict(type='cmd', argv=['bash', '-c', EXTPKG_SH, 'extpkg', cap, base64.b64encode(txt.encode()).decode(), '{OUT}']))

class State:
    def __init__(self, d):
        self.d = d; os.makedirs(d, exist_ok=True)
        self.seen_done = set(l.strip() for l in open(self.f('seen_done.txt'))) if os.path.exists(self.f('seen_done.txt')) else set()
        self.leaves = {}          # (cap, pl) -> line
        for fn in os.listdir(d):
            m = re.fullmatch(r'ext_c?(\w+)\.tsv', fn)
            if m:
                for l in open(self.f(fn)):
                    w = l.split()
                    if len(w) >= 4: self.leaves[(m.group(1), int(w[3]))] = l
    def f(self, n): return os.path.join(self.d, n)
    def add_leaf(self, cap, key, labs, flag, src):
        pl = pl_of(labs)
        if (cap, pl) in self.leaves: return None
        line = '%s %s %s %d %s\n' % (key, ','.join(map(str, labs)), flag, pl, src)
        self.leaves[(cap, pl)] = line
        with open(self.f('ext_c%s.tsv' % cap if cap.isdigit() else 'ext_%s.tsv' % cap), 'a') as fh: fh.write(line)
        return (key, labs, flag, pl)
    def mark_done(self, ids):
        with open(self.f('seen_done.txt'), 'a') as fh: fh.write(''.join(i + '\n' for i in ids))
        self.seen_done |= set(ids)
    def pend(self, specs):
        with open(self.f('pending.jsonl'), 'a') as fh: fh.write(''.join(json.dumps(s) + '\n' for s in specs))

def kext_of_tarball(bucket, obj, tmp):
    objstore.download_file(bucket, obj, tmp)
    out = ''
    for member in ('emit/kext.txt', 'kext.txt'):
        r = subprocess.run(['bash', '-c', 'zstd -dc %s | tar -xOf - %s 2>/dev/null' % (tmp, member)], capture_output=True, text=True)
        if r.stdout.strip(): out = r.stdout; break
    os.remove(tmp)
    leaves = []
    for l in out.splitlines():
        w = l.split()
        if w and w[0] == 'KEXT': w = w[1:]
        if len(w) < 4: continue
        m = re.match(r'c(436|422)', w[0])          # c436, c422 and their heavy contexts (c436h209: job 209's sub-jobs, same IP)
        mh = re.match(r'(h\d+)(h\d+)?$', w[0])     # class-raise contexts: h490, h490h9 (heavy job 9 of class h490)
        if m: cap = m.group(1)
        elif mh: cap = mh.group(1)
        else: raise RuntimeError('EXT leaf of an unknown context %s' % w[0])
        leaves.append((cap, w[1], list(map(int, w[2].split(','))), w[3]))
    return leaves

def submit(bucket, prefix, st):
    """insert STATE/pending.jsonl at the head of PREFIX/packages.jsonl (generation-matched), then move them to submitted"""
    pf = st.f('pending.jsonl')
    if not os.path.exists(pf) or not os.path.getsize(pf): return 0
    new = [l for l in open(pf) if l.strip()]
    qlines = [json.dumps({k: v for k, v in json.loads(l).items() if not k.startswith('_')}) + '\n' for l in new]
    for att in range(10):
        r = objstore.get(bucket, prefix + '/packages.jsonl')
        if r is None: raise RuntimeError('no packages.jsonl')
        cur, gen = r[0].decode(), r[1]
        have = set(json.loads(l)['id'] for l in cur.splitlines() if l.strip())
        add = [l for l in qlines if json.loads(l)['id'] not in have]
        if not add: break
        try:
            objstore.put(bucket, prefix + '/packages.jsonl', (''.join(add) + cur).encode(), if_generation=gen)
            break
        except objstore.Precondition:
            time.sleep(2 + att)
    else:
        raise RuntimeError('packages.jsonl kept changing')
    with open(st.f('submitted.jsonl'), 'a') as fh: fh.write(''.join(new))
    os.remove(pf)
    log('submitted', len(add), 'EXT packages at the head of', prefix + '/packages.jsonl')
    return len(add)

def archive(bucket, st):
    files = sorted(fn for fn in os.listdir(st.d) if fn.startswith('ext_') and fn.endswith('.tsv'))
    sums = ''
    for fn in files:
        objstore.upload_file(bucket, os.environ.get('EXT_ARCHIVE', 'repro/ext/lists') + '/' + fn, st.f(fn))
        sums += '%s  %s\n' % (hashlib.sha256(open(st.f(fn), 'rb').read()).hexdigest(), fn)
    objstore.put(bucket, os.environ.get('EXT_ARCHIVE', 'repro/ext/lists') + '/SHA256SUMS', sums.encode())

GROUPS = {'U': 32}       # leaves per package by flag (S, B, E: alone, they can be large)
EQF_MIN = 4              # without the EqF tools (EQF_LIVE False), a SAT leaf whose equal-first-factor product is >= EQF_MIN is held
EQF_LIVE = True          # the EqF tools (tools v5 on) are in use: no holding; held leaves are queued by `extscan.py release`

def eqf_factor(labs):
    """the order of the equal-first-factor symmetry: the product of (multiplicity)! over the leaf's labels (equal labels = equal
    first factors; the labels index the IP's VT)"""
    import math, collections
    f = 1
    for m in collections.Counter(labs).values(): f *= math.factorial(m)
    return f

def upload_leaves(a, lines, tag):
    """one leaf-list object for a round's packages; returns (object, sha256)"""
    data = ''.join(lines).encode(); sha = hashlib.sha256(data).hexdigest()
    obj = '%s/extleaves/%s_%s.txt' % (a.prefix, tag, sha[:12])
    f = os.path.join(a.state, 'lastround.txt'); open(f, 'wb').write(data)
    objstore.upload_file(a.bucket, obj, f)
    m = objstore.stat(a.bucket, obj)
    assert m and int(m['size']) == len(data), 'leaf list upload failed'
    return obj, sha

def scan_once(a, st):
    from concurrent.futures import ThreadPoolExecutor
    ids = [it['name'].rsplit('/', 1)[1][:-len('.json')] for it in objstore.ls(a.bucket, a.prefix + '/done/')]
    new = [i for i in ids if i not in st.seen_done and not i.startswith('ext_')]
    def read(pid):
        r = objstore.get(a.bucket, '%s/done/%s.json' % (a.prefix, pid))
        if r is None: return pid, None
        d = json.loads(r[0])
        if d.get('kext', 0) <= 0: return pid, []
        return pid, kext_of_tarball(a.bucket, d['object'], os.path.join(st.d, 'tmp.%s.tar.zst' % pid))
    with ThreadPoolExecutor(16) as ex:
        res = list(ex.map(read, new))
    # new leaves of the round, in done-record order, deduplicated against the state and within the round
    fresh = {}; order = []; ok_ids = []
    for pid, ks in res:
        if ks is None: continue
        ok_ids.append(pid)
        for cap, key, labs, flag in ks:
            pl = pl_of(labs)
            if (cap, pl) in st.leaves or (cap, pl) in fresh: continue
            fresh[(cap, pl)] = (cap, key, labs, flag, pid); order.append((cap, pl))
    groups = {}; held = []
    for kk in order:
        cap, key, labs, flag, pid = fresh[kk]
        if cap.startswith('h') and flag == 'S':
            held.append((cap, key, labs, flag, kk[1], pid, -1)); continue        # class route: a SAT leaf is not expected (reported)
        if flag == 'S' and eqf_factor(labs) >= EQF_MIN and not a.no_eqf_hold and not EQF_LIVE:
            held.append((cap, key, labs, flag, kk[1], pid, eqf_factor(labs))); continue
        groups.setdefault((cap, flag), []).append((key, labs, flag, kk[1]))
    if held:
        with open(st.f('held_eqf.tsv'), 'a') as fh:
            fh.write(''.join('%s %s %s %s %d %s %d\n' % (cap, key, ','.join(map(str, labs)), flag, pl, pid, F) for cap, key, labs, flag, pl, pid, F in held if F >= 0))
        with open(st.f('held_class.tsv'), 'a') as fh:
            fh.write(''.join('%s %s %s %s %d %s\n' % (cap, key, ','.join(map(str, labs)), flag, pl, pid) for cap, key, labs, flag, pl, pid, F in held if F < 0))
    pk = []
    for (cap, flag), lfs in sorted(groups.items()):
        g = GROUPS.get(flag, 1)
        pk += [(cap, lfs[i:i + g]) for i in range(0, len(lfs), g)]
    specs = []
    if pk:
        lines = [leafline(*x) for _, lfs in pk for x in lfs]
        obj, sha = upload_leaves(a, lines, time.strftime('%Y%m%dT%H%M%S', time.gmtime()))
        at = 0
        for cap, lfs in pk:
            sp = spec(cap, lfs, ref=(obj, sha, at, at + len(lfs)))
            if giant_like(cap, lfs): sp.update(min_mem_gb=128, pin_box=pin_for(sp['id'])); nosplit(sp)
            specs.append(sp); at += len(lfs)
    # pending first, then the leaves: a kill between the two never marks a leaf known that was not submitted (at worst some leaves
    # are submitted again in another package)
    if specs: st.pend(specs)
    for kk in order:
        cap, key, labs, flag, pid = fresh[kk]; st.add_leaf(cap, key, labs, flag, pid)
    st.mark_done(ok_ids)
    if specs: archive(a.bucket, st)
    log('scanned %d new done records (%d total); %d new EXT leaves in %d packages, %d held (EqF or class route); %d known' % (len(ok_ids), len(ids), len(order) - len(held), len(specs), len(held), len(st.leaves)))

def park(a, pid, by):
    """set a failed package's lease to "parked" (superseded by `by`) if it is still failed; True when parked (or already parked)"""
    r = objstore.get(a.bucket, '%s/lease/%s' % (a.prefix, pid))
    if r is None: return False
    d = json.loads(r[0])
    if d.get('state') == 'parked': return True
    if d.get('state') != 'failed': return False
    d.update(state='parked', reason='superseded by %s (EXT resubmission)' % by, t=time.time())
    try:
        objstore.put(a.bucket, '%s/lease/%s' % (a.prefix, pid), json.dumps(d), if_generation=r[1])
        objstore.put(a.bucket, '%s/parked/%s' % (a.prefix, pid), ('superseded by %s' % by).encode())
        return True
    except objstore.Precondition:
        return False

def resubmit(a, st):
    """failed EXT packages: when the latest attempt of a package failed (and none succeeded), the same leaves go in again under
    the next attempt id (_r2, _r3, ...) with the current bootstrap"""
    if not os.path.exists(st.f('submitted.jsonl')): return
    sub = {}
    for l in open(st.f('submitted.jsonl')): x = json.loads(l); sub[x['id']] = x
    failed = set(it['name'].rsplit('/', 1)[1] for it in objstore.ls(a.bucket, a.prefix + '/failed/ext_'))
    # a parked latest attempt is resubmitted like a failed one
    failed |= set(it['name'].rsplit('/', 1)[1] for it in objstore.ls(a.bucket, a.prefix + '/parked/ext_'))
    done = set(it['name'].rsplit('/', 1)[1][:-len('.json')] for it in objstore.ls(a.bucket, a.prefix + '/done/ext_'))
    att = {}
    for pid in sub:
        if pid.endswith('.sb'):        # a split final (cutgiant.py): a done one counts for its family, it is never resubmitted itself
            q = pid[:-3]; m = re.fullmatch(r'(.*)_r(\d+)', q); att.setdefault(m.group(1) if m else q, []).append((-1, pid)); continue
        m = re.fullmatch(r'(.*)_r(\d+)', pid)
        base, n = (m.group(1), int(m.group(2))) if m else (pid, 1)
        att.setdefault(base, []).append((n, pid))
    redo = []
    for base, lst in sorted(att.items()):
        n, latest = max(lst)
        if latest in failed and not any(p in done for _, p in lst) and n < 8:     # up to _r8
            # another attempt of the same leaf still running: no new attempt
            def _held(p):
                r = objstore.get(a.bucket, '%s/lease/%s' % (a.prefix, p))
                return bool(r) and json.loads(r[0]).get('state') == 'held'
            if any(_held(p) for _, p in lst if p != latest): continue
            # park the failed attempt first (generation-matched): the sweep must not requeue it, or two attempts with different
            # tools could both succeed and put two contents under the same module names; skip if it is no longer failed
            if not park(a, latest, '%s_r%d' % (base, n + 1)): continue
            o = sub[base]
            leaves = [(x['key'], list(map(int, x['labels'].split(','))), x['flag'], int(x['pl'])) for x in o.get('leaves') or o['_leaves']]
            redo.append((o['cap'], leaves, '%s_r%d' % (base, n + 1)))
    if redo:
        obj, sha = upload_leaves(a, [leafline(*x) for _, lfs, _ in redo for x in lfs], 'resubmit_' + time.strftime('%Y%m%dT%H%M%S', time.gmtime()))
        specs = []; at = 0
        for cap, lfs, nid in redo:
            # a resubmission needs >= 128 GB (a giant leaf's aggregator: 56 GB predicted at 533k main bits) and is pinned to a member
            # of the pin pool (by id), so no ordinary machine claims it
            hb = pin_for(nid)
            specs.append(nosplit(spec(cap, lfs, pid=nid, ref=(obj, sha, at, at + len(lfs)), min_mem_gb=128, pin_box=hb))); at += len(lfs)
        st.pend(specs); log('resubmit: %d failed EXT packages -> %s' % (len(specs), [x['id'] for x in specs]))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd'); ap.add_argument('args', nargs='*')
    ap.add_argument('--bucket', default=os.environ.get('STORE')); ap.add_argument('--prefix', default=os.environ.get('QUEUE_PREFIX'))
    ap.add_argument('--state', default=os.path.join(HERE, 'state')); ap.add_argument('--loop', type=int, default=0)
    ap.add_argument('--submit', action='store_true'); ap.add_argument('--no-eqf-hold', action='store_true'); ap.add_argument('--with-pkg', action='store_true')
    a = ap.parse_args(); st = State(a.state)
    if a.cmd == 'scan':
        while True:
            try:
                scan_once(a, st); resubmit(a, st)
                if a.submit: submit(a.bucket, a.prefix, st)     # one rewrite of packages.jsonl per round
            except Exception as e: log('scan error:', repr(e))
            if not a.loop: break
            time.sleep(a.loop)
    elif a.cmd == 'class':
        fn, cap = a.args
        leaves = []
        for l in open(fn):
            w = l.split()
            if len(w) < 3: continue
            labs = list(map(int, w[1].split(',')))
            if len(w) > 3: assert int(w[3]) == pl_of(labs), w[0]
            leaves.append((w[0], labs, w[2], pl_of(labs)))
        for k, labs, f, pl in leaves: st.add_leaf(cap, k, labs, f, 'class-list')
        st.pend([spec(cap, leaves, pid='ext_%s' % cap)])
        archive(a.bucket, st); log('class %s: %d leaves pending as ext_%s' % (cap, len(leaves), cap))
        if a.submit: submit(a.bucket, a.prefix, st)
    elif a.cmd == 'resubmit':
        resubmit(a, st)
        if a.submit: submit(a.bucket, a.prefix, st)
    elif a.cmd == 'release':
        # the SAT leaves held for EqF (state/held_eqf.tsv): one package per leaf, at the head of the queue (the EqF tools route them)
        done_rel = set(l.strip() for l in open(st.f('released_eqf.txt'))) if os.path.exists(st.f('released_eqf.txt')) else set()
        rows = [l.split() for l in open(st.f('held_eqf.tsv'))] if os.path.exists(st.f('held_eqf.tsv')) else []
        todo = [(w[0], w[1], list(map(int, w[2].split(','))), w[3], int(w[4])) for w in rows if '%s:%s' % (w[0], w[4]) not in done_rel]
        if todo:
            lines = [leafline(k, labs, f, pl) for _, k, labs, f, pl in todo]
            obj, sha = upload_leaves(a, lines, 'eqf_' + time.strftime('%Y%m%dT%H%M%S', time.gmtime()))
            st.pend([spec(cap, [(k, labs, f, pl)], ref=(obj, sha, i, i + 1)) for i, (cap, k, labs, f, pl) in enumerate(todo)])
            with open(st.f('released_eqf.txt'), 'a') as fh: fh.write(''.join('%s:%d\n' % (cap, pl) for cap, _, _, _, pl in todo))
        log('release: %d held SAT leaves queued as EqF packages' % len(todo))
        if a.submit: submit(a.bucket, a.prefix, st)
    elif a.cmd == 'classrelease':
        # class leaves held in state/held_class.tsv (flags U/B/E): packages as in a scan round
        done_rel = set(l.strip() for l in open(st.f('released_class.txt'))) if os.path.exists(st.f('released_class.txt')) else set()
        rows = [l.split() for l in open(st.f('held_class.tsv'))] if os.path.exists(st.f('held_class.tsv')) else []
        todo = [(w[0], w[1], list(map(int, w[2].split(','))), w[3], int(w[4])) for w in rows if w[3] != 'S' and '%s:%s' % (w[0], w[4]) not in done_rel]
        groups = {}
        for cap, k, labs, f, pl in todo: groups.setdefault((cap, f), []).append((k, labs, f, pl))
        pk = []
        for (cap, f), lfs in sorted(groups.items()):
            g = GROUPS.get(f, 1); pk += [(cap, lfs[i:i + g]) for i in range(0, len(lfs), g)]
        if pk:
            obj, sha = upload_leaves(a, [leafline(*x) for _, lfs in pk for x in lfs], 'class_' + time.strftime('%Y%m%dT%H%M%S', time.gmtime()))
            specs = []; at = 0
            for cap, lfs in pk:
                specs.append(spec(cap, lfs, ref=(obj, sha, at, at + len(lfs)))); at += len(lfs)
            st.pend(specs)
            with open(st.f('released_class.txt'), 'a') as fh: fh.write(''.join('%s:%d\n' % (cap, pl) for cap, _, _, _, pl in todo))
        log('classrelease: %d class leaves in %d packages' % (len(todo), len(pk)))
        if a.submit: submit(a.bucket, a.prefix, st)
    elif a.cmd == 'chunks':
        cap = a.args[0]
        done = set(it['name'].rsplit('/', 1)[1][:-len('.json')] for it in objstore.ls(a.bucket, a.prefix + '/done/ext_'))
        subs = [json.loads(l) for l in open(st.f('submitted.jsonl'))] if os.path.exists(st.f('submitted.jsonl')) else []
        best = {}; ndone = collections.Counter()
        for s in subs:
            if s['cap'] != cap: continue
            base = re.sub(r'_r\d+$', '', re.sub(r'\.sb$', '', s['id']))      # ID.sb (cutgiant.py's split final) is an attempt of ID
            if s['id'] in done: best[base] = s['id']; ndone[base] += 1
            else: best.setdefault(base, None)
        for base, k in ndone.items():
            if k > 1: print('# CONFLICT: %d done attempts of %s (two contents under the same module names)' % (k, base))
        bysub = {x['id']: x for x in subs}
        verify = '--verify' in sys.argv
        for base, pid in sorted(best.items()):
            if pid is None: print('# not done:', base); continue
            if not verify:
                # the chunk is a deterministic function of the package's leaves (extpkg.py: dedup and sort by pl, sha256 name)
                pls = sorted(set(int(x['pl']) for x in (bysub[pid].get('leaves') or bysub[pid]['_leaves'])))
                if cap.startswith('h'):   # class route (extpkg.nd_package)
                    name = 'NDX.%s.X%s' % (cap, hashlib.sha256(('%s:' % cap + ','.join(map(str, pls))).encode()).hexdigest()[:16])
                else:
                    name = 'PLE.c%s.X%s' % (cap, hashlib.sha256(('c%s:' % cap + ','.join(map(str, pls))).encode()).hexdigest()[:16])
                print('%s %s%s' % (name, ','.join(map(str, pls)), (' ' + pid) if '--with-pkg' in sys.argv else '')); continue
            r = objstore.get(a.bucket, '%s/done/%s.json' % (a.prefix, pid))
            d = json.loads(r[0]); t = os.path.join(st.d, 'tmp.tar.zst'); objstore.download_file(a.bucket, d['object'], t)
            dn = json.loads(subprocess.run(['bash', '-c', 'zstd -dc %s | tar -xOf - emit/DONE' % t], capture_output=True, text=True).stdout)
            os.remove(t)
            print('%s %s' % (dn['pubs'][0][0], ','.join(dn['pls'])))
    else:
        sys.exit(__doc__)

main()
