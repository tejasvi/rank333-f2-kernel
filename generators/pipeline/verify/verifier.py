#!/usr/bin/env python3
"""verifier.py [--loop 600] [--par 96] [--once]: the live, incremental verifier of the queue's done packages (objstore PREFIX):
integrity, one name one content, and the modhash gate evaluated per package against the producers.  Every loop:
  1. the done/ listing (generation per record); new or rewritten records are read; packages no longer done (superseded) leave the
     produced index (their modules may then be produced again by the replacement).
  2. each new package's tarball, in t_done order (a package's deps are done, so verified, before it):
     * integrity (as scan.py): tarball sha256 = record; every .olean/.olean.private/.olean.server/.ir non-empty, "olean" magic,
       toolchain 4.30.0, last 4 KiB not all zero, sha256 = the package's SHA256SUMS; every module results.jsonl records as built
       has its .olean; .kman/.mhash non-empty;
     * own hashes: each module's KMH line (its .mhash) = sha256 of the shipped .olean (and .olean.private when shipped);
     * store imports (KIMP lines whose path is the box store): the module is produced by this package or by a done package, with
       the same olean hash (and private hash when imported with `import all`);
     * closure imports: resolved through the final top's LEAN_PATH (FINAL_DIR/lpath_final.txt, first root holding the .olean) to a
       file with the same olean hash (private hash when all=1); a module missing there is a problem;
     * NAME-CONFLICT: a module it produces that a different done package already produced with different content;
     * ENV-SHADOW: a module it produces that is also on the final LEAN_PATH; SUSPECT-NAME: an .olean/.olean.private whose bytes
       contain sorryAx, ofReduceBool or trustCompiler (to inspect: a use of any is an extra axiom the audits also report);
     * obligations (audit/obl.txt) into the per-tier union; table modules (.kplain) into the table index.
State: SCAN_DIR/verifier.db (sqlite: produced, packages, problems, obl, tables).  Outputs: SCAN_DIR/verifier.status (one line, also
printed), problems in the db (and SCAN_DIR/verifier_problems.jsonl rewritten every loop); SCAN_DIR/done_records.jsonl caches the done
records.  Paths and settings: queue/kitenv.py (PB_WORK, SCAN_DIR, FINAL_DIR, PB_STORE_PREFIX), the store: objstore.py.  Empty logs of table modules are not problems (by design)."""
import collections, concurrent.futures as cf, hashlib, io, json, os, sqlite3, subprocess, sys, tarfile, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = KE.SCAN; os.makedirs(H, exist_ok=True)
a = sys.argv[1:]
par = int(a[a.index('--par') + 1]) if '--par' in a else 96
loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 600
LP = open(os.path.join(KE.FINAL, 'lpath_final.txt')).read().strip().split(':')
OLEANISH = ('.olean', '.olean.private', '.olean.server', '.ir')
db = sqlite3.connect(KE.VERIFIER_DB, timeout=600)
db.execute('pragma journal_mode=wal')
db.executescript('''
create table if not exists produced (module text primary key, pid text, olean text, private text);
create table if not exists packages (pid text primary key, gen text, t_done real, tier text, modules int, nprob int, t_ver real);
create table if not exists problems (pid text, kind text, detail text);
create table if not exists obl (tier text, module text, const text, primary key (tier, module, const)) without rowid;
create table if not exists tables (pid text, module text);
create index if not exists problems_pid on problems(pid);
create index if not exists produced_pid on produced(pid);
create index if not exists tables_pid on tables(pid);
''')
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
def tier(pid):
    for p, t in (('II.KM2X', 'caseII'), ('II.KM2P', 'caseII'), ('II.JOIN', 'caseII-join'), ('ext_', 'EXT'), ('kcagg', 'classagg'), ('kc_', 'classes'),
                 ('agg_ext', 'ext-top'), ('agg_', 'agg'), ('pt_', 'point'), ('I13', 'I13'), ('I.', 'I'), ('w1_', 'c436/c422/held')):
        if pid.startswith(p): return t
    return 'other'
def env_names():
    """every module name on the final LEAN_PATH (an .olean under some root)"""
    out = set()
    for root in LP:
        for dp, _, fs in os.walk(root):
            for f in fs:
                if f.endswith('.olean'): out.add(os.path.relpath(os.path.join(dp, f[:-6]), root).replace('/', '.'))
    return out
ENV = env_names()
SUSPECT = (b'sorryAx', b'ofReduceBool', b'trustCompiler')
envcache = {}
def env_hash(mod):
    """(path, olean sha256, private sha256 or None) of mod through the final LEAN_PATH, or None"""
    if mod in envcache: return envcache[mod]
    rel = mod.replace('.', '/') + '.olean'; r = None
    for root in LP:
        f = os.path.join(root, rel)
        if os.path.exists(f):
            sh = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
            r = (f, sh(f), sh(f + '.private') if os.path.exists(f + '.private') else None); break
    envcache[mod] = r; return r

def fetch_parse(rec):
    try: return fetch_parse1(rec)
    except Exception as e: return dict(id=rec['id'], error=repr(e)[:200])

def fetch_parse1(rec):
    """download + parse one package (thread): integrity problems and the records the global checks need"""
    pid = rec['id']; probs = []
    try:
        raw = objstore.fetch(B, rec['object'], timeout=180, tries=6)
    except Exception as e:
        return dict(id=pid, error='download: %r' % e)
    if hashlib.sha256(raw).hexdigest() != rec.get('sha256'): probs.append(('INTEGRITY', 'tarball sha256 != done record'))
    p = subprocess.run(['zstd', '-dc'], input=raw, capture_output=True)
    if p.returncode != 0: return dict(id=pid, error='zstd failed')
    tf = tarfile.open(fileobj=io.BytesIO(p.stdout), mode='r:')
    files = {}; sums = {}; results = []; obl = []
    for m in tf.getmembers():
        if not m.isfile(): continue
        n = m.name
        if n.startswith('store/'): files[n] = tf.extractfile(m).read()
        elif n == 'SHA256SUMS':
            for l in tf.extractfile(m).read().decode(errors='replace').splitlines():
                if '  ' in l: h, f = l.split('  ', 1); sums[f] = h
        elif n == 'results.jsonl':
            for l in tf.extractfile(m).read().decode(errors='replace').splitlines():
                try: results.append(json.loads(l))
                except ValueError: probs.append(('INTEGRITY', 'results.jsonl unreadable line'))
        elif n == 'audit/obl.txt':
            obl = [tuple(l.split()[:2]) for l in tf.extractfile(m).read().decode(errors='replace').splitlines() if len(l.split()) >= 2]
    sha = {}
    for n, data in files.items():
        if n.endswith(OLEANISH):
            if not data: probs.append(('INTEGRITY', 'empty ' + n)); continue
            if data[:5] != b'olean': probs.append(('INTEGRITY', 'no olean magic ' + n)); continue
            if data[7:13] != b'4.30.0': probs.append(('INTEGRITY', 'not 4.30.0 ' + n))
            if len(data) >= 4096 and not data[-4096:].strip(b'\0'): probs.append(('INTEGRITY', 'zero tail ' + n))
        elif n.endswith(('.kman', '.mhash')) and not data: probs.append(('INTEGRITY', 'empty ' + n))
        if n.endswith(('.olean', '.olean.private')):
            sha[n] = hashlib.sha256(data).hexdigest()
            hit = [x.decode() for x in SUSPECT if x in data]
            if hit: probs.append(('SUSPECT-NAME', '%s mentions %s' % (n, ','.join(hit))))
        if n in sums and (sha.get(n) or hashlib.sha256(data).hexdigest()) != sums[n]: probs.append(('INTEGRITY', 'sha256 != SHA256SUMS ' + n))
    for x in results:
        if x.get('exit') == 0 and 'store/' + x['module'].replace('.', '/') + '.olean' not in files:
            probs.append(('INTEGRITY', 'built module without .olean ' + x['module']))
    prod = {}; imps = set(); tables = []
    for n, data in files.items():
        if n.endswith('.kplain'): tables.append(n[6:-7].replace('/', '.'))
        if not n.endswith('.mhash'): continue
        for l in data.decode(errors='replace').splitlines():
            t = l.split()
            if not t: continue
            if t[0] == 'KMH':
                kv = dict(x.split('=', 1) for x in t[2:] if '=' in x); prod[t[1]] = (kv.get('olean'), kv.get('private'))
                base = 'store/' + t[1].replace('.', '/')
                if base + '.olean' in sha and sha[base + '.olean'] != kv.get('olean'): probs.append(('OWNHASH', '%s .olean != its KMH' % t[1]))
                if base + '.olean.private' in sha and kv.get('private') and sha[base + '.olean.private'] != kv.get('private'):
                    probs.append(('OWNHASH', '%s .olean.private != its KMH' % t[1]))
            elif t[0] == 'KIMP' and len(t) >= 3:
                kv = dict(x.split('=', 1) for x in t[3:] if '=' in x)
                imps.add((t[1], t[2].startswith(KE.STORE_PREFIX), kv.get('olean'), kv.get('private'), kv.get('all') == '1'))
    return dict(id=pid, probs=probs, prod=prod, imps=imps, obl=obl, tables=tables, modules=len(prod))

PROD = {}          # module -> (pid, olean, private): the produced index in memory (the db table is its persistent copy)
PEND = []          # produced rows not yet written
def load_produced():
    for m, pid, o, pr in db.execute('select module, pid, olean, private from produced'): PROD[m] = (pid, o, pr)
    log('produced index loaded: %d modules' % len(PROD))

def privok(rec_priv, have_priv):
    """an `import all` import (the importer saw the private part): the recorded private hash and the final side's must both exist and
    agree; for other imports private parts are never compared (modhash.py: one side without its private part is only counted)"""
    return rec_priv not in (None, '-') and have_priv not in (None, '-') and rec_priv == have_priv

def apply(res, rec, done_now):
    """global checks (main thread, t_done order) and index updates"""
    pid = res['id']; probs = list(res['probs']); cur = db.cursor()
    for mod, (o, pr) in res['prod'].items():
        if mod in ENV: probs.append(('ENV-SHADOW', '%s produces %s, which is also on the final LEAN_PATH' % (pid, mod)))
        row = PROD.get(mod)
        if row and row[0] != pid and row[0] in done_now and (row[1] != o):
            probs.append(('NAME-CONFLICT', '%s: %s (olean %s) vs %s (olean %s)' % (mod, pid, (o or '')[:12], row[0], (row[1] or '')[:12])))
            continue
        PROD[mod] = (pid, o, pr); PEND.append((mod, pid, o, pr))
    for mod, store, o, pr, al in res['imps']:
        if store:
            own = res['prod'].get(mod)
            if own: ok = own[0] == o and (not al or privok(pr, own[1])); src = 'own'
            else:
                row = PROD.get(mod)
                if not row or row[0] not in done_now: probs.append(('IMPORT-UNRESOLVED', '%s imports %s: no done producer' % (pid, mod))); continue
                ok = row[1] == o and (not al or privok(pr, row[2])); src = row[0]
            if not ok: probs.append(('IMPORT-HASH', '%s imports %s (all=%d): hash differs from producer %s' % (pid, mod, al, src)))
        else:
            e = env_hash(mod)
            if e is None: probs.append(('ENV-MISSING', '%s imports %s: not on the final LEAN_PATH' % (pid, mod))); continue
            if e[1] != o or (al and not privok(pr, e[2])): probs.append(('ENV-HASH', '%s imports %s (all=%d): differs from %s' % (pid, mod, al, e[0])))
    t = tier(pid)
    cur.executemany('insert or ignore into obl values (?,?,?)', [(t, m, c) for m, c in res['obl']])
    cur.execute('delete from tables where pid=?', (pid,)); cur.executemany('insert into tables values (?,?)', [(pid, m) for m in res['tables']])
    cur.execute('delete from problems where pid=?', (pid,)); cur.executemany('insert into problems values (?,?,?)', [(pid, k, d) for k, d in probs])
    # an import whose producer is not verified yet (download error this loop) is retried: the package keeps no generation
    gen = None if any(k == 'IMPORT-UNRESOLVED' for k, _ in probs) else rec.get('_gen')
    cur.execute('insert or replace into packages values (?,?,?,?,?,?,?)', (pid, gen, rec.get('t_done') or 0, t, res['modules'], len(probs), time.time()))

def one_loop():
    listing = {it['name'].rsplit('/', 1)[1][:-5]: str(it['generation']) for it in objstore.ls(B, P + '/done/') if it['name'].endswith('.json')}
    have = dict(db.execute('select pid, gen from packages').fetchall())
    gone = set(have) - set(listing)
    if gone:
        gs = set(gone)
        for m in [m for m, v in PROD.items() if v[0] in gs]: del PROD[m]
    for pid in gone:
        db.execute('delete from produced where pid=?', (pid,)); db.execute('delete from packages where pid=?', (pid,))
        db.execute('delete from problems where pid=?', (pid,)); db.execute('delete from tables where pid=?', (pid,))
    todo = [i for i, g in listing.items() if have.get(i) != g]
    cache = {}
    cf_ = os.path.join(H, 'done_records.jsonl')
    if os.path.exists(cf_):
        for l in open(cf_):
            try: r = json.loads(l)
            except ValueError: continue
            if listing.get(r['id']) == r.get('_gen'): cache[r['id']] = r
    def rd(i):
        if i in cache: return cache[i]
        try:
            g = objstore.get(B, P + '/done/%s.json' % i, timeout=30, tries=4)
            if not g: return None
            d = json.loads(g[0]); d.pop('spec', None); d.pop('kext_lines', None); d['_gen'] = str(g[1]); return d
        except Exception as e:
            log('record read failed (next loop)', i, repr(e)[:120]); return None
    with cf.ThreadPoolExecutor(64) as ex: recs = [r for r in ex.map(rd, todo) if r]
    with open(cf_, 'a') as f:
        for r in recs:
            if r['id'] not in cache: f.write(json.dumps(r) + '\n')
    recs.sort(key=lambda r: r.get('t_done') or 0)
    done_now = set(listing); n = 0; errs = 0
    def flush():
        if PEND: db.executemany('insert or replace into produced values (?,?,?,?)', PEND); PEND.clear()
        db.commit()
    import multiprocessing
    # processes, not threads: parsing a tarball is ~0.2 s of GIL-bound Python, which capped threads at ~6 packages/s
    with cf.ProcessPoolExecutor(int(os.environ.get('VERIFIER_PROCS', 48)), mp_context=multiprocessing.get_context('fork')) as ex:
        # in chunks: map submits everything at once, and finished results would pile up in memory while the main process applies
        # them in t_done order
        for c0 in range(0, len(recs), 4000):
            chunk = recs[c0:c0 + 4000]
            for rec, res in zip(chunk, ex.map(fetch_parse, chunk, chunksize=8)):
                if 'error' in res: errs += 1; continue
                apply(res, rec, done_now); n += 1
            flush(); log('verified %d/%d' % (n, len(recs)))
    flush()
    pcounts = dict(db.execute('select kind, count(*) from problems group by kind').fetchall())
    obl = dict(db.execute('select tier, count(*) from obl group by tier').fetchall())
    npk = db.execute('select count(*) from packages').fetchone()[0]; nmod = db.execute('select count(*) from produced').fetchone()[0]
    ntab = db.execute('select count(*) from tables').fetchone()[0]
    with open(os.path.join(H, 'verifier_problems.jsonl.tmp'), 'w') as f:
        for pid, k, d in db.execute('select pid, kind, detail from problems order by kind, pid'): f.write(json.dumps(dict(pid=pid, kind=k, detail=d)) + '\n')
    os.replace(os.path.join(H, 'verifier_problems.jsonl.tmp'), os.path.join(H, 'verifier_problems.jsonl'))
    line = '%s verified %d done packages (%d new, %d superseded removed, %d download errors retried next loop), %d modules, %d table modules; problems %s; obligation unions %s' % (
        time.strftime('%FT%TZ', time.gmtime()), npk, n, len(gone), errs, nmod, ntab, json.dumps(pcounts), json.dumps(obl))
    open(os.path.join(H, 'verifier.status'), 'w').write(line + '\n'); print(line, flush=True)

load_produced()
while True:
    try: one_loop()
    except Exception as e: log('loop error', repr(e)[:300])
    if '--once' in a: break
    time.sleep(loop)
