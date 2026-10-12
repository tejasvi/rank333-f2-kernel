#!/usr/bin/env python3
"""v5.py [--snapshot SNAPDIR]: the V5 census (V5_CHECKLIST.md): one PASS/FAIL line per item from the artifacts, written to
FINAL_DIR/V5_RESULT.txt (and the set lists to FINAL_DIR/V5_SETS.tsv).  Run after the last verifier and walk passes and
final_build.sh.  Items not yet producible print PENDING (a PENDING is not a PASS).  With --snapshot: the queue state of that frozen
snapshot (snapshot.py) instead of live listings.  Env: kitenv.py (FINAL_DIR, SCAN_DIR, VERIFIER_DB, REAUDIT_FILE, GATES_FILE),
objstore.py; V5_TOOLCHAIN_CLOSURE (the file name of the toolchain closure in the done records' provenance; default
kclosure_v1.tar.zst)."""
import collections, glob, gzip, json, os, sqlite3, sys, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = KE.FINAL
TCLOS = os.environ.get('V5_TOOLCHAIN_CLOSURE', 'kclosure_v1.tar.zst')
out = []
def item(k, ok, msg): out.append('%-4s %-8s %s' % (k, ('PASS' if ok else 'FAIL') if ok is not None else 'PENDING', msg)); print(out[-1], flush=True)
SNAP = sys.argv[sys.argv.index('--snapshot') + 1] if '--snapshot' in sys.argv else None
if SNAP:     # one frozen snapshot (snapshot.py): the done listing, spec lines, parked and superseded ids, gate lines
    SID = json.load(open(os.path.join(SNAP, 'SNAPSHOT.json')))['id']
    listing = dict(l.rstrip('\n').split('\t') for l in open(os.path.join(SNAP, 'done_listing.tsv')) if l.strip())
    pk = [json.loads(l) for l in open(os.path.join(SNAP, 'packages.jsonl')) if l.strip()]
    parked = {l.strip() for l in open(os.path.join(SNAP, 'parked.txt')) if l.strip()}
    superseded = {l.strip() for l in open(os.path.join(SNAP, 'superseded.txt')) if l.strip()}
    gates = [json.loads(l) for l in open(os.path.join(SNAP, 'gates.jsonl')) if l.strip()]
else:
    SID = 'live'
    listing = {it['name'].rsplit('/', 1)[1][:-5]: str(it['generation']) for it in objstore.ls(B, P + '/done/', fields='name,generation') if it['name'].endswith('.json')}
    pk = [json.loads(l) for l in objstore.get(B, P + '/packages.jsonl')[0].decode().splitlines() if l.strip()]
    parked = {it['name'].rsplit('/', 1)[1] for it in objstore.ls(B, P + '/parked/', fields='name')}
    superseded = {it['name'].rsplit('/', 1)[1][:-5] for it in objstore.ls(B, P + '/superseded/', fields='name') if it['name'].endswith('.json')}
    gates = []
    for f in KE.gate_files():
        if f.startswith('//'):                        # a gate file kept as a store object, "//<namespace>/<name>" (the EXT top lines)
            gb, go = f[2:].split('/', 1); g = objstore.get(gb, go)
            gates += [json.loads(l) for l in (g[0].decode().splitlines() if g else []) if l.strip()]
            continue
        gates += [json.loads(l) for l in open(f) if l.strip()]
ids = [x['id'] for x in pk]; notdone = [i for i in ids if i not in listing and i not in parked]
# A0: the sets.  (a) the final set: the producers of R22K.Final's top-store modules (census/closure_classified.tsv, store-PASS rows)
# and, through the spec lines' "deps", everything they build on;  (b) every done record that is not superseded;  (c) = (b) - (a)
SPEC = {x['id']: x for x in pk}
start = {l.rstrip('\n').split('\t')[3] for l in open(os.path.join(H, 'census', 'closure_classified.tsv')) if l.split('\t')[1] == 'store-PASS'}
dag = set(); st = list(start)
while st:
    i = st.pop()
    if i in dag: continue
    dag.add(i); st += [d for d in (SPEC.get(i) or {}).get('deps') or [] if d not in dag]
# an id with both a done and a superseded record was rebuilt in place: the superseded record is its earlier build (another tarball),
# the done record the rebuild; it is in (b) when the two records name different tarballs
rebuilt = {}
for i in sorted(set(listing) & superseded):
    s_ = objstore.get(B, P + '/superseded/%s.json' % i); d_ = objstore.get(B, P + '/done/%s.json' % i)
    if s_ and d_ and json.loads(s_[0]).get('sha256') != json.loads(d_[0]).get('sha256'): rebuilt[i] = (json.loads(s_[0]).get('superseded_reason') or '')[:120]
setb = {i for i in listing if i not in superseded or i in rebuilt}
outside = sorted(setb - dag)
repl = {}
for x in pk:
    for r in x.get('replaces') or []:
        if x['id'] in dag: repl.setdefault(r, x['id'])
why = {i: ('replaced by %s (its spec field "replaces"); no final-set package depends on it' % repl[i]) if i in repl else 'no final-set package depends on it' for i in outside}
open(os.path.join(H, 'V5_SETS.tsv'), 'w').write('# snapshot %s\n# set\tid\tnote\n' % SID + ''.join('outside\t%s\t%s\n' % (i, why[i]) for i in outside))
open(os.path.join(H, 'V5_SETS.tsv'), 'a').write(''.join('rebuilt\t%s\tdone record = the rebuild; the superseded record is its earlier build (%s)\n' % (i, r) for i, r in sorted(rebuilt.items())))
item('A0', dag <= setb and setb == set(listing), 'sets: (a) final set = R22K.Final\'s dependency DAG (%d producers of its %d top-store modules, closed under spec deps) = %d packages, %d of them done; '
     '(b) done, non-superseded records = %d (%d of them rebuilt in place: an earlier build of the id is superseded); (c) = (b) - (a) = %d (V5_SETS.tsv): %s' % (
     len(start), sum(1 for l in open(os.path.join(H, 'census', 'closure_classified.tsv')) if l.split('\t')[1] == 'store-PASS'), len(dag), len(dag & setb), len(setb), len(rebuilt), len(outside),
     '; '.join('%s: %s' % (i, why[i]) for i in outside[:3]) + (' ...' if len(outside) > 3 else '')))
missdep = sorted({d for g in gates if g['id'] not in parked for d in g.get('deps', []) if d not in listing})   # a parked (retired) gate line is not in the set
item('A1', not notdone and not missdep, 'package set: %d done, %d parked (superseded/retired), %d not done; gated deps not done: %d %s' % (
    len(listing), len(parked), len(notdone), len(missdep), missdep[:5]))
recs = {}
for l in open(KE.DONE_RECORDS):
    try: r = json.loads(l)
    except ValueError: continue
    if listing.get(r['id']) == r.get('_gen'): recs[r['id']] = r
# packages finalized by a worker version without the audit are re-audited offline with the worker's own code and the KMod library's
# kmod_audit.py (crosscheck.sh; REAUDIT_FILE lines: mine=PASS kmod_audit=PASS and the external walk std=3 bad=0)
re_ok = KE.reaudit_ok()
nopass = [i for i, r in recs.items() if (r.get('audit') or {}).get('result') != 'PASS' and i not in re_ok]
nopass_a = [i for i in nopass if i in dag]
item('A2', len(recs) == len(listing) and not nopass, 'audit PASS in %d of %d done records, set (b) (%d by the offline re-audit; %d records not cached); final set (a): PASS in %d of %d; without PASS: %d %s' % (
    len(recs) - len(nopass), len(listing), len(re_ok & set(recs)), len(listing) - len(recs), len(dag & set(recs)) - len(nopass_a), len(dag), len(nopass), nopass[:5]))
db = sqlite3.connect(KE.VERIFIER_DB, timeout=600)
ver = dict(db.execute('select pid, gen from packages').fetchall())
unver = [i for i, g in listing.items() if ver.get(i) != g]
pcounts = dict(db.execute('select kind, count(*) from problems group by kind').fetchall())
def kcount(*ks): return sum(pcounts.get(k, 0) for k in ks)
item('B1', not unver and kcount('INTEGRITY') == 0, 'integrity: %d done packages verified (%d not yet); INTEGRITY problems %d' % (len(listing) - len(unver), len(unver), kcount('INTEGRITY')))
item('B2', not unver and kcount('OWNHASH') == 0, 'own hashes: OWNHASH problems %d' % kcount('OWNHASH'))
conf = os.path.join(H, 'topstore', 'CONFLICTS.jsonl'); resf = os.path.join(H, 'topstore', 'CONFLICTS_RESOLVED.jsonl')
# a top-store NAME-CONFLICT counts unless resolved (resolve_conflicts.py: one package built twice, public parts identical) or its
# package is no longer done (superseded: its files were never installed over the store's copy, which belongs to the done producer)
resolved = {(json.loads(l)['pid'], json.loads(l)['file']) for l in open(resf)} if os.path.exists(resf) else set()
nconf = sum(1 for l in open(conf) if (json.loads(l)['pid'], json.loads(l)['file']) not in resolved and json.loads(l)['pid'] in listing) if os.path.exists(conf) else 0
item('B3', not unver and kcount('NAME-CONFLICT', 'ENV-SHADOW') == 0 and nconf == 0, 'one name one content: NAME-CONFLICT %d, ENV-SHADOW %d, top-store conflicts %d' % (
    kcount('NAME-CONFLICT'), kcount('ENV-SHADOW'), nconf))
mh = os.path.join(H, 'top', 'log', 'final_ext.txt')
item('B4', not unver and kcount('IMPORT-HASH', 'IMPORT-UNRESOLVED', 'ENV-MISSING', 'ENV-HASH') == 0, 'modhash gate: IMPORT-HASH %d, IMPORT-UNRESOLVED %d, ENV-MISSING %d, ENV-HASH %d' % (
    kcount('IMPORT-HASH'), kcount('IMPORT-UNRESOLVED'), kcount('ENV-MISSING'), kcount('ENV-HASH')))
ec = os.path.join(H, 'top', 'log', 'envcheck.txt')
item('B5', (('changed 0, added 0, removed 0' in open(ec).read()) if os.path.exists(ec) else None), open(ec).read().splitlines()[0] if os.path.exists(ec) else 'environment check not run yet (final.sh)')
tot = db.execute('select count(*) from obl').fetchone()[0]
try:
    wk = db.execute('select count(*) from walked').fetchone()[0]; wf = db.execute('select count(*) from walkfail').fetchone()[0]
except sqlite3.OperationalError: wk = wf = 0
std = set(); badb = 0
for f in glob.glob(os.path.join(H, 'walk', 'batches', '*.json')):
    r = json.load(open(f)); std |= set(r.get('std', []))
    if not r.get('ok') and not os.path.basename(f).startswith('final_test'): badb += 1
# entries of the union that no passed batch walked: an entry whose module has neither a current done producer (verifier.db produced)
# nor a file on the final LEAN_PATH came from a retired package's audit (no current package can import such a module: B4 has no
# IMPORT-UNRESOLVED), so it is outside the set (A1) and listed, not required
pend = db.execute('select o.module, o.const from obl o left join walked w on o.tier=w.tier and o.module=w.module and o.const=w.const where w.batch is null').fetchall()
LPR = open(os.path.join(H, 'lpath_final.txt')).read().strip().split(':')
def on_env(m): return any(os.path.exists(os.path.join(r, *m.split('.')) + '.olean') for r in LPR)
prodcur = {}
for m_, p_ in db.execute('select module, pid from produced'): prodcur[m_] = p_
stale = [(m_, c_) for m_, c_ in pend if not (m_ in prodcur and prodcur[m_] in listing) and not on_env(m_)]
open(os.path.join(H, 'walk', 'C1_excluded_retired.tsv'), 'w').write(''.join('%s\t%s\n' % x for x in stale))
item('C1', wk + len(stale) == tot and badb == 0 and not unver and std <= {'propext', 'Classical.choice', 'Quot.sound'},
     'external walk: %d of %d obligation entries walked, %d excluded (modules of retired packages only: no current producer, not on the final LEAN_PATH; walk/C1_excluded_retired.tsv); failed batches %d (recorded %d); EXT STD union %s' % (
    wk, tot, len(stale), badb, wf, sorted(std)))
au = os.path.join(H, 'top', 'log', 'audit.txt')
fe = open(mh).read() if os.path.exists(mh) else ''
fel = [l for l in fe.splitlines() if l.strip()]
item('C2', (os.path.exists(au) and open(au).read().strip().endswith('PASS') and fel[-1].endswith('-> PASS') if fel else None) if os.path.exists(au) else None,
     'kmod_audit --root R22K.Final: %s; external step: %s' % (open(au).read().strip().splitlines()[-1] if os.path.exists(au) else 'not run', ' | '.join(x[:160] for x in fel[-2:]) if fel else 'not run'))
ax = os.path.join(H, 'top', 'log', 'Axioms.log')
n = open(ax).read().count('depends on axioms: [propext, Classical.choice, Quot.sound]') if os.path.exists(ax) else 0
item('C3', (n == 5) if os.path.exists(ax) else None, '#print axioms: %d of 5 public theorems use exactly [propext, Classical.choice, Quot.sound]' % n)
item('C4', kcount('SUSPECT-NAME') == 0 and not unver, 'no sorryAx / ofReduceBool / trustCompiler: SUSPECT-NAME hits %d (C1-C3 also report any extra axiom)' % kcount('SUSPECT-NAME'))
lean = collections.Counter()
for r in recs.values():
    for it in ((r.get('provenance') or {}).get('closure') or []):
        if it.get('object', '').endswith(TCLOS): lean[it.get('sha256')] += 1
vals = {k for k in lean if k}
item('C5', len(vals) == 1, 'one kernel: %s (toolchain) sha256 over the done records with provenance: %s (records predating provenance: %d; the only toolchain closure published)' % (TCLOS, 
    {k[:16]: v for k, v in lean.items() if k}, lean.get(None, 0)))
fl = os.path.join(H, 'top', 'log', 'Final.lean.sha256')
item('D1', (True if os.path.exists(fl) else None), 'final instance: %s' % (open(fl).read().strip() if os.path.exists(fl) else 'not generated yet'))
open(os.path.join(H, 'V5_RESULT.txt'), 'w').write('%s V5 census, snapshot %s\n' % (time.strftime('%FT%TZ', time.gmtime()), SID) + '\n'.join(out) + '\n')
