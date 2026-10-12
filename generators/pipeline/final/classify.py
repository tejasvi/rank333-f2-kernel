#!/usr/bin/env python3
"""classify.py [--snapshot SNAPDIR]: every module of R22K.Final's exported import closure (FINAL_DIR/census/closure.txt, written by
Closure.lean with Lean's own loader) classified by where Lean resolves it (first LEAN_PATH root holding its top-level package dir, as
Lean does: FINAL_DIR/top/build, FINAL_DIR/topstore/store, then FINAL_DIR/lpath_final.txt) and, for top-store modules, by its
producing package (verifier db produced: module -> pid, olean sha256) and that package's audit (done record audit.result PASS, or
the offline re-audit, kitenv REAUDIT_FILE).  With --snapshot: the done list of that frozen snapshot (snapshot.py).  Writes
FINAL_DIR/census/closure_classified.tsv and CENSUS_SUMMARY.txt and prints the counts."""
import collections, hashlib, json, os, sqlite3, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'queue'))
import kitenv as KE
F = KE.FINAL; H = os.path.join(F, 'census')
roots = [os.path.join(F, 'top', 'build'), os.path.join(F, 'topstore', 'store')] + open(os.path.join(F, 'lpath_final.txt')).read().strip().split(':')
mods = [l.strip() for l in open(os.path.join(H, 'closure.txt')) if l.strip()]
def resolve(m):
    top = m.split('.')[0]
    for r in roots:
        if '.' not in m:      # a single-component module: its .olean sits at the root
            if os.path.exists(os.path.join(r, m + '.olean')): return r, os.path.join(r, m + '.olean')
            continue
        if os.path.isdir(os.path.join(r, top)): return r, os.path.join(r, *m.split('.')) + '.olean'
    return None, None
db = sqlite3.connect(KE.VERIFIER_DB, timeout=60)
done = {}
for l in open(KE.DONE_RECORDS):
    try: r = json.loads(l)
    except ValueError: continue
    done[r['id']] = r
re_ok = KE.reaudit_ok()
SNAP = sys.argv[sys.argv.index('--snapshot') + 1] if '--snapshot' in sys.argv else None
if SNAP:     # the frozen snapshot's done list (snapshot.py)
    SID = json.load(open(os.path.join(SNAP, 'SNAPSHOT.json')))['id']; listing = set(json.load(open(os.path.join(SNAP, 'done_ids.json'))))
else:
    SID = 'live'
    listing = set(json.load(open(os.path.join(H, 'done_listing.json')))) if os.path.exists(os.path.join(H, 'done_listing.json')) else None
c = collections.Counter(); out = []; unc = []
for m in mods:
    r, f = resolve(m)
    if r is None or not os.path.exists(f): c['UNRESOLVED'] += 1; unc.append((m, 'unresolved')); out.append((m, 'UNRESOLVED', '', '')); continue
    if r == roots[0]:
        c['final/top/build (R22K)'] += 1; out.append((m, 'top-build', r, '')); continue
    if r == roots[1]:
        sha = hashlib.sha256(open(f, 'rb').read()).hexdigest()
        pids = [p for (p, o) in db.execute('select pid, olean from produced where module = ?', (m,)) if o == sha]
        pids = [p for p in pids if p in done and (listing is None or p in listing)]
        if not pids: c['store: no current producer'] += 1; unc.append((m, 'no current producing package with this olean')); out.append((m, 'STORE-UNCOVERED', '', '')); continue
        ok = [p for p in pids if (done[p].get('audit') or {}).get('result') == 'PASS' or p in re_ok]
        if not ok: c['store: producer without audit PASS'] += 1; unc.append((m, 'producers %s without PASS' % pids[:3])); out.append((m, 'STORE-NOPASS', '', ' '.join(pids))); continue
        c['store: package audit PASS'] += 1; out.append((m, 'store-PASS', '', ok[0])); continue
    c['environment: ' + r.split('/lean/')[-1]] += 1; out.append((m, 'env', r, ''))
open(os.path.join(H, 'closure_classified.tsv'), 'w').write(''.join('\t'.join(x) + '\n' for x in out))
L = ['census of R22K.Final\'s exported import closure, snapshot %s (%s)' % (SID, __import__('time').strftime('%FT%TZ', __import__('time').gmtime())), 'closure modules %d' % len(mods)]
for k, v in sorted(c.items(), key=lambda kv: -kv[1]): L.append('  %-60s %d' % (k, v))
L.append('uncovered %d %s' % (len(unc), unc[:10]))
L.append('top-store producers (distinct packages): %d' % len({x[3] for x in out if x[1] == 'store-PASS'}))
open(os.path.join(H, 'CENSUS_SUMMARY.txt'), 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
