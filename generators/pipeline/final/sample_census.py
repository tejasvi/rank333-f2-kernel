#!/usr/bin/env python3
"""sample_census.py [--snapshot SNAPDIR] [--tsv FILE]: the F1 private-sample census over FINAL_DIR/recheck/sample_check.jsonl (all
runs) and sample_overlay.jsonl (the harness cases checked again with a merged root).  Classes: PASS (leanchecker rc 0 and the sample's sha256 = the build's KMH private hash); FAIL (a kernel or
elaboration error, or a hash mismatch); not checkable by policy ("missing data file for module": an import-all sibling's private part
deleted by the KMod policy); not checkable by the harness (scratch-store package-dir shadowing not resolved by the overlay); skipped
(package superseded).  The latest row per sample object wins (the overlay row over the first run's).  With --snapshot, every sample is
also placed in a set of that frozen snapshot: the final set (R22K.Final's dependency DAG), done outside it, or not done (superseded);
--tsv FILE writes the per-sample results (package, module, set, class, sample and build private sha256: names and hashes only)."""
import collections, json, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'queue'))
import kitenv as KE
H = os.path.join(KE.FINAL, 'recheck')
rows = {}
for f in ('sample_check.jsonl', 'sample_overlay.jsonl'):
    p = os.path.join(H, f)
    if not os.path.exists(p): continue
    for l in open(p):
        try: r = json.loads(l)
        except Exception: continue
        if r.get('object'): rows[r['object']] = r
def tier(p):
    for a, b in (('II.', 'case II'), ('ext_c4', 'EXT giant'), ('ext_', 'EXT'), ('kcagg', 'class aggregation'), ('kc', 'classes'),
                 ('agg_ext', 'EXT tops'), ('agg', 'e1g aggregation'), ('pt_', 'point'), ('I13', 'case I13'), ('I.', 'case I'), ('w1_', 'c436/c422/held')):
        if p.startswith(a): return b
    return 'other'
def cls(r):
    t = (r.get('tail') or '') + ' ' + (r.get('note') or '')
    if 'superseded' in t and r.get('ok') is None: return 'skipped (superseded)'
    if r.get('kmh_match') is False and r.get('rc') is not None: return 'FAIL (hash mismatch)'
    if r.get('rc') == 0 and r.get('kmh_match'): return 'PASS'
    if 'missing data file for module' in t: return 'not checkable (policy)'
    if 'object file' in t and 'does not exist' in t: return 'not checkable (harness)'
    return 'FAIL'
import sys
SNAP = sys.argv[sys.argv.index('--snapshot') + 1] if '--snapshot' in sys.argv else None
SID = 'live'; setof = lambda p: 'all'
if SNAP:     # the frozen snapshot (snapshot.py): (a) the final set, (b) - (a) outside it, and packages no longer done
    SID = json.load(open(os.path.join(SNAP, 'SNAPSHOT.json')))['id']
    done = set(json.load(open(os.path.join(SNAP, 'done_ids.json'))))
    spec = {json.loads(l)['id']: json.loads(l) for l in open(os.path.join(SNAP, 'packages.jsonl')) if l.strip()}
    F = os.path.dirname(H)
    st = [l.rstrip('\n').split('\t')[3] for l in open(os.path.join(F, 'census', 'closure_classified.tsv')) if l.split('\t')[1] == 'store-PASS']
    dag = set()
    while st:
        i = st.pop()
        if i in dag: continue
        dag.add(i); st += [d for d in (spec.get(i) or {}).get('deps') or [] if d not in dag]
    setof = lambda p: 'final set' if p in dag else ('done, outside the final set' if p in done else 'not done (superseded)')
C = collections.Counter(); T = collections.defaultdict(collections.Counter); S = collections.defaultdict(collections.Counter); fails = []; odd = []
for o, r in rows.items():
    c = cls(r); C[c] += 1; T[tier(r.get('pkg', ''))][c] += 1; s_ = setof(r.get('pkg', '')); S[s_][c] += 1
    if c.startswith('FAIL'): fails.append((r.get('module'), (r.get('tail') or r.get('note') or '')[-160:]))
    if s_ != 'not done (superseded)' and c == 'skipped (superseded)': odd.append((r.get('pkg'), r.get('module')))
out = ['F1 private-sample census (corrected classes, %d samples), snapshot %s: %s' % (len(rows), SID, ', '.join('%s %d' % kv for kv in sorted(C.items())))]
for t in sorted(T): out.append('  %-20s %s' % (t, ', '.join('%s %d' % kv for kv in sorted(T[t].items()))))
if SNAP:
    out.append('  by set:')
    for t in sorted(S): out.append('    %-28s %s' % (t, ', '.join('%s %d' % kv for kv in sorted(S[t].items()))))
    out.append('  samples of done packages that the run skipped as superseded: %d %s' % (len(odd), odd[:5]))
if fails: out.append('  FAIL rows: %s' % fails[:10])
print('\n'.join(out))
if '--tsv' in sys.argv:      # per-sample results, names and hashes only
    with open(sys.argv[sys.argv.index('--tsv') + 1], 'w') as f:
        f.write('# snapshot %s\n# package\tmodule\tset\tclass\tsample_private_sha256\tbuild_private_sha256\n' % SID)
        for o, r in sorted(rows.items(), key=lambda kv: (kv[1].get('pkg', ''), kv[0])):
            mod = r.get('module') or o.rsplit('/', 1)[-1][:-len('.olean.private')]
            f.write('%s\t%s\t%s\t%s\t%s\t%s\n' % (r.get('pkg', ''), mod, setof(r.get('pkg', '')), cls(r), r.get('private_sha') or '', r.get('kmh_private') or ''))
