#!/usr/bin/env python3
"""final_ext.py OBLFILE [--tag NAME] [--par 8]: the external step of the final audit (V5 C1/C2) for the obligations that
`kmod_audit.py --no-ext --obl-out OBLFILE` left over (`<module> <constant>` per line), with walk.py's batch runner:
  * a module on the final LEAN_PATH: KModExt at the private level, LEAN_PATH = FINAL_DIR/lpath_final.txt (batches of <= 150 modules);
  * a module produced by a done package: resolved through that package's manifest (.kman: the constant is a KPUB theorem, or an
    .EXT occurring in a KPUB statement, KModTyChk) or, for a data table, walked by KModExt over the producer's extracted tarball;
  * any other module: an error.
Obligations the union walk already walked in a passed batch are reused (listed with their batch in FINAL_DIR/walk/final_<tag>_reused.tsv).
Batch records in FINAL_DIR/walk/batches/final_<tag>_*.json; prints one PASS/FAIL line; exit 0 iff every batch passed."""
import collections, json, os, sqlite3, sys
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue')); sys.path.insert(0, os.path.join(K_, 'final'))
a = sys.argv[1:]
import walk, objstore, kitenv as KE
H = KE.FINAL
obl = sorted({tuple(l.split()[:2]) for l in open(a[0]) if len(l.split()) >= 2})
tag = a[a.index('--tag') + 1] if '--tag' in a else 'top'
ENV = walk.env_names()
db = sqlite3.connect(KE.VERIFIER_DB, timeout=600)
# obligations the union walk (walk.py) already walked in a PASSED batch (table walked: inserted only for ok batches) are reused:
# the same (module, constant) walked by the same KModExt over the same environment; only the rest is walked here
walked = {}
for m_, c_, b_ in db.execute('select module, const, batch from walked'): walked[(m_, c_)] = b_
reused = [k for k in obl if k in walked]
obl = [k for k in obl if k not in walked]
print('final_ext: %d obligations already walked by the union walk in passed batches (reused), %d to walk now' % (len(reused), len(obl)), flush=True)
open(os.path.join(H, 'walk', 'final_%s_reused.tsv' % tag), 'w').write(''.join('%s\t%s\t%s\n' % (m_, c_, walked[(m_, c_)]) for m_, c_ in reused))
mods = {m for m, _ in obl}
prod = {m: pid for m, pid in db.execute('select module, pid from produced') if m in mods}
env = [k for k in obl if k[0] in ENV and k[0] not in prod]
store = collections.defaultdict(list); unknown = []
for k in obl:
    if k[0] in prod: store[prod[k[0]]].append(k)
    elif k[0] not in ENV: unknown.append(k)
jobs = []; cur = []; ms = set()
for k in env:
    if k[0] not in ms and len(ms) >= 150: jobs.append(('final_%s_env%03d' % (tag, len(jobs)), cur, [])); cur, ms = [], set()
    cur.append(k); ms.add(k[0])
if cur: jobs.append(('final_%s_env%03d' % (tag, len(jobs)), cur, []))
pids = sorted(store)
for i in range(0, len(pids), 100):
    grp = []
    for pid in pids[i:i + 100]:
        d = json.loads(objstore.get(walk.B, walk.P + '/done/%s.json' % pid)[0]); grp.append((pid, d['object'], d['sha256']))
    jobs.append(('final_%s_store%03d' % (tag, len(jobs)), [k for p, _, _ in grp for k in store[p]], grp))
import concurrent.futures as cf
par = int(a[a.index('--par') + 1]) if '--par' in a else 8
with cf.ThreadPoolExecutor(par) as ex: res = list(ex.map(lambda j: walk.run_batch(*j), jobs))
bad = [r for r in res if not r.get('ok')]
std = sorted({s for r in res for s in r.get('std', [])})
print('%s: %d external obligations (%d env, %d store in %d packages, %d unknown); %d batches, %d failed; manifest-resolved %d, tycheck %d, walked %d; std %s -> %s' % (
    tag, len(obl), len(env), sum(len(v) for v in store.values()), len(store), len(unknown), len(res), len(bad),
    sum(r.get('manifest', 0) for r in res), sum(r.get('tycheck', 0) for r in res), sum(r.get('walked', 0) for r in res), std,
    'PASS' if not bad and not unknown and set(std) <= walk.STD else 'FAIL'))
for r in bad[:10]: print('  FAILED', r['batch'], json.dumps({k: r.get(k) for k in ('rc', 'extsum', 'bad', 'errors', 'error')})[:400])
for k in unknown[:10]: print('  UNKNOWN module', k)
sys.exit(0 if not bad and not unknown and set(std) <= walk.STD else 1)
