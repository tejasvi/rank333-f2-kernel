#!/usr/bin/env python3
"""mkjoinpkg.py JOINOUT PACKAGES OUTDIR STOREDIR: case-II join (py/joinemit.py's OUT after the bundle's mkpkgw.py) as two packages
for the worker, both pre-emitted tarballs (no `then` step):
- II.JOINI: the item modules KM2.I* (each converts its phase-0 segments at unit time, py/unitconv.py), with the 61 pcerts p0/seg_*.r3
  and phase 0's records; no deps. Its public roots are all item modules (no "pub" row), so its pubs object holds them all.
- II.JOIN: the Cov chunks KM2.A* (their specs refer to the packages' `<pkg>.Top.cov` by index, src/pkgs.exports) and the top KM2.Top
  ("pub" KM2.Top.segs : AllL SegsOfKeyCC [1]); deps II.JOINI and every case-II package of PACKAGES, "deps_pubs": true.
pred_gb: item units x JGB_SCALE (default 1.15: KM2.I3 peaked at 17.96 GB RssAnon on the build machine against 16.2 predicted); chunks and top
JAGG_GB (default 4.0: they import up to a few thousand package tops). Writes OUTDIR/pkgs/{JOINI,JOIN}.tar (sorted, fixed mtime) and
OUTDIR/PACKAGES.jsonl; nothing is uploaded. Env JNAME (default JOIN): the packages are II.<JNAME>I and II.<JNAME> (JOIN2 after the
giant jobs' expansion, runs/p0x). PACKAGES may be a comma-separated list of package lists. JITEMS / JSKIPI=1: ship only the chunk
package, over an item package already built (II.JOIN4B over II.JOIN4I, level-ordered chunks)."""
import sys, os, json, tarfile, hashlib, glob
J, pk_f, out, store = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4].rstrip('/')
SC = float(os.environ.get('JGB_SCALE', '1.15')); AGB = float(os.environ.get('JAGG_GB', '4.0'))
os.makedirs(out + '/pkgs', exist_ok=True)
man = [json.loads(l) for l in open(J + '/manifest.jsonl')]
items = [m for m in man if m['module'].startswith('KM2.I')]; rest = [m for m in man if not m['module'].startswith('KM2.I')]
assert len(items) + len(rest) == len(man) and any(m['module'] == 'KM2.Top' and m.get('pub') == 'KM2.Top.segs' for m in rest)
for m in items: m['pred_gb'] = round(m['pred_gb'] * SC, 2)
for m in rest: m['pred_gb'] = AGB; m['deps'] = [d for d in m['deps'] if not d.startswith('KM2.I')]
for m in items: m['wave'] = 0
common = ['kmod_unit.sh', 'lpath_common.txt', 'emit.json', 'join.json'] + sorted(os.path.relpath(p, J) for p in glob.glob(J + '/tools/*'))
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''): h.update(b)
    return h.hexdigest()
def mktar(name, files, rows):
    mf = '%s/pkgs/%s.manifest.jsonl' % (out, name); open(mf, 'w').write(''.join(json.dumps(r) + '\n' for r in rows))
    path = '%s/pkgs/%s.tar' % (out, name)
    with tarfile.open(path, 'w', format=tarfile.GNU_FORMAT) as t:
        def add(src, arc):
            ti = t.gettarinfo(src, arc); ti.mtime = 1791500000; ti.uid = ti.gid = 0; ti.uname = ti.gname = ''
            with open(src, 'rb') as f: t.addfile(ti, f)
        add(mf, 'manifest.jsonl')
        for f in sorted(set(files)): add(os.path.join(J, f), f)
    return path
fi = common + sorted(os.path.relpath(p, J) for p in glob.glob(J + '/src/KM2/I*.lean') + glob.glob(J + '/src/KM2/I*.items')) + \
     sorted(os.path.relpath(p, J) for p in glob.glob(J + '/p0/seg_*.r3')) + [x for x in ('p0/recipecheck.txt', 'p0/check.txt', 'p0/SHA256SUMS.txt', 'p0/batches.tsv') if os.path.exists(J + '/' + x)]
fa = common + sorted(os.path.relpath(p, J) for p in glob.glob(J + '/src/KM2/A*.lean') + glob.glob(J + '/src/KM2/A*.spec')) + ['src/KM2/Top.lean', 'src/pkgs.exports']
ids = [json.loads(l)['id'] for f in pk_f.split(',') for l in open(f) if l.strip()]
JN = os.environ.get('JNAME', 'JOIN')
JI = os.environ.get('JITEMS', 'II.%sI' % JN)   # the item package the chunks build on (JITEMS=II.JOIN4I: a re-chunked join over built items)
SKIPI = os.environ.get('JSKIPI') == '1'        # do not write the item package again
lines = []
for name, files, rows, deps, extra in ([] if SKIPI else [(JN + 'I', fi, items, [], {})]) + [(JN, fa, rest, [JI] + ids, {'deps_pubs': True})]:
    p = mktar(name, files, rows); sz = os.path.getsize(p)
    ln = dict(id='II.%s' % name, kind='normal', emit=dict(type='tarball', object='%s/pkgs/%s.tar' % (store, name), manifest='manifest.jsonl'),
              sha256=sha(p), units=len(rows), records=sum(r.get('records', 0) for r in rows), pred_s=round(sum(r['pred_s'] for r in rows), 1),
              max_pred_gb=max(r['pred_gb'] for r in rows), disk_gb=round(2.2 * sz / 1e9 + 40, 1), deps=deps, tier='caseII')
    ln.update(extra); lines.append(ln)
    print('%s: %d units, %d records, pred_s %.0f, max pred_gb %.2f, tar %.2f GB, %d deps' % (ln['id'], ln['units'], ln['records'], ln['pred_s'], ln['max_pred_gb'], sz / 1e9, len(deps)))
open(out + '/PACKAGES.jsonl', 'w').write(''.join(json.dumps(x) + '\n' for x in lines))
