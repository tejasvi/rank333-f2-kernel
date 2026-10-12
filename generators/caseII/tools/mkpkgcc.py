#!/usr/bin/env python3
"""mkpkgcc.py JOBS OUTDIR STOREDIR [TARGET] [HEAVY]: case-II packages (CC route) for the worker, from py/mkjobscc.py's job table.

A package is a job list: OUTDIR/pkgs/<name>.tar.zst holds spec.json ({"prefix", "jobs": [[batch, idx, [labels…]], …], "jobfile",
"lines": [first, last]}) and emit.sh (`exec bash ${KINDS_BUNDLE:?set KINDS_BUNDLE}/emitcc.sh "$PWD"`). The worker extracts it,
runs emit.sh (generation, conversion and module emission on the build machine; nothing but the package's public oleans and kman leaves it),
then builds manifest.jsonl's units.
- Jobs over HEAVY estimated CC nodes (default 1.5e6) are packages of their own; the others are grouped in job-table order up to TARGET
  nodes (default 8e4) or 2,000 jobs.
- OUTDIR/PACKAGES.jsonl, one line per package: id (II.<name>), kind (heavy | normal), emit {type tarball, object STOREDIR/pkgs/<name>.tar.zst,
  manifest manifest.jsonl, then [./emit.sh]}, jobs, est_nodes, pred_s (0.35 s per node: the first package's unit wall per record on
  main, lazy conversion + elaboration + kernel), max_pred_gb (16: a lone 34 MB-segment item module), disk_gb (lazy conversion keeps
  only the segments, about 35 KB per node, plus 30% and 10 GB), emit_gb (64: helpers at about 4 GB each), deps [], tier caseII, jobfile + lines (the job table's line range) for
  reproducibility.
Prints the package count and sizes; the tarballs are written but not uploaded. Env PKG_PREFIX (default KM2P): the packages' name prefix
(KM2X for the sub-jobs of runs/p0x's expanded jobs)."""
import sys, os, json, io, tarfile, hashlib
jobs_f, out, store = sys.argv[1], sys.argv[2], sys.argv[3].rstrip('/')
TARGET = float(sys.argv[4]) if len(sys.argv) > 4 else 8e4; HEAVY = float(sys.argv[5]) if len(sys.argv) > 5 else 1.5e6
os.makedirs(out + '/pkgs', exist_ok=True)
J = []
for n, l in enumerate(open(jobs_f), 1):
    a = l.split()
    if a: J.append((n, a[0], int(a[1]), int(a[3]), [int(x) for x in a[4:]]))
pk = []; cur = []; cs = 0
def flush():
    global cur, cs
    if cur: pk.append(('normal', cur)); cur = []; cs = 0
for j in J:
    if j[3] > HEAVY: pk.append(('heavy', [j])); continue
    if cur and (cs + j[3] > TARGET or len(cur) >= 2000): flush()
    cur.append(j); cs += j[3]
flush()
EMIT = '#!/bin/bash\n# emit.sh: case-II package emission (the worker `then` step): the bundle\'s emitcc.sh in this package dir\nexec bash ${KINDS_BUNDLE:?set KINDS_BUNDLE}/emitcc.sh "$PWD"\n'
lines = []
for k, (kind, js) in enumerate(pk):
    name = '%s%06d' % (os.environ.get('PKG_PREFIX', 'KM2P'), k)
    spec = dict(prefix=name, jobfile=os.path.basename(jobs_f), lines=[js[0][0], js[-1][0]], jobs=[[b, i, pre] for _, b, i, _, pre in js])
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode='w') as t:
        for fn, data, mode in (('spec.json', json.dumps(spec).encode(), 0o644), ('emit.sh', EMIT.encode(), 0o755)):
            ti = tarfile.TarInfo(fn); ti.size = len(data); ti.mode = mode; ti.mtime = 1791500000; t.addfile(ti, io.BytesIO(data))
    raw = buf.getvalue()
    path = '%s/pkgs/%s.tar' % (out, name); open(path, 'wb').write(raw)
    est = sum(j[3] for j in js)
    lines.append(dict(id='II.%s' % name, kind=kind, emit=dict(type='tarball', object='%s/pkgs/%s.tar' % (store, name), manifest='manifest.jsonl',
                      then=['./emit.sh']), sha256=hashlib.sha256(raw).hexdigest(), jobs=len(js), est_nodes=est,
                      pred_s=round(0.35 * est, 1), max_pred_gb=16.0, disk_gb=round(est * 35e3 * 1.3 / 1e9 + 10, 1), emit_gb=64,
                      deps=[], tier='caseII', jobfile=spec['jobfile'], lines=spec['lines']))
open(out + '/PACKAGES.jsonl', 'w').write(''.join(json.dumps(x) + '\n' for x in lines))
h = [x for x in lines if x['kind'] == 'heavy']; nm = [x for x in lines if x['kind'] == 'normal']
print('%d packages: %d heavy (est %.3g nodes, disk_gb max %.0f), %d normal (est %.3g nodes); pred_s total %.3g; disk_gb max normal %.0f' % (
    len(lines), len(h), sum(x['est_nodes'] for x in h), max([x['disk_gb'] for x in h] or [0]), len(nm), sum(x['est_nodes'] for x in nm),
    sum(x['pred_s'] for x in lines), max([x['disk_gb'] for x in nm] or [0])))
