#!/usr/bin/env python3
"""backfill_pubs.py [--dry]: the pubs object for done packages finalized by a worker version that wrote none, so that dependents
fetching "deps_pubs" find their root modules.  Per such package: its result tarball (sha256 = the done record) gives the manifest
(roots = modules marked "pub", else every module with a .kman: finalize's own rule) and the root files; the pubs tar (roots'
.olean/.ilean/.kman/.mhash/.olean.server + emit/DONE, emit/kext.txt + SHA256SUMS) is uploaded to PREFIX/pubs/<shard>/<tag>.<box>.tar
and the done record gains pubs_object/pubs_sha256/pubs_size and, when it has none, audit.roots with result PASS and its source: the
offline re-audit (kitenv REAUDIT_FILE, written by crosscheck.sh: the worker's audit code and the KMod library's kmod_audit.py c7594ac1,
external walk std=3 bad=0).
The done record is rewritten generation-checked; "backfill" records what was added and when."""
import hashlib, io, json, os, subprocess, sys, tarfile, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
dry = '--dry' in sys.argv
re_ok = {l.split()[0]: l.strip() for l in (open(KE.REAUDIT) if os.path.exists(KE.REAUDIT) else []) if 'mine=PASS kmod_audit=PASS' in l and ' bad=0' in l}
# candidates from the verifier's record cache (every done record, current generation): those without a pubs object; each is then
# re-read from the store (content + generation) before anything is written
listing = {it['name'].rsplit('/', 1)[1][:-5]: str(it['generation']) for it in objstore.ls(B, P + '/done/', fields='name,generation') if it['name'].endswith('.json')}
todo = set()
for l in open(KE.DONE_RECORDS):
    try: r = json.loads(l)
    except ValueError: continue
    # only records the deps_pubs path cannot serve: no pubs object AND no audit roots (with roots, the worker falls back to the full
    # tarball and extracts the roots' files)
    if r['id'] in listing and not r.get('pubs_object') and not (r.get('audit') or {}).get('roots'): todo.add(r['id'])
todo = sorted(todo)
def need(pid):
    g = objstore.get(B, P + '/done/%s.json' % pid)
    if not g: return None
    d = json.loads(g[0])
    return (pid, d, g[1]) if not d.get('pubs_object') else None
import concurrent.futures as cf
with cf.ThreadPoolExecutor(64) as ex: cand = [x for x in ex.map(need, todo) if x]
print('done records without a pubs object:', len(cand), [c[0] for c in cand[:10]])
n = 0
for pid, d, gen in cand:
    raw = objstore.fetch(B, d['object'])
    if hashlib.sha256(raw).hexdigest() != d['sha256']: print(pid, 'tarball sha256 differs: skipped'); continue
    tf = tarfile.open(fileobj=io.BytesIO(subprocess.run(['zstd', '-dc'], input=raw, capture_output=True, check=True).stdout))
    names = {m.name: m for m in tf.getmembers() if m.isfile()}
    man = [json.loads(l) for l in tf.extractfile('manifest.jsonl').read().decode().splitlines() if l.strip()]
    mods = [m['module'] for m in man]
    roots = [m['module'] for m in man if m.get('pub')]
    if not roots: print(pid, 'manifest has no pub rows: skipped (not backfilled)'); continue
    files = {}
    for r in roots:
        for x in ('.olean', '.ilean', '.kman', '.mhash', '.olean.server'):
            a = 'store/' + r.replace('.', '/') + x
            if a in names: files[a] = tf.extractfile(names[a]).read()
    for x in ('emit/DONE', 'emit/kext.txt'):
        if x in names: files[x] = tf.extractfile(names[x]).read()
    if not any(f.endswith('.olean') for f in files): print(pid, 'no root .olean found: skipped', roots[:3]); continue
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode='w') as out:
        sums = ''.join('%s  %s\n' % (hashlib.sha256(b).hexdigest(), a) for a, b in sorted(files.items()) if a.startswith('store/'))
        for a, b in list(sorted(files.items())) + [('SHA256SUMS', sums.encode())]:
            ti = tarfile.TarInfo(a); ti.size = len(b); ti.mtime = int(time.time()); out.addfile(ti, io.BytesIO(b))
    pt = buf.getvalue(); psha = hashlib.sha256(pt).hexdigest()
    tag_box = d['object'].rsplit('/', 1)[1][:-len('.tar.zst')]
    pname = '%s/pubs/%s/%s.tar' % (P, d['object'].split('/')[-2], tag_box)
    add = dict(pubs_object=pname, pubs_sha256=psha, pubs_size=len(pt))
    if not d.get('audit'):
        if pid not in re_ok: print(pid, 'no audit and not in the offline re-audit: pubs only');
        else: add['audit'] = dict(roots=roots, result='PASS', source='offline re-audit: ' + re_ok[pid][:200])
    print(pid, 'roots', len(roots), 'pubs', len(pt), 'bytes ->', pname, '(audit backfilled)' if 'audit' in add else '')
    if dry: continue
    objstore.put(B, pname, pt)
    st = objstore.stat(B, pname)
    if not st or int(st['size']) != len(pt): print(pid, 'pubs upload verification failed'); continue
    objstore.put(B, P + '/done_orig/%s.json' % pid, json.dumps(d))      # the original record, kept beside
    d.update(add); d['backfill'] = dict(t=time.time(), date=time.strftime('%FT%TZ', time.gmtime()), added=sorted(add), source_tarball=d['object'],
                                        source_tarball_sha256=d['sha256'], reaudit=re_ok.get(pid), original=P + '/done_orig/%s.json' % pid,
                                        by='native/infra/phaseb/final/backfill_pubs.py')
    try: objstore.put(B, P + '/done/%s.json' % pid, json.dumps(d), if_generation=gen); n += 1
    except objstore.Precondition: print(pid, 'done record changed meanwhile: not updated')
print('backfilled %d of %d' % (n, len(cand)))
