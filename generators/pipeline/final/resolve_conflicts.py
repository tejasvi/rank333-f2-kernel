#!/usr/bin/env python3
"""resolve_conflicts.py [--dry]: resolve top-store NAME-CONFLICTs (FINAL_DIR/topstore/CONFLICTS.jsonl) caused by ONE package built
twice (its lease expired on a loaded worker while that worker was still building; the second build's done record replaced the first,
and the top store had installed the first build's files): for each conflicting file of a package that is still done, if every
.olean / .ilean / .olean.server the package's CURRENT pubs object ships is byte-identical to the store's copy (same public modules), the
store's differing file (.kman / .mhash: timing lines and the private part's KSHA) is replaced by the current pubs' version and added
to the package's top-store record; anything else is left alone and reported.  Log: FINAL_DIR/topstore/CONFLICTS_RESOLVED.jsonl."""
import hashlib, io, json, os, sys, tarfile, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = KE.FINAL
T = os.path.join(H, 'topstore'); dry = '--dry' in sys.argv
sha = lambda b: hashlib.sha256(b).hexdigest()
done_res = set()
if os.path.exists(os.path.join(T, 'CONFLICTS_RESOLVED.jsonl')):
    for l in open(os.path.join(T, 'CONFLICTS_RESOLVED.jsonl')):
        d = json.loads(l); done_res.add((d['pid'], d['file']))
by = {}
for l in open(os.path.join(T, 'CONFLICTS.jsonl')):
    d = json.loads(l)
    if (d['pid'], d['file']) not in done_res: by.setdefault(d['pid'], set()).add(d['file'])
for pid, files in sorted(by.items()):
    g = objstore.get(B, P + '/done/%s.json' % pid)
    if not g: print(pid, 'no done record (superseded?): left alone'); continue
    rec = json.loads(g[0])
    if not rec.get('pubs_object'): print(pid, 'no pubs object: left alone'); continue
    raw = objstore.fetch(B, rec['pubs_object'])
    if sha(raw) != rec.get('pubs_sha256'): print(pid, 'pubs sha256 differs from the done record: left alone'); continue
    tf = tarfile.open(fileobj=io.BytesIO(raw)); M = {m.name: tf.extractfile(m).read() for m in tf.getmembers() if m.isfile()}
    pub = [f for f in M if f.startswith('store/') and (f.endswith('.olean') or f.endswith('.ilean') or f.endswith('.olean.server'))]
    same = all(os.path.exists(os.path.join(T, f)) and open(os.path.join(T, f), 'rb').read() == M[f] for f in pub)
    if not pub or not same: print(pid, 'public modules differ from the store (or none): left alone', len(pub)); continue
    recf = os.path.join(T, 'pkgs', pid + '.json'); trec = json.load(open(recf)) if os.path.exists(recf) else dict(files={})
    if not isinstance(trec.get('files'), dict): print(pid, 'top-store record files is not a {path: sha256} map: left alone'); continue
    for f in sorted(files):
        if f not in M: print(pid, f, 'not in the current pubs: left alone'); continue
        old = open(os.path.join(T, f), 'rb').read() if os.path.exists(os.path.join(T, f)) else b''
        ent = dict(pid=pid, file=f, t=time.time(), date=time.strftime('%FT%TZ', time.gmtime()), old_sha256=sha(old), new_sha256=sha(M[f]),
                   pubs_object=rec['pubs_object'], done_box=rec.get('box'), reason='one package built twice (lease expired on a loaded worker); '
                   'public .olean/.ilean/.olean.server byte-identical; .kman/.mhash differ in timing lines and the private part\'s KSHA; '
                   'the store now holds the current done record\'s file')
        print(('DRY ' if dry else '') + 'resolve', pid, f, ent['old_sha256'][:12], '->', ent['new_sha256'][:12])
        if dry: continue
        p = os.path.join(T, f); open(p + '.res', 'wb').write(M[f]); os.replace(p + '.res', p)
        trec['files'][f] = sha(M[f])        # topstore.py's record: {path relative to the top store: sha256}
        with open(os.path.join(T, 'CONFLICTS_RESOLVED.jsonl'), 'a') as o: o.write(json.dumps(ent) + '\n')
    if not dry: json.dump(trec, open(recf + '.tmp', 'w')); os.replace(recf + '.tmp', recf)
