#!/usr/bin/env python3
"""snapshot.py [--check SNAPDIR]: freeze the queue's final state into FINAL_DIR/snap/<id>/ for the census runs (v5.py, classify.py,
report and sample census with --snapshot), so that every count comes from one state.
  done_listing.tsv   id <TAB> generation of every done record (done/<id>.json)
  superseded.txt     ids with a superseded/ record;  parked.txt  ids with a parked/ marker
  packages.jsonl     the spec lines (one generation);  gates.jsonl  the gate lines (GATES_FILE: local files and stored gate files)
  done_ids.json      sorted done ids (the form report_extra and classify read)
  SNAPSHOT.json      the id (snap-<UTC time>-<12 hex of the files' hashes>), the time, and sha256 of every file above plus the verifier db
--check SNAPDIR: list again and compare with SNAPDIR (records the result in SNAPDIR/CHECK.txt): the state must be unchanged."""
import hashlib, json, os, sys, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = KE.FINAL
def sha(b): return hashlib.sha256(b).hexdigest()
def state():
    listing = {it['name'].rsplit('/', 1)[1][:-5]: str(it['generation']) for it in objstore.ls(B, P + '/done/', fields='name,generation') if it['name'].endswith('.json')}
    sup = sorted(it['name'].rsplit('/', 1)[1][:-5] for it in objstore.ls(B, P + '/superseded/', fields='name') if it['name'].endswith('.json'))
    parked = sorted(it['name'].rsplit('/', 1)[1] for it in objstore.ls(B, P + '/parked/', fields='name'))
    pkb, pkg = objstore.get(B, P + '/packages.jsonl')
    gates = []
    for f in KE.gate_files():
        if f.startswith('//'):
            gb, go = f[2:].split('/', 1); g = objstore.get(gb, go)
            gates += [l for l in (g[0].decode().splitlines() if g else []) if l.strip()]
        else:
            gates += [l.rstrip('\n') for l in open(f) if l.strip()]
    return listing, sup, parked, pkb, pkg, gates
if '--check' in sys.argv:
    d = sys.argv[sys.argv.index('--check') + 1]
    listing, sup, parked, pkb, pkg, gates = state()
    S = json.load(open(os.path.join(d, 'SNAPSHOT.json')))
    old = dict(l.rstrip('\n').split('\t') for l in open(os.path.join(d, 'done_listing.tsv')))
    diffs = []
    if old != listing: diffs.append('done listing differs: %d added, %d removed, %d regenerated' % (
        len(set(listing) - set(old)), len(set(old) - set(listing)), sum(1 for i in set(old) & set(listing) if old[i] != listing[i])))
    if sha(pkb) != S['files']['packages.jsonl']: diffs.append('packages.jsonl differs')
    if sorted(sup) != [l.strip() for l in open(os.path.join(d, 'superseded.txt')) if l.strip()]: diffs.append('superseded/ differs')
    if sorted(parked) != [l.strip() for l in open(os.path.join(d, 'parked.txt')) if l.strip()]: diffs.append('parked/ differs')
    if sha(('\n'.join(gates) + '\n').encode()) != S['files']['gates.jsonl']: diffs.append('gates differ')
    msg = '%s check of %s: %s' % (time.strftime('%FT%TZ', time.gmtime()), S['id'], 'UNCHANGED' if not diffs else 'CHANGED: ' + '; '.join(diffs))
    open(os.path.join(d, 'CHECK.txt'), 'a').write(msg + '\n'); print(msg); sys.exit(0 if not diffs else 1)
t = time.gmtime()
listing, sup, parked, pkb, pkg, gates = state()
files = {}
blobs = {'done_listing.tsv': ''.join('%s\t%s\n' % (i, listing[i]) for i in sorted(listing)).encode(),
         'superseded.txt': ''.join(i + '\n' for i in sup).encode(), 'parked.txt': ''.join(i + '\n' for i in parked).encode(),
         'packages.jsonl': pkb, 'gates.jsonl': ('\n'.join(gates) + '\n').encode(), 'done_ids.json': json.dumps(sorted(listing)).encode()}
for k, b in blobs.items(): files[k] = sha(b)
h = hashlib.sha256()
with open(KE.VERIFIER_DB, 'rb') as f:
    for c in iter(lambda: f.read(1 << 24), b''): h.update(c)
files['verifier.db'] = h.hexdigest()
sid = 'snap-%s-%s' % (time.strftime('%Y%m%dT%H%MZ', t), sha(json.dumps(files, sort_keys=True).encode())[:12])
d = os.path.join(H, 'snap', sid); os.makedirs(d, exist_ok=True)
for k, b in blobs.items(): open(os.path.join(d, k), 'wb').write(b)
S = dict(id=sid, time=time.strftime('%FT%TZ', t), done=len(listing), superseded=len(sup), parked=len(parked), packages_jsonl_generation=pkg,
         spec_lines=sum(1 for l in pkb.decode().splitlines() if l.strip()), gate_lines=len(gates), files=files)
json.dump(S, open(os.path.join(d, 'SNAPSHOT.json'), 'w'), indent=1)
open(os.path.join(H, 'snap', 'CURRENT'), 'w').write(sid + '\n')
print(json.dumps(S, indent=1))
