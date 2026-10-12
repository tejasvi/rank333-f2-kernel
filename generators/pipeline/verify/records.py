#!/usr/bin/env python3
"""records.py [--par 64]: every done record of the queue (PREFIX/done/*.json), minus "spec"/"kext_lines", into
SCAN_DIR/done_records.jsonl (incremental: ids already in the file are not read again; a record whose object changed is re-read when
the listing's generation differs).  Prints counts and total tarball/pubs bytes."""
import concurrent.futures as cf, json, os, sys, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = KE.SCAN; os.makedirs(H, exist_ok=True)
OUT = os.path.join(H, 'done_records.jsonl')
par = int(sys.argv[sys.argv.index('--par') + 1]) if '--par' in sys.argv else 64
have = {}
if os.path.exists(OUT):
    for l in open(OUT):
        try: r = json.loads(l); have[r['id']] = r
        except ValueError: pass
listing = {it['name'].rsplit('/', 1)[1][:-len('.json')]: it['generation'] for it in objstore.ls(B, P + '/done/') if it['name'].endswith('.json')}
todo = [i for i, g in listing.items() if i not in have or have[i].get('_gen') != g]
def rd(i):
    for t in range(4):
        try:
            g = objstore.get(B, P + '/done/%s.json' % i, timeout=30, tries=3)
            if g is None: return i, None
            d = json.loads(g[0]); d.pop('kext_lines', None)
            sp = d.pop('spec', None) or {}
            d['_kind'] = sp.get('kind'); d['_tier'] = sp.get('tier'); d['_deps'] = len(sp.get('deps') or []); d['_gen'] = str(g[1])
            return i, d
        except Exception as e:
            err = e; time.sleep(2)
    return i, None
n = 0
with cf.ThreadPoolExecutor(par) as ex, open(OUT, 'a') as f:
    for i, d in ex.map(rd, todo):
        if d: f.write(json.dumps(d) + '\n'); have[i] = d; n += 1
gone = set(have) - set(listing)
tot = sum(int(have[i].get('size') or 0) for i in listing if i in have); ptot = sum(int(have[i].get('pubs_size') or 0) for i in listing if i in have)
print('%s done listed %d, read now %d, in file %d, no longer done %d; tarballs %.1f GB, pubs %.1f GB' % (
    time.strftime('%FT%TZ', time.gmtime()), len(listing), n, len(have), len(gone), tot / 1e9, ptot / 1e9))
json.dump(sorted(listing), open(os.path.join(H, 'done_ids.json'), 'w'))
