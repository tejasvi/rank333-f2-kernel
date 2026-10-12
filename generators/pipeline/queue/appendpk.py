#!/usr/bin/env python3
"""appendpk.py BUCKET PREFIX FILE...: append package lines (new ids only) to a running queue's packages.jsonl (generation-checked
rewrite); workers reload it on their next rescan."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objstore
B, P = sys.argv[1], sys.argv[2].rstrip('/')
for att in range(5):
    r = objstore.get(B, P + '/packages.jsonl'); gen = r[1]
    pk = r[0].decode().splitlines(); ids = {json.loads(l)['id'] for l in pk if l.strip()}
    new = []
    for f in sys.argv[3:]:
        for l in open(f):
            if l.strip() and json.loads(l)['id'] not in ids: new.append(l.rstrip('\n')); ids.add(json.loads(l)['id'])
    try:
        objstore.put(B, P + '/packages.jsonl', '\n'.join([l for l in pk if l.strip()] + new) + '\n', if_generation=gen)
        print('appended %d packages (now %d)' % (len(new), len(ids))); break
    except objstore.Precondition:
        continue
