#!/usr/bin/env python3
"""front.py BUCKET PREFIX ID... : move existing package lines to the head of packages.jsonl (generation-checked rewrite; claim order =
file order, so these are claimed first); unknown ids are reported."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objstore
B, P, ids = sys.argv[1], sys.argv[2].rstrip('/'), sys.argv[3:]
for att in range(5):
    r = objstore.get(B, P + '/packages.jsonl'); gen = r[1]
    L = [l for l in r[0].decode().splitlines() if l.strip()]
    head = []; rest = []
    for l in L:
        (head if json.loads(l)['id'] in ids else rest).append(l)
    found = {json.loads(l)['id'] for l in head}
    try:
        objstore.put(B, P + '/packages.jsonl', '\n'.join(sorted(head, key=lambda l: ids.index(json.loads(l)['id'])) + rest) + '\n', if_generation=gen)
        print('moved %d to the front (%d lines); not found: %s' % (len(head), len(L), sorted(set(ids) - found))); break
    except objstore.Precondition:
        continue
