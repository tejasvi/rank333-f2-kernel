#!/usr/bin/env python3
"""requeue.py BUCKET PREFIX --reason TEXT ID... : put parked/failed packages back into the queue after inspection (e.g. an unclean
audit traced to outputs lost in an abrupt machine stop): the lease (parked or failed, never held or done), parked/<id>, failed/<id> and
attempts/<id> are deleted; the reason goes to requeued/<id> (an audit trail).  Prints one line per id."""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objstore
a = sys.argv[1:]; B, P = a[0], a[1].rstrip('/'); reason = a[a.index('--reason') + 1]
ids = [x for i, x in enumerate(a[2:], 2) if x != '--reason' and a[i - 1] != '--reason']
for pid in ids:
    l = objstore.get(B, P + '/lease/' + pid); st = json.loads(l[0]).get('state') if l else None
    if st in ('held', 'done'): print(pid, '| lease is', st, '- not touched'); continue
    prev = dict(lease=l[0].decode()[:600] if l else None, parked=(objstore.get(B, P + '/parked/' + pid) or [b''])[0].decode()[:600])
    objstore.put(B, P + '/requeued/' + pid, json.dumps(dict(t=time.time(), reason=reason, prev=prev)))
    if l: objstore.delete(B, P + '/lease/' + pid, if_generation=l[1])
    for sub in ('parked', 'failed', 'attempts'):
        if objstore.get(B, P + '/%s/%s' % (sub, pid)): objstore.delete(B, P + '/%s/%s' % (sub, pid))
    print(pid, '| requeued (lease was %s)' % st, flush=True)
