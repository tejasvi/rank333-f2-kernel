#!/usr/bin/env python3
"""unsupersede.py BUCKET PREFIX --reason TEXT ID... : undo supersede.py for packages retired by mistake (e.g. the done groups of a
winning split final, which are that final's dependencies): superseded/<id>.json goes
back to done/<id>.json (the superseded_* keys dropped, unsuperseded_reason/_t added; the tar/pubs objects it names never moved), the
lease becomes {"state": "done", ...} again, parked/<id> is removed, and the reason goes to unsuperseded/<id> (an audit trail).  Refuses
an id that already has a done record or has no superseded record.  Prints one line per id."""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objstore
a = sys.argv[1:]; B, P = a[0], a[1].rstrip('/'); reason = a[a.index('--reason') + 1]
ids = [x for i, x in enumerate(a[2:], 2) if x != '--reason' and a[i - 1] != '--reason']
for pid in ids:
    if objstore.get(B, P + '/done/%s.json' % pid): print(pid, '| already has a done record: untouched'); continue
    s = objstore.get(B, P + '/superseded/%s.json' % pid)
    if not s: print(pid, '| no superseded record: untouched'); continue
    r = json.loads(s[0]); prev = {k: r.pop(k, None) for k in ('superseded_by', 'superseded_reason', 'superseded_t')}
    now = time.time(); r.update(unsuperseded_reason=reason, unsuperseded_t=now)
    objstore.put(B, P + '/done/%s.json' % pid, json.dumps(r))
    objstore.put(B, P + '/lease/' + pid, json.dumps(dict(state='done', box=r.get('box'), t=now, sha256=r.get('sha256'))))
    if objstore.get(B, P + '/parked/' + pid): objstore.delete(B, P + '/parked/' + pid)
    objstore.put(B, P + '/unsuperseded/' + pid, json.dumps(dict(t=now, reason=reason, prev=prev)))
    objstore.delete(B, P + '/superseded/%s.json' % pid)
    print(pid, '| superseded/ -> done/, lease done, parked marker removed', flush=True)
