#!/usr/bin/env python3
"""supersede.py BUCKET PREFIX --reason TEXT [--by-suffix SFX] ID... : retire packages for good (a re-emitted replacement exists, or the
package lost a first-finisher race): a done record moves to superseded/<id>.json (with superseded_by, reason, time; its tar/pubs objects stay where
they are, named in the record), the lease becomes "parked" with the reason (a box building it loses the lease and drops it; the sweep
never requeues a parked package), parked/<id> gets the reason, a failed/<id> marker is removed.  Prints one line per id."""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objstore
a = sys.argv[1:]; B, P = a[0], a[1].rstrip('/')
reason = a[a.index('--reason') + 1]; sfx = a[a.index('--by-suffix') + 1] if '--by-suffix' in a else None
skip = {i for i, x in enumerate(a) if x in ('--reason', '--by-suffix')}; skip |= {i + 1 for i in skip}
ids = [x for i, x in enumerate(a[2:], 2) if i not in skip]
for pid in ids:
    by = pid + sfx if sfx else None; why = reason + (' (superseded by %s)' % by if by else ''); now = time.time(); out = []
    d = objstore.get(B, P + '/done/%s.json' % pid)
    if d:
        r = json.loads(d[0]); r.update(superseded_by=by, superseded_reason=why, superseded_t=now)
        objstore.put(B, P + '/superseded/%s.json' % pid, json.dumps(r)); objstore.delete(B, P + '/done/%s.json' % pid); out.append('done record -> superseded/')
    l = objstore.get(B, P + '/lease/' + pid)
    prev = json.loads(l[0]).get('state') if l else None
    objstore.put(B, P + '/lease/' + pid, json.dumps(dict(state='parked', box='operator', t=now, reason=why[:500], prev_state=prev)))
    objstore.put(B, P + '/parked/' + pid, why[:500]); out.append('lease %s -> parked' % prev)
    if objstore.get(B, P + '/failed/' + pid):
        objstore.delete(B, P + '/failed/' + pid); out.append('failed marker removed')
    print(pid, '|', ', '.join(out), flush=True)
