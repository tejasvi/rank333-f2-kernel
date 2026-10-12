#!/usr/bin/env python3
"""multirace.py [--loop 30] A1,A2[,...] [B1,B2 ...]: first finisher wins among attempts of ONE package (e.g. race attempts of a giant
EXT leaf, ext_..._r5 and ext_..._r6), each attempt counting together with its split build (<id>.sb final and
<id>.sb<w>_<i> groups).  As soon as any id of an attempt is done, every package of every other attempt is retired (supersede.py: lease
parked, a done record if any to superseded/), done or not, so exactly one attempt of the leaf is ever done.  An attempt base id whose
lease is 'failed' is parked (lease "parked" + parked/<id>: the EXT scan then spawns no further attempt).  Exits when every group is
resolved (after a 30 min watch for done records that reappear).  Env: objstore.py; retiring runs queue/supersede.py."""
import gzip, json, os, subprocess, sys, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
PB = KE.QUEUE
def park(pid, why):
    l = objstore.get(B, P + '/lease/' + pid)
    try: objstore.put(B, P + '/lease/' + pid, json.dumps(dict(state='parked', box='operator', t=time.time(), reason=why[:500])), if_generation=l[1] if l else 0)
    except objstore.Precondition: return 'lease changed: not parked'
    objstore.put(B, P + '/parked/' + pid, why[:500]); return 'parked'
a = sys.argv[1:]; loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 30
groups = [g.split(',') for i, g in enumerate(a) if not g.startswith('--') and (i == 0 or a[i - 1] != '--loop')]
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
resolved = {}
while True:
    done = set(json.loads(gzip.decompress(objstore.get(B, P + '/done.json.gz')[0]))['ids'])
    pk = [json.loads(l)['id'] for l in objstore.get(B, P + '/packages.jsonl')[0].decode().splitlines() if l.strip()]
    for gi, g in enumerate(groups):
        fam = {b: [i for i in pk if i == b or i.startswith(b + '.sb')] for b in g}
        if gi not in resolved:
            for b in g:
                l = objstore.get(B, P + '/lease/' + b)
                if l and json.loads(l[0]).get('state') == 'failed':
                    log('parked failed', b, '|', park(b, 'race attempt failed outright: parked, so the EXT scan spawns no further attempt'))
            win = next((b for b in g for i in fam[b] if i in done and (i == b or i == b + '.sb')), None)
            if not win: continue
            resolved[gi] = win
        win = resolved[gi]
        lose = [i for b in g if b != win for i in fam[b]]
        live = [i for i in lose if i in done or not (objstore.get(B, P + '/lease/' + i) and json.loads(objstore.get(B, P + '/lease/' + i)[0]).get('state') == 'parked')]
        if live:
            r = subprocess.run([sys.executable, os.path.join(PB, 'supersede.py'), B, P, '--reason',
                                'giant EXT attempt race (multirace.py): %s finished first; the other attempts and their split builds are retired' % win] + live,
                               capture_output=True, text=True)
            log('group', g, 'won by', win, '; retired', live, '|', r.stdout.strip()[-200:])
    if len(resolved) == len(groups):
        # keep watching a little longer for done records that reappear (finalize racing the park), then exit
        _grace = globals().get('_grace') or time.time()
        if time.time() - _grace > 1800: log('all resolved; exiting'); break
    time.sleep(loop)
