#!/usr/bin/env python3
"""extcut_race.py [--loop 60] [--dry] ID... (+ EXTCUT_IDS, re-read every loop): first finisher wins between a giant EXT package ID and
its cut build.  The cut (cutgiant.py, the ext generators) splits an emitted ID into group packages ID.sb0_<k> (H + a share of the
parts) and a final ID.sb (H + A + chunk, "deps_pubs" on the groups); all of them are queued (appendpk.py, front.py) while ID still
builds its parts.  Per ID, as soon as one side is done:
  * ID.sb done and ID not done: ID.sb wins and ID is retired (the groups are ID.sb's dependencies);
  * ID done: ID wins and the cut's packages not yet done (its groups and final) are retired;
  the cut's packages are the spec lines with "split_of" (or "family") = ID;
  retiring = queue/supersede.py (done record to superseded/, lease parked: a worker still building it drops it).
  A retired package whose done record shows up again (a finalize racing the park) is retired again, every loop, EXCEPT the winner's
  own split packages: when ID.sb won, its groups ID.sb0_<k> are its dependencies and are never retired.
The EXT aggregation accepts a done ID.sb as that leaf's package.  State: EXTCUT_STATE (default PB_WORK/split/extcut_state.json:
{"queued": {ID: [cut package ids]}, "resolved": {ID: winner}}); log: stdout.  Env: EXTCUT_IDS (a file, one ID per line), objstore.py."""
import gzip, json, os, subprocess, sys, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
PB = KE.QUEUE
a = sys.argv[1:]; loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 0; dry = '--dry' in a
IDS = [x for i, x in enumerate(a) if not x.startswith('--') and (i == 0 or a[i - 1] != '--loop')]
STATE = os.environ.get('EXTCUT_STATE', os.path.join(KE.WORK, 'split', 'extcut_state.json'))
IDF = os.environ.get('EXTCUT_IDS', os.path.join(KE.WORK, 'split', 'extcut_ids.txt'))
st = json.load(open(STATE)) if os.path.exists(STATE) else dict(queued={}, resolved={})
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
def save():
    if not dry:
        os.makedirs(os.path.dirname(STATE), exist_ok=True); json.dump(st, open(STATE + '.tmp', 'w'), indent=0); os.replace(STATE + '.tmp', STATE)
def supersede(ids, why):
    r = subprocess.run([sys.executable, os.path.join(PB, 'supersede.py'), B, P, '--reason', why] + ids, capture_output=True, text=True)
    return r.stdout.strip()[-200:]
while True:
    try:
        done = set(json.loads(gzip.decompress(objstore.get(B, P + '/done.json.gz')[0]))['ids'])
        pk = [json.loads(l) for l in objstore.get(B, P + '/packages.jsonl')[0].decode().splitlines() if l.strip()]
        ids = IDS + ([l.strip() for l in open(IDF) if l.strip() and l.strip() not in IDS] if os.path.exists(IDF) else [])
        for pid in ids:      # the cut's packages: the queued spec lines that split pid
            cut = [x['id'] for x in pk if x.get('split_of') == pid or x.get('family') == pid]
            if cut and sorted(cut) != sorted(st['queued'].get(pid, [])): st['queued'][pid] = sorted(cut)
        for pid, cut in list(st['queued'].items()):
            if pid in st['resolved']:
                win = st['resolved'][pid]
                # the winner's own split packages are never losers: when <pid>.sb won, its groups are its dependencies
                back = [i for i in [pid, pid + '.sb'] + cut if i != win and i in done and not (win == pid + '.sb' and i.startswith(pid + '.sb'))]
                if back and not dry:
                    log(pid, 're-retired', back, '|', supersede(back, 'giant EXT cut race: %s won; the done record of a retired alternative appeared again (finalize raced the park): retired again' % win))
                continue
            fin = pid + '.sb'
            if fin in done and pid not in done: win, lose = fin, [pid]
            elif pid in done: win, lose = pid, [i for i in cut if i not in done]
            else: continue
            log(pid, 'won by', win, '; retiring', lose)
            if not dry and lose: log(supersede(lose, 'giant EXT cut race (extcut_race.py): %s finished first; first finisher wins' % win))
            st['resolved'][pid] = win; save()
        save()
    except Exception as e:
        log('error', repr(e)[:300])
    if not loop: break
    time.sleep(loop)
