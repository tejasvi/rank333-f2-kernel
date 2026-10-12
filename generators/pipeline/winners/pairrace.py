#!/usr/bin/env python3
"""pairrace.py GATEFILE GATED_ID ALT1 ALT2 ... [--loop 60]: first finisher wins among packages that build the same thing (e.g.
II.KM2P001116 and its race copy II.KM2P001116.h8): as soon as one is done, the gated line GATED_ID in GATEFILE (a gate file read by
gateappend) names it as its dependency in place of the other alternatives (flock GATEFILE.lock), and every other alternative is
retired (supersede.py: lease parked, a done record if any to superseded/), so exactly one of them is ever a dependency and enters the
top store (two done at once: the one the top store installed, FINAL_DIR/topstore/pkgs/<id>.json, else the earliest t_done).  Exits
after resolving (or every loop when --loop is given and nothing is done yet).  Log: stdout.  Env: kitenv.py, objstore.py."""
import fcntl, gzip, json, os, subprocess, sys, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
PB = KE.QUEUE
a = sys.argv[1:]; loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 0
pos = [x for i, x in enumerate(a) if not x.startswith('--') and (i == 0 or a[i - 1] != '--loop')]
GF, G, ALTS = pos[0], pos[1], pos[2:]
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
while True:
    done = set(json.loads(gzip.decompress(objstore.get(B, P + '/done.json.gz')[0]))['ids'])
    dn = [x for x in ALTS if x in done]
    if dn:
        # two done at once: the one the top store installed (FINAL_DIR/topstore/pkgs/<id>.json), else the earliest t_done
        inst = [x for x in dn if os.path.exists(os.path.join(KE.FINAL, 'topstore', 'pkgs', x + '.json'))]
        def tdone(x):
            g = objstore.get(B, P + '/done/%s.json' % x); return json.loads(g[0]).get('t_done', 9e18) if g else 9e18
        win = inst[0] if len(inst) == 1 else min(dn, key=tdone)
        with open(GF + '.lock', 'w') as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            L = [json.loads(l) for l in open(GF) if l.strip()]
            for x in L:
                if x['id'] == G:
                    old = list(x['deps']); x['deps'] = [d for d in x['deps'] if d not in ALTS or d == win]
                    if win not in x['deps']: x['deps'].append(win)
                    log(G, 'deps', [d for d in old if d in ALTS], '->', win)
            open(GF + '.tmp', 'w').write(''.join(json.dumps(x) + '\n' for x in L)); os.replace(GF + '.tmp', GF)
        lose = [x for x in ALTS if x != win]
        r = subprocess.run([sys.executable, os.path.join(PB, 'supersede.py'), B, P, '--reason',
                            'first finisher wins (pairrace.py): %s finished first; the other copies are retired' % win] + lose, capture_output=True, text=True)
        log('retired', lose, '|', r.stdout.strip()[-200:])
        break
    if not loop: break
    time.sleep(loop)
