#!/usr/bin/env python3
"""ptc_resolve.py [--loop 120]: first finisher wins among each point package pt_XXXX.v8 and its parallel replacements (pt_XXXX.v9,
.v10, ...: the spec lines of PT_DIR/pt_v*.jsonl, each with "parent": the range's v8 package; a replacement may itself be split, its
final "<id>.sb").  Per range, as soon as one attempt is done:
  * the winner is agg_ptc's dependency for that range (AGG_PLAN rewritten when the dependency changes; the gate re-reads
    it, and agg_ptc is appended only when every dependency is done);
  * the loser is retired with supersede.py (done record, if any, to superseded/; lease parked: a box still building it drops it), so
    its outputs never enter the final store (each attempt has its own module names); with a losing attempt go its split build's
    packages that are not done.
Exactly one package per range is ever a dependency.  Log: one line per change and a status line per loop.  Env: PT_DIR (default
PB_WORK/point), AGG_PLAN (default PB_WORK/agg/agg_plan.jsonl; locked with race.py), objstore.py."""
import glob, json, os, subprocess, sys, time, gzip, fcntl
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = os.environ.get('PT_DIR', os.path.join(KE.WORK, 'point')); PB = KE.QUEUE
loop = int(sys.argv[sys.argv.index('--loop') + 1]) if '--loop' in sys.argv else 0
def alt_sets():
    # range (its v8 package) -> every attempt: v8 and the replacements of every PT_DIR/pt_v*.jsonl; re-read each loop
    alts = {}
    for f in sorted(glob.glob(os.path.join(H, 'pt_v*.jsonl')), key=lambda f: int(''.join(c for c in os.path.basename(f) if c.isdigit()) or 0)):
        for l in open(f):
            if l.strip(): x = json.loads(l); alts.setdefault(x['parent'], [x['parent']]).append(x['id'])
    return alts
AGG = os.environ.get('AGG_PLAN', os.path.join(KE.WORK, 'agg', 'agg_plan.jsonl'))
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
retired = set()
while True:
    try:
        done = set(json.loads(gzip.decompress(objstore.get(B, P + '/done.json.gz')[0]))['ids'])
        PKIDS = [json.loads(l)['id'] for l in objstore.get(B, P + '/packages.jsonl')[0].decode().splitlines() if l.strip() and '.sb' in l]
        lk = open(AGG + '.lock', 'w'); fcntl.flock(lk, fcntl.LOCK_EX)     # shared with race.py (both rewrite the file)
        L = [json.loads(l) for l in open(AGG) if l.strip()]
        agg = next(x for x in L if x['id'] == 'agg_ptc')
        deps = list(agg['deps']); changed = False; status = []
        for v8, alts in alt_sets().items():
            cur = [y for y in alts if y in deps]
            dn = [y for y in alts if y in done]
            if not dn: status.append('%s pending' % v8[:-3]); continue
            win = cur[0] if cur and cur[0] in dn else dn[0]
            if len(cur) != 1: log('ERROR agg_ptc lists', cur, 'for range', v8); continue
            if win != cur[0]:
                deps[deps.index(cur[0])] = win; changed = True; log('agg_ptc dependency', cur[0], '->', win)
            for lose in alts:
                if lose == win: continue
                if lose in retired and lose not in done: continue      # retired again only if its done record reappeared (finalize raced the park)
                # with a losing attempt go its split build's packages that are not done (groups <lose>.sb<w>_<i>, final <lose>.sb)
                base = lose[:-3] if lose.endswith('.sb') else lose
                extra = [i for i in PKIDS if i.startswith(base + '.sb') and i not in done and i != win and i != lose]
                r = subprocess.run([sys.executable, os.path.join(PB, 'supersede.py'), B, P, '--reason',
                                    'point replacement race: %s finished first (first finisher wins); the other attempts of the range are retired' % win, lose] + extra,
                                   capture_output=True, text=True)
                log('retired', lose, '|', r.stdout.strip()[-160:]); retired.add(lose)
            status.append('%s won by %s' % (v8[:-3], win.rsplit('.', 1)[1]))
        if changed:
            assert len(deps) == len(set(deps)) == len(agg['deps'])
            agg['deps'] = deps
            open(AGG + '.tmp', 'w').write(''.join(json.dumps(x) + '\n' for x in L)); os.replace(AGG + '.tmp', AGG)
        lk.close()
        log('status:', ', '.join(status))
    except Exception as e:
        log('error', repr(e)[:300])
        try: lk.close()
        except Exception: pass
    if not loop: break
    time.sleep(loop)
