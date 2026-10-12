#!/usr/bin/env python3
"""race.py [--loop 120] [--dry]: first finisher wins for every range with alternative builds (exactly one package per range feeds
the aggregation).  A slot is one dependency X of an aggregation line in AGG_PLAN for which an alternative exists:
  X.re, X.r2  parallel re-emissions of X (RACE_DIR/reemit/*.jsonl, "replaces": X; new module names)
  X.sb      split build of X: the final package of family X (RACE_DIR/lines/*.lines.jsonl; its group packages carry "family": X)
  X.re.sb, X.r2.sb  split builds of the re-emissions (families X.re, X.r2)
As soon as one alternative is done (done.json.gz):
  * it is the aggregation line's dependency (the line is rewritten when that changes; the gate re-reads the file and appends the line
    once every dependency is done).  If several are done, the current dependency stays if it is one of them, else the earliest t_done;
  * every other alternative is retired with supersede.py (done record to superseded/, lease parked: a box building it drops it), and so
    are the group packages of each losing family (family X when the winner is not X.sb, family X.re when the winner is not X.re.sb),
    so no two packages with one module name ever both enter the top store;
  * a retired package whose done record shows up again (a finalize racing the park) is retired again, every loop.
The aggregation file is rewritten under an flock (AGG_PLAN.lock) shared with ptc_resolve.py.  State: RACE_DIR/race_state.json (winners,
retired ids).  Log: one line per change and a status line per loop.  Env: RACE_DIR (default PB_WORK/split), AGG_PLAN (the aggregation
lines, default PB_WORK/agg/agg_plan.jsonl), objstore.py; retiring runs queue/supersede.py."""
import fcntl, glob, gzip, json, os, subprocess, sys, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore, kitenv as KE
B, P = objstore.BUCKET, objstore.PREFIX
H = os.environ.get('RACE_DIR', os.path.join(KE.WORK, 'split')); PB = KE.QUEUE
a = sys.argv[1:]; loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 0; dry = '--dry' in a
AGG = os.environ.get('AGG_PLAN', os.path.join(KE.WORK, 'agg', 'agg_plan.jsonl')); STATE = os.path.join(H, 'race_state.json')
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
st = json.load(open(STATE)) if os.path.exists(STATE) else dict(winners={}, retired=[])
retired = set(st['retired'])
def save():
    st['retired'] = sorted(retired); open(STATE + '.tmp', 'w').write(json.dumps(st, indent=0)); os.replace(STATE + '.tmp', STATE)
def lines(pattern):
    out = []
    for f in sorted(glob.glob(os.path.join(H, pattern))):
        for l in open(f):
            if l.strip():
                try: out.append(json.loads(l))
                except ValueError: pass
    return out
def retire(ids, why):
    ids = sorted(set(ids) - retired) if why != 'again' else sorted(set(ids))
    if not ids: return
    if dry: log('DRY would retire', len(ids), ids[:8]); return
    for i in range(0, len(ids), 200):
        ch = ids[i:i + 200]
        r = subprocess.run([sys.executable, os.path.join(PB, 'supersede.py'), B, P, '--reason', why if why != 'again' else
                            'first finisher wins (race.py): retired earlier, its done record appeared again (finalize raced the park)'] + ch,
                           capture_output=True, text=True)
        log('retired', len(ch), ch[:6], '|', (r.stdout.strip().splitlines() or [''])[-1][:200], r.stderr.strip()[-200:])
        retired.update(ch)
    save()
while True:
    try:
        done = set(json.loads(gzip.decompress(objstore.get(B, P + '/done.json.gz')[0]))['ids'])
        res = {}                                   # X -> its re-emissions (X.re, X.r2, ...)
        for x in lines('reemit/*.jsonl'):
            if x.get('replaces'): res.setdefault(x['replaces'], []).append(x['id'])
        base_of = {r: X for X, rs in res.items() for r in rs}
        sbl = lines('lines/*.lines.jsonl')
        fam = {}; finals = {}
        for x in sbl:
            if x.get('family'):
                fam.setdefault(x['family'], []).append(x['id'])
                # a family's split final: "<F>.sb" (first cut) or a re-cut's final (kind splitbuild-final, e.g. "<F>.sb2")
                if x['id'] == x['family'] + '.sb' or x.get('kind') == 'splitbuild-final':
                    if x['id'] not in finals.setdefault(x['family'], []): finals[x['family']].append(x['id'])
        final_of = {f: F for F, fs in finals.items() for f in fs}
        status = []
        # retired packages whose done record came back
        back = sorted(retired & done)
        if back: log('done records back for retired packages:', back[:10]); retire(back, 'again')
        with open(AGG + '.lock', 'w') as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            L = [json.loads(l) for l in open(AGG) if l.strip()]
            changed = False
            for ag in L:
                deps = ag.get('deps') or []
                for k, d in enumerate(list(deps)):
                    X = final_of.get(d, d)
                    X = base_of.get(X, X)
                    srcs = [X] + res.get(X, [])         # the packages whose build (or split build) can fill this slot
                    alts = srcs + [f for F in srcs for f in finals.get(F, [])]
                    if len(alts) == 1: continue
                    dn = [y for y in alts if y in done]
                    if not dn: status.append('%s pending' % X); continue
                    if d in dn: win = d
                    else:
                        tds = {}
                        for y in dn:
                            g = objstore.get(B, P + '/done/%s.json' % y)
                            tds[y] = json.loads(g[0]).get('t_done', 9e18) if g else 9e18
                        win = min(dn, key=lambda y: tds[y])
                    if win != d:
                        if win in deps: log('ERROR', ag['id'], 'already lists', win); continue
                        deps[k] = win; changed = True; log(ag['id'], 'dependency', d, '->', win)
                    st['winners'][X] = win
                    lose = [y for y in alts if y != win]
                    for F in srcs:
                        if F in fam and win not in finals.get(F, []): lose += fam[F]
                    retire(lose, 'first finisher wins (race.py): %s finished first for range %s; the other attempts of the range (and their split-build group packages) are retired' % (win, X))
                    status.append('%s won by %s' % (X, win))
            if changed and not dry:
                for ag in L: assert len(ag.get('deps') or []) == len(set(ag.get('deps') or []))
                open(AGG + '.tmp', 'w').write(''.join(json.dumps(x) + '\n' for x in L)); os.replace(AGG + '.tmp', AGG)
        save()
        log('status: %d slots, %d won, %d pending; %d retired' % (len(status), sum(1 for s in status if ' won ' in s), sum(1 for s in status if s.endswith('pending')), len(retired)),
            '|', ', '.join(s for s in status if ' won ' in s)[:600])
    except Exception as e:
        log('error', repr(e)[:300])
    if not loop: break
    time.sleep(loop)
