#!/usr/bin/env python3
"""kccut.py OUT.jsonl [TARGET_S]: the class tier's package cut list (21 hcap-native raise classes), mkcut.py's kinds, from the native
per-root-job counts (rootjobs.tsv: 0.5 ms per st-node + ms_leaf(c) per leaf, E1G layout) and the giants' search-only counts
(giants/h<c>_<J>/giant.json: sub-jobs at depth D of the giant root jobs, i.e. those predicted over 3e5 s):
  range       light root jobs [a, b) (each at most 600 s), cut at TARGET_S (default 5400) and at every split or giant job;
              emitpkg.sh h<c> a b OUT
  split       one root job of 600 s .. 3e5 s: split at depth 7 directly (batched split, recursively);
              emitpkg.sh h<c> k k+1 OUT --split 7
  heavy-sub   light sub-jobs [a, b) of giant J (local indices of its depth-D frontier, each at most 600 s), cut at TARGET_S;
              emitpkg.sh h<c> a b OUT --heavy J
  heavy-split one sub-job of giant J over 600 s (or over the count budget): split at depth D+2 directly;
              emitpkg.sh h<c> s s+1 OUT --heavy J --split D+2
The companion OUT's kc_heavy.jsonl lists every giant for the aggregation phase (its table KC.Sh<c>_<J>, top chain, range [J, J+1))."""
import sys, json, os
OUT = sys.argv[1]; TARGET = float(sys.argv[2]) if len(sys.argv) > 2 else 5400.0
SKIPG = '--no-giants' in sys.argv   # range and split packages only (the giants' heavy packages come in a second list)
GONLY = '--giants-only' in sys.argv
pending = []
I = os.environ.get('KC_INPUTS', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'inputs', 'classes'))
G = os.path.join(I, 'giants') + '/'
PRICE = {'485': 4.65, '487': 6.94, '490': 8.04, '454': 9.18, '470': 7.98, '473': 9.60, '476': 10.21, '465': 16.35, '455': 14.71, '456': 10.98,
         '471': 4.21, '475': 10.53, '458': 7.06, '464': 10.49, '472': 19.92, '450': 8.57, '451': 23.84, '469': 7.26, '463': 5.06, '420': 81.22, '460': 7.21}
LIMIT, GIANT = 600.0, 3e5
rows = {}
for l in open(os.path.join(I, 'rootjobs.tsv')):
    c, k, n, lv, p = l.split('\t'); rows.setdefault(c, []).append((int(k), int(n), int(lv), float(p)))
pk = []; heavy = []
ID0 = int([a for a in sys.argv if a.startswith('--id0=')][0][6:]) if any(a.startswith('--id0=') for a in sys.argv) else 0
def add(**r):
    if GONLY and r['kind'] in ('range', 'split'): return
    r['id'] = 'kc_%05d' % (ID0 + len(pk)); r.setdefault('pred_gb_max', 5.0); pk.append(r)
for c in sorted(rows, key=lambda c: -sum(x[3] for x in rows[c])):
    ctx = 'h' + c; msl = max(6.0, 1.6 * PRICE[c]); cur = []; cs = 0.0
    def flush():
        global cur, cs
        if cur: add(cap=ctx, kind='range', a=cur[0], b=cur[-1] + 1, args=[ctx, cur[0], cur[-1] + 1], pred_s=round(cs, 1)); cur, cs = [], 0.0
    for k, n, lv, p in sorted(rows[c]):
        if p <= LIMIT:
            if cur and cs + p > TARGET: flush()
            cur.append(k); cs += p; continue
        flush()
        if p <= GIANT:
            add(cap=ctx, kind='split', a=k, b=k + 1, args=[ctx, k, k + 1, '--split', 7], pred_s=round(p, 1)); continue
        if not os.path.exists(G + '%s_%d/giant.json' % (ctx, k)):
            if SKIPG: pending.append((ctx, k, p)); continue
            raise SystemExit('giant %s/%d not counted yet' % (ctx, k))
        if SKIPG: continue
        g = json.load(open(G + '%s_%d/giant.json' % (ctx, k))); D = g['depth']; cnt = g['counts']; hv = set(g['over_budget'])
        tot = 0.0; sc = []; ss = 0.0
        def flush_s():
            global sc, ss
            if sc: add(cap=ctx, kind='heavy-sub', job=k, a=sc[0], b=sc[-1] + 1, args=[ctx, sc[0], sc[-1] + 1, '--heavy', k], pred_s=round(ss, 1)); sc, ss = [], 0.0
        for s in range(g['subjobs']):
            if s in hv: q = None
            else: sn, sl = cnt[str(s)]; q = (0.5 * sn + msl * sl) / 1000.0
            if q is not None and q <= LIMIT:
                if sc and ss + q > TARGET: flush_s()
                sc.append(s); ss += q; tot += q; continue
            flush_s()
            qq = q if q is not None else 2 * GIANT   # over the count budget: unknown, at least ~1e5 s
            add(cap=ctx, kind='heavy-split', job=k, a=s, b=s + 1, args=[ctx, s, s + 1, '--heavy', k, '--split', D + 2], pred_s=round(qq, 1)); tot += qq
        flush_s()
        heavy.append(dict(cap=ctx, job=k, prefix=g['prefix'], depth=D, subjobs=g['subjobs'], over_budget=len(hv), pred_s=round(tot, 1)))
    flush()
with open(OUT, 'w') as f:
    for r in pk: f.write(json.dumps(r) + '\n')
if not SKIPG:
  with open(os.path.join(os.path.dirname(os.path.abspath(OUT)), 'kc_heavy.jsonl'), 'w') as f:
    for r in heavy: f.write(json.dumps(r) + '\n')
if pending: print('giants pending (not in this list):', len(pending), 'pred %.3e s' % sum(x[2] for x in pending))
import collections
kc = collections.Counter(r['kind'] for r in pk)
print('%d packages %s, pred %.3e s = %.0f CPU-hours; %d giants; max package pred %.0f s' % (len(pk), dict(kc), sum(r['pred_s'] for r in pk),
      sum(r['pred_s'] for r in pk) / 3600, len(heavy), max(r['pred_s'] for r in pk)))
