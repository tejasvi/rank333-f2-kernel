"""predict.py: expected-size multipliers (emitter kernel prediction / cut-list price) for the not-yet-done c436/c422 wave-1
packages, from the done records (the emitter's pred_s) and the census features (rows2.json):
  1. heavy-sub / heavy-split of a heavy job J with done packages: the median multiplier of J's done packages, shrunk toward the
     kind/cap median with weight 3 (log scale);
  2. else, done packages of the heavy jobs nearest to J in the depth-6 order (index window, at least 8 packages);
  3. else (ranges, splits, heavy jobs without neighbours): the kind/cap median times the leaf-fraction factor of the done set;
  4. measured by emission on the development host: w1_00000 2507/17.1, w1_03803 97397/37117.
Writes expected_size.jsonl (all not-done packages, by expected size) and far_above_list.jsonl (multiplier >= 1.5)."""
import json, math, collections, statistics as st, bisect
rows = json.load(open('rows2.json'))
taken = set(json.load(open('taken.json'))['ids'])
D = [r for r in rows if r['done'] and r.get('epred') and r['list_s'] > 0]
for r in D: r['m'] = r['epred'] / r['list_s']; r['lf'] = r['leaves'] / max(r['nodes'], 1)
MEAS = {'w1_00000': 2506.6 / 17.1, 'w1_03803': 97397.5 / 37117.2}
lg = lambda x: math.log(max(x, 1e-6))
gmed = {}
for k in ('range', 'split', 'heavy-sub', 'heavy-split'):
    for C in ('436', '422'):
        s = [r['m'] for r in D if r['kind'] == k and r['cap'] == C]
        gmed[(k, C)] = st.median(s) if len(s) >= 5 else st.median([r['m'] for r in D if r['cap'] == C])
# leaf-fraction factor (relative to the overall median), from the done set
allmed = st.median([r['m'] for r in D])
lfb = collections.defaultdict(list)
for r in D: lfb[min(int(r['lf'] * 10), 9)].append(r['m'])
lff = {b: (st.median(v) / allmed if len(v) >= 30 else 1.0) for b, v in lfb.items()}
byJ = collections.defaultdict(list)
for r in D:
    if r['job'] >= 0: byJ[(r['cap'], r['job'])].append(r['m'])
for i, m in MEAS.items():
    r = next(x for x in rows if x['id'] == i)
    if r['job'] >= 0: byJ[(r['cap'], r['job'])].append(m)
Js = {C: sorted(J for (c, J) in byJ if c == C) for C in ('436', '422')}
out = []
for r in rows:
    if r['done'] or r['id'] in taken and r['id'] not in MEAS: continue
    C, k = r['cap'], r['kind']; lf = r['leaves'] / max(r['nodes'], 1)
    base = gmed[(k, C)] * lff.get(min(int(lf * 10), 9), 1.0); basis = 'kind/cap median x leaf fraction'
    if r['id'] in MEAS:
        m = MEAS[r['id']]; basis = 'measured (emission on the development host)'
    elif r['job'] >= 0 and (C, r['job']) in byJ:
        s = byJ[(C, r['job'])]; n = len(s)
        m = math.exp((n * lg(st.median(s)) + 3 * lg(base)) / (n + 3)); basis = 'heavy job %d: %d done siblings (median %.2f)' % (r['job'], n, st.median(s))
    elif r['job'] >= 0 and Js[C]:
        i = bisect.bisect_left(Js[C], r['job']); near = []
        lo, hi = i - 1, i
        while len(near) < 8 and (lo >= 0 or hi < len(Js[C])):
            if hi < len(Js[C]) and (lo < 0 or Js[C][hi] - r['job'] <= r['job'] - Js[C][lo]): near += byJ[(C, Js[C][hi])]; hi += 1
            else: near += byJ[(C, Js[C][lo])]; lo -= 1
        m = math.exp((len(near) * lg(st.median(near)) + 3 * lg(base)) / (len(near) + 3)); basis = 'nearest heavy jobs (%d done packages, median %.2f)' % (len(near), st.median(near))
    else:
        m = base
    out.append({'id': r['id'], 'cap': C, 'kind': k, 'job': r['job'], 'a': r['a'], 'b': r['b'], 'list_s': r['list_s'], 'mult': round(m, 2),
                'expected_s': round(r['list_s'] * m, 1), 'basis': basis, 'taken': r['id'] in taken})
out.sort(key=lambda o: -o['expected_s'])
with open('expected_size.jsonl', 'w') as f:
    for o in out: f.write(json.dumps(o) + '\n')
far = [o for o in out if o['mult'] >= 1.5]
far.sort(key=lambda o: -o['expected_s'])
with open('far_above_list.jsonl', 'w') as f:
    for o in far: f.write(json.dumps(o) + '\n')
print(len(out), 'not-done packages;', sum(1 for o in out if o['taken']), 'of them taken (in progress)')
print('far above list (mult >= 1.5):', len(far), ' expected %.0f vCPU-h vs list %.0f' % (sum(o['expected_s'] for o in far) / 3600, sum(o['list_s'] for o in far) / 3600))
print('all not-done: expected %.0f vCPU-h vs list %.0f (isolated kernel, before the co-tenancy factor)' % (sum(o['expected_s'] for o in out) / 3600, sum(o['list_s'] for o in out) / 3600))
c = collections.Counter(o['basis'].split(':')[0].split(' (')[0] for o in out); print(c.most_common(6))
for o in far[:15]: print(o['id'], o['kind'], o['cap'], o['job'], o['list_s'], o['mult'], o['expected_s'], o['basis'])
