import json, math, collections, statistics as st
import os
R22 = os.environ.get('R22_ROOT', '.')   # the development layout's root (package mode does not use it)
R = R22 + '/e1g/E1P/run/cap2/'
rows = json.load(open('rows.json'))
fr6 = {}
for C in ('436', '422'):
    fr6[C] = {}
    for ln in open(R + 'fr%s_d6.txt' % C):
        k, p = ln.split(); fr6[C][int(k)] = p
subp = {}
def sp(C, J, a):
    if (C, J) not in subp: subp[(C, J)] = [ln.split()[1] for ln in open(R + 'sub%s/%d.txt' % (C, J))]
    return subp[(C, J)][a]
def dups(p):
    v = p.split(','); return len(v) - len(set(v))
for r in rows:
    if r['kind'] in ('range', 'split'): ps = [fr6[r['cap']][k] for k in range(r['a'], r['b'])]
    else: ps = [sp(r['cap'], r['job'], k) for k in range(r['a'], r['b'])]
    ds = [dups(p) for p in ps]
    r['dupmax'] = max(ds); r['dup0'] = ds[0]; r['pre0'] = ps[0]
json.dump(rows, open('rows2.json', 'w'))
D = [r for r in rows if r['done'] and r.get('epred') and r['list_s'] > 0]
for r in D: r['m'] = r['epred'] / r['list_s']
by = collections.defaultdict(list)
for r in D: by[(r['kind'], r['dupmax'])].append(r['m'])
for k in sorted(by): s = by[k]; print('%-12s dupmax=%d n=%5d median m=%.2f p90=%.2f max=%.2f' % (k[0], k[1], len(s), st.median(s), sorted(s)[int(.9*len(s))], max(s)))
# distribution of dupmax over not-done packages by kind
nd = collections.Counter((r['kind'], r['dupmax']) for r in rows if not r['done'])
print(sorted(nd.items()))
r0 = [r for r in rows if r['id'] in ('w1_00000', 'w1_03803')]
for r in r0: print(r['id'], r['kind'], r['cap'], r.get('job'), r['a'], r['b'], r['list_s'], r['nodes'], r['leaves'], r['dupmax'], r['pre0'])
