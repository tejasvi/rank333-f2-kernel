import json, glob, sys, collections, math
import os
R22 = os.environ.get('R22_ROOT', '.')   # the development layout's root (package mode does not use it)
R = R22 + '/e1g/E1P/run/cap2/'
P = R22 + '/e1g/pkg/'
# done records
txt = ''.join(open(f).read() for f in sorted(glob.glob('parts/*.json')))
dec = json.JSONDecoder(); i = 0; done = {}
while i < len(txt):
    while i < len(txt) and txt[i].isspace(): i += 1
    if i >= len(txt): break
    o, j = dec.raw_decode(txt, i); i = j
    done[o['id']] = {k: o.get(k) for k in ('pred_s', 'cpu_s', 'wall_s', 'emit_s', 'kext', 'modules', 'max_anon_gb')}
print(len(done), 'done records')
# cut list
pk = [json.loads(l) for l in open(P + 'wave1_packages.jsonl')]
# census per depth-6 job and per sub-job prefix
fe = {}
for C in ('436', '422'):
    d1 = {}
    for ln in open(R + 'js%s_1.txt' % C):
        f = ln.split(); d1[int(f[0])] = (int(f[1]), int(f[2]))
    sub = {}
    for ln in open(R + 'js%s_2.txt' % C):
        f = ln.split(); sub[int(f[1])] = (int(f[2]), int(f[3]))
    pc = {}
    for ln in open(R + 'subfr%s.txt' % C):
        k, p = ln.split(); pc[p] = sub.get(int(k), (0, 0))
    fe[C] = (d1, pc)
subcache = {}
def subjobs(C, J):
    if (C, J) not in subcache:
        subcache[(C, J)] = [fe[C][1].get(ln.split()[1], (0, 0)) for ln in open(R + 'sub%s/%d.txt' % (C, J))]
    return subcache[(C, J)]
rows = []
for p in pk:
    C = p['cap']
    if p['kind'] in ('range', 'split'):
        nl = [fe[C][0].get(k, (0, 0)) for k in range(p['a'], p['b'])]
    else:
        nl = subjobs(C, p['job'])[p['a']:p['b']]
    n = sum(x[0] for x in nl); l = sum(x[1] for x in nl); mx = max((x[0] for x in nl), default=0)
    r = dict(id=p['id'], cap=C, kind=p['kind'], job=p.get('job', -1), a=p['a'], b=p['b'], list_s=p['pred_s'], nodes=n, leaves=l, njobs=len(nl), maxnodes=mx)
    d = done.get(p['id'])
    if d: r.update(done=1, epred=d['pred_s'], cpu=d['cpu_s'], emit=d['emit_s'], kext=d['kext'])
    else: r['done'] = 0
    rows.append(r)
json.dump(rows, open('rows.json', 'w'))
print(len(rows), 'packages;', sum(r['done'] for r in rows), 'done in the cut list')
