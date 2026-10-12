#!/usr/bin/env python3
"""mkaggplan.py QUEUE.jsonl OUT.jsonl TOOLSDIR: the aggregation packages of c436, c422 and the point tier, as queue lines of
the Phase-B worker (deps with deps_pubs, emit deps_first: each dependency's root modules in the store, its DONE / kext.txt in
{DEPS}/<id>/), all on the tools tree TOOLSDIR:
  agg_<C>h<J>   per heavy depth-6 job J of cap C: mkagg --heavy-only over J's packages (heavy-sub and heavy-split of the cut
                list): aggregators, J's top chain over KH.S<C>_<J> and its range [J, J+1) over KH.HT<C> (pub KJ.agg<C>h<J>.R.ok;
                its DONE is also the range [J, J+1));
  agg_<C>_root  per cap: mkagg in the plain mode over the cap's range and split packages and its agg_<C>h<J> packages (every
                dependency a range of depth-6 jobs): the root range aggregators and KJ.agg<C>_Root (#e1groot, about 7 min); exports
                Root<C>.ext.txt (the root's external-leaf list, for the EXT tops; also KROOTEXT lines in its log);
  agg_ptc       the point tier: mkagg ptc over the 84 pt_*.v8 packages: KJ.aggptc_A (root range over E1P.Rptc_HT) and
                KJ.aggptc_Point (`KJ.aggptc.point`).
No step needs private parts or main.  The point packages are taken from the queue (ids pt_*.v8), the others from the cut list."""
import sys, json, collections
import os
R22 = os.environ.get('R22_ROOT', '.')   # the development layout's root (package mode does not use it)
Q, OUT, T = sys.argv[1], sys.argv[2], sys.argv[3].rstrip('/')
P = R22 + '/e1g/pkg/'
SCRIPT = ('set -e; export PYTHONDONTWRITEBYTECODE=1; '
          'exec python3 %s/py/mkagg.py "$1" "$2" "$3" --tools %s ${4:+"$4"}' % (T, T))
def line(id_, cap, kind, deps, pred_s, gb, mode, export=None):
    d = dict(id=id_, cap=cap, kind=kind, tier='agg' + cap, pred_s=pred_s, pred_gb_max=gb, deps=deps, deps_pubs=True,
             emit=dict(type='cmd', deps_first=True, manifest='manifest.jsonl', as_gb=40,
                       argv=['bash', '-c', SCRIPT, 'mkagg', cap, '{OUT}', '{DEPS}'] + ([mode] if mode else [])))
    if export: d['export'] = export
    return d
cut = [json.loads(l) for l in open(P + 'wave1_packages.jsonl')]
heavy = [json.loads(l) for l in open(P + 'wave1_packages_heavy.jsonl')]
byJ = collections.defaultdict(list); light = collections.defaultdict(list)
for p in cut:
    if p['kind'] in ('heavy-sub', 'heavy-split'): byJ[(p['cap'], p['job'])].append(p)
    else: light[p['cap']].append(p['id'])
lines = []
for h in heavy:
    C, J = h['cap'], h['job']; ps = sorted(byJ[(C, J)], key=lambda p: p['a'])
    assert ps and ps[0]['a'] == 0 and all(ps[i]['a'] == ps[i - 1]['b'] for i in range(1, len(ps))) and ps[-1]['b'] == h['subjobs'], (C, J)
    nag = -(-len(ps) // 100) + (1 if len(ps) > 100 else 0)
    lines.append(line('agg_%sh%d' % (C, J), C, 'agg-heavy', [p['id'] for p in ps], round(120 + 10 * nag + 0.05 * len(ps), 1), 4.0, '--heavy-only'))
for C, rp in (('436', 1000.0), ('422', 600.0)):
    deps = sorted(light[C]) + ['agg_%sh%d' % (C, h['job']) for h in heavy if h['cap'] == C]
    lines.append(line('agg_%s_root' % C, C, 'agg-root', deps, rp, 8.0, None, export=['Root%s.ext.txt' % C]))
pt = sorted((json.loads(l) for l in open(Q) if l.strip() and json.loads(l)['id'].startswith('pt_') and json.loads(l)['id'].endswith('.v8')),
            key=lambda p: p['a'])
assert len(pt) == 84 and pt[0]['a'] == 0 and all(pt[i]['a'] == pt[i - 1]['b'] for i in range(1, len(pt))) and pt[-1]['b'] == 2352, 'pt_*.v8 coverage'
lines.append(line('agg_ptc', 'ptc', 'agg-point', [p['id'] for p in pt], 120.0, 4.0, None))
with open(OUT, 'w') as f:
    for d in lines: f.write(json.dumps(d) + '\n')
c = collections.Counter(d['kind'] for d in lines)
print('%d aggregation packages: %s; deps: heavy %d, roots %s, point %d' % (len(lines), dict(c), sum(len(d['deps']) for d in lines if d['kind'] == 'agg-heavy'),
      [len(d['deps']) for d in lines if d['kind'] == 'agg-root'], len(lines[-1]['deps'])))
