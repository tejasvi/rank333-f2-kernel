#!/usr/bin/env python3
"""splitbuild.py PKGDIR ID OBJ SHA OUTDIR [--group-s S] [--group-n N]: the BUILD of one emitted package spread over many
packages (the emission is reused as is: no re-emission, no closure or Lean change).
  PKGDIR  the emitted package (manifest.jsonl, src/, DONE, kext.txt, inputs.sha256), as uploaded to OBJ (sha256 SHA, a tar.zst
          that extracts to manifest.jsonl, src/, ... at its top level)
  waves   every non-table module gets wave 0 if it imports no other non-table module of the package, else 1 + the largest wave
          of those it imports; a module never imports one of its own wave
  groups  the leading waves whose predicted work exceeds 1.5 S are each cut into groups (about S predicted kernel s or N
          modules each); a group package builds its modules, every one a root (KPUB: leaf ranges, tops, aggregators), plus
          the split / heavy-leaf tables they import (no KPUB; rebuilt wherever needed, byte-identical since a table module is
          a function of its data file); its deps are the packages holding the modules its modules import (deps_pubs: their
          roots land in the store)
  final   all later waves, up to the original package's root (the pub of its DONE, alone in the last wave), in one package
          <ID>.sb, which keeps the original DONE and kext.txt, so agg_<C>h<J> takes <ID>.sb in place of <ID>
Writes OUTDIR/<ID>/g<w>_<i>.jsonl (the group manifests, to upload next to OBJ) and OUTDIR/<ID>.lines.jsonl (the queue lines; the
emission downloads OBJ and its group manifest from MANPFX, given by --manpfx)."""
import sys, os, re, json, argparse, collections
ap = argparse.ArgumentParser()
ap.add_argument('pkg'); ap.add_argument('id'); ap.add_argument('obj'); ap.add_argument('sha'); ap.add_argument('out')
ap.add_argument('--group-s', type=float, default=40000.0); ap.add_argument('--group-n', type=int, default=1500)
ap.add_argument('--manpfx', required=True, help='STORE/PATH: the group manifests are stored as MANPFX/<ID>/g<w>_<i>.jsonl')
ap.add_argument('--tier', default='splitbuild')
ap.add_argument('--raw-gb', type=float, default=0.0, help='the extracted size of OBJ without run/ and emit.log (each package extracts all of it)')
a = ap.parse_args()
M = [json.loads(l) for l in open(os.path.join(a.pkg, 'manifest.jsonl')) if l.strip()]
by = {m['module']: m for m in M}
done = json.load(open(os.path.join(a.pkg, 'DONE')))
assert len(done['pubs']) == 1, done['pubs']; root = done['pubs'][0][0]
tables = {m['module'] for m in M if m['kind'] == 'table'}
def kax(m):
    t = open(os.path.join(a.pkg, m['src'])).read()
    r = re.findall(r'^#kax (\S+)', t, re.M)
    assert r, 'no #kax in %s' % m['module']; return r[0]
# build cost per module as measured in production (w1_23429.sb1_2): leaf ranges about their pred_s; tops about 5.6x
# their pred_s; tables and aggregators about 9-10 s each (pred 1 s); a top or range also pulls its split table into its group
def cost(k):
    m = by[k]; kd = m['kind']
    if kd == 'table': return 9.0
    if kd == 'agg': return 10.0
    if kd == 'top': return 5.6 * m['pred_s'] + 9.0 + 9.0
    return m['pred_s'] + 9.0
wave = {}
def W(k):
    if k not in wave:
        nd = [d for d in by[k]['deps'] if d in by and d not in tables]
        wave[k] = 0 if not nd else 1 + max(W(d) for d in nd)
    return wave[k]
sys.setrecursionlimit(100000)
for k in by:
    if k not in tables: W(k)
last = max(wave.values()); assert wave[root] == last and [k for k in wave if wave[k] == last] == [root], ('the root is not alone in the last wave', root)
for k in by:   # tables import no module of the package
    if k in tables: assert not [d for d in by[k]['deps'] if d in by], k
os.makedirs(os.path.join(a.out, a.id), exist_ok=True)
groups = []   # (wave, index, [modules]); the final package is (last, 0)
wsum = collections.defaultdict(float)
for k, w in wave.items(): wsum[w] += cost(k)
split_upto = 0
while split_upto < last and wsum[split_upto] > 1.5 * a.group_s: split_upto += 1   # waves 0 .. split_upto-1 are cut into groups
for w in range(split_upto):
    ms = sorted((k for k in wave if wave[k] == w), key=lambda k: -cost(k))
    ng = max(1, int(-(-wsum[w] // a.group_s)), -(-len(ms) // a.group_n))
    bins = [[] for _ in range(ng)]; load = [0.0] * ng
    for k in ms:   # largest first into the lightest group
        i = min(range(ng), key=lambda j: load[j]); bins[i].append(k); load[i] += cost(k)
    groups += [(w, i, b) for i, b in enumerate(bins) if b]
groups.append((last, 0, sorted(k for k in wave if wave[k] >= split_upto)))
gid = {}
for w, i, ms in groups:
    for k in ms: gid[k] = (w, i)
def pid(w, i): return '%s.sb' % a.id if w == last else '%s.sb%d_%d' % (a.id, w, i)
lines = []
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sbtables
extra_tables = sbtables.checked_tables(by, a.pkg)   # tables the package's audit imports through checked lifted modules (KModTyChk)
for w, i, ms in groups:
    need_t = sorted({d for k in ms for d in by[k]['deps'] if d in tables} | extra_tables(ms))
    rows = [dict(by[t]) for t in need_t]
    for r in rows: r.pop('pub', None)
    final = (w == last)
    for k in sorted(ms, key=lambda k: wave[k]):
        r = dict(by[k]); r.pop('pub', None)
        if not final or k == root: r['pub'] = kax(by[k])   # group modules are all roots; the final package's root is the package's
        rows.append(r)
    deps = sorted({pid(*gid[d]) for k in ms for d in by[k]['deps'] if d in gid and gid[d] != (w, i)})
    mf = os.path.join(a.out, a.id, 'g%d_%d.jsonl' % (w, i))
    open(mf, 'w').write(''.join(json.dumps(r) + '\n' for r in rows))
    script = ('set -e; O="$1"; mkdir -p "$O"; $FETCH %s "$O/p.tar.zst"; '
              '[ "$(sha256sum "$O/p.tar.zst" | cut -c1-64)" = %s ]; zstd -dc "$O/p.tar.zst" | tar xf - -C "$O" --exclude=./run --exclude=./emit.log; rm -f "$O/p.tar.zst"; '
              '$FETCH %s/%s/g%d_%d.jsonl "$O/manifest.jsonl"%s') % (
              a.obj, a.sha, a.manpfx, a.id, w, i,
              '' if final else '; rm -f "$O/DONE" "$O/kext.txt" "$O/inputs.sha256"')
    pred = round(sum(cost(k) - (9.0 if by[k]['kind'] in ('top', 'leafrange', 'leaf-range') else 0.0) for k in ms) + 9.0 * len(need_t), 1)   # measured costs
    gb = max([by[k].get('pred_gb', 1.0) for k in ms] + [by[t].get('pred_gb', 0.45) for t in need_t] + [1.0])
    disk = round(a.raw_gb + 0.004 * len(rows) + 2.0, 1)   # the whole extracted package, its outputs, and the tarball before extraction
    lines.append(dict(id=pid(w, i), cap=str(done['cap'])[1:] if str(done['cap']) in ('c436', 'c422') else str(done['cap']), kind='splitbuild-final' if final else 'splitbuild', tier=a.tier,
                      pred_s=pred, pred_gb_max=round(gb + 0.5, 2), min_mem_gb=round(2 * gb + 16, 1), disk_gb=disk, family=a.id,
                      deps=deps, deps_pubs=True, parent=a.id,
                      emit=dict(type='cmd', deps_first=False, manifest='manifest.jsonl', as_gb=40,
                                argv=['bash', '-c', script, 'splitbuild', '{OUT}'])))
with open(os.path.join(a.out, '%s.lines.jsonl' % a.id), 'w') as f:
    for d in lines: f.write(json.dumps(d) + '\n')
c = collections.Counter(w for w, i, ms in groups if w != last)
print('%s: %d modules (%d tables) in %d waves; waves 0..%d cut into %d group packages (per wave %s); final %s with %d modules, %.0f s; '
      'predicted %.0f s in all, max group %.0f s' % (a.id, len(M), len(tables), last + 1, split_upto - 1, sum(c.values()), dict(sorted(c.items())),
      pid(last, 0), len(groups[-1][2]), lines[-1]['pred_s'], sum(d['pred_s'] for d in lines), max(d['pred_s'] for d in lines[:-1]) if len(lines) > 1 else 0))
