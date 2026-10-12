#!/usr/bin/env python3
# cutgiant.py (reference copy): cuts an emitted giant EXT package into group packages (H + parts) and a final package (H + A + chunk).
# Regeneration does not need it: the emission spec and the group manifests of every cut family are shipped (inputs/ext/cut/).
# Reads $STORE (object store), $STORE_GET (download command of the cut packages), $QUEUE_PREFIX, $PIPELINE_DIR (objstore.py).
"""cutgiant.py ID [--groups N] [--prefix P]: the parts cut of an emitted giant EXT package.

A giant (H, P0..Pn, A, chunk; the parts depend on H only) whose emitted dir is stored as PREFIX/emitted/ID.tar.zst (+ ID.json with
its sha256) is cut into split lines of the queue:
  ID.sb0_<k>  (kind splitbuild)        manifest = H + a slice of the parts (balanced by pred_s); H is a table module without a .kman,
                                       so it is built in every group; the parts ship as the group's pubs;
  ID.sb       (kind splitbuild-final)  manifest = H + A + the chunk; deps = the groups, deps_pubs (A imports every part from the store).
Manifests go to PREFIX/splitbuild/ID/g0_<k>.jsonl and final.jsonl, the lines to PREFIX/splitbuild/ID/lines.jsonl (and stdout). The
final's id is registered in extscan's state/submitted.jsonl with the leaves of ID (so `extscan.py chunks` and aggauto take ID.sb as
that leaf's package: its chunk is the same module, PLE.c<cap>.X<hash>)."""
import sys, os, json, subprocess, hashlib, tempfile
sys.path.insert(0, os.environ.get('PIPELINE_DIR', '.')); import objstore
HERE = os.path.dirname(os.path.abspath(__file__))
B = os.environ.get('STORE')
a = sys.argv[1:]
pid = a[0]
N = int(a[a.index('--groups') + 1]) if '--groups' in a else 4
P = a[a.index('--prefix') + 1] if '--prefix' in a else os.environ.get('QUEUE_PREFIX')
DRY = '--dry' in a           # test: no uploads, no state change (with --obj OBJ --sha SHA: another emitted tarball)
if '--obj' in a:
    obj, sha = a[a.index('--obj') + 1], a[a.index('--sha') + 1]
else:
    meta = json.loads(objstore.get(B, '%s/emitted/%s.json' % (P, pid))[0])
    sha = meta.get('sha256') or meta.get('tar_sha256')
    obj = '%s/emitted/%s.tar.zst' % (P, pid)
d = tempfile.mkdtemp(prefix='cut_', dir='/tmp')
t = os.path.join(d, 'p.tar.zst')
objstore.download_file(B, obj, t)
got = hashlib.sha256(open(t, 'rb').read()).hexdigest()
assert got == sha, (got, sha)
mem = subprocess.run(['bash', '-c', 'zstd -dc %s | tar -tf - | grep -E "(^|/)manifest.jsonl$" | head -1' % t], capture_output=True, text=True).stdout.strip()
man = [json.loads(l) for l in subprocess.run(['bash', '-c', 'zstd -dc %s | tar -xOf - %s' % (t, mem)], capture_output=True, text=True).stdout.splitlines() if l.strip()]
os.remove(t)
H = [m for m in man if m.get('kind') == 'table']
parts = [m for m in man if m.get('kind') == 'part']
rest = [m for m in man if m.get('kind') not in ('table', 'part')]          # A (agg) and the chunk (glue)
assert len(H) == 1 and parts and any(m.get('kind') == 'agg' for m in rest), (len(H), len(parts), [m.get('kind') for m in rest])
# balance the parts over N groups by pred_s (greedy, largest first), each group keeps manifest order
bins = [[0.0, []] for _ in range(N)]
for i, m in sorted(enumerate(parts), key=lambda x: -float(x[1].get('pred_s', 60))):
    b = min(bins, key=lambda x: x[0]); b[0] += float(m.get('pred_s', 60)); b[1].append(i)
groups = [[parts[i] for i in sorted(b[1])] for b in bins if b[1]]
def upload_manifest(name, ms):
    p = os.path.join(d, name); open(p, 'w').write(''.join(json.dumps(m) + '\n' for m in ms))
    if not DRY: objstore.upload_file(B, '%s/splitbuild/%s/%s' % (P, pid, name), p)
    return '%s/splitbuild/%s/%s' % (P, pid, name)
# the closure parts that the EXT modules import (S4 and port modules), installed as the EXT bootstrap installs them (a machine that
# builds a cut group may never have run an EXT emission): the bootstrap minus its final exec line
_BOOT = open(os.path.join(HERE, 'extpkg_v11.sh')).read()
INSTALL = _BOOT[:_BOOT.rindex('exec python3')]
def emit(mobj, final):
    s = (INSTALL + '\n' + 'set -e; O="$1"; mkdir -p "$O"; $STORE_GET "$STORE" %s "$O/p.tar.zst"; [ "$(sha256sum "$O/p.tar.zst" | cut -c1-64)" = %s ]; '
         'zstd -dc "$O/p.tar.zst" | tar xf - -C "$O" --exclude=./run --exclude=./emit.log; rm -f "$O/p.tar.zst"; '
         '$STORE_GET "$STORE" %s "$O/manifest.jsonl"' % (obj, sha, mobj))
    if not final: s += '; rm -f "$O/DONE" "$O/kext.txt" "$O/inputs.sha256"'
    return dict(type='cmd', deps_first=False, manifest='manifest.jsonl', as_gb=31, argv=['bash', '-c', s, 'splitbuild', '{OUT}'])
lines = []
cap = pid.split('_')[1][1:] if pid.split('_')[1].startswith('c') else pid.split('_')[1]
gids = []
for k, g in enumerate(groups):
    gid = '%s.sb0_%d' % (pid, k); gids.append(gid)
    mobj = upload_manifest('g0_%d.jsonl' % k, H + g)
    lines.append(dict(id=gid, cap=cap, kind='splitbuild', tier='splitbuild', family=pid, parent=pid, split_of=pid,
                      pred_s=round(sum(float(m.get('pred_s', 60)) for m in H + g), 1), pred_gb_max=max(float(m.get('pred_gb', 1)) for m in H + g),
                      min_mem_gb=64, deps=[], deps_pubs=False, emit=emit(mobj, False)))
mobj = upload_manifest('final.jsonl', H + rest)
agb = max(float(m.get('pred_gb', 1)) for m in rest)
lines.append(dict(id=pid + '.sb', cap=cap, kind='splitbuild-final', tier='splitbuild', family=pid, parent=pid, split_of=pid,
                  pred_s=round(sum(float(m.get('pred_s', 60)) for m in H + rest), 1), pred_gb_max=agb, min_mem_gb=max(64, int(2 * agb + 16)),
                  deps=gids, deps_pubs=True, emit=emit(mobj, True),
                  pubs=[[m['module'], m['pub']] for m in rest if m.get('pub')]))
lp = os.path.join(d, 'lines.jsonl'); open(lp, 'w').write(''.join(json.dumps(x) + '\n' for x in lines))
if DRY:
    print('DRY: %s' % d); sys.exit(0)
objstore.upload_file(B, '%s/splitbuild/%s/lines.jsonl' % (P, pid), lp)
# register ID.sb as an attempt of ID's leaf in extscan's state (its chunk is the same module)
sub = {}
for l in open(os.path.join(HERE, 'state', 'submitted.jsonl')): x = json.loads(l); sub[x['id']] = x
if pid + '.sb' not in sub:
    base = dict(sub[pid]); base['id'] = pid + '.sb'; base['note'] = 'parts cut of %s (cutgiant.py): %d groups' % (pid, len(groups))
    base['split_of'] = pid
    with open(os.path.join(HERE, 'state', 'submitted.jsonl'), 'a') as f: f.write(json.dumps(base) + '\n')
print('cut %s: %d parts in %d groups (%s), final %s.sb (A pred_gb %.1f); lines: %s/splitbuild/%s/lines.jsonl in the store' % (
    pid, len(parts), len(groups), ', '.join(str(len(g)) for g in groups), pid, agb, P, pid))
