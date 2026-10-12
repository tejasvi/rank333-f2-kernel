#!/usr/bin/env python3
"""mkpkg2.py STAGE PREFIX [--meas RESULTS] TRACE...: stage-2 package (module-path case-II slice) in the layout
(konly/reh/stage1_setup.sh): STAGE is tarred as pkg_kmod_cc.tar.zst, and the build machine extracts it to $KP/kmod_cc.

STAGE must already hold (runs/reh/mkstage2.sh):
- data/: the items, as hard links;
- src/<PREFIX>/: py/mkslice2.py's sources, generated in STAGE with relative item dirs (data/...) and SPECROOT=src;
- src/manifest.tsv and src/<PREFIX>_waves.txt.

This script adds:
- manifest.jsonl: one cmd unit per module, `./kmod_unit.sh <module>` with cwd "." and env KMOD_OUT={STORE}. Fields:
  - tier caseII; kind heavy | light | agg | top; deps (in-package modules only); records; "pub" on the top line;
  - pred_s, s on the build machine, close to isolated. For item modules, the fit on the stage-2 local test (45 item modules at 16 slots, the build machine's
    other load about 60 of 384 cores; residual sd 4.1 s): 11.8 + 0.586 x predicted kernel s + 1.433 per 1,000 records + 2,773 x
    input GB - 47 per 100 items, at least 8 s. That load is close to isolated: the job C0_C416266 took 431 s here and 418 s built
    6 at a time. For agg/top: 8 s + 20 ms per item;
  - pred_gb, peak anonymous GB: mkimod.py's module-path model + 0.5 GB margin (the fit's largest residual was 0.58 GB); 1.8 for
    agg/top (measured 1.1-1.6). With --meas RESULTS (a sched.py results.jsonl of this package on the build machine), at least 1.1 x the
    measured peak, and the line also records main_s / main_gb (measured wall and peak RssAnon);
  - kind heavy: the largest batch is predicted over 1.58 GB (py/mkslice2.py's heavy class), else light;
- kmod_unit.sh, plus tools/kmod_build.sh and tools/nothp.py (pinned copies of leaf2/kmod/tools);
- root/<abs>: every module the traced builds (strace openat; one item module, one aggregator, the top) opened under the own roots,
  except generated slices (KM*). From the port build only .olean and .ir: the builds and an in-process #kax never read the port's
  .olean.private / .olean.server (tested: an item module, an aggregator and the top build with clean manifests without them; they
  are 13 GB). kmod_audit.py's external walk needs them, so it runs where the full port is (main). From the other roots, all siblings
  except .ilean;
- lpath_common.txt: the own roots, then Mathlib and core (port/out/tools/lp_mod.sh), all under @CLOSURE_ROOT@. kinds/mod2/build has
  only kinds-only module names (KB, KDK, KDK321; mod/rename.py) and imports the port's KD / KD321 from the port build, so no two roots
  share a top-level directory and the order is free;
- README.txt.

Split cases (py/splitpkg.py): a leaf package has no top module; its one unimported module is its root chunk, and "pub" is that
chunk's `<A>.cov`. A join package imports other packages' root chunks; its README names them (env PKG_NOTE).
env PKG_CLOSURE=DIR: take root/ and lpath_common.txt from DIR (a prepared closure: DIR/root, DIR/lpath_common.txt) instead of tracing,
e.g. on a machine without the port build; PKG_ROOT=0 leaves root/ out (the consumer's closure has it)."""
import sys, os, re, json, shutil, subprocess
L = os.environ.get('KINDS_R22', '.') + '/lean/'
OWN_ROOTS = [L + 'kinds/mod2/build', L + 's443/mod/build', L + 'leaf2/kmod/build', L + 'native/infra/port/out/build']
EXTS = ('.olean', '.olean.server', '.olean.private', '.ir', '.ilean')
PORT = L + 'native/infra/port/out/build'
def exts_of(stem): return ('.olean', '.ir') if stem.startswith(PORT + '/') else ('.olean', '.olean.server', '.olean.private', '.ir')
GEN = re.compile(r'^KM[A-Z0-9]*/')
st, pfx, traces = os.path.abspath(sys.argv[1]), sys.argv[2], sys.argv[3:]
meas = {}
if traces and traces[0] == '--meas':
    for l in open(traces[1]):
        x = json.loads(l)
        if x.get('exit') == 0: meas[x['module']] = x
    traces = traces[2:]
def link(a, b):
    os.makedirs(os.path.dirname(b), exist_ok=True)
    if os.path.exists(b): return
    try: os.link(a, b)
    except OSError: shutil.copy2(a, b)
# manifest
waves = [l.split() for l in open('%s/src/%s_waves.txt' % (st, pfx)) if l.strip()]
rows = {l.split('\t')[0]: l.rstrip('\n').split('\t') for l in open(st + '/src/manifest.tsv') if l.startswith(pfx + '.')}
mods = [m for w in waves for m in w]
inpkg = set(mods); out = []
for w, ms in enumerate(waves):
    for m in ms:
        r = rows[m]; kind = r[1]; nit = int(r[2]); recs = int(r[3]); ks = float(r[4]); gb = float(r[5]); ingb = int(r[6]) / 1e9
        if kind == 'items': kind = 'heavy' if gb - 1.2 - 35.0 * ingb > 1.58 else 'light'
        deps = [x for x in r[7].split(',') if x in inpkg]
        agg = kind in ('agg', 'top')
        if os.environ.get('PKG_MODEL') == '321':   # py/mkimod321.py's models: 20 s of module overhead + its predicted s
            ps = 8.0 + 0.02 * nit if agg else 20.0 + ks
        else:
            ps = 8.0 + 0.02 * nit if agg else max(8.0, 11.8 + 0.586 * ks + 1.433 * recs / 1000 + 2773.0 * ingb - 47.0 * nit / 100)
        pg = 1.8 if agg else gb + 0.5
        row = dict(module=m, cmd='./kmod_unit.sh %s' % m, cwd='.', env={'KMOD_OUT': '{STORE}'}, tier=os.environ.get('PKG_TIER', 'caseII'), kind=kind, deps=deps,
                   pred_s=round(ps, 1), pred_gb=round(pg, 2), records=recs, wave=w)
        if m in meas:
            x = meas[m]; row['pred_gb'] = round(max(pg, 1.1 * x['max_anon_gb']), 2)
            row['main_s'] = round(x['wall'], 1); row['main_gb'] = round(x['max_anon_gb'], 3)
        if kind == 'top':
            mv = re.search(r'^#kmVI321 (\S+) ', open('%s/src/%s.lean' % (st, m.replace('.', '/'))).read(), re.M)
            row['pub'] = mv.group(1) if mv else '%s.segs' % m
        out.append(row)
imported = set(d for r in out for d in r['deps'])
tops = [r for r in out if r['module'] not in imported]
assert len(tops) == 1, 'one top-level module expected: %s' % [r['module'] for r in tops][:5]
if 'pub' not in tops[0]:   # a leaf package of a split case: its root chunk
    assert tops[0]['kind'] == 'agg'; tops[0]['pub'] = '%s.cov' % tops[0]['module']
PUB = tops[0]['pub']
open(st + '/manifest.jsonl', 'w').write(''.join(json.dumps(x) + '\n' for x in out))
# tools and the unit wrapper
os.makedirs(st + '/tools', exist_ok=True)
for f in ('kmod_build.sh', 'nothp.py'): shutil.copy2(L + 'leaf2/kmod/tools/' + f, st + '/tools/' + f)
open(st + '/kmod_unit.sh', 'w').write('''#!/bin/bash
# kmod_unit.sh MODULE: one unit of a stage-2 case-II slice. Runs the pinned kmod_build.sh (THP off, RLIMIT_AS 64 GiB, nice 10)
# on src/<MODULE>.lean, from the package root: the sources read data/... and src/... relative to it.
# - Writes the module's .olean, .ilean and .kman manifest (KPUB, KAX, KAXSUM, KAXP, KTIME, KSHA) to KMOD_OUT, the scheduler's store
#   (env "KMOD_OUT": "{STORE}"). The private olean is deleted after a clean audit.
# - Imports resolve through KMOD_OUT first, then LEAN_PATH (the scheduler's: lpath_common.txt + store).
# - Lean: KMOD_LEAN, default the toolchain under @CLOSURE_ROOT@.
D=$(dirname "$(readlink -f "$0")")
: ${KMOD_OUT:?KMOD_OUT unset} ${KMOD_LEAN:=lean}
export KMOD_SRC=$D/src KMOD_LOG=${KMOD_LOG:-$D/log} KMOD_LEAN KMOD_OUT KMOD_LEAN_PATH=${LEAN_PATH:-$(cat $D/lpath_common.txt)}
cd "$D" && exec bash "$D/tools/kmod_build.sh" "$1"
''')
os.chmod(st + '/kmod_unit.sh', 0o755)
# closure
CLOS = os.environ.get('PKG_CLOSURE')
stems = set()
for t in ([] if CLOS else traces):
    for ln in open(t):
        if 'ENOENT' in ln: continue
        mm = re.search(r'"(/[^"]+)"', ln)
        if not mm: continue
        p = mm.group(1)
        for root in OWN_ROOTS:
            if p.startswith(root + '/'):
                rel = p[len(root) + 1:]
                if GEN.match(rel): break
                for e in EXTS:
                    if p.endswith(e): stems.add(p[:-len(e)]); break
                break
nf = 0; nb = 0; used = set()
if CLOS:
    if os.environ.get('PKG_ROOT', '1') != '0':
        for dp, dn, fn in os.walk(CLOS + '/root'):
            for f in fn:
                a = os.path.join(dp, f); link(a, st + '/root' + a[len(CLOS + '/root'):]); nf += 1; nb += os.path.getsize(a)
    shutil.copy2(CLOS + '/lpath_common.txt', st + '/lpath_common.txt')
    roots = [r[len('@CLOSURE_ROOT@'):] for r in open(CLOS + '/lpath_common.txt').read().strip().split(':') if r[len('@CLOSURE_ROOT@'):] in OWN_ROOTS]
for s in sorted(stems):
    for e in exts_of(s):
        if os.path.exists(s + e):
            link(s + e, st + '/root' + s + e); nf += 1; nb += os.path.getsize(s + e)
    used.update(r for r in OWN_ROOTS if s.startswith(r + '/'))
if not CLOS:
    roots = [r for r in OWN_ROOTS if r in used]
    ext = subprocess.run([L + 'native/infra/port/out/tools/lp_mod.sh'], capture_output=True, text=True, check=True).stdout.strip().split(':')
    open(st + '/lpath_common.txt', 'w').write(':'.join(['@CLOSURE_ROOT@' + r for r in roots + ext]) + '\n')
assert roots[0] == L + 'kinds/mod2/build'
kinds = {}
for r in out: kinds[r['kind']] = kinds.get(r['kind'], 0) + 1
items = sum(int(rows[m][2]) for m in mods if rows[m][1] == 'items'); recs = sum(r['records'] for r in out)
DESC = os.environ.get('PKG_DESC', "the module-path case-II slice %s on the CC route's table 436+422" % pfx)
NAME = os.environ.get('PKG_NAME', 'pkg_kmod_cc')
open(st + '/README.txt', 'w').write(('''Package ''' + NAME + ''': ''' + DESC + ''', in the package layout.
- Contents: %d items with %d records in %d item modules, Cov aggregators (children before parents), and the top-level
  module %s (pub %s).
- Units: manifest.jsonl, cmd units `./kmod_unit.sh <module>` with cwd "." and env KMOD_OUT={STORE}. kmod_build.sh writes each module's
  .olean and .kman to the store. Each line has deps, pred_s, pred_gb, kind (heavy | light | agg | top) and records.
''' + ('''- root/: kinds/mod2/build (the case-II library: KB, KDK, KDK321), plus the other module files the builds open (traced): port modules as
  .olean + .ir.''' if nf else '''- root/: not in this package. The shared closure (pkg_kmod_321_closure: root/ + lpath_common.txt, the same files) provides
  it; merge its root/ into @CLOSURE_ROOT@ once per machine.''') + '''
- Module names: every module name maps to one file. The rebuilt XComp / XBatch (and XBatchO / LoadXB, which import them) and its
  KD / KD321 additions carry kinds-only names KDK.* / KDK321.*; the port's unchanged KD / KD321 modules come from the port build. The
  LEAN_PATH order is free.
- Audit on the build machine: the module graph only, with kmod_audit.py --root %s --build <store> --no-ext. The external walk checks
  Mathlib, core and port obligations with KModExt at the private level. It needs the port's .olean.private files, which this package
  leaves out (13 GB), so it runs where the full port build is installed.
''') % (items, recs, kinds.get('heavy', 0) + kinds.get('light', 0), tops[0]['module'], PUB, tops[0]['module']) + os.environ.get('PKG_NOTE', '') + os.environ.get('PKG_TEST', ''))
print('%s: %d units %s; %d items, %d records; predicted %.0f s, max pred_gb %.2f; closure %d files (%.1f MB) in roots %s' % (
    st, len(out), kinds, items, recs, sum(r['pred_s'] for r in out), max(r['pred_gb'] for r in out), nf, nb / 1e6,
    [r[len(L):] for r in roots]))
