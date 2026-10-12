#!/usr/bin/env python3
"""mkpkgw.py OUT PREFIX BUNDLE "T0 T1 T2": the worker-side part of case-II package emission (emitcc.sh step 4), in the package dir
OUT after py/mkslice2.py and the rekey top:
- manifest.jsonl: one cmd unit per module, `./kmod_unit.sh <module>`, cwd ".", env KMOD_OUT={STORE}; tier caseII; kind heavy | light
  | agg | top; deps (in-package); records; wave; pred_s / pred_gb by runs/reh/mkpkg2.py's CC model (items: 11.8 + 0.586 x predicted kernel
  s + 1.433 per 1,000 records + 2,773 x input GB - 47 per 100 items, at least 8 s; peak + 0.5 GB; agg / top: 8 s + 20 ms per item,
  1.8 GB); "pub" on <PREFIX>.Top (its .cov: the job roots' minimal keys);
- kmod_unit.sh, tools/kmod_build.sh and tools/nothp.py (the bundle's pinned copies), lpath_common.txt (the library closure's line);
- emit.json: the bundle version and the sha256 of the generator, glue, recipe and table files, recipecheck's output, the job / item /
  record counts, the generation, conversion and emission times, and the converted bytes.
Every manifest row records the emitting bundle's version ("bundle"). The case-II join (py/joinemit.py, OUT/join.json present): "pub" on
<PREFIX>.Top.segs (AllL SegsOfKeyCC over the roots' minimal keys); emit.json takes join.json's counts, the pcerts' sha256 and the
phase-0 recipecheck output (OUT/p0/recipecheck.txt)."""
import sys, os, json, shutil, hashlib, glob
out, pfx, B, ts = sys.argv[1], sys.argv[2], sys.argv[3], [int(x) for x in sys.argv[4].split()]
R = B + '/r22'; VER = open(B + '/VERSION').read().strip() if os.path.exists(B + '/VERSION') else '-'
JOIN = json.load(open(out + '/join.json')) if os.path.exists(out + '/join.json') else None
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''): h.update(b)
    return h.hexdigest()
waves = [l.split() for l in open('%s/src/%s_waves.txt' % (out, pfx)) if l.strip()]
rows = {l.split('\t')[0]: l.rstrip('\n').split('\t') for l in open(out + '/src/manifest.tsv') if l.startswith(pfx + '.')}
mods = [m for w in waves for m in w]; inpkg = set(mods); man = []
for w, ms in enumerate(waves):
    for m in ms:
        r = rows[m]; kind = r[1]; nit = int(r[2]); recs = int(r[3]); ks = float(r[4]); gb = float(r[5]); ingb = int(r[6]) / 1e9
        if kind == 'items': kind = 'heavy' if gb - 1.2 - 35.0 * ingb > 1.58 else 'light'
        agg = kind in ('agg', 'top'); lazy = os.path.exists('%s/src/%s.items' % (out, m.replace('.', '/')))
        if lazy: kind = 'light' if gb + 0.5 <= 6 else 'heavy'
        ps = 8.0 + 0.02 * nit if agg else (ks if lazy else max(8.0, 11.8 + 0.586 * ks + 1.433 * recs / 1000 + 2773.0 * ingb - 47.0 * nit / 100))
        row = dict(module=m, cmd='./kmod_unit.sh %s' % m, cwd='.', env={'KMOD_OUT': '{STORE}'}, tier='caseII', kind=kind,
                   deps=[x for x in r[7].split(',') if x in inpkg], pred_s=round(ps, 1), pred_gb=round(1.8 if agg else gb + 0.5, 2),
                   records=recs, wave=w, bundle=VER)
        if m == pfx + '.Top': row['pub'] = pfx + ('.Top.segs' if JOIN else '.Top.cov')
        man.append(row)
imported = set(d for r in man for d in r['deps'])
tops = [r['module'] for r in man if r['module'] not in imported]
assert tops == [pfx + '.Top'], 'one top-level module expected: %s' % tops[:5]
open(out + '/manifest.jsonl', 'w').write(''.join(json.dumps(x) + '\n' for x in man))
os.makedirs(out + '/tools', exist_ok=True)
for f in ('kmod_build.sh', 'nothp.py'): shutil.copy2(R + '/lean/leaf2/kmod/tools/' + f, out + '/tools/' + f)
open(out + '/lpath_common.txt', 'w').write(open(B + '/lpath_common.txt').read().replace('@CLOSURE_ROOT@', os.environ['CLOSURE_ROOT']).replace('@LEAN_TOOLCHAIN@', os.environ.get('LEAN_TOOLCHAIN', '')))
open(out + '/kmod_unit.sh', 'w').write('''#!/bin/bash
# kmod_unit.sh MODULE: one unit of a kinds case-II package. An item module (src/<MODULE>.items exists) first converts its items
# (the bundle's py/unitconv.py: itembin + pcseg + kitem + itemkey from the package's segments, keys checked, real source written);
# then the pinned kmod_build.sh (THP off, RLIMIT_AS 64 GiB, nice 10) on src/<MODULE>.lean from the package root writes the module's
# .olean, .ilean and .kman to KMOD_OUT (the scheduler's store) and deletes the private olean after a clean audit; then the module's
# converted items are deleted. Env KINDS_BUNDLE (the emitter bundle directory), CLOSURE_ROOT and LEAN_TOOLCHAIN (lpath_common.txt placeholders).
D=$(dirname "$(readlink -f "$0")"); M=$1; MP=$(echo $M | tr . /)
: ${KMOD_OUT:?KMOD_OUT unset} ${KMOD_LEAN:=lean}
KB=${KINDS_BUNDLE:?set KINDS_BUNDLE to the emitter bundle directory}; export KINDS_R22=$KB/r22 LD_LIBRARY_PATH=$KB/bin${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
if [ -f "$D/src/$MP.items" ]; then ${KPY:-python3} "$KINDS_R22/lean/kinds/py/unitconv.py" "$D" "$M" || exit 1; fi
export KMOD_SRC=$D/src KMOD_LOG=${KMOD_LOG:-$D/log} KMOD_LEAN KMOD_OUT KMOD_LEAN_PATH=${LEAN_PATH:-$(cat $D/lpath_common.txt)}
cd "$D" && bash "$D/tools/kmod_build.sh" "$M"; rc=$?
[ -f "$D/src/$MP.items" ] && awk '{print "data/q/"$1".d"}' "$D/src/$MP.items" | (cd "$D" && xargs -r rm -rf)
exit $rc
''')
os.chmod(out + '/kmod_unit.sh', 0o755)
if JOIN:
    spec = dict(jobs=[None] * JOIN['jobs']); nitems = JOIN['segments']; cbytes = sum(os.path.getsize(p) for p in glob.glob(out + '/p0/seg_*.r3'))
else:
    spec = json.load(open(out + '/spec.json'))
    nitems = sum(1 for l in open(out + '/q/plan.txt') if l.startswith('I '))
    cbytes = sum(os.path.getsize(p) for p in glob.glob(out + '/q/h*/pc.r3.xq'))   # the segments kept for the units
info = dict(prefix=pfx, bundle=VER,
            sha256={k: sha(p) for k, p in (('prof7R3q_b12d', R + '/xq/r3q/bin/prof7R3q_b12d'), ('r3qglue', R + '/xq/r3q/bin/r3qglue'),
                                           ('recipe', R + '/lean/kinds/runs/xqcc/recipe_cc.txt' if JOIN else out + '/q/recipe_cc.txt'),
                                           ('tab', R + '/lean/kinds/data/cc/cc436_422/tab_cc436_422.bin'),
                                           ('kept', R + '/lean/kinds/data/cc/cc436_422/kept_cc436_422.txt'),
                                           ('c2t', R + '/lean/kinds/data/cc/cc436_422/cc436_422.c2t'),
                                           ('lab', R + '/lean/kinds/data/cc/cc436_422/keptcc436_422_lab.bin'))},
            recipecheck=open(out + ('/p0/recipecheck.txt' if JOIN else '/q/recipecheck.txt')).read().strip(), jobs=len(spec['jobs']), items=nitems,
            records=sum(r['records'] for r in man), units=len(man), converted_bytes=cbytes,
            gen_s=ts[1] - ts[0], conv_s=ts[2] - ts[1], pred_s=round(sum(r['pred_s'] for r in man), 1), max_pred_gb=max(r['pred_gb'] for r in man))
if JOIN: info['join'] = JOIN
json.dump(info, open(out + '/emit.json', 'w'), indent=1)
print('%s: %d jobs, %d items, %d records, %d units, predicted %.0f s, max pred_gb %.2f, converted %.1f GB, gen %d s, conv %d s' % (
    pfx, info['jobs'], nitems, info['records'], len(man), info['pred_s'], info['max_pred_gb'], cbytes / 1e9, info['gen_s'], info['conv_s']))
