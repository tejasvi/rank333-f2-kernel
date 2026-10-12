#!/usr/bin/env python3
"""kmod_audit_obl.py --root MOD --build DIR [--build DIR ...] [--keys FILE] [--ext-out FILE] [--no-ext] [--obl-out FILE]

The top-level step of the KMod compositional axiom audit (the KMod library's kmod_audit.py with --obl-out: the obligations left for
the external step are written to a file, for final_ext.py).  Reads every <module>.kman under the build
dirs and walks the module graph down from the root through the obligations:
  * every reached module must have a manifest with a KPUB line and, for each KPUB theorem, a KAXSUM with bad=0 and
    local_axioms=0 (and no KAX BAD line);
  * an obligation `KAX OBL <N> <c>` with N a KMod module (it has a manifest) must name one of N's KPUB theorems, or an
    external-leaf list `NS.EXT` that occurs in the statement of one of N's KPUB theorems (checked in Lean at the exported level,
    queue/KModTyChk.lean: N's own walk of that theorem entered the list, value included); N is then walked in turn;
  * the other obligations (vocabulary, Mathlib, core) are collected and checked by the external walk queue/KModExt.lean
    (`lean --run`, every module at the private level; LEAN_PATH = the build dirs + $KMOD_LEAN_PATH), which must report bad=0;
  * the root's KAXP line, if any (Lean's own collectAxioms), must list only propext, Classical.choice, Quot.sound.
Optional: --keys FILE (all keys of the frontier, one per line, in order): the KKEY ranges [first, last] of the reached modules
must partition the list exactly.  --ext-out FILE: the KEXT labels of the reached modules (`<module> <label>` per line).
Prints totals (modules, units, kernel ms, wall, max RSS) and PASS/FAIL; exit status 0 iff PASS.  Lean: $KMOD_LEAN, else kitenv's
PB_LEAN."""
import argparse, os, subprocess, sys, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'queue'))
import kitenv as KE
STD = {'propext', 'Classical.choice', 'Quot.sound'}
ap = argparse.ArgumentParser()
ap.add_argument('--root', required=True); ap.add_argument('--build', action='append', required=True)
ap.add_argument('--keys'); ap.add_argument('--ext-out'); ap.add_argument('--obl-out'); ap.add_argument('--no-ext', action='store_true')
a = ap.parse_args()
TOOLS = KE.QUEUE          # KModTyChk.lean, KModExt.lean
LEAN = os.environ.get('KMOD_LEAN', KE.LEAN)

def parse(path):
    m = {'pub': [], 'sum': {}, 'obl': [], 'bad': [], 'kaxp': {}, 'keys': [], 'ext': [], 'units': 0, 'kms': 0, 'wall': 0.0,
         'rss': 0, 'path': path}
    for line in open(path):
        f = line.split()
        if not f: continue
        t = f[0]
        if t == 'KMOD': m['name'] = f[1]
        elif t == 'KPUB': m['pub'].append(f[1])
        elif t == 'KAXSUM':
            kv = dict(x.split('=', 1) for x in f[2:] if '=' in x); m['sum'][f[1]] = kv
        elif t == 'KAX' and f[1] == 'OBL': m['obl'].append((f[2], f[3]))
        elif t == 'KAX' and f[1] == 'BAD': m['bad'].append(' '.join(f[2:]))
        elif t == 'KAXP': m['kaxp'][f[1]] = set(f[2].split(',')) if len(f) > 2 and f[2] else set()
        elif t == 'KKEY': m['keys'].append((f[1], f[2]))
        elif t == 'KEXT': m['ext'].append(' '.join(f[1:]))
        elif t == 'KUNITS':
            kv = dict(x.split('=', 1) for x in f[2:] if '=' in x)
            m['units'] += int(kv.get('lits', kv.get('units', '0')) or 0); m['kms'] += int(kv.get('kernel_ms', '0') or 0)
        elif t == 'KTIME':
            kv = dict(x.split('=', 1) for x in f[1:] if '=' in x); m['wall'] = float(kv.get('wall', 0)); m['rss'] = int(kv.get('maxrss_kb', 0))
    return m

man = {}
for d in a.build:
    for dp, _, fs in os.walk(d):
        for fn in fs:
            if fn.endswith('.kman'):
                m = parse(os.path.join(dp, fn))
                if 'name' in m: man[m['name']] = m
errs = []; ext = set(); seen = set(); stack = [a.root]; tycheck = set()
if a.root not in man: errs.append('root %s has no manifest' % a.root)
while stack:
    mod = stack.pop()
    if mod in seen or mod not in man: continue
    seen.add(mod); m = man[mod]
    if not m['pub']: errs.append('%s: no KPUB' % mod)
    for t in m['pub']:
        s = m['sum'].get(t)
        if s is None: errs.append('%s: no KAXSUM for %s' % (mod, t))
        elif s.get('bad') != '0' or s.get('local_axioms') != '0': errs.append('%s: KAXSUM %s bad=%s local_axioms=%s' % (mod, t, s.get('bad'), s.get('local_axioms')))
    for b in m['bad']: errs.append('%s: KAX BAD %s' % (mod, b))
    for (n, c) in m['obl']:
        if n in man:
            # a KMod child may be referenced through its public theorem, or through an external-leaf list NS.EXT that occurs in the
            # statement (type) of one of the child's KPUB theorems (a lifted range `∀ E, ExtSub NS.EXT E → …`, a class root over
            # KC.h<c>.EXT): the child's own #kax walk of that theorem entered NS.EXT (its value included), so the child's clean KAXSUM
            # covers it.  The statement check runs in Lean (tools/KModTyChk.lean, exported level) for all such pairs at once.
            if c not in man[n]['pub']:
                if c.endswith('.EXT'): tycheck.add((n, c))
                else: errs.append('%s: obligation %s of KMod module %s is not its public theorem' % (mod, c, n))
            stack.append(n)
        else: ext.add((n, c))
if tycheck:   # NS.EXT obligations: the list must occur in the statement of one of the module's KPUB theorems
    tf = '/tmp/kmod_tychk_%d.txt' % os.getpid()
    open(tf, 'w').write(''.join('%s %s %s\n' % (n, c, ' '.join(man[n]['pub'])) for n, c in sorted(tycheck)))
    env = dict(os.environ); env['LEAN_PATH'] = ':'.join([os.path.abspath(d) for d in a.build] + ([env['KMOD_LEAN_PATH']] if env.get('KMOD_LEAN_PATH') else []))
    env['PATH'] = os.path.dirname(LEAN) + ':' + env.get('PATH', '')
    r = subprocess.run(['nice', '-n', '10', LEAN, '--run', os.path.join(TOOLS, 'KModTyChk.lean'), tf], capture_output=True, text=True, env=env)
    ok = set(tuple(l.split()[1:3]) for l in r.stdout.splitlines() if l.startswith('TYOK'))
    for n, c in sorted(tycheck):
        if (n, c) not in ok: errs.append('obligation %s of KMod module %s: not in the statement of any of its public theorems%s' % (
            c, n, '' if r.returncode in (0, 2) else ' (statement check failed: %s)' % r.stderr.strip()[-300:]))
    print('statement check: %d NS.EXT obligations, %d in a public statement' % (len(tycheck), len(ok)))
for t, axs in man.get(a.root, {}).get('kaxp', {}).items():
    if not axs <= STD: errs.append('root KAXP %s: %s' % (t, ','.join(sorted(axs - STD))))
if not man.get(a.root, {}).get('kaxp'): print('note: the root has no KAXP line')
# external walk
extsum = 'skipped'
# (the KMod library's kmod_audit.py, md5 c7594ac1, with ONE change: --obl-out is also written with --no-ext, so the final audit's
#  external step can run as final_ext.py; the walk and every rule above are unchanged)
if ext and a.no_ext and a.obl_out:
    with open(a.obl_out, 'w') as f: f.write(''.join('%s %s\n' % x for x in sorted(ext)))
if ext and not a.no_ext:
    of = a.obl_out or '/tmp/kmod_obl_%d.txt' % os.getpid()
    open(of, 'w').write(''.join('%s %s\n' % x for x in sorted(ext)))
    env = dict(os.environ); env['LEAN_PATH'] = ':'.join([os.path.abspath(d) for d in a.build] + ([env['KMOD_LEAN_PATH']] if env.get('KMOD_LEAN_PATH') else []))
    env['PATH'] = os.path.dirname(LEAN) + ':' + env.get('PATH', '')
    r = subprocess.run(['nice', '-n', '10', LEAN, '--run', os.path.join(TOOLS, 'KModExt.lean'), of], capture_output=True, text=True, env=env)
    out = r.stdout.splitlines()
    for l in out:
        if l.startswith('EXT BAD'): errs.append('external: ' + l)
    extsum = ([l for l in out if l.startswith('EXTSUM')] or ['EXTSUM missing: ' + r.stderr.strip()[-300:]])[0]
    if r.returncode != 0 and not any(l.startswith('EXT BAD') for l in out): errs.append('external walk failed: ' + extsum)
# keys
if a.keys:
    keys = [l.strip() for l in open(a.keys) if l.strip()]; pos = {k: i for i, k in enumerate(keys)}; cover = [0] * len(keys)
    for mod in seen:
        for (f, l) in man[mod]['keys']:
            if f not in pos or l not in pos or pos[f] > pos[l]: errs.append('%s: KKEY %s %s not a range of the key list' % (mod, f, l)); continue
            for i in range(pos[f], pos[l] + 1): cover[i] += 1
    gaps = sum(1 for c in cover if c == 0); dup = sum(1 for c in cover if c > 1)
    if gaps or dup: errs.append('keys: %d uncovered, %d covered more than once (of %d)' % (gaps, dup, len(keys)))
    print('keys: %d, uncovered %d, multiply covered %d' % (len(keys), gaps, dup))
if a.ext_out:
    with open(a.ext_out, 'w') as f:
        for mod in sorted(seen):
            for e in man[mod]['ext']: f.write('%s %s\n' % (mod, e))
R = [man[x] for x in seen]
print('modules: %d reached of %d manifests; units %d; kernel %.1f s; wall %.1f s; max RSS %.2f GB; external obligations %d; %s'
      % (len(seen), len(man), sum(m['units'] for m in R), sum(m['kms'] for m in R) / 1000, sum(m['wall'] for m in R),
         max([m['rss'] for m in R] or [0]) / 1048576, len(ext), extsum))
unreached = sorted(set(man) - seen)
if unreached: print('not reached from the root: %d (e.g. %s)' % (len(unreached), ', '.join(unreached[:5])))
for e in errs[:50]: print('ERROR', e)
if len(errs) > 50: print('... %d errors in all' % len(errs))
print('PASS' if not errs else 'FAIL (%d errors)' % len(errs))
sys.exit(0 if not errs else 1)
