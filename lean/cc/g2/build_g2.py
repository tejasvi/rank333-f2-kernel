#!/usr/bin/env python3
"""build_g2.py [-j N] [--check]: build the 36,956 G2 modules into mod/build, in dependency order, N processes at a time (default 8; a block
module takes up to about 6 GB).

Inputs, under this directory:
  mod/src/G2/          the 19 sources in the repository plus the 36,937 generated ones (zenodo g2_src_generated.tar.zst, members
                       g2/mod/src/G2/...);
  data/, l2/split/     the binary literal files the loaders read by relative paths (zenodo g2_data.tar.zst, g2_split.tar.zst).
Modules: G2.Disp, G2.Asm2, G2.WLoad and those of mod/manifest_c303.jsonl and mod/manifest_c321.jsonl; dependencies from the import lines.
Each module: $LEAN -DElab.async=false -j1 -R mod/src mod/src/G2/<M>.lean -o mod/build/G2/<M>.olean -i mod/build/G2/<M>.ilean, run from this
directory, with LEAN_PATH = mod/build : $LEAN_PATH_ENV (the KMod build, the frozen port build, Mathlib and its dependencies, the Lean
toolchain; lean/TOOLCHAIN.md). Logs in mod/log. With --check, compares every .olean and .olean.private with OLEANS.sha256.zst at the end.
A module whose .olean exists is not rebuilt."""
import os, sys, json, subprocess, time, hashlib
G = os.path.dirname(os.path.abspath(__file__)); os.chdir(G)
J = int(sys.argv[sys.argv.index('-j') + 1]) if '-j' in sys.argv else 8
LEAN = os.environ.get('LEAN', 'lean')
env = dict(os.environ); env['LEAN_PATH'] = os.path.join(G, 'mod/build') + ':' + os.environ['LEAN_PATH_ENV']
mods = ['G2.Disp', 'G2.Asm2', 'G2.WLoad']
for c in (303, 321):
    mods += [json.loads(l)['module'] for l in open('mod/manifest_c%d.jsonl' % c) if l.strip()]
M = {}                                   # module -> its G2 imports (public, private and meta), read from the source
for k in mods:
    imps = [l.split()[-1] for l in open('mod/src/G2/%s.lean' % k[3:], encoding='utf-8')
            if l.split()[:1] in (['import'], ['public'], ['meta']) and 'import' in l.split()[:3]]
    M[k] = [i for i in imps if i.startswith('G2.')]
os.makedirs('mod/build/G2', exist_ok=True); os.makedirs('mod/log', exist_ok=True)
done = {k for k in M if os.path.exists('mod/build/G2/%s.olean' % k[3:])}
pending = [k for k in M if k not in done]; running = {}; failed = []
NI = max(0, 10 - os.nice(0))
while pending or running:
    for k in [k for k in pending if all(d in done for d in M[k] if d in M)]:
        if len(running) >= J: break
        m = k[3:]
        argv = ['nice', '-n', str(NI), LEAN, '-DElab.async=false', '-j1', '-R', 'mod/src', 'mod/src/G2/%s.lean' % m,
                '-o', 'mod/build/G2/%s.olean' % m, '-i', 'mod/build/G2/%s.ilean' % m]
        running[subprocess.Popen(argv, env=env, stdout=open('mod/log/%s.log' % m, 'w'), stderr=subprocess.STDOUT)] = k
        pending.remove(k)
    for p in list(running):
        if p.poll() is not None:
            k = running.pop(p)
            if p.returncode == 0: done.add(k)
            else: failed.append(k); print('FAIL', k, flush=True)
    if failed and not running: break
    time.sleep(0.2)
print('built %d of %d modules, %d failed' % (len(done), len(M), len(failed)))
if failed: sys.exit(1)
if '--check' in sys.argv:
    lst = subprocess.run(['zstd', '-dc', os.path.join(G, 'OLEANS.sha256.zst')], capture_output=True, check=True).stdout
    r = subprocess.run(['sha256sum', '--quiet', '-c', '-'], input=lst, cwd=os.path.join(G, 'mod/build'))
    print('OLEANS.sha256: %s' % ('all match' if r.returncode == 0 else 'MISMATCH'))
    sys.exit(r.returncode)
