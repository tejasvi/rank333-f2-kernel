#!/usr/bin/env python3
# aggext.py (reference copy): writes the chunk list and the EXT top sources of a cap (mkexttop.py) and, with --package, its queue line.
# Regeneration does not need it: the inputs of every top (inputs/ext/tops/) and its mkexttop arguments (package_tools.tsv.zst) are shipped.
# Reads $STORE (object store), $QUEUE_PREFIX (queue prefix), $PIPELINE_DIR (objstore.py, the store client), $PIN_POOL.
"""aggext.py OUTDIR CAP=ORDERFILE [CAP=ORDERFILE ...] | --fetch CAP ... [--state DIR] [--prefix P]: the EXT tops for the final
assembly. With --fetch the order files come from the queue: agg_<C>_root (Root<C>.ext.txt) and kcagg_h<c> (ext_pl.txt).

For every CAP (436, 422: the CC caps; h<c>: a class-raise class) with its ORDERFILE (one decimal pl per line, in the order of
`KJ.agg<CAP>.Root.EXT` or `KC.h<c>.EXT`, duplicates kept):
  1. the chunks of the done EXT packages of CAP (`extscan.py chunks CAP`: names from the packages' leaves, latest successful
     attempt of each package) -> OUTDIR/<CAP>/chunks.txt; a package that is not done stops this cap (listed in OUTDIR/<CAP>/notdone.txt);
  2. `mkexttop.py CAP chunks.txt OUTDIR/<CAP> --order ORDERFILE [--root-module KJ.agg<CAP>_Root]` -> OUTDIR/<CAP>/src/...,
     manifest.jsonl (sched.py lines): CC (v4) `PLE.c<CAP>.Ext.hext_of` and `PLE.c<CAP>.Sub.sub` (the instance passes `_ hext_of
     Sub.sub`; every module of the tree is a pub, the final instance imports it publicly through Sub) or `NDX.h<c>.x<c>` (class, the
     top its only pub).
Every ORDERFILE entry must be in some chunk (mkexttop checks). Build with the EXT packages' public oleans in the store
(LEAN_PATH = store first, then the closure); the private-level external walk (kmod_audit) runs against the S4 private oleans. Writes OUTDIR/SUMMARY.txt."""
import sys, os, subprocess, json
HERE = os.path.dirname(os.path.abspath(__file__))
out = os.path.abspath(sys.argv[1]); os.makedirs(out, exist_ok=True)
state = sys.argv[sys.argv.index('--state') + 1] if '--state' in sys.argv else os.path.join(HERE, 'state')
prefix = sys.argv[sys.argv.index('--prefix') + 1] if '--prefix' in sys.argv else os.environ.get('QUEUE_PREFIX')
def fetch_order(cap, d):
    """the order file from the queue: the cap root package agg_<C>_root (Root<C>.ext.txt in its export) or the class
    aggregation package kcagg_h<c> (emit/ext_pl.txt in its pubs object); None if not done yet"""
    sys.path.insert(0, os.environ.get('PIPELINE_DIR', '.')); import objstore
    pid, member = ('kcagg_%s' % cap, 'ext_pl.txt') if cap.startswith('h') else ('agg_%s_root' % cap, 'Root%s.ext.txt' % cap)
    r = objstore.get(os.environ['STORE'], '%s/done/%s.json' % (prefix, pid))
    if r is None: return None
    rec = json.loads(r[0]); obj = rec.get('pubs_object') or rec['object']
    t = os.path.join(d, 'pkg.tar'); objstore.download_file(os.environ['STORE'], obj, t)
    lst = subprocess.run(['bash', '-c', '(zstd -dc %s 2>/dev/null || cat %s) | tar -tf -' % (t, t)], capture_output=True, text=True).stdout.split()
    mem = [m for m in lst if m.endswith(member)]
    if not mem: raise RuntimeError('%s: no %s in %s' % (pid, member, obj))
    f = os.path.join(d, 'order.txt')
    subprocess.run(['bash', '-c', '(zstd -dc %s 2>/dev/null || cat %s) | tar -xOf - %s > %s' % (t, t, mem[0], f)], check=True)
    os.remove(t)
    return f

summary = []
args = [a for a in sys.argv[2:] if not a.startswith('--') and a not in (state, prefix)]
if '--fetch' in sys.argv:
    args = []
    for cap in sys.argv[sys.argv.index('--fetch') + 1:]:
        if cap.startswith('--'): break
        d = os.path.join(out, cap); os.makedirs(d, exist_ok=True)
        f = fetch_order(cap, d)
        if f is None: summary.append('%s: its root/aggregation package is not done yet' % cap)
        else: args.append('%s=%s' % (cap, f))
for arg in args:
    if '=' not in arg: continue
    cap, order = arg.split('=', 1)
    d = os.path.join(out, cap); os.makedirs(d, exist_ok=True)
    r = subprocess.run([sys.executable, os.path.join(HERE, 'extscan.py'), 'chunks', cap, '--state', state, '--prefix', prefix, '--with-pkg'],
                       capture_output=True, text=True)
    lines = r.stdout.splitlines()
    pkgs = sorted(set(l.split()[2] for l in lines if l and not l.startswith('#') and len(l.split()) > 2))
    lines = [' '.join(l.split()[:2]) if l and not l.startswith('#') else l for l in lines]
    notdone = [l for l in lines if l.startswith('# not done') or l.startswith('# CONFLICT')]
    open(os.path.join(d, 'chunks.txt'), 'w').write(''.join(l + '\n' for l in lines if l and not l.startswith('#')))
    open(os.path.join(d, 'notdone.txt'), 'w').write(''.join(l + '\n' for l in notdone))
    if notdone:
        summary.append('%s: %d EXT packages not done yet (notdone.txt); no top' % (cap, len(notdone))); continue
    # CC caps: the top's Sub module states KJ.agg<C>.Root.EXT ⊆ PLE.c<C>.Ext.EXT, importing the root module KJ.agg<C>_Root; fan 25
    # splits the root-list check into segments SubS<k> built in parallel. In the final set the 436 top has these arguments and the 422
    # top has --root-module only (package_tools.tsv lists the arguments of every top)
    rootmod = [] if cap.startswith('h') else ['--root-module', 'KJ.agg%s_Root' % cap, '--fan', '25', '--fan-auto']
    m = subprocess.run([sys.executable, os.path.join(HERE, 'mkexttop.py'), cap, os.path.join(d, 'chunks.txt'), d, '--order', os.path.abspath(order)] + rootmod,
                       capture_output=True, text=True)
    summary.append('%s: %s%s' % (cap, m.stdout.strip(), (' ERROR ' + m.stderr.strip()[-500:]) if m.returncode else ''))
    if m.returncode == 0 and '--package' in sys.argv:
        # a pre-emitted queue package: manifest + sources, deps = the root/class aggregation and the EXT packages
        man = [json.loads(l) for l in open(os.path.join(d, 'manifest.jsonl'))]
        for x in man: x.pop('env', None)
        open(os.path.join(d, 'manifest.jsonl'), 'w').write(''.join(json.dumps(x) + '\n' for x in man))
        import hashlib
        t = os.path.join(out, 'agg_ext_%s.tar.zst' % cap)
        subprocess.run(['bash', '-c', 'cd %s && tar -cf - manifest.jsonl src | zstd -19 -q -f -o %s' % (d, t)], check=True)
        sha = hashlib.sha256(open(t, 'rb').read()).hexdigest()
        obj = '%s/aggext/agg_ext_%s_%s.tar.zst' % (prefix, cap, sha[:12])
        sys.path.insert(0, os.environ.get('PIPELINE_DIR', '.')); import objstore
        objstore.upload_file(os.environ['STORE'], obj, t)
        top = man[-1]
        rootpkg = 'kcagg_%s' % cap if cap.startswith('h') else 'agg_%s_root' % cap
        # CC tops: many 7 GB modules and the Sub module (~15 GB at 206k entries): min_mem_gb 64, pinned to the pin pool when one is set
        pin = os.environ.get('PIN_POOL', '').split()
        line = dict(id='agg_ext_%s' % cap, cap=cap, kind='ext-top', pred_s=round(sum(x['pred_s'] for x in man) + 60, 1),
                    **({} if cap.startswith('h') else dict(min_mem_gb=64, **({'pin_box': pin[0]} if pin else {}))),
                    pred_gb_max=max(x['pred_gb'] for x in man), disk_gb=max(1, len(pkgs) // 200),
                    deps=[rootpkg] + pkgs, deps_pubs=True,
                    emit=dict(type='tarball', object=obj, manifest='manifest.jsonl', sha256=sha),
                    pubs=[[x['module'], x['pub']] for x in man if 'pub' in x], export=[],
                    note='EXT top of %s over %s (aggext.py)' % (cap, 'KC.%s.EXT' % cap if cap.startswith('h') else 'KJ.agg%s.Root.EXT' % cap))
        open(os.path.join(out, 'agg_ext_%s.line.json' % cap), 'w').write(json.dumps(line) + '\n')
        summary.append('%s: package line %s (%d deps)' % (cap, os.path.join(out, 'agg_ext_%s.line.json' % cap), len(line['deps'])))
open(os.path.join(out, 'SUMMARY.txt'), 'w').write('\n'.join(summary) + '\n')
print('\n'.join(summary))
