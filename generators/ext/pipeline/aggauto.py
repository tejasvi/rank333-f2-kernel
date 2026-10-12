#!/usr/bin/env python3
# aggauto.py (reference copy): runs aggext.py --package for each cap once its root package and all its EXT packages are done.
# Regeneration does not need it: the inputs and arguments of every EXT top are shipped (inputs/ext/tops/, package_tools.tsv.zst).
# Reads $STORE (object store), $QUEUE_PREFIX (queue prefix), $PIPELINE_DIR (objstore.py, the store client).
"""aggauto.py [--loop S]: when a class's kcagg_h<c> (or a cap's agg_<C>_root) is done and every EXT package of that cap is done,
build its EXT top package (aggext.py --fetch CAP --package) once, and publish the line: appended to aggout/lines.jsonl and uploaded
to $QUEUE_PREFIX/aggext/lines.jsonl in the store (the queue gate reads it). Caps already emitted (aggout/<cap>.line.json
or agg_ext_<cap> done) are skipped. Logs to aggout/aggauto.log."""
import sys, os, json, re, time, subprocess, collections
sys.path.insert(0, os.environ.get('PIPELINE_DIR', '.'))
import objstore
HERE = os.path.dirname(os.path.abspath(__file__)); OUT = os.path.join(HERE, 'aggout'); os.makedirs(OUT, exist_ok=True)
B = os.environ.get('STORE'); P = os.environ.get('QUEUE_PREFIX')
def log(*a):
    with open(os.path.join(OUT, 'aggauto.log'), 'a') as f: f.write(time.strftime('%FT%TZ ', time.gmtime()) + ' '.join(map(str, a)) + '\n')
def once():
    done = set(it['name'].rsplit('/', 1)[1][:-5] for it in objstore.ls(B, P + '/done/'))
    sub = [json.loads(l) for l in open(os.path.join(HERE, 'state', 'submitted.jsonl'))]
    att = collections.defaultdict(list)
    for s in sub:
        q = re.sub(r'\.sb$', '', s['id'])     # ID.sb (cutgiant.py's split final) is an attempt of ID
        m = re.fullmatch(r'(.*)_r(\d+)', q); att[(s['cap'], m.group(1) if m else q)].append(s['id'])
    pend = collections.Counter(cap for (cap, base), ids in att.items() if not any(i in done for i in ids))
    for cap in sorted(set(s['cap'] for s in sub)):
        rootpkg = 'kcagg_%s' % cap if cap.startswith('h') else 'agg_%s_root' % cap
        lf = os.path.join(OUT, '%s.line.json' % cap)
        prior = [os.path.join(HERE, d, 'agg_ext_%s.line.json' % cap) for d in os.listdir(HERE) if d.startswith('agg') and os.path.isdir(os.path.join(HERE, d))]
        if os.path.exists(lf) or 'agg_ext_%s' % cap in done or any(os.path.exists(x) for x in prior): continue
        if rootpkg not in done or pend[cap]: continue
        d = os.path.join(OUT, 'run_%s' % cap)
        r = subprocess.run([sys.executable, os.path.join(HERE, 'aggext.py'), d, '--fetch', cap, '--package'], capture_output=True, text=True)
        log(cap, r.stdout.strip().replace('\n', ' | '), r.stderr.strip()[-300:])
        src = os.path.join(d, 'agg_ext_%s.line.json' % cap)
        if os.path.exists(src):
            line = open(src).read()
            open(lf, 'w').write(line)
            with open(os.path.join(OUT, 'lines.jsonl'), 'a') as f: f.write(line)
            objstore.upload_file(B, P + '/aggext/lines.jsonl', os.path.join(OUT, 'lines.jsonl'))
            log(cap, 'line published')
loop = int(sys.argv[sys.argv.index('--loop') + 1]) if '--loop' in sys.argv else 0
while True:
    try: once()
    except Exception as e: log('error', repr(e))
    if not loop: break
    time.sleep(loop)
