#!/usr/bin/env python3
"""gateappend.py BUCKET PREFIX [FILE.jsonl ...] [--files-from LIST] [--loop S]: append each package line of the FILEs (aggregation steps:
the e1g heavy-job aggregations and cap roots, class aggregations, the EXT tops, the caseII join) to the queue head the moment all
its "deps" have done records (done.json.gz snapshot, else a done/ listing); a line already in packages.jsonl is never appended again.
The FILEs, and LIST (one gate file per line, relative to this directory; '#' comments), are re-read every loop: gates can be added
without a restart.  Log: one line per loop."""
import gzip, json, os, subprocess, sys, time
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, H)
import objstore
a = sys.argv[1:]; B, P = a[0], a[1].rstrip('/')
loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 0
files = [x for i, x in enumerate(a[2:], 2) if not x.startswith('--') and a[i - 1] not in ('--loop', '--files-from')]
lst = a[a.index('--files-from') + 1] if '--files-from' in a else None
while True:
    try:
        lines = []
        fl = files + ([l.split('#')[0].strip() for l in open(os.path.join(H, lst)) if l.split('#')[0].strip()] if lst else [])
        for f in dict.fromkeys(fl):
            if f.startswith('//'):
                # a gate list published as a store object (append-only), "//<namespace>/<name>", e.g. the EXT tops' aggext/lines.jsonl
                g = objstore.get(f[2:].split('/', 1)[0], f[2:].split('/', 1)[1])
                if g: lines += [json.loads(l) for l in g[0].decode().splitlines() if l.strip()]
            else:
                lines += [json.loads(l) for l in open(f) if l.strip()]
        g = objstore.get(B, P + '/done.json.gz'); done = None
        if g:
            d = json.loads(gzip.decompress(g[0]))
            if time.time() - d.get('t', 0) < 600: done = set(d['ids'])
        if done is None: done = {it['name'].rsplit('/', 1)[1][:-5] for it in objstore.ls(B, P + '/done/')}
        r = objstore.get(B, P + '/packages.jsonl'); have = {json.loads(l)['id'] for l in r[0].decode().splitlines() if l.strip()}
        ready = [x for x in lines if x['id'] not in have and set(x.get('deps', [])) <= done]
        waiting = [x for x in lines if x['id'] not in have and not set(x.get('deps', [])) <= done]
        if ready:
            f = '/tmp/gateappend_%d.jsonl' % os.getpid(); open(f, 'w').write(''.join(json.dumps(x) + '\n' for x in ready))
            out = subprocess.run([sys.executable, os.path.join(H, 'pbq.py'), 'add', B, P, f, '--front'], capture_output=True, text=True).stdout.strip()
            print(time.strftime('%FT%TZ', time.gmtime()), 'appended %d: %s | %s' % (len(ready), ' '.join(x['id'] for x in ready[:12]), out), flush=True)
        near = sorted(waiting, key=lambda x: len(set(x.get('deps', [])) - done))[:3]
        print(time.strftime('%FT%TZ', time.gmtime()), '%d gated lines: %d in the queue, %d waiting; closest: %s' % (
            len(lines), sum(1 for x in lines if x['id'] in have), len(waiting),
            ', '.join('%s (%d/%d deps missing)' % (x['id'], len(set(x['deps']) - done), len(x['deps'])) for x in near)), flush=True)
    except Exception as e:
        print(time.strftime('%FT%TZ', time.gmtime()), 'error', repr(e)[:200], flush=True)
    if not loop: break
    time.sleep(loop)
