#!/usr/bin/env python3
"""topstore.py OUTDIR [--loop 300] [--par 32]: the store the final top builds and is audited against (FINAL_DIR/topstore), filled
incrementally: the pubs object of every done package of the queue (the public root modules: .olean/.ilean/.kman/.mhash/.olean.server,
plus emit/DONE, kext.txt and the package's exported files), each verified (pubs sha256 = its done record, then every file against the
object's SHA256SUMS) and merged into OUTDIR/store; a file already present with DIFFERENT content is a NAME-CONFLICT (recorded in
OUTDIR/CONFLICTS.jsonl, never overwritten).  A package whose done record disappears (superseded) has its files removed again (each
file only if it is still the one it installed).  Packages without a pubs object (done before pubs existed) contribute their root
modules from the full tarball.  OUTDIR/pkgs/<id>.json: the installed files and their sha256 (resumable); OUTDIR/STATUS: one line."""
import concurrent.futures as cf, hashlib, io, json, os, subprocess, sys, tarfile, time
K_ = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(K_, 'queue'))
import objstore
B, P = objstore.BUCKET, objstore.PREFIX
a = sys.argv[1:]; OUT = os.path.abspath(a[0])
loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 300; par = int(a[a.index('--par') + 1]) if '--par' in a else 32
for d in ('store', 'pkgs', 'emit'): os.makedirs(os.path.join(OUT, d), exist_ok=True)
def log(*x): print(time.strftime('%FT%TZ', time.gmtime()), *x, flush=True)
sha = lambda b: hashlib.sha256(b).hexdigest()

def fetch(pid):
    try: return fetch1(pid)
    except Exception as e: return pid, None, 'fetch failed (next loop): %r' % e

def fetch1(pid):
    """(pid, gen, {arcname: bytes}) of the package's public part, verified, or (pid, gen, error string)"""
    g = objstore.get(B, P + '/done/%s.json' % pid, timeout=30, tries=4)
    if not g: return pid, None, 'no done record'
    rec = json.loads(g[0]); gen = str(g[1])
    if rec.get('pubs_object'):
        raw = objstore.fetch(B, rec['pubs_object'], timeout=120, tries=6)
        if sha(raw) != rec.get('pubs_sha256'): return pid, gen, 'pubs sha256 differs from the done record'
        tf = tarfile.open(fileobj=io.BytesIO(raw), mode='r:')
    else:
        raw = objstore.fetch(B, rec['object'], timeout=180, tries=6)
        if sha(raw) != rec.get('sha256'): return pid, gen, 'tarball sha256 differs from the done record'
        tf = tarfile.open(fileobj=io.BytesIO(subprocess.run(['zstd', '-dc'], input=raw, capture_output=True).stdout), mode='r:')
    files = {}; sums = {}
    roots = tuple('store/' + r.replace('.', '/') + '.' for r in ((rec.get('audit') or {}).get('roots') or []))
    for m in tf.getmembers():
        if not m.isfile(): continue
        if m.name == 'SHA256SUMS':
            sums = {f: h for h, f in (l.split('  ', 1) for l in tf.extractfile(m).read().decode().splitlines() if '  ' in l)}
        elif m.name.startswith('emit/') or (m.name.startswith('store/') and (rec.get('pubs_object') or m.name.startswith(roots))):
            files[m.name] = tf.extractfile(m).read()
    for f, b in files.items():
        if f.startswith('store/') and f in sums and sha(b) != sums[f]: return pid, gen, 'sha256 differs from SHA256SUMS: ' + f
    return pid, gen, files

def main():
    while True:
        try:
            listing = {it['name'].rsplit('/', 1)[1][:-5]: str(it['generation']) for it in objstore.ls(B, P + '/done/') if it['name'].endswith('.json')}
            have = {}
            for f in os.listdir(OUT + '/pkgs'):
                if f.endswith('.json'): have[f[:-5]] = json.load(open(os.path.join(OUT, 'pkgs', f)))
            # superseded: remove the files it installed (only those still holding its content)
            users = {}
            for pid, v in have.items():
                for f in v['files']: users[f] = users.get(f, 0) + 1
            for pid in set(have) - set(listing):
                for f, h in have[pid]['files'].items():
                    p = os.path.join(OUT, f)
                    if users.get(f, 0) <= 1 and os.path.exists(p) and sha(open(p, 'rb').read()) == h: os.remove(p)
                    users[f] = users.get(f, 1) - 1
                os.remove(os.path.join(OUT, 'pkgs', pid + '.json')); log('removed superseded', pid)
            todo = [i for i, g in listing.items() if have.get(i, {}).get('gen') != g]
            n = nconf = nerr = 0
            with cf.ThreadPoolExecutor(par) as ex, open(os.path.join(OUT, 'CONFLICTS.jsonl'), 'a') as cfl:
                for pid, gen, files in ex.map(fetch, todo):
                    if isinstance(files, str): nerr += 1; log('error', pid, files); continue
                    inst = {}
                    for f, b in files.items():
                        dst = os.path.join(OUT, f) if f.startswith('store/') else os.path.join(OUT, 'emit', pid, f[5:])
                        os.makedirs(os.path.dirname(dst), exist_ok=True)
                        if f.startswith('store/') and os.path.exists(dst):
                            if sha(open(dst, 'rb').read()) != sha(b):
                                cfl.write(json.dumps(dict(t=time.time(), pid=pid, file=f)) + '\n'); nconf += 1; continue
                        else:
                            open(dst + '.tmp', 'wb').write(b); os.replace(dst + '.tmp', dst)
                        inst[os.path.relpath(dst, OUT)] = sha(b)
                    json.dump(dict(gen=gen, files=inst), open(os.path.join(OUT, 'pkgs', pid + '.json'), 'w')); n += 1
            line = '%s top store: %d done packages installed (%d new, %d errors), %d NAME-CONFLICT files this pass' % (
                time.strftime('%FT%TZ', time.gmtime()), len(os.listdir(OUT + '/pkgs')), n, nerr, nconf)
            open(os.path.join(OUT, 'STATUS'), 'w').write(line + '\n'); print(line, flush=True)
        except Exception as e:
            log('loop error', repr(e)[:300])
        if not loop: break
        time.sleep(loop)

if __name__ == '__main__':
    main()
