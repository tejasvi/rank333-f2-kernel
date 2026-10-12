import os, sys, time
root = sys.argv[1]   # the build store (output root of the module builds)
n = 0; bad = []
for dp, dn, fn in os.walk(root):
    for f in fn:
        if not (f.endswith('.olean') or f.endswith('.olean.private') or f.endswith('.olean.server') or f.endswith('.ir')): continue
        p = os.path.join(dp, f)
        try:
            sz = os.path.getsize(p)
            if sz < 96: bad.append((p, sz, 'short')); continue
            with open(p, 'rb') as fh:
                fh.seek(sz - 64); tail = fh.read(64)
            n += 1
            if tail == bytes(64): bad.append((p, sz, os.path.getmtime(p)))
        except Exception as e:
            bad.append((p, -1, repr(e)[:60]))
print('scanned', n, 'zero-tail', len(bad))
for b in bad[:50]: print('BAD', b[0], b[1], time.strftime('%FT%TZ', time.gmtime(b[2])) if isinstance(b[2], float) else b[2])
