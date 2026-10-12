#!/usr/bin/env python3
"""unitconv.py D MODULE: the lazy conversion of one item module of a case-II package (run by kmod_unit.sh before the build).

For each line `id file off len key dead` of D/src/<MODULE as path>.items (py/emitlazy.py), in order: `r3qglue --itembin FILE OFF LEN`
(or, for `seg:<pcert>:<id>` lines of py/joinemit.py, py/pcseg.py on that phase-0 segment), py/pcseg.py (header hdr_ccw.r3, FLAGS_CCW's), py/kitem.py (CC route cc436_422: the bundle's kept rows, c2t and RT entries) and
py/itemkey.py into D/data/q/<id>.d. Checks: kitem wrote table_0.bin (or dead.bin), the key equals the stub's (the queue's interface),
and dead.bin exists exactly when the stub says the root is dead. Then py/mkimod.py writes the module's real source (items I0, I1, … in
the stub's order, so the chunk specs' indices stay valid) over the stub. Exit 1 on any mismatch. Env KINDS_R22 (the bundle's r22 tree)."""
import sys, os, subprocess, tempfile, shutil
sys.set_int_max_str_digits(0)
R22 = os.environ.get('KINDS_R22', '.'); K = R22 + '/lean/kinds'; C = K + '/data/cc/cc436_422'
GLUE = R22 + '/xq/r3q/bin/r3qglue'; PY = sys.executable
D, M = sys.argv[1], sys.argv[2]; mp = M.replace('.', '/')
items = [l.split() for l in open('%s/src/%s.items' % (D, mp)) if l.strip()]
env = dict(os.environ, KI_MEMB=os.environ.get('KI_MEMB', '1.2'), KI_PERMISSIVE='1', PCSEG_HDR=C + '/hdr_ccw.r3')
dirs = []
for iid, f, off, n, key, dead in items:
    d = '%s/data/q/%s.d' % (D, iid); b = '%s/data/q/%s.bin' % (D, iid); t = '%s/data/q/%s.txt' % (D, iid)
    os.makedirs(D + '/data/q', exist_ok=True); shutil.rmtree(d, ignore_errors=True)
    if f.startswith('seg:'):   # a phase-0 segment (py/joinemit.py): seg:<pcert>:<segment id>
        _, pf, sid = f.split(':')
        if not os.path.isabs(pf): pf = os.path.join(D, pf)   # py/joinemit.py names its pcerts relative to the package dir
        with open(t, 'w') as o: subprocess.run([PY, K + '/py/pcseg.py', pf, sid], stdout=o, check=True, env=env)
    else:
        subprocess.run([GLUE, '--itembin', f, off, n, b], check=True, capture_output=True)
        with open(t, 'w') as o: subprocess.run([PY, K + '/py/pcseg.py', b, '0'], stdout=o, check=True, env=env)
        os.remove(b)
    with open(d + '.conv.log', 'w') as o:
        subprocess.run([PY, K + '/py/kitem.py', t, C + '/kept_cc436_422.txt', C + '/cc436_422.c2t', C + '/kept_rt.bin', d, '20'],
                       stdout=o, stderr=subprocess.STDOUT, env=env)
    if not os.path.exists(d + '/table_0.bin') and not os.path.exists(d + '/dead.bin'):
        sys.exit('unitconv: %s item %s: kitem failed: %s' % (M, iid, open(d + '.conv.log').read().strip().split('\n')[-1][:200]))
    subprocess.run([PY, K + '/py/itemkey.py', t, d], check=True, env=env)
    os.remove(t)
    k = open(d + '/key.txt').read().split()[0]
    if k != key: sys.exit('unitconv: %s item %s: key differs from the queue interface' % (M, iid))
    if os.path.exists(d + '/dead.bin') != (dead == '1'): sys.exit('unitconv: %s item %s: dead root %s, the stub says %s' % (M, iid, os.path.exists(d + '/dead.bin'), dead))
    dirs.append('data/q/%s.d' % iid)
tmp = tempfile.mkdtemp(dir=D)
subprocess.run([PY, K + '/py/mkimod.py', tmp, M, 'cc436_422'] + dirs, check=True, cwd=D, stdout=subprocess.DEVNULL)
shutil.move('%s/%s.lean' % (tmp, mp), '%s/src/%s.lean' % (D, mp)); shutil.rmtree(tmp)
print('unitconv: %s: %d items converted' % (M, len(items)))
