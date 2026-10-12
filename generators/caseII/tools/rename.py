#!/usr/bin/env python3
"""rename.py SRC DST: copy module tree SRC (mod/src) to DST (mod2/src), giving every kinds-built module of the KD / KD321
prefixes a kinds-only name (RENAME below), so that every module name in the build universe maps to exactly one file:
- XComp and XBatch differ from the port's; XBatchO and LoadXB import XBatch;
- the others exist only in the case-II library.
The port's unchanged KD / KD321 modules are imported from the port build, and kinds/mod2/build seeds nothing.
Rewritten: file paths, import lines, and the module docstring's first line. Constant names are unchanged (namespace KD …): an
environment that imported both the port's KD.XComp and KDK.XComp would fail on duplicate constants, so the mix cannot pass
silently. No module in closure imports the port's XComp, XBatch, XBatchO or LoadXB (checked on the traced closure).
Also writes DST/../build_order.txt from SRC/../build_order.txt."""
import sys, os, re
RENAME = {f'KD.{m}': f'KDK.{m}' for m in ('XComp', 'XBatch', 'XBatchO', 'LoadXB', 'Frame', 'FrameU', 'ItemK', 'CutFrame', 'ItemR',
                                          'XComp2', 'XBatch2', 'ItemR2', 'LoadXB2')}
RENAME.update({f'KD321.{m}': f'KDK321.{m}' for m in ('Flook', 'Root', 'Ext', 'Batch321')})
if __name__ == '__main__':
    src, dst = sys.argv[1], sys.argv[2]
    n = 0
    for dp, _, fs in os.walk(src):
        for f in fs:
            if not f.endswith('.lean'): continue
            rel = os.path.relpath(os.path.join(dp, f), src)[:-5]; m = rel.replace('/', '.'); nm = RENAME.get(m, m)
            t = open(os.path.join(dp, f)).read()
            t = re.sub(r'^((?:public )?(?:meta )?import )(\S+)', lambda x: x.group(1) + RENAME.get(x.group(2), x.group(2)), t, flags=re.M)
            if nm != m: t = t.replace('/-! # %s:' % m, '/-! # %s (kinds-only name of %s):' % (nm, m), 1)
            o = os.path.join(dst, nm.replace('.', '/') + '.lean'); os.makedirs(os.path.dirname(o), exist_ok=True)
            open(o, 'w').write(t); n += 1
    bo = os.path.join(os.path.dirname(src.rstrip('/')), 'build_order.txt')
    out = [RENAME.get(l.strip(), l.strip()) for l in open(bo) if l.strip()]
    open(os.path.join(os.path.dirname(dst.rstrip('/')), 'build_order.txt'), 'w').write('\n'.join(out) + '\n')
    print('renamed tree: %d files, %d modules renamed' % (n, len(RENAME)))
