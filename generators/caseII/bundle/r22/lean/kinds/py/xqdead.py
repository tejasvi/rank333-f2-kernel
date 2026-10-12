#!/usr/bin/env python3
"""xqdead.py PLAN [PAR]: the dead-root items of a queue run (xqaudit --plan) without converting anything.

For every piece or job item (kinds P / J; a range item, kind Q, has an OPEN root by construction: py/pcseg.py writes its NODE + OPEN,
which r3qglue's text leaves out), `r3qglue --itemtext FILE OFF LEN`. The item's root is a dead node when its first O / C / L record is a C (a node cut)
or an L (a leaf) with no OPEN before it: py/kitem.py's rule, which then writes dead.bin. The dead kind is C<kind> for a node cut
(C5 / C6: node cut 5 / 6, an X part with a certificate; C3: look-ahead; C1 C2 C4 C7-C11: the other cuts) or L<code> for a leaf
(L0: profile leaf, L4: rootcut leaf).
Prints `DEAD id parent kind depth label deadkind` per dead-root item, then `items N dead D (rate) {deadkind: count}`."""
import os
import sys, subprocess, collections
from concurrent.futures import ThreadPoolExecutor
GLUE = os.environ.get('KINDS_R22', '.') + '/xq/r3q/bin/r3qglue'
plan = sys.argv[1]; par = int(sys.argv[2]) if len(sys.argv) > 2 else 8
items = []
for ln in open(plan):
    a = ln.split()
    if not a or a[0] != 'I': continue
    seg = [x for x in a if x.startswith('seg=')][0][4:].split(':')
    items.append((a[1], a[2], a[3], seg[1], seg[2], seg[3]))
def chk(it):
    if it[2] not in ('P', 'J'): return it, None
    p = subprocess.Popen([GLUE, '--itemtext'] + list(it[3:6]), stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    node = None; res = None
    for ln in p.stdout:
        a = ln.split()
        if not a or a[0][0] == '#': continue
        if a[0] == 'N': node = (a[1], a[2]); continue
        if a[0] == 'O': break
        if a[0] in ('C', 'L'): res = (node, a[0] + a[1]); break
    p.stdout.close(); p.kill(); p.wait()
    return it, res
with ThreadPoolExecutor(par) as ex: out = list(ex.map(chk, items))
cnt = collections.Counter()
for it, res in out:
    if res is None: continue
    node, dk = res; cnt[dk] += 1
    print('DEAD %s %s %s %s %s %s' % (it[0], it[1], it[2], node[0] if node else '-', node[1] if node else '-', dk))
nd = sum(cnt.values())
print('items %d dead %d (%.4f%%) %s' % (len(items), nd, 100.0 * nd / max(1, len(items)), dict(cnt)))
