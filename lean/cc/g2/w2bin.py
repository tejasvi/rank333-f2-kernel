#!/usr/bin/env python3
"""w2bin.py CLASS: the E1 witness table $E1ROOT/E1/C<C>X_W.lean (`def W : List (List Nat) := [[…], …]`) as data/C<C>X_W.bin
(u32 count, then per row u32 length and u32 entries), for G2.WLoad's #g2w."""
import sys, re, struct, os
c = int(sys.argv[1])
src = open(os.path.join(os.environ['E1ROOT'], 'E1/C%dX_W.lean' % c)).read()
m = re.search(r'def W : List \(List Nat\) := \[(.*)\]\s*\nend E1\.C%dX' % c, src, re.S)
body = m.group(1)
rows = [[int(x) for x in r.split(',') if x.strip()] for r in re.findall(r'\[([0-9, ]*)\]', body)]
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data/C%dX_W.bin' % c)
with open(out, 'wb') as f:
    f.write(struct.pack('<I', len(rows)))
    for r in rows:
        f.write(struct.pack('<I', len(r))); f.write(b''.join(struct.pack('<I', x) for x in r))
print('C%dX_W rows' % c, len(rows), 'entries', sum(map(len, rows)), '->', out)
