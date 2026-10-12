#!/usr/bin/env python3
"""mknest.py NAME OUT CHUNKNODES: Lean modules for a nested split leaf (S7/NestT.lean: threaded sub-record slices) from OUT.bin
(literal 0 = the main leaf record, literal k+1 = record k's certificate), OUT.recs (first line m0, then record k: `path|a|m`,
with a = m0 + the counts of the records before k: checked here) and OUT.sizes (record node counts):
L5/t/<NAME>_Data (literals, `recs` = (path, count, certificate), `paths`, `m0`), L5/t/<NAME>_C<j> (chunks of records of at
most CHUNKNODES nodes and MAXREC records, `S7X.chunkT` with the chunk's range start), L5/t/<NAME> (main record, join, and
`leaf` from `S7X.nestSplitT_sound'`)."""
import sys, os
name, out, CN = sys.argv[1], sys.argv[2], int(sys.argv[3])
G2 = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + '/'
L5 = G2 + 'l2/L5/t/'
lines = [l.rstrip('\n') for l in open(out + '.recs') if l.strip()]
m0 = int(lines[0]); recs = [l.split('|') for l in lines[1:]]
sizes = [int(x) for x in open(out + '.sizes') if x.strip()]
assert len(sizes) == len(recs)
K = len(recs)
# range starts: BFS numbering allocates each record's sub-records right after the previous record's
starts = []; a = m0
for p, ak, m in recs:
    assert int(ak) == a, ('non-consecutive ranges', ak, a)
    starts.append(a); a += int(m)
MAXREC = 64
hdr = 'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
body = ',\n'.join('(%s, %s, %s.L%d)' % (p, m, name, k + 1) for k, (p, ak, m) in enumerate(recs))
open(L5 + name + '_Data.lean', 'w').write('import S7.NestT\nimport E1.E1Load\n' + hdr +
  '#e1lits %s "%s.bin"\nnamespace %s\nopen BC7x\n'
  '/-- records `(path, sub-record count, certificate)`, BFS order of the record tree (sub-record ranges consecutive) -/\n'
  'noncomputable def recs : List (List Step × Nat × Nat) := [\n%s\n]\n'
  'noncomputable def paths : List (List Step) := recs.map Prod.fst\n'
  '/-- the main record\'s external subtrees are records `0 .. m0-1` -/\ndef m0 : Nat := %d\nend %s\n' % (name, out, name, body, m0, name))
chunks = []; a = 0
while a < K:
    m = 0; tot = 0
    while a + m < K and (m == 0 or (tot + sizes[a + m] <= CN and m < MAXREC)): tot += sizes[a + m]; m += 1
    chunks.append((a, m)); a += m
for j, (a, m) in enumerate(chunks):
    open(L5 + '%s_C%d.lean' % (name, j), 'w').write('import L5.t.%s_Data\n' % name + hdr +
      'namespace %s\ntheorem ok%d : S7X.chunkT (lits.getD 0 0) paths recs %d %d %d = true := by decide +kernel\nend %s\n'
      % (name, j, a, m, starts[a], name))
L = ['import L5.t.%s_C%d' % (name, j) for j in range(len(chunks))] + ['import L5.t.%s_Data' % name, hdr,
     'namespace %s' % name, 'open BC7x S7X',
     'theorem main : leafSX (lits.getD 0 0) ((recs.map Prod.fst).take m0) = true := by decide +kernel',
     'theorem lenR : recs.length = %d := by decide' % K]
if chunks:
    L.append('theorem all : chunkT (lits.getD 0 0) paths recs 0 %d m0 = true := by' % K)
    acc = chunks[0][1]
    L.append('  have h0 : chunkT (lits.getD 0 0) paths recs 0 %d m0 = true := ok0' % acc)
    for t, (a, m) in enumerate(chunks[1:], 1):
        L.append('  have h%d : chunkT (lits.getD 0 0) paths recs 0 %d m0 = true :=' % (t, acc + m))
        L.append('    chunkT_join _ _ _ 0 %d %d m0 %d (by rw [lenR]; decide) (by decide +kernel) h%d ok%d' % (acc, m, starts[a], t - 1, t))
        acc += m
    L.append('  exact h%d' % (len(chunks) - 1))
else:
    L.append('theorem all : chunkT (lits.getD 0 0) paths recs 0 0 m0 = true := rfl')
L += ['/-- **the leaf has no decomposition** (nested split leaf: main record and %d records) -/' % K,
      'theorem leaf : S5.NoDecomp (S5.leafT (lits.getD 0 0)) (S5.leafN (lits.getD 0 0)) (S6.leafDom6 (lits.getD 0 0)) :=',
      '  nestSplitT_sound\' _ recs m0 main (by rw [lenR]; exact all)',
      'end %s' % name, '#print axioms %s.leaf' % name, '']
open(L5 + name + '.lean', 'w').write('\n'.join(L))
print('records', K, 'chunks', len(chunks))
