#!/usr/bin/env python3
"""tomod_g2.py CLASS: module-form G2 sources for the E1 route's class CLASS (303 or 321) in mod/src/G2/, plus the build manifest.

Sources ($E1ROOT, the E1 route's source tree, is only read):
  $E1ROOT/E1/C<C>X_Lits, C<C>X_W, C<C>X_N, C<C>X (chain loader, witnesses, length, chain), $E1ROOT/E1/E<C>M_Lits, E<C>M_C<j>
  (monolithic external leaves), $E1ROOT/E1/E<C> (the class theorem e<C>_final);
  l2/E1/C<C>X_B<j> (blocks, blocks.py) and l2/L5/t/E<C>S<k>{,_Data,_C<j>} (split leaves, splitgen.py).
Renames (one name, one content): modules E1.C<C>X* / E1.E<C>M* / E1.E<C> / L5.t.E<C>S* become G2.C<C>X* / G2.E<C>M* / G2.E<C> /
G2.E<C>S*, and so do their namespaces (E1.C<C>X, E1.E<C>M, E1.E<C>, E<C>S<k>). Everything else (E1.IP_e<C>, E1.SL_e<C>,
E1.OK_e<C>, E1.E1Load, E1.Asm, E1.AsmG, E1.AsmN, E1.ExtLeaf, S7.NestT, HC.Pad, RT.Cls_e<C>) is the port's vocabulary.
Data: #e1lits files are copied to data/ (sha256 in data/SHA256) and referenced there by paths relative to this directory. The witness table C<C>X_W is
loaded from data/C<C>X_W.bin (w2bin.py) by G2.WLoad's #g2w instead of the list literal.
Module form as the port's conversion of the 55 E1 crowns: `module`, `public import R22Port.U_d41d8cd98f00`, every import public,
`@[expose] public section`. The crown G2.Crown<C> imports the class theorem privately and proves, by KMod's #kpubterm (KPUB),
  G2.Crown<C>.crown : ∀ (hcls : ∀ c, RT.Fact (RT.kM RT.Cls_e<C>.CL c) (RT.cLB RT.Cls_e<C>.CL c)), HC.E1Concl E1.IP_e<C>.Em 18
then #kax and #print axioms.
Manifest mod/manifest_c<C>.jsonl (the module scheduler, lean_g2.sh, output mod/build): one unit per module
(src, cwd src), deps from the imports, tier g2, kind lits|w|n|block|chain|mono|split_data|split_chunk|split|final|crown; the
module hash records are written as modules finish."""
import sys, os, re, json, glob, shutil, hashlib
c = int(sys.argv[1])
L2 = os.environ['E1ROOT'].rstrip('/') + '/'            # E1ROOT: the E1 route's source tree
G = os.path.dirname(os.path.abspath(__file__)) + '/'                # this directory (the G2 root)
SRC = G + 'mod/src/G2/'; DATA = G + 'data/'
os.makedirs(SRC, exist_ok=True); os.makedirs(DATA, exist_ok=True)
CX, EM, EF, ES = 'C%dX' % c, 'E%dM' % c, 'E%d' % c, 'E%dS' % c

def rename_mod(m):
    if m == 'E1.' + CX or m.startswith('E1.' + CX + '_'): return 'G2.' + m[3:]
    if m.startswith('E1.' + EM): return 'G2.' + m[3:]
    if m == 'E1.' + EF: return 'G2.' + EF
    if m.startswith('L5.t.' + ES): return 'G2.' + m[5:]
    return m
def rename_body(s):
    s = re.sub(r'\bE1\.%s\b' % CX, 'G2.' + CX, s)
    s = re.sub(r'\bE1\.%s\b' % EM, 'G2.' + EM, s)
    s = re.sub(r'\bE1\.%s\b' % EF, 'G2.' + EF, s)
    s = re.sub(r'(?<![\w./])%s(\d+)\b' % ES, r'G2.%s\1' % ES, s)
    return s
datamap = {}
def data_path(p):
    if p.startswith(G): return p                      # already ours (split leaves)
    if p not in datamap:
        dst = DATA + os.path.basename(p)
        if not os.path.exists(dst) or os.path.getsize(dst) != os.path.getsize(p): shutil.copyfile(p, dst)
        datamap[p] = dst
    return datamap[p]
def kind_of(name):
    if name.endswith('_Lits') and name.startswith(CX): return 'lits'
    if name == CX + '_W': return 'w'
    if name == CX + '_N': return 'n'
    if name.startswith(CX + '_B'): return 'block'
    if name == CX: return 'chain'
    if name.startswith(EM): return 'mono'
    if re.fullmatch(ES + r'\d+_Data', name): return 'split_data'
    if re.fullmatch(ES + r'\d+_C\d+', name): return 'split_chunk'
    if re.fullmatch(ES + r'\d+', name): return 'split'
    if name == EF: return 'final'
    return '?'
man = []
def convert(path, name):
    lines = open(path).read().split('\n')
    imps = [rename_mod(l.split()[1]) for l in lines if l.startswith('import ')]
    body = '\n'.join(l for l in lines if not l.startswith('import ') and not l.startswith('#print axioms'))
    body = rename_body(body)
    body = re.sub(r'(#e1lits \S+ ")([^"]+)(")', lambda m: m.group(1) + os.path.relpath(data_path(m.group(2)), G) + m.group(3), body)
    out = ['module', 'public import R22Port.U_d41d8cd98f00'] + ['public import ' + m for m in imps] + ['@[expose] public section', body]
    open(SRC + name + '.lean', 'w').write('\n'.join(out))
    deps = [m for m in imps if m.startswith('G2.')]
    man.append(dict(module='G2.' + name, src='src/G2/%s.lean' % name, cwd='src', tier='g2', kind=kind_of(name), deps=deps,
                    pred_s=30.0, pred_gb=4.0))
def write_w():
    # the witness table loaded from binary (w2bin.py, G2.WLoad's #g2w): the list literal does not elaborate in reasonable time
    # at 182,520 rows; same value
    out = ['module', 'public import R22Port.U_d41d8cd98f00', 'public import G2.%s_Lits' % CX, 'public import E1.AsmG',
           'meta import G2.WLoad', '@[expose] public section', 'set_option maxRecDepth 10000000', 'set_option maxHeartbeats 0',
           '/-! # Glue witnesses of the chain `%s`: header record `j` of block `i` is glued to block `W[i][j]` (leaf2\'s' % CX,
           'E1/%s_W.lean, converted by g2/w2bin.py and loaded by `#g2w`) -/' % CX,
           '#g2w G2.%s "data/C%dX_W.bin"' % (CX, c), '']
    open(SRC + CX + '_W.lean', 'w').write('\n'.join(out))
    man.append(dict(module='G2.%s_W' % CX, src='src/G2/%s_W.lean' % CX, cwd='src', tier='g2', kind='w',
                    deps=['G2.%s_Lits' % CX], pred_s=30.0, pred_gb=8.0))
convert(L2 + 'E1/%s_Lits.lean' % CX, CX + '_Lits')
write_w()
for n in ('_N', ''): convert(L2 + 'E1/%s%s.lean' % (CX, n), CX + n)
for f in sorted(glob.glob(G + 'l2/E1/%s_B*.lean' % CX)): convert(f, os.path.basename(f)[:-5])
for f in sorted(glob.glob(L2 + 'E1/%s_*.lean' % EM)): convert(f, os.path.basename(f)[:-5])
for f in sorted(glob.glob(G + 'l2/L5/t/%s*.lean' % ES)): convert(f, os.path.basename(f)[:-5])
convert(L2 + 'E1/%s.lean' % EF, EF)
crown = 'Crown%d' % c
open(SRC + crown + '.lean', 'w').write('\n'.join([
    'module', 'public import R22Port.U_d41d8cd98f00', 'public import HC.Pad', 'public import E1.IP_e%d' % c,
    'public import RT.Cls_e%d' % c, 'import G2.%s' % EF, 'meta import KMod.Units', 'meta import KMod.Audit',
    'set_option Elab.async false',
    '/-! # The crown of class %d (G2): `HC.E1Concl Em 18` (E1 for the IP `e%d`), given the IP\'s class table' % (c, c),
    '',
    'The statement of `G2.%s.e%d_final` (leaf2\'s E1 route, kernel only), whose conclusion is literally the body of' % (EF, c),
    '`HC.E1Concl Em 18`. The job modules (chain, blocks, external leaves) are a private import. It replaces',
    '`E1NR1.Crown%d.crown g%d` (native glue and #ndbool) in R22B.CapLeaf2. -/' % (c, c),
    '#kpubterm G2.%s.crown : ∀ (hcls : ∀ c, RT.Fact (RT.kM RT.Cls_e%d.CL c) (RT.cLB RT.Cls_e%d.CL c)),' % (crown, c, c),
    '    HC.E1Concl E1.IP_e%d.Em 18 := fun hcls => G2.%s.e%d_final hcls' % (c, EF, c),
    '#kax G2.%s.crown' % crown, '#print axioms G2.%s.crown' % crown, '']))
man.append(dict(module='G2.' + crown, src='src/G2/%s.lean' % crown, cwd='src', tier='g2', kind='crown', deps=['G2.' + EF],
                pred_s=60.0, pred_gb=8.0))
with open(DATA + 'SHA256', 'a') as f:
    for src, dst in sorted(datamap.items()):
        h = hashlib.sha256(open(dst, 'rb').read()).hexdigest()
        f.write('%s  %s  (from %s)\n' % (h, os.path.basename(dst), os.path.relpath(src, L2)))
open(G + 'mod/manifest_c%d.jsonl' % c, 'w').write(''.join(json.dumps(x) + '\n' for x in man))
from collections import Counter
print('class', c, 'modules', len(man), dict(Counter(x['kind'] for x in man)), 'data files', len(datamap))
