#!/usr/bin/env python3
"""kmod.py: emitter-side helpers of the KMod library (rules: AUDIT.md).

Literal files:   write_lits(path, lits) / read_lits(path)   (the `#e1lits` format: u32 count, then u32 nbytes + LE bytes each)
Module sources:  unit_module(...) for a module that checks unit groups and exports one theorem; agg_module(...) for an
                 aggregator over child modules (private imports, a term proof); write_module(src_root, mod, text).
Trees:           agg_tree(items, fanin, mk_agg) builds the aggregation levels; write_plan(path, stages) for kmod_plan.sh.
Every module gets `#kax <thm>` (the per-module audit; kmod_build.sh refuses a module without a clean KAXSUM); the root
should also get `#kaxp <thm>`.  Theorem names default to `<module>.ok`.
"""
import os, struct

def write_lits(path, lits):
    with open(path, 'wb') as f:
        f.write(struct.pack('<I', len(lits)))
        for x in lits:
            b = x.to_bytes((x.bit_length() + 7) // 8, 'little') if x else b''
            f.write(struct.pack('<I', len(b))); f.write(b)

def read_lits(path):
    b = open(path, 'rb').read(); n = struct.unpack_from('<I', b, 0)[0]; off = 4; out = []
    for _ in range(n):
        nb = struct.unpack_from('<I', b, off)[0]; off += 4
        out.append(int.from_bytes(b[off:off + nb], 'little')); off += nb
    return out

def _q(s):
    return '"' + str(s).replace('\\', '\\\\').replace('"', '\\"') + '"'

HEADER_OPTS = 'set_option Elab.async false\nset_option maxRecDepth 100000\n'

def unit_module(mod, vocab, groups, stmt, comb=None, comb_groups=None, term=None, thm=None, meta_imports=(),
                priv_imports=(), keys=None, ext=(), kaxp=False):
    """Source of a unit module.
    vocab:        public imports (the statement vocabulary, and whatever the checkers unfold, all @[expose])
    groups:       [(G, lit_path, arity, checker_term)], checker_term a Lean term of type Nat → Bool
    stmt:         the public statement (Lean term over the public vocabulary)
    comb:         the combinator constant (type KMod.Combinator) and comb_groups the groups it gets (default: all), or
    term:         a proof term instead
    meta_imports: the emitter's combinator module(s); priv_imports: proof-only modules (KMod.Vocab is always imported)
    keys:         (first, last) for KKEY; ext: labels for KEXT"""
    thm = thm or mod + '.ok'
    s = ['module'] + ['public import %s' % v for v in vocab]
    s += ['meta import KMod.Units', 'meta import KMod.Audit'] + ['meta import %s' % m for m in meta_imports]
    s += ['import KMod.Vocab'] + ['import %s' % m for m in priv_imports]
    s.append(HEADER_OPTS.rstrip('\n'))
    for g, path, k, chk in groups:
        s.append('#kunits %s %s %d (%s)' % (g, _q(path), k, chk))
    if comb is not None:
        s.append('#kpub %s : %s := %s %s' % (thm, stmt, comb, ' '.join(comb_groups or [g[0] for g in groups])))
    else:
        s.append('#kpubterm %s : %s := %s' % (thm, stmt, term))
    s.append('#kax %s' % thm)
    if kaxp: s.append('#kaxp %s' % thm)
    if keys: s.append('#kkey %s %s' % (_q(keys[0]), _q(keys[1])))
    if ext: s.append('#kext ' + ' '.join(_q(e) for e in ext))
    return '\n'.join(s) + '\n'

def agg_module(mod, vocab, children, stmt, term, thm=None, priv_imports=(), kaxp=False):
    """Source of an aggregator: private imports of the child modules, one public theorem proved by `term` (which names the
    children's theorems)."""
    thm = thm or mod + '.ok'
    s = ['module'] + ['public import %s' % v for v in vocab]
    s += ['meta import KMod.Units', 'meta import KMod.Audit'] + ['import %s' % c for c in children]
    s += ['import %s' % m for m in priv_imports]
    s.append(HEADER_OPTS.rstrip('\n'))
    s.append('#kpubterm %s : %s := %s' % (thm, stmt, term))
    s.append('#kax %s' % thm)
    if kaxp: s.append('#kaxp %s' % thm)
    return '\n'.join(s) + '\n'

def write_module(src_root, mod, text):
    p = os.path.join(src_root, *mod.split('.')) + '.lean'
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w').write(text)
    return p

def agg_tree(items, fanin, mk_agg):
    """items: [(module, payload)] of stage 0.  mk_agg(level, j, kids) -> (module, payload), called for each aggregator of
    level >= 1 over kids = [(module, payload)] (at most `fanin`; the caller writes the source there).  Returns
    (stages, (root_module, root_payload)), stages[0] = the item modules."""
    stages = [[m for m, _ in items]]; cur = list(items); lev = 0
    while len(cur) > 1:
        lev += 1; nxt = []
        for j in range(0, len(cur), fanin):
            nxt.append(mk_agg(lev, j // fanin, cur[j:j + fanin]))
        stages.append([m for m, _ in nxt]); cur = nxt
    return stages, cur[0]

def write_plan(path, stages):
    open(path, 'w').write(''.join(' '.join(s) + '\n' for s in stages))
