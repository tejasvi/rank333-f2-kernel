#!/usr/bin/env python3
"""mkexttop.py CAP CHUNKS OUTDIR [--order ROOTEXT] [--root-module M] [--slice 1000] [--maxch 100] [--fan 100]: the EXT top of a cap
(aggregation) over the EXT packages' chunks. v4 (2026-10-10): CC caps (436, 422) without big literals above the slices.

CHUNKS: one line per EXT package chunk, "<chunk module> <pl>,<pl>,…" (CC: `<chunk>.ok : ∀ (ext : List ℕ), ∀ pl ∈ [pls],
L479.LeafNoExt (E1G.OK_c<CAP>.Cx ext) E1G.IP_c<CAP>.Em 14 pl`; class h<c>: `<chunk>.ok : ∀ pl ∈ [pls], S5.NoDecomp …`; extpkg.py,
`extscan.py chunks CAP`). ENTRIES = the ROOTEXT list (--order: the E1G emitter's `KJ.agg<CAP>.Root.EXT` or the class route's `KC.h<c>.EXT`, in its
order, duplicates kept; one pl per line), else the chunks' lists concatenated. Slices: at most SLICE entries and at most MAXCH distinct
chunks each (cut early when the next entry needs a new chunk beyond MAXCH), each entry by its chunk's theorem and a membership
`decide +kernel` in that chunk's list (<= 32 entries).
CC caps (v4), in OUTDIR/src/PLE/c<CAP>/:
  S<j>.lean      `@[expose] public def PLE.c<CAP>.S<j>.EXT : List ℕ := [slice]` and `PLE.c<CAP>.S<j>.ok : ∀ (ext : List ℕ), ∀ pl ∈
                 PLE.c<CAP>.S<j>.EXT, LeafNoExt …` (imports its chunks privately);
  L<l>_<k>.lean  levels of at most FAN children until at most FAN remain: `EXT := c1.EXT ++ (c2.EXT ++ (… ++ cn.EXT))` (right-nested)
                 and `ok` by `List.mem_append` (no literal, no decide); children imported publicly (their EXT must unfold downstream);
  Ext.lean       `PLE.c<CAP>.Ext.EXT` (the same over the top parts) and `PLE.c<CAP>.Ext.hext_of : ∀ (ext : List ℕ), (∀ pl ∈ ext, pl ∈
                 PLE.c<CAP>.Ext.EXT) → ∀ pl ∈ ext, LeafNoExt (E1G.OK_c<CAP>.Cx ext) E1G.IP_c<CAP>.Em 14 pl`;
  Sub.lean       (with --order and --root-module, the module of the E1G emitter's root, KJ.agg<CAP>_Root) `PLE.c<CAP>.Sub.sub : ∀ pl ∈
                 KJ.agg<CAP>.Root.EXT, pl ∈ PLE.c<CAP>.Ext.EXT`: the flattened tree is ENTRIES (asserted here), so the two lists are
                 equal; the kernel checks it once (SUBPROOF below), the only step that walks all ENTRIES.
  The final instance passes `_ PLE.c<CAP>.Ext.hext_of PLE.c<CAP>.Sub.sub` (all<C> := PLE.c<CAP>.Ext.EXT).
Class caps h<c> (v3 form, unchanged statements), in OUTDIR/src/NDX/h<c>/: S<j> over literals, levels `have e : [all] = [a] ++ ([b] ++ …)
  := by decide +kernel` (right-nested since v4) and the top NDX.h<c>.Top with `NDX.h<c>.x<c> : ∀ pl ∈ [KC.h<c>.EXT's literal], …`.
Also OUTDIR/manifest.jsonl (sched.py lines; `pub` on the top, and for a CC cap on every module: the whole tree is imported
publicly by Sub, so every module must reach the final store) and OUTDIR/ALL.txt. Every module has one KPUB (#kpubterm) and #kax."""
import sys, os, json
sys.set_int_max_str_digits(0)
CC = {'436': dict(imps=['S4.CCLeaf', 'S4.CC436'], cx='E1G.OK_c436.Cx', ns='E1G.IP_c436'),
      '422': dict(imps=['S4.CCLeaf', 'LG.IPC422'], cx='E1G.OK_c422.Cx', ns='E1G.IP_c422')}
OPTS = ['meta import KMod.Units', 'meta import KMod.Audit', 'set_option Elab.async false', 'set_option maxHeartbeats 0',
        'set_option maxRecDepth 100000']
cap, chf, out = sys.argv[1], sys.argv[2], os.path.abspath(sys.argv[3])
def opt(n, d): return type(d)(sys.argv[sys.argv.index(n) + 1]) if n in sys.argv else d
ORDER, SLICE, MAXCH, FAN = opt('--order', ''), opt('--slice', 1000), opt('--maxch', 100), opt('--fan', 100)
ROOTMOD = opt('--root-module', '')
CLASS = cap.startswith('h')          # a class-raise class h<c>: chunks NDX.h<c>.X<…>.ok (NoDecomp), top NDX.h<c>.Top with x<c>
if CLASS:
    ns = 'E1G.IP_' + cap
    cfg = dict(imps=['R22Port.U_d41d8cd98f00', 'HCap.IP_' + cap, 'S4.SplitRN'], ns=ns)
else:
    cfg = CC[cap]
chunks = []
for ln in open(chf):
    t = ln.split()
    if len(t) == 2 and not t[0].startswith('#'): chunks.append((t[0], [int(x) for x in t[1].split(',')]))
assert chunks, 'no chunks'
d = os.path.join(out, 'src', *(('NDX', cap) if cap.startswith('h') else ('PLE', 'c%s' % cap))); os.makedirs(d, exist_ok=True)
lit = lambda ps: '[%s]' % ', '.join(map(str, ps))
def stmt(lst):
    if CLASS:
        r0 = 'E1G.leafRec %s.R %s.VT %s.DOM pl 0' % (cfg['ns'], cfg['ns'], cfg['ns'])
        return '∀ pl ∈ %s, S5.NoDecomp (S5.leafT (%s)) (S5.leafN (%s)) (S6.leafDom6 (%s))' % (lst, r0, r0, r0)
    return '∀ (ext : List ℕ), ∀ pl ∈ %s, L479.LeafNoExt (%s ext) %s.Em 14 pl' % (lst, cfg['cx'], cfg['ns'])
PFX = 'NDX.%s' % cap if CLASS else 'PLE.c%s' % cap
EXTV = '' if CLASS else 'ext '            # the class statement has no ext binder
def head(): return ['module'] + ['public import ' + x for x in cfg['imps']]
man = []
def emit(name, rel, kind, deps, lines, n):
    open(os.path.join(d, rel), 'w').write('\n'.join(lines))
    man.append(dict(module=name, src='src/%s/%s' % (PFX.replace('.', '/'), rel), cwd='src', tier='ext', kind=kind, deps=deps,
                    pred_s=round(10.0 + 0.004 * n, 1), pred_gb=round(7.0 + 0.00003 * n, 2)))   # the imports alone: ~6.5 GB
where = {}
for ci, (_, ps) in enumerate(chunks):
    for p in ps: where.setdefault(p, ci)
entries = [int(l) for l in open(ORDER) if l.strip()] if ORDER else [p for _, ps in chunks for p in ps]
miss = [p for p in entries if p not in where]
assert not miss, '%d entries are in no chunk, e.g. %d' % (len(miss), miss[0])
# slices
slices, cur, used = [], [], set()
for p in entries:
    c = where[p]
    if cur and (len(cur) >= SLICE or (c not in used and len(used) >= MAXCH)):
        slices.append((cur, used)); cur, used = [], set()
    cur.append(p); used.add(c)
if cur: slices.append((cur, used))
parts = []         # (module, theorem, entries)
SUBV = opt('--subproof', 'B')
def SUBPROOF(sub, rx, ax):
    if SUBV == 'A':      # kernel defeq of the two lists (the elaborator checks it too)
        return ['#kpubterm %s.sub : ∀ pl ∈ %s, pl ∈ %s := fun _ h => h' % (sub, rx, ax)]
    if SUBV == 'B':      # List.beq evaluated by the kernel, then LawfulBEq
        return ['theorem %s.e : %s = %s := eq_of_beq (by decide +kernel)' % (sub, rx, ax),
                '#kpubterm %s.sub : ∀ pl ∈ %s, pl ∈ %s := fun pl h => %s.e ▸ h' % (sub, rx, ax, sub)]
    if SUBV == 'C':      # List's DecidableEq evaluated by the kernel
        return ['theorem %s.e : %s = %s := by decide +kernel' % (sub, rx, ax),
                '#kpubterm %s.sub : ∀ pl ∈ %s, pl ∈ %s := fun pl h => %s.e ▸ h' % (sub, rx, ax, sub)]
    raise ValueError(SUBV)
def chain(sl, ev):
    """the slice proof: `List.forall_mem_cons.2 ⟨<chunk>.ok [ext] p (by decide +kernel), …, List.forall_mem_nil _⟩`, linear in the slice (an
    n-way `rcases … rfl` over the membership disjunction is super-quadratic: 427 entries took 2,700 s, the chain 8 s)"""
    t = 'List.forall_mem_nil _'
    for p in reversed(sl): t = 'List.forall_mem_cons.2 ⟨%s.ok %s%d (by decide +kernel), %s⟩' % (chunks[where[p]][0], ev, p, t)
    return t
def rnest(xs):
    """x1 ++ (x2 ++ (… ++ xn)): right-nested, so `simp only [List.mem_append]` gives `_ ∨ (_ ∨ …)` and `rcases h | h | …` takes the
    parts in order (a left-nested `++` gives `(_ ∨ _) ∨ _`, which rcases does not split that way)"""
    return xs[0] if len(xs) == 1 else '%s ++ (%s)' % (xs[0], rnest(xs[1:]))
parts = []         # (module, theorem, entries)
if CLASS:
    # v3 form: statements over literals (NDX.h<c>.x<c> must be DEFEQ to KC.h<c>.EXT's literal)
    for j, (sl, used) in enumerate(slices):
        name = '%s.S%d' % (PFX, j); cs = sorted(used)
        L = head() + ['import ' + chunks[c][0] for c in cs] + OPTS + [
            '/-! EXT top of %s, slice %d (%d entries, %d chunks; generated by s443/extpkg/mkexttop.py v4) -/' % (cap, j, len(sl), len(cs)),
            '#kpubterm %s.ok : %s :=' % (name, stmt(lit(sl))), '  ' + chain(sl, ''), '#kax %s.ok' % name, '']
        emit(name, 'S%d.lean' % j, 'glue', [chunks[c][0] for c in cs], L, len(sl))
        parts.append((name, name + '.ok', sl))
    def join_proof(ps):
        allp = [p for _, _, e in ps for p in e]
        if len(ps) == 1: return ['  intro %spl hpl' % EXTV, '  exact %s %spl hpl' % (ps[0][1], EXTV)], allp
        L = ['  intro %spl hpl' % EXTV,
             '  have e : %s = %s := by decide +kernel' % (lit(allp), rnest([lit(e) for _, _, e in ps])),
             '  rw [e] at hpl', '  simp only [List.mem_append] at hpl', '  rcases hpl with ' + ' | '.join(['h'] * len(ps))]
        L += ['  · exact %s %spl h' % (th, EXTV) for _, th, _ in ps]
        return L, allp
    lvl = 0
    while len(parts) > FAN:
        nxt = []
        for k in range(0, len(parts), FAN):
            grp = parts[k:k + FAN]; name = '%s.L%d_%d' % (PFX, lvl, k // FAN)
            pr, allp = join_proof(grp)
            L = head() + ['import ' + m for m, _, _ in grp] + OPTS + [
                '/-! EXT top of %s, level %d, part %d (%d entries; generated by s443/extpkg/mkexttop.py) -/' % (cap, lvl, k // FAN, len(allp)),
                '#kpubterm %s.ok : %s := by' % (name, stmt(lit(allp)))] + pr + ['#kax %s.ok' % name, '']
            emit(name, 'L%d_%d.lean' % (lvl, k // FAN), 'glue', [m for m, _, _ in grp], L, len(allp))
            nxt.append((name, name + '.ok', allp))
        parts = nxt; lvl += 1
    pr, allp = join_proof(parts)
    assert allp == entries
    top = 'NDX.%s.Top' % cap; xn = 'x' + cap[1:]
    L = head() + ['import ' + m for m, _, _ in parts] + OPTS + [
        '/-! EXT top of class %s: %d chunks, %d slices, %d levels, %d entries; the class root\'s `%s` (generated by '
        's443/extpkg/mkexttop.py) -/' % (cap, len(chunks), len(slices), lvl, len(entries), xn),
        '#kpubterm NDX.%s.%s : %s := by' % (cap, xn, stmt(lit(allp)))] + pr + [
        '#kax NDX.%s.%s' % (cap, xn), '#print axioms NDX.%s.%s' % (cap, xn), '']
    emit(top, 'Top.lean', 'top', [m for m, _, _ in parts], L, len(allp))
    man[-1]['pub'] = 'NDX.%s.%s' % (cap, xn)
else:
    # v4: each slice's list is an exposed def; levels and the top are appends of their children's defs (no literal, no decide)
    for j, (sl, used) in enumerate(slices):
        name = '%s.S%d' % (PFX, j); cs = sorted(used)
        L = head() + ['import ' + chunks[c][0] for c in cs] + OPTS + [
            '/-! EXT top of c%s, slice %d (%d entries, %d chunks; generated by s443/extpkg/mkexttop.py v4) -/' % (cap, j, len(sl), len(cs)),
            '@[expose] public def %s.EXT : List ℕ := %s' % (name, lit(sl)),
            '#kpubterm %s.ok : %s :=' % (name, stmt(name + '.EXT')), '  fun ext => ' + chain(sl, 'ext '), '#kax %s.ok' % name, '']
        emit(name, 'S%d.lean' % j, 'glue', [chunks[c][0] for c in cs], L, len(sl))
        man[-1]['pub'] = name + '.ok'        # v4: every module is public (the final instance imports the whole tree through Sub)
        parts.append((name, name + '.ok', sl))
    def join_lines(name, grp):
        return ['@[expose] public def %s.EXT : List ℕ := %s' % (name, rnest([m + '.EXT' for m, _, _ in grp])),
                '#kpubterm %s.ok : %s := by' % (name, stmt(name + '.EXT')), '  intro ext pl hpl',
                '  simp only [%s.EXT, List.mem_append] at hpl' % name] + (
                ['  rcases hpl with ' + ' | '.join(['h'] * len(grp))] + ['  · exact %s ext pl h' % th for _, th, _ in grp]
                if len(grp) > 1 else ['  exact %s ext pl hpl' % grp[0][1]])
    lvl = 0
    import math
    if '--fan-auto' in sys.argv:
        # one level only, so the top parts (the root-list check's segments SubS<k>) stay small: fan >= sqrt(#slices)
        FAN = max(FAN, math.isqrt(len(parts) - 1) + 1)
    while len(parts) > FAN:
        nxt = []
        for k in range(0, len(parts), FAN):
            grp = parts[k:k + FAN]; name = '%s.L%d_%d' % (PFX, lvl, k // FAN)
            allp = [p for _, _, e in grp for p in e]
            L = head() + ['public import ' + m for m, _, _ in grp] + OPTS + [
                '/-! EXT top of c%s, level %d, part %d (%d children, %d entries; generated by s443/extpkg/mkexttop.py v4) -/' % (
                    cap, lvl, k // FAN, len(grp), len(allp))] + join_lines(name, grp) + ['#kax %s.ok' % name, '']
            emit(name, 'L%d_%d.lean' % (lvl, k // FAN), 'glue', [m for m, _, _ in grp], L, len(grp))
            man[-1]['pub'] = name + '.ok'
            nxt.append((name, name + '.ok', allp))
        parts = nxt; lvl += 1
    allp = [p for _, _, e in parts for p in e]
    assert allp == entries
    top = 'PLE.c%s.Ext' % cap
    L = head() + ['public import ' + m for m, _, _ in parts] + OPTS + [
        '/-! EXT top of c%s: %d chunks, %d slices, %d levels, %d entries%s; `hext_of` for the final instance, with all<C> := '
        '`PLE.c%s.Ext.EXT` (generated by s443/extpkg/mkexttop.py v4) -/' % (cap, len(chunks), len(slices), lvl, len(entries),
                                                                          ' (the root EXT list)' if ORDER else '', cap)]
    L += join_lines(top, parts)[:1]
    L += ['theorem %s.okAll : %s := by' % (top, stmt(top + '.EXT'))] + join_lines(top, parts)[2:]
    L += ['#kpubterm %s.hext_of : ∀ (ext : List ℕ), (∀ pl ∈ ext, pl ∈ %s.EXT) →' % (top, top),
          '    ∀ pl ∈ ext, L479.LeafNoExt (%s ext) %s.Em 14 pl := fun ext h pl hp => %s.okAll ext pl (h pl hp)' % (cfg['cx'], cfg['ns'], top),
          '#kax %s.hext_of' % top, '#print axioms %s.hext_of' % top, '']
    emit(top, 'Ext.lean', 'top', [m for m, _, _ in parts], L, len(parts))
    man[-1]['pub'] = top + '.hext_of'
    SPLIT = opt('--subsplit', 120000)
    if ORDER and ROOTMOD and len(entries) > SPLIT and len(parts) > 1:
        # v4b (2026-10-10): the equality split over the top parts, one module each (they build in parallel): SubS<k> proves
        # `(ROOT.drop a_k).take n_k = P_k.EXT` (the last one `ROOT.drop a_k = P_k.EXT`) by the kernel's List.beq; Sub chains them with
        # List.take_append_drop / List.drop_drop (no computation). The whole check took 287 s for c422's 96,469 entries locally.
        sub = 'PLE.c%s.Sub' % cap; rx = 'KJ.agg%s.Root.EXT' % cap
        offs = []; a = 0
        for m_, _, e in parts: offs.append((m_, a, len(e))); a += len(e)
        segs = []
        for k, (m_, a, n) in enumerate(offs):
            sk = '%s.SubS%d' % (PFX, k); last = k == len(offs) - 1
            lhs = '%s.drop %d' % (rx, a) if last else '(%s.drop %d).take %d' % (rx, a, n)
            L = ['module', 'public import ' + m_, 'public import ' + ROOTMOD] + OPTS + [
                '/-! `%s.seg`: entries %d..%d of hcls\'s root list are %s.EXT (generated by s443/extpkg/mkexttop.py v4b) -/' % (sk, a, a + n, m_),
                'theorem %s.e : %s = %s.EXT := eq_of_beq (by decide +kernel)' % (sk, lhs, m_),
                '#kpubterm %s.seg : %s = %s.EXT := %s.e' % (sk, lhs, m_, sk), '#kax %s.seg' % sk, '']
            emit(sk, 'SubS%d.lean' % k, 'top', [m_], L, n)
            man[-1].update(pred_s=round(30 + 0.004 * n, 1), pred_gb=round(7 + 0.00004 * n, 2), pub=sk + '.seg')
            segs.append((sk, a, n))
        chainE = segs[-1][0] + '.seg'
        for sk, a, n in reversed(segs[:-1]):
            chainE = 'PLE.c%s.Sub.cons_seg (by decide) %s.seg (%s)' % (cap, sk, chainE) if False else '%s.cons_seg (b := %d) (by decide) %s.seg (%s)' % (sub, a + n, sk, chainE)
        L = ['module', 'public import ' + top, 'public import ' + ROOTMOD] + ['public import ' + sk for sk, _, _ in segs] + OPTS + [
            '/-! `%s.sub`: hcls\'s root list is the EXT top\'s list (%d entries, same order, duplicates kept), from the %d segments SubS<k>; '
            'the final instance\'s sub<C> (generated by s443/extpkg/mkexttop.py v4b) -/' % (sub, len(entries), len(segs)),
            'theorem %s.cons_seg {l P R : List ℕ} {a n b : ℕ} (hb : a + n = b) (h1 : (l.drop a).take n = P) (h2 : l.drop b = R) :' % sub,
            '    l.drop a = P ++ R := by',
            '  subst hb', '  rw [← h1, ← h2, ← List.drop_drop]', '  exact (List.take_append_drop n (l.drop a)).symm',
            'theorem %s.e : %s = %s.EXT := by' % (sub, rx, top),
            '  have h : %s.drop 0 = %s := %s' % (rx, rnest([m_ + '.EXT' for m_, _, _ in offs]), chainE),
            '  rw [List.drop_zero] at h', '  exact h',
            '#kpubterm %s.sub : ∀ pl ∈ %s, pl ∈ %s.EXT := fun pl h => %s.e ▸ h' % (sub, rx, top, sub),
            '#kax %s.sub' % sub, '#print axioms %s.sub' % sub, '']
        emit(sub, 'Sub.lean', 'top', [top] + [sk for sk, _, _ in segs], L, len(segs))
        man[-1].update(pred_s=60.0, pred_gb=8.0, pub=sub + '.sub')
    elif ORDER and ROOTMOD:
        # the only step over all entries: KJ.agg<CAP>.Root.EXT (the E1G emitter's raw-literal list) = PLE.c<CAP>.Ext.EXT (the tree), by the kernel
        sub = 'PLE.c%s.Sub' % cap; rx = 'KJ.agg%s.Root.EXT' % cap
        L = ['module', 'public import ' + top, 'public import ' + ROOTMOD] + OPTS + [
            '/-! `%s.sub`: hcls\'s root list is the EXT top\'s list (%d entries, same order, duplicates kept); the final instance\'s '
            'sub<C> (generated by s443/extpkg/mkexttop.py v4) -/' % (sub, len(entries))] + SUBPROOF(sub, rx, top + '.EXT') + [
            '#kax %s.sub' % sub, '#print axioms %s.sub' % sub, '']
        emit(sub, 'Sub.lean', 'top', [top], L, len(entries))
        # 300k entries (scale test): 64 s, 16.8 GB (List.beq over the tree, kernel)
        man[-1].update(pred_s=round(30 + 0.0005 * len(entries), 1), pred_gb=round(7 + 0.00004 * len(entries), 2), pub=sub + '.sub')
open(os.path.join(out, 'manifest.jsonl'), 'w').write(''.join(json.dumps(x) + '\n' for x in man))
open(os.path.join(out, 'ALL.txt'), 'w').write(''.join('%d\n' % p for p in allp))
print('%s: %d chunks, %d slices, %d levels, %d entries -> %s' % (cap, len(chunks), len(slices), lvl, len(entries), man[-1]['pub']))
