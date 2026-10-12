#!/usr/bin/env python3
"""modhash.py: "one module name, one content" for Lean module stores.

Lean resolves `import A.B` through LEAN_PATH (then the toolchain's lib/lean): the FIRST entry that has a directory `A` (or a file
`A.olean`) is chosen and the module must be there (`Lean.SearchPath.findWithExt`); imported declarations are never re-checked.  So a
module built against one file for a name and later imported next to a different file for the same name has its statements read under
the other's definitions.  This tool makes that impossible to miss:

  record OLEAN MODULE [--lean-path LP] [--out FILE]
      at build time, right after MODULE was compiled to OLEAN with LEAN_PATH LP (default: $LEAN_PATH): read OLEAN's import header
      (OleanImports.lean: Lean.readModuleData), resolve every import exactly as Lean does, and write the record
      (default OLEAN with .olean replaced by .mhash; the lines can also be appended to a kmod .kman):
        KMH <module> olean=<sha256> private=<sha256|->       the module's own .olean / .olean.private
        KLP <LEAN_PATH as used>
        KIMP <import> <resolved .olean path> olean=<sha256> private=<sha256|-> all=<0|1> exp=<0|1> meta=<0|1>
  record-many LISTFILE
      the same for many modules with one header-reading process: LISTFILE lines "olean<TAB>module<TAB>LEAN_PATH[<TAB>out]"
  check [--store DIR[@LPFILE]]... [--universe DIR]... [--lean-path LP | --lean-path-file F] [--lpath-tsv F] [--manifest F]
        [--write-manifest F] [--map OLD=NEW]... [--jobs N] [--cache F]
      post hoc, over a store (every .olean under the --store directories; default: the --universe directories):
      U  rule 1 (universe): every .olean under every --universe directory (default: the store, the entries of the default LEAN_PATH and
         the toolchain's lib/lean) is hashed; a module name with two different .olean contents anywhere is a NAME-CONFLICT, even if no
         importer sees both;
      R  per store module: its record (.mhash next to the olean, or KMH/KLP/KIMP lines in a .kman) gives the LEAN_PATH it was built
         with and the hashes it saw; without a record the module's LEAN_PATH comes from --lpath-tsv ("module<TAB>LEAN_PATH"), else
         from its store's LPFILE (--store DIR@LPFILE: the LEAN_PATH that tree's build script uses), else the default.  Its imports are read from the olean itself and resolved through that LEAN_PATH: UNRESOLVED (no such file),
         RECORD-IMPORTS (the record's import list differs from the olean header), STALE (an import's file or resolution differs from
         what was recorded at build time), REBUILT (the module's own olean differs from its record);
      I  one content per name across everything resolved: an import name resolving to two different contents (from two importers, or
         differing from the store's own olean of that name) is an IMPORT-CONFLICT; .olean.private parts present on both sides and
         different are a PRIVATE-CONFLICT (one side without its private part is only counted);
      M  with --manifest ("module sha256-of-.olean" lines, the frozen manifest): every store module and every resolved import must
         match it: MANIFEST-MISMATCH; names absent from it are NOT-IN-MANIFEST.  --write-manifest writes that file for everything
         resolved (store modules and their imports, transitively through the store).
      --map OLD=NEW rewrites path prefixes in the records (KLP and KIMP paths) before they are used: a store built under OLD and
      re-materialized under NEW (e.g. the package tarballs extracted elsewhere) is checked against its records.
      Prints the violations and a SUMMARY line; exit 1 on any violation (NAME-CONFLICT, UNRESOLVED, RECORD-IMPORTS, STALE, PRIVATE-MISSING, REBUILT,
      IMPORT-CONFLICT, PRIVATE-CONFLICT, MANIFEST-MISMATCH, NOT-IN-MANIFEST).
Hashes are cached by (path, size, mtime) in --cache (default ~/.cache/modhash.json).  Toolchain: $MH_TC (default: the root of
the lean on PATH; its lib/lean ends the search path), LEAN binary: $LEAN or $MH_TC/bin/lean; OleanImports.lean: $MH_TOOL, else next to this file, else
../tools/."""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

TC = os.environ.get('MH_TC') or os.path.dirname(os.path.dirname(shutil.which('lean') or '/usr/bin/lean'))   # the toolchain root (bin/lean, lib/lean)
LEAN = os.environ.get('LEAN', TC + '/bin/lean')
SYSLIB = TC + '/lib/lean'
_here = os.path.dirname(os.path.realpath(__file__))
TOOL = os.environ.get('MH_TOOL') or next((t for t in (os.path.join(_here, 'OleanImports.lean'), os.path.join(_here, '..', 'tools', 'OleanImports.lean')) if os.path.exists(t)), '')

class Hasher:
    def __init__(self, cache, jobs):
        self.cf = cache; self.jobs = jobs
        try: self.c = json.load(open(cache))
        except Exception: self.c = {}
    def one(self, p):
        try: st = os.stat(p)
        except FileNotFoundError: return None
        k = os.path.realpath(p); e = self.c.get(k)
        if e and e[0] == st.st_size and e[1] == st.st_mtime_ns: return e[2]
        h = hashlib.sha256()
        with open(p, 'rb') as f:
            for b in iter(lambda: f.read(1 << 22), b''): h.update(b)
        d = h.hexdigest(); self.c[k] = [st.st_size, st.st_mtime_ns, d]; return d
    def many(self, ps):
        ps = list(dict.fromkeys(ps))
        with ThreadPoolExecutor(self.jobs) as ex: return dict(zip(ps, ex.map(self.one, ps)))
    def save(self):
        if not self.cf: return
        os.makedirs(os.path.dirname(self.cf) or '.', exist_ok=True)
        t = self.cf + '.tmp%d' % os.getpid(); json.dump(self.c, open(t, 'w')); os.replace(t, self.cf)

def lp_entries(lp):
    return [e for e in lp.split(':') if e] + [SYSLIB]

def resolve(entries, mod):
    """Lean's SearchPath.findWithExt "olean": the first entry with a directory (or .olean file) named after the root component"""
    comps = mod.split('.'); pkg = comps[0]
    for p in entries:
        if os.path.isdir(os.path.join(p, pkg)) or os.path.exists(os.path.join(p, pkg + '.olean')):
            return os.path.join(p, *comps) + '.olean'
    return None

def read_imports(oleans):
    """{olean: (isModule, [(module, all, exp, meta)])} via OleanImports.lean; errors as {olean: ('ERR', message)}"""
    out = {}
    if not oleans: return out
    with tempfile.TemporaryDirectory() as td:
        lf = os.path.join(td, 'l.txt'); of = os.path.join(td, 'o.txt')
        open(lf, 'w').write('\n'.join(oleans) + '\n')
        env = dict(os.environ); env.pop('LEAN_PATH', None)
        subprocess.run([LEAN, '--run', TOOL, lf, of], env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        cur = None
        for l in open(of):
            w = l.rstrip('\n').split(' ')
            if w[0] == 'OLEAN': cur = ' '.join(w[1:-2]); out[cur] = (w[-2] == '1', [])
            elif w[0] == 'IMP': out[cur][1].append((w[1], w[2], w[3], w[4]))
            elif w[0] == 'ERR': out[w[1]] = ('ERR', ' '.join(w[2:]))
    for o in oleans:
        out.setdefault(o, ('ERR', 'not read'))
    return out

def priv(p): return p + '.private'

def modname(root, path):
    return os.path.relpath(path, root)[:-len('.olean')].replace(os.sep, '.')

def walk_oleans(d):
    for r, _, fs in os.walk(d):
        for f in fs:
            if f.endswith('.olean'): yield os.path.join(r, f)

MAPS = []
def remap(p):
    for o, n in MAPS:
        p = p.replace(o, n)
    return p

def parse_record(path):
    rec = {'imports': []}
    for l in open(path, errors='replace'):
        w = l.rstrip('\n').split(' ')
        if w[0] == 'KMH': rec['module'] = w[1]; rec['olean'] = w[2].split('=', 1)[1]; rec['private'] = w[3].split('=', 1)[1]
        elif w[0] == 'KLP': rec['lpath'] = remap(' '.join(w[1:]))
        elif w[0] == 'KIMP':
            fl = dict(x.split('=', 1) for x in w[5:8] if '=' in x)
            rec['imports'].append((w[1], remap(w[2]), w[3].split('=', 1)[1], w[4].split('=', 1)[1], fl.get('all', '0')))
    return rec if 'module' in rec else None

def find_record(olean):
    base = olean[:-len('.olean')]
    for x in (base + '.mhash', base + '.kman'):
        if os.path.exists(x):
            r = parse_record(x)
            if r: return r, x
    return None, None

def write_record(H, olean, module, lp, imp, out):
    ent = lp_entries(lp); lines = []; own = H.many([olean, priv(olean)])
    lines.append('KMH %s olean=%s private=%s' % (module, own[olean], own[priv(olean)] or '-'))
    lines.append('KLP %s' % lp); bad = 0
    res = [(m, resolve(ent, m), f) for m, *f in imp]
    hs = H.many([p for _, p, _ in res if p] + [priv(p) for _, p, _ in res if p])
    for m, p, f in res:
        if p is None or hs.get(p) is None: bad += 1; lines.append('KIMP %s - olean=- private=- all=%s exp=%s meta=%s UNRESOLVED' % ((m,) + tuple(f))); continue
        lines.append('KIMP %s %s olean=%s private=%s all=%s exp=%s meta=%s' % (m, p, hs[p], hs.get(priv(p)) or '-', f[0], f[1], f[2]))
    open(out, 'w').write('\n'.join(lines) + '\n')
    return len(res), bad

def cmd_record_many(a):
    H = Hasher(a.cache, a.jobs); rows = []
    for l in open(a.listfile):
        w = l.rstrip('\n').split('\t')
        if len(w) >= 3: rows.append((w[0], w[1], w[2], w[3] if len(w) > 3 and w[3] else w[0][:-len('.olean')] + '.mhash'))
    heads = read_imports([r[0] for r in rows]); nbad = 0; nerr = 0
    for olean, module, lp, out in rows:
        h = heads[olean]
        if h[0] == 'ERR': nerr += 1; print('modhash record-many: cannot read %s: %s' % (olean, h[1])); continue
        n, bad = write_record(H, olean, module, lp, h[1], out); nbad += bad
        if bad: print('modhash record-many: %s: %d UNRESOLVED' % (module, bad))
    H.save(); print('modhash record-many: %d modules, %d unreadable, %d unresolved imports' % (len(rows), nerr, nbad))
    sys.exit(1 if nbad or nerr else 0)

def cmd_record(a):
    lp = a.lean_path if a.lean_path is not None else os.environ.get('LEAN_PATH', '')
    H = Hasher(a.cache, a.jobs); ent = lp_entries(lp)
    imp = read_imports([a.olean])[a.olean]
    if imp[0] == 'ERR': sys.exit('modhash record: cannot read %s: %s' % (a.olean, imp[1]))
    lines = []; own = H.many([a.olean, priv(a.olean)])
    lines.append('KMH %s olean=%s private=%s' % (a.module, own[a.olean], own[priv(a.olean)] or '-'))
    lines.append('KLP %s' % lp); bad = 0
    res = [(m, resolve(ent, m), f) for m, *f in imp[1]]
    hs = H.many([p for _, p, _ in res if p] + [priv(p) for _, p, _ in res if p])
    for m, p, f in res:
        if p is None or hs.get(p) is None: bad += 1; lines.append('KIMP %s - olean=- private=- all=%s exp=%s meta=%s UNRESOLVED' % ((m,) + tuple(f))); continue
        lines.append('KIMP %s %s olean=%s private=%s all=%s exp=%s meta=%s' % (m, p, hs[p], hs.get(priv(p)) or '-', f[0], f[1], f[2]))
    out = a.out or (a.olean[:-len('.olean')] + '.mhash')
    open(out, 'w').write('\n'.join(lines) + '\n'); H.save()
    print('modhash record: %s: %d imports%s -> %s' % (a.module, len(res), '' if not bad else ', %d UNRESOLVED' % bad, out))
    sys.exit(1 if bad else 0)

def cmd_check(a):
    for x in a.map:
        o, n = x.split('=', 1); MAPS.append((o, n))
    H = Hasher(a.cache, a.jobs)
    deflp = a.lean_path if a.lean_path is not None else (open(a.lean_path_file).read().strip() if a.lean_path_file else os.environ.get('LEAN_PATH', ''))
    slp = {}
    for x in a.store:
        if '@' in x: d, f = x.rsplit('@', 1); slp[d] = open(f).read().strip()
    stores = [x.rsplit('@', 1)[0] for x in a.store] or a.universe
    if not stores: sys.exit('modhash check: give --store and/or --universe directories')
    universe = a.universe or list(dict.fromkeys(stores + [e for e in lp_entries(deflp)] + [e for v in slp.values() for e in lp_entries(v)]))
    lptsv = {}
    if a.lpath_tsv:
        for l in open(a.lpath_tsv):
            if '\t' in l: m, p = l.rstrip('\n').split('\t', 1); lptsv[m] = p
    viol = []; info = []
    def V(kind, msg): viol.append((kind, msg))
    # U: the universe
    files = {}
    for d in universe:
        for p in walk_oleans(d): files[p] = modname(d, p)
    hs = H.many(list(files))
    byname = {}
    for p, m in files.items():
        if hs[p] is not None: byname.setdefault(m, {}).setdefault(hs[p], []).append(p)
    for m, d in sorted(byname.items()):
        if len(d) > 1:
            V('NAME-CONFLICT', '%s: %s' % (m, '; '.join('%s… %s' % (h[:12], ', '.join(sorted(ps)[:3]) + (' +%d' % (len(ps) - 3) if len(ps) > 3 else '')) for h, ps in sorted(d.items()))))
    # R: store modules
    smods = {}; sdir = {}
    for d in stores:
        for p in walk_oleans(d): smods[p] = modname(d, p); sdir[p] = d
    heads = read_imports(sorted(smods))
    content = {}      # name -> {sha: [who]}
    pcontent = {}     # name -> {sha: [who]}
    def add(name, sha, psha, who):
        content.setdefault(name, {}).setdefault(sha, []).append(who)
        if psha: pcontent.setdefault(name, {}).setdefault(psha, []).append(who)
    need = []
    plan = []
    nrec = 0
    for p, m in sorted(smods.items()):
        own = H.one(p); ownp = H.one(priv(p)); add(m, own, ownp, 'store:' + p)
        rec, rp = find_record(p)
        if rec: nrec += 1
        lp = rec['lpath'] if rec and 'lpath' in rec else lptsv.get(m, slp.get(sdir[p], deflp))
        if rec and rec.get('olean') not in (None, own): V('REBUILT', '%s: olean %s… now, %s… in its record %s' % (m, own[:12], rec['olean'][:12], rp))
        if rec and rec.get('private') not in (None, '-') and ownp is not None and rec['private'] != ownp:
            V('REBUILT', '%s: .olean.private %s… now, %s… in its record %s' % (m, ownp[:12], rec['private'][:12], rp))
        h = heads[p]
        if h[0] == 'ERR': V('UNRESOLVED', '%s: cannot read its header: %s' % (p, h[1])); continue
        ent = lp_entries(lp); res = []
        for im, *f in h[1]:
            q = resolve(ent, im)
            if q is None or not os.path.exists(q): V('UNRESOLVED', '%s imports %s: no file through its LEAN_PATH' % (m, im)); continue
            res.append((im, q)); need += [q, priv(q)]
        plan.append((p, m, rec, rp, res))
        if rec:
            ri = [x[0] for x in rec['imports']]; hi = [x[0] for x in h[1]]
            if ri != hi: V('RECORD-IMPORTS', '%s: record %s lists %d imports, the olean %d' % (m, rp, len(ri), len(hi)))
    ih = H.many(need)
    for p, m, rec, rp, res in plan:
        recd = {x[0]: x for x in rec['imports']} if rec else {}
        for im, q in res:
            add(im, ih[q], ih.get(priv(q)), '%s->%s' % (m, q))
            if im in recd:
                _, rq, ro, rpv, al = recd[im]
                if rq != q or ro != ih[q]:
                    V('STALE', '%s imports %s: built against %s (%s…), now %s (%s…)' % (m, im, rq, ro[:12], q, ih[q][:12]))
                elif al == '1':
                    # a private-level import (`import all`): the build used the import's private part too, so that part must be
                    # present and the one recorded (same public olean with another private part = another module)
                    cur = ih.get(priv(q))
                    if cur is None: V('PRIVATE-MISSING', '%s imports all of %s: built against private part %s…, none present at %s' % (m, im, rpv[:12], priv(q)))
                    elif rpv != cur: V('STALE', '%s imports all of %s: built against private part %s…, now %s…' % (m, im, rpv[:12], cur[:12]))
                    if rpv not in (None, '-'): add(im, ih[q], rpv, 'record:%s' % m)
    # I: one content per name
    for m, d in sorted(content.items()):
        if len(d) > 1:
            V('IMPORT-CONFLICT', '%s: %s' % (m, '; '.join('%s… <- %s' % (h[:12], ', '.join(w[:2]) + (' +%d' % (len(w) - 2) if len(w) > 2 else '')) for h, w in sorted(d.items()))))
    for m, d in sorted(pcontent.items()):
        if len(d) > 1: V('PRIVATE-CONFLICT', '%s: %d different .olean.private contents' % (m, len(d)))
    # M: manifest
    if a.manifest:
        man = {}
        for l in open(a.manifest):
            w = l.split()
            if len(w) >= 2: man[w[0]] = w[1]
        for m, d in sorted(content.items()):
            for h in d:
                if m not in man: V('NOT-IN-MANIFEST', m)
                elif man[m] != h: V('MANIFEST-MISMATCH', '%s: %s… resolved, %s… in the manifest' % (m, h[:12], man[m][:12]))
    if a.write_manifest:
        open(a.write_manifest, 'w').write(''.join('%s %s\n' % (m, next(iter(d))) for m, d in sorted(content.items()) if len(d) == 1))
    H.save()
    vcounts = {}
    for k, msg in viol:
        vcounts[k] = vcounts.get(k, 0) + 1
        if vcounts[k] <= a.show: print('%s %s' % (k, msg))
    print('SUMMARY universe_files=%d universe_names=%d store_modules=%d records=%d names_resolved=%d violations=%d %s' % (
        len(files), len(byname), len(smods), nrec, len(content), len(viol), ' '.join('%s=%d' % kv for kv in sorted(vcounts.items()))))
    sys.exit(1 if viol else 0)

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest='cmd', required=True)
    r = sp.add_parser('record'); r.add_argument('olean'); r.add_argument('module'); r.add_argument('--lean-path'); r.add_argument('--out')
    rm = sp.add_parser('record-many'); rm.add_argument('listfile')
    c = sp.add_parser('check'); c.add_argument('--store', action='append', default=[]); c.add_argument('--universe', action='append', default=[])
    c.add_argument('--lean-path'); c.add_argument('--lean-path-file'); c.add_argument('--lpath-tsv'); c.add_argument('--manifest')
    c.add_argument('--write-manifest'); c.add_argument('--show', type=int, default=50); c.add_argument('--map', action='append', default=[])
    for x in (r, rm, c):
        x.add_argument('--jobs', type=int, default=16); x.add_argument('--cache', default=os.path.expanduser('~/.cache/modhash.json'))
    a = ap.parse_args()
    {'record': cmd_record, 'record-many': cmd_record_many, 'check': cmd_check}[a.cmd](a)

main()
