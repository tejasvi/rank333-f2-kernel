#!/usr/bin/env python3
"""sbtables.py: the split / heavy-leaf tables each split-build package must build so that its audit can import, at the
exported level, every lifted module its walk reaches (the worker's KModTyChk imports each lifted module whose NS.EXT another
module uses; a lifted range or aggregator publicly imports its table, and tables are never shipped in pubs).
  lifted(m)  = m has its own external leaves (#kext lines) or imports a lifted module
  checked    = the lifted children of every module whose list has >= 2 segments (own leaves, lifted children): their NS.EXT
               occur in its proof, so the audit imports them at the exported level
  need(P)    = the tables P's modules import  +  the tables publicly imported by every checked module reachable from P
For every family in $R22_ROOT/e1g/pkg/sb/READY.txt (and its re-cut, RECUT.txt), prints the packages whose manifest lacks tables of need(P),
and writes sb/<F>.tablefix.json: {package id: [missing table modules]}."""
import sys, os, re, json, glob, collections
R22 = os.environ.get('R22_ROOT', '.')   # the development layout's root (package mode does not use it)
SB = R22 + '/e1g/pkg/sb/'
def analyze(F, lines_files):
    pkg = SB + F + '/pkg'
    M = {json.loads(l)['module']: json.loads(l) for l in open(pkg + '/manifest.jsonl') if l.strip()}
    tables = {k for k, m in M.items() if m['kind'] == 'table'}
    src = {}
    def text(k):
        if k not in src: src[k] = open(os.path.join(pkg, M[k]['src'])).read()
        return src[k]
    pubimp = {k: set(re.findall(r'^public import (\S+)', text(k), re.M)) & tables for k in M if k not in tables}
    own = {k for k in M if k not in tables and re.search(r'^#kext ', text(k), re.M)}
    lifted = {}
    sys.setrecursionlimit(100000)
    def L(k):
        if k not in lifted:
            lifted[k] = False
            lifted[k] = k in own or any(L(d) for d in M[k]['deps'] if d in M and d not in tables)
        return lifted[k]
    for k in M:
        if k not in tables: L(k)
    reach_memo = {}
    def reach(k):   # non-table modules reachable from k (k included)
        if k not in reach_memo:
            s = {k}
            for d in M[k]['deps']:
                if d in M and d not in tables: s |= reach(d)
            reach_memo[k] = s
        return reach_memo[k]
    fix = {}
    for lf in lines_files:
        if not os.path.exists(lf): continue
        for l in open(lf):
            d = json.loads(l); arg = d['emit']['argv'][2]
            m = re.search(r'/(%s)/([^/]+)\.jsonl' % re.escape(F), arg)
            if not m: continue
            mf = SB + F + ('/recut/' if '/r' in '/' + m.group(2)[:1] and os.path.exists(SB + F + '/recut/' + m.group(2) + '.jsonl') else '/plan/' + F + '/') + m.group(2) + '.jsonl'
            if not os.path.exists(mf): continue
            rows = [json.loads(x) for x in open(mf)]
            have = {r['module'] for r in rows if r['module'] in tables}
            mods = [r['module'] for r in rows if r['module'] not in tables]
            R = set().union(*(reach(k) for k in mods)) if mods else set()
            # a module whose external-leaf list has at least 2 segments (its own leaves, each lifted child) names every lifted
            # child's NS.EXT in its proof (appendSegs); those children are the audit's statement checks (KModTyChk imports them)
            need = set()
            for k in R:
                lc = [x for x in M[k]['deps'] if x in M and x not in tables and lifted[x]]
                if (1 if k in own else 0) + len(lc) >= 2:
                    for x in lc: need |= pubimp[x]
            miss = sorted(need - have)
            if miss: fix[d['id']] = miss
    nl = sum(1 for k in lifted if lifted[k]); nlr = sum(1 for k in lifted if lifted[k] and pubimp[k])
    return fix, nl, nlr
if __name__ == '__main__':
    fams = [l.split()[0] for l in open(SB + 'READY.txt') if l.strip()]
    tot = 0
    for F in fams:
        if not os.path.exists(SB + F + '/pkg/manifest.jsonl'): continue
        fix, nl, nlr = analyze(F, [SB + F + '.lines.jsonl', SB + F + '.recut.lines.jsonl'])
        json.dump(fix, open(SB + F + '.tablefix.json', 'w'), indent=0)
        tot += len(fix)
        if fix: print('%s: %d lifted modules (%d with a public table import); packages missing tables: %s' % (F, nl, nlr, {k: v for k, v in fix.items()}))
    print('packages needing a table fix: %d' % tot)

def checked_tables(M, pkgdir):
    """for the module rows M (dict) of an emitted package: the function giving, for a set of the package's non-table modules, the
    tables their audit needs beyond their own imports (the public table imports of every checked module reachable from them)"""
    tables = {k for k, m in M.items() if m['kind'] == 'table'}
    txt = {k: open(os.path.join(pkgdir, M[k]['src'])).read() for k in M if k not in tables}
    pubimp = {k: set(re.findall(r'^public import (\S+)', txt[k], re.M)) & tables for k in txt}
    own = {k for k in txt if re.search(r'^#kext ', txt[k], re.M)}
    lifted = {}
    def L(k):
        if k not in lifted:
            lifted[k] = False
            lifted[k] = k in own or any(L(d) for d in M[k]['deps'] if d in M and d not in tables)
        return lifted[k]
    sys.setrecursionlimit(1000000)
    for k in txt: L(k)
    need_of = {}   # importer m -> tables of its checked children
    for k in txt:
        lc = [x for x in M[k]['deps'] if x in M and x not in tables and lifted[x]]
        if (1 if k in own else 0) + len(lc) >= 2:
            t = set().union(*(pubimp[x] for x in lc))
            if t: need_of[k] = t
    def extra(mods):
        seen = set(); st = list(mods); out = set()
        while st:
            k = st.pop()
            if k in seen: continue
            seen.add(k); out |= need_of.get(k, set())
            st += [d for d in M[k]['deps'] if d in M and d not in tables and d not in seen]
        return out
    return extra
