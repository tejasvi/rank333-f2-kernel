#!/usr/bin/env python3
"""splitpkg.py MODE SRC OUT BUDGET MAXROOTS: cut one queue run's item tree into leaf packages (complete subtrees) and one join package.

MODE plan: SRC is an xqaudit --plan file. The tree comes from the I lines' parent field; an item's size is its segment's bytes.
MODE dirs: SRC is a directory of kitem item dirs (*.d with key.txt). The tree comes from the keys' children (segkey); an item's size
           is its input bytes (*.bin).

- An item is small when its subtree's size is at most BUDGET. Job roots (items without a parent) are never small.
- Leaf units are the maximal small subtrees. They are packed in DFS preorder into leaf packages L000, L001, ... of at most BUDGET
  bytes and MAXROOTS units each, so py/mkaggf.py with AGG_LEAF=1 and FANIN >= MAXROOTS puts each package's roots in one root chunk.
- Every other item (the spine: the job roots, and the items whose subtree exceeds BUDGET) goes to the join package J. Its children
  in leaf packages are covered through the leaves' export maps (mkaggf AGG_EXT).

Writes OUT/parts.json: {name: {kind: leaf|join, items: [ids], bytes, units}}. In plan mode it also writes OUT/<name>.plan: the plan's
non-I lines, then that part's I lines (py/xqitems.py takes it as a plan). In dirs mode it writes OUT/<name>.dirs, one item dir per line.
Prints the cut: packages, their sizes, and the join's share."""
import sys, os, json, collections
sys.set_int_max_str_digits(0)
sys.setrecursionlimit(1000000)
mode, src, out, budget, maxroots = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4]), int(sys.argv[5])
os.makedirs(out, exist_ok=True)
size = {}; parent = {}; line = {}; head = []; order = []
if mode == 'plan':
    for ln in open(src):
        a = ln.split()
        if not a: continue
        if a[0] != 'I': head.append(ln); continue
        seg = [x for x in a if x.startswith('seg=')][0][4:].split(':')
        if a[1] in size: sys.exit('splitpkg: item %s twice in the plan' % a[1])
        size[a[1]] = int(seg[3]); parent[a[1]] = a[2]; line[a[1]] = ln; order.append(a[1])
elif mode == 'dirs':
    sys.path.insert(0, os.environ.get('KINDS_R22', '.') + '/lean/native/infra/lib/py')
    import segkey
    iface = {}; kids = {}
    for d in sorted(os.listdir(src)):
        p = os.path.join(src, d)
        if not d.endswith('.d') or not os.path.exists(p + '/key.txt'): continue
        dk = segkey.decode(int(open(p + '/key.txt').read().split()[0]))
        i = os.path.abspath(p); order.append(i)
        iface[(dk['root'], dk['lo'])] = i
        kids[i] = [(e, 0) for e in dk['ext']] + [(tuple(n), l) for (n, l) in dk['rng']]
        size[i] = sum(os.path.getsize(os.path.join(p, f)) for f in os.listdir(p) if f.endswith('.bin'))
    for i in order:
        for c in kids[i]:
            if c not in iface: sys.exit('splitpkg: child %s of %s is not an item here' % (c, i))
            if iface[c] in parent: sys.exit('splitpkg: %s has two parents' % iface[c])
            parent[iface[c]] = i
    for i in order: parent.setdefault(i, None)
else: sys.exit('splitpkg: MODE is plan or dirs')
ch = collections.defaultdict(list)
for i in order:
    if parent[i] in size: ch[parent[i]].append(i)
roots = [i for i in order if parent[i] not in size]
sub = {}
def subtree(i):          # iterative post-order sums
    st = [(i, 0)]
    while st:
        x, k = st.pop()
        if k < len(ch[x]): st.append((x, k + 1)); st.append((ch[x][k], 0))
        else: sub[x] = size[x] + sum(sub[c] for c in ch[x])
for r in roots: subtree(r)
assert len(sub) == len(order), 'items not below a root (a cycle)'
small = lambda i: parent[i] in size and sub[i] <= budget
# DFS preorder: spine items, and the maximal small subtrees (units) in order
spine = []; units = []
st = list(reversed(roots))
while st:
    x = st.pop()
    if small(x): units.append(x); continue
    spine.append(x)
    st.extend(reversed(ch[x]))
def members(u):
    res = []; st = [u]
    while st:
        x = st.pop(); res.append(x); st.extend(reversed(ch[x]))
    return res
parts = collections.OrderedDict(); cur = []; cb = 0
def flush():
    global cur, cb
    if cur:
        parts['L%03d' % len(parts)] = dict(kind='leaf', units=len(cur), bytes=cb, items=[m for u in cur for m in members(u)])
    cur = []; cb = 0
for u in units:
    if cur and (cb + sub[u] > budget or len(cur) >= maxroots): flush()
    cur.append(u); cb += sub[u]
flush()
parts['J'] = dict(kind='join', units=len(roots), bytes=sum(size[i] for i in spine), items=spine)
n = sum(len(p['items']) for p in parts.values())
assert n == len(order) and len(set(m for p in parts.values() for m in p['items'])) == n, 'the parts do not cover each item once'
json.dump(parts, open(os.path.join(out, 'parts.json'), 'w'))
for name, p in parts.items():
    if mode == 'plan':
        with open(os.path.join(out, name + '.plan'), 'w') as f:
            f.write(''.join(head)); f.write(''.join(line[i] for i in p['items']))
    else:
        open(os.path.join(out, name + '.dirs'), 'w').write(''.join(i + '\n' for i in p['items']))
lb = sorted(p['bytes'] for p in parts.values() if p['kind'] == 'leaf')
tot = sum(size.values())
print('splitpkg: %d items, %.3g bytes; %d leaf packages (bytes min %.3g, median %.3g, max %.3g; units max %d), join %d items (%.3g bytes, '
      '%.1f%%; %d roots)' % (len(order), tot, len(lb), lb[0] if lb else 0, lb[len(lb) // 2] if lb else 0, lb[-1] if lb else 0,
      max([p['units'] for p in parts.values() if p['kind'] == 'leaf'] or [0]), len(spine), parts['J']['bytes'],
      100.0 * parts['J']['bytes'] / tot, len(roots)))
