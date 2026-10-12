#!/usr/bin/env python3
"""splitrun.py PLAN WORK PFX LO HI: the packages of one big case under --rord 321 (e.g. I13) from one queue run, on one build machine. Resumable.

1. py/splitpkg.py plan PLAN WORK/parts BUDGET MAXROOTS: leaf packages L000, L001, ... (complete subtrees) and the join package J.
2. Each leaf part (CONC at once; a part starts only when MemAvailable >= MEMMIN GB):
   - py/xqitems.py on WORK/parts/<part>.plan into WORK/items/<part> (PAR conversions; XQ_ORD=321): 0 conversion failures and every
     key equal to the queue's interface, else the part is marked failed (WORK/fail/<part>);
   - runs/reh/mkstage321.sh <PFX><part> with STAGE_R462=0 AGG_LEAF=1: item modules and aggregators, no top; the root chunk's cov is
     the package's pub, and its export map goes to WORK/exports/<part>.exports;
   - runs/reh/mkpkg2.py with PKG_CLOSURE (PKG_ROOT=0 by default: the closure ships once, separately); tar + zstd into
     WORK/pkg/<NAME>_<part>.tar.zst, and its sha256 into <file>.sha256, written last (the package is complete).
     the tarballs are then copied to the package store (sha256-verified) and removed here;
   - the stage and the items are deleted; WORK/done/<part>.json records the package.
3. The join part J, after every leaf is done: its items (the job items and the spine), the root 462, aggregators whose children in
   leaf packages are the leaves' exported covs (AGG_EXT), and the top (#kmVI321: R22B.Final's vI form). Same checks.
4. WORK/INDEX.jsonl: one line per package (name, sha256, bytes, kind, units, pred_s, max pred_gb, records, items, pub, top, needs);
   main uploads it after the packages.
env: BUDGET (segment bytes per leaf, default 4e8), MAXROOTS (default = FANIN), FANIN (400), MAXS (60), CONC (6), PAR (48), MEMMIN (120),
     XQ_HDR (the run's pcert header; required), KPY (Python with numpy for kitem.py), PKG_CLOSURE (required), PKG_ROOT (0),
     PKG_TIER (caseI13), NAME (pkg_kmod_I13), DESC (the README's description). Absolute nice 10 for every child."""
import sys, os, json, subprocess, shutil, hashlib, time, threading
from concurrent.futures import ThreadPoolExecutor
plan, work, pfx, lo, hi = sys.argv[1:6]
K = os.environ.get('KINDS_R22', '.') + '/lean/kinds'
E = os.environ
BUDGET = E.get('BUDGET', '4e8'); FANIN = E.get('FANIN', '400'); MAXROOTS = E.get('MAXROOTS', FANIN); MAXS = E.get('MAXS', '60')
CONC = int(E.get('CONC', '6')); PAR = E.get('PAR', '48'); MEMMIN = float(E.get('MEMMIN', '120'))
NAME = E.get('NAME', 'pkg_kmod_I13'); TIER = E.get('PKG_TIER', 'caseI13')
DESC = E.get('DESC', 'case (I13) (CaseK %s %s) under --rord 321' % (lo, hi))
assert E.get('XQ_HDR') and E.get('PKG_CLOSURE'), 'XQ_HDR and PKG_CLOSURE are required'
NI = str(max(0, 10 - os.nice(0)))
for d in ('parts', 'items', 'exports', 'done', 'fail', 'logs', 'pkg'): os.makedirs(os.path.join(work, d), exist_ok=True)
lock = threading.Lock()
def log(*a):
    with lock:
        with open(os.path.join(work, 'splitrun.log'), 'a') as f: f.write(time.strftime('%H:%M:%S ') + ' '.join(str(x) for x in a) + '\n')
def run(cmd, logf, env=None, cwd=None):
    with open(logf, 'a') as o:
        return subprocess.run(['nice', '-n', NI] + cmd, stdout=o, stderr=subprocess.STDOUT, env=dict(E, **(env or {})), cwd=cwd).returncode
def memavail():
    for ln in open('/proc/meminfo'):
        if ln.startswith('MemAvailable:'): return int(ln.split()[1]) / 1e6
def sha256(p):
    s = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 22), b''): s.update(b)
    return s.hexdigest()
def fail(part, what):
    open(os.path.join(work, 'fail', part), 'w').write(what); log(part, 'FAIL', what.split('\n')[0]); return None
def one(part, kind, ext_files=()):
    done = os.path.join(work, 'done', part + '.json')
    if os.path.exists(done): return json.load(open(done))
    lg = os.path.join(work, 'logs', part + '.txt'); open(lg, 'w').close()
    while memavail() < MEMMIN: time.sleep(20)
    pp = os.path.join(work, 'parts', part + '.plan'); idir = os.path.join(work, 'items', part)
    nitems = sum(1 for ln in open(pp) if ln.startswith('I '))
    shutil.rmtree(idir, ignore_errors=True)
    t0 = time.time()
    xenv = dict(XQ_ORD='321', XQ_LO=lo, XQ_HI=hi, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1')
    xl = os.path.join(work, 'logs', part + '.xq.txt'); open(xl, 'w').close()
    rc = run([sys.executable, K + '/py/xqitems.py', pp, idir, PAR], xl, env=xenv)
    xt = open(xl).read()
    if not (rc == 0 and 'conversion failures 0' in xt and ('key mismatches 0 of %d' % nitems) in xt):
        return fail(part, 'xqitems rc %d\n%s' % (rc, xt[-2000:]))
    for f in os.listdir(idir):
        if f.endswith('.txt'): os.remove(os.path.join(idir, f))      # pcseg's text (conversion input only)
    t1 = time.time()
    mp = pfx + part; st = K + '/runs/reh/stage321_' + mp
    senv = dict(KPY=sys.executable, STAGE_R462='1' if kind == 'join' else '0')
    if kind == 'leaf': senv['AGG_LEAF'] = '1'
    else: senv['AGG_EXT'] = ' '.join(ext_files)
    rc = run(['bash', K + '/runs/reh/mkstage321.sh', mp, lo, hi, idir, MAXS, FANIN], lg, env=senv)
    if rc: return fail(part, 'mkstage321 rc %d' % rc)
    if kind == 'leaf':
        shutil.copy2('%s/src/%s.exports' % (st, mp), os.path.join(work, 'exports', part + '.exports'))
        note = ('- Split case: this is a leaf package (complete subtrees, no top). Its pub is its root chunk\'s cov; the join package %s_J '
                'imports it.\n' % NAME)
    else:
        nl = len([p for p in os.listdir(os.path.join(work, 'done')) if p.startswith('L')])
        note = ('- Split case: this is the join package. Its aggregators import the root chunks (pubs) of the %d leaf packages %s_L000 ... '
                '(INDEX.jsonl), so it builds only on a store that already holds their outputs.\n' % (nl, NAME))
    penv = dict(PKG_MODEL='321', PKG_TIER=TIER, PKG_NAME='%s_%s' % (NAME, part), PKG_ROOT=E.get('PKG_ROOT', '0'), PKG_NOTE=note,
                PKG_DESC='%s, part %s (%s) of the queue run of jobs 0 and 1 (prof7R3q_b14, FLAGS_I13 + --pcwit, --xqcap 10000, server rord=321)' % (DESC, part, kind),
                PKG_TEST='- Each item converted with 0 model notes and its key equal to the queue\'s interface; the contract and loaders are '
                         'those of pkg_kmod_321I (kinds\' the design notes).\n')
    rc = run([sys.executable, K + '/runs/reh/mkpkg2.py', st, mp], lg, env=penv)
    if rc: return fail(part, 'mkpkg2 rc %d' % rc)
    tb = os.path.join(work, 'pkg', '%s_%s.tar.zst' % (NAME, part))
    members = [m for m in ('README.txt', 'manifest.jsonl', 'lpath_common.txt', 'kmod_unit.sh', 'tools', 'src', 'data', 'root') if os.path.exists(os.path.join(st, m))]
    rc = subprocess.run('nice -n %s tar cf - %s | nice -n %s zstd -q -T8 -3 -o %s -f' % (NI, ' '.join(members), NI, tb), shell=True, cwd=st).returncode
    if rc: return fail(part, 'tar rc %d' % rc)
    sha = sha256(tb)
    man = [json.loads(l) for l in open(st + '/manifest.jsonl')]
    rec = dict(part=part, kind=kind, name=os.path.basename(tb), sha256=sha, bytes=os.path.getsize(tb), units=len(man),
               pred_s=round(sum(x['pred_s'] for x in man), 1), max_pred_gb=max(x['pred_gb'] for x in man), records=sum(x['records'] for x in man),
               items=nitems, pub=[x['pub'] for x in man if 'pub' in x][0], top=[x['module'] for x in man if 'pub' in x][0],
               needs=[] if kind == 'leaf' else 'all leaf packages', conv_s=round(t1 - t0), total_s=round(time.time() - t0))
    shutil.copy2(st + '/manifest.jsonl', os.path.join(work, 'logs', part + '.manifest.jsonl'))
    shutil.copy2(st + '/README.txt', os.path.join(work, 'logs', part + '.README.txt'))
    shutil.rmtree(st); shutil.rmtree(idir)
    open(tb + '.sha256', 'w').write('%s  %s\n' % (sha, os.path.basename(tb)))
    json.dump(rec, open(done + '.tmp', 'w')); os.rename(done + '.tmp', done)
    log(part, 'done', rec['units'], 'units', rec['records'], 'records', rec['bytes'], 'bytes', 'conv %ds total %ds' % (rec['conv_s'], rec['total_s']))
    return rec
if not os.path.exists(os.path.join(work, 'parts', 'parts.json')):
    r = subprocess.run([sys.executable, K + '/py/splitpkg.py', 'plan', plan, os.path.join(work, 'parts'), BUDGET, MAXROOTS], capture_output=True, text=True)
    log(r.stdout.strip(), r.stderr.strip()[-500:])
    if r.returncode: sys.exit('splitpkg failed')
parts = json.load(open(os.path.join(work, 'parts', 'parts.json')))
leaves = [p for p in parts if parts[p]['kind'] == 'leaf']
only = E.get('ONLY', '').split()          # env ONLY: just these parts (a trial)
log('start: %d leaf parts, join %d items%s' % (len(leaves), len(parts['J']['items']), ' (only %s)' % only if only else ''))
todo = [p for p in leaves if not only or p in only]
with ThreadPoolExecutor(CONC) as ex: res = list(ex.map(lambda p: one(p, 'leaf'), todo))
if any(r is None for r in res): log('leaf failures: %s' % [p for p, r in zip(todo, res) if r is None]); sys.exit(1)
if only: log('trial done'); sys.exit(0)
J = one('J', 'join', [os.path.join(work, 'exports', p + '.exports') for p in leaves])
if J is None: sys.exit(1)
idx = os.path.join(work, 'INDEX.jsonl')
with open(idx + '.tmp', 'w') as f:
    for p in leaves + ['J']: f.write(json.dumps(json.load(open(os.path.join(work, 'done', p + '.json')))) + '\n')
os.rename(idx + '.tmp', idx)
log('all done: %d packages' % (len(leaves) + 1))
