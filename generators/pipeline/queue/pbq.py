#!/usr/bin/env python3
"""pbq.py: the package queue on an object store (objstore.py; no server).  Layout under PREFIX in the store namespace:
  packages.jsonl            the package list (one JSON spec line per package: id, kind, pred_s, emit, deps, ...; claim order = file order)
  lease/<id>                {"state": "held"|"done"|"failed"|"parked", "box", "t", "attempts", ...}; created with if_generation=0, so
                            exactly one worker holds a package; renewed (generation-matched rewrite) every RENEW s by its worker
  done/<id>.json            the result record (tarball name, sha256, md5, modules, audit, timings, provenance), written before the
                            lease turns "done"
  failed/<id>               marker of a failed package (removed when the sweep requeues it), so counts need listings only
  parked/<id>               marker of a parked package (its lease stays "parked": never released or requeued by the sweep)
  attempts/<id>             the attempt count of a requeued package
  tar/<shard>/<id>.<t>.<box>.tar.zst   the package's result tarball (shard = first 2 hex digits of sha1(id))
  pubs/<shard>/<id>...tar   the package's public parts for dependents (roots and the modules dependents import)
  sample/<id>/...           the seeded share of private parts kept for the independent re-check
  taken.json.gz, done.json.gz   snapshots of the leased and done ids (pbq.py snapshot), read by claimers
  CONTROL                   optional JSON {"launch": false}: workers stop claiming while it says so
Rules: a "held" lease not renewed for TTL s (or held by a worker missing from the workers file, when one is given) is deleted by the
sweep and the package becomes claimable again; a "failed" lease is requeued while attempts < MAXATT, else parked for inspection;
a kernel rejection or an unclean audit is parked for inspection at once; "done" leases stay.

CLI:  pbq.py init BUCKET PREFIX packages.jsonl | add BUCKET PREFIX FILE [--front] | status BUCKET PREFIX
      | snapshot BUCKET PREFIX [--loop S] | sweep BUCKET PREFIX [--loop S] [--workers-file F]
Library (worker): Queue(bucket, prefix, box).claim(), .adopt(id), .renew(id), .release(id), .done(id, record), .park(id, reason),
.fail(id, reason), .launch_allowed()
Env: PBQ_TTL (lease expiry, default 1200 s), PBQ_RESCAN, PBQ_WINDOW, PBQ_MAX_MISSES (claim tuning)."""
import gzip, hashlib, random, json, os, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import objstore

TTL = int(os.environ.get('PBQ_TTL', 1200)); RENEW = 300; MAXATT = 3   # TTL: the sweep's expiry; at most MAXATT attempts, then parked 'inspect'

def shard(pid): return hashlib.sha1(pid.encode()).hexdigest()[:2]

class Queue:
    def __init__(self, bucket, prefix, box, cache_dir='/tmp'):
        self.b, self.p, self.box = bucket, prefix.rstrip('/'), box
        self.gen = {}      # id -> generation of our lease
        self.cursor = 0; self.last_scan = 0.0; self.taken = set()
        self.pkf = os.path.join(cache_dir, 'packages_%s.jsonl' % hashlib.sha1((bucket + prefix).encode()).hexdigest()[:8])
        self.pkgen = None; self.load_packages()
    def load_packages(self):
        """(re)load packages.jsonl when its generation changed: packages can be appended to a running queue"""
        m = objstore.stat(self.b, self.p + '/packages.jsonl')
        if m is None: raise RuntimeError('no packages.jsonl under %s' % self.p)
        if self.pkgen == m['generation'] and os.path.exists(self.pkf): return False
        objstore.download_file(self.b, self.p + '/packages.jsonl', self.pkf); self.pkgen = m['generation']
        self.pk = [json.loads(l) for l in open(self.pkf) if l.strip()]
        self.byid = {x['id']: x for x in self.pk}
        return True
    def _lease(self, pid): return self.p + '/lease/' + pid
    def launch_allowed(self):
        c = objstore.get(self.b, self.p + '/CONTROL')
        if c is None: return True
        try: return bool(json.loads(c[0]).get('launch', True))
        except Exception: return True
    def rescan(self):
        """refresh the package list (if changed) and the set of leased ids (every PBQ_RESCAN s, default 90, or when the cursor
        reaches the end): from the sweep's snapshot taken.json.gz (one object, rewritten every sweep) when it is under 10 min old,
        else by listing lease/ (slow at a full round trip per 1000 leases)"""
        try: self.load_packages()
        except Exception: pass
        snap = None
        try:
            g = objstore.get(self.b, self.p + '/taken.json.gz')
            if g:
                d = json.loads(gzip.decompress(g[0]))
                if time.time() - d.get('t', 0) < 600: snap = set(d['ids'])
        except Exception: snap = None
        if snap is None: snap = {it['name'].rsplit('/', 1)[1] for it in objstore.ls(self.b, self.p + '/lease/')}
        self.taken = snap | set(self.gen)
        self.cursor = 0; self.last_scan = time.time()
    def done_ids(self):
        """ids with a done record (cached for 60 s): from the snapshot done.json.gz when under 10 min old, else by listing done/"""
        if time.time() - getattr(self, '_done_t', 0) > 60:
            snap = None
            try:
                g = objstore.get(self.b, self.p + '/done.json.gz', timeout=30, tries=2)
                if g:
                    d = json.loads(gzip.decompress(g[0]))
                    if time.time() - d.get('t', 0) < 600: snap = set(d['ids'])
            except Exception: snap = None
            self._done = snap if snap is not None else {it['name'].rsplit('/', 1)[1][:-len('.json')] for it in objstore.ls(self.b, self.p + '/done/')}
            self._done_t = time.time()
        return self._done
    def claim(self, skip=(), fits=None):
        """the next unleased package near the head of the list whose "deps" (package ids: e.g. a split case's leaves before its join)
        are all done; None when nothing is claimable now.  The first PBQ_WINDOW (128) eligible packages from the cursor are tried
        in a box-random order: boxes scanning the same list from the same snapshot of taken leases then rarely collide on one
        lease (each collision is a failed conditional write at a full round trip to the store), and list order (priority, head
        inserts first) still holds to within the window"""
        if time.time() - self.last_scan > int(os.environ.get('PBQ_RESCAN', 30)) or self.cursor >= len(self.pk): self.rescan()
        W = int(os.environ.get('PBQ_WINDOW', 4096))
        rng = getattr(self, '_rng', None) or random.Random('%s.%f' % (self.box, time.time())); self._rng = rng
        done = None
        def eligible(x):
            nonlocal done
            if x['id'] in self.taken or x['id'] in skip: return False
            if x.get('deps'):
                done = done if done is not None else self.done_ids()
                if not set(x['deps']) <= done: return False      # not ready: revisited after the next rescan
            if fits is not None and not fits(x): return False      # too big for this box now (disk permit)
            return True
        while self.cursor < len(self.pk):
            while self.cursor < len(self.pk) and not eligible(self.pk[self.cursor]): self.cursor += 1
            cand = []; i = self.cursor
            while i < len(self.pk) and len(cand) < W:
                if eligible(self.pk[i]): cand.append(self.pk[i])
                i += 1
            if not cand: return None
            # head-biased random order: position = window x u^4 (u uniform), so ~35% of claims land in the first 64 eligible packages
            # (head inserts: the point tier, joins, the largest packages) while the rest spread over the window (few collisions)
            def order(left=list(range(len(cand)))):
                while left:
                    yield cand[left.pop(min(int(len(left) * rng.random() ** 4), len(left) - 1))]
            misses = 0
            for x in order():
                # a stale snapshot makes the head of the window mostly taken: after 24 collisions in a row this call gives up (the
                # claimer retries in 10 s from a fresher snapshot) instead of walking thousands of taken candidates one round trip each
                if misses >= int(os.environ.get('PBQ_MAX_MISSES', 24)): return None
                body = json.dumps(dict(state='held', box=self.box, t=time.time(), attempts=1))
                try:
                    # one quick attempt: a create that gets no answer is not retried blind (a stalled write can take minutes);
                    # the lease object itself then says whether the create happened, and for whom
                    m = objstore.put(self.b, self._lease(x['id']), body, if_generation=0, timeout=15, tries=1)
                except objstore.Precondition:
                    self.taken.add(x['id']); misses += 1; continue
                except Exception:
                    try: r = objstore.get(self.b, self._lease(x['id']))
                    except Exception: r = None
                    if not r or json.loads(r[0]).get('box') != self.box:
                        self.taken.add(x['id']); misses += 1; continue
                    m = {'generation': r[1]}
                self.gen[x['id']] = int(m['generation']); self.taken.add(x['id'])
                prev = objstore.get(self.b, self.p + '/attempts/' + x['id'])      # a requeued package carries its attempt count
                if prev is not None:
                    try:
                        m = objstore.put(self.b, self._lease(x['id']), json.dumps(dict(state='held', box=self.box, t=time.time(), attempts=int(prev[0]) + 1)),
                                    if_generation=self.gen[x['id']])
                        self.gen[x['id']] = int(m['generation'])
                    except objstore.Precondition:
                        self.gen.pop(x['id'], None); continue
                return x
        return None
    def adopt(self, pid):
        """after a restart: take back our own unexpired lease of pid (True), or learn it is lost (False)"""
        r = objstore.get(self.b, self._lease(pid))
        if r is None: return False
        d = json.loads(r[0])
        if d.get('box') != self.box or d.get('state') != 'held': return False
        self.gen[pid] = r[1]; return self.renew(pid)
    def release(self, pid):
        """give our lease back (a package dropped after a restart before it was queued): claimable again at once, by any box; the
        attempt count is unchanged (a restart is not a failed attempt)"""
        g = self.gen.pop(pid, None)
        if g is None: return False
        try:
            objstore.delete(self.b, self._lease(pid), if_generation=g); self.taken.discard(pid); return True
        except objstore.Precondition:
            return False
    def renew(self, pid):
        g = self.gen.get(pid)
        if g is None: return False
        r = objstore.get(self.b, self._lease(pid))
        d = json.loads(r[0]) if r else {}
        if not r or d.get('box') != self.box or d.get('state') != 'held': self.gen.pop(pid, None); return False
        # a newer generation that still names this box as holder: our own earlier write whose response was lost (only the holder
        # rewrites a held lease; the sweep deletes, and a new claim names its own box): still ours
        g = r[1]
        d['t'] = time.time()
        try:
            m = objstore.put(self.b, self._lease(pid), json.dumps(d), if_generation=g)
        except objstore.Precondition:
            self.gen.pop(pid, None); return False
        self.gen[pid] = int(m['generation']); return True
    def done(self, pid, record):
        objstore.put(self.b, self.p + '/done/%s.json' % pid, json.dumps(record))
        g = self.gen.get(pid)
        d = dict(state='done', box=self.box, t=time.time(), sha256=record.get('sha256'))
        try:
            objstore.put(self.b, self._lease(pid), json.dumps(d), if_generation=g)
        except objstore.Precondition:
            # the lease was swept and maybe re-claimed while we finished: the done record stands; the other box's result is a
            # duplicate that the store keeps under the same name only if identical (tarball sha256 in both done records)
            pass
        self.gen.pop(pid, None)
    def park(self, pid, reason):
        """park the package (keeps its lease, state "parked"): no retry burns on the same tools; it still counts as remaining work"""
        g = self.gen.pop(pid, None)
        if g is None: return     # the lease is no longer ours (lost, released, moved to another box): never overwrite it
        try:
            objstore.put(self.b, self._lease(pid), json.dumps(dict(state='parked', box=self.box, t=time.time(), reason=reason[:500])), if_generation=g)
            objstore.put(self.b, self.p + '/parked/' + pid, reason[:500])
        except objstore.Precondition:
            pass
    def fail(self, pid, reason):
        g = self.gen.pop(pid, None)
        if g is None: return     # the lease is no longer ours (an emission that failed after its lease was lost or moved): keep the new holder's
        r = objstore.get(self.b, self._lease(pid)); att = json.loads(r[0]).get('attempts', 1) if r else 1
        try:
            objstore.put(self.b, self._lease(pid), json.dumps(dict(state='failed', box=self.box, t=time.time(), attempts=att, reason=reason[:500])), if_generation=g)
            objstore.put(self.b, self.p + '/failed/' + pid, reason[:500])
        except objstore.Precondition:
            pass

def counts(bucket, prefix, pk_pred):
    """listing-only queue state: (done_pred_s, remaining_pred_s, n_done, n_failed, n_held, n_total); pk_pred = {id: pred_s}"""
    p = prefix.rstrip('/')
    done = {it['name'].rsplit('/', 1)[1][:-len('.json')] for it in objstore.ls(bucket, p + '/done/', fields='name')}
    failed = {it['name'].rsplit('/', 1)[1] for it in objstore.ls(bucket, p + '/failed/', fields='name')}
    leased = {it['name'].rsplit('/', 1)[1] for it in objstore.ls(bucket, p + '/lease/', fields='name')}
    parked = {it['name'].rsplit('/', 1)[1] for it in objstore.ls(bucket, p + '/parked/', fields='name')}
    held = leased - done - failed - parked
    d = sum(v for k, v in pk_pred.items() if k in done)
    counts.parked = len(parked)          # (kept out of the tuple for compatibility)
    return d, sum(pk_pred.values()) - d, len(done & set(pk_pred)), len(failed), len(held), len(pk_pred)

def running_boxes(path=None):
    """the live workers: one name per line in the workers file (sweep --workers-file F, or env PBQ_WORKERS_FILE); None = unknown
    (then only the TTL releases a lease)"""
    path = path or os.environ.get('PBQ_WORKERS_FILE')
    if not path or not os.path.exists(path): return None
    return {l.split()[0]: 'RUNNING' for l in open(path) if l.strip()}

def _ts(rfc3339):
    import datetime
    return datetime.datetime.fromisoformat(rfc3339.replace('Z', '+00:00')).timestamp()

def sweep(bucket, prefix, log=print, workers_file=None):
    """listing-driven: only leases not renewed for TTL s (object 'updated' time) that are neither done nor failed are read; failed
    packages come from the failed/ markers.  Releases expired leases and leases of workers that no longer exist (workers file);
    requeues failed packages below MAXATT (attempt count kept in attempts/<id>)."""
    p = prefix.rstrip('/'); live = running_boxes(workers_file); now = time.time()
    n = {'leases': 0, 'checked': 0, 'released': 0, 'requeued': 0, 'review': 0, 'parked': 0}
    done = {it['name'].rsplit('/', 1)[1][:-len('.json')] for it in objstore.ls(bucket, p + '/done/', fields='name')}
    parked = {it['name'].rsplit('/', 1)[1] for it in objstore.ls(bucket, p + '/parked/', fields='name')}; n['parked'] = len(parked)
    failed = {it['name'].rsplit('/', 1)[1] for it in objstore.ls(bucket, p + '/failed/', fields='name')}
    ids = []
    for it in objstore.ls(bucket, p + '/lease/', fields='name,updated'):
        n['leases'] += 1; pid = it['name'].rsplit('/', 1)[1]; ids.append(pid)
        if pid in done or pid in parked: continue
        old = now - _ts(it['updated']) > TTL
        if not old and pid not in failed:
            continue          # renewed within TTL: its worker is alive (a vanished worker stops renewing, so its leases age out)
        r = objstore.get(bucket, it['name'])
        if r is None: continue
        try: d = json.loads(r[0])
        except ValueError:
            log('unreadable lease %s (%d bytes): skipped' % (it['name'], len(r[0]))); continue
        s = d.get('state'); n['checked'] += 1
        try:
            gone = live is not None and d.get('box') not in live
            if s == 'held' and (now - d.get('t', 0) > TTL or gone):
                objstore.delete(bucket, it['name'], if_generation=r[1]); n['released'] += 1
                log('released %s (worker %s%s, %.0f s old)' % (it['name'], d.get('box'), ' gone' if gone else '', now - d.get('t', 0)))
            elif s == 'failed' and ('[KERNEL' in d.get('reason', '') or ',KERNEL' in d.get('reason', '') or d.get('reason', '').startswith('unclean audit')):
                # a kernel rejection or an unclean audit is a correctness signal: parked for inspection, never requeued blindly
                tag = 'inspect-audit' if d.get('reason', '').startswith('unclean audit') else 'inspect-kernel'
                objstore.put(bucket, it['name'], json.dumps(dict(d, state='parked', reason=tag + ': ' + d.get('reason', '')[:480])), if_generation=r[1])
                objstore.put(bucket, p + '/parked/' + pid, tag + ': ' + d.get('reason', '')[:480]); n['parked'] += 1
                log('PARKED %s %s: %s' % (tag, pid, d.get('reason', '')[:200]))
            elif s == 'failed' and d.get('attempts', 1) >= MAXATT:
                # attempts exhausted: parked for inspection (never looping)
                objstore.put(bucket, it['name'], json.dumps(dict(d, state='parked', reason='inspect: ' + d.get('reason', '')[:480])), if_generation=r[1])
                objstore.put(bucket, p + '/parked/' + pid, 'inspect: %d attempts: ' % d.get('attempts', 1) + d.get('reason', '')[:450]); n['parked'] += 1
                log('PARKED inspect %s after %d attempts: %s' % (pid, d.get('attempts', 1), d.get('reason', '')[:200]))
            elif s == 'failed':
                if d.get('attempts', 1) < MAXATT:
                    objstore.put(bucket, p + '/attempts/' + pid, str(d.get('attempts', 1)))
                    objstore.delete(bucket, it['name'], if_generation=r[1]); objstore.delete(bucket, p + '/failed/' + pid); n['requeued'] += 1
                    log('requeued %s (attempt %d failed: %s)' % (pid, d.get('attempts', 1), d.get('reason', '')[:120]))
                else: n['review'] += 1
        except objstore.Precondition:
            pass
    # (taken.json.gz is written by `pbq.py snapshot` only: a sweep's listing is older by the time it ends and would replace a fresher one)
    return n

def main():
    a = sys.argv[1:]
    if a[0] == 'init':
        bucket, prefix, f = a[1:4]
        ids = [json.loads(l)['id'] for l in open(f) if l.strip()]
        assert len(ids) == len(set(ids)), 'duplicate package ids'
        objstore.upload_file(bucket, prefix.rstrip('/') + '/packages.jsonl', f); print('init: %d packages' % len(ids))
    elif a[0] == 'add':
        # pbq.py add BUCKET PREFIX FILE [--front]: append new package lines (new ids only); --front puts them at the head of the claim
        # order (workers restart their cursor at the next rescan, within 10 min)
        bucket, prefix, f = a[1:4]; front = '--front' in a
        for att in range(5):
            r = objstore.get(bucket, prefix.rstrip('/') + '/packages.jsonl'); gen = r[1]
            old = [l for l in r[0].decode().splitlines() if l.strip()]; ids = {json.loads(l)['id'] for l in old}
            new = [l.rstrip('\n') for l in open(f) if l.strip() and json.loads(l)['id'] not in ids]
            body = '\n'.join((new + old) if front else (old + new)) + '\n'
            try:
                objstore.put(bucket, prefix.rstrip('/') + '/packages.jsonl', body, if_generation=gen); print('added %d packages (%s); now %d' % (len(new), 'front' if front else 'end', len(old) + len(new))); break
            except objstore.Precondition:
                continue
    elif a[0] == 'status':
        bucket, prefix = a[1:3]; c = {}
        for it in objstore.ls(bucket, prefix.rstrip('/') + '/lease/'):
            r = objstore.get(bucket, it['name']); s = json.loads(r[0]).get('state') if r else '?'; c[s] = c.get(s, 0) + 1
        nd = sum(1 for _ in objstore.ls(bucket, prefix.rstrip('/') + '/done/'))
        print(json.dumps(dict(leases=c, done_records=nd)))
    elif a[0] == 'snapshot':
        # pbq.py snapshot BUCKET PREFIX [--loop S]: the taken-lease and done snapshots (taken.json.gz, done.json.gz) every S s.  The
        # listings run in parallel over id prefixes (each covering <= 4,000 package ids) and ask for names only, so the snapshot
        # stays fresh on a queue of ~10^5 packages (claimers working from a stale snapshot collide on taken packages)
        bucket, prefix = a[1:3]; loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 0; p = prefix.rstrip('/')
        import concurrent.futures as cf
        pkgen = [None]; pfx = [['']]
        def prefixes():
            m = objstore.stat(bucket, p + '/packages.jsonl')
            if m and m['generation'] != pkgen[0]:
                r = objstore.get(bucket, p + '/packages.jsonl'); ids = [json.loads(l)['id'] for l in r[0].decode().splitlines() if l.strip()]
                out = []; todo = [('', ids)]
                while todo:
                    pre, grp = todo.pop()
                    if len(grp) <= 4000 or len(pre) >= 12: out.append(pre); continue
                    sub = {}
                    for i in grp: sub.setdefault(i[:len(pre) + 1], []).append(i)
                    todo += list(sub.items())
                pfx[0] = out; pkgen[0] = m['generation']
            return pfx[0]
        def names(sub, cut=0):
            def one(pre): return [it['name'].rsplit('/', 1)[1] for it in objstore.ls(bucket, p + '/' + sub + '/' + pre, fields='name')]
            with cf.ThreadPoolExecutor(32) as ex: got = [n for L in ex.map(one, prefixes()) for n in L]
            # an id shorter than its prefix (a prefix that is itself an id) is listed by several prefixes: dedup
            return sorted(set(n[:-cut] if cut else n for n in got))
        while True:
            t = time.time()
            try:
                ids = names('lease')
                objstore.put(bucket, p + '/taken.json.gz', gzip.compress(json.dumps(dict(t=t, ids=ids)).encode()), content_type='application/gzip')
                dn = names('done', len('.json'))
                objstore.put(bucket, p + '/done.json.gz', gzip.compress(json.dumps(dict(t=t, ids=dn)).encode()), content_type='application/gzip')
                print(time.strftime('%FT%TZ', time.gmtime()), 'snapshot %d leases, %d done in %.1f s (%d prefixes)' % (len(ids), len(dn), time.time() - t, len(pfx[0])), flush=True)
            except Exception as e:
                print(time.strftime('%FT%TZ', time.gmtime()), 'snapshot error (continuing)', repr(e)[:300], flush=True)
            if not loop: break
            time.sleep(max(0, loop - (time.time() - t)))
    elif a[0] == 'sweep':
        bucket, prefix = a[1:3]; loop = int(a[a.index('--loop') + 1]) if '--loop' in a else 0
        wf = a[a.index('--workers-file') + 1] if '--workers-file' in a else None
        while True:
            try:
                n = sweep(bucket, prefix, log=lambda s: print(time.strftime('%FT%TZ', time.gmtime()), s, flush=True), workers_file=wf)
                print(time.strftime('%FT%TZ', time.gmtime()), 'sweep', json.dumps(n), flush=True)
            except Exception as e:      # one bad object or a transient error must not stop the sweeping
                print(time.strftime('%FT%TZ', time.gmtime()), 'sweep error (continuing)', repr(e)[:300], flush=True)
            if not loop: break
            time.sleep(loop)

if __name__ == '__main__':
    main()
