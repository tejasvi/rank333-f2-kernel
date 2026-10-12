#!/usr/bin/env python3
"""objstore.py: the object-store client of the build queue (standard library only).  Every queue object (spec list, leases, done
records, tarballs) lives in a store namespace ("bucket") under a name; every write can carry a generation precondition, which is what
makes the queue's leases atomic.

Backend (env PB_STORE):
  file:///ABS/DIR    a local directory: object NAME of namespace B is DIR/B/NAME; its generation is an integer kept in
                     DIR/B/NAME.gen~; writes go to a temporary file and are renamed into place under an fcntl lock (DIR/.lock~),
                     so preconditions hold across processes on one machine (or on a shared filesystem with POSIX locks)
  http(s)://...      a JSON object API with generation preconditions: env PB_STORE_API and PB_STORE_UPLOAD are URL templates with
                     one %s for the namespace (object metadata at API/<quoted name>, media at ...?alt=media, uploads at
                     UPLOAD?uploadType=media&name=<quoted name>, preconditions as ifGenerationMatch=<n>, listings as
                     API?prefix=...&pageToken=...); a bearer token comes from the command in env PB_STORE_TOKEN_CMD (cached 25 min)
Namespace and queue prefix: env PB_BUCKET (default "kp") and PB_PREFIX (default "pb/run"), exported here as BUCKET and PREFIX.

Operations (same in both backends):
  put(bucket, name, data, if_generation=None) -> metadata dict; raises Precondition when the generation does not match
                                                 (if_generation=0: the object must not exist)
  get(bucket, name) -> (bytes, generation) or None        stat(bucket, name) -> metadata dict or None
  fetch(bucket, name) -> bytes (one read, no consistency check: immutable objects such as tarballs)
  delete(bucket, name, if_generation=None) -> True / False (absent) / raises Precondition
  ls(bucket, prefix, fields=None) -> iterator of metadata dicts (name, generation, size, updated, md5Hash)
  upload_file(bucket, name, path, if_generation=None) -> metadata;  download_file(bucket, name, path) -> bytes written
The http backend retries transient errors (429, 5xx, timeouts) with exponential backoff."""
import base64, datetime, fcntl, hashlib, json, os, subprocess, time, urllib.error, urllib.parse, urllib.request

STORE = os.environ.get('PB_STORE', 'file://' + os.path.abspath('pbstore'))
BUCKET = os.environ.get('PB_BUCKET', 'kp')
PREFIX = os.environ.get('PB_PREFIX', 'pb/run').rstrip('/')

class Precondition(Exception):
    pass

def _q(name): return urllib.parse.quote(name, safe='')

# ---------------------------------------------------------------- file backend
class _File:
    def __init__(self, root):
        self.root = root; os.makedirs(root, exist_ok=True)
    def _p(self, bucket, name):
        p = os.path.normpath(os.path.join(self.root, bucket, name))
        if not p.startswith(os.path.normpath(os.path.join(self.root, bucket)) + os.sep): raise ValueError('bad object name %r' % name)
        return p
    def _lock(self):
        f = open(os.path.join(self.root, '.lock~'), 'a'); fcntl.flock(f, fcntl.LOCK_EX); return f
    def _gen(self, p):
        try: return int(open(p + '.gen~').read().strip() or 0)
        except FileNotFoundError: return 0
    def _meta(self, bucket, name, p):
        st = os.stat(p); b = open(p, 'rb').read()
        return dict(name=name, bucket=bucket, generation=str(self._gen(p)), size=str(st.st_size),
                    updated=datetime.datetime.fromtimestamp(st.st_mtime, datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%S.%fZ'),
                    md5Hash=base64.b64encode(hashlib.md5(b).digest()).decode())
    def put(self, bucket, name, data, if_generation=None, **kw):
        p = self._p(bucket, name); os.makedirs(os.path.dirname(p), exist_ok=True)
        with self._lock():
            cur = self._gen(p) if os.path.exists(p) else 0
            if if_generation is not None and int(if_generation) != cur: raise Precondition(name)
            g = max(cur, self._gen(p)) + 1
            t = p + '.tmp~%d' % os.getpid()
            with open(t, 'wb') as f: f.write(data); f.flush(); os.fsync(f.fileno())
            os.replace(t, p); open(p + '.gen~', 'w').write(str(g))
            return self._meta(bucket, name, p)
    def stat(self, bucket, name, **kw):
        p = self._p(bucket, name)
        return self._meta(bucket, name, p) if os.path.exists(p) else None
    def get(self, bucket, name, **kw):
        p = self._p(bucket, name)
        with self._lock():
            if not os.path.exists(p): return None
            return (open(p, 'rb').read(), self._gen(p))
    def delete(self, bucket, name, if_generation=None, **kw):
        p = self._p(bucket, name)
        with self._lock():
            if not os.path.exists(p): return False
            if if_generation is not None and int(if_generation) != self._gen(p): raise Precondition(name)
            os.remove(p)       # the generation file stays: a re-created object continues the count (no ABA)
            return True
    def ls(self, bucket, prefix='', fields=None):
        base = os.path.join(self.root, bucket)
        out = []
        for dp, dn, fn in os.walk(base):
            for f in fn:
                if f.endswith('.gen~') or '.tmp~' in f: continue
                name = os.path.relpath(os.path.join(dp, f), base).replace(os.sep, '/')
                if name.startswith(prefix): out.append(name)
        for name in sorted(out):
            m = self._meta(bucket, name, os.path.join(base, name))
            yield {k: m[k] for k in fields.split(',')} if fields else m

# ---------------------------------------------------------------- http backend
class _Http:
    def __init__(self):
        self.api = os.environ['PB_STORE_API']; self.up = os.environ['PB_STORE_UPLOAD']; self.tok = [None, 0.0]
    def token(self):
        if self.tok[0] and time.time() < self.tok[1]: return self.tok[0]
        self.tok[0] = subprocess.check_output(os.environ['PB_STORE_TOKEN_CMD'], shell=True, text=True).strip(); self.tok[1] = time.time() + 1500
        return self.tok[0]
    def req(self, method, url, data=None, headers=None, raw=False, ok404=False, timeout=90, tries=8):
        h = {'Authorization': 'Bearer ' + self.token()}; h.update(headers or {})
        for att in range(tries):
            try:
                # a connection without a byte for `timeout` s is treated as stalled and retried
                r = urllib.request.urlopen(urllib.request.Request(url, data=data, headers=h, method=method), timeout=timeout)
                b = r.read()
                return b if raw else (json.loads(b) if b else {})
            except urllib.error.HTTPError as e:
                if e.code == 412: raise Precondition(url)
                if e.code == 404 and ok404: return None
                if e.code in (401,): self.tok[0] = None; h['Authorization'] = 'Bearer ' + self.token()
                elif e.code not in (408, 429, 500, 502, 503, 504): raise
            except (urllib.error.URLError, TimeoutError, ConnectionError, OSError):
                pass
            time.sleep(min(60, 2 ** att))
        raise RuntimeError('objstore: giving up on %s %s' % (method, url))
    def put(self, bucket, name, data, if_generation=None, content_type='application/octet-stream', timeout=90, tries=8):
        url = self.up % bucket + '?uploadType=media&name=' + _q(name)
        if if_generation is not None: url += '&ifGenerationMatch=%d' % int(if_generation)
        return self.req('POST', url, data=data, headers={'Content-Type': content_type}, timeout=timeout, tries=tries)
    def stat(self, bucket, name, timeout=90, tries=8):
        return self.req('GET', self.api % bucket + '/' + _q(name), ok404=True, timeout=timeout, tries=tries)
    def get(self, bucket, name, timeout=90, tries=8):
        """(content, generation) of one consistent generation: an object rewritten between the stat and the read is read again"""
        for att in range(10):
            m = self.stat(bucket, name, timeout=timeout, tries=tries)
            if m is None: return None
            try:
                b = self.req('GET', self.api % bucket + '/' + _q(name) + '?alt=media&ifGenerationMatch=' + str(m['generation']), raw=True, ok404=True, timeout=timeout, tries=tries)
            except Precondition:
                continue
            if b is None: continue
            return (b, int(m['generation']))
        raise RuntimeError('objstore.get: %s keeps changing' % name)
    def fetch(self, bucket, name, timeout=180, tries=8):
        return self.req('GET', self.api % bucket + '/' + _q(name) + '?alt=media', raw=True, timeout=timeout, tries=tries)
    def delete(self, bucket, name, if_generation=None, **kw):
        url = self.api % bucket + '/' + _q(name) + ('?ifGenerationMatch=%d' % int(if_generation) if if_generation is not None else '')
        return self.req('DELETE', url, ok404=True, raw=True) is not None
    def ls(self, bucket, prefix='', fields=None):
        tok = ''
        while True:
            url = self.api % bucket + '?prefix=' + _q(prefix) + '&maxResults=1000' + ('&pageToken=' + _q(tok) if tok else '') + \
                  ('&fields=' + _q('items(%s),nextPageToken' % fields) if fields else '')
            d = self.req('GET', url)
            for it in d.get('items', []): yield it
            tok = d.get('nextPageToken', '')
            if not tok: return

_B = _File(STORE[len('file://'):]) if STORE.startswith('file://') else _Http()

def put(bucket, name, data, if_generation=None, content_type='application/octet-stream', timeout=90, tries=8):
    if isinstance(data, str): data = data.encode()
    if isinstance(_B, _File): return _B.put(bucket, name, data, if_generation)
    return _B.put(bucket, name, data, if_generation, content_type=content_type, timeout=timeout, tries=tries)
def stat(bucket, name, timeout=90, tries=8): return _B.stat(bucket, name, timeout=timeout, tries=tries)
def get(bucket, name, timeout=90, tries=8): return _B.get(bucket, name, timeout=timeout, tries=tries)
def fetch(bucket, name, timeout=180, tries=8):
    if isinstance(_B, _File):
        g = _B.get(bucket, name)
        if g is None: raise FileNotFoundError(name)
        return g[0]
    return _B.fetch(bucket, name, timeout=timeout, tries=tries)
def delete(bucket, name, if_generation=None): return _B.delete(bucket, name, if_generation=if_generation)
def ls(bucket, prefix='', fields=None): return _B.ls(bucket, prefix, fields)
def upload_file(bucket, name, path, if_generation=None):
    """one-request upload (files up to a few GB); returns the object metadata (md5Hash, size)"""
    with open(path, 'rb') as f: data = f.read()
    return put(bucket, name, data, if_generation=if_generation)
def download_file(bucket, name, path):
    b = fetch(bucket, name)
    tmp = path + '.part%d' % os.getpid()
    with open(tmp, 'wb') as f: f.write(b); f.flush(); os.fsync(f.fileno())
    os.replace(tmp, path)
    return len(b)
