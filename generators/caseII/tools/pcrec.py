#!/usr/bin/env python3
"""pcrec.py PCERT... : the comparison hashes of phase-0 pcerts. One TSV line per file: name, bytes, sha256 of the file, sha256 of the
header without its run-specific lines, sha256 of the records.

A pcert is a text header ending with the line `#end`, then binary records. The header lines `#R3PC 1 fp=<fingerprint>` (a per-run
fingerprint), `#table <path>` and `#kept <path>` (where the run found its table files) depend on the run; every other header line and
the records do not. Two runs of the same phase-0 command on the same tables give the same header hash and the same records hash."""
import sys, os, hashlib
from concurrent.futures import ProcessPoolExecutor
SKIP = (b'#R3PC ', b'#table ', b'#kept ')

def one(f):
    hf, hh, hr = hashlib.sha256(), hashlib.sha256(), hashlib.sha256(); n = 0; inh = True
    with open(f, 'rb') as h:
        while inh:
            ln = h.readline()
            if not ln: break
            hf.update(ln); n += len(ln)
            if not ln.startswith(SKIP): hh.update(ln)
            if ln == b'#end\n': inh = False
        while True:
            b = h.read(1 << 24)
            if not b: break
            hf.update(b); hr.update(b); n += len(b)
    return '%s\t%d\t%s\t%s\t%s' % (os.path.basename(f), n, hf.hexdigest(), hh.hexdigest(), hr.hexdigest())

if __name__ == '__main__':
    fs = sys.argv[1:]
    with ProcessPoolExecutor(int(os.environ.get('PAR', '8'))) as ex:
        for line in ex.map(one, fs): print(line, flush=True)
