#!/usr/bin/env python3
"""mkslice.py CTX START COUNT NAME [THREADS [SPLITDEPTH]]: jobs START .. START+COUNT-1 of a context (c436, c422, ptc) as KJ
modules over the context's job table (kjlib.make_slice):
  1. emits the jobs (lineenum9qe_ld5, delegated layout: leaves of >= 64 bits as blocks of their own, 16k block limit;
     certificates over kjlib.EXTBITS bits external; E1P_LEAFDUMP for the bit model) into the context's run directory;
  2. per job: blocks, glue witnesses, units (kjlib.write_job);
  3. oversize jobs (over 600 s) split 2 levels deeper, recursively; heavy leaves (over 5 s) apart;
  4. leaf-range modules (#e1gjobs / #e1pjobs, <= 300 s) and fan-in-100 aggregators, each with #kax / #kkey (#kext);
  5. the manifest and the build order in slice_<NAME>/.
  SPLITDEPTH (known heavy jobs): no whole-job emission; every job of the range is split at that depth."""
import sys, os
sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kjlib as K
ctx, start, count, name = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
TH = int(sys.argv[5]) if len(sys.argv) > 5 else 14
FS = int(sys.argv[6]) if len(sys.argv) > 6 else 0
K.make_slice(ctx, start, count, name, TH, FS)
