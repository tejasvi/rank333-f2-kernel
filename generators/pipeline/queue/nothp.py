#!/usr/bin/env python3
"""nothp.py CMD...: run CMD with transparent huge pages disabled for it and its children (prctl PR_SET_THP_DISABLE), so that
the Lean heap is not backed by 2 MB pages (on a machine with THP=always, which inflates each lean process's anonymous memory
several-fold)."""
import ctypes, os, sys
libc = ctypes.CDLL(None, use_errno=True)
if libc.prctl(41, 1, 0, 0, 0) != 0: sys.exit('prctl(PR_SET_THP_DISABLE) failed: errno %d' % ctypes.get_errno())
os.execvp(sys.argv[1], sys.argv[1:])
