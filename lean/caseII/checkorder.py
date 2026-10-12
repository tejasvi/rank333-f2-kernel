#!/usr/bin/env python3
"""checkorder.py [ORDERFILE...]: the build order as one sequence (default build_order.txt then build_order_ext.txt) must be topological:
every import of a listed module that is itself listed comes earlier. Exit 1 and print the violations otherwise."""
import sys, os, re
M = os.path.dirname(os.path.abspath(__file__))
files = sys.argv[1:] or [M + '/build_order.txt', M + '/build_order_ext.txt']
order = [m for f in files for m in open(f).read().split()]
pos = {m: i for i, m in enumerate(order)}
if len(pos) != len(order): sys.exit('checkorder: a module is listed twice')
bad = sorted({(m, imp) for i, m in enumerate(order)
              for imp in re.findall(r'^(?:public )?(?:meta )?import (\S+)', open(os.path.join(M, 'src', m.replace('.', '/') + '.lean')).read(), re.M)
              if imp in pos and pos[imp] > i})
print('checkorder: %d modules, %d violations%s' % (len(order), len(bad), ''.join('\n  %s imports %s (listed later)' % b for b in bad)))
sys.exit(1 if bad else 0)
