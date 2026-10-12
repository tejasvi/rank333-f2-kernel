module
public import R22K.FinalAll
public import PLE.c436.Sub
public import PLE.c422.Sub
public import KJ.agg436_Root
public import KJ.agg422_Root
public meta import Lean
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-! CHECK ONLY: the published c436 and c422 producers against R22K.FinalAll's binders (the cap roots `KJ.agg<C>.Root`, the EXT tops `PLE.c<C>`) -/
#check (R22K.FinalAll.rank_ge_23_of (ext436 := KJ.agg436.Root.EXT) (root436 := KJ.agg436.Root.root) (hx436 := PLE.c436.Ext.hext_of)
  (sub436 := PLE.c436.Sub.sub) (ext422 := KJ.agg422.Root.EXT) (root422 := KJ.agg422.Root.root) (hx422 := PLE.c422.Ext.hext_of)
  (sub422 := PLE.c422.Sub.sub))
#print axioms PLE.c436.Sub.sub
#print axioms PLE.c436.Ext.hext_of
