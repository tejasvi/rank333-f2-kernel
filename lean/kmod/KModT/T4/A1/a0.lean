module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
import KModT.T4.L.m0
import KModT.T4.L.m1
import KModT.T4.L.m2
import KModT.T4.L.m3
set_option Elab.async false
set_option maxRecDepth 100000
#kpubterm KModT.T4.A1.a0.ok : KModT.Good 4000 := (KModT.good_add (KModT.good_add KModT.T4.L.m0.ok KModT.T4.L.m1.ok) (KModT.good_add KModT.T4.L.m2.ok KModT.T4.L.m3.ok))
#kax KModT.T4.A1.a0.ok
