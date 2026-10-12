module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
import KModT.T1.L.m4
import KModT.T1.L.m5
import KModT.T1.L.m6
import KModT.T1.L.m7
set_option Elab.async false
set_option maxRecDepth 100000
#kpubterm KModT.T1.A1.a1.ok : KModT.Good 4000 := (KModT.good_add (KModT.good_add KModT.T1.L.m4.ok KModT.T1.L.m5.ok) (KModT.good_add KModT.T1.L.m6.ok KModT.T1.L.m7.ok))
#kax KModT.T1.A1.a1.ok
