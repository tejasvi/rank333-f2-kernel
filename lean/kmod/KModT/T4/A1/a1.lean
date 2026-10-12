module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
import KModT.T4.L.m4
import KModT.T4.L.m5
import KModT.T4.L.m6
import KModT.T4.L.m7
set_option Elab.async false
set_option maxRecDepth 100000
#kpubterm KModT.T4.A1.a1.ok : KModT.Good 4000 := (KModT.good_add (KModT.good_add KModT.T4.L.m4.ok KModT.T4.L.m5.ok) (KModT.good_add KModT.T4.L.m6.ok KModT.T4.L.m7.ok))
#kax KModT.T4.A1.a1.ok
