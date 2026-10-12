module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
import KModT.T4.A1.a0
import KModT.T4.A1.a1
set_option Elab.async false
set_option maxRecDepth 100000
#kpubterm KModT.T4.A2.a0.ok : KModT.Good 8000 := (KModT.good_add KModT.T4.A1.a0.ok KModT.T4.A1.a1.ok)
#kax KModT.T4.A2.a0.ok
#kaxp KModT.T4.A2.a0.ok
