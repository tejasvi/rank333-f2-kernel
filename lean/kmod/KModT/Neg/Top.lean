module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
import KModT.Neg.Ax
import KModT.T1.A2.a0
set_option Elab.async false
#kpubterm KModT.Neg.Top.ok : KModT.Good 8001 := KModT.good_add KModT.T1.A2.a0.ok KModT.Neg.Ax.ok
#kax KModT.Neg.Top.ok
#kaxp KModT.Neg.Top.ok
