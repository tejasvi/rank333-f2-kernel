module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
set_option Elab.async false
private axiom cheat : KModT.Good 1
#kpubterm KModT.Neg.Ax.ok : KModT.Good 1 := cheat
#kax KModT.Neg.Ax.ok
