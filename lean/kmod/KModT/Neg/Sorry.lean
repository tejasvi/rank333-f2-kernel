module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
set_option Elab.async false
#kpubterm KModT.Neg.Sorry.ok : KModT.Good 1 := sorry
#kax KModT.Neg.Sorry.ok
