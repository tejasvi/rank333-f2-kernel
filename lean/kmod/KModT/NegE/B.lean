module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
import KModT.NegE.A
set_option Elab.async false
#kpubterm KModT.NegE.B.ok : True := (fun (_ : KModT.NegE.A.EXT.length = 1) => trivial) rfl
#kax KModT.NegE.B.ok
