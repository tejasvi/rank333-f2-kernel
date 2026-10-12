module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
meta import KModT.Comb
import KMod.Vocab
set_option Elab.async false
set_option maxRecDepth 100000
#kunits V "test/data/T1_m3.bin" 1 (fun R => BC7.leafS R)
#kpub KModT.T1.L.m3.ok : KModT.Good 1000 := KModT.goodComb V
#kax KModT.T1.L.m3.ok
#kkey "3000" "3999"
