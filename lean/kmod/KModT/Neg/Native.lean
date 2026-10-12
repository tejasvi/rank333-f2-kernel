module
public import KModT.Good
meta import KMod.Units
meta import KMod.Audit
set_option Elab.async false
#kpubterm KModT.Neg.Native.ok : KModT.Good 1 := (fun (_ : (2 : Nat) + 2 = 4) => KModT.good_one (R := 2958199950160750294259647328010767958381811568369751658674835952681334753542630613513645218700671016482363875839791602583789083157739961312996470344238026884915478820400711690532790891959766748725547159853960599443669395) (by decide +kernel)) (by native_decide)
#kax KModT.Neg.Native.ok
#kaxp KModT.Neg.Native.ok
