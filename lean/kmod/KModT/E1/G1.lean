module
public import E1G.IP_l479cw
public import E1G.SL_l479cw
meta import KMod.Units
meta import KMod.Audit
meta import KModT.E1Comb
import KMod.Vocab
set_option Elab.async false
set_option maxRecDepth 100000
#kunits B "test/data/R479_20.bin" (fun L => E1G.block E1G.IP_l479cw.C (E1G.slc E1G.SL_l479cw.chunk) E1G.IP_l479cw.UB E1G.IP_l479cw.UBR L)
#kdispatch Lf B
#klits W "test/data/wf20.bin"
#kdispatch Wf W
#kunits G "test/data/idx20.bin" 4 (fun i => Nat.blt 0 (Lf (Wf i)) && Nat.blt (Wf i) 20)
#kpub KModT.E1.G1.ok : ∃ Lf : Nat → Nat, ∀ i, i < 20 → E1G.block E1G.IP_l479cw.C (E1G.slc E1G.SL_l479cw.chunk) E1G.IP_l479cw.UB E1G.IP_l479cw.UBR (Lf i) = true := KModT.e1Comb B
#kax KModT.E1.G1.ok
#kkey "R479:0" "R479:19"
#kext "1 2 3" "4 5"
