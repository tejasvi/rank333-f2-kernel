module
public import E1G.IP_l479cw
public import E1G.SL_l479cw
meta import KMod.Units
meta import KMod.Audit
meta import KModT.E1Comb
import KMod.Vocab
set_option Elab.async false
set_option maxRecDepth 100000
#kunits B "port_data/106292b62dcc2dcc2a4b6a65ab1eaa1a/R479.bin" 4 (fun L => E1G.block E1G.IP_l479cw.C (E1G.slc E1G.SL_l479cw.chunk) E1G.IP_l479cw.UB E1G.IP_l479cw.UBR L)
#kdispatch Lf B
#kpub KModT.E1.B4.ok : ∃ Lf : Nat → Nat, ∀ i, i < 227 → E1G.block E1G.IP_l479cw.C (E1G.slc E1G.SL_l479cw.chunk) E1G.IP_l479cw.UB E1G.IP_l479cw.UBR (Lf i) = true := KModT.e1Comb B
#kax KModT.E1.B4.ok
#kaxp KModT.E1.B4.ok
