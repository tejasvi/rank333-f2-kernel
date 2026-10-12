module
public import R22Port.U_d41d8cd98f00
public import HC.Pad
public import E1.IP_e321
public import RT.Cls_e321
import G2.E321
meta import KMod.Units
meta import KMod.Audit
set_option Elab.async false
/-! # The crown of class 321 (G2): `HC.E1Concl Em 18` (E1 for the IP `e321`), given the IP's class table

The statement of `G2.E321.e321_final` (leaf2's E1 route, kernel only), whose conclusion is literally the body of
`HC.E1Concl Em 18`. The job modules (chain, blocks, external leaves) are a private import. It replaces
`E1NR1.Crown321.crown g321` (native glue and #ndbool) in R22B.CapLeaf2. -/
#kpubterm G2.Crown321.crown : ∀ (hcls : ∀ c, RT.Fact (RT.kM RT.Cls_e321.CL c) (RT.cLB RT.Cls_e321.CL c)),
    HC.E1Concl E1.IP_e321.Em 18 := fun hcls => G2.E321.e321_final hcls
#kax G2.Crown321.crown
#print axioms G2.Crown321.crown
