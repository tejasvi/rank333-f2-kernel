module
public import R22Port.U_d41d8cd98f00
public import HC.Pad
public import E1.IP_e303
public import RT.Cls_e303
import G2.E303
meta import KMod.Units
meta import KMod.Audit
set_option Elab.async false
/-! # The crown of class 303 (G2): `HC.E1Concl Em 18` (E1 for the IP `e303`), given the IP's class table

The statement of `G2.E303.e303_final` (leaf2's E1 route, kernel only), whose conclusion is literally the body of
`HC.E1Concl Em 18`. The job modules (chain, blocks, external leaves) are a private import. It replaces
`E1NR1.Crown303.crown g303` (native glue and #ndbool) in R22B.CapLeaf2. -/
#kpubterm G2.Crown303.crown : ∀ (hcls : ∀ c, RT.Fact (RT.kM RT.Cls_e303.CL c) (RT.cLB RT.Cls_e303.CL c)),
    HC.E1Concl E1.IP_e303.Em 18 := fun hcls => G2.E303.e303_final hcls
#kax G2.Crown303.crown
#print axioms G2.Crown303.crown
