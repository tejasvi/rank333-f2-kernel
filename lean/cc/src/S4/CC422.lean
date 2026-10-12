module
public import R22Port.U_d41d8cd98f00
public import S4.CCLeaf
public import LG.IPC422
/-! # The CC instance of class 422 (`L479.CCInst 422 19 14`) on the context-cap IP `c422`

`E1G.IP_c422` / `E1G.OK_c422` is the coset IP of `pc/ipc2_422.txt` (md5 f3bc13d2) in the order `o422_tighta` (md5 9fc56c95):
`E = span{1, 20, 66}`, `R = 19`, 63 labels, group of order 8, case row cap 6 at `i2 = 2823`. `L479.IPC422.ipg` holds its
facts. The symmetries `(true, 161, 273)` (`K_422` into `E`) and `(true, 273, 161)` (`E` into `K_422`) are decided there.

* `L479.CC422.inst ext henum hext`: the instance from the enumeration (`EnumOK (Cx ext) sl UB`, the E1G chains on
  this context) and the external leaves (`LeafNoExt`);
* `L479.CC422.inst_cert ext cert henum h`: the same with each external leaf given by its certificate (UNSAT, or the
  lifting test `PL.ltW3` on `pts = [1, 20, 21, 66, 67, 86, 87]`). -/
@[expose] public section

namespace L479.CC422
open E1GS E1G.IP_c422 E1G.OK_c422

def pts : List ℕ := [1, 20, 21, 66, 67, 86, 87]
theorem pts_nd : pts.Nodup := by decide
theorem pts_ok : PL.ptsOK pts Em = true := by decide +kernel
theorem pts_all : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts := PL.ptsOK_spec pts_ok

theorem inst (ext : List ℕ) (henum : EnumOK (Cx ext) sl UB) (hext : ∀ pl ∈ ext, LeafNoExt (Cx ext) Em 14 pl) :
    CCInst 422 19 14 :=
  ⟨Cx ext, Em, LB, LBR, UB, Ntab, nrows, i2, sl, tab, ge, L479.IPC422.ipg ext, rfl, henum, hext,
    by decide +kernel, ⟨true, 161, 273, by decide, by decide, L479.IPC422.mapK⟩,
    ⟨true, 273, 161, by decide, by decide, L479.IPC422.mapE⟩⟩

theorem inst_cert (ext : List ℕ) (cert : ℕ → ℕ) (henum : EnumOK (Cx ext) sl UB)
    (h : ∀ pl ∈ ext,
      S5.NoDecomp (S5.leafT (E1G.leafRec R VT DOM pl (cert pl))) (S5.leafN (E1G.leafRec R VT DOM pl (cert pl)))
        (S6.leafDom6 (E1G.leafRec R VT DOM pl (cert pl))) ∨
      BC7L.leafSL (PL.ltW3 pts 3) (E1G.leafRec R VT DOM pl (cert pl)) = true) : CCInst 422 19 14 :=
  inst ext henum (PL.leaves_of_cert (L479.IPC422.ipg ext) pts pts_nd pts_all cert h)

end L479.CC422

#print axioms L479.CC422.inst
#print axioms L479.CC422.inst_cert
