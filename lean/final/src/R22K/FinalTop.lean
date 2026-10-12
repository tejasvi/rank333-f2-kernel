module
public import R22Port.U_d41d8cd98f00
public import S4.Top436
public import R22B.Segs
public import KB.AggCC_cc436_422
public import KB.Agg321
public import E1GK.ExtMono
public import HC.RRData
meta import KMod.Audit
/-! # R22K.FinalTop: the kernel-only final theorem, from each tier's root statement as its emitter publishes it

`R22K.FinalTop.rank_ge_23` proves `Top.RankGe23` through the CC route `Top.rank_ge_23_436_422` (s443/mod/src/S4/Top436.lean). Every
hypothesis is one tier's public root theorem in the exact form its emitter writes (the producer is named on each binder group):

* **capacity table** `hCap` (`R22K.Cap.hCap`, module R22K.Cap: R22B.CapLeaf2 renamed, with the G2 crowns and the class
  certificates `KC.h<c>.classLB`), **RR table** `hrr` (`HC.rr_all`), **point lemma** `point` (`KJ.aggptc.point`);
* **Gram props** (`R22B.GramCrown`);
* **c436 / c422**: the root `KJ.agg<C>.Root.root` over its list `KJ.agg<C>.Root.EXT` (`#e1groot`, the canonical-point
  statement over `E1GS.withExt IP.C EXT`), and the EXT top `PLE.c<C>.Ext.hext_of` over its literal `ALL` with
  `EXT ⊆ ALL` (decided at instantiation);
* **case II**: the case-(II) root `KM2.Top.segs : R22N.AllL KB.SegsOfKeyCC [root keys]` (`#kmTop`), with the key of the case's root
  `((1, 0), 0)`;
* **cases I / I13**: `KMIA.Top.vI` / `KMJJ.Top.vI` (`#kmVI321`, `R22B.Final`'s `vI` form over `KB.CheckedAny321 0 12` /
  `KB.CheckedAny321 13 13`), turned into segment families by `R22B.segs_of_covH_roots` with the contract `KB.segRefAny321`.

The final instance (R22K.Final) applies this theorem to the named public theorems.
KMod form: the proof is the private theorem `main`; `#k1top` publishes it as `R22K.FinalTop.rank_ge_23` (KPUB), with `#kax` and
`#print axioms` (KAXSUM, KAXP lines for the module's .kman). -/
set_option Elab.async false
@[expose] public section

noncomputable section
namespace R22K.FinalTop
open Top R3RT.SpecO

private theorem main
    -- capacity table (`R22K.Cap.hCap …`), RR table (`HC.rr_all`), point lemma (`KJ.aggptc.point`)
    (hrr : HC.RRAll)
    (hCap : ∀ p ∈ HC.T_K3eD_Cls.RL, p.1 ≠ 492 → HC.ClassLB p.1 p.2)
    (point : ∀ (_ : HC.RRAll) (_ : ∀ p ∈ HC.T_K3eD_Cls.RL, p.1 ≠ 492 → HC.ClassLB p.1 p.2), HC.ClassLB 492 21)
    -- Gram props (`R22B.GramCrown`)
    (g175 : G.NoFam_17_5_0) (g1903 : G.NoFam_19_0_3) (g1822 : G.NoFam_18_2_2) (g1741 : G.NoFam_17_4_1)
    (g1732 : G.NoFam_17_3_2) (g1813 : G.NoFam_18_1_3)
    (oc0 : G.OrbitComplete2) (oc1 : G.OrbitComplete3 1) (oc2 : G.OrbitComplete3 2)
    -- c436: the root (`KJ.agg436.Root.EXT`, `KJ.agg436.Root.root`), the EXT top (`ALL`, `PLE.c436.Ext.hext_of`)
    (ext436 : List ℕ)
    (root436 : ∀ x : ℕ → ℕ, E1GS.Glob (E1GS.withExt E1G.IP_c436.C ext436) x →
      (∀ i < 2 ^ 15, E1GS.SlotV x (E1G.slc E1G.SL_c436.chunk i)) → (∀ l < 127, x l ≤ E1G.fld E1G.IP_c436.UB l) →
      (∃ l < 127, 0 < x l) → False)
    (all436 : List ℕ)
    (hx436 : ∀ (ext : List ℕ), (∀ pl ∈ ext, pl ∈ all436) →
      ∀ pl ∈ ext, L479.LeafNoExt (E1G.OK_c436.Cx ext) E1G.IP_c436.Em 14 pl)
    (sub436 : ∀ pl ∈ ext436, pl ∈ all436)
    -- c422: likewise (`KJ.agg422.Root.EXT`, `KJ.agg422.Root.root`; `PLE.c422.Ext.hext_of`)
    (ext422 : List ℕ)
    (root422 : ∀ x : ℕ → ℕ, E1GS.Glob (E1GS.withExt E1G.IP_c422.C ext422) x →
      (∀ i < 2 ^ 15, E1GS.SlotV x (E1G.slc E1G.SL_c422.chunk i)) → (∀ l < 127, x l ≤ E1G.fld E1G.IP_c422.UB l) →
      (∃ l < 127, 0 < x l) → False)
    (all422 : List ℕ)
    (hx422 : ∀ (ext : List ℕ), (∀ pl ∈ ext, pl ∈ all422) →
      ∀ pl ∈ ext, L479.LeafNoExt (E1G.OK_c422.Cx ext) E1G.IP_c422.Em 14 pl)
    (sub422 : ∀ pl ∈ ext422, pl ∈ all422)
    -- case II: the top `KM2.Top.segs` over its root keys; `kII` the key of the root `((1, 0), 0)`
    (keysII : List ℕ) (segsII : R22N.AllL KB.SegsOfKeyCC keysII)
    (kII : ℕ) (hkII : kII ∈ keysII) (hrII : (R22N.SegI.ofKey kII).root = (1, 0)) (hlII : (R22N.SegI.ofKey kII).lo = 0)
    -- case I: `KMIA.Top.vI`; case I13: `KMJJ.Top.vI`
    (vI : ∀ l ∈ ([0, 168, 462] : List ℕ), R22N.Cov (KB.CheckedAny321 0 12) ((2 ^ l, l), 0))
    (vI13 : ∀ l ∈ ([0, 168, 462] : List ℕ), R22N.Cov (KB.CheckedAny321 13 13) ((2 ^ l, l), 0)) :
    RankGe23 := by
  -- case II: the root key's segment family; the table `KCC_cc436_422.L` is the CC route's `L`
  obtain ⟨ιII, sII, hsII, hgII, i0, hr0, hl0⟩ := R22N.allL_mem segsII kII hkII
  -- cases I / I13: `R22B.Final`'s step
  obtain ⟨ιI, sI, hsI, hgI, hrI⟩ :=
    R22B.segs_of_covH_roots _ _ _ (KB.CheckedAny321 0 12) (KB.segRefAny321 0 12)
      (fun x => ∃ l ∈ ([0, 168, 462] : List ℕ), x = ((2 ^ l, l), 0)) (fun x ⟨l, hl, hx⟩ => hx ▸ vI l hl)
  obtain ⟨ιI13, sI13, hsI13, hgI13, hrI13⟩ :=
    R22B.segs_of_covH_roots _ _ _ (KB.CheckedAny321 13 13) (KB.segRefAny321 13 13)
      (fun x => ∃ l ∈ ([0, 168, 462] : List ℕ), x = ((2 ^ l, l), 0)) (fun x ⟨l, hl, hx⟩ => hx ▸ vI13 l hl)
  exact rank_ge_23_436_422 (point hrr hCap) hCap g175 g1903 g1822 g1741 g1732 g1813 oc0 oc1 oc2
    ext436 root436 (fun pl hpl => hx436 ext436 sub436 pl hpl)
    ext422 root422 (fun pl hpl => hx422 ext422 sub422 pl hpl)
    ιII sII (fun hcf htf => hsII ⟨hcf, htf⟩) hgII ⟨i0, hr0.trans hrII, hl0.trans hlII⟩
    ιI sI hsI hgI (fun l hl => hrI _ ⟨l, hl, rfl⟩)
    ιI13 sI13 hsI13 hgI13 (fun l hl => hrI13 _ ⟨l, hl, rfl⟩)

#k1top R22K.FinalTop.rank_ge_23 [main]

end R22K.FinalTop
end
