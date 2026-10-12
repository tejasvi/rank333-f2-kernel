module
public import R22Port.U_d41d8cd98f00
public import KDK321.Ext
public import KDK.XBatchO
/-! # KDK321.Batch321 (kinds-only name of KD321.Batch321): the composed main-search batch checker at `--rord 321` (cases (I) / (I13))

The order-generic `KD.batchXO np ext` (`KD/XBatchO.lean`: L1 v5's `node5`, the bound bulk-peel part with the
deficit table's masks from `np`, and a per-node extension `ext` on the child frame) instantiated at
* the order `Top321.O`, any universe `Ω` (the 321 run's table facts hold at `ΩT`),
* `np = RT.O321.lpar511` (`npOK321`, from `vecOK321`),
* `ext = ext321h lo hi` (the KD321 records of one OPEN node: suffix break, PREFF / DOOM, CANON; `ext321_sound`),
* stack frames `FrameOK0` (valid, or the empty prefix's `(0, 0, CONF1, 0, 0)` below the depth-1 job root), whose node5
  contract is `node5_spec0` (`n5contract0`).
**`batch321_sound`**: an accepted batch gives `KD.BatchOKXO` (per node: the T/C kills, every bulk-peel child dead, a valid
child frame with `ext321` accepted on it); **`batch321_node`** turns the extension into the dead-children facts. -/
@[expose] public section
noncomputable section
namespace KD321
open RootSound R3RT R3RT.SpecO BC4 BC5 Classical

/-- the 321 odd-pairing masks satisfy the batch checker's `NpOK` -/
theorem npOK321 : KD.NpOK Top321.O RT.O321.lpar511 := fun X _ hX l hl => vecOK321.np_bit X hX l hl

/-- node5's contract for valid-or-empty frames, any order and universe -/
theorem n5contract0 (O : LabelOrder) (Ω : Spec.Dec22 → Prop) :
    KD.N5Contract O Ω (fun f => FrameOK0 O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2) :=
  fun S D N U dP c2 h suf rec ks k hF hC hH hR hn => node5_spec0 S D N U dP c2 h suf rec ks k hF hC hH hR hn

/-- the per-node extension at 321: `ext321` on the child frame (the conflict table is not used) -/
def ext321h (lo hi : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ × List ℕ × List ℕ) → Bool :=
  fun S D _N U d last e => ext321 lo hi S D U d last e

/-- **the composed batch checker at `--rord 321`** (case window `lo..hi`) -/
def batch321 (lo hi : ℕ) (tab : ℕ → ℕ) (st : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (nodes : List (KD.NodeX × (ℕ × List ℕ × List ℕ))) : Bool :=
  KD.batchXO RT.O321.lpar511 (ext321h lo hi) tab st nodes

/-- **Soundness of the 321 batch checker.** -/
theorem batch321_sound {Ω : Spec.Dec22 → Prop} (lo hi : ℕ) (tab : ℕ → ℕ) (hT : KD.TabOKO Top321.O Ω tab)
    (st : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (nodes : List (KD.NodeX × (ℕ × List ℕ × List ℕ)))
    (hst : ∀ f ∈ st, FrameOK0 Top321.O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2)
    (hnodes : ∀ x ∈ nodes, KD.C2OKO Top321.O Ω ((x.1.2.2.2.1 >>> 8) % 512) x.1.1 ∧
      HOK Top321.O ((x.1.2.2.2.1 >>> 8) % 512) x.1.2.1)
    (hfacts : ∀ x ∈ nodes, (∀ ag ∈ KD.nodeAggs x.1, KD.C2OKO Top321.O Ω ag.1 ag.2.1) ∧
      (∀ c ∈ KD.nodeKids x.1, KD.KidXOKO Top321.O Ω c))
    (h : batch321 lo hi tab st nodes = true) : KD.BatchOKXO Top321.O Ω (ext321h lo hi) st nodes :=
  KD.batchXO_sound npOK321 (n5contract0 Top321.O Ω) (fun S D N U d hF => frameOK0_of S D N U d hF) tab hT st nodes hst
    hnodes hfacts h

/-- **the extension's meaning on a node of an accepted batch**: on the child frame `(S', D', N', U', d')` that `BatchOKXO`
provides, children `≥ b` are dead for `Ω`, each PREFF / DOOM record's child for `Ω ∩ CaseK lo hi`, each CANON child for
canonical decompositions -/
theorem batch321_node {Ω : Spec.Dec22 → Prop} {lo hi S D N U d last : ℕ} {e : ℕ × List ℕ × List ℕ}
    (hF : KD.FrameOKO Top321.O Ω S D N U d) (h : ext321h lo hi S D N U d last e = true) :
    (∀ u, e.1 ≤ u → ∀ A : Spec.Dec22, Ω A → ¬ Continues Top321.O A S last u) ∧
    (∀ it ∈ e.2.1, ∀ A : Spec.Dec22, Ω A → CaseK lo hi A →
      ¬ Continues Top321.O A S last (Nat.land (Nat.shiftRight it 2) 511)) ∧
    (∀ Sc ∈ e.2.2, ∀ u, (canonKids Top321.LABT321 Sc).testBit u = true → ∀ A : Spec.Dec22, Canon Top321.O A →
      ¬ Continues Top321.O A S last u) :=
  ext321_sound hF h

end KD321
