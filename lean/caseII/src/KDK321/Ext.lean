module
public import R22Port.U_d41d8cd98f00
public import KD321.Canon
public import KD321.Leaf
public import KDK321.Flook
public import KDK321.Root
/-! # KDK321.Ext (kinds-only name of KD321.Ext): the kinds extras of one node over a label order, as one hook

* **OPEN node** (`extO`, on the child frame `(S', D', N', U', d')` that `node5` passes to its continuation, top label `last`):
  datum `e = (b, its, cs)`: the suffix break label `b`, the PREFF / DOOM records `its` (`tag | u << 2 | X << 11`, tag 0 PREFF
  with functional `X`, tag 1 DOOM) and the L3 node records `cs` (one `C3T` node record at field 0 of each `Sc`, witnesses of
  the node's CANON children).  **`extO_sound`**: children `≥ b` are dead for `Ω`; each record's child is dead for
  `Ω ∩ CaseK lo hi`; each child in `canonKids LT Sc` is dead for canonical decompositions.
* **Node without child loop** (cut node or leaf, on the frame `frame5` computes), datum `(kind, payload)`:
  `cut7O` (node cut 7, the rank-1 window), `flookRecO` (leaf code 4 at `d = 22`), `leafBindO` (leaf code 0 with its v7
  record).  `cut7O_sound`, `KD321.flookRecO_sound`, `KD321.leaf_node_deadO`.
The `--rord 321` instance: `vf = RT.O321.vecL`, `npf = RT.O321.lpar511`, `r1m = R1M321`, `nr1m = NR1M321`,
`LT = Top321.LABT321`, `lf = lf321`; `(lo, hi) = (0, 12)` for case (I), `(13, 13)` for case (I13). -/
@[expose] public section
set_option exponentiation.threshold 1024
noncomputable section
namespace KD321
open RootSound R3RT R3RT.SpecO BC4 BC5 Finset Classical

/-- all L3 node records of a node, bound to its prefix `S` and checked -/
def canonAllT (LT S : ℕ) (cs : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun Sc _ acc => canonNode LT Sc S && acc) cs

theorem canonAllT_mem {LT S : ℕ} : ∀ (cs : List ℕ), canonAllT LT S cs = true → ∀ Sc ∈ cs, canonNode LT Sc S = true
  | [], _, Sc, h => absurd h List.not_mem_nil
  | x :: xs, h, Sc, hm => by
    have h' : (canonNode LT x S && canonAllT LT S xs) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact h'.1
    · exact canonAllT_mem xs h'.2 Sc hm'

/-- **the extras of an OPEN node** (datum `(b, its, cs)`) -/
def extO (vf npf : ℕ → ℕ) (r1m nr1m lo hi LT : ℕ) (S D U d last : ℕ) (e : ℕ × List ℕ × List ℕ) : Bool :=
  kindsNodeO vf npf r1m nr1m lo hi S D U d last e.1 e.2.1 && canonAllT LT S e.2.2

theorem extO_sound {O : LabelOrder} {vf npf : ℕ → ℕ} {r1m nr1m LT : ℕ} (hV : VecOK O vf npf) (hR : R1OK O r1m nr1m)
    (hL : LabO O LT) {Ω : Spec.Dec22 → Prop} {lo hi S D N U d last : ℕ} {e : ℕ × List ℕ × List ℕ}
    (hF : FrameOK O Ω S D N U d) (h : extO vf npf r1m nr1m lo hi LT S D U d last e = true) :
    (∀ u, e.1 ≤ u → ∀ A : Spec.Dec22, Ω A → ¬ Continues O A S last u) ∧
    (∀ it ∈ e.2.1, ∀ A : Spec.Dec22, Ω A → CaseK lo hi A → ¬ Continues O A S last (Nat.land (Nat.shiftRight it 2) 511)) ∧
    (∀ Sc ∈ e.2.2, ∀ u, (canonKids LT Sc).testBit u = true → ∀ A : Spec.Dec22, Canon O A → ¬ Continues O A S last u) := by
  unfold extO at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hk, hc⟩ := h
  obtain ⟨h1, h2⟩ := kindsNodeO_sound hV hR hF hk
  have hS : S >>> last = 1 := by
    unfold kindsNodeO at hk; simp only [Bool.and_eq_true] at hk; exact KD.beq_true hk.1.1.1
  exact ⟨h1, h2, fun Sc hSc => canonNode_sound hL hS hF.2.1 (canonAllT_mem _ hc Sc hSc)⟩

/-- node cut 7 on the cut node's own frame -/
def cut7O (r1m nr1m lo hi S D d last : ℕ) : Bool :=
  Nat.beq (Nat.shiftRight S last) 1 && Nat.ble d 22 && winOKO r1m nr1m S D d last lo hi

theorem cut7O_sound {O : LabelOrder} {r1m nr1m : ℕ} (hR : R1OK O r1m nr1m) {Ω : Spec.Dec22 → Prop}
    {lo hi S D N U d last : ℕ} (hF : FrameOK O Ω S D N U d) (h : cut7O r1m nr1m lo hi S D d last = true) :
    ∀ A : Spec.Dec22, Ω A → CaseK lo hi A → ¬ Below O A S last := by
  unfold cut7O at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hS, hd⟩, hw⟩ := h
  exact winO_sound hR hF (KD.beq_true hS) hd hw

/-! ## The `--rord 321` instance -/

/-- the extras of an OPEN node of case `(lo, hi)` under `--rord 321` -/
abbrev ext321 (lo hi S D U d last : ℕ) (e : ℕ × List ℕ × List ℕ) : Bool :=
  extO RT.O321.vecL RT.O321.lpar511 R1M321 NR1M321 lo hi Top321.LABT321 S D U d last e

theorem ext321_sound {Ω : Spec.Dec22 → Prop} {lo hi S D N U d last : ℕ} {e : ℕ × List ℕ × List ℕ}
    (hF : FrameOK Top321.O Ω S D N U d) (h : ext321 lo hi S D U d last e = true) :
    (∀ u, e.1 ≤ u → ∀ A : Spec.Dec22, Ω A → ¬ Continues Top321.O A S last u) ∧
    (∀ it ∈ e.2.1, ∀ A : Spec.Dec22, Ω A → CaseK lo hi A →
      ¬ Continues Top321.O A S last (Nat.land (Nat.shiftRight it 2) 511)) ∧
    (∀ Sc ∈ e.2.2, ∀ u, (canonKids Top321.LABT321 Sc).testBit u = true → ∀ A : Spec.Dec22, Canon Top321.O A →
      ¬ Continues Top321.O A S last u) :=
  extO_sound vecOK321 r1OK321 labO321 hF h

end KD321
