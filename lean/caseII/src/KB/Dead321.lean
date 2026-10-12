module
public import R22Port.U_d41d8cd98f00
public import KB.Item321
/-! # KB.Dead321: dead-root items of cases (I) / (I13) under `--rord 321`

A queue run splits off pieces whose root R3 then kills by a node cut 5 / 6 with a certificate (case (I13) has such pieces; case (I)
had none). Such an item has no OPEN record: its only node is the root, and `py/kitem.py` writes the root's parent frame and the cut
as a dead child of that frame (`dead.bin`, the X part of `KB.DPay.xcut`).
* `CheckedDead321 lo hi key`: an accepted job table (`TabV321`), the root's parent frame (`rootChkW` with the 321 tables and the
  witness rows), the root's record a node cut 5 / 6 (`isXcut`) accepted by `dkidOK` with the 321 hyperplane masks and tables, and the
  key's interface (root, `lo = 0`, no ranges, no external children);
* **`segRefDead321 lo hi : SegRefHK ClassFacts Top321.O (CaseK lo hi) (CheckedDead321 lo hi)`**, by the order-generic
  `KB.xcutOK_sound` (the X part kills its child for every decomposition) and `KB.rootChkW_sound`. -/
@[expose] public section
set_option maxHeartbeats 4000000
noncomputable section
namespace KB
open R3RT.SpecO KD

/-- the dead child's payload is a node cut 5 / 6 (`DPay.xcut`) -/
def isXcut (k : DKid) : Bool :=
  DPay.rec (motive := fun _ => Bool) (fun _ _ _ => false) (fun _ _ _ _ _ _ _ => false) (fun _ => false)
    (fun _ _ _ _ _ _ _ _ _ => true) k.2.2.2.2.2.2

/-- **the item predicate of a dead-root item of case `(lo, hi)` under `--rord 321`**: the root is killed by a node cut 5 / 6 on its
parent frame -/
def CheckedDead321 (_lo _hi : ℕ) (key : ℕ) : Prop :=
  ∃ (tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (k : DKid),
    TabV321 tab ∧ rootChkW R22D.T321.CONF1T KI321.c2T KI321.hkT tab pl W lastP f0 = true ∧ isXcut k = true ∧
    dkidOK RT.O321.lpar511 KI321.c2T KI321.hkT KI.cpT tab f0.1 f0.2.1 f0.2.2.1 f0.2.2.2.1 f0.2.2.2.2 lastP k = true ∧
    (R22N.SegI.ofKey key).root = (f0.1 ||| 2 ^ dkLab k, dkLab k) ∧ (R22N.SegI.ofKey key).lo = 0 ∧
    (R22N.SegI.ofKey key).rng = [] ∧ (R22N.SegI.ofKey key).ext = []

/-- **a dead-root item is a certified segment**: its only node is the root, killed by its node cut 5 / 6 -/
theorem segRefDead321 (lo hi : ℕ) : SegRefHK R3RT.Spec.ClassFacts Top321.O (CaseK lo hi) (CheckedDead321 lo hi) := by
  intro key ⟨tab, pl, W, lastP, f0, k, htv, hroot, hx, hdk, hkr, hlo, hrng, hext⟩
  refine ⟨⟨(R22N.SegI.ofKey key).root, (R22N.SegI.ofKey key).lo, ∅, {(R22N.SegI.ofKey key).root},
    {e | e ∈ (R22N.SegI.ofKey key).ext}, {p | p ∈ (R22N.SegI.ofKey key).rng}⟩, rfl, rfl, rfl, rfl, fun hcls => ?_⟩
  have hT : TabOKO Top321.O ΩT tab := tabV321_sound tab htv hcls
  have hF := rootChkW_sound (hc1_321 hcls) (hc2_321 hcls) hh321 hT hroot
  have hS := rootChkW_top hroot
  obtain ⟨c2, h', hdr, r2, r1, r0, pay⟩ := k
  cases pay with
  | xcut x2 x1 nrows aggs XL HP DEFP J kid =>
    unfold dkidOK at hdk
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hdk
    obtain ⟨⟨⟨⟨hlu, hu5⟩, _⟩, _⟩, hkl, hxc⟩ := hdk
    have hdead := xcutOK_sound KD321.npOK321 tab hT (hc2_321 hcls) hcp321 hF hS hxc
    refine ⟨Or.inr rfl, fun h0 => by simp [hlo] at h0, fun p hp => by simp [hrng] at hp, fun n hn => ?_,
      fun n hn => absurd hn (Set.notMem_empty n)⟩
    rw [Set.mem_singleton_iff] at hn
    subst hn
    rw [hkr]
    intro A _ _ hB
    have h1 := hdead A trivial
    rw [hkl] at h1
    exact h1 ⟨hlu, hu5, hB⟩
  | cut _ _ _ => exact absurd hx (by simp [isXcut])
  | flook _ _ _ _ _ _ _ => exact absurd hx (by simp [isXcut])
  | leaf _ => exact absurd hx (by simp [isXcut])

end KB

#print axioms KB.segRefDead321
