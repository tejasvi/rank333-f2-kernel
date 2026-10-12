module
public import R22Port.U_d41d8cd98f00
public import KB.Item321
public import KB.Dead321
public import R22B.Segs
/-! # KB.Agg321: the `Cov` aggregation of cases (I) / (I13) under `--rord 321`

* `CheckedRoot462 lo hi k`: the depth-1 job root 462, a dead node (node cut 7 at depth 1; `KD321.root462_empty`,
  `root462_empty13` by `decide`), as a segment with the key's interface;
* `CheckedAny321 lo hi`: an OPEN-root item, possibly a range item or one with range children (`CheckedR321 lo hi`), the root
  462, or a dead-root item (a piece whose root is killed by a node cut 5 / 6, `KB.Dead321`); **`segRefAny321`**;
* **`segs_of_cov321`**: a `R22N.Cov` derivation over such items gives what `Top.rank_ge_23_L479` consumes for case `(lo, hi)`
  (`hsegI` at `0 12`, `hsegI13` at `13 13`): the glued segments certified under `R3RT.Spec.ClassFacts`, and the covered
  interface as a root;
* per-key statements `CovOfKey321 lo hi k`, `SegsOfKey321 lo hi k` for the module-form aggregators and the stand-in top. -/
@[expose] public section
set_option maxHeartbeats 4000000
noncomputable section
namespace KB
open R3RT.SpecO

/-- the job root 462 (a dead node at depth 1) as a checked item of case `(lo, hi)` -/
def CheckedRoot462 (lo hi : ℕ) (k : ℕ) : Prop :=
  (∀ A : R3RT.Spec.Dec22, CaseK lo hi A → ¬ Below Top321.O A (2 ^ 462) 462) ∧ (R22N.SegI.ofKey k).root = (2 ^ 462, 462) ∧
    (R22N.SegI.ofKey k).lo = 0 ∧ (R22N.SegI.ofKey k).ext = [] ∧ (R22N.SegI.ofKey k).rng = []

theorem segRefRoot462 (H : Prop) (lo hi : ℕ) : SegRefHK H Top321.O (CaseK lo hi) (CheckedRoot462 lo hi) := by
  intro key ⟨hemp, hkr, hlo, hext, hrng⟩
  refine ⟨⟨(R22N.SegI.ofKey key).root, (R22N.SegI.ofKey key).lo, ∅, {(R22N.SegI.ofKey key).root},
    {e | e ∈ (R22N.SegI.ofKey key).ext}, {p | p ∈ (R22N.SegI.ofKey key).rng}⟩, rfl, rfl, rfl, rfl, fun _ => ?_⟩
  refine ⟨Or.inr rfl, fun h0 => by simp [hlo] at h0, fun p hp => by simp [hrng] at hp, fun n hn => ?_,
    fun n hn => absurd hn (Set.notMem_empty n)⟩
  rw [Set.mem_singleton_iff] at hn
  subst hn
  rw [hkr]
  intro A _ hC hB
  exact hemp A hC hB

/-- an item of case `(lo, hi)` under `--rord 321`: an OPEN root, the dead job root 462, or a dead-root item -/
abbrev CheckedAny321 (lo hi : ℕ) (k : ℕ) : Prop := CheckedR321 lo hi k ∨ (CheckedRoot462 lo hi k ∨ CheckedDead321 lo hi k)

theorem segRefAny321 (lo hi : ℕ) : R22B.SegRefH R3RT.Spec.ClassFacts Top321.O (CaseK lo hi) (CheckedAny321 lo hi) := by
  intro k hk
  rcases hk with hk | hk | hk
  · exact segRefR321 lo hi k hk
  · exact segRefRoot462 _ lo hi k hk
  · exact segRefDead321 lo hi k hk

/-- **a `Cov` derivation over items of case `(lo, hi)` gives the glued, certified segment family** -/
theorem segs_of_cov321 (lo hi : ℕ) (x : (ℕ × ℕ) × ℕ) (hx : R22N.Cov (CheckedAny321 lo hi) x) :
    ∃ (ι : Type) (segs : ι → Top.Seg), (R3RT.Spec.ClassFacts → ∀ i, Top.SegOKO Top321.O (CaseK lo hi) (segs i)) ∧
      Top.GlueOK segs ∧ ∃ i, (segs i).root = x.1 ∧ (segs i).lo = x.2 :=
  R22B.segs_of_covH R3RT.Spec.ClassFacts Top321.O (CaseK lo hi) (CheckedAny321 lo hi) (segRefAny321 lo hi) x hx

/-- the module-form aggregators' per-key statement -/
def CovOfKey321 (lo hi : ℕ) (k : ℕ) : Prop :=
  R22N.Cov (CheckedAny321 lo hi) ((R22N.SegI.ofKey k).root, (R22N.SegI.ofKey k).lo)

/-- the stand-in top's per-key statement -/
def SegsOfKey321 (lo hi : ℕ) (k : ℕ) : Prop :=
  ∃ (ι : Type) (segs : ι → Top.Seg), (R3RT.Spec.ClassFacts → ∀ i, Top.SegOKO Top321.O (CaseK lo hi) (segs i)) ∧
    Top.GlueOK segs ∧ ∃ i, (segs i).root = (R22N.SegI.ofKey k).root ∧ (segs i).lo = (R22N.SegI.ofKey k).lo

theorem segsOfKey321_of_cov (lo hi k : ℕ) (h : CovOfKey321 lo hi k) : SegsOfKey321 lo hi k :=
  segs_of_cov321 lo hi _ h

/-- an item without external children or ranges covers its interface -/
theorem covOfKey321_leaf (lo hi k : ℕ) (hk : CheckedAny321 lo hi k) (he : (R22N.SegI.ofKey k).ext = [])
    (hr : (R22N.SegI.ofKey k).rng = []) : CovOfKey321 lo hi k :=
  R22N.Cov.mk k hk (fun e h => by rw [he] at h; cases h) (fun p h => by rw [hr] at h; cases h)

/-- **the roots of case `(lo, hi)` in `R22B.Final`'s form** (`vI` / `vI13`): the three depth-1 job roots covered -/
theorem vI_of (c : ℕ → Prop) (h0 : R22N.Cov c ((2 ^ 0, 0), 0)) (h1 : R22N.Cov c ((2 ^ 168, 168), 0))
    (h2 : R22N.Cov c ((2 ^ 462, 462), 0)) : ∀ l ∈ ([0, 168, 462] : List ℕ), R22N.Cov c ((2 ^ l, l), 0) := by
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl <;> assumption

/-- the dead root 462 of case (I) / (I13) -/
theorem root462_I : ∀ A : R3RT.Spec.Dec22, CaseK 0 12 A → ¬ Below Top321.O A (2 ^ 462) 462 := KD321.root462_empty
theorem root462_I13 : ∀ A : R3RT.Spec.Dec22, CaseK 13 13 A → ¬ Below Top321.O A (2 ^ 462) 462 := KD321.root462_empty13

end KB
#print axioms KB.segs_of_cov321
