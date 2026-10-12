module
public import R22Port.U_d41d8cd98f00
public import KB.DefsR
public import KB.ExtII
/-! # KB.ItemRII: the kernel track's items with range segments in the segment contract

* `segOKO_of_covR`: a covered tree with a lower bound and ranges (`KD.ItemCovR`), the key's interface and every range above the
  bound is a certified segment (`Top.SegOKO`, no dead nodes); a range segment's root is no child of its OPEN nodes because they
  all sit at or above the root's label.
* **`itemR_segRef`** / **`segRefHR`**: `SegRefHK H O C (CheckedR …)`, for any order, universe, extension family and job-table
  predicate with their soundness facts.
* **`segRefRII`**: case (II)'s instance with `extIIR` (`extII_soundII` on the first component). -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
noncomputable section
namespace KB
open R3RT.SpecO KD

/-- **a covered tree with a bound and ranges is a certified segment** -/
theorem segOKO_of_covR {O : LabelOrder} {C : R3RT.Spec.Dec22 → Prop} {key : ℕ} {K : Set (ℕ × ℕ)}
    (hrl : ∀ p ∈ (R22N.SegI.ofKey key).rng, (R22N.SegI.ofKey key).lo < p.2)
    (h : ItemCovR O C (R22N.SegI.ofKey key).root (R22N.SegI.ofKey key).lo K {e | e ∈ (R22N.SegI.ofKey key).ext}
      {p | p ∈ (R22N.SegI.ofKey key).rng}) : Top.SegOKO O C (segK key K) := by
  obtain ⟨hr, hK⟩ := h
  refine ⟨Or.inl hr, fun _ n hn u hu => ?_, fun p hp => ?_, fun n hn => by simp [segK] at hn, fun n hn => ?_⟩
  · -- a child of an OPEN node is never the root: the node's label is at or above the root's
    obtain ⟨-, -, hle, -⟩ := hK n hn
    intro e
    have : u = (R22N.SegI.ofKey key).root.2 := by
      have := congrArg Prod.snd e; simpa [segK] using this
    omega
  · -- every range is above its node's bound in the segment
    have hp' : p ∈ (R22N.SegI.ofKey key).rng := hp
    have := hrl p hp'
    unfold Top.Seg.lb; simp only [segK]; split_ifs <;> omega
  · obtain ⟨htop, hc, -, hcov⟩ := hK n hn
    refine ⟨htop, hc, fun u hu1 hu2 => ?_⟩
    rcases hcov u hu1 hu2 with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **from covered trees with ranges to the contract**: the segment exists unconditionally; its OPEN nodes are chosen under the
facts -/
theorem segRef_of_covR {O : LabelOrder} {C : R3RT.Spec.Dec22 → Prop} (H : Prop) (key : ℕ)
    (hrl : ∀ p ∈ (R22N.SegI.ofKey key).rng, (R22N.SegI.ofKey key).lo < p.2)
    (hK : H → ∃ K, ItemCovR O C (R22N.SegI.ofKey key).root (R22N.SegI.ofKey key).lo K {e | e ∈ (R22N.SegI.ofKey key).ext}
      {p | p ∈ (R22N.SegI.ofKey key).rng}) :
    ∃ g : Top.Seg, g.root = (R22N.SegI.ofKey key).root ∧ g.lo = (R22N.SegI.ofKey key).lo ∧
      g.ext = {e | e ∈ (R22N.SegI.ofKey key).ext} ∧ g.rng = {p | p ∈ (R22N.SegI.ofKey key).rng} ∧
      (H → Top.SegOKO O C g) := by
  by_cases hH : H
  · obtain ⟨K, hc⟩ := hK hH
    exact ⟨segK key K, rfl, rfl, rfl, rfl, fun _ => segOKO_of_covR hrl hc⟩
  · exact ⟨segK key ∅, rfl, rfl, rfl, rfl, fun h => absurd h hH⟩

/-- **an accepted item with ranges gives the contract's segment** -/
theorem itemR_segRef {E : Type} {O : LabelOrder} {Ω C : R3RT.Spec.Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk rg : E → ℕ}
    (H : Prop) (hnp : NpOK O np) (hh : ∀ l, l < 511 → HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (c1 : ℕ) (hc1 : H → Conf1OK O Ω c1) (hc2 : H → ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hExt : H → ExtSound O Ω C ext acc) (key : ℕ) (tab : ℕ → ℕ) (hT : H → TabOKO O Ω tab)
    (pl W : List ℕ) (lastP : ℕ) (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (hroot : rootChk0 c1 c2T hkT tab pl W lastP f0 = true)
    (l0 pend0 lo : ℕ) (hp0 : Nat.beq pend0 (Nat.shiftLeft 1 l0) = true) (extL : List (ℕ × ℕ)) (rngL : List ((ℕ × ℕ) × ℕ))
    (out : List FrP) (hch : ChainR np c2T hkT cpT extL lo rngL ext acc xk rg tab [(f0, pend0)] out)
    (hfin : pendZ out = true) (hrl : allB (fun p => Nat.blt lo p.2) rngL = true)
    (hkr : (R22N.SegI.ofKey key).root = (f0.1 ||| 2 ^ l0, l0)) (hlo : (R22N.SegI.ofKey key).lo = lo)
    (hrng : (R22N.SegI.ofKey key).rng = rngL) (hext : (R22N.SegI.ofKey key).ext = extL) :
    ∃ g : Top.Seg, g.root = (R22N.SegI.ofKey key).root ∧ g.lo = (R22N.SegI.ofKey key).lo ∧
      g.ext = {e | e ∈ (R22N.SegI.ofKey key).ext} ∧ g.rng = {p | p ∈ (R22N.SegI.ofKey key).rng} ∧
      (H → Top.SegOKO O C g) := by
  have hpend : pend0 = 2 ^ l0 := by
    rw [Nat.beq_eq, L5.shl_eq, Nat.shiftLeft_eq, one_mul] at hp0; exact hp0
  subst hpend
  refine segRef_of_covR H key (fun p hp => ?_) (fun hH => ?_)
  · rw [hrng] at hp; rw [hlo]
    have := allB_spec hrl p hp
    simpa [Nat.blt_eq] using this
  · rw [hkr, hlo, hext, hrng]
    exact itemR_cov (Fr := fun f => KD321.FrameOK0 O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2) hnp
      (KD321.n5contract0 O Ω) (fun S D N U d hF => KD321.frameOK0_of S D N U d hF) tab (hT hH) (hc2 hH) hh hcp hCΩ
      (hExt hH) f0 (rootChk0_sound (hc1 hH) (hc2 hH) hh (hT hH) hroot) l0 out hch hfin

/-- **the kernel track's checker contract with ranges**: `R22B.SegRefH H O C (CheckedR …)` -/
theorem segRefHR {E : Type} {O : LabelOrder} {Ω C : R3RT.Spec.Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {ext : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk rg : E → ℕ}
    (H : Prop) (hnp : NpOK O np) (hh : ∀ l, l < 511 → HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (c1 : ℕ) (hc1 : H → Conf1OK O Ω c1) (hc2 : H → ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hExt : H → ∀ tab, TabOKO O Ω tab → ExtSound O Ω C (ext tab) acc) (TabV : (ℕ → ℕ) → Prop)
    (hTV : ∀ tab, TabV tab → H → TabOKO O Ω tab) :
    SegRefHK H O C (CheckedR np c2T hkT cpT ext acc xk rg c1 TabV) := by
  intro key ⟨tab, pl, W, lastP, f0, l0, pend0, lo, extL, rngL, out, htv, hroot, hp0, hch, hfin, hrl, hkr, hlo, hrng, hext⟩
  exact itemR_segRef H hnp hh hcp hCΩ c1 hc1 hc2 (fun hH => hExt hH tab (hTV tab htv hH)) key tab (hTV tab htv) pl W lastP
    f0 hroot l0 pend0 lo hp0 extL rngL out hch hfin hrl hkr hlo hrng hext

/-- the case-(II) extension with range starts is sound (`extII_soundII` on the datum's first component) -/
theorem extIIR_soundII {np c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} (tab : ℕ → ℕ) (hnp : NpOK LO123 np)
    (hT : TabOKU (CaseK 14 22) tab) (hc2 : ∀ l, l < 511 → C2OKU (CaseK 14 22) l (c2T l))
    (hh : ∀ l, l < 511 → HOK LO123 l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (hTF : TypeFacts) :
    ExtSound LO123 (CaseK 14 22) (CaseK 14 22) (extIIR np c2T hkT cpT tab) accIIR :=
  fun S' D' N' U' d' last e hF hS hl hd h u hu1 hu2 ha =>
    extII_soundII tab hnp hT hc2 hh hcp hTF S' D' N' U' d' last e.1 hF hS hl hd h u hu1 hu2 ha

/-- **case (II)'s contract for items with ranges** -/
theorem segRefRII {c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {c1 : ℕ} (hh : ∀ l, l < 511 → HOK LO123 l (hkT l))
    (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (hc1 : HII → Conf1OK LO123 (CaseK 14 22) c1)
    (hc2 : HII → ∀ l, l < 511 → C2OKU (CaseK 14 22) l (c2T l)) :
    SegRefHK HII LO123 (CaseK 14 22)
      (CheckedR R3RT.nperpL c2T hkT cpT (fun tab => extIIR R3RT.nperpL c2T hkT cpT tab) accIIR xkIIR rgIIR c1 TabVII) :=
  segRefHR HII npOK_123 hh hcp (fun _ h => h) c1 hc1 hc2
    (fun hH tab hT => extIIR_soundII tab npOK_123 hT (hc2 hH) hh hcp hH.2) TabVII (fun tab h hH => tabVII_sound tab h hH.1)

end KB
