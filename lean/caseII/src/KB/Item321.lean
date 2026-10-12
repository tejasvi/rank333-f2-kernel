module
public import R22Port.U_d41d8cd98f00
public import KB.Defs321
public import KB.ExtII
public import KB.ItemRII
public import KDK321.Batch321
public import KB.Flook321
public import L5.T321H
public import NNP.Bind321
/-! # KB.Item321: the kernel track's checker contract for cases (I) / (I13) under `--rord 321`

* **`dkid321OK_sound`**: an accepted dead child (node cut 7, node cut 3 / leaf code 4, leaf code 0) of a node with a valid frame is
  empty for `Ω ∩ CaseK lo hi` (look-ahead and leaves: nonzero `b`, `c`);
* **`ext321K_sound`**: `KD.ExtSound Top321.O Ω (CaseK lo hi) (ext321K lo hi c2T hkT tab) acc321`;
* the static facts at `Top321.O` over the trivial universe `ΩT`: the label tables (`hc2_321` from the port's bindings
  `NNB.b321` through `L5O.bindQ_spec321`; `hh321` = the hit vectors `L5O.hitV`), the cap-1 table (`hc1_321`), the job table
  (`tabV321_sound` through `L5O.table_spec321`), all under revision 5's `R3RT.Spec.ClassFacts`;
* **`segRef321 lo hi : SegRefHK ClassFacts Top321.O (CaseK lo hi) (CheckedK321 lo hi)`**: what `Top.rank_ge_23_L479`'s `hsegI`
  (`lo hi = 0 12`) and `hsegI13` (`13 13`) take per item. -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section
namespace KB
open R3RT.SpecO KD

/-- **a dead child at `--rord 321` is dead** -/
theorem dkid321OK_sound {Ω : R3RT.Spec.Dec22 → Prop} {lo hi : ℕ} {c2T hkT tab : ℕ → ℕ}
    (hT : TabOKO Top321.O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO Top321.O Ω l (c2T l))
    (hh : ∀ l, l < 511 → HOK Top321.O l (hkT l))
    {S D N U d last : ℕ} (hF : FrameOKO Top321.O Ω S D N U d) (k : DKid321)
    (h : dkid321OK lo hi c2T hkT tab S D N U d last k = true) :
    last < dk321Lab k ∧ dk321Lab k < 511 ∧ ∀ A : R3RT.Spec.Dec22, Ω A → CaseK lo hi A → (∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) →
      ¬ Below Top321.O A (S ||| 2 ^ dk321Lab k) (dk321Lab k) := by
  obtain ⟨c2, h', hdr, r2, r1, r0, pay⟩ := k
  unfold dkid321OK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hlu, hu5⟩, hc2e⟩, hhe⟩, hw⟩ := h
  obtain ⟨rec, hrec, hlr, hk⟩ := withRec_sound tab hT hdr r2 r1 r0 _ hw
  have hlab : dk321Lab (c2, h', hdr, r2, r1, r0, pay) = (rec >>> 8) % 512 := by
    show Nat.land (Nat.shiftRight hdr 8) 511 = _; rw [land511, L5.shr_eq, hlr]
  rw [hlab] at hlu hu5 hc2e hhe ⊢
  have hc2' : C2OKO Top321.O Ω ((rec >>> 8) % 512) c2 := by rw [hc2e]; exact hc2 _ hu5
  have hh' : HOK Top321.O ((rec >>> 8) % 512) h' := by rw [hhe]; exact hh _ hu5
  refine ⟨hlu, hu5, fun A hΩ hC hnz => ?_⟩
  cases pay with
  | cut7 =>
    have hk5 : R3RT.frame5 S D N U d c2 h' rec (fun S' D' _ _ =>
        KD321.cut7O KD321.R1M321 KD321.NR1M321 lo hi S' D' (Nat.succ d) (Nat.land (Nat.shiftRight rec 8) 511)) = true := hk
    obtain ⟨D', hF', hk'⟩ := (L5O.frame5_spec : Frame5Spec Top321.O Ω) S D N U d c2 h' rec _ hF hc2' hh' hrec hk5
    rw [last_eq] at hk'
    exact KD321.cut7O_sound KD321.r1OK321 hF' hk' A hΩ hC
  | flook t nT h2 TL TY SL SY =>
    have hk5 : R3RT.frame5 S D N U d c2 h' rec (fun S' D' _ U' =>
        KD321.flookOKO RT.O321.vecL RT.O321.lpar511 S' D' U' (Nat.succ d) (Nat.land (Nat.shiftRight rec 8) 511) t nT h2 TL TY SL SY)
        = true := hk
    obtain ⟨D', hF', hk'⟩ := (L5O.frame5_spec : Frame5Spec Top321.O Ω) S D N U d c2 h' rec _ hF hc2' hh' hrec hk5
    rw [last_eq] at hk'
    exact KD321.flookOKO_sound_nz KD321.vecOK321 hF' hk' A hΩ hnz
  | leaf R =>
    have hk2 : (BC7s.leafS R && R3RT.frame5 S D N U d c2 h' rec (fun S' _ _ _ =>
        Nat.beq (Nat.succ d) 22 && KD321.leafBindO KD321.lf321 R S')) = true := hk
    rw [Bool.and_eq_true] at hk2
    obtain ⟨hR, hk5⟩ := hk2
    have htop := top_of_frame5 hk5
    obtain ⟨D', hF', hk'⟩ := (L5O.frame5_spec : Frame5Spec Top321.O Ω) S D N U d c2 h' rec _ hF hc2' hh' hrec hk5
    rw [Bool.and_eq_true] at hk'
    obtain ⟨hd, hb⟩ := hk'
    replace hd := Nat.eq_of_beq_eq_true hd
    obtain ⟨_, hS511, hcard, _⟩ := frameOKO_basic hF'
    rw [show d + 1 = 22 from hd] at hcard
    exact KD321.leaf_node_deadO KD321.lfOK321 hR hb htop hS511 hcard A hnz

theorem canonM321_testBit {u : ℕ} : ∀ (cs : List ℕ), (canonM321 cs).testBit u = true →
    ∃ Sc ∈ cs, (KD321.canonKids Top321.LABT321 Sc).testBit u = true
  | [], h => by simp [canonM321] at h
  | Sc :: t, h => by
    change (Nat.lor (KD321.canonKids Top321.LABT321 Sc) (canonM321 t)).testBit u = true at h
    rw [L5.lor_eq, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨Sc, List.mem_cons_self .., h⟩
    · obtain ⟨Sc', hm, h'⟩ := canonM321_testBit t h
      exact ⟨Sc', List.mem_cons_of_mem _ hm, h'⟩

/-- **the 321 extension is sound** (`KD.ExtSound`) -/
theorem ext321K_sound {Ω : R3RT.Spec.Dec22 → Prop} {lo hi : ℕ} {c2T hkT : ℕ → ℕ} (tab : ℕ → ℕ)
    (hT : TabOKO Top321.O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO Top321.O Ω l (c2T l))
    (hh : ∀ l, l < 511 → HOK Top321.O l (hkT l)) (hCΩ : ∀ A, CaseK lo hi A → Ω A)
    (hnz : ∀ A : R3RT.Spec.Dec22, ∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) :
    ExtSound Top321.O Ω (CaseK lo hi) (ext321K lo hi c2T hkT tab) acc321 := by
  intro S D N U d last e hF hS hl511 hd h u hu1 hu2 hacc
  obtain ⟨b, its, cs, dks, xm⟩ := e
  unfold ext321K at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hx, hdk⟩ := h
  obtain ⟨hsuf, hits, hcan⟩ := KD321.ext321_sound hF hx
  unfold acc321 at hacc
  simp only [L5.lor_eq, Nat.testBit_or, Bool.or_eq_true] at hacc
  rcases hacc with (hb | hi) | (hc | hk)
  · -- the suffix break
    rw [testBit_geM, decide_eq_true_eq] at hb
    exact fun A _ hC => hsuf u hb.1 A (hCΩ A hC)
  · -- PREFF / DOOM
    obtain ⟨it, hit, hiu⟩ := (maskL_testBit _ u its).mp hi
    intro A _ hC
    have := hits it hit A (hCΩ A hC) hC
    rwa [hiu] at this
  · -- CANON
    obtain ⟨Sc, hSc, hk⟩ := canonM321_testBit cs hc
    intro A hcn _
    exact hcan Sc hSc u hk A hcn
  · -- dead children
    obtain ⟨k, hkm, hku⟩ := (maskL_testBit _ u dks).mp hk
    obtain ⟨_, _, hdead⟩ := dkid321OK_sound hT hc2 hh hF k (allB_spec hdk k hkm)
    intro A _ hC hcont
    rw [← hku] at hcont
    exact hdead A (hCΩ A hC) hC (hnz A) hcont.2.2

/-! ## The static facts at `Top321.O` -/

/-- the dispatcher's cap-2 tables are the port's (`R22D.T321.c2tN`) -/
theorem c2T321_all : S5.allLT 511 (fun l => Nat.beq (KI321.c2T l) (R22D.T321.c2tN.getD l 0)) = true := by decide +kernel
/-- the dispatcher's hit vectors are `L5O.hitV` of the 321 codes -/
theorem hkT321_all : S5.allLT 511 (fun l => Nat.beq (KI321.hkT l) (L5O.hitV (RT.O321.vecL l))) = true := by decide +kernel
theorem cp321_all : S5.allLT 511 (fun u => KD.constBeq (510 - u) (KI.cpT u)) = true := by decide +kernel

theorem hcp321 : ∀ u, u < 511 → KD.CPn (510 - u) (KI.cpT u) := fun u hu =>
  KD.cpn_of_beq (by omega) (S5.allLT_spec cp321_all u hu)

theorem hh321 (l : ℕ) (hl : l < 511) : HOK Top321.O l (KI321.hkT l) :=
  L5O.hok_of Top321.O l _ (Nat.eq_of_beq_eq_true (S5.allLT_spec hkT321_all l hl))

theorem hc2_321 (hcls : R3RT.Spec.ClassFacts) (l : ℕ) (hl : l < 511) : C2OKO Top321.O ΩT l (KI321.c2T l) := by
  rw [Nat.eq_of_beq_eq_true (S5.allLT_spec c2T321_all l hl)]
  obtain ⟨rows, hb⟩ := NNB.b321 l hl
  exact (L5O.bindQ_spec321 Top321.labK321 l rows _ _ (classFactsC_true.mpr hcls)).1 hl hb

theorem hc1_321 (hcls : R3RT.Spec.ClassFacts) : Conf1OK Top321.O ΩT R22D.T321.CONF1T := by
  obtain ⟨rows, hb⟩ := NNB.b321_c1
  exact (L5O.bindQ_spec321 Top321.labK321 511 rows _ _ (classFactsC_true.mpr hcls)).2 hb

theorem tabV321_sound (tab : ℕ → ℕ) (h : TabV321 tab) (hcls : R3RT.Spec.ClassFacts) : TabOKO Top321.O ΩT tab := by
  obtain ⟨chunk, N, nch, hent, hch, hN, hok⟩ := h
  exact L5O.table_spec321 Top321.labK321 chunk tab N nch hent hch hN (classFactsC_true.mpr hcls) hok

/-! ## The contract -/

/-- **the kernel track's checker contract for case `(lo, hi)` under `--rord 321`** -/
theorem segRef321 (lo hi : ℕ) : SegRefHK R3RT.Spec.ClassFacts Top321.O (CaseK lo hi) (CheckedK321 lo hi) :=
  segRefHK_K (Ω := ΩT) R3RT.Spec.ClassFacts KD321.npOK321 hh321 hcp321 (fun _ _ => trivial) R22D.T321.CONF1T hc1_321
    (fun hcls l hl => hc2_321 hcls l hl)
    (fun hcls tab hT => ext321K_sound tab hT (hc2_321 hcls) hh321 (fun _ _ => trivial) (Top.dec22_bc HC.rr_all))
    TabV321 (fun tab h hcls => tabV321_sound tab h hcls)

/-- the 321 extension with range starts is sound (`ext321K_sound` on the datum's first component) -/
theorem ext321KR_sound {Ω : R3RT.Spec.Dec22 → Prop} {lo hi : ℕ} {c2T hkT : ℕ → ℕ} (tab : ℕ → ℕ)
    (hT : TabOKO Top321.O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO Top321.O Ω l (c2T l))
    (hh : ∀ l, l < 511 → HOK Top321.O l (hkT l)) (hCΩ : ∀ A, CaseK lo hi A → Ω A)
    (hnz : ∀ A : R3RT.Spec.Dec22, ∀ s, A.b s ≠ 0 ∧ A.c s ≠ 0) :
    ExtSound Top321.O Ω (CaseK lo hi) (ext321KR lo hi c2T hkT tab) acc321R :=
  fun S' D' N' U' d' last e hF hS hl hd h u hu1 hu2 ha =>
    ext321K_sound tab hT hc2 hh hCΩ hnz S' D' N' U' d' last e.1 hF hS hl hd h u hu1 hu2 ha

/-- **the kernel track's checker contract for case `(lo, hi)` under `--rord 321`, with ranges** -/
theorem segRefR321 (lo hi : ℕ) : SegRefHK R3RT.Spec.ClassFacts Top321.O (CaseK lo hi) (CheckedR321 lo hi) :=
  segRefHR (Ω := ΩT) R3RT.Spec.ClassFacts KD321.npOK321 hh321 hcp321 (fun _ _ => trivial) R22D.T321.CONF1T hc1_321
    (fun hcls l hl => hc2_321 hcls l hl)
    (fun hcls tab hT => ext321KR_sound tab hT (hc2_321 hcls) hh321 (fun _ _ => trivial) (Top.dec22_bc HC.rr_all))
    TabV321 (fun tab h hcls => tabV321_sound tab h hcls)

end KB
#print axioms KB.segRef321
#print axioms KB.segRefR321
