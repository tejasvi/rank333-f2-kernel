module
public import R22Port.U_d41d8cd98f00
public import KDK.ItemK
/-! # KDK.ItemR (kinds-only name of KD.ItemR): items with range segments (kind 3) and range references (RG)

`itemXR'` is `KD.itemXS'` with two more ways for a node's child to be accounted for, the two of `Top.SegOKO` with `lo` and `rng`:
* **the root's lower bound `lo`**: the item root's own frame does not hold the labels below `lo` (a range segment accounts only for
  its root's children `≥ lo`). The root is the record whose parent frame is the stack's last one (the root's parent frame, with
  only the root's label pending), so `lowOf st' lo` excuses those labels there and nowhere else;
* **a range reference** `rg e < 511` on a record: its node's children `≥ rg e` belong to the range segment `((S', last), rg e)`,
  which must be in the item's range list `rngL` (`rngMem`); `rg e = 511` is none.

**`itemXR'_sound`** keeps `InvR`: `InvP`'s coverage with the two new cases, every recorded node at or above the root's label, every
pending label at or above it, and the stack's last frame the root's parent with at most the root's label pending.
**`itemR_cov`**: a chain of batches (`ChainR`) from `[(f0, 2^l0)]` to a stack without pending labels gives `ItemCovR`. -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
noncomputable section
namespace KD
open R3RT.Spec RootSound BC4 BC5 Classical
open R3RT (M511 foldR node5 mapL mkD)

/-! ## The checker -/

/-- the labels `l .. 510` (none for `l ≥ 511`) -/
def geL (l : ℕ) : ℕ := Nat.sub (Nat.shiftLeft 1 511) (Nat.shiftLeft 1 l)

/-- the labels below `lo` -/
def ltL (lo : ℕ) : ℕ := Nat.sub (Nat.shiftLeft 1 lo) 1

/-- the root's excused children: the labels below `lo` when the frame below the record is the stack's last one -/
def lowOf (st' : List FrP) (lo : ℕ) : ℕ := List.rec (motive := fun _ => ℕ) (ltL lo) (fun _ _ _ => 0) st'

/-- `((S', last), l)` is an entry of the range list -/
def rngMem (rngL : List ((ℕ × ℕ) × ℕ)) (S' last l : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ acc => (Nat.beq p.1.1 S' && Nat.beq p.1.2 last && Nat.beq p.2 l) || acc) rngL

/-- a new node's pending children: `pendOf` without the root's excused labels and the labels handed to a range -/
def pendR (last : ℕ) (ks : List ℕ) (kids : List KidX) (acc xk D' low rgl : ℕ) : ℕ :=
  K2.andn (K2.andn (pendOf last ks kids acc xk D') low) (geL rgl)

/-- **one batch of an item with ranges** from the stack `st` to the stack `out` -/
def itemXR' {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (extL : List (ℕ × ℕ))
    (lo : ℕ) (rngL : List ((ℕ × ℕ) × ℕ))
    (ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk rg : E → ℕ) (tab : ℕ → ℕ) :
    List FrP → List (NodeX × E) → List FrP → Bool
  | st, [], out => stEq st out
  | st, (x, e) :: rest, out =>
    match List.drop (Nat.land x.2.2.2.1 255) st with
    | [] => false
    | ((S, D, N, U, dP), pend) :: st' =>
      pendZ (List.take (Nat.land x.2.2.2.1 255) st) &&
      Nat.beq (bitAt pend (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) 1 && Nat.ble (Nat.succ dP) 21 &&
      statX c2T hkT cpT x &&
      nodeXO np tab S D N U dP x (fun S' D' N' U' =>
        ext S' D' N' U' (Nat.succ dP) (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) e &&
        (Nat.beq (xk e) 0 || Nat.beq (xkRest extL S' (xk e)) 0) &&
        (Nat.beq (rg e) 511 || rngMem rngL S' (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) (rg e)) &&
        itemXR' np c2T hkT cpT extL lo rngL ext acc xk rg tab
          (((S', D', N', U', Nat.succ dP),
              pendR (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) (nodeKs x) (nodeKids x) (acc e) (xk e) D' (lowOf st' lo) (rg e)) ::
            ((S, D, N, U, dP), clrBit pend (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) :: st') rest out)

/-! ## Bits -/

theorem geL_testBit {l u : ℕ} (h : (geL l).testBit u = true) : l ≤ u ∧ u < 511 := by
  unfold geL at h
  rw [L5.nsub_eq, L5.shl_eq, L5.shl_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul] at h
  rcases Nat.lt_or_ge 511 l with hl | hl
  · rw [Nat.sub_eq_zero_of_le (Nat.pow_le_pow_right (by norm_num) hl.le)] at h; simp at h
  · rw [L5.testBit_pow_sub_pow 511 l u hl] at h
    simpa using h

theorem ltL_testBit {lo u : ℕ} (h : (ltL lo).testBit u = true) : u < lo := by
  unfold ltL at h
  rw [L5.nsub_eq, L5.shl_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one] at h
  simpa using h

theorem lowOf_testBit {st' : List FrP} {lo u : ℕ} (h : (lowOf st' lo).testBit u = true) : st' = [] ∧ u < lo := by
  cases st' with
  | nil => exact ⟨rfl, ltL_testBit h⟩
  | cons a t => change (0 : ℕ).testBit u = true at h; simp at h

theorem rngMem_spec : ∀ {rngL : List ((ℕ × ℕ) × ℕ)} {S' last l : ℕ}, rngMem rngL S' last l = true → ((S', last), l) ∈ rngL
  | [], _, _, _, h => by cases h
  | p :: t, S', last, l, h => by
    change ((Nat.beq p.1.1 S' && Nat.beq p.1.2 last && Nat.beq p.2 l) || rngMem t S' last l) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨⟨p1, p2⟩, p3⟩ := p
      simp only at h1 h2 h3; subst h1 h2 h3; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (rngMem_spec h)

theorem pendR_testBit (last : ℕ) (ks : List ℕ) (kids : List KidX) (a x D' low rgl u : ℕ) :
    (pendR last ks kids a x D' low rgl).testBit u =
      ((pendOf last ks kids a x D').testBit u && !low.testBit u && !(geL rgl).testBit u) := by
  unfold pendR; simp only [K2.testBit_andn]

theorem getLast?_of_drop {st : List FrP} {k : ℕ} {a : FrP} (h : st.drop k = [a]) : st.getLast? = some a := by
  rw [← List.take_append_drop k st, h, List.getLast?_append]; simp

theorem getLast?_of_drop_cons {st : List FrP} {k : ℕ} {a b : FrP} {t : List FrP} (h : st.drop k = a :: b :: t) :
    st.getLast? = (b :: t).getLast? := by
  rw [← List.take_append_drop k st, h, List.getLast?_append, List.getLast?_cons_cons]
  cases hb : (b :: t).getLast? with
  | none => simp at hb
  | some c => simp

/-! ## The invariant -/

/-- the invariant of an item's stack with ranges (`InvP` plus the root's lower bound `lo` and the ranges `R`) -/
structure InvR (O : R3RT.SpecO.LabelOrder) (C : Dec22 → Prop) (Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop) (K X : Set (ℕ × ℕ))
    (R : Set ((ℕ × ℕ) × ℕ)) (P l0 lo : ℕ) (st : List FrP) : Prop where
  fr : ∀ f ∈ st, Fr f.1
  cov : ∀ n ∈ K, n.1 >>> n.2 = 1 ∧ pcnt511 n.1 ≤ 21 ∧ l0 ≤ n.2 ∧ ∀ u, n.2 < u → u < 511 →
    R3RT.SpecO.ChildDead O C n.1 n.2 u ∨ (n.1 ||| 2 ^ u, u) ∈ X ∨ (n.1 ||| 2 ^ u, u) ∈ K ∨
      (n = (P ||| 2 ^ l0, l0) ∧ u < lo) ∨ (∃ l, (n, l) ∈ R ∧ l ≤ u) ∨
      ∃ f ∈ st, f.1.1 = n.1 ∧ f.2.testBit u = true
  root : (P ||| 2 ^ l0, l0) ∈ K ∨ ∃ f ∈ st, f.1.1 = P ∧ f.2.testBit l0 = true
  pl0 : ∀ f ∈ st, ∀ u, f.2.testBit u = true → l0 ≤ u
  bot : ∃ fb pb, st.getLast? = some (fb, pb) ∧ fb.1 = P ∧ ∀ u, pb.testBit u = true → u = l0

/-! ## One batch -/

/-- **Soundness of one batch of an item with ranges.** -/
theorem itemXR'_sound {E : Type} {O : R3RT.SpecO.LabelOrder} {Ω C : Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {extL : List (ℕ × ℕ)} {lo : ℕ} {rngL : List ((ℕ × ℕ) × ℕ)}
    {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk rg : E → ℕ}
    {Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop} {P l0 : ℕ}
    (hnp : NpOK O np) (hN5 : N5Contract O Ω Fr) (hFr : ∀ S D N U d, FrameOKO O Ω S D N U d → Fr (S, D, N, U, d))
    (tab : ℕ → ℕ) (hT : TabOKO O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (hExt : ExtSound O Ω C ext acc) :
    ∀ (nodes : List (NodeX × E)) (st out : List FrP) (K : Set (ℕ × ℕ)),
      InvR O C Fr K {e | e ∈ extL} {p | p ∈ rngL} P l0 lo st →
      itemXR' np c2T hkT cpT extL lo rngL ext acc xk rg tab st nodes out = true →
      ∃ K', InvR O C Fr K' {e | e ∈ extL} {p | p ∈ rngL} P l0 lo out := by
  intro nodes
  induction nodes with
  | nil =>
    intro st out K hI hb
    simp only [itemXR'] at hb
    rw [← stEq_spec hb]; exact ⟨K, hI⟩
  | cons xe rest ih =>
    intro st out K hI hb
    obtain ⟨x, e⟩ := xe
    obtain ⟨c2, h, suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x
    simp only [itemXR'] at hb
    rw [land255, hdr_last] at hb
    rcases hd : List.drop (hdr % 256) st with _ | ⟨⟨⟨S, D, N, U, dP⟩, pend⟩, st'⟩
    · rw [hd] at hb; exact absurd hb (by simp)
    · rw [hd] at hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨⟨⟨hz, hbit⟩, hdep⟩, hstat⟩, hnode⟩ := hb
      have hmemd : ∀ f, f ∈ List.drop (hdr % 256) st → f ∈ st := fun f hf => List.mem_of_mem_drop hf
      have hf0 : ((S, D, N, U, dP), pend) ∈ st := hmemd _ (by rw [hd]; exact List.mem_cons_self ..)
      have hF : Fr (S, D, N, U, dP) := hI.fr _ hf0
      have hpl : pend.testBit ((hdr >>> 8) % 512) = true := by
        rw [Nat.beq_eq, bitAt_eq] at hbit
        by_contra hq
        rw [if_neg hq] at hbit; exact absurd hbit (by decide)
      have hl0 : l0 ≤ (hdr >>> 8) % 512 := hI.pl0 _ hf0 _ hpl
      obtain ⟨hx, hxf⟩ := statX_sound hc2 hh hcp _ hstat
      obtain ⟨hK, hkid, hS1, hl511, D', hF', hk⟩ := nodeXO_sound hnp hN5 tab hT _ _ hF hx hxf hnode
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hk
      obtain ⟨⟨⟨hext, hxk⟩, hrg⟩, hrest⟩ := hk
      simp only [nodeKs, nodeKids] at hK hkid hrest
      have hdep' : dP + 1 ≤ 21 := by simpa using hdep
      have hcard : pcnt511 (S ||| 2 ^ ((hdr >>> 8) % 512)) ≤ 21 := by
        have := (frameOKO_basic hF').2.2.1; unfold pcnt511; rw [this]; exact hdep'
      -- the stack's last frame: the root's parent, with at most the root's label pending
      obtain ⟨fb, pb, hlast, hfb, hpb⟩ := hI.bot
      refine ih _ out (insert (S ||| 2 ^ ((hdr >>> 8) % 512), (hdr >>> 8) % 512) K) ⟨?_, ?_, ?_, ?_, ?_⟩ hrest
      · -- valid frames
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hFr _ _ _ _ _ hF'
        · rcases List.mem_cons.mp hf with rfl | hf
          · exact hF
          · exact hI.fr f (hmemd f (by rw [hd]; exact List.mem_cons_of_mem _ hf))
      · -- coverage
        intro n hn
        rcases Set.mem_insert_iff.mp hn with rfl | hn
        · refine ⟨hS1, hcard, hl0, fun u hu1 hu2 => ?_⟩
          by_cases hpu : (pendR ((hdr >>> 8) % 512) ks kids (acc e) (xk e) D' (lowOf st' lo) (rg e)).testBit u = true
          · right; right; right; right; right; exact ⟨_, List.mem_cons_self .., rfl, hpu⟩
          · rw [pendR_testBit] at hpu
            cases hlw : (lowOf st' lo).testBit u
            · cases hgl : (geL (rg e)).testBit u
              · -- `pendOf` does not hold `u`: the cases of `itemXS'_sound`
                rw [hlw, hgl] at hpu
                simp only [Bool.not_false, Bool.and_true] at hpu
                rw [pendOf_testBit, above511_testBit hl511, decide_eq_true ⟨hu1, hu2⟩] at hpu
                cases hkm : (killMask ks).testBit u
                · cases hcm : (kidMask kids).testBit u
                  · cases ham : (acc e).testBit u
                    · cases hxm : (xk e).testBit u
                      · cases hdm : D'.testBit u
                        · rw [hkm, hcm, ham, hxm, hdm] at hpu; exact absurd rfl hpu
                        · left
                          intro A _ hC hcont
                          have hl' := shr_one_lastOf hS1
                          have hB : R3RT.SpecO.Below O A (S ||| 2 ^ ((hdr >>> 8) % 512))
                              (lastOf (S ||| 2 ^ ((hdr >>> 8) % 512))) := by
                            rw [hl']; exact L5O.cont_below A _ _ u hcont
                          exact (frameOKO_apply hF' A (hCΩ A hC) hB).1 u (by rw [hl']; exact hu1) hu2 hdm
                            (L5O.cont_has A _ _ u hcont)
                      · right; left
                        rcases hxk with h0 | h0
                        · rw [Nat.beq_eq] at h0; rw [h0] at hxm; simp at hxm
                        · rw [Nat.beq_eq] at h0; exact xkRest_mem h0 hxm
                    · left; exact hExt _ _ _ _ _ _ _ hF' hS1 hl511 hdep' hext u hu1 hu2 ham
                  · left
                    obtain ⟨c, hc, hcu⟩ := (maskL_testBit _ u kids).mp hcm
                    intro A _ hC; rw [← hcu]; exact hkid c hc A (hCΩ A hC)
                · left
                  obtain ⟨kr, hkr, hku⟩ := (maskL_testBit _ u ks).mp hkm
                  intro A _ hC
                  have := hK kr hkr A (hCΩ A hC)
                  rwa [show kr % 512 = u by rw [← hku, land511]] at this
              · -- handed to a range: the record's range start is at most `u`, and the range is in the list
                obtain ⟨hle, hu511⟩ := geL_testBit hgl
                right; right; right; right; left
                refine ⟨rg e, ?_, hle⟩
                rcases hrg with h0 | h0
                · rw [Nat.beq_eq] at h0; omega
                · exact rngMem_spec h0
            · -- the root's excused labels: this record's parent frame is the stack's last one
              obtain ⟨hst', hulo⟩ := lowOf_testBit hlw
              subst hst'
              have hgl := getLast?_of_drop hd
              rw [hlast] at hgl
              simp only [Option.some.injEq, Prod.mk.injEq] at hgl
              obtain ⟨hfbe, hpbe⟩ := hgl
              have hS : S = P := by rw [hfbe] at hfb; exact hfb
              have hlab : (hdr >>> 8) % 512 = l0 := hpb _ (by rw [hpbe]; exact hpl)
              right; right; right; left
              exact ⟨by rw [hS, hlab], hulo⟩
        · obtain ⟨htop, hc, hln, hcov⟩ := hI.cov n hn
          refine ⟨htop, hc, hln, fun u hu1 hu2 => ?_⟩
          rcases hcov u hu1 hu2 with h1 | h1 | h1 | h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl (Set.mem_insert_of_mem _ h1)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
          · rcases pend_move hd hz ((S ||| 2 ^ ((hdr >>> 8) % 512), D', N ||| c2, U + h, Nat.succ dP),
                pendR ((hdr >>> 8) % 512) ks kids (acc e) (xk e) D' (lowOf st' lo) (rg e)) ((hdr >>> 8) % 512) _ _ h1
              with ⟨h2, h3⟩ | h2
            · right; right; left
              have : n.1 ||| 2 ^ u = S ||| 2 ^ ((hdr >>> 8) % 512) := by rw [h2, h3]
              rw [show (n.1 ||| 2 ^ u, u) = (S ||| 2 ^ ((hdr >>> 8) % 512), (hdr >>> 8) % 512) by rw [this, h3]]
              exact Set.mem_insert _ _
            · right; right; right; right; right; exact h2
      · -- the root
        rcases hI.root with h1 | h1
        · exact Or.inl (Set.mem_insert_of_mem _ h1)
        · rcases pend_move hd hz ((S ||| 2 ^ ((hdr >>> 8) % 512), D', N ||| c2, U + h, Nat.succ dP),
              pendR ((hdr >>> 8) % 512) ks kids (acc e) (xk e) D' (lowOf st' lo) (rg e)) ((hdr >>> 8) % 512) _ _ h1
            with ⟨h2, h3⟩ | h2
          · left
            rw [show (P ||| 2 ^ l0, l0) = (S ||| 2 ^ ((hdr >>> 8) % 512), (hdr >>> 8) % 512) by rw [h2, h3]]
            exact Set.mem_insert _ _
          · right; exact h2
      · -- pending labels stay at or above the root's label
        intro f hf u hu
        rcases List.mem_cons.mp hf with rfl | hf
        · simp only at hu
          rw [pendR_testBit, Bool.and_eq_true, Bool.and_eq_true, pendOf_testBit] at hu
          have ha := hu.1.1
          simp only [Bool.and_eq_true] at ha
          rw [above511_testBit hl511] at ha
          have := ha.1.1.1.1.1; simp at this; omega
        · rcases List.mem_cons.mp hf with rfl | hf
          · simp only at hu
            rw [clrBit_testBit, Bool.and_eq_true] at hu
            exact hI.pl0 _ hf0 u hu.1
          · exact hI.pl0 f (hmemd f (by rw [hd]; exact List.mem_cons_of_mem _ hf)) u hu
      · -- the stack's last frame
        cases st' with
        | nil =>
          have hgl := getLast?_of_drop hd
          rw [hlast] at hgl
          simp only [Option.some.injEq, Prod.mk.injEq] at hgl
          obtain ⟨hfbe, hpbe⟩ := hgl
          refine ⟨(S, D, N, U, dP), clrBit pend ((hdr >>> 8) % 512), by simp, by rw [hfbe] at hfb; exact hfb, fun u hu => ?_⟩
          rw [clrBit_testBit, Bool.and_eq_true] at hu
          exact hpb u (by rw [hpbe]; exact hu.1)
        | cons b t =>
          refine ⟨fb, pb, ?_, hfb, hpb⟩
          rw [List.getLast?_cons_cons, List.getLast?_cons_cons, ← getLast?_of_drop_cons hd, hlast]

/-! ## Chains of batches and the item -/

/-- a chain of accepted batches with ranges from the stack `st` to the stack `out` -/
inductive ChainR {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (extL : List (ℕ × ℕ)) (lo : ℕ)
    (rngL : List ((ℕ × ℕ) × ℕ)) (ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk rg : E → ℕ) (tab : ℕ → ℕ) :
    List FrP → List FrP → Prop
  | nil (st : List FrP) : ChainR np c2T hkT cpT extL lo rngL ext acc xk rg tab st st
  | cons (st mid out : List FrP) (b : List (NodeX × E)) :
      itemXR' np c2T hkT cpT extL lo rngL ext acc xk rg tab st b mid = true →
      ChainR np c2T hkT cpT extL lo rngL ext acc xk rg tab mid out → ChainR np c2T hkT cpT extL lo rngL ext acc xk rg tab st out

theorem chainR_sound {E : Type} {O : R3RT.SpecO.LabelOrder} {Ω C : Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {extL : List (ℕ × ℕ)} {lo : ℕ} {rngL : List ((ℕ × ℕ) × ℕ)}
    {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk rg : E → ℕ}
    {Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop} {P l0 : ℕ}
    (hnp : NpOK O np) (hN5 : N5Contract O Ω Fr) (hFr : ∀ S D N U d, FrameOKO O Ω S D N U d → Fr (S, D, N, U, d))
    (tab : ℕ → ℕ) (hT : TabOKO O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (hExt : ExtSound O Ω C ext acc) {st out : List FrP}
    (hch : ChainR np c2T hkT cpT extL lo rngL ext acc xk rg tab st out) :
    ∀ K, InvR O C Fr K {e | e ∈ extL} {p | p ∈ rngL} P l0 lo st →
      ∃ K', InvR O C Fr K' {e | e ∈ extL} {p | p ∈ rngL} P l0 lo out := by
  induction hch with
  | nil st => exact fun K hI => ⟨K, hI⟩
  | cons st mid out b hb _ ih =>
    intro K hI
    obtain ⟨K1, hI1⟩ := itemXR'_sound hnp hN5 hFr tab hT hc2 hh hcp hCΩ hExt b st mid K hI hb
    exact ih K1 hI1

/-- **a covered tree with a lower bound and ranges**: its OPEN nodes `K` contain the root; each has its top bit, at most 21
prefix labels, its label at or above the root's, and each child above its label dead, OPEN, external (`X`), below the root's
bound `lo`, or handed to a range of `R` -/
def ItemCovR (O : R3RT.SpecO.LabelOrder) (C : Dec22 → Prop) (root : ℕ × ℕ) (lo : ℕ) (K X : Set (ℕ × ℕ))
    (R : Set ((ℕ × ℕ) × ℕ)) : Prop :=
  root ∈ K ∧ ∀ n ∈ K, n.1 >>> n.2 = 1 ∧ pcnt511 n.1 ≤ 21 ∧ root.2 ≤ n.2 ∧ ∀ u, n.2 < u → u < 511 →
    R3RT.SpecO.ChildDead O C n.1 n.2 u ∨ (n.1 ||| 2 ^ u, u) ∈ K ∨ (n.1 ||| 2 ^ u, u) ∈ X ∨ (n = root ∧ u < lo) ∨
      (∃ l, (n, l) ∈ R ∧ l ≤ u)

/-- **an item's chain covers its tree**: from the root's parent frame `f0` with only the root's label `l0` pending to a stack
without pending labels -/
theorem itemR_cov {E : Type} {O : R3RT.SpecO.LabelOrder} {Ω C : Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {extL : List (ℕ × ℕ)} {lo : ℕ} {rngL : List ((ℕ × ℕ) × ℕ)}
    {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk rg : E → ℕ}
    {Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop}
    (hnp : NpOK O np) (hN5 : N5Contract O Ω Fr) (hFr : ∀ S D N U d, FrameOKO O Ω S D N U d → Fr (S, D, N, U, d))
    (tab : ℕ → ℕ) (hT : TabOKO O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (hExt : ExtSound O Ω C ext acc)
    (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (hF0 : Fr f0) (l0 : ℕ) (out : List FrP)
    (hch : ChainR np c2T hkT cpT extL lo rngL ext acc xk rg tab [(f0, 2 ^ l0)] out) (hfin : pendZ out = true) :
    ∃ K, ItemCovR O C (f0.1 ||| 2 ^ l0, l0) lo K {e | e ∈ extL} {p | p ∈ rngL} := by
  have hb0 : ∀ u, (2 ^ l0 : ℕ).testBit u = true → u = l0 := by
    intro u hu; rw [Nat.testBit_two_pow] at hu; simpa [eq_comm] using hu
  have hI0 : InvR O C Fr ∅ {e | e ∈ extL} {p | p ∈ rngL} f0.1 l0 lo [(f0, 2 ^ l0)] :=
    ⟨fun f hf => by rw [List.mem_singleton] at hf; rw [hf]; exact hF0, fun n hn => absurd hn (Set.notMem_empty n),
      Or.inr ⟨(f0, 2 ^ l0), List.mem_singleton_self _, rfl, by rw [Nat.testBit_two_pow_self]⟩,
      fun f hf u hu => by rw [List.mem_singleton] at hf; rw [hf] at hu; exact (hb0 u hu).ge,
      ⟨f0, 2 ^ l0, rfl, rfl, hb0⟩⟩
  obtain ⟨K, hI⟩ := chainR_sound hnp hN5 hFr tab hT hc2 hh hcp hCΩ hExt hch ∅ hI0
  have hnp' : ∀ T u, ¬ ∃ f ∈ out, f.1.1 = T ∧ f.2.testBit u = true := by
    rintro T u ⟨f, hf, _, hu⟩; rw [pendZ_spec hfin f hf] at hu; simp at hu
  refine ⟨K, ?_, fun n hn => ?_⟩
  · rcases hI.root with h | h
    · exact h
    · exact absurd h (hnp' _ _)
  · obtain ⟨htop, hc, hln, hcov⟩ := hI.cov n hn
    refine ⟨htop, hc, hln, fun u hu1 hu2 => ?_⟩
    rcases hcov u hu1 hu2 with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact absurd h (hnp' _ _)

end KD
