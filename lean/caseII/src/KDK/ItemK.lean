module
public import R22Port.U_d41d8cd98f00
public import KDK.XBatchO
public import KDK.FrameU
/-! # KDK.ItemK (kinds-only name of KD.ItemK): one item (a job's or a piece's stream) of the kernel track as a covered tree

An item's OPEN records are checked in **chained batches** (one kernel declaration each).  `itemXS'` is `batchXO'` with
* a **pending mask** in every stack frame: a node's mask holds the labels above `last` that it neither kills (L1's T/C kills,
  the X part's children) nor accounts for (the extension's accounted children `acc e`, its external children `xk e`, the dead
  labels `D'` of its frame).  A record
  is checked on a frame with its label pending, which it clears; frames are popped only with an empty mask;
* the **static data** of each record compared with the label tables (`statX`: the node's cap-2 table `c2T` and hit vector `hkT`,
  the aggregates' and children's cap-2 tables, the children's window constants `cpT`);
* the **external children** looked up in the item's interface list `extL` (`xkRest`);
* at the end of a batch, the stack compared with the next batch's input (`stEq`).

**`itemXS'_sound`**: an accepted batch keeps the invariant `InvP`: every frame valid (`Fr`); every recorded node has its top bit,
at most 21 prefix labels, and each child above its label dead (`ChildDead O C`), external, recorded, or pending in a frame of the
stack; the item root is recorded or pending.  **`itemK_cov`**: a chain of batches (`ChainK`) from the root's parent frame with
the root's label pending to a stack without pending labels gives a covered tree (`ItemCovK`): a set of OPEN nodes containing the
root, each child of each node dead, OPEN, or external.  **`itemK_sound`**: the same from an accepted root frame (`rootChk`, the
prefix's frame as `KD.rootFrame_okU` builds it), under facts `H` that give the tables' semantics. -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
noncomputable section
namespace KD
open R3RT.Spec RootSound BC4 BC5 Classical
open R3RT (M511 foldR node5 mapL mkD)

/-! ## The checker -/

/-- a stack frame with its pending-children mask -/
abbrev FrP := (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ

/-- `OR` of `2^(f a)` over a list -/
def maskL {α : Type} (f : α → ℕ) (l : List α) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ acc => Nat.lor (Nat.shiftLeft 1 (f a)) acc) l

/-- the labels of L1's T/C kills -/
def killMask (ks : List ℕ) : ℕ := maskL (fun kr => Nat.land kr 511) ks

/-- the labels of the X part's children -/
def kidMask (kids : List KidX) : ℕ := maskL (fun c => c.1) kids

/-- the labels `last + 1 .. 510` -/
def above511 (last : ℕ) : ℕ := Nat.sub (Nat.shiftLeft 1 511) (Nat.shiftLeft 1 (Nat.add last 1))

/-- a node's pending children: above `last`, minus the kills, the X children, the accounted and the external children, and
the dead labels `D'` of its frame -/
def pendOf (last : ℕ) (ks : List ℕ) (kids : List KidX) (acc xk D' : ℕ) : ℕ :=
  K2.andn (K2.andn (K2.andn (K2.andn (K2.andn (above511 last) (killMask ks)) (kidMask kids)) acc) xk) D'

def clrBit (m l : ℕ) : ℕ := K2.andn m (Nat.shiftLeft 1 l)

/-- no frame of the list has a pending child -/
def pendZ (st : List FrP) : Bool := List.rec (motive := fun _ => Bool) true (fun f _ acc => Nat.beq f.2 0 && acc) st

def allB {α : Type} (p : α → Bool) (l : List α) : Bool := List.rec (motive := fun _ => Bool) true (fun a _ acc => p a && acc) l

def tupBeq (a b : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2.1 b.2.2.1 && Nat.beq a.2.2.2.1 b.2.2.2.1 && Nat.beq a.2.2.2.2 b.2.2.2.2

/-- a child's static data: its cap-2 table and window constants are the tables' -/
def kidStat (c2T : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (c : KidX) : Bool :=
  Nat.blt c.1 511 && Nat.beq c.2.2.2.2.1 (c2T c.1) && tupBeq c.2.2.2.2.2 (cpT c.1)

/-- an aggregate's cap-2 table is the table's -/
def aggStat (c2T : ℕ → ℕ) (ag : Agg) : Bool := Nat.blt ag.1 511 && Nat.beq ag.2.1 (c2T ag.1)

/-- **a record's static data** against the label tables -/
def statX (c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (x : NodeX) : Bool :=
  Nat.blt (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) 511 &&
  Nat.beq x.1 (c2T (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) &&
  Nat.beq x.2.1 (hkT (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) &&
  allB (aggStat c2T) (nodeAggs x) && allB (kidStat c2T cpT) (nodeKids x)

/-- the labels `u` of mask `m` whose child key `(S' ||| 2^u, u)` is not in `extL` (and possibly more) -/
def xkRest (extL : List (ℕ × ℕ)) (S' m : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) m
    (fun p _ acc => cond (Nat.beq p.1 (Nat.lor S' (Nat.shiftLeft 1 p.2))) (clrBit acc p.2) acc) extL

def frEq (a b : FrP) : Bool :=
  Nat.beq a.1.1 b.1.1 && Nat.beq a.1.2.1 b.1.2.1 && Nat.beq a.1.2.2.1 b.1.2.2.1 && Nat.beq a.1.2.2.2.1 b.1.2.2.2.1 &&
    Nat.beq a.1.2.2.2.2 b.1.2.2.2.2 && Nat.beq a.2 b.2

def stEq : List FrP → List FrP → Bool :=
  -- nested `List.rec` (no overlapping match: no splitter with unexported `_sparseCasesOn` auxiliaries; the ExposeCheck rule)
  List.rec (motive := fun _ => List FrP → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false (fun b m' _ => frEq a b && ih m') m)

/-- **one batch of an item** from the stack `st` to the stack `out` -/
def itemXS' {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (extL : List (ℕ × ℕ))
    (ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk : E → ℕ) (tab : ℕ → ℕ) :
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
        itemXS' np c2T hkT cpT extL ext acc xk tab
          (((S', D', N', U', Nat.succ dP),
              pendOf (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) (nodeKs x) (nodeKids x) (acc e) (xk e) D') ::
            ((S, D, N, U, dP), clrBit pend (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) :: st') rest out)

/-! ## Bits -/

theorem maskL_testBit {α : Type} (f : α → ℕ) (u : ℕ) : ∀ l : List α, (maskL f l).testBit u = true ↔ ∃ a ∈ l, f a = u
  | [] => by simp [maskL]
  | a :: l => by
    have ih := maskL_testBit f u l
    change (Nat.lor (Nat.shiftLeft 1 (f a)) (maskL f l)).testBit u = true ↔ _
    rw [L5.lor_eq, L5.shl_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, ih]
    simp only [decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, hbu⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, hbu⟩
    · rintro ⟨b, (rfl | hb), hbu⟩
      · exact Or.inl hbu
      · exact Or.inr ⟨b, hb, hbu⟩

theorem above511_testBit {last u : ℕ} (hl : last < 511) : (above511 last).testBit u = decide (last < u ∧ u < 511) := by
  unfold above511
  rw [L5.nsub_eq, L5.shl_eq, L5.shl_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul, L5.nadd_eq,
    L5.testBit_pow_sub_pow 511 (last + 1) u (by omega)]
  apply decide_eq_decide.mpr; omega

theorem clrBit_testBit (m l u : ℕ) : (clrBit m l).testBit u = (m.testBit u && !decide (l = u)) := by
  unfold clrBit; rw [K2.testBit_andn, L5.shl_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem pendOf_testBit (last : ℕ) (ks : List ℕ) (kids : List KidX) (a x D' u : ℕ) :
    (pendOf last ks kids a x D').testBit u = ((above511 last).testBit u && !(killMask ks).testBit u &&
      !(kidMask kids).testBit u && !a.testBit u && !x.testBit u && !D'.testBit u) := by
  unfold pendOf; simp only [K2.testBit_andn]

theorem pendZ_spec : ∀ {l : List FrP}, pendZ l = true → ∀ f ∈ l, f.2 = 0
  | [], _, f, hf => by simp at hf
  | g :: l, h, f, hf => by
    have h' : (Nat.beq g.2 0 && pendZ l) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h'.1
    · exact pendZ_spec h'.2 f hf

theorem allB_spec {α : Type} {p : α → Bool} : ∀ {l : List α}, allB p l = true → ∀ a ∈ l, p a = true
  | [], _, a, ha => by simp at ha
  | b :: l, h, a, ha => by
    have h' : (p b && allB p l) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h'.1
    · exact allB_spec h'.2 a ha

theorem tupBeq_spec {a b : ℕ × ℕ × ℕ × ℕ × ℕ} (h : tupBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [tupBeq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  subst h1 h2 h3 h4 h5; rfl

theorem frEq_spec {a b : FrP} (h : frEq a b = true) : a = b := by
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, a6⟩ := a
  obtain ⟨⟨b1, b2, b3, b4, b5⟩, b6⟩ := b
  simp only [frEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6; rfl

theorem stEq_spec : ∀ {l m : List FrP}, stEq l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    have h' : (frEq a b && stEq l m) = true := h
    rw [Bool.and_eq_true] at h'
    rw [frEq_spec h'.1, stEq_spec h'.2]
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true

theorem xkRest_keep (S' m u : ℕ) (hm : m.testBit u = true) :
    ∀ (extL : List (ℕ × ℕ)), (S' ||| 2 ^ u, u) ∉ extL → (xkRest extL S' m).testBit u = true
  | [], _ => hm
  | p :: l, hn => by
    have ih := xkRest_keep S' m u hm l (fun h => hn (List.mem_cons_of_mem _ h))
    change (cond (Nat.beq p.1 (Nat.lor S' (Nat.shiftLeft 1 p.2))) (clrBit (xkRest l S' m) p.2) (xkRest l S' m)).testBit u = true
    cases hb : Nat.beq p.1 (Nat.lor S' (Nat.shiftLeft 1 p.2))
    · exact ih
    · rw [cond_true, clrBit_testBit, ih]
      have hp1 : p.1 = S' ||| 2 ^ p.2 := by
        rw [Nat.beq_eq] at hb; rw [hb, L5.lor_eq, L5.shl_eq, Nat.shiftLeft_eq, one_mul]
      have : p.2 ≠ u := by
        intro e; apply hn; rw [List.mem_cons]; left
        obtain ⟨p1, p2⟩ := p; simp only at hp1 e; subst e; rw [hp1]
      simp [this]

theorem xkRest_mem {extL : List (ℕ × ℕ)} {S' m : ℕ} (h : xkRest extL S' m = 0) {u : ℕ} (hm : m.testBit u = true) :
    (S' ||| 2 ^ u, u) ∈ extL := by
  by_contra hn
  have := xkRest_keep S' m u hm extL hn
  rw [h] at this; simp at this

theorem land511 (k : ℕ) : Nat.land k 511 = k % 512 := by
  rw [L5.land_eq, show (511 : ℕ) = 2 ^ 9 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem land255 (k : ℕ) : Nat.land k 255 = k % 256 := by
  rw [L5.land_eq, show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem hdr_last (hdr : ℕ) : (hdr.shiftRight 8).land 511 = (hdr >>> 8) % 512 := by
  rw [land511, L5.shr_eq]

/-! ## Static data -/

/-- **the static data of an accepted record** are the facts `nodeXO_sound` needs, from the tables' facts -/
theorem statX_sound {O : R3RT.SpecO.LabelOrder} {Ω : Dec22 → Prop} {c2T hkT : ℕ → ℕ} {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ}
    (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l)) (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l))
    (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (x : NodeX) (h : statX c2T hkT cpT x = true) :
    (C2OKO O Ω ((x.2.2.2.1 >>> 8) % 512) x.1 ∧ R3RT.SpecO.HOK O ((x.2.2.2.1 >>> 8) % 512) x.2.1) ∧
    ((∀ ag ∈ nodeAggs x, C2OKO O Ω ag.1 ag.2.1) ∧ (∀ c ∈ nodeKids x, KidXOKO O Ω c)) := by
  unfold statX at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hl, hc⟩, hhh⟩, hag⟩, hkid⟩ := h
  rw [hdr_last] at hl hc hhh
  refine ⟨⟨by rw [hc]; exact hc2 _ hl, by rw [hhh]; exact hh _ hl⟩, fun ag hag' => ?_, fun c hc' => ?_⟩
  · have := allB_spec hag ag hag'
    simp only [aggStat, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    rw [this.2]; exact hc2 _ this.1
  · have := allB_spec hkid c hc'
    simp only [kidStat, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨by rw [h2]; exact hc2 _ h1, ?_⟩
    rw [tupBeq_spec h3]; exact hcp _ h1

/-! ## The invariant -/

/-- the number of prefix labels -/
def pcnt511 (S : ℕ) : ℕ := ((Finset.range 511).filter (fun l => S.testBit l = true)).card

/-- what a run has established: valid frames; every recorded node (top bit, at most 21 prefix labels) has each child dead,
external, recorded, or pending in a frame of the stack; the root `(P ||| 2^l0, l0)` is recorded or pending in a frame of
prefix `P` -/
structure InvP (O : R3RT.SpecO.LabelOrder) (C : Dec22 → Prop) (Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop) (K X : Set (ℕ × ℕ))
    (P l0 : ℕ) (st : List FrP) : Prop where
  fr : ∀ f ∈ st, Fr f.1
  cov : ∀ n ∈ K, n.1 >>> n.2 = 1 ∧ pcnt511 n.1 ≤ 21 ∧ ∀ u, n.2 < u → u < 511 →
    R3RT.SpecO.ChildDead O C n.1 n.2 u ∨ (n.1 ||| 2 ^ u, u) ∈ X ∨ (n.1 ||| 2 ^ u, u) ∈ K ∨
      ∃ f ∈ st, f.1.1 = n.1 ∧ f.2.testBit u = true
  root : (P ||| 2 ^ l0, l0) ∈ K ∨ ∃ f ∈ st, f.1.1 = P ∧ f.2.testBit l0 = true

/-- the extension's contract: on a valid child frame, an accepted extension accounts for its children (dead in the case `C`) -/
def ExtSound {E : Type} (O : R3RT.SpecO.LabelOrder) (Ω C : Dec22 → Prop) (ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool)
    (acc : E → ℕ) : Prop :=
  ∀ S' D' N' U' d' last e, FrameOKO O Ω S' D' N' U' d' → S' >>> last = 1 → last < 511 → d' ≤ 21 →
    ext S' D' N' U' d' last e = true → ∀ u, last < u → u < 511 → (acc e).testBit u = true →
      R3RT.SpecO.ChildDead O C S' last u

/-- a pending child of the old stack is the new node or pending in the new stack -/
theorem pend_move {st st' : List FrP} {k : ℕ} {f0 : FrP} (hd : st.drop k = f0 :: st') (hz : pendZ (st.take k) = true)
    (newF : FrP) (last T u : ℕ) (h : ∃ f ∈ st, f.1.1 = T ∧ f.2.testBit u = true) :
    (T = f0.1.1 ∧ u = last) ∨ ∃ f ∈ newF :: (f0.1, clrBit f0.2 last) :: st', f.1.1 = T ∧ f.2.testBit u = true := by
  obtain ⟨f, hf, hT, hu⟩ := h
  rw [← List.take_append_drop k st, hd] at hf
  rcases List.mem_append.mp hf with hf | hf
  · rw [pendZ_spec hz f hf] at hu; simp at hu
  · rcases List.mem_cons.mp hf with rfl | hf
    · by_cases hul : u = last
      · exact Or.inl ⟨hT.symm, hul⟩
      · right
        refine ⟨(f.1, clrBit f.2 last), List.mem_cons_of_mem _ (List.mem_cons_self ..), hT, ?_⟩
        rw [clrBit_testBit, hu]; simp [Ne.symm hul]
    · right; exact ⟨f, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf), hT, hu⟩

/-! ## One batch -/

/-- **Soundness of one batch of an item.** -/
theorem itemXS'_sound {E : Type} {O : R3RT.SpecO.LabelOrder} {Ω C : Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {extL : List (ℕ × ℕ)} {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk : E → ℕ}
    {Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop} {P l0 : ℕ}
    (hnp : NpOK O np) (hN5 : N5Contract O Ω Fr) (hFr : ∀ S D N U d, FrameOKO O Ω S D N U d → Fr (S, D, N, U, d))
    (tab : ℕ → ℕ) (hT : TabOKO O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (hExt : ExtSound O Ω C ext acc) :
    ∀ (nodes : List (NodeX × E)) (st out : List FrP) (K : Set (ℕ × ℕ)),
      InvP O C Fr K {e | e ∈ extL} P l0 st →
      itemXS' np c2T hkT cpT extL ext acc xk tab st nodes out = true →
      ∃ K', InvP O C Fr K' {e | e ∈ extL} P l0 out := by
  intro nodes
  induction nodes with
  | nil =>
    intro st out K hI hb
    simp only [itemXS'] at hb
    rw [← stEq_spec hb]; exact ⟨K, hI⟩
  | cons xe rest ih =>
    intro st out K hI hb
    obtain ⟨x, e⟩ := xe
    obtain ⟨c2, h, suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x
    simp only [itemXS'] at hb
    rw [land255, hdr_last] at hb
    rcases hd : List.drop (hdr % 256) st with _ | ⟨⟨⟨S, D, N, U, dP⟩, pend⟩, st'⟩
    · rw [hd] at hb; exact absurd hb (by simp)
    · rw [hd] at hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨⟨⟨hz, _hbit⟩, hdep⟩, hstat⟩, hnode⟩ := hb
      have hmemd : ∀ f, f ∈ List.drop (hdr % 256) st → f ∈ st := fun f hf => List.mem_of_mem_drop hf
      have hf0 : ((S, D, N, U, dP), pend) ∈ st := hmemd _ (by rw [hd]; exact List.mem_cons_self ..)
      have hF : Fr (S, D, N, U, dP) := hI.fr _ hf0
      obtain ⟨hx, hxf⟩ := statX_sound hc2 hh hcp _ hstat
      obtain ⟨hK, hkid, hS1, hl511, D', hF', hk⟩ := nodeXO_sound hnp hN5 tab hT _ _ hF hx hxf hnode
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hk
      obtain ⟨⟨hext, hxk⟩, hrest⟩ := hk
      simp only [nodeKs, nodeKids] at hK hkid hrest
      have hdep' : dP + 1 ≤ 21 := by simpa using hdep
      have hcard : pcnt511 (S ||| 2 ^ ((hdr >>> 8) % 512)) ≤ 21 := by
        have := (frameOKO_basic hF').2.2.1; unfold pcnt511; rw [this]; exact hdep'
      refine ih _ out (insert (S ||| 2 ^ ((hdr >>> 8) % 512), (hdr >>> 8) % 512) K) ⟨?_, ?_, ?_⟩ hrest
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
        · refine ⟨hS1, hcard, fun u hu1 hu2 => ?_⟩
          by_cases hpu : (pendOf ((hdr >>> 8) % 512) ks kids (acc e) (xk e) D').testBit u = true
          · right; right; right; exact ⟨_, List.mem_cons_self .., rfl, hpu⟩
          · rw [pendOf_testBit, above511_testBit hl511, decide_eq_true ⟨hu1, hu2⟩] at hpu
            cases hkm : (killMask ks).testBit u
            · cases hcm : (kidMask kids).testBit u
              · cases ham : (acc e).testBit u
                · cases hxm : (xk e).testBit u
                  · cases hdm : D'.testBit u
                    · rw [hkm, hcm, ham, hxm, hdm] at hpu; exact absurd rfl hpu
                    · -- a dead label of the node's frame
                      left
                      intro A _ hC hcont
                      have hl' := shr_one_lastOf hS1
                      have hB : R3RT.SpecO.Below O A (S ||| 2 ^ ((hdr >>> 8) % 512)) (lastOf (S ||| 2 ^ ((hdr >>> 8) % 512))) := by
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
        · obtain ⟨htop, hc, hcov⟩ := hI.cov n hn
          refine ⟨htop, hc, fun u hu1 hu2 => ?_⟩
          rcases hcov u hu1 hu2 with h1 | h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl (Set.mem_insert_of_mem _ h1)))
          · rcases pend_move hd hz ((S ||| 2 ^ ((hdr >>> 8) % 512), D', N ||| c2, U + h, Nat.succ dP),
                pendOf ((hdr >>> 8) % 512) ks kids (acc e) (xk e) D') ((hdr >>> 8) % 512) _ _ h1 with ⟨h2, h3⟩ | h2
            · right; right; left
              have : n.1 ||| 2 ^ u = S ||| 2 ^ ((hdr >>> 8) % 512) := by rw [h2, h3]
              rw [show (n.1 ||| 2 ^ u, u) = (S ||| 2 ^ ((hdr >>> 8) % 512), (hdr >>> 8) % 512) by rw [this, h3]]
              exact Set.mem_insert _ _
            · right; right; right; exact h2
      · -- the root
        rcases hI.root with h1 | h1
        · exact Or.inl (Set.mem_insert_of_mem _ h1)
        · rcases pend_move hd hz ((S ||| 2 ^ ((hdr >>> 8) % 512), D', N ||| c2, U + h, Nat.succ dP),
              pendOf ((hdr >>> 8) % 512) ks kids (acc e) (xk e) D') ((hdr >>> 8) % 512) _ _ h1 with ⟨h2, h3⟩ | h2
          · left
            rw [show (P ||| 2 ^ l0, l0) = (S ||| 2 ^ ((hdr >>> 8) % 512), (hdr >>> 8) % 512) by rw [h2, h3]]
            exact Set.mem_insert _ _
          · right; exact h2

/-! ## Chains of batches and the item -/

/-- a chain of accepted batches from the stack `st` to the stack `out` -/
inductive ChainK {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (extL : List (ℕ × ℕ))
    (ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk : E → ℕ) (tab : ℕ → ℕ) : List FrP → List FrP → Prop
  | nil (st : List FrP) : ChainK np c2T hkT cpT extL ext acc xk tab st st
  | cons (st mid out : List FrP) (b : List (NodeX × E)) :
      itemXS' np c2T hkT cpT extL ext acc xk tab st b mid = true → ChainK np c2T hkT cpT extL ext acc xk tab mid out →
      ChainK np c2T hkT cpT extL ext acc xk tab st out

theorem chainK_sound {E : Type} {O : R3RT.SpecO.LabelOrder} {Ω C : Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {extL : List (ℕ × ℕ)} {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk : E → ℕ}
    {Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop} {P l0 : ℕ}
    (hnp : NpOK O np) (hN5 : N5Contract O Ω Fr) (hFr : ∀ S D N U d, FrameOKO O Ω S D N U d → Fr (S, D, N, U, d))
    (tab : ℕ → ℕ) (hT : TabOKO O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (hExt : ExtSound O Ω C ext acc) {st out : List FrP}
    (hch : ChainK np c2T hkT cpT extL ext acc xk tab st out) :
    ∀ K, InvP O C Fr K {e | e ∈ extL} P l0 st → ∃ K', InvP O C Fr K' {e | e ∈ extL} P l0 out := by
  induction hch with
  | nil st => exact fun K hI => ⟨K, hI⟩
  | cons st mid out b hb _ ih =>
    intro K hI
    obtain ⟨K1, hI1⟩ := itemXS'_sound hnp hN5 hFr tab hT hc2 hh hcp hCΩ hExt b st mid K hI hb
    exact ih K1 hI1

/-- **a covered tree**: its OPEN nodes `K` contain the root; each has its top bit, at most 21 prefix labels, and each child above
its label dead in the case `C`, OPEN, or external (`X`) -/
def ItemCovK (O : R3RT.SpecO.LabelOrder) (C : Dec22 → Prop) (root : ℕ × ℕ) (K X : Set (ℕ × ℕ)) : Prop :=
  root ∈ K ∧ ∀ n ∈ K, n.1 >>> n.2 = 1 ∧ pcnt511 n.1 ≤ 21 ∧ ∀ u, n.2 < u → u < 511 →
    R3RT.SpecO.ChildDead O C n.1 n.2 u ∨ (n.1 ||| 2 ^ u, u) ∈ K ∨ (n.1 ||| 2 ^ u, u) ∈ X

/-- **an item's chain covers its tree**: from the root's parent frame `f0` with the root's label `l0` pending to a stack
without pending labels -/
theorem itemK_cov {E : Type} {O : R3RT.SpecO.LabelOrder} {Ω C : Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {extL : List (ℕ × ℕ)} {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk : E → ℕ}
    {Fr : ℕ × ℕ × ℕ × ℕ × ℕ → Prop}
    (hnp : NpOK O np) (hN5 : N5Contract O Ω Fr) (hFr : ∀ S D N U d, FrameOKO O Ω S D N U d → Fr (S, D, N, U, d))
    (tab : ℕ → ℕ) (hT : TabOKO O Ω tab) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u))
    (hCΩ : ∀ A, C A → Ω A) (hExt : ExtSound O Ω C ext acc)
    (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (hF0 : Fr f0) (l0 pend0 : ℕ) (hp0 : pend0.testBit l0 = true) (out : List FrP)
    (hch : ChainK np c2T hkT cpT extL ext acc xk tab [(f0, pend0)] out) (hfin : pendZ out = true) :
    ∃ K, ItemCovK O C (f0.1 ||| 2 ^ l0, l0) K {e | e ∈ extL} := by
  have hI0 : InvP O C Fr ∅ {e | e ∈ extL} f0.1 l0 [(f0, pend0)] :=
    ⟨fun f hf => by rw [List.mem_singleton] at hf; rw [hf]; exact hF0, fun n hn => absurd hn (Set.notMem_empty n),
      Or.inr ⟨(f0, pend0), List.mem_singleton_self _, rfl, hp0⟩⟩
  obtain ⟨K, hI⟩ := chainK_sound hnp hN5 hFr tab hT hc2 hh hcp hCΩ hExt hch ∅ hI0
  have hnp' : ∀ T u, ¬ ∃ f ∈ out, f.1.1 = T ∧ f.2.testBit u = true := by
    rintro T u ⟨f, hf, _, hu⟩; rw [pendZ_spec hfin f hf] at hu; simp at hu
  refine ⟨K, ?_, fun n hn => ?_⟩
  · rcases hI.root with h | h
    · exact h
    · exact absurd h (hnp' _ _)
  · obtain ⟨htop, hc, hcov⟩ := hI.cov n hn
    refine ⟨htop, hc, fun u hu1 hu2 => ?_⟩
    rcases hcov u hu1 hu2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact absurd h (hnp' _ _)

/-! ## The root's parent frame -/

/-- **a job root's parent frame over an order** (`rootFrame_okU` over `O`, with the cap-2 tables' self slots empty below 511):
`(S, D, N, U, |S|)` is valid when `N` is the cap-1 table with the prefix labels' cap-2 tables, `U = packU O S`, and every dead
label of `D` conflicts in `N` with a prefix label -/
theorem rootFrame_okO {O : R3RT.SpecO.LabelOrder} {Ω : Dec22 → Prop} {S last N U D : ℕ} (hS : S >>> last = 1)
    (hS511 : S < 2 ^ 511) (c1 : ℕ) (hc1 : R3RT.SpecO.Conf1OK O Ω c1) (c2 : ℕ → ℕ)
    (hc2 : ∀ p, p < 511 → S.testBit p = true → C2OKO O Ω p (c2 p))
    (hc2self : ∀ p, p < 511 → S.testBit p = true → ∀ w, w < 511 → (c2 p >>> (512 * p)).testBit w = false)
    (hN : ∀ v w, (N >>> (512 * v)).testBit w = true →
      (c1 >>> (512 * v)).testBit w = true ∨ ∃ p, p < 511 ∧ S.testBit p = true ∧ (c2 p >>> (512 * v)).testBit w = true)
    (hD : ∀ l, D.testBit l = true → ∃ q, q < 511 ∧ S.testBit q = true ∧ (N >>> (512 * q)).testBit l = true)
    (hU : U = R3RT.SpecO.packU O S) :
    FrameOKO O Ω S D N U (pcnt511 S) := by
  have hlast := shr_one_lastOf hS
  have hpos : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · rw [h, Nat.zero_shiftRight] at hS; exact absurd hS (by decide)
    · exact h
  have hpre : ∀ A : Dec22, R3RT.SpecO.Below O A S (lastOf S) → ∀ p, p < 511 → S.testBit p = true →
      R3RT.SpecO.Has O A p := by
    intro A hA p hp hSp
    have hpl : p ≤ lastOf S := by
      rw [hlast]; by_contra hc; push Not at hc; rw [shr_one_bit hS p (by omega)] at hSp; simp at hSp; omega
    exact (hA p hp hpl).2 hSp
  have hconf : ∀ A : Dec22, Ω A → R3RT.SpecO.Below O A S (lastOf S) → ∀ v w, v < 511 → w < 511 → S.testBit w = false →
      v ≠ w → (N >>> (512 * v)).testBit w = true → R3RT.SpecO.Has O A v → ¬ R3RT.SpecO.Has O A w := by
    intro A hΩ hA v w hv hw hSw hvw hbit hAv hAw
    rcases hN v w hbit with h1 | ⟨p, hp, hSp, h2⟩
    · obtain ⟨m, hm, hmv, hmw⟩ := hc1 v w hv hw (Ne.symm hvw) h1
      have hc := card_two_le (R3RT.SpecO.inMask O A m) v w
        (by simp only [R3RT.SpecO.inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
        (by simp only [R3RT.SpecO.inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩) hvw
      have := rowOKO_apply hm A hΩ; omega
    · have hpw : w ≠ p := by intro e; rw [e, hSp] at hSw; exact absurd hSw (by decide)
      by_cases hpv : v = p
      · subst hpv; rw [hc2self v hp hSp w hw] at h2; exact absurd h2 (by decide)
      · obtain ⟨m, hm, hmp, hmv, hmw⟩ := hc2 p hp hSp v w hv hw hpw (Ne.symm hvw) h2
        have hAp := hpre A hA p hp hSp
        have hc := card_three_le (R3RT.SpecO.inMask O A m) p v w
          (by simp only [R3RT.SpecO.inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hp, hmp, hAp⟩)
          (by simp only [R3RT.SpecO.inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hv, hmv, hAv⟩)
          (by simp only [R3RT.SpecO.inMask, Finset.mem_filter, Finset.mem_range]; exact ⟨hw, hmw, hAw⟩)
          (Ne.symm hpv) (Ne.symm hpw) hvw
        have := rowOKO_apply hm A hΩ; omega
  refine ⟨hpos, hS511, rfl, hU, fun A hΩ hA => ⟨?_, ?_⟩⟩
  · intro l hl hl5 hDl hAl
    obtain ⟨q, hq, hSq, hbit⟩ := hD l hDl
    have hql : q ≠ l := by
      intro e; subst e
      have : q ≤ lastOf S := by
        rw [hlast]; by_contra hc; push Not at hc; rw [shr_one_bit hS q (by omega)] at hSq; simp at hSq; omega
      omega
    have hSl : S.testBit l = false := by rw [shr_one_bit hS l (by omega)]; simp; rw [← hlast]; omega
    exact hconf A hΩ hA q l hq hl5 hSl hql hbit (hpre A hA q hq hSq) hAl
  · intro v w hv hw _ hSw hvw hbit hAv hAw
    exact hconf A hΩ hA v w hv hw hSw hvw hbit hAv hAw

/-- strictly increasing -/
def incrL (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t acc => allB (fun b => Nat.blt a b) t && acc) l

/-- `N`: the cap-1 table with the prefix labels' cap-2 tables -/
def rootN (c1 : ℕ) (c2T : ℕ → ℕ) (pl : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) c1 (fun p _ acc => Nat.lor (c2T p) acc) pl

/-- `D`: the labels below 511 in conflict (`N`) with a prefix label -/
def rootD (N : ℕ) (pl : List ℕ) : ℕ :=
  Nat.land (List.rec (motive := fun _ => ℕ) 0 (fun p _ acc => Nat.lor (Nat.shiftRight N (Nat.mul 512 p)) acc) pl) M511

/-- `U`: the prefix labels' hit vectors added -/
def rootU (hkT : ℕ → ℕ) (pl : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun p _ acc => Nat.add (hkT p) acc) pl

/-- the prefix labels' cap-2 tables have empty self slots below 511 -/
def selfZ (c2T : ℕ → ℕ) (pl : List ℕ) : Bool :=
  allB (fun p => Nat.beq (Nat.land (Nat.shiftRight (c2T p) (Nat.mul 512 p)) M511) 0) pl

/-- **the root's parent frame check**: the prefix labels `pl` (increasing, top label `lastP`) and the frame `(S, D, N, U, d)`
built from them as `KD.rootFrame_okU` builds it (the converter `py/kx3.py`'s root frame) -/
def rootChk (c1 : ℕ) (c2T hkT : ℕ → ℕ) (pl : List ℕ) (lastP : ℕ) (f : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  incrL pl && Nat.beq f.1 (maskL (fun p => p) pl) && Nat.blt f.1 (Nat.shiftLeft 1 511) &&
  Nat.beq (Nat.shiftRight f.1 lastP) 1 && selfZ c2T pl &&
  Nat.beq f.2.2.1 (rootN c1 c2T pl) && Nat.beq f.2.1 (rootD f.2.2.1 pl) && Nat.beq f.2.2.2.1 (rootU hkT pl) &&
  Nat.beq f.2.2.2.2 (L5.pcnt 511 f.1)

theorem rootN_testBit (c1 : ℕ) (c2T : ℕ → ℕ) (i : ℕ) :
    ∀ pl : List ℕ, (rootN c1 c2T pl).testBit i = true → c1.testBit i = true ∨ ∃ p ∈ pl, (c2T p).testBit i = true
  | [], h => Or.inl h
  | p :: l, h => by
    change (Nat.lor (c2T p) (rootN c1 c2T l)).testBit i = true at h
    rw [L5.lor_eq, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inr ⟨p, List.mem_cons_self .., h⟩
    · rcases rootN_testBit c1 c2T i l h with h | ⟨q, hq, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h⟩

theorem rootD_aux (N l : ℕ) : ∀ pl : List ℕ,
    (List.rec (motive := fun _ => ℕ) 0 (fun p _ acc => Nat.lor (Nat.shiftRight N (Nat.mul 512 p)) acc) pl).testBit l = true →
      ∃ q ∈ pl, (N >>> (512 * q)).testBit l = true
  | [], h => by simp at h
  | p :: t, h => by
    change (Nat.lor (Nat.shiftRight N (Nat.mul 512 p)) (List.rec (motive := fun _ => ℕ) 0
      (fun p _ acc => Nat.lor (Nat.shiftRight N (Nat.mul 512 p)) acc) t)).testBit l = true at h
    rw [L5.lor_eq, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨p, List.mem_cons_self .., h⟩
    · obtain ⟨q, hq, h⟩ := rootD_aux N l t h
      exact ⟨q, List.mem_cons_of_mem _ hq, h⟩

theorem rootD_testBit {N l : ℕ} {pl : List ℕ} (h : (rootD N pl).testBit l = true) :
    l < 511 ∧ ∃ q ∈ pl, (N >>> (512 * q)).testBit l = true := by
  unfold rootD at h
  rw [L5.land_eq, Nat.testBit_and, Bool.and_eq_true, R3RT.m511_bit, decide_eq_true_eq] at h
  exact ⟨h.2, rootD_aux N l pl h.1⟩

theorem incrL_cons {a : ℕ} {t : List ℕ} (h : incrL (a :: t) = true) : (∀ b ∈ t, a < b) ∧ incrL t = true := by
  have h' : (allB (fun b => Nat.blt a b) t && incrL t) = true := h
  simp only [Bool.and_eq_true] at h'
  exact ⟨fun b hb => by have := allB_spec h'.1 b hb; simpa using this, h'.2⟩

theorem rootU_eq {O : R3RT.SpecO.LabelOrder} {hkT : ℕ → ℕ} (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) :
    ∀ pl : List ℕ, incrL pl = true → (∀ p ∈ pl, p < 511) → rootU hkT pl = R3RT.SpecO.packU O (maskL (fun p => p) pl)
  | [], _, _ => by
    show 0 = R3RT.SpecO.packU O 0
    unfold R3RT.SpecO.packU R3RT.SpecO.hits; simp
  | p :: t, hinc, h511 => by
    obtain ⟨hlt, hinc'⟩ := incrL_cons hinc
    have ih := rootU_eq hh t hinc' (fun q hq => h511 q (List.mem_cons_of_mem _ hq))
    change Nat.add (hkT p) (rootU hkT t) = R3RT.SpecO.packU O (Nat.lor (Nat.shiftLeft 1 p) (maskL (fun p => p) t))
    have hnot : (maskL (fun p => p) t).testBit p = false := by
      cases hb : (maskL (fun p => p) t).testBit p
      · rfl
      · obtain ⟨b, hb', hbp⟩ := (maskL_testBit _ p t).mp hb
        have := hlt b hb'; omega
    rw [L5.nadd_eq, L5.lor_eq, L5.shl_eq, Nat.shiftLeft_eq, one_mul, Nat.lor_comm,
      L5O.packU_or _ p _ hnot (h511 p (List.mem_cons_self ..)) (hh p (h511 p (List.mem_cons_self ..))), ← ih, Nat.add_comm]

/-- **an accepted root frame is valid** -/
theorem rootChk_sound {O : R3RT.SpecO.LabelOrder} {Ω : Dec22 → Prop} {c1 : ℕ} {c2T hkT : ℕ → ℕ} {pl : List ℕ}
    {lastP : ℕ} {f : ℕ × ℕ × ℕ × ℕ × ℕ} (hc1 : R3RT.SpecO.Conf1OK O Ω c1) (hc2 : ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l)) (h : rootChk c1 c2T hkT pl lastP f = true) :
    FrameOKO O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2 := by
  obtain ⟨S, D, N, U, d⟩ := f
  unfold rootChk at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hinc, hS⟩, hS511⟩, hlast⟩, hself⟩, hN⟩, hD⟩, hU⟩, hd⟩ := h
  have hS511' : S < 2 ^ 511 := by rwa [L5.shl_eq, Nat.shiftLeft_eq, one_mul] at hS511
  have hbit : ∀ q, S.testBit q = true ↔ q ∈ pl := by
    intro q; rw [hS, maskL_testBit]; simp
  have hpl511 : ∀ p ∈ pl, p < 511 := by
    intro p hp
    have := (hbit p).mpr hp
    by_contra hc; push Not at hc
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hS511' (Nat.pow_le_pow_right (by norm_num) hc))] at this
    exact absurd this (by decide)
  have hd' : d = pcnt511 S := by rw [hd, L5.pcnt_eq_card]; rfl
  subst hd'
  refine rootFrame_okO (by rwa [L5.shr_eq] at hlast) hS511' c1 hc1 c2T (fun p hp _ => hc2 p hp) ?_ ?_ ?_ ?_
  · intro p _ hSp w hw
    have := allB_spec hself p ((hbit p).mp hSp)
    simp only [Nat.beq_eq] at this
    have h2 : (Nat.land (Nat.shiftRight (c2T p) (Nat.mul 512 p)) M511).testBit w = false := by rw [this]; simp
    rw [L5.land_eq, Nat.testBit_and, R3RT.m511_bit, decide_eq_true hw, Bool.and_true, L5.shr_eq] at h2
    exact h2
  · intro v w hb
    rw [hN, Nat.testBit_shiftRight] at hb
    rcases rootN_testBit c1 c2T _ pl hb with h1 | ⟨p, hp, h1⟩
    · left; rw [Nat.testBit_shiftRight]; exact h1
    · right; exact ⟨p, hpl511 p hp, (hbit p).mpr hp, by rw [Nat.testBit_shiftRight]; exact h1⟩
  · intro l hl
    rw [hD] at hl
    obtain ⟨_, q, hq, h1⟩ := rootD_testBit hl
    exact ⟨q, hpl511 q hq, (hbit q).mpr hq, h1⟩
  · rw [hU, hS]; exact rootU_eq hh pl hinc hpl511

/-! ## The item under facts -/

/-- **the item theorem** (frames `FrameOKO O Ω`): an accepted root frame `f0` (prefix labels `pl`), a chain of accepted batches
from `[(f0, pend0)]` (the root's label `l0` pending) to a stack without pending labels give, under facts `H` that make the row
table, the cap-1 and cap-2 tables and the extension sound, a covered tree with root `(f0.1 ||| 2^l0, l0)` and external children
`extL` -/
theorem itemK_sound {E : Type} {O : R3RT.SpecO.LabelOrder} {Ω C : Dec22 → Prop} {np c2T hkT : ℕ → ℕ}
    {cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ} {extL : List (ℕ × ℕ)} {ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool} {acc xk : E → ℕ}
    (H : Prop) (hnp : NpOK O np) (hh : ∀ l, l < 511 → R3RT.SpecO.HOK O l (hkT l))
    (hcp : ∀ u, u < 511 → CPn (510 - u) (cpT u)) (hCΩ : ∀ A, C A → Ω A) (tab : ℕ → ℕ) (c1 : ℕ)
    (hT : H → TabOKO O Ω tab) (hc1 : H → R3RT.SpecO.Conf1OK O Ω c1) (hc2 : H → ∀ l, l < 511 → C2OKO O Ω l (c2T l))
    (hExt : H → ExtSound O Ω C ext acc)
    (pl : List ℕ) (lastP : ℕ) (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (hroot : rootChk c1 c2T hkT pl lastP f0 = true)
    (l0 pend0 : ℕ) (hp0 : pend0.testBit l0 = true) (out : List FrP)
    (hch : ChainK np c2T hkT cpT extL ext acc xk tab [(f0, pend0)] out) (hfin : pendZ out = true) :
    H → ∃ K, ItemCovK O C (f0.1 ||| 2 ^ l0, l0) K {e | e ∈ extL} := fun hH =>
  itemK_cov (Fr := fun f => FrameOKO O Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2) hnp (n5contract_frameOK O Ω)
    (fun _ _ _ _ _ hf => hf) tab (hT hH) (hc2 hH) hh hcp hCΩ (hExt hH) f0 (rootChk_sound (hc1 hH) (hc2 hH) hh hroot)
    l0 pend0 hp0 out hch hfin

end KD
