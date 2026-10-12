module
public import R22Port.U_d41d8cd98f00
public import KDK.XComp
/-! # KDK.XComp2 (kinds-only name of KD.XComp2): a cheaper front end of the X part, reduced to `KD.xpartC` (K3 bookkeeping levers)

Profile of `KD.xpartC` on 192 records of the 436+422 sample (KB/ProfB.lean, in-process variants): X-steps 37%, the step validity
pass `xcOK` 13%, `fuX` and `crX` 10%, the child matrices 12%, the step list walk (pairs, projections, `hslot`) 8%.  Besides the
X-steps, most of this is kernel bookkeeping: `&&` and `||` (about 18 µs each), projections of step pairs, a second walk over the
steps.  This front end keeps every check and the X-steps themselves, and changes only how they are written:
* **packed steps** `w = d + 32 j` (`XC2`): a step is one literal, decoded by one `land` and one shift (no pair, no projection);
* **violation sums** instead of `&&` chains: a child's range tests, `F_u`, child rows and step bounds add up to one natural number
  `kidV`, and the child is checked by one `Nat.beq kidV 0`; a step's violation is `(1 - d) + ((d + [u ∈ H_j]) - DEF_j)`
  (truncated subtraction), an in-branch's is the distance between its aggregate's label and its pick, a child row's is
  `(1 - [residual ≤ 1]) (1 - [u ∈ row])`, with the residual-1 positions as one mask per node (`r1M`);
* **one walk** (`walk2`): the tree walk reads the packed steps and the aggregates directly (`toXT3c` is not built).

**`xpartC2_imp`**: an accepted `xpartC2` makes `xpartC` accept the same node with the trees unpacked (`XC2.toXC`), so
`xpartC2_soundO` follows from `xpartC_soundO`. -/
@[expose] public section
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000
noncomputable section
namespace KD
open K2 R3RT.Spec
open R3RT (M511)

/-- a hybrid tree with packed steps `d + 32 j` (`d < 32`): `XC` with one natural number per step -/
inductive XC2 where
  | leaf : List ℕ → ℕ → XC2
  | node : List ℕ → ℕ → ℕ → XC2 → XC2 → XC2
  | cut : XC2

def stD (w : ℕ) : ℕ := Nat.land w 31
def stJ (w : ℕ) : ℕ := Nat.shiftRight w 5

def unpackL (sts : List ℕ) : List (ℕ × ℕ) :=
  List.rec (motive := fun _ => List (ℕ × ℕ)) [] (fun w _ ih => (stJ w, stD w) :: ih) sts

/-- the unpacked tree -/
def XC2.toXC : XC2 → XC
  | .leaf sts fin => .leaf (unpackL sts) (stJ fin, stD fin)
  | .node sts v k l r => .node (unpackL sts) v k l.toXC r.toXC
  | .cut => .cut

/-! ## Violation sums -/

/-- a step's violation: 0 iff `1 ≤ d` and `d + [u ∈ H_j] ≤ DEF_j` -/
def stV (HP DEFP u w : ℕ) : ℕ :=
  Nat.add (Nat.sub 1 (stD w)) (Nat.sub (Nat.add (stD w) (bitAt (hslot HP (stJ w)) u)) (byteAt DEFP (stJ w)))

def stsV (HP DEFP u : ℕ) (sts : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add (stV HP DEFP u w) ih) sts

/-- 0 iff `a = b` -/
def distN (a b : ℕ) : ℕ := Nat.add (Nat.sub a b) (Nat.sub b a)

/-- the tree's violation: its steps, and every in-branch's aggregate label against its pick -/
def xcV (HP DEFP u : ℕ) (aggs : List Agg) (t : XC2) : ℕ :=
  XC2.rec (motive := fun _ => ℕ)
    (fun sts fin => Nat.add (stsV HP DEFP u sts) (stV HP DEFP u fin))
    (fun sts v k _ _ ihl ihr =>
      Nat.add (Nat.add (stsV HP DEFP u sts) (distN (aggAt aggs k).1 (Nat.add (Nat.succ u) v))) (Nat.add ihl ihr))
    0 t

/-- the node's residual-1 positions `[0, b1) ∪ [m, e1)` as a mask -/
def r1M (b1 m e1 : ℕ) : ℕ := Nat.lor (Nat.sub (Nat.shiftLeft 1 b1) 1) (Nat.sub (Nat.shiftLeft 1 e1) (Nat.shiftLeft 1 m))

def r1b (R1M p : ℕ) : ℕ := Nat.land (Nat.shiftRight R1M p) 1

/-- the child rows' violation: 0 iff each has residual ≤ 1 or holds `u` -/
def crV (mk : ℕ → ℕ) (R1M u : ℕ) (cr : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun p _ ih => Nat.add (Nat.mul (Nat.sub 1 (r1b R1M p)) (Nat.sub 1 (bitAt (mk p) u))) ih) cr

/-- `F_u` from the frame, as `fuX` computes it -/
def fuC (D Anode u : ℕ) : ℕ :=
  andn (andn (Nat.sub (Nat.shiftLeft 1 511) (Nat.shiftLeft 1 (Nat.add u 1))) D) (rowA 512 Anode u)

/-! ## The walk on packed steps -/

def runS2 (NA REP GRD LOWS MODM o HP : ℕ) (sts : List ℕ) (c : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun c => c)
    (fun w _ ih c => ih (xstepL NA REP GRD LOWS MODM c (Nat.shiftRight (hslot HP (stJ w)) o) (stD w))) sts c

/-- `K2.checkXT3L` on `toXT3c HP aggs t.toXC`, read directly from the packed tree -/
def walk2 (REP GRD LOWS MODM S TOP o T HP : ℕ) (aggs : List Agg) (t : XC2) : ℕ → ℕ → ℕ → Bool :=
  XC2.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool)
    (fun sts fin NA c _ =>
      fewerB (Nat.land (runS2 NA REP GRD LOWS MODM o HP sts c) (Nat.shiftRight (hslot HP (stJ fin)) o)) (stD fin))
    (fun sts v k _ _ ihl ihr NA c P =>
      brk3L ihl ihr NA (andn NA (Nat.shiftRight (aggAt aggs k).2.2.1 (Nat.add (Nat.mul S o) o))) v S TOP
        (runS2 NA REP GRD LOWS MODM o HP sts c) P)
    (fun _ _ P => overB P T) t

/-- `K2.childL4X` without child rows of its own (as `kidX` calls it), on the packed tree -/
def childL4X2 (REPm REP GRD LOWS MODM DIAG ALL S TOP o T Anode C2u Fu HP : ℕ) (aggs : List Agg) (t : XC2) : Bool :=
  walk2 REP GRD LOWS MODM S TOP o T HP aggs t
    (Nat.lor (Nat.xor ALL (addCl (Nat.shiftRight (Nat.lor Anode C2u) (Nat.add (Nat.mul S o) o)) REPm REP (shiftL o []))) DIAG)
    (Nat.land (Nat.shiftRight Fu o) (Nat.sub TOP 1)) 0

/-! ## Children and the X part -/

/-- a child with a packed tree: `(u, F_u, child-row positions, tree, c2t_u, (REP, REPm, GRD, LOWS, DIAG))` -/
abbrev KidX2 := ℕ × ℕ × List ℕ × XC2 × ℕ × (ℕ × ℕ × ℕ × ℕ × ℕ)

def KidX2.toKidX (c : KidX2) : KidX := (c.1, c.2.1, c.2.2.1, c.2.2.2.1.toXC, c.2.2.2.2.1, c.2.2.2.2.2)

/-- the child's violation sum -/
def kidV (D last R1M Anode HP DEFP : ℕ) (mk : ℕ → ℕ) (aggs : List Agg) (c : KidX2) : ℕ :=
  Nat.add (Nat.add (Nat.sub (Nat.succ last) c.1) (Nat.sub (Nat.succ c.1) 511))
    (Nat.add (Nat.xor c.2.1 (fuC D Anode c.1)) (Nat.add (crV mk R1M c.1 c.2.2.1) (xcV HP DEFP c.1 aggs c.2.2.2.1)))

/-- **the child check** (`kidX` with the front end above) -/
def kidX2 (D last R1M Anode HP DEFP T : ℕ) (mk : ℕ → ℕ) (aggs : List Agg) (c : KidX2) : Bool :=
  Nat.beq (kidV D last R1M Anode HP DEFP mk aggs c) 0 &&
  childL4X2 c.2.2.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.1 M511 c.2.2.2.2.2.2.2.2.2
    (Nat.mul c.2.2.2.2.2.1 (Nat.sub (Nat.shiftLeft 1 (Nat.sub 510 c.1)) 1)) 512
    (Nat.shiftLeft 1 (Nat.sub 510 c.1)) (Nat.succ c.1) T (K2.addCl Anode REPmF REPF (R3RT.mapL mk c.2.2.1)) c.2.2.2.2.1 c.2.1 HP
    aggs c.2.2.2.1

def kidsX2 (D last R1M Anode HP DEFP T : ℕ) (mk : ℕ → ℕ) (aggs : List Agg) (ks : List KidX2) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => kidX2 D last R1M Anode HP DEFP T mk aggs c && ih) ks

/-- **the X part of a node** (as `xpartC`, children with packed trees) -/
def xpartC2 (np : ℕ → ℕ) (S D N U du last b1 m e1 : ℕ) (mk : ℕ → ℕ) (nrows : List ℕ) (aggs : List Agg) (XL : List ℕ)
    (HP DEFP J : ℕ) (kids : List KidX2) : Bool :=
  nrOK b1 m e1 nrows && aggsX mk aggs && dtOK np U du HP DEFP J XL 0 && Nat.blt DEFP (Nat.shiftLeft 1 (Nat.mul 8 J)) &&
    kidsX2 D last (r1M b1 m e1) (anodeX N mk nrows) HP DEFP (Nat.sub 21 du) mk aggs kids

/-! ## Reduction to `xpartC` -/

theorem add_eq_zero' {a b : ℕ} (h : Nat.add a b = 0) : a = 0 ∧ b = 0 := Nat.add_eq_zero_iff.mp h

theorem xor_eq_zero' {a b : ℕ} (h : Nat.xor a b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => Nat.testBit x i) h
  simp only [Nat.zero_testBit] at h1
  change (a ^^^ b).testBit i = false at h1
  rw [Nat.testBit_xor] at h1
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem stV_ok {HP DEFP J u w : ℕ} (h : stV HP DEFP u w = 0) : stepC HP DEFP J u (stJ w, stD w) = true := by
  obtain ⟨h1, h2⟩ := add_eq_zero' h
  have hd : 1 ≤ stD w := by have := Nat.sub_eq_zero_iff_le.mp h1; omega
  have hb := Nat.sub_eq_zero_iff_le.mp h2
  unfold stepC
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
  exact ⟨by omega, hb⟩

theorem stsV_ok {HP DEFP J u : ℕ} : ∀ {sts : List ℕ}, stsV HP DEFP u sts = 0 → stepsCOK HP DEFP J u (unpackL sts) = true
  | [], _ => rfl
  | w :: sts, h => by
    obtain ⟨h1, h2⟩ := add_eq_zero' h
    change (stepC HP DEFP J u (stJ w, stD w) && stepsCOK HP DEFP J u (unpackL sts)) = true
    rw [stV_ok h1, stsV_ok h2]; rfl

theorem distN_eq {a b : ℕ} (h : distN a b = 0) : a = b := by
  obtain ⟨h1, h2⟩ := add_eq_zero' h
  have := Nat.sub_eq_zero_iff_le.mp h1; have := Nat.sub_eq_zero_iff_le.mp h2; omega

theorem xcV_ok {HP DEFP J u : ℕ} {aggs : List Agg} : ∀ (t : XC2), xcV HP DEFP u aggs t = 0 → xcOK HP DEFP J u aggs t.toXC = true
  | .leaf sts fin, h => by
    obtain ⟨h1, h2⟩ := add_eq_zero' h
    change (stepsCOK HP DEFP J u (unpackL sts) && stepC HP DEFP J u (stJ fin, stD fin)) = true
    rw [stsV_ok h1, stV_ok h2]; rfl
  | .node sts v k l r, h => by
    obtain ⟨h12, h34⟩ := add_eq_zero' h
    obtain ⟨h1, h2⟩ := add_eq_zero' h12
    obtain ⟨h3, h4⟩ := add_eq_zero' h34
    change (stepsCOK HP DEFP J u (unpackL sts) && Nat.beq (aggAt aggs k).1 (Nat.add (Nat.succ u) v) &&
      xcOK HP DEFP J u aggs l.toXC && xcOK HP DEFP J u aggs r.toXC) = true
    rw [stsV_ok h1, distN_eq h2, xcV_ok l h3, xcV_ok r h4, Nat.beq_refl]; rfl
  | .cut, _ => rfl

theorem testBit_r1M {b1 m e1 p : ℕ} (h : (r1M b1 m e1).testBit p = true) : p < b1 ∨ (m ≤ p ∧ p < e1) := by
  unfold r1M at h
  change ((1 <<< b1 - 1) ||| (1 <<< e1 - 1 <<< m)).testBit p = true at h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · left; rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one] at h; simpa using h
  · right
    by_cases hme : m ≤ e1
    · have he : 1 <<< e1 - 1 <<< m = (2 ^ (e1 - m) - 1) <<< m := by
        rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add, Nat.one_mul, Nat.sub_add_cancel hme]
      rw [he, Nat.testBit_shiftLeft, Bool.and_eq_true, Nat.testBit_two_pow_sub_one] at h
      simp only [ge_iff_le, decide_eq_true_eq] at h
      omega
    · have : 1 <<< e1 - 1 <<< m = 0 := by
        rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
        exact Nat.sub_eq_zero_of_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [this, Nat.zero_testBit] at h; exact absurd h (by simp)

theorem r1b_ok {b1 m e1 p : ℕ} (h : Nat.sub 1 (r1b (r1M b1 m e1) p) = 0) : r1pos b1 m e1 p = true := by
  have h1 : 1 ≤ r1b (r1M b1 m e1) p := Nat.sub_eq_zero_iff_le.mp h
  have hb : (r1M b1 m e1).testBit p = true := by
    unfold r1b at h1
    change 1 ≤ (r1M b1 m e1 >>> p) &&& 1 at h1
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at h1
    have : r1M b1 m e1 / 2 ^ p % 2 = 1 := by omega
    simp [this]
  unfold r1pos
  rcases testBit_r1M hb with h2 | ⟨h2, h3⟩
  · simp [Nat.blt_eq, h2]
  · simp [Nat.blt_eq, Nat.ble_eq, h2, h3]

theorem bitAt_le (m u : ℕ) : bitAt m u ≤ 1 := by
  unfold bitAt; change (m >>> u) &&& 1 ≤ 1; exact Nat.and_le_right

theorem crV_ok {mk : ℕ → ℕ} {b1 m e1 u : ℕ} : ∀ {cr : List ℕ}, crV mk (r1M b1 m e1) u cr = 0 → crX mk b1 m e1 u cr = true
  | [], _ => rfl
  | p :: cr, h => by
    obtain ⟨h1, h2⟩ := add_eq_zero' h
    change ((r1pos b1 m e1 p || Nat.beq (bitAt (mk p) u) 1) && crX mk b1 m e1 u cr) = true
    rw [crV_ok h2, Bool.and_true]
    rcases Nat.mul_eq_zero.mp h1 with h3 | h3
    · rw [r1b_ok h3]; rfl
    · have h4 : bitAt (mk p) u = 1 := by have := Nat.sub_eq_zero_iff_le.mp h3; have := bitAt_le (mk p) u; omega
      rw [h4, Bool.or_eq_true]; right; rfl

theorem runS2_eq (NA REP GRD LOWS MODM o HP : ℕ) : ∀ (sts : List ℕ) (c : ℕ),
    runS2 NA REP GRD LOWS MODM o HP sts c = runSoL NA REP GRD LOWS MODM o (stepsC HP (unpackL sts)) c
  | [], _ => rfl
  | w :: sts, c => by
    change runS2 NA REP GRD LOWS MODM o HP sts (xstepL NA REP GRD LOWS MODM c (Nat.shiftRight (hslot HP (stJ w)) o) (stD w)) =
      runSoL NA REP GRD LOWS MODM o (stepsC HP (unpackL sts)) (xstepL NA REP GRD LOWS MODM c (Nat.shiftRight (hslot HP (stJ w)) o) (stD w))
    exact runS2_eq NA REP GRD LOWS MODM o HP sts _

theorem walk2_eq (REP GRD LOWS MODM S TOP o T HP : ℕ) (aggs : List Agg) : ∀ (t : XC2),
    walk2 REP GRD LOWS MODM S TOP o T HP aggs t = checkXT3L REP GRD LOWS MODM S TOP o T (toXT3c HP aggs t.toXC)
  | .leaf sts fin => by
    funext NA c P
    change fewerB (Nat.land (runS2 NA REP GRD LOWS MODM o HP sts c) (Nat.shiftRight (hslot HP (stJ fin)) o)) (stD fin) =
      fewerB (Nat.land (runSoL NA REP GRD LOWS MODM o (stepsC HP (unpackL sts)) c) (Nat.shiftRight (hslot HP (stJ fin)) o)) (stD fin)
    rw [runS2_eq]
  | .node sts v k l r => by
    funext NA c P
    have hl := walk2_eq REP GRD LOWS MODM S TOP o T HP aggs l
    have hr := walk2_eq REP GRD LOWS MODM S TOP o T HP aggs r
    change brk3L (walk2 REP GRD LOWS MODM S TOP o T HP aggs l) (walk2 REP GRD LOWS MODM S TOP o T HP aggs r) NA
        (andn NA (Nat.shiftRight (aggAt aggs k).2.2.1 (Nat.add (Nat.mul S o) o))) v S TOP
        (runS2 NA REP GRD LOWS MODM o HP sts c) P =
      brk3L (checkXT3L REP GRD LOWS MODM S TOP o T (toXT3c HP aggs l.toXC))
        (checkXT3L REP GRD LOWS MODM S TOP o T (toXT3c HP aggs r.toXC)) NA
        (andn NA (Nat.shiftRight (aggAt aggs k).2.2.1 (Nat.add (Nat.mul S o) o))) v S TOP
        (runSoL NA REP GRD LOWS MODM o (stepsC HP (unpackL sts)) c) P
    rw [hl, hr, runS2_eq]
  | .cut => rfl

theorem childL4X2_eq (REPm REP GRD LOWS MODM DIAG ALL S TOP o T Anode C2u Fu HP : ℕ) (aggs : List Agg) (t : XC2) :
    childL4X2 REPm REP GRD LOWS MODM DIAG ALL S TOP o T Anode C2u Fu HP aggs t =
      childL4X REPm REP GRD LOWS MODM DIAG ALL S TOP o T Anode C2u Fu [] (toXT3c HP aggs t.toXC) := by
  unfold childL4X2 childL4X
  rw [walk2_eq]; rfl

theorem kidX2_imp {D last b1 m e1 Anode HP DEFP J T : ℕ} {mk : ℕ → ℕ} {aggs : List Agg} {c : KidX2}
    (h : kidX2 D last (r1M b1 m e1) Anode HP DEFP T mk aggs c = true) :
    kidX D last b1 m e1 Anode HP DEFP J T mk aggs c.toKidX = true := by
  obtain ⟨u, Fu, cr, t, C2u, cs⟩ := c
  unfold kidX2 at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hV, hW⟩ := h
  unfold kidV at hV
  obtain ⟨hab, hcd⟩ := add_eq_zero' hV
  obtain ⟨ha, hb⟩ := add_eq_zero' hab
  obtain ⟨hc, hd⟩ := add_eq_zero' hcd
  obtain ⟨he, hf⟩ := add_eq_zero' hd
  have hlu : last < u := by have := Nat.sub_eq_zero_iff_le.mp ha; simp only at this; omega
  have hu : u < 511 := by have := Nat.sub_eq_zero_iff_le.mp hb; simp only at this; omega
  have hfu : Fu = fuC D Anode u := xor_eq_zero' hc
  have hbeq : Nat.beq Fu (fuC D Anode u) = true := by rw [hfu]; exact Nat.beq_refl _
  change (Nat.blt last u && Nat.blt u 511 && Nat.beq Fu (fuC D Anode u) && crX mk b1 m e1 u cr &&
    xcOK HP DEFP J u aggs t.toXC && _) = true
  rw [Nat.blt_eq.mpr hlu, Nat.blt_eq.mpr hu, hbeq, crV_ok he, xcV_ok t hf]
  simp only [Bool.true_and]
  change childL4X2 _ _ _ _ M511 _ _ 512 _ (Nat.succ u) T _ C2u Fu HP aggs t = true at hW
  rw [childL4X2_eq] at hW
  exact hW

theorem kidsX2_imp {D last b1 m e1 Anode HP DEFP J T : ℕ} {mk : ℕ → ℕ} {aggs : List Agg} :
    ∀ {ks : List KidX2}, kidsX2 D last (r1M b1 m e1) Anode HP DEFP T mk aggs ks = true →
      kidsX D last b1 m e1 Anode HP DEFP J T mk aggs (ks.map KidX2.toKidX) = true
  | [], _ => rfl
  | c :: ks, h => by
    change (kidX2 D last (r1M b1 m e1) Anode HP DEFP T mk aggs c && kidsX2 D last (r1M b1 m e1) Anode HP DEFP T mk aggs ks) = true at h
    rw [Bool.and_eq_true] at h
    change (kidX D last b1 m e1 Anode HP DEFP J T mk aggs c.toKidX && kidsX D last b1 m e1 Anode HP DEFP J T mk aggs (ks.map KidX2.toKidX)) = true
    rw [kidX2_imp h.1, kidsX2_imp h.2]; rfl

/-- **`xpartC2` reduces to `xpartC`** on the unpacked trees -/
theorem xpartC2_imp {np : ℕ → ℕ} {S D N U du last b1 m e1 : ℕ} {mk : ℕ → ℕ} {nrows : List ℕ} {aggs : List Agg} {XL : List ℕ}
    {HP DEFP J : ℕ} {kids : List KidX2}
    (h : xpartC2 np S D N U du last b1 m e1 mk nrows aggs XL HP DEFP J kids = true) :
    xpartC np S D N U du last b1 m e1 mk nrows aggs XL HP DEFP J (kids.map KidX2.toKidX) = true := by
  unfold xpartC2 at h
  unfold xpartC
  rw [Bool.and_eq_true] at h
  rw [kidsX2_imp h.2, Bool.and_true]
  exact h.1

/-- **Soundness of `xpartC2`**: every listed child is dead -/
theorem xpartC2_soundO {O : R3RT.SpecO.LabelOrder} {Ω : Dec22 → Prop} {np : ℕ → ℕ} {S D N U du last b1 m e1 HP DEFP J : ℕ}
    {mk : ℕ → ℕ} {nrows : List ℕ} {aggs : List Agg} {XL : List ℕ} {kids : List KidX2}
    (hF : FrameOKO O Ω S D N U du) (hS : S >>> last = 1) (hD : DictSemXO O Ω S last mk (rposB b1 m e1))
    (hmk : ∀ p, mk p < 2 ^ 511)
    (hagg : ∀ ag ∈ aggs, C2OKO O Ω ag.1 ag.2.1) (hkids : ∀ c ∈ kids, KidXOKO O Ω c.toKidX)
    (hnp : NpOK O np) (h : xpartC2 np S D N U du last b1 m e1 mk nrows aggs XL HP DEFP J kids = true) :
    ∀ c ∈ kids, ∀ A : Dec22, Ω A → ¬ R3RT.SpecO.Continues O A S last c.1 := by
  intro c hc
  have := xpartC_soundO hF hS hD hmk hagg (fun c' hc' => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc'; exact hkids y hy) hnp (xpartC2_imp h)
  exact this c.toKidX (List.mem_map.mpr ⟨c, hc, rfl⟩)

end KD
