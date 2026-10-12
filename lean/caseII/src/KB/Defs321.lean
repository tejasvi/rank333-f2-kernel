module
public import R22Port.U_d41d8cd98f00
public import KB.Defs
public import KB.DefsR
public import KB.Stat321
public import KB.StatII
public import KDK321.Ext
public import KDK321.Flook
public import KD321.Leaf
public import L5.O321
/-! # KB.Defs321: the kernel track's item check for cases (I) / (I13) under `--rord 321` (definitions)

The item predicate of `KB.CheckedK` (`KD.itemXS'` batches, the root frame `rootChk0`, a job table, the key's interface) at the
`--rord 321` order (`Top321.O`, hyperplane masks `RT.O321.lpar511`), with
* the label tables `KI321.c2T`, `KI321.hkT` (`KB.Stat321`), the cap-1 table `R22D.T321.CONF1T` and the window constants `KI.cpT`;
* R3's guarded per-job table over the 321 row interface `L5O.rowE321` (`TabV321`);
* **the 321 extension** `ext321K lo hi` of an OPEN node on its own frame, datum `(b, its, cs, dks, xm)`:
  - `KD321.ext321 lo hi` on `(b, its, cs)`: the suffix break, the PREFF / DOOM records (dead for `Ω ∩ CaseK lo hi`), the L3
    node records of the CANON children (`Top321.LABT321`);
  - `dkid321OK` for each dead child (a node without child loop): its frame5 record's rows from the job table (`withRec`), its
    cap-2 table and hit vector against the label tables, and its kind on the frame `frame5` computes: node cut 7
    (`KD321.cut7O`, the rank-1 window of the case), node cut 3 / leaf code 4 (`KD321.flookOKO` with the 321 tables, any tight list:
    `KB.Flook321`), leaf code 0 (the v7
    record `BC7s.leafS` bound to the 22 labels by `KD321.leafBindO KD321.lf321`);
  - `xm`: the external children (DON / JOB references, looked up in the item key by `KD.itemXS'`).
`acc321 e` is the label mask of the children the extension accounts for. -/
@[expose] public section
set_option maxHeartbeats 4000000
noncomputable section
namespace KB
open R3RT.SpecO KD

/-- the payload of a dead child at `--rord 321` -/
inductive DPay321 where
  | cut7
  | flook (t nT h2 : ℕ) (TL TY SL SY : List ℕ)
  | leaf (R : ℕ)

/-- a dead child: cap-2 table, hit vector, frame5 record header, rows (job-table indices by class 2 / 1 / 0), payload -/
abbrev DKid321 := ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ × DPay321

/-- the dead child's label -/
def dk321Lab (k : DKid321) : ℕ := Nat.land (Nat.shiftRight k.2.2.1 8) 511

/-- the kind's check on the frame `frame5` computes from the parent frame `(S, D, N, U, d)` and the child's record -/
def dpay321OK (lo hi : ℕ) (S D N U d c2 h rec : ℕ) : DPay321 → Bool
  | .cut7 => R3RT.frame5 S D N U d c2 h rec (fun S' D' _ _ =>
      KD321.cut7O KD321.R1M321 KD321.NR1M321 lo hi S' D' (Nat.succ d) (Nat.land (Nat.shiftRight rec 8) 511))
  | .flook t nT h2 TL TY SL SY => R3RT.frame5 S D N U d c2 h rec (fun S' D' _ U' =>
      KD321.flookOKO RT.O321.vecL RT.O321.lpar511 S' D' U' (Nat.succ d) (Nat.land (Nat.shiftRight rec 8) 511) t nT h2 TL TY SL SY)
  | .leaf R => BC7s.leafS R && R3RT.frame5 S D N U d c2 h rec (fun S' _ _ _ =>
      Nat.beq (Nat.succ d) 22 && KD321.leafBindO KD321.lf321 R S')

/-- **a dead child** of the OPEN node `(S, last)` with frame `(S, D, N, U, d)` -/
def dkid321OK (lo hi : ℕ) (c2T hkT tab : ℕ → ℕ) (S D N U d last : ℕ) (k : DKid321) : Bool :=
  Nat.blt last (dk321Lab k) && Nat.blt (dk321Lab k) 511 && Nat.beq k.1 (c2T (dk321Lab k)) && Nat.beq k.2.1 (hkT (dk321Lab k)) &&
  withRec tab k.2.2.1 k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 (fun rec => dpay321OK lo hi S D N U d k.1 k.2.1 rec k.2.2.2.2.2.2)

/-- the extension datum: suffix break, PREFF / DOOM records, L3 node records (CANON), dead children, external children -/
abbrev ExtD321 := ℕ × List ℕ × List ℕ × List DKid321 × ℕ

/-- **the 321 extension** of an OPEN node on its own frame -/
def ext321K (lo hi : ℕ) (c2T hkT tab : ℕ → ℕ) (S D N U d last : ℕ) (e : ExtD321) : Bool :=
  KD321.ext321 lo hi S D U d last (e.1, e.2.1, e.2.2.1) && allB (dkid321OK lo hi c2T hkT tab S D N U d last) e.2.2.2.1

/-- the CANON children of the node records (the 321 key table) -/
def canonM321 (cs : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun Sc _ acc => Nat.lor (KD321.canonKids Top321.LABT321 Sc) acc) cs

/-- **the children the extension accounts for** -/
def acc321 (e : ExtD321) : ℕ :=
  Nat.lor (Nat.lor (geM e.1) (maskL (fun it => Nat.land (Nat.shiftRight it 2) 511) e.2.1))
    (Nat.lor (canonM321 e.2.2.1) (maskL dk321Lab e.2.2.2.1))

/-- the external children -/
def xk321 (e : ExtD321) : ℕ := e.2.2.2.2

/-- the job table of a 321 item: R3's guarded per-job table over `L5O.rowE321` (`#r3tableQ`) -/
def TabV321 (tab : ℕ → ℕ) : Prop :=
  ∃ (chunk : ℕ → ℕ) (N nch : ℕ), (∀ i, tab i = (chunk (i / 64) >>> (552 * (i % 64))) % 2 ^ 552) ∧
    (∀ q, nch ≤ q → chunk q = 0) ∧ (∀ i, N ≤ i → tab i = 0) ∧ R3RT.tabOKQ L5O.rowE321 chunk 64 N nch = true

/-- the loader's job table is a `TabV321` table (as `KB.tabVII_of`, with the 321 row interface) -/
theorem tabV321_of (chunk : ℕ → ℕ) (N nch : ℕ) (entry : ℕ → ℕ)
    (hent : ∀ i, entry i = Nat.land (Nat.shiftRight (chunk (Nat.div i 64)) (Nat.mul 552 (Nat.mod i 64))) (2 ^ 552 - 1))
    (hch : ∀ q, nch ≤ q → chunk q = 0) (hnch : nch = (N + 63) / 64)
    (hlast : Nat.blt (chunk (nch - 1)) (2 ^ (552 * (N - 64 * (nch - 1)))) = true)
    (hok : R3RT.tabOKQ L5O.rowE321 chunk 64 N nch = true) : TabV321 entry := by
  have hent' : ∀ i, entry i = (chunk (i / 64) >>> (552 * (i % 64))) % 2 ^ 552 := by
    intro i; rw [hent i, L5.land_eq, L5.shr_eq, Nat.and_two_pow_sub_one_eq_mod]; rfl
  refine ⟨chunk, N, nch, hent', hch, fun i hi => ?_, hok⟩
  rw [hent' i]
  by_cases hq : nch ≤ i / 64
  · rw [hch _ hq, Nat.zero_shiftRight, Nat.zero_mod]
  · push Not at hq
    have h1 : 64 * nch ≤ N + 63 := by rw [hnch]; exact Nat.mul_div_le (N + 63) 64
    have hlo : 64 * (nch - 1) < N := by omega
    have hi64 : i / 64 = nch - 1 := by omega
    have hmod : N - 64 * (nch - 1) ≤ i % 64 := by omega
    rw [hi64]
    have hb := Nat.blt_eq.mp hlast
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by
      exact Nat.mul_le_mul_left 552 hmod))), Nat.zero_mod]

/-- **the kernel track's item predicate of case `(lo, hi)` under `--rord 321`** -/
abbrev CheckedK321 (lo hi : ℕ) : ℕ → Prop :=
  CheckedK RT.O321.lpar511 KI321.c2T KI321.hkT KI.cpT (fun tab => ext321K lo hi KI321.c2T KI321.hkT tab) acc321 xk321
    R22D.T321.CONF1T TabV321

/-! ## With ranges (queue items: split units leave range items, `KB.CheckedR`) -/

/-- the extension datum with the record's range start (`511`: no range reference) -/
abbrev ExtR321 := ExtD321 × ℕ

def ext321KR (lo hi : ℕ) (c2T hkT tab : ℕ → ℕ) (S D N U d last : ℕ) (e : ExtR321) : Bool :=
  ext321K lo hi c2T hkT tab S D N U d last e.1
def acc321R (e : ExtR321) : ℕ := acc321 e.1
def xk321R (e : ExtR321) : ℕ := xk321 e.1
def rg321R (e : ExtR321) : ℕ := e.2

/-- **the kernel track's item predicate of case `(lo, hi)` under `--rord 321`, with ranges** (`KB.CheckedR`: a range item's root
bound `lo` and its range children; an item without ranges has `lo = 0` and no range list) -/
abbrev CheckedR321 (lo hi : ℕ) : ℕ → Prop :=
  CheckedR RT.O321.lpar511 KI321.c2T KI321.hkT KI.cpT (fun tab => ext321KR lo hi KI321.c2T KI321.hkT tab) acc321R xk321R rg321R
    R22D.T321.CONF1T TabV321

end KB
