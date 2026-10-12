module
public import R22Port.U_d41d8cd98f00
public import KDK.ItemK
public import KDK.CutFrame
public import KD.Canon
public import KD321.Canon
public import L5.Bind5II
public import R22N.Glue
/-! # KB.Defs: the definitions of the kernel track's item check (light: no top-level skeleton imported)

The item checks (`KD.itemXS'` batches with the case-(II) extension `extII`, the root frame `rootChk0`, R3's job table `TabVII`)
and the item predicate `CheckedK` need only these definitions; the soundness proofs and the segment contract are in
`KB.ItemII` / `KB.ExtII` (which import `Top.TopL479`), so the per-item checking processes import this file and the tables only.

* `rootChk0`: the root's parent frame (the empty prefix's `(0, 0, c1, 0, 0)` for a depth-1 root, else `KD.rootChk`).
* `extII` (datum `ExtD = (b, its, cs, dks, xm)`), `accII`, `xkII`: the case-(II) extension of an OPEN node (`KB.ExtII`).
* `TabVII`: R3's guarded per-job table over `rowEII`; `tabVII_of` builds it from the loader's definitions (`guard_zero`).
* `CheckedK`: the item predicate; `AllBelow`: finite conjunctions (one proof term per index). -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000000
set_option maxRecDepth 100000
noncomputable section
namespace KB
open R3RT.SpecO KD
open R3RT (M511 foldR mkD)

/-- the dead labels of a root frame with witness rows `W` (job-table indices): the labels in conflict (`N`) with a prefix label,
and the labels of the witness rows -/
def rootDW (tab : ℕ → ℕ) (N : ℕ) (pl W : List ℕ) : ℕ :=
  Nat.land (Nat.lor (List.rec (motive := fun _ => ℕ) 0 (fun p _ acc => Nat.lor (Nat.shiftRight N (Nat.mul 512 p)) acc) pl)
    (List.rec (motive := fun _ => ℕ) 0 (fun w _ acc => Nat.lor (tab w) acc) W)) M511

/-- **the root's parent frame with witness rows**: as `KD.rootChk`, with dead labels from the conflicts and from witness rows of
the job table, each full at the prefix (its count of prefix labels equals its cap), as R3's state at a job or piece root holds them -/
def rootChkW (c1 : ℕ) (c2T hkT tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  incrL pl && Nat.beq f.1 (maskL (fun p => p) pl) && Nat.blt f.1 (Nat.shiftLeft 1 511) &&
  Nat.beq (Nat.shiftRight f.1 lastP) 1 && selfZ c2T pl &&
  Nat.beq f.2.2.1 (rootN c1 c2T pl) && Nat.beq f.2.1 (rootDW tab f.2.2.1 pl W) && Nat.beq f.2.2.2.1 (rootU hkT pl) &&
  Nat.beq f.2.2.2.2 (L5.pcnt 511 f.1) &&
  allB (fun w => Nat.beq (L5.pcnt 511 (Nat.land (tab w) f.1)) (Nat.mod (Nat.shiftRight (tab w) 511) 512)) W

/-- the root's parent frame: the empty prefix's `(0, 0, c1, 0, 0)` for a depth-1 root (`pl = []`), else `rootChkW` with the
witness rows `W` of the inherited dead labels (a piece root's #pcwit rows; none for a job root) -/
def rootChk0 (c1 : ℕ) (c2T hkT tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  match pl with
  | [] => Nat.beq f.1 0 && Nat.beq f.2.1 0 && Nat.beq f.2.2.1 c1 && Nat.beq f.2.2.2.1 0 && Nat.beq f.2.2.2.2 0
  | _ :: _ => rootChkW c1 c2T hkT tab pl W lastP f

/-- the payload of a node without child loop -/
inductive DPay where
  | cut (kind arg i : ℕ)
  | flook (t nT h2 : ℕ) (TL TY SL SY : List ℕ)
  | leaf (R : ℕ)
  /-- a node cut 5 / 6: its 27.11 certificate as a hybrid X part with one child, on its own dictionary (rows by job-table index,
  class 2 `x2`, class 1 `x1`) -/
  | xcut (x2 x1 nrows : List ℕ) (aggs : List Agg) (XL : List ℕ) (HP DEFP J : ℕ) (kid : KidX)

/-- a dead child: cap-2 table, hit vector, frame5 record header, rows (job-table indices by class 2 / 1 / 0), payload -/
abbrev DKid := ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ × DPay

/-- a record's rows fetched from the job table by index (as `KD.nodeXO`), then the continuation on the assembled record -/
def withRec (tab : ℕ → ℕ) (hdr : ℕ) (r2 r1 r0 : List ℕ) (k : ℕ → Bool) : Bool :=
  foldR tab 2 r2 0 0 0 0 (fun MB2 E2 b2 c2' =>
    foldR tab 1 r1 MB2 E2 b2 0 (fun MB1 E1 b1 c1' =>
      foldR tab 0 r0 MB1 E1 b1 0 (fun MB E bad c0' =>
        Nat.beq bad 0 && Nat.beq c2' (Nat.land (Nat.shiftRight hdr 52) 1023) &&
        Nat.beq c1' (Nat.land (Nat.shiftRight hdr 32) 1023) && Nat.beq c0' (Nat.land (Nat.shiftRight hdr 22) 1023) &&
        k (Nat.lor (Nat.land hdr 18446744073709551615)
          (Nat.shiftLeft (Nat.lor MB (Nat.shiftLeft E (Nat.mul 512 (Nat.add c0' (Nat.add c1' c2'))))) 64)))))

/-- the kind's check on the parent frame -/
def dpayOK (tab : ℕ → ℕ) (S D N U d c2 h rec : ℕ) : DPay → Bool
  | .cut kind arg i =>
    cutNode S D N U d c2 h rec kind arg (Nat.mod (tab i) (Nat.shiftLeft 1 511)) (Nat.mod (Nat.shiftRight (tab i) 511) 512)
  | .flook t nT h2 TL TY SL SY =>
    -- `KD.flookOK` on the frame frame5 builds, also with an empty tight list (sound for nonzero `b`, `c`)
    R3RT.frame5 S D N U d c2 h rec
      (fun S' D' _ U' => flookOK S' D' U' 0 (Nat.succ d) (Nat.land (Nat.shiftRight rec 8) 511) t nT h2 TL TY SL SY)
  | .leaf R => BC7s.leafS R && leafNode S D N U d c2 h rec R
  | .xcut _ _ _ _ _ _ _ _ _ => false

/-- **a node cut 5 / 6 as an X part** on the parent node `(S, last)` with frame `(S, D, N, U, d)`: the rows fetched from the job
table (as `KD.nodeXO`'s extras: class 2 `x2`, class 1 `x1`), L1's blocks of their counts at `S`, the static data of the child and
the aggregates, and `KD.xpartC` with this dictionary (`mkD 0 MBx 0`: residual 1 below `|x1|`, 2 above) and the one child -/
def xcutOK (np c2T : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (tab : ℕ → ℕ) (S D N U d last : ℕ) (x2 x1 nrows : List ℕ)
    (aggs : List Agg) (XL : List ℕ) (HP DEFP J : ℕ) (kid : KidX) : Bool :=
  foldR tab 2 x2 0 0 0 0 (fun MBx2 Ex2 bx2 _ =>
    foldR tab 1 x1 MBx2 Ex2 bx2 0 (fun MBx Ex badx cx' =>
      Nat.beq badx 0 && Nat.ble d 127 &&
      L1.blocks MBx Ex (Nat.mul S L1.REP63) (Nat.div (Nat.add (Nat.add cx' (List.length x2)) 62) 63) &&
      allB (aggStat c2T) aggs && kidStat c2T cpT kid &&
      xpartC np S D N U d last 0 0 cx' (mkD 0 MBx 0) nrows aggs XL HP DEFP J [kid]))

/-- the dead child's label -/
def dkLab (k : DKid) : ℕ := Nat.land (Nat.shiftRight k.2.2.1 8) 511

/-- **a dead child** of the node `(S, last)` with frame `(S, D, N, U, d)`: a node cut 5 / 6 by its X part on this frame, every
other kind on the child's frame5 frame -/
def dkidOK (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (tab : ℕ → ℕ) (S D N U d last : ℕ) (k : DKid) : Bool :=
  Nat.blt last (dkLab k) && Nat.blt (dkLab k) 511 && Nat.beq k.1 (c2T (dkLab k)) && Nat.beq k.2.1 (hkT (dkLab k)) &&
  match k.2.2.2.2.2.2 with
  | .xcut x2 x1 nrows aggs XL HP DEFP J kid =>
    Nat.beq kid.1 (dkLab k) && xcutOK np c2T cpT tab S D N U d last x2 x1 nrows aggs XL HP DEFP J kid
  | _ => withRec tab k.2.2.1 k.2.2.2.1 k.2.2.2.2.1 k.2.2.2.2.2.1 (fun rec => dpayOK tab S D N U d k.1 k.2.1 rec k.2.2.2.2.2.2)

/-! ## The extension -/

/-- the extension datum: suffix break, PREFF / DOOM / TYPE records, L3 node records (CANON), dead children, and the mask of
the external children (JOB / DON references, looked up in the item key by `KD.itemXS'`) -/
abbrev ExtD := ℕ × List ℕ × List ℕ × List DKid × ℕ

/-- **the case-(II) extension** of an OPEN node on its own frame -/
def extII (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (tab : ℕ → ℕ) (S D N U d last : ℕ) (e : ExtD) : Bool :=
  kindsNode S D U 0 d last e.1 e.2.1 && allB (fun Sc => KD321.canonNode C3.LABT Sc S) e.2.2.1 &&
  allB (dkidOK np c2T hkT cpT tab S D N U d last) e.2.2.2.1

/-- the CANON children of the node records -/
def canonM (cs : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun Sc _ acc => Nat.lor (KD321.canonKids C3.LABT Sc) acc) cs

/-- **the children the extension accounts for** -/
def accII (e : ExtD) : ℕ :=
  Nat.lor (Nat.lor (geM e.1) (maskL (fun it => Nat.land (Nat.shiftRight it 2) 511) e.2.1))
    (Nat.lor (canonM e.2.2.1) (maskL dkLab e.2.2.2.1))

/-- the external children -/
def xkII (e : ExtD) : ℕ := e.2.2.2.2

/-- the job table of a case-(II) item: R3's guarded per-job table over `rowEII` (`#r3tableQ`: `Pfx.chunk`, `Pfx.N`, `Pfx.tab_ok`) -/
def TabVII (tab : ℕ → ℕ) : Prop :=
  ∃ (chunk : ℕ → ℕ) (N nch : ℕ), (∀ i, tab i = (chunk (i / 64) >>> (552 * (i % 64))) % 2 ^ 552) ∧
    (∀ q, nch ≤ q → chunk q = 0) ∧ (∀ i, N ≤ i → tab i = 0) ∧ R3RT.tabOKQ L5II.rowEII chunk 64 N nch = true

theorem guard_zero (D : ℕ → ℕ) (nch q : ℕ) (hq : nch ≤ q) :
    Bool.rec (motive := fun _ => ℕ) 0 (D q) (Nat.blt q nch) = 0 := by
  have : Nat.blt q nch = false := by
    cases h : Nat.blt q nch
    · rfl
    · exact absurd (Nat.blt_eq.mp h) (by omega)
  rw [this]

theorem tabVII_of (chunk : ℕ → ℕ) (N nch : ℕ) (entry : ℕ → ℕ)
    (hent : ∀ i, entry i = Nat.land (Nat.shiftRight (chunk (Nat.div i 64)) (Nat.mul 552 (Nat.mod i 64))) (2 ^ 552 - 1))
    (hch : ∀ q, nch ≤ q → chunk q = 0) (hnch : nch = (N + 63) / 64)
    (hlast : Nat.blt (chunk (nch - 1)) (2 ^ (552 * (N - 64 * (nch - 1)))) = true)
    (hok : R3RT.tabOKQ L5II.rowEII chunk 64 N nch = true) : TabVII entry := by
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


/-- `P 0 ∧ … ∧ P (n - 1)` as a nested conjunction (kernel-friendly: one proof term per index) -/
def AllBelow (P : ℕ → Prop) (n : ℕ) : Prop := Nat.rec (motive := fun _ => Prop) True (fun k acc => acc ∧ P k) n

theorem allBelow_spec {P : ℕ → Prop} : ∀ {n : ℕ}, AllBelow P n → ∀ q, q < n → P q
  | 0, _, q, hq => absurd hq (Nat.not_lt_zero q)
  | n + 1, h, q, hq => by
    have h' : AllBelow P n ∧ P n := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact allBelow_spec h'.1 q hq
    · exact h'.2


/-- **the kernel track's item predicate**: a job table accepted by `TabV`, a root frame, a chain of accepted batches (the
extension `ext tab` may read the job table) and a final stack that fit the key -/
def CheckedK {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ)
    (ext : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk : E → ℕ) (c1 : ℕ) (TabV : (ℕ → ℕ) → Prop) (key : ℕ) :
    Prop :=
  ∃ (tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (l0 pend0 : ℕ) (extL : List (ℕ × ℕ))
    (out : List FrP),
    TabV tab ∧ rootChk0 c1 c2T hkT tab pl W lastP f0 = true ∧ pend0.testBit l0 = true ∧
    ChainK np c2T hkT cpT extL (ext tab) acc xk tab [(f0, pend0)] out ∧ pendZ out = true ∧
    (R22N.SegI.ofKey key).root = (f0.1 ||| 2 ^ l0, l0) ∧ (R22N.SegI.ofKey key).lo = 0 ∧
    (R22N.SegI.ofKey key).rng = [] ∧ (R22N.SegI.ofKey key).ext = extL


/-- **the item predicate of an item whose root is a dead node** (a node without child loop: cut, look-ahead, leaf, node cut 5 / 6): an
accepted job table, the root's parent frame (`rootChkW`, depth ≥ 2, with witness rows) and the root's dead-child record checked on
it (`dkidOK`), and the key's interface (root, `lo = 0`, no ranges, no external children) -/
def CheckedDeadK (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (c1 : ℕ) (TabV : (ℕ → ℕ) → Prop) (key : ℕ) : Prop :=
  ∃ (tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f0 : ℕ × ℕ × ℕ × ℕ × ℕ) (k : DKid),
    TabV tab ∧ rootChkW c1 c2T hkT tab pl W lastP f0 = true ∧
    dkidOK np c2T hkT cpT tab f0.1 f0.2.1 f0.2.2.1 f0.2.2.2.1 f0.2.2.2.2 lastP k = true ∧
    (R22N.SegI.ofKey key).root = (f0.1 ||| 2 ^ dkLab k, dkLab k) ∧ (R22N.SegI.ofKey key).lo = 0 ∧
    (R22N.SegI.ofKey key).rng = [] ∧ (R22N.SegI.ofKey key).ext = []

end KB
