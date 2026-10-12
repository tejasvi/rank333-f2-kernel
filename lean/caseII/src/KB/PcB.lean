module
public import R22Port.U_d41d8cd98f00
public import KB.Defs
/-! # KB.PcB: a byte-table popcount for the root frames, and the fast root check

`KB.rootChkW` counts the prefix labels of every witness row with `L5.pcnt 511`, a 511-step recursion: about 44 ms of kernel time per
row, and a range item of case (I) carries about 257 witness rows. `pcB n x` adds byte popcounts from a 256-entry table `PC8` (4 bits
per entry): 64 steps for 512 bits.
* **`pcnt_eq_pcB`**: `L5.pcnt 511 x = pcB 64 x` for `x < 2^511`;
* `rootChkWF` / `rootChk0F`: `rootChkW` / `rootChk0` with `pcB 64` for `L5.pcnt 511`. **`rootChk0F_imp`**: an accepted fast check is an
  accepted `rootChk0`. The loader evaluates the fast check and states `rootChk0 … = true` through this lemma (no evaluation), so the
  item predicates are unchanged. -/
@[expose] public section
set_option maxRecDepth 10000
noncomputable section
namespace KB
open KD

/-- the popcounts of the bytes `0 .. 255`, 4 bits each -/
def PC8 : ℕ := 0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110
def pc8 (y : ℕ) : ℕ := Nat.mod (Nat.shiftRight PC8 (Nat.mul 4 y)) 16
/-- the popcount of the low `8 n` bits, by bytes -/
def pcB (n x : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (pc8 (Nat.mod (Nat.shiftRight x (Nat.mul 8 i)) 256))) n

theorem pc8_all : S5.allLT 256 (fun y => Nat.beq (pc8 y) (L5.pcnt 8 y)) = true := by decide +kernel

theorem pc8_eq (y : ℕ) (hy : y < 256) : pc8 y = L5.pcnt 8 y := Nat.eq_of_beq_eq_true (S5.allLT_spec pc8_all y hy)

theorem pcnt_add (m x : ℕ) : ∀ k, L5.pcnt (m + k) x = L5.pcnt m x + L5.pcnt k (x >>> m)
  | 0 => by simp [L5.pcnt_zero]
  | k + 1 => by
    rw [show m + (k + 1) = (m + k) + 1 by omega, L5.pcnt_succ, pcnt_add m x k, L5.pcnt_succ, Nat.testBit_shiftRight]
    omega

theorem pcnt_mod (x : ℕ) : ∀ k, L5.pcnt k (x % 2 ^ k) = L5.pcnt k x := by
  intro k
  have : ∀ j, j ≤ k → L5.pcnt j (x % 2 ^ k) = L5.pcnt j x := by
    intro j
    induction j with
    | zero => intro _; simp [L5.pcnt_zero]
    | succ j ih =>
      intro hj
      rw [L5.pcnt_succ, L5.pcnt_succ, ih (by omega), Nat.testBit_mod_two_pow]
      simp [show j < k by omega]
  exact this k le_rfl

theorem pcB_eq (x : ℕ) : ∀ n, pcB n x = L5.pcnt (8 * n) x
  | 0 => by simp [pcB, L5.pcnt_zero]
  | n + 1 => by
    show Nat.add (pcB n x) (pc8 (Nat.mod (Nat.shiftRight x (Nat.mul 8 n)) 256)) = _
    rw [pcB_eq x n, show 8 * (n + 1) = 8 * n + 8 by ring, pcnt_add (8 * n) x 8]
    have h256 : Nat.mod (Nat.shiftRight x (Nat.mul 8 n)) 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [pc8_eq _ h256, show Nat.mod (Nat.shiftRight x (Nat.mul 8 n)) 256 = (x >>> (8 * n)) % 2 ^ 8 from rfl, pcnt_mod]
    rfl

/-- **the byte popcount below `2^511`** -/
theorem pcnt_eq_pcB (x : ℕ) (hx : x < 2 ^ 511) : L5.pcnt 511 x = pcB 64 x := by
  rw [pcB_eq x 64]
  have h : L5.pcnt (8 * 64) x = L5.pcnt 511 x + (x.testBit 511).toNat := L5.pcnt_succ 511 x
  rw [h, Nat.testBit_lt_two_pow hx]; rfl

/-- `rootChkW` with the byte popcount -/
def rootChkWF (c1 : ℕ) (c2T hkT tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  incrL pl && Nat.beq f.1 (maskL (fun p => p) pl) && Nat.blt f.1 (Nat.shiftLeft 1 511) &&
  Nat.beq (Nat.shiftRight f.1 lastP) 1 && selfZ c2T pl &&
  Nat.beq f.2.2.1 (rootN c1 c2T pl) && Nat.beq f.2.1 (rootDW tab f.2.2.1 pl W) && Nat.beq f.2.2.2.1 (rootU hkT pl) &&
  Nat.beq f.2.2.2.2 (pcB 64 f.1) &&
  allB (fun w => Nat.beq (pcB 64 (Nat.land (tab w) f.1)) (Nat.mod (Nat.shiftRight (tab w) 511) 512)) W

/-- `rootChk0` with the byte popcount -/
def rootChk0F (c1 : ℕ) (c2T hkT tab : ℕ → ℕ) (pl W : List ℕ) (lastP : ℕ) (f : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  match pl with
  | [] => Nat.beq f.1 0 && Nat.beq f.2.1 0 && Nat.beq f.2.2.1 c1 && Nat.beq f.2.2.2.1 0 && Nat.beq f.2.2.2.2 0
  | _ :: _ => rootChkWF c1 c2T hkT tab pl W lastP f

theorem allB_mono {α : Type} {p q : α → Bool} (h : ∀ a, p a = true → q a = true) : ∀ {l : List α}, allB p l = true → allB q l = true
  | [], _ => rfl
  | a :: l, hl => by
    change (p a && allB p l) = true at hl
    change (q a && allB q l) = true
    rw [Bool.and_eq_true] at hl ⊢
    exact ⟨h a hl.1, allB_mono h hl.2⟩

theorem rootChkWF_imp {c1 : ℕ} {c2T hkT tab : ℕ → ℕ} {pl W : List ℕ} {lastP : ℕ} {f : ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : rootChkWF c1 c2T hkT tab pl W lastP f = true) : rootChkW c1 c2T hkT tab pl W lastP f = true := by
  unfold rootChkWF at h
  unfold rootChkW
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have hf : f.1 < 2 ^ 511 := by
    have := Nat.blt_eq.mp h3
    rwa [show Nat.shiftLeft 1 511 = 2 ^ 511 by rw [show Nat.shiftLeft 1 511 = 1 <<< 511 from rfl, Nat.shiftLeft_eq, one_mul]] at this
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, by rw [pcnt_eq_pcB _ hf]; exact h9⟩, allB_mono (fun w hw => ?_) h10⟩
  have hw' : Nat.land (tab w) f.1 < 2 ^ 511 := lt_of_le_of_lt (by
    show (tab w) &&& f.1 ≤ f.1; exact Nat.and_le_right) hf
  rw [pcnt_eq_pcB _ hw']; exact hw

/-- **an accepted fast root check is an accepted `rootChk0`** -/
theorem rootChk0F_imp {c1 : ℕ} {c2T hkT tab : ℕ → ℕ} {pl W : List ℕ} {lastP : ℕ} {f : ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : rootChk0F c1 c2T hkT tab pl W lastP f = true) : rootChk0 c1 c2T hkT tab pl W lastP f = true := by
  cases pl with
  | nil => exact h
  | cons p pl => exact rootChkWF_imp h

end KB
#print axioms KB.rootChk0F_imp
