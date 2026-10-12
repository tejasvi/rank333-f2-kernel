module
public import R22Port.U_d41d8cd98f00
public import E1.Asm
public import E1.AsmG
public import E1.AsmN
/-! # G2.Asm2: block and glue checks of a long chain through an O(log n) lookup

`E1S.blkChk` and `E1S.glueChkR` (E1.Asm/AsmG; E1.AsmN's recursor forms) reach block `k` of the chain `Ss` by walking the list,
O(k) per access; for the 182,520 blocks of class 303 that walk costs seconds per block. Here the blocks and the witness rows
are read through functions `f : ℕ → ℕ` and `fw : ℕ → List ℕ` (binary dispatchers, O(log n) kernel steps; G2.WLoad's `#g2f`,
`#g2w`), tied to the lists once for the whole chain:
* `eqL Ss (gen f N 0) = true` (one walk over `Ss`) gives `Ss.getD k 0 = f k` for `k < N` (`getD_of_eqL`), and
  `eqLL W (genW fw N 0) = true` gives `W.getD k [] = fw k` (`getDW_of_eqLL`);
* `blkChkF_eq`: `blkChkF C sl UB UBR f a m = blkChk C sl UB UBR Ss a m`; `glueChkRF_eq`: `glueChkRF f fw N a m = glueChkR Ss W a m`
  (`N = Ss.length`, `a + m ≤ N`).
So a chain's block modules keep their statements (`okM`: `blkChk … lits ga gm = true`, `okG`: `glueChkR lits W ga gm = true`)
and the chain module is unchanged. -/
@[expose] public section
namespace G2A
open E1S

/-- `[f k, f (k+1), …, f (k+n-1)]`, by one recursor -/
def gen (f : ℕ → ℕ) (n : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => []) (fun _ ih k => f k :: ih (k + 1)) n

theorem gen_getD (f : ℕ → ℕ) : ∀ (n k i : ℕ), i < n → (gen f n k).getD i 0 = f (k + i) := by
  intro n
  induction n with
  | zero => intro k i hi; omega
  | succ n ih =>
    intro k i hi
    cases i with
    | zero => rfl
    | succ i =>
      show (gen f n (k + 1)).getD i 0 = f (k + (i + 1))
      rw [ih (k + 1) i (by omega)]; congr 1; omega

/-- the rows `[fw k, …, fw (k+n-1)]` -/
def genW (fw : ℕ → List ℕ) (n : ℕ) : ℕ → List (List ℕ) :=
  Nat.rec (motive := fun _ => ℕ → List (List ℕ)) (fun _ => []) (fun _ ih k => fw k :: ih (k + 1)) n

theorem genW_getD (fw : ℕ → List ℕ) : ∀ (n k i : ℕ), i < n → (genW fw n k).getD i [] = fw (k + i) := by
  intro n
  induction n with
  | zero => intro k i hi; omega
  | succ n ih =>
    intro k i hi
    cases i with
    | zero => rfl
    | succ i =>
      show (genW fw n (k + 1)).getD i [] = fw (k + (i + 1))
      rw [ih (k + 1) i (by omega)]; congr 1; omega

/-- equality of `ℕ` lists, by one recursor walk -/
def eqL : List ℕ → List ℕ → Bool :=
  @List.rec ℕ (fun _ => List ℕ → Bool) (fun l => @List.rec ℕ (fun _ => Bool) true (fun _ _ _ => false) l)
    (fun a _ ih l => @List.rec ℕ (fun _ => Bool) false (fun b t _ => Nat.beq a b && ih t) l)

theorem eqL_spec : ∀ (a b : List ℕ), eqL a b = true → a = b := by
  intro a
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons _ _ => exact absurd h Bool.false_ne_true
  | cons x a ih => intro b h; cases b with
    | nil => exact absurd h Bool.false_ne_true
    | cons y b =>
      have h' : (Nat.beq x y && eqL a b) = true := h
      rw [Bool.and_eq_true] at h'
      rw [Nat.eq_of_beq_eq_true h'.1, ih b h'.2]

/-- equality of lists of `ℕ` lists -/
def eqLL : List (List ℕ) → List (List ℕ) → Bool :=
  @List.rec (List ℕ) (fun _ => List (List ℕ) → Bool) (fun l => @List.rec (List ℕ) (fun _ => Bool) true (fun _ _ _ => false) l)
    (fun a _ ih l => @List.rec (List ℕ) (fun _ => Bool) false (fun b t _ => eqL a b && ih t) l)

theorem eqLL_spec : ∀ (a b : List (List ℕ)), eqLL a b = true → a = b := by
  intro a
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons _ _ => exact absurd h Bool.false_ne_true
  | cons x a ih => intro b h; cases b with
    | nil => exact absurd h Bool.false_ne_true
    | cons y b =>
      have h' : (eqL x y && eqLL a b) = true := h
      rw [Bool.and_eq_true] at h'
      rw [eqL_spec x y h'.1, ih b h'.2]

theorem getD_of_eqL {Ss : List ℕ} {f : ℕ → ℕ} {N : ℕ} (h : eqL Ss (gen f N 0) = true) (k : ℕ) (hk : k < N) :
    Ss.getD k 0 = f k := by
  rw [eqL_spec _ _ h, gen_getD f N 0 k hk, Nat.zero_add]

theorem getDW_of_eqLL {W : List (List ℕ)} {fw : ℕ → List ℕ} {N : ℕ} (h : eqLL W (genW fw N 0) = true) (k : ℕ) (hk : k < N) :
    W.getD k [] = fw k := by
  rw [eqLL_spec _ _ h, genW_getD fw N 0 k hk, Nat.zero_add]

theorem getD_take_of_lt {α : Type} (l : List α) (n k : ℕ) (d : α) (hk : k < n) : (l.take n).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- as `getD_of_eqL` through `Ss.take N` (the kernel walks `Ss.take N` in linear time, `Ss` itself much slower) -/
theorem getD_of_eqL_take {Ss : List ℕ} {f : ℕ → ℕ} {N : ℕ} (h : eqL (Ss.take N) (gen f N 0) = true) (k : ℕ) (hk : k < N) :
    Ss.getD k 0 = f k := by
  rw [← getD_take_of_lt Ss N k 0 hk]; exact getD_of_eqL h k hk

theorem getDW_of_eqLL_take {W : List (List ℕ)} {fw : ℕ → List ℕ} {N : ℕ} (h : eqLL (W.take N) (genW fw N 0) = true) (k : ℕ)
    (hk : k < N) : W.getD k [] = fw k := by
  rw [← getD_take_of_lt W N k [] hk]; exact getDW_of_eqLL h k hk

theorem getD_drop' {α : Type} (l : List α) (a i : ℕ) (d : α) : (l.drop a).getD i d = l.getD (a + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- one chunk `a .. a+m-1` of the chain agrees with `f` (the kernel walks short chunks fast; one walk over a long list in
lockstep with `gen` is much slower than linear) -/
theorem getD_of_chunk {Ss : List ℕ} {f : ℕ → ℕ} {a m : ℕ} (h : eqL ((Ss.drop a).take m) (gen f m a) = true) (k : ℕ) (ha : a ≤ k)
    (hk : k < a + m) : Ss.getD k 0 = f k := by
  have e := eqL_spec _ _ h
  have h1 : ((Ss.drop a).take m).getD (k - a) 0 = (gen f m a).getD (k - a) 0 := by rw [e]
  rw [getD_take_of_lt _ _ _ _ (by omega), getD_drop', gen_getD f m a (k - a) (by omega), Nat.add_sub_cancel' ha] at h1
  exact h1

theorem getDW_of_chunk {W : List (List ℕ)} {fw : ℕ → List ℕ} {a m : ℕ} (h : eqLL ((W.drop a).take m) (genW fw m a) = true) (k : ℕ)
    (ha : a ≤ k) (hk : k < a + m) : W.getD k [] = fw k := by
  have e := eqLL_spec _ _ h
  have h1 : ((W.drop a).take m).getD (k - a) [] = (genW fw m a).getD (k - a) [] := by rw [e]
  rw [getD_take_of_lt _ _ _ _ (by omega), getD_drop', genW_getD fw m a (k - a) (by omega), Nat.add_sub_cancel' ha] at h1
  exact h1

theorem getD_join {Ss : List ℕ} {f : ℕ → ℕ} {a b c : ℕ} (h1 : ∀ k, a ≤ k → k < b → Ss.getD k 0 = f k)
    (h2 : ∀ k, b ≤ k → k < c → Ss.getD k 0 = f k) : ∀ k, a ≤ k → k < c → Ss.getD k 0 = f k := by
  intro k ha hc
  by_cases hb : k < b
  · exact h1 k ha hb
  · exact h2 k (by omega) hc

theorem getDW_join {W : List (List ℕ)} {fw : ℕ → List ℕ} {a b c : ℕ} (h1 : ∀ k, a ≤ k → k < b → W.getD k [] = fw k)
    (h2 : ∀ k, b ≤ k → k < c → W.getD k [] = fw k) : ∀ k, a ≤ k → k < c → W.getD k [] = fw k := by
  intro k ha hc
  by_cases hb : k < b
  · exact h1 k ha hb
  · exact h2 k (by omega) hc

/-! ## Blocks -/

/-- `blkChk` through `f` -/
noncomputable def blkChkF (C : E1.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (f : ℕ → ℕ) (a m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i b => b && E1.block C sl UB UBR (f (a + i))) m

theorem blkChkF_eq (C : E1.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (Ss : List ℕ) (f : ℕ → ℕ) (a : ℕ) :
    ∀ m, (∀ i < m, Ss.getD (a + i) 0 = f (a + i)) → blkChkF C sl UB UBR f a m = blkChk C sl UB UBR Ss a m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hf
    show (blkChkF C sl UB UBR f a m && E1.block C sl UB UBR (f (a + m))) =
      (blkChk C sl UB UBR Ss a m && E1.block C sl UB UBR (Ss.getD (a + m) 0))
    rw [ih (fun i hi => hf i (by omega)), hf m (by omega)]

theorem blkChkF_zero (C : E1.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (f : ℕ → ℕ) (a : ℕ) : blkChkF C sl UB UBR f a 0 = true := rfl

theorem blkChkF_succ_of (C : E1.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (f : ℕ → ℕ) (a m : ℕ) (h1 : blkChkF C sl UB UBR f a m = true)
    (h2 : E1.block C sl UB UBR (f (a + m)) = true) : blkChkF C sl UB UBR f a (m + 1) = true := by
  show (blkChkF C sl UB UBR f a m && E1.block C sl UB UBR (f (a + m))) = true
  rw [h1, h2]; rfl

/-- blocks `a .. a+m-1` of the chain, from `f` agreeing with it below `N` -/
theorem blkChk_of_F (C : E1.Ctx) (sl : ℕ → ℕ) (UB UBR : ℕ) (Ss : List ℕ) (f : ℕ → ℕ) (N : ℕ)
    (hf : ∀ k < N, Ss.getD k 0 = f k) (a m : ℕ) (hm : a + m ≤ N) (h : blkChkF C sl UB UBR f a m = true) :
    blkChk C sl UB UBR Ss a m = true := by
  rw [← blkChkF_eq C sl UB UBR Ss f a m (fun i hi => hf (a + i) (by omega))]; exact h

/-! ## Glue -/

/-- `glue1` through `f`, with the length `N` -/
noncomputable def glue1F (f : ℕ → ℕ) (N i j i' : ℕ) : Bool :=
  Nat.blt i i' && Nat.blt i' N && (E1.glue (recOf (f i) j) (f i') || E1.glue0 (recOf (f i) j) (f i'))

/-- `glueRow` through `f` and `fw` -/
noncomputable def glueRowF (f : ℕ → ℕ) (fw : ℕ → List ℕ) (N i : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1F f N i j (nthD 0 (fw i) j)) (E1.rd 8 (E1.bS2 (f i)))

/-- `glueChkR` through `f` and `fw` -/
noncomputable def glueChkRF (f : ℕ → ℕ) (fw : ℕ → List ℕ) (N a m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i b => b && glueRowF f fw N (a + i)) m

theorem glue1F_eq (Ss : List ℕ) (f : ℕ → ℕ) (N i j i' : ℕ) (hN : N = Ss.length) (hf : ∀ k < N, Ss.getD k 0 = f k)
    (hi : i < N) : glue1F f N i j i' = glue1 Ss i j i' := by
  unfold glue1F glue1
  rw [← hN, hf i hi]
  by_cases h : i' < N
  · rw [hf i' h]
  · have hb : Nat.blt i' N = false := by
      cases hc : Nat.blt i' N
      · rfl
      · exact absurd (Nat.blt_eq.mp hc) h
    rw [hb]; simp

theorem glueRowF_eq (Ss : List ℕ) (W : List (List ℕ)) (f : ℕ → ℕ) (fw : ℕ → List ℕ) (N i : ℕ) (hN : N = Ss.length)
    (hf : ∀ k < N, Ss.getD k 0 = f k) (hw : W.getD i [] = fw i) (hi : i < N) : glueRowF f fw N i = glueRow Ss W i := by
  unfold glueRowF glueRow
  rw [hf i hi, hw]
  generalize E1.rd 8 (E1.bS2 (f i)) = K
  induction K with
  | zero => rfl
  | succ K ih =>
    show (Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1F f N i j (nthD 0 (fw i) j)) K &&
        glue1F f N i K (nthD 0 (fw i) K)) =
      (Nat.rec (motive := fun _ => Bool) true (fun j c => c && glue1 Ss i j ((fw i).getD j 0)) K &&
        glue1 Ss i K ((fw i).getD K 0))
    rw [ih, glue1F_eq Ss f N i K _ hN hf hi, nthD_eq]

theorem glueChkRF_eq (Ss : List ℕ) (W : List (List ℕ)) (f : ℕ → ℕ) (fw : ℕ → List ℕ) (N a : ℕ) (hN : N = Ss.length)
    (hf : ∀ k < N, Ss.getD k 0 = f k) (hw : ∀ k < N, W.getD k [] = fw k) :
    ∀ m, a + m ≤ N → glueChkRF f fw N a m = glueChkR Ss W a m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    show (glueChkRF f fw N a m && glueRowF f fw N (a + m)) = (glueChkR Ss W a m && glueRow Ss W (a + m))
    rw [ih (by omega), glueRowF_eq Ss W f fw N (a + m) hN hf (hw (a + m) (by omega)) (by omega)]

/-- glue rows `a .. a+m-1` of the chain, from `f`, `fw` agreeing with it below `N` -/
theorem glueChkR_of_F (Ss : List ℕ) (W : List (List ℕ)) (f : ℕ → ℕ) (fw : ℕ → List ℕ) (N : ℕ) (hN : N = Ss.length)
    (hf : ∀ k < N, Ss.getD k 0 = f k) (hw : ∀ k < N, W.getD k [] = fw k) (a m : ℕ) (hm : a + m ≤ N)
    (h : glueChkRF f fw N a m = true) : glueChkR Ss W a m = true := by
  rw [← glueChkRF_eq Ss W f fw N a hN hf hw m hm]; exact h

end G2A
