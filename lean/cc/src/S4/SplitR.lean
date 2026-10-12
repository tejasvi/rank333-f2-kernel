module
public import R22Port.U_d41d8cd98f00
public import S4.SplitQ
/-! # Sibling ranges in split records (`PL.checkSXR`)

`S4.SplitQ` cuts a certificate only at whole subtrees. A branch node with thousands of small children (the UNSAT ABORT
leaves of c436: one node with 14,208 children of about 42 bits) then leaves a record that cannot be checked in bounded
memory. Here an external item is either a subtree or a **range of consecutive siblings**:
* `Item = (P, c)`: for `c = 0` the subtree at path `P`; for `c ≥ 1` the children `i, …, i+c-1` of one branch node, where
  `P`'s last step names child `i` (`expand` lists the paths an item stands for).
* Record encoding: a dead node with `X = 0` is a marker, followed by a 16-bit count `c` (26 bits in all). `c = 0` marks one
  external subtree (it takes the next item, which must be `(its path, 0)`); `c ≥ 1`, in place of child `i` of a branch node,
  marks children `i, …, i+c-1` as one range item (the next item must be `(path of child i, c)`), and those children are skipped
  (`PL.kloopR`).
* `PL.checkSXR lt`: `PL.checkSXL` with these markers. `PL.forestOK lt R Pn t sym cdir nt sl i c ps cert`: the record of a range
  item, i.e. children `i … i+c-1` of the node at `Pn` walked in turn, with markers for the items `ps` inside.
  `PL.subMainOKR`: the record of a subtree item with inner items. `PL.leafSXR`: the main record.
* Semantics: `PL.PathsOKR lt Q R items`, every decomposition at the end state of every path of every item, with the invariant,
  is refuted.

Soundness: `checkSXR_sound`, `pathsOKR_of_forest`, `pathsOKR_of_submain`, `pathsOKR_of_sub`, `pathsOKR_of_str`,
`leafSXR_sound_paths`; instance `Q = LiftK` with the test with guessed terms: `noLiftK_of_items`. -/
@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PL
open BC4 BC5 BC6s BC7s S5 S6 S7 RootSound Matrix BC7T S7L BC7x S7X
open BC6 (KB18 KBT KERV KM0 KM1 KM2 KM3 KM4 KM5 KM6 KM7 KM8 KMS LKB18 LKBT LKERV R90 R91 R92 R93 R94 R95 R96 R97 R98 RGE RK3)

noncomputable section

/-! ## Items -/

/-- an external item: the subtree at path `P` (`c = 0`), or `c ≥ 1` consecutive siblings, the first at path `P` -/
abbrev Item := List Step × Nat

/-- a step with its candidate index advanced by `k` -/
def bumpS (s : Step) (k : Nat) : Step := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2 + k)

/-- a path with its last step's candidate index advanced by `k` -/
def bump : List Step → Nat → List Step
  | [], _ => []
  | [s], k => [bumpS s k]
  | s :: s' :: P, k => s :: bump (s' :: P) k

theorem bump_snoc (s : Step) (k : Nat) : ∀ Pn : List Step, bump (Pn ++ [s]) k = Pn ++ [bumpS s k]
  | [] => rfl
  | [a] => rfl
  | a :: b :: Pn => by
    show a :: bump (b :: Pn ++ [s]) k = a :: (b :: Pn ++ [bumpS s k])
    rw [bump_snoc s k (b :: Pn)]

/-- the paths an item stands for -/
def expand : Item → List (List Step)
  | (P, 0) => [P]
  | (P, c + 1) => (List.range (c + 1)).map (bump P)

theorem mem_expand_zero (P : List Step) : P ∈ expand (P, 0) := List.mem_singleton_self P

theorem mem_expand_range (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i0 c j : Nat) (hc : 1 ≤ c)
    (h0 : i0 ≤ j) (h1 : j < i0 + c) :
    Pn ++ [(t, sym, cdir, nt, sl, j)] ∈ expand (Pn ++ [(t, sym, cdir, nt, sl, i0)], c) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  show Pn ++ [(t, sym, cdir, nt, sl, j)] ∈ (List.range (c' + 1)).map (bump (Pn ++ [(t, sym, cdir, nt, sl, i0)]))
  refine List.mem_map.mpr ⟨j - i0, List.mem_range.mpr (by omega), ?_⟩
  rw [bump_snoc]
  show Pn ++ [(t, sym, cdir, nt, sl, i0 + (j - i0))] = _
  rw [show i0 + (j - i0) = j by omega]

theorem expand_range_cases (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c : Nat) (hc : c ≠ 0)
    (P : List Step) (hP : P ∈ expand (Pn ++ [(t, sym, cdir, nt, sl, i)], c)) :
    ∃ k < c, P = Pn ++ [(t, sym, cdir, nt, sl, i + k)] := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hP' : P ∈ (List.range (c' + 1)).map (bump (Pn ++ [(t, sym, cdir, nt, sl, i)])) := hP
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hP'
  exact ⟨k, List.mem_range.mp hk, by rw [bump_snoc]; rfl⟩

/-- every decomposition with the invariant at the end state of path `P` (replayed from `root`) is refuted -/
def RefP (Q : (Nat → Nat) → (Nat → Nat) → Prop) (T n dom need : Nat) (root : Nat × Asg × List Rec) (P : List Step) : Prop :=
  ∀ b c, Inv T n dom b c (walk T (mkSSP T n) need root P).1 (walk T (mkSSP T n) need root P).2.1
      (walk T (mkSSP T n) need root P).2.2 → AsgOK T n b c (walk T (mkSSP T n) need root P).1
        (walk T (mkSSP T n) need root P).2.1 → LGok n need b c → Q b c → False

/-! ## The kids loop with ranges -/

/-- **the kids loop with sibling ranges**: `skip` children still covered by the last range marker; a range marker (dead node,
`X = 0`, count `c ≥ 1`) in place of child `i` takes the next item, which must be `(Pn ++ [step i], c)`, and skips `c` children -/
def kloopR (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (Pn : List Step) (t : Nat) (sym cdir : Bool)
    (nt sl : List Nat) (cs : List (Nat × Nat)) : Nat → Nat → List Item → Nat → Bool × List Item × Nat :=
  @List.rec (Nat × Nat) (fun _ => Nat → Nat → List Item → Nat → Bool × List Item × Nat)
    (fun _ skip ps S => (Nat.beq skip 0, ps, S))
    (fun p _ ihc i skip ps S =>
      cond (Nat.beq skip 0)
        (cond (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
          (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
            (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                (ihc (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)) (false, ps', S)) ps)
          (let r := f p i ps S; cond r.1 (ihc (Nat.succ i) 0 r.2.1 r.2.2) (false, r.2.1, r.2.2)))
        (ihc (Nat.succ i) (Nat.pred skip) ps S)) cs

theorem kloopR_cons (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (Pn : List Step) (t : Nat)
    (sym cdir : Bool) (nt sl : List Nat) (p : Nat × Nat) (cs : List (Nat × Nat)) (i skip : Nat) (ps : List Item) (S : Nat) :
    kloopR f Pn t sym cdir nt sl (p :: cs) i skip ps S =
      cond (Nat.beq skip 0)
        (cond (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
          (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
            (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)) (false, ps', S)) ps)
          (cond (f p i ps S).1 (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) 0 (f p i ps S).2.1 (f p i ps S).2.2)
            (false, (f p i ps S).2.1, (f p i ps S).2.2)))
        (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred skip) ps S) := rfl

theorem kloopR_ps (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (Pn : List Step) (t : Nat)
    (sym cdir : Bool) (nt sl : List Nat) (hf : ∀ p i ps S, ∀ I ∈ (f p i ps S).2.1, I ∈ ps) :
    ∀ cs i skip ps S, ∀ I ∈ (kloopR f Pn t sym cdir nt sl cs i skip ps S).2.1, I ∈ ps := by
  intro cs
  induction cs with
  | nil => intro i skip ps S I hI; exact hI
  | cons q cs ih =>
    intro i skip ps S I hI
    rw [kloopR_cons] at hI
    cases hs : Nat.beq skip 0
    · rw [hs, cond_false] at hI; exact ih _ _ _ _ I hI
    · rw [hs, cond_true] at hI
      cases hm : (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
      · rw [hm, cond_false] at hI
        cases hq : (f q i ps S).1
        · rw [hq, cond_false] at hI; exact hf q i ps S I hI
        · rw [hq, cond_true] at hI; exact hf q i ps S I (ih _ _ _ _ I hI)
      · rw [hm, cond_true] at hI
        cases ps with
        | nil => exact absurd hI List.not_mem_nil
        | cons I0 ps' =>
          cases he : ((I0.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I0.2 (rd 16 (sk 10 S)))
          · have hI' : I ∈ ps' := by
              have : (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
                  (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                    (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)) (false, ps', S))
                  (I0 :: ps')) = (false, ps', S) := by
                show cond _ _ _ = _
                rw [he, cond_false]
              rw [this] at hI; exact hI
            exact List.mem_cons_of_mem _ hI'
          · have hI' : I ∈ ps' := by
              have : (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
                  (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                    (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)) (false, ps', S))
                  (I0 :: ps')) = kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S) := by
                show cond _ _ _ = _
                rw [he, cond_true]
              rw [this] at hI; exact ih _ _ _ _ I hI
            exact List.mem_cons_of_mem _ hI'

/-- an accepted kids loop: each child is walked by `f` (with a sub-list of the items), still covered by the pending range
(`j < skip`), or covered by a range item of `ps` -/
theorem kloopR_ok (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (Pn : List Step) (t : Nat)
    (sym cdir : Bool) (nt sl : List Nat) (hf : ∀ p i ps S, ∀ I ∈ (f p i ps S).2.1, I ∈ ps) :
    ∀ cs i skip ps S, (kloopR f Pn t sym cdir nt sl cs i skip ps S).1 = true →
      ∀ j < cs.length, j < skip ∨ (∃ ps' S', (∀ I ∈ ps', I ∈ ps) ∧ (f (cs.getD j (0, 0)) (i + j) ps' S').1 = true) ∨
        (∃ i0 c, (Pn ++ [(t, sym, cdir, nt, sl, i0)], c) ∈ ps ∧ 1 ≤ c ∧ i0 ≤ i + j ∧ i + j < i0 + c) := by
  intro cs
  induction cs with
  | nil => intro i skip ps S _ j hj; exact absurd hj (by simp)
  | cons q cs ih =>
    intro i skip ps S h j hj
    rw [kloopR_cons] at h
    cases hs : Nat.beq skip 0
    · -- still inside a range
      rw [hs, cond_false] at h
      have hsk : skip ≠ 0 := fun h0 => by rw [h0] at hs; exact absurd hs (by decide)
      rcases j with _ | j
      · exact Or.inl (by omega)
      · rcases ih _ _ _ _ h j (by simp at hj; omega) with h1 | ⟨ps', S', hps', hS'⟩ | ⟨i0, c, hI, hc, h0, h1⟩
        · exact Or.inl (by rw [Nat.pred_eq_sub_one] at h1; omega)
        · refine Or.inr (Or.inl ⟨ps', S', hps', ?_⟩)
          simp only [List.getD_cons_succ]
          rw [show i + (j + 1) = Nat.succ i + j by omega]; exact hS'
        · exact Or.inr (Or.inr ⟨i0, c, hI, hc, by omega, by omega⟩)
    · have hs0 : skip = 0 := Nat.eq_of_beq_eq_true hs
      rw [hs, cond_true] at h
      cases hm : (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
      · -- an ordinary child
        rw [hm, cond_false] at h
        cases hq : (f q i ps S).1
        · rw [hq, cond_false] at h; exact absurd h Bool.false_ne_true
        · rw [hq, cond_true] at h
          rcases j with _ | j
          · exact Or.inr (Or.inl ⟨ps, S, fun I hI => hI, by simpa using hq⟩)
          · rcases ih _ _ _ _ h j (by simp at hj; omega) with h1 | ⟨ps', S', hps', hS'⟩ | ⟨i0, c, hI, hc, h0, h1⟩
            · exact absurd h1 (Nat.not_lt_zero _)
            · refine Or.inr (Or.inl ⟨ps', S', fun I hI => hf q i ps S I (hps' I hI), ?_⟩)
              simp only [List.getD_cons_succ]
              rw [show i + (j + 1) = Nat.succ i + j by omega]; exact hS'
            · exact Or.inr (Or.inr ⟨i0, c, hf q i ps S _ hI, hc, by omega, by omega⟩)
      · -- a range marker
        rw [hm, cond_true] at h
        have hc1 : rd 16 (sk 10 S) ≠ 0 := by
          intro h0
          rw [h0] at hm
          simp at hm
        cases ps with
        | nil => exact absurd h Bool.false_ne_true
        | cons I0 ps' =>
          cases he : ((I0.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I0.2 (rd 16 (sk 10 S)))
          · have : (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
                (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                  (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)) (false, ps', S))
                (I0 :: ps')).1 = false := by
              show (cond ((I0.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I0.2 (rd 16 (sk 10 S)))
                (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)) (false, ps', S)).1 = false
              rw [he, cond_false]
            rw [this] at h; exact absurd h Bool.false_ne_true
          · have hI0 : I0 = (Pn ++ [(t, sym, cdir, nt, sl, i)], rd 16 (sk 10 S)) := by
              rw [Bool.and_eq_true] at he
              obtain ⟨h1, h2⟩ := he
              obtain ⟨P0, c0⟩ := I0
              have e1 : P0 = Pn ++ [(t, sym, cdir, nt, sl, i)] := beq_iff_eq.mp h1
              have e2 : c0 = rd 16 (sk 10 S) := Nat.eq_of_beq_eq_true h2
              rw [e1, e2]
            have h' : (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)).1 = true := by
              have : (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
                  (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                    (kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S)) (false, ps', S))
                  (I0 :: ps')) = kloopR f Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) ps' (sk 26 S) := by
                show cond _ _ _ = _
                rw [he, cond_true]
              rw [this] at h; exact h
            have hmem : (Pn ++ [(t, sym, cdir, nt, sl, i)], rd 16 (sk 10 S)) ∈ I0 :: ps' := by
              rw [hI0]; exact List.mem_cons_self
            rcases j with _ | j
            · exact Or.inr (Or.inr ⟨i, rd 16 (sk 10 S), hmem, by omega, by omega, by omega⟩)
            · rcases ih _ _ _ _ h' j (by simp at hj; omega) with h1 | ⟨ps'', S', hps', hS'⟩ | ⟨i0, c, hI, hc, h0, h1⟩
              · exact Or.inr (Or.inr ⟨i, rd 16 (sk 10 S), hmem, by omega, by omega, by rw [Nat.pred_eq_sub_one] at h1; omega⟩)
              · refine Or.inr (Or.inl ⟨ps'', S', fun I hI => List.mem_cons_of_mem _ (hps' I hI), ?_⟩)
                simp only [List.getD_cons_succ]
                rw [show i + (j + 1) = Nat.succ i + j by omega]; exact hS'
              · exact Or.inr (Or.inr ⟨i0, c, List.mem_cons_of_mem _ hI, hc, by omega, by omega⟩)

/-! ## The walk with ranges -/

/-- **the record walk with sibling ranges**: `PL.checkSXL` with 26-bit markers (`X = 0`, then a 16-bit count) and the kids
loop `PL.kloopR` -/
def checkSXR (lt : Asg → Nat → Bool) (fuel : Nat) :
    Nat → Nat → Nat → Nat → Asg → List Rec → Nat → List Step → List Item → Nat → Bool × List Item × Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat → Asg → List Rec → Nat → List Step → List Item → Nat → Bool × List Item × Nat)
    (fun _ _ _ _ _ _ _ _ ps S => (false, ps, S))
    (fun _ ih TERMS SS ACT need asg recs dom pth ps S =>
      cond (Nat.beq (rd 1 S) 0)
        (cond (Nat.beq (rd 9 (sk 1 S)) 0)
           (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], sk 26 S)
              (fun I ps' _ => (Nat.beq (rd 16 (sk 10 S)) 0 && (I.1 == pth.reverse) && Nat.beq I.2 0, ps', sk 26 S)) ps)
           (bit dom (rd 9 (sk 1 S)) && over6 SS ACT asg (rd 9 (sk 1 S)), ps, sk 10 S))
        (cond (Nat.beq (rd 6 S) 63)
          ((Nat.beq ACT 0 && lt asg (rd (rd 24 (sk 6 S)) (sk 30 S)), ps, sk (rd 24 (sk 6 S)) (sk 30 S)))
          (let S1 := sk 1 S
           let t := rd 5 S1
           let sym := Nat.beq (rd 1 (sk 5 S1)) 1
           let cdir := Nat.beq (rd 1 (sk 6 S1)) 1
           let ntr := rdList (rd 4 (sk 7 S1)) (sk 11 S1)
           let slr := rdList (rd 3 ntr.2) (sk 3 ntr.2)
           let nt := ntr.1
           let sl := slr.1
           let a := Nat.land (Nat.shiftRight TERMS (Nat.mul 9 t)) 511
           let nr := mkRecs6 SS ACT asg nt []
           let cs := cands TERMS SS ACT need asg recs t sym cdir nt sl
           let ss := mkSls6 SS ACT asg sl
           let kr := kloopR (fun p i ps S => ih TERMS SS (childSt TERMS SS ACT asg recs t nt p).1 need
               (childSt TERMS SS ACT asg recs t nt p).2.1 (childSt TERMS SS ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) pth.reverse t sym cdir nt sl cs 0 0 ps slr.2
           (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 && kr.1,
            kr.2.1, kr.2.2))))
    fuel

theorem checkSXR_succ (lt : Asg → Nat → Bool) (fuel TERMS SS ACT need : Nat) (asg : Asg) (recs : List Rec) (dom : Nat)
    (pth : List Step) (ps : List Item) (S : Nat) :
    checkSXR lt (fuel + 1) TERMS SS ACT need asg recs dom pth ps S =
      cond (Nat.beq (rd 1 S) 0)
        (cond (Nat.beq (rd 9 (sk 1 S)) 0)
           (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], sk 26 S)
              (fun I ps' _ => (Nat.beq (rd 16 (sk 10 S)) 0 && (I.1 == pth.reverse) && Nat.beq I.2 0, ps', sk 26 S)) ps)
           (bit dom (rd 9 (sk 1 S)) && over6 SS ACT asg (rd 9 (sk 1 S)), ps, sk 10 S))
        (cond (Nat.beq (rd 6 S) 63)
          ((Nat.beq ACT 0 && lt asg (rd (rd 24 (sk 6 S)) (sk 30 S)), ps, sk (rd 24 (sk 6 S)) (sk 30 S)))
          (let S1 := sk 1 S
           let t := rd 5 S1
           let sym := Nat.beq (rd 1 (sk 5 S1)) 1
           let cdir := Nat.beq (rd 1 (sk 6 S1)) 1
           let ntr := rdList (rd 4 (sk 7 S1)) (sk 11 S1)
           let slr := rdList (rd 3 ntr.2) (sk 3 ntr.2)
           let nt := ntr.1
           let sl := slr.1
           let a := Nat.land (Nat.shiftRight TERMS (Nat.mul 9 t)) 511
           let nr := mkRecs6 SS ACT asg nt []
           let cs := cands TERMS SS ACT need asg recs t sym cdir nt sl
           let ss := mkSls6 SS ACT asg sl
           let kr := kloopR (fun p i ps S => checkSXR lt fuel TERMS SS (childSt TERMS SS ACT asg recs t nt p).1 need
               (childSt TERMS SS ACT asg recs t nt p).2.1 (childSt TERMS SS ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) pth.reverse t sym cdir nt sl cs 0 0 ps slr.2
           (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 && kr.1,
            kr.2.1, kr.2.2))) := rfl

theorem checkSXR_ps (lt : Asg → Nat → Bool) (TERMS SS need dom : Nat) : ∀ fuel ACT asg recs pth ps S,
    ∀ I ∈ (checkSXR lt fuel TERMS SS ACT need asg recs dom pth ps S).2.1, I ∈ ps := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs pth ps S I hI; exact hI
  | succ fuel ih =>
    intro ACT asg recs pth ps S I hI
    rw [checkSXR_succ] at hI
    revert hI
    cases Nat.beq (rd 1 S) 0
    · rw [cond_false]
      cases Nat.beq (rd 6 S) 63
      · rw [cond_false]
        intro hI
        exact kloopR_ps _ _ _ _ _ _ _ (fun p i ps S => ih _ _ _ _ ps S) _ _ _ _ _ I hI
      · rw [cond_true]; intro hI; exact hI
    · rw [cond_true]
      cases Nat.beq (rd 9 (sk 1 S)) 0
      · rw [cond_false]; intro hI; exact hI
      · rw [cond_true]
        cases ps with
        | nil => intro hI; exact absurd hI List.not_mem_nil
        | cons I0 ps' => intro hI; exact List.mem_cons_of_mem _ hI

/-- **Records with sibling ranges.** An accepted record refutes every decomposition at its node with `Q`, given that every
decomposition at the end state of each path of each external item (`expand`) with `Q` is refuted. -/
theorem checkSXR_sound (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (T n dom need : Nat) (hn : n ≤ 31)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK T n b c 0 asg → Q b c → False)
    (root : Nat × Asg × List Rec) (items : List Item)
    (H : ∀ I ∈ items, ∀ P ∈ expand I, RefP Q T n dom need root P) :
    ∀ fuel ACT asg recs (pth : List Step) (ps : List Item) S, (∀ I ∈ ps, I ∈ items) →
      (ACT, asg, recs) = walk T (mkSSP T n) need root pth.reverse →
      (checkSXR lt fuel T (mkSSP T n) ACT need asg recs dom pth ps S).1 = true →
      ∀ b c, Inv T n dom b c ACT asg recs → AsgOK T n b c ACT asg → LGok n need b c → Q b c → False := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs pth ps S _ _ h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro ACT asg recs pth ps S hps hst hchk b c hinv hasg hlg hq
    rw [checkSXR_succ] at hchk
    revert hchk
    cases hb : Nat.beq (rd 1 S) 0
    · rw [cond_false]
      cases ht31 : Nat.beq (rd 6 S) 63
      · rw [cond_false]
        show let S1 := sk 1 S
          let t := rd 5 S1
          let sym := Nat.beq (rd 1 (sk 5 S1)) 1
          let cdir := Nat.beq (rd 1 (sk 6 S1)) 1
          let ntr := rdList (rd 4 (sk 7 S1)) (sk 11 S1)
          let slr := rdList (rd 3 ntr.2) (sk 3 ntr.2)
          let nt := ntr.1
          let sl := slr.1
          let a := Nat.land (Nat.shiftRight T (Nat.mul 9 t)) 511
          let nr := mkRecs6 (mkSSP T n) ACT asg nt []
          let cs := cands T (mkSSP T n) ACT need asg recs t sym cdir nt sl
          let ss := mkSls6 (mkSSP T n) ACT asg sl
          let kr := kloopR (fun p i ps S => checkSXR lt fuel T (mkSSP T n) (childSt T (mkSSP T n) ACT asg recs t nt p).1 need
               (childSt T (mkSSP T n) ACT asg recs t nt p).2.1 (childSt T (mkSSP T n) ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) pth.reverse t sym cdir nt sl cs 0 0 ps slr.2
          (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 &&
            kr.1) = true → False
        intro S1 t sym cdir ntr slr nt sl a nr cs ss kr hchk
        have ha : a = aT T t := rfl
        have hcs : cs = brCands7 (mkSSP T n) ACT need asg recs t a nt sl sym cdir := rfl
        have hnr : nr = mkRecs6 (mkSSP T n) ACT asg nt [] := rfl
        have hss : ss = mkSls6 (mkSSP T n) ACT asg sl := rfl
        have hkr : kr = kloopR (fun p i ps S => checkSXR lt fuel T (mkSSP T n) (childSt T (mkSSP T n) ACT asg recs t nt p).1
             need (childSt T (mkSSP T n) ACT asg recs t nt p).2.1 (childSt T (mkSSP T n) ACT asg recs t nt p).2.2 dom
             ((t, sym, cdir, nt, sl, i) :: pth) ps S) pth.reverse t sym cdir nt sl cs 0 0 ps slr.2 := rfl
        have hnt : ∀ x ∈ nt, x < 512 := rdList_lt _ _
        have hsl : ∀ x ∈ sl, x < 512 := rdList_lt _ _
        have hcs' : cs = cands T (mkSSP T n) ACT need asg recs t sym cdir nt sl := rfl
        clear_value S1 t sym cdir ntr slr nt sl a nr cs ss kr
        subst ha hnr hss hkr
        simp only [Bool.and_eq_true] at hchk
        obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hchk
        have hact : ACT.testBit t = true := by rw [← S5.bit_eq]; exact h1
        have htn : t < n := hinv.act t hact
        obtain ⟨p, hp, b', c', hinv', hlg', hpe, hmove'⟩ := br_step7_ex T n dom need (by omega) (mkSSP T n)
          (mkSSP_ok T n (by omega)) ACT asg recs t sym cdir nt sl hnt hsl h1 h2 h3 h4 h5 h6 h7 b c hinv hlg
        rw [← hcs] at hp
        obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
        have hgd : cs.getD j (0, 0) = p := by rw [List.getD_eq_getElem _ _ hj, hpj]
        have hst' : childSt T (mkSSP T n) ACT asg recs t nt p =
            walk T (mkSSP T n) need root ((t, sym, cdir, nt, sl, j) :: pth).reverse := by
          rw [List.reverse_cons, walk_append, ← hst]
          show childSt T (mkSSP T n) ACT asg recs t nt p =
            childSt T (mkSSP T n) ACT asg recs t nt ((cands T (mkSSP T n) ACT need asg recs t sym cdir nt sl).getD j (0, 0))
          rw [← hcs', hgd]
        have hasg' : AsgOK T n b' c' (ACT ^^^ 1 <<< t) ((aT T t, p.1, p.2) :: asg) := by
          rw [hpe]; exact asgOK_step (asgOK_move hasg hmove') t htn hact
        rcases kloopR_ok _ _ _ _ _ _ _ (fun p i ps S => checkSXR_ps lt _ _ _ _ _ _ _ _ _ ps S) cs 0 0 ps slr.2 h8 j hj with
          h0 | ⟨ps', S', hps', hS'⟩ | ⟨i0, c0, hI, hc0, hi0, hj0⟩
        · exact absurd h0 (Nat.not_lt_zero _)
        · rw [hgd, Nat.zero_add] at hS'
          rw [childSt_eq] at hst' hS'
          exact ih _ _ _ _ ps' S' (fun I hI => hps I (hps' I hI)) hst' hS' b' c' hinv' hasg' hlg'
            (q_of_move Q hmove hmove' hq)
        · -- child `j` lies in a range item: its path is one of the item's paths
          have hmem := mem_expand_range pth.reverse t sym cdir nt sl i0 c0 j hc0 (by omega) (by omega)
          have hR := H _ (hps _ hI) _ hmem b' c'
          rw [List.reverse_cons] at hst'
          rw [← hst', childSt_eq] at hR
          exact hR hinv' hasg' hlg' (q_of_move Q hmove hmove' hq)
      · rw [cond_true]
        intro hchk
        have hchk' : (Nat.beq ACT 0 && lt asg (rd (rd 24 (sk 6 S)) (sk 30 S))) = true := hchk
        rw [Bool.and_eq_true] at hchk'
        obtain ⟨hA, hw⟩ := hchk'
        have hA' : ACT = 0 := Nat.eq_of_beq_eq_true hA
        subst hA'
        exact hleaf asg _ b c hw hasg hq
    · rw [cond_true]
      cases hX : Nat.beq (rd 9 (sk 1 S)) 0
      · rw [cond_false]
        intro hchk
        exact over_step7 T n dom (by omega) (mkSSP T n) (mkSSP_ok T n (by omega)) ACT asg recs _
          (lt_of_lt_of_eq (rd_lt 9 _) (by norm_num)) hchk b c hinv
      · rw [cond_true]
        cases ps with
        | nil => intro hchk; exact absurd hchk Bool.false_ne_true
        | cons I ps' =>
          intro hchk
          have hchk' : (Nat.beq (rd 16 (sk 10 S)) 0 && (I.1 == pth.reverse) && Nat.beq I.2 0) = true := hchk
          simp only [Bool.and_eq_true] at hchk'
          obtain ⟨⟨_, hP⟩, hc⟩ := hchk'
          have hP' : I.1 = pth.reverse := beq_iff_eq.mp hP
          have hc' : I.2 = 0 := Nat.eq_of_beq_eq_true hc
          have hI : I = (pth.reverse, 0) := by
            obtain ⟨P0, c0⟩ := I
            simp only at hP' hc'
            rw [hP', hc']
          have hmem : pth.reverse ∈ expand I := by rw [hI]; exact mem_expand_zero _
          have hR := H I (hps I List.mem_cons_self) _ hmem b c
          rw [← hst] at hR
          exact hR hinv hasg hlg hq

/-! ## Item records and the semantic statement -/

/-- the state at the end of path `P` of the leaf with header `R` -/
abbrev walkR (R : Nat) (P : List Step) : Nat × Asg × List Rec :=
  walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P

/-- **every decomposition at the end state of every path of every item, with the invariant, is refuted** (the public
statement of a part module) -/
def PathsOKR (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop) (R : Nat) (items : List Item) : Prop :=
  ∀ I ∈ items, ∀ P ∈ expand I,
    RefP Q (hdr R).2.1 (hdr R).1 (hdr R).2.2.1 (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P

theorem pathsOKR_append {lt : Asg → Nat → Bool} {Q : (Nat → Nat) → (Nat → Nat) → Prop} {R : Nat} {l1 l2 : List Item}
    (h1 : PathsOKR lt Q R l1) (h2 : PathsOKR lt Q R l2) : PathsOKR lt Q R (l1 ++ l2) := by
  intro I hI
  rcases List.mem_append.mp hI with h | h
  · exact h1 I h
  · exact h2 I h

theorem pathsOKR_nil {lt : Asg → Nat → Bool} {Q : (Nat → Nat) → (Nat → Nat) → Prop} {R : Nat} : PathsOKR lt Q R [] :=
  fun I hI => absurd hI List.not_mem_nil

/-- **a range item's record**: children `i, …, i+c-1` (`c ≥ 1`, all present) of the branch node at path `Pn` with branch data
`t sym cdir nt sl`, each walked by `checkSXR` in turn, external items `ps` inside -/
def forestOK (lt : Asg → Nat → Bool) (R : Nat) (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c : Nat)
    (ps : List Item) (cert : Nat) : Bool :=
  let st := walkR R Pn
  let cs := cands (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 (hdr R).2.2.2.1 st.2.1 st.2.2 t sym cdir nt sl
  Nat.ble (hdr R).1 31 && !Nat.beq c 0 && Nat.ble (i + c) cs.length &&
    (kloopR (fun p j ps S => checkSXR lt 64 (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1)
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt p).1 (hdr R).2.2.2.1
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt p).2.1
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt p).2.2 (hdr R).2.2.1
        ((t, sym, cdir, nt, sl, j) :: Pn.reverse) ps S)
      Pn t sym cdir nt sl ((cs.drop i).take c) i 0 ps cert).1

/-- **a range item is refuted**, given its inner items -/
theorem pathsOKR_of_forest (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c : Nat) (ps : List Item) (cert : Nat)
    (h : forestOK lt R Pn t sym cdir nt sl i c ps cert = true) (hsub : PathsOKR lt Q R ps) :
    PathsOKR lt Q R [(Pn ++ [(t, sym, cdir, nt, sl, i)], c)] := by
  unfold forestOK at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hn, hc⟩, hlen⟩, hk⟩ := h
  have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hc; exact absurd hc (by decide)
  intro I hI P hP
  rw [List.mem_singleton] at hI
  subst hI
  obtain ⟨k, hk', rfl⟩ := expand_range_cases Pn t sym cdir nt sl i c hc0 P hP
  intro b0 c0 hinv hasg hlg hq
  set st := walkR R Pn with hstdef
  set cs := cands (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 (hdr R).2.2.2.1 st.2.1 st.2.2 t sym cdir nt sl with hcsdef
  have hlen' : ((cs.drop i).take c).length = c := by
    rw [List.length_take, List.length_drop]; omega
  have hget : ((cs.drop i).take c).getD k (0, 0) = cs.getD (i + k) (0, 0) := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp [List.getElem_take, List.getElem_drop]
  -- the end state of the child's path is the child state
  have hwalk : walkR R (Pn ++ [(t, sym, cdir, nt, sl, i + k)]) =
      childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0)) := by
    show walk _ _ _ _ (Pn ++ [(t, sym, cdir, nt, sl, i + k)]) = _
    rw [walk_append]
    rfl
  rcases kloopR_ok _ _ _ _ _ _ _ (fun p i ps S => checkSXR_ps lt _ _ _ _ _ _ _ _ _ ps S) _ i 0 ps cert hk k (by omega) with
    h0 | ⟨ps', S', hps', hS'⟩ | ⟨i0, c1, hI, hc1, hi0, hj0⟩
  · exact absurd h0 (Nat.not_lt_zero _)
  · rw [hget] at hS'
    have hst : ((childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0))).1,
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0))).2.1,
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0))).2.2) =
        walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], [])
          ((t, sym, cdir, nt, sl, i + k) :: Pn.reverse).reverse := by
      rw [List.reverse_cons, List.reverse_reverse]
      exact hwalk.symm
    have hinv' := hinv
    have hasg' := hasg
    change Inv _ _ _ b0 c0 (walkR R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).1
      (walkR R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).2.1 (walkR R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).2.2 at hinv'
    change AsgOK _ _ b0 c0 (walkR R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).1
      (walkR R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).2.1 at hasg'
    rw [hwalk] at hinv' hasg'
    exact checkSXR_sound lt Q hmove _ _ _ _ hn hleaf (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) ps hsub 64 _ _ _ _ ps' S'
      hps' hst hS' b0 c0 hinv' hasg' hlg hq
  · exact hsub _ hI _ (mem_expand_range Pn t sym cdir nt sl i0 c1 (i + k) hc1 hi0 hj0) b0 c0 hinv hasg hlg hq

/-- **a subtree item's record with inner items** (a nested part rooted at path `P`) -/
def subMainOKR (lt : Asg → Nat → Bool) (R : Nat) (P : List Step) (ps : List Item) (cert : Nat) : Bool :=
  Nat.ble (hdr R).1 31 &&
    (checkSXR lt 64 (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (walkR R P).1 (hdr R).2.2.2.1 (walkR R P).2.1 (walkR R P).2.2
      (hdr R).2.2.1 P.reverse ps cert).1

theorem pathsOKR_of_submain (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (P : List Step) (ps : List Item) (cert : Nat) (h : subMainOKR lt R P ps cert = true) (hsub : PathsOKR lt Q R ps) :
    PathsOKR lt Q R [(P, 0)] := by
  intro I hI P' hP' b c hinv hasg hlg hq
  rw [List.mem_singleton] at hI
  subst hI
  have hP : P' = P := List.mem_singleton.mp hP'
  subst hP
  unfold subMainOKR at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  exact checkSXR_sound lt Q hmove _ _ _ _ h.1 hleaf (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) ps hsub 64 _ _ _
    P'.reverse ps cert (fun x hx => hx) (by rw [List.reverse_reverse]) h.2 b c hinv hasg hlg hq

/-- a subtree item checked as a plain sub-record (no inner items) -/
theorem pathsOKR_of_sub (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (P : List Step) (cert : Nat) (h : subOKL lt R P cert = true) : PathsOKR lt Q R [(P, 0)] := by
  intro I hI P' hP'
  rw [List.mem_singleton] at hI
  subst hI
  have hP : P' = P := List.mem_singleton.mp hP'
  subst hP
  exact subOKL_sound lt Q hmove R hleaf P' cert h

/-! ## Balanced trees of item records (a part's combining step) -/

/-- a binary tree of item records: plain sub-records (`one`) and range records without inner items (`rng`) -/
inductive STR where
  | one (P : List Step) (cert : Nat)
  | rng (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c cert : Nat)
  | node (a b : STR)

/-- the items in order -/
def STR.items : STR → List Item
  | .one P _ => [(P, 0)]
  | .rng Pn t sym cdir nt sl i c _ => [(Pn ++ [(t, sym, cdir, nt, sl, i)], c)]
  | .node a b => a.items ++ b.items

/-- every record of the tree is accepted -/
def STR.ok (lt : Asg → Nat → Bool) (R : Nat) : STR → Prop
  | .one P cert => subOKL lt R P cert = true
  | .rng Pn t sym cdir nt sl i c cert => forestOK lt R Pn t sym cdir nt sl i c [] cert = true
  | .node a b => a.ok lt R ∧ b.ok lt R

theorem pathsOKR_of_str (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False) :
    ∀ t : STR, t.ok lt R → PathsOKR lt Q R t.items := by
  intro t
  induction t with
  | one P cert => intro h; exact pathsOKR_of_sub lt Q hmove R hleaf P cert h
  | rng Pn t sym cdir nt sl i c cert =>
    intro h; exact pathsOKR_of_forest lt Q hmove R hleaf Pn t sym cdir nt sl i c [] cert h pathsOKR_nil
  | node a b iha ihb => intro h; exact pathsOKR_append (iha h.1) (ihb h.2)

/-! ## The main record -/

/-- **the main record** with sibling ranges (as `PL.leafSXL`, walked by `checkSXR`) -/
def leafSXR (lt : Asg → Nat → Bool) (R : Nat) (items : List Item) : Bool :=
  Nat.ble (rd 6 R) 31 &&
    ((Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
        Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0) && Nat.blt (rkSum (leafT R) (leafN R)) 27 ||
     (checkSXR lt 64 (leafT R) (mkSSP (leafT R) (leafN R)) (Nat.pred (Nat.shiftLeft 1 (leafN R)))
        (cond (Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
            Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
          (needP (leafT R) (leafN R) (Nat.sub (rkSum (leafT R) (leafN R)) 27)) 0) [] [] (leafDom6 R) [] items
        (cond (Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
          (sk 2 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) (sk 514 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)))).1)

theorem leafSXR_eq (lt : Asg → Nat → Bool) (R : Nat) (items : List Item) : leafSXR lt R items =
    (Nat.ble (rd 6 R) 31 &&
      ((Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
          Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0) && Nat.blt (rkSum (leafT R) (leafN R)) 27 ||
       (checkSXR lt 64 (leafT R) (mkSSP (leafT R) (leafN R)) (Nat.pred (Nat.shiftLeft 1 (leafN R)))
          (cond (Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
              Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
            (needP (leafT R) (leafN R) (Nat.sub (rkSum (leafT R) (leafN R)) 27)) 0) [] [] (leafDom6 R) [] items
          (cond (Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
            (sk 2 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) (sk 514 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)))).1)) := rfl

/-- **the aggregator**: the main record and the items' statements refute every decomposition of the record with `Q` -/
theorem leafSXR_sound_paths (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (leafT R) (leafN R) b c 0 asg → Q b c → False)
    (items : List Item) (hmain : leafSXR lt R items = true) (hparts : PathsOKR lt Q R items)
    (b c : Nat → Nat) (hbc : BC (leafN R) b c)
    (hd : ∀ X, X < 512 → (leafDom6 R).testBit X = true →
      TX (toM3 X) = ∑ t ∈ (Finset.range (leafN R)).filter (fun t => par (aT (leafT R) t &&& X) = true),
        vecMulVec (nv (b t)) (nv (c t))) (hq : Q b c) : False := by
  rw [leafSXR_eq] at hmain
  set R1 := sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R with hR1
  set dm := Nat.beq (rd 1 R1) 0 with hdm
  set lg := Nat.beq (rd 1 (sk 1 R1)) 1 && dm with hlg
  set RS := rkSum (leafT R) (leafN R) with hRS
  have epred : Nat.pred (Nat.shiftLeft 1 (leafN R)) = 2 ^ leafN R - 1 := by
    show 1 <<< leafN R - 1 = _; rw [Nat.one_shiftLeft]
  rw [epred] at hmain
  rw [Bool.and_eq_true, Nat.ble_eq, Bool.or_eq_true] at hmain
  obtain ⟨hn, hmain⟩ := hmain
  have hfull : lg = true → leafDom6 R = ALLNZ := by
    intro hl
    have hd' : dm = true := by rw [hlg, Bool.and_eq_true] at hl; exact hl.2
    show cond dm ALLNZ _ = ALLNZ
    rw [hd', cond_true]
  have hdfull : lg = true → ∀ X, X < 512 → ALLNZ.testBit X = true →
      TX (toM3 X) = ∑ t ∈ (Finset.range (leafN R)).filter (fun t => par (aT (leafT R) t &&& X) = true),
        vecMulVec (nv (b t)) (nv (c t)) := by
    intro hl X hX hX'
    exact hd X hX (by rw [hfull hl]; exact hX')
  rcases hmain with h | h
  · rw [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hl, hlt⟩ := h
    have := (lg_root (leafT R) (leafN R) b c hbc (hdfull hl)).1
    omega
  · have hlgok : LGok (leafN R) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0) b c := by
      cases hl : lg
      · rw [cond_false]; exact lgok_zero _ b c hbc
      · rw [cond_true]
        exact (lg_root (leafT R) (leafN R) b c hbc (hdfull hl)).2
    have hH : ∀ I ∈ items, ∀ P ∈ expand I, RefP Q (leafT R) (leafN R) (leafDom6 R)
        (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0) (2 ^ leafN R - 1, [], []) P := by
      intro I hI P hP
      have hs := hparts I hI P hP
      have e : Nat.pred (Nat.shiftLeft 1 (hdr R).1) = 2 ^ leafN R - 1 := epred
      rw [e] at hs
      exact hs
    exact checkSXR_sound lt Q hmove (leafT R) (leafN R) (leafDom6 R) _ hn hleaf (2 ^ leafN R - 1, [], [])
      items hH 64 _ [] [] [] _ _ (fun P hP => hP) rfl h b c (S5.inv_root _ _ _ b c hbc hd)
      (asgOK_root _ _ b c) hlgok hq

/-! ## The instance: `LiftK` and the test with guessed terms -/

theorem pathsOKR_of_strW3 (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (t : STR) (ht : t.ok (ltW3 pts k) R) :
    PathsOKR (ltW3 pts k) (QK (leafN R) Em k) R t.items :=
  pathsOKR_of_str (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) t ht

theorem pathsOKR_of_submainW3 (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (P : List Step) (ps : List Item)
    (cert : Nat) (h : subMainOKR (ltW3 pts k) R P ps cert = true) (hsub : PathsOKR (ltW3 pts k) (QK (leafN R) Em k) R ps) :
    PathsOKR (ltW3 pts k) (QK (leafN R) Em k) R [(P, 0)] :=
  pathsOKR_of_submain (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) P ps cert h hsub

theorem pathsOKR_of_forestW3 (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (Pn : List Step) (t : Nat) (sym cdir : Bool)
    (nt sl : List Nat) (i c : Nat) (ps : List Item) (cert : Nat) (h : forestOK (ltW3 pts k) R Pn t sym cdir nt sl i c ps cert = true)
    (hsub : PathsOKR (ltW3 pts k) (QK (leafN R) Em k) R ps) :
    PathsOKR (ltW3 pts k) (QK (leafN R) Em k) R [(Pn ++ [(t, sym, cdir, nt, sl, i)], c)] :=
  pathsOKR_of_forest (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) Pn t sym cdir nt sl i c ps
    cert h hsub

/-- **a split leaf with sibling ranges**: the main record and its items' statements give `NoLiftK` -/
theorem noLiftK_of_items (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (items : List Item)
    (hmain : leafSXR (ltW3 pts k) R items = true) (hparts : PathsOKR (ltW3 pts k) (QK (leafN R) Em k) R items) :
    L479.NoLiftK (leafT R) (leafN R) (S6.leafDom6 R) Em k := by
  intro b c hbc hd hl
  exact leafSXR_sound_paths (ltW3 pts k) (QK (leafN R) Em k)
    (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) items hmain hparts
    b c hbc hd hl

end

end PL

#print axioms PL.checkSXR_sound
#print axioms PL.pathsOKR_of_forest
#print axioms PL.pathsOKR_of_submain
#print axioms PL.pathsOKR_of_str
#print axioms PL.leafSXR_sound_paths
#print axioms PL.noLiftK_of_items
#print axioms PL.pathsOKR_of_strW3
#print axioms PL.pathsOKR_of_submainW3
#print axioms PL.pathsOKR_of_forestW3
