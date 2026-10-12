module
public import S4.SplitRN
/-! # Equal-first-factor ordering in the v7L walk (`PL.checkSXRE`; the EqF option of the walk)

Terms with equal first factor `a_t` are interchangeable: swapping `(b_u, c_u)` and `(b_v, c_v)` when `a_u = a_v` keeps the
decomposition. So the walk need only refute **canonical** decompositions (`Canon T n a0 b c`): within every group of equal first
factor other than `a0`'s, the keys `512 b + c` are non-decreasing in the term index. `a0` is the first factor of the root
branch term `t0`, whose group stays out of the ordering, so the GL3 root move (`sym`, `hmove`) keeps normalising `t0`. Any
decomposition maps to a canonical one by that root move followed by swaps inside the other groups (`canon_exists`), and swaps
keep `BC`, the residual identity `HD`, every `RecOK` (the hit sets are swap-stable) and `LiftK` (its term set is permuted).

`PL.checkSXRE lt a0` is `PL.checkSXR lt` with three changes:
* at a root node (`asg = []`) the branch term is in `a0`'s group;
* `ordOK`: when branching on `t` outside `a0`'s group, every larger-index term of `t`'s group is still active (so the assigned
  members of `t`'s group are exactly smaller-index ones);
* skip runs in the kids loop (`kloopRE`): a dead node with `X = 0` and a 16-bit value `v ≥ 32768` stands for `v - 32767` kids
  whose candidates are all `skipOK` (outside `a0`'s group, with a key below a key already assigned in the group): they cannot be
  canonical, so they need no subtree. Range markers keep `1 ≤ v ≤ 32767`.
`skipOK` compares the candidate's key with the keys of the assignment entries `e` whose first-factor value `e.1` equals the
branch term's first factor `a` (the entries record `(a_u, b_u, c_u)` of the assigned terms `u`); `ordOK` is checked at every branch
node outside `a0`'s group, in the main record and in every sub-record (`checkSXRE` is the walk of all of them, and `forestOKE`
checks it at its own node). Records, paths and items keep the semantics of `S4.SplitR`; the item statements (`RefPE`, `PathsOKRE`) add the hypothesis
`Canon` (for nodes below the root). Lemma G is off (`need = 0`: the domain is a mask, as for every external leaf).
Results: `checkSXRE_sound`, the item lemmas, `leafSXRE_sound_paths`, `noLiftK_of_itemsE`, `noDecomp_of_itemsE`. -/
@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PL
open BC4 BC5 BC6s BC7s S5 S6 S7 RootSound Matrix BC7T S7L BC7x S7X

noncomputable section

/-! ## The canonical form -/

/-- the key of a pair `(b, c)` -/
def keyP (b c : Nat) : Nat := 512 * b + c

/-- **canonical decompositions**: within every group of equal first factor other than `a0`'s, the keys are non-decreasing in
the term index -/
def Canon (T n a0 : Nat) (b c : Nat → Nat) : Prop :=
  ∀ u v, u < v → v < n → aT T u = aT T v → aT T u ≠ a0 → keyP (b u) (c u) ≤ keyP (b v) (c v)

/-- `Q` is invariant under swapping two terms with the same first factor (all that canonicalisation uses) -/
def SwapInv (T n : Nat) (Q : (Nat → Nat) → (Nat → Nat) → Prop) : Prop :=
  ∀ (b c : Nat → Nat) (u v : Nat), u < n → v < n → aT T u = aT T v → Q b c →
    Q (fun w => b (Equiv.swap u v w)) (fun w => c (Equiv.swap u v w))

/-- the order rule at a branch node on term `t`: outside `a0`'s group, every larger-index term of `t`'s group is active -/
def ordOK (T ACT a0 t : Nat) : Bool :=
  Nat.beq (aT T t) a0 ||
    (List.range 32).all (fun u => !(Nat.beq (aT T u) (aT T t) && Nat.blt t u) || bit ACT u)

/-- a kid whose candidate `p` (for a term of group `a`) is outside `a0`'s group and has a key below a key already assigned in
the group: it cannot belong to a canonical decomposition -/
def skipOK (a0 : Nat) (asg : Asg) (a : Nat) (p : Nat × Nat) : Bool :=
  !(Nat.beq a a0) && asg.any (fun e => Nat.beq e.1 a && Nat.blt (keyP p.1 p.2) (keyP e.2.1 e.2.2))

/-! ## The kids loop with skip runs -/

/-- **the kids loop with ranges and skip runs** (`PL.kloopR` plus skip runs): `skip` children still covered by the last range
marker, `chk` children still in the current skip run (each must satisfy `g`); a marker (dead node, `X = 0`, 16-bit `v`) in place
of child `i` is a skip run of `v - 32767` children if `v ≥ 32768`, else (for `v ≥ 1`) a range item as in `kloopR` -/
def kloopRE (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (g : Nat × Nat → Bool) (Pn : List Step) (t : Nat)
    (sym cdir : Bool) (nt sl : List Nat) (cs : List (Nat × Nat)) : Nat → Nat → Nat → List Item → Nat → Bool × List Item × Nat :=
  @List.rec (Nat × Nat) (fun _ => Nat → Nat → Nat → List Item → Nat → Bool × List Item × Nat)
    (fun _ skip chk ps S => (Nat.beq skip 0 && Nat.beq chk 0, ps, S))
    (fun p _ ihc i skip chk ps S =>
      cond (Nat.beq skip 0)
        (cond (Nat.beq chk 0)
          (cond (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && Nat.ble 32768 (rd 16 (sk 10 S)))
            (cond (g p) (ihc (Nat.succ i) 0 (rd 16 (sk 10 S) - 32768) ps (sk 26 S)) (false, ps, S))
            (cond (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
              (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
                (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                    (ihc (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) 0 ps' (sk 26 S)) (false, ps', S)) ps)
              (let r := f p i ps S; cond r.1 (ihc (Nat.succ i) 0 0 r.2.1 r.2.2) (false, r.2.1, r.2.2))))
          (cond (g p) (ihc (Nat.succ i) 0 (Nat.pred chk) ps S) (false, ps, S)))
        (ihc (Nat.succ i) (Nat.pred skip) chk ps S)) cs

theorem kloopRE_cons (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (g : Nat × Nat → Bool) (Pn : List Step)
    (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (p : Nat × Nat) (cs : List (Nat × Nat)) (i skip chk : Nat) (ps : List Item)
    (S : Nat) :
    kloopRE f g Pn t sym cdir nt sl (p :: cs) i skip chk ps S =
      cond (Nat.beq skip 0)
        (cond (Nat.beq chk 0)
          (cond (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && Nat.ble 32768 (rd 16 (sk 10 S)))
            (cond (g p) (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) 0 (rd 16 (sk 10 S) - 32768) ps (sk 26 S)) (false, ps, S))
            (cond (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
              (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
                (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
                    (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) 0 ps' (sk 26 S))
                    (false, ps', S)) ps)
              (cond (f p i ps S).1 (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) 0 0 (f p i ps S).2.1 (f p i ps S).2.2)
                (false, (f p i ps S).2.1, (f p i ps S).2.2))))
          (cond (g p) (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) 0 (Nat.pred chk) ps S) (false, ps, S)))
        (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred skip) chk ps S) := rfl

/-- the range-marker branch, item by item (as in `kloopR`) -/
theorem kloopRE_rng (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (g : Nat × Nat → Bool) (Pn : List Step)
    (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (cs : List (Nat × Nat)) (i : Nat) (S : Nat) (I0 : Item) (ps' : List Item) :
    (@List.rec Item (fun _ => Bool × List Item × Nat) (false, [], S)
      (fun I ps' _ => cond ((I.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I.2 (rd 16 (sk 10 S)))
          (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) 0 ps' (sk 26 S)) (false, ps', S))
      (I0 :: ps')) =
      cond ((I0.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I0.2 (rd 16 (sk 10 S)))
        (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) (Nat.pred (rd 16 (sk 10 S))) 0 ps' (sk 26 S)) (false, ps', S) := rfl

theorem kloopRE_ps (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (g : Nat × Nat → Bool) (Pn : List Step)
    (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (hf : ∀ p i ps S, ∀ I ∈ (f p i ps S).2.1, I ∈ ps) :
    ∀ cs i skip chk ps S, ∀ I ∈ (kloopRE f g Pn t sym cdir nt sl cs i skip chk ps S).2.1, I ∈ ps := by
  intro cs
  induction cs with
  | nil => intro i skip chk ps S I hI; exact hI
  | cons q cs ih =>
    intro i skip chk ps S I hI
    rw [kloopRE_cons] at hI
    cases hs : Nat.beq skip 0
    · rw [hs, cond_false] at hI; exact ih _ _ _ _ _ I hI
    · rw [hs, cond_true] at hI
      cases hc : Nat.beq chk 0
      · rw [hc, cond_false] at hI
        cases hg : g q
        · rw [hg, cond_false] at hI; exact hI
        · rw [hg, cond_true] at hI; exact ih _ _ _ _ _ I hI
      · rw [hc, cond_true] at hI
        cases hk : (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && Nat.ble 32768 (rd 16 (sk 10 S)))
        · rw [hk, cond_false] at hI
          cases hm : (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
          · rw [hm, cond_false] at hI
            cases hq : (f q i ps S).1
            · rw [hq, cond_false] at hI; exact hf q i ps S I hI
            · rw [hq, cond_true] at hI; exact hf q i ps S I (ih _ _ _ _ _ I hI)
          · rw [hm, cond_true] at hI
            cases ps with
            | nil => exact absurd hI List.not_mem_nil
            | cons I0 ps' =>
              rw [kloopRE_rng] at hI
              cases he : ((I0.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I0.2 (rd 16 (sk 10 S)))
              · rw [he, cond_false] at hI; exact List.mem_cons_of_mem _ hI
              · rw [he, cond_true] at hI; exact List.mem_cons_of_mem _ (ih _ _ _ _ _ I hI)
        · rw [hk, cond_true] at hI
          cases hg : g q
          · rw [hg, cond_false] at hI; exact hI
          · rw [hg, cond_true] at hI; exact ih _ _ _ _ _ I hI

/-- an accepted kids loop with skip runs: each child is still covered by the pending range (`j < skip`), satisfies `g` (it was
in a skip run), is walked by `f` (with a sub-list of the items), or is covered by a range item of `ps` -/
theorem kloopRE_ok (f : Nat × Nat → Nat → List Item → Nat → Bool × List Item × Nat) (g : Nat × Nat → Bool) (Pn : List Step)
    (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (hf : ∀ p i ps S, ∀ I ∈ (f p i ps S).2.1, I ∈ ps) :
    ∀ cs i skip chk ps S, (kloopRE f g Pn t sym cdir nt sl cs i skip chk ps S).1 = true →
      ∀ j < cs.length, j < skip ∨ g (cs.getD j (0, 0)) = true ∨
        (∃ ps' S', (∀ I ∈ ps', I ∈ ps) ∧ (f (cs.getD j (0, 0)) (i + j) ps' S').1 = true) ∨
        (∃ i0 c, (Pn ++ [(t, sym, cdir, nt, sl, i0)], c) ∈ ps ∧ 1 ≤ c ∧ i0 ≤ i + j ∧ i + j < i0 + c) := by
  intro cs
  induction cs with
  | nil => intro i skip chk ps S _ j hj; exact absurd hj (by simp)
  | cons q cs ih =>
    intro i skip chk ps S h j hj
    rw [kloopRE_cons] at h
    -- the children after the first: from the loop on `cs` started at `i + 1`
    have shift : ∀ skip' chk' ps' S', (∀ I ∈ ps', I ∈ ps) → (kloopRE f g Pn t sym cdir nt sl cs (Nat.succ i) skip' chk' ps' S').1 = true →
        ∀ j', j' < cs.length → j' < skip' ∨ g (cs.getD j' (0, 0)) = true ∨
          (∃ ps'' S'', (∀ I ∈ ps'', I ∈ ps) ∧ (f (cs.getD j' (0, 0)) (i + (j' + 1)) ps'' S'').1 = true) ∨
          (∃ i0 c, (Pn ++ [(t, sym, cdir, nt, sl, i0)], c) ∈ ps ∧ 1 ≤ c ∧ i0 ≤ i + (j' + 1) ∧ i + (j' + 1) < i0 + c) := by
      intro skip' chk' ps' S' hps' h' j' hj'
      rcases ih _ _ _ _ _ h' j' hj' with h1 | h1 | ⟨ps'', S'', hps'', hS''⟩ | ⟨i0, c, hI, hc, h0, h1⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · refine Or.inr (Or.inr (Or.inl ⟨ps'', S'', fun I hI => hps' I (hps'' I hI), ?_⟩))
        rw [show i + (j' + 1) = Nat.succ i + j' by omega]; exact hS''
      · exact Or.inr (Or.inr (Or.inr ⟨i0, c, hps' _ hI, hc, by omega, by omega⟩))
    cases hs : Nat.beq skip 0
    · -- still inside a range
      rw [hs, cond_false] at h
      have hsk : skip ≠ 0 := fun h0 => by rw [h0] at hs; exact absurd hs (by decide)
      rcases j with _ | j
      · exact Or.inl (by omega)
      · rcases shift _ _ _ _ (fun I hI => hI) h j (by simp at hj; omega) with h1 | h1 | h1 | h1
        · exact Or.inl (by rw [Nat.pred_eq_sub_one] at h1; omega)
        · exact Or.inr (Or.inl (by simpa using h1))
        · exact Or.inr (Or.inr (Or.inl (by simpa using h1)))
        · exact Or.inr (Or.inr (Or.inr h1))
    · have hs0 : skip = 0 := Nat.eq_of_beq_eq_true hs
      rw [hs, cond_true] at h
      cases hc : Nat.beq chk 0
      · -- inside a skip run
        rw [hc, cond_false] at h
        cases hg : g q
        · rw [hg, cond_false] at h; exact absurd h Bool.false_ne_true
        · rw [hg, cond_true] at h
          rcases j with _ | j
          · exact Or.inr (Or.inl (by simpa using hg))
          · rcases shift _ _ _ _ (fun I hI => hI) h j (by simp at hj; omega) with h1 | h1 | h1 | h1
            · exact absurd h1 (Nat.not_lt_zero _)
            · exact Or.inr (Or.inl (by simpa using h1))
            · exact Or.inr (Or.inr (Or.inl (by simpa using h1)))
            · exact Or.inr (Or.inr (Or.inr h1))
      · rw [hc, cond_true] at h
        cases hk : (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && Nat.ble 32768 (rd 16 (sk 10 S)))
        · rw [hk, cond_false] at h
          cases hm : (Nat.beq (rd 1 S) 0 && Nat.beq (rd 9 (sk 1 S)) 0 && !Nat.beq (rd 16 (sk 10 S)) 0)
          · -- an ordinary child
            rw [hm, cond_false] at h
            cases hq : (f q i ps S).1
            · rw [hq, cond_false] at h; exact absurd h Bool.false_ne_true
            · rw [hq, cond_true] at h
              rcases j with _ | j
              · exact Or.inr (Or.inr (Or.inl ⟨ps, S, fun I hI => hI, by simpa using hq⟩))
              · rcases shift _ _ _ _ (hf q i ps S) h j (by simp at hj; omega) with h1 | h1 | h1 | h1
                · exact absurd h1 (Nat.not_lt_zero _)
                · exact Or.inr (Or.inl (by simpa using h1))
                · exact Or.inr (Or.inr (Or.inl (by simpa using h1)))
                · exact Or.inr (Or.inr (Or.inr h1))
          · -- a range marker
            rw [hm, cond_true] at h
            have hc1 : rd 16 (sk 10 S) ≠ 0 := by
              intro h0
              rw [h0] at hm
              simp at hm
            cases ps with
            | nil => exact absurd h Bool.false_ne_true
            | cons I0 ps' =>
              rw [kloopRE_rng] at h
              cases he : ((I0.1 == Pn ++ [(t, sym, cdir, nt, sl, i)]) && Nat.beq I0.2 (rd 16 (sk 10 S)))
              · rw [he, cond_false] at h; exact absurd h Bool.false_ne_true
              · rw [he, cond_true] at h
                have hI0 : I0 = (Pn ++ [(t, sym, cdir, nt, sl, i)], rd 16 (sk 10 S)) := by
                  rw [Bool.and_eq_true] at he
                  obtain ⟨h1, h2⟩ := he
                  obtain ⟨P0, c0⟩ := I0
                  have e1 : P0 = Pn ++ [(t, sym, cdir, nt, sl, i)] := beq_iff_eq.mp h1
                  have e2 : c0 = rd 16 (sk 10 S) := Nat.eq_of_beq_eq_true h2
                  rw [e1, e2]
                have hmem : (Pn ++ [(t, sym, cdir, nt, sl, i)], rd 16 (sk 10 S)) ∈ I0 :: ps' := by
                  rw [hI0]; exact List.mem_cons_self
                rcases j with _ | j
                · exact Or.inr (Or.inr (Or.inr ⟨i, rd 16 (sk 10 S), hmem, by omega, by omega, by omega⟩))
                · rcases shift _ _ _ _ (fun I hI => List.mem_cons_of_mem _ hI) h j (by simp at hj; omega) with h1 | h1 | h1 | h1
                  · exact Or.inr (Or.inr (Or.inr ⟨i, rd 16 (sk 10 S), hmem, by omega, by omega,
                      by rw [Nat.pred_eq_sub_one] at h1; omega⟩))
                  · exact Or.inr (Or.inl (by simpa using h1))
                  · exact Or.inr (Or.inr (Or.inl (by simpa using h1)))
                  · exact Or.inr (Or.inr (Or.inr h1))
        · -- a skip-run marker: this child starts the run
          rw [hk, cond_true] at h
          cases hg : g q
          · rw [hg, cond_false] at h; exact absurd h Bool.false_ne_true
          · rw [hg, cond_true] at h
            rcases j with _ | j
            · exact Or.inr (Or.inl (by simpa using hg))
            · rcases shift _ _ _ _ (fun I hI => hI) h j (by simp at hj; omega) with h1 | h1 | h1 | h1
              · exact absurd h1 (Nat.not_lt_zero _)
              · exact Or.inr (Or.inl (by simpa using h1))
              · exact Or.inr (Or.inr (Or.inl (by simpa using h1)))
              · exact Or.inr (Or.inr (Or.inr h1))

/-! ## The walk -/

/-- **the reduced record walk**: `PL.checkSXR` with the root group check, the order rule `ordOK` and skip runs -/
def checkSXRE (lt : Asg → Nat → Bool) (a0 fuel : Nat) :
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
           let kr := kloopRE (fun p i ps S => ih TERMS SS (childSt TERMS SS ACT asg recs t nt p).1 need
               (childSt TERMS SS ACT asg recs t nt p).2.1 (childSt TERMS SS ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) (skipOK a0 asg a) pth.reverse t sym cdir nt sl cs 0 0 0 ps slr.2
           (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 &&
              ((!asg.isEmpty) || Nat.beq a a0) && ordOK TERMS ACT a0 t && kr.1,
            kr.2.1, kr.2.2))))
    fuel

/-! ## Item statements -/

/-- `RefP` with the canonical form: a path's end state refutes every canonical decomposition (below the root) -/
def RefPE (Q : (Nat → Nat) → (Nat → Nat) → Prop) (T n dom need a0 : Nat) (root : Nat × Asg × List Rec) (P : List Step) : Prop :=
  ∀ b c, Inv T n dom b c (walk T (mkSSP T n) need root P).1 (walk T (mkSSP T n) need root P).2.1
      (walk T (mkSSP T n) need root P).2.2 → AsgOK T n b c (walk T (mkSSP T n) need root P).1
        (walk T (mkSSP T n) need root P).2.1 → LGok n need b c → Q b c →
          ((walk T (mkSSP T n) need root P).2.1 ≠ [] → Canon T n a0 b c) → False

/-- the state at the end of path `P` of the leaf with header `R`, Lemma G off -/
abbrev walkRE (R : Nat) (P : List Step) : Nat × Asg × List Rec :=
  walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) 0 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P

/-- every canonical decomposition at the end state of every path of every item is refuted (a part module's statement) -/
def PathsOKRE (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop) (a0 R : Nat) (items : List Item) : Prop :=
  ∀ I ∈ items, ∀ P ∈ expand I,
    RefPE Q (hdr R).2.1 (hdr R).1 (hdr R).2.2.1 0 a0 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P

/-- a range item's record (`PL.forestOK` for the reduced walk). Its own kids loop has no skip runs (`g = false`): a
non-canonical kid is skipped in the parent record, where the decomposition at the node is known; inside each kid's record
(`checkSXRE`) skip runs are allowed -/
def forestOKE (lt : Asg → Nat → Bool) (a0 R : Nat) (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c : Nat)
    (ps : List Item) (cert : Nat) : Bool :=
  let st := walkRE R Pn
  let cs := cands (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 0 st.2.1 st.2.2 t sym cdir nt sl
  Nat.ble (hdr R).1 31 && !Nat.beq c 0 && Nat.ble (i + c) cs.length &&
    (kloopRE (fun p j ps S => checkSXRE lt a0 64 (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1)
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt p).1 0
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt p).2.1
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt p).2.2 (hdr R).2.2.1
        ((t, sym, cdir, nt, sl, j) :: Pn.reverse) ps S)
      (fun _ => false) Pn t sym cdir nt sl ((cs.drop i).take c) i 0 0 ps cert).1

/-- a subtree item's record with inner items (`PL.subMainOKR` for the reduced walk) -/
def subMainOKRE (lt : Asg → Nat → Bool) (a0 R : Nat) (P : List Step) (ps : List Item) (cert : Nat) : Bool :=
  Nat.ble (hdr R).1 31 &&
    (checkSXRE lt a0 64 (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (walkRE R P).1 0 (walkRE R P).2.1 (walkRE R P).2.2
      (hdr R).2.2.1 P.reverse ps cert).1

/-- a plain sub-record (no inner items) of the reduced walk -/
def subOKLE (lt : Asg → Nat → Bool) (a0 R : Nat) (P : List Step) (cert : Nat) : Bool := subMainOKRE lt a0 R P [] cert

/-- a binary tree of item records of the reduced walk -/
def STR.okE (lt : Asg → Nat → Bool) (a0 R : Nat) : STR → Prop
  | .one P cert => subOKLE lt a0 R P cert = true
  | .rng Pn t sym cdir nt sl i c cert => forestOKE lt a0 R Pn t sym cdir nt sl i c [] cert = true
  | .node x y => x.okE lt a0 R ∧ y.okE lt a0 R

/-- **the main record** of the reduced walk: the domain is a mask (no Lemma G), the certificate at bit 514 of the dom block -/
def leafSXRE (lt : Asg → Nat → Bool) (a0 R : Nat) (items : List Item) : Bool :=
  Nat.ble (rd 6 R) 31 && Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 1 &&
    (checkSXRE lt a0 64 (leafT R) (mkSSP (leafT R) (leafN R)) (Nat.pred (Nat.shiftLeft 1 (leafN R))) 0 [] [] (leafDom6 R) []
      items (sk 514 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))).1

/-! ## Soundness -/

/-! ## Swaps keep the node data -/

theorem swap_lt {n u v w : Nat} (hu : u < n) (hv : v < n) (hw : w < n) : Equiv.swap u v w < n := by
  rw [Equiv.swap_apply_def]; split_ifs <;> assumption

/-- swapping two active terms of one group keeps every hit set -/
theorem swap_mem_hitS {T n ACT X u v : Nat} (hu : u < n) (hv : v < n) (hau : ACT.testBit u = true)
    (hav : ACT.testBit v = true) (ha : aT T u = aT T v) (w : Nat) :
    w ∈ hitS T n ACT X ↔ Equiv.swap u v w ∈ hitS T n ACT X := by
  rw [mem_hitS, mem_hitS]
  rcases eq_or_ne w u with rfl | hwu
  · rw [Equiv.swap_apply_left]
    constructor
    · rintro ⟨_, _, h⟩; exact ⟨hv, hav, by rw [← ha]; exact h⟩
    · rintro ⟨_, _, h⟩; exact ⟨hu, hau, by rw [ha]; exact h⟩
  rcases eq_or_ne w v with rfl | hwv
  · rw [Equiv.swap_apply_right]
    constructor
    · rintro ⟨_, _, h⟩; exact ⟨hu, hau, by rw [ha]; exact h⟩
    · rintro ⟨_, _, h⟩; exact ⟨hv, hav, by rw [← ha]; exact h⟩
  · rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]

theorem inv_swap {T n dom ACT : Nat} {asg : Asg} {recs : List Rec} {b c : Nat → Nat} {u v : Nat} (hu : u < n) (hv : v < n)
    (hau : ACT.testBit u = true) (hav : ACT.testBit v = true) (ha : aT T u = aT T v) (hinv : Inv T n dom b c ACT asg recs) :
    Inv T n dom (fun w => b (Equiv.swap u v w)) (fun w => c (Equiv.swap u v w)) ACT asg recs := by
  have hs : ∀ X w, w ∈ hitS T n ACT X ↔ Equiv.swap u v w ∈ hitS T n ACT X := fun X w => swap_mem_hitS hu hv hau hav ha w
  refine ⟨hinv.act, fun t ht => hinv.bc _ (swap_lt hu hv ht), hinv.asg_lt, fun X hX hd => ?_, hinv.root, fun r hr => ?_⟩
  · rw [hinv.hd X hX hd]
    exact (Finset.sum_equiv (Equiv.swap u v) (hs X) (fun _ _ => rfl)).symm
  · obtain ⟨h1, h2, h3⟩ := hinv.recs r hr
    refine ⟨h1, fun s t hsm htm => ?_, fun t htm => h3 _ ((hs r.X t).mp htm)⟩
    rw [h2 _ _ ((hs r.X s).mp hsm) ((hs r.X t).mp htm)]
    simp only [(Equiv.swap u v).injective.eq_iff]

theorem asgOK_swap {T n ACT : Nat} {asg : Asg} {b c : Nat → Nat} {u v : Nat} (hau : ACT.testBit u = true)
    (hav : ACT.testBit v = true) (h : AsgOK T n b c ACT asg) :
    AsgOK T n (fun w => b (Equiv.swap u v w)) (fun w => c (Equiv.swap u v w)) ACT asg := by
  obtain ⟨ts, hnd, hmem, he⟩ := h
  refine ⟨ts, hnd, hmem, ?_⟩
  rw [he]
  apply List.map_congr_left
  intro t ht
  have hf := ((hmem t).mp ht).2
  have htu : t ≠ u := fun e => by rw [e, hau] at hf; exact absurd hf (by decide)
  have htv : t ≠ v := fun e => by rw [e, hav] at hf; exact absurd hf (by decide)
  simp only [Equiv.swap_apply_of_ne_of_ne htu htv]

/-- the lift predicate is swap-invariant (its set of outside terms is permuted) -/
theorem swapInv_QK (T n Em k : Nat) : SwapInv T n (QK n Em k) := by
  intro b c u v hu hv _ h
  obtain ⟨P, hP, hP2, f, g, hfg, hX⟩ := h
  refine ⟨P, hP, hP2, f, g, hfg, fun X hXl => ?_⟩
  obtain ⟨S, hS, he⟩ := hX X hXl
  refine ⟨S.map (Equiv.swap u v).toEmbedding, fun x hx => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_range.mpr (swap_lt hu hv (Finset.mem_range.mp (hS hs)))
  · rw [Finset.sum_map]
    simp only [Equiv.toEmbedding_apply, Equiv.swap_apply_self]
    exact he

/-! ## The potential `Σ w · key` and canonicalisation -/

/-- the potential of a decomposition: `Σ_{w < n} w · key(b w, c w)`; a swap of an inverted pair raises it -/
def phi (n : Nat) (b c : Nat → Nat) : Nat := ∑ w ∈ Finset.range n, w * keyP (b w) (c w)

theorem phi_swap (n u v : Nat) (hu : u < n) (hv : v < n) (huv : u ≠ v) (b c : Nat → Nat) :
    phi n (fun w => b (Equiv.swap u v w)) (fun w => c (Equiv.swap u v w)) + u * keyP (b u) (c u) + v * keyP (b v) (c v) =
      phi n b c + u * keyP (b v) (c v) + v * keyP (b u) (c u) := by
  unfold phi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hu), ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hu)]
  have hv' : v ∈ (Finset.range n).erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_range.mpr hv⟩
  rw [← Finset.add_sum_erase _ _ hv', ← Finset.add_sum_erase _ _ hv']
  have hrest : ∑ w ∈ ((Finset.range n).erase u).erase v, w * keyP (b (Equiv.swap u v w)) (c (Equiv.swap u v w)) =
      ∑ w ∈ ((Finset.range n).erase u).erase v, w * keyP (b w) (c w) := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]
  rw [hrest]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

theorem phi_le (n : Nat) (b c : Nat → Nat) (hbc : BC n b c) : phi n b c ≤ n * (n * 262144) := by
  unfold phi
  have h : ∀ w ∈ Finset.range n, w * keyP (b w) (c w) ≤ n * 262144 := by
    intro w hw
    have hwn := Finset.mem_range.mp hw
    obtain ⟨_, hb, _, hc⟩ := hbc w hwn
    have hk : keyP (b w) (c w) ≤ 262144 := by unfold keyP; omega
    exact Nat.mul_le_mul (by omega) hk
  calc ∑ w ∈ Finset.range n, w * keyP (b w) (c w) ≤ ∑ _w ∈ Finset.range n, n * 262144 := Finset.sum_le_sum h
    _ = n * (n * 262144) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- one swap of an inverted pair outside `a0`'s group: the node data and `Q` are kept, the potential rises, `a0`'s group is fixed -/
theorem canon_step (Q : (Nat → Nat) → (Nat → Nat) → Prop) (T n dom a0 ACT : Nat) (asg : Asg) (recs : List Rec)
    (hQ : SwapInv T n Q) (hact : ∀ u, u < n → aT T u ≠ a0 → ACT.testBit u = true) (b c : Nat → Nat)
    (hinv : Inv T n dom b c ACT asg recs) (hasg : AsgOK T n b c ACT asg) (hq : Q b c) (hcan : ¬ Canon T n a0 b c) :
    ∃ b' c' : Nat → Nat, Inv T n dom b' c' ACT asg recs ∧ AsgOK T n b' c' ACT asg ∧ Q b' c' ∧ phi n b c < phi n b' c' ∧
      ∀ w, aT T w = a0 → b' w = b w ∧ c' w = c w := by
  obtain ⟨u, v, huv, hvn, ha, ha0, hk⟩ : ∃ u v, u < v ∧ v < n ∧ aT T u = aT T v ∧ aT T u ≠ a0 ∧
      keyP (b v) (c v) < keyP (b u) (c u) := by
    by_contra hne
    apply hcan
    intro u v huv hvn ha ha0
    by_contra hlt
    exact hne ⟨u, v, huv, hvn, ha, ha0, Nat.lt_of_not_le hlt⟩
  have hun : u < n := by omega
  have hau := hact u hun ha0
  have hav := hact v hvn (by rw [← ha]; exact ha0)
  refine ⟨fun w => b (Equiv.swap u v w), fun w => c (Equiv.swap u v w), inv_swap hun hvn hau hav ha hinv,
    asgOK_swap hau hav hasg, hQ b c u v hun hvn ha hq, ?_, fun w hw => ?_⟩
  · have e := phi_swap n u v hun hvn (by omega) b c
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt huv
    obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_lt hk
    rw [hf] at e
    nlinarith
  · have hwu : w ≠ u := fun e => ha0 (e ▸ hw)
    have hwv : w ≠ v := fun e => ha0 (ha ▸ e ▸ hw)
    simp only [Equiv.swap_apply_of_ne_of_ne hwu hwv, and_self]

/-- **canonicalisation**: at a node whose active terms include every term outside `a0`'s group, a decomposition can be made
canonical by swaps inside those groups, keeping the node data, `Q`, and every term of `a0`'s group -/
theorem canon_exists (Q : (Nat → Nat) → (Nat → Nat) → Prop) (T n dom a0 ACT : Nat) (asg : Asg) (recs : List Rec)
    (hQ : SwapInv T n Q) (hact : ∀ u, u < n → aT T u ≠ a0 → ACT.testBit u = true) (b c : Nat → Nat)
    (hinv : Inv T n dom b c ACT asg recs) (hasg : AsgOK T n b c ACT asg) (hq : Q b c) :
    ∃ b' c' : Nat → Nat, Inv T n dom b' c' ACT asg recs ∧ AsgOK T n b' c' ACT asg ∧ Q b' c' ∧ Canon T n a0 b' c' ∧
      ∀ u, aT T u = a0 → b' u = b u ∧ c' u = c u := by
  suffices h : ∀ m, ∀ b c : Nat → Nat, n * (n * 262144) - phi n b c ≤ m → Inv T n dom b c ACT asg recs →
      AsgOK T n b c ACT asg → Q b c → ∃ b' c' : Nat → Nat, Inv T n dom b' c' ACT asg recs ∧ AsgOK T n b' c' ACT asg ∧
        Q b' c' ∧ Canon T n a0 b' c' ∧ ∀ u, aT T u = a0 → b' u = b u ∧ c' u = c u from h _ b c le_rfl hinv hasg hq
  intro m
  induction m with
  | zero =>
    intro b c hm hinv hasg hq
    by_cases hcan : Canon T n a0 b c
    · exact ⟨b, c, hinv, hasg, hq, hcan, fun _ _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨b', c', hinv', _, _, hlt, _⟩ := canon_step Q T n dom a0 ACT asg recs hQ hact b c hinv hasg hq hcan
      have := phi_le n b' c' hinv'.bc
      omega
  | succ m ih =>
    intro b c hm hinv hasg hq
    by_cases hcan : Canon T n a0 b c
    · exact ⟨b, c, hinv, hasg, hq, hcan, fun _ _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨b', c', hinv', hasg', hq', hlt, hfix⟩ := canon_step Q T n dom a0 ACT asg recs hQ hact b c hinv hasg hq hcan
      have := phi_le n b' c' hinv'.bc
      obtain ⟨b'', c'', h1, h2, h3, h4, h5⟩ := ih b' c' (by omega) hinv' hasg' hq'
      refine ⟨b'', c'', h1, h2, h3, h4, fun w hw => ?_⟩
      obtain ⟨e1, e2⟩ := h5 w hw
      obtain ⟨f1, f2⟩ := hfix w hw
      exact ⟨e1.trans f1, e2.trans f2⟩

theorem checkSXRE_succ (lt : Asg → Nat → Bool) (a0 fuel TERMS SS ACT need : Nat) (asg : Asg) (recs : List Rec) (dom : Nat)
    (pth : List Step) (ps : List Item) (S : Nat) :
    checkSXRE lt a0 (fuel + 1) TERMS SS ACT need asg recs dom pth ps S =
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
           let kr := kloopRE (fun p i ps S => checkSXRE lt a0 fuel TERMS SS (childSt TERMS SS ACT asg recs t nt p).1 need
               (childSt TERMS SS ACT asg recs t nt p).2.1 (childSt TERMS SS ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) (skipOK a0 asg a) pth.reverse t sym cdir nt sl cs 0 0 0 ps slr.2
           (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 &&
              ((!asg.isEmpty) || Nat.beq a a0) && ordOK TERMS ACT a0 t && kr.1,
            kr.2.1, kr.2.2))) := rfl

theorem checkSXRE_ps (lt : Asg → Nat → Bool) (a0 TERMS SS need dom : Nat) : ∀ fuel ACT asg recs pth ps S,
    ∀ I ∈ (checkSXRE lt a0 fuel TERMS SS ACT need asg recs dom pth ps S).2.1, I ∈ ps := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs pth ps S I hI; exact hI
  | succ fuel ih =>
    intro ACT asg recs pth ps S I hI
    rw [checkSXRE_succ] at hI
    revert hI
    cases Nat.beq (rd 1 S) 0
    · rw [cond_false]
      cases Nat.beq (rd 6 S) 63
      · rw [cond_false]
        intro hI
        exact kloopRE_ps _ _ _ _ _ _ _ _ (fun p i ps S => ih _ _ _ _ ps S) _ _ _ _ _ _ I hI
      · rw [cond_true]; intro hI; exact hI
    · rw [cond_true]
      cases Nat.beq (rd 9 (sk 1 S)) 0
      · rw [cond_false]; intro hI; exact hI
      · rw [cond_true]
        cases ps with
        | nil => intro hI; exact absurd hI List.not_mem_nil
        | cons I0 ps' => intro hI; exact List.mem_cons_of_mem _ hI

/-- at the root (empty assignment) every term is active -/
theorem act_of_root {T n ACT : Nat} {b c : Nat → Nat} (hasg : AsgOK T n b c ACT []) (u : Nat) (hu : u < n) :
    ACT.testBit u = true := by
  obtain ⟨ts, _, hmem, he⟩ := hasg
  have hts : ts = [] := by
    cases ts with
    | nil => rfl
    | cons x xs => simp at he
  by_contra h
  have hm : u ∈ ts := (hmem u).mpr ⟨hu, by simpa using h⟩
  rw [hts] at hm
  exact absurd hm List.not_mem_nil

theorem testBit_xor_one_shiftLeft {ACT t u : Nat} (h : u ≠ t) : (ACT ^^^ 1 <<< t).testBit u = ACT.testBit u := by
  rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  have : decide (t = u) = false := by simp [Ne.symm h]
  rw [this, Bool.xor_false]

/-- **the skip runs are sound**: a canonical decomposition's own candidate at a branch node is never skippable, given the
order rule and the assignment's correctness -/
theorem skipOK_canon {T n ACT a0 t : Nat} {asg : Asg} {b c : Nat → Nat} (hn : n ≤ 32) (htn : t < n)
    (hact : ACT.testBit t = true) (hasg : AsgOK T n b c ACT asg) (hcan : Canon T n a0 b c)
    (hord : ordOK T ACT a0 t = true) : skipOK a0 asg (aT T t) (b t, c t) = false := by
  unfold skipOK
  cases hz : Nat.beq (aT T t) a0
  · have hne0 : aT T t ≠ a0 := fun e => by rw [e] at hz; simp at hz
    simp only [Bool.not_false, Bool.true_and]
    rw [List.any_eq_false]
    intro e he hcond
    obtain ⟨ts, hnd, hmem, rfl⟩ := hasg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    obtain ⟨hun, hfu⟩ := (hmem u).mp hu
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨hau, hlt⟩ := hcond
    have hau' : aT T u = aT T t := Nat.eq_of_beq_eq_true hau
    have hlt' : keyP (b t) (c t) < keyP (b u) (c u) := Nat.le_of_ble_eq_true hlt
    unfold ordOK at hord
    rw [hz, Bool.false_or, List.all_eq_true] at hord
    have hcu := hord u (List.mem_range.mpr (by omega))
    have hbitu : bit ACT u = false := by rw [S5.bit_eq]; exact hfu
    rw [hbitu, Bool.or_false, hau, Bool.true_and] at hcu
    have hut : ¬ t < u := by
      intro h
      have hb : Nat.blt t u = true := Nat.blt_eq.mpr h
      rw [hb] at hcu
      exact absurd hcu (by decide)
    have hne : u ≠ t := fun e => by rw [e, hact] at hfu; exact absurd hfu (by decide)
    have := hcan u t (by omega) htn hau' (by rw [hau']; exact hne0)
    omega
  · simp

/-- **Records of the reduced walk.** An accepted record refutes every decomposition at its node with `Q` that is canonical
(below the root), given that every canonical decomposition at the end state of each path of each external item is refuted -/
theorem checkSXRE_sound (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (T n dom a0 : Nat) (hn : n ≤ 31) (hswap : SwapInv T n Q)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK T n b c 0 asg → Q b c → False)
    (root : Nat × Asg × List Rec) (items : List Item)
    (H : ∀ I ∈ items, ∀ P ∈ expand I, RefPE Q T n dom 0 a0 root P) :
    ∀ fuel ACT asg recs (pth : List Step) (ps : List Item) S, (∀ I ∈ ps, I ∈ items) →
      (ACT, asg, recs) = walk T (mkSSP T n) 0 root pth.reverse →
      (checkSXRE lt a0 fuel T (mkSSP T n) ACT 0 asg recs dom pth ps S).1 = true →
      ∀ b c, Inv T n dom b c ACT asg recs → AsgOK T n b c ACT asg → Q b c → (asg ≠ [] → Canon T n a0 b c) → False := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs pth ps S _ _ h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro ACT asg recs pth ps S hps hst hchk b c hinv hasg hq hcan
    have hlg : LGok n 0 b c := lgok_zero n b c hinv.bc
    rw [checkSXRE_succ] at hchk
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
          let cs := cands T (mkSSP T n) ACT 0 asg recs t sym cdir nt sl
          let ss := mkSls6 (mkSSP T n) ACT asg sl
          let kr := kloopRE (fun p i ps S => checkSXRE lt a0 fuel T (mkSSP T n) (childSt T (mkSSP T n) ACT asg recs t nt p).1 0
               (childSt T (mkSSP T n) ACT asg recs t nt p).2.1 (childSt T (mkSSP T n) ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) (skipOK a0 asg a) pth.reverse t sym cdir nt sl cs 0 0 0 ps slr.2
          (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 &&
            ((!asg.isEmpty) || Nat.beq a a0) && ordOK T ACT a0 t && kr.1) = true → False
        intro S1 t sym cdir ntr slr nt sl a nr cs ss kr hchk
        have ha : a = aT T t := rfl
        have hcs : cs = brCands7 (mkSSP T n) ACT 0 asg recs t a nt sl sym cdir := rfl
        have hnr : nr = mkRecs6 (mkSSP T n) ACT asg nt [] := rfl
        have hss : ss = mkSls6 (mkSSP T n) ACT asg sl := rfl
        have hkr : kr = kloopRE (fun p i ps S => checkSXRE lt a0 fuel T (mkSSP T n) (childSt T (mkSSP T n) ACT asg recs t nt p).1
             0 (childSt T (mkSSP T n) ACT asg recs t nt p).2.1 (childSt T (mkSSP T n) ACT asg recs t nt p).2.2 dom
             ((t, sym, cdir, nt, sl, i) :: pth) ps S) (skipOK a0 asg a) pth.reverse t sym cdir nt sl cs 0 0 0 ps slr.2 := rfl
        have hnt : ∀ x ∈ nt, x < 512 := rdList_lt _ _
        have hsl : ∀ x ∈ sl, x < 512 := rdList_lt _ _
        have hcs' : cs = cands T (mkSSP T n) ACT 0 asg recs t sym cdir nt sl := rfl
        clear_value S1 t sym cdir ntr slr nt sl a nr cs ss kr
        subst ha hnr hss hkr
        simp only [Bool.and_eq_true] at hchk
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hroot⟩, hord⟩, h8⟩ := hchk
        have hact : ACT.testBit t = true := by rw [← S5.bit_eq]; exact h1
        have htn : t < n := hinv.act t hact
        obtain ⟨p, hp, b', c', hinv', hlg', hpe, hmove'⟩ := br_step7_ex T n dom 0 (by omega) (mkSSP T n)
          (mkSSP_ok T n (by omega)) ACT asg recs t sym cdir nt sl hnt hsl h1 h2 h3 h4 h5 h6 h7 b c hinv hlg
        rw [← hcs] at hp
        obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
        have hgd : cs.getD j (0, 0) = p := by rw [List.getD_eq_getElem _ _ hj, hpj]
        have hst' : childSt T (mkSSP T n) ACT asg recs t nt p =
            walk T (mkSSP T n) 0 root ((t, sym, cdir, nt, sl, j) :: pth).reverse := by
          rw [List.reverse_cons, walk_append, ← hst]
          show childSt T (mkSSP T n) ACT asg recs t nt p =
            childSt T (mkSSP T n) ACT asg recs t nt ((cands T (mkSSP T n) ACT 0 asg recs t sym cdir nt sl).getD j (0, 0))
          rw [← hcs', hgd]
        have hasg' : AsgOK T n b' c' (ACT ^^^ 1 <<< t) ((aT T t, p.1, p.2) :: asg) := by
          rw [hpe]; exact asgOK_step (asgOK_move hasg hmove') t htn hact
        have hq' := q_of_move Q hmove hmove' hq
        -- the decomposition carried below the node: canonical
        obtain ⟨b'', c'', hinv'', hasg'', hq'', hcan'', hpe''⟩ : ∃ b'' c'' : Nat → Nat,
            Inv T n dom b'' c'' (ACT ^^^ 1 <<< t) ((aT T t, p.1, p.2) :: asg)
              (updRecs (aT T t) p.1 p.2 (brAllr7 (mkSSP T n) ACT asg recs nt)) ∧
            AsgOK T n b'' c'' (ACT ^^^ 1 <<< t) ((aT T t, p.1, p.2) :: asg) ∧ Q b'' c'' ∧ Canon T n a0 b'' c'' ∧
            p = (b'' t, c'' t) := by
          by_cases hae : asg = []
          · -- the root: canonicalise the moved decomposition at the child, where only `t` (in `a0`'s group) is assigned
            have ha0 : aT T t = a0 := by
              have hr := hroot
              rw [hae] at hr
              simpa using hr
            have hall : ∀ u, u < n → aT T u ≠ a0 → (ACT ^^^ 1 <<< t).testBit u = true := by
              intro u hu hua
              have hut : u ≠ t := fun e => hua (e ▸ ha0)
              rw [testBit_xor_one_shiftLeft hut]
              rw [hae] at hasg
              exact act_of_root hasg u hu
            obtain ⟨b'', c'', e1, e2, e3, e4, e5⟩ := canon_exists Q T n dom a0 _ _ _ hswap hall b' c' hinv' hasg' hq'
            obtain ⟨f1, f2⟩ := e5 t ha0
            exact ⟨b'', c'', e1, e2, e3, e4, by rw [hpe, f1, f2]⟩
          · -- below the root the step does not move the decomposition
            have hmv : b' = b ∧ c' = c := by
              rcases hmove' with h | ⟨h, _⟩
              · exact h
              · exact absurd h hae
            obtain ⟨rfl, rfl⟩ := hmv
            exact ⟨b', c', hinv', hasg', hq', hcan hae, hpe⟩
        rcases kloopRE_ok _ _ _ _ _ _ _ _ (fun p i ps S => checkSXRE_ps lt a0 _ _ _ _ _ _ _ _ _ ps S) cs 0 0 0 ps slr.2 h8 j hj with
          h0 | hg | ⟨ps', S', hps', hS'⟩ | ⟨i0, c0, hI, hc0, hi0, hj0⟩
        · exact absurd h0 (Nat.not_lt_zero _)
        · -- a skipped child: never the candidate of a canonical decomposition
          rw [hgd] at hg
          by_cases hae : asg = []
          · rw [hae] at hg
            simp [skipOK] at hg
          · have hmv : b' = b ∧ c' = c := by
              rcases hmove' with h | ⟨h, _⟩
              · exact h
              · exact absurd h hae
            obtain ⟨rfl, rfl⟩ := hmv
            rw [hpe, skipOK_canon (by omega) htn hact hasg (hcan hae) hord] at hg
            exact absurd hg Bool.false_ne_true
        · rw [hgd, Nat.zero_add] at hS'
          rw [childSt_eq] at hst' hS'
          exact ih _ _ _ _ ps' S' (fun I hI => hps I (hps' I hI)) hst' hS' b'' c'' hinv'' hasg'' hq'' (fun _ => hcan'')
        · -- child `j` lies in a range item: its path is one of the item's paths
          have hmem := mem_expand_range pth.reverse t sym cdir nt sl i0 c0 j hc0 (by omega) (by omega)
          have hR := H _ (hps _ hI) _ hmem b'' c''
          rw [List.reverse_cons] at hst'
          rw [← hst', childSt_eq] at hR
          exact hR hinv'' hasg'' (lgok_zero n b'' c'' hinv''.bc) hq'' (fun _ => hcan'')
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
          exact hR hinv hasg hlg hq hcan

/-- the leaf test that accepts nothing and the lift invariant are swap-invariant -/
theorem swapInv_QT (T n : Nat) : SwapInv T n QT := fun _ _ _ _ _ _ _ _ => trivial

theorem pathsOKRE_append {lt : Asg → Nat → Bool} {Q : (Nat → Nat) → (Nat → Nat) → Prop} {a0 R : Nat} {l1 l2 : List Item}
    (h1 : PathsOKRE lt Q a0 R l1) (h2 : PathsOKRE lt Q a0 R l2) : PathsOKRE lt Q a0 R (l1 ++ l2) := by
  intro I hI
  rcases List.mem_append.mp hI with h | h
  · exact h1 I h
  · exact h2 I h

theorem pathsOKRE_nil {lt : Asg → Nat → Bool} {Q : (Nat → Nat) → (Nat → Nat) → Prop} {a0 R : Nat} : PathsOKRE lt Q a0 R [] :=
  fun I hI => absurd hI List.not_mem_nil

/-- **a range item of the reduced walk is refuted**, given its inner items -/
theorem pathsOKRE_of_forest (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (a0 R : Nat) (hswap : SwapInv (hdr R).2.1 (hdr R).1 Q)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c : Nat) (ps : List Item) (cert : Nat)
    (h : forestOKE lt a0 R Pn t sym cdir nt sl i c ps cert = true) (hsub : PathsOKRE lt Q a0 R ps) :
    PathsOKRE lt Q a0 R [(Pn ++ [(t, sym, cdir, nt, sl, i)], c)] := by
  unfold forestOKE at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hn, hc⟩, hlen⟩, hk⟩ := h
  have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hc; exact absurd hc (by decide)
  intro I hI P hP
  rw [List.mem_singleton] at hI
  subst hI
  obtain ⟨k, hk', rfl⟩ := expand_range_cases Pn t sym cdir nt sl i c hc0 P hP
  intro b0 c0 hinv hasg hlg hq hcan
  set st := walkRE R Pn with hstdef
  set cs := cands (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 0 st.2.1 st.2.2 t sym cdir nt sl with hcsdef
  have hlen' : ((cs.drop i).take c).length = c := by
    rw [List.length_take, List.length_drop]; omega
  have hget : ((cs.drop i).take c).getD k (0, 0) = cs.getD (i + k) (0, 0) := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp [List.getElem_take, List.getElem_drop]
  have hwalk : walkRE R (Pn ++ [(t, sym, cdir, nt, sl, i + k)]) =
      childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0)) := by
    show walk _ _ _ _ (Pn ++ [(t, sym, cdir, nt, sl, i + k)]) = _
    rw [walk_append]
    rfl
  rcases kloopRE_ok _ _ _ _ _ _ _ _ (fun p i ps S => checkSXRE_ps lt a0 _ _ _ _ _ _ _ _ _ ps S) _ i 0 0 ps cert hk k (by omega) with
    h0 | hg | ⟨ps', S', hps', hS'⟩ | ⟨i0, c1, hI, hc1, hi0, hj0⟩
  · exact absurd h0 (Nat.not_lt_zero _)
  · exact absurd hg Bool.false_ne_true
  · rw [hget] at hS'
    have hst : ((childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0))).1,
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0))).2.1,
        (childSt (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) st.1 st.2.1 st.2.2 t nt (cs.getD (i + k) (0, 0))).2.2) =
        walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) 0 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], [])
          ((t, sym, cdir, nt, sl, i + k) :: Pn.reverse).reverse := by
      rw [List.reverse_cons, List.reverse_reverse]
      exact hwalk.symm
    have hinv' := hinv
    have hasg' := hasg
    have hcan' := hcan
    change Inv _ _ _ b0 c0 (walkRE R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).1
      (walkRE R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).2.1 (walkRE R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).2.2 at hinv'
    change AsgOK _ _ b0 c0 (walkRE R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).1
      (walkRE R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).2.1 at hasg'
    change (walkRE R (Pn ++ [(t, sym, cdir, nt, sl, i + k)])).2.1 ≠ [] → Canon _ _ a0 b0 c0 at hcan'
    rw [hwalk] at hinv' hasg' hcan'
    exact checkSXRE_sound lt Q hmove _ _ _ a0 hn hswap hleaf (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) ps hsub 64 _ _ _ _ ps' S'
      hps' hst hS' b0 c0 hinv' hasg' hq hcan'
  · exact hsub _ hI _ (mem_expand_range Pn t sym cdir nt sl i0 c1 (i + k) hc1 hi0 hj0) b0 c0 hinv hasg hlg hq hcan

theorem pathsOKRE_of_submain (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (a0 R : Nat) (hswap : SwapInv (hdr R).2.1 (hdr R).1 Q)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (P : List Step) (ps : List Item) (cert : Nat) (h : subMainOKRE lt a0 R P ps cert = true) (hsub : PathsOKRE lt Q a0 R ps) :
    PathsOKRE lt Q a0 R [(P, 0)] := by
  intro I hI P' hP' b c hinv hasg hlg hq hcan
  rw [List.mem_singleton] at hI
  subst hI
  have hP : P' = P := List.mem_singleton.mp hP'
  subst hP
  unfold subMainOKRE at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  exact checkSXRE_sound lt Q hmove _ _ _ a0 h.1 hswap hleaf (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) ps hsub 64 _ _ _
    P'.reverse ps cert (fun x hx => hx) (by rw [List.reverse_reverse]) h.2 b c hinv hasg hq hcan

theorem pathsOKRE_of_sub (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (a0 R : Nat) (hswap : SwapInv (hdr R).2.1 (hdr R).1 Q)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (P : List Step) (cert : Nat) (h : subOKLE lt a0 R P cert = true) : PathsOKRE lt Q a0 R [(P, 0)] :=
  pathsOKRE_of_submain lt Q hmove a0 R hswap hleaf P [] cert h pathsOKRE_nil

theorem pathsOKRE_of_str (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (a0 R : Nat) (hswap : SwapInv (hdr R).2.1 (hdr R).1 Q)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False) :
    ∀ t : STR, t.okE lt a0 R → PathsOKRE lt Q a0 R t.items := by
  intro t
  induction t with
  | one P cert => intro h; exact pathsOKRE_of_sub lt Q hmove a0 R hswap hleaf P cert h
  | rng Pn t sym cdir nt sl i c cert =>
    intro h; exact pathsOKRE_of_forest lt Q hmove a0 R hswap hleaf Pn t sym cdir nt sl i c [] cert h pathsOKRE_nil
  | node a b iha ihb => intro h; exact pathsOKRE_append (iha h.1) (ihb h.2)

/-- **the aggregator** of the reduced walk: the main record and the items' statements refute every decomposition with `Q` -/
theorem leafSXRE_sound_paths (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (a0 R : Nat) (hswap : SwapInv (leafT R) (leafN R) Q)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (leafT R) (leafN R) b c 0 asg → Q b c → False)
    (items : List Item) (hmain : leafSXRE lt a0 R items = true) (hparts : PathsOKRE lt Q a0 R items)
    (b c : Nat → Nat) (hbc : BC (leafN R) b c)
    (hd : ∀ X, X < 512 → (leafDom6 R).testBit X = true →
      TX (toM3 X) = ∑ t ∈ (Finset.range (leafN R)).filter (fun t => par (aT (leafT R) t &&& X) = true),
        vecMulVec (nv (b t)) (nv (c t))) (hq : Q b c) : False := by
  unfold leafSXRE at hmain
  simp only [Bool.and_eq_true] at hmain
  obtain ⟨⟨hn, _⟩, hmain⟩ := hmain
  have hn' : leafN R ≤ 31 := Nat.le_of_ble_eq_true hn
  have epred : Nat.pred (Nat.shiftLeft 1 (leafN R)) = 2 ^ leafN R - 1 := by
    show 1 <<< leafN R - 1 = _; rw [Nat.one_shiftLeft]
  have hinv0 : Inv (leafT R) (leafN R) (leafDom6 R) b c (Nat.pred (Nat.shiftLeft 1 (leafN R))) [] [] := by
    rw [epred]; exact S5.inv_root _ _ _ b c hbc hd
  have hasg0 : AsgOK (leafT R) (leafN R) b c (Nat.pred (Nat.shiftLeft 1 (leafN R))) [] := by
    rw [epred]; exact asgOK_root _ _ b c
  have H : ∀ I ∈ items, ∀ P ∈ expand I,
      RefPE Q (leafT R) (leafN R) (leafDom6 R) 0 a0 (Nat.pred (Nat.shiftLeft 1 (leafN R)), [], []) P :=
    fun I hI P hP => hparts I hI P hP
  exact checkSXRE_sound lt Q hmove (leafT R) (leafN R) (leafDom6 R) a0 hn' hswap hleaf _ items H 64 _ [] [] [] items _
    (fun I hI => hI) rfl hmain b c hinv0 hasg0 hq (fun h => absurd rfl h)

/-- **a split leaf of the reduced walk**: the main record and its items' statements give `NoLiftK` -/
theorem noLiftK_of_itemsE (pts : List Nat) (k Em a0 : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (items : List Item)
    (hmain : leafSXRE (ltW3 pts k) a0 R items = true) (hparts : PathsOKRE (ltW3 pts k) (QK (leafN R) Em k) a0 R items) :
    L479.NoLiftK (leafT R) (leafN R) (S6.leafDom6 R) Em k := by
  intro b c hbc hd hl
  exact leafSXRE_sound_paths (ltW3 pts k) (QK (leafN R) Em k)
    (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) a0 R (swapInv_QK _ _ _ _)
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) items hmain hparts
    b c hbc hd hl

/-- **an UNSAT split leaf of the reduced walk**: the main record and its items' statements give `NoDecomp` -/
theorem noDecomp_of_itemsE (a0 R : Nat) (items : List Item) (hmain : leafSXRE ltF a0 R items = true)
    (hparts : PathsOKRE ltF QT a0 R items) : S5.NoDecomp (leafT R) (leafN R) (S6.leafDom6 R) := by
  rintro ⟨b, c, hbc, hd⟩
  exact leafSXRE_sound_paths ltF QT qT_move a0 R (swapInv_QT _ _) (ltF_leaf _ _) items hmain hparts b c hbc hd trivial

end

end PL

namespace PL
open BC4 BC5 BC6s BC7s S5 S6 S7 RootSound Matrix BC7T S7L BC7x S7X
noncomputable section

/-! ## Instances: the plane lift (`ltW3`, `QK`) and NoDecomp (`ltF`, `QT`) -/

theorem pathsOKRE_of_strW3 (pts : List Nat) (k Em a0 : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (t : STR) (ht : t.okE (ltW3 pts k) a0 R) :
    PathsOKRE (ltW3 pts k) (QK (leafN R) Em k) a0 R t.items :=
  pathsOKRE_of_str (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) a0 R
    (swapInv_QK _ _ _ _) (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) t ht

theorem pathsOKRE_of_submainW3 (pts : List Nat) (k Em a0 : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (P : List Step) (ps : List Item)
    (cert : Nat) (h : subMainOKRE (ltW3 pts k) a0 R P ps cert = true)
    (hsub : PathsOKRE (ltW3 pts k) (QK (leafN R) Em k) a0 R ps) :
    PathsOKRE (ltW3 pts k) (QK (leafN R) Em k) a0 R [(P, 0)] :=
  pathsOKRE_of_submain (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h)
    a0 R (swapInv_QK _ _ _ _) (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq))
    P ps cert h hsub

theorem pathsOKRE_of_forestW3 (pts : List Nat) (k Em a0 : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (Pn : List Step) (t : Nat) (sym cdir : Bool)
    (nt sl : List Nat) (i c : Nat) (ps : List Item) (cert : Nat)
    (h : forestOKE (ltW3 pts k) a0 R Pn t sym cdir nt sl i c ps cert = true)
    (hsub : PathsOKRE (ltW3 pts k) (QK (leafN R) Em k) a0 R ps) :
    PathsOKRE (ltW3 pts k) (QK (leafN R) Em k) a0 R [(Pn ++ [(t, sym, cdir, nt, sl, i)], c)] :=
  pathsOKRE_of_forest (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h)
    a0 R (swapInv_QK _ _ _ _) (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq))
    Pn t sym cdir nt sl i c ps cert h hsub

theorem pathsOKRE_of_strF (a0 R : Nat) (t : STR) (ht : t.okE ltF a0 R) : PathsOKRE ltF QT a0 R t.items :=
  pathsOKRE_of_str ltF QT qT_move a0 R (swapInv_QT _ _) (ltF_leaf _ _) t ht

theorem pathsOKRE_of_submainF (a0 R : Nat) (P : List Step) (ps : List Item) (cert : Nat)
    (h : subMainOKRE ltF a0 R P ps cert = true) (hsub : PathsOKRE ltF QT a0 R ps) : PathsOKRE ltF QT a0 R [(P, 0)] :=
  pathsOKRE_of_submain ltF QT qT_move a0 R (swapInv_QT _ _) (ltF_leaf _ _) P ps cert h hsub

theorem pathsOKRE_of_forestF (a0 R : Nat) (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c : Nat)
    (ps : List Item) (cert : Nat) (h : forestOKE ltF a0 R Pn t sym cdir nt sl i c ps cert = true)
    (hsub : PathsOKRE ltF QT a0 R ps) : PathsOKRE ltF QT a0 R [(Pn ++ [(t, sym, cdir, nt, sl, i)], c)] :=
  pathsOKRE_of_forest ltF QT qT_move a0 R (swapInv_QT _ _) (ltF_leaf _ _) Pn t sym cdir nt sl i c ps cert h hsub

end
end PL

#print axioms PL.canon_exists
#print axioms PL.checkSXRE_sound
#print axioms PL.pathsOKRE_of_forest
#print axioms PL.pathsOKRE_of_submain
#print axioms PL.pathsOKRE_of_str
#print axioms PL.leafSXRE_sound_paths
#print axioms PL.noLiftK_of_itemsE
#print axioms PL.noDecomp_of_itemsE
#print axioms PL.swapInv_QK
#print axioms PL.pathsOKRE_of_strW3
#print axioms PL.pathsOKRE_of_forestW3
#print axioms PL.pathsOKRE_of_strF
