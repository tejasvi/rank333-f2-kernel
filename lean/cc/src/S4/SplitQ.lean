module
public import R22Port.U_d41d8cd98f00
public import S4.PlaneW3
public import S7.Split
/-! # Split SAT leaves: v7x (main record + sub-records) with SAT leaves and any invariant `Q`

A big SAT-leaf certificate is cut into a **main record** and **sub-records**, each checked as its own declaration (bounded
memory per declaration).
* `PL.checkSXL lt`: `BC7x.checkSX` with BC7L's SAT leaves (`t = 31`, `ACT = 0`, the leaf test `lt asg w`). A dead
  node with `X = 0` is an external marker: it takes the next sub-record path, which must be its own.
* `PL.subOKL lt R P cert`: the subtree at path `P`, replayed from the root by `BC7x.walk`, then checked by
  `BC7L.checkSL lt` from there.
* `PL.leafSXL lt R paths`: the main record.

Soundness (as `S7/Split.lean`, with `AsgOK` and `Q` carried as in `PL.checkSLQ_sound`):
* `checkSXL_sound`: an accepted main record refutes every decomposition at its node with `Q`, given that every
  decomposition at the end state of each external path with `Q` is refuted;
* `subOKL_sound`: an accepted sub-record refutes its path;
* `leafSXL_sound`; instance `Q = LiftK`: `leafSXLW3_noLiftK` and `leafNoExt_of_splitW3` (an external leaf of a coset IP). -/
@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PL
open BC4 BC5 BC6s BC7s S5 S6 S7 RootSound Matrix BC7T S7L BC7x S7X
open BC6 (KB18 KBT KERV KM0 KM1 KM2 KM3 KM4 KM5 KM6 KM7 KM8 KMS LKB18 LKBT LKERV R90 R91 R92 R93 R94 R95 R96 R97 R98 RGE RK3)

noncomputable section

/-- **the main record walk**: `BC7x.checkSX` with SAT leaves -/
def checkSXL (lt : Asg → Nat → Bool) (fuel : Nat) :
    Nat → Nat → Nat → Nat → Asg → List Rec → Nat → List Step → List (List Step) → Nat → Bool × List (List Step) × Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat → Asg → List Rec → Nat → List Step → List (List Step) → Nat →
      Bool × List (List Step) × Nat)
    (fun _ _ _ _ _ _ _ _ ps S => (false, ps, S))
    (fun _ ih TERMS SS ACT need asg recs dom pth ps S =>
      cond (Nat.beq (rd 1 S) 0)
        (cond (Nat.beq (rd 9 (sk 1 S)) 0)
           (@List.rec (List Step) (fun _ => Bool × List (List Step) × Nat) (false, [], sk 10 S)
              (fun P ps' _ => (P == pth.reverse, ps', sk 10 S)) ps)
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
           let kr := kloop (fun p i ps S => ih TERMS SS (childSt TERMS SS ACT asg recs t nt p).1 need
               (childSt TERMS SS ACT asg recs t nt p).2.1 (childSt TERMS SS ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) cs 0 ps slr.2
           (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 && kr.1,
            kr.2.1, kr.2.2))))
    fuel

/-- **a sub-record**: the subtree at path `P` of the leaf with header `R`, checked with SAT leaves -/
def subOKL (lt : Asg → Nat → Bool) (R : Nat) (P : List Step) (cert : Nat) : Bool :=
  Nat.ble (hdr R).1 31 &&
    (BC7L.checkSL lt 64 (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1)
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).1
      (hdr R).2.2.2.1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.2
      (hdr R).2.2.1 cert).1

/-- **the main record** of a split SAT leaf -/
def leafSXL (lt : Asg → Nat → Bool) (R : Nat) (paths : List (List Step)) : Bool :=
  Nat.ble (rd 6 R) 31 &&
    ((Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
        Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0) && Nat.blt (rkSum (leafT R) (leafN R)) 27 ||
     (checkSXL lt 64 (leafT R) (mkSSP (leafT R) (leafN R)) (Nat.pred (Nat.shiftLeft 1 (leafN R)))
        (cond (Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
            Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
          (needP (leafT R) (leafN R) (Nat.sub (rkSum (leafT R) (leafN R)) 27)) 0) [] [] (leafDom6 R) [] paths
        (cond (Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
          (sk 2 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) (sk 514 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)))).1)

theorem checkSXL_succ (lt : Asg → Nat → Bool) (fuel TERMS SS ACT need : Nat) (asg : Asg) (recs : List Rec) (dom : Nat)
    (pth : List Step) (ps : List (List Step)) (S : Nat) :
    checkSXL lt (fuel + 1) TERMS SS ACT need asg recs dom pth ps S =
      cond (Nat.beq (rd 1 S) 0)
        (cond (Nat.beq (rd 9 (sk 1 S)) 0)
           (@List.rec (List Step) (fun _ => Bool × List (List Step) × Nat) (false, [], sk 10 S)
              (fun P ps' _ => (P == pth.reverse, ps', sk 10 S)) ps)
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
           let kr := kloop (fun p i ps S => checkSXL lt fuel TERMS SS (childSt TERMS SS ACT asg recs t nt p).1 need
               (childSt TERMS SS ACT asg recs t nt p).2.1 (childSt TERMS SS ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) cs 0 ps slr.2
           (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 && kr.1,
            kr.2.1, kr.2.2))) := rfl

theorem checkSXL_ps (lt : Asg → Nat → Bool) (TERMS SS need dom : Nat) : ∀ fuel ACT asg recs pth ps S,
    ∀ P ∈ (checkSXL lt fuel TERMS SS ACT need asg recs dom pth ps S).2.1, P ∈ ps := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs pth ps S P hP; exact hP
  | succ fuel ih =>
    intro ACT asg recs pth ps S P hP
    rw [checkSXL_succ] at hP
    revert hP
    cases Nat.beq (rd 1 S) 0
    · rw [cond_false]
      cases Nat.beq (rd 6 S) 63
      · rw [cond_false]
        intro hP
        exact kloop_ps _ (fun p i ps S => ih _ _ _ _ ps S) _ _ _ _ P hP
      · rw [cond_true]; intro hP; exact hP
    · rw [cond_true]
      cases Nat.beq (rd 9 (sk 1 S)) 0
      · rw [cond_false]; intro hP; exact hP
      · rw [cond_true]
        cases ps with
        | nil => intro hP; exact absurd hP List.not_mem_nil
        | cons Q ps' => intro hP; exact List.mem_cons_of_mem _ hP

/-- **Main records with SAT leaves.** -/
theorem checkSXL_sound (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (T n dom need : Nat) (hn : n ≤ 31)
    (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK T n b c 0 asg → Q b c → False)
    (root : Nat × Asg × List Rec) (paths : List (List Step))
    (H : ∀ P ∈ paths, ∀ b c, Inv T n dom b c (walk T (mkSSP T n) need root P).1 (walk T (mkSSP T n) need root P).2.1
      (walk T (mkSSP T n) need root P).2.2 → AsgOK T n b c (walk T (mkSSP T n) need root P).1
        (walk T (mkSSP T n) need root P).2.1 → LGok n need b c → Q b c → False) :
    ∀ fuel ACT asg recs (pth : List Step) (ps : List (List Step)) S, (∀ P ∈ ps, P ∈ paths) →
      (ACT, asg, recs) = walk T (mkSSP T n) need root pth.reverse →
      (checkSXL lt fuel T (mkSSP T n) ACT need asg recs dom pth ps S).1 = true →
      ∀ b c, Inv T n dom b c ACT asg recs → AsgOK T n b c ACT asg → LGok n need b c → Q b c → False := by
  intro fuel
  induction fuel with
  | zero => intro ACT asg recs pth ps S _ _ h; exact absurd h Bool.false_ne_true
  | succ fuel ih =>
    intro ACT asg recs pth ps S hps hst hchk b c hinv hasg hlg hq
    rw [checkSXL_succ] at hchk
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
          let kr := kloop (fun p i ps S => checkSXL lt fuel T (mkSSP T n) (childSt T (mkSSP T n) ACT asg recs t nt p).1 need
               (childSt T (mkSSP T n) ACT asg recs t nt p).2.1 (childSt T (mkSSP T n) ACT asg recs t nt p).2.2 dom
               ((t, sym, cdir, nt, sl, i) :: pth) ps S) cs 0 ps slr.2
          (bit ACT t && ((!sym) || asg.isEmpty) && allDom dom nt && nr.1 && allDom dom sl && allThru a sl && ss.1 &&
            kr.1) = true → False
        intro S1 t sym cdir ntr slr nt sl a nr cs ss kr hchk
        have ha : a = aT T t := rfl
        have hcs : cs = brCands7 (mkSSP T n) ACT need asg recs t a nt sl sym cdir := rfl
        have hnr : nr = mkRecs6 (mkSSP T n) ACT asg nt [] := rfl
        have hss : ss = mkSls6 (mkSSP T n) ACT asg sl := rfl
        have hkr : kr = kloop (fun p i ps S => checkSXL lt fuel T (mkSSP T n) (childSt T (mkSSP T n) ACT asg recs t nt p).1
             need (childSt T (mkSSP T n) ACT asg recs t nt p).2.1 (childSt T (mkSSP T n) ACT asg recs t nt p).2.2 dom
             ((t, sym, cdir, nt, sl, i) :: pth) ps S) cs 0 ps slr.2 := rfl
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
        obtain ⟨ps', S', hps', hS'⟩ := kloop_ok _ (fun p i ps S => checkSXL_ps lt _ _ _ _ _ _ _ _ _ ps S) cs 0 ps slr.2 h8 j hj
        rw [hgd, Nat.zero_add] at hS'
        have hst' : childSt T (mkSSP T n) ACT asg recs t nt p =
            walk T (mkSSP T n) need root ((t, sym, cdir, nt, sl, j) :: pth).reverse := by
          rw [List.reverse_cons, walk_append, ← hst]
          show childSt T (mkSSP T n) ACT asg recs t nt p =
            childSt T (mkSSP T n) ACT asg recs t nt ((cands T (mkSSP T n) ACT need asg recs t sym cdir nt sl).getD j (0, 0))
          rw [← hcs', hgd]
        rw [childSt_eq] at hst' hS'
        have hasg' : AsgOK T n b' c' (ACT ^^^ 1 <<< t) ((aT T t, p.1, p.2) :: asg) := by
          rw [hpe]; exact asgOK_step (asgOK_move hasg hmove') t htn hact
        exact ih _ _ _ _ ps' S' (fun P hP => hps P (hps' P hP)) hst' hS' b' c' hinv' hasg' hlg'
          (q_of_move Q hmove hmove' hq)
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
        | cons Q' ps' =>
          intro hchk
          have hQ : Q' = pth.reverse := beq_iff_eq.mp hchk
          have hmem : pth.reverse ∈ paths := by rw [← hQ]; exact hps Q' List.mem_cons_self
          have := H _ hmem b c
          rw [← hst] at this
          exact this hinv hasg hlg hq

/-- **Sub-records with SAT leaves.** -/
theorem subOKL_sound (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (P : List Step) (cert : Nat) (h : subOKL lt R P cert = true) :
    ∀ b c, Inv (hdr R).2.1 (hdr R).1 (hdr R).2.2.1 b c
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.2 →
      AsgOK (hdr R).2.1 (hdr R).1 b c
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.1 →
      LGok (hdr R).1 (hdr R).2.2.2.1 b c → Q b c → False := by
  unfold subOKL at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  intro b c hinv hasg hlg hq
  exact checkSLQ_sound lt Q hmove _ _ _ _ h.1 hleaf 64 _ _ _ _ h.2 b c hinv hasg hlg hq

theorem leafSXL_eq (lt : Asg → Nat → Bool) (R : Nat) (paths : List (List Step)) : leafSXL lt R paths =
    (Nat.ble (rd 6 R) 31 &&
      ((Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
          Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0) && Nat.blt (rkSum (leafT R) (leafN R)) 27 ||
       (checkSXL lt 64 (leafT R) (mkSSP (leafT R) (leafN R)) (Nat.pred (Nat.shiftLeft 1 (leafN R)))
          (cond (Nat.beq (rd 1 (sk 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R))) 1 &&
              Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
            (needP (leafT R) (leafN R) (Nat.sub (rkSum (leafT R) (leafN R)) 27)) 0) [] [] (leafDom6 R) [] paths
          (cond (Nat.beq (rd 1 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) 0)
            (sk 2 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)) (sk 514 (sk (Nat.add 6 (Nat.mul 9 (rd 6 R))) R)))).1)) := rfl

/-- **Split SAT leaves.** An accepted main record with an accepted sub-record for each external path refutes every
decomposition of the record (on its domain) with `Q`. -/
theorem leafSXL_sound (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (leafT R) (leafN R) b c 0 asg → Q b c → False)
    (subs : List (List Step × Nat)) (hmain : leafSXL lt R (subs.map Prod.fst) = true)
    (hsubs : ∀ q ∈ subs, subOKL lt R q.1 q.2 = true) (b c : Nat → Nat) (hbc : BC (leafN R) b c)
    (hd : ∀ X, X < 512 → (leafDom6 R).testBit X = true →
      TX (toM3 X) = ∑ t ∈ (Finset.range (leafN R)).filter (fun t => par (aT (leafT R) t &&& X) = true),
        vecMulVec (nv (b t)) (nv (c t))) (hq : Q b c) : False := by
  rw [leafSXL_eq] at hmain
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
    have hH : ∀ P ∈ subs.map Prod.fst, ∀ b c, Inv (leafT R) (leafN R) (leafDom6 R) b c
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).1
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).2.1
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).2.2 →
        AsgOK (leafT R) (leafN R) b c
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).1
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).2.1 →
        LGok (leafN R) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0) b c → Q b c → False := by
      intro P hP b' c' hinv' hasg' hlg' hq'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hP
      have hs := subOKL_sound lt Q hmove R hleaf q.1 q.2 (hsubs q hq)
      have e : Nat.pred (Nat.shiftLeft 1 (hdr R).1) = 2 ^ leafN R - 1 := epred
      rw [e] at hs
      exact hs b' c' hinv' hasg' hlg' hq'
    exact checkSXL_sound lt Q hmove (leafT R) (leafN R) (leafDom6 R) _ hn hleaf (2 ^ leafN R - 1, [], [])
      (subs.map Prod.fst) hH 64 _ [] [] [] _ _ (fun P hP => hP) rfl h b c (S5.inv_root _ _ _ b c hbc hd)
      (asgOK_root _ _ b c) hlgok hq

/-- **split SAT leaves with `k` inside terms, the test with guessed terms** -/
theorem leafSXLW3_noLiftK (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (subs : List (List Step × Nat))
    (hmain : leafSXL (ltW3 pts k) R (subs.map Prod.fst) = true)
    (hsubs : ∀ q ∈ subs, subOKL (ltW3 pts k) R q.1 q.2 = true) :
    L479.NoLiftK (leafT R) (leafN R) (S6.leafDom6 R) Em k := by
  intro b c hbc hd hl
  exact leafSXL_sound (ltW3 pts k) (fun b c => L479.LiftK (leafN R) b c Em k)
    (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) subs hmain hsubs
    b c hbc hd hl

/-- **the external leaf of a coset IP, refuted by a split certificate** (`k = 22 - R`; any `E`, `R`, `lo`) -/
theorem leafNoExt_of_splitW3 {C : E1G.Ctx} {Em lo pl : ℕ} (pts : List Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (cert : ℕ) (subs : List (List Step × Nat))
    (hN : C.N ≤ 127) (hR : C.R ≤ 31) (hC : E1GS.Cosets Em C.VT C.N) (hD : E1GS.DomPerp C.DOM Em)
    (hDOM : C.DOM < 2 ^ 512)
    (hmain : leafSXL (ltW3 pts (22 - C.R)) (E1G.leafRec C.R C.VT C.DOM pl cert) (subs.map Prod.fst) = true)
    (hsubs : ∀ q ∈ subs, subOKL (ltW3 pts (22 - C.R)) (E1G.leafRec C.R C.VT C.DOM pl cert) q.1 q.2 = true) :
    L479.LeafNoExt C Em lo pl := by
  have h := leafSXLW3_noLiftK pts (22 - C.R) Em hnd hpts _ subs hmain hsubs
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM] at h
  apply L479.leafNoExt_of_noLiftK hN hR hC hD hDOM
  rw [E1GS.leafT_rec _ _ _ _ _ (by omega) hDOM, E1GS.leafN_rec _ _ _ _ _ (by omega) hDOM,
    E1GS.leafDom_rec _ _ _ _ _ (by omega) hDOM]
  exact h

/-! ## Decidable plane facts -/

/-- no repeated entries -/
def nodupB : List Nat → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

theorem nodupB_spec : ∀ l : List Nat, nodupB l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
    intro h
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun ha => ?_, ih h.2⟩
    have := List.contains_iff_mem.mpr ha
    rw [h.1] at this; exact absurd this (by decide)

/-- the points of `E` listed: a decidable check over the 512 vectors -/
def ptsOKB (pts : List Nat) (Em : Nat) : Bool :=
  S5.allLT 512 (fun p => Nat.beq p 0 || !Em.testBit p || pts.contains p)

theorem ptsOKB_spec {pts : List Nat} {Em : Nat} (h : ptsOKB pts Em = true) :
    ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts := by
  intro p hp h0 he
  have h1 := S5.allLT_spec h p hp
  have hb : Nat.beq p 0 = false := by
    cases hq : Nat.beq p 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hq) h0
  rw [hb, he] at h1
  simpa using h1

/-! ## Balanced trees of sub-records (the module layout's combining step) -/

/-- a binary tree of sub-records `(path, certificate)` -/
inductive ST where
  | leaf (P : List Step) (c : Nat)
  | node (a b : ST)

/-- the sub-records in order -/
def ST.list : ST → List (List Step × Nat)
  | .leaf P c => [(P, c)]
  | .node a b => a.list ++ b.list

/-- every sub-record of the tree is accepted -/
def ST.ok (lt : Asg → Nat → Bool) (R : Nat) : ST → Prop
  | .leaf P c => subOKL lt R P c = true
  | .node a b => a.ok lt R ∧ b.ok lt R

theorem ST.ok_mem (lt : Asg → Nat → Bool) (R : Nat) : ∀ t : ST, t.ok lt R → ∀ q ∈ t.list, subOKL lt R q.1 q.2 = true := by
  intro t
  induction t with
  | leaf P c => intro h q hq; simp only [ST.list, List.mem_singleton] at hq; subst hq; exact h
  | node a b iha ihb =>
    intro h q hq
    simp only [ST.list, List.mem_append] at hq
    rcases hq with hq | hq
    · exact iha h.1 q hq
    · exact ihb h.2 q hq

/-- **a split SAT leaf from a tree of accepted sub-records** -/
theorem noLiftK_of_tree (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (t : ST)
    (hmain : leafSXL (ltW3 pts k) R (t.list.map Prod.fst) = true) (hsubs : t.ok (ltW3 pts k) R) :
    L479.NoLiftK (leafT R) (leafN R) (S6.leafDom6 R) Em k :=
  leafSXLW3_noLiftK pts k Em hnd hpts R t.list hmain (ST.ok_mem _ R t hsubs)

/-! ## Giant SAT leaves across modules: the semantic path statement -/

/-- **every decomposition at the end state of each path of `paths` with the invariant is refuted** (the public statement of a
part module; the sub-record certificates stay private) -/
def PathsOK (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop) (R : Nat) (paths : List (List Step)) : Prop :=
  ∀ P ∈ paths, ∀ b c, Inv (hdr R).2.1 (hdr R).1 (hdr R).2.2.1 b c
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.2 →
      AsgOK (hdr R).2.1 (hdr R).1 b c
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.1 →
      LGok (hdr R).1 (hdr R).2.2.2.1 b c → Q b c → False

theorem pathsOK_append {lt : Asg → Nat → Bool} {Q : (Nat → Nat) → (Nat → Nat) → Prop} {R : Nat} {ps1 ps2 : List (List Step)}
    (h1 : PathsOK lt Q R ps1) (h2 : PathsOK lt Q R ps2) : PathsOK lt Q R (ps1 ++ ps2) := by
  intro P hP
  rcases List.mem_append.mp hP with h | h
  · exact h1 P h
  · exact h2 P h

/-- a part module: its tree of accepted sub-records -/
theorem pathsOK_of_tree (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (t : ST) (ht : t.ok lt R) : PathsOK lt Q R (t.list.map Prod.fst) := by
  intro P hP
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hP
  exact subOKL_sound lt Q hmove R hleaf q.1 q.2 (ST.ok_mem lt R t ht q hq)

/-- **the aggregator of a giant SAT leaf**: the main record and the parts' path statements -/
theorem leafSXL_sound_paths (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (leafT R) (leafN R) b c 0 asg → Q b c → False)
    (paths : List (List Step)) (hmain : leafSXL lt R paths = true) (hparts : PathsOK lt Q R paths)
    (b c : Nat → Nat) (hbc : BC (leafN R) b c)
    (hd : ∀ X, X < 512 → (leafDom6 R).testBit X = true →
      TX (toM3 X) = ∑ t ∈ (Finset.range (leafN R)).filter (fun t => par (aT (leafT R) t &&& X) = true),
        vecMulVec (nv (b t)) (nv (c t))) (hq : Q b c) : False := by
  rw [leafSXL_eq] at hmain
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
    have hH : ∀ P ∈ paths, ∀ b c, Inv (leafT R) (leafN R) (leafDom6 R) b c
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).1
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).2.1
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).2.2 →
        AsgOK (leafT R) (leafN R) b c
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).1
        (walk (leafT R) (mkSSP (leafT R) (leafN R)) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0)
          (2 ^ leafN R - 1, [], []) P).2.1 →
        LGok (leafN R) (cond lg (needP (leafT R) (leafN R) (Nat.sub RS 27)) 0) b c → Q b c → False := by
      intro P hP b' c' hinv' hasg' hlg' hq'
      have hs := hparts P hP
      have e : Nat.pred (Nat.shiftLeft 1 (hdr R).1) = 2 ^ leafN R - 1 := epred
      rw [e] at hs
      exact hs b' c' hinv' hasg' hlg' hq'
    exact checkSXL_sound lt Q hmove (leafT R) (leafN R) (leafDom6 R) _ hn hleaf (2 ^ leafN R - 1, [], [])
      paths hH 64 _ [] [] [] _ _ (fun P hP => hP) rfl h b c (S5.inv_root _ _ _ b c hbc hd)
      (asgOK_root _ _ b c) hlgok hq

/-- **a nested part**: the part's own main record for the subtree at path `P` (external markers for the part's sub-records
`ps`, full paths from the leaf root) -/
def subMainOK (lt : Asg → Nat → Bool) (R : Nat) (P : List Step) (ps : List (List Step)) (cert : Nat) : Bool :=
  Nat.ble (hdr R).1 31 &&
    (checkSXL lt 64 (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1)
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).1
      (hdr R).2.2.2.1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.1
      (walk (hdr R).2.1 (mkSSP (hdr R).2.1 (hdr R).1) (hdr R).2.2.2.1 (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) P).2.2
      (hdr R).2.2.1 P.reverse ps cert).1

/-- **a nested part refutes its path**, given its sub-records' paths -/
theorem pathsOK_of_submain (lt : Asg → Nat → Bool) (Q : (Nat → Nat) → (Nat → Nat) → Prop)
    (hmove : ∀ (b c : Nat → Nat) (p q : Nat × Nat), mul3 p.1 p.2 = 273 → mul3 q.1 q.2 = 273 → Q b c →
      Q (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))))
    (R : Nat) (hleaf : ∀ asg w (b c : Nat → Nat), lt asg w = true → AsgOK (hdr R).2.1 (hdr R).1 b c 0 asg → Q b c → False)
    (P : List Step) (ps : List (List Step)) (cert : Nat) (h : subMainOK lt R P ps cert = true)
    (hsub : PathsOK lt Q R ps) : PathsOK lt Q R [P] := by
  intro P' hP' b c hinv hasg hlg hq
  rw [List.mem_singleton] at hP'
  rw [hP'] at hinv hasg
  unfold subMainOK at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  exact checkSXL_sound lt Q hmove _ _ _ _ h.1 hleaf (Nat.pred (Nat.shiftLeft 1 (hdr R).1), [], []) ps hsub 64 _ _ _
    P.reverse ps cert (fun x hx => hx) (by rw [List.reverse_reverse]) h.2 b c hinv hasg hlg hq

/-- the LiftK invariant and the test with guessed terms, for the part and aggregator modules -/
abbrev QK (n Em k : Nat) : (Nat → Nat) → (Nat → Nat) → Prop := fun b c => L479.LiftK n b c Em k

theorem pathsOK_of_treeW3 (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (t : ST) (ht : t.ok (ltW3 pts k) R) :
    PathsOK (ltW3 pts k) (QK (leafN R) Em k) R (t.list.map Prod.fst) :=
  pathsOK_of_tree (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) t ht

theorem pathsOK_of_submainW3 (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (P : List Step) (ps : List (List Step))
    (cert : Nat) (h : subMainOK (ltW3 pts k) R P ps cert = true) (hsub : PathsOK (ltW3 pts k) (QK (leafN R) Em k) R ps) :
    PathsOK (ltW3 pts k) (QK (leafN R) Em k) R [P] :=
  pathsOK_of_submain (ltW3 pts k) (QK (leafN R) Em k) (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) P ps cert h hsub

/-- a nested part with no sub-records (the whole subtree in the part's main record) -/
theorem pathsOK_nil {lt : Asg → Nat → Bool} {Q : (Nat → Nat) → (Nat → Nat) → Prop} {R : Nat} : PathsOK lt Q R [] :=
  fun P hP => absurd hP List.not_mem_nil

theorem noLiftK_of_paths (pts : List Nat) (k Em : Nat) (hnd : pts.Nodup)
    (hpts : ∀ p, p < 512 → p ≠ 0 → Em.testBit p = true → p ∈ pts) (R : Nat) (paths : List (List Step))
    (hmain : leafSXL (ltW3 pts k) R paths = true) (hparts : PathsOK (ltW3 pts k) (QK (leafN R) Em k) R paths) :
    L479.NoLiftK (leafT R) (leafN R) (S6.leafDom6 R) Em k := by
  intro b c hbc hd hl
  exact leafSXL_sound_paths (ltW3 pts k) (QK (leafN R) Em k)
    (fun b c p q hp hq h => liftK_move (leafN R) Em k b c p q hp hq h) R
    (fun asg w b c hw hasg hq => ltW3_sound pts k Em hnd hpts asg w hw (liftKL_of_complete hasg hq)) paths hmain hparts
    b c hbc hd hl

end

end PL

#print axioms PL.checkSXL_sound
#print axioms PL.subOKL_sound
#print axioms PL.leafSXL_sound
#print axioms PL.leafSXLW3_noLiftK
#print axioms PL.leafNoExt_of_splitW3
#print axioms PL.noLiftK_of_tree
#print axioms PL.pathsOK_of_treeW3
#print axioms PL.noLiftK_of_paths
#print axioms PL.pathsOK_of_submainW3
