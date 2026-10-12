module
public import S4.SplitR
public import E1G.Bridge2
/-! # `NoDecomp` from split records with sibling ranges (UNSAT leaves)

`S4.SplitR`'s soundness with the leaf test that accepts nothing (`ltF`) and the trivial invariant (`QT`): an accepted main
record and its items' statements refute every decomposition of the record's terms on its domain, i.e. `S5.NoDecomp`. This is
the statement of the class-raise tier's external leaves (`x<c> : ∀ pl ∈ EXT, NoDecomp …`, certificates over E1P_EXTBITS or
over gen7's budget). The certificates come from `gen7pc --split3` without `--plane`, which emits no SAT leaf (a decomposition
ends the run with `SAT`), so every record is checked against `ltF`.

`noDecomp_rec0` drops the certificate: `leafT`, `leafN` and `leafDom6` of `E1G.leafRec R VT DOM pl cert` do not depend on
`cert` (`E1GS.leafT_rec`, `leafN_rec`, `leafDom_rec`), so the leaf module's record gives the statement for `cert = 0`. -/
@[expose] public section

set_option linter.unusedVariables false

namespace PL
open BC4 BC5 BC6s BC7s S5 S6 S7 RootSound Matrix BC7T S7L BC7x S7X

/-- the leaf test that accepts nothing: a record checked against it has no SAT leaf -/
def ltF : Asg → Nat → Bool := fun _ _ => false

/-- the trivial invariant -/
def QT : (Nat → Nat) → (Nat → Nat) → Prop := fun _ _ => True

theorem qT_move (b c : Nat → Nat) (p q : Nat × Nat) (hp : mul3 p.1 p.2 = 273) (hq : mul3 q.1 q.2 = 273) (h : QT b c) :
    QT (fun u => mul3 (mul3 (b u) p.1) q.1) (fun u => mul3 q.2 (mul3 p.2 (c u))) := trivial

theorem ltF_leaf (T n : Nat) (asg : Asg) (w : Nat) (b c : Nat → Nat) (h : ltF asg w = true) (hasg : AsgOK T n b c 0 asg)
    (hq : QT b c) : False := Bool.false_ne_true h

theorem pathsOKR_of_strF (R : Nat) (t : STR) (ht : t.ok ltF R) : PathsOKR ltF QT R t.items :=
  pathsOKR_of_str ltF QT qT_move R (ltF_leaf _ _) t ht

theorem pathsOKR_of_submainF (R : Nat) (P : List Step) (ps : List Item) (cert : Nat) (h : subMainOKR ltF R P ps cert = true)
    (hsub : PathsOKR ltF QT R ps) : PathsOKR ltF QT R [(P, 0)] :=
  pathsOKR_of_submain ltF QT qT_move R (ltF_leaf _ _) P ps cert h hsub

theorem pathsOKR_of_forestF (R : Nat) (Pn : List Step) (t : Nat) (sym cdir : Bool) (nt sl : List Nat) (i c : Nat)
    (ps : List Item) (cert : Nat) (h : forestOK ltF R Pn t sym cdir nt sl i c ps cert = true) (hsub : PathsOKR ltF QT R ps) :
    PathsOKR ltF QT R [(Pn ++ [(t, sym, cdir, nt, sl, i)], c)] :=
  pathsOKR_of_forest ltF QT qT_move R (ltF_leaf _ _) Pn t sym cdir nt sl i c ps cert h hsub

/-- **an UNSAT split leaf with sibling ranges**: the main record and its items' statements give `NoDecomp` -/
theorem noDecomp_of_items (R : Nat) (items : List Item) (hmain : leafSXR ltF R items = true)
    (hparts : PathsOKR ltF QT R items) : S5.NoDecomp (leafT R) (leafN R) (S6.leafDom6 R) := by
  rintro ⟨b, c, hbc, hd⟩
  exact leafSXR_sound_paths ltF QT qT_move R (ltF_leaf _ _) items hmain hparts b c hbc hd trivial

/-- `NoDecomp` of an E1G leaf record does not depend on its certificate -/
theorem noDecomp_rec0 (R VT DOM pl cert : Nat) (hR : R < 64) (hDOM : DOM < 2 ^ 512)
    (h : S5.NoDecomp (leafT (E1G.leafRec R VT DOM pl cert)) (leafN (E1G.leafRec R VT DOM pl cert))
      (S6.leafDom6 (E1G.leafRec R VT DOM pl cert))) :
    S5.NoDecomp (leafT (E1G.leafRec R VT DOM pl 0)) (leafN (E1G.leafRec R VT DOM pl 0))
      (S6.leafDom6 (E1G.leafRec R VT DOM pl 0)) := by
  rw [E1GS.leafT_rec R VT DOM pl cert hR hDOM, E1GS.leafN_rec R VT DOM pl cert hR hDOM,
    E1GS.leafDom_rec R VT DOM pl cert hR hDOM] at h
  rw [E1GS.leafT_rec R VT DOM pl 0 hR hDOM, E1GS.leafN_rec R VT DOM pl 0 hR hDOM, E1GS.leafDom_rec R VT DOM pl 0 hR hDOM]
  exact h

/-- the chunk modules' step: a leaf module's record `R0 = E1G.leafRec R VT DOM pl cert` gives the statement for `cert = 0` -/
theorem noDecomp_of_rec (R VT DOM pl cert R0 : Nat) (hr : R0 = E1G.leafRec R VT DOM pl cert) (hR : R < 64)
    (hDOM : DOM < 2 ^ 512) (h : S5.NoDecomp (leafT R0) (leafN R0) (S6.leafDom6 R0)) :
    S5.NoDecomp (leafT (E1G.leafRec R VT DOM pl 0)) (leafN (E1G.leafRec R VT DOM pl 0))
      (S6.leafDom6 (E1G.leafRec R VT DOM pl 0)) :=
  noDecomp_rec0 R VT DOM pl cert hR hDOM (hr ▸ h)

end PL

#print axioms PL.pathsOKR_of_strF
#print axioms PL.pathsOKR_of_submainF
#print axioms PL.pathsOKR_of_forestF
#print axioms PL.noDecomp_of_items
#print axioms PL.noDecomp_rec0
#print axioms PL.noDecomp_of_rec
