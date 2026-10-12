module
public import E1G.Hdr
public import E1GK.ChainF
/-! # The E1G job statements are monotone in the external-leaf list `EXT`

`Glob C x` mentions `C.EXT` only in its `leaf` field, through `E1G.leafOK`, and `leafOK` reads `C.EXT` only in the membership
scan of a cert-0 (external) leaf.  So whatever is proved for every `x` with `Glob C x` (a job's `JobOK`, a range of them, an
`EnumOK`) also holds against any context `C'` that agrees with `C` on `R`, `N`, `VT`, `DOM`, `GP` and whose `EXT` contains
`C.EXT`.  Jobs are proved against their own lists (`[]` for a job without external leaves), and a tier's statement over the
census list follows by `rangeOK_ext_mono` / `forall_glob_ext_mono` and an inclusion (`subset_of_all`, decided by the kernel).
The `{C with EXT := e}` forms take the field equalities by `rfl` (e.g. `E1G.OK_c436.Cx e = {E1G.IP_c436.C with EXT := e}`). -/
@[expose] public section

namespace E1GS

/-- the scan in `E1G.leafOK`'s cert-0 branch finds `pl` only if `pl ∈ L` -/
theorem extScan_mem (pl : ℕ) : ∀ L : List ℕ,
    (@List.rec ℕ (fun _ => Bool) false (fun e _ ih => @Bool.rec (fun _ => Bool) ih true (Nat.beq e pl)) L) = true → pl ∈ L
  | [], h => nomatch h
  | e :: L, h => by
    have h' : @Bool.rec (fun _ => Bool)
        (@List.rec ℕ (fun _ => Bool) false (fun e _ ih => @Bool.rec (fun _ => Bool) ih true (Nat.beq e pl)) L) true
        (Nat.beq e pl) = true := h
    cases he : Nat.beq e pl with
    | false => rw [he] at h'; exact List.mem_cons.mpr (Or.inr (extScan_mem pl L h'))
    | true => exact List.mem_cons.mpr (Or.inl (Nat.eq_of_beq_eq_true he).symm)

/-- and it finds every `pl ∈ L` -/
theorem mem_extScan (pl : ℕ) : ∀ L : List ℕ, pl ∈ L →
    (@List.rec ℕ (fun _ => Bool) false (fun e _ ih => @Bool.rec (fun _ => Bool) ih true (Nat.beq e pl)) L) = true
  | [], h => absurd h (List.not_mem_nil)
  | e :: L, h => by
    show @Bool.rec (fun _ => Bool)
        (@List.rec ℕ (fun _ => Bool) false (fun e _ ih => @Bool.rec (fun _ => Bool) ih true (Nat.beq e pl)) L) true
        (Nat.beq e pl) = true
    cases he : Nat.beq e pl with
    | true => rfl
    | false =>
      rcases List.mem_cons.mp h with h1 | h1
      · subst h1; rw [Nat.beq_refl] at he; exact absurd he Bool.noConfusion
      · exact mem_extScan pl L h1

theorem leafOK_ext_mono {C C' : E1G.Ctx} (hR : C'.R = C.R) (hVT : C'.VT = C.VT) (hDOM : C'.DOM = C.DOM)
    (hsub : ∀ p ∈ C.EXT, p ∈ C'.EXT) (pl cert : ℕ) (h : E1G.leafOK C pl cert = true) : E1G.leafOK C' pl cert = true := by
  unfold E1G.leafOK at h ⊢
  rw [hR, hVT, hDOM]
  cases hc : Nat.beq cert 0 with
  | false => rw [hc] at h; exact h
  | true => rw [hc] at h; exact mem_extScan pl _ (hsub pl (extScan_mem pl _ h))

theorem glob_ext_mono {C C' : E1G.Ctx} (hR : C'.R = C.R) (hN : C'.N = C.N) (hVT : C'.VT = C.VT) (hDOM : C'.DOM = C.DOM)
    (hGP : C'.GP = C.GP) (hsub : ∀ p ∈ C.EXT, p ∈ C'.EXT) {x : ℕ → ℕ} (h : Glob C' x) : Glob C x where
  N_le := by rw [← hN]; exact h.N_le
  R_le := by rw [← hR]; exact h.R_le
  xN := fun l hl => h.xN l (by rw [hN]; exact hl)
  xR := by rw [← hR]; exact h.xR
  leaf := fun pl cert hm hok => h.leaf pl cert (by rw [hR]; exact hm) (leafOK_ext_mono hR hVT hDOM hsub pl cert hok)
  canon := by rw [← hGP]; exact h.canon
  gp := by rw [← hGP, ← hN]; exact h.gp

/-- anything proved for every `x` with `Glob C x` (e.g. `L479.EnumOK C sl UB`, by unfolding) -/
theorem forall_glob_ext_mono {C C' : E1G.Ctx} (hR : C'.R = C.R) (hN : C'.N = C.N) (hVT : C'.VT = C.VT)
    (hDOM : C'.DOM = C.DOM) (hGP : C'.GP = C.GP) (hsub : ∀ p ∈ C.EXT, p ∈ C'.EXT) {Q : (ℕ → ℕ) → Prop}
    (h : ∀ x, Glob C x → Q x) : ∀ x, Glob C' x → Q x :=
  fun x hg => h x (glob_ext_mono hR hN hVT hDOM hGP hsub hg)

theorem jobOK_ext_mono {C C' : E1G.Ctx} (hR : C'.R = C.R) (hN : C'.N = C.N) (hVT : C'.VT = C.VT) (hDOM : C'.DOM = C.DOM)
    (hGP : C'.GP = C.GP) (hsub : ∀ p ∈ C.EXT, p ∈ C'.EXT) {sl : ℕ → ℕ} {UB S : ℕ} (h : JobOK C sl UB S) :
    JobOK C' sl UB S :=
  fun x hg => h x (glob_ext_mono hR hN hVT hDOM hGP hsub hg)

theorem rangeOK_ext_mono {C C' : E1G.Ctx} (hR : C'.R = C.R) (hN : C'.N = C.N) (hVT : C'.VT = C.VT)
    (hDOM : C'.DOM = C.DOM) (hGP : C'.GP = C.GP) (hsub : ∀ p ∈ C.EXT, p ∈ C'.EXT) {sl : ℕ → ℕ} {UB : ℕ} {T : ℕ → ℕ}
    {a m : ℕ} (h : RangeOK (fun k => JobOK C sl UB (T k)) a m) : RangeOK (fun k => JobOK C' sl UB (T k)) a m :=
  fun i h1 h2 => jobOK_ext_mono hR hN hVT hDOM hGP hsub (h i h1 h2)

/-- the inclusion as a kernel-decidable Bool -/
theorem subset_of_all {L e : List ℕ} (h : L.all (fun p => e.elem p) = true) : ∀ p ∈ L, p ∈ e := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simpa using this

theorem jobOK_withExt {C : E1G.Ctx} (e : List ℕ) (hsub : ∀ p ∈ C.EXT, p ∈ e) {sl : ℕ → ℕ} {UB S : ℕ}
    (h : JobOK C sl UB S) : JobOK { C with EXT := e } sl UB S :=
  jobOK_ext_mono (C := C) (C' := { C with EXT := e }) rfl rfl rfl rfl rfl hsub h

theorem rangeOK_withExt {C : E1G.Ctx} (e : List ℕ) (hsub : ∀ p ∈ C.EXT, p ∈ e) {sl : ℕ → ℕ} {UB : ℕ} {T : ℕ → ℕ}
    {a m : ℕ} (h : RangeOK (fun k => JobOK C sl UB (T k)) a m) : RangeOK (fun k => JobOK { C with EXT := e } sl UB (T k)) a m :=
  rangeOK_ext_mono (C := C) (C' := { C with EXT := e }) rfl rfl rfl rfl rfl hsub h

/-! ## The lifted statements of job modules with external leaves

A module whose jobs contain external leaves proves its jobs against `withExt IP.C X` (`X`: its list) and exports
`∀ E, ExtSub X E → RangeOK (fun k => JobOK (withExt IP.C E) sl UB (T k)) a m`; aggregators append their children's lists
(`extSub_append_left/right`), a module without external leaves is lifted by `rangeOK_lift_base`, and the root takes `E` to be
its own list (`extSub_refl`).  `withExt IP.C E` is `{IP.C with EXT := E}` (e.g. `E1G.OK_c436.Cx E`) by unfolding. -/

/-- `{C with EXT := E}` -/
def withExt (C : E1G.Ctx) (E : List ℕ) : E1G.Ctx := { C with EXT := E }
/-- the inclusion of external-leaf lists -/
def ExtSub (X E : List ℕ) : Prop := ∀ p ∈ X, p ∈ E

theorem extSub_refl (X : List ℕ) : ExtSub X X := fun _ h => h
theorem extSub_nil (E : List ℕ) : ExtSub [] E := fun _ h => absurd h List.not_mem_nil
theorem extSub_append_left {A B E : List ℕ} (h : ExtSub (A ++ B) E) : ExtSub A E :=
  fun p hp => h p (List.mem_append.mpr (Or.inl hp))
theorem extSub_append_right {A B E : List ℕ} (h : ExtSub (A ++ B) E) : ExtSub B E :=
  fun p hp => h p (List.mem_append.mpr (Or.inr hp))

theorem jobOK_lift {C : E1G.Ctx} {X : List ℕ} {sl : ℕ → ℕ} {UB S : ℕ} (h : JobOK (withExt C X) sl UB S) :
    ∀ E, ExtSub X E → JobOK (withExt C E) sl UB S :=
  fun E hE => jobOK_ext_mono (C := withExt C X) (C' := withExt C E) rfl rfl rfl rfl rfl hE h

theorem rangeOK_lift {C : E1G.Ctx} {X : List ℕ} {sl : ℕ → ℕ} {UB : ℕ} {T : ℕ → ℕ} {a m : ℕ}
    (h : RangeOK (fun k => JobOK (withExt C X) sl UB (T k)) a m) :
    ∀ E, ExtSub X E → RangeOK (fun k => JobOK (withExt C E) sl UB (T k)) a m :=
  fun E hE => rangeOK_ext_mono (C := withExt C X) (C' := withExt C E) rfl rfl rfl rfl rfl hE h

/-- a module without external leaves (its context `C` has `C.EXT = []`, e.g. `IP.C`) -/
theorem rangeOK_lift_base {C : E1G.Ctx} (hC : C.EXT = []) {sl : ℕ → ℕ} {UB : ℕ} {T : ℕ → ℕ} {a m : ℕ}
    (h : RangeOK (fun k => JobOK C sl UB (T k)) a m) (E : List ℕ) :
    RangeOK (fun k => JobOK (withExt C E) sl UB (T k)) a m :=
  rangeOK_ext_mono (C := C) (C' := withExt C E) rfl rfl rfl rfl rfl (by rw [hC]; exact extSub_nil E) h

theorem jobOK_lift_base {C : E1G.Ctx} (hC : C.EXT = []) {sl : ℕ → ℕ} {UB S : ℕ} (h : JobOK C sl UB S) (E : List ℕ) :
    JobOK (withExt C E) sl UB S :=
  jobOK_ext_mono (C := C) (C' := withExt C E) rfl rfl rfl rfl rfl (by rw [hC]; exact extSub_nil E) h

/-- `∀ E, ExtSub X E → JobOK (withExt C E) …` at `E := withExt`'s own list: a chain checked against `withExt C Y` uses its
children's lifted statements at `Y` -/
theorem jobOK_at {C : E1G.Ctx} {X Y : List ℕ} {sl : ℕ → ℕ} {UB S : ℕ} (h : ∀ E, ExtSub X E → JobOK (withExt C E) sl UB S)
    (hXY : ExtSub X Y) : JobOK (withExt C Y) sl UB S := h Y hXY

end E1GS

#print axioms E1GS.rangeOK_withExt
#print axioms E1GS.forall_glob_ext_mono
#print axioms E1GS.subset_of_all
