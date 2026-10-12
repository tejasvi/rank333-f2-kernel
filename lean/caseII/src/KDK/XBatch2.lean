module
public import R22Port.U_d41d8cd98f00
public import KDK.XComp2
public import KDK.XBatchO
/-! # KDK.XBatch2 (kinds-only name of KD.XBatch2): `KD.batchX` with the X part's cheaper front end (`KD.xpartC2`, packed trees)

`batchX2 tab st nodes` is `batchX` with `xpartC2` in place of `xpartC`; a node's children carry packed trees (`KidX2`).
**`batchX2_imp`**: an accepted `batchX2` makes `batchX` accept the same batch with the trees unpacked, so **`batchX2_sound`**
(the contract `BatchOKX` of the unpacked batch) follows from `batchX_sound`. -/
@[expose] public section
set_option maxRecDepth 10000
noncomputable section
namespace KD
open R3RT.Spec
open R3RT (foldR node5 mkD)

/-- a node record with packed children (`NodeX` with `List KidX2`) -/
abbrev NodeX2 := ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List Agg × List ℕ × ℕ × ℕ × ℕ ×
  List KidX2

def NodeX2.toNodeX : NodeX2 → NodeX
  | (c2, h, suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids) =>
    (c2, h, suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids.map KidX2.toKidX)

def batchX2' (tab : ℕ → ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) → List NodeX2 → Bool
  | _, [] => true
  | st, (c2, h, suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids) :: rest =>
    match List.drop (Nat.land hdr 255) st with
    | [] => false
    | (S, D, N, U, dP) :: st' =>
      foldR tab 2 r2 0 0 0 0 (fun MB2 E2 b2 c2' =>
        foldR tab 1 r1 MB2 E2 b2 0 (fun MB1 E1 b1 c1' =>
          foldR tab 0 r0 MB1 E1 b1 0 (fun MB E bad c0' =>
            foldR tab 2 x2 0 0 bad 0 (fun MBx2 Ex2 bx2 _ =>
              foldR tab 1 x1 MBx2 Ex2 bx2 0 (fun MBx Ex badx cx' =>
                Nat.beq badx 0 && Nat.beq c2' (Nat.land (Nat.shiftRight hdr 52) 1023) &&
                Nat.beq c1' (Nat.land (Nat.shiftRight hdr 32) 1023) && Nat.beq c0' (Nat.land (Nat.shiftRight hdr 22) 1023) &&
                node5 S D N U dP c2 h suf
                  (Nat.lor (Nat.land hdr 18446744073709551615)
                    (Nat.shiftLeft (Nat.lor MB (Nat.shiftLeft E (Nat.mul 512 (Nat.add c0' (Nat.add c1' c2'))))) 64)) ks
                  (fun S' D' N' U' =>
                    L1.blocks MBx Ex (Nat.mul S' L1.REP63) (Nat.div (Nat.add (Nat.add cx' (List.length x2)) 62) 63) &&
                    xpartC2 R3RT.nperpL S' D' N' U' (Nat.succ dP) (Nat.land (Nat.shiftRight hdr 8) 511) (Nat.add c0' c1')
                      (Nat.add c0' (Nat.add c1' c2')) (Nat.add (Nat.add c0' (Nat.add c1' c2')) cx')
                      (mkD MB MBx (Nat.add c0' (Nat.add c1' c2'))) nrows aggs XL HP DEFP J kids &&
                    batchX2' tab ((S', D', N', U', Nat.succ dP) :: (S, D, N, U, dP) :: st') rest))))))

def batchX2 (tab : ℕ → ℕ) (st : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (nodes : List NodeX2) : Bool := batchX2' tab st nodes

theorem foldR_and_imp {tab : ℕ → ℕ} {r : ℕ} {L : List ℕ} {MB E b c : ℕ} {k k' : ℕ → ℕ → ℕ → ℕ → Bool}
    (hk : ∀ a b c d, k a b c d = true → k' a b c d = true) (h : foldR tab r L MB E b c k = true) : foldR tab r L MB E b c k' = true := by
  induction L generalizing MB E b c with
  | nil => exact hk _ _ _ _ h
  | cons x L ih => exact ih h

theorem node5_mono {S D N U dP c2 h suf rec : ℕ} {ks : List ℕ} {k k' : ℕ → ℕ → ℕ → ℕ → Bool}
    (hk : ∀ a b c d, k a b c d = true → k' a b c d = true) (hn : node5 S D N U dP c2 h suf rec ks k = true) :
    node5 S D N U dP c2 h suf rec ks k' = true := by
  unfold node5 at hn ⊢
  simp only [Bool.and_eq_true] at hn ⊢
  exact ⟨hn.1, hk _ _ _ _ hn.2⟩

theorem batchX2'_imp (tab : ℕ → ℕ) : ∀ (nodes : List NodeX2) (st : List (ℕ × ℕ × ℕ × ℕ × ℕ)),
    batchX2' tab st nodes = true → batchX' tab st (nodes.map NodeX2.toNodeX) = true := by
  intro nodes
  induction nodes with
  | nil => intro st _; rfl
  | cons x rest ih =>
    intro st h
    obtain ⟨c2, h', suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x
    simp only [List.map_cons, NodeX2.toNodeX]
    unfold batchX2' at h
    unfold batchX'
    revert h
    rcases List.drop (Nat.land hdr 255) st with _ | ⟨⟨S, D, N, U, dP⟩, st'⟩
    · intro h; exact h
    · intro h
      simp only at h ⊢
      refine foldR_and_imp (fun _ _ _ _ h2 => foldR_and_imp (fun _ _ _ _ h1 => foldR_and_imp (fun _ _ _ _ h0 =>
        foldR_and_imp (fun _ _ _ _ hx2 => foldR_and_imp (fun _ _ _ _ hx1 => ?_) hx2) h0) h1) h2) h
      rw [Bool.and_eq_true] at hx1 ⊢
      refine ⟨hx1.1, ?_⟩
      revert hx1
      intro hx1
      exact node5_mono (fun S' D' N' U' hk => by
        rw [Bool.and_eq_true, Bool.and_eq_true] at hk ⊢
        exact ⟨⟨hk.1.1, xpartC2_imp hk.1.2⟩, ih _ hk.2⟩) hx1.2
/-- **`batchX2`'s contract**: the contract of `batchX` on the batch with unpacked trees -/
theorem batchX2_sound {Ω : Dec22 → Prop} (tab : ℕ → ℕ) (hT : TabOKU Ω tab) (st : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (nodes : List NodeX2)
    (hst : ∀ f ∈ st, FrameOKU Ω f.1 f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2)
    (hnodes : ∀ x ∈ nodes, C2OKU Ω ((x.2.2.2.1 >>> 8) % 512) x.1 ∧
      R3RT.SpecO.HOK R3RT.SpecO.LO123 ((x.2.2.2.1 >>> 8) % 512) x.2.1)
    (hfacts : ∀ x ∈ nodes, (∀ ag ∈ x.2.2.2.2.2.2.2.2.2.2.2.1, C2OKU Ω ag.1 ag.2.1) ∧
      (∀ c ∈ x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, KidXOK Ω c.toKidX))
    (h : batchX2 tab st nodes = true) : BatchOKX Ω st (nodes.map NodeX2.toNodeX) := by
  refine batchX_sound tab hT st _ hst ?_ ?_ (batchX2'_imp tab nodes st h)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c2, h', suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := y
    have := hnodes _ hy
    simp only [NodeX2.toNodeX] at this ⊢
    exact this
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c2, h', suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := y
    obtain ⟨ha, hk⟩ := hfacts _ hy
    simp only [NodeX2.toNodeX, nodeAggs, nodeKids] at ha hk ⊢
    refine ⟨ha, fun c hc => ?_⟩
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    exact hk c' hc'
end KD
