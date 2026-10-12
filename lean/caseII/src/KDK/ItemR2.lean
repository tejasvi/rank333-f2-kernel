module
public import R22Port.U_d41d8cd98f00
public import KDK.ItemR
public import KDK.XBatch2
/-! # KDK.ItemR2 (kinds-only name of KD.ItemR2): items with the X part's cheaper front end (`KD.xpartC2`, packed trees)

`itemXR2'` is `KD.itemXR'` on records with packed children (`NodeX2`): `nodeXO2` runs `xpartC2` in place of `xpartC`, and the
static check, the children's mask and the pending labels read the same fields of `KidX2`.  **`itemXR2'_imp`**: an accepted batch
of `itemXR2'` makes `itemXR'` accept the same batch with the trees unpacked (`NodeX2.toNodeX`), so every theorem about `itemXR'`
(`itemXR'_sound`, `ChainR`, `itemR_cov`, the KB contract) applies to the unpacked records. -/
@[expose] public section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section
namespace KD
open R3RT.Spec
open R3RT (foldR node5 mkD)

def nodeKs2 (x : NodeX2) : List ℕ := x.2.2.2.2.2.2.2.2.2.1
def nodeAggs2 (x : NodeX2) : List Agg := x.2.2.2.2.2.2.2.2.2.2.2.1
def nodeKids2 (x : NodeX2) : List KidX2 := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

def kidStat2 (c2T : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (c : KidX2) : Bool :=
  Nat.blt c.1 511 && Nat.beq c.2.2.2.2.1 (c2T c.1) && tupBeq c.2.2.2.2.2 (cpT c.1)

def statX2 (c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (x : NodeX2) : Bool :=
  Nat.blt (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) 511 &&
  Nat.beq x.1 (c2T (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) &&
  Nat.beq x.2.1 (hkT (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) &&
  allB (aggStat c2T) (nodeAggs2 x) && allB (kidStat2 c2T cpT) (nodeKids2 x)

def kidMask2 (kids : List KidX2) : ℕ := maskL (fun c => c.1) kids

def pendOf2 (last : ℕ) (ks : List ℕ) (kids : List KidX2) (acc xk D' : ℕ) : ℕ :=
  K2.andn (K2.andn (K2.andn (K2.andn (K2.andn (above511 last) (killMask ks)) (kidMask2 kids)) acc) xk) D'

def pendR2 (last : ℕ) (ks : List ℕ) (kids : List KidX2) (acc xk D' low rgl : ℕ) : ℕ :=
  K2.andn (K2.andn (pendOf2 last ks kids acc xk D') low) (geL rgl)

def nodeXO2 (np : ℕ → ℕ) (tab : ℕ → ℕ) (S D N U dP : ℕ) : NodeX2 → (ℕ → ℕ → ℕ → ℕ → Bool) → Bool
  | (c2, h, suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids), k =>
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
                  xpartC2 np S' D' N' U' (Nat.succ dP) (Nat.land (Nat.shiftRight hdr 8) 511) (Nat.add c0' c1')
                    (Nat.add c0' (Nat.add c1' c2')) (Nat.add (Nat.add c0' (Nat.add c1' c2')) cx')
                    (mkD MB MBx (Nat.add c0' (Nat.add c1' c2'))) nrows aggs XL HP DEFP J kids &&
                  k S' D' N' U'))))))

/-- **one batch of an item with ranges**, packed children -/
def itemXR2' {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (extL : List (ℕ × ℕ))
    (lo : ℕ) (rngL : List ((ℕ × ℕ) × ℕ))
    (ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk rg : E → ℕ) (tab : ℕ → ℕ) :
    List FrP → List (NodeX2 × E) → List FrP → Bool
  | st, [], out => stEq st out
  | st, (x, e) :: rest, out =>
    match List.drop (Nat.land x.2.2.2.1 255) st with
    | [] => false
    | ((S, D, N, U, dP), pend) :: st' =>
      pendZ (List.take (Nat.land x.2.2.2.1 255) st) &&
      Nat.beq (bitAt pend (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) 1 && Nat.ble (Nat.succ dP) 21 &&
      statX2 c2T hkT cpT x &&
      nodeXO2 np tab S D N U dP x (fun S' D' N' U' =>
        ext S' D' N' U' (Nat.succ dP) (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) e &&
        (Nat.beq (xk e) 0 || Nat.beq (xkRest extL S' (xk e)) 0) &&
        (Nat.beq (rg e) 511 || rngMem rngL S' (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) (rg e)) &&
        itemXR2' np c2T hkT cpT extL lo rngL ext acc xk rg tab
          (((S', D', N', U', Nat.succ dP),
              pendR2 (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511) (nodeKs2 x) (nodeKids2 x) (acc e) (xk e) D' (lowOf st' lo) (rg e)) ::
            ((S, D, N, U, dP), clrBit pend (Nat.land (Nat.shiftRight x.2.2.2.1 8) 511)) :: st') rest out)

/-! ## Reduction to `itemXR'` -/

theorem allB_map {α β : Type} (p : β → Bool) (f : α → β) : ∀ (l : List α), allB p (l.map f) = allB (fun a => p (f a)) l
  | [] => rfl
  | a :: l => by
    change (p (f a) && allB p (l.map f)) = (p (f a) && allB (fun a => p (f a)) l)
    rw [allB_map p f l]

theorem maskL_map {α β : Type} (g : β → ℕ) (f : α → β) : ∀ (l : List α), maskL g (l.map f) = maskL (fun a => g (f a)) l
  | [] => rfl
  | a :: l => by
    change Nat.lor (Nat.shiftLeft 1 (g (f a))) (maskL g (l.map f)) = Nat.lor (Nat.shiftLeft 1 (g (f a))) (maskL (fun a => g (f a)) l)
    rw [maskL_map g f l]

theorem statX2_eq (c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (x : NodeX2) : statX2 c2T hkT cpT x = statX c2T hkT cpT x.toNodeX := by
  obtain ⟨c2, h, suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x
  simp only [statX2, statX, NodeX2.toNodeX, nodeAggs2, nodeKids2, nodeAggs, nodeKids, allB_map]
  rfl

theorem pendR2_eq (last : ℕ) (ks : List ℕ) (kids : List KidX2) (acc xk D' low rgl : ℕ) :
    pendR2 last ks kids acc xk D' low rgl = pendR last ks (kids.map KidX2.toKidX) acc xk D' low rgl := by
  simp only [pendR2, pendR, pendOf2, pendOf, kidMask2, kidMask, maskL_map]
  rfl

theorem nodeXO2_imp {np tab : ℕ → ℕ} {S D N U dP : ℕ} {x : NodeX2} {k2 k : ℕ → ℕ → ℕ → ℕ → Bool}
    (hk : ∀ a b c d, k2 a b c d = true → k a b c d = true) (h : nodeXO2 np tab S D N U dP x k2 = true) :
    nodeXO np tab S D N U dP x.toNodeX k = true := by
  obtain ⟨c2, h', suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x
  simp only [NodeX2.toNodeX]
  unfold nodeXO2 at h
  unfold nodeXO
  refine foldR_and_imp (fun _ _ _ _ h2 => foldR_and_imp (fun _ _ _ _ h1 => foldR_and_imp (fun _ _ _ _ h0 =>
    foldR_and_imp (fun _ _ _ _ hx2 => foldR_and_imp (fun _ _ _ _ hx1 => ?_) hx2) h0) h1) h2) h
  rw [Bool.and_eq_true] at hx1 ⊢
  refine ⟨hx1.1, node5_mono (fun S' D' N' U' hq => ?_) hx1.2⟩
  rw [Bool.and_eq_true, Bool.and_eq_true] at hq ⊢
  exact ⟨⟨hq.1.1, xpartC2_imp hq.1.2⟩, hk _ _ _ _ hq.2⟩

/-- **`itemXR2'` reduces to `itemXR'`** on the unpacked records -/
theorem itemXR2'_imp {E : Type} (np c2T hkT : ℕ → ℕ) (cpT : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ) (extL : List (ℕ × ℕ))
    (lo : ℕ) (rngL : List ((ℕ × ℕ) × ℕ)) (ext : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E → Bool) (acc xk rg : E → ℕ) (tab : ℕ → ℕ) :
    ∀ (nodes : List (NodeX2 × E)) (st out : List FrP),
      itemXR2' np c2T hkT cpT extL lo rngL ext acc xk rg tab st nodes out = true →
      itemXR' np c2T hkT cpT extL lo rngL ext acc xk rg tab st (nodes.map (fun p => (p.1.toNodeX, p.2))) out = true := by
  intro nodes
  induction nodes with
  | nil => intro st out h; exact h
  | cons p rest ih =>
    intro st out h
    obtain ⟨x, e⟩ := p
    have hhdr : (x.toNodeX).2.2.2.1 = x.2.2.2.1 := by
      obtain ⟨c2, h', suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x; rfl
    have hks : nodeKs x.toNodeX = nodeKs2 x := by
      obtain ⟨c2, h', suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x; rfl
    have hkids : nodeKids x.toNodeX = (nodeKids2 x).map KidX2.toKidX := by
      obtain ⟨c2, h', suf, hdr, r2, r1, r0, x2, x1, ks, nrows, aggs, XL, HP, DEFP, J, kids⟩ := x; rfl
    simp only [List.map_cons]
    unfold itemXR2' at h
    unfold itemXR'
    rw [hhdr]
    revert h
    rcases List.drop (Nat.land x.2.2.2.1 255) st with _ | ⟨⟨⟨S, D, N, U, dP⟩, pend⟩, st'⟩
    · intro h; exact h
    · intro h
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨⟨⟨⟨hz, hb⟩, hd⟩, hs⟩, hn⟩ := h
      refine ⟨⟨⟨⟨hz, hb⟩, hd⟩, by rw [← statX2_eq]; exact hs⟩, nodeXO2_imp (fun S' D' N' U' hq => ?_) hn⟩
      simp only [Bool.and_eq_true] at hq ⊢
      obtain ⟨⟨⟨he, hx⟩, hr⟩, hi⟩ := hq
      refine ⟨⟨⟨he, hx⟩, hr⟩, ?_⟩
      rw [hks, hkids, ← pendR2_eq]
      exact ih _ _ hi
end KD
