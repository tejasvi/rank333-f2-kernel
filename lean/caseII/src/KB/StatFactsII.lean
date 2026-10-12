module
public import R22Port.U_d41d8cd98f00
public import L5.T321H
public import KB.ExtII
public import KB.BindII_00
public import KB.BindII_01
public import KB.BindII_02
public import KB.BindII_03
public import KB.BindII_04
public import KB.BindII_05
public import KB.BindII_06
public import KB.BindII_07
public import KB.BindII_08
public import KB.BindII_09
public import KB.BindII_10
public import KB.BindII_11
public import KB.BindII_12
public import KB.BindII_13
public import KB.BindII_14
public import KB.BindII_15
public import KB.BindII_c1
/-! # KB.StatFactsII: the static facts of case (II)'s item checker, and its contract without hypotheses

* `hcII` / `hc1II`: the label tables `KI.c2T` (cap 2) and `KI.c1` (cap 1) are valid under the class facts: R3's binding of each
  table to RT's verified kept rows (`R3RT.bindQ` over `L5II.rowEII`, kernel checks `KI.bq_<q>` in `KB.BindII_*`, collected in
  `KI.c2_all`) and `L5II.bindQ_specII`.
* `hhII`: `KI.hkT l` is label `l`'s hit vector (one kernel evaluation over the 511 labels, `L5O.hok_of`).
* `hcpII`: `KI.cpT u` are the window constants of `510 - u` fields (one kernel evaluation of `KD.constBeq`, `KD.cpn_of_beq`).
* **`segRefII_full`**: `SegRefHK HII LO123 (CaseK 14 22) CheckedII` (`= R22B.SegRefH`), with `CheckedII` the kernel track's item
  predicate at case (II)'s tables: every item key with an accepted item check has a segment with exactly its interface, certified
  under the facts `HII = ClassFactsC (CaseK 14 22) HC.cLBII ∧ KD.TypeFacts`. -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
#kibindAll
noncomputable section
namespace KB
open R3RT.SpecO

theorem hk_all : S5.allLT 511 (fun l => Nat.beq (KI.hkT l) (L5O.hitV (R3RT.vecL l))) = true := by decide +kernel

theorem hhII : ∀ l, l < 511 → HOK LO123 l (KI.hkT l) := fun l hl =>
  L5O.hok_of LO123 l (KI.hkT l) (Nat.eq_of_beq_eq_true (S5.allLT_spec hk_all l hl))

theorem cp_all : S5.allLT 511 (fun u => KD.constBeq (510 - u) (KI.cpT u)) = true := by decide +kernel

theorem hcpII : ∀ u, u < 511 → KD.CPn (510 - u) (KI.cpT u) := fun u hu =>
  KD.cpn_of_beq (by omega) (S5.allLT_spec cp_all u hu)

theorem h479II : HC.cLBII 479 = 21 := by simp [HC.cLBII]

theorem hc2II : HII → ∀ l, l < 511 → KD.C2OKU (CaseK 14 22) l (KI.c2T l) := fun hH l hl =>
  (L5II.bindQ_specII HC.cLBII h479II (fun c hc => if_neg hc) l (KI.bindRows l) (KI.c2T l) KI.DC hH.1).1 hl
    (allBelow_spec KI.c2_all l hl)

theorem hc1II : HII → Conf1OK LO123 (CaseK 14 22) KI.c1 := fun hH =>
  (L5II.bindQ_specII HC.cLBII h479II (fun c hc => if_neg hc) 511 KI.rows_511 KI.c1 KI.DC hH.1).2 KI.bq_511

/-- **the kernel track's checker contract for case (II)**, without hypotheses -/
theorem segRefII_full : SegRefHK HII LO123 (CaseK 14 22) CheckedII :=
  segRefII hhII hcpII hc1II hc2II

/-- the same for items whose root is a dead node -/
theorem segRefDeadII_full : SegRefHK HII LO123 (CaseK 14 22) CheckedDeadII :=
  segRefDeadII hhII hcpII hc1II hc2II

/-- **the kernel track's checker contract for case (II), all items** (OPEN or dead root) -/
theorem segRefAllII : SegRefHK HII LO123 (CaseK 14 22) (fun k => CheckedII k ∨ CheckedDeadII k) :=
  fun k h => h.elim (segRefII_full k) (segRefDeadII_full k)

end KB
