module
public import R22Port.U_d41d8cd98f00
public import KB.LoadItem
/-! # KB.StatII: the label tables of case (II)'s item checker (`KI.c2T`, `KI.hkT`, `KI.cpT`, `KI.c1`), `KB.LoadItem`'s
`#kdstatII` on R3's case-(II) static tables `rerun/r3/rt479/C3eDII.c2t` (cap-1 table `KI.c1`; its per-label cap-2 tables equal
`R3RT.TabC3eD`'s `L1.T.c2t_<l>`, checked: one table differs, slot 511, the cap-1 table) -/
@[expose] public section
#kdstatII "data/rt479/C3eDII.c2t"

namespace KB
/-- the kernel track's item predicate of case (II): `KD.batchX`'s node check with the case-(II) extension, R3's per-job table,
the root frame and the key's interface, at case (II)'s label tables -/
abbrev CheckedII : ℕ → Prop :=
  CheckedK R3RT.nperpL KI.c2T KI.hkT KI.cpT (fun tab => extII R3RT.nperpL KI.c2T KI.hkT KI.cpT tab) accII xkII KI.c1 TabVII
/-- the item predicate of case (II) for items whose root is a dead node -/
abbrev CheckedDeadII : ℕ → Prop := CheckedDeadK R3RT.nperpL KI.c2T KI.hkT KI.cpT KI.c1 TabVII
end KB
