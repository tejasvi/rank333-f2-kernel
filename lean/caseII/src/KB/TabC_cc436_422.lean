module
public import R22Port.U_d41d8cd98f00
public import L1.Load
/-! L1's static exclusion tables `L1.T.c2t_<l>` and `L1.T.CONF1T` for the kept rows of the CC route's case-(II) table cc436_422
(`py/mkcc.py cc436_422 "436:19,422:19"`), from `kinds/data/cc/cc436_422/cc436_422.c2t`.  Import this instead of `R3RT.TabC3eD` in
timing files of records generated on that table (`kxu.sh` with `KXU_TAB=KB.TabC_cc436_422`). -/
@[expose] public section
#l1tables "data/cc436_422/cc436_422.c2t"
