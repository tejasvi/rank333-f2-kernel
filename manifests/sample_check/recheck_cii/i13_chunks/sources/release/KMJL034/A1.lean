module
meta import KMod.Units
meta import KMod.Audit
public import KB.Agg321
meta import KB.ModAgg321
import KMJL034.I1
import KMJL034.I2
import KMJL034.I4
import KMJL034.I12
import KMJL034.I13
import KMJL034.I14
import KMJL034.I15
import KMJL034.A0
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000000
run_cmd Lean.modifyEnv (Lean.LibrarySuggestions.typePrefixDenyListExt.addEntry · `R22N.AllL)
/-! Cov aggregator KMJL034.A1 over 42 items (42 exported; py/mkaggf.py) -/
#kmAggF321 KMJL034.A1.cov 13 13 "src/KMJL034/A1.spec"
#kax KMJL034.A1.cov
