module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_12 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b36 25733174 = (v1b39, 26615167) := by decide +kernel

theorem block1_13 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b39 26615167 = (v1b42, 27476480) := by decide +kernel

theorem block1_14 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b42 27476480 = (v1b45, 28314287) := by decide +kernel

end
end Track2Weak.Cert
