module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_9 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b27 22990895 = (v1b30, 23921966) := by decide +kernel

theorem block1_10 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b30 23921966 = (v1b33, 24835725) := by decide +kernel

theorem block1_11 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b33 24835725 = (v1b36, 25733174) := by decide +kernel

end
end Track2Weak.Cert
