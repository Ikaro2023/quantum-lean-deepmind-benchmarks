module
public import Track2Weak.WeakCertStates0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block0_3 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b9 860033 = (v0b12, 1335335) := by decide +kernel

theorem block0_4 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b12 1335335 = (v0b15, 1876350) := by decide +kernel

theorem block0_5 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b15 1876350 = (v0b18, 2473022) := by decide +kernel

end
end Track2Weak.Cert
