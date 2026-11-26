module
public import Track2Weak.WeakCertStates0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block0_12 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b36 6876486 = (v0b39, 7704354) := by decide +kernel

theorem block0_13 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b39 7704354 = (v0b42, 8548976) := by decide +kernel

theorem block0_14 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b42 8548976 = (v0b45, 9407077) := by decide +kernel

end
end Track2Weak.Cert
