module
public import Track2Weak.WeakCertStates0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block0_0 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b0 3 = (v0b3, 173998) := by decide +kernel

theorem block0_1 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b3 173998 = (v0b6, 465997) := by decide +kernel

theorem block0_2 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b6 465997 = (v0b9, 860033) := by decide +kernel

end
end Track2Weak.Cert
