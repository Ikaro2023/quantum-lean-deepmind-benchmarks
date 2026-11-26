module
public import Track2Weak.WeakCertStates0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block0_6 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b18 2473022 = (v0b21, 3117921) := by decide +kernel

theorem block0_7 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b21 3117921 = (v0b24, 3804960) := by decide +kernel

theorem block0_8 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b24 3804960 = (v0b27, 4528906) := by decide +kernel

end
end Track2Weak.Cert
