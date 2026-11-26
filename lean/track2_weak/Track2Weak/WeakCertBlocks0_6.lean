module
public import Track2Weak.WeakCertStates0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block0_18 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b54 12032334 = (v0b57, 12915389) := by decide +kernel

theorem block0_19 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b57 12915389 = (v0b60, 13798149) := by decide +kernel

theorem block0_20 : rkm128kSubstepLoop 2 512 28817 28 hb0 v0b60 13798149 = (v0b62, 14385365) := by decide +kernel

end
end Track2Weak.Cert
