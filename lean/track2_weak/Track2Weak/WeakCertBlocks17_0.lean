module
public import Track2Weak.WeakCertStates17

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block17_0 : rkm128kSubstepLoop 1 512 28817 28 hb17 v17b0 34866298 = (v17b1, 34891878) := by decide +kernel

end
end Track2Weak.Cert
