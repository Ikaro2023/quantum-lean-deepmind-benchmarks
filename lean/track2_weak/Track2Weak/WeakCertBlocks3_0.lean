module
public import Track2Weak.WeakCertStates3

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block3_0 : rkm128kSubstepLoop 1 512 28817 28 hb3 v3b0 33822103 = (v3b1, 33930849) := by decide +kernel

end
end Track2Weak.Cert
