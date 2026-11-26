module
public import Track2Weak.WeakCertStates4

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block4_0 : rkm128kSubstepLoop 1 512 28817 28 hb4 v4b0 33930851 = (v4b1, 34027525) := by decide +kernel

end
end Track2Weak.Cert
