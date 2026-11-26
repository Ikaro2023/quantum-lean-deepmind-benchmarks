module
public import Track2Weak.WeakCertStates11

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block11_0 : rkm128kSubstepLoop 1 512 28817 28 hb11 v11b0 34636617 = (v11b1, 34690854) := by decide +kernel

end
end Track2Weak.Cert
