module
public import Track2Weak.WeakCertStates22

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block22_0 : rkm128kSubstepLoop 3 512 28817 28 hb22 v22b0 35052010 = (v22b3, 35088540) := by decide +kernel

theorem block22_1 : rkm128kSubstepLoop 1 512 28817 28 hb22 v22b3 35088540 = (v22b4, 35100420) := by decide +kernel

end
end Track2Weak.Cert
