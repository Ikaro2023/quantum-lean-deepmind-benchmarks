module
public import Track2Weak.WeakCertStates2

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block2_0 : rkm128kSubstepLoop 2 512 28817 28 hb2 v2b0 33577970 = (v2b2, 33822101) := by decide +kernel

end
end Track2Weak.Cert
