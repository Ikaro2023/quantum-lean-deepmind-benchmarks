module
public import Track2Weak.WeakCertStates10

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block10_0 : rkm128kSubstepLoop 1 512 28817 28 hb10 v10b0 34584106 = (v10b1, 34636614) := by decide +kernel

end
end Track2Weak.Cert
