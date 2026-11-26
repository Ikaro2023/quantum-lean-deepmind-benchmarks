module
public import Track2Weak.WeakCertStates7

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block7_0 : rkm128kSubstepLoop 1 512 28817 28 hb7 v7b0 34228239 = (v7b1, 34342745) := by decide +kernel

end
end Track2Weak.Cert
