module
public import Track2Weak.WeakCertStates6

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block6_0 : rkm128kSubstepLoop 1 512 28817 28 hb6 v6b0 34133448 = (v6b1, 34228237) := by decide +kernel

end
end Track2Weak.Cert
