module
public import Track2Weak.WeakCertStates9

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block9_0 : rkm128kSubstepLoop 1 512 28817 28 hb9 v9b0 34487188 = (v9b1, 34584103) := by decide +kernel

end
end Track2Weak.Cert
