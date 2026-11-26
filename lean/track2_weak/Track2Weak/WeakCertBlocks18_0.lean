module
public import Track2Weak.WeakCertStates18

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block18_0 : rkm128kSubstepLoop 1 512 28817 28 hb18 v18b0 34891881 = (v18b1, 34916785) := by decide +kernel

end
end Track2Weak.Cert
