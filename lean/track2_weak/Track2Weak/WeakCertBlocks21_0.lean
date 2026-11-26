module
public import Track2Weak.WeakCertStates21

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block21_0 : rkm128kSubstepLoop 3 512 28817 28 hb21 v21b0 35002125 = (v21b3, 35052007) := by decide +kernel

end
end Track2Weak.Cert
