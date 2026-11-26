module
public import Track2Weak.WeakCertStates5

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block5_0 : rkm128kSubstepLoop 1 512 28817 28 hb5 v5b0 34027527 = (v5b1, 34133446) := by decide +kernel

end
end Track2Weak.Cert
