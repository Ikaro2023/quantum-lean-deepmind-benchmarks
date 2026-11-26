module
public import Track2Weak.WeakCertStates16

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block16_0 : rkm128kSubstepLoop 1 512 28817 28 hb16 v16b0 34837921 = (v16b1, 34866295) := by decide +kernel

end
end Track2Weak.Cert
