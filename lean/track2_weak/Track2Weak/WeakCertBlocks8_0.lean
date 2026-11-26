module
public import Track2Weak.WeakCertStates8

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block8_0 : rkm128kSubstepLoop 2 512 28817 28 hb8 v8b0 34342747 = (v8b2, 34487186) := by decide +kernel

end
end Track2Weak.Cert
