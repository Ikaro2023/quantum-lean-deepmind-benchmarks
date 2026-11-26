module
public import Track2Weak.WeakCertStates19

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block19_0 : rkm128kSubstepLoop 1 512 28817 28 hb19 v19b0 34916788 = (v19b1, 34944268) := by decide +kernel

end
end Track2Weak.Cert
