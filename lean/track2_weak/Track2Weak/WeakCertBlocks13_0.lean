module
public import Track2Weak.WeakCertStates13

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block13_0 : rkm128kSubstepLoop 1 512 28817 28 hb13 v13b0 34735859 = (v13b1, 34775147) := by decide +kernel

end
end Track2Weak.Cert
