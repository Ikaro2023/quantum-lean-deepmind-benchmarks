module
public import Track2Weak.WeakCertStates14

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block14_0 : rkm128kSubstepLoop 1 512 28817 28 hb14 v14b0 34775150 = (v14b1, 34807250) := by decide +kernel

end
end Track2Weak.Cert
