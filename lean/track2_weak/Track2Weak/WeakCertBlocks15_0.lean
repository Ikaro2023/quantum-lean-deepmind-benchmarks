module
public import Track2Weak.WeakCertStates15

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block15_0 : rkm128kSubstepLoop 1 512 28817 28 hb15 v15b0 34807253 = (v15b1, 34837918) := by decide +kernel

end
end Track2Weak.Cert
