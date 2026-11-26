module
public import Track2Weak.WeakCertStates23

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block23_0 : rkm128kSubstepLoop 3 512 28817 28 hb23 v23b0 35100423 = (v23b3, 35128611) := by decide +kernel

theorem block23_1 : rkm128kSubstepLoop 2 512 28817 28 hb23 v23b3 35128611 = (v23b5, 35144918) := by decide +kernel

end
end Track2Weak.Cert
