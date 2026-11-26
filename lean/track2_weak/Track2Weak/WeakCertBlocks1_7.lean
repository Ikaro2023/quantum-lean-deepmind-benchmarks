module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_21 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b63 32761982 = (v1b66, 33381118) := by decide +kernel

theorem block1_22 : rkm128kSubstepLoop 1 512 28817 28 hb1 v1b66 33381118 = (v1b67, 33577968) := by decide +kernel

end
end Track2Weak.Cert
