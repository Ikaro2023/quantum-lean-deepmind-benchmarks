module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_15 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b45 28314287 = (v1b48, 29128723) := by decide +kernel

theorem block1_16 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b48 29128723 = (v1b51, 29917525) := by decide +kernel

theorem block1_17 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b51 29917525 = (v1b54, 30677883) := by decide +kernel

end
end Track2Weak.Cert
