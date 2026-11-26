module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_0 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b0 14385367 = (v1b3, 15334389) := by decide +kernel

theorem block1_1 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b3 15334389 = (v1b6, 16287869) := by decide +kernel

theorem block1_2 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b6 16287869 = (v1b9, 17248507) := by decide +kernel

end
end Track2Weak.Cert
