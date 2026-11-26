module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_18 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b54 30677883 = (v1b57, 31407158) := by decide +kernel

theorem block1_19 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b57 31407158 = (v1b60, 32102885) := by decide +kernel

theorem block1_20 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b60 32102885 = (v1b63, 32761982) := by decide +kernel

end
end Track2Weak.Cert
