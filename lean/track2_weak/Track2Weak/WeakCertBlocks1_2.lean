module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_6 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b18 20141531 = (v1b21, 21101675) := by decide +kernel

theorem block1_7 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b21 21101675 = (v1b24, 22050938) := by decide +kernel

theorem block1_8 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b24 22050938 = (v1b27, 22990895) := by decide +kernel

end
end Track2Weak.Cert
