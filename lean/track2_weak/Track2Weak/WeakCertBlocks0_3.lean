module
public import Track2Weak.WeakCertStates0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block0_9 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b27 4528906 = (v0b30, 5284913) := by decide +kernel

theorem block0_10 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b30 5284913 = (v0b33, 6068742) := by decide +kernel

theorem block0_11 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b33 6068742 = (v0b36, 6876486) := by decide +kernel

end
end Track2Weak.Cert
