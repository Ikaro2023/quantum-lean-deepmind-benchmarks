module
public import Track2Weak.WeakCertStates1

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block1_3 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b9 17248507 = (v1b12, 18215245) := by decide +kernel

theorem block1_4 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b12 18215245 = (v1b15, 19179171) := by decide +kernel

theorem block1_5 : rkm128kSubstepLoop 3 512 28817 28 hb1 v1b15 19179171 = (v1b18, 20141531) := by decide +kernel

end
end Track2Weak.Cert
