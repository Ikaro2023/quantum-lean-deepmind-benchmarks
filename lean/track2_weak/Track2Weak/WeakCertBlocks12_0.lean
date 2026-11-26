module
public import Track2Weak.WeakCertStates12

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block12_0 : rkm128kSubstepLoop 1 512 28817 28 hb12 v12b0 34690857 = (v12b1, 34735856) := by decide +kernel

end
end Track2Weak.Cert
