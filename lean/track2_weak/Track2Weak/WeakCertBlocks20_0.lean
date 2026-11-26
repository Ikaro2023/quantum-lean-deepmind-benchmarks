module
public import Track2Weak.WeakCertStates20

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block20_0 : rkm128kSubstepLoop 2 512 28817 28 hb20 v20b0 34944271 = (v20b2, 35002122) := by decide +kernel

end
end Track2Weak.Cert
