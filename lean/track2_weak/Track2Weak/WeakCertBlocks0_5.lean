module
public import Track2Weak.WeakCertStates0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem block0_15 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b45 9407077 = (v0b48, 10275560) := by decide +kernel

theorem block0_16 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b48 10275560 = (v0b51, 11151596) := by decide +kernel

theorem block0_17 : rkm128kSubstepLoop 3 512 28817 28 hb0 v0b51 11151596 = (v0b54, 12032334) := by decide +kernel

end
end Track2Weak.Cert
