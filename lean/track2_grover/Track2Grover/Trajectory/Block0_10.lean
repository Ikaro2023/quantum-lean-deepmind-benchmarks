module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block160 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V160 27979618 = (seg0V164, 28896896) := by decide +kernel

theorem seg0Block164 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V164 28896896 = (seg0V168, 29814542) := by decide +kernel

theorem seg0Block168 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V168 29814542 = (seg0V172, 30732054) := by decide +kernel

theorem seg0Block172 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V172 30732054 = (seg0V176, 31648943) := by decide +kernel
end
end Track2Grover.FindAllCell
