module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block160 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V160 64810825 = (seg1V164, 65365278) := by decide +kernel

theorem seg1Block164 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V164 65365278 = (seg1V168, 65904282) := by decide +kernel

theorem seg1Block168 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V168 65904282 = (seg1V172, 66427264) := by decide +kernel

theorem seg1Block172 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V172 66427264 = (seg1V176, 66933860) := by decide +kernel
end
end Track2Grover.FindAllCell
