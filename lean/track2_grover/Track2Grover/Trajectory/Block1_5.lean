module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block80 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V80 51026261 = (seg1V84, 51818525) := by decide +kernel

theorem seg1Block84 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V84 51818525 = (seg1V88, 52601586) := by decide +kernel

theorem seg1Block88 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V88 52601586 = (seg1V92, 53375189) := by decide +kernel

theorem seg1Block92 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V92 53375189 = (seg1V96, 54139036) := by decide +kernel
end
end Track2Grover.FindAllCell
