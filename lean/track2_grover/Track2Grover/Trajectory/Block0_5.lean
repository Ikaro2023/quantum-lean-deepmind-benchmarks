module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block80 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V80 10615344 = (seg0V84, 11396203) := by decide +kernel

theorem seg0Block84 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V84 11396203 = (seg0V88, 12190913) := by decide +kernel

theorem seg0Block88 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V88 12190913 = (seg0V92, 12998576) := by decide +kernel

theorem seg0Block92 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V92 12998576 = (seg0V96, 13818366) := by decide +kernel
end
end Track2Grover.FindAllCell
