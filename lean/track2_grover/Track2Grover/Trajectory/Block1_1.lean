module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block16 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V16 37336046 = (seg1V20, 38234908) := by decide +kernel

theorem seg1Block20 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V20 38234908 = (seg1V24, 39129599) := by decide +kernel

theorem seg1Block24 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V24 39129599 = (seg1V28, 40019802) := by decide +kernel

theorem seg1Block28 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V28 40019802 = (seg1V32, 40905093) := by decide +kernel
end
end Track2Grover.FindAllCell
