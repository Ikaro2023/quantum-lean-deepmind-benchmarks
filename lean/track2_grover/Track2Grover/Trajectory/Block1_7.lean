module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block112 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V112 57091742 = (seg1V116, 57802901) := by decide +kernel

theorem seg1Block116 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V116 57802901 = (seg1V120, 58502680) := by decide +kernel

theorem seg1Block120 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V120 58502680 = (seg1V124, 59190892) := by decide +kernel

theorem seg1Block124 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V124 59190892 = (seg1V128, 59867142) := by decide +kernel
end
end Track2Grover.FindAllCell
