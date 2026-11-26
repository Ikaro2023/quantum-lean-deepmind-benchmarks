module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block96 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V96 54139036 = (seg1V100, 54892894) := by decide +kernel

theorem seg1Block100 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V100 54892894 = (seg1V104, 55636473) := by decide +kernel

theorem seg1Block104 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V104 55636473 = (seg1V108, 56369506) := by decide +kernel

theorem seg1Block108 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V108 56369506 = (seg1V112, 57091742) := by decide +kernel
end
end Track2Grover.FindAllCell
