module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block192 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V192 68784368 = (seg1V196, 69199894) := by decide +kernel

theorem seg1Block196 : rkm128kSubstepLoop 3 512 28817 28 seg1H seg1V196 69199894 = (seg1V199, 69498377) := by decide +kernel
end
end Track2Grover.FindAllCell
