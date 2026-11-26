module
public import Track2Grover.Trajectory.States20

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg20Block0 : rkm128kSubstepLoop 4 512 28817 28 seg20H seg20V0 71891208 = (seg20V4, 72119109) := by decide +kernel

theorem seg20Block4 : rkm128kSubstepLoop 1 512 28817 28 seg20H seg20V4 72119109 = (seg20V5, 72172538) := by decide +kernel
end
end Track2Grover.FindAllCell
