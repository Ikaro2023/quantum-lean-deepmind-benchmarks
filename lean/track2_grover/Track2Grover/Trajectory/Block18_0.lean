module
public import Track2Grover.Trajectory.States18

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg18Block0 : rkm128kSubstepLoop 1 512 28817 28 seg18H seg18V0 71581303 = (seg18V1, 71641175) := by decide +kernel
end
end Track2Grover.FindAllCell
