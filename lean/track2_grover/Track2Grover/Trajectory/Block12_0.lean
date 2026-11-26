module
public import Track2Grover.Trajectory.States12

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg12Block0 : rkm128kSubstepLoop 1 512 28817 28 seg12H seg12V0 70867379 = (seg12V1, 70946041) := by decide +kernel
end
end Track2Grover.FindAllCell
