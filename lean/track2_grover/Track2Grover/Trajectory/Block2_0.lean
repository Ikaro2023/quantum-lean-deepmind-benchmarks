module
public import Track2Grover.Trajectory.States2

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg2Block0 : rkm128kSubstepLoop 2 512 28817 28 seg2H seg2V0 69498379 = (seg2V2, 69683483) := by decide +kernel
end
end Track2Grover.FindAllCell
