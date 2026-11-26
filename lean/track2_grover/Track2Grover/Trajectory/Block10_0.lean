module
public import Track2Grover.Trajectory.States10

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg10Block0 : rkm128kSubstepLoop 1 512 28817 28 seg10H seg10V0 70636592 = (seg10V1, 70713610) := by decide +kernel
end
end Track2Grover.FindAllCell
