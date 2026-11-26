module
public import Track2Grover.Trajectory.States11

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg11Block0 : rkm128kSubstepLoop 2 512 28817 28 seg11H seg11V0 70713612 = (seg11V2, 70867377) := by decide +kernel
end
end Track2Grover.FindAllCell
