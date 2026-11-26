module
public import Track2Grover.Trajectory.States8

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg8Block0 : rkm128kSubstepLoop 1 512 28817 28 seg8H seg8V0 70393914 = (seg8V1, 70471892) := by decide +kernel
end
end Track2Grover.FindAllCell
