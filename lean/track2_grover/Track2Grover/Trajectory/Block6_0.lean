module
public import Track2Grover.Trajectory.States6

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg6Block0 : rkm128kSubstepLoop 1 512 28817 28 seg6H seg6V0 70140073 = (seg6V1, 70220755) := by decide +kernel
end
end Track2Grover.FindAllCell
