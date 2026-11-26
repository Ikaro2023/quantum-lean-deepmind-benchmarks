module
public import Track2Grover.Trajectory.States13

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg13Block0 : rkm128kSubstepLoop 1 512 28817 28 seg13H seg13V0 70946043 = (seg13V1, 71020184) := by decide +kernel
end
end Track2Grover.FindAllCell
