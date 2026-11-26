module
public import Track2Grover.Trajectory.States15

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg15Block0 : rkm128kSubstepLoop 1 512 28817 28 seg15H seg15V0 71172180 = (seg15V1, 71237660) := by decide +kernel
end
end Track2Grover.FindAllCell
