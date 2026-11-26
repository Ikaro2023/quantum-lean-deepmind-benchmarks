module
public import Track2Grover.Trajectory.States14

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg14Block0 : rkm128kSubstepLoop 2 512 28817 28 seg14H seg14V0 71020186 = (seg14V2, 71172178) := by decide +kernel
end
end Track2Grover.FindAllCell
