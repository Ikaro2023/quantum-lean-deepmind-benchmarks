module
public import Track2Grover.Trajectory.States16

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg16Block0 : rkm128kSubstepLoop 1 512 28817 28 seg16H seg16V0 71237662 = (seg16V1, 71306386) := by decide +kernel
end
end Track2Grover.FindAllCell
