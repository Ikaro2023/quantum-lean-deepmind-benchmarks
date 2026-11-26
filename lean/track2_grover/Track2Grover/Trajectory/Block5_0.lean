module
public import Track2Grover.Trajectory.States5

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg5Block0 : rkm128kSubstepLoop 2 512 28817 28 seg5H seg5V0 69962176 = (seg5V2, 70140071) := by decide +kernel
end
end Track2Grover.FindAllCell
