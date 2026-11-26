module
public import Track2Grover.Trajectory.States3

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg3Block0 : rkm128kSubstepLoop 1 512 28817 28 seg3H seg3V0 69683485 = (seg3V1, 69777732) := by decide +kernel
end
end Track2Grover.FindAllCell
