module
public import Track2Grover.Trajectory.States4

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg4Block0 : rkm128kSubstepLoop 2 512 28817 28 seg4H seg4V0 69777734 = (seg4V2, 69962174) := by decide +kernel
end
end Track2Grover.FindAllCell
