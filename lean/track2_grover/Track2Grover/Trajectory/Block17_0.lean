module
public import Track2Grover.Trajectory.States17

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg17Block0 : rkm128kSubstepLoop 4 512 28817 28 seg17H seg17V0 71306388 = (seg17V4, 71581301) := by decide +kernel
end
end Track2Grover.FindAllCell
