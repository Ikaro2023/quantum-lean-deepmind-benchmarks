module
public import Track2Grover.Trajectory.States19

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg19Block0 : rkm128kSubstepLoop 4 512 28817 28 seg19H seg19V0 71641177 = (seg19V4, 71891206) := by decide +kernel
end
end Track2Grover.FindAllCell
