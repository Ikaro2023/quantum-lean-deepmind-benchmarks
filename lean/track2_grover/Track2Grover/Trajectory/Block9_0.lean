module
public import Track2Grover.Trajectory.States9

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg9Block0 : rkm128kSubstepLoop 2 512 28817 28 seg9H seg9V0 70471894 = (seg9V2, 70636590) := by decide +kernel
end
end Track2Grover.FindAllCell
