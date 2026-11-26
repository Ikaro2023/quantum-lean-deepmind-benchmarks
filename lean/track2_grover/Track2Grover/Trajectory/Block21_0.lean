module
public import Track2Grover.Trajectory.States21

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg21Block0 : rkm128kSubstepLoop 1 512 28817 28 seg21H seg21V0 72172540 = (seg21V1, 72220568) := by decide +kernel
end
end Track2Grover.FindAllCell
