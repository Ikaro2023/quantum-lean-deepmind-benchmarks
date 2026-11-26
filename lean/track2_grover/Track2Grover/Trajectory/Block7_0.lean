module
public import Track2Grover.Trajectory.States7

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg7Block0 : rkm128kSubstepLoop 2 512 28817 28 seg7H seg7V0 70220757 = (seg7V2, 70393912) := by decide +kernel
end
end Track2Grover.FindAllCell
