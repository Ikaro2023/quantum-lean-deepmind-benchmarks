module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block32 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V32 40905093 = (seg1V36, 41785154) := by decide +kernel

theorem seg1Block36 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V36 41785154 = (seg1V40, 42659636) := by decide +kernel

theorem seg1Block40 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V40 42659636 = (seg1V44, 43528181) := by decide +kernel

theorem seg1Block44 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V44 43528181 = (seg1V48, 44390471) := by decide +kernel
end
end Track2Grover.FindAllCell
