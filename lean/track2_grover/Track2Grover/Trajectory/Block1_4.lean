module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block64 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V64 47770712 = (seg1V68, 48597006) := by decide +kernel

theorem seg1Block68 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V68 48597006 = (seg1V72, 49415219) := by decide +kernel

theorem seg1Block72 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V72 49415219 = (seg1V76, 50225067) := by decide +kernel

theorem seg1Block76 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V76 50225067 = (seg1V80, 51026261) := by decide +kernel
end
end Track2Grover.FindAllCell
