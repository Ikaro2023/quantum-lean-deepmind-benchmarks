module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block48 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V48 44390471 = (seg1V52, 45246182) := by decide +kernel

theorem seg1Block52 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V52 45246182 = (seg1V56, 46094992) := by decide +kernel

theorem seg1Block56 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V56 46094992 = (seg1V60, 46936603) := by decide +kernel

theorem seg1Block60 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V60 46936603 = (seg1V64, 47770712) := by decide +kernel
end
end Track2Grover.FindAllCell
