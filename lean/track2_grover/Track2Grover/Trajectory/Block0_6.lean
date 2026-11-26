module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block96 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V96 13818366 = (seg0V100, 14649429) := by decide +kernel

theorem seg0Block100 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V100 14649429 = (seg0V104, 15491006) := by decide +kernel

theorem seg0Block104 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V104 15491006 = (seg0V108, 16342305) := by decide +kernel

theorem seg0Block108 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V108 16342305 = (seg0V112, 17202583) := by decide +kernel
end
end Track2Grover.FindAllCell
