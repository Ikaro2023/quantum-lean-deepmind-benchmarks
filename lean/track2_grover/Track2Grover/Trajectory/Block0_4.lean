module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block64 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V64 7649135 = (seg0V68, 8365105) := by decide +kernel

theorem seg0Block68 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V68 8365105 = (seg0V72, 9098824) := by decide +kernel

theorem seg0Block72 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V72 9098824 = (seg0V76, 9849239) := by decide +kernel

theorem seg0Block76 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V76 9849239 = (seg0V80, 10615344) := by decide +kernel
end
end Track2Grover.FindAllCell
