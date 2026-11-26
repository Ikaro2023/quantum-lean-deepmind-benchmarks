module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block112 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V112 17202583 = (seg0V116, 18071107) := by decide +kernel

theorem seg0Block116 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V116 18071107 = (seg0V120, 18947167) := by decide +kernel

theorem seg0Block120 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V120 18947167 = (seg0V124, 19830100) := by decide +kernel

theorem seg0Block124 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V124 19830100 = (seg0V128, 20719197) := by decide +kernel
end
end Track2Grover.FindAllCell
