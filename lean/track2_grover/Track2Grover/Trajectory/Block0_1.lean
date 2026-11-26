module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block16 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V16 963728 = (seg0V20, 1338550) := by decide +kernel

theorem seg0Block20 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V20 1338550 = (seg0V24, 1757724) := by decide +kernel

theorem seg0Block24 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V24 1757724 = (seg0V28, 2216472) := by decide +kernel

theorem seg0Block28 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V28 2216472 = (seg0V32, 2710593) := by decide +kernel
end
end Track2Grover.FindAllCell
