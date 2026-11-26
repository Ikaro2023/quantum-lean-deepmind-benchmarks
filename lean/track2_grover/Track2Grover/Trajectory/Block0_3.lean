module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block48 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V48 4985624 = (seg0V52, 5618947) := by decide +kernel

theorem seg0Block52 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V52 5618947 = (seg0V56, 6274868) := by decide +kernel

theorem seg0Block56 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V56 6274868 = (seg0V60, 6952005) := by decide +kernel

theorem seg0Block60 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V60 6952005 = (seg0V64, 7649135) := by decide +kernel
end
end Track2Grover.FindAllCell
