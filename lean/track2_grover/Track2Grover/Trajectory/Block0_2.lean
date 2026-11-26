module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block32 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V32 2710593 = (seg0V36, 3236944) := by decide +kernel

theorem seg0Block36 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V36 3236944 = (seg0V40, 3792927) := by decide +kernel

theorem seg0Block40 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V40 3792927 = (seg0V44, 4376470) := by decide +kernel

theorem seg0Block44 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V44 4376470 = (seg0V48, 4985624) := by decide +kernel
end
end Track2Grover.FindAllCell
