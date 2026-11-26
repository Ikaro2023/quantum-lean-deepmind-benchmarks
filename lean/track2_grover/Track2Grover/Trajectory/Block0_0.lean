module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block0 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V0 3 = (seg0V4, 154593) := by decide +kernel

theorem seg0Block4 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V4 154593 = (seg0V8, 368784) := by decide +kernel

theorem seg0Block8 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V8 368784 = (seg0V12, 638821) := by decide +kernel

theorem seg0Block12 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V12 638821 = (seg0V16, 963728) := by decide +kernel
end
end Track2Grover.FindAllCell
