module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block176 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V176 31648943 = (seg0V180, 32564735) := by decide +kernel

theorem seg0Block180 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V180 32564735 = (seg0V184, 33478967) := by decide +kernel

theorem seg0Block184 : rkm128kSubstepLoop 1 512 28817 28 seg0H seg0V184 33478967 = (seg0V185, 33707228) := by decide +kernel
end
end Track2Grover.FindAllCell
