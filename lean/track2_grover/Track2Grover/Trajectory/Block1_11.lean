module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block176 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V176 66933860 = (seg1V180, 67423409) := by decide +kernel

theorem seg1Block180 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V180 67423409 = (seg1V184, 67895417) := by decide +kernel

theorem seg1Block184 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V184 67895417 = (seg1V188, 68349289) := by decide +kernel

theorem seg1Block188 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V188 68349289 = (seg1V192, 68784368) := by decide +kernel
end
end Track2Grover.FindAllCell
