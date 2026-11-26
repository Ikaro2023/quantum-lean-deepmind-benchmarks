module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block128 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V128 20719197 = (seg0V132, 21613841) := by decide +kernel

theorem seg0Block132 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V132 21613841 = (seg0V136, 22513353) := by decide +kernel

theorem seg0Block136 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V136 22513353 = (seg0V140, 23417171) := by decide +kernel

theorem seg0Block140 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V140 23417171 = (seg0V144, 24324660) := by decide +kernel
end
end Track2Grover.FindAllCell
