module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block128 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V128 59867142 = (seg1V132, 60531124) := by decide +kernel

theorem seg1Block132 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V132 60531124 = (seg1V136, 61182617) := by decide +kernel

theorem seg1Block136 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V136 61182617 = (seg1V140, 61821264) := by decide +kernel

theorem seg1Block140 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V140 61821264 = (seg1V144, 62446856) := by decide +kernel
end
end Track2Grover.FindAllCell
