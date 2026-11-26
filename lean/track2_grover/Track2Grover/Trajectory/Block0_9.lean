module
public import Track2Grover.Trajectory.States0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Block144 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V144 24324660 = (seg0V148, 25235215) := by decide +kernel

theorem seg0Block148 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V148 25235215 = (seg0V152, 26148253) := by decide +kernel

theorem seg0Block152 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V152 26148253 = (seg0V156, 27063226) := by decide +kernel

theorem seg0Block156 : rkm128kSubstepLoop 4 512 28817 28 seg0H seg0V156 27063226 = (seg0V160, 27979618) := by decide +kernel
end
end Track2Grover.FindAllCell
