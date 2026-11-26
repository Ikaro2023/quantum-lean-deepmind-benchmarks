module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block144 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V144 62446856 = (seg1V148, 63059002) := by decide +kernel

theorem seg1Block148 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V148 63059002 = (seg1V152, 63657285) := by decide +kernel

theorem seg1Block152 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V152 63657285 = (seg1V156, 64241345) := by decide +kernel

theorem seg1Block156 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V156 64241345 = (seg1V160, 64810825) := by decide +kernel
end
end Track2Grover.FindAllCell
