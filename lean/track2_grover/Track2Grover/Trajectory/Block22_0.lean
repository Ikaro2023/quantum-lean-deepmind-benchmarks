module
public import Track2Grover.Trajectory.States22

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg22Block0 : rkm128kSubstepLoop 4 512 28817 28 seg22H seg22V0 72220570 = (seg22V4, 72418501) := by decide +kernel

theorem seg22Block4 : rkm128kSubstepLoop 2 512 28817 28 seg22H seg22V4 72418501 = (seg22V6, 72507248) := by decide +kernel
end
end Track2Grover.FindAllCell
