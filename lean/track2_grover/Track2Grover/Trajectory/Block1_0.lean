module
public import Track2Grover.Trajectory.States1

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Block0 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V0 33707230 = (seg1V4, 34618636) := by decide +kernel

theorem seg1Block4 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V4 34618636 = (seg1V8, 35527524) := by decide +kernel

theorem seg1Block8 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V8 35527524 = (seg1V12, 36433450) := by decide +kernel

theorem seg1Block12 : rkm128kSubstepLoop 4 512 28817 28 seg1H seg1V12 36433450 = (seg1V16, 37336046) := by decide +kernel
end
end Track2Grover.FindAllCell
