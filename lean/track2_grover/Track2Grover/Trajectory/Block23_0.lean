module
public import Track2Grover.Trajectory.States23

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg23Block0 : rkm128kSubstepLoop 4 512 28817 28 seg23H seg23V0 72507250 = (seg23V4, 72669005) := by decide +kernel

theorem seg23Block4 : rkm128kSubstepLoop 1 512 28817 28 seg23H seg23V4 72669005 = (seg23V5, 72704159) := by decide +kernel
end
end Track2Grover.FindAllCell
