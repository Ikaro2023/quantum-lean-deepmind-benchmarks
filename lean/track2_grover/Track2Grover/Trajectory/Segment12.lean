module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block12_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg12Walk : rkm128kSubstepLoop 1 512 28817 28 seg12H seg12V0 70867379 = (seg12V1, 70946041) := by
  exact seg12Block0

theorem seg12Result : rkm128kRunOneSeg 1024 2 512 segment12 1 512 70867377 seg12V0 =
    (1, 512, 70946041, seg12Next) := by
  rw [runOne_normal (seg := segment12) (lPrev := 1) (dCur := 512) (accPad := 70867377)
    (vec := seg12V0) (d := 512) (bCapCeil := 28817) (hb := seg12H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment12 512 (rkm128kSubstepLoop 1 512 28817 28 seg12H seg12V0 70867379) = _
  rw [seg12Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
