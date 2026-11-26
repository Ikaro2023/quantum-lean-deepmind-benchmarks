module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block18_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg18Walk : rkm128kSubstepLoop 1 512 28817 28 seg18H seg18V0 71581303 = (seg18V1, 71641175) := by
  exact seg18Block0

theorem seg18Result : rkm128kRunOneSeg 1024 2 512 segment18 1 512 71581301 seg18V0 =
    (1, 512, 71641175, seg18Next) := by
  rw [runOne_normal (seg := segment18) (lPrev := 1) (dCur := 512) (accPad := 71581301)
    (vec := seg18V0) (d := 512) (bCapCeil := 28817) (hb := seg18H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment18 512 (rkm128kSubstepLoop 1 512 28817 28 seg18H seg18V0 71581303) = _
  rw [seg18Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
