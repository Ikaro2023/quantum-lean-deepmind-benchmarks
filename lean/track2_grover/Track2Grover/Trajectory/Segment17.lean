module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block17_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg17Walk : rkm128kSubstepLoop 4 512 28817 28 seg17H seg17V0 71306388 = (seg17V4, 71581301) := by
  exact seg17Block0

theorem seg17Result : rkm128kRunOneSeg 1024 2 512 segment17 1 512 71306386 seg17V0 =
    (1, 512, 71581301, seg17Next) := by
  rw [runOne_normal (seg := segment17) (lPrev := 1) (dCur := 512) (accPad := 71306386)
    (vec := seg17V0) (d := 512) (bCapCeil := 28817) (hb := seg17H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment17 512 (rkm128kSubstepLoop 4 512 28817 28 seg17H seg17V0 71306388) = _
  rw [seg17Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
