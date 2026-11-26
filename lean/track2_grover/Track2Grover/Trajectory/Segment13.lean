module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block13_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg13Walk : rkm128kSubstepLoop 1 512 28817 28 seg13H seg13V0 70946043 = (seg13V1, 71020184) := by
  exact seg13Block0

theorem seg13Result : rkm128kRunOneSeg 1024 2 512 segment13 1 512 70946041 seg13V0 =
    (1, 512, 71020184, seg13Next) := by
  rw [runOne_normal (seg := segment13) (lPrev := 1) (dCur := 512) (accPad := 70946041)
    (vec := seg13V0) (d := 512) (bCapCeil := 28817) (hb := seg13H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment13 512 (rkm128kSubstepLoop 1 512 28817 28 seg13H seg13V0 70946043) = _
  rw [seg13Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
