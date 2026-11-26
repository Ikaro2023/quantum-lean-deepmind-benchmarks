module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block19_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg19Walk : rkm128kSubstepLoop 4 512 28817 28 seg19H seg19V0 71641177 = (seg19V4, 71891206) := by
  exact seg19Block0

theorem seg19Result : rkm128kRunOneSeg 1024 2 512 segment19 1 512 71641175 seg19V0 =
    (1, 512, 71891206, seg19Next) := by
  rw [runOne_normal (seg := segment19) (lPrev := 1) (dCur := 512) (accPad := 71641175)
    (vec := seg19V0) (d := 512) (bCapCeil := 28817) (hb := seg19H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment19 512 (rkm128kSubstepLoop 4 512 28817 28 seg19H seg19V0 71641177) = _
  rw [seg19Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
