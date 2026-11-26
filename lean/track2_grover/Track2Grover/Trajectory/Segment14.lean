module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block14_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg14Walk : rkm128kSubstepLoop 2 512 28817 28 seg14H seg14V0 71020186 = (seg14V2, 71172178) := by
  exact seg14Block0

theorem seg14Result : rkm128kRunOneSeg 1024 2 512 segment14 1 512 71020184 seg14V0 =
    (1, 512, 71172178, seg14Next) := by
  rw [runOne_normal (seg := segment14) (lPrev := 1) (dCur := 512) (accPad := 71020184)
    (vec := seg14V0) (d := 512) (bCapCeil := 28817) (hb := seg14H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment14 512 (rkm128kSubstepLoop 2 512 28817 28 seg14H seg14V0 71020186) = _
  rw [seg14Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
