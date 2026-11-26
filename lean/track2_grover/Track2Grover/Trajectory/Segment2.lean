module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block2_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg2Walk : rkm128kSubstepLoop 2 512 28817 28 seg2H seg2V0 69498379 = (seg2V2, 69683483) := by
  exact seg2Block0

theorem seg2Result : rkm128kRunOneSeg 1024 2 512 segment2 1 512 69498377 seg2V0 =
    (1, 512, 69683483, seg2Next) := by
  rw [runOne_normal (seg := segment2) (lPrev := 1) (dCur := 512) (accPad := 69498377)
    (vec := seg2V0) (d := 512) (bCapCeil := 28817) (hb := seg2H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment2 512 (rkm128kSubstepLoop 2 512 28817 28 seg2H seg2V0 69498379) = _
  rw [seg2Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
