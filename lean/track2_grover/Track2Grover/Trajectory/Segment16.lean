module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block16_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg16Walk : rkm128kSubstepLoop 1 512 28817 28 seg16H seg16V0 71237662 = (seg16V1, 71306386) := by
  exact seg16Block0

theorem seg16Result : rkm128kRunOneSeg 1024 2 512 segment16 1 512 71237660 seg16V0 =
    (1, 512, 71306386, seg16Next) := by
  rw [runOne_normal (seg := segment16) (lPrev := 1) (dCur := 512) (accPad := 71237660)
    (vec := seg16V0) (d := 512) (bCapCeil := 28817) (hb := seg16H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment16 512 (rkm128kSubstepLoop 1 512 28817 28 seg16H seg16V0 71237662) = _
  rw [seg16Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
