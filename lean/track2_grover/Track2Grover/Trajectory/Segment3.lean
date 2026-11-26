module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block3_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg3Walk : rkm128kSubstepLoop 1 512 28817 28 seg3H seg3V0 69683485 = (seg3V1, 69777732) := by
  exact seg3Block0

theorem seg3Result : rkm128kRunOneSeg 1024 2 512 segment3 1 512 69683483 seg3V0 =
    (1, 512, 69777732, seg3Next) := by
  rw [runOne_normal (seg := segment3) (lPrev := 1) (dCur := 512) (accPad := 69683483)
    (vec := seg3V0) (d := 512) (bCapCeil := 28817) (hb := seg3H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment3 512 (rkm128kSubstepLoop 1 512 28817 28 seg3H seg3V0 69683485) = _
  rw [seg3Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
