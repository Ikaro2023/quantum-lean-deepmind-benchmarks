module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block9_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg9Walk : rkm128kSubstepLoop 2 512 28817 28 seg9H seg9V0 70471894 = (seg9V2, 70636590) := by
  exact seg9Block0

theorem seg9Result : rkm128kRunOneSeg 1024 2 512 segment9 1 512 70471892 seg9V0 =
    (1, 512, 70636590, seg9Next) := by
  rw [runOne_normal (seg := segment9) (lPrev := 1) (dCur := 512) (accPad := 70471892)
    (vec := seg9V0) (d := 512) (bCapCeil := 28817) (hb := seg9H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment9 512 (rkm128kSubstepLoop 2 512 28817 28 seg9H seg9V0 70471894) = _
  rw [seg9Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
