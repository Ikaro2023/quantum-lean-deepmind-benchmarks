module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block10_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg10Walk : rkm128kSubstepLoop 1 512 28817 28 seg10H seg10V0 70636592 = (seg10V1, 70713610) := by
  exact seg10Block0

theorem seg10Result : rkm128kRunOneSeg 1024 2 512 segment10 1 512 70636590 seg10V0 =
    (1, 512, 70713610, seg10Next) := by
  rw [runOne_normal (seg := segment10) (lPrev := 1) (dCur := 512) (accPad := 70636590)
    (vec := seg10V0) (d := 512) (bCapCeil := 28817) (hb := seg10H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment10 512 (rkm128kSubstepLoop 1 512 28817 28 seg10H seg10V0 70636592) = _
  rw [seg10Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
