module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block5_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg5Walk : rkm128kSubstepLoop 2 512 28817 28 seg5H seg5V0 69962176 = (seg5V2, 70140071) := by
  exact seg5Block0

theorem seg5Result : rkm128kRunOneSeg 1024 2 512 segment5 1 512 69962174 seg5V0 =
    (1, 512, 70140071, seg5Next) := by
  rw [runOne_normal (seg := segment5) (lPrev := 1) (dCur := 512) (accPad := 69962174)
    (vec := seg5V0) (d := 512) (bCapCeil := 28817) (hb := seg5H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment5 512 (rkm128kSubstepLoop 2 512 28817 28 seg5H seg5V0 69962176) = _
  rw [seg5Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
