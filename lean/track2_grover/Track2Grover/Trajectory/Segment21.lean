module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block21_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg21Walk : rkm128kSubstepLoop 1 512 28817 28 seg21H seg21V0 72172540 = (seg21V1, 72220568) := by
  exact seg21Block0

theorem seg21Result : rkm128kRunOneSeg 1024 2 512 segment21 1 512 72172538 seg21V0 =
    (1, 512, 72220568, seg21Next) := by
  rw [runOne_normal (seg := segment21) (lPrev := 1) (dCur := 512) (accPad := 72172538)
    (vec := seg21V0) (d := 512) (bCapCeil := 28817) (hb := seg21H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment21 512 (rkm128kSubstepLoop 1 512 28817 28 seg21H seg21V0 72172540) = _
  rw [seg21Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
