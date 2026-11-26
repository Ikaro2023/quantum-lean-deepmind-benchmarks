module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block4_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg4Walk : rkm128kSubstepLoop 2 512 28817 28 seg4H seg4V0 69777734 = (seg4V2, 69962174) := by
  exact seg4Block0

theorem seg4Result : rkm128kRunOneSeg 1024 2 512 segment4 1 512 69777732 seg4V0 =
    (1, 512, 69962174, seg4Next) := by
  rw [runOne_normal (seg := segment4) (lPrev := 1) (dCur := 512) (accPad := 69777732)
    (vec := seg4V0) (d := 512) (bCapCeil := 28817) (hb := seg4H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment4 512 (rkm128kSubstepLoop 2 512 28817 28 seg4H seg4V0 69777734) = _
  rw [seg4Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
