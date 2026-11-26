module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block7_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg7Walk : rkm128kSubstepLoop 2 512 28817 28 seg7H seg7V0 70220757 = (seg7V2, 70393912) := by
  exact seg7Block0

theorem seg7Result : rkm128kRunOneSeg 1024 2 512 segment7 1 512 70220755 seg7V0 =
    (1, 512, 70393912, seg7Next) := by
  rw [runOne_normal (seg := segment7) (lPrev := 1) (dCur := 512) (accPad := 70220755)
    (vec := seg7V0) (d := 512) (bCapCeil := 28817) (hb := seg7H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment7 512 (rkm128kSubstepLoop 2 512 28817 28 seg7H seg7V0 70220757) = _
  rw [seg7Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
