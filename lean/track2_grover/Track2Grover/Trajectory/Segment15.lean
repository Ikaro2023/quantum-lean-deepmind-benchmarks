module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block15_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg15Walk : rkm128kSubstepLoop 1 512 28817 28 seg15H seg15V0 71172180 = (seg15V1, 71237660) := by
  exact seg15Block0

theorem seg15Result : rkm128kRunOneSeg 1024 2 512 segment15 1 512 71172178 seg15V0 =
    (1, 512, 71237660, seg15Next) := by
  rw [runOne_normal (seg := segment15) (lPrev := 1) (dCur := 512) (accPad := 71172178)
    (vec := seg15V0) (d := 512) (bCapCeil := 28817) (hb := seg15H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment15 512 (rkm128kSubstepLoop 1 512 28817 28 seg15H seg15V0 71172180) = _
  rw [seg15Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
