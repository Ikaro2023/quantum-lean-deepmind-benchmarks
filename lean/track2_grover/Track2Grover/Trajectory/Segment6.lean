module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block6_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg6Walk : rkm128kSubstepLoop 1 512 28817 28 seg6H seg6V0 70140073 = (seg6V1, 70220755) := by
  exact seg6Block0

theorem seg6Result : rkm128kRunOneSeg 1024 2 512 segment6 1 512 70140071 seg6V0 =
    (1, 512, 70220755, seg6Next) := by
  rw [runOne_normal (seg := segment6) (lPrev := 1) (dCur := 512) (accPad := 70140071)
    (vec := seg6V0) (d := 512) (bCapCeil := 28817) (hb := seg6H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment6 512 (rkm128kSubstepLoop 1 512 28817 28 seg6H seg6V0 70140073) = _
  rw [seg6Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
