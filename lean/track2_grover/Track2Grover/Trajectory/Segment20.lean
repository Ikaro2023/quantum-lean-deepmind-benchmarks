module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block20_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg20Walk : rkm128kSubstepLoop 5 512 28817 28 seg20H seg20V0 71891208 = (seg20V5, 72172538) := by
  rw [show (5 : Nat) = 4 + 1 from rfl, walkAdd, seg20Block0]
  exact seg20Block4

theorem seg20Result : rkm128kRunOneSeg 1024 2 512 segment20 1 512 71891206 seg20V0 =
    (1, 512, 72172538, seg20Next) := by
  rw [runOne_normal (seg := segment20) (lPrev := 1) (dCur := 512) (accPad := 71891206)
    (vec := seg20V0) (d := 512) (bCapCeil := 28817) (hb := seg20H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment20 512 (rkm128kSubstepLoop 5 512 28817 28 seg20H seg20V0 71891208) = _
  rw [seg20Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
