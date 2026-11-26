module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block23_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg23Walk : rkm128kSubstepLoop 5 512 28817 28 seg23H seg23V0 72507250 = (seg23V5, 72704159) := by
  rw [show (5 : Nat) = 4 + 1 from rfl, walkAdd, seg23Block0]
  exact seg23Block4

theorem seg23Result : rkm128kRunOneSeg 1024 2 512 segment23 1 512 72507248 seg23V0 =
    (1, 512, 72704159, seg23Next) := by
  rw [runOne_normal (seg := segment23) (lPrev := 1) (dCur := 512) (accPad := 72507248)
    (vec := seg23V0) (d := 512) (bCapCeil := 28817) (hb := seg23H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment23 512 (rkm128kSubstepLoop 5 512 28817 28 seg23H seg23V0 72507250) = _
  rw [seg23Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
