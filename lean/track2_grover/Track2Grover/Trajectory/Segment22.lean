module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block22_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg22Walk : rkm128kSubstepLoop 6 512 28817 28 seg22H seg22V0 72220570 = (seg22V6, 72507248) := by
  rw [show (6 : Nat) = 4 + 2 from rfl, walkAdd, seg22Block0]
  exact seg22Block4

theorem seg22Result : rkm128kRunOneSeg 1024 2 512 segment22 1 512 72220568 seg22V0 =
    (1, 512, 72507248, seg22Next) := by
  rw [runOne_normal (seg := segment22) (lPrev := 1) (dCur := 512) (accPad := 72220568)
    (vec := seg22V0) (d := 512) (bCapCeil := 28817) (hb := seg22H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment22 512 (rkm128kSubstepLoop 6 512 28817 28 seg22H seg22V0 72220570) = _
  rw [seg22Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
