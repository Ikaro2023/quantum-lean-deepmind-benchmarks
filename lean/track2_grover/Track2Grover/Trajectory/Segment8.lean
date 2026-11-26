module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block8_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg8Walk : rkm128kSubstepLoop 1 512 28817 28 seg8H seg8V0 70393914 = (seg8V1, 70471892) := by
  exact seg8Block0

theorem seg8Result : rkm128kRunOneSeg 1024 2 512 segment8 1 512 70393912 seg8V0 =
    (1, 512, 70471892, seg8Next) := by
  rw [runOne_normal (seg := segment8) (lPrev := 1) (dCur := 512) (accPad := 70393912)
    (vec := seg8V0) (d := 512) (bCapCeil := 28817) (hb := seg8H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment8 512 (rkm128kSubstepLoop 1 512 28817 28 seg8H seg8V0 70393914) = _
  rw [seg8Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
