module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block11_0

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg11Walk : rkm128kSubstepLoop 2 512 28817 28 seg11H seg11V0 70713612 = (seg11V2, 70867377) := by
  exact seg11Block0

theorem seg11Result : rkm128kRunOneSeg 1024 2 512 segment11 1 512 70713610 seg11V0 =
    (1, 512, 70867377, seg11Next) := by
  rw [runOne_normal (seg := segment11) (lPrev := 1) (dCur := 512) (accPad := 70713610)
    (vec := seg11V0) (d := 512) (bCapCeil := 28817) (hb := seg11H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment11 512 (rkm128kSubstepLoop 2 512 28817 28 seg11H seg11V0 70713612) = _
  rw [seg11Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
