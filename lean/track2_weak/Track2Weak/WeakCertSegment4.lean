module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks4_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run4 : rkm128kSubstepLoop 1 512 28817 28 hb4 v4b0 33930851 = (v4b1, 34027525) := by
  exact block4_0

theorem segResult4 : rkm128kRunOneSeg 1024 2 512 seg4 1 512 33930849 v4b0 =
      (1, 512, 34027525, out4) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg4) (lPrev := 1) (dCur := 512)
    (accPad := 33930849) (vec := v4b0) (d := 512) (bCapCeil := 28817) (hb := hb4)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg4 512
    (rkm128kSubstepLoop 1 512 28817 28 hb4 v4b0 33930851) = _
  rw [run4]
  decide +kernel

end
end Track2Weak.Cert
