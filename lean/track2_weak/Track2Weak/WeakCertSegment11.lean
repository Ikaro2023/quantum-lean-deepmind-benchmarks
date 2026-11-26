module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks11_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run11 : rkm128kSubstepLoop 1 512 28817 28 hb11 v11b0 34636617 = (v11b1, 34690854) := by
  exact block11_0

theorem segResult11 : rkm128kRunOneSeg 1024 2 512 seg11 1 512 34636615 v11b0 =
      (1, 512, 34690854, out11) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg11) (lPrev := 1) (dCur := 512)
    (accPad := 34636615) (vec := v11b0) (d := 512) (bCapCeil := 28817) (hb := hb11)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg11 512
    (rkm128kSubstepLoop 1 512 28817 28 hb11 v11b0 34636617) = _
  rw [run11]
  decide +kernel

end
end Track2Weak.Cert
