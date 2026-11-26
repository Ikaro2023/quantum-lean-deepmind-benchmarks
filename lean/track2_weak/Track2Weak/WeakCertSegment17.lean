module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks17_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run17 : rkm128kSubstepLoop 1 512 28817 28 hb17 v17b0 34866298 = (v17b1, 34891878) := by
  exact block17_0

theorem segResult17 : rkm128kRunOneSeg 1024 2 512 seg17 1 512 34866296 v17b0 =
      (1, 512, 34891878, out17) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg17) (lPrev := 1) (dCur := 512)
    (accPad := 34866296) (vec := v17b0) (d := 512) (bCapCeil := 28817) (hb := hb17)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg17 512
    (rkm128kSubstepLoop 1 512 28817 28 hb17 v17b0 34866298) = _
  rw [run17]
  decide +kernel

end
end Track2Weak.Cert
