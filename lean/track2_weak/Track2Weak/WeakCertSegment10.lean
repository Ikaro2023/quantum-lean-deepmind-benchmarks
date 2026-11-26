module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks10_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run10 : rkm128kSubstepLoop 1 512 28817 28 hb10 v10b0 34584106 = (v10b1, 34636614) := by
  exact block10_0

theorem segResult10 : rkm128kRunOneSeg 1024 2 512 seg10 1 512 34584104 v10b0 =
      (1, 512, 34636614, out10) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg10) (lPrev := 1) (dCur := 512)
    (accPad := 34584104) (vec := v10b0) (d := 512) (bCapCeil := 28817) (hb := hb10)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg10 512
    (rkm128kSubstepLoop 1 512 28817 28 hb10 v10b0 34584106) = _
  rw [run10]
  decide +kernel

end
end Track2Weak.Cert
