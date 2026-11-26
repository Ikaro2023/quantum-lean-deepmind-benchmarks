module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks19_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run19 : rkm128kSubstepLoop 1 512 28817 28 hb19 v19b0 34916788 = (v19b1, 34944268) := by
  exact block19_0

theorem segResult19 : rkm128kRunOneSeg 1024 2 512 seg19 1 512 34916786 v19b0 =
      (1, 512, 34944268, out19) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg19) (lPrev := 1) (dCur := 512)
    (accPad := 34916786) (vec := v19b0) (d := 512) (bCapCeil := 28817) (hb := hb19)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg19 512
    (rkm128kSubstepLoop 1 512 28817 28 hb19 v19b0 34916788) = _
  rw [run19]
  decide +kernel

end
end Track2Weak.Cert
