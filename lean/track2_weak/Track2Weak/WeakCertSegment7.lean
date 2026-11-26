module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks7_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run7 : rkm128kSubstepLoop 1 512 28817 28 hb7 v7b0 34228239 = (v7b1, 34342745) := by
  exact block7_0

theorem segResult7 : rkm128kRunOneSeg 1024 2 512 seg7 1 512 34228237 v7b0 =
      (1, 512, 34342745, out7) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg7) (lPrev := 1) (dCur := 512)
    (accPad := 34228237) (vec := v7b0) (d := 512) (bCapCeil := 28817) (hb := hb7)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg7 512
    (rkm128kSubstepLoop 1 512 28817 28 hb7 v7b0 34228239) = _
  rw [run7]
  decide +kernel

end
end Track2Weak.Cert
