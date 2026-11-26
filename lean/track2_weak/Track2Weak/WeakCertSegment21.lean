module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks21_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run21 : rkm128kSubstepLoop 3 512 28817 28 hb21 v21b0 35002125 = (v21b3, 35052007) := by
  exact block21_0

theorem segResult21 : rkm128kRunOneSeg 1024 2 512 seg21 1 512 35002123 v21b0 =
      (1, 512, 35052007, out21) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg21) (lPrev := 1) (dCur := 512)
    (accPad := 35002123) (vec := v21b0) (d := 512) (bCapCeil := 28817) (hb := hb21)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg21 512
    (rkm128kSubstepLoop 3 512 28817 28 hb21 v21b0 35002125) = _
  rw [run21]
  decide +kernel

end
end Track2Weak.Cert
