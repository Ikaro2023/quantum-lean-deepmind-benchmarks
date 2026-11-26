module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks15_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run15 : rkm128kSubstepLoop 1 512 28817 28 hb15 v15b0 34807253 = (v15b1, 34837918) := by
  exact block15_0

theorem segResult15 : rkm128kRunOneSeg 1024 2 512 seg15 1 512 34807251 v15b0 =
      (1, 512, 34837918, out15) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg15) (lPrev := 1) (dCur := 512)
    (accPad := 34807251) (vec := v15b0) (d := 512) (bCapCeil := 28817) (hb := hb15)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg15 512
    (rkm128kSubstepLoop 1 512 28817 28 hb15 v15b0 34807253) = _
  rw [run15]
  decide +kernel

end
end Track2Weak.Cert
