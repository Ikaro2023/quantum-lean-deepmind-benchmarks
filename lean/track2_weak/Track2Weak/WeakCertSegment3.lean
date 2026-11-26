module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks3_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run3 : rkm128kSubstepLoop 1 512 28817 28 hb3 v3b0 33822103 = (v3b1, 33930849) := by
  exact block3_0

theorem segResult3 : rkm128kRunOneSeg 1024 2 512 seg3 1 512 33822101 v3b0 =
      (1, 512, 33930849, out3) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg3) (lPrev := 1) (dCur := 512)
    (accPad := 33822101) (vec := v3b0) (d := 512) (bCapCeil := 28817) (hb := hb3)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg3 512
    (rkm128kSubstepLoop 1 512 28817 28 hb3 v3b0 33822103) = _
  rw [run3]
  decide +kernel

end
end Track2Weak.Cert
