module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks2_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run2 : rkm128kSubstepLoop 2 512 28817 28 hb2 v2b0 33577970 = (v2b2, 33822101) := by
  exact block2_0

theorem segResult2 : rkm128kRunOneSeg 1024 2 512 seg2 1 512 33577968 v2b0 =
      (1, 512, 33822101, out2) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg2) (lPrev := 1) (dCur := 512)
    (accPad := 33577968) (vec := v2b0) (d := 512) (bCapCeil := 28817) (hb := hb2)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg2 512
    (rkm128kSubstepLoop 2 512 28817 28 hb2 v2b0 33577970) = _
  rw [run2]
  decide +kernel

end
end Track2Weak.Cert
