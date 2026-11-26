module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks16_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run16 : rkm128kSubstepLoop 1 512 28817 28 hb16 v16b0 34837921 = (v16b1, 34866295) := by
  exact block16_0

theorem segResult16 : rkm128kRunOneSeg 1024 2 512 seg16 1 512 34837919 v16b0 =
      (1, 512, 34866295, out16) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg16) (lPrev := 1) (dCur := 512)
    (accPad := 34837919) (vec := v16b0) (d := 512) (bCapCeil := 28817) (hb := hb16)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg16 512
    (rkm128kSubstepLoop 1 512 28817 28 hb16 v16b0 34837921) = _
  rw [run16]
  decide +kernel

end
end Track2Weak.Cert
