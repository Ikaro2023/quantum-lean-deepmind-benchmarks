module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks9_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run9 : rkm128kSubstepLoop 1 512 28817 28 hb9 v9b0 34487188 = (v9b1, 34584103) := by
  exact block9_0

theorem segResult9 : rkm128kRunOneSeg 1024 2 512 seg9 1 512 34487186 v9b0 =
      (1, 512, 34584103, out9) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg9) (lPrev := 1) (dCur := 512)
    (accPad := 34487186) (vec := v9b0) (d := 512) (bCapCeil := 28817) (hb := hb9)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg9 512
    (rkm128kSubstepLoop 1 512 28817 28 hb9 v9b0 34487188) = _
  rw [run9]
  decide +kernel

end
end Track2Weak.Cert
