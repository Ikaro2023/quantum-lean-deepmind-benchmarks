module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks5_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run5 : rkm128kSubstepLoop 1 512 28817 28 hb5 v5b0 34027527 = (v5b1, 34133446) := by
  exact block5_0

theorem segResult5 : rkm128kRunOneSeg 1024 2 512 seg5 1 512 34027525 v5b0 =
      (1, 512, 34133446, out5) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg5) (lPrev := 1) (dCur := 512)
    (accPad := 34027525) (vec := v5b0) (d := 512) (bCapCeil := 28817) (hb := hb5)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg5 512
    (rkm128kSubstepLoop 1 512 28817 28 hb5 v5b0 34027527) = _
  rw [run5]
  decide +kernel

end
end Track2Weak.Cert
