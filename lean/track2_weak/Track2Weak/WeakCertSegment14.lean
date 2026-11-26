module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks14_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run14 : rkm128kSubstepLoop 1 512 28817 28 hb14 v14b0 34775150 = (v14b1, 34807250) := by
  exact block14_0

theorem segResult14 : rkm128kRunOneSeg 1024 2 512 seg14 1 512 34775148 v14b0 =
      (1, 512, 34807250, out14) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg14) (lPrev := 1) (dCur := 512)
    (accPad := 34775148) (vec := v14b0) (d := 512) (bCapCeil := 28817) (hb := hb14)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg14 512
    (rkm128kSubstepLoop 1 512 28817 28 hb14 v14b0 34775150) = _
  rw [run14]
  decide +kernel

end
end Track2Weak.Cert
