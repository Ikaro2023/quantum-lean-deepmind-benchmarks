module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks13_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run13 : rkm128kSubstepLoop 1 512 28817 28 hb13 v13b0 34735859 = (v13b1, 34775147) := by
  exact block13_0

theorem segResult13 : rkm128kRunOneSeg 1024 2 512 seg13 1 512 34735857 v13b0 =
      (1, 512, 34775147, out13) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg13) (lPrev := 1) (dCur := 512)
    (accPad := 34735857) (vec := v13b0) (d := 512) (bCapCeil := 28817) (hb := hb13)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg13 512
    (rkm128kSubstepLoop 1 512 28817 28 hb13 v13b0 34735859) = _
  rw [run13]
  decide +kernel

end
end Track2Weak.Cert
