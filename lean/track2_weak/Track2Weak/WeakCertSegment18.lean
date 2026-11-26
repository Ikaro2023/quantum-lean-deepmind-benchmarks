module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks18_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run18 : rkm128kSubstepLoop 1 512 28817 28 hb18 v18b0 34891881 = (v18b1, 34916785) := by
  exact block18_0

theorem segResult18 : rkm128kRunOneSeg 1024 2 512 seg18 1 512 34891879 v18b0 =
      (1, 512, 34916785, out18) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg18) (lPrev := 1) (dCur := 512)
    (accPad := 34891879) (vec := v18b0) (d := 512) (bCapCeil := 28817) (hb := hb18)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg18 512
    (rkm128kSubstepLoop 1 512 28817 28 hb18 v18b0 34891881) = _
  rw [run18]
  decide +kernel

end
end Track2Weak.Cert
