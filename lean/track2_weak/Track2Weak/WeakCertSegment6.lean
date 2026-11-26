module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks6_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run6 : rkm128kSubstepLoop 1 512 28817 28 hb6 v6b0 34133448 = (v6b1, 34228237) := by
  exact block6_0

theorem segResult6 : rkm128kRunOneSeg 1024 2 512 seg6 1 512 34133446 v6b0 =
      (1, 512, 34228237, out6) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg6) (lPrev := 1) (dCur := 512)
    (accPad := 34133446) (vec := v6b0) (d := 512) (bCapCeil := 28817) (hb := hb6)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg6 512
    (rkm128kSubstepLoop 1 512 28817 28 hb6 v6b0 34133448) = _
  rw [run6]
  decide +kernel

end
end Track2Weak.Cert
