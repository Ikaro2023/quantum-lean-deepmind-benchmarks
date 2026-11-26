module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks8_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run8 : rkm128kSubstepLoop 2 512 28817 28 hb8 v8b0 34342747 = (v8b2, 34487186) := by
  exact block8_0

theorem segResult8 : rkm128kRunOneSeg 1024 2 512 seg8 1 512 34342745 v8b0 =
      (1, 512, 34487186, out8) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg8) (lPrev := 1) (dCur := 512)
    (accPad := 34342745) (vec := v8b0) (d := 512) (bCapCeil := 28817) (hb := hb8)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg8 512
    (rkm128kSubstepLoop 2 512 28817 28 hb8 v8b0 34342747) = _
  rw [run8]
  decide +kernel

end
end Track2Weak.Cert
