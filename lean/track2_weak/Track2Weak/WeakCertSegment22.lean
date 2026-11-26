module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks22_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run22 : rkm128kSubstepLoop 4 512 28817 28 hb22 v22b0 35052010 = (v22b4, 35100420) := by
  rw [show (4 : Nat) = 3 + 1 from rfl, Track2Weak.SegmentGlue.walkAdd, block22_0]
  exact block22_1

theorem segResult22 : rkm128kRunOneSeg 1024 2 512 seg22 1 512 35052008 v22b0 =
      (1, 512, 35100420, out22) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg22) (lPrev := 1) (dCur := 512)
    (accPad := 35052008) (vec := v22b0) (d := 512) (bCapCeil := 28817) (hb := hb22)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg22 512
    (rkm128kSubstepLoop 4 512 28817 28 hb22 v22b0 35052010) = _
  rw [run22]
  decide +kernel

end
end Track2Weak.Cert
