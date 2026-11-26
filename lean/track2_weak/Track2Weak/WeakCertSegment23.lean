module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks23_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run23 : rkm128kSubstepLoop 5 512 28817 28 hb23 v23b0 35100423 = (v23b5, 35144918) := by
  rw [show (5 : Nat) = 3 + 2 from rfl, Track2Weak.SegmentGlue.walkAdd, block23_0]
  exact block23_1

theorem segResult23 : rkm128kRunOneSeg 1024 2 512 seg23 1 512 35100421 v23b0 =
      (1, 512, 35144918, out23) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg23) (lPrev := 1) (dCur := 512)
    (accPad := 35100421) (vec := v23b0) (d := 512) (bCapCeil := 28817) (hb := hb23)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg23 512
    (rkm128kSubstepLoop 5 512 28817 28 hb23 v23b0 35100423) = _
  rw [run23]
  decide +kernel

end
end Track2Weak.Cert
