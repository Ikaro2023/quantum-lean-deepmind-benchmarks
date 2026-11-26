module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks20_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run20 : rkm128kSubstepLoop 2 512 28817 28 hb20 v20b0 34944271 = (v20b2, 35002122) := by
  exact block20_0

theorem segResult20 : rkm128kRunOneSeg 1024 2 512 seg20 1 512 34944269 v20b0 =
      (1, 512, 35002122, out20) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg20) (lPrev := 1) (dCur := 512)
    (accPad := 34944269) (vec := v20b0) (d := 512) (bCapCeil := 28817) (hb := hb20)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg20 512
    (rkm128kSubstepLoop 2 512 28817 28 hb20 v20b0 34944271) = _
  rw [run20]
  decide +kernel

end
end Track2Weak.Cert
