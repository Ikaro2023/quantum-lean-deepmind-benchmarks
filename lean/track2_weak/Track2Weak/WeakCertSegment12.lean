module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks12_0

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run12 : rkm128kSubstepLoop 1 512 28817 28 hb12 v12b0 34690857 = (v12b1, 34735856) := by
  exact block12_0

theorem segResult12 : rkm128kRunOneSeg 1024 2 512 seg12 1 512 34690855 v12b0 =
      (1, 512, 34735856, out12) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg12) (lPrev := 1) (dCur := 512)
    (accPad := 34690855) (vec := v12b0) (d := 512) (bCapCeil := 28817) (hb := hb12)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg12 512
    (rkm128kSubstepLoop 1 512 28817 28 hb12 v12b0 34690857) = _
  rw [run12]
  decide +kernel

end
end Track2Weak.Cert
