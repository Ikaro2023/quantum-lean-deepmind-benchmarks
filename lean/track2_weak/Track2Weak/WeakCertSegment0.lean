module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks0_0
public import Track2Weak.WeakCertBlocks0_1
public import Track2Weak.WeakCertBlocks0_2
public import Track2Weak.WeakCertBlocks0_3
public import Track2Weak.WeakCertBlocks0_4
public import Track2Weak.WeakCertBlocks0_5
public import Track2Weak.WeakCertBlocks0_6

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run0 : rkm128kSubstepLoop 62 512 28817 28 hb0 v0b0 3 = (v0b62, 14385365) := by
  rw [show (62 : Nat) = 3 + 59 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_0]
  rw [show (59 : Nat) = 3 + 56 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_1]
  rw [show (56 : Nat) = 3 + 53 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_2]
  rw [show (53 : Nat) = 3 + 50 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_3]
  rw [show (50 : Nat) = 3 + 47 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_4]
  rw [show (47 : Nat) = 3 + 44 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_5]
  rw [show (44 : Nat) = 3 + 41 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_6]
  rw [show (41 : Nat) = 3 + 38 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_7]
  rw [show (38 : Nat) = 3 + 35 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_8]
  rw [show (35 : Nat) = 3 + 32 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_9]
  rw [show (32 : Nat) = 3 + 29 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_10]
  rw [show (29 : Nat) = 3 + 26 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_11]
  rw [show (26 : Nat) = 3 + 23 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_12]
  rw [show (23 : Nat) = 3 + 20 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_13]
  rw [show (20 : Nat) = 3 + 17 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_14]
  rw [show (17 : Nat) = 3 + 14 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_15]
  rw [show (14 : Nat) = 3 + 11 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_16]
  rw [show (11 : Nat) = 3 + 8 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_17]
  rw [show (8 : Nat) = 3 + 5 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_18]
  rw [show (5 : Nat) = 3 + 2 from rfl, Track2Weak.SegmentGlue.walkAdd, block0_19]
  exact block0_20

theorem segResult0 : rkm128kRunOneSeg 1024 2 512 seg0 1 512 1 v0b0 =
      (1, 512, 14385365, out0) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg0) (lPrev := 1) (dCur := 512)
    (accPad := 1) (vec := v0b0) (d := 512) (bCapCeil := 28817) (hb := hb0)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg0 512
    (rkm128kSubstepLoop 62 512 28817 28 hb0 v0b0 3) = _
  rw [run0]
  decide +kernel

end
end Track2Weak.Cert
