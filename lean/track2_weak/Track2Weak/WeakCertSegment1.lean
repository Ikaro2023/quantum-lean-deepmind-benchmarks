module
public import Track2Weak.WeakCertGlue
public import Track2Weak.WeakCertBlocks1_0
public import Track2Weak.WeakCertBlocks1_1
public import Track2Weak.WeakCertBlocks1_2
public import Track2Weak.WeakCertBlocks1_3
public import Track2Weak.WeakCertBlocks1_4
public import Track2Weak.WeakCertBlocks1_5
public import Track2Weak.WeakCertBlocks1_6
public import Track2Weak.WeakCertBlocks1_7

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem run1 : rkm128kSubstepLoop 67 512 28817 28 hb1 v1b0 14385367 = (v1b67, 33577968) := by
  rw [show (67 : Nat) = 3 + 64 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_0]
  rw [show (64 : Nat) = 3 + 61 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_1]
  rw [show (61 : Nat) = 3 + 58 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_2]
  rw [show (58 : Nat) = 3 + 55 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_3]
  rw [show (55 : Nat) = 3 + 52 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_4]
  rw [show (52 : Nat) = 3 + 49 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_5]
  rw [show (49 : Nat) = 3 + 46 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_6]
  rw [show (46 : Nat) = 3 + 43 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_7]
  rw [show (43 : Nat) = 3 + 40 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_8]
  rw [show (40 : Nat) = 3 + 37 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_9]
  rw [show (37 : Nat) = 3 + 34 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_10]
  rw [show (34 : Nat) = 3 + 31 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_11]
  rw [show (31 : Nat) = 3 + 28 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_12]
  rw [show (28 : Nat) = 3 + 25 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_13]
  rw [show (25 : Nat) = 3 + 22 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_14]
  rw [show (22 : Nat) = 3 + 19 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_15]
  rw [show (19 : Nat) = 3 + 16 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_16]
  rw [show (16 : Nat) = 3 + 13 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_17]
  rw [show (13 : Nat) = 3 + 10 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_18]
  rw [show (10 : Nat) = 3 + 7 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_19]
  rw [show (7 : Nat) = 3 + 4 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_20]
  rw [show (4 : Nat) = 3 + 1 from rfl, Track2Weak.SegmentGlue.walkAdd, block1_21]
  exact block1_22

theorem segResult1 : rkm128kRunOneSeg 1024 2 512 seg1 1 512 14385365 v1b0 =
      (1, 512, 33577968, out1) := by
  rw [Track2Weak.SegmentGlue.runOne_normal (seg := seg1) (lPrev := 1) (dCur := 512)
    (accPad := 14385365) (vec := v1b0) (d := 512) (bCapCeil := 28817) (hb := hb1)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change Track2Weak.SegmentGlue.postWalk seg1 512
    (rkm128kSubstepLoop 67 512 28817 28 hb1 v1b0 14385367) = _
  rw [run1]
  decide +kernel

end
end Track2Weak.Cert
