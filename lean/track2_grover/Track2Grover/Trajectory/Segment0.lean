module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block0_0
public import Track2Grover.Trajectory.Block0_1
public import Track2Grover.Trajectory.Block0_2
public import Track2Grover.Trajectory.Block0_3
public import Track2Grover.Trajectory.Block0_4
public import Track2Grover.Trajectory.Block0_5
public import Track2Grover.Trajectory.Block0_6
public import Track2Grover.Trajectory.Block0_7
public import Track2Grover.Trajectory.Block0_8
public import Track2Grover.Trajectory.Block0_9
public import Track2Grover.Trajectory.Block0_10
public import Track2Grover.Trajectory.Block0_11

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg0Walk : rkm128kSubstepLoop 185 512 28817 28 seg0H seg0V0 3 = (seg0V185, 33707228) := by
  rw [show (185 : Nat) = 4 + 181 from rfl, walkAdd, seg0Block0]
  rw [show (181 : Nat) = 4 + 177 from rfl, walkAdd, seg0Block4]
  rw [show (177 : Nat) = 4 + 173 from rfl, walkAdd, seg0Block8]
  rw [show (173 : Nat) = 4 + 169 from rfl, walkAdd, seg0Block12]
  rw [show (169 : Nat) = 4 + 165 from rfl, walkAdd, seg0Block16]
  rw [show (165 : Nat) = 4 + 161 from rfl, walkAdd, seg0Block20]
  rw [show (161 : Nat) = 4 + 157 from rfl, walkAdd, seg0Block24]
  rw [show (157 : Nat) = 4 + 153 from rfl, walkAdd, seg0Block28]
  rw [show (153 : Nat) = 4 + 149 from rfl, walkAdd, seg0Block32]
  rw [show (149 : Nat) = 4 + 145 from rfl, walkAdd, seg0Block36]
  rw [show (145 : Nat) = 4 + 141 from rfl, walkAdd, seg0Block40]
  rw [show (141 : Nat) = 4 + 137 from rfl, walkAdd, seg0Block44]
  rw [show (137 : Nat) = 4 + 133 from rfl, walkAdd, seg0Block48]
  rw [show (133 : Nat) = 4 + 129 from rfl, walkAdd, seg0Block52]
  rw [show (129 : Nat) = 4 + 125 from rfl, walkAdd, seg0Block56]
  rw [show (125 : Nat) = 4 + 121 from rfl, walkAdd, seg0Block60]
  rw [show (121 : Nat) = 4 + 117 from rfl, walkAdd, seg0Block64]
  rw [show (117 : Nat) = 4 + 113 from rfl, walkAdd, seg0Block68]
  rw [show (113 : Nat) = 4 + 109 from rfl, walkAdd, seg0Block72]
  rw [show (109 : Nat) = 4 + 105 from rfl, walkAdd, seg0Block76]
  rw [show (105 : Nat) = 4 + 101 from rfl, walkAdd, seg0Block80]
  rw [show (101 : Nat) = 4 + 97 from rfl, walkAdd, seg0Block84]
  rw [show (97 : Nat) = 4 + 93 from rfl, walkAdd, seg0Block88]
  rw [show (93 : Nat) = 4 + 89 from rfl, walkAdd, seg0Block92]
  rw [show (89 : Nat) = 4 + 85 from rfl, walkAdd, seg0Block96]
  rw [show (85 : Nat) = 4 + 81 from rfl, walkAdd, seg0Block100]
  rw [show (81 : Nat) = 4 + 77 from rfl, walkAdd, seg0Block104]
  rw [show (77 : Nat) = 4 + 73 from rfl, walkAdd, seg0Block108]
  rw [show (73 : Nat) = 4 + 69 from rfl, walkAdd, seg0Block112]
  rw [show (69 : Nat) = 4 + 65 from rfl, walkAdd, seg0Block116]
  rw [show (65 : Nat) = 4 + 61 from rfl, walkAdd, seg0Block120]
  rw [show (61 : Nat) = 4 + 57 from rfl, walkAdd, seg0Block124]
  rw [show (57 : Nat) = 4 + 53 from rfl, walkAdd, seg0Block128]
  rw [show (53 : Nat) = 4 + 49 from rfl, walkAdd, seg0Block132]
  rw [show (49 : Nat) = 4 + 45 from rfl, walkAdd, seg0Block136]
  rw [show (45 : Nat) = 4 + 41 from rfl, walkAdd, seg0Block140]
  rw [show (41 : Nat) = 4 + 37 from rfl, walkAdd, seg0Block144]
  rw [show (37 : Nat) = 4 + 33 from rfl, walkAdd, seg0Block148]
  rw [show (33 : Nat) = 4 + 29 from rfl, walkAdd, seg0Block152]
  rw [show (29 : Nat) = 4 + 25 from rfl, walkAdd, seg0Block156]
  rw [show (25 : Nat) = 4 + 21 from rfl, walkAdd, seg0Block160]
  rw [show (21 : Nat) = 4 + 17 from rfl, walkAdd, seg0Block164]
  rw [show (17 : Nat) = 4 + 13 from rfl, walkAdd, seg0Block168]
  rw [show (13 : Nat) = 4 + 9 from rfl, walkAdd, seg0Block172]
  rw [show (9 : Nat) = 4 + 5 from rfl, walkAdd, seg0Block176]
  rw [show (5 : Nat) = 4 + 1 from rfl, walkAdd, seg0Block180]
  exact seg0Block184

theorem seg0Result : rkm128kRunOneSeg 1024 2 512 segment0 1 0 1 seg0V0 =
    (1, 512, 33707228, seg0Next) := by
  rw [runOne_normal (seg := segment0) (lPrev := 1) (dCur := 0) (accPad := 1)
    (vec := seg0V0) (d := 512) (bCapCeil := 28817) (hb := seg0H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment0 512 (rkm128kSubstepLoop 185 512 28817 28 seg0H seg0V0 3) = _
  rw [seg0Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
