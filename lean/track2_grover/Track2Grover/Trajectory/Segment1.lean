module
public import Track2Grover.Trajectory.Glue
public import Track2Grover.Trajectory.Block1_0
public import Track2Grover.Trajectory.Block1_1
public import Track2Grover.Trajectory.Block1_2
public import Track2Grover.Trajectory.Block1_3
public import Track2Grover.Trajectory.Block1_4
public import Track2Grover.Trajectory.Block1_5
public import Track2Grover.Trajectory.Block1_6
public import Track2Grover.Trajectory.Block1_7
public import Track2Grover.Trajectory.Block1_8
public import Track2Grover.Trajectory.Block1_9
public import Track2Grover.Trajectory.Block1_10
public import Track2Grover.Trajectory.Block1_11
public import Track2Grover.Trajectory.Block1_12

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem seg1Walk : rkm128kSubstepLoop 199 512 28817 28 seg1H seg1V0 33707230 = (seg1V199, 69498377) := by
  rw [show (199 : Nat) = 4 + 195 from rfl, walkAdd, seg1Block0]
  rw [show (195 : Nat) = 4 + 191 from rfl, walkAdd, seg1Block4]
  rw [show (191 : Nat) = 4 + 187 from rfl, walkAdd, seg1Block8]
  rw [show (187 : Nat) = 4 + 183 from rfl, walkAdd, seg1Block12]
  rw [show (183 : Nat) = 4 + 179 from rfl, walkAdd, seg1Block16]
  rw [show (179 : Nat) = 4 + 175 from rfl, walkAdd, seg1Block20]
  rw [show (175 : Nat) = 4 + 171 from rfl, walkAdd, seg1Block24]
  rw [show (171 : Nat) = 4 + 167 from rfl, walkAdd, seg1Block28]
  rw [show (167 : Nat) = 4 + 163 from rfl, walkAdd, seg1Block32]
  rw [show (163 : Nat) = 4 + 159 from rfl, walkAdd, seg1Block36]
  rw [show (159 : Nat) = 4 + 155 from rfl, walkAdd, seg1Block40]
  rw [show (155 : Nat) = 4 + 151 from rfl, walkAdd, seg1Block44]
  rw [show (151 : Nat) = 4 + 147 from rfl, walkAdd, seg1Block48]
  rw [show (147 : Nat) = 4 + 143 from rfl, walkAdd, seg1Block52]
  rw [show (143 : Nat) = 4 + 139 from rfl, walkAdd, seg1Block56]
  rw [show (139 : Nat) = 4 + 135 from rfl, walkAdd, seg1Block60]
  rw [show (135 : Nat) = 4 + 131 from rfl, walkAdd, seg1Block64]
  rw [show (131 : Nat) = 4 + 127 from rfl, walkAdd, seg1Block68]
  rw [show (127 : Nat) = 4 + 123 from rfl, walkAdd, seg1Block72]
  rw [show (123 : Nat) = 4 + 119 from rfl, walkAdd, seg1Block76]
  rw [show (119 : Nat) = 4 + 115 from rfl, walkAdd, seg1Block80]
  rw [show (115 : Nat) = 4 + 111 from rfl, walkAdd, seg1Block84]
  rw [show (111 : Nat) = 4 + 107 from rfl, walkAdd, seg1Block88]
  rw [show (107 : Nat) = 4 + 103 from rfl, walkAdd, seg1Block92]
  rw [show (103 : Nat) = 4 + 99 from rfl, walkAdd, seg1Block96]
  rw [show (99 : Nat) = 4 + 95 from rfl, walkAdd, seg1Block100]
  rw [show (95 : Nat) = 4 + 91 from rfl, walkAdd, seg1Block104]
  rw [show (91 : Nat) = 4 + 87 from rfl, walkAdd, seg1Block108]
  rw [show (87 : Nat) = 4 + 83 from rfl, walkAdd, seg1Block112]
  rw [show (83 : Nat) = 4 + 79 from rfl, walkAdd, seg1Block116]
  rw [show (79 : Nat) = 4 + 75 from rfl, walkAdd, seg1Block120]
  rw [show (75 : Nat) = 4 + 71 from rfl, walkAdd, seg1Block124]
  rw [show (71 : Nat) = 4 + 67 from rfl, walkAdd, seg1Block128]
  rw [show (67 : Nat) = 4 + 63 from rfl, walkAdd, seg1Block132]
  rw [show (63 : Nat) = 4 + 59 from rfl, walkAdd, seg1Block136]
  rw [show (59 : Nat) = 4 + 55 from rfl, walkAdd, seg1Block140]
  rw [show (55 : Nat) = 4 + 51 from rfl, walkAdd, seg1Block144]
  rw [show (51 : Nat) = 4 + 47 from rfl, walkAdd, seg1Block148]
  rw [show (47 : Nat) = 4 + 43 from rfl, walkAdd, seg1Block152]
  rw [show (43 : Nat) = 4 + 39 from rfl, walkAdd, seg1Block156]
  rw [show (39 : Nat) = 4 + 35 from rfl, walkAdd, seg1Block160]
  rw [show (35 : Nat) = 4 + 31 from rfl, walkAdd, seg1Block164]
  rw [show (31 : Nat) = 4 + 27 from rfl, walkAdd, seg1Block168]
  rw [show (27 : Nat) = 4 + 23 from rfl, walkAdd, seg1Block172]
  rw [show (23 : Nat) = 4 + 19 from rfl, walkAdd, seg1Block176]
  rw [show (19 : Nat) = 4 + 15 from rfl, walkAdd, seg1Block180]
  rw [show (15 : Nat) = 4 + 11 from rfl, walkAdd, seg1Block184]
  rw [show (11 : Nat) = 4 + 7 from rfl, walkAdd, seg1Block188]
  rw [show (7 : Nat) = 4 + 3 from rfl, walkAdd, seg1Block192]
  exact seg1Block196

theorem seg1Result : rkm128kRunOneSeg 1024 2 512 segment1 1 512 33707228 seg1V0 =
    (1, 512, 69498377, seg1Next) := by
  rw [runOne_normal (seg := segment1) (lPrev := 1) (dCur := 512) (accPad := 33707228)
    (vec := seg1V0) (d := 512) (bCapCeil := 28817) (hb := seg1H)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl]
  change postWalk segment1 512 (rkm128kSubstepLoop 199 512 28817 28 seg1H seg1V0 33707230) = _
  rw [seg1Walk]
  decide +kernel
end
end Track2Grover.FindAllCell
