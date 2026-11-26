module
public import Track2Grover.Trajectory.Segment0
public import Track2Grover.Trajectory.Segment1
public import Track2Grover.Trajectory.Segment2
public import Track2Grover.Trajectory.Segment3
public import Track2Grover.Trajectory.Segment4
public import Track2Grover.Trajectory.Segment5
public import Track2Grover.Trajectory.Segment6
public import Track2Grover.Trajectory.Segment7
public import Track2Grover.Trajectory.Segment8
public import Track2Grover.Trajectory.Segment9
public import Track2Grover.Trajectory.Segment10
public import Track2Grover.Trajectory.Segment11
public import Track2Grover.Trajectory.Segment12
public import Track2Grover.Trajectory.Segment13
public import Track2Grover.Trajectory.Segment14
public import Track2Grover.Trajectory.Segment15
public import Track2Grover.Trajectory.Segment16
public import Track2Grover.Trajectory.Segment17
public import Track2Grover.Trajectory.Segment18
public import Track2Grover.Trajectory.Segment19
public import Track2Grover.Trajectory.Segment20
public import Track2Grover.Trajectory.Segment21
public import Track2Grover.Trajectory.Segment22
public import Track2Grover.Trajectory.Segment23

namespace Track2Grover.FindAllCell
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 25000
set_option maxHeartbeats 0
theorem runChecked : rkm128kRunSegs 1024 2 512 schedule 1 0 1 [Int.ofNat wdScale] =
    (1, 512, 72704159, seg23Next) := by
  calc
    rkm128kRunSegs 1024 2 512 schedule 1 0 1 [Int.ofNat wdScale] = rkm128kRunSegs 1024 2 512 [segment1, segment2, segment3, segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 33707228 seg0Next :=
      foldStep [segment1, segment2, segment3, segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg0Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment2, segment3, segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 69498377 seg1Next :=
      foldStep [segment2, segment3, segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg1Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment3, segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 69683483 seg2Next :=
      foldStep [segment3, segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg2Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 69777732 seg3Next :=
      foldStep [segment4, segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg3Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 69962174 seg4Next :=
      foldStep [segment5, segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg4Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70140071 seg5Next :=
      foldStep [segment6, segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg5Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70220755 seg6Next :=
      foldStep [segment7, segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg6Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70393912 seg7Next :=
      foldStep [segment8, segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg7Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70471892 seg8Next :=
      foldStep [segment9, segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg8Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70636590 seg9Next :=
      foldStep [segment10, segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg9Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70713610 seg10Next :=
      foldStep [segment11, segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg10Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70867377 seg11Next :=
      foldStep [segment12, segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg11Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 70946041 seg12Next :=
      foldStep [segment13, segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg12Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 71020184 seg13Next :=
      foldStep [segment14, segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg13Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 71172178 seg14Next :=
      foldStep [segment15, segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg14Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 71237660 seg15Next :=
      foldStep [segment16, segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg15Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment17, segment18, segment19, segment20, segment21, segment22, segment23] 1 512 71306386 seg16Next :=
      foldStep [segment17, segment18, segment19, segment20, segment21, segment22, segment23] seg16Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment18, segment19, segment20, segment21, segment22, segment23] 1 512 71581301 seg17Next :=
      foldStep [segment18, segment19, segment20, segment21, segment22, segment23] seg17Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment19, segment20, segment21, segment22, segment23] 1 512 71641175 seg18Next :=
      foldStep [segment19, segment20, segment21, segment22, segment23] seg18Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment20, segment21, segment22, segment23] 1 512 71891206 seg19Next :=
      foldStep [segment20, segment21, segment22, segment23] seg19Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment21, segment22, segment23] 1 512 72172538 seg20Next :=
      foldStep [segment21, segment22, segment23] seg20Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment22, segment23] 1 512 72220568 seg21Next :=
      foldStep [segment22, segment23] seg21Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [segment23] 1 512 72507248 seg22Next :=
      foldStep [segment23] seg22Result (by decide +kernel)
    _ = rkm128kRunSegs 1024 2 512 [] 1 512 72704159 seg23Next :=
      foldStep [] seg23Result (by decide +kernel)
    _ = (1, 512, 72704159, seg23Next) := rfl

theorem rowChecked : rkm128kEvalRowLo12 1024 2 512 schedule = hitRow :=
  rowFromRun (by decide +kernel) runChecked (by decide +kernel)

#print axioms rowChecked
end
end Track2Grover.FindAllCell
