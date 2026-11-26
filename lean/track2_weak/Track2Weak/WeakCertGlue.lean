module
public import Track2Grover.FindAllEvaluator

namespace Track2Weak.SegmentGlue
open QuantumComputation.Specs.DickeSol
@[expose] public section

private theorem forceNat {α : Type} (x : Nat) (k : Nat → α) :
    HighDForce.withForcedNat x k = k x := by
  simp [HighDForce.withForcedNat, Nat.one_add]

private theorem forceList {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by cases xs <;> rfl

theorem walkAdd (k1 k2 d bCapCeil degP : Nat) (hb vec : List Int) (accPad : Nat) :
    rkm128kSubstepLoop (k1 + k2) d bCapCeil degP hb vec accPad =
      let st := rkm128kSubstepLoop k1 d bCapCeil degP hb vec accPad
      rkm128kSubstepLoop k2 d bCapCeil degP hb st.1 st.2 := by
  induction k1 generalizing vec accPad with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [rkm128kSubstepLoop]
    cases rkm128kSubstep d bCapCeil degP hb vec accPad with
    | mk v p =>
      dsimp only
      simp only [forceList, forceNat]
      exact ih v p

/-- Segment-level guard checks with the long orbital iteration factored out. -/
def parametersRejected (s : Rkm128kSeg) (lPrev d : Nat) : Bool :=
  let mEff := Nat.mul s.lS 1024
  Bool.or (primNatBlt s.lS lPrev)
    (Bool.or (primNatBlt 2 s.lS)
    (Bool.or (primNatBlt mEff 1)
    (Bool.or (primNatBlt 8192 mEff)
    (Bool.or (primNatBlt d 1)
    (Bool.or (Nat.beq s.tau9 0)
    (Bool.or (primNatBlt 4000000000 s.tau9)
    (Bool.or (Nat.beq s.nSub 0)
    (Bool.or (primNatBlt 16384 s.nSub)
    (Bool.or (Nat.beq s.degP 0)
    (Bool.or (primNatBlt 64 s.degP)
      (primNatBlt (Nat.add d 1) (rkmBoolListLen s.mask))))))))))))

def postWalk (s : Rkm128kSeg) (d : Nat) (v : List Int × Nat) :
    Nat × Nat × Nat × List Int :=
  match v with
  | (vec, pad) =>
    cond (Bool.or (Nat.beq pad 0) (primNatBlt 100000000000000 pad))
      (0, 0, 0, []) (s.lS, d, pad, rkmApplyMaskBits s.mask vec)

theorem runOne_normal {seg : Rkm128kSeg} {lPrev dCur accPad d bCapCeil : Nat} {hb vec : List Int}
    (h0 : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) = false)
    (hd : highdNatMin (Nat.mul seg.lS 1024) 512 = d)
    (h1 : parametersRejected seg lPrev d = false)
    (h2 : Bool.or (primNatBlt (Nat.div (Nat.mul seg.tau9 1000000) seg.nSub) 1)
        (Bool.not (altCheckHbTight (Nat.mul seg.lS 1024) 512 0 d)) = false)
    (hc : rkm128kCeilDiv15 (Nat.mul 2 (altMaxBHiFrom (Nat.mul seg.lS 1024) 512 0 d)) = bCapCeil)
    (hh : altBuildHbFrom (Nat.mul seg.lS 1024) 512
        (Nat.div (Nat.mul seg.tau9 1000000) seg.nSub) 0 d = hb) :
    rkm128kRunOneSeg 1024 2 512 seg lPrev dCur accPad vec =
      postWalk seg d (rkm128kSubstepLoop seg.nSub d bCapCeil seg.degP hb vec (Nat.add accPad 2)) := by
  unfold parametersRejected at h1
  simp only [rkm128kRunOneSeg, forceNat, forceList, h0, hd, h1, h2, hc, hh, Bool.cond_false]
  cases rkm128kSubstepLoop seg.nSub d bCapCeil seg.degP hb vec (Nat.add accPad 2) with
  | mk v p =>
    simp only [postWalk]

end
end Track2Weak.SegmentGlue
