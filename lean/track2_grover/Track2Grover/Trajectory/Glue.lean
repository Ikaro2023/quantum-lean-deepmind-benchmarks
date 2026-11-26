module
public import Track2Grover.FindAllData

namespace Track2Grover.FindAllCell
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

theorem joinWalk {a b d cap deg p q : Nat} {hb v w : List Int} {result : List Int × Nat}
    (left : rkm128kSubstepLoop a d cap deg hb v p = (w, q))
    (right : rkm128kSubstepLoop b d cap deg hb w q = result) :
    rkm128kSubstepLoop (a + b) d cap deg hb v p = result := by
  rw [walkAdd, left]
  exact right

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

theorem runCons (s : Rkm128kSeg) (rest : List Rkm128kSeg) (l d p : Nat) (v : List Int)
    (h : Bool.or (primNatBlt l 1) (Nat.beq p 0) = false) :
    rkm128kRunSegs 1024 2 512 (s :: rest) l d p v =
      let st := rkm128kRunOneSeg 1024 2 512 s l d p v
      rkm128kRunSegs 1024 2 512 rest st.1 st.2.1 st.2.2.1 st.2.2.2 := by
  rw [rkm128kRunSegs]
  simp only [h, Bool.cond_false]
  cases rkm128kRunOneSeg 1024 2 512 s l d p v with
  | mk l dp =>
    obtain ⟨d, p, v⟩ := dp
    simp only [forceNat, forceList]

theorem foldStep {seg : Rkm128kSeg} {l d p l' d' p' : Nat} {v v' : List Int}
    (rest : List Rkm128kSeg)
    (segDone : rkm128kRunOneSeg 1024 2 512 seg l d p v = (l', d', p', v'))
    (guard : Bool.or (primNatBlt l 1) (Nat.beq p 0) = false) :
    rkm128kRunSegs 1024 2 512 (seg :: rest) l d p v =
      rkm128kRunSegs 1024 2 512 rest l' d' p' v' := by
  rw [runCons seg rest l d p v guard, segDone]

theorem rowFromRun {segs : List Rkm128kSeg} {st : Nat × Nat × Nat × List Int} {row : List Nat}
    (hg : Bool.or (Nat.beq (rkm128kSegListLen segs) 0)
      (Bool.or (primNatBlt 128 (rkm128kSegListLen segs))
        (Bool.or (primNatBlt 512 2) (primNatBlt 1024 512))) = false)
    (hrun : rkm128kRunSegs 1024 2 512 segs 1 0 1 [Int.ofNat wdScale] = st)
    (hfinal : rkm128kFinalizeState st = row) :
    rkm128kEvalRowLo12 1024 2 512 segs = row := by
  simp only [rkm128kEvalRowLo12, hg, Bool.cond_false, hrun, hfinal]

end
end Track2Grover.FindAllCell
