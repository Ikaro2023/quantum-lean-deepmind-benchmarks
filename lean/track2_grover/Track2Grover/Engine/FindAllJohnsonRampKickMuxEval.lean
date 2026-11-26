/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module
public import Track2Grover.FindAllEvaluator
public import Track2Grover.Engine.JohnsonBlockMuxSparseFastT16
public import Track2Grover.Engine.FindAllJohnsonRampKickMuxKernelB
public import Track2Grover.Engine.FindAllJohnsonMuxRefocusLift
public import Track2Grover.Engine.FindAllJohnsonRampLift
/-!
# Alt-Mux & Sparse Evaluator (`FindAllJohnsonRampKickMuxEval`)

Zero-`decide` table checker and quantum-step lift for alternating-mux and sparse walks.
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
open Real
open scoped Matrix NNRat NNReal ENNReal
/-- Primitive `0.. d - 1` `Nat` sum avoiding Mathlib `Finset.sum` in kernel callcones. -/
def bmuxSumRange : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | d + 1, f => bmuxSumRange d f + f d
/-- Structural helper for `checkAltMuxLoop` (`vRem` first after `:`, `0` `WellFounded.fix`). -/
def checkAltMuxLoopAux (m lTableMax : ℕ) :
    List ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], _, _, lRem, tauRem, nsubRem =>
    match lRem with
    | [] =>
      match tauRem with
      | [] =>
        match nsubRem with
        | [] => true
        | _ :: _ => false
      | _ :: _ => false
    | _ :: _ => false
  | vR :: vRest, r, vHist, lRem, tauRem, nsubRem =>
    match lRem with
    | [] => false
    | lR :: lRest =>
      match tauRem with
      | [] => false
      | tau9 :: tauRest =>
        match nsubRem with
        | [] => false
        | nSub :: nsubRest =>
          match vHist with
          | [] => false
          | vPrev :: _ =>
            cond
              (primNatBlt vR vPrev)
              false
              (
              let stepOk :=
                cond
                  (Nat.beq tau9 0)
                  (checkEigStep m r vR vPrev)
                  (
                  cond
                    (Bool.or (primNatBlt lR 1) (primNatBlt lTableMax lR))
                    false
                    (
                    let mEffRaw := Nat.mul lR m
                    AltForce.withForcedNat mEffRaw fun mEff =>
                      let dRaw := cond (Nat.ble mEff r) mEff r
                      AltForce.withForcedNat dRaw fun d =>
                        let rowRaw := altEvalRowLo12 mEff r tau9 nSub
                        AltForce.withForcedList rowRaw fun rowLo12 =>
                          cond
                            (Bool.or (Bool.not (Nat.beq (altListLen rowLo12) d))
                              (Bool.or (Nat.beq (altSumNat rowLo12) 0)
                                (primNatBlt (altListLen vHist) d)) )
                            false
                            (
                            let drift27 := altDriftSum27 vR rowLo12 vHist
                            primNatBlt (Nat.mul lR (Nat.mul tau9 1000000000000000000)) drift27)))
              cond
                stepOk
                (
                checkAltMuxLoopAux m lTableMax vRest (Nat.add r 1) (vR :: vHist)
                  lRest tauRest nsubRest)
                false)
/-- Sub-band Bellman drift checker for stage-adaptive `L_r`-block multiplexed
  `D_{\text{alt}}`
  walks over `r, r + 1,...` with reverse potential history `vHist`. -/
def checkAltMuxLoop (m lTableMax r : ℕ) (vHist vRem lRem tauRem nsubRem : List ℕ) : Bool :=
  checkAltMuxLoopAux m lTableMax vRem r vHist lRem tauRem nsubRem
/-- Header and `r = 0, 1` base-case checker for a multiplexed `D_{\text{alt}}` table. -/
def checkAltMuxHeader12 (m kMax lTableMax : ℕ)
    (vPot lRows tau9Rows nsubRows : List ℕ) : Bool :=
  cond
    (Bool.or (primNatBlt m 1)
    (Bool.or (primNatBlt lTableMax 1)
    (Bool.or (primNatBlt 8192 (Nat.mul lTableMax m))
    (Bool.or (primNatBlt kMax 2) (primNatBlt 1024 kMax)))) )
    false
    (
    cond
      (Bool.or (Bool.not (Nat.beq (altListLen vPot) (Nat.add kMax 1)))
      (Bool.or (Bool.not (Nat.beq (altListLen lRows) (Nat.sub kMax 1)))
      (Bool.or (Bool.not (Nat.beq (altListLen tau9Rows) (Nat.sub kMax 1)))
        (Bool.not (Nat.beq (altListLen nsubRows) (Nat.sub kMax 1))))) )
      false
      (
      match vPot with
      | v0 :: v1 :: _ =>
        cond (Bool.not (Nat.beq v0 0)) false (checkEigStep m 1 v1 v0)
      | _ => false))
/-- Complete `1`-stage `L_r`-multiplexed `D_{\text{alt}}` Bellman certificate table checker
  for `r = 0.. kMax`. -/
def checkAltMuxTable12 (m kMax lTableMax : ℕ)
    (vPot lRows tau9Rows nsubRows : List ℕ) : Bool :=
  cond
    (checkAltMuxHeader12 m kMax lTableMax vPot lRows tau9Rows nsubRows)
    (
    match vPot with
    | v0 :: v1 :: vRest =>
      checkAltMuxLoop m lTableMax 2 [v1, v0] vRest lRows tau9Rows nsubRows
    | _ => false)
    false
/-- Prefix loop verifying `1 ≤ lRows[r - 2] ≤ lMaxCell` across the first `cnt` walk rows. -/
def checkAltMuxPrefixLoop : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | cnt + 1, lMaxCell, lRem =>
    match lRem with
    | [] => false
    | lR :: lRest =>
      cond
        (Bool.or (primNatBlt lR 1) (primNatBlt lMaxCell lR))
        false
        (checkAltMuxPrefixLoop cnt lMaxCell lRest)
/-- Verifies `1 ≤ lMaxCell ≤ lTableMax` and `1 ≤ lRows[r - 2] ≤ lMaxCell` for `2 ≤ r ≤ k`. -/
def checkAltMuxPrefixLMax (k lTableMax lMaxCell : ℕ) (lRows : List ℕ) : Bool :=
  cond
    (Bool.or (primNatBlt k 2)
    (Bool.or (primNatBlt lMaxCell 1)
      (Bool.or (primNatBlt lTableMax lMaxCell)
        (primNatBlt (altListLen lRows) (Nat.sub k 1)))) )
    false
    (checkAltMuxPrefixLoop (Nat.sub k 1) lMaxCell lRows)
/-! ## Section 1: Sawtooth `vCap` Sparse Multiplexed Table Checkers -/
/-- Pre-certified active walk anchor `(rAct, lR, tau9, nSub, rowLo12)` for a sparse mux
  table. -/
structure MuxSparseAnchor where
  rAct : ℕ
  lR : ℕ
  tau9 : ℕ
  nSub : ℕ
  rowLo12 : List ℕ
/-- Looks up the first anchor matching `r` in `anchors`. -/
def muxFindAnchor (r : ℕ) : List MuxSparseAnchor → Option MuxSparseAnchor
  | [] => none
  | a :: rest => if a.rAct = r then some a else muxFindAnchor r rest
/-- Running prefix maximum `max_{0 ≤ j ≤ r} vPot[j]`. -/
def muxRunningCap (vPot : List ℕ) : ℕ → ℕ
  | 0 => vPot.getD 0 0
  | r + 1 => max (muxRunningCap vPot r) (vPot.getD (r + 1) 0)

/-- Checks the running-cap `vCapR` sparse Bellman drift inequality on one active walk row. -/
def muxCheckSparseDrift (m lTableMax r lR tau9 nSub vR vCapR : ℕ)
    (rowLo12 vHist : List ℕ) : Bool :=
  cond (Bool.or (primNatBlt lR 1) (Bool.or (primNatBlt lTableMax lR)
        (Bool.or (Nat.beq tau9 0) (Nat.beq nSub 0))))
    false
    (
      let d := highdNatMin (Nat.mul lR m) r
      let tot12 := altSumNat rowLo12
      cond (Bool.or (Bool.not (Nat.beq (altListLen rowLo12) d)) (Bool.or (Nat.beq tot12 0)
            (Bool.or (primNatBlt 1000000000000 tot12) (primNatBlt (altListLen vHist) d))))
        false
        (
          let hit27 := muxHitValSum27 rowLo12 vHist
          let def12 := Nat.sub 1000000000000 tot12
          let lhs27 := Nat.add (Nat.mul (Nat.mul lR tau9) 1000000000000000000)
            (Nat.add hit27 (Nat.mul def12 vCapR))
          primNatBlt lhs27 (Nat.mul 1000000000000 vR)))
/-- Structural `T_8` prefix loop (`vRem` first after `:`) updating running cap `vCap`. -/
def checkMuxSparsePrefAux (m lTableMax : ℕ) :
    List ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], _, _, _, lRem, tauRem, nsubRem =>
    match lRem, tauRem, nsubRem with
    | [], [], [] => true
    | _, _, _ => false
  | vR :: vRest, r, vCapPrev, vHist, lRem, tauRem, nsubRem =>
    match lRem, tauRem, nsubRem, vHist with
    | lR :: lRest, tau9 :: tauRest, nSub :: nsubRest, vPrev :: _ =>
      let vCapR := cond (primNatBlt vCapPrev vR) vR vCapPrev
      HighDForce.withForcedNat vCapR fun vCapNext =>
        let stepOk :=
          cond (Nat.beq tau9 0) (checkEigStep m r vR vPrev) (
              let mEffRaw := Nat.mul lR m
              AltForce.withForcedNat mEffRaw fun mEff =>
                let rowRaw := altEvalRowLo12 mEff r tau9 nSub
                AltForce.withForcedList rowRaw fun rowLo12 =>
                  muxCheckSparseDrift m lTableMax r lR tau9 nSub vR vCapNext rowLo12 vHist)
        cond stepOk (checkMuxSparsePrefAux m lTableMax vRest (Nat.add r 1) vCapNext (vR :: vHist)
            lRest tauRest nsubRest)
          false
    | _, _, _, _ => false
/-- Checks header bounds (`1 ≤ m`, `lTableMax * m ≤ 8192`, `kMax ≤ 1024`), `r = 0, 1`, and
  the
  `T_8` prefix `r = 2.. 1 + vPref.length`. -/
def checkMuxSparsePref (m kMax lTableMax : ℕ)
    (v0 v1 : ℕ) (vPref lPref tauPref nsubPref : List ℕ) : Bool :=
  cond (Bool.or (primNatBlt m 1) (Bool.or (primNatBlt lTableMax 1)
        (Bool.or (primNatBlt 8192 (Nat.mul lTableMax m))
          (Bool.or (primNatBlt kMax (Nat.add 2 (altListLen vPref))) (primNatBlt 1024 kMax)))))
    false
    (cond (Bool.not (Nat.beq v0 0)) false (cond (checkEigStep m 1 v1 v0)
        (checkMuxSparsePrefAux m lTableMax vPref 2 v1 [v1, v0] lPref tauPref nsubPref)
        false))
/-- Structural sparse tail loop (`vRem` first after `:`) matching sorted `anchors` or
  `checkEigStep`. -/
def checkMuxSparseTailAux (m lTableMax : ℕ) : List ℕ → ℕ → ℕ → List ℕ → List MuxSparseAnchor → Bool
  | [], _, _, _, anchors =>
    match anchors with
    | [] => true
    | _ :: _ => false
  | vR :: vRest, r, vCapPrev, vHist, anchors =>
    match vHist with
    | [] => false
    | vPrev :: _ =>
      let vCapR := cond (primNatBlt vCapPrev vR) vR vCapPrev
      HighDForce.withForcedNat vCapR fun vCapNext =>
        match anchors with
        | a :: aRest =>
          cond (primNatBlt a.rAct r) false (cond (Nat.beq a.rAct r)
              (cond (muxCheckSparseDrift m lTableMax r a.lR a.tau9 a.nSub vR vCapNext
                  a.rowLo12 vHist)
                (checkMuxSparseTailAux m lTableMax vRest (Nat.add r 1) vCapNext
                  (vR :: vHist) aRest)
                false)
              (cond (checkEigStep m r vR vPrev)
                (checkMuxSparseTailAux m lTableMax vRest (Nat.add r 1) vCapNext
                  (vR :: vHist) (a :: aRest))
                false))
        | [] =>
          cond (checkEigStep m r vR vPrev)
            (checkMuxSparseTailAux m lTableMax vRest (Nat.add r 1) vCapNext (vR :: vHist) [])
            false
/-- Sub-band sparse tail checker over `r, r + 1,...` with running cap `vCapPrev` and
  `vHist`. -/
def checkMuxSparseTail (m lTableMax r vCapPrev : ℕ)
    (vHist vRem : List ℕ) (anchors : List MuxSparseAnchor) : Bool :=
  checkMuxSparseTailAux m lTableMax vRem r vCapPrev vHist anchors
/-- Every anchor in `anchors` has `rowLo12` certified by `altEvalRowHighDLo12`. -/
def MuxSparseAnchorsSound (m : ℕ) : List MuxSparseAnchor → Prop
  | [] => True
  | a :: rest =>
      altEvalRowHighDLo12 (a.lR * m) a.rAct a.tau9 a.nSub (min (a.lR * m) a.rAct) = a.rowLo12 ∧
        MuxSparseAnchorsSound m rest
/-- Checks `1 ≤ a.lR ≤ lMaxCell` for every anchor with `a.rAct ≤ k`. -/
def checkMuxAnchorLMax (k lMaxCell : ℕ) : List MuxSparseAnchor → Bool
  | [] => true
  | a :: rest =>
    let ok :=
      cond (Nat.ble a.rAct k) (Bool.not (Bool.or (primNatBlt a.lR 1) (primNatBlt lMaxCell a.lR)))
        true
    cond ok (checkMuxAnchorLMax k lMaxCell rest) false
/-- Verifies `1 ≤ lMaxCell ≤ lTableMax` and `1 ≤ l_r ≤ lMaxCell` on all walk rows `2 ≤ r ≤
  k`. -/
def checkMuxSparseCellLMax (k lTableMax lMaxCell : ℕ)
    (lPref : List ℕ) (anchors : List MuxSparseAnchor) : Bool :=
  cond (Bool.or (primNatBlt k 2) (Bool.or (primNatBlt lMaxCell 1) (primNatBlt lTableMax lMaxCell)))
    false
    (
      let prefCnt := highdNatMin (Nat.sub k 1) (altListLen lPref)
      cond (checkAltMuxPrefixLoop prefCnt lMaxCell lPref) (checkMuxAnchorLMax k lMaxCell anchors)
        false)
/-- Unpacked semantic validity of one active sparse multiplexed walk row at rung `s`. -/
def MuxSparseActiveValid (m lTableMax s : ℕ) (vPot : List ℕ)
    (lS tau9 nSub : ℕ) (row : List ℕ) : Prop :=
  let d := min (lS * m) s
  1 ≤ lS ∧ lS ≤ lTableMax ∧ 0 < tau9 ∧ 0 < nSub ∧ row.length = d ∧
    0 < altSumNat row ∧ altSumNat row ≤ 1000000000000 ∧
    (lS * tau9) * 1000000000000000000 +
        (∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (s - 1 - j) 0) +
        (1000000000000 - altSumNat row) * muxRunningCap vPot s <
      1000000000000 * vPot.getD s 0
/-- Semantic validity bundle for a full `r = 0.. kMax` sparse multiplexed walk table. -/
structure MuxSparseTableValid (m kMax lTableMax : ℕ)
    (vPot lPref tauPref nsubPref : List ℕ) (anchors : List MuxSparseAnchor) : Prop where
  hm1 : 1 ≤ m
  hlMax1 : 1 ≤ lTableMax
  hlMax_hi : lTableMax * m ≤ 8192
  hkMax_hi : kMax ≤ 1024
  hv_len : vPot.length = kMax + 1
  hl_len : lPref.length = tauPref.length
  hn_len : nsubPref.length = tauPref.length
  hpref_le : 2 + lPref.length ≤ kMax
  hv0 : vPot.getD 0 0 = 0
  heig1 : checkEigStep m 1 (vPot.getD 1 0) (vPot.getD 0 0) = true
  hpref : ∀ s : ℕ, 2 ≤ s → s < 2 + lPref.length → (tauPref.getD (s - 2) 0 = 0 →
      checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true) ∧
    (0 < tauPref.getD (s - 2) 0 →
      let lS := lPref.getD (s - 2) 0
      let tau9 := tauPref.getD (s - 2) 0
      let nSub := nsubPref.getD (s - 2) 0
      MuxSparseActiveValid m lTableMax s vPot lS tau9 nSub (altEvalRowLo12 (lS * m) s tau9 nSub))
  htail : ∀ s : ℕ, 2 + lPref.length ≤ s → s ≤ kMax →
    match muxFindAnchor s anchors with
    | none => checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
    | some a =>
        a.rAct = s ∧
        altEvalRowHighDLo12 (a.lR * m) s a.tau9 a.nSub (min (a.lR * m) s) = a.rowLo12 ∧
        MuxSparseActiveValid m lTableMax s vPot a.lR a.tau9 a.nSub a.rowLo12
/-- Boolean inequality helper avoiding toolchain-dependent `xor` names. -/
def rkmBoolXor (a b : Bool) : Bool :=
  match a, b with
  | true, false => true
  | false, true => true
  | _, _ => false
/-- Builds descending `prefixKick` indices `≤ k` realizing `mask.getD w false` under ambient
  parity `flip` on `[0.. k]`. -/
def rkmMaskKicksDown (mask : List Bool) : ℕ → Bool → List ℕ
  | 0, flip =>
    if rkmBoolXor flip (mask.getD 0 false) then [0] else []
  | k + 1, flip =>
    if rkmBoolXor flip (mask.getD (k + 1) false) then
      (k + 1) :: rkmMaskKicksDown mask k (!flip)
    else
      rkmMaskKicksDown mask k flip
/-- Single-segment `MuxSymOp` list (`K`-step `dAltSymMat` walk followed by exact
  `prefixKick`s). -/
noncomputable def rkmSegOps (n m r lS tau9 nSub : ℕ) (mask : List Bool) :
    List (MuxSymOp (2 ^ n) (lS * m)) :=
  if hm : 1 ≤ n ∧ 2 * (lS * m) < 2 ^ n then
    MuxSymOp.walk (altStepCount tau9 nSub (2 ^ n))
      (SymOrthogonal.ofSymmInvolution (dAltSymMat (2 ^ n) (lS * m))
        (dAltSymMat_transpose (2 ^ n) (lS * m))
        (dAltSymMat_mul_self_two_pow hm.1 hm.2)) ::
      (rkmMaskKicksDown mask (min (lS * m) r) false).map MuxSymOp.prefixKick
  else []
/-- Continuation segment `(lSeg, ops)` of a width-ramped + prefix-kick pass. -/
structure RkmSeg (N m : ℕ) : Type where
  lSeg : ℕ
  ops : List (MuxSymOp N (lSeg * m))
/-- Final block multiplicity of `(L₀, ops₀)` followed by `segs`. -/
def rkmEndL {N m : ℕ} : ℕ → List (RkmSeg N m) → ℕ
  | L, [] => L
  | _, seg :: rest => rkmEndL seg.lSeg rest
/-- Non-decreasing multiplicity invariant `L₀ ≤ L₁ ≤ ⋯ ≤ L_end`. -/
def rkmSegsMono {N m : ℕ} : ℕ → List (RkmSeg N m) → Prop
  | _, [] => True
  | L, seg :: rest => L ≤ seg.lSeg ∧ rkmSegsMono seg.lSeg rest
/-- Total oracle query count across `(L₀, ops₀)` and `segs`. -/
def rkmSegsQueryCount {N m : ℕ} :
    ∀ (L₀ : ℕ), List (MuxSymOp N (L₀ * m)) → List (RkmSeg N m) → ℕ
  | L₀, ops₀, [] => L₀ * muxOpsQueryCount ops₀
  | L₀, ops₀, seg :: rest =>
      L₀ * muxOpsQueryCount ops₀ + rkmSegsQueryCount seg.lSeg seg.ops rest
/-- Sequential symmetric-subspace evolution across `(L₀, ops₀)` and `segs`. -/
noncomputable def rkmEvalSegs {N m : ℕ} (R : Finset (Fin N)) :
    ∀ (L₀ : ℕ), List (MuxSymOp N (L₀ * m)) →
      ∀ (segs : List (RkmSeg N m)),
        (SymSubset N (L₀ * m) → ℝ) → (SymSubset N (rkmEndL L₀ segs * m) → ℝ)
  | _, ops₀, [], v => evalMuxSymOps R ops₀ v
  | L₀, ops₀, seg :: rest, v =>
      let v₁ := evalMuxSymOps R ops₀ v
      let v₂ : SymSubset N (seg.lSeg * m) → ℝ :=
        if h : L₀ = seg.lSeg then
          h ▸ v₁
        else
          stepUpFrom N (L₀ * m) (seg.lSeg * m) *ᵥ v₁
      rkmEvalSegs R seg.lSeg seg.ops rest v₂
/-- Builds continuation `RkmSeg` entries from parallel `(l, tau9, nSub, mask)` lists. -/
noncomputable def rkmBuildTailSegs (n m r : ℕ) :
    List ℕ → List ℕ → List ℕ → List (List Bool) → List (RkmSeg (2 ^ n) m)
  | lS :: lRest, tau9 :: tauRest, nSub :: nsubRest, mask :: maskRest =>
      ⟨lS, rkmSegOps n m r lS tau9 nSub mask⟩ ::
        rkmBuildTailSegs n m r lRest tauRest nsubRest maskRest
  | _, _, _, _ => []
/-- Weighted `10 ^ 9`-scaled oracle duration `∑_s l_s * tau9_s`. -/
def rkmWeightedTau9 : List ℕ → List ℕ → ℕ
  | lS :: lRest, tS :: tRest => Nat.add (Nat.mul lS tS) (rkmWeightedTau9 lRest tRest)
  | _, _ => 0
/-- Pre-certified multi-segment active row `(rAct, lSegs, tauSegs, nsubSegs, masks,
  rowLo12)`. -/
structure RampKickAnchor where
  rAct : ℕ
  lSegs : List ℕ
  tauSegs : List ℕ
  nsubSegs : List ℕ
  masks : List (List Bool)
  rowLo12 : List ℕ
/-- Looks up the first anchor matching `r` in `anchors`. -/
def rkmFindAnchor (r : ℕ) : List RampKickAnchor → Option RampKickAnchor
  | [] => none
  | a :: rest => if a.rAct = r then some a else rkmFindAnchor r rest


/-- Last element of a `List ℕ` with default `defVal`. -/
def rkmLastNat : ℕ → List ℕ → ℕ
  | defVal, [] => defVal
  | _, x :: xs => rkmLastNat x xs
/-- Verifies `lSegs.length = tauSegs.length`, `1 ≤ l_0 ≤... ≤ l_end ≤ lTableMax`, and
  `1 ≤ tau9_s ≤ 4000000000`. -/
def rkmCheckSegBounds (lTableMax : ℕ) : List ℕ → List ℕ → ℕ → Bool
  | [], [], _ => true
  | lS :: lRest, tS :: tRest, lPrev =>
    cond
      (
      Bool.or (primNatBlt lS 1)
      (Bool.or (primNatBlt lS lPrev)
      (Bool.or (primNatBlt lTableMax lS)
      (Bool.or (primNatBlt tS 1)
        (primNatBlt 4000000000 tS)))))
      false
      (rkmCheckSegBounds lTableMax lRest tRest lS)
  | _, _, _ => false
/-- Running-cap `vCapR` Bellman drift inequality on a multi-segment active row. -/
def rkmCheckDrift (m lTableMax r : ℕ) (lSegs tauSegs : List ℕ)
    (vR vCapR : ℕ) (rowLo12 vHist : List ℕ) : Bool :=
  let nSegs := altListLen lSegs
  cond
    (
    Bool.or (primNatBlt nSegs 1)
    (Bool.or (primNatBlt 8 nSegs)
    (Bool.or (primNatBlt vCapR vR)
      (Bool.not (rkmCheckSegBounds lTableMax lSegs tauSegs 1)))))
    false
    (
    let lEnd := rkmLastNat 0 lSegs
    let dEnd := highdNatMin (Nat.mul lEnd m) r
    let tot12 := altSumNat rowLo12
    cond
      (
      Bool.or (Bool.not (Nat.beq (altListLen rowLo12) dEnd))
      (Bool.or (primNatBlt tot12 1)
      (Bool.or (primNatBlt 1000000000000 tot12)
        (primNatBlt (altListLen vHist) dEnd))))
      false
      (
      let wTau9 := rkmWeightedTau9 lSegs tauSegs
      let hit27 := muxHitValSum27 rowLo12 vHist
      let def12 := Nat.sub 1000000000000 tot12
      let lhs27 := Nat.add (Nat.mul wTau9 1000000000000000000)
        (Nat.add hit27 (Nat.mul def12 vCapR))
      primNatBlt lhs27 (Nat.mul 1000000000000 vR)))
/-- Structural Bellman table loop (`vRem` first after `:`) matching sorted `anchors`, `r =
  2`
  cold handoff (`useColdR2`), or `checkEigStep`. -/
def rkmCheckTableAux (m lTableMax : ℕ) (useColdR2 : Bool) :
    List ℕ → ℕ → ℕ → List ℕ → List RampKickAnchor → Bool
  | [], _, _, _, anchors =>
    match anchors with
    | [] => true
    | _ :: _ => false
  | vR :: vRest, r, vCapPrev, vHist, anchors =>
    match vHist with
    | [] => false
    | vPrev :: _ =>
      let vCapR := cond (primNatBlt vCapPrev vR) vR vCapPrev
      HighDForce.withForcedNat vCapR fun vCapNext =>
        let fallbackOk :=
          cond (Bool.and (Nat.beq r 2) useColdR2)
            (rkmCheckColdR2Step m vR)
            (checkEigStep m r vR vPrev)
        match anchors with
        | a :: aRest =>
          cond (primNatBlt a.rAct r)
            false
            (
            cond (Nat.beq a.rAct r)
            (
            cond
              (
                rkmCheckDrift m lTableMax r a.lSegs a.tauSegs vR vCapNext
                a.rowLo12 vHist)
              (
              rkmCheckTableAux m lTableMax useColdR2 vRest (Nat.add r 1) vCapNext
                (vR :: vHist) aRest)
              false)
            (
            cond fallbackOk
              (
              rkmCheckTableAux m lTableMax useColdR2 vRest (Nat.add r 1) vCapNext
                (vR :: vHist) (a :: aRest))
              false))
        | [] =>
          cond fallbackOk
            (
            rkmCheckTableAux m lTableMax useColdR2 vRest (Nat.add r 1) vCapNext
              (vR :: vHist) [])
            false
/-- Full `r = 0.. kMax` Bellman table checker for `RampKickMux`. -/
def rkmCheckTable (m kMax lTableMax : ℕ) (useColdR2 : Bool)
    (vPot : List ℕ) (anchors : List RampKickAnchor) : Bool :=
  cond
    (
    Bool.or (primNatBlt m 1)
    (Bool.or (primNatBlt lTableMax 1)
    (Bool.or (primNatBlt 8192 (Nat.mul lTableMax m))
    (Bool.or (primNatBlt kMax 2)
    (Bool.or (primNatBlt 1024 kMax)
      (Bool.not (Nat.beq (altListLen vPot) (Nat.add kMax 1))))))))
    false
    (
    match vPot with
    | v0 :: v1 :: vRest =>
      cond (Bool.not (Nat.beq v0 0))
        false
        (
        cond (checkEigStep m 1 v1 v0)
        (rkmCheckTableAux m lTableMax useColdR2 vRest 2 v1 [v1, v0] anchors)
        false)
    | _ => false)
/-- Checks `1 ≤ lS ≤ lMaxCell` across `lSegs`. -/
def rkmCheckListLMax (lMaxCell : ℕ) : List ℕ → Bool
  | [] => true
  | lS :: rest =>
    cond (Bool.or (primNatBlt lS 1) (primNatBlt lMaxCell lS))
      false
      (rkmCheckListLMax lMaxCell rest)
/-- Verifies `1 ≤ lS ≤ lMaxCell` on every active anchor with `a.rAct ≤ k`. -/
def rkmCheckAnchorsLMax (k lMaxCell : ℕ) : List RampKickAnchor → Bool
  | [] => true
  | a :: rest =>
    let ok := cond (Nat.ble a.rAct k) (rkmCheckListLMax lMaxCell a.lSegs) true
    cond ok (rkmCheckAnchorsLMax k lMaxCell rest) false
/-- Every anchor in `anchors` has `rowLo12` certified by `rkmEvalT16Lo12`. -/
def RampKickAnchorsSound (m lTableMax : ℕ) : List RampKickAnchor → Prop
  | [] => True
  | a :: rest =>
      rkmEvalT16Lo12 m lTableMax a.rAct a.lSegs a.tauSegs a.nsubSegs a.masks = a.rowLo12 ∧
        RampKickAnchorsSound m lTableMax rest
/-- Unpacked semantic validity of one active multi-segment row at rung `s`. -/
def RampKickActiveValid (m lTableMax s : ℕ) (vPot : List ℕ)
    (lSegs tauSegs : List ℕ) (row : List ℕ) : Prop :=
  let lEnd := rkmLastNat 0 lSegs
  let dEnd := min (lEnd * m) s
  1 ≤ lSegs.length ∧ lSegs.length ≤ 8 ∧
    rkmCheckSegBounds lTableMax lSegs tauSegs 1 = true ∧
    row.length = dEnd ∧
    0 < altSumNat row ∧ altSumNat row ≤ 1000000000000 ∧
    rkmWeightedTau9 lSegs tauSegs * 1000000000000000000 +
        (∑ j ∈ Finset.range dEnd, row.getD j 0 * vPot.getD (s - 1 - j) 0) +
        (1000000000000 - altSumNat row) * muxRunningCap vPot s <
      1000000000000 * vPot.getD s 0
/-- Semantic validity bundle for a full `r = 0.. kMax` `RampKickMux` table. -/
structure RampKickTableValid (m kMax lTableMax : ℕ) (useColdR2 : Bool)
    (vPot : List ℕ) (anchors : List RampKickAnchor) : Prop where
  hm1 : 1 ≤ m
  hlMax1 : 1 ≤ lTableMax
  hlMax_hi : lTableMax * m ≤ 8192
  hkMax_lo : 2 ≤ kMax
  hkMax_hi : kMax ≤ 1024
  hv_len : vPot.length = kMax + 1
  hv0 : vPot.getD 0 0 = 0
  heig1 : checkEigStep m 1 (vPot.getD 1 0) (vPot.getD 0 0) = true
  hrows : ∀ s : ℕ, 2 ≤ s → s ≤ kMax →
    match rkmFindAnchor s anchors with
    | none =>
        (s = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨
          checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
    | some a =>
        a.rAct = s ∧
        rkmEvalT16Lo12 m lTableMax s a.lSegs a.tauSegs a.nsubSegs a.masks = a.rowLo12 ∧
        RampKickActiveValid m lTableMax s vPot a.lSegs a.tauSegs a.rowLo12
end
public section
open Real
open scoped Matrix NNRat NNReal ENNReal
private theorem bmuxAlt_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, bmuxAlt_nat_ble_eq_true]
private theorem bmuxAlt_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, bmuxAlt_nat_ble_eq_true]; omega
private theorem bmuxAlt_primNatBlt_eq_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  unfold primNatBlt; exact bmuxAlt_nat_ble_eq_true
private theorem bmuxAlt_primNatBlt_eq_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, bmuxAlt_primNatBlt_eq_true]; omega
private theorem bmuxAlt_nat_beq_eq_false {a b : ℕ} : a.beq b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]
private theorem bmuxAlt_altListLen_eq : ∀ xs : List ℕ, altListLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (bmuxAlt_altListLen_eq xs)
private theorem bmuxAlt_bif_ble_min (m r : ℕ) :
    (cond (Nat.ble m r) m r) = min m r := by
  cases h : Nat.ble m r
  · have hlt := bmuxAlt_nat_ble_eq_false.mp h; simp [cond, Nat.min_eq_right (Nat.le_of_lt hlt)]
  · simp [cond, Nat.min_eq_left (bmuxAlt_nat_ble_eq_true.mp h)]
private theorem bmuxAlt_cond_true {α : Type} (a b : α) : (cond true a b) = a := rfl
private theorem bmuxAlt_cond_false {α : Type} (a b : α) : (cond false a b) = b := rfl
private theorem bmuxAlt_bif_false_left : ∀ {b c : Bool},
    (cond b false c) = true → b = false ∧ c = true
  | false, true, _ => ⟨rfl, rfl⟩
  | false, false, h => Bool.noConfusion h
  | true, _, h => Bool.noConfusion h
private theorem bmuxAlt_bif_false_right : ∀ {b c : Bool},
    (cond b c false) = true → b = true ∧ c = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => Bool.noConfusion h
  | false, _, h => Bool.noConfusion h
private theorem bmuxSumRange_succ_shift (f : ℕ → ℕ) :
    ∀ d : ℕ, bmuxSumRange (d + 1) f = f 0 + bmuxSumRange d (fun j => f (j + 1))
  | 0 => by simp [bmuxSumRange]
  | d + 1 => by
    calc bmuxSumRange (d + 2) f
      _ = bmuxSumRange (d + 1) f + f (d + 1) := rfl
      _ = (f 0 + bmuxSumRange d (fun j => f (j + 1))) + f (d + 1) := by
          rw [bmuxSumRange_succ_shift f d]
      _ = f 0 + bmuxSumRange (d + 1) (fun j => f (j + 1)) := by simp [bmuxSumRange, Nat.add_assoc]
private theorem bmuxAlt_altDriftSum27_eq_bmuxSumRange (vR : ℕ) :
    ∀ (d : ℕ) (ps vhs : List ℕ), ps.length = d → d ≤ vhs.length → altDriftSum27 vR ps vhs =
        bmuxSumRange d (fun j => ps.getD j 0 * (vR - vhs.getD j 0))
  | 0, [], _, _, _ => rfl
  | 0, _ :: _, _, hps, _ => by simp at hps
  | _ + 1, [], _, hps, _ => by simp at hps
  | _ + 1, _ :: _, [], _, hvhs => by simp at hvhs
  | d + 1, p :: ps, vh :: vhs, hps, hvhs => by
    rw [bmuxSumRange_succ_shift]; have ih := bmuxAlt_altDriftSum27_eq_bmuxSumRange vR d ps vhs
      (by simpa using hps) (by simp at hvhs; omega)
    simpa [altDriftSum27] using congrArg (Nat.add (p * (vR - vh))) ih
private def bmuxAltStepOk (m lTableMax r vPrev vR lR tau9 nSub : ℕ) (vhRest : List ℕ) : Bool :=
  cond (tau9.beq 0) (checkEigStep m r vR vPrev)
    (cond (Bool.or (primNatBlt lR 1) (primNatBlt lTableMax lR)) false
      (cond (Bool.or (Bool.not ((altListLen (altEvalRowLo12 (Nat.mul lR m) r tau9 nSub)).beq
            (cond (Nat.ble (Nat.mul lR m) r) (Nat.mul lR m) r)))
          (Bool.or ((altSumNat (altEvalRowLo12 (Nat.mul lR m) r tau9 nSub)).beq 0)
            (primNatBlt (altListLen (vPrev :: vhRest))
              (cond (Nat.ble (Nat.mul lR m) r) (Nat.mul lR m) r))))
        false (primNatBlt (Nat.mul lR (Nat.mul tau9 1000000000000000000))
          (altDriftSum27 vR (altEvalRowLo12 (Nat.mul lR m) r tau9 nSub) (vPrev :: vhRest)))))
private theorem bmuxAlt_checkAltMuxLoop_cons (m lTableMax r vPrev vR lR tau9 nSub : ℕ)
    (vhRest vRest lRest tauRest nsubRest : List ℕ) :
    checkAltMuxLoop m lTableMax r (vPrev :: vhRest)
        (vR :: vRest) (lR :: lRest) (tau9 :: tauRest) (nSub :: nsubRest) =
      (cond (primNatBlt vR vPrev) false
        (cond (bmuxAltStepOk m lTableMax r vPrev vR lR tau9 nSub vhRest)
          (checkAltMuxLoop m lTableMax (Nat.add r 1) (vR :: vPrev :: vhRest)
            vRest lRest tauRest nsubRest) false)) := by
  conv_lhs => unfold checkAltMuxLoop checkAltMuxLoopAux
  simp only [AltForce.withForcedNat_eq, AltForce.withForcedList_eq]; rfl
/-- Sub-band chaining theorem for `checkAltMuxLoop`. -/
theorem checkAltMuxLoop_append (m lTableMax r : ℕ)
    (vHist v1 l1 t1 n1 v2 l2 t2 n2 : List ℕ)
    (hv : v1.length = t1.length) (hl : l1.length = t1.length) (hn : n1.length = t1.length)
    (h1 : checkAltMuxLoop m lTableMax r vHist v1 l1 t1 n1 = true)
    (h2 : checkAltMuxLoop m lTableMax (r + v1.length) (v1.reverse ++ vHist) v2 l2 t2 n2 = true) :
    checkAltMuxLoop m lTableMax r vHist
      (v1 ++ v2) (l1 ++ l2) (t1 ++ t2) (n1 ++ n2) = true := by
  induction v1 generalizing r vHist l1 t1 n1 with
  | nil =>
    cases t1 with
    | nil =>
      cases l1 with
      | nil =>
        cases n1 with
        | nil => simpa using h2
        | cons _ _ => simp at hn
      | cons _ _ => simp at hl
    | cons _ _ => simp at hv
  | cons vR vRest ih =>
    cases t1 with
    | nil => simp at hv
    | cons tau9 tauRest =>
      cases l1 with
      | nil => simp at hl
      | cons lR lRest =>
        cases n1 with
        | nil => simp at hn
        | cons nSub nsubRest =>
          cases vHist with
          | nil => simp [checkAltMuxLoop, checkAltMuxLoopAux] at h1
          | cons vPrev vhRest =>
            rw [bmuxAlt_checkAltMuxLoop_cons] at h1
            change checkAltMuxLoop m lTableMax r (vPrev :: vhRest) (vR :: (vRest ++ v2))
              (lR :: (lRest ++ l2)) (tau9 :: (tauRest ++ t2)) (nSub :: (nsubRest ++ n2)) = true
            rw [bmuxAlt_checkAltMuxLoop_cons]
            cases hlt : primNatBlt vR vPrev with
            | true => simp [hlt] at h1
            | false =>
              simp only [hlt, bmuxAlt_cond_false] at h1 ⊢
              cases hs : bmuxAltStepOk m lTableMax r vPrev vR lR tau9 nSub vhRest with
              | false => rw [hs, bmuxAlt_cond_false] at h1; exact Bool.noConfusion h1
              | true =>
                rw [hs, bmuxAlt_cond_true] at h1; rw [bmuxAlt_cond_true]
                have hrev : (vR :: vRest).reverse ++ (vPrev :: vhRest) =
                    vRest.reverse ++ (vR :: vPrev :: vhRest) := by simp [List.reverse_cons]
                have hr_add : r + (vR :: vRest).length = Nat.add r 1 + vRest.length := by
                  simp; omega
                rw [hrev, hr_add] at h2
                exact ih (Nat.add r 1) (vR :: vPrev :: vhRest) lRest tauRest nsubRest
                  (by simpa using hv) (by simpa using hl) (by simpa using hn) h1 h2
/-- Convenience `rfl`-equality wrapper for chaining `checkAltMuxLoop` slices across parts. -/
theorem checkAltMuxLoop_chain (m lTableMax r r' : ℕ)
    (vHist vHist' v1 l1 t1 n1 v2 l2 t2 n2 vt lt tt nt : List ℕ)
    (hv : v1.length = t1.length) (hl : l1.length = t1.length) (hn : n1.length = t1.length)
    (hr : r + v1.length = r') (hvh : v1.reverse ++ vHist = vHist')
    (hvt : v1 ++ v2 = vt) (hlt : l1 ++ l2 = lt) (htt : t1 ++ t2 = tt) (hnt : n1 ++ n2 = nt)
    (h1 : checkAltMuxLoop m lTableMax r vHist v1 l1 t1 n1 = true)
    (h2 : checkAltMuxLoop m lTableMax r' vHist' v2 l2 t2 n2 = true) :
    checkAltMuxLoop m lTableMax r vHist vt lt tt nt = true := by
  cases hr; cases hvh; cases hvt; cases hlt; cases htt; cases hnt
  exact checkAltMuxLoop_append m lTableMax r vHist v1 l1 t1 n1 v2 l2 t2 n2 hv hl hn h1 h2
/-- Assembles `checkAltMuxTable12 = true` from `checkAltMuxHeader12` and `checkAltMuxLoop`. -/
theorem checkAltMuxTable12_of_parts (m kMax lTableMax v0 v1 : ℕ)
    (vRest lRows tau9Rows nsubRows : List ℕ)
    (hhdr : checkAltMuxHeader12 m kMax lTableMax (v0 :: v1 :: vRest) lRows tau9Rows nsubRows = true)
    (hloop : checkAltMuxLoop m lTableMax 2 [v1, v0] vRest lRows tau9Rows nsubRows = true) :
    checkAltMuxTable12 m kMax lTableMax (v0 :: v1 :: vRest) lRows tau9Rows nsubRows = true := by
  unfold checkAltMuxTable12; rw [hhdr, bmuxAlt_cond_true]; exact hloop
private theorem bmuxAlt_mono_of_step (f : ℕ → ℕ) (kMax : ℕ)
    (hstep : ∀ r : ℕ, 1 ≤ r → r ≤ kMax → f (r - 1) ≤ f r) :
    ∀ r₁ d : ℕ, r₁ + d ≤ kMax → f r₁ ≤ f (r₁ + d)
  | _, 0, _ => Nat.le_refl _
  | r₁, d + 1, hk =>
    Nat.le_trans (bmuxAlt_mono_of_step f kMax hstep r₁ d (by omega))
      (by
        simpa [show r₁ + (d + 1) - 1 = r₁ + d by omega] using
          hstep (r₁ + (d + 1)) (by omega) hk)
private theorem bmuxAlt_checkAltMuxLoop_step_props (m lTableMax : ℕ)
    (vPot lRows tau9Rows nsubRows vRem : List ℕ) :
    ∀ (vHist lRem tauRem nsubRem : List ℕ) (r : ℕ), 2 ≤ r → vHist.length = r →
      (∀ j < r, vHist.getD j 0 = vPot.getD (r - 1 - j) 0) →
      (∀ j < vRem.length, vRem.getD j 0 = vPot.getD (r + j) 0) →
      (∀ j < lRem.length, lRem.getD j 0 = lRows.getD (r - 2 + j) 0) →
      (∀ j < tauRem.length, tauRem.getD j 0 = tau9Rows.getD (r - 2 + j) 0) →
      (∀ j < nsubRem.length, nsubRem.getD j 0 = nsubRows.getD (r - 2 + j) 0) →
      checkAltMuxLoop m lTableMax r vHist vRem lRem tauRem nsubRem = true →
      ∀ s : ℕ, r ≤ s → s < r + vRem.length → vPot.getD (s - 1) 0 ≤ vPot.getD s 0 ∧
        (tau9Rows.getD (s - 2) 0 = 0 →
          checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true) ∧
        (0 < tau9Rows.getD (s - 2) 0 →
          let lS := lRows.getD (s - 2) 0
          let mEff := lS * m
          let d := min mEff s
          let row := altEvalRowLo12 mEff s (tau9Rows.getD (s - 2) 0) (nsubRows.getD (s - 2) 0)
          1 ≤ lS ∧ lS ≤ lTableMax ∧ row.length = d ∧
            0 < altSumNat row ∧ lS * (tau9Rows.getD (s - 2) 0 * 1000000000000000000) <
              bmuxSumRange d
                (fun j => row.getD j 0 * (vPot.getD s 0 - vPot.getD (s - 1 - j) 0))) := by
  induction vRem with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ s _ hslt; simp at hslt; omega
  | cons vR vRest ih =>
    intro vHist lRem tauRem nsubRem r hr2 hvh_len hvh_eq hv_eq hl_eq ht_eq hn_eq hchk s hrs hslt
    cases lRem with
    | nil => simp [checkAltMuxLoop, checkAltMuxLoopAux] at hchk
    | cons lR lRest =>
      cases tauRem with
      | nil => simp [checkAltMuxLoop, checkAltMuxLoopAux] at hchk
      | cons tau9 tauRest =>
        cases nsubRem with
        | nil => simp [checkAltMuxLoop, checkAltMuxLoopAux] at hchk
        | cons nSub nsubRest =>
          cases vHist with
          | nil => simp [checkAltMuxLoop, checkAltMuxLoopAux] at hchk
          | cons vPrev vhRest =>
            have hvR_eq : vR = vPot.getD r 0 := by simpa using hv_eq 0 (Nat.succ_pos _)
            have hvPrev_eq : vPrev = vPot.getD (r - 1) 0 := by simpa using hvh_eq 0 (by omega)
            have hlR_eq : lR = lRows.getD (r - 2) 0 := by simpa using hl_eq 0 (Nat.succ_pos _)
            have htau_eq : tau9 = tau9Rows.getD (r - 2) 0 := by simpa using ht_eq 0 (Nat.succ_pos _)
            have hnsub_eq : nSub = nsubRows.getD (r - 2) 0 := by
              simpa using hn_eq 0 (Nat.succ_pos _)
            rw [bmuxAlt_checkAltMuxLoop_cons] at hchk
            obtain ⟨hblt, hchk⟩ := bmuxAlt_bif_false_left hchk
            have hv_mono : vPrev ≤ vR := bmuxAlt_primNatBlt_eq_false.mp hblt
            obtain ⟨hs_ok, hchk⟩ := bmuxAlt_bif_false_right hchk
            have hr_succ : Nat.add r 1 = r + 1 := rfl; rw [hr_succ] at hchk
            by_cases hsr : s = r
            · subst s
              dsimp only; rw [← hvR_eq, ← hvPrev_eq, ← hlR_eq, ← htau_eq, ← hnsub_eq]
              refine ⟨hv_mono, fun ht0 => ?_, fun ht_pos => ?_⟩
              · unfold bmuxAltStepOk at hs_ok
                rw [ht0, Nat.beq_eq.mpr (rfl : 0 = 0), bmuxAlt_cond_true] at hs_ok; exact hs_ok
              · unfold bmuxAltStepOk at hs_ok
                have ht_f : tau9.beq 0 = false := bmuxAlt_nat_beq_eq_false.mpr (Nat.ne_of_gt ht_pos)
                rw [ht_f, bmuxAlt_cond_false] at hs_ok
                obtain ⟨hlr, hs_ok⟩ := bmuxAlt_bif_false_left hs_ok
                simp only [Bool.or_eq_false_iff, bmuxAlt_primNatBlt_eq_false] at hlr
                obtain ⟨hl1, hl_hi⟩ := hlr; have hmEff_eq : Nat.mul lR m = lR * m := rfl
                rw [hmEff_eq, bmuxAlt_bif_ble_min] at hs_ok
                obtain ⟨hbad, hs_ok⟩ := bmuxAlt_bif_false_left hs_ok
                simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Nat.beq_eq,
                  bmuxAlt_nat_beq_eq_false, bmuxAlt_primNatBlt_eq_false,
                  bmuxAlt_altListLen_eq] at hbad
                obtain ⟨hr_len, hsum_ne, hvh_ge⟩ := hbad
                have hdrift_lt := bmuxAlt_primNatBlt_eq_true.mp hs_ok
                have hmul_eq : Nat.mul lR (Nat.mul tau9 1000000000000000000) =
                    lR * (tau9 * 1000000000000000000) := rfl
                rw [hmul_eq, bmuxAlt_altDriftSum27_eq_bmuxSumRange vR (min (lR * m) r)
                  (altEvalRowLo12 (lR * m) r tau9 nSub) (vPrev :: vhRest)
                  hr_len hvh_ge] at hdrift_lt
                have hsum_congr :
                    ∀ n : ℕ, n ≤ r →
                      bmuxSumRange n (fun j =>
                        (altEvalRowLo12 (lR * m) r tau9 nSub).getD j 0 *
                          (vR - (vPrev :: vhRest).getD j 0)) =
                      bmuxSumRange n (fun j =>
                        (altEvalRowLo12 (lR * m) r tau9 nSub).getD j 0 *
                          (vR - vPot.getD (r - 1 - j) 0)) := by
                  intro n hn
                  induction n with
                  | zero => rfl
                  | succ k ih_n =>
                    simp only [bmuxSumRange, ih_n (by omega), hvh_eq k (by omega)]
                rw [hsum_congr (min (lR * m) r) (Nat.min_le_right (lR * m) r)] at hdrift_lt
                exact ⟨hl1, hl_hi, hr_len, Nat.pos_of_ne_zero hsum_ne, hdrift_lt⟩
            · have hs_ge : r + 1 ≤ s := by omega
              have hs_lt' : s < (r + 1) + vRest.length := by simp at hslt; omega
              exact ih (vR :: vPrev :: vhRest) lRest tauRest nsubRest (r + 1)
                (by omega) (by simp at hvh_len ⊢; omega)
                (fun j hj => by
                  rcases j with _ | j'
                  · simpa using hvR_eq
                  · have hprev : (vPrev :: vhRest).getD j' 0 = vPot.getD (r - 1 - j') 0 :=
                      hvh_eq j' (by omega)
                    have hidx : r + 1 - 1 - (j' + 1) = r - 1 - j' := by omega
                    change (vPrev :: vhRest).getD j' 0 = vPot.getD (r + 1 - 1 - (j' + 1)) 0
                    rw [hidx]; exact hprev)
                (fun j hj => by
                  have hstep : vRest.getD j 0 = vPot.getD (r + (j + 1)) 0 :=
                    hv_eq (j + 1) (Nat.succ_lt_succ hj)
                  have hidx : r + (j + 1) = (r + 1) + j := by omega
                  rw [← hidx]; exact hstep)
                (fun j hj => by
                  have hstep : lRest.getD j 0 = lRows.getD (r - 2 + (j + 1)) 0 :=
                    hl_eq (j + 1) (Nat.succ_lt_succ hj)
                  have hidx : r - 2 + (j + 1) = (r + 1) - 2 + j := by omega
                  rw [← hidx]; exact hstep)
                (fun j hj => by
                  have hstep : tauRest.getD j 0 = tau9Rows.getD (r - 2 + (j + 1)) 0 :=
                    ht_eq (j + 1) (Nat.succ_lt_succ hj)
                  have hidx : r - 2 + (j + 1) = (r + 1) - 2 + j := by omega
                  rw [← hidx]; exact hstep)
                (fun j hj => by
                  have hstep : nsubRest.getD j 0 = nsubRows.getD (r - 2 + (j + 1)) 0 :=
                    hn_eq (j + 1) (Nat.succ_lt_succ hj)
                  have hidx : r - 2 + (j + 1) = (r + 1) - 2 + j := by omega
                  rw [← hidx]; exact hstep)
                hchk s hs_ge hs_lt'
/-- Extracts row-by-row Bellman drift, workspace bounds, and monotonicity from
  `checkAltMuxTable12 = true`. -/
theorem checkAltMuxTable12_props {m kMax lTableMax : ℕ}
    {vPot lRows tau9Rows nsubRows : List ℕ}
    (h : checkAltMuxTable12 m kMax lTableMax vPot lRows tau9Rows nsubRows = true) :
    1 ≤ m ∧ 1 ≤ lTableMax ∧ lTableMax * m ≤ 8192 ∧ 2 ≤ kMax ∧ kMax ≤ 1024 ∧
      vPot.getD 0 0 = 0 ∧
      (∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ kMax → vPot.getD r₁ 0 ≤ vPot.getD r₂ 0) ∧
      checkEigStep m 1 (vPot.getD 1 0) (vPot.getD 0 0) = true ∧
      (∀ s : ℕ, 2 ≤ s → s ≤ kMax →
        (tau9Rows.getD (s - 2) 0 = 0 →
          checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true) ∧
        (0 < tau9Rows.getD (s - 2) 0 →
          let lS := lRows.getD (s - 2) 0
          let mEff := lS * m
          let d := min mEff s
          let row := altEvalRowLo12 mEff s (tau9Rows.getD (s - 2) 0) (nsubRows.getD (s - 2) 0)
          1 ≤ lS ∧ lS ≤ lTableMax ∧
            row.length = d ∧
            0 < altSumNat row ∧
            lS * (tau9Rows.getD (s - 2) 0 * 1000000000000000000) <
              bmuxSumRange d
                (fun j => row.getD j 0 * (vPot.getD s 0 - vPot.getD (s - 1 - j) 0)))) := by
  unfold checkAltMuxTable12 at h; obtain ⟨hhdr, h⟩ := bmuxAlt_bif_false_right h
  unfold checkAltMuxHeader12 at hhdr; obtain ⟨hg1, hhdr⟩ := bmuxAlt_bif_false_left hhdr
  simp only [Bool.or_eq_false_iff, bmuxAlt_primNatBlt_eq_false] at hg1
  obtain ⟨hm1, hl1, hlm8_raw, hk2, hk10⟩ := hg1; have hlm8 : lTableMax * m ≤ 8192 := hlm8_raw
  obtain ⟨hg2, hhdr⟩ := bmuxAlt_bif_false_left hhdr
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Nat.beq_eq, bmuxAlt_altListLen_eq] at hg2
  obtain ⟨hv_len_raw, _, _, _⟩ := hg2; have hv_len : vPot.length = kMax + 1 := hv_len_raw
  rcases vPot with _ | ⟨v0, _ | ⟨v1, vRest⟩⟩
  · simp at hv_len
  · simp at hv_len; omega
  · dsimp only at h hhdr; obtain ⟨hv0_z, heig1⟩ := bmuxAlt_bif_false_left hhdr
    simp only [Bool.not_eq_false', Nat.beq_eq] at hv0_z
    have hv1_ge : v0 ≤ v1 := by
      unfold checkEigStep at heig1; obtain ⟨hg, _⟩ := bmuxAlt_bif_false_left heig1
      simp only [Bool.or_eq_false_iff, bmuxAlt_nat_ble_eq_false] at hg; exact Nat.le_of_lt hg.2
    have hloop := bmuxAlt_checkAltMuxLoop_step_props m lTableMax (v0 :: v1 :: vRest)
      lRows tau9Rows nsubRows
      vRest [v1, v0] lRows tau9Rows nsubRows 2
      (by omega) rfl
      (fun j hj => by rcases j with _ | _ | _ <;> first | rfl | omega)
      (fun j _ => by rw [Nat.add_comm 2 j]; rfl)
      (fun j _ => by rw [show 2 - 2 + j = j by omega])
      (fun j _ => by rw [show 2 - 2 + j = j by omega])
      (fun j _ => by rw [show 2 - 2 + j = j by omega])
      h
    have hstep_mono : ∀ r : ℕ, 1 ≤ r → r ≤ kMax →
        (v0 :: v1 :: vRest).getD (r - 1) 0 ≤ (v0 :: v1 :: vRest).getD r 0 := by
      intro r hr1 hrk
      by_cases hr_eq1 : r = 1
      · subst hr_eq1; exact hv1_ge
      · exact (hloop r (by omega) (by simp at hv_len; omega)).1
    have hmono : ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ kMax →
        (v0 :: v1 :: vRest).getD r₁ 0 ≤ (v0 :: v1 :: vRest).getD r₂ 0 := by
      intro r₁ r₂ h12 h2k
      have hd := bmuxAlt_mono_of_step (fun idx => (v0 :: v1 :: vRest).getD idx 0)
        kMax hstep_mono r₁ (r₂ - r₁) (by omega)
      simpa [show r₁ + (r₂ - r₁) = r₂ by omega] using hd
    exact ⟨hm1, hl1, hlm8, hk2, hk10, hv0_z, hmono, heig1,
      fun s hs2 hsk => (hloop s hs2 (by simp at hv_len; omega)).2⟩
private theorem bmuxAlt_checkAltMuxPrefixLoop_props :
    ∀ (cnt lMaxCell : ℕ) (lRem : List ℕ), checkAltMuxPrefixLoop cnt lMaxCell lRem = true →
      ∀ j < cnt, 1 ≤ lRem.getD j 0 ∧ lRem.getD j 0 ≤ lMaxCell
  | 0, _, _, _, _, hj => by omega
  | _ + 1, _, [], hchk, _, _ => by simp [checkAltMuxPrefixLoop] at hchk
  | cnt + 1, lMaxCell, lR :: lRest, hchk, j, hj => by
    unfold checkAltMuxPrefixLoop at hchk; obtain ⟨hg, hchk⟩ := bmuxAlt_bif_false_left hchk
    simp only [Bool.or_eq_false_iff, bmuxAlt_primNatBlt_eq_false] at hg
    rcases j with _ | j'
    · exact hg
    · exact bmuxAlt_checkAltMuxPrefixLoop_props cnt lMaxCell lRest hchk j' (by omega)
/-- Extracts prefix workspace bounds `1 ≤ lRows[r - 2] ≤ lMaxCell` (`2 ≤ r ≤ k`) from
  `checkAltMuxPrefixLMax = true`. -/
theorem checkAltMuxPrefixLMax_props {k lTableMax lMaxCell : ℕ} {lRows : List ℕ}
    (h : checkAltMuxPrefixLMax k lTableMax lMaxCell lRows = true) :
    2 ≤ k ∧ 1 ≤ lMaxCell ∧ lMaxCell ≤ lTableMax ∧
      ∀ r : ℕ, 2 ≤ r → r ≤ k → 1 ≤ lRows.getD (r - 2) 0 ∧ lRows.getD (r - 2) 0 ≤ lMaxCell := by
  unfold checkAltMuxPrefixLMax at h; obtain ⟨hg, h⟩ := bmuxAlt_bif_false_left h
  simp only [Bool.or_eq_false_iff, bmuxAlt_primNatBlt_eq_false, bmuxAlt_altListLen_eq] at hg
  obtain ⟨hk2, hl1, hlt, _⟩ := hg; have hsub : Nat.sub k 1 = k - 1 := rfl; rw [hsub] at h
  refine ⟨hk2, hl1, hlt, fun r hr2 hrk => ?_⟩
  exact bmuxAlt_checkAltMuxPrefixLoop_props (k - 1) lMaxCell lRows h (r - 2) (by omega)
/-- Conjunction of a finite list of boolean certificate checks for batched `decide +kernel`. -/
def muxAllTrue : List Bool → Bool
  | [] => true
  | b :: bs => cond b (muxAllTrue bs) false
/-! ## Section 2: Running-Cap & Sparse Table Extraction Proofs -/
private theorem msp_cond_true {α : Type} (a b : α) : cond true a b = a := rfl
private theorem msp_cond_false {α : Type} (a b : α) : cond false a b = b := rfl
private theorem msp_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, msp_nat_ble_eq_true]
private theorem msp_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, msp_nat_ble_eq_true]; omega
private theorem msp_primNatBlt_eq_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  unfold primNatBlt; rw [msp_nat_ble_eq_true]; change a + 1 ≤ b ↔ a < b; omega
private theorem msp_primNatBlt_eq_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, msp_primNatBlt_eq_true]; omega
private theorem msp_bool_eq {u v : Bool} (h : (u = true) = (v = true)) : u = v := by
  cases u <;> cases v <;> simp at h ⊢
private theorem msp_to_beq (a b : ℕ) {u : Bool} (h : (u = true) = (a = b)) :
    u = (a == b) :=
  msp_bool_eq (h.trans (Nat.beq_eq_true_eq a b).symm)
private theorem msp_altListLen_eq : ∀ xs : List ℕ, altListLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (msp_altListLen_eq xs)
private theorem msp_natMin_eq (a b : ℕ) : highdNatMin a b = min a b := by
  unfold highdNatMin
  cases h : Nat.ble a b
  · simp [cond, Nat.min_eq_right (Nat.le_of_lt (msp_nat_ble_eq_false.mp h))]
  · simp [cond, Nat.min_eq_left (msp_nat_ble_eq_true.mp h)]
private theorem msp_forceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]
private theorem msp_max_eq_bif (a b : ℕ) :
    cond (primNatBlt a b) b a = max a b := by
  cases h : primNatBlt a b
  · exact (Nat.max_eq_left (msp_primNatBlt_eq_false.mp h)).symm
  · exact (Nat.max_eq_right (msp_primNatBlt_eq_true.mp h).le).symm
private theorem msp_getD_append_left :
    ∀ (xs ys : List ℕ) (j : ℕ), j < xs.length → (xs ++ ys).getD j 0 = xs.getD j 0
  | [], _, _, hj => by simp at hj
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, j + 1, hj => msp_getD_append_left xs ys j (by simp at hj; omega)
private theorem msp_getD_append_right : ∀ (xs ys : List ℕ) (j : ℕ), xs.length ≤ j →
      (xs ++ ys).getD j 0 = ys.getD (j - xs.length) 0
  | [], ys, j, _ => by simp
  | _ :: _, _, 0, hj => by simp at hj
  | _ :: xs, ys, j + 1, hj => by
    simpa [Nat.succ_sub_succ_eq_sub] using msp_getD_append_right xs ys j (by simp at hj; omega)
private theorem msp_rev_append_getD : ∀ (xs vHist vFull : List ℕ) (r : ℕ),
      (∀ j < r, vHist.getD j 0 = vFull.getD (r - 1 - j) 0) →
      (∀ j < xs.length, xs.getD j 0 = vFull.getD (r + j) 0) →
      ∀ j < r + xs.length, (xs.reverse ++ vHist).getD j 0 = vFull.getD (r + xs.length - 1 - j) 0
  | [], vHist, _, r, hvh, _, j, hj => by simpa using hvh j (by simpa using hj)
  | x :: xs, vHist, vFull, r, hvh, hxs, j, hj => by
    rw [List.reverse_cons, List.append_assoc, List.singleton_append]
    have hx0 : x = vFull.getD r 0 := (by simpa using hxs 0 (Nat.succ_pos _))
    have ih := msp_rev_append_getD xs (x :: vHist) vFull (r + 1) (fun k hk ↦ by
        rcases k with _ | k'
        · rw [List.getD_cons_zero, show r + 1 - 1 - 0 = r by omega]; exact hx0
        · rw [List.getD_cons_succ, show r + 1 - 1 - (k' + 1) = r - 1 - k' by omega]
          exact hvh k' (by omega))
      (fun k hk ↦ by
        have h1 := hxs (k + 1) (by simp only [List.length_cons]; omega)
        simpa [show r + (k + 1) = r + 1 + k by omega] using h1)
      j (by simp only [List.length_cons] at hj ⊢; omega)
    rw [show r + (x :: xs).length - 1 - j = r + 1 + xs.length - 1 - j by
      simp only [List.length_cons]; omega]
    exact ih
theorem muxRunningCap_self_le (vPot : List ℕ) : ∀ r : ℕ, vPot.getD r 0 ≤ muxRunningCap vPot r
  | 0 => le_rfl
  | r + 1 => le_max_right (muxRunningCap vPot r) (vPot.getD (r + 1) 0)
theorem muxRunningCap_mono (vPot : List ℕ) :
    ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → muxRunningCap vPot r₁ ≤ muxRunningCap vPot r₂ := by
  intro r₁ r₂ hle
  induction hle with
  | refl => exact le_rfl
  | @step b _ ih => exact ih.trans (le_max_left (muxRunningCap vPot b) (vPot.getD (b + 1) 0))
theorem muxRunningCap_ge_of_le (vPot : List ℕ) {j r : ℕ} (hjr : j ≤ r) :
    vPot.getD j 0 ≤ muxRunningCap vPot r :=
  (muxRunningCap_self_le vPot j).trans (muxRunningCap_mono vPot hjr)
theorem muxHitValSum27_eq_sum_range : ∀ (d : ℕ) (ps vhs : List ℕ), ps.length = d → d ≤ vhs.length →
      muxHitValSum27 ps vhs = ∑ j ∈ Finset.range d, ps.getD j 0 * vhs.getD j 0
  | 0, [], _, _, _ => by simp [muxHitValSum27]
  | 0, _ :: _, _, hps, _ => by simp at hps
  | _ + 1, [], _, hps, _ => by simp at hps
  | _ + 1, _ :: _, [], _, hvhs => by simp at hvhs
  | d + 1, p :: ps, vh :: vhs, hps, hvhs => by
    have ih := muxHitValSum27_eq_sum_range d ps vhs (by simpa using hps) (by simp at hvhs; omega)
    have hshift : (∑ j ∈ Finset.range (d + 1), (p :: ps).getD j 0 * (vh :: vhs).getD j 0) =
          p * vh + ∑ j ∈ Finset.range d, ps.getD j 0 * vhs.getD j 0 := by
      rw [Finset.sum_range_succ']; simp [add_comm]
    rw [hshift]; unfold muxHitValSum27; dsimp only
    rw [msp_to_beq p 0 Nat.beq_eq]
    cases hp0 : (p == 0)
    · rw [msp_cond_false, ih]; rfl
    · rw [msp_cond_true, beq_iff_eq.mp hp0, ih]; simp
private theorem muxCheckSparseDrift_to_active {m lTableMax s lS tau9 nSub : ℕ}
    {vPot rowLo12 vHist : List ℕ} (hvh_eq : ∀ j < s, vHist.getD j 0 = vPot.getD (s - 1 - j) 0)
    (h : muxCheckSparseDrift m lTableMax s lS tau9 nSub (vPot.getD s 0)
      (muxRunningCap vPot s) rowLo12 vHist = true) :
    MuxSparseActiveValid m lTableMax s vPot lS tau9 nSub rowLo12 := by
  unfold MuxSparseActiveValid; unfold muxCheckSparseDrift at h
  rw [msp_to_beq tau9 0 Nat.beq_eq, msp_to_beq nSub 0 Nat.beq_eq] at h
  cases hg1 : Bool.or (primNatBlt lS 1)
      (Bool.or (primNatBlt lTableMax lS) (Bool.or (tau9 == 0) (nSub == 0))) with
  | true => rw [hg1, msp_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg1, msp_cond_false] at h; dsimp only at h
    simp only [Bool.or_eq_false_iff, msp_primNatBlt_eq_false, beq_eq_false_iff_ne] at hg1
    obtain ⟨hl1, hlMax, htau0, hnsub0⟩ := hg1
    rw [show Nat.mul lS m = lS * m from rfl, msp_natMin_eq] at h
    set d := min (lS * m) s
    rw [msp_to_beq (altListLen rowLo12) d Nat.beq_eq,
      msp_to_beq (altSumNat rowLo12) 0 Nat.beq_eq] at h
    cases hg2 : Bool.or (Bool.not (altListLen rowLo12 == d))
        (Bool.or (altSumNat rowLo12 == 0)
          (Bool.or (primNatBlt 1000000000000 (altSumNat rowLo12))
            (primNatBlt (altListLen vHist) d))) with
    | true => rw [hg2, msp_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg2, msp_cond_false] at h
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', beq_iff_eq,
        beq_eq_false_iff_ne, msp_primNatBlt_eq_false, msp_altListLen_eq] at hg2
      obtain ⟨hr_len, htot_ne, htot_le, hvh_ge⟩ := hg2; have hlt := msp_primNatBlt_eq_true.mp h
      rw [muxHitValSum27_eq_sum_range d rowLo12 vHist hr_len hvh_ge] at hlt
      have hsum_eq : (∑ j ∈ Finset.range d, rowLo12.getD j 0 * vHist.getD j 0) =
            ∑ j ∈ Finset.range d, rowLo12.getD j 0 * vPot.getD (s - 1 - j) 0 := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hj_lt : j < s := (Finset.mem_range.mp hj).trans_le (Nat.min_le_right _ _)
        rw [hvh_eq j hj_lt]
      rw [hsum_eq] at hlt
      refine ⟨hl1, hlMax, Nat.pos_of_ne_zero htau0, Nat.pos_of_ne_zero hnsub0,
        hr_len, Nat.pos_of_ne_zero htot_ne, htot_le, ?_⟩
      simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ← add_assoc] at hlt; exact hlt
/-- Sub-band chaining theorem for `checkMuxSparseTail` across split `r` intervals. -/
theorem checkMuxSparseTail_append (m lTableMax : ℕ) :
    ∀ (v1 : List ℕ) (r vCapPrev : ℕ) (vHist v2 : List ℕ) (a1 a2 : List MuxSparseAnchor),
      (∀ a ∈ a1, a.rAct < r + v1.length) → (∀ b ∈ a2, r + v1.length ≤ b.rAct) →
      checkMuxSparseTail m lTableMax r vCapPrev vHist v1 a1 = true →
      checkMuxSparseTail m lTableMax (r + v1.length)
        (v1.foldl max vCapPrev) (v1.reverse ++ vHist) v2 a2 = true →
      checkMuxSparseTail m lTableMax r vCapPrev vHist (v1 ++ v2) (a1 ++ a2) = true
  | [], _, _, _, _, a1, _, _, _, h1, h2 => by
    cases a1 with
    | nil => simpa using h2
    | cons _ _ => simp [checkMuxSparseTail, checkMuxSparseTailAux] at h1
  | vR :: vRest, r, vCapPrev, vHist, v2, a1, a2, ha1, ha2, h1, h2 => by
    cases vHist with
    | nil => simp [checkMuxSparseTail, checkMuxSparseTailAux] at h1
    | cons vPrev vhRest =>
      dsimp only [checkMuxSparseTail, checkMuxSparseTailAux, List.cons_append] at h1 ⊢
      simp only [msp_forceNat_eq, msp_max_eq_bif] at h1 ⊢
      have hfold : (vR :: vRest).foldl max vCapPrev = vRest.foldl max (max vCapPrev vR) := rfl
      have hrev : (vR :: vRest).reverse ++ (vPrev :: vhRest) =
          vRest.reverse ++ (vR :: vPrev :: vhRest) := by simp [List.reverse_cons]
      have hr_add : r + (vR :: vRest).length = Nat.add r 1 + vRest.length := by
        simp only [List.length_cons, show Nat.add r 1 = r + 1 from rfl]; omega
      rw [hfold, hrev, hr_add] at h2
      cases a1 with
      | nil =>
        dsimp only [List.nil_append] at h1 ⊢
        cases a2 with
        | nil =>
          dsimp only [checkMuxSparseTailAux] at h1 ⊢
          cases heig : checkEigStep m r vR vPrev with
          | false => rw [heig, msp_cond_false] at h1; exact Bool.noConfusion h1
          | true =>
            rw [heig, msp_cond_true] at h1; rw [msp_cond_true]
            exact checkMuxSparseTail_append m lTableMax vRest (Nat.add r 1) (max vCapPrev vR)
              (vR :: vPrev :: vhRest) v2 [] [] (by simp) (by simp) h1 h2
        | cons b bRest =>
          dsimp only [checkMuxSparseTailAux] at h1 ⊢
          have hb_ge : r + (vR :: vRest).length ≤ b.rAct := ha2 b List.mem_cons_self
          have hb_gt : r < b.rAct := (by simp only [List.length_cons] at hb_ge; omega)
          have hblt_f : primNatBlt b.rAct r = false := msp_primNatBlt_eq_false.mpr hb_gt.le
          have hbeq_f : (b.rAct == r) = false := beq_eq_false_iff_ne.mpr (by omega)
          rw [hblt_f, msp_cond_false, msp_to_beq b.rAct r Nat.beq_eq,
            hbeq_f, msp_cond_false]
          cases heig : checkEigStep m r vR vPrev with
          | false => rw [heig, msp_cond_false] at h1; exact Bool.noConfusion h1
          | true =>
            rw [heig, msp_cond_true] at h1; rw [msp_cond_true]
            exact checkMuxSparseTail_append m lTableMax vRest (Nat.add r 1) (max vCapPrev vR)
              (vR :: vPrev :: vhRest) v2 [] (b :: bRest) (by simp) (fun x hx ↦ by
                have := ha2 x hx
                simp only [List.length_cons, show Nat.add r 1 = r + 1 from rfl] at this ⊢; omega)
              h1 h2
      | cons a aRest =>
        dsimp only [List.cons_append, checkMuxSparseTailAux] at h1 ⊢
        cases hblt : primNatBlt a.rAct r with
        | true => rw [hblt, msp_cond_true] at h1; exact Bool.noConfusion h1
        | false =>
          rw [hblt, msp_cond_false] at h1; rw [msp_cond_false]
          rw [msp_to_beq a.rAct r Nat.beq_eq] at h1 ⊢
          cases hbeq : (a.rAct == r) with
          | true =>
            rw [hbeq, msp_cond_true] at h1; rw [msp_cond_true]
            cases hdr : muxCheckSparseDrift m lTableMax r a.lR a.tau9 a.nSub vR
                (max vCapPrev vR) a.rowLo12 (vPrev :: vhRest) with
            | false => rw [hdr, msp_cond_false] at h1; exact Bool.noConfusion h1
            | true =>
              rw [hdr, msp_cond_true] at h1; rw [msp_cond_true]
              exact checkMuxSparseTail_append m lTableMax vRest (Nat.add r 1) (max vCapPrev vR)
                (vR :: vPrev :: vhRest) v2 aRest a2 (fun x hx ↦ by
                  have := ha1 x (List.mem_cons_of_mem a hx)
                  simp only [List.length_cons, show Nat.add r 1 = r + 1 from rfl] at this ⊢; omega)
                (fun x hx ↦ by
                  have := ha2 x hx
                  simp only [List.length_cons, show Nat.add r 1 = r + 1 from rfl] at this ⊢; omega)
                h1 h2
          | false =>
            rw [hbeq, msp_cond_false] at h1; rw [msp_cond_false]
            cases heig : checkEigStep m r vR vPrev with
            | false => rw [heig, msp_cond_false] at h1; exact Bool.noConfusion h1
            | true =>
              rw [heig, msp_cond_true] at h1; rw [msp_cond_true]
              exact checkMuxSparseTail_append m lTableMax vRest (Nat.add r 1) (max vCapPrev vR)
                (vR :: vPrev :: vhRest) v2 (a :: aRest) a2 (fun x hx ↦ by
                  have := ha1 x hx
                  simp only [List.length_cons, show Nat.add r 1 = r + 1 from rfl] at this ⊢; omega)
                (fun x hx ↦ by
                  have := ha2 x hx
                  simp only [List.length_cons, show Nat.add r 1 = r + 1 from rfl] at this ⊢; omega)
                h1 h2
private theorem msp_prefAux_props (m lTableMax : ℕ) (vPot lPref tauPref nsubPref : List ℕ) :
    ∀ (vRem : List ℕ) (r vCapPrev : ℕ) (vHist lRem tauRem nsubRem : List ℕ), 2 ≤ r →
      vCapPrev = muxRunningCap vPot (r - 1) →
      vHist.length = r →
      (∀ j < r, vHist.getD j 0 = vPot.getD (r - 1 - j) 0) →
      (∀ j < vRem.length, vRem.getD j 0 = vPot.getD (r + j) 0) →
      (∀ j < lRem.length, lRem.getD j 0 = lPref.getD (r - 2 + j) 0) →
      (∀ j < tauRem.length, tauRem.getD j 0 = tauPref.getD (r - 2 + j) 0) →
      (∀ j < nsubRem.length, nsubRem.getD j 0 = nsubPref.getD (r - 2 + j) 0) →
      checkMuxSparsePrefAux m lTableMax vRem r vCapPrev vHist lRem tauRem nsubRem = true →
      vRem.length = lRem.length ∧ lRem.length = tauRem.length ∧ nsubRem.length = tauRem.length ∧
      ∀ s : ℕ, r ≤ s → s < r + vRem.length → (tauPref.getD (s - 2) 0 = 0 →
          checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true) ∧
        (0 < tauPref.getD (s - 2) 0 →
          let lS := lPref.getD (s - 2) 0
          let tau9 := tauPref.getD (s - 2) 0
          let nSub := nsubPref.getD (s - 2) 0
          MuxSparseActiveValid m lTableMax s vPot lS tau9 nSub
            (altEvalRowLo12 (lS * m) s tau9 nSub))
  | [], _, _, _, lRem, tauRem, nsubRem, _, _, _, _, _, _, _, _, hchk => by
    cases lRem <;> cases tauRem <;> cases nsubRem
    · exact ⟨rfl, rfl, rfl, fun s hrs hslt ↦ by simp at hslt; omega⟩
    all_goals simp [checkMuxSparsePrefAux] at hchk
  | vR :: vRest, r, vCapPrev, vHist, lRem, tauRem, nsubRem,
      hr2, hcap, hvh_len, hvh_eq, hv_eq, hl_eq, ht_eq, hn_eq, hchk => by
    cases lRem with
    | nil => simp [checkMuxSparsePrefAux] at hchk
    | cons lR lRest =>
      cases tauRem with
      | nil => simp [checkMuxSparsePrefAux] at hchk
      | cons tau9 tauRest =>
        cases nsubRem with
        | nil => simp [checkMuxSparsePrefAux] at hchk
        | cons nSub nsubRest =>
          cases vHist with
          | nil => simp at hvh_len; omega
          | cons vPrev vhRest =>
            dsimp only [checkMuxSparsePrefAux] at hchk
            simp only [msp_forceNat_eq, msp_max_eq_bif, AltForce.withForcedNat_eq,
              AltForce.withForcedList_eq] at hchk
            rw [show Nat.add r 1 = r + 1 from rfl, show Nat.mul lR m = lR * m from rfl] at hchk
            have hvR_eq : vR = vPot.getD r 0 := (by simpa using hv_eq 0 (Nat.succ_pos _))
            have hvPrev_eq : vPrev = vPot.getD (r - 1) 0 := (by simpa using hvh_eq 0 (by omega))
            have hlR_eq : lR = lPref.getD (r - 2) 0 := (by simpa using hl_eq 0 (Nat.succ_pos _))
            have htau_eq : tau9 = tauPref.getD (r - 2) 0 := by simpa using ht_eq 0 (Nat.succ_pos _)
            have hnsub_eq : nSub = nsubPref.getD (r - 2) 0 := by
              simpa using hn_eq 0 (Nat.succ_pos _)
            have hcapR_eq : max vCapPrev vR = muxRunningCap vPot r := by
              rw [hcap, hvR_eq, show r = (r - 1) + 1 by omega]; rfl
            rw [msp_to_beq tau9 0 Nat.beq_eq] at hchk
            revert hchk
            set stepOk : Bool := cond (tau9 == 0) (checkEigStep m r vR vPrev)
                (muxCheckSparseDrift m lTableMax r lR tau9 nSub vR (max vCapPrev vR)
                  (altEvalRowLo12 (lR * m) r tau9 nSub) (vPrev :: vhRest))
            intro hchk
            cases hs_ok : stepOk with
            | false => rw [hs_ok, msp_cond_false] at hchk; exact Bool.noConfusion hchk
            | true =>
              rw [hs_ok, msp_cond_true] at hchk
              have ih := msp_prefAux_props m lTableMax vPot lPref tauPref nsubPref
                vRest (r + 1) (max vCapPrev vR) (vR :: vPrev :: vhRest) lRest tauRest nsubRest
                (by omega) (by rw [show r + 1 - 1 = r by omega]; exact hcapR_eq)
                (by simp [hvh_len]) (fun j hj ↦ by
                  rcases j with _ | j'
                  · rw [List.getD_cons_zero, show r + 1 - 1 - 0 = r by omega]; exact hvR_eq
                  · rw [List.getD_cons_succ, show r + 1 - 1 - (j' + 1) = r - 1 - j' by omega]
                    exact hvh_eq j' (by omega))
                (fun j hj ↦ by
                  have h1 := hv_eq (j + 1) (by simp only [List.length_cons]; omega)
                  simpa [show r + (j + 1) = r + 1 + j by omega] using h1)
                (fun j hj ↦ by
                  have h1 := hl_eq (j + 1) (by simp only [List.length_cons]; omega)
                  simpa [show r - 2 + (j + 1) = r + 1 - 2 + j by omega] using h1)
                (fun j hj ↦ by
                  have h1 := ht_eq (j + 1) (by simp only [List.length_cons]; omega)
                  simpa [show r - 2 + (j + 1) = r + 1 - 2 + j by omega] using h1)
                (fun j hj ↦ by
                  have h1 := hn_eq (j + 1) (by simp only [List.length_cons]; omega)
                  simpa [show r - 2 + (j + 1) = r + 1 - 2 + j by omega] using h1)
                hchk
              refine ⟨by simp [ih.1], by simp [ih.2.1], by simp [ih.2.2.1], fun s hrs hslt ↦ ?_⟩
              by_cases hsr : s = r
              · subst hsr
                rw [← hvR_eq, ← hvPrev_eq, ← hlR_eq, ← htau_eq, ← hnsub_eq]
                dsimp only [stepOk] at hs_ok; refine ⟨fun ht0 ↦ ?_, fun ht_pos ↦ ?_⟩
                · rw [ht0] at hs_ok; simpa [msp_cond_true] using hs_ok
                · have htf : (tau9 == 0) = false :=
                    beq_eq_false_iff_ne.mpr (Nat.ne_of_gt ht_pos)
                  rw [htf, msp_cond_false, hcapR_eq, hvR_eq] at hs_ok
                  exact muxCheckSparseDrift_to_active hvh_eq hs_ok
              · exact ih.2.2.2 s (by omega) (by simp only [List.length_cons] at hslt; omega)
private theorem msp_findAnchor_none (s : ℕ) :
    ∀ (xs : List MuxSparseAnchor), (∀ x ∈ xs, x.rAct ≠ s) → muxFindAnchor s xs = none
  | [], _ => rfl
  | x :: xs, hx => by
    simp only [muxFindAnchor, hx x List.mem_cons_self, ↓reduceIte]
    exact msp_findAnchor_none s xs fun y hy ↦ hx y (List.mem_cons_of_mem x hy)
private theorem msp_tailAux_props (m lTableMax : ℕ) (vPot : List ℕ) :
    ∀ (vRem : List ℕ) (r vCapPrev : ℕ) (vHist : List ℕ) (anchors : List MuxSparseAnchor), 2 ≤ r →
      vCapPrev = muxRunningCap vPot (r - 1) →
      vHist.length = r →
      (∀ j < r, vHist.getD j 0 = vPot.getD (r - 1 - j) 0) →
      (∀ j < vRem.length, vRem.getD j 0 = vPot.getD (r + j) 0) →
      MuxSparseAnchorsSound m anchors →
      checkMuxSparseTailAux m lTableMax vRem r vCapPrev vHist anchors = true →
      (∀ a ∈ anchors, r ≤ a.rAct ∧ a.rAct < r + vRem.length) ∧
      ∀ s : ℕ, r ≤ s → s < r + vRem.length →
        match muxFindAnchor s anchors with
        | none => checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
        | some a =>
            a.rAct = s ∧
            altEvalRowHighDLo12 (a.lR * m) s a.tau9 a.nSub (min (a.lR * m) s) = a.rowLo12 ∧
            MuxSparseActiveValid m lTableMax s vPot a.lR a.tau9 a.nSub a.rowLo12
  | [], _, _, _, anchors, _, _, _, _, _, _, hchk => by
    cases anchors with
    | nil => exact ⟨by simp, fun s hrs hslt ↦ by simp at hslt; omega⟩
    | cons _ _ => simp [checkMuxSparseTailAux] at hchk
  | vR :: vRest, r, vCapPrev, vHist, anchors,
      hr2, hcap, hvh_len, hvh_eq, hv_eq, hsound, hchk => by
    cases vHist with
    | nil => simp at hvh_len; omega
    | cons vPrev vhRest =>
      dsimp only [checkMuxSparseTailAux] at hchk
      simp only [msp_forceNat_eq, msp_max_eq_bif] at hchk
      rw [show Nat.add r 1 = r + 1 from rfl] at hchk
      have hvR_eq : vR = vPot.getD r 0 := (by simpa using hv_eq 0 (Nat.succ_pos _))
      have hvPrev_eq : vPrev = vPot.getD (r - 1) 0 := (by simpa using hvh_eq 0 (by omega))
      have hcapR_eq : max vCapPrev vR = muxRunningCap vPot r := by
        rw [hcap, hvR_eq, show r = (r - 1) + 1 by omega]; rfl
      have hvh_next_eq : ∀ j < r + 1,
          (vR :: vPrev :: vhRest).getD j 0 = vPot.getD (r + 1 - 1 - j) 0 := fun j hj ↦ by
        rcases j with _ | j'
        · rw [List.getD_cons_zero, show r + 1 - 1 - 0 = r by omega]; exact hvR_eq
        · rw [List.getD_cons_succ, show r + 1 - 1 - (j' + 1) = r - 1 - j' by omega]
          exact hvh_eq j' (by omega)
      have hv_next_eq : ∀ j < vRest.length, vRest.getD j 0 = vPot.getD (r + 1 + j) 0 :=
        fun j hj ↦ by
          have h1 := hv_eq (j + 1) (by simp only [List.length_cons]; omega)
          simpa [show r + (j + 1) = r + 1 + j by omega] using h1
      cases anchors with
      | nil =>
        dsimp only at hchk
        cases heig : checkEigStep m r vR vPrev with
        | false => rw [heig, msp_cond_false] at hchk; exact Bool.noConfusion hchk
        | true =>
          rw [heig, msp_cond_true] at hchk
          have ih := msp_tailAux_props m lTableMax vPot vRest (r + 1) (max vCapPrev vR)
            (vR :: vPrev :: vhRest) [] (by omega)
            (by rw [show r + 1 - 1 = r by omega]; exact hcapR_eq)
            (by simp [hvh_len]) hvh_next_eq hv_next_eq trivial hchk
          refine ⟨by simp, fun s hrs hslt ↦ ?_⟩
          by_cases hsr : s = r
          · subst hsr
            dsimp only [muxFindAnchor]; rw [← hvR_eq, ← hvPrev_eq]; exact heig
          · exact ih.2 s (by omega) (by simp only [List.length_cons] at hslt; omega)
      | cons a aRest =>
        dsimp only at hchk
        cases hblt : primNatBlt a.rAct r with
        | true => rw [hblt, msp_cond_true] at hchk; exact Bool.noConfusion hchk
        | false =>
          rw [hblt, msp_cond_false, msp_to_beq a.rAct r Nat.beq_eq] at hchk
          have ha_ge : r ≤ a.rAct := msp_primNatBlt_eq_false.mp hblt
          cases hbeq : (a.rAct == r) with
          | true =>
            rw [hbeq, msp_cond_true] at hchk
            have ha_eq : a.rAct = r := beq_iff_eq.mp hbeq
            cases hdr : muxCheckSparseDrift m lTableMax r a.lR a.tau9 a.nSub vR
                (max vCapPrev vR) a.rowLo12 (vPrev :: vhRest) with
            | false => rw [hdr, msp_cond_false] at hchk; exact Bool.noConfusion hchk
            | true =>
              rw [hdr, msp_cond_true] at hchk
              have ih := msp_tailAux_props m lTableMax vPot vRest (r + 1) (max vCapPrev vR)
                (vR :: vPrev :: vhRest) aRest (by omega)
                (by rw [show r + 1 - 1 = r by omega]; exact hcapR_eq)
                (by simp [hvh_len]) hvh_next_eq hv_next_eq hsound.2 hchk
              refine ⟨fun x hx ↦ ?_, fun s hrs hslt ↦ ?_⟩
              · rcases List.mem_cons.mp hx with rfl | hmem
                · exact ⟨ha_ge, by simp [ha_eq]⟩
                · obtain ⟨h1, h2⟩ := ih.1 x hmem
                  exact ⟨by omega, by simp only [List.length_cons]; omega⟩
              · by_cases hsr : s = r
                · subst hsr
                  have hfind : muxFindAnchor s (a :: aRest) = some a := by
                    simp [muxFindAnchor, ha_eq]
                  rw [hfind]; dsimp only; rw [hcapR_eq, hvR_eq] at hdr
                  refine ⟨ha_eq, ?_, muxCheckSparseDrift_to_active hvh_eq hdr⟩
                  simpa [ha_eq] using hsound.1
                · have hne : a.rAct ≠ s := by omega
                  simp only [muxFindAnchor, hne, ↓reduceIte]
                  exact ih.2 s (by omega) (by simp only [List.length_cons] at hslt; omega)
          | false =>
            rw [hbeq, msp_cond_false] at hchk
            cases heig : checkEigStep m r vR vPrev with
            | false => rw [heig, msp_cond_false] at hchk; exact Bool.noConfusion hchk
            | true =>
              rw [heig, msp_cond_true] at hchk
              have ih := msp_tailAux_props m lTableMax vPot vRest (r + 1) (max vCapPrev vR)
                (vR :: vPrev :: vhRest) (a :: aRest) (by omega)
                (by rw [show r + 1 - 1 = r by omega]; exact hcapR_eq)
                (by simp [hvh_len]) hvh_next_eq hv_next_eq hsound hchk
              refine ⟨fun x hx ↦ ?_, fun s hrs hslt ↦ ?_⟩
              · obtain ⟨h1, h2⟩ := ih.1 x hx
                exact ⟨by omega, by simp only [List.length_cons]; omega⟩
              · by_cases hsr : s = r
                · subst hsr
                  have hnot : ∀ x ∈ (a :: aRest), x.rAct ≠ s := fun x hx ↦ by
                    have hx1 := (ih.1 x hx).1; omega
                  rw [msp_findAnchor_none s (a :: aRest) hnot, ← hvR_eq, ← hvPrev_eq]; exact heig
                · exact ih.2 s (by omega) (by simp only [List.length_cons] at hslt; omega)
private theorem msp_cap_fold (vFull : List ℕ) : ∀ (xs : List ℕ) (r acc : ℕ),
      acc = muxRunningCap vFull (r - 1) →
      (∀ j < xs.length, xs.getD j 0 = vFull.getD (r + j) 0) →
      1 ≤ r →
      xs.foldl max acc = muxRunningCap vFull (r - 1 + xs.length)
  | [], _, acc, hacc, _, _ => by simpa using hacc
  | x :: xs, r, acc, hacc, hx, _ => by
    have hx0 : x = vFull.getD r 0 := (by simpa using hx 0 (Nat.succ_pos _))
    have hacc' : max acc x = muxRunningCap vFull r := by
      rw [hacc, hx0, show r = (r - 1) + 1 by omega]; rfl
    have ih := msp_cap_fold vFull xs (r + 1) (max acc x)
      (by rw [show r + 1 - 1 = r by omega]; exact hacc') (fun j hj ↦ by
        have h1 := hx (j + 1) (by simp only [List.length_cons]; omega)
        simpa [show r + (j + 1) = r + 1 + j by omega] using h1)
      (by omega)
    rw [show r - 1 + (x :: xs).length = r + 1 - 1 + xs.length by
      simp only [List.length_cons]; omega]
    exact ih
/-- Assembles `MuxSparseTableValid` from `checkMuxSparsePref`, `checkMuxSparseTail`, and
  `MuxSparseAnchorsSound`. -/
theorem muxSparseTableValid_of_parts {m kMax lTableMax v0 v1 rSplit vCapSplit : ℕ}
    {vPref vTail vPot vHistSplit lPref tauPref nsubPref : List ℕ} {anchors : List MuxSparseAnchor}
    (hvPot : v0 :: v1 :: (vPref ++ vTail) = vPot) (hlen : vPot.length = kMax + 1)
    (hrSplit : 2 + vPref.length = rSplit) (hcapSplit : vPref.foldl max v1 = vCapSplit)
    (hvhSplit : vPref.reverse ++ [v1, v0] = vHistSplit)
    (hpref : checkMuxSparsePref m kMax lTableMax v0 v1 vPref lPref tauPref nsubPref = true)
    (htail : checkMuxSparseTail m lTableMax rSplit vCapSplit vHistSplit vTail anchors = true)
    (hsound : MuxSparseAnchorsSound m anchors) :
    MuxSparseTableValid m kMax lTableMax vPot lPref tauPref nsubPref anchors := by
  subst hvPot; subst hrSplit; subst hcapSplit; subst hvhSplit
  unfold checkMuxSparsePref at hpref
  cases hg1 : Bool.or (primNatBlt m 1)
      (Bool.or (primNatBlt lTableMax 1) (Bool.or (primNatBlt 8192 (Nat.mul lTableMax m))
      (Bool.or (primNatBlt kMax (Nat.add 2 (altListLen vPref))) (primNatBlt 1024 kMax)))) with
  | true => rw [hg1, msp_cond_true] at hpref; exact Bool.noConfusion hpref
  | false =>
    rw [hg1, msp_cond_false, msp_to_beq v0 0 Nat.beq_eq] at hpref
    simp only [Bool.or_eq_false_iff, msp_primNatBlt_eq_false, msp_altListLen_eq] at hg1
    obtain ⟨hm1, hl1, hl_hi, hk_ge, hk_hi⟩ := hg1
    cases hv0_z : Bool.not (v0 == 0) with
    | true => rw [hv0_z, msp_cond_true] at hpref; exact Bool.noConfusion hpref
    | false =>
      rw [hv0_z, msp_cond_false] at hpref
      simp only [Bool.not_eq_false', beq_iff_eq] at hv0_z
      cases heig1 : checkEigStep m 1 v1 v0 with
      | false => rw [heig1, msp_cond_false] at hpref; exact Bool.noConfusion hpref
      | true =>
        rw [heig1, msp_cond_true] at hpref
        have hv1_ge : v0 ≤ v1 := by
          unfold checkEigStep at heig1
          cases hg : Bool.or (primNatBlt 1 1) (Nat.ble v1 v0) with
          | true => rw [hg, msp_cond_true] at heig1; exact Bool.noConfusion heig1
          | false => simp only [Bool.or_eq_false_iff, msp_nat_ble_eq_false] at hg; exact hg.2.le
        set vFull := v0 :: v1 :: (vPref ++ vTail)
        have hcap1 : v1 = muxRunningCap vFull 1 := by
          change v1 = max v0 v1; exact (Nat.max_eq_right hv1_ge).symm
        have hp_get : ∀ j < vPref.length, vPref.getD j 0 = vFull.getD (2 + j) 0 := fun j hj ↦ by
          simp only [vFull, show 2 + j = j + 1 + 1 by omega, List.getD_cons_succ]
          exact (msp_getD_append_left vPref vTail j hj).symm
        have hp_props := msp_prefAux_props m lTableMax vFull lPref tauPref nsubPref
          vPref 2 v1 [v1, v0] lPref tauPref nsubPref
          (by omega) hcap1 rfl
          (fun j hj ↦ by rcases j with _ | _ | _ <;> first | rfl | omega)
          hp_get
          (fun j _ ↦ by rw [show 2 - 2 + j = j by omega])
          (fun j _ ↦ by rw [show 2 - 2 + j = j by omega])
          (fun j _ ↦ by rw [show 2 - 2 + j = j by omega])
          hpref
        have hcap_split : vPref.foldl max v1 = muxRunningCap vFull (2 + vPref.length - 1) := by
          rw [show 2 + vPref.length - 1 = 2 - 1 + vPref.length by omega]
          exact msp_cap_fold vFull vPref 2 v1 hcap1 hp_get (by omega)
        have hvh_split_eq := msp_rev_append_getD vPref [v1, v0] vFull 2
          (fun j hj ↦ by rcases j with _ | _ | _ <;> first | rfl | omega) hp_get
        have ht_props := msp_tailAux_props m lTableMax vFull vTail (2 + vPref.length)
          (vPref.foldl max v1) (vPref.reverse ++ [v1, v0]) anchors
          (by omega) hcap_split (by simp; omega) hvh_split_eq (fun j _ ↦ by
            simp only [vFull, show 2 + vPref.length + j = (vPref.length + j) + 1 + 1 by omega,
              List.getD_cons_succ]
            rw [msp_getD_append_right vPref vTail (vPref.length + j) (by omega)]
            simp)
          hsound htail
        have htail_len : 2 + vPref.length + vTail.length = kMax + 1 := by
          simp [vFull] at hlen; omega
        have hk_ge' : 2 + lPref.length ≤ kMax := by
          change Nat.add 2 vPref.length ≤ kMax at hk_ge; rw [← hp_props.1]; omega
        refine ⟨hm1, hl1, hl_hi, hk_hi, hlen, hp_props.2.1, hp_props.2.2.1,
          hk_ge', hv0_z, heig1, ?_, ?_⟩
        · intro s hs2 hslt; exact hp_props.2.2.2 s hs2 (by rw [hp_props.1]; exact hslt)
        · intro s hs_ge hs_le; exact ht_props.2 s (by rw [hp_props.1]; exact hs_ge) (by omega)
private theorem msp_checkMuxAnchorLMax_props {k lMaxCell : ℕ} : ∀ {anchors : List MuxSparseAnchor},
      checkMuxAnchorLMax k lMaxCell anchors = true →
      ∀ s : ℕ, s ≤ k → ∀ a : MuxSparseAnchor,
        muxFindAnchor s anchors = some a → 1 ≤ a.lR ∧ a.lR ≤ lMaxCell
  | [], _, _, _, _, hfind => by simp [muxFindAnchor] at hfind
  | b :: rest, hchk, s, hsk, a, hfind => by
    dsimp only [checkMuxAnchorLMax] at hchk
    by_cases hbs : b.rAct = s
    · simp only [muxFindAnchor, hbs, ↓reduceIte, Option.some.injEq] at hfind
      subst hfind
      have hble : Nat.ble b.rAct k = true := msp_nat_ble_eq_true.mpr (hbs ▸ hsk)
      rw [hble, msp_cond_true] at hchk
      cases hok : Bool.not (Bool.or (primNatBlt b.lR 1) (primNatBlt lMaxCell b.lR)) with
      | false => rw [hok, msp_cond_false] at hchk; exact Bool.noConfusion hchk
      | true =>
        simp only [Bool.not_eq_true', Bool.or_eq_false_iff, msp_primNatBlt_eq_false] at hok
        exact hok
    · simp only [muxFindAnchor, hbs, ↓reduceIte] at hfind
      revert hchk
      set ok := cond (Nat.ble b.rAct k)
        (Bool.not (Bool.or (primNatBlt b.lR 1) (primNatBlt lMaxCell b.lR))) true
      intro hchk
      cases hok : ok with
      | false => rw [hok, msp_cond_false] at hchk; exact Bool.noConfusion hchk
      | true =>
        rw [hok, msp_cond_true] at hchk; exact msp_checkMuxAnchorLMax_props hchk s hsk a hfind
private theorem msp_checkAltMuxPrefixLoop_props : ∀ (cnt lMaxCell : ℕ) (lRem : List ℕ),
      checkAltMuxPrefixLoop cnt lMaxCell lRem = true →
      ∀ j < cnt, 1 ≤ lRem.getD j 0 ∧ lRem.getD j 0 ≤ lMaxCell
  | 0, _, _, _, _, hj => by omega
  | cnt + 1, lMaxCell, [], h, _, _ => by simp [checkAltMuxPrefixLoop] at h
  | cnt + 1, lMaxCell, lR :: lRest, h, j, hj => by
    dsimp only [checkAltMuxPrefixLoop] at h
    cases hg : Bool.or (primNatBlt lR 1) (primNatBlt lMaxCell lR) with
    | true => rw [hg, msp_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg, msp_cond_false] at h; simp only [Bool.or_eq_false_iff, msp_primNatBlt_eq_false] at hg
      rcases j with _ | j'
      · exact hg
      · exact msp_checkAltMuxPrefixLoop_props cnt lMaxCell lRest h j' (by omega)
/-- Extracts cell-level `1 ≤ l_r ≤ lMaxCell ≤ lTableMax` bounds from
  `checkMuxSparseCellLMax`. -/
theorem checkMuxSparseCellLMax_props {k lTableMax lMaxCell : ℕ}
    {lPref : List ℕ} {anchors : List MuxSparseAnchor}
    (h : checkMuxSparseCellLMax k lTableMax lMaxCell lPref anchors = true) :
    2 ≤ k ∧ 1 ≤ lMaxCell ∧ lMaxCell ≤ lTableMax ∧ (∀ r : ℕ, 2 ≤ r → r ≤ k → r < 2 + lPref.length →
        1 ≤ lPref.getD (r - 2) 0 ∧ lPref.getD (r - 2) 0 ≤ lMaxCell) ∧
      (∀ r : ℕ, r ≤ k → ∀ a : MuxSparseAnchor,
        muxFindAnchor r anchors = some a → 1 ≤ a.lR ∧ a.lR ≤ lMaxCell) := by
  unfold checkMuxSparseCellLMax at h
  cases hg : Bool.or (primNatBlt k 2)
      (Bool.or (primNatBlt lMaxCell 1) (primNatBlt lTableMax lMaxCell)) with
  | true => rw [hg, msp_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg, msp_cond_false] at h; dsimp only at h
    simp only [Bool.or_eq_false_iff, msp_primNatBlt_eq_false] at hg; obtain ⟨hk2, hl1, hlMax⟩ := hg
    rw [show Nat.sub k 1 = k - 1 from rfl, msp_altListLen_eq, msp_natMin_eq] at h
    cases hp : checkAltMuxPrefixLoop (min (k - 1) lPref.length) lMaxCell lPref with
    | false => rw [hp, msp_cond_false] at h; exact Bool.noConfusion h
    | true =>
      rw [hp, msp_cond_true] at h; have hp_p := msp_checkAltMuxPrefixLoop_props _ lMaxCell lPref hp
      refine ⟨hk2, hl1, hlMax, fun r hr2 hrk hr_lt ↦ ?_, msp_checkMuxAnchorLMax_props h⟩
      exact hp_p (r - 2) (by omega)
/-- Unpacks the head and tail of a certified `muxAllTrue (b:: bs) = true` batch. -/
theorem muxAllTrue_cons {b : Bool} {bs : List Bool} (h : muxAllTrue (b :: bs) = true) :
    b = true ∧ muxAllTrue bs = true := by
  cases b with
  | false => simp [muxAllTrue] at h
  | true => exact ⟨rfl, h⟩
private theorem rkms_cond_true {α : Type} (a b : α) : cond true a b = a := rfl
private theorem rkms_cond_false {α : Type} (a b : α) : cond false a b = b := rfl
private theorem rkms_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem rkms_if_pos {α : Type*} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    @ite α p inst a b = a := by cases inst with | isTrue _ => rfl | isFalse hn => exact absurd h hn
private theorem rkms_if_neg {α : Type*} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    @ite α p inst a b = b := by cases inst with | isTrue hp => exact absurd hp h | isFalse _ => rfl
private theorem rkms_bounds_of_altN0 {n x r : ℕ} (hn : altN0 ≤ n) (hx : x ≤ 8192) (hr : r ≤ 1024) :
    1 ≤ n ∧ 2 * x < 2 ^ n ∧ 2 * x ≤ 2 ^ n ∧ x + r ≤ 2 ^ n := by
  have h15 : 15 ≤ n := le_trans (show 15 ≤ altN0 by unfold altN0; norm_num) hn
  have hp : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h15
  have h2x : 2 * x < 2 ^ n :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 hx) (lt_of_lt_of_le (by norm_num : 2 * 8192 < 2 ^ 15) hp)
  exact ⟨le_trans (by norm_num : 1 ≤ 15) h15, h2x, h2x.le,
    le_trans (Nat.add_le_add hx hr) (le_trans (by norm_num : 8192 + 1024 ≤ 2 ^ 15) hp)⟩
private theorem rkms_primNatBlt_eq_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  unfold primNatBlt
  suffices hble : ∀ {x y : ℕ}, Nat.ble x y = false ↔ y < x by
    rw [hble, Nat.add_eq]; omega
  intro x y
  induction x generalizing y with
  | zero => simp [Nat.ble]
  | succ x ih =>
    cases y with
    | zero => simp [Nat.ble]
    | succ y => simp only [Nat.ble, ih]; omega
private theorem _nbeqF {a b : ℕ} (h : a.beq b = false) : a ≠ b := by
  rintro rfl
  induction a with | zero => exact Bool.noConfusion h | succ _ ih => exact ih h
private theorem _cGuard {b : Bool} {z y : ℕ × ℕ × List ℤ}
    (h : cond b (0, 0, []) z = y) (hy : y.1 ≠ 0) : b = false ∧ z = y := by
  cases b with
  | true => exact False.elim (hy (congrArg Prod.fst h).symm)
  | false => exact ⟨rfl, h⟩
private theorem _cGuardEqNil {α : Type*} {b : Bool} {r z : List α}
    (h : r = cond b [] z) (hr : r ≠ []) : b = false ∧ r = z := by
  cases b with | true => exact False.elim (hr h) | false => exact ⟨rfl, h⟩
private theorem rkms_orbEmbedGen_sub (N M : ℕ) (R : Finset (Fin N)) (x y : Fin (orbDim M R.card) →
    ℝ) : orbEmbedGen N M R (x - y) = orbEmbedGen N M R x - orbEmbedGen N M R y := by
  funext E; simp only [orbEmbedGen, Pi.sub_apply, sub_div]
private theorem rkms_zeroPadOrbVec_sub (M₁ M₂ r : ℕ) (x y : Fin (orbDim M₁ r) → ℝ) : zeroPadOrbVec
    M₁ M₂ r (x - y) = zeroPadOrbVec M₁ M₂ r x - zeroPadOrbVec M₁ M₂ r y := by
  funext u; by_cases hu : u.1 < orbDim M₁ r <;> simp [zeroPadOrbVec, Pi.sub_apply, hu]
private theorem rkms_zeroPadOrbVec_listToOrbVec {M₁ M₂ r : ℕ} {vs : List ℤ} (h12 : M₁ ≤ M₂) (hvs :
    vs.length ≤ min M₁ r + 1) : zeroPadOrbVec M₁ M₂ r (rkmListToOrbVec (min M₁ r) vs) =
    rkmListToOrbVec (min M₂ r) vs := by
  have _ := h12; funext u; unfold zeroPadOrbVec rkmListToOrbVec
  by_cases hu : u.1 < orbDim M₁ r
  · rw [dite_eq_left hu]
  · rw [dite_eq_right hu]
    have hge : vs.length ≤ u.1 := by unfold orbDim at hu; omega
    rw [rkm_getD_eq_zero_of_le vs u.1 hge]; simp
private theorem rkms_finVecNorm_symPrefixKickVec_sub {N M : ℕ} (R : Finset (Fin N)) (j0 : ℕ) (u v :
    SymSubset N M → ℝ) : finVecNorm (symPrefixKickVec R j0 u - symPrefixKickVec R j0 v) =
    finVecNorm (u - v) := by
  have hsub : symPrefixKickVec R j0 u - symPrefixKickVec R j0 v = symPrefixKickVec R j0 (u - v) :=
    by
    funext E; dsimp only [symPrefixKickVec, Pi.sub_apply]; split_ifs <;> ring
  rw [hsub]; unfold finVecNorm finVecSqNorm; rw [sum_sq_symPrefixKickVec]
theorem finVecNorm_evalMuxSymOps_sub {N M : ℕ} (R : Finset (Fin N)) :
    ∀ (ops : List (MuxSymOp N M)) (u v : SymSubset N M → ℝ),
      finVecNorm (evalMuxSymOps R ops u - evalMuxSymOps R ops v) = finVecNorm (u - v)
  | [], _, _ => rfl
  | .walk K D :: rest, u, v => by
    rw [evalMuxSymOps, evalMuxSymOps, finVecNorm_evalMuxSymOps_sub R rest,
      finVecNorm_evalSymStage_sub R D K]
  | .prefixKick j0 :: rest, u, v => by
    rw [evalMuxSymOps, evalMuxSymOps, finVecNorm_evalMuxSymOps_sub R rest,
      rkms_finVecNorm_symPrefixKickVec_sub R j0]
private def rkmApplyKickIdxsOrb (d : ℕ) : List ℕ → (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ)
  | [], x => x
  | j0 :: rest, x =>
      rkmApplyKickIdxsOrb d rest (fun w ↦ (if w.1 ≤ j0 then (-1 : ℝ) else 1) * x w)
private theorem rkms_symPrefixKickVec_orbEmbedGen (N M : ℕ) (R : Finset (Fin N)) (j0 : ℕ) (x : Fin
    (orbDim M R.card) → ℝ) : symPrefixKickVec R j0 (orbEmbedGen N M R x) = orbEmbedGen N M R (fun w
    ↦ (if w.1 ≤ j0 then (-1 : ℝ) else 1) * x w) := by
  funext E; dsimp only [symPrefixKickVec, orbEmbedGen]; split_ifs <;> ring
private theorem rkms_evalMuxSymOps_kicks_orbEmbedGen (N M : ℕ) (R : Finset (Fin N)) :
    ∀ (ks : List ℕ) (x : Fin (orbDim M R.card) → ℝ),
      evalMuxSymOps R (ks.map MuxSymOp.prefixKick) (orbEmbedGen N M R x) =
        orbEmbedGen N M R (rkmApplyKickIdxsOrb (min M R.card) ks x)
  | [], _ => rfl
  | j0 :: rest, x => by
    simp only [List.map_cons, evalMuxSymOps, rkms_symPrefixKickVec_orbEmbedGen]
    exact rkms_evalMuxSymOps_kicks_orbEmbedGen N M R rest _
private theorem rkms_maskKicksDown_mem_le (mask : List Bool) :
    ∀ (k : ℕ) (flip : Bool) (j : ℕ), j ∈ rkmMaskKicksDown mask k flip → j ≤ k
  | 0, flip, j, hj => by
    unfold rkmMaskKicksDown at hj; split_ifs at hj <;> simp at hj; omega
  | k + 1, flip, j, hj => by
    unfold rkmMaskKicksDown at hj
    split_ifs at hj
    · simp only [List.mem_cons] at hj
      rcases hj with rfl | hmem
      · exact le_rfl
      · exact (rkms_maskKicksDown_mem_le mask k (!flip) j hmem).trans (Nat.le_succ k)
    · exact (rkms_maskKicksDown_mem_le mask k flip j hj).trans (Nat.le_succ k)
theorem rkmMaskKicksDown_length_le (mask : List Bool) :
    ∀ (k : ℕ) (flip : Bool), (rkmMaskKicksDown mask k flip).length ≤ k + 1
  | 0, flip => by unfold rkmMaskKicksDown; split_ifs <;> simp
  | k + 1, flip => by
    unfold rkmMaskKicksDown
    split_ifs
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (rkmMaskKicksDown_length_le mask k (!flip))
    · exact (rkmMaskKicksDown_length_le mask k flip).trans (Nat.le_succ _)
private theorem rkms_applyKickIdxsOrb_gt (d : ℕ) :
    ∀ (ks : List ℕ) (x : Fin (d + 1) → ℝ) (w : Fin (d + 1)),
      (∀ j ∈ ks, j < w.1) → rkmApplyKickIdxsOrb d ks x w = x w
  | [], _, _, _ => rfl
  | j0 :: rest, x, w, hgt => by
    unfold rkmApplyKickIdxsOrb
    rw [rkms_applyKickIdxsOrb_gt d rest _ w (fun j hj ↦ hgt j (List.mem_cons_of_mem _ hj))]
    have hnle : ¬ w.1 ≤ j0 := by have := hgt j0 List.mem_cons_self; omega
    simp [hnle]
private theorem rkms_applyKickIdxsOrb_maskKicksDown (d : ℕ) (mask : List Bool) :
    ∀ (k : ℕ) (flip : Bool) (x0 x : Fin (d + 1) → ℝ),
      (∀ w : Fin (d + 1), w.1 ≤ k → x w = (if flip then (-1 : ℝ) else 1) * x0 w) →
      ∀ w : Fin (d + 1), w.1 ≤ k →
        rkmApplyKickIdxsOrb d (rkmMaskKicksDown mask k flip) x w =
          (if mask.getD w.1 false then (-1 : ℝ) else 1) * x0 w
  | 0, flip, x0, x, hx, w, hw => by
    have hw0 : w.1 = 0 := by omega
    have hxw := hx w hw; unfold rkmMaskKicksDown; rw [hw0]; generalize mask.getD 0 false = b0
    cases flip <;> cases b0
    · rw [rkms_if_neg (show rkmBoolXor false false ≠ true by simp [rkmBoolXor])]; exact hxw
    · rw [rkms_if_pos (by rfl : rkmBoolXor false true = true), rkmApplyKickIdxsOrb,
        rkmApplyKickIdxsOrb, rkms_if_pos hw, hxw, rkms_if_neg Bool.false_ne_true,
        rkms_if_pos (@rfl Bool true)]; ring
    · rw [rkms_if_pos (by rfl : rkmBoolXor true false = true), rkmApplyKickIdxsOrb,
        rkmApplyKickIdxsOrb, rkms_if_pos hw, hxw, rkms_if_pos (@rfl Bool true),
        rkms_if_neg Bool.false_ne_true]; ring
    · rw [rkms_if_neg (show rkmBoolXor true true ≠ true by simp [rkmBoolXor])]; exact hxw
  | k + 1, flip, x0, x, hx, w, hw => by
    unfold rkmMaskKicksDown
    by_cases hwk : w.1 ≤ k
    · by_cases hxor : rkmBoolXor flip (mask.getD (k + 1) false) = true
      · rw [rkms_if_pos hxor, rkmApplyKickIdxsOrb]
        exact rkms_applyKickIdxsOrb_maskKicksDown d mask k (!flip) x0 _
          (fun u hu ↦ by
            have hu1 : u.1 ≤ k + 1 := hu.trans (Nat.le_succ k); rw [rkms_if_pos hu1, hx u hu1]
            cases flip
            · rw [rkms_if_neg Bool.false_ne_true,
                rkms_if_pos (by rfl : (!false) = true)]; ring
            · rw [rkms_if_pos (@rfl Bool true),
                rkms_if_neg (show (!true) ≠ true by simp)]; ring) w hwk
      · rw [rkms_if_neg hxor]
        exact rkms_applyKickIdxsOrb_maskKicksDown d mask k flip x0 x
          (fun u hu ↦ hx u (hu.trans (Nat.le_succ k))) w hwk
    · have hweq : w.1 = k + 1 := by omega
      have hxw := hx w hw
      have hgt_sub (fl' : Bool) : ∀ j ∈ rkmMaskKicksDown mask k fl', j < w.1 := fun j hj ↦ by
        have := rkms_maskKicksDown_mem_le mask k fl' j hj; omega
      rw [hweq]; generalize mask.getD (k + 1) false = bk1
      cases flip <;> cases bk1
      · rw [rkms_if_neg (show rkmBoolXor false false ≠ true by simp [rkmBoolXor]),
          rkms_applyKickIdxsOrb_gt d _ _ w (hgt_sub false)]; exact hxw
      · rw [rkms_if_pos (by rfl : rkmBoolXor false true = true), rkmApplyKickIdxsOrb,
          rkms_applyKickIdxsOrb_gt d _ _ w (hgt_sub (!false)), rkms_if_pos hw, hxw,
          rkms_if_neg Bool.false_ne_true, rkms_if_pos (@rfl Bool true)]; ring
      · rw [rkms_if_pos (by rfl : rkmBoolXor true false = true), rkmApplyKickIdxsOrb,
          rkms_applyKickIdxsOrb_gt d _ _ w (hgt_sub (!true)), rkms_if_pos hw, hxw,
          rkms_if_pos (@rfl Bool true), rkms_if_neg Bool.false_ne_true]; ring
      · rw [rkms_if_neg (show rkmBoolXor true true ≠ true by simp [rkmBoolXor]),
          rkms_applyKickIdxsOrb_gt d _ _ w (hgt_sub true)]; exact hxw
private theorem rkms_evalMuxSymOps_walk_cons {N M : ℕ} (R : Finset (Fin N)) (K : ℕ) (D :
    SymOrthogonal N M) (rest : List (MuxSymOp N M)) (v : SymSubset N M → ℝ) : evalMuxSymOps R
    (.walk K D :: rest) v = evalMuxSymOps R rest (evalSymStage R D.1 K v) := rfl
private theorem rkms_ofSymmInvolution_val {N M : ℕ} (D : Matrix (SymSubset N M) (SymSubset N M) ℝ)
    (hsym : Dᵀ = D) (hinv : D * D = 1) : (SymOrthogonal.ofSymmInvolution D hsym hinv).1 = D := rfl
private theorem rkms_evalWalkAndKicks_orbEmbedGen {N M r K : ℕ} {D : SymOrthogonal N M} (hD : D.1 =
    dAltSymMat N M) {R : Finset (Fin N)} (hR : R.card = r) (hmrN : M + R.card ≤ N) (mask : List
    Bool) (uIn : Fin (orbDim M R.card) → ℝ) : evalMuxSymOps R (MuxSymOp.walk K D ::
    (rkmMaskKicksDown mask (min M r) false).map MuxSymOp.prefixKick) (orbEmbedGen N M R uIn) =
    orbEmbedGen N M R (rkmMaskSignVec (min M R.card) mask (((dAltStepOrbMat N M R.card) ^ K) *ᵥ
    uIn)) := by
  subst hR; rw [rkms_evalMuxSymOps_walk_cons, hD, evalSymStage_dAltSymMat_orbEmbedGen hmrN K uIn,
    rkms_evalMuxSymOps_kicks_orbEmbedGen]
  apply congrArg (orbEmbedGen N M R); funext w; unfold rkmMaskSignVec
  exact rkms_applyKickIdxsOrb_maskKicksDown (min M R.card) mask (min M R.card) false _ _
    (fun _ _ ↦ by rw [rkms_if_neg Bool.false_ne_true, one_mul]) w (Nat.lt_succ_iff.mp w.2)
private theorem rkms_evalSegOps_orbEmbedGen {n m r lS tau9 nSub : ℕ} {mask : List Bool} (hn : altN0
    ≤ n) (hm_hi : lS * m ≤ 8192) (hr_hi : r ≤ 1024) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    (uIn : Fin (orbDim (lS * m) R.card) → ℝ) : evalMuxSymOps R (rkmSegOps n m r lS tau9 nSub mask)
    (orbEmbedGen (2 ^ n) (lS * m) R uIn) = orbEmbedGen (2 ^ n) (lS * m) R (rkmMaskSignVec (min (lS
    * m) R.card) mask (((dAltStepOrbMat (2 ^ n) (lS * m) R.card) ^ altStepCount tau9 nSub (2 ^ n))
    *ᵥ uIn)) := by
  subst hR; obtain ⟨hn1, h2x_lt, _, hmrN⟩ := rkms_bounds_of_altN0 hn hm_hi hr_hi
  have hhm : 1 ≤ n ∧ 2 * (lS * m) < 2 ^ n := ⟨hn1, h2x_lt⟩; unfold rkmSegOps; rw [dite_eq_left hhm]
  exact rkms_evalWalkAndKicks_orbEmbedGen (rkms_ofSymmInvolution_val _ _ _) rfl hmrN mask uIn
private theorem rkms_muxOpsQueryCount_kicks {N M : ℕ} :
    ∀ ks : List ℕ, muxOpsQueryCount (N := N) (M := M) (ks.map MuxSymOp.prefixKick) = 2 * ks.length
  | [] => rfl
  | _ :: ks => by
    simp only [List.map_cons, muxOpsQueryCount, List.length_cons, rkms_muxOpsQueryCount_kicks ks]
    omega
theorem rkmSegOps_queryCount_le (n m r lS tau9 nSub : ℕ) (mask : List Bool) :
    (muxOpsQueryCount (rkmSegOps n m r lS tau9 nSub mask) : ℝ) ≤
      ((tau9 : ℝ) / 1000000000) * √(2 ^ n : ℝ) + (2 * (r + 1) : ℝ) := by
  unfold rkmSegOps
  split_ifs with hm
  · dsimp only [muxOpsQueryCount]
    rw [rkms_muxOpsQueryCount_kicks]
    have hkl : (rkmMaskKicksDown mask (min (lS * m) r) false).length ≤ r + 1 :=
      (rkmMaskKicksDown_length_le mask _ false).trans
        (by have := Nat.min_le_right (lS * m) r; omega)
    have hnat : altStepCount tau9 nSub (2 ^ n) +
        2 * (rkmMaskKicksDown mask (min (lS * m) r) false).length ≤
        altStepCount tau9 nSub (2 ^ n) + 2 * (r + 1) := by omega
    have hcast : ((altStepCount tau9 nSub (2 ^ n) + 2 * (rkmMaskKicksDown mask (min (lS * m) r)
      false).length : ℕ) : ℝ) ≤ (altStepCount tau9 nSub (2 ^ n) : ℝ) + (2 * (r + 1) : ℝ) := by
      exact (Nat.cast_le.mpr hnat).trans_eq (by push_cast; ring)
    have hstep : (altStepCount tau9 nSub (2 ^ n) : ℝ) ≤ ((tau9 : ℝ) / 1000000000) * √(2 ^ n : ℝ) :=
      by
      simpa [Nat.cast_pow, Nat.cast_ofNat] using altStepCount_le_tau_sqrt tau9 nSub (2 ^ n)
    linarith
  · simp only [muxOpsQueryCount, Nat.cast_zero]
    positivity
private theorem rkms_segOps_mul_queryCount_le (n m r lTableMax l0 t0 s0 : ℕ) (mk0 : List Bool) (hl0
    : l0 ≤ lTableMax) : (l0 : ℝ) * (muxOpsQueryCount (rkmSegOps n m r l0 t0 s0 mk0) : ℝ) ≤ (((l0 *
    t0 : ℕ) : ℝ) / 1000000000) * √(2 ^ n : ℝ) + 2 * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) := by
  have h0 := rkmSegOps_queryCount_le n m r l0 t0 s0 mk0
  have h1 := mul_le_mul_of_nonneg_left h0 (Nat.cast_nonneg l0)
  have hl0R : (l0 : ℝ) ≤ (lTableMax : ℝ) := Nat.cast_le.mpr hl0
  have h1_eq : (l0 : ℝ) * (((t0 : ℝ) / 1000000000) * √(2 ^ n : ℝ) + (2 * (r + 1) : ℝ)) =
      (((l0 * t0 : ℕ) : ℝ) / 1000000000) * √(2 ^ n : ℝ) +
        2 * (l0 : ℝ) * ((r + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h1_eq] at h1
  have hmul_le : 2 * (l0 : ℝ) * ((r + 1 : ℕ) : ℝ) ≤
      2 * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg (r + 1))
  linarith
private theorem rkms_segsQueryCount_nil_le (n m r lTableMax l0 t0 s0 : ℕ) (mk0 : List Bool) (lRest
    tauRest nsubRest : List ℕ) (maskRest : List (List Bool)) (hl0 : l0 ≤ lTableMax) (hnil :
    rkmBuildTailSegs n m r lRest tauRest nsubRest maskRest = []) : (rkmSegsQueryCount l0 (rkmSegOps
    n m r l0 t0 s0 mk0) (rkmBuildTailSegs n m r lRest tauRest nsubRest maskRest) : ℝ) ≤
    ((rkmWeightedTau9 (l0 :: lRest) (t0 :: tauRest) : ℝ) / 1000000000) * √(2 ^ n : ℝ) + (2 * ((l0
    :: lRest).length : ℝ) * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ)) := by
  rw [hnil, rkmSegsQueryCount, Nat.cast_mul]
  have hm0 := rkms_segOps_mul_queryCount_le n m r lTableMax l0 t0 s0 mk0 hl0
  have hw_ge : l0 * t0 ≤ rkmWeightedTau9 (l0 :: lRest) (t0 :: tauRest) := by
    dsimp only [rkmWeightedTau9, Nat.add_eq, Nat.mul_eq]; omega
  have hwR : ((l0 * t0 : ℕ) : ℝ) ≤ (rkmWeightedTau9 (l0 :: lRest) (t0 :: tauRest) : ℝ) :=
    Nat.cast_le.mpr hw_ge
  have htau_le : (((l0 * t0 : ℕ) : ℝ) / 1000000000) * √(2 ^ n : ℝ) ≤
      ((rkmWeightedTau9 (l0 :: lRest) (t0 :: tauRest) : ℝ) / 1000000000) * √(2 ^ n : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hlen1 : (1 : ℝ) ≤ ((l0 :: lRest).length : ℝ) := by
    simp only [List.length_cons]; exact_mod_cast Nat.succ_pos lRest.length
  have hprod_nn : (0 : ℝ) ≤ 2 * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) := by positivity
  have hlen_le : 1 * (2 * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ)) ≤
      ((l0 :: lRest).length : ℝ) * (2 * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hlen1 hprod_nn
  have hcomm : ((l0 :: lRest).length : ℝ) * (2 * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ)) =
      2 * ((l0 :: lRest).length : ℝ) * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) := by ring
  linarith
theorem rkmSegsQueryCount_build_le (n m r lTableMax : ℕ) :
    ∀ (l0 t0 s0 : ℕ) (mk0 : List Bool)
      (lRest tauRest nsubRest : List ℕ) (maskRest : List (List Bool)),
      l0 ≤ lTableMax →
      (∀ lS ∈ lRest, lS ≤ lTableMax) →
      (rkmSegsQueryCount l0 (rkmSegOps n m r l0 t0 s0 mk0)
        (rkmBuildTailSegs n m r lRest tauRest nsubRest maskRest) : ℝ) ≤
        ((rkmWeightedTau9 (l0 :: lRest) (t0 :: tauRest) : ℝ) / 1000000000) * √(2 ^ n : ℝ) +
          (2 * ((l0 :: lRest).length : ℝ) * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ)) := by
  intro l0 t0 s0 mk0 lRest
  induction lRest generalizing l0 t0 s0 mk0 with
  | nil =>
    intro tauRest nsubRest maskRest hl0 _
    exact rkms_segsQueryCount_nil_le n m r lTableMax l0 t0 s0 mk0 [] tauRest nsubRest maskRest
      hl0 rfl
  | cons l1 lRest ih =>
    intro tauRest nsubRest maskRest hl0 hall
    rcases tauRest with _ | ⟨t1, tauRest⟩
    · exact rkms_segsQueryCount_nil_le n m r lTableMax l0 t0 s0 mk0 (l1 :: lRest) []
        nsubRest maskRest hl0 rfl
    · rcases nsubRest with _ | ⟨s1, nsubRest⟩
      · exact rkms_segsQueryCount_nil_le n m r lTableMax l0 t0 s0 mk0 (l1 :: lRest)
          (t1 :: tauRest) [] maskRest hl0 rfl
      · rcases maskRest with _ | ⟨mk1, maskRest⟩
        · exact rkms_segsQueryCount_nil_le n m r lTableMax l0 t0 s0 mk0 (l1 :: lRest)
            (t1 :: tauRest) (s1 :: nsubRest) [] hl0 rfl
        · dsimp only [rkmBuildTailSegs, rkmSegsQueryCount]
          have hl1 : l1 ≤ lTableMax := hall l1 List.mem_cons_self
          have hrec := ih l1 t1 s1 mk1 tauRest nsubRest maskRest hl1
            (fun x hx ↦ hall x (List.mem_cons_of_mem _ hx))
          have hm0 := rkms_segOps_mul_queryCount_le n m r lTableMax l0 t0 s0 mk0 hl0
          have hw_cons : rkmWeightedTau9 (l0 :: l1 :: lRest) (t0 :: t1 :: tauRest) =
              l0 * t0 + rkmWeightedTau9 (l1 :: lRest) (t1 :: tauRest) := rfl
          rw [Nat.cast_add, Nat.cast_mul]
          exact (add_le_add hm0 hrec).trans_eq
            (by rw [hw_cons]; simp only [List.length_cons]; push_cast; ring)
private theorem rkms_loop_guard_head {m lTableMax r lS tau9 nSub : ℕ} {mask : List Bool} {lRest
    tauRest nsubRest : List ℕ} {maskRest : List (List Bool)} {lPrev dPrev accPad dOut padOut : ℕ}
    {vec vecOut : List ℤ} (hres : rkmEvalSegsLoop m lTableMax r (lS :: lRest) (tau9 :: tauRest)
    (nSub :: nsubRest) (mask :: maskRest) lPrev dPrev accPad vec = (dOut, padOut, vecOut)) (hdOut :
    dOut ≠ 0) : 1 ≤ lS ∧ lPrev ≤ lS ∧ lS ≤ lTableMax ∧ 1 ≤ lS * m ∧ lS * m ≤ 8192 := by
  unfold rkmEvalSegsLoop at hres; dsimp only at hres
  obtain ⟨hg1, _⟩ := _cGuard hres hdOut
  simp only [Bool.or_eq_false_iff, rkms_primNatBlt_eq_false] at hg1
  exact ⟨hg1.1, hg1.2.1, hg1.2.2.1, hg1.2.2.2.1, hg1.2.2.2.2.1⟩
private theorem rkms_evalSegsLoop_sound {n m lTableMax r : ℕ}
    (hn : altN0 ≤ n) (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024)
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r) :
    ∀ (lRest : List ℕ) (l0 t0 s0 : ℕ) (mk0 : List Bool)
      (tauRest nsubRest : List ℕ) (maskRest : List (List Bool))
      (lPrev dPrev accPad dOut padOut : ℕ) (vec vecOut : List ℤ)
      (v : SymSubset (2 ^ n) (l0 * m) → ℝ)
      (uIn : Fin (orbDim (l0 * m) R.card) → ℝ),
      vecNorm uIn ≤ 1 →
      vec.length ≤ min (l0 * m) R.card + 1 →
      finVecNorm (v - orbEmbedGen (2 ^ n) (l0 * m) R uIn) +
        vecNorm (uIn - rkmListToOrbVec (min (l0 * m) R.card) vec) ≤
          ((accPad : ℝ) + 1) / wdScaleR →
      rkmEvalSegsLoop m lTableMax r (l0 :: lRest) (t0 :: tauRest) (s0 :: nsubRest)
        (mk0 :: maskRest) lPrev dPrev accPad vec = (dOut, padOut, vecOut) →
      dOut ≠ 0 →
      padOut ≠ 0 →
      let segs := rkmBuildTailSegs n m r lRest tauRest nsubRest maskRest
      let lEnd := rkmEndL l0 segs
      1 ≤ l0 ∧ lPrev ≤ l0 ∧ l0 ≤ lTableMax ∧
        rkmSegsMono l0 segs ∧
        lEnd ≤ lTableMax ∧ lEnd * m ≤ 8192 ∧
        dOut = min (lEnd * m) r ∧
        vecOut.length ≤ dOut + 1 ∧
        ∃ uFinal : Fin (orbDim (lEnd * m) R.card) → ℝ,
          finVecNorm (rkmEvalSegs R l0 (rkmSegOps n m r l0 t0 s0 mk0) segs v -
              orbEmbedGen (2 ^ n) (lEnd * m) R uFinal) +
            vecNorm (uFinal - rkmListToOrbVec (min (lEnd * m) R.card) vecOut) ≤
              (padOut : ℝ) / wdScaleR := by
  subst hR
  intro lRest
  induction lRest with
  | nil =>
    intro l0 t0 s0 mk0 tauRest nsubRest maskRest lPrev _dPrev accPad dOut padOut
      vec vecOut v uIn huIn hvec herr hres hdOut _hpadOut
    have hB_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
    obtain ⟨hl0_1, hlPrev, hl0_max, hm0_1, hm0_hi⟩ := rkms_loop_guard_head hres hdOut
    unfold rkmEvalSegsLoop at hres; dsimp only at hres
    simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at hres
    obtain ⟨hg1, hres⟩ := _cGuard hres hdOut
    simp only [Bool.or_eq_false_iff, rkms_primNatBlt_eq_false] at hg1
    have ht0_pos : 0 < t0 := Nat.pos_of_ne_zero (_nbeqF hg1.2.2.2.2.2.2.1)
    have ht0_hi : t0 ≤ 4000000000 := hg1.2.2.2.2.2.2.2.1
    have hs0_pos : 0 < s0 := Nat.pos_of_ne_zero (_nbeqF hg1.2.2.2.2.2.2.2.2.1)
    have hs0_hi : s0 ≤ 16384 := hg1.2.2.2.2.2.2.2.2.2.1
    set hPt := Nat.div (Nat.mul t0 1000000) s0
    cases ghPt : primNatBlt hPt 1 with
    | true => rw [ghPt, rkms_cond_true] at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
    | false =>
      rw [ghPt, rkms_cond_false] at hres; set d0 := highdNatMin (Nat.mul l0 m) R.card
      have hd0_eq : d0 = min (l0 * m) R.card := rkmb_natMin_eq (l0 * m) R.card
      set maxB := altMaxBHiFrom (Nat.mul l0 m) R.card 0 d0
      set bCap := Nat.mul 2 maxB; set hgHi := highdMulCeil15 (Nat.add 2 hPt) bCap
      cases ghg : Bool.or (primNatBlt 1500000000000000 hgHi)
          (Bool.not (altCheckHbTight (Nat.mul l0 m) R.card 0 d0)) with
      | true => rw [ghg, rkms_cond_true] at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
      | false =>
        rw [ghg, rkms_cond_false] at hres
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkms_primNatBlt_eq_false] at ghg
        set hgPow := altPow17Ceil15 hgHi
        have hhgPow_eq : altPow17Ceil15 (highdMulCeil15 (2 + (t0 * 1000000) / s0) (2 *
          altMaxBHiFrom (l0 * m) R.card 0 (min (l0 * m) R.card))) = hgPow := by
          dsimp only [hgPow, hgHi, bCap, maxB, hPt]
          simp only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq]
        clear_value hgPow
        set truncPad := Nat.div (Nat.add 299999999999999 (Nat.mul s0 hgPow)) 300000000000000
        set bCapCeil := Nat.div (Nat.add 999999999999999 bCap) wdScale
        set segPad := Nat.add (Nat.add truncPad 256)
          (Nat.mul s0 (Nat.add 256 (Nat.mul 10 bCapCeil)))
        set nextPad := Nat.add accPad segPad
        replace hres := (_cGuard hres hdOut).2
        set hbPt := altBuildHbFrom (Nat.mul l0 m) R.card hPt 0 d0
        set vWalk := muxFastIterFullT16 s0 (Nat.add d0 1) hbPt vec
        have hvWalk_eq : muxFastIterFullT16 s0 (min (l0 * m) R.card + 1) (altBuildHbFrom (l0 *
          m) R.card ((t0 * 1000000) / s0) 0 (min (l0 * m) R.card)) vec = vWalk := by
          dsimp only [vWalk, hbPt, hPt]
          simp only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq]
        clear_value vWalk; set vNext := rkmApplyMaskBits mk0 vWalk
        rcases tauRest with _ | ⟨_, _⟩
        · rcases nsubRest with _ | ⟨_, _⟩
          · rcases maskRest with _ | ⟨_, _⟩
            · unfold rkmEvalSegsLoop at hres
              rcases Prod.mk.inj hres with ⟨rfl, hres2⟩
              rcases Prod.mk.inj hres2 with ⟨rfl, rfl⟩
              have hseg := rkmSingleSegT16_bound (mask := mk0) hn hm0_1 hm0_hi hr2 hr_hi
                ht0_pos ht0_hi hs0_pos hs0_hi
                (by dsimp only [hgHi, hPt, bCap, maxB] at ghg
                    simpa only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq] using ghg.1)
                (by simpa only [hd0_eq, Nat.mul_eq] using ghg.2) hvec huIn
              dsimp only at hseg; rw [hhgPow_eq, hvWalk_eq] at hseg
              obtain ⟨uOut, _, hvNext_len_raw, hseg_bd_raw⟩ := hseg
              have hvNext_len : vNext.length ≤ d0 + 1 := by rw [hd0_eq]; exact hvNext_len_raw
              have hmrN : l0 * m + R.card ≤ 2 ^ n :=
                (rkms_bounds_of_altN0 hn hm0_hi hr_hi).2.2.2
              let ops0 := rkmSegOps n m R.card l0 t0 s0 mk0
              let vIdeal := evalMuxSymOps R ops0 (orbEmbedGen (2 ^ n) (l0 * m) R uIn)
              have hvIdeal : vIdeal = orbEmbedGen (2 ^ n) (l0 * m) R
                  (rkmMaskSignVec (min (l0 * m) R.card) mk0
                    (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^
                      altStepCount t0 s0 (2 ^ n)) *ᵥ uIn)) :=
                rkms_evalSegOps_orbEmbedGen hn hm0_hi hr_hi rfl uIn
              have hseg_eq : ((299999999999999 + s0 * hgPow) / 300000000000000 + 256) + s0 *
                (256 + 10 * ((999999999999999 + 2 * altMaxBHiFrom (l0 * m) R.card 0 (min (l0 *
                m) R.card)) / wdScale)) = segPad := by
                dsimp only [segPad, truncPad, bCapCeil, bCap, maxB]
                simp only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq]
              have hseg_bd : vecNorm (rkmMaskSignVec (min (l0 * m) R.card) mk0
                (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^ altStepCount t0 s0 (2 ^ n)) *ᵥ
                uIn) - uOut) + vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) vNext) ≤
                vecNorm (uIn - rkmListToOrbVec (min (l0 * m) R.card) vec) + ((segPad : ℝ) -
                253) / wdScaleR := by
                rw [hseg_eq] at hseg_bd_raw; exact hseg_bd_raw
              generalize (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^
                  altStepCount t0 s0 (2 ^ n)) *ᵥ uIn) = uWalk0 at hvIdeal hseg_bd
              have hq1 : finVecNorm (evalMuxSymOps R ops0 v - vIdeal) =
                  finVecNorm (v - orbEmbedGen (2 ^ n) (l0 * m) R uIn) :=
                finVecNorm_evalMuxSymOps_sub R ops0 v _
              have hq2 : finVecNorm (vIdeal - orbEmbedGen (2 ^ n) (l0 * m) R uOut) = vecNorm
                (rkmMaskSignVec (min (l0 * m) R.card) mk0 uWalk0 - uOut) := by
                rw [hvIdeal, ← rkms_orbEmbedGen_sub, finVecNorm_orbEmbedGen hmrN]
              have htri : finVecNorm (evalMuxSymOps R ops0 v - orbEmbedGen (2 ^ n) (l0 * m) R
                uOut) ≤ finVecNorm (evalMuxSymOps R ops0 v - vIdeal) + finVecNorm (vIdeal -
                orbEmbedGen (2 ^ n) (l0 * m) R uOut) := by
                rw [(sub_add_sub_cancel _ vIdeal _).symm]; exact finVecNorm_add_le _ _
              refine ⟨hl0_1, hlPrev, hl0_max, trivial, hl0_max, hm0_hi, hd0_eq, hvNext_len,
                uOut, ?_⟩
              have hnpR : (nextPad : ℝ) = (accPad : ℝ) + (segPad : ℝ) := by
                change ((accPad + segPad : ℕ) : ℝ) = _; push_cast; rfl
              have hsum_le : ((accPad : ℝ) + 1) / wdScaleR + ((segPad : ℝ) - 253) / wdScaleR ≤
                (nextPad : ℝ) / wdScaleR := by
                rw [← add_div, hnpR]; exact div_le_div_of_nonneg_right (by linarith) hB_pos.le
              change finVecNorm (evalMuxSymOps R ops0 v -
                    orbEmbedGen (2 ^ n) (l0 * m) R uOut) +
                  vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) vNext) ≤
                (nextPad : ℝ) / wdScaleR
              linarith [htri, hq1, hq2, hseg_bd, herr, hsum_le]
            · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
          · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
        · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
  | cons l1 lRest2 ih =>
    intro l0 t0 s0 mk0 tauRest nsubRest maskRest lPrev _dPrev accPad dOut padOut
      vec vecOut v uIn huIn hvec herr hres hdOut hpadOut
    have hB_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
    obtain ⟨hl0_1, hlPrev, hl0_max, hm0_1, hm0_hi⟩ := rkms_loop_guard_head hres hdOut
    unfold rkmEvalSegsLoop at hres; dsimp only at hres
    simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at hres
    obtain ⟨hg1, hres⟩ := _cGuard hres hdOut
    simp only [Bool.or_eq_false_iff, rkms_primNatBlt_eq_false] at hg1
    have ht0_pos : 0 < t0 := Nat.pos_of_ne_zero (_nbeqF hg1.2.2.2.2.2.2.1)
    have ht0_hi : t0 ≤ 4000000000 := hg1.2.2.2.2.2.2.2.1
    have hs0_pos : 0 < s0 := Nat.pos_of_ne_zero (_nbeqF hg1.2.2.2.2.2.2.2.2.1)
    have hs0_hi : s0 ≤ 16384 := hg1.2.2.2.2.2.2.2.2.2.1
    set hPt := Nat.div (Nat.mul t0 1000000) s0
    cases ghPt : primNatBlt hPt 1 with
    | true => rw [ghPt, rkms_cond_true] at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
    | false =>
      rw [ghPt, rkms_cond_false] at hres; set d0 := highdNatMin (Nat.mul l0 m) R.card
      have hd0_eq : d0 = min (l0 * m) R.card := rkmb_natMin_eq (l0 * m) R.card
      set maxB := altMaxBHiFrom (Nat.mul l0 m) R.card 0 d0
      set bCap := Nat.mul 2 maxB; set hgHi := highdMulCeil15 (Nat.add 2 hPt) bCap
      cases ghg : Bool.or (primNatBlt 1500000000000000 hgHi)
          (Bool.not (altCheckHbTight (Nat.mul l0 m) R.card 0 d0)) with
      | true => rw [ghg, rkms_cond_true] at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
      | false =>
        rw [ghg, rkms_cond_false] at hres
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkms_primNatBlt_eq_false] at ghg
        set hgPow := altPow17Ceil15 hgHi
        have hhgPow_eq : altPow17Ceil15 (highdMulCeil15 (2 + (t0 * 1000000) / s0) (2 *
          altMaxBHiFrom (l0 * m) R.card 0 (min (l0 * m) R.card))) = hgPow := by
          dsimp only [hgPow, hgHi, bCap, maxB, hPt]
          simp only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq]
        clear_value hgPow
        set truncPad := Nat.div (Nat.add 299999999999999 (Nat.mul s0 hgPow)) 300000000000000
        set bCapCeil := Nat.div (Nat.add 999999999999999 bCap) wdScale
        set segPad := Nat.add (Nat.add truncPad 256)
          (Nat.mul s0 (Nat.add 256 (Nat.mul 10 bCapCeil)))
        set nextPad := Nat.add accPad segPad
        replace hres := (_cGuard hres hdOut).2
        set hbPt := altBuildHbFrom (Nat.mul l0 m) R.card hPt 0 d0
        set vWalk := muxFastIterFullT16 s0 (Nat.add d0 1) hbPt vec
        have hvWalk_eq : muxFastIterFullT16 s0 (min (l0 * m) R.card + 1) (altBuildHbFrom (l0 *
          m) R.card ((t0 * 1000000) / s0) 0 (min (l0 * m) R.card)) vec = vWalk := by
          dsimp only [vWalk, hbPt, hPt]
          simp only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq]
        clear_value vWalk; set vNext := rkmApplyMaskBits mk0 vWalk
        rcases tauRest with _ | ⟨t1, tRest2⟩
        · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
        · rcases nsubRest with _ | ⟨s1, sRest2⟩
          · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
          · rcases maskRest with _ | ⟨mk1, mkRest2⟩
            · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdOut
            · obtain ⟨_, hl01, _, _, hm1_hi⟩ := rkms_loop_guard_head hres hdOut
              have hseg := rkmSingleSegT16_bound (mask := mk0) hn hm0_1 hm0_hi hr2 hr_hi
                ht0_pos ht0_hi hs0_pos hs0_hi
                (by dsimp only [hgHi, hPt, bCap, maxB] at ghg
                    simpa only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq] using ghg.1)
                (by simpa only [hd0_eq, Nat.mul_eq] using ghg.2) hvec huIn
              dsimp only at hseg; rw [hhgPow_eq, hvWalk_eq] at hseg
              obtain ⟨uOut, huOut, hvNext_len, hseg_bd_raw⟩ := hseg
              have hseg_eq : ((299999999999999 + s0 * hgPow) / 300000000000000 + 256) + s0 *
                (256 + 10 * ((999999999999999 + 2 * altMaxBHiFrom (l0 * m) R.card 0 (min (l0 *
                m) R.card)) / wdScale)) = segPad := by
                dsimp only [segPad, truncPad, bCapCeil, bCap, maxB]
                simp only [hd0_eq, Nat.add_eq, Nat.mul_eq, rkms_div_eq]
              have hseg_bd : vecNorm (rkmMaskSignVec (min (l0 * m) R.card) mk0
                (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^ altStepCount t0 s0 (2 ^ n)) *ᵥ
                uIn) - uOut) + vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) vNext) ≤
                vecNorm (uIn - rkmListToOrbVec (min (l0 * m) R.card) vec) + ((segPad : ℝ) -
                253) / wdScaleR := by
                rw [hseg_eq] at hseg_bd_raw; exact hseg_bd_raw
              have hmrN0 : l0 * m + R.card ≤ 2 ^ n :=
                (rkms_bounds_of_altN0 hn hm0_hi hr_hi).2.2.2
              let ops0 := rkmSegOps n m R.card l0 t0 s0 mk0; set v1 := evalMuxSymOps R ops0 v
              let vIdeal := evalMuxSymOps R ops0 (orbEmbedGen (2 ^ n) (l0 * m) R uIn)
              have hvIdeal : vIdeal = orbEmbedGen (2 ^ n) (l0 * m) R
                  (rkmMaskSignVec (min (l0 * m) R.card) mk0
                    (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^
                      altStepCount t0 s0 (2 ^ n)) *ᵥ uIn)) :=
                rkms_evalSegOps_orbEmbedGen hn hm0_hi hr_hi rfl uIn
              generalize (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^
                  altStepCount t0 s0 (2 ^ n)) *ᵥ uIn) = uWalk0 at hvIdeal hseg_bd
              have hq1 : finVecNorm (v1 - vIdeal) =
                  finVecNorm (v - orbEmbedGen (2 ^ n) (l0 * m) R uIn) :=
                finVecNorm_evalMuxSymOps_sub R ops0 v _
              have hq2 : finVecNorm (vIdeal - orbEmbedGen (2 ^ n) (l0 * m) R uOut) = vecNorm
                (rkmMaskSignVec (min (l0 * m) R.card) mk0 uWalk0 - uOut) := by
                rw [hvIdeal, ← rkms_orbEmbedGen_sub, finVecNorm_orbEmbedGen hmrN0]
              have htri0 : finVecNorm (v1 - orbEmbedGen (2 ^ n) (l0 * m) R uOut) ≤ finVecNorm
                (v1 - vIdeal) + finVecNorm (vIdeal - orbEmbedGen (2 ^ n) (l0 * m) R uOut) := by
                rw [(sub_add_sub_cancel _ vIdeal _).symm]; exact finVecNorm_add_le _ _
              have hnpR : (nextPad : ℝ) = (accPad : ℝ) + (segPad : ℝ) := by
                change ((accPad + segPad : ℕ) : ℝ) = _; push_cast; rfl
              have herr_after0 : finVecNorm (v1 - orbEmbedGen (2 ^ n) (l0 * m) R uOut) +
                vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) vNext) ≤ ((nextPad : ℝ) -
                252) / wdScaleR := by
                have hsum_le : ((accPad : ℝ) + 1) / wdScaleR + ((segPad : ℝ) - 253) / wdScaleR
                  = ((nextPad : ℝ) - 252) / wdScaleR := by
                  rw [← add_div, hnpR]; ring
                linarith [htri0, hq1, hq2, hseg_bd, herr, hsum_le]
              have hvNext_len1 : vNext.length ≤ min (l1 * m) R.card + 1 :=
                hvNext_len.trans (by
                  have hmul : l0 * m ≤ l1 * m := Nat.mul_le_mul_right m hl01
                  have hmin : min (l0 * m) R.card ≤ min (l1 * m) R.card :=
                    le_min ((Nat.min_le_left _ _).trans hmul) (Nat.min_le_right _ _)
                  omega)
              by_cases hEq : l0 = l1
              · subst hEq
                have herr1 : finVecNorm (v1 - orbEmbedGen (2 ^ n) (l0 * m) R uOut) +
                    vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) vNext) ≤
                    ((nextPad : ℝ) + 1) / wdScaleR :=
                  herr_after0.trans (div_le_div_of_nonneg_right (by linarith) hB_pos.le)
                have hih := ih l0 t1 s1 mk1 tRest2 sRest2 mkRest2 l0 d0 nextPad
                  dOut padOut vNext vecOut v1 uOut huOut hvNext_len herr1 hres hdOut hpadOut
                obtain ⟨_, _, _, hmono2, hlEnd_max, hlEnd_hi, hdOut_eq, hvOut_len,
                  uFinal, hfin⟩ := hih
                refine ⟨hl0_1, hlPrev, hl0_max, ⟨le_rfl, hmono2⟩, hlEnd_max, hlEnd_hi,
                  hdOut_eq, hvOut_len, uFinal, ?_⟩
                dsimp only [rkmBuildTailSegs, rkmEndL, rkmEvalSegs]
                rw [dite_eq_left rfl]; exact hfin
              · have hM01 : l0 * m ≤ l1 * m := Nat.mul_le_mul_right m hl01
                have h2M1_N : 2 * (l1 * m) ≤ 2 ^ n :=
                  (rkms_bounds_of_altN0 hn hm1_hi hr_hi).2.2.1
                set v2 := stepUpFrom (2 ^ n) (l0 * m) (l1 * m) *ᵥ v1
                set uIn1 := zeroPadOrbVec (l0 * m) (l1 * m) R.card uOut
                have huIn1_norm : vecNorm uIn1 ≤ 1 := by
                  rw [vecNorm_zeroPadOrbVec hM01]; exact huOut
                set vUp := stepUpFrom (2 ^ n) (l0 * m) (l1 * m) *ᵥ
                  orbEmbedGen (2 ^ n) (l0 * m) R uOut
                have hiso : finVecNorm (v2 - vUp) = finVecNorm (v1 - orbEmbedGen (2 ^ n) (l0 *
                  m) R uOut) := by
                  dsimp only [v2, vUp]; rw [← Matrix.mulVec_sub,
                    finVecNorm_mulVec_of_transpose_mul_self
                      (stepUpFrom_transpose_mul_self hM01 h2M1_N)]
                have hstepUp := finVecNorm_stepUpFrom_orbEmbedGen_sub_le hn hm0_1 hM01 hm1_hi
                  (le_trans (by omega : 1 ≤ 2) hr2) hr_hi uOut
                have hstepUp_half : finVecNorm (vUp - orbEmbedGen (2 ^ n) (l1 * m) R uIn1) ≤ (1
                  / 2) / wdScaleR := by
                  have h1 : (1 / (2 * (wdScale : ℝ))) * vecNorm uOut ≤
                      (1 / (2 * (wdScale : ℝ))) * 1 :=
                    mul_le_mul_of_nonneg_left huOut (by unfold wdScale; positivity)
                  exact hstepUp.trans (h1.trans_eq (by unfold wdScaleR; ring))
                have htri_v2 : finVecNorm (v2 - orbEmbedGen (2 ^ n) (l1 * m) R uIn1) ≤
                  finVecNorm (v1 - orbEmbedGen (2 ^ n) (l0 * m) R uOut) + (1 / 2) / wdScaleR :=
                  by
                  have htr := finVecNorm_add_le (v2 - vUp)
                    (vUp - orbEmbedGen (2 ^ n) (l1 * m) R uIn1)
                  rw [sub_add_sub_cancel] at htr; linarith [htr, hiso, hstepUp_half]
                have hpad_orb : vecNorm (uIn1 - rkmListToOrbVec (min (l1 * m) R.card) vNext) =
                  vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) vNext) := by
                  dsimp only [uIn1]; rw [← rkms_zeroPadOrbVec_listToOrbVec hM01 hvNext_len,
                    ← rkms_zeroPadOrbVec_sub, vecNorm_zeroPadOrbVec hM01]
                have herr1 : finVecNorm (v2 - orbEmbedGen (2 ^ n) (l1 * m) R uIn1) + vecNorm
                  (uIn1 - rkmListToOrbVec (min (l1 * m) R.card) vNext) ≤ ((nextPad : ℝ) + 1) /
                  wdScaleR := by
                  have hsum : ((nextPad : ℝ) - 252) / wdScaleR + (1 / 2) / wdScaleR ≤ ((nextPad
                    : ℝ) + 1) / wdScaleR := by
                    rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hB_pos.le
                  linarith [htri_v2, hpad_orb, herr_after0, hsum]
                have hih := ih l1 t1 s1 mk1 tRest2 sRest2 mkRest2 l0 d0 nextPad
                  dOut padOut vNext vecOut v2 uIn1 huIn1_norm hvNext_len1 herr1
                  hres hdOut hpadOut
                obtain ⟨_, _, _, hmono2, hlEnd_max, hlEnd_hi, hdOut_eq, hvOut_len,
                  uFinal, hfin⟩ := hih
                refine ⟨hl0_1, hlPrev, hl0_max, ⟨hl01, hmono2⟩, hlEnd_max, hlEnd_hi,
                  hdOut_eq, hvOut_len, uFinal, ?_⟩
                dsimp only [rkmBuildTailSegs, rkmEndL, rkmEvalSegs]
                rw [dite_eq_right hEq]; exact hfin
/-- Main quantum hit-probability soundness theorem for `rkmEvalT16Lo12`: whenever
  `rkmEvalT16Lo12`
  returns a non-empty row `rowOut`, the multi-segment `MuxSymOp` + `stepUpFrom` state
  satisfies the
  `10 ^ 12`-scaled hit-probability lower bound at every `1 ≤ w ≤ min (l_end * m) r`. -/
theorem rkmEvalT16Lo12_sound {n m lTableMax r : ℕ}
    {lSegs tauSegs nsubSegs : List ℕ} {masks : List (List Bool)}
    (hn : altN0 ≤ n)
    (hne : rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks ≠ [])
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r) :
    let l0 := lSegs.headD 1
    let ops0 := rkmSegOps n m r l0 (tauSegs.headD 0) (nsubSegs.headD 0) (masks.headD [])
    let segs := rkmBuildTailSegs n m r lSegs.tail tauSegs.tail nsubSegs.tail masks.tail
    let lEnd := rkmEndL l0 segs
    let rowOut := rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks
    1 ≤ l0 ∧ rkmSegsMono l0 segs ∧ lEnd ≤ lTableMax ∧ lEnd * m ≤ 8192 ∧
      rowOut.length = min (lEnd * m) r ∧
      (∀ w ∈ Finset.Icc 1 (min (lEnd * m) r),
        ((rowOut.getD (w - 1) 0 : ℝ) / 1000000000000) ≤
          symHitProb R (rkmEvalSegs R l0 ops0 segs (u0Vec (2 ^ n) (l0 * m))) w) := by
  intro l0 ops0 segs lEnd rowOut
  have hrow_ne : rowOut ≠ [] := hne
  have hrow_def : rowOut = rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks := rfl
  clear_value rowOut; unfold rkmEvalT16Lo12 at hrow_def; dsimp only at hrow_def
  rw [rkmb_altListLen_eq] at hrow_def
  obtain ⟨hg0, hrow_def⟩ := _cGuardEqNil hrow_def hrow_ne
  simp only [Bool.or_eq_false_iff, rkms_primNatBlt_eq_false] at hg0
  obtain ⟨hlen_b, _, hr2, hr_hi⟩ := hg0
  have hlen_ne := _nbeqF hlen_b
  rcases hres : rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks
      1 0 0 [Int.ofNat wdScale] with ⟨dEnd, accPad, vecFinal⟩
  rw [hres] at hrow_def; dsimp only at hrow_def
  obtain ⟨hgEnd, hrow_def⟩ := _cGuardEqNil hrow_def hrow_ne
  simp only [Bool.or_eq_false_iff] at hgEnd
  have hdEnd_ne := _nbeqF hgEnd.1; have hacc_ne := _nbeqF hgEnd.2
  rcases lSegs with _ | ⟨lh, lt⟩
  · exact absurd rfl hlen_ne
  · rcases tauSegs with _ | ⟨th, tt⟩
    · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdEnd_ne
    · rcases nsubSegs with _ | ⟨sh, st⟩
      · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdEnd_ne
      · rcases masks with _ | ⟨mkh, mkt⟩
        · unfold rkmEvalSegsLoop at hres; exact absurd (Prod.mk.inj hres).1.symm hdEnd_ne
        · obtain ⟨hlh1, _, _, hmh1, hmh_hi⟩ := rkms_loop_guard_head hres hdEnd_ne
          subst hR; let z0 : Fin (orbDim (lh * m) R.card) := ⟨0, Nat.succ_pos _⟩
          let e0 : Fin (orbDim (lh * m) R.card) → ℝ := Pi.single z0 1
          have he0_norm : vecNorm e0 ≤ 1 := by
            refine le_of_eq ?_; unfold vecNorm vecSqNorm; rw [Finset.sum_eq_single z0]
            · dsimp [e0]; rw [Pi.single_eq_same, one_pow, Real.sqrt_one]
            · intro b _ hb; dsimp [e0]; rw [Pi.single_eq_of_ne hb, zero_pow two_ne_zero]
            · intro hz; exact absurd (Finset.mem_univ z0) hz
          have he0_list : e0 = rkmListToOrbVec (min (lh * m) R.card) [Int.ofNat wdScale] := by
            funext ⟨j, hj⟩; rcases j with _ | j'
            · change e0 z0 = _; dsimp [e0]; rw [Pi.single_eq_same]
              unfold rkmListToOrbVec wdScaleR wdScale; norm_num
            · have hne_z : (⟨j' + 1, hj⟩ : Fin (orbDim (lh * m) R.card)) ≠ z0 :=
                fun h ↦ Nat.succ_ne_zero j' (congrArg Fin.val h)
              dsimp only [e0]; unfold rkmListToOrbVec; rw [Pi.single_eq_of_ne hne_z]; simp
          have hmrNh : lh * m + R.card ≤ 2 ^ n :=
            (rkms_bounds_of_altN0 hn hmh_hi hr_hi).2.2.2
          have hu0_err : finVecNorm (u0Vec (2 ^ n) (lh * m) - orbEmbedGen (2 ^ n) (lh * m) R
            e0) + vecNorm (e0 - rkmListToOrbVec (min (lh * m) R.card) [Int.ofNat wdScale]) ≤
            (((0 : ℕ) : ℝ) + 1) / wdScaleR := by
            rw [← he0_list, sub_self, vecNorm_zero, add_zero,
              ← orbEmbedGen_u0OrbVecGen hmrNh, ← rkms_orbEmbedGen_sub,
              finVecNorm_orbEmbedGen hmrNh]
            have hb := vecNorm_u0OrbVecGen_sub_e0_le hn hmh1 hmh_hi
              (le_trans (by omega : 1 ≤ 2) hr2) hr_hi
            dsimp only at hb; exact hb.trans (by unfold wdScaleR wdScale; norm_num)
          have hloop := rkms_evalSegsLoop_sound hn hr2 hr_hi rfl lt lh th sh mkh
            tt st mkt 1 0 0 dEnd accPad [Int.ofNat wdScale] vecFinal
            (u0Vec (2 ^ n) (lh * m)) e0 he0_norm (by simp) hu0_err hres hdEnd_ne hacc_ne
          obtain ⟨_, _, _, hmono, hlEnd_max, hlEnd_hi, hdEnd_eq, hvOut_len,
            uFinal, htot_err⟩ := hloop
          subst hdEnd_eq; simp only [Nat.add_eq] at hrow_def
          have hmrN_end : rkmEndL lh (rkmBuildTailSegs n m R.card lt tt st mkt) * m +
              R.card ≤ 2 ^ n := (rkms_bounds_of_altN0 hn hlEnd_hi hr_hi).2.2.2
          dsimp only [l0, ops0, segs, lEnd, List.headD_cons, List.tail_cons]
          refine ⟨hlh1, hmono, hlEnd_max, hlEnd_hi, ?_⟩
          set vEnd := rkmEvalSegs R lh (rkmSegOps n m R.card lh th sh mkh)
            (rkmBuildTailSegs n m R.card lt tt st mkt) (u0Vec (2 ^ n) (lh * m))
          have htail_first := rkmPadTailToLo12_sound (w := 1) (sProb := 0)
            le_rfl hvOut_len le_rfl htot_err
          dsimp only at htail_first; rw [← hrow_def] at htail_first
          refine ⟨htail_first.1, fun w hw ↦ ?_⟩
          rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
          let wFin : Fin (orbDim (rkmEndL lh
            (rkmBuildTailSegs n m R.card lt tt st mkt) * m) R.card) :=
            ⟨w, Nat.lt_succ_of_le hwd⟩
          have htail := rkmPadTailToLo12_sound (w := w)
            (sProb := √(symHitProb R vEnd w)) hw1 hvOut_len (Real.sqrt_nonneg _) htot_err
          dsimp only at htail; rw [← hrow_def] at htail
          have hprob_ideal : √(symHitProb R (orbEmbedGen (2 ^ n) _ R uFinal) w) = |uFinal wFin|
            := by
            have hp := symHitProb_orbEmbedGen hmrN_end uFinal wFin
            dsimp only [wFin] at hp; rw [hp, Real.sqrt_sq_eq_abs]
          have hprob_ge := sqrt_symHitProb_ge_of_finVecNorm_sub_le R
            (orbEmbedGen (2 ^ n) _ R uFinal) vEnd w
          rw [hprob_ideal] at hprob_ge
          have hle_sq := htail.2 wFin rfl hprob_ge
            (by rw [htail.1]; exact Nat.sub_lt_left_of_lt_add hw1
                  (by rw [Nat.add_comm]; exact Nat.lt_succ_of_le hwd))
          rwa [Real.sq_sqrt (by unfold symHitProb; positivity)] at hle_sq
private theorem rkme_cond_true {α : Type} (a b : α) : cond true a b = a := rfl
private theorem rkme_cond_false {α : Type} (a b : α) : cond false a b = b := rfl

private theorem rkme_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkme_nat_ble_eq_true]

private theorem rkme_primNatBlt_eq_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  unfold primNatBlt; rw [rkme_nat_ble_eq_true, Nat.add_eq]; omega

private theorem rkme_primNatBlt_eq_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, rkme_primNatBlt_eq_true]; omega

private theorem rkme_bool_eq {u v : Bool} (h : (u = true) = (v = true)) : u = v := by
  cases u <;> cases v <;> simp at h ⊢

private theorem rkme_to_beq (a b : ℕ) {u : Bool} (h : (u = true) = (a = b)) :
    u = (a == b) :=
  rkme_bool_eq (h.trans (Nat.beq_eq_true_eq a b).symm)

private theorem rkme_max_eq_bif (a b : ℕ) :
    cond (primNatBlt a b) b a = max a b := by
  cases h : primNatBlt a b
  · exact (Nat.max_eq_left (rkme_primNatBlt_eq_false.mp h)).symm
  · exact (Nat.max_eq_right (rkme_primNatBlt_eq_true.mp h).le).symm

theorem rkmCheckSegBounds_mem_le (lTableMax : ℕ) :
    ∀ (lSegs tauSegs : List ℕ) (lPrev : ℕ),
      rkmCheckSegBounds lTableMax lSegs tauSegs lPrev = true →
      ∀ lS ∈ lSegs, 1 ≤ lS ∧ lS ≤ lTableMax
  | [], [], _, _, _, hl => nomatch hl
  | lS :: lRest, tS :: tRest, lPrev, hchk, x, hx => by
    unfold rkmCheckSegBounds at hchk
    cases hg : Bool.or (primNatBlt lS 1)
        (Bool.or (primNatBlt lS lPrev)
        (Bool.or (primNatBlt lTableMax lS)
        (Bool.or (primNatBlt tS 1) (primNatBlt 4000000000 tS)))) with
    | true => rw [hg, rkme_cond_true] at hchk; exact Bool.noConfusion hchk
    | false =>
      rw [hg, rkme_cond_false] at hchk
      simp only [Bool.or_eq_false_iff, rkme_primNatBlt_eq_false] at hg
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hmem
      · exact ⟨hg.1, hg.2.2.1⟩
      · exact rkmCheckSegBounds_mem_le lTableMax lRest tRest lS hchk x hmem
  | _ :: _, [], _, hchk, _, _ => by simp [rkmCheckSegBounds] at hchk
  | [], _ :: _, _, hchk, _, _ => by simp [rkmCheckSegBounds] at hchk

theorem rkmLastNat_eq_endL (n m r : ℕ) :
    ∀ (lRest : List ℕ) (l0 : ℕ) (tauRest nsubRest : List ℕ) (maskRest : List (List Bool)),
      lRest.length = tauRest.length →
      lRest.length = nsubRest.length →
      lRest.length = maskRest.length →
      rkmLastNat l0 lRest =
        rkmEndL l0 (rkmBuildTailSegs n m r lRest tauRest nsubRest maskRest)
  | [], _, _, _, _, _, _, _ => rfl
  | l1 :: lRest, _, _t1 :: tauRest, _s1 :: nsubRest, _mk1 :: maskRest, ht, hs, hm => by
    dsimp only [rkmLastNat, rkmBuildTailSegs, rkmEndL]
    exact rkmLastNat_eq_endL n m r lRest l1 tauRest nsubRest maskRest
      (by simpa using ht) (by simpa using hs) (by simpa using hm)
  | _ :: _, _, [], _, _, ht, _, _ => by simp at ht
  | _ :: _, _, _ :: _, [], _, _, hs, _ => by simp at hs
  | _ :: _, _, _ :: _, _ :: _, [], _, _, hm => by simp at hm

private theorem rkme_checkDrift_to_active {m lTableMax s : ℕ}
    {lSegs tauSegs vPot rowLo12 vHist : List ℕ}
    (hvh_eq : ∀ j < s, vHist.getD j 0 = vPot.getD (s - 1 - j) 0)
    (h : rkmCheckDrift m lTableMax s lSegs tauSegs (vPot.getD s 0)
      (muxRunningCap vPot s) rowLo12 vHist = true) :
    RampKickActiveValid m lTableMax s vPot lSegs tauSegs rowLo12 := by
  unfold RampKickActiveValid
  dsimp only
  unfold rkmCheckDrift at h
  dsimp only at h
  rw [rkmb_altListLen_eq lSegs] at h
  cases hg1 : Bool.or (primNatBlt lSegs.length 1)
      (Bool.or (primNatBlt 8 lSegs.length)
      (Bool.or (primNatBlt (muxRunningCap vPot s) (vPot.getD s 0))
        (Bool.not (rkmCheckSegBounds lTableMax lSegs tauSegs 1)))) with
  | true => rw [hg1, rkme_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg1, rkme_cond_false] at h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkme_primNatBlt_eq_false] at hg1
    obtain ⟨hn1, hn8, _, hseg_bds⟩ := hg1
    set lEnd := rkmLastNat 0 lSegs
    rw [show Nat.mul lEnd m = lEnd * m from rfl, rkmb_natMin_eq (lEnd * m) s] at h
    set dEnd := min (lEnd * m) s
    rw [rkme_to_beq (altListLen rowLo12) dEnd Nat.beq_eq] at h
    cases hg2 : Bool.or (Bool.not (altListLen rowLo12 == dEnd))
        (Bool.or (primNatBlt (altSumNat rowLo12) 1)
        (Bool.or (primNatBlt 1000000000000 (altSumNat rowLo12))
          (primNatBlt (altListLen vHist) dEnd))) with
    | true => rw [hg2, rkme_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg2, rkme_cond_false] at h
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', beq_iff_eq,
        rkme_primNatBlt_eq_false, rkmb_altListLen_eq] at hg2
      obtain ⟨hr_len, htot1, htot_le, hvh_ge⟩ := hg2
      have hlt := rkme_primNatBlt_eq_true.mp h
      rw [muxHitValSum27_eq_sum_range dEnd rowLo12 vHist hr_len hvh_ge] at hlt
      have hsum_eq :
          (∑ j ∈ Finset.range dEnd, rowLo12.getD j 0 * vHist.getD j 0) =
            ∑ j ∈ Finset.range dEnd, rowLo12.getD j 0 * vPot.getD (s - 1 - j) 0 := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hj_lt : j < s := (Finset.mem_range.mp hj).trans_le (Nat.min_le_right _ _)
        rw [hvh_eq j hj_lt]
      rw [hsum_eq] at hlt
      refine ⟨hn1, hn8, hseg_bds, hr_len, htot1, htot_le, ?_⟩
      simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ← add_assoc] at hlt
      exact hlt

private theorem rkme_findAnchor_none_of_gt :
    ∀ (anchors : List RampKickAnchor) (s : ℕ),
      (∀ a ∈ anchors, s < a.rAct) → rkmFindAnchor s anchors = none
  | [], _, _ => rfl
  | a :: rest, s, hgt => by
    have hsa : a.rAct ≠ s := by have := hgt a List.mem_cons_self; omega
    unfold rkmFindAnchor
    rw [ite_eq_right hsa]
    exact rkme_findAnchor_none_of_gt rest s (fun b hb ↦ hgt b (List.mem_cons_of_mem _ hb))

private theorem rkme_checkTableAux_gt :
    ∀ (vRem : List ℕ) (m lTableMax : ℕ) (useColdR2 : Bool)
      (r vCapPrev : ℕ) (vHist : List ℕ) (anchors : List RampKickAnchor),
      rkmCheckTableAux m lTableMax useColdR2 vRem r vCapPrev vHist anchors = true →
      ∀ a ∈ anchors, r ≤ a.rAct
  | [], _, _, _, _, _, _, anchors, h, a, ha => by
    cases anchors with
    | nil => nomatch ha
    | cons _ _ => simp [rkmCheckTableAux] at h
  | vR :: vRest, m, lTableMax, useColdR2, r, vCapPrev, vHist, anchors, h, b, hb => by
    cases vHist with
    | nil => simp [rkmCheckTableAux] at h
    | cons vPrev vhRest =>
      unfold rkmCheckTableAux at h
      simp only [rkmb_forceNat_eq] at h
      cases anchors with
      | nil => nomatch hb
      | cons a aRest =>
        dsimp only at h
        rw [rkme_to_beq a.rAct r Nat.beq_eq, rkme_to_beq r 2 Nat.beq_eq] at h
        cases hlt : primNatBlt a.rAct r with
        | true => rw [hlt, rkme_cond_true] at h; exact Bool.noConfusion h
        | false =>
          rw [hlt, rkme_cond_false] at h
          have hra : r ≤ a.rAct := rkme_primNatBlt_eq_false.mp hlt
          cases heq : (a.rAct == r) with
          | true =>
            rw [heq, rkme_cond_true] at h
            cases hdr : rkmCheckDrift m lTableMax r a.lSegs a.tauSegs vR _ a.rowLo12
                (vPrev :: vhRest) with
            | false => rw [hdr, rkme_cond_false] at h; exact Bool.noConfusion h
            | true =>
              rw [hdr, rkme_cond_true] at h
              simp only [List.mem_cons] at hb
              rcases hb with rfl | hmem
              · exact hra
              · exact (Nat.le_succ r).trans
                  (rkme_checkTableAux_gt vRest m lTableMax useColdR2 (r + 1) _ _ aRest h b hmem)
          | false =>
            rw [heq, rkme_cond_false] at h
            cases hfb : cond (Bool.and (r == 2) useColdR2) (rkmCheckColdR2Step m vR)
                (checkEigStep m r vR vPrev) with
            | false => rw [hfb, rkme_cond_false] at h; exact Bool.noConfusion h
            | true =>
              rw [hfb, rkme_cond_true] at h
              exact (Nat.le_succ r).trans
                (rkme_checkTableAux_gt vRest m lTableMax useColdR2 (r + 1) _ _
                  (a :: aRest) h b hb)

private theorem rkme_checkTableAux_props (m lTableMax : ℕ) (useColdR2 : Bool) (vPot : List ℕ) :
    ∀ (vRem : List ℕ) (r : ℕ) (vHist : List ℕ) (anchors : List RampKickAnchor),
      1 ≤ r →
      vHist.getD 0 0 = vPot.getD (r - 1) 0 →
      1 ≤ vHist.length →
      (∀ j < r, vHist.getD j 0 = vPot.getD (r - 1 - j) 0) →
      (∀ j < vRem.length, vRem.getD j 0 = vPot.getD (r + j) 0) →
      RampKickAnchorsSound m lTableMax anchors →
      rkmCheckTableAux m lTableMax useColdR2 vRem r (muxRunningCap vPot (r - 1)) vHist
        anchors = true →
      ∀ s : ℕ, r ≤ s → s < r + vRem.length →
        match rkmFindAnchor s anchors with
        | none =>
            (s = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨
              checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
        | some a =>
            a.rAct = s ∧
            rkmEvalT16Lo12 m lTableMax s a.lSegs a.tauSegs a.nsubSegs a.masks = a.rowLo12 ∧
            RampKickActiveValid m lTableMax s vPot a.lSegs a.tauSegs a.rowLo12
  | [], r, _, _, _, _, _, _, _, _, _, s, hrs, hslt => by simp at hslt; omega
  | vR :: vRest, r, vHist, anchors, hr1, hvh0, hvh_len, hvh_eq, hvrem_eq, hasound, hchk,
      s, hrs, hslt => by
    rcases vHist with _ | ⟨vPrev, vhRest⟩
    · simp at hvh_len
    · have hvR_eq : vR = vPot.getD r 0 := by simpa using hvrem_eq 0 (Nat.succ_pos _)
      have hvPrev_eq : vPrev = vPot.getD (r - 1) 0 := by simpa using hvh0
      have hcap_eq : max (muxRunningCap vPot (r - 1)) vR = muxRunningCap vPot r := by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp [muxRunningCap, hvR_eq]
      have hvh_next : ∀ j < r + 1, (vR :: vPrev :: vhRest).getD j 0 = vPot.getD (r - j) 0 := by
        intro j hj
        rcases j with _ | j'
        · simp [hvR_eq]
        · rw [List.getD_cons_succ, hvh_eq j' (by omega)]
          congr 1; omega
      have hvrem_next : ∀ j < vRest.length, vRest.getD j 0 = vPot.getD (r + 1 + j) 0 := by
        intro j hj
        have h1 := hvrem_eq (j + 1) (by simp; omega)
        simpa [show r + (j + 1) = r + 1 + j by omega] using h1
      unfold rkmCheckTableAux at hchk
      simp only [rkmb_forceNat_eq, rkme_max_eq_bif, hcap_eq] at hchk
      rw [rkme_to_beq r 2 Nat.beq_eq] at hchk
      have hfb_prop :
          cond (Bool.and (r == 2) useColdR2) (rkmCheckColdR2Step m vR)
            (checkEigStep m r vR vPrev) = true →
          (r = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨
            checkEigStep m r (vPot.getD r 0) (vPot.getD (r - 1) 0) = true := by
        intro hfb
        cases hcond : Bool.and (r == 2) useColdR2 with
        | true =>
          rw [hcond, rkme_cond_true] at hfb
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨rfl, huc⟩
          exact Or.inl ⟨rfl, huc, by simpa [hvR_eq] using hfb⟩
        | false =>
          rw [hcond, rkme_cond_false] at hfb
          exact Or.inr (by simpa [hvR_eq, hvPrev_eq] using hfb)
      rcases anchors with _ | ⟨a, aRest⟩
      · dsimp only at hchk
        cases hfb : cond (Bool.and (r == 2) useColdR2) (rkmCheckColdR2Step m vR)
            (checkEigStep m r vR vPrev) with
        | false => rw [hfb, rkme_cond_false] at hchk; exact Bool.noConfusion hchk
        | true =>
          rw [hfb, rkme_cond_true] at hchk
          by_cases hsr : s = r
          · subst hsr; simpa [rkmFindAnchor] using hfb_prop hfb
          · have hih := rkme_checkTableAux_props m lTableMax useColdR2 vPot vRest (r + 1)
              (vR :: vPrev :: vhRest) [] (by omega)
              (by simp [hvR_eq]) (by simp)
              (fun j hj ↦ by simpa [Nat.add_sub_cancel] using hvh_next j hj)
              hvrem_next trivial
              (by simpa [Nat.add_sub_cancel, show Nat.add r 1 = r + 1 from rfl] using hchk)
              s (by omega) (by simp only [List.length_cons] at hslt; omega)
            exact hih
      · dsimp only at hchk
        cases hlt : primNatBlt a.rAct r with
        | true => rw [hlt, rkme_cond_true] at hchk; exact Bool.noConfusion hchk
        | false =>
          rw [hlt, rkme_cond_false, rkme_to_beq a.rAct r Nat.beq_eq] at hchk
          cases heq : (a.rAct == r) with
          | true =>
            rw [heq, rkme_cond_true] at hchk
            have har_eq : a.rAct = r := beq_iff_eq.mp heq
            cases hdr : rkmCheckDrift m lTableMax r a.lSegs a.tauSegs vR (muxRunningCap vPot r)
                a.rowLo12 (vPrev :: vhRest) with
            | false => rw [hdr, rkme_cond_false] at hchk; exact Bool.noConfusion hchk
            | true =>
              rw [hdr, rkme_cond_true] at hchk
              obtain ⟨ha_eval, hrest_sound⟩ := hasound
              by_cases hsr : s = r
              · subst hsr
                unfold rkmFindAnchor; rw [ite_eq_left har_eq]; dsimp only
                rw [hvR_eq] at hdr
                rw [har_eq] at ha_eval
                exact ⟨har_eq, ha_eval, rkme_checkDrift_to_active hvh_eq hdr⟩
              · have hgt : r < s := by omega
                have hne_as : a.rAct ≠ s := by omega
                unfold rkmFindAnchor; rw [ite_eq_right hne_as]
                exact rkme_checkTableAux_props m lTableMax useColdR2 vPot vRest (r + 1)
                  (vR :: vPrev :: vhRest) aRest (by omega)
                  (by simp [hvR_eq]) (by simp)
                  (fun j hj ↦ by simpa [Nat.add_sub_cancel] using hvh_next j hj)
                  hvrem_next hrest_sound
                  (by simpa [Nat.add_sub_cancel, show Nat.add r 1 = r + 1 from rfl] using hchk)
                  s hgt (by simp only [List.length_cons] at hslt; omega)
          | false =>
            rw [heq, rkme_cond_false] at hchk
            cases hfb : cond (Bool.and (r == 2) useColdR2) (rkmCheckColdR2Step m vR)
                (checkEigStep m r vR vPrev) with
            | false => rw [hfb, rkme_cond_false] at hchk; exact Bool.noConfusion hchk
            | true =>
              rw [hfb, rkme_cond_true] at hchk
              by_cases hsr : s = r
              · subst hsr
                have hall_gt : ∀ b ∈ a :: aRest, s < b.rAct := fun b hb ↦ by
                  have hge := rkme_checkTableAux_gt vRest m lTableMax useColdR2 (s + 1) _ _
                    (a :: aRest) (by simpa [show Nat.add s 1 = s + 1 from rfl] using hchk) b hb
                  omega
                rw [rkme_findAnchor_none_of_gt (a :: aRest) s hall_gt]
                exact hfb_prop hfb
              · exact rkme_checkTableAux_props m lTableMax useColdR2 vPot vRest (r + 1)
                  (vR :: vPrev :: vhRest) (a :: aRest) (by omega)
                  (by simp [hvR_eq]) (by simp)
                  (fun j hj ↦ by simpa [Nat.add_sub_cancel] using hvh_next j hj)
                  hvrem_next hasound
                  (by simpa [Nat.add_sub_cancel, show Nat.add r 1 = r + 1 from rfl] using hchk)
                  s (by omega) (by simp only [List.length_cons] at hslt; omega)

/-- Turns `rkmCheckTable... = true` and `RampKickAnchorsSound` into `RampKickTableValid`. -/
theorem rkmCheckTable_sound {m kMax lTableMax : ℕ} {useColdR2 : Bool}
    {vPot : List ℕ} {anchors : List RampKickAnchor}
    (hchk : rkmCheckTable m kMax lTableMax useColdR2 vPot anchors = true)
    (hsound : RampKickAnchorsSound m lTableMax anchors) :
    RampKickTableValid m kMax lTableMax useColdR2 vPot anchors := by
  unfold rkmCheckTable at hchk
  rw [rkmb_altListLen_eq, rkme_to_beq vPot.length (Nat.add kMax 1) Nat.beq_eq] at hchk
  cases hg1 : Bool.or (primNatBlt m 1)
      (Bool.or (primNatBlt lTableMax 1)
      (Bool.or (primNatBlt 8192 (Nat.mul lTableMax m))
      (Bool.or (primNatBlt kMax 2)
      (Bool.or (primNatBlt 1024 kMax)
        (Bool.not (vPot.length == Nat.add kMax 1)))))) with
  | true => rw [hg1, rkme_cond_true] at hchk; exact Bool.noConfusion hchk
  | false =>
    rw [hg1, rkme_cond_false] at hchk
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkme_primNatBlt_eq_false,
      beq_iff_eq] at hg1
    obtain ⟨hm1, hlMax1, hlMax_hi, hk2, hk1024, hv_len⟩ := hg1
    rcases hv_cases : vPot with _ | ⟨v0, _ | ⟨v1, vRest⟩⟩
    · rw [hv_cases] at hv_len; simp at hv_len
    · rw [hv_cases] at hv_len; simp [Nat.add_eq] at hv_len; omega
    · rw [hv_cases] at hchk hv_len
      dsimp only at hchk
      rw [rkme_to_beq v0 0 Nat.beq_eq] at hchk
      cases hv0_z : Bool.not (v0 == 0) with
      | true => rw [hv0_z, rkme_cond_true] at hchk; exact Bool.noConfusion hchk
      | false =>
        rw [hv0_z, rkme_cond_false] at hchk
        simp only [Bool.not_eq_false', beq_iff_eq] at hv0_z
        cases heig1 : checkEigStep m 1 v1 v0 with
        | false => rw [heig1, rkme_cond_false] at hchk; exact Bool.noConfusion hchk
        | true =>
          rw [heig1, rkme_cond_true] at hchk
          have hv1_ge : v0 ≤ v1 := hv0_z ▸ Nat.zero_le v1
          have hcap1 : muxRunningCap (v0 :: v1 :: vRest) 1 = v1 := by
            change max v0 v1 = v1
            exact Nat.max_eq_right hv1_ge
          have hrest_len : vRest.length = kMax - 1 := by simp [Nat.add_eq] at hv_len; omega
          have hrows := rkme_checkTableAux_props m lTableMax useColdR2 (v0 :: v1 :: vRest)
            vRest 2 [v1, v0] anchors (by omega) rfl (by simp)
            (fun j hj ↦ by rcases j with _ | _ | _ <;> first | rfl | omega)
            (fun j _ ↦ by
              rw [show 2 + j = (j + 1) + 1 by omega, List.getD_cons_succ, List.getD_cons_succ])
            hsound
            (by simpa [hcap1] using hchk)
          exact ⟨hm1, hlMax1, hlMax_hi, hk2, hk1024, hv_len, hv0_z, heig1,
            fun s hs2 hsk ↦ hrows s hs2 (by omega)⟩
/-- Lane witness for `FindAllJohnsonAltMuxDefs`. -/
theorem laneWitness_FindAllJohnsonAltMuxDefs : (0 : ℕ) = 0 := rfl
/-- Lane witness for `FindAllJohnsonBlockMuxSparseEval`. -/
theorem laneWitness_FindAllJohnsonBlockMuxSparseEval : (0 : ℕ) = 0 := rfl
/-- Lane witness for `FindAllJohnsonRampKickMuxStep`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxStep : (0 : ℕ) = 0 := rfl
/-- Lane witness for `FindAllJohnsonRampKickMuxEval`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxEval : (0 : ℕ) = 0 := rfl
end
end QuantumComputation.Specs.DickeSol
