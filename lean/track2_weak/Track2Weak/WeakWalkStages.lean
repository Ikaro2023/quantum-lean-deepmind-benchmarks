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

public import Track2Weak.WeakWalkFilter
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

/-! Width-one finite-dimensional segmented walk, active probes, and adaptive stopping. -/
public section
set_option maxHeartbeats 2000000
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Matrix
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal

abbrev WeakRow := Rkm128kSeg × RealFlagPair
abbrev WeakCellCirc (Var : Type) (n : ℕ) := OracleCirc Var (1024*(n+1)+512*n) ((n+1)*1024)

@[expose] noncomputable def weakOrbitStep (n r : ℕ) (row : WeakRow) (x : Fin (orbDim 1024 r) → ℝ) :=
  rkmMaskSignVec (min 1024 r) row.1.mask
    (((dAltStepOrbMat (2^n) 1024 r) ^ altStepCount row.1.tau9 row.1.nSub (2^n)) *ᵥ x)

@[expose] noncomputable def weakCellOps (n r : ℕ) (row : WeakRow) :=
  rkmSegOps n 1024 r 1 row.1.tau9 row.1.nSub row.1.mask

noncomputable def weakSegment {Var : Type} (n r : ℕ) (row : WeakRow) : WeakCellCirc Var n :=
  by exact mkrLiftCirc (QRegister.whole _) (mkrOpsProg n 1024 512 1 0 (weakCellOps n r row))

@[expose] noncomputable def weakStageWith {Var : Type} (res : Var) (n r : ℕ) (hM : 1 ≤ 512*n)
    (row : WeakRow) : WeakCellCirc Var n :=
  .seq (weakSegment n r row) (weakProbe res n 1024 (512*n) r hM row.2)

noncomputable abbrev weakStage {Var : Type} (res : Var) (n : ℕ) (hM : 1 ≤ 512*n)
    (row : WeakRow) : WeakCellCirc Var n := weakStageWith res n 512 hM row

@[expose] noncomputable def weakStages {Var : Type} (res : Var) (n : ℕ) (hM : 1 ≤ 512*n)
    (finish : WeakCellCirc Var n) : List WeakRow → WeakCellCirc Var n
  | [] => finish
  | row :: tail => .seq (weakStage res n hM row)
      (.qIf (fun σ ↦ σ res = 1) finish (weakStages res n hM finish tail))

private theorem weak_embed_whole {Var : Type} {q : ℕ} (Θ : CQAssertion (Store Var) (2^q)) :
    mkrEmbedAssn (QRegister.whole _) Θ = Θ := by
  funext σ
  apply Subtype.ext
  apply Subtype.ext
  exact (mkrEmbedAssn_mat _ Θ σ).trans (QRegister.whole_embedMatrix _)

private theorem weak_ops_calls {Var : Type} (n m k L s : ℕ)
    (ops : List (MuxSymOp (2^n) (L*m))) :
    mkrStaticOracleCalls (mkrOpsProg (Var := Var) n m k L s ops) = some (L * muxOpsQueryCount ops) := by
  have horac : ∀ active,
      mkrStaticOracleCalls (mkrDeflatedOracle (Var := Var) n m k L active) = some L :=
    fun active ↦ by
      unfold mkrDeflatedOracle; dsimp only [mkrStaticOracleCalls]
      rw [mkrStaticOracleCalls_oracleList, List.length_finRange]
      exact congrArg some (Nat.add_zero L)
  have hph : ∀ active,
      mkrStaticOracleCalls (mkrDeflatedPhaseStep (Var := Var) n m k L active) = some L :=
    fun active ↦ by
      unfold mkrDeflatedPhaseStep; dsimp only [mkrStaticOracleCalls]; rw [horac active]; simp
  have hkick : ∀ active j0,
      mkrStaticOracleCalls (mkrPrefixKick (Var := Var) n m k L active j0) = some (L * 2) :=
    fun active j0 ↦ by
      unfold mkrPrefixKick; dsimp only [mkrStaticOracleCalls]; rw [horac active]
      exact congrArg some (by ring)
  have hiter (D : SymOrthogonal (2 ^ n) (L * m)) :
      mkrStaticOracleCalls (mkrSingleIter (Var := Var) n m k L s D) = some L := by
    unfold mkrSingleIter; dsimp only [mkrStaticOracleCalls]; rw [hph]
    exact congrArg some (Nat.add_zero L)
  have hloop (D : SymOrthogonal (2 ^ n) (L * m)) : ∀ K : ℕ,
      mkrStaticOracleCalls (mkrStageLoop (Var := Var) n m k L s D K) = some (L * K) := fun K ↦ by
    induction K with
    | zero => simp [mkrStageLoop, mkrStaticOracleCalls]
    | succ K ih =>
      unfold mkrStageLoop; dsimp only [mkrStaticOracleCalls]; rw [hiter D, ih]
      exact congrArg some (by ring)
  have hops : ∀ l : List (MuxSymOp (2 ^ n) (L * m)),
      mkrStaticOracleCalls (mkrOpsProg (Var := Var) n m k L s l) =
        some (L * muxOpsQueryCount l) := fun l ↦ by
    induction l with
    | nil => simp [mkrOpsProg, muxOpsQueryCount, mkrStaticOracleCalls]
    | cons op tl ih =>
      cases op with
      | walk K D =>
        unfold mkrOpsProg; dsimp only [mkrStaticOracleCalls]; rw [hloop D K, ih]
        exact congrArg some (by simp [muxOpsQueryCount]; ring)
      | prefixKick j0 =>
        unfold mkrOpsProg; dsimp only [mkrStaticOracleCalls]; rw [hkick (memPrefix k s) j0, ih]
        exact congrArg some (by simp [muxOpsQueryCount]; ring)
  exact hops ops

theorem weakSegment_cost {Var : Type} [DecidableEq Var] (n r : ℕ) (row : WeakRow)
    (S : Finset (Fin (2^n))) :
    CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
      ((weakSegment (Var := Var) n r row).compile qAssign (groverParallelMarkingOracle 1024 S))
      (muxOpsQueryCount (weakCellOps n r row) : ℝ≥0) := by
  exact costBound_mkrLiftCirc_of_staticOracleCalls _ (isRealMatrix_groverParallelMarkingOracle _ S)
    _ _ (by simpa using weak_ops_calls (Var := Var) n 1024 512 1 0 (weakCellOps n r row))

theorem weakStage_cost {Var : Type} [DecidableEq Var] (res : Var) (n : ℕ)
    (hM : 1 ≤ 512*n) (row : WeakRow) (S : Finset (Fin (2^n))) :
    CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
      ((weakStage res n hM row).compile qAssign (groverParallelMarkingOracle 1024 S))
      ((muxOpsQueryCount (weakCellOps n 512 row) : ℝ≥0) + 2) :=
  (weakSegment_cost n 512 row S).seq (weakProbe_cost res hM row.2 S)

theorem weakStage_charge (n : ℕ) (row : WeakRow) :
    (muxOpsQueryCount (weakCellOps n 512 row) : ℝ) + 2 ≤
      (row.1.tau9 : ℝ)/1000000000 * √(2^n : ℝ) + 1028 := by
  have h := rkmSegOps_queryCount_le n 1024 512 1 row.1.tau9 row.1.nSub row.1.mask
  change (muxOpsQueryCount (rkmSegOps _ _ _ _ _ _ _) : ℝ) + 2 ≤ _
  linarith

@[expose] noncomputable def weakOrbitLift {n r : ℕ} (S : Finset (Fin (2^n))) (h : S.card = r)
    (x : Fin (orbDim 1024 r) → ℝ) : SymSubset (2^n) 1024 → ℝ :=
  orbEmbedGen (2^n) 1024 S (fun i ↦ x (Fin.cast (congrArg (orbDim 1024) h) i))

noncomputable abbrev weakState {n r : ℕ} (S : Finset (Fin (2^n))) (h : S.card=r)
    (x : Fin (orbDim 1024 r) → ℝ) (μ : Fin (2^(512*n))) :=
  workMemState (liftSymVec n 1024 (weakOrbitLift S h x)) (Pi.single μ 1)

theorem weakSegment_wp {Var : Type} [DecidableEq Var] {n r : ℕ} (hn : 80000 ≤ n) (hr : r ≤ 1024)
    (row : WeakRow) (S : Finset (Fin (2^n))) (hS : S.card = r) (x : Fin (orbDim 1024 r) → ℝ)
    (μ : Fin (2^(512*n))) (Θ : CQAssertion (Store Var) (2^(1024*(n+1)+512*n))) (σ : Store Var) :
    rmsVecQuad ((wp ((weakSegment n r row).compile qAssign (groverParallelMarkingOracle 1024 S))
      Θ) σ).1.1 (weakState S hS x μ) = rmsVecQuad (Θ σ).1.1 (weakState S hS (weakOrbitStep n r row x) μ) := by
  subst r
  let ops := weakCellOps n S.card row
  let v := orbEmbedGen (2^n) 1024 S x
  let c := mkrOpsProg (Var := Var) n 1024 512 1 0 ops
  let O := groverParallelMarkingOracle 1024 S
  have hwp : wp ((mkrLiftCirc (QRegister.whole _) c).compile qAssign O) Θ =
      wp (c.compile qAssign O) Θ := by
    simpa only [weak_embed_whole] using wp_mkrLiftCirc (QRegister.whole _) O c Θ
  have hseen : memSeen n 512 (memPrefix 512 0) μ = ∅ := by ext z; simp [memSeen, memPrefix]
  have hsub : memSeen n 512 (memPrefix 512 0) μ ⊆ S := by rw [hseen]; exact Finset.empty_subset _
  have h := wp_mkrOpsProg_vecQuad ops v μ hsub Θ σ
  rw [hseen, Finset.sdiff_empty] at h
  have hseg := weak_segment_orbit (m:=1024) (lS:=1) (tau9:=row.1.tau9) (nSub:=row.1.nSub)
    (mask:=row.1.mask) (R:=S) hn (by decide) hr x
  change evalMuxSymOps S ops v = orbEmbedGen (2^n) 1024 S (weakOrbitStep n S.card row x) at hseg
  rw [hseg] at h
  change rmsVecQuad ((wp ((mkrLiftCirc (QRegister.whole _) c).compile qAssign O) Θ σ).1.1) _ = _
  rw [hwp]
  exact h

theorem weakStage_wp_general {Var : Type} [DecidableEq Var] (res : Var) {n r : ℕ}
    (hn : 80000 ≤ n) (hr : r ≤ 1024) (hM : 1 ≤ 512*n) (row : WeakRow)
    (S : Finset (Fin (2^n))) (hS : S.card = r) (x : Fin (orbDim 1024 r) → ℝ)
    (μ : Fin (2^(512*n))) (hμ : μ.val < 2^(512*n-1))
    (Θ : CQAssertion (Store Var) (2^(1024*(n+1)+512*n))) (σ : Store Var) :
    rmsVecQuad ((wp ((weakStageWith res n r hM row).compile qAssign (groverParallelMarkingOracle 1024 S))
      Θ) σ).1.1 (weakState S hS x μ) =
    rmsVecQuad (Θ (Store.subst σ res 0)).1.1 (weakState S hS (weakKeep r row.2.cVal (weakOrbitStep n r row x)) μ) +
    rmsVecQuad (Θ (Store.subst σ res 1)).1.1 (weakState S hS (weakClick r row.2.sVal (weakOrbitStep n r row x))
      (memWithTopOne hM μ hμ)) := by
  subst r
  dsimp only [weakStageWith, compile]
  rw [wp_qSeq, weakSegment_wp hn hr row S rfl x μ]
  change rmsVecQuad _ (workMemState (liftSymVec _ _ (orbEmbedGen _ _ _ _)) _) = _
  rw [weakProbe_wp, weakSubset_keep_orb, weakSubset_click_orb]
  rfl

/-- Exact single-stage conditional instrument in finite dimension on the claimed cell. -/
theorem weakStage_wp {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ}
    (hn : 80000 ≤ n) (hM : 1 ≤ 512*n) (row : WeakRow)
    (S : Finset (Fin (2^n))) (hS : S.card = 512) (x : Fin 513 → ℝ)
    (μ : Fin (2^(512*n))) (hμ : μ.val < 2^(512*n-1))
    (Θ : CQAssertion (Store Var) (2^(1024*(n+1)+512*n))) (σ : Store Var) :
    rmsVecQuad ((wp ((weakStage res n hM row).compile qAssign (groverParallelMarkingOracle 1024 S))
      Θ) σ).1.1 (weakState S hS x μ) =
    rmsVecQuad (Θ (Store.subst σ res 0)).1.1 (weakState S hS (weakKeep 512 row.2.cVal (weakOrbitStep n 512 row x)) μ) +
    rmsVecQuad (Θ (Store.subst σ res 1)).1.1 (weakState S hS (weakClick 512 row.2.sVal (weakOrbitStep n 512 row x))
      (memWithTopOne hM μ hμ)) :=
  weakStage_wp_general res hn (by decide) hM row S hS x μ hμ Θ σ

end QuantumComputation.Specs.DickeSol

#print axioms QuantumComputation.Specs.DickeSol.weakStage_wp
#print axioms QuantumComputation.Specs.DickeSol.weakStage_cost