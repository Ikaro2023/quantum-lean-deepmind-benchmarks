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

public import Track2Grover.Engine.FindAllJohnsonAltStep
public import Track2Grover.Engine.FindAllJohnsonMuxRefocusLift
public import Track2Grover.Engine.FindAllJohnsonP01
public import Track2Grover.Engine.FindAllJohnsonRampKickMuxEval
public import Track2Grover.Engine.FindAllJohnsonRampLift
public import Track2Grover.Engine.GaussianHammingZoomK2Base
public import Track2Grover.Engine.MultiTapStage2AGL1QHL
public import Track2Grover.Engine.WeakDickeCore

/-
# `MuxRefocus`, `RampMuxSparse` QHL, & `RampKickMux` Bridge (`FindAllJohnsonRampKickMuxBridge`)
-/

section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
private lemma qhlQSet_val {Var : Type} {d : ℕ} [NeZero d]
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qSet σ).1.1 =
      (θ σ).1.1 0 0 • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qSet_apply_mat θ σ
end

namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace
@[expose] public section
/-- Multi-hit branch precondition assertion after `mkrPassFront`. -/
noncomputable def mkrDispPre {Var : Type} (res : Var) (n m_tot k : ℕ)
    (S : Finset (Fin (2 ^ n))) (s u : ℕ) : CQAssertion (Store Var) (2 ^ (m_tot * (n + 1) + k * n))
      :=
  fun τ ↦ if 1 ≤ τ res ∧ τ res ≤ (u : ℤ) then validObs n m_tot k S (s + (τ res).toNat) τ
  else validObs n m_tot k S s τ
/-- Classical store predicate testing whether `res` recorded exactly `w` distinct hits. -/
abbrev mkrHitPred {Var : Type} (res : Var) (w : ℕ) (σ : Store Var) : Prop := σ res = (w : ℤ)
/-- Classical store predicate testing whether `res` missed `1..u` (`0` hits). -/
abbrev mkrMissPred {Var : Type} (res : Var) (u : ℕ) (σ : Store Var) : Prop :=
  ∀ w ∈ Finset.Icc 1 u, σ res ≠ (w : ℤ)
end
public section
/- ## 1. Quadratic Form & Pure-Unitary Helpers -/
private noncomputable def mkrVecQuad {d : ℕ} (A : Operator d) (ψ : Fin d → ℂ) : ℂ :=
  star ψ ⬝ᵥ (A *ᵥ ψ)
private lemma mkrVecQuad_single {d : ℕ} (A : Operator d) (z : Fin d) :
    A z z = mkrVecQuad A (Pi.single z 1) := by
  simp [mkrVecQuad]
private lemma mkrVecQuad_conj {d : ℕ} (U A : Operator d) (ψ : Fin d → ℂ) :
    mkrVecQuad (Uᴴ * A * U) ψ = mkrVecQuad A (U *ᵥ ψ) := by
  unfold mkrVecQuad; rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
  set v := A *ᵥ (U *ᵥ ψ)
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
private lemma mkrVecQuad_diagonal_sum_single {d : ℕ} {ι : Type*} [Fintype ι]
    (g : Fin d → ℂ) (v : ι → ℝ) (idx : ι → Fin d) (hinj : Function.Injective idx) :
    mkrVecQuad (diagonal g) (∑ i : ι, (v i : ℂ) • Pi.single (idx i) 1) =
      ∑ i : ι, ((v i) ^ 2 : ℂ) * g (idx i) := by
  classical
  let ψ : Fin d → ℂ := ∑ i : ι, (v i : ℂ) • Pi.single (idx i) 1
  have hψ_at (i : ι) : ψ (idx i) = (v i : ℂ) := by
    simp only [ψ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [sum_eq_single i (fun j hj ↦ by simp [hinj.ne hj.symm])]
    simp
  have hψ_out (z : Fin d) (hz : z ∉ Finset.univ.image idx) : ψ z = 0 := by
    simp only [ψ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hne : z ≠ idx i := fun h ↦ hz (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩)
    simp [hne]
  unfold mkrVecQuad; change ∑ z : Fin d, star (ψ z) * (diagonal g *ᵥ ψ) z = _
  simp only [mulVec_diagonal]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image idx))
    (fun z _ hz ↦ by simp [hψ_out z hz]),
    Finset.sum_image (fun i _ j _ h ↦ hinj h)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [hψ_at i, Complex.star_def, Complex.conj_ofReal]
  ring
private lemma mkrWorkMemState_sum_left {W M : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (∑ i ∈ s, f i) φ = ∑ i ∈ s, workMemState (f i) φ := by
  funext z
  simp [workMemState, Finset.sum_apply, Finset.sum_mul]
private lemma mkrWorkMemState_smul_left {W M : ℕ} (c : ℂ)
    (ψ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (c • ψ) φ = c • workMemState ψ φ := by
  funext z
  dsimp only [workMemState, Pi.smul_apply, smul_eq_mul]; ring
private lemma mkrWp_mapAndMeasureLow {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M)))
    (oracle : Unitary (2 ^ O)) (H : ℤ → Operator (2 ^ (W + M)))
    (Φ : CQAssertion (Store Var) (2 ^ (W + M))) (hΦ : ∀ τ, (Φ τ).1.1 = H (τ res)) (σ : Store Var) :
    ((wp ((mapAndMeasureLow res W M O g).compile qAssign oracle) Φ) σ).1.1 =
      diagonal (fun z : Fin (2 ^ (W + M)) ↦
        H (Int.ofNat ((lowHighEquiv W M (g z)).1).val) (g z) (g z)) := by
  unfold mapAndMeasureLow; dsimp only [compile]; rw [wp_qSeq]
  let M_meas : Operator (2 ^ (W + M)) :=
    ∑ o : Fin (2 ^ W), (lowBlock W M).basisOutcomeProjector o * H (Int.ofNat o.val) *
        (lowBlock W M).basisOutcomeProjector o
  have hmeas (τ : Store Var) : ((wp (measureRegister res (lowBlock W M)) Φ) τ).1.1 = M_meas := by
    rw [wp_measureRegister]
    exact Finset.sum_congr rfl fun o _ ↦ by rw [hΦ]; simp [Store.subst]
  rw [wp_qMap res g oracle (fun _ ↦ M_meas) _ hmeas σ]; refine congrArg diagonal (funext fun z ↦ ?_)
  dsimp only [M_meas]; rw [Matrix.sum_apply]
  let o₀ : Fin (2 ^ W) := (lowHighEquiv W M (g z)).1
  rw [sum_eq_single o₀ (fun o ho ↦ by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
      extractIndex_lowBlock, ite_eq_right (Ne.symm ho), mul_zero])]
  rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
    extractIndex_lowBlock, ite_eq_left rfl, one_mul, mul_one]
private def mkrPureUnitaryProg {Var : Type} {d : ℕ} : QProg Var d → Prop
  | .skip => True
  | .qAssign _ => True
  | .qSeq c₁ c₂ => mkrPureUnitaryProg c₁ ∧ mkrPureUnitaryProg c₂
  | _ => False
private lemma mkrWp_eq_of_pureUnitary {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {P : QProg Var d} (hP : mkrPureUnitaryProg P) {Θ₁ Θ₂ : CQAssertion (Store Var) d}
    {σ₁ σ₂ : Store Var} (h : Θ₁ σ₁ = Θ₂ σ₂) : wp P Θ₁ σ₁ = wp P Θ₂ σ₂ := by
  induction P generalizing Θ₁ Θ₂ with
  | «skip» => exact h
  | qAssign U =>
    rw [wp_qAssign, wp_qAssign, CQAssertion.qAssign_apply, CQAssertion.qAssign_apply, h]
  | qSeq c₁ c₂ ih₁ ih₂ => rw [wp_qSeq, wp_qSeq]; exact ih₁ hP.1 (ih₂ hP.2 h)
  | _ => cases hP
private lemma mkrStaticOracleCalls_dispFin {Var : Type} (res : Var) {Q O D : ℕ}
    (br : Fin D → OracleCirc Var Q O) (hbr : ∀ o, mkrStaticOracleCalls (br o) = some 0) :
    ∀ l : List (Fin D), mkrStaticOracleCalls (dispFin res br l) = some 0
  | [] => rfl
  | o :: rest => by
    dsimp only [dispFin, mkrStaticOracleCalls]
    rw [hbr o, mkrStaticOracleCalls_dispFin res br hbr rest]; rfl
theorem mkrStaticOracleCalls_mapAndMeasureLow {Var : Type} (res : Var)
    (W M O : ℕ) (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M))) :
    mkrStaticOracleCalls (mapAndMeasureLow res W M O g) = some 0 := by
  unfold mapAndMeasureLow qMap; dsimp only [mkrStaticOracleCalls]
  rw [mkrStaticOracleCalls_dispFin res _ (fun _ ↦ rfl)]
/- ## 2. `L`-Group Multiplexed Oracle & Exact `2L`-Query Prefix-Weight Kick -/
private abbrev mkrGroupReg (n m L : ℕ) (c : Fin L) : QRegister (m * (n + 1)) ((L * m) * (n + 1)) :=
  groupReg (n := n) (rfl : L * m = L * m) c
private abbrev mkrOracleReg (n m k L : ℕ) (c : Fin L) :
    QRegister ((n + 1) * m) ((L * m) * (n + 1) + k * n) :=
  (lowBlock ((L * m) * (n + 1)) (k * n)).compose ((mkrGroupReg n m L c).compose (fullReg n m))
private noncomputable def mkrOracleList {Var : Type} (n m k L : ℕ) :
    List (Fin L) → OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | c :: cs => .seq (.oracle (mkrOracleReg n m k L c)) (mkrOracleList n m k L cs)
private noncomputable def mkrPermList (n m L : ℕ) (S : Finset (Fin (2 ^ n))) :
    List (Fin L) → Equiv.Perm (Fin (2 ^ ((L * m) * (n + 1))))
  | [] => 1
  | c :: cs => mkrPermList n m L S cs * liftPerm (mkrGroupReg n m L c) (parallelMarkPerm n m S)
private lemma extractIndex_mkrPermList {n m L : ℕ} (S : Finset (Fin (2 ^ n))) :
    ∀ (l : List (Fin L)), l.Nodup → ∀ (w : Fin (2 ^ ((L * m) * (n + 1)))) (d : Fin L),
        (mkrGroupReg n m L d).extractIndex (mkrPermList n m L S l w) =
          if d ∈ l then parallelMarkPerm n m S ((mkrGroupReg n m L d).extractIndex w)
          else (mkrGroupReg n m L d).extractIndex w
  | [], _, w, d => by simp [mkrPermList]
  | c :: cs, hl, w, d => by
    rcases List.nodup_cons.mp hl with ⟨hc_not, hcs⟩; dsimp only [mkrPermList, Equiv.Perm.mul_apply]
    rw [extractIndex_mkrPermList S cs hcs]
    by_cases hdc : d = c
    · subst hdc
      rw [ite_eq_right hc_not, liftPerm_apply_eq_replaceIndex,
        QRegister.extractIndex_replaceIndex, ite_eq_left List.mem_cons_self]
    · rw [liftPerm_apply_eq_replaceIndex,
        QRegister.extractIndex_replaceIndex_of_disjoint _ _
          (groupReg_disjointWires (rfl : L * m = L * m) hdc)]
      simp [List.mem_cons, hdc]
private lemma mkrPermList_finRange_eq_parallelMarkPerm (n m L : ℕ) (S : Finset (Fin (2 ^ n))) :
    mkrPermList n m L S (List.finRange L) = parallelMarkPerm n (L * m) S := by
  ext w : 1
  apply (basisBits ((L * m) * (n + 1))).injective
  funext q
  obtain ⟨⟨ab, r⟩, rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨⟨c, j⟩, rfl⟩ := finProdFinEquiv.surjective ab
  have hc_eq : (mkrGroupReg n m L c).extractIndex (mkrPermList n m L S (List.finRange L) w) =
        (mkrGroupReg n m L c).extractIndex (parallelMarkPerm n (L * m) S w) := by
    rw [extractIndex_mkrPermList S (List.finRange L) (List.nodup_finRange L),
      ite_eq_left (List.mem_finRange c),
      extractIndex_groupReg_parallelMarkPerm (rfl : L * m = L * m)]
  rw [← slotReg_apply n (L * m) (finProdFinEquiv (c, j)) r,
    show slotReg n (L * m) (finProdFinEquiv (c, j)) =
        (mkrGroupReg n m L c).compose (slotReg n m j) from
      (groupReg_compose_slotReg (rfl : L * m = L * m) c j).symm]
  change basisBits _ _ (((mkrGroupReg n m L c).compose (slotReg n m j)) r) =
    basisBits _ _ (((mkrGroupReg n m L c).compose (slotReg n m j)) r)
  rw [← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex,
    QRegister.extractIndex_compose, QRegister.extractIndex_compose, hc_eq]
private lemma wp_mkrOracleList_vecQuad {Var : Type} [DecidableEq Var] {n m k L : ℕ}
    (S : Finset (Fin (2 ^ n))) :
    ∀ (l : List (Fin L)) (ψ : Fin (2 ^ ((L * m) * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
      (Θ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))) (σ : Store Var), mkrVecQuad
        (((wp ((mkrOracleList (Var := Var) n m k L l).compile qAssign
            (groverParallelMarkingOracle m S)) Θ) σ).1.1)
        (workMemState ψ (Pi.single μ 1)) =
      mkrVecQuad ((Θ σ).1.1)
        (workMemState ((permutationUnitary (mkrPermList n m L S l)).1 *ᵥ ψ) (Pi.single μ 1))
  | [], ψ, μ, Θ, σ => by
    have h1 : (permutationUnitary (1 : Equiv.Perm (Fin (2 ^ ((L * m) * (n + 1)))))).1 = 1 := by
      ext i j; simp
    dsimp only [mkrOracleList, mkrPermList, compile]; rw [wp_skip, h1, Matrix.one_mulVec]
  | c :: cs, ψ, μ, Θ, σ => by
    dsimp only [mkrOracleList, mkrPermList, compile]
    rw [wp_qSeq, wp_qAssign, qhlQAssign_val, mkrVecQuad_conj]
    have hemb : ((mkrOracleReg n m k L c).embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ
            workMemState ψ (Pi.single μ 1) = workMemState ((permutationUnitary
              (liftPerm (mkrGroupReg n m L c) (parallelMarkPerm n m S))).1 *ᵥ ψ)
            (Pi.single μ 1) := by
      dsimp only [mkrOracleReg]
      rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_compose,
        fullReg_embedUnitary_eq_permutationUnitary S, embedUnitary_permutationUnitary,
        QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState]
    rw [hemb, wp_mkrOracleList_vecQuad S cs, mulVec_mulVec, ← Submonoid.coe_mul,
      ← permutationUnitary_mul]
private noncomputable def mkrDeflatedOracle {Var : Type} (n m k L : ℕ)
    (active : Finset (Fin k)) : OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (mkrOracleList n m k L (List.finRange L))
    (.step (phaseTag (permutationUnitary (unmarkPerm n (L * m) k active))))
private noncomputable def mkrDeflatedPhaseStep {Var : Type} (n m k L : ℕ)
    (active : Finset (Fin k)) : OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m) :=
  let fc := (lowBlock ((L * m) * (n + 1)) (k * n)).embedUnitary (flagConj n (L * m))
  .seq (.step (phaseTag fc)) (.seq (mkrDeflatedOracle n m k L active) (.step (phaseTag fc)))
private lemma wp_mkrDeflatedOracle_vecQuad {Var : Type} [DecidableEq Var] {n m k L : ℕ}
    {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k))
    (ψ : Fin (2 ^ ((L * m) * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k active μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))) (σ : Store Var) : mkrVecQuad
      (((wp ((mkrDeflatedOracle (Var := Var) n m k L active).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState ψ (Pi.single μ 1)) =
    mkrVecQuad ((Θ σ).1.1) (workMemState
        ((permutationUnitary (parallelMarkPerm n (L * m) (S \ memSeen n k active μ))).1 *ᵥ ψ)
        (Pi.single μ 1)) := by
  unfold mkrDeflatedOracle; dsimp only [compile]
  rw [wp_qSeq, wp_mkrOracleList_vecQuad S (List.finRange L),
    mkrPermList_finRange_eq_parallelMarkPerm, wp_qAssign, wp_phaseTag,
    qhlQAssign_val, mkrVecQuad_conj,
    permutationUnitary_unmarkPerm_mulVec_workMemState, mulVec_mulVec, ← Submonoid.coe_mul,
    ← permutationUnitary_mul, parallelMarkPerm_mul_of_subset hsub]
private lemma wp_mkrDeflatedPhaseStep_vecQuad {Var : Type} [DecidableEq Var] {n m k L : ℕ}
    {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k))
    (ψ : Fin (2 ^ ((L * m) * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k active μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))) (σ : Store Var) : mkrVecQuad
      (((wp ((mkrDeflatedPhaseStep (Var := Var) n m k L active).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState ψ (Pi.single μ 1)) =
    mkrVecQuad ((Θ σ).1.1)
      (workMemState (sDiagM n (L * m) (S \ memSeen n k active μ) *ᵥ ψ) (Pi.single μ 1)) := by
  unfold mkrDeflatedPhaseStep; dsimp only [compile]
  rw [wp_qSeq, wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, mkrVecQuad_conj,
    QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
    wp_mkrDeflatedOracle_vecQuad active _ μ hsub, wp_qAssign, wp_phaseTag,
    qhlQAssign_val, mkrVecQuad_conj, QRegister.embedUnitary_val,
    embedMatrix_lowBlock_mulVec_workMemState, ← fullReg_embedUnitary_eq_permutationUnitary,
    mulVec_mulVec, mulVec_mulVec, flagConj_mul_embed_mul_flagConj]
private noncomputable def mkrSignDiagUnitary {d : ℕ} (b : Fin d → Bool) : Unitary d :=
  ⟨diagonal (fun i ↦ if b i then -1 else 1), by
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    split <;> simp⟩
private lemma mkrSignDiagUnitary_mulVec_single {d : ℕ} (b : Fin d → Bool) (z : Fin d) (c : ℂ) :
    (mkrSignDiagUnitary b).1 *ᵥ Pi.single z c =
      Pi.single z ((if b z then (-1 : ℂ) else 1) * c) := by
  funext w
  dsimp only [mkrSignDiagUnitary]; rw [mulVec_diagonal]
  by_cases hw : w = z <;> simp [hw]
private theorem mkr_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, mkr_nat_ble_eq_true]
private noncomputable def mkrTagWeightKickUnitary (n M j0 : ℕ) : Unitary (2 ^ (M * (n + 1))) :=
  mkrSignDiagUnitary (fun w ↦ Nat.ble (markedSlotAddrs n M w).length j0)
private noncomputable def mkrPrefixKick {Var : Type} (n m k L : ℕ)
    (active : Finset (Fin k)) (j0 : ℕ) : OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (mkrDeflatedOracle n m k L active)
    (.seq (.step (phaseTag ((lowBlock ((L * m) * (n + 1)) (k * n)).embedUnitary
        (mkrTagWeightKickUnitary n (L * m) j0))))
      (mkrDeflatedOracle n m k L active))
private lemma mkrTagWeightKick_conj_liftSymVec {n M : ℕ} (R : Finset (Fin (2 ^ n)))
    (j0 : ℕ) (u : SymSubset (2 ^ n) M → ℝ) : (permutationUnitary (parallelMarkPerm n M R)).1 *ᵥ
      ((mkrTagWeightKickUnitary n M j0).1 *ᵥ
        ((permutationUnitary (parallelMarkPerm n M R)).1 *ᵥ liftSymVec n M u)) =
      liftSymVec n M (symPrefixKickVec R j0 u) := by
  rw [liftSymVec_eq_sum_single, liftSymVec_eq_sum_single,
    Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun E _ ↦ ?_; dsimp only [mkrTagWeightKickUnitary]
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
    permutationUnitary_mulVec_single, mkrSignDiagUnitary_mulVec_single,
    permutationUnitary_mulVec_single, parallelMarkPerm_involutive,
    (markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E).2, mul_one]
  simp only [mkr_nat_ble_eq_true]
  funext z
  dsimp only [symPrefixKickVec, Pi.smul_apply]
  by_cases hz : z = subsetWorkIdx n M E <;> by_cases hle : (E.1 ∩ R).card ≤ j0 <;>
    simp [hz, hle]
private lemma wp_mkrPrefixKick_vecQuad {Var : Type} [DecidableEq Var] {n m k L : ℕ}
    {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k)) (j0 : ℕ)
    (u : SymSubset (2 ^ n) (L * m) → ℝ) (μ : Fin (2 ^ (k * n))) (hsub : memSeen n k active μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))) (σ : Store Var) : mkrVecQuad
      (((wp ((mkrPrefixKick (Var := Var) n m k L active j0).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState (liftSymVec n (L * m) u) (Pi.single μ 1)) =
    mkrVecQuad ((Θ σ).1.1) (workMemState
        (liftSymVec n (L * m) (symPrefixKickVec (S \ memSeen n k active μ) j0 u))
        (Pi.single μ 1)) := by
  unfold mkrPrefixKick; dsimp only [compile]
  rw [wp_qSeq, wp_qSeq, wp_mkrDeflatedOracle_vecQuad active _ μ hsub,
    wp_qAssign, wp_phaseTag, qhlQAssign_val, mkrVecQuad_conj,
    QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
    wp_mkrDeflatedOracle_vecQuad active _ μ hsub, mkrTagWeightKick_conj_liftSymVec]
private noncomputable def mkrSingleIter {Var : Type} (n m k L s : ℕ)
    (D : SymOrthogonal (2 ^ n) (L * m)) :
    OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (mkrDeflatedPhaseStep n m k L (memPrefix k s))
    (.step (phaseTag ((lowBlock ((L * m) * (n + 1)) (k * n)).embedUnitary
      (liftSymOrthogonal n (L * m) D))))
private noncomputable def mkrStageLoop {Var : Type} (n m k L s : ℕ)
    (D : SymOrthogonal (2 ^ n) (L * m)) :
    ℕ → OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m)
  | 0 => .skip
  | K + 1 => .seq (mkrSingleIter n m k L s D) (mkrStageLoop n m k L s D K)
private noncomputable def mkrOpsProg {Var : Type} (n m k L s : ℕ) :
    List (MuxSymOp (2 ^ n) (L * m)) → OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | .walk K D :: rest => .seq (mkrStageLoop n m k L s D K) (mkrOpsProg n m k L s rest)
  | .prefixKick j0 :: rest =>
      .seq (mkrPrefixKick n m k L (memPrefix k s) j0) (mkrOpsProg n m k L s rest)
private lemma pureUnitary_mkrOracleList {Var : Type} (n m k L : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : ∀ l : List (Fin L),
      mkrPureUnitaryProg ((mkrOracleList (Var := Var) n m k L l).compile qAssign oracle)
  | [] => trivial
  | _ :: cs => ⟨trivial, pureUnitary_mkrOracleList n m k L oracle cs⟩
private lemma pureUnitary_mkrDeflatedOracle {Var : Type} (n m k L : ℕ)
    (active : Finset (Fin k)) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    mkrPureUnitaryProg ((mkrDeflatedOracle (Var := Var) n m k L active).compile qAssign oracle) :=
  ⟨pureUnitary_mkrOracleList n m k L oracle (List.finRange L), trivial⟩
private lemma pureUnitary_mkrOpsProg {Var : Type} {n m k L s : ℕ}
    (ops : List (MuxSymOp (2 ^ n) (L * m))) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    mkrPureUnitaryProg ((mkrOpsProg (Var := Var) n m k L s ops).compile qAssign oracle) := by
  have hloop (D : SymOrthogonal (2 ^ n) (L * m)) : ∀ K : ℕ, mkrPureUnitaryProg
        ((mkrStageLoop (Var := Var) n m k L s D K).compile qAssign oracle) := fun K ↦ by
    induction K with
    | zero => trivial
    | succ K ih =>
      exact ⟨⟨⟨trivial, pureUnitary_mkrDeflatedOracle n m k L _ oracle, trivial⟩, trivial⟩, ih⟩
  induction ops with
  | nil => trivial
  | cons op rest ih =>
    cases op with
    | walk K D => exact ⟨hloop D K, ih⟩
    | prefixKick j0 =>
      exact ⟨⟨pureUnitary_mkrDeflatedOracle n m k L _ oracle, trivial,
        pureUnitary_mkrDeflatedOracle n m k L _ oracle⟩, ih⟩
private lemma wp_mkrOpsProg_vecQuad {Var : Type} [DecidableEq Var] {n m k L s : ℕ}
    {S : Finset (Fin (2 ^ n))} (ops : List (MuxSymOp (2 ^ n) (L * m)))
    (v : SymSubset (2 ^ n) (L * m) → ℝ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k (memPrefix k s) μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))) (σ : Store Var) : mkrVecQuad
      (((wp ((mkrOpsProg (Var := Var) n m k L s ops).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState (liftSymVec n (L * m) v) (Pi.single μ 1)) =
    mkrVecQuad ((Θ σ).1.1) (workMemState
        (liftSymVec n (L * m) (evalMuxSymOps (S \ memSeen n k (memPrefix k s) μ) ops v))
        (Pi.single μ 1)) := by
  let R := S \ memSeen n k (memPrefix k s) μ
  have hiter (D : SymOrthogonal (2 ^ n) (L * m)) (u : SymSubset (2 ^ n) (L * m) → ℝ)
      (Ψ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))) :
      mkrVecQuad (((wp ((mkrSingleIter (Var := Var) n m k L s D).compile qAssign
          (groverParallelMarkingOracle m S)) Ψ) σ).1.1)
        (workMemState (liftSymVec n (L * m) u) (Pi.single μ 1)) =
      mkrVecQuad ((Ψ σ).1.1)
        (workMemState (liftSymVec n (L * m) (D.1 *ᵥ symZVec R u)) (Pi.single μ 1)) := by
    unfold mkrSingleIter; dsimp only [compile]
    rw [wp_qSeq, wp_mkrDeflatedPhaseStep_vecQuad (memPrefix k s) _ μ hsub,
      sDiagM_mulVec_liftSymVec, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      mkrVecQuad_conj, QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      liftSymOrthogonal_mulVec]
  have hloop (D : SymOrthogonal (2 ^ n) (L * m)) : ∀ (K : ℕ) (u : SymSubset (2 ^ n) (L * m) → ℝ)
        (Ψ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))),
        mkrVecQuad (((wp ((mkrStageLoop (Var := Var) n m k L s D K).compile qAssign
            (groverParallelMarkingOracle m S)) Ψ) σ).1.1)
          (workMemState (liftSymVec n (L * m) u) (Pi.single μ 1)) =
        mkrVecQuad ((Ψ σ).1.1)
          (workMemState (liftSymVec n (L * m) (evalSymStage R D.1 K u)) (Pi.single μ 1)) := by
    intro K
    induction K with
    | zero => intro u Ψ; rfl
    | succ K ih =>
      intro u Ψ
      unfold mkrStageLoop; dsimp only [compile]; rw [wp_qSeq, hiter D u _, ih, evalSymStage]
  induction ops generalizing v with
  | nil => rfl
  | cons op tl ih =>
    cases op with
    | walk K D =>
      unfold mkrOpsProg; dsimp only [compile]; rw [wp_qSeq, hloop D K v _, ih, evalMuxSymOps]
    | prefixKick j0 =>
      unfold mkrOpsProg; dsimp only [compile]
      rw [wp_qSeq, wp_mkrPrefixKick_vecQuad (memPrefix k s) j0 v μ hsub, ih, evalMuxSymOps]
/- ## 3. Pass Front & Multi-Hit Branch Dispatcher -/
private lemma mkrSum_sq_symInjMat_mulVec (n m : ℕ) (v : SymSubset (2 ^ n) m → ℝ) :
    (∑ z : Fin (2 ^ (m * (n + 1))), ((symInjMat n m *ᵥ v) z) ^ 2) =
      ∑ E : SymSubset (2 ^ n) m, (v E) ^ 2 := by
  let J := symInjMat n m
  have h1 : (∑ z, ((J *ᵥ v) z) ^ 2) = (J *ᵥ v) ⬝ᵥ (J *ᵥ v) := by simp [dotProduct, sq]
  have h2 : (J *ᵥ v) ⬝ᵥ (J *ᵥ v) = v ⬝ᵥ ((Jᵀ * J) *ᵥ v) := by
    rw [← mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h1, h2, symInjMat_transpose_mul_self, Matrix.one_mulVec]; simp [dotProduct, sq]
private lemma mkrMarkedSlotAddrs_length_lt_pow (n m : ℕ) (w : Fin (2 ^ (m * (n + 1)))) :
    (markedSlotAddrs n m w).length < 2 ^ (m * (n + 1)) := by
  have hdedup : ∀ l : List (Fin (2 ^ n)), l.dedup.length ≤ l.length := fun l ↦ by
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.dedup_cons]
      split_ifs <;> simp only [List.length_cons] <;> omega
  have h1 : (markedSlotAddrs n m w).length ≤ m := by
    unfold markedSlotAddrs
    calc ((((List.finRange m).filter _).map _).dedup).length
        ≤ (((List.finRange m).filter _).map _).length := hdedup _
      _ = ((List.finRange m).filter _).length := List.length_map _
      _ ≤ (List.finRange m).length := List.length_filter_le _ _
      _ = m := List.length_finRange
  have h2 : m < 2 ^ m := m.lt_two_pow_self; have h3 : 2 ^ m ≤ 2 ^ (m * (n + 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right m (Nat.succ_pos n))
  omega
private def mkrHitCodeFn (n m_tot k : ℕ)
    (z : Fin (2 ^ (m_tot * (n + 1) + k * n))) : Fin (2 ^ (m_tot * (n + 1) + k * n)) :=
  let wm := lowHighEquiv (m_tot * (n + 1)) (k * n) z
  (lowHighEquiv (m_tot * (n + 1)) (k * n)).symm (⟨(markedSlotAddrs n m_tot wm.1).length,
      mkrMarkedSlotAddrs_length_lt_pow n m_tot wm.1⟩, wm.2)
/-- Single multiplexed pass front executing `ops` on `SymSubset (2 ^ n) (L * m)` and
  recording up
  to `min (L * m) (k - s)` distinct hits into the `k * n`-qubit archive. -/
noncomputable def mkrPassFront {Var : Type} (res : Var) (n m k L s : ℕ)
    (hLmN : L * m ≤ 2 ^ n) (ops : List (MuxSymOp (2 ^ n) (L * m))) :
    OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m) :=
  let W := (L * m) * (n + 1)
  let M := k * n
  let O := (n + 1) * m
  .seq (workReset res W M O) (.seq (.step (phaseTag ((lowBlock W M).embedUnitary
        (householderPrepUnitary (symInjMat n (L * m) *ᵥ u0Vec (2 ^ n) (L * m))
          (by rw [mkrSum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hLmN)))))
      (.seq (mkrOpsProg n m k L s ops) (.seq (mkrDeflatedOracle n m k L (memPrefix k s))
          (.seq (.step (phaseTag (permutationUnitary
              (memWriteBatchPerm s (markedSlotAddrs n (L * m))))))
            (mapAndMeasureLow res W M O (mkrHitCodeFn n (L * m) k))))))
private lemma mkrStaticOracleCalls_oracleList {Var : Type} (n m k L : ℕ) : ∀ l : List (Fin L),
      mkrStaticOracleCalls (mkrOracleList (Var := Var) n m k L l) = some l.length
  | [] => rfl
  | _ :: cs => by
    dsimp only [mkrOracleList, mkrStaticOracleCalls]
    rw [mkrStaticOracleCalls_oracleList n m k L cs]; exact congrArg some (Nat.add_comm 1 cs.length)
theorem mkrStaticOracleCalls_passFront {Var : Type} (res : Var) (n m k L s : ℕ)
    (hLmN : L * m ≤ 2 ^ n) (ops : List (MuxSymOp (2 ^ n) (L * m))) :
    mkrStaticOracleCalls (mkrPassFront (Var := Var) res n m k L s hLmN ops) =
      some (L * muxOpsQueryCount ops + L) := by
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
  unfold mkrPassFront workReset; dsimp only [mkrStaticOracleCalls]
  rw [mkrStaticOracleCalls_mapAndMeasureLow, hops ops, horac,
    mkrStaticOracleCalls_mapAndMeasureLow]
  exact congrArg some (by ring)
private lemma wp_mkrPassFront_diag {Var : Type} [DecidableEq Var] (res : Var)
    {n m k L s : ℕ} (hLmN : L * m ≤ 2 ^ n) (ops : List (MuxSymOp (2 ^ n) (L * m)))
    (S : Finset (Fin (2 ^ n))) (G : ℤ → Fin (2 ^ (k * n)) → ℝ)
    (Φ : CQAssertion (Store Var) (2 ^ ((L * m) * (n + 1) + k * n))) (hΦ : ∀ τ : Store Var, (Φ τ).1.1
      =
        diagonal (fun z ↦ (G (τ res) (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2 : ℂ)))
    (σ : Store Var) : ∃ d_out : Fin (2 ^ ((L * m) * (n + 1) + k * n)) → ℂ,
      ((wp ((mkrPassFront res n m k L s hLmN ops).compile qAssign
          (groverParallelMarkingOracle m S)) Φ) σ).1.1 = diagonal d_out ∧
      ∀ z : Fin (2 ^ ((L * m) * (n + 1) + k * n)),
        let μ := (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2
        MemPrefixValid S s μ →
          let R := S \ memSeen n k (memPrefix k s) μ
          let v_fin := evalMuxSymOps R ops (u0Vec (2 ^ n) (L * m))
          d_out z = ∑ E : SymSubset (2 ^ n) (L * m), ((v_fin E) ^ 2 : ℂ) *
            (G (Int.ofNat (E.1 ∩ R).card) ((addrEquiv n k).symm (addrEquiv n k μ +
                batchDelta s (markedSlotAddrs n (L * m))
                  (parallelMarkPerm n (L * m) R (subsetWorkIdx n (L * m) E)))) : ℂ) := by
  let W := (L * m) * (n + 1)
  let M := k * n
  let O := (n + 1) * m
  let oracle := groverParallelMarkingOracle m S
  let P_ms : QProg Var (2 ^ (W + M)) :=
    (mapAndMeasureLow res W M O (mkrHitCodeFn n (L * m) k)).compile qAssign oracle
  let c_u : OracleCirc Var (W + M) O :=
    .seq (.step (phaseTag ((lowBlock W M).embedUnitary
        (householderPrepUnitary (symInjMat n (L * m) *ᵥ u0Vec (2 ^ n) (L * m))
          (by rw [mkrSum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hLmN)))))
      (.seq (mkrOpsProg n m k L s ops) (.seq (mkrDeflatedOracle n m k L (memPrefix k s))
          (.step (phaseTag (permutationUnitary
            (memWriteBatchPerm (k := k) s (markedSlotAddrs n (L * m))))))))
  let P_u : QProg Var (2 ^ (W + M)) := c_u.compile qAssign oracle
  let d_ms : Fin (2 ^ (W + M)) → ℂ := fun z' ↦
    (G (Int.ofNat (markedSlotAddrs n (L * m) (lowHighEquiv W M z').1).length)
      (lowHighEquiv W M z').2 : ℂ)
  have hms_mat (τ : Store Var) : ((wp P_ms Φ) τ).1.1 = diagonal d_ms := by
    rw [mkrWp_mapAndMeasureLow res (mkrHitCodeFn n (L * m) k) oracle
      (fun r_val ↦ diagonal (fun z' ↦ (G r_val (lowHighEquiv W M z').2 : ℂ))) Φ hΦ τ]
    refine congrArg diagonal (funext fun z' ↦ ?_); rw [Matrix.diagonal_apply_eq]
    dsimp only [mkrHitCodeFn, d_ms]; rw [Equiv.apply_symm_apply]
  have hPu : mkrPureUnitaryProg P_u := by
    dsimp only [P_u, c_u, compile]
    exact ⟨trivial, pureUnitary_mkrOpsProg ops oracle,
      pureUnitary_mkrDeflatedOracle n m k L _ oracle, trivial⟩
  let M_in : Operator (2 ^ (W + M)) := ((wp P_u (wp P_ms Φ)) σ).1.1
  let c_tail : OracleCirc Var (W + M) O :=
    .seq (.step (phaseTag ((lowBlock W M).embedUnitary
        (householderPrepUnitary (symInjMat n (L * m) *ᵥ u0Vec (2 ^ n) (L * m))
          (by rw [mkrSum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hLmN)))))
      (.seq (mkrOpsProg n m k L s ops) (.seq (mkrDeflatedOracle n m k L (memPrefix k s))
          (.seq (.step (phaseTag (permutationUnitary
              (memWriteBatchPerm (k := k) s (markedSlotAddrs n (L * m))))))
            (mapAndMeasureLow res W M O (mkrHitCodeFn n (L * m) k)))))
  have hinner (τ : Store Var) : ((wp (c_tail.compile qAssign oracle) Φ) τ).1.1 = M_in := by
    have hwp_eq : wp (c_tail.compile qAssign oracle) Φ = wp P_u (wp P_ms Φ) := by
      dsimp only [c_tail, P_u, c_u, P_ms, compile]; simp only [wp_qSeq]
    rw [hwp_eq]; have heq_ms : wp P_ms Φ τ = wp P_ms Φ σ :=
      Subtype.ext (HermitianMat.ext ((hms_mat τ).trans (hms_mat σ).symm))
    exact congrArg (fun x ↦ x.1.1) (mkrWp_eq_of_pureUnitary hPu heq_ms)
  refine ⟨fun z ↦ M_in (resetWorkFn W M z) (resetWorkFn W M z), ?_, fun z hval ↦ ?_⟩
  · unfold mkrPassFront workReset
    change (((wp ((mapAndMeasureLow res W M O (resetWorkFn W M)).compile qAssign oracle ;;
      c_tail.compile qAssign oracle) Φ) σ).1.1) = _
    rw [wp_qSeq, mkrWp_mapAndMeasureLow res (resetWorkFn W M) oracle
      (fun _ ↦ M_in) _ hinner σ]
  · let μ := (lowHighEquiv W M z).2
    let R := S \ memSeen n k (memPrefix k s) μ
    let v_fin := evalMuxSymOps R ops (u0Vec (2 ^ n) (L * m))
    have hsub : memSeen n k (memPrefix k s) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
    dsimp only [resetWorkFn]
    rw [mkrVecQuad_single M_in ((lowHighEquiv W M).symm (0, μ)), ← workMemState_single]
    dsimp only [M_in, P_u, c_u, compile]
    rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      mkrVecQuad_conj, QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      householderPrepUnitary_mulVec_zero]
    change mkrVecQuad _
      (workMemState (liftSymVec n (L * m) (u0Vec (2 ^ n) (L * m))) (Pi.single μ 1)) = _
    rw [wp_mkrOpsProg_vecQuad ops _ μ hsub,
      wp_mkrDeflatedOracle_vecQuad (memPrefix k s) _ μ hsub]
    change mkrVecQuad _ (workMemState
        ((permutationUnitary (parallelMarkPerm n (L * m) R)).1 *ᵥ liftSymVec n (L * m) v_fin)
        (Pi.single μ 1)) = _
    let w_E (E : SymSubset (2 ^ n) (L * m)) : Fin (2 ^ W) :=
      parallelMarkPerm n (L * m) R (subsetWorkIdx n (L * m) E)
    let μ_E (E : SymSubset (2 ^ n) (L * m)) : Fin (2 ^ M) :=
      (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s (markedSlotAddrs n (L * m)) (w_E E))
    let idx (E : SymSubset (2 ^ n) (L * m)) : Fin (2 ^ (W + M)) :=
      (lowHighEquiv W M).symm (w_E E, μ_E E)
    have hinj : Function.Injective idx := fun E₁ E₂ h ↦ by
      have hw : w_E E₁ = w_E E₂ := congrArg Prod.fst ((lowHighEquiv W M).symm.injective h)
      exact subsetWorkIdx_injective n (L * m) ((parallelMarkPerm n (L * m) R).injective hw)
    have hvec_eq :
        (permutationUnitary (memWriteBatchPerm (k := k) s (markedSlotAddrs n (L * m)))).1 *ᵥ
          workMemState
            ((permutationUnitary (parallelMarkPerm n (L * m) R)).1 *ᵥ liftSymVec n (L * m) v_fin)
            (Pi.single μ 1) =
          ∑ E : SymSubset (2 ^ n) (L * m), (v_fin E : ℂ) • Pi.single (idx E) 1 := by
      rw [liftSymVec_eq_sum_single n (L * m) v_fin, Matrix.mulVec_sum, mkrWorkMemState_sum_left,
        Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun E _ ↦ ?_
      rw [Matrix.mulVec_smul, permutationUnitary_mulVec_single, mkrWorkMemState_smul_left,
        Matrix.mulVec_smul]
      congr 1
      exact (permutationUnitary_memAddPerm_mulVec_single
        (batchDelta s (markedSlotAddrs n (L * m))) (w_E E) μ).trans
        (workMemState_single (w_E E) (μ_E E))
    rw [wp_qAssign, wp_phaseTag, qhlQAssign_val, mkrVecQuad_conj, hvec_eq]
    change mkrVecQuad (((wp P_ms Φ) σ).1.1)
      (∑ E : SymSubset (2 ^ n) (L * m), (v_fin E : ℂ) • Pi.single (idx E) 1) = _
    rw [hms_mat σ, mkrVecQuad_diagonal_sum_single d_ms v_fin idx hinj]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    congr 1
    dsimp only [d_ms, idx]
    rw [Equiv.apply_symm_apply, (markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E).2]
theorem mkrEmbedAssn_dispPre {Var : Type} (res : Var) {n m_sub m_tot k W_pad : ℕ}
    (hW : W_pad + m_sub * (n + 1) = m_tot * (n + 1)) (S : Finset (Fin (2 ^ n))) (s u : ℕ) :
    mkrEmbedAssn (Var := Var) (mkrTopSliceReg W_pad (m_sub * (n + 1)) (m_tot * (n + 1)) (k * n) hW)
        (mkrDispPre res n m_sub k S s u) =
      mkrDispPre res n m_tot k S s u := by
  funext τ
  dsimp only [mkrEmbedAssn, mkrDispPre]
  split_ifs with h
  · exact congrFun (mkrEmbedAssn_validObs (Var := Var) hW S (s + (τ res).toNat)) τ
  · exact congrFun (mkrEmbedAssn_validObs (Var := Var) hW S s) τ
theorem wp_mkrPassFront_dispPre {Var : Type} [DecidableEq Var] (res : Var)
    {n m k L s : ℕ} (hLmN : L * m ≤ 2 ^ n) (_hs : s ≤ k) (ops : List (MuxSymOp (2 ^ n) (L * m)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) : validObs (Var := Var) n (L * m) k S s ≤
      wp ((mkrPassFront res n m k L s hLmN ops).compile qAssign (groverParallelMarkingOracle m S))
        (mkrDispPre res n (L * m) k S s (min (L * m) (k - s))) := by
  intro σ
  let b := min (L * m) (k - s)
  let G (r_val : ℤ) (μ' : Fin (2 ^ (k * n))) : ℝ :=
    open Classical in
    if MemPrefixValid S (if 1 ≤ r_val ∧ r_val ≤ (b : ℤ) then s + r_val.toNat else s) μ'
    then 1 else 0
  have hΦ (τ : Store Var) : (mkrDispPre res n (L * m) k S s b τ).1.1 =
        diagonal (fun z ↦ (G (τ res) (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2 : ℂ)) := by
    dsimp only [mkrDispPre]
    split_ifs with h
    · dsimp only [validObs]; rw [realDiagObs_mat]; refine congrArg diagonal (funext fun z ↦ ?_)
      dsimp only [validInd, G]; rw [ite_eq_left h]
    · dsimp only [validObs]; rw [realDiagObs_mat]; refine congrArg diagonal (funext fun z ↦ ?_)
      dsimp only [validInd, G]; rw [ite_eq_right h]
  obtain ⟨d_out, hmat, hd_valid⟩ :=
    wp_mkrPassFront_diag res hLmN ops S G (mkrDispPre res n (L * m) k S s b) hΦ σ
  have hbnd := observable_diag_real_bounds _ d_out hmat
  have hmat_re : ((wp ((mkrPassFront res n m k L s hLmN ops).compile qAssign
      (groverParallelMarkingOracle m S)) (mkrDispPre res n (L * m) k S s b)) σ).1.1 =
      diagonal (fun z ↦ ((d_out z).re : ℂ)) := by
    rw [hmat]
    exact congrArg diagonal (funext fun z ↦ (hbnd z).1)
  refine realDiagObs_le_of_mat (fun z ↦ (hbnd z).2.1) (fun z ↦ (hbnd z).2.2) hmat_re fun z ↦ ?_
  dsimp only [validInd]
  open Classical in
  by_cases hval : MemPrefixValid S s (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hval]
    let μ := (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2
    let R := S \ memSeen n k (memPrefix k s) μ
    have hseen := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = k - s := by
      dsimp only [R, μ]; rw [Finset.card_sdiff_of_subset hseen.2, hcard, hseen.1]
    have h1 : d_out z = 1 := by
      rw [hd_valid z hval]
      have hterm (E : SymSubset (2 ^ n) (L * m)) : (G (Int.ofNat (E.1 ∩ R).card)
            ((addrEquiv n k).symm (addrEquiv n k μ + batchDelta s (markedSlotAddrs n (L * m))
                (parallelMarkPerm n (L * m) R (subsetWorkIdx n (L * m) E)))) : ℂ) = 1 := by
        have hm_mark := markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E
        have hc_m : (E.1 ∩ R).card ≤ L * m :=
          (Finset.card_le_card Finset.inter_subset_left).trans_eq E.2
        have hc_r : (E.1 ∩ R).card ≤ k - s :=
          (Finset.card_le_card Finset.inter_subset_right).trans_eq hR_card
        have hc_b : (E.1 ∩ R).card ≤ b := le_min hc_m hc_r
        have hidx_eq : (if 1 ≤ Int.ofNat (E.1 ∩ R).card ∧ Int.ofNat (E.1 ∩ R).card ≤ (b : ℤ)
              then s + (Int.ofNat (E.1 ∩ R).card).toNat else s) = s + (E.1 ∩ R).card := by
          by_cases hc0 : (E.1 ∩ R).card = 0
          · simp [hc0]
          · have hcond : 1 ≤ Int.ofNat (E.1 ∩ R).card ∧ Int.ofNat (E.1 ∩ R).card ≤ (b : ℤ) := by
              rw [Int.ofNat_eq_natCast]
              exact ⟨by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc0, by exact_mod_cast hc_b⟩
            rw [ite_eq_left hcond]; rfl
        have hadv := memPrefixValid_batchAdvance hval (markedSlotAddrs n (L * m))
          (parallelMarkPerm n (L * m) R (subsetWorkIdx n (L * m) E))
          (nodup_markedSlotAddrs n (L * m) _)
          (by rw [hm_mark.2]; omega)
          hm_mark.1
        rw [hm_mark.2] at hadv; dsimp only [G]; rw [hidx_eq, ite_eq_left hadv]
        exact Complex.ofReal_one
      rw [Finset.sum_congr rfl fun E _ ↦ by rw [hterm E, mul_one]]
      simp_rw [← Complex.ofReal_pow]
      rw [← Complex.ofReal_sum, sum_sq_evalMuxSymOps, sum_sq_u0Vec hLmN, Complex.ofReal_one]
    rw [h1, Complex.one_re]
  · rw [ite_eq_right hval]; exact (hbnd z).2.1
theorem wp_mkrPassFront_hitProb {Var : Type} [DecidableEq Var] (res : Var)
    {n m k L s w : ℕ} (hLmN : L * m ≤ 2 ^ n) (_hs : s ≤ k) (ops : List (MuxSymOp (2 ^ n) (L * m)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {c_lo : ℝ} (hc0 : 0 ≤ c_lo) (hc1 : c_lo ≤ 1)
    (hlo : ∀ R : Finset (Fin (2 ^ n)), R.card = k - s →
      c_lo ≤ symHitProb R (evalMuxSymOps R ops (u0Vec (2 ^ n) (L * m))) w) :
    scaledValidObs (Var := Var) n (L * m) k S s c_lo hc0 hc1 ≤
      wp ((mkrPassFront res n m k L s hLmN ops).compile qAssign (groverParallelMarkingOracle m S))
        (liftPureProp (mkrHitPred res w)) := by
  intro σ
  let G (r_val : ℤ) (_ : Fin (2 ^ (k * n))) : ℝ := if r_val = (w : ℤ) then 1 else 0
  have hΦ (τ : Store Var) :
      (liftPureProp (d := 2 ^ ((L * m) * (n + 1) + k * n)) (mkrHitPred res w) τ).1.1 =
        diagonal (fun z ↦ (G (τ res) (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2 : ℂ)) := by
    rw [liftPureProp_apply]
    by_cases hp : mkrHitPred res w τ
    · rw [ite_eq_left hp]; have hp' : τ res = (w : ℤ) := hp; simp [hp', G]
    · rw [ite_eq_right hp]; have hp' : τ res ≠ (w : ℤ) := hp; simp [hp', G]
  obtain ⟨d_out, hmat, hd_valid⟩ :=
    wp_mkrPassFront_diag res hLmN ops S G (liftPureProp (mkrHitPred res w)) hΦ σ
  have hbnd := observable_diag_real_bounds _ d_out hmat
  have hmat_re : ((wp ((mkrPassFront res n m k L s hLmN ops).compile qAssign
      (groverParallelMarkingOracle m S)) (liftPureProp (mkrHitPred res w))) σ).1.1 =
      diagonal (fun z ↦ ((d_out z).re : ℂ)) := by
    rw [hmat]
    exact congrArg diagonal (funext fun z ↦ (hbnd z).1)
  refine realDiagObs_le_of_mat (fun z ↦ (hbnd z).2.1) (fun z ↦ (hbnd z).2.2) hmat_re fun z ↦ ?_
  dsimp only [validInd]
  open Classical in
  by_cases hval : MemPrefixValid S s (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hval, mul_one]
    let μ := (lowHighEquiv ((L * m) * (n + 1)) (k * n) z).2
    let R := S \ memSeen n k (memPrefix k s) μ
    have hseen := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = k - s := by
      dsimp only [R, μ]; rw [Finset.card_sdiff_of_subset hseen.2, hcard, hseen.1]
    have hprob : d_out z = (symHitProb R (evalMuxSymOps R ops (u0Vec (2 ^ n) (L * m))) w : ℂ) := by
      rw [hd_valid z hval]; unfold symHitProb; rw [Complex.ofReal_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun E _ ↦ ?_; dsimp only [G]
      have heq_iff : (Int.ofNat (E.1 ∩ R).card = (w : ℤ)) ↔ ((E.1 ∩ R).card = w) := by simp
      by_cases hew : (E.1 ∩ R).card = w
      · rw [ite_eq_left (heq_iff.mpr hew), ite_eq_left hew]; push_cast; ring
      · rw [ite_eq_right (mt heq_iff.mp hew), ite_eq_right hew]; simp
    rw [hprob, Complex.ofReal_re]; exact hlo R hR_card
  · rw [ite_eq_right hval, mul_zero]; exact (hbnd z).2.1
end
end QuantumComputation.Specs.DickeSol

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace

/- ## 1. Multi-Hit Branch Dispatcher & State-Restriction Partitioning -/

/-- Classical branch cascade dispatching recorded hit counts `w ∈ 1..u` to `onHit w`. -/
noncomputable def mkrDispHits {Var : Type} (res : Var) {Q O : ℕ}
    (onHit : ℕ → OracleCirc Var Q O) (onZero : OracleCirc Var Q O) :
    ℕ → OracleCirc Var Q O
  | 0 => onZero
  | u + 1 => .qIf (mkrHitPred res (u + 1)) (onHit (u + 1)) (mkrDispHits res onHit onZero u)

theorem wp_mkrDispHits_ge {Var : Type} [DecidableEq Var] (res : Var)
    {n m_tot m_orac k s : ℕ} {S : Finset (Fin (2 ^ n))}
    (onHit : ℕ → OracleCirc Var (m_tot * (n + 1) + k * n) ((n + 1) * m_orac))
    (onZero : OracleCirc Var (m_tot * (n + 1) + k * n) ((n + 1) * m_orac))
    (Θ : CQAssertion (Store Var) (2 ^ (m_tot * (n + 1) + k * n)))
    (honZero : validObs n m_tot k S s ≤
      wp (onZero.compile qAssign (groverParallelMarkingOracle m_orac S)) Θ)
    (u : ℕ)
    (honHit : ∀ w ∈ Finset.Icc 1 u, validObs n m_tot k S (s + w) ≤
      wp ((onHit w).compile qAssign (groverParallelMarkingOracle m_orac S)) Θ) :
    mkrDispPre res n m_tot k S s u ≤
      wp ((mkrDispHits res onHit onZero u).compile qAssign
        (groverParallelMarkingOracle m_orac S)) Θ := by
  induction u with
  | zero =>
    intro σ
    have hf : ¬ (1 ≤ σ res ∧ σ res ≤ ((0 : ℕ) : ℤ)) := by omega
    dsimp only [mkrDispPre, mkrDispHits]
    rw [ite_eq_right hf]
    exact honZero σ
  | succ u ih =>
    intro σ
    dsimp only [mkrDispHits, compile]
    rw [wp_qIf]
    dsimp only
    by_cases hh : mkrHitPred res (u + 1) σ
    · rw [ite_eq_left hh]
      have h1 : 1 ≤ σ res ∧ σ res ≤ ((u + 1 : ℕ) : ℤ) := by
        dsimp only [mkrHitPred] at hh; omega
      have hnat : (σ res).toNat = u + 1 := by
        dsimp only [mkrHitPred] at hh; omega
      dsimp only [mkrDispPre]
      rw [ite_eq_left h1, hnat]
      exact honHit (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) σ
    · rw [ite_eq_right hh]
      have heqv : (1 ≤ σ res ∧ σ res ≤ ((u + 1 : ℕ) : ℤ)) ↔ (1 ≤ σ res ∧ σ res ≤ (u : ℤ)) := by
        dsimp only [mkrHitPred] at hh; omega
      have hpre : mkrDispPre res n m_tot k S s (u + 1) σ = mkrDispPre res n m_tot k S s u σ := by
        dsimp only [mkrDispPre]
        exact if_congr heqv rfl rfl
      rw [hpre]
      exact ih (fun w hw ↦ honHit w (Finset.Icc_subset_Icc_right (Nat.le_succ u) hw)) σ

theorem mkrDispHits_trace_and_cost {Var : Type} [DecidableEq Var] (res : Var)
    {Q O : ℕ} (oracle : Unitary (2 ^ O)) (model : CostModel (2 ^ Q))
    (onHit : ℕ → OracleCirc Var Q O) (onZero : OracleCirc Var Q O)
    (u : ℕ) (Γ : CQState (Store Var) (2 ^ Q)) :
    (Γ.restrict (mkrMissPred res u)).trace +
        ∑ w ∈ Finset.Icc 1 u, (Γ.restrict (mkrHitPred res w)).trace = Γ.trace ∧
      expectedCost model ((mkrDispHits res onHit onZero u).compile qAssign oracle) Γ =
        expectedCost model (onZero.compile qAssign oracle) (Γ.restrict (mkrMissPred res u)) +
          ∑ w ∈ Finset.Icc 1 u,
            expectedCost model ((onHit w).compile qAssign oracle)
              (Γ.restrict (mkrHitPred res w)) := by
  induction u generalizing Γ with
  | zero =>
    have hmiss0 : Γ.restrict (mkrMissPred res 0) = Γ :=
      CQState.restrict_of_forall (fun σ w hw ↦ by simp at hw) Γ
    simp [mkrDispHits, hmiss0]
  | succ u ih =>
    let Γ' := Γ.restrict (¬ mkrHitPred res (u + 1) ·)
    have hmiss_eq : Γ'.restrict (mkrMissPred res u) = Γ.restrict (mkrMissPred res (u + 1)) := by
      apply Subtype.ext; funext σ
      simp only [Γ', CQState.restrict_coe]
      by_cases h1 : mkrHitPred res (u + 1) σ
      · have hm : ¬ mkrMissPred res (u + 1) σ := fun hm ↦
          hm (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) h1
        rw [ite_eq_right (not_not.mpr h1), ite_self, ite_eq_right hm]
      · have heqv : mkrMissPred res u σ ↔ mkrMissPred res (u + 1) σ := by
          simp only [mkrMissPred, Finset.mem_Icc]
          refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ h w ⟨hw.1, by omega⟩⟩
          by_cases hwu : w = u + 1
          · subst hwu; exact h1
          · exact h w ⟨hw.1, by omega⟩
        by_cases h2 : mkrMissPred res u σ
        · rw [ite_eq_left h2, ite_eq_left h1, ite_eq_left (heqv.mp h2)]
        · rw [ite_eq_right h2, ite_eq_right (mt heqv.mpr h2)]
    have hhit_eq (w : ℕ) (hw : w ∈ Finset.Icc 1 u) :
        Γ'.restrict (mkrHitPred res w) = Γ.restrict (mkrHitPred res w) := by
      apply Subtype.ext; funext σ
      simp only [Γ', CQState.restrict_coe]
      by_cases hw_p : mkrHitPred res w σ
      · have hne : ¬ mkrHitPred res (u + 1) σ := by
          rcases Finset.mem_Icc.mp hw with ⟨_, hwu⟩
          dsimp only [mkrHitPred] at hw_p ⊢
          omega
        rw [ite_eq_left hw_p, ite_eq_left hne, ite_eq_left hw_p]
      · rw [ite_eq_right hw_p, ite_eq_right hw_p]
    obtain ⟨htr_ih, hcost_ih⟩ := ih Γ'
    rw [hmiss_eq, Finset.sum_congr rfl fun w hw ↦ by rw [hhit_eq w hw]] at htr_ih hcost_ih
    have htr_top := Γ.trace_restrict_add_trace_restrict_not (mkrHitPred res (u + 1))
    dsimp only [mkrDispHits, compile]
    rw [expectedCost_qIf]
    change _ ∧ expectedCost model ((onHit (u + 1)).compile qAssign oracle)
        (Γ.restrict (mkrHitPred res (u + 1))) +
        expectedCost model ((mkrDispHits res onHit onZero u).compile qAssign oracle) Γ' = _
    rw [hcost_ih]
    have hsucc_tr :
        (∑ w ∈ Finset.Icc 1 (u + 1), (Γ.restrict (mkrHitPred res w)).trace) =
          (∑ w ∈ Finset.Icc 1 u, (Γ.restrict (mkrHitPred res w)).trace) +
            (Γ.restrict (mkrHitPred res (u + 1))).trace :=
      Finset.sum_Icc_succ_top (by omega) _
    have hsucc_c :
        (∑ w ∈ Finset.Icc 1 (u + 1),
          expectedCost model ((onHit w).compile qAssign oracle)
            (Γ.restrict (mkrHitPred res w))) =
        (∑ w ∈ Finset.Icc 1 u,
          expectedCost model ((onHit w).compile qAssign oracle)
            (Γ.restrict (mkrHitPred res w))) +
          expectedCost model ((onHit (u + 1)).compile qAssign oracle)
            (Γ.restrict (mkrHitPred res (u + 1))) :=
      Finset.sum_Icc_succ_top (by omega) _
    refine ⟨by rw [hsucc_tr, ← add_assoc, htr_ih, add_comm]; exact htr_top, ?_⟩
    rw [hsucc_c]
    abel

theorem mkrExpect_restrict_valid_branches {Var : Type} {n m_tot k s b : ℕ}
    (res : Var) {S : Finset (Fin (2 ^ n))}
    {Δ₁ : CQState (Store Var) (2 ^ (m_tot * (n + 1) + k * n))}
    (hdisp : 𝔼[Δ₁, mkrDispPre res n m_tot k S s b] = Δ₁.trace) :
    𝔼[Δ₁.restrict (mkrMissPred res b), validObs n m_tot k S s] =
        (Δ₁.restrict (mkrMissPred res b)).trace ∧
      ∀ w ∈ Finset.Icc 1 b,
        𝔼[Δ₁.restrict (mkrHitPred res w), validObs n m_tot k S (s + w)] =
          (Δ₁.restrict (mkrHitPred res w)).trace := by
  have hexp_part (p : Store Var → Prop) [DecidablePred p] :
      𝔼[Δ₁.restrict p, mkrDispPre res n m_tot k S s b] = (Δ₁.restrict p).trace := by
    have hpart : 𝔼[Δ₁, mkrDispPre res n m_tot k S s b] =
        𝔼[Δ₁.restrict p, mkrDispPre res n m_tot k S s b] +
          𝔼[Δ₁.restrict (¬ p ·), mkrDispPre res n m_tot k S s b] := by
      simpa using
        expect_ite_partition p Δ₁
          (mkrDispPre res n m_tot k S s b) (mkrDispPre res n m_tot k S s b)
    have h1 : 𝔼[Δ₁.restrict p, mkrDispPre res n m_tot k S s b] ≤ (Δ₁.restrict p).trace := by
      rw [← expect_top (Δ₁.restrict p)]; exact expect_mono le_rfl le_top
    have h2 : 𝔼[Δ₁.restrict (¬ p ·), mkrDispPre res n m_tot k S s b] ≤
        (Δ₁.restrict (¬ p ·)).trace := by
      rw [← expect_top (Δ₁.restrict (¬ p ·))]; exact expect_mono le_rfl le_top
    have htr : ((Δ₁.restrict p).trace : ℝ) + (Δ₁.restrict (¬ p ·)).trace = Δ₁.trace := by
      exact_mod_cast Δ₁.trace_restrict_add_trace_restrict_not p
    linarith
  have hcongr (p : Store Var → Prop) [DecidablePred p]
      (Θ : CQAssertion (Store Var) (2 ^ (m_tot * (n + 1) + k * n)))
      (hσ : ∀ σ, p σ → mkrDispPre res n m_tot k S s b σ = Θ σ) :
      𝔼[Δ₁.restrict p, Θ] = 𝔼[Δ₁.restrict p, mkrDispPre res n m_tot k S s b] := by
    rw [expect_eq_tsum, expect_eq_tsum]
    refine tsum_congr fun σ ↦ ?_
    by_cases hp : p σ
    · simp [CQState.restrict_coe, hp, hσ σ hp]
    · simp [CQState.restrict_coe, hp]
  refine ⟨?_, fun w hw ↦ ?_⟩
  · rw [hcongr (mkrMissPred res b) _ fun σ hp ↦ by
      have hf : ¬ (1 ≤ σ res ∧ σ res ≤ (b : ℤ)) := fun h1b ↦ by
        let w₀ := (σ res).toNat
        have hw₀ : w₀ ∈ Finset.Icc 1 b := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact hp w₀ hw₀ (by omega)
      dsimp only [mkrDispPre]
      rw [ite_eq_right hf]]
    exact hexp_part (mkrMissPred res b)
  · rw [hcongr (mkrHitPred res w) _ fun σ hp ↦ by
      rcases Finset.mem_Icc.mp hw with ⟨hw1, hwb⟩
      dsimp only [mkrHitPred] at hp
      have ht : 1 ≤ σ res ∧ σ res ≤ (b : ℤ) := by omega
      have hnat : (σ res).toNat = w := by omega
      dsimp only [mkrDispPre]
      rw [ite_eq_left ht, hnat]]
    exact hexp_part (mkrHitPred res w)

/- ## 2. Top-Slice Subregisters & Lifted Eigenvalue-Locking Fallback -/

theorem mkrPadEq (n m L_max L : ℕ) (hL : L ≤ L_max) :
    (((L_max - L) * m) * (n + 1)) + ((L * m) * (n + 1)) = (L_max * m) * (n + 1) := by
  rw [← Nat.add_mul, ← Nat.add_mul, Nat.sub_add_cancel hL]

theorem mkrPadEq1 (n m L_max : ℕ) (hL1 : 1 ≤ L_max) :
    (((L_max - 1) * m) * (n + 1)) + (m * (n + 1)) = (L_max * m) * (n + 1) := by
  simpa [Nat.one_mul] using mkrPadEq n m L_max 1 hL1

/-- Top-slice `L * m`-slot subregister sharing the `k * n`-qubit archive inside `L_max * m`. -/
abbrev mkrSubRegL (n m k L_max L : ℕ) (hL : L ≤ L_max) :
    QRegister ((L * m) * (n + 1) + k * n) ((L_max * m) * (n + 1) + k * n) :=
  mkrTopSliceReg (((L_max - L) * m) * (n + 1)) ((L * m) * (n + 1))
    ((L_max * m) * (n + 1)) (k * n) (mkrPadEq n m L_max L hL)

/-- Top-slice `1 * m`-slot subregister sharing the `k * n`-qubit archive inside `L_max * m`. -/
abbrev mkrSubReg1 (n m k L_max : ℕ) (hL1 : 1 ≤ L_max) :
    QRegister (m * (n + 1) + k * n) ((L_max * m) * (n + 1) + k * n) :=
  mkrTopSliceReg (((L_max - 1) * m) * (n + 1)) (m * (n + 1))
    ((L_max * m) * (n + 1)) (k * n) (mkrPadEq1 n m L_max hL1)

/-- Single `1 * m`-lane `eigLockStage` lifted into the `(L_max * m)`-slot register. -/
noncomputable def mkrLiftEigLockStage {Var : Type} (res : Var) (n m k L_max : ℕ)
    (hL1 : 1 ≤ L_max) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) (s : Fin k) :
    OracleCirc Var ((L_max * m) * (n + 1) + k * n) ((n + 1) * m) :=
  mkrLiftCirc (mkrSubReg1 n m k L_max hL1) (eigLockStage res n m k hm_grid hk_grid hn200 s)

theorem wp_mkrLiftEigLockStage_ge {Var : Type} [DecidableEq Var] {n m k L_max : ℕ}
    (res : Var) (hL1 : 1 ≤ L_max) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k) :
    validObs (Var := Var) n (L_max * m) k S s.val ≤
      wp ((mkrLiftEigLockStage res n m k L_max hL1 hm_grid hk_grid hn200 s).compile qAssign
          (groverParallelMarkingOracle m S))
        (validObs n (L_max * m) k S (s.val + 1)) := by
  unfold mkrLiftEigLockStage
  rw [← mkrEmbedAssn_validObs (Var := Var) (mkrPadEq1 n m L_max hL1) S s.val,
    ← mkrEmbedAssn_validObs (Var := Var) (mkrPadEq1 n m L_max hL1) S (s.val + 1),
    wp_mkrLiftCirc]
  exact mkrEmbedAssn_mono _ ((eigLockStage_wp_and_active res hm_grid hk_grid hn200 hcard s).1)

theorem expectedCost_mkrLiftEigLockStage_le {Var : Type} [DecidableEq Var] {n m k L_max : ℕ}
    (res : Var) (hL1 : 1 ≤ L_max) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k)
    {Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n))}
    (hV : 𝔼[Δ, validObs n (L_max * m) k S s.val] = Δ.trace) :
    expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((mkrLiftEigLockStage res n m k L_max hL1 hm_grid hk_grid hn s).compile qAssign
        (groverParallelMarkingOracle m S)) Δ ≤
      stateMass Δ * ENNReal.ofReal (stageCostReal n m (k - s.val)) := by
  set r := k - s.val
  set p := oddFrac n m r
  set K := subSchedule p
  set q := subFailProb p K
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
  have hq0 : 0 ≤ q := subFailProb_nonneg p K
  have hq1 : q < 1 := hhyps.2.2.2.2
  have h1q_pos : 0 < 1 - q := sub_pos.mpr hq1
  let oracle := groverParallelMarkingOracle m S
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  let r1 := mkrSubReg1 n m k L_max hL1
  let model : CostModel (2 ^ ((L_max * m) * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
  let setup0 := eigSetup (Var := Var) res n m k s K
  let body0 := eigBody (Var := Var) res n m k hm1 s (subTargetRatio p K) hhyps.1.le hhyps.2.1.le
  let readout0 := eigReadout (Var := Var) n m k s
  let setupP := (mkrLiftCirc r1 setup0).compile qAssign oracle
  let bodyP := (mkrLiftCirc r1 body0).compile qAssign oracle
  let readoutP := (mkrLiftCirc r1 readout0).compile qAssign oracle
  let guard : Store Var → Prop := fun σ ↦ σ res = 0
  have hact := (eigLockStage_wp_and_active res hm_grid hk_grid hn hcard s).2
  have hinv0 : 𝔼[Δ, invalidObs n (L_max * m) k S s.val] = 0 := expect_invalidObs_eq_zero hV
  set Δ₁ := (interp setupP).toStateFun Δ
  set Δ₂ := (interp (.qWhile guard bodyP)).toStateFun Δ₁
  have hst_ph : ∀ active,
      mkrStaticOracleCalls (deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
        (Q := m * (n + 1) + k * n) le_rfl active) = some 1 := fun _ ↦ rfl
  have hst_iter : ∀ t : ℕ,
      mkrStaticOracleCalls (groverSubIter (Var := Var) n m k (memPrefix k s.val) t) = some t :=
    fun t ↦ by
      induction t with
      | zero => rfl
      | succ t ih =>
        unfold groverSubIter
        dsimp only [mkrStaticOracleCalls]
        rw [ih, hst_ph]
  have hst_setup : mkrStaticOracleCalls setup0 = some (K + 1) := by
    dsimp only [setup0]
    unfold eigSetup workReset
    dsimp only [mkrStaticOracleCalls]
    rw [mkrStaticOracleCalls_mapAndMeasureLow, hst_iter K, hst_ph]
    exact congrArg some (by omega)
  have hst_body : mkrStaticOracleCalls body0 = some 1 := by
    dsimp only [body0]; unfold eigBody; dsimp only [mkrStaticOracleCalls]; rw [hst_ph]
  have hst_read : mkrStaticOracleCalls readout0 = some 1 := by
    dsimp only [readout0]; unfold eigReadout markAndWrite deflatedOracle; rfl
  have hsetup_le : expectedCost model setupP Δ ≤ stateMass Δ * ((K + 1 : ℕ) : ℝ≥0∞) := by
    simpa using costBound_mkrLiftCirc_of_staticOracleCalls r1 hor setup0 (K + 1) hst_setup Δ
  have hread_le : expectedCost model readoutP Δ₂ ≤ stateMass Δ * 1 := by
    have h1 := costBound_mkrLiftCirc_of_staticOracleCalls r1 hor readout0 1 hst_read Δ₂
    have hm2 : stateMass Δ₂ ≤ stateMass Δ :=
      (stateMass_interp_le (.qWhile guard bodyP) Δ₁).trans (stateMass_interp_le setupP Δ)
    simpa using h1.trans (mul_le_mul_of_nonneg_right hm2 zero_le)
  have hiter_le (t : ℕ) :
      stateMass (activeIter guard bodyP t Δ₁) ≤ stateMass Δ * (ENNReal.ofReal q) ^ t := by
    rw [← ofReal_expect_whileActiveWP, ← wp_expectation_eq setupP Δ]
    have hwp_le :
        wp setupP (whileActiveWP (wp bodyP) guard t) ≤
          (scaledValidObs n (L_max * m) k S s.val (q ^ t)
              (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)).add
            (invalidObs n (L_max * m) k S s.val)
            (scaledValid_add_invalid_le_one n (L_max * m) k S s.val (q ^ t) _ _) := by
      dsimp only [setupP, bodyP, r1]
      rw [whileActiveWP_mkrLiftCirc, wp_mkrLiftCirc]
      refine (mkrEmbedAssn_mono _ (hact t)).trans_eq ?_
      rw [mkrEmbedAssn_add]
      congr 1
      · exact mkrEmbedAssn_scaledValidObs (mkrPadEq1 n m L_max hL1) S s.val (q ^ t) _ _
      · exact mkrEmbedAssn_invalidObs (mkrPadEq1 n m L_max hL1) S s.val
    have hexp_le : 𝔼[Δ, wp setupP (whileActiveWP (wp bodyP) guard t)] ≤ q ^ t * Δ.trace := by
      calc 𝔼[Δ, wp setupP (whileActiveWP (wp bodyP) guard t)]
          ≤ 𝔼[Δ, (scaledValidObs n (L_max * m) k S s.val (q ^ t)
              (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)).add
              (invalidObs n (L_max * m) k S s.val)
              (scaledValid_add_invalid_le_one n (L_max * m) k S s.val (q ^ t) _ _)] :=
            expect_mono le_rfl hwp_le
        _ = 𝔼[Δ, scaledValidObs n (L_max * m) k S s.val (q ^ t)
              (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)] +
            𝔼[Δ, invalidObs n (L_max * m) k S s.val] :=
            expect_assertion_add _ _ _ _
        _ = q ^ t * 𝔼[Δ, validObs n (L_max * m) k S s.val] + 0 := by
            rw [hinv0, expect_eq_mul_of_apply_eq_smul Δ (q ^ t)
              (scaledValidObs_smul n (L_max * m) k S s.val (q ^ t) _ _)]
        _ = q ^ t * Δ.trace := by rw [hV, add_zero]
    calc ENNReal.ofReal 𝔼[Δ, wp setupP (whileActiveWP (wp bodyP) guard t)]
        ≤ ENNReal.ofReal (q ^ t * Δ.trace) := ENNReal.ofReal_le_ofReal hexp_le
      _ = stateMass Δ * (ENNReal.ofReal q) ^ t := by
          rw [mul_comm, ENNReal.ofReal_mul (by exact_mod_cast Δ.trace_nonneg),
            ← stateMass_eq_ofReal_trace, ENNReal.ofReal_pow hq0]
  have hwhile_le :
      expectedCost model (.qWhile guard bodyP) Δ₁ ≤
        stateMass Δ * ENNReal.ofReal (1 - q)⁻¹ := by
    have hb : CostBound (Var := Var) model bodyP 1 := by
      simpa using costBound_mkrLiftCirc_of_staticOracleCalls r1 hor body0 1 hst_body
    calc expectedCost model (.qWhile guard bodyP) Δ₁
        ≤ expectedIterations guard bodyP Δ₁ * (1 : ℝ≥0) :=
          expectedCost_qWhile_le hb guard Δ₁
      _ = ∑' t : ℕ, stateMass (activeIter guard bodyP t Δ₁) := by
          simp [expectedIterations]
      _ ≤ ∑' t : ℕ, stateMass Δ * (ENNReal.ofReal q) ^ t :=
          ENNReal.tsum_le_tsum hiter_le
      _ = stateMass Δ * (1 - ENNReal.ofReal q)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = stateMass Δ * ENNReal.ofReal (1 - q)⁻¹ := by
          have hsub : 1 - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
            simpa using (ENNReal.ofReal_sub 1 hq0).symm
          rw [hsub, ENNReal.ofReal_inv_of_pos h1q_pos]
  change expectedCost model (setupP ;; (.qWhile guard bodyP ;; readoutP)) Δ ≤ _
  rw [expectedCost_qSeq, expectedCost_qSeq]
  calc expectedCost model setupP Δ +
        (expectedCost model (.qWhile guard bodyP) Δ₁ + expectedCost model readoutP Δ₂)
      ≤ stateMass Δ * ((K + 1 : ℕ) : ℝ≥0∞) +
          (stateMass Δ * ENNReal.ofReal (1 - q)⁻¹ + stateMass Δ * 1) :=
        add_le_add hsetup_le (add_le_add hwhile_le hread_le)
    _ = stateMass Δ * (((K + 1 : ℕ) : ℝ≥0∞) + ENNReal.ofReal (1 - q)⁻¹ + 1) := by ring
    _ = stateMass Δ * ENNReal.ofReal (stageCostReal n m r) := by
        congr 1
        have hK1 : ((K + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((K : ℝ) + 1) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg K) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one]
        have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        rw [hK1, h1, ← ENNReal.ofReal_add (by positivity) (inv_nonneg.mpr h1q_pos.le),
          ← ENNReal.ofReal_add (by positivity) zero_le_one]
        dsimp only [stageCostReal, p, K, q]
        congr 1
        ring

theorem mkrValidState_step {Var : Type} [DecidableEq Var] {n m_tot k j j' : ℕ}
    {S : Finset (Fin (2 ^ n))} {P : QProg Var (2 ^ (m_tot * (n + 1) + k * n))}
    {Δ : CQState (Store Var) (2 ^ (m_tot * (n + 1) + k * n))}
    (hV : 𝔼[Δ, validObs n m_tot k S j] = Δ.trace)
    (hwp : validObs n m_tot k S j ≤ wp P (validObs n m_tot k S j')) :
    let Δ' := (interp P).toStateFun Δ
    𝔼[Δ', validObs n m_tot k S j'] = Δ'.trace ∧ stateMass Δ' = stateMass Δ := by
  intro Δ'
  have h1 : (Δ.trace : ℝ) ≤ 𝔼[Δ', validObs n m_tot k S j'] := by
    rw [← hV, ← wp_expectation_eq]
    exact expect_mono le_rfl hwp
  have h2 : 𝔼[Δ', validObs n m_tot k S j'] ≤ (Δ'.trace : ℝ) := by
    rw [← expect_top Δ']
    exact expect_mono le_rfl le_top
  have h3 : (Δ'.trace : ℝ) ≤ (Δ.trace : ℝ) := by
    exact_mod_cast (interp P).trace_toStateFun_le Δ
  refine ⟨by linarith, ?_⟩
  rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace,
    show (Δ'.trace : ℝ) = Δ.trace by linarith]

theorem mkrStageCostReal_le_linear_S0 {n m k r : ℕ} (hn : 600 ≤ n)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    0 ≤ stageCostReal n m r ∧
      stageCostReal n m r ≤
        (π / 8 + 1 / 4) * √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) + 5 := by
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  have hr_hi : r ≤ 1024 := hrk.trans hk_hi
  have h2r_le : 2 * r ≤ 2 ^ n := by
    calc 2 * r ≤ 2 * 1024 := by omega
      _ ≤ 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hr_lt : r < 2 ^ n := by omega
  set p := oddFrac n m r
  set K := subSchedule p
  have hp_pos : 0 < p := (oddFrac_pos_lt_one hm1 hr1 hr_lt).1
  set p₀ : ℝ := ((m : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)
  set S₀ : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))
  have hmr_pos : (0 : ℝ) < (m : ℝ) * (r : ℝ) := by positivity
  have hmr_le : (m : ℝ) * (r : ℝ) ≤ 16 ^ 5 := by
    have : m * r ≤ 1024 * 1024 := Nat.mul_le_mul hm_hi hr_hi
    calc (m : ℝ) * (r : ℝ) = ((m * r : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((1024 * 1024 : ℕ) : ℝ) := by exact_mod_cast this
      _ = 16 ^ 5 := by norm_num
  have h2n_ge : (16 ^ 150 : ℝ) ≤ (2 ^ n : ℝ) := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hS0_sq : S₀ ^ 2 = (2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)) := Real.sq_sqrt (by positivity)
  have hS0_sq_ge : (16 : ℝ) ^ 145 ≤ S₀ ^ 2 := by
    rw [hS0_sq, le_div_iff₀ hmr_pos]
    calc (16 : ℝ) ^ 145 * ((m : ℝ) * (r : ℝ))
        ≤ (16 : ℝ) ^ 145 * (16 : ℝ) ^ 5 := mul_le_mul_of_nonneg_left hmr_le (by positivity)
      _ = (16 : ℝ) ^ 150 := by norm_num
      _ ≤ (2 ^ n : ℝ) := h2n_ge
  have hS0_ge : (4 : ℝ) ^ 145 ≤ S₀ := by
    have h145 : ((4 : ℝ) ^ 145) ^ 2 = (16 : ℝ) ^ 145 := by norm_num
    nlinarith [Real.sqrt_nonneg ((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))]
  rcases oddFrac_sandwich (m := m) h2r_le with ⟨hp_lo, hp_hi⟩
  change p₀ * (1 - p₀) ≤ p at hp_lo
  change p ≤ p₀ at hp_hi
  have hp0_inv : p₀ * S₀ ^ 2 = 1 := by
    rw [hS0_sq]; dsimp only [p₀]; field_simp [hmr_pos.ne']
  have h1_div_sqrt_ge : S₀ ≤ 1 / √p := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hp_pos)]
    have hle : √p ≤ √p₀ := Real.sqrt_le_sqrt hp_hi
    have hmul : S₀ * √p₀ = 1 := by
      have hsq : (S₀ * √p₀) ^ 2 = 1 := by
        rw [mul_pow, hS0_sq, Real.sq_sqrt (by positivity)]
        dsimp only [p₀]; field_simp [hmr_pos.ne']
      nlinarith [show 0 ≤ S₀ * √p₀ by positivity]
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq hmul
  have hs16 : 16 ≤ 1 / √p := by
    calc (16 : ℝ) ≤ (4 : ℝ) ^ 145 := by norm_num
      _ ≤ S₀ := hS0_ge
      _ ≤ 1 / √p := h1_div_sqrt_ge
  have h1_div_sqrt_le : 1 / √p ≤ S₀ + 1 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hp_pos)]
    suffices hsq : 1 ≤ ((S₀ + 1) * √p) ^ 2 by
      nlinarith [show 0 ≤ (S₀ + 1) * √p by positivity]
    rw [mul_pow, Real.sq_sqrt hp_pos.le]
    have hp0_eq : p₀ = 1 / S₀ ^ 2 := by rw [eq_div_iff (by positivity)]; exact hp0_inv
    have hpoly : 1 ≤ (S₀ + 1) ^ 2 * (p₀ * (1 - p₀)) := by
      rw [hp0_eq, ← sub_nonneg]
      have hS4 : (0 : ℝ) < S₀ ^ 4 := by positivity
      have hnum :
          (S₀ + 1) ^ 2 * (1 / S₀ ^ 2 * (1 - 1 / S₀ ^ 2)) - 1 =
            (2 * S₀ ^ 3 - 2 * S₀ - 1) / S₀ ^ 4 := by
        field_simp [show S₀ ≠ 0 by positivity]; ring
      rw [hnum]
      refine div_nonneg ?_ hS4.le
      have hS2 : (2 : ℝ) ≤ S₀ := le_trans (by norm_num) hS0_ge
      have hdecomp : 2 * S₀ ^ 3 - 2 * S₀ - 1 =
          (S₀ - 2) * (2 * S₀ ^ 2 + 4 * S₀ + 6) + 11 := by ring
      rw [hdecomp]
      have hsub : 0 ≤ S₀ - 2 := by linarith
      positivity
    exact hpoly.trans (mul_le_mul_of_nonneg_left hp_lo (sq_nonneg _))
  obtain ⟨hhyps, hqbound⟩ := subSchedule_hyps_le hp_pos hs16
  have h1q_pos : 0 < 1 - subFailProb p K := sub_pos.mpr hhyps.2.2.2.2
  have hnn : 0 ≤ stageCostReal n m r := by dsimp only [stageCostReal, p, K]; positivity
  refine ⟨hnn, ?_⟩
  have hπ_hi : π < 4 := Real.pi_lt_four
  dsimp only [stageCostReal, p, K]
  have h1 : (π / 8 + 1 / 4) * (1 / √p) ≤ (π / 8 + 1 / 4) * (S₀ + 1) :=
    mul_le_mul_of_nonneg_left h1_div_sqrt_le (by positivity)
  linarith

/-- Sequential fallback cascade of lifted `eigLockStage` calls from `j` to `k`. -/
noncomputable def mkrLiftEigLockStagesFrom {Var : Type} (res : Var) (n m k L_max : ℕ)
    (hL1 : 1 ≤ L_max) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) :
    (j : ℕ) → OracleCirc Var ((L_max * m) * (n + 1) + k * n) ((n + 1) * m)
  | j =>
      if hj : j < k then
        .seq (mkrLiftEigLockStage res n m k L_max hL1 hm_grid hk_grid hn200 ⟨j, hj⟩)
          (mkrLiftEigLockStagesFrom res n m k L_max hL1 hm_grid hk_grid hn200 (j + 1))
      else .skip
termination_by j => k - j

theorem wp_mkrLiftEigLockStagesFrom_ge {Var : Type} [DecidableEq Var] {n m k L_max : ℕ}
    (res : Var) (hL1 : 1 ≤ L_max) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k →
      validObs (Var := Var) n (L_max * m) k S j ≤
        wp ((mkrLiftEigLockStagesFrom res n m k L_max hL1 hm_grid hk_grid hn200 j).compile qAssign
            (groverParallelMarkingOracle m S))
          (validObs n (L_max * m) k S k)
  | 0, j, hd, _ => by
    have hjeq : j = k := by omega
    subst hjeq
    rw [mkrLiftEigLockStagesFrom]
    simp
  | d + 1, j, hd, _ => by
    have hj : j < k := by omega
    rw [mkrLiftEigLockStagesFrom, dite_eq_left hj]
    dsimp only [compile]
    rw [wp_qSeq]
    have hih := wp_mkrLiftEigLockStagesFrom_ge res hL1 hm_grid hk_grid hn200 hcard d (j + 1)
      (by omega) (by omega)
    exact (wp_mkrLiftEigLockStage_ge res hL1 hm_grid hk_grid hn200 hcard ⟨j, hj⟩).trans
      (wp_mono _ hih)

theorem expectedCost_mkrLiftEigLockStagesFrom_le {Var : Type} [DecidableEq Var]
    {n m k L_max : ℕ} (res : Var) (hL1 : 1 ≤ L_max) (hm_grid : m ∈ groverGrid)
    (hk_grid : k ∈ groverGrid) (hn600 : 600 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k →
      ∀ Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n)),
        𝔼[Δ, validObs n (L_max * m) k S j] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          ((mkrLiftEigLockStagesFrom res n m k L_max hL1 hm_grid hk_grid (by omega) j).compile
            qAssign (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ * ENNReal.ofReal ((2 * (d : ℝ)) * √(2 ^ n : ℝ))
  | 0, j, hd, _, Δ, _ => by
    have hjeq : j = k := by omega
    subst hjeq
    rw [mkrLiftEigLockStagesFrom, dite_eq_right (lt_irrefl j)]
    simp [compile]
  | d + 1, j, hd, _, Δ, hV => by
    have hj : j < k := by omega
    have hn200 : 200 ≤ n := by omega
    rw [mkrLiftEigLockStagesFrom, dite_eq_left hj]
    dsimp only [compile]
    rw [expectedCost_qSeq]
    let stageP :=
      (mkrLiftEigLockStage (Var := Var) res n m k L_max hL1 hm_grid hk_grid hn200 ⟨j, hj⟩).compile
        qAssign (groverParallelMarkingOracle m S)
    have hwp_st :=
      wp_mkrLiftEigLockStage_ge (Var := Var) res hL1 hm_grid hk_grid hn200 hcard ⟨j, hj⟩
    have hstep_V := mkrValidState_step hV hwp_st
    have hcost_st := expectedCost_mkrLiftEigLockStage_le res hL1 hm_grid hk_grid hn200 hcard
      ⟨j, hj⟩ hV
    have hih := expectedCost_mkrLiftEigLockStagesFrom_le res hL1 hm_grid hk_grid hn600 hcard
      d (j + 1) (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
    rw [hstep_V.2] at hih
    have hlin := mkrStageCostReal_le_linear_S0 (k := k) (r := k - j) hn600 hm_grid hk_grid
      (by omega) (by omega)
    have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    have hmr1 : (1 : ℝ) ≤ (m : ℝ) * ((k - j : ℕ) : ℝ) := by
      have : 1 ≤ m * (k - j) := by simpa using Nat.mul_le_mul hm1 (by omega : 1 ≤ k - j)
      exact_mod_cast this
    have hsq_le : √((2 ^ n : ℝ) / ((m : ℝ) * ((k - j : ℕ) : ℝ))) ≤ √(2 ^ n : ℝ) :=
      Real.sqrt_le_sqrt (div_le_self (by positivity) hmr1)
    have h5_le : (5 : ℝ) ≤ √(2 ^ n : ℝ) := by
      have h25 : (25 : ℝ) ≤ (2 ^ n : ℝ) := by
        calc (25 : ℝ) ≤ (2 : ℝ) ^ 5 := by norm_num
          _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      calc (5 : ℝ) = √(25 : ℝ) := by norm_num
        _ ≤ √(2 ^ n : ℝ) := Real.sqrt_le_sqrt h25
    have hcoef_le : (π / 8 + 1 / 4) ≤ 1 := by linarith [Real.pi_lt_four]
    have hst_bound : stageCostReal n m (k - j) ≤ 2 * √(2 ^ n : ℝ) := by
      calc stageCostReal n m (k - j)
          ≤ (π / 8 + 1 / 4) * √((2 ^ n : ℝ) / ((m : ℝ) * ((k - j : ℕ) : ℝ))) + 5 := hlin.2
        _ ≤ 1 * √(2 ^ n : ℝ) + √(2 ^ n : ℝ) :=
            add_le_add (mul_le_mul hcoef_le hsq_le (Real.sqrt_nonneg _) zero_le_one) h5_le
        _ = 2 * √(2 ^ n : ℝ) := by ring
    calc expectedCost _ stageP Δ + expectedCost _ _ ((interp stageP).toStateFun Δ)
        ≤ stateMass Δ * ENNReal.ofReal (2 * √(2 ^ n : ℝ)) +
            stateMass Δ * ENNReal.ofReal ((2 * (d : ℝ)) * √(2 ^ n : ℝ)) :=
          add_le_add
            (hcost_st.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hst_bound)
              zero_le))
            hih
      _ = stateMass Δ *
            (ENNReal.ofReal (2 * √(2 ^ n : ℝ)) +
              ENNReal.ofReal ((2 * (d : ℝ)) * √(2 ^ n : ℝ))) := by ring
      _ = stateMass Δ * ENNReal.ofReal ((2 * ((d + 1 : ℕ) : ℝ)) * √(2 ^ n : ℝ)) := by
          congr 1
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; push_cast; ring

end
end QuantumComputation.Specs.DickeSol

namespace QuantumComputation.Specs.DickeSol

open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace

@[expose] public section

/-- Continuation segment of a width-ramped multiplexed pass at block multiplicity `lSeg`. -/
structure RampMuxSeg (N m : ℕ) : Type where
  lSeg : ℕ
  ops : List (MuxSymOp N (lSeg * m))

/-- Final block multiplicity `L_S` of `(L₀, ops₀)` followed by `segs`. -/
def rmsEndL {N m : ℕ} : ℕ → List (RampMuxSeg N m) → ℕ
  | L, [] => L
  | _, seg :: rest => rmsEndL seg.lSeg rest

/-- Non-decreasing multiplicity invariant `L₀ ≤ L₁ ≤ ⋯ ≤ L_S`. -/
def rmsSegsMono {N m : ℕ} : ℕ → List (RampMuxSeg N m) → Prop
  | _, [] => True
  | L, seg :: rest => L ≤ seg.lSeg ∧ rmsSegsMono seg.lSeg rest

/-- Total oracle query count across all pass segments (excluding final `+ L_end` deflation). -/
def rmsSegsQueryCount {N m : ℕ} :
    ∀ (L₀ : ℕ), List (MuxSymOp N (L₀ * m)) → List (RampMuxSeg N m) → ℕ
  | L₀, ops₀, [] => L₀ * muxOpsQueryCount ops₀
  | L₀, ops₀, seg :: rest =>
      L₀ * muxOpsQueryCount ops₀ + rmsSegsQueryCount seg.lSeg seg.ops rest

/-- Sequential symmetric-subspace evolution across `(L₀, ops₀)` and `segs`. -/
noncomputable def evalRampMuxSegs {N m : ℕ} (R : Finset (Fin N)) :
    ∀ (L₀ : ℕ), List (MuxSymOp N (L₀ * m)) →
      ∀ (segs : List (RampMuxSeg N m)),
        (SymSubset N (L₀ * m) → ℝ) → (SymSubset N (rmsEndL L₀ segs * m) → ℝ)
  | _, ops₀, [], v => evalMuxSymOps R ops₀ v
  | L₀, ops₀, seg :: rest, v =>
      let v₁ := evalMuxSymOps R ops₀ v
      let v₂ : SymSubset N (seg.lSeg * m) → ℝ :=
        if h : L₀ = seg.lSeg then
          h ▸ v₁
        else
          stepUpFrom N (L₀ * m) (seg.lSeg * m) *ᵥ v₁
      evalRampMuxSegs R seg.lSeg seg.ops rest v₂

/-- Active work-prefix register `[0.. (l * m) * (n + 1) - 1]` inside `(L * m) * (n + 1)`. -/
def rmsActiveWorkReg (n m L l : ℕ) (hl : l ≤ L) :
    QRegister ((l * m) * (n + 1)) ((L * m) * (n + 1)) :=
  QRegister.block 0 ((l * m) * (n + 1)) (by
    rw [Nat.zero_add]
    exact Nat.mul_le_mul_right (n + 1) (Nat.mul_le_mul_right m hl))

/-- Relative work-prefix register `[0.. M₁ * (n + 1) - 1]` inside `M₂ * (n + 1)`. -/
def rmsRelWorkReg (n M₁ M₂ : ℕ) (hM : M₁ ≤ M₂) :
    QRegister (M₁ * (n + 1)) (M₂ * (n + 1)) :=
  QRegister.block 0 (M₁ * (n + 1)) (by
    rw [Nat.zero_add]
    exact Nat.mul_le_mul_right (n + 1) hM)

/-- Split subregister selecting low `W₁` work wires and shared `M` archive wires inside `W₂
  + M`. -/
def rmsSubReg (W₁ W₂ M : ℕ) (hW : W₁ ≤ W₂) : QRegister (W₁ + M) (W₂ + M) :=
  (QRegister.block 0 W₁ (by omega)).concat (highBlock W₂ M)
    (QRegister.block_disjoint_of_le 0 W₁ W₂ M (by omega) (by omega) (by omega))

end

public section

theorem rmsEndL_ge {N m : ℕ} :
    ∀ {L₀ : ℕ} {segs : List (RampMuxSeg N m)}, rmsSegsMono L₀ segs → L₀ ≤ rmsEndL L₀ segs
  | _, [], _ => le_rfl
  | _, _ :: _, h => h.1.trans (rmsEndL_ge h.2)

theorem sum_sq_evalRampMuxSegs {N m : ℕ} (R : Finset (Fin N)) :
    ∀ {L₀ : ℕ} (ops₀ : List (MuxSymOp N (L₀ * m))) (segs : List (RampMuxSeg N m)),
      rmsSegsMono L₀ segs → 2 * (rmsEndL L₀ segs * m) ≤ N →
      ∀ (v : SymSubset N (L₀ * m) → ℝ),
        (∑ E : SymSubset N (rmsEndL L₀ segs * m), (evalRampMuxSegs R L₀ ops₀ segs v E) ^ 2) =
          ∑ E : SymSubset N (L₀ * m), (v E) ^ 2
  | _, ops₀, [], _, _, v => sum_sq_evalMuxSymOps R ops₀ v
  | L₀, ops₀, seg :: rest, hmono, h2Le, v => by
    let v₁ := evalMuxSymOps R ops₀ v
    let v₂ : SymSubset N (seg.lSeg * m) → ℝ :=
      if h : L₀ = seg.lSeg then h ▸ v₁ else stepUpFrom N (L₀ * m) (seg.lSeg * m) *ᵥ v₁
    refine (sum_sq_evalRampMuxSegs R seg.ops rest hmono.2 h2Le v₂).trans ?_
    dsimp only [v₂, v₁]
    by_cases hEq : L₀ = seg.lSeg
    · subst hEq
      simp only [↓reduceDIte]
      exact sum_sq_evalMuxSymOps R ops₀ v
    · rw [dite_eq_right hEq]
      have hl₂ : seg.lSeg ≤ rmsEndL seg.lSeg rest := rmsEndL_ge hmono.2
      have h2M2 : 2 * (seg.lSeg * m) ≤ N :=
        (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right m hl₂)).trans h2Le
      have hStS := stepUpFrom_transpose_mul_self (Nat.mul_le_mul_right m hmono.1) h2M2
      have hdot :
          (∑ E, ((stepUpFrom N (L₀ * m) (seg.lSeg * m) *ᵥ evalMuxSymOps R ops₀ v) E) ^ 2) =
            ∑ E₁, (evalMuxSymOps R ops₀ v E₁) ^ 2 := by
        change finVecSqNorm _ = finVecSqNorm _
        rw [← sq_finVecNorm, ← sq_finVecNorm, finVecNorm_mulVec_of_transpose_mul_self hStS]
      exact hdot.trans (sum_sq_evalMuxSymOps R ops₀ v)

theorem sum_symHitProb_evalRampMuxSegs {N m : ℕ} (R : Finset (Fin N))
    {L₀ : ℕ} (ops₀ : List (MuxSymOp N (L₀ * m))) (segs : List (RampMuxSeg N m))
    (hmono : rmsSegsMono L₀ segs) (h2Le : 2 * (rmsEndL L₀ segs * m) ≤ N) :
    (∑ w ∈ Finset.range (min (rmsEndL L₀ segs * m) R.card + 1),
      symHitProb R (evalRampMuxSegs R L₀ ops₀ segs (u0Vec N (L₀ * m))) w) = 1 := by
  have hl₀ : L₀ ≤ rmsEndL L₀ segs := rmsEndL_ge hmono
  have hL₀N : L₀ * m ≤ N :=
    (Nat.mul_le_mul_right m hl₀).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans h2Le)
  rw [sum_symHitProb_eq_sum_sq, sum_sq_evalRampMuxSegs R ops₀ segs hmono h2Le, sum_sq_u0Vec hL₀N]

/- ## 1. Zero-Padding State & Orthogonal Step-Up Unitary -/

/-- Vector quadratic form `⟨ψ, A ψ⟩` on `Fin d → ℂ`. -/
noncomputable def rmsVecQuad {d : ℕ} (A : Operator d) (ψ : Fin d → ℂ) : ℂ :=
  star ψ ⬝ᵥ (A *ᵥ ψ)

theorem rmsVecQuad_single {d : ℕ} (A : Operator d) (z : Fin d) :
    A z z = rmsVecQuad A (Pi.single z 1) := by
  simp [rmsVecQuad]

theorem rmsVecQuad_conj {d : ℕ} (U A : Operator d) (ψ : Fin d → ℂ) :
    rmsVecQuad (Uᴴ * A * U) ψ = rmsVecQuad A (U *ᵥ ψ) := by
  unfold rmsVecQuad
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
  generalize A *ᵥ (U *ᵥ ψ) = φ
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem rmsVecQuad_diagonal_sum_single {d : ℕ} {ι : Type*} [Fintype ι]
    (g : Fin d → ℂ) (v : ι → ℝ) (idx : ι → Fin d) (hinj : Function.Injective idx) :
    rmsVecQuad (diagonal g) (∑ i : ι, (v i : ℂ) • Pi.single (idx i) 1) =
      ∑ i : ι, ((v i) ^ 2 : ℂ) * g (idx i) := by
  classical
  let ψ : Fin d → ℂ := ∑ i : ι, (v i : ℂ) • Pi.single (idx i) 1
  have hψ_at (i : ι) : ψ (idx i) = (v i : ℂ) := by
    simp only [ψ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [sum_eq_single i (fun j hj ↦ by simp [hinj.ne hj.symm])]
    simp
  have hψ_out (z : Fin d) (hz : z ∉ Finset.univ.image idx) : ψ z = 0 := by
    simp only [ψ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hne : z ≠ idx i := fun h ↦ hz (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩)
    simp [hne]
  unfold rmsVecQuad
  change ∑ z : Fin d, star (ψ z) * (diagonal g *ᵥ ψ) z = _
  simp only [mulVec_diagonal]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image idx))
    (fun z _ hz ↦ by simp [hψ_out z hz]),
    Finset.sum_image (fun i _ j _ h ↦ hinj h)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hψ_at i, Complex.star_def, Complex.conj_ofReal]
  ring

theorem rmsWorkMemState_sum_left {W M : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (∑ i ∈ s, f i) φ = ∑ i ∈ s, workMemState (f i) φ := by
  funext z
  simp [workMemState, Finset.sum_apply, Finset.sum_mul]

theorem rmsWorkMemState_smul_left {W M : ℕ} (c : ℂ)
    (ψ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (c • ψ) φ = c • workMemState ψ φ := by
  funext z
  dsimp only [workMemState, Pi.smul_apply, smul_eq_mul]
  ring

private lemma rms_extractIndex_zero {q Q : ℕ} (r : QRegister q Q) : r.extractIndex 0 = 0 := by
  apply (basisBits q).injective
  funext i
  rw [r.basisBits_extractIndex, basisBits_zero, basisBits_zero]
  rfl

private lemma rms_replaceIndex_zero_zero {q Q : ℕ} (r : QRegister q Q) :
    r.replaceIndex 0 0 = 0 :=
  r.replaceIndex_eq_of_extractIndex_eq_of_agreeOutside 0 0 0 (rms_extractIndex_zero r)
    (fun _ _ ↦ rfl)

/-- Zero-pads `ψ` on `r: QRegister q Q` with `|0⟩` on complement wires. -/
noncomputable def rmsPadState {q Q : ℕ} (r : QRegister q Q) (ψ : Fin (2 ^ q) → ℂ) :
    Fin (2 ^ Q) → ℂ :=
  r.tensorState ψ (Pi.single (r.basisSplitEquiv 0).2 1)

theorem rms_padState_single_zero {q Q : ℕ} (r : QRegister q Q) :
    rmsPadState r (Pi.single 0 1) = Pi.single 0 1 := by
  unfold rmsPadState
  rw [r.tensorState_single_replaceIndex 0 0, rms_replaceIndex_zero_zero]

theorem rms_padState_self (W : ℕ) (hW : 0 + W ≤ W) (ψ : Fin (2 ^ W) → ℂ) :
    rmsPadState (QRegister.block 0 W hW) ψ = ψ := by
  let r := QRegister.block 0 W hW
  funext z
  have hex : r.extractIndex z = z := by
    apply (basisBits W).injective
    funext i
    have hri : r i = i := Fin.ext (by simp [r])
    rw [r.basisBits_extractIndex, hri]
  have hag : r.AgreeOutside z 0 := fun q hq ↦ (hq ⟨q, Fin.ext (by simp [r])⟩).elim
  dsimp only [rmsPadState, QRegister.tensorState]
  rw [hex, Pi.single_apply, ite_eq_left ((r.basisSplit_environment_eq_iff z 0).mpr hag), mul_one]

theorem rms_embedMatrix_mulVec_padState {q Q : ℕ} (r : QRegister q Q)
    (A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ) (ψ : Fin (2 ^ q) → ℂ) :
    r.embedMatrix A *ᵥ rmsPadState r ψ = rmsPadState r (A *ᵥ ψ) :=
  r.embedMatrix_mulVec_tensorState A ψ _

theorem rms_padState_compose {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k)
    (ψ : Fin (2 ^ m) → ℂ) :
    rmsPadState outer (rmsPadState inner ψ) = rmsPadState (outer.compose inner) ψ := by
  funext z
  dsimp only [rmsPadState, QRegister.tensorState]
  rw [outer.extractIndex_compose]
  simp only [Pi.single_apply]
  have h_env_iff :
      (((outer.compose inner).basisSplitEquiv z).2 = ((outer.compose inner).basisSplitEquiv 0).2) ↔
        ((outer.basisSplitEquiv z).2 = (outer.basisSplitEquiv 0).2) ∧
          ((inner.basisSplitEquiv (outer.extractIndex z)).2 = (inner.basisSplitEquiv 0).2) := by
    rw [QRegister.basisSplit_environment_eq_iff, QRegister.basisSplit_environment_eq_iff,
      QRegister.basisSplit_environment_eq_iff]
    simpa only [rms_extractIndex_zero] using outer.agreeOutside_compose_iff inner z 0
  by_cases hc :
      ((outer.compose inner).basisSplitEquiv z).2 = ((outer.compose inner).basisSplitEquiv 0).2
  · rcases h_env_iff.mp hc with ⟨hout, hin⟩
    rw [ite_eq_left hin, ite_eq_left hout, ite_eq_left hc]
    ring
  · have hnot := mt h_env_iff.mpr hc
    by_cases hin :
        (inner.basisSplitEquiv (outer.extractIndex z)).2 = (inner.basisSplitEquiv 0).2
    · rw [ite_eq_left hin, ite_eq_right (fun ho ↦ hnot ⟨ho, hin⟩), ite_eq_right hc]
      ring
    · rw [ite_eq_right hin, ite_eq_right hc]
      ring

theorem rms_activeWorkReg_compose_relWorkReg {n m L l₁ l₂ : ℕ}
    (hl12 : l₁ ≤ l₂) (hl2 : l₂ ≤ L) :
    (rmsActiveWorkReg n m L l₂ hl2).compose (rmsRelWorkReg n (l₁ * m) (l₂ * m)
      (Nat.mul_le_mul_right m hl12)) =
      rmsActiveWorkReg n m L l₁ (hl12.trans hl2) := by
  ext i
  simp [rmsActiveWorkReg, rmsRelWorkReg]

private lemma rms_subReg_compose_lowBlock (W₁ W₂ M : ℕ) (hW : W₁ ≤ W₂) :
    (rmsSubReg W₁ W₂ M hW).compose (lowBlock W₁ M) =
      (lowBlock W₂ M).compose (QRegister.block 0 W₁ (by omega)) := by
  apply QRegister.ext
  apply Function.Embedding.ext
  intro i
  have hi : lowBlock W₁ M i = Fin.castAdd M i := Fin.ext (by simp [lowBlock])
  change (rmsSubReg W₁ W₂ M hW).compose (lowBlock W₁ M) i =
    (lowBlock W₂ M).compose (QRegister.block 0 W₁ _) i
  rw [QRegister.compose_apply, hi, rmsSubReg, QRegister.concat_apply_left]
  ext
  simp [lowBlock]

private lemma rms_subReg_compose_highBlock (W₁ W₂ M : ℕ) (hW : W₁ ≤ W₂) :
    (rmsSubReg W₁ W₂ M hW).compose (highBlock W₁ M) = highBlock W₂ M := by
  apply QRegister.ext
  apply Function.Embedding.ext
  intro i
  have hi : highBlock W₁ M i = Fin.natAdd W₁ i := Fin.ext (by simp [highBlock])
  change (rmsSubReg W₁ W₂ M hW).compose (highBlock W₁ M) i = highBlock W₂ M i
  rw [QRegister.compose_apply, hi, rmsSubReg, QRegister.concat_apply_right]

private lemma rms_lowHighEquiv_extractIndex_subReg (W₁ W₂ M : ℕ) (hW : W₁ ≤ W₂)
    (z : Fin (2 ^ (W₂ + M))) :
    lowHighEquiv W₁ M ((rmsSubReg W₁ W₂ M hW).extractIndex z) =
      ((QRegister.block 0 W₁ (by omega)).extractIndex (lowHighEquiv W₂ M z).1,
        (lowHighEquiv W₂ M z).2) := by
  apply Prod.ext
  · rw [← extractIndex_lowBlock, ← QRegister.extractIndex_compose, rms_subReg_compose_lowBlock,
      QRegister.extractIndex_compose, extractIndex_lowBlock]
  · rw [← extractIndex_highBlock, ← QRegister.extractIndex_compose, rms_subReg_compose_highBlock,
      extractIndex_highBlock]

theorem rms_workMemState_padState (W₁ W₂ M : ℕ) (hW : W₁ ≤ W₂)
    (ψ : Fin (2 ^ W₁) → ℂ) (μ : Fin (2 ^ M)) :
    workMemState (rmsPadState (QRegister.block 0 W₁ (by omega)) ψ) (Pi.single μ 1) =
      rmsPadState (rmsSubReg W₁ W₂ M hW) (workMemState ψ (Pi.single μ 1)) := by
  let rW : QRegister W₁ W₂ := QRegister.block 0 W₁ (by omega)
  let rS : QRegister (W₁ + M) (W₂ + M) := rmsSubReg W₁ W₂ M hW
  have hmem (q : Fin (W₂ + M)) : q ∈ Set.range rS.wires ↔ q.val < W₁ ∨ W₂ ≤ q.val := by
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
      cases s with
      | inl iL =>
        change (rS (Fin.castAdd M iL)).val < W₁ ∨ _
        dsimp only [rS, rmsSubReg]
        rw [QRegister.concat_apply_left]; exact Or.inl (by simp [iL.isLt])
      | inr iR =>
        change _ ∨ W₂ ≤ (rS (Fin.natAdd W₁ iR)).val
        dsimp only [rS, rmsSubReg]
        rw [QRegister.concat_apply_right]; exact Or.inr (by simp [highBlock])
    · rintro (hlt | hge)
      · refine ⟨Fin.castAdd M ⟨q.val, hlt⟩, ?_⟩
        dsimp only [rS, rmsSubReg]
        rw [QRegister.concat_apply_left]; ext; simp
      · refine ⟨Fin.natAdd W₁ ⟨q.val - W₂, by omega⟩, ?_⟩
        dsimp only [rS, rmsSubReg]
        rw [QRegister.concat_apply_right]; ext; simp [highBlock]; omega
  funext z
  simp only [workMemState, rmsPadState, QRegister.tensorState,
    rms_lowHighEquiv_extractIndex_subReg W₁ W₂ M hW z, Pi.single_apply]
  have hag_iff : rW.AgreeOutside (lowHighEquiv W₂ M z).1 0 ↔ rS.AgreeOutside z 0 := by
    constructor
    · intro hw q hq
      rw [hmem, not_or, not_lt, not_le] at hq
      have hqW_not : (⟨q.val, hq.2⟩ : Fin W₂) ∉ Set.range rW.wires := by
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        simp only [rW, QRegister.block_apply_val, Nat.zero_add] at hv
        exact absurd (hv ▸ i.isLt) (not_lt.mpr hq.1)
      have hb := hw ⟨q.val, hq.2⟩ hqW_not
      rw [← extractIndex_lowBlock W₂ M z, QRegister.basisBits_extractIndex,
        basisBits_zero, Pi.zero_apply] at hb
      have hlow : lowBlock W₂ M ⟨q.val, hq.2⟩ = q := Fin.ext (by simp [lowBlock])
      rw [← hlow, hb, basisBits_zero, Pi.zero_apply]
    · intro hs qW hqW
      have hqW_ge : W₁ ≤ qW.val := by
        by_contra hlt
        exact hqW ⟨⟨qW.val, by omega⟩, Fin.ext (by simp [rW])⟩
      have hq_not : lowBlock W₂ M qW ∉ Set.range rS.wires := by
        rw [hmem]; simp [lowBlock]; omega
      rw [← extractIndex_lowBlock W₂ M z, QRegister.basisBits_extractIndex, hs _ hq_not,
        basisBits_zero, basisBits_zero, Pi.zero_apply, Pi.zero_apply]
  have h_env_iff :
      ((rW.basisSplitEquiv (lowHighEquiv W₂ M z).1).2 = (rW.basisSplitEquiv 0).2) ↔
        ((rS.basisSplitEquiv z).2 = (rS.basisSplitEquiv 0).2) := by
    rw [QRegister.basisSplit_environment_eq_iff, QRegister.basisSplit_environment_eq_iff]
    exact hag_iff
  by_cases hs : (rS.basisSplitEquiv z).2 = (rS.basisSplitEquiv 0).2
  · rw [ite_eq_left (h_env_iff.mpr hs), ite_eq_left hs]
    ring
  · rw [ite_eq_right (mt h_env_iff.mp hs), ite_eq_right hs]
    ring

/- ## 2. Zero-Qubit Real Orthogonal `rmsOrthSwapUnitary` Lifting `stepUpFrom` -/

private noncomputable def rms_flipWirePerm (W : ℕ) (w : Fin W) : Equiv.Perm (Fin (2 ^ W)) :=
  (basisBits W).trans
    ((Equiv.addRight (fun q : Fin W ↦ if q = w then (1 : ZMod 2) else 0)).trans
      (basisBits W).symm)

private lemma rms_basisBits_flipWirePerm (W : ℕ) (w : Fin W) (z : Fin (2 ^ W)) (q : Fin W) :
    basisBits W (rms_flipWirePerm W w z) q =
      basisBits W z q + if q = w then (1 : ZMod 2) else 0 := by
  simp [rms_flipWirePerm]

private noncomputable def rms_padSubsetIdx (n M₁ M₂ : ℕ) (hM : M₁ ≤ M₂)
    (E₁ : SymSubset (2 ^ n) M₁) : Fin (2 ^ (M₂ * (n + 1))) :=
  (rmsRelWorkReg n M₁ M₂ hM).replaceIndex 0 (subsetWorkIdx n M₁ E₁)

private lemma rms_padSubsetIdx_injective (n M₁ M₂ : ℕ) (hM : M₁ ≤ M₂) :
    Function.Injective (rms_padSubsetIdx n M₁ M₂ hM) := fun _ _ h ↦
  subsetWorkIdx_injective n M₁ (by
    simpa [rms_padSubsetIdx] using congrArg (rmsRelWorkReg n M₁ M₂ hM).extractIndex h)

private lemma rms_padState_liftSymVec (n M₁ M₂ : ℕ) (hM : M₁ ≤ M₂)
    (v : SymSubset (2 ^ n) M₁ → ℝ) :
    rmsPadState (rmsRelWorkReg n M₁ M₂ hM) (liftSymVec n M₁ v) =
      ∑ E₁ : SymSubset (2 ^ n) M₁,
        (v E₁ : ℂ) • Pi.single (rms_padSubsetIdx n M₁ M₂ hM E₁) 1 := by
  unfold rmsPadState
  rw [liftSymVec_eq_sum_single, (rmsRelWorkReg n M₁ M₂ hM).tensorState_sum_left]
  refine Finset.sum_congr rfl fun E₁ _ ↦ ?_
  rw [(rmsRelWorkReg n M₁ M₂ hM).tensorState_smul_left,
    (rmsRelWorkReg n M₁ M₂ hM).tensorState_single_replaceIndex 0]
  rfl

private noncomputable def rms_flippedPadIdx (n M₁ M₂ : ℕ) (hM12 : M₁ < M₂)
    (E₁ : SymSubset (2 ^ n) M₁) : Fin (2 ^ (M₂ * (n + 1))) :=
  rms_flipWirePerm (M₂ * (n + 1)) (slotReg n M₂ ⟨M₁, hM12⟩ 0)
    (rms_padSubsetIdx n M₁ M₂ hM12.le E₁)

private lemma rms_flippedPadIdx_injective (n M₁ M₂ : ℕ) (hM12 : M₁ < M₂) :
    Function.Injective (rms_flippedPadIdx n M₁ M₂ hM12) :=
  (rms_flipWirePerm _ _).injective.comp (rms_padSubsetIdx_injective n M₁ M₂ hM12.le)

private lemma rms_flippedPadIdx_ne_subsetWorkIdx (n M₁ M₂ : ℕ) (hM12 : M₁ < M₂)
    (E₁ : SymSubset (2 ^ n) M₁) (E₂ : SymSubset (2 ^ n) M₂) :
    rms_flippedPadIdx n M₁ M₂ hM12 E₁ ≠ subsetWorkIdx n M₂ E₂ := by
  let w₀ : Fin (M₂ * (n + 1)) := slotReg n M₂ ⟨M₁, hM12⟩ 0
  have hw₀_val : w₀.val = M₁ * (n + 1) := by simp [w₀, slotReg]
  have hw₀_not_rel : w₀ ∉ Set.range (rmsRelWorkReg n M₁ M₂ hM12.le).wires := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    simp only [rmsRelWorkReg, QRegister.block_apply_val, Nat.zero_add, hw₀_val] at hv
    exact (lt_irrefl _ (hv ▸ i.isLt)).elim
  have hw₀_not_addr : w₀ ∉ Set.range (addrReg n M₂).wires := by
    rintro ⟨u, hu⟩
    obtain ⟨⟨j', r⟩, rfl⟩ := finProdFinEquiv.surjective u
    have hu' : addrReg n M₂ (finProdFinEquiv (j', r)) = slotReg n M₂ ⟨M₁, hM12⟩ 0 := hu
    rw [addrReg_apply, slotReg_apply, slotReg_apply] at hu'
    exact Fin.succ_ne_zero r (congrArg Prod.snd (finProdFinEquiv.injective hu'))
  intro heq
  have hb := congrArg (fun z ↦ basisBits (M₂ * (n + 1)) z w₀) heq
  have hpad0 : basisBits (M₂ * (n + 1)) (rms_padSubsetIdx n M₁ M₂ hM12.le E₁) w₀ = 0 := by
    rw [rms_padSubsetIdx,
      (rmsRelWorkReg n M₁ M₂ hM12.le).basisBits_replaceIndex_of_not_mem 0 _ w₀ hw₀_not_rel,
      basisBits_zero, Pi.zero_apply]
  have hflip1 : basisBits (M₂ * (n + 1)) (rms_flippedPadIdx n M₁ M₂ hM12 E₁) w₀ = 1 := by
    dsimp only [rms_flippedPadIdx]
    rw [rms_basisBits_flipWirePerm, hpad0, ite_eq_left rfl, zero_add]
  have hsub0 : basisBits (M₂ * (n + 1)) (subsetWorkIdx n M₂ E₂) w₀ = 0 := by
    simpa only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply] using
      congrFun (env_subsetWorkIdx n M₂ E₂) ⟨w₀, hw₀_not_addr⟩
  rw [hflip1, hsub0] at hb
  exact one_ne_zero hb

private noncomputable def rms_flippedInjMat (n M₁ M₂ : ℕ) (hM12 : M₁ < M₂) :
    Matrix (Fin (2 ^ (M₂ * (n + 1)))) (SymSubset (2 ^ n) M₁) ℝ :=
  fun z E₁ ↦ if z = rms_flippedPadIdx n M₁ M₂ hM12 E₁ then 1 else 0

private noncomputable def rms_orthReflRealMat (n M₁ M₂ : ℕ) (hM12 : M₁ < M₂) :
    Matrix (Fin (2 ^ (M₂ * (n + 1)))) (Fin (2 ^ (M₂ * (n + 1)))) ℝ :=
  let W := rms_flippedInjMat n M₁ M₂ hM12 - symInjMat n M₂ * stepUpFrom (2 ^ n) M₁ M₂
  1 - W * Wᵀ

private lemma rms_orthRefl_props {n M₁ M₂ : ℕ} (hM12 : M₁ < M₂) (h2M : 2 * M₂ ≤ 2 ^ n) :
    let R := rms_orthReflRealMat n M₁ M₂ hM12
    R * Rᵀ = 1 ∧
      R * rms_flippedInjMat n M₁ M₂ hM12 = symInjMat n M₂ * stepUpFrom (2 ^ n) M₁ M₂ := by
  let S := stepUpFrom (2 ^ n) M₁ M₂
  let J₂ := symInjMat n M₂ * S
  let W := rms_flippedInjMat n M₁ M₂ hM12 - J₂
  have hJ1tJ1 : (rms_flippedInjMat n M₁ M₂ hM12)ᵀ * rms_flippedInjMat n M₁ M₂ hM12 = 1 := by
    ext E₁ E₁'
    rw [Matrix.mul_apply, Matrix.one_apply]
    by_cases h : E₁ = E₁'
    · subst h
      rw [ite_eq_left rfl, sum_eq_single (rms_flippedPadIdx n M₁ M₂ hM12 E₁)
        (fun z hz ↦ by simp [rms_flippedInjMat, hz])]
      simp [rms_flippedInjMat]
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero fun z _ ↦ ?_
      simp only [Matrix.transpose_apply, rms_flippedInjMat]
      by_cases hz : z = rms_flippedPadIdx n M₁ M₂ hM12 E₁
      · subst hz
        have hne : rms_flippedPadIdx n M₁ M₂ hM12 E₁ ≠ rms_flippedPadIdx n M₁ M₂ hM12 E₁' :=
          fun h2 ↦ h (rms_flippedPadIdx_injective n M₁ M₂ hM12 h2)
        simp [hne]
      · simp [hz]
  have hJ2tJ2 : J₂ᵀ * J₂ = 1 := by
    dsimp only [J₂]
    rw [Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (symInjMat n M₂)ᵀ (symInjMat n M₂) S,
      symInjMat_transpose_mul_self, Matrix.one_mul,
      stepUpFrom_transpose_mul_self hM12.le h2M]
  have hJ1tSym : (rms_flippedInjMat n M₁ M₂ hM12)ᵀ * symInjMat n M₂ = 0 := by
    ext E₁ E₂
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    simp only [Matrix.transpose_apply, rms_flippedInjMat, symInjMat]
    by_cases hz : z = rms_flippedPadIdx n M₁ M₂ hM12 E₁
    · subst hz
      simp [rms_flippedPadIdx_ne_subsetWorkIdx n M₁ M₂ hM12 E₁ E₂]
    · simp [hz]
  have hJ1tJ2 : (rms_flippedInjMat n M₁ M₂ hM12)ᵀ * J₂ = 0 := by
    dsimp only [J₂]; rw [← Matrix.mul_assoc, hJ1tSym, Matrix.zero_mul]
  have hJ2tJ1 : J₂ᵀ * rms_flippedInjMat n M₁ M₂ hM12 = 0 := by
    rw [← Matrix.transpose_transpose (rms_flippedInjMat n M₁ M₂ hM12), ← Matrix.transpose_mul,
      hJ1tJ2, Matrix.transpose_zero]
  have hWtW : Wᵀ * W = (2 : ℝ) • 1 := by
    dsimp only [W]
    rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hJ1tJ1, hJ1tJ2, hJ2tJ1, hJ2tJ2, sub_zero, zero_sub, sub_neg_eq_add, ← two_smul ℝ 1]
  have hSym : (1 - W * Wᵀ)ᵀ = 1 - W * Wᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  refine ⟨?_, ?_⟩
  · change (1 - W * Wᵀ) * (1 - W * Wᵀ)ᵀ = 1
    rw [hSym, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_assoc W Wᵀ (W * Wᵀ), ← Matrix.mul_assoc Wᵀ W Wᵀ, hWtW,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, two_smul]
    abel
  · have hWtJ1 : Wᵀ * rms_flippedInjMat n M₁ M₂ hM12 = 1 := by
      dsimp only [W]
      rw [Matrix.transpose_sub, Matrix.sub_mul, hJ1tJ1, hJ2tJ1, sub_zero]
    change (1 - W * Wᵀ) * rms_flippedInjMat n M₁ M₂ hM12 = J₂
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hWtJ1, Matrix.mul_one]
    dsimp only [W]
    abel

/-- Zero-query, `+0`-qubit unitary on `M₂ * (n + 1)` work wires mapping the zero-padded
  symmetric
  subspace `rmsPadState (rmsRelWorkReg n M₁ M₂ _) (liftSymVec n M₁ v)` (`M₁ < M₂`, `2 * M₂ ≤
  2 ^ n`)
  onto `liftSymVec n M₂ (stepUpFrom (2 ^ n) M₁ M₂ *ᵥ v)`. -/
noncomputable def rmsOrthSwapUnitary (n M₁ M₂ : ℕ) (hM12 : M₁ < M₂) (h2M : 2 * M₂ ≤ 2 ^ n) :
    Unitary (2 ^ (M₂ * (n + 1))) :=
  let R₀ := rms_orthReflRealMat n M₁ M₂ hM12
  let U_refl : Unitary (2 ^ (M₂ * (n + 1))) :=
    ⟨R₀.map Complex.ofRealHom, by
      rw [Matrix.mem_unitaryGroup_iff]
      have hstar : star (R₀.map Complex.ofRealHom) = R₀ᵀ.map Complex.ofRealHom := by
        ext i j; simp
      rw [hstar, ← Matrix.map_mul, (rms_orthRefl_props hM12 h2M).1]
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]⟩
  U_refl * permutationUnitary (rms_flipWirePerm (M₂ * (n + 1)) (slotReg n M₂ ⟨M₁, hM12⟩ 0))

theorem rmsOrthSwapUnitary_mulVec_padState {n M₁ M₂ : ℕ} (hM12 : M₁ < M₂)
    (h2M : 2 * M₂ ≤ 2 ^ n) (v : SymSubset (2 ^ n) M₁ → ℝ) :
    (rmsOrthSwapUnitary n M₁ M₂ hM12 h2M).1 *ᵥ
        rmsPadState (rmsRelWorkReg n M₁ M₂ hM12.le) (liftSymVec n M₁ v) =
      liftSymVec n M₂ (stepUpFrom (2 ^ n) M₁ M₂ *ᵥ v) := by
  let perm := rms_flipWirePerm (M₂ * (n + 1)) (slotReg n M₂ ⟨M₁, hM12⟩ 0)
  let R₀ := rms_orthReflRealMat n M₁ M₂ hM12
  have hval : (rmsOrthSwapUnitary n M₁ M₂ hM12 h2M).1 =
      R₀.map Complex.ofRealHom * (permutationUnitary perm).1 := rfl
  rw [hval, rms_padState_liftSymVec, ← mulVec_mulVec]
  have hperm_vec :
      (permutationUnitary perm).1 *ᵥ
          (∑ E₁ : SymSubset (2 ^ n) M₁,
            (v E₁ : ℂ) • Pi.single (rms_padSubsetIdx n M₁ M₂ hM12.le E₁) 1) =
        fun y ↦ Complex.ofRealHom ((rms_flippedInjMat n M₁ M₂ hM12 *ᵥ v) y) := by
    rw [Matrix.mulVec_sum]
    funext z
    simp only [Finset.sum_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      permutationUnitary_mulVec_single, Pi.single_apply, Matrix.mulVec, dotProduct,
      rms_flippedInjMat, Complex.ofRealHom_eq_coe, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun E₁ _ ↦ ?_
    dsimp only [perm, rms_flippedPadIdx]
    by_cases hz :
        z = rms_flipWirePerm (M₂ * (n + 1)) (slotReg n M₂ ⟨M₁, hM12⟩ 0)
          (rms_padSubsetIdx n M₁ M₂ hM12.le E₁) <;>
      simp [hz]
  have hreal :
      R₀ *ᵥ (rms_flippedInjMat n M₁ M₂ hM12 *ᵥ v) =
        symInjMat n M₂ *ᵥ (stepUpFrom (2 ^ n) M₁ M₂ *ᵥ v) := by
    rw [mulVec_mulVec, (rms_orthRefl_props hM12 h2M).2, ← mulVec_mulVec]
  rw [hperm_vec]
  funext z
  exact
    ((RingHom.map_mulVec Complex.ofRealHom R₀
      (rms_flippedInjMat n M₁ M₂ hM12 *ᵥ v) z).symm).trans
      (congrArg Complex.ofRealHom (congrFun hreal z))

end
end QuantumComputation.Specs.DickeSol

@[expose] public section

namespace QuantumComputation.Specs.GroverFindAll.MuxColdTail

open Operator Matrix Real QProg QProg.Notation ResourceCounting
open QuantumComputation.Specs
open QuantumComputation.Specs.GroverFindAll
open QuantumComputation.Specs.GroverFindAll.MultiTapStage2
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation

/- ## 1. General Diagonal Observable & `qSet` Subregister Lifting -/

/-- Lifting `DickeSol.realDiagObs` along `r: QRegister q Q` pulls the diagonal indicator
  back along
  `r.extractIndex`. -/
theorem liftObservable_realDiagObs {q Q : ℕ} (r : QRegister q Q)
    (f : Fin (2 ^ q) → ℝ) (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) :
    liftObservable r (DickeSol.realDiagObs f h0 h1) =
      DickeSol.realDiagObs (fun z ↦ f (r.extractIndex z))
        (fun z ↦ h0 (r.extractIndex z))
        (fun z ↦ h1 (r.extractIndex z)) := by
  apply Subtype.ext
  apply HermitianMat.ext
  simp only [← HermitianMat.val_eq_coe]
  rw [liftObservable_mat, DickeSol.realDiagObs_mat, QRegister.embedMatrix_diagonal,
    DickeSol.realDiagObs_mat]

/-- Global `qSet` commutes with `liftAssertion r` because `r.extractIndex 0 = 0`. -/
theorem wp_qSet_liftAssertion {Var : Type} [DecidableEq Var] {q Q : ℕ}
    (r : QRegister q Q) (Θ : CQAssertion (Store Var) (2 ^ q)) :
    wp (.qSet : QProg Var (2 ^ Q)) (liftAssertion r Θ) =
      liftAssertion r (wp (.qSet : QProg Var (2 ^ q)) Θ) := by
  funext σ
  apply Subtype.ext
  apply HermitianMat.ext
  change ((wp (.qSet : QProg Var (2 ^ Q)) (liftAssertion r Θ)) σ).1.1 =
    (liftAssertion r (wp (.qSet : QProg Var (2 ^ q)) Θ) σ).1.1
  rw [wp_qSet, qhlQSet_val, liftAssertion_apply, liftObservable_mat,
    liftAssertion_apply, liftObservable_mat, wp_qSet, qhlQSet_val,
    QRegister.embedMatrix_smul, QRegister.embedMatrix_one, QRegister.embedMatrix_apply,
    extractIndex_zero_reg, ite_eq_left rfl, mul_one]

/-- Partial trace `marginalState r` commutes with full-system `qSet`. -/
theorem marginalState_interp_qSet {Var : Type} [DecidableEq Var] {q Q : ℕ}
    (r : QRegister q Q) (Δ : CQState (Store Var) (2 ^ Q)) :
    marginalState r ((interp (.qSet : QProg Var (2 ^ Q))).toStateFun Δ) =
      (interp (.qSet : QProg Var (2 ^ q))).toStateFun (marginalState r Δ) := by
  refine cqState_eq_of_forall_expect_eq fun Θ ↦ ?_
  rw [← expect_liftAssertion_eq_marginalState, ← wp_expectation_eq,
    wp_qSet_liftAssertion, expect_liftAssertion_eq_marginalState, wp_expectation_eq]

/-- Any valid QHL triple `⦃ ⊤ ⦄ c ⦃ Ψ ⦄` implies the pointwise assertion inequality `⊤ ≤ wp
  c Ψ`. -/
theorem top_le_wp_of_triple_top {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {c : QProg Var d} {Ψ : CQAssertion (Store Var) d}
    (h : ⦃ (⊤ : CQAssertion (Store Var) d) ⦄ c ⦃ Ψ ⦄) :
    (⊤ : CQAssertion (Store Var) d) ≤ wp c Ψ := by
  open Classical in
  intro σ₀
  set O := wp c Ψ σ₀
  set D : HermitianMat (Fin d) ℂ := 1 - O.1
  have hD_nn : 0 ≤ D := sub_nonneg.mpr O.2.2
  set M : ℝ := max 1 D.trace
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left 1 D.trace)
  let ρ : 𝒟 (Fin d) := ⟨M⁻¹ • D, smul_nonneg (inv_nonneg.mpr hM_pos.le) hD_nn, by
    rw [← HermitianMat.one_inner, inner_smul_right, HermitianMat.one_inner]
    exact (mul_le_mul_of_nonneg_left (le_max_right 1 D.trace)
      (inv_nonneg.mpr hM_pos.le)).trans_eq (inv_mul_cancel₀ hM_pos.ne')⟩
  let Γ : CQState (Store Var) d := ⟨fun σ ↦ if σ = σ₀ then ρ else 0,
    ρ.trace, by
      have hf : (fun σ : Store Var ↦ ((if σ = σ₀ then ρ else 0 : 𝒟 (Fin d))).trace) =
          fun σ ↦ if σ = σ₀ then ρ.trace else 0 := by
        funext σ
        by_cases hσ : σ = σ₀ <;> simp [hσ]
      rw [hf]
      exact ⟨hasSum_ite_eq σ₀ ρ.trace, ρ.trace_le_one⟩⟩
  have hΓ := h Γ
  rw [← wp_expectation_eq] at hΓ
  have hexp_top : 𝔼[Γ, ⊤] = ⟪(1 : HermitianMat (Fin d) ℂ), ρ.1⟫_ℝ := by
    rw [expect_eq_tsum, tsum_eq_single σ₀]
    · simp [Γ]
    · intro σ hσ
      simp [Γ, hσ]
  have hexp_O : 𝔼[Γ, wp c Ψ] = ⟪O.1, ρ.1⟫_ℝ := by
    rw [expect_eq_tsum, tsum_eq_single σ₀]
    · simp [Γ, O]
    · intro σ hσ
      simp [Γ, hσ]
  rw [hexp_top, hexp_O] at hΓ
  have hsub : ⟪(1 : HermitianMat (Fin d) ℂ), ρ.1⟫_ℝ - ⟪O.1, ρ.1⟫_ℝ ≤ 0 := sub_nonpos.mpr hΓ
  rw [← inner_sub_left, show (1 : HermitianMat (Fin d) ℂ) - O.1 = D from rfl,
    show ρ.1 = M⁻¹ • D from rfl, inner_smul_right] at hsub
  change M⁻¹ * ⟪D, D⟫_ℝ ≤ 0 at hsub
  have hDD_le : ⟪D, D⟫_ℝ ≤ 0 := by
    calc ⟪D, D⟫_ℝ
        = M * (M⁻¹ * ⟪D, D⟫_ℝ) := by rw [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul]
      _ ≤ M * 0 := mul_le_mul_of_nonneg_left hsub hM_pos.le
      _ = 0 := mul_zero M
  have hDD0 : ⟪D, D⟫_ℝ = 0 := le_antisymm hDD_le (HermitianMat.inner_ge_zero hD_nn hD_nn)
  change (1 : HermitianMat (Fin d) ℂ) ≤ O.1
  exact le_of_eq (sub_eq_zero.mp (inner_self_eq_zero.mp hDD0))

/-- Lifting `qSet;; c` via `embedOracleCirc r` preserves `⊤ ≤ wp... (liftPureProp P)`. -/
theorem wp_qSet_embedOracleCirc_liftPureProp {Var : Type} [DecidableEq Var] {q Q w : ℕ}
    (r : QRegister q Q) (c : OracleDynamicCircuit (Unitary (2 ^ q)) Var q w)
    (O : Unitary (2 ^ w)) {P : Store Var → Prop}
    (hcorr : (⊤ : CQAssertion (Store Var) (2 ^ q)) ≤
      wp (QProg.qSet ;; c.compile QProg.qAssign O) (liftPureProp P)) :
    (⊤ : CQAssertion (Store Var) (2 ^ Q)) ≤
      wp (QProg.qSet ;; (embedOracleCirc r c).compile QProg.qAssign O) (liftPureProp P) := by
  rw [wp_qSeq, ← liftAssertion_liftPureProp r P, wp_embedOracleCirc_liftAssertion,
    wp_qSet_liftAssertion, ← wp_qSeq]
  have htop : liftAssertion r (⊤ : CQAssertion (Store Var) (2 ^ q)) = ⊤ := by
    funext σ
    apply Subtype.ext
    apply HermitianMat.ext
    change (liftAssertion r ⊤ σ).1.1 = 1
    rw [liftAssertion_apply, liftObservable_mat]
    exact r.embedMatrix_one
  rw [← htop]
  exact fun σ ↦ liftObservable_mono r (hcorr σ)

/-- Lifting `qSet;; c` via `embedOracleCirc r` preserves `CostBound` for any real oracle
  `O`. -/
theorem costBound_qSet_embedOracleCirc {Var : Type} [DecidableEq Var] {q Q w : ℕ}
    (r : QRegister q Q) (c : OracleDynamicCircuit (Unitary (2 ^ q)) Var q w)
    {O : Unitary (2 ^ w)} (hO : GroverSol.IsRealMatrix O.1) {b : ℝ≥0}
    (hcb : CostBound (Var := Var) (CostModel.ofEmbeddedOracle O)
      (QProg.qSet ;; c.compile QProg.qAssign O) b) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle O)
      (QProg.qSet ;; (embedOracleCirc r c).compile QProg.qAssign O) b := by
  intro Δ
  set modelQ : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle O
  set modelq : CostModel (2 ^ q) := CostModel.ofEmbeddedOracle O
  have hresQ : modelQ.resetCost = 0 := rfl
  have hresq : modelq.resetCost = 0 := rfl
  rw [expectedCost_qSeq, expectedCost_qSet, hresQ, Nat.cast_zero, mul_zero, zero_add]
  calc expectedCost modelQ ((embedOracleCirc r c).compile QProg.qAssign O)
        ((interp (.qSet : QProg Var (2 ^ Q))).toStateFun Δ)
      ≤ expectedCost modelq (c.compile QProg.qAssign O)
          (marginalState r ((interp (.qSet : QProg Var (2 ^ Q))).toStateFun Δ)) :=
        expectedCost_embedOracleCirc_le r c hO _
    _ = expectedCost modelq (c.compile QProg.qAssign O)
          ((interp (.qSet : QProg Var (2 ^ q))).toStateFun (marginalState r Δ)) := by
        rw [marginalState_interp_qSet]
    _ = expectedCost modelq (QProg.qSet ;; c.compile QProg.qAssign O)
          (marginalState r Δ) := by
        rw [expectedCost_qSeq, expectedCost_qSet, hresq, Nat.cast_zero, mul_zero, zero_add]
    _ ≤ stateMass (marginalState r Δ) * (b : ℝ≥0∞) := hcb (marginalState r Δ)
    _ = stateMass Δ * (b : ℝ≥0∞) := by rw [stateMass_marginalState]

/- ## 2. Split-Register `muxColdReg` & `+0`-Oracle `validObs` QHL Transport -/

/-- Split subregister selecting the first `m * (n + 1)` work wires `[0.. m * (n + 1) - 1]`
  and
  the shared `k * n` archive wires `[(L_max * m) * (n + 1).. (L_max * m) * (n + 1) + k * n -
  1]`
  inside `((L_max * m) * (n + 1) + k * n)` qubits (`Stage1.qubits n (L_max * m) k`),
  skipping the
  `(L_max - 1) * m * (n + 1)` middle mux wires with zero SWAPs and zero extra qubits. -/
def muxColdReg (n m L_max k : ℕ) (hL : 1 ≤ L_max) :
    QRegister (m * (n + 1) + k * n) ((L_max * m) * (n + 1) + k * n) :=
  (QRegister.block 0 (m * (n + 1))
    (by
      have hmL := Nat.mul_le_mul_right (n + 1) (Nat.le_mul_of_pos_left m hL)
      omega)).concat
    (DickeSol.highBlock ((L_max * m) * (n + 1)) (k * n))
    (QRegister.block_disjoint_of_le 0 (m * (n + 1)) ((L_max * m) * (n + 1)) (k * n) _ _
      (by
        have hmL := Nat.mul_le_mul_right (n + 1) (Nat.le_mul_of_pos_left m hL)
        omega))

/-- `muxColdReg` maps `lowBlock (m * (n + 1)) (k * n)` to the contiguous low `m * (n + 1)`
  block. -/
theorem muxColdReg_compose_lowBlock (n m L_max k : ℕ) (hL : 1 ≤ L_max) :
    (muxColdReg n m L_max k hL).compose (DickeSol.lowBlock (m * (n + 1)) (k * n)) =
      QRegister.block 0 (m * (n + 1))
        (by
          have hmL := Nat.mul_le_mul_right (n + 1) (Nat.le_mul_of_pos_left m hL)
          omega) := by
  apply QRegister.ext
  apply Function.Embedding.ext
  intro i
  have hi : DickeSol.lowBlock (m * (n + 1)) (k * n) i = Fin.castAdd (k * n) i :=
    Fin.ext (by simp [DickeSol.lowBlock])
  change (muxColdReg n m L_max k hL).compose (DickeSol.lowBlock (m * (n + 1)) (k * n)) i =
    QRegister.block 0 (m * (n + 1)) _ i
  rw [QRegister.compose_apply, hi, muxColdReg, QRegister.concat_apply_left]

/-- `muxColdReg` maps `highBlock (m * (n + 1)) (k * n)` directly to
  `highBlock ((L_max * m) * (n + 1)) (k * n)`. -/
theorem muxColdReg_compose_highBlock (n m L_max k : ℕ) (hL : 1 ≤ L_max) :
    (muxColdReg n m L_max k hL).compose (DickeSol.highBlock (m * (n + 1)) (k * n)) =
      DickeSol.highBlock ((L_max * m) * (n + 1)) (k * n) := by
  apply QRegister.ext
  apply Function.Embedding.ext
  intro i
  have hi : DickeSol.highBlock (m * (n + 1)) (k * n) i = Fin.natAdd (m * (n + 1)) i :=
    Fin.ext (by simp [DickeSol.highBlock])
  change (muxColdReg n m L_max k hL).compose (DickeSol.highBlock (m * (n + 1)) (k * n)) i =
    DickeSol.highBlock ((L_max * m) * (n + 1)) (k * n) i
  rw [QRegister.compose_apply, hi, muxColdReg, QRegister.concat_apply_right]

/-- Extracting `muxColdReg` preserves the `k * n`-bit archive component identically. -/
theorem lowHighEquiv_snd_extractIndex_muxColdReg (n m L_max k : ℕ) (hL : 1 ≤ L_max)
    (z : Fin (2 ^ ((L_max * m) * (n + 1) + k * n))) :
    (DickeSol.lowHighEquiv (m * (n + 1)) (k * n)
        ((muxColdReg n m L_max k hL).extractIndex z)).2 =
      (DickeSol.lowHighEquiv ((L_max * m) * (n + 1)) (k * n) z).2 := by
  rw [← DickeSol.extractIndex_highBlock, ← QRegister.extractIndex_compose,
    muxColdReg_compose_highBlock, DickeSol.extractIndex_highBlock]

/-- Exact assertion identity: lifting `validObs n m k S j` along `muxColdReg` equals
  `validObs n (L_max * m) k S j` on the full multiplexed space with no side condition on the
  `(L_max - 1) * m * (n + 1)` idle mux wires. -/
theorem liftAssertion_muxColdReg_validObs {Var : Type} (n m L_max k : ℕ) (hL : 1 ≤ L_max)
    (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    liftAssertion (muxColdReg n m L_max k hL) (DickeSol.validObs (Var := Var) n m k S j) =
      DickeSol.validObs (Var := Var) n (L_max * m) k S j := by
  funext σ
  dsimp only [liftAssertion, DickeSol.validObs]
  rw [liftObservable_realDiagObs]
  apply Subtype.ext
  apply HermitianMat.ext
  simp only [← HermitianMat.val_eq_coe]
  rw [DickeSol.realDiagObs_mat, DickeSol.realDiagObs_mat]
  refine congrArg Matrix.diagonal (funext fun z ↦ congrArg Complex.ofReal ?_)
  dsimp only [DickeSol.validInd]
  rw [lowHighEquiv_snd_extractIndex_muxColdReg n m L_max k hL z]

/-- Embed any `(m, k)` dynamic circuit on `Stage1.qubits n m k` into `Stage1.qubits n (L_max
  * m) k`
  along `muxColdReg`. -/
noncomputable abbrev embedMuxColdCircuit {Var : Type} {w : ℕ}
    (n m L_max k : ℕ) (hL : 1 ≤ L_max)
    (c : OracleDynamicCircuit (Unitary (2 ^ (m * (n + 1) + k * n))) Var
      (m * (n + 1) + k * n) w) :
    OracleDynamicCircuit (Unitary (2 ^ ((L_max * m) * (n + 1) + k * n))) Var
      ((L_max * m) * (n + 1) + k * n) w :=
  embedOracleCirc (muxColdReg n m L_max k hL) c

/-- Weakest-precondition transport of `validObs n m k S s → validObs n m k S s'` onto
  `validObs n (L_max * m) k S s → validObs n (L_max * m) k S s'`. -/
theorem wp_embedMuxCold_validObs_ge {Var : Type} [DecidableEq Var] {n m L_max k w : ℕ}
    (hL : 1 ≤ L_max) {S : Finset (Fin (2 ^ n))} {s s' : ℕ}
    (c : OracleDynamicCircuit (Unitary (2 ^ (m * (n + 1) + k * n))) Var
      (m * (n + 1) + k * n) w)
    (O : Unitary (2 ^ w))
    (hwp : DickeSol.validObs (Var := Var) n m k S s ≤
      wp (c.compile QProg.qAssign O) (DickeSol.validObs n m k S s')) :
    DickeSol.validObs (Var := Var) n (L_max * m) k S s ≤
      wp ((embedMuxColdCircuit n m L_max k hL c).compile QProg.qAssign O)
        (DickeSol.validObs n (L_max * m) k S s') := by
  rw [← liftAssertion_muxColdReg_validObs n m L_max k hL S s,
    ← liftAssertion_muxColdReg_validObs n m L_max k hL S s',
    wp_embedOracleCirc_liftAssertion]
  exact fun σ ↦ liftObservable_mono (muxColdReg n m L_max k hL) (hwp σ)

/-- Weakest-precondition transport of `validObs n m k S s → liftPureProp P` onto
  `validObs n (L_max * m) k S s → liftPureProp P`. -/
theorem wp_embedMuxCold_liftPureProp_ge {Var : Type} [DecidableEq Var] {n m L_max k w : ℕ}
    (hL : 1 ≤ L_max) {S : Finset (Fin (2 ^ n))} {s : ℕ}
    (c : OracleDynamicCircuit (Unitary (2 ^ (m * (n + 1) + k * n))) Var
      (m * (n + 1) + k * n) w)
    (O : Unitary (2 ^ w)) {P : Store Var → Prop}
    (hwp : DickeSol.validObs (Var := Var) n m k S s ≤
      wp (c.compile QProg.qAssign O) (liftPureProp P)) :
    DickeSol.validObs (Var := Var) n (L_max * m) k S s ≤
      wp ((embedMuxColdCircuit n m L_max k hL c).compile QProg.qAssign O) (liftPureProp P) := by
  rw [← liftAssertion_muxColdReg_validObs n m L_max k hL S s,
    ← liftAssertion_liftPureProp (muxColdReg n m L_max k hL) P,
    wp_embedOracleCirc_liftAssertion]
  exact fun σ ↦ liftObservable_mono (muxColdReg n m L_max k hL) (hwp σ)

/-- `+0`-oracle expected-cost transport: any `(m, k)` cold-tail circuit `c` certified under
  `validObs n m k S s` runs via `embedMuxColdCircuit` on any multiplexed state `Δ`
  satisfying
  `𝔼[Δ, validObs n (L_max * m) k S s] = Δ.trace` with the exact same `stateMass Δ * B` cost
  bound. -/
theorem expectedCost_embedMuxCold_of_validObs_le {Var : Type} [DecidableEq Var]
    {n m L_max k w : ℕ} (hL : 1 ≤ L_max) {S : Finset (Fin (2 ^ n))} {s : ℕ}
    (c : OracleDynamicCircuit (Unitary (2 ^ (m * (n + 1) + k * n))) Var
      (m * (n + 1) + k * n) w)
    {O : Unitary (2 ^ w)} (hO : GroverSol.IsRealMatrix O.1) {B : ℝ≥0∞}
    (hcost : ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
      𝔼[Γ, DickeSol.validObs n m k S s] = Γ.trace →
      expectedCost (CostModel.ofEmbeddedOracle O) (c.compile QProg.qAssign O) Γ ≤
        stateMass Γ * B)
    {Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n))}
    (hV : 𝔼[Δ, DickeSol.validObs n (L_max * m) k S s] = Δ.trace) :
    expectedCost (CostModel.ofEmbeddedOracle O)
      ((embedMuxColdCircuit n m L_max k hL c).compile QProg.qAssign O) Δ ≤
      stateMass Δ * B := by
  let r := muxColdReg n m L_max k hL
  have hmarg_V : 𝔼[marginalState r Δ, DickeSol.validObs n m k S s] =
      (marginalState r Δ).trace := by
    rw [← expect_liftAssertion_eq_marginalState, liftAssertion_muxColdReg_validObs, hV,
      trace_marginalState]
  calc expectedCost (CostModel.ofEmbeddedOracle O)
        ((embedMuxColdCircuit n m L_max k hL c).compile QProg.qAssign O) Δ
      ≤ expectedCost (CostModel.ofEmbeddedOracle O) (c.compile QProg.qAssign O)
          (marginalState r Δ) := expectedCost_embedOracleCirc_le r c hO Δ
    _ ≤ stateMass (marginalState r Δ) * B := hcost (marginalState r Δ) hmarg_V
    _ = stateMass Δ * B := by rw [stateMass_marginalState]

/- ## 3. Hereditary Downward Closure of `GoodSuffix` -/

/-- Any subset of a finite set on which `f` is injective (`(S₂.image f).card = S₂.card`)
  also has
  `(S₁.image f).card = S₁.card`. -/
theorem card_image_eq_of_subset {α β : Type*} [DecidableEq β]
    {S₁ S₂ : Finset α} (f : α → β) (hsub : S₁ ⊆ S₂)
    (hcard : (S₂.image f).card = S₂.card) :
    (S₁.image f).card = S₁.card := by
  classical
  have hpart : (S₂ \ S₁).card + S₁.card = S₂.card := Finset.card_sdiff_add_card_eq_card hsub
  have hunion : S₂.image f = S₁.image f ∪ (S₂ \ S₁).image f := by
    rw [← Finset.image_union, Finset.union_sdiff_of_subset hsub]
  have hle1 : (S₁.image f).card ≤ S₁.card := Finset.card_image_le
  have hle2 : ((S₂ \ S₁).image f).card ≤ (S₂ \ S₁).card := Finset.card_image_le
  have hle_u : (S₂.image f).card ≤ (S₁.image f).card + ((S₂ \ S₁).image f).card := by
    rw [hunion]
    exact Finset.card_union_le _ _
  omega

/-- `DickeSol.GoodSuffix` is downward-closed under arbitrary subset inclusion `S₁ ⊆ S₂`. -/
theorem GoodSuffix.subset {n s W m : ℕ}
    {e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)}
    {S₁ S₂ : Finset (Fin (2 ^ n))} (hsub : S₁ ⊆ S₂) (hgood : DickeSol.GoodSuffix e S₂) :
    DickeSol.GoodSuffix e S₁ :=
  card_image_eq_of_subset (DickeSol.suffixOf e) hsub hgood

/-- Deflating any discovered subset `T` from a `GoodSuffix` target set `S` preserves
  `GoodSuffix`
  deterministically on `S \ T` for every possible trajectory. -/
theorem GoodSuffix.sdiff {n s W m : ℕ}
    {e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)}
    {S : Finset (Fin (2 ^ n))} (T : Finset (Fin (2 ^ n))) (hgood : DickeSol.GoodSuffix e S) :
    DickeSol.GoodSuffix e (S \ T) :=
  GoodSuffix.subset Finset.sdiff_subset hgood

/-- For any valid archive prefix `MemPrefixValid S s₀ μ` and `GoodSuffix e S`, the deflated
  target
  residual `S \ memSeen n k (memPrefix k s₀) μ` has cardinality `S.card - s₀` and satisfies
  `GoodSuffix e` deterministically. -/
theorem GoodSuffix.memSeen_sdiff {n s W m k s₀ : ℕ}
    {e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)}
    {S : Finset (Fin (2 ^ n))} {μ : Fin (2 ^ (k * n))}
    (hval : DickeSol.MemPrefixValid S s₀ μ) (hgood : DickeSol.GoodSuffix e S) :
    DickeSol.GoodSuffix e (S \ DickeSol.memSeen n k (DickeSol.memPrefix k s₀) μ) ∧
      (S \ DickeSol.memSeen n k (DickeSol.memPrefix k s₀) μ).card = S.card - s₀ := by
  obtain ⟨hcard_T, hsub_T⟩ := DickeSol.card_memSeen_of_memPrefixValid hval
  have hadd := Finset.card_sdiff_add_card_eq_card hsub_T
  exact ⟨GoodSuffix.sdiff _ hgood, by omega⟩

/-- Best certified `(m, 2)` relative cost across `m ∈ groverGrid` (`2 ≤ m`):
  `FindAllJohnsonP01` on
  `m ∈ {2, 4, 8}` and `GaussianHammingZoomK2Base` on `m ∈ {16.. 1024}`. -/
def muxColdAvg2RelCost (m : ℕ) : ℚ≥0 :=
  if FindAllJohnsonP01.isJohnsonP01K2Cell m 2 then
    FindAllJohnsonP01.relCostJohnsonP01K2 m 2
  else
    GaussianHammingZoomK2Base.relCostGaussianHammingZoomK2Base m 2

/-- Prefix subregister embedding `m * (n + 1) + 2 * n` into `findAllQubits n m 2`. -/
def avg2SubReg (n m : ℕ) : QRegister (m * (n + 1) + 2 * n) (findAllQubits n m 2) :=
  QRegister.block 0 (m * (n + 1) + 2 * n) (by unfold findAllQubits; nlinarith)

/-- Unified `(m, 2)` dynamic circuit on `findAllQubits n m 2` dispatching
  `FindAllJohnsonP01` on
  `m ∈ {2, 4, 8}` and `GaussianHammingZoomK2Base` on `m ∈ {16.. 1024}`. -/
noncomputable def muxColdAvg2Circuit {Var : Type} [DecidableEq Var] (res : Var) (n m : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m 2)) Var
      (findAllQubits n m 2) ((n + 1) * m) :=
  if FindAllJohnsonP01.isJohnsonP01K2Cell m 2 then
    embedOracleCirc (avg2SubReg n m) (FindAllJohnsonP01.findAllJohnsonP01K2Circuit res n m 2)
  else
    embedOracleCirc (avg2SubReg n m)
      (GaussianHammingZoomK2Base.findAllGaussianHammingZoomK2BaseCircuit res n m 2)

private lemma avg2_grid_cases {m : ℕ} (hm_grid : m ∈ GroverSol.groverGrid) (hm2 : 2 ≤ m) :
    FindAllJohnsonP01.isJohnsonP01K2Cell m 2 = true ∨
      (FindAllJohnsonP01.isJohnsonP01K2Cell m 2 = false ∧
        GaussianHammingZoomK2Base.isGaussianHammingZoomK2BaseCell m 2 = true) := by
  simp only [GroverSol.groverGrid, Finset.mem_image, Finset.mem_range] at hm_grid
  obtain ⟨i, hi, rfl⟩ := hm_grid
  interval_cases i <;> first | omega | exact Or.inl rfl | exact Or.inr ⟨rfl, rfl⟩

private lemma avg2_oracle_eq {n : ℕ} (m : ℕ) (B : Finset (Fin (2 ^ n))) :
    GroverSol.groverParallelMarkingOracle m B = parallelMarkingOracle m B := by
  unfold GroverSol.groverParallelMarkingOracle GroverSol.groverSetMarkingOracle
    parallelMarkingOracle setMarkingOracle
  rfl

/-- Uniform-average correctness and `AvgOracleCostBound` of `muxColdAvg2Circuit` for every
  `m ∈ groverGrid` with `2 ≤ m`. -/
theorem muxColdAvg2_spec {Var : Type} [DecidableEq Var] (res : Var) {m : ℕ}
    (hm_grid : m ∈ GroverSol.groverGrid) (hm2 : 2 ≤ m) :
    ∃ n₀ : ℕ, 600 ≤ n₀ ∧ ∀ n ≥ n₀,
      (∀ B ∈ GroverSol.groverTargetSets n 2,
        (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m 2)) ≤
          wp (QProg.qSet ;; (muxColdAvg2Circuit res n m).compile QProg.qAssign
              (GroverSol.groverParallelMarkingOracle m B))
            (liftPureProp (fun τ ↦ GroverSol.decodeTargets n 2 (τ res) = B))) ∧
      GroverSol.AvgOracleCostBound (Var := Var) 2
        (fun B ↦ CostModel.ofEmbeddedOracle (GroverSol.groverParallelMarkingOracle m B))
        (fun B ↦ QProg.qSet ;; (muxColdAvg2Circuit res n m).compile QProg.qAssign
          (GroverSol.groverParallelMarkingOracle m B))
        (((muxColdAvg2RelCost m : ℝ) * GroverSol.groverHarmonicSqrtSum 2) *
          ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ)))) := by
  rcases avg2_grid_cases hm_grid hm2 with hp01 | ⟨hnp01, hzoom⟩
  · obtain ⟨n₁, hn₁⟩ := FindAllJohnsonP01.johnsonP01K2_relCost (Var := Var) res hp01
    refine ⟨max 600 n₁, le_max_left 600 n₁, fun n hn ↦ ?_⟩
    have hn1 : 1 ≤ n := le_trans (by norm_num : 1 ≤ 600) ((le_max_left 600 n₁).trans hn)
    have hn_ge : n₁ ≤ n := (le_max_right 600 n₁).trans hn
    have hkN : 2 ≤ 2 ^ n :=
      le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hn1)
    have hcirc : muxColdAvg2Circuit (Var := Var) res n m =
        embedOracleCirc (avg2SubReg n m)
          (FindAllJohnsonP01.findAllJohnsonP01K2Circuit res n m 2) := by
      simp [muxColdAvg2Circuit, hp01]
    have hrel : muxColdAvg2RelCost m = FindAllJohnsonP01.relCostJohnsonP01K2 m 2 := by
      simp [muxColdAvg2RelCost, hp01]
    obtain ⟨q, hq_cb, hq_sum⟩ := hn₁ n hn_ge hkN
    refine ⟨fun B hB ↦ ?_, q, fun B hB ↦ ?_, ?_⟩
    · rw [hcirc, avg2_oracle_eq]
      have htri := FindAllJohnsonP01.johnsonP01K2_correctness (Var := Var) res
        hn1 hp01 hkN hB
      exact wp_qSet_embedOracleCirc_liftPureProp (avg2SubReg n m) _ _
        (top_le_wp_of_triple_top htri)
    · dsimp only
      rw [hcirc, avg2_oracle_eq]
      exact costBound_qSet_embedOracleCirc (avg2SubReg n m) _
        (isRealMatrix_parallelMarkingOracle B) (hq_cb B hB)
    · rw [hrel]
      dsimp only [GroverSol.groverTargetSets, GroverSol.groverHarmonicSqrtSum]
      exact hq_sum.trans_eq (by ring)
  · obtain ⟨n₁, hn₁⟩ :=
      GaussianHammingZoomK2Base.gaussianHammingZoomK2Base_relCost (Var := Var) res hzoom
    refine ⟨max 600 n₁, le_max_left 600 n₁, fun n hn ↦ ?_⟩
    have hn1 : 1 ≤ n := le_trans (by norm_num : 1 ≤ 600) ((le_max_left 600 n₁).trans hn)
    have hn_ge : n₁ ≤ n := (le_max_right 600 n₁).trans hn
    have hkN : 2 ≤ 2 ^ n :=
      le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hn1)
    have hcirc : muxColdAvg2Circuit (Var := Var) res n m =
        embedOracleCirc (avg2SubReg n m)
          (GaussianHammingZoomK2Base.findAllGaussianHammingZoomK2BaseCircuit res n m 2) := by
      simp [muxColdAvg2Circuit, hnp01]
    have hrel :
        muxColdAvg2RelCost m =
          GaussianHammingZoomK2Base.relCostGaussianHammingZoomK2Base m 2 := by
      simp [muxColdAvg2RelCost, hnp01]
    obtain ⟨q, hq_cb, hq_sum⟩ := hn₁ n hn_ge hkN
    refine ⟨fun B hB ↦ ?_, q, fun B hB ↦ ?_, ?_⟩
    · rw [hcirc, avg2_oracle_eq]
      have htri := GaussianHammingZoomK2Base.gaussianHammingZoomK2Base_correctness (Var := Var)
        res hn1 hzoom hkN hB
      exact wp_qSet_embedOracleCirc_liftPureProp (avg2SubReg n m) _ _
        (top_le_wp_of_triple_top htri)
    · dsimp only
      rw [hcirc, avg2_oracle_eq]
      exact costBound_qSet_embedOracleCirc (avg2SubReg n m) _
        (isRealMatrix_parallelMarkingOracle B) (hq_cb B hB)
    · rw [hrel]
      dsimp only [GroverSol.groverTargetSets, GroverSol.groverHarmonicSqrtSum]
      exact hq_sum.trans_eq (by ring)

/-- For every `L_max ≥ 2` and `1 ≤ m`, `Stage1.qubits n (L_max * m) k` already dominates
  `findAllQubits n m k = (n + 1) * m + n * k + 1` with zero extra qubits. -/
theorem findAllQubits_le_muxQubits {n m L_max k : ℕ} (hL2 : 2 ≤ L_max) (hm1 : 1 ≤ m) :
    findAllQubits n m k ≤ (L_max * m) * (n + 1) + k * n := by
  unfold findAllQubits
  have h1m : n + 1 ≤ m * (n + 1) := Nat.le_mul_of_pos_left (n + 1) hm1
  have hLm : 2 * m ≤ L_max * m := Nat.mul_le_mul_right m hL2
  have hmul : (2 * m) * (n + 1) ≤ (L_max * m) * (n + 1) := Nat.mul_le_mul_right (n + 1) hLm
  nlinarith

private lemma sum_stateMass_sliceState {Var : Type} {d : ℕ}
    (res : Var) (W : ℕ) (Γ : CQState (Store Var) d) :
    (∑ v ∈ Finset.range (2 ^ W), stateMass (sliceState res 0 W v Γ)) = stateMass Γ := by
  simp_rw [stateMass_eq_ofReal_trace]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ CQState.trace_nonneg _), ← NNReal.coe_sum,
    QuantumComputation.Specs.GroverFindAll.sum_sliceState_trace]

private lemma wp_measure_highBlock_slice_le_invalidObs {Var : Type} [DecidableEq Var]
    {n M_work k Q : ℕ} (res : Var) (hQ_st1 : M_work * (n + 1) + k * n ≤ Q)
    {S : Finset (Fin (2 ^ n))} {j μVal : ℕ} (hμ : μVal < 2 ^ (k * n))
    (hbad : ¬ DickeSol.MemPrefixValid S j ⟨μVal, hμ⟩) :
    let st1Reg : QRegister (M_work * (n + 1) + k * n) Q :=
      QRegister.block 0 (M_work * (n + 1) + k * n) ((Nat.zero_add _).trans_le hQ_st1)
    let archReg : QRegister (k * n) Q :=
      st1Reg.compose (DickeSol.highBlock (M_work * (n + 1)) (k * n))
    let cond : Store Var → Prop := fun σ ↦ ((σ res).toNat / 2 ^ 0) % 2 ^ (k * n) = μVal
    wp (QProg.measureRegister res archReg) (liftPureProp cond) ≤
      liftAssertion st1Reg (DickeSol.invalidObs n M_work k S j) := by
  intro st1Reg archReg cond σ
  let f_bad (z : Fin (2 ^ Q)) : ℝ :=
    open Classical in
    if (archReg.extractIndex z).val = μVal then 1 else 0
  have hf_b (z : Fin (2 ^ Q)) : 0 ≤ f_bad z ∧ f_bad z ≤ 1 := by
    dsimp only [f_bad]
    split_ifs <;> constructor <;> norm_num
  have hmat : ((wp (QProg.measureRegister res archReg) (liftPureProp cond)) σ).1.1 =
      Matrix.diagonal (fun z ↦ (f_bad z : ℂ)) := by
    rw [DickeSol.wp_measureRegister]
    ext z₁ z₂
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hz : z₁ = z₂
    · subst hz
      let o₀ := archReg.extractIndex z₁
      rw [Finset.sum_eq_single o₀ (fun o _ ho ↦ by
        simp [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
          Matrix.diagonal_mul, o₀, Ne.symm ho])
        (fun hnot ↦ absurd (Finset.mem_univ o₀) hnot)]
      simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
        Matrix.diagonal_mul, o₀, ↓reduceIte, one_mul, mul_one, liftPureProp_apply]
      have hcond_iff : cond (Store.subst σ res (Int.ofNat o₀.val)) ↔ o₀.val = μVal := by
        dsimp only [cond]
        simp [Store.subst, Nat.mod_eq_of_lt o₀.isLt]
      dsimp only [f_bad, o₀]
      open Classical in
      by_cases hm_eq : (archReg.extractIndex z₁).val = μVal
      · rw [ite_eq_left (hcond_iff.mpr hm_eq), ite_eq_left hm_eq]
        simp
      · rw [ite_eq_right (mt hcond_iff.mp hm_eq), ite_eq_right hm_eq]
        simp
    · simp only [hz, ↓reduceIte]
      refine Finset.sum_eq_zero fun o _ ↦ ?_
      simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
        Matrix.diagonal_mul, liftPureProp_apply]
      open Classical in
      by_cases hc : cond (Store.subst σ res (Int.ofNat o.val))
      · rw [ite_eq_left hc]
        simp [hz]
      · rw [ite_eq_right hc]
        simp
  dsimp only [liftAssertion, DickeSol.invalidObs]
  rw [liftObservable_realDiagObs]
  refine DickeSol.le_realDiagObs_of_mat (fun z ↦ (hf_b z).1) (fun z ↦ (hf_b z).2) hmat fun z ↦ ?_
  dsimp only [f_bad, DickeSol.invalidInd]
  have hextr : archReg.extractIndex z =
      (DickeSol.lowHighEquiv (M_work * (n + 1)) (k * n) (st1Reg.extractIndex z)).2 := by
    dsimp only [archReg]
    rw [QRegister.extractIndex_compose, DickeSol.extractIndex_highBlock]
  open Classical in
  by_cases hm_eq : (archReg.extractIndex z).val = μVal
  · have ho_eq :
        (DickeSol.lowHighEquiv (M_work * (n + 1)) (k * n) (st1Reg.extractIndex z)).2 =
          ⟨μVal, hμ⟩ :=
      Fin.ext (hextr.symm.trans (congrArg _ rfl) ▸ hm_eq)
    rw [ite_eq_left hm_eq, ho_eq, ite_eq_right hbad]
  · rw [ite_eq_right hm_eq]
    split_ifs <;> norm_num

/-- Cold-tail `r_rem = 2` readout circuit on `Q` qubits (`M_work * (n + 1) + k * n ≤ Q`,
  `findAllQubits n m k ≤ Q`): measures the `k * n`-bit archive register into `res`, branches via
  `dispBits` to decode `T := memSeen n k (memPrefix k (k - 2)) ⟨μVal, hμ⟩`, and finishes the
  final `2` targets with `deflatedForallTwoFromAvgCircuit` using `muxColdAvg2Circuit`. -/
noncomputable def coldTailValidObsR2Circuit {Var : Type} [DecidableEq Var]
    (res : Var) (n m M_work k Q : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (hQ_st1 : M_work * (n + 1) + k * n ≤ Q) (hQ_fa : findAllQubits n m k ≤ Q) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  let st1Reg : QRegister (M_work * (n + 1) + k * n) Q :=
    QRegister.block 0 (M_work * (n + 1) + k * n) ((Nat.zero_add _).trans_le hQ_st1)
  let archReg : QRegister (k * n) Q :=
    st1Reg.compose (DickeSol.highBlock (M_work * (n + 1)) (k * n))
  .seq (.measure res archReg)
    (dispBits res (k * n) 0 fun μVal ↦
      if hμ : μVal < 2 ^ (k * n) then
        let T := DickeSol.memSeen n k (DickeSol.memPrefix k (k - 2)) ⟨μVal, hμ⟩
        deflatedForallTwoFromAvgCircuit res n m k Q hm_grid hk_grid hm2 hk2 hQ_fa
          (muxColdAvg2Circuit res n m) T
      else .skip)

/-- Pointwise soundness and expected-cost bound for `coldTailValidObsR2Circuit` from any
  incoming
  `CQState` `Δ` satisfying `𝔼[Δ, liftAssertion st1Reg (validObs n M_work k S (k - 2))] =
  Δ.trace`
  (zero `GoodSuffix` hypothesis, zero clean-ancilla requirement on work wires). -/
theorem coldTailValidObsR2_transition {Var : Type} [DecidableEq Var]
    (res : Var) {m M_work k : ℕ}
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) :
    ∃ n₀ : ℕ, 600 ≤ n₀ ∧ ∀ {n Q : ℕ}, n₀ ≤ n →
      ∀ (hQ_st1 : M_work * (n + 1) + k * n ≤ Q) (hQ_fa : findAllQubits n m k ≤ Q)
        {S : Finset (Fin (2 ^ n))}, S.card = k →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)},
      let st1Reg : QRegister (M_work * (n + 1) + k * n) Q :=
        QRegister.block 0 (M_work * (n + 1) + k * n) ((Nat.zero_add _).trans_le hQ_st1)
      𝔼[Δ, liftAssertion st1Reg (DickeSol.validObs n M_work k S (k - 2))] = Δ.trace →
      let prog :=
        (coldTailValidObsR2Circuit res n m M_work k Q hm_grid hk_grid hm2 hk2
          hQ_st1 hQ_fa).compile QProg.qAssign (parallelMarkingOracle m S)
      let uAvg := (muxColdAvg2RelCost m : ℝ) * GroverSol.groverHarmonicSqrtSum 2
      let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
      𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
          stateMass Δ * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := by
  obtain ⟨n₀, hn0_600, havg2_spec⟩ := muxColdAvg2_spec (Var := Var) res hm_grid hm2
  refine ⟨n₀, hn0_600, fun {n Q} hn hQ_st1 hQ_fa {S} hS {Δ} hV ↦ ?_⟩
  have hn600 : 600 ≤ n := hn0_600.trans hn
  obtain ⟨hcorr2, havg2⟩ := havg2_spec n hn
  let st1Reg : QRegister (M_work * (n + 1) + k * n) Q :=
    QRegister.block 0 (M_work * (n + 1) + k * n) ((Nat.zero_add _).trans_le hQ_st1)
  let archReg : QRegister (k * n) Q :=
    st1Reg.compose (DickeSol.highBlock (M_work * (n + 1)) (k * n))
  let oracle := parallelMarkingOracle m S
  let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle oracle
  let post : CQAssertion (Store Var) (2 ^ Q) :=
    liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
  let uAvg : ℝ := (muxColdAvg2RelCost m : ℝ) * GroverSol.groverHarmonicSqrtSum 2
  let unit : ℝ := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
  have huAvg_nn : 0 ≤ uAvg := by
    dsimp only [uAvg, GroverSol.groverHarmonicSqrtSum]
    positivity
  let fBranch (μVal : ℕ) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
    if hμ : μVal < 2 ^ (k * n) then
      let T := DickeSol.memSeen n k (DickeSol.memPrefix k (k - 2)) ⟨μVal, hμ⟩
      deflatedForallTwoFromAvgCircuit res n m k Q hm_grid hk_grid hm2 hk2 hQ_fa
        (muxColdAvg2Circuit res n m) T
    else .skip
  set Δ_meas := (interp (QProg.measureRegister res archReg)).toStateFun Δ
  have htrace_meas : Δ_meas.trace = Δ.trace :=
    CQState.trace_qMeasurement_of_complete res archReg.computationalBasisMeasurement Δ
  have hmass_meas : stateMass Δ_meas = stateMass Δ := by
    rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htrace_meas]
  have hinv0 : 𝔼[Δ, liftAssertion st1Reg (DickeSol.invalidObs n M_work k S (k - 2))] = 0 := by
    rw [expect_liftAssertion_eq_marginalState]
    refine DickeSol.expect_invalidObs_eq_zero ?_
    rw [← expect_liftAssertion_eq_marginalState, hV, trace_marginalState]
  have hbranch (μVal : ℕ) (hμ : μVal < 2 ^ (k * n)) :
      let Ξ := sliceState res 0 (k * n) μVal Δ_meas
      let p_μ := (fBranch μVal).compile QProg.qAssign oracle
      𝔼[(interp p_μ).toStateFun Ξ, post] = Ξ.trace ∧
        expectedCost model p_μ Ξ ≤
          stateMass Ξ * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := by
    intro Ξ p_μ
    dsimp only [p_μ, fBranch]
    rw [dite_eq_left hμ]
    by_cases hval : DickeSol.MemPrefixValid S (k - 2) ⟨μVal, hμ⟩
    · obtain ⟨hcard_T, hTS⟩ := DickeSol.card_memSeen_of_memPrefixValid hval
      have hST2 :
          (S \ DickeSol.memSeen n k (DickeSol.memPrefix k (k - 2)) ⟨μVal, hμ⟩).card = 2 := by
        have hadd := Finset.card_sdiff_add_card_eq_card hTS
        omega
      exact deflatedForallTwoFromAvg_transition res hn600 hm_grid hk_grid hm2 hk2 hQ_fa
        (muxColdAvg2Circuit res n m) huAvg_nn hcorr2 havg2 hS hTS hST2 Ξ
    · let cond : Store Var → Prop := fun σ ↦ ((σ res).toNat / 2 ^ 0) % 2 ^ (k * n) = μVal
      have hle_inv := wp_measure_highBlock_slice_le_invalidObs (Var := Var) res hQ_st1 hμ hval
      have htr_le : (Ξ.trace : ℝ) ≤ 0 := by
        calc (Ξ.trace : ℝ)
            = 𝔼[Δ_meas, liftPureProp cond] :=
              trueState_trace_eq_expect_liftPureProp cond Δ_meas
          _ = 𝔼[Δ, wp (QProg.measureRegister res archReg) (liftPureProp cond)] := by
              rw [wp_expectation_eq]
          _ ≤ 𝔼[Δ, liftAssertion st1Reg (DickeSol.invalidObs n M_work k S (k - 2))] :=
              expect_mono le_rfl hle_inv
          _ = 0 := hinv0
      have hΞ0 : Ξ = 0 :=
        cqState_eq_zero_of_trace_eq_zero (le_antisymm htr_le (CQState.trace_nonneg Ξ))
      rw [hΞ0, interp_toStateFun_zero, expect_zero_state, CQState.trace_zero,
        expectedCost_zero_cqState]
      exact ⟨rfl, zero_le⟩
  dsimp only [coldTailValidObsR2Circuit, OracleDynamicCircuit.compile]
  change 𝔼[(interp (QProg.measureRegister res archReg ;;
        (dispBits res (k * n) 0 fBranch).compile QProg.qAssign oracle)).toStateFun Δ, post] =
      Δ.trace ∧
    expectedCost model
      (QProg.measureRegister res archReg ;;
        (dispBits res (k * n) 0 fBranch).compile QProg.qAssign oracle) Δ ≤
      stateMass Δ * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit)
  constructor
  · change 𝔼[(interp ((dispBits res (k * n) 0 fBranch).compile QProg.qAssign oracle)).toStateFun
        Δ_meas, post] = Δ.trace
    rw [MultiTapStage2.expect_dispBits]
    calc ∑ v ∈ Finset.range (2 ^ (k * n)),
          𝔼[(interp ((fBranch v).compile QProg.qAssign oracle)).toStateFun
            (sliceState res 0 (k * n) v Δ_meas), post]
        = ∑ v ∈ Finset.range (2 ^ (k * n)), ((sliceState res 0 (k * n) v Δ_meas).trace : ℝ) :=
          Finset.sum_congr rfl fun v hv ↦ (hbranch v (Finset.mem_range.mp hv)).1
      _ = Δ_meas.trace := by
          rw [← NNReal.coe_sum,
            QuantumComputation.Specs.GroverFindAll.sum_sliceState_trace res (k * n) Δ_meas]
      _ = Δ.trace := congrArg NNReal.toReal htrace_meas
  · rw [expectedCost_qSeq]
    have hmeas0 : expectedCost model (QProg.measureRegister res archReg) Δ = 0 := by
      have hm_cb : CostBound (Var := Var) model (QProg.measureRegister res archReg) 0 := by
        simpa [QProg.measureRegister, model, CostModel.ofEmbeddedOracle] using
          CostBound.qMeasure (Var := Var) model res _
      exact nonpos_iff_eq_zero.mp (by simpa using hm_cb Δ)
    rw [hmeas0, zero_add]
    change expectedCost model
        ((dispBits res (k * n) 0 fBranch).compile QProg.qAssign oracle) Δ_meas ≤ _
    rw [expectedCost_dispBits]
    calc ∑ v ∈ Finset.range (2 ^ (k * n)),
          expectedCost model ((fBranch v).compile QProg.qAssign oracle)
            (sliceState res 0 (k * n) v Δ_meas)
        ≤ ∑ v ∈ Finset.range (2 ^ (k * n)),
            stateMass (sliceState res 0 (k * n) v Δ_meas) *
              ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) :=
          Finset.sum_le_sum fun v hv ↦ (hbranch v (Finset.mem_range.mp hv)).2
      _ = (∑ v ∈ Finset.range (2 ^ (k * n)),
            stateMass (sliceState res 0 (k * n) v Δ_meas)) *
              ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := (Finset.sum_mul _ _ _).symm
      _ = stateMass Δ_meas * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := by
          rw [sum_stateMass_sliceState]
      _ = stateMass Δ * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := by
          rw [hmass_meas]

/-- Turnkey `+0`-qubit, `+0`-oracle `r_rem = 2` cold-tail circuit directly on
  `Stage1.qubits n (L_max * m) k = (L_max * m) * (n + 1) + k * n` for any `2 ≤ L_max`. -/
noncomputable abbrev muxColdValidObsR2Circuit {Var : Type} [DecidableEq Var]
    (res : Var) (n m L_max k : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hL2 : 2 ≤ L_max) (hk2 : 2 ≤ k) :
    OracleDynamicCircuit (Unitary (2 ^ ((L_max * m) * (n + 1) + k * n))) Var
      ((L_max * m) * (n + 1) + k * n) ((n + 1) * m) :=
  coldTailValidObsR2Circuit res n m (L_max * m) k ((L_max * m) * (n + 1) + k * n)
    hm_grid hk_grid hm2 hk2 le_rfl (findAllQubits_le_muxQubits hL2 (Nat.one_le_of_lt hm2))

/-- Turnkey (`2 ≤ L_max`) cold-tail handoff directly from
  `𝔼[Δ, validObs n (L_max * m) k S (k - 2)] = Δ.trace` on `Stage1.qubits n (L_max * m) k`
  with
  `+0` extra qubits and `+0` extra oracle calls. -/
theorem muxColdValidObsR2_transition {Var : Type} [DecidableEq Var]
    (res : Var) {m L_max k : ℕ}
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hL2 : 2 ≤ L_max) (hk2 : 2 ≤ k) :
    ∃ n₀ : ℕ, 600 ≤ n₀ ∧ ∀ {n : ℕ}, n₀ ≤ n →
      ∀ {S : Finset (Fin (2 ^ n))}, S.card = k →
      ∀ {Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n))},
      𝔼[Δ, DickeSol.validObs n (L_max * m) k S (k - 2)] = Δ.trace →
      let prog :=
        (muxColdValidObsR2Circuit res n m L_max k hm_grid hk_grid hm2 hL2 hk2).compile
          QProg.qAssign (parallelMarkingOracle m S)
      let uAvg := (muxColdAvg2RelCost m : ℝ) * GroverSol.groverHarmonicSqrtSum 2
      let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
      𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
          stateMass Δ * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := by
  obtain ⟨n₀, hn0_600, hgen⟩ :=
    coldTailValidObsR2_transition (Var := Var) res (M_work := L_max * m) hm_grid hk_grid hm2 hk2
  refine ⟨n₀, hn0_600, fun {n} hn {S} hS {Δ} hV ↦ ?_⟩
  have hid :
      liftAssertion (allWiresReg ((L_max * m) * (n + 1) + k * n))
          (DickeSol.validObs (Var := Var) n (L_max * m) k S (k - 2)) =
        DickeSol.validObs n (L_max * m) k S (k - 2) := by
    funext σ
    dsimp only [liftAssertion, DickeSol.validObs]
    rw [liftObservable_realDiagObs]
    apply Subtype.ext
    apply HermitianMat.ext
    simp only [← HermitianMat.val_eq_coe]
    rw [DickeSol.realDiagObs_mat, DickeSol.realDiagObs_mat]
    refine congrArg Matrix.diagonal (funext fun z ↦ congrArg Complex.ofReal ?_)
    rw [extractIndex_allWiresReg]
  have hblk :
      QRegister.block 0 ((L_max * m) * (n + 1) + k * n)
          ((Nat.zero_add _).trans_le le_rfl) =
        allWiresReg ((L_max * m) * (n + 1) + k * n) :=
    rfl
  refine hgen hn le_rfl (findAllQubits_le_muxQubits hL2 (Nat.one_le_of_lt hm2)) hS ?_
  rwa [hblk, hid]

end QuantumComputation.Specs.GroverFindAll.MuxColdTail
end

/-
# Cold `r = 2` Handoff & Step Checker (`FindAllJohnsonRampMuxSparseCold`)

Provides the choice-free `r = 2` `MuxColdTail` correctness bridge and primitive-`Nat`
Bellman boundary checker for width-ramped multiplexed renewal schedules:

1. **Primitive `r = 2` Cold-Tail Checker (`rmsColdR2NumDen`, `rmsCheckColdR2Step`,
   `rmsCheckColdR2Step_sound`)**:
   Certifies `((muxColdAvg2RelCost m * H_2 + 10 ^ (-9)) * (π / 4) / √m) ≤ v2 / 10 ^ 15` on
   `m ∈ groverGrid` (`2 ≤ m`) using `altIsqrt15` and `pi4_lt_p01`.
2. **All-`n ≥ 600` `MuxColdTail` `validObs` Correctness (`rmsMuxColdValidObsR2_correct`)**:
   Establishes `𝔼[(interp prog).toStateFun Δ, decodeTargets = S] = Δ.trace` unconditionally
   for
   every `600 ≤ n` constructively.
-/

namespace QuantumComputation.Specs.DickeSol

open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal)
open QuantumComputation.Specs.GroverFindAll
open QuantumComputation.Specs.GroverFindAll.MultiTapStage2
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace

@[expose] public section

/-- Exact `(num, den)` upper table for `MuxColdTail.muxColdAvg2RelCost m` on `2 ≤ m ≤ 1024`. -/
def rmsColdR2NumDen (m : ℕ) : ℕ × ℕ :=
  cond (m.beq 2) (666702407513, 1000000000000) <|
  cond (m.beq 4) (591373726471, 1000000000000) <|
  cond (m.beq 8) (141689829501, 250000000000) <|
  cond (m.beq 16) (923009733, 1707106781) <|
  cond (m.beq 32) (898435153, 1707106781) <|
  cond (m.beq 64) (887112193, 1707106781) <|
  cond (m.beq 128) (882583166, 1707106781) <|
  cond (m.beq 256) (877613017, 1707106781) <|
  cond (m.beq 512) (873773349, 1707106781) <|
  cond (m.beq 1024) (873464631, 1707106781)
    (0, 0)

/-- Primitive-`Nat` certificate check that `(v2 / 10 ^ 15)` strictly dominates
  `((muxColdAvg2RelCost m * H_2 + 10 ^ (-9)) * (π / 4) / √m)`. -/
def rmsCheckColdR2Step (m v2 : ℕ) : Bool :=
  let nd := rmsColdR2NumDen m
  cond (nd.2.beq 0) false <|
    let sqLo := (altIsqrt15 m).1
    cond (sqLo.beq 0) false <|
      let lhs := Nat.mul (Nat.add (Nat.mul nd.1 1707106781186548) (Nat.mul nd.2 1000000))
        785398163397449
      let rhs := Nat.mul (Nat.mul v2 nd.2) sqLo
      primNatBlt lhs rhs

end

public section

theorem rmsGroverGrid_eq :
    groverGrid = QuantumComputation.Specs.GroverSol.groverGrid := rfl

theorem rmsGroverTargetSets_eq (n k : ℕ) :
    groverTargetSets n k = QuantumComputation.Specs.GroverSol.groverTargetSets n k := rfl

theorem rmsDecodeTargets_eq_sol (n k : ℕ) (z : ℤ) :
    decodeTargets n k z = QuantumComputation.Specs.GroverSol.decodeTargets n k z := by
  unfold decodeTargets QuantumComputation.Specs.GroverSol.decodeTargets
  rfl

theorem rmsDecodeTargets_eq_local (n k : ℕ) (z : ℤ) :
    decodeTargets n k z = decodeTargetsLocal n k z := by
  unfold decodeTargets decodeTargetsLocal
  rfl

theorem rmsOracle_eq_sol {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    groverParallelMarkingOracle m S =
      QuantumComputation.Specs.GroverSol.groverParallelMarkingOracle m S := by
  unfold groverParallelMarkingOracle groverSetMarkingOracle
    QuantumComputation.Specs.GroverSol.groverParallelMarkingOracle
    QuantumComputation.Specs.GroverSol.groverSetMarkingOracle
  rfl

theorem rmsOracle_eq_local {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    groverParallelMarkingOracle m S = parallelMarkingOracle m S := by
  unfold groverParallelMarkingOracle groverSetMarkingOracle
    parallelMarkingOracle setMarkingOracle
  rfl

theorem rmsHarmonic_eq_sol (k : ℕ) :
    groverHarmonicSqrtSum k =
      QuantumComputation.Specs.GroverSol.groverHarmonicSqrtSum k := by
  unfold groverHarmonicSqrtSum QuantumComputation.Specs.GroverSol.groverHarmonicSqrtSum
  rfl

private lemma rmsColdR2NumDen_le {m : ℕ} (hm_grid : m ∈ groverGrid) (hm2 : 2 ≤ m) :
    0 < (rmsColdR2NumDen m).2 ∧
      ((GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ)) ≤
        ((rmsColdR2NumDen m).1 : ℝ) / ((rmsColdR2NumDen m).2 : ℝ) := by
  simp only [groverGrid, Finset.mem_image, Finset.mem_range] at hm_grid
  obtain ⟨i, hi, rfl⟩ := hm_grid; interval_cases i
  · omega
  all_goals
    norm_num only; dsimp only [rmsColdR2NumDen]; refine ⟨by norm_num, ?_⟩
    conv_lhs =>
      simp [GroverFindAll.MuxColdTail.muxColdAvg2RelCost,
        GroverFindAll.FindAllJohnsonP01.isJohnsonP01K2Cell,
        GroverFindAll.FindAllJohnsonP01.relCostJohnsonP01K2,
        GroverFindAll.GaussianHammingZoomK2Base.relCostGaussianHammingZoomK2Base,
        NNRat.divNat_eq_div]
    norm_num

/-- Soundness of `rmsCheckColdR2Step` for `m ∈ groverGrid` (`2 ≤ m`). -/
theorem rmsCheckColdR2Step_sound {m v2 : ℕ} (hm_grid : m ∈ groverGrid) (hm2 : 2 ≤ m)
    (hchk : rmsCheckColdR2Step m v2 = true) :
    (((GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 +
        1 / (10 : ℝ) ^ 9) * ((π / 4) / √(m : ℝ))) ≤ (v2 : ℝ) / wdScaleR := by
  obtain ⟨hden_pos, hrel_le⟩ := rmsColdR2NumDen_le hm_grid hm2
  unfold rmsCheckColdR2Step at hchk
  dsimp only at hchk
  set nd := rmsColdR2NumDen m
  have hcf : ∀ {c b : Bool}, cond c false b = true → c = false ∧ b = true := by
    intro c b h; cases c
    · exact ⟨rfl, h⟩
    · cases h
  replace hchk := (hcf hchk).2; set sqLo := (altIsqrt15 m).1
  have hsq0 := (hcf hchk).1; replace hchk := (hcf hchk).2
  rcases eq_or_ne sqLo 0 with h0 | hne
  · rw [h0] at hsq0; cases hsq0
  · have hsq_pos : 0 < sqLo := by omega
    have hlt_nat :
        (nd.1 * 1707106781186548 + nd.2 * 1000000) * 785398163397449 < (v2 * nd.2) * sqLo := by
      unfold primNatBlt at hchk
      have hb := Nat.ble_eq.mp hchk
      change (nd.1 * 1707106781186548 + nd.2 * 1000000) * 785398163397449 + 1 ≤
        (v2 * nd.2) * sqLo at hb
      omega
    have hlt_R :
        (((nd.1 : ℝ) * 1707106781186548 + (nd.2 : ℝ) * 1000000) * 785398163397449) ≤
          ((v2 : ℝ) * (nd.2 : ℝ)) * (sqLo : ℝ) := by
      exact_mod_cast hlt_nat.le
    have hH2 : groverHarmonicSqrtSum 2 ≤ (1707106781186548 : ℝ) / (10 : ℝ) ^ 15 := by
      have hset : Finset.Icc (1 : ℕ) 2 = {1, 2} := by ext x; simp; omega
      unfold groverHarmonicSqrtSum; rw [hset, Finset.sum_pair (by omega)]
      have hsq2 : (1414213562373095 : ℝ) / (10 : ℝ) ^ 15 ≤ √(2 : ℝ) := by
        refine Real.le_sqrt_of_sq_le ?_
        norm_num
      have hinv2 : 1 / √(2 : ℝ) ≤ (707106781186548 : ℝ) / (10 : ℝ) ^ 15 := by
        have hpos : (0 : ℝ) < (1414213562373095 : ℝ) / (10 : ℝ) ^ 15 := by norm_num
        calc 1 / √(2 : ℝ)
            ≤ 1 / ((1414213562373095 : ℝ) / (10 : ℝ) ^ 15) :=
              one_div_le_one_div_of_le hpos hsq2
          _ ≤ (707106781186548 : ℝ) / (10 : ℝ) ^ 15 := by norm_num
      norm_num at hinv2 ⊢
      linarith
    have hB15 : wdScaleR = (10 : ℝ) ^ 15 := by unfold wdScaleR wdScale; norm_num
    have hpi4 : π / 4 ≤ (785398163397449 : ℝ) / (10 : ℝ) ^ 15 := by
      rw [← hB15]
      exact pi4_lt_p01.le
    have hsqrt_m : (sqLo : ℝ) / (10 : ℝ) ^ 15 ≤ √(m : ℝ) := by
      rw [← hB15]
      exact (altIsqrt15_sound m).1
    have hm_pos : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
    have hdenR_pos : (0 : ℝ) < (nd.2 : ℝ) := by exact_mod_cast hden_pos
    have hsqR_pos : (0 : ℝ) < (sqLo : ℝ) := by exact_mod_cast hsq_pos
    have hrel_nn : 0 ≤ (GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) := by positivity
    have hH2_nn : 0 ≤ groverHarmonicSqrtSum 2 := by
      unfold groverHarmonicSqrtSum
      exact Finset.sum_nonneg fun _ _ ↦ by positivity
    have hterm1 :
        (GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 +
            1 / (10 : ℝ) ^ 9 ≤
          ((nd.1 : ℝ) * 1707106781186548 + (nd.2 : ℝ) * 1000000) /
            ((nd.2 : ℝ) * (10 : ℝ) ^ 15) := by
      have hm1 :
          (GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 ≤
            ((nd.1 : ℝ) / (nd.2 : ℝ)) * ((1707106781186548 : ℝ) / (10 : ℝ) ^ 15) :=
        mul_le_mul hrel_le hH2 hH2_nn (by positivity)
      have heq :
          ((nd.1 : ℝ) / (nd.2 : ℝ)) * ((1707106781186548 : ℝ) / (10 : ℝ) ^ 15) +
              1 / (10 : ℝ) ^ 9 =
            ((nd.1 : ℝ) * 1707106781186548 + (nd.2 : ℝ) * 1000000) /
              ((nd.2 : ℝ) * (10 : ℝ) ^ 15) := by
        field_simp [hdenR_pos.ne']
        ring
      linarith
    have hpi_div :
        (π / 4) / √(m : ℝ) ≤ (785398163397449 : ℝ) / (sqLo : ℝ) := by
      calc (π / 4) / √(m : ℝ)
          ≤ (π / 4) / ((sqLo : ℝ) / (10 : ℝ) ^ 15) :=
            div_le_div_of_nonneg_left (div_nonneg Real.pi_pos.le (by norm_num))
              (div_pos hsqR_pos (by positivity)) hsqrt_m
        _ ≤ ((785398163397449 : ℝ) / (10 : ℝ) ^ 15) / ((sqLo : ℝ) / (10 : ℝ) ^ 15) :=
            div_le_div_of_nonneg_right hpi4 (by positivity)
        _ = (785398163397449 : ℝ) / (sqLo : ℝ) := by
            field_simp [hsqR_pos.ne']
    have hb_nn : 0 ≤ ((nd.1 : ℝ) * 1707106781186548 + (nd.2 : ℝ) * 1000000) /
        ((nd.2 : ℝ) * (10 : ℝ) ^ 15) :=
      div_nonneg
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num))
          (mul_nonneg (Nat.cast_nonneg _) (by norm_num)))
        (by positivity)
    have hc_nn : 0 ≤ (π / 4) / √(m : ℝ) :=
      div_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) hm_pos.le
    calc (((GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 +
            1 / (10 : ℝ) ^ 9) * ((π / 4) / √(m : ℝ)))
        ≤ (((nd.1 : ℝ) * 1707106781186548 + (nd.2 : ℝ) * 1000000) /
            ((nd.2 : ℝ) * (10 : ℝ) ^ 15)) * ((785398163397449 : ℝ) / (sqLo : ℝ)) :=
          mul_le_mul hterm1 hpi_div hc_nn hb_nn
      _ = (((nd.1 : ℝ) * 1707106781186548 + (nd.2 : ℝ) * 1000000) * 785398163397449) /
            (((nd.2 : ℝ) * (sqLo : ℝ)) * (10 : ℝ) ^ 15) := by
          field_simp [hdenR_pos.ne', hsqR_pos.ne']
      _ ≤ (((v2 : ℝ) * (nd.2 : ℝ)) * (sqLo : ℝ)) /
            (((nd.2 : ℝ) * (sqLo : ℝ)) * (10 : ℝ) ^ 15) :=
          div_le_div_of_nonneg_right hlt_R (by positivity)
      _ = (v2 : ℝ) / wdScaleR := by
          unfold wdScaleR wdScale
          norm_num
          field_simp [hdenR_pos.ne', hsqR_pos.ne']

private lemma rmsAvg2_grid_cases {m : ℕ} (hm_grid : m ∈ groverGrid) (hm2 : 2 ≤ m) :
    GroverFindAll.FindAllJohnsonP01.isJohnsonP01K2Cell m 2 = true ∨
      (GroverFindAll.FindAllJohnsonP01.isJohnsonP01K2Cell m 2 = false ∧
        GroverFindAll.GaussianHammingZoomK2Base.isGaussianHammingZoomK2BaseCell m 2 = true) := by
  simp only [groverGrid, Finset.mem_image, Finset.mem_range] at hm_grid
  obtain ⟨i, hi, rfl⟩ := hm_grid
  interval_cases i <;> first | omega | exact Or.inl rfl | exact Or.inr ⟨rfl, rfl⟩

private lemma rmsMuxColdAvg2_correct {Var : Type} [DecidableEq Var] (res : Var) {n m : ℕ}
    (hm_grid : m ∈ groverGrid) (hm2 : 2 ≤ m) (hn1 : 1 ≤ n)
    {B : Finset (Fin (2 ^ n))}
    (hB : B ∈ QuantumComputation.Specs.GroverSol.groverTargetSets n 2) :
    (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m 2)) ≤
      wp (QProg.qSet ;;
        (GroverFindAll.MuxColdTail.muxColdAvg2Circuit res n m).compile qAssign
          (QuantumComputation.Specs.GroverSol.groverParallelMarkingOracle m B))
        (liftPureProp
          (fun τ ↦ QuantumComputation.Specs.GroverSol.decodeTargets n 2 (τ res) = B)) := by
  have hkN : 2 ≤ 2 ^ n :=
    le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hn1)
  have hB' : B ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2 := hB
  have hor_eq :
      QuantumComputation.Specs.GroverSol.groverParallelMarkingOracle m B =
        parallelMarkingOracle m B :=
    (rmsOracle_eq_sol m B).symm.trans (rmsOracle_eq_local m B)
  have hpost_eq :
      (fun τ : Store Var ↦
          QuantumComputation.Specs.GroverSol.decodeTargets n 2 (τ res) = B) =
        fun τ ↦ decodeTargetsLocal n 2 (τ res) = B :=
    funext fun τ ↦ by rw [← rmsDecodeTargets_eq_sol, rmsDecodeTargets_eq_local]
  rcases rmsAvg2_grid_cases hm_grid hm2 with hp01 | ⟨hnp01, hzoom⟩
  · have hcirc : GroverFindAll.MuxColdTail.muxColdAvg2Circuit (Var := Var) res n m =
        embedOracleCirc (GroverFindAll.MuxColdTail.avg2SubReg n m)
          (GroverFindAll.FindAllJohnsonP01.findAllJohnsonP01K2Circuit res n m 2) := by
      unfold GroverFindAll.MuxColdTail.muxColdAvg2Circuit
      exact ite_eq_left hp01
    rw [hcirc, hor_eq, hpost_eq]
    have htri := GroverFindAll.FindAllJohnsonP01.johnsonP01K2_correctness (Var := Var) res
      hn1 hp01 hkN hB'
    exact GroverFindAll.MuxColdTail.wp_qSet_embedOracleCirc_liftPureProp _ _ _
      (GroverFindAll.MuxColdTail.top_le_wp_of_triple_top htri)
  · have hcirc : GroverFindAll.MuxColdTail.muxColdAvg2Circuit (Var := Var) res n m =
        embedOracleCirc (GroverFindAll.MuxColdTail.avg2SubReg n m)
          (GroverFindAll.GaussianHammingZoomK2Base.findAllGaussianHammingZoomK2BaseCircuit
            res n m 2) := by
      unfold GroverFindAll.MuxColdTail.muxColdAvg2Circuit
      have hne : ¬ (GroverFindAll.FindAllJohnsonP01.isJohnsonP01K2Cell m 2 = true) := by
        rw [hnp01]; exact Bool.false_ne_true
      exact ite_eq_right hne
    rw [hcirc, hor_eq, hpost_eq]
    have htri :=
      GroverFindAll.GaussianHammingZoomK2Base.gaussianHammingZoomK2Base_correctness (Var := Var)
        res hn1 hzoom hkN hB'
    exact GroverFindAll.MuxColdTail.wp_qSet_embedOracleCirc_liftPureProp _ _ _
      (GroverFindAll.MuxColdTail.top_le_wp_of_triple_top htri)

end

section
open scoped QuantumComputation.Specs.GroverFindAll.MultiTapStage2.GF2nForallA

private lemma rmsDeflatedForallTwo_correct {Var : Type} [DecidableEq Var] (res : Var)
    {n m k Q : ℕ} (hn600 : 600 ≤ n)
    (hm_grid : m ∈ QuantumComputation.Specs.GroverSol.groverGrid)
    (hk_grid : k ∈ QuantumComputation.Specs.GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hQ : findAllQubits n m k ≤ Q)
    {S T : Finset (Fin (2 ^ n))} (hS : S.card = k) (hTS : T ⊆ S) (hST2 : (S \ T).card = 2)
    (Ξ : CQState (Store Var) (2 ^ Q)) :
    let prog :=
      (deflatedForallTwoFromAvgCircuit res n m k Q hm_grid hk_grid hm2 hk2 hQ
        (GroverFindAll.MuxColdTail.muxColdAvg2Circuit res n m) T).compile qAssign
          (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Ξ,
      liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace := by
  intro prog
  have hn0 : n ≠ 0 := by omega
  have hn1 : 1 ≤ n := by omega
  have hm_wd : m ∈ groverGrid := by rwa [rmsGroverGrid_eq]
  have horacle : IsRealMatrix (parallelMarkingOracle m S).1 :=
    isRealMatrix_parallelMarkingOracle S
  let hseed : 2 * n ≤ Q := by unfold findAllQubits at hQ; nlinarith
  let sub2 : QRegister (findAllQubits n m 2) Q :=
    QRegister.block 0 (findAllQubits n m 2) (by unfold findAllQubits at hQ ⊢; nlinarith)
  let memK : QRegister (n * k) Q :=
    QRegister.block 0 (n * k) (by unfold findAllQubits at hQ; nlinarith)
  let R := S \ T
  let cAvg2 := GroverFindAll.MuxColdTail.muxColdAvg2Circuit (Var := Var) res n m
  dsimp only [prog, deflatedForallTwoFromAvgCircuit]
  rw [dite_eq_right hn0]
  have hrst0 := resetAllCircuit_transition res horacle Ξ
  set Ξ₁ := (interp ((resetAllCircuit res).compile qAssign
    (parallelMarkingOracle m S))).toStateFun Ξ
  set Ξ₂ := (interp ((sampleSeedCircuit res n Q ((n + 1) * m) hseed).compile qAssign
    (parallelMarkingOracle m S))).toStateFun Ξ₁
  let postS : CQAssertion (Store Var) (2 ^ Q) :=
    liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
  let branchFn (uVal : ℕ) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
    if hu : uVal < 2 ^ (2 * n) then
      let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
      if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
        stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
      else
        let perm := GF2nForallA.finAffinePerm hn0
          (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
          (GF2nForallA.seedToGFPair hn0 u).2
        .seq (resetAllCircuit res)
          (.seq (deflateCirc n m T (permOracleCirc n m perm (embedOracleCirc sub2 cAvg2)))
            (dispBits res (2 * n) 0 fun wVal ↦
              let R_dec := (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding
              setClassicalValCircuit res memK (encodeFinsetVal n k (T ∪ R_dec))))
    else .skip
  have hbranch (uVal : ℕ) (hu : uVal < 2 ^ (2 * n)) :
      𝔼[(interp ((branchFn uVal).compile qAssign (parallelMarkingOracle m S))).toStateFun
        (sliceState res 0 (2 * n) uVal Ξ₂), postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
    let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
    let Δ_sl := sliceState res 0 (2 * n) uVal Ξ₂
    have htr_sl : (Δ_sl.trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
      have hs := sampleSeed_sliceState_trace res n Q ((n + 1) * m) hseed
        (parallelMarkingOracle m S) hrst0.2.2.2 hu
      rw [hrst0.2.1] at hs
      exact hs
    dsimp only [branchFn]
    rw [dite_eq_left hu]
    by_cases ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0
    · rw [dite_eq_left ha]
      exact (stage2Fuel0_transition res hn600 hm_grid hk_grid hQ hS hTS Δ_sl).1.trans htr_sl
    · rw [dite_eq_right ha]
      let perm := GF2nForallA.finAffinePerm hn0
        (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
        (GF2nForallA.seedToGFPair hn0 u).2
      let B := R.map perm.toEmbedding
      have hB_mem : B ∈ QuantumComputation.Specs.GroverSol.groverTargetSets n 2 := by
        rw [QuantumComputation.Specs.GroverSol.groverTargetSets, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, by simp [B, R, hST2]⟩
      have hrst_u := resetAllCircuit_transition res horacle Δ_sl
      set Δ_u := (interp ((resetAllCircuit res).compile qAssign
        (parallelMarkingOracle m S))).toStateFun Δ_sl
      let cEmb := embedOracleCirc sub2 cAvg2
      let γ_u := marginalState sub2 Δ_u
      have hγ_supp := supportedOn_zero_marginalState sub2 hrst_u.2.2.2
      have hγ_qset : γ_u = (interp QProg.qSet).toStateFun γ_u := by
        rw [interp_qSet]
        exact cqState_eq_qSet_of_supportedOn_zero hγ_supp
      let postB_loc : CQAssertion (Store Var) (2 ^ findAllQubits n m 2) :=
        liftPureProp (fun τ ↦ QuantumComputation.Specs.GroverSol.decodeTargets n 2 (τ res) = B)
      let postB_glob : CQAssertion (Store Var) (2 ^ Q) :=
        liftPureProp (fun τ ↦ decodeTargetsLocal n 2 (τ res) = B)
      have hliftB : liftAssertion sub2 postB_loc = postB_glob := by
        have hp :
            (fun τ : Store Var ↦
                QuantumComputation.Specs.GroverSol.decodeTargets n 2 (τ res) = B) =
              fun τ ↦ decodeTargetsLocal n 2 (τ res) = B :=
          funext fun τ ↦ by rw [← rmsDecodeTargets_eq_sol, rmsDecodeTargets_eq_local]
        dsimp only [postB_loc, postB_glob]
        rw [hp]
        exact liftAssertion_liftPureProp sub2 _
      let afterC := (interp ((deflateCirc n m T (permOracleCirc n m perm cEmb)).compile
        qAssign (parallelMarkingOracle m S))).toStateFun Δ_u
      have hafterC_B : 𝔼[afterC, postB_glob] = (Δ_u.trace : ℝ) := by
        dsimp only [afterC]
        rw [interp_deflateCirc n m hTS, interp_permOracleCirc n m perm R cEmb,
          ← hliftB, expect_liftAssertion_eq_marginalState, marginalState_interp_embedOracleCirc]
        have horB :
            parallelMarkingOracle m B =
              QuantumComputation.Specs.GroverSol.groverParallelMarkingOracle m B :=
          (rmsOracle_eq_local m B).symm.trans (rmsOracle_eq_sol m B)
        set pSol := QProg.qSet ;; cAvg2.compile qAssign
          (QuantumComputation.Specs.GroverSol.groverParallelMarkingOracle m B)
        have hprog_qset :
            (interp (cAvg2.compile qAssign (parallelMarkingOracle m B))).toStateFun γ_u =
              (interp pSol).toStateFun γ_u := by
          dsimp only [pSol]
          rw [horB, interp_qSeq, QMonad.Q.toStateFun_bind, ← hγ_qset]
        rw [hprog_qset]
        have hge : (γ_u.trace : ℝ) ≤ 𝔼[(interp pSol).toStateFun γ_u, postB_loc] := by
          rw [← expect_top γ_u, ← wp_expectation_eq]
          exact expect_mono le_rfl (rmsMuxColdAvg2_correct res hm_wd hm2 hn1 hB_mem)
        have hle1 : 𝔼[(interp pSol).toStateFun γ_u, postB_loc] ≤
            (((interp pSol).toStateFun γ_u).trace : ℝ) := by
          rw [← expect_top _]; exact expect_mono le_rfl le_top
        have hle2 : (((interp pSol).toStateFun γ_u).trace : ℝ) ≤ γ_u.trace := by
          exact_mod_cast (interp _).trace_toStateFun_le γ_u
        have htr_γ : (γ_u.trace : ℝ) = Δ_u.trace := by
          dsimp only [γ_u]; rw [trace_marginalState]
        linarith
      have htr_after : (afterC.trace : ℝ) = Δ_u.trace := by
        have h1 : 𝔼[afterC, postB_glob] ≤ afterC.trace := by
          rw [← expect_top afterC]; exact expect_mono le_rfl le_top
        have h2 : (afterC.trace : ℝ) ≤ Δ_u.trace := by
          exact_mod_cast (interp _).trace_toStateFun_le Δ_u
        linarith
      let writeBr (wVal : ℕ) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
        let R_dec := (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding
        setClassicalValCircuit res memK (encodeFinsetVal n k (T ∪ R_dec))
      have hw_br (wVal : ℕ) (_hw : wVal < 2 ^ (2 * n)) :
          𝔼[(interp ((writeBr wVal).compile qAssign (parallelMarkingOracle m S))).toStateFun
            (sliceState res 0 (2 * n) wVal afterC), postS] =
            (sliceState res 0 (2 * n) wVal afterC).trace := by
        let Ξ_w := sliceState res 0 (2 * n) wVal afterC
        by_cases hBw : decodeTargetsLocal n 2 (wVal : ℤ) = B
        · have hset_eq : T ∪ (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding = S := by
            rw [hBw, finset_map_symm_map perm R]
            exact Finset.union_sdiff_of_subset hTS
          dsimp only [writeBr]
          rw [hset_eq]
          exact (setClassicalValCircuit_transition res memK (encodeFinsetVal n k S) horacle
            (fun σ ↦ by simp [Store.subst, decodeTargetsLocal_encodeFinsetVal hS]) Ξ_w).1
        · let condW : Store Var → Prop := fun τ ↦ ((τ res).toNat / 2 ^ 0) % 2 ^ (2 * n) = wVal
          have hdisj :
              ∀ τ : Store Var, condW τ → ¬ (decodeTargetsLocal n 2 (τ res) = B) := fun τ hc hb ↦ by
            have hmod : decodeTargetsLocal n 2 (wVal : ℤ) = decodeTargetsLocal n 2 (τ res) := by
              have hc' : (((τ res).toNat / 2 ^ 0) % 2 ^ (2 * n) : ℕ) = wVal := hc
              rw [← hc', pow_zero, Nat.div_one, show 2 * n = n * 2 by ring,
                decodeTargetsLocal_mod_pow]
            exact hBw (hmod.trans hb)
          have hle_not :
              liftPureProp (d := 2 ^ Q) condW ≤
                liftPureProp (fun τ ↦ ¬ (decodeTargetsLocal n 2 (τ res) = B)) := by
            intro τ
            rw [liftPureProp_apply, liftPureProp_apply]
            open Classical in
            by_cases hc : condW τ
            · rw [ite_eq_left hc, ite_eq_left (hdisj τ hc)]
            · rw [ite_eq_right hc]
              exact bot_le
          have hpart_B :
              𝔼[afterC, postB_glob] +
                𝔼[afterC, liftPureProp (fun τ ↦ ¬ (decodeTargetsLocal n 2 (τ res) = B))] =
                afterC.trace := by
            have hp := expect_ite_partition (fun τ : Store Var ↦ decodeTargetsLocal n 2 (τ res) = B)
              afterC ⊤ ⊤
            simp only [ite_self] at hp
            rw [expect_top, expect_top, expect_top] at hp
            have hb1 : 𝔼[afterC, postB_glob] =
                (afterC.restrict (fun τ ↦ decodeTargetsLocal n 2 (τ res) = B)).trace :=
              expect_liftPureProp _ afterC
            have hb2 : 𝔼[afterC, liftPureProp (fun τ ↦ ¬ (decodeTargetsLocal n 2 (τ res) = B))] =
                (afterC.restrict (fun τ ↦ ¬ (decodeTargetsLocal n 2 (τ res) = B))).trace :=
              expect_liftPureProp _ afterC
            linarith
          have htr_w_le : (Ξ_w.trace : ℝ) ≤ 0 := by
            calc (Ξ_w.trace : ℝ)
                = 𝔼[afterC, liftPureProp condW] :=
                  trueState_trace_eq_expect_liftPureProp condW afterC
              _ ≤ 𝔼[afterC, liftPureProp (fun τ ↦ ¬ (decodeTargetsLocal n 2 (τ res) = B))] :=
                  expect_mono le_rfl hle_not
              _ = 0 := by linarith
          have hΞw0 : Ξ_w = 0 :=
            cqState_eq_zero_of_trace_eq_zero (le_antisymm htr_w_le (CQState.trace_nonneg Ξ_w))
          change 𝔼[(interp ((writeBr wVal).compile qAssign (parallelMarkingOracle m S))).toStateFun
            Ξ_w, postS] = Ξ_w.trace
          rw [hΞw0, interp_toStateFun_zero, expect_zero_state, CQState.trace_zero, NNReal.coe_zero]
      simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
      change 𝔼[(interp ((dispBits res (2 * n) 0 writeBr).compile qAssign
        (parallelMarkingOracle m S))).toStateFun afterC, postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace
      rw [MultiTapStage2.expect_dispBits]
      calc ∑ v ∈ Finset.range (2 ^ (2 * n)),
            𝔼[(interp ((writeBr v).compile qAssign (parallelMarkingOracle m S))).toStateFun
              (sliceState res 0 (2 * n) v afterC), postS]
          = ∑ v ∈ Finset.range (2 ^ (2 * n)), ((sliceState res 0 (2 * n) v afterC).trace : ℝ) :=
            Finset.sum_congr rfl fun v hv ↦ hw_br v (Finset.mem_range.mp hv)
        _ = afterC.trace := by rw [← NNReal.coe_sum, sum_sliceState_trace res (2 * n) afterC]
        _ = Δ_u.trace := htr_after
        _ = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by rw [hrst_u.2.1, htr_sl]
  simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
  change 𝔼[(interp ((dispBits res (2 * n) 0 branchFn).compile qAssign
    (parallelMarkingOracle m S))).toStateFun Ξ₂, postS] = Ξ.trace
  rw [MultiTapStage2.expect_dispBits]
  rw [Finset.sum_congr rfl (fun uVal hu ↦ hbranch uVal (Finset.mem_range.mp hu)),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
    mul_one_div_cancel (by positivity), one_mul]

end

public section

private lemma rmsWp_measure_arch_slice_le_invalidObs {Var : Type} [DecidableEq Var]
    {n M_work k : ℕ} (res : Var)
    {S : Finset (Fin (2 ^ n))} {j μVal : ℕ} (hμ : μVal < 2 ^ (k * n))
    (hbad : ¬ MemPrefixValid S j ⟨μVal, hμ⟩) :
    let Q := M_work * (n + 1) + k * n
    let st1Reg : QRegister Q Q := QRegister.block 0 Q ((Nat.zero_add Q).trans_le le_rfl)
    let archReg : QRegister (k * n) Q := st1Reg.compose (highBlock (M_work * (n + 1)) (k * n))
    let cond : Store Var → Prop := fun σ ↦ ((σ res).toNat / 2 ^ 0) % 2 ^ (k * n) = μVal
    wp (measureRegister res archReg) (liftPureProp cond) ≤ invalidObs n M_work k S j := by
  intro Q st1Reg archReg cond σ
  let f_bad (z : Fin (2 ^ Q)) : ℝ :=
    open Classical in
    if (archReg.extractIndex z).val = μVal then 1 else 0
  have hf_b (z : Fin (2 ^ Q)) : 0 ≤ f_bad z ∧ f_bad z ≤ 1 := by
    dsimp only [f_bad]
    split_ifs <;> constructor <;> norm_num
  have hmat : ((wp (measureRegister res archReg) (liftPureProp cond)) σ).1.1 =
      diagonal (fun z ↦ (f_bad z : ℂ)) := by
    rw [wp_measureRegister]
    ext z₁ z₂
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hz : z₁ = z₂
    · subst hz
      let o₀ := archReg.extractIndex z₁
      rw [Finset.sum_eq_single o₀ (fun o _ ho ↦ by
        simp [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
          Matrix.diagonal_mul, o₀, Ne.symm ho])
        (fun hnot ↦ absurd (Finset.mem_univ o₀) hnot)]
      simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
        Matrix.diagonal_mul, o₀, ↓reduceIte, one_mul, mul_one, liftPureProp_apply]
      have hcond_iff : cond (Store.subst σ res (Int.ofNat o₀.val)) ↔ o₀.val = μVal := by
        dsimp only [cond]
        simp [Store.subst, Nat.mod_eq_of_lt o₀.isLt]
      dsimp only [f_bad, o₀]
      open Classical in
      by_cases hm_eq : (archReg.extractIndex z₁).val = μVal
      · rw [ite_eq_left (hcond_iff.mpr hm_eq), ite_eq_left hm_eq]
        simp
      · rw [ite_eq_right (mt hcond_iff.mp hm_eq), ite_eq_right hm_eq]
        simp
    · simp only [hz, ↓reduceIte]
      refine Finset.sum_eq_zero fun o _ ↦ ?_
      simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
        Matrix.diagonal_mul, liftPureProp_apply]
      open Classical in
      by_cases hc : cond (Store.subst σ res (Int.ofNat o.val))
      · rw [ite_eq_left hc]
        simp [hz]
      · rw [ite_eq_right hc]
        simp
  refine le_realDiagObs_of_mat (fun z ↦ (hf_b z).1) (fun z ↦ (hf_b z).2) hmat fun z ↦ ?_
  dsimp only [f_bad, invalidInd]
  have hextr : archReg.extractIndex z =
      (lowHighEquiv (M_work * (n + 1)) (k * n) z).2 := by
    have hblk : st1Reg = allWiresReg Q := rfl
    dsimp only [archReg]
    rw [QRegister.extractIndex_compose, extractIndex_highBlock, hblk,
      extractIndex_allWiresReg]
  open Classical in
  by_cases hm_eq : (archReg.extractIndex z).val = μVal
  · have ho_eq : (lowHighEquiv (M_work * (n + 1)) (k * n) z).2 = ⟨μVal, hμ⟩ :=
      Fin.ext (hextr ▸ hm_eq)
    rw [ite_eq_left hm_eq, ho_eq, ite_eq_right hbad]
  · rw [ite_eq_right hm_eq]
    split_ifs <;> norm_num

/-- All-`n ≥ 600` probability-`1` correctness of `MuxColdTail.muxColdValidObsR2Circuit`
  (choice-free). -/
theorem rmsMuxColdValidObsR2_correct {Var : Type} [DecidableEq Var] (res : Var)
    {n m L_max k : ℕ} (hn600 : 600 ≤ n)
    (hm_grid : m ∈ QuantumComputation.Specs.GroverSol.groverGrid)
    (hk_grid : k ∈ QuantumComputation.Specs.GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hL2 : 2 ≤ L_max) (hk2 : 2 ≤ k)
    {S : Finset (Fin (2 ^ n))} (hS : S.card = k)
    {Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n))}
    (hV : 𝔼[Δ, validObs n (L_max * m) k S (k - 2)] = Δ.trace) :
    let prog :=
      (GroverFindAll.MuxColdTail.muxColdValidObsR2Circuit res n m L_max k
        hm_grid hk_grid hm2 hL2 hk2).compile qAssign (groverParallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ,
      liftPureProp (fun τ ↦ decodeTargets n k (τ res) = S)] = Δ.trace := by
  intro prog
  let M_work := L_max * m
  let Q := M_work * (n + 1) + k * n
  let hQ_fa := GroverFindAll.MuxColdTail.findAllQubits_le_muxQubits (n := n) (k := k) hL2
    (Nat.one_le_of_lt hm2)
  let st1Reg : QRegister Q Q := QRegister.block 0 Q ((Nat.zero_add Q).trans_le le_rfl)
  let archReg : QRegister (k * n) Q := st1Reg.compose (highBlock (M_work * (n + 1)) (k * n))
  let oracle := parallelMarkingOracle m S
  let post : CQAssertion (Store Var) (2 ^ Q) :=
    liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
  have hpost_eq :
      liftPureProp (d := 2 ^ Q) (fun τ ↦ decodeTargets n k (τ res) = S) = post := rfl
  let fBranch (μVal : ℕ) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
    if hμ : μVal < 2 ^ (k * n) then
      let T := memSeen n k (memPrefix k (k - 2)) ⟨μVal, hμ⟩
      deflatedForallTwoFromAvgCircuit res n m k Q hm_grid hk_grid hm2 hk2 hQ_fa
        (GroverFindAll.MuxColdTail.muxColdAvg2Circuit res n m) T
    else .skip
  set Δ_meas := (interp (measureRegister res archReg)).toStateFun Δ
  have htrace_meas : Δ_meas.trace = Δ.trace :=
    CQState.trace_qMeasurement_of_complete res archReg.computationalBasisMeasurement Δ
  have hinv0 : 𝔼[Δ, invalidObs n M_work k S (k - 2)] = 0 := expect_invalidObs_eq_zero hV
  have hbranch (μVal : ℕ) (hμ : μVal < 2 ^ (k * n)) :
      𝔼[(interp ((fBranch μVal).compile qAssign oracle)).toStateFun
        (sliceState res 0 (k * n) μVal Δ_meas), post] =
        (sliceState res 0 (k * n) μVal Δ_meas).trace := by
    let Ξ := sliceState res 0 (k * n) μVal Δ_meas
    dsimp only [fBranch]
    rw [dite_eq_left hμ]
    by_cases hval : MemPrefixValid S (k - 2) ⟨μVal, hμ⟩
    · obtain ⟨hcard_T, hTS⟩ := card_memSeen_of_memPrefixValid hval
      have hST2 : (S \ memSeen n k (memPrefix k (k - 2)) ⟨μVal, hμ⟩).card = 2 := by
        have hadd := Finset.card_sdiff_add_card_eq_card hTS
        omega
      exact rmsDeflatedForallTwo_correct res hn600 hm_grid hk_grid hm2 hk2 hQ_fa hS hTS hST2 Ξ
    · let cond : Store Var → Prop := fun σ ↦ ((σ res).toNat / 2 ^ 0) % 2 ^ (k * n) = μVal
      have hle_inv :=
        rmsWp_measure_arch_slice_le_invalidObs (Var := Var) (M_work := M_work) res hμ hval
      have htr_le : (Ξ.trace : ℝ) ≤ 0 := by
        calc (Ξ.trace : ℝ)
            = 𝔼[Δ_meas, liftPureProp cond] :=
              trueState_trace_eq_expect_liftPureProp cond Δ_meas
          _ = 𝔼[Δ, wp (measureRegister res archReg) (liftPureProp cond)] := by
              rw [wp_expectation_eq]
          _ ≤ 𝔼[Δ, invalidObs n M_work k S (k - 2)] := expect_mono le_rfl hle_inv
          _ = 0 := hinv0
      have hΞ0 : Ξ = 0 :=
        cqState_eq_zero_of_trace_eq_zero (le_antisymm htr_le (CQState.trace_nonneg Ξ))
      change 𝔼[(interp (_)).toStateFun Ξ, post] = Ξ.trace
      rw [hΞ0, interp_toStateFun_zero, expect_zero_state, CQState.trace_zero, NNReal.coe_zero]
  dsimp only [prog]
  rw [rmsOracle_eq_local, hpost_eq]
  dsimp only [GroverFindAll.MuxColdTail.muxColdValidObsR2Circuit,
    GroverFindAll.MuxColdTail.coldTailValidObsR2Circuit, compile]
  change 𝔼[(interp (measureRegister res archReg ;;
    (dispBits res (k * n) 0 fBranch).compile qAssign oracle)).toStateFun Δ, post] = Δ.trace
  rw [interp_qSeq, QMonad.Q.toStateFun_bind]
  change 𝔼[(interp ((dispBits res (k * n) 0 fBranch).compile qAssign oracle)).toStateFun
    Δ_meas, post] = Δ.trace
  rw [MultiTapStage2.expect_dispBits]
  calc ∑ v ∈ Finset.range (2 ^ (k * n)),
        𝔼[(interp ((fBranch v).compile qAssign oracle)).toStateFun
          (sliceState res 0 (k * n) v Δ_meas), post]
      = ∑ v ∈ Finset.range (2 ^ (k * n)), ((sliceState res 0 (k * n) v Δ_meas).trace : ℝ) :=
        Finset.sum_congr rfl fun v hv ↦ hbranch v (Finset.mem_range.mp hv)
    _ = Δ_meas.trace := by rw [← NNReal.coe_sum, sum_sliceState_trace res (k * n) Δ_meas]
    _ = Δ.trace := congrArg NNReal.toReal htrace_meas

end
end QuantumComputation.Specs.DickeSol

namespace QuantumComputation.Specs.DickeSol

open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace

public section

/- ## 3. Active-Prefix Deflated Multiplexed Ops, Step-Up Circuits & Pass Front -/

private abbrev rms_groupReg (n m L : ℕ) (c : Fin L) :
    QRegister (m * (n + 1)) ((L * m) * (n + 1)) :=
  groupReg (n := n) (rfl : L * m = L * m) c
private abbrev rms_oracleReg (n m k L : ℕ) (c : Fin L) :
    QRegister ((n + 1) * m) ((L * m) * (n + 1) + k * n) :=
  (lowBlock ((L * m) * (n + 1)) (k * n)).compose ((rms_groupReg n m L c).compose (fullReg n m))
private noncomputable def rms_oracleList {Var : Type} (n m k L : ℕ) :
    List (Fin L) → OracleCirc Var ((L * m) * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | c :: cs => .seq (.oracle (rms_oracleReg n m k L c)) (rms_oracleList n m k L cs)
private noncomputable def rms_permList (n m L : ℕ) (S : Finset (Fin (2 ^ n))) :
    List (Fin L) → Equiv.Perm (Fin (2 ^ ((L * m) * (n + 1))))
  | [] => 1
  | c :: cs => rms_permList n m L S cs * liftPerm (rms_groupReg n m L c) (parallelMarkPerm n m S)
private lemma rms_extractIndex_permList {n m L : ℕ} (S : Finset (Fin (2 ^ n))) :
    ∀ (l : List (Fin L)), l.Nodup → ∀ (w : Fin (2 ^ ((L * m) * (n + 1)))) (d : Fin L),
        (rms_groupReg n m L d).extractIndex (rms_permList n m L S l w) =
          if d ∈ l then parallelMarkPerm n m S ((rms_groupReg n m L d).extractIndex w)
          else (rms_groupReg n m L d).extractIndex w
  | [], _, _, _ => by simp [rms_permList]
  | c :: cs, hl, w, d => by
    rcases List.nodup_cons.mp hl with ⟨hc_not, hcs⟩
    dsimp only [rms_permList, Equiv.Perm.mul_apply]; rw [rms_extractIndex_permList S cs hcs]
    by_cases hdc : d = c
    · subst hdc
      rw [ite_eq_right hc_not, liftPerm_apply_eq_replaceIndex, QRegister.extractIndex_replaceIndex,
        ite_eq_left List.mem_cons_self]
    · rw [liftPerm_apply_eq_replaceIndex, QRegister.extractIndex_replaceIndex_of_disjoint _ _
          (groupReg_disjointWires (rfl : L * m = L * m) hdc)]
      simp [List.mem_cons, hdc]
private lemma rms_permList_finRange_eq_parallelMarkPerm (n m L : ℕ) (S : Finset (Fin (2 ^ n))) :
    rms_permList n m L S (List.finRange L) = parallelMarkPerm n (L * m) S := by
  ext w : 1
  apply (basisBits ((L * m) * (n + 1))).injective
  funext q
  obtain ⟨⟨ab, r⟩, rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨⟨c, j⟩, rfl⟩ := finProdFinEquiv.surjective ab
  have hc_eq :
      (rms_groupReg n m L c).extractIndex (rms_permList n m L S (List.finRange L) w) =
        (rms_groupReg n m L c).extractIndex (parallelMarkPerm n (L * m) S w) := by
    rw [rms_extractIndex_permList S (List.finRange L) (List.nodup_finRange L),
      ite_eq_left (List.mem_finRange c),
      extractIndex_groupReg_parallelMarkPerm (rfl : L * m = L * m)]
  rw [← slotReg_apply n (L * m) (finProdFinEquiv (c, j)) r,
    show slotReg n (L * m) (finProdFinEquiv (c, j)) =
        (rms_groupReg n m L c).compose (slotReg n m j) from
      (groupReg_compose_slotReg (rfl : L * m = L * m) c j).symm]
  change basisBits _ _ (((rms_groupReg n m L c).compose (slotReg n m j)) r) =
    basisBits _ _ (((rms_groupReg n m L c).compose (slotReg n m j)) r)
  rw [← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex,
    QRegister.extractIndex_compose, QRegister.extractIndex_compose, hc_eq]
private noncomputable def rmsSignDiagUnitary {d : ℕ} (b : Fin d → Bool) : Unitary d :=
  ⟨diagonal (fun i ↦ if b i then -1 else 1), by
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]; intro i
    split <;> simp⟩
private lemma rmsSignDiagUnitary_mulVec_single {d : ℕ} (b : Fin d → Bool) (z : Fin d) (c : ℂ) :
    (rmsSignDiagUnitary b).1 *ᵥ Pi.single z c =
      Pi.single z ((if b z then (-1 : ℂ) else 1) * c) := by
  funext w; dsimp only [rmsSignDiagUnitary]; rw [mulVec_diagonal]
  by_cases hw : w = z <;> simp [hw]
private theorem rms_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rms_nat_ble_eq_true]
private noncomputable def rmsTagWeightKickUnitary (n M j0 : ℕ) : Unitary (2 ^ (M * (n + 1))) :=
  rmsSignDiagUnitary (fun w ↦ Nat.ble (markedSlotAddrs n M w).length j0)
private lemma rmsTagWeightKick_conj_liftSymVec {n M : ℕ} (R : Finset (Fin (2 ^ n)))
    (j0 : ℕ) (u : SymSubset (2 ^ n) M → ℝ) : (permutationUnitary (parallelMarkPerm n M R)).1 *ᵥ
      ((rmsTagWeightKickUnitary n M j0).1 *ᵥ
        ((permutationUnitary (parallelMarkPerm n M R)).1 *ᵥ liftSymVec n M u)) =
      liftSymVec n M (symPrefixKickVec R j0 u) := by
  rw [liftSymVec_eq_sum_single, liftSymVec_eq_sum_single,
    Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  dsimp only [rmsTagWeightKickUnitary]
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
    permutationUnitary_mulVec_single, rmsSignDiagUnitary_mulVec_single,
    permutationUnitary_mulVec_single, parallelMarkPerm_involutive,
    (markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E).2, mul_one]
  simp only [rms_nat_ble_eq_true]
  funext z; dsimp only [symPrefixKickVec, Pi.smul_apply]
  by_cases hz : z = subsetWorkIdx n M E <;> by_cases hle : (E.1 ∩ R).card ≤ j0 <;>
    simp [hz, hle]
private noncomputable def rms_segDeflatedOracle {Var : Type} (n m k L_end l : ℕ)
    (hl : l ≤ L_end) (active : Finset (Fin k)) :
    OracleCirc Var ((L_end * m) * (n + 1) + k * n) ((n + 1) * m) :=
  let rSeg := rmsSubReg ((l * m) * (n + 1)) ((L_end * m) * (n + 1)) (k * n)
    (Nat.mul_le_mul_right (n + 1) (Nat.mul_le_mul_right m hl))
  .seq (mkrLiftCirc rSeg (rms_oracleList n m k l (List.finRange l)))
    (.step (phaseTag (rSeg.embedUnitary (permutationUnitary (unmarkPerm n (l * m) k active)))))
private noncomputable def rms_segSingleIter {Var : Type} (n m k L_end l s : ℕ)
    (hl : l ≤ L_end) (D : SymOrthogonal (2 ^ n) (l * m)) :
    OracleCirc Var ((L_end * m) * (n + 1) + k * n) ((n + 1) * m) :=
  let rW := (lowBlock ((L_end * m) * (n + 1)) (k * n)).compose (rmsActiveWorkReg n m L_end l hl)
  let fc := rW.embedUnitary (flagConj n (l * m))
  .seq (.seq (.step (phaseTag fc))
      (.seq (rms_segDeflatedOracle n m k L_end l hl (memPrefix k s)) (.step (phaseTag fc))))
    (.step (phaseTag (rW.embedUnitary (liftSymOrthogonal n (l * m) D))))
private noncomputable def rms_segStageLoop {Var : Type} (n m k L_end l s : ℕ)
    (hl : l ≤ L_end) (D : SymOrthogonal (2 ^ n) (l * m)) :
    ℕ → OracleCirc Var ((L_end * m) * (n + 1) + k * n) ((n + 1) * m)
  | 0 => .skip
  | K + 1 =>
      .seq (rms_segSingleIter n m k L_end l s hl D) (rms_segStageLoop n m k L_end l s hl D K)
private noncomputable def rms_segOpsProg {Var : Type} (n m k L_end l s : ℕ) (hl : l ≤ L_end) :
    List (MuxSymOp (2 ^ n) (l * m)) → OracleCirc Var ((L_end * m) * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | .walk K D :: rest =>
      .seq (rms_segStageLoop n m k L_end l s hl D K) (rms_segOpsProg n m k L_end l s hl rest)
  | .prefixKick j0 :: rest =>
      let rW := (lowBlock ((L_end * m) * (n + 1)) (k * n)).compose (rmsActiveWorkReg n m L_end l hl)
      .seq (.seq (rms_segDeflatedOracle n m k L_end l hl (memPrefix k s))
          (.seq (.step (phaseTag (rW.embedUnitary (rmsTagWeightKickUnitary n (l * m) j0))))
            (rms_segDeflatedOracle n m k L_end l hl (memPrefix k s))))
        (rms_segOpsProg n m k L_end l s hl rest)
private noncomputable def rms_stepUpCirc {Var : Type} (n m k L_end l₁ l₂ : ℕ)
    (hm_pos : 0 < m) (hl12 : l₁ ≤ l₂) (hl₂ : l₂ ≤ L_end) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) :
    OracleCirc Var ((L_end * m) * (n + 1) + k * n) ((n + 1) * m) :=
  if hEq : l₁ = l₂ then
    .skip
  else
    let rW₂ :=
      (lowBlock ((L_end * m) * (n + 1)) (k * n)).compose (rmsActiveWorkReg n m L_end l₂ hl₂)
    have hlt : l₁ * m < l₂ * m := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hl12 hEq) hm_pos
    have h2M₂ : 2 * (l₂ * m) ≤ 2 ^ n :=
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right m hl₂)).trans h2Le
    .step (phaseTag (rW₂.embedUnitary (rmsOrthSwapUnitary n (l₁ * m) (l₂ * m) hlt h2M₂)))
private noncomputable def rms_segsProg {Var : Type} (n m k L_end s : ℕ)
    (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) :
    ∀ (L₀ : ℕ), List (MuxSymOp (2 ^ n) (L₀ * m)) → ∀ (segs : List (RampMuxSeg (2 ^ n) m)),
        rmsSegsMono L₀ segs → rmsEndL L₀ segs = L_end →
        OracleCirc Var ((L_end * m) * (n + 1) + k * n) ((n + 1) * m)
  | L₀, ops₀, [], _, hEnd =>
      rms_segOpsProg n m k L_end L₀ s (le_of_eq hEnd) ops₀
  | L₀, ops₀, seg :: rest, hmono, hEnd =>
      have hl₀ : L₀ ≤ L_end := hEnd ▸ rmsEndL_ge hmono
      have hl₁ : seg.lSeg ≤ L_end := hEnd ▸ rmsEndL_ge hmono.2
      .seq (rms_segOpsProg n m k L_end L₀ s hl₀ ops₀)
        (.seq (rms_stepUpCirc n m k L_end L₀ seg.lSeg hm_pos hmono.1 hl₁ h2Le)
          (rms_segsProg n m k L_end s hm_pos h2Le seg.lSeg seg.ops rest hmono.2 hEnd))
private def rms_noMeas {Var : Type} {Q O : ℕ} : OracleCirc Var Q O → Prop
  | .skip | .step _ | .oracle _ => True
  | .seq c₁ c₂ => rms_noMeas c₁ ∧ rms_noMeas c₂
  | _ => False
private lemma rms_wp_eq_of_noMeas {Var : Type} [DecidableEq Var] {Q O : ℕ}
    {c : OracleCirc Var Q O} (hc : rms_noMeas c) (oracle : Unitary (2 ^ O))
    {Θ₁ Θ₂ : CQAssertion (Store Var) (2 ^ Q)} {σ₁ σ₂ : Store Var} (h : Θ₁ σ₁ = Θ₂ σ₂) :
    wp (c.compile qAssign oracle) Θ₁ σ₁ = wp (c.compile qAssign oracle) Θ₂ σ₂ := by
  induction c generalizing Θ₁ Θ₂ with
  | «skip» => exact h
  | «step» U =>
    dsimp only [compile]
    rw [wp_qAssign, wp_qAssign, CQAssertion.qAssign_apply, CQAssertion.qAssign_apply, h]
  | oracle r =>
    dsimp only [compile]
    rw [wp_qAssign, wp_qAssign, CQAssertion.qAssign_apply, CQAssertion.qAssign_apply, h]
  | seq c₁ c₂ ih₁ ih₂ =>
    dsimp only [compile]; rw [wp_qSeq, wp_qSeq]; exact ih₁ hc.1 (ih₂ hc.2 h)
  | _ => cases hc
private lemma rms_noMeas_liftOracleList {Var : Type} {n m k l Q : ℕ}
    (r : QRegister ((l * m) * (n + 1) + k * n) Q) :
    ∀ ls : List (Fin l), rms_noMeas (mkrLiftCirc r (rms_oracleList (Var := Var) n m k l ls))
  | [] => trivial
  | _ :: cs => ⟨trivial, rms_noMeas_liftOracleList r cs⟩
private lemma rms_noMeas_segsProg {Var : Type} {n m k L_end s : ℕ}
    (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) :
    ∀ {L₀ : ℕ} (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m)))
      (segs : List (RampMuxSeg (2 ^ n) m)) (hmono : rmsSegsMono L₀ segs)
      (hEnd : rmsEndL L₀ segs = L_end),
      rms_noMeas (rms_segsProg (Var := Var) n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd) := by
  have horac : ∀ {l} (hl : l ≤ L_end) (active : Finset (Fin k)),
      rms_noMeas (rms_segDeflatedOracle (Var := Var) n m k L_end l hl active) :=
    fun _ _ ↦ ⟨rms_noMeas_liftOracleList _ (List.finRange _), trivial⟩
  have hops : ∀ {l} (hl : l ≤ L_end) (ops : List (MuxSymOp (2 ^ n) (l * m))),
      rms_noMeas (rms_segOpsProg (Var := Var) n m k L_end l s hl ops) := fun {l} hl ops ↦ by
    have hloop (D : SymOrthogonal (2 ^ n) (l * m)) (K : ℕ) :
        rms_noMeas (rms_segStageLoop (Var := Var) n m k L_end l s hl D K) := by
      induction K with
      | zero => trivial
      | succ _ ih => exact ⟨⟨⟨trivial, horac hl _, trivial⟩, trivial⟩, ih⟩
    induction ops with
    | nil => trivial
    | cons op _ ih => cases op with
      | walk K D => exact ⟨hloop D K, ih⟩
      | prefixKick _ => exact ⟨⟨horac hl _, trivial, horac hl _⟩, ih⟩
  have hstep : ∀ {l₁ l₂} (hl12 : l₁ ≤ l₂) (hl₂ : l₂ ≤ L_end),
      rms_noMeas (rms_stepUpCirc (Var := Var) n m k L_end l₁ l₂ hm_pos hl12 hl₂ h2Le) :=
    fun hl12 hl₂ ↦ by unfold rms_stepUpCirc; split_ifs <;> trivial
  intro L₀ ops₀ segs
  induction segs generalizing L₀ with
  | nil => intro _ hEnd; exact hops (le_of_eq hEnd) ops₀
  | cons seg rest ih =>
    intro hmono hEnd; exact ⟨hops _ ops₀, hstep hmono.1 _, ih seg.ops hmono.2 hEnd⟩
private lemma rms_mkrStaticOracleCalls_liftOracleList {Var : Type} {n m k l Q : ℕ}
    (r : QRegister ((l * m) * (n + 1) + k * n) Q) : ∀ ls : List (Fin l),
      mkrStaticOracleCalls (mkrLiftCirc r (rms_oracleList (Var := Var) n m k l ls)) =
        some ls.length
  | [] => rfl
  | _ :: cs => by
    dsimp only [rms_oracleList, mkrLiftCirc, mkrStaticOracleCalls]
    rw [rms_mkrStaticOracleCalls_liftOracleList r cs]; exact congrArg some (Nat.one_add _)
private lemma rms_mkrStaticOracleCalls_segsProg {Var : Type} {n m k L_end s : ℕ}
    (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) :
    ∀ (segs : List (RampMuxSeg (2 ^ n) m)) {L₀ : ℕ} (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m)))
      (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end), mkrStaticOracleCalls
        (rms_segsProg (Var := Var) n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd) =
        some (rmsSegsQueryCount L₀ ops₀ segs) := by
  have horac : ∀ {l} (hl : l ≤ L_end) (active : Finset (Fin k)),
      mkrStaticOracleCalls (rms_segDeflatedOracle (Var := Var) n m k L_end l hl active) =
        some l := fun _ _ ↦ by
    unfold rms_segDeflatedOracle; dsimp only [mkrStaticOracleCalls]
    rw [rms_mkrStaticOracleCalls_liftOracleList]
    simp
  have hstep : ∀ {l₁ l₂} (hl12 : l₁ ≤ l₂) (hl₂ : l₂ ≤ L_end), mkrStaticOracleCalls
        (rms_stepUpCirc (Var := Var) n m k L_end l₁ l₂ hm_pos hl12 hl₂ h2Le) = some 0 :=
    fun _ _ ↦ by unfold rms_stepUpCirc; split_ifs <;> rfl
  have hops : ∀ {l} (hl : l ≤ L_end) (ops : List (MuxSymOp (2 ^ n) (l * m))),
      mkrStaticOracleCalls (rms_segOpsProg (Var := Var) n m k L_end l s hl ops) =
        some (l * muxOpsQueryCount ops) := fun {l} hl ops ↦ by
    have hloop (D : SymOrthogonal (2 ^ n) (l * m)) (K : ℕ) :
        mkrStaticOracleCalls (rms_segStageLoop (Var := Var) n m k L_end l s hl D K) =
          some (K * l) := by
      induction K with
      | zero => simp [rms_segStageLoop, mkrStaticOracleCalls]
      | succ K ih =>
        unfold rms_segStageLoop rms_segSingleIter; dsimp only [mkrStaticOracleCalls]
        rw [horac hl _, ih]
        exact congrArg some (by ring)
    induction ops with
    | nil => simp [rms_segOpsProg, muxOpsQueryCount, mkrStaticOracleCalls]
    | cons op _ ih =>
      cases op with
      | walk K D =>
        unfold rms_segOpsProg; dsimp only [mkrStaticOracleCalls]
        rw [hloop D K, ih]; exact congrArg some (by simp [muxOpsQueryCount]; ring)
      | prefixKick _ =>
        unfold rms_segOpsProg; dsimp only [mkrStaticOracleCalls]
        rw [horac hl _, ih]; exact congrArg some (by simp [muxOpsQueryCount]; ring)
  intro segs
  induction segs with
  | nil => intro _ ops₀ _ hEnd; exact hops (le_of_eq hEnd) ops₀
  | cons seg rest ih =>
    intro _ ops₀ hmono hEnd; unfold rms_segsProg; dsimp only [mkrStaticOracleCalls]
    rw [hops _ ops₀, hstep hmono.1 _, ih seg.ops hmono.2 hEnd]
    exact congrArg some (by simp [rmsSegsQueryCount])
private lemma rms_embedWork_mulVec {n m k L_end l : ℕ} (hl : l ≤ L_end)
    (U : Unitary (2 ^ ((l * m) * (n + 1))))
    (ψ : Fin (2 ^ ((l * m) * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n))) :
    (((lowBlock ((L_end * m) * (n + 1)) (k * n)).compose
        (rmsActiveWorkReg n m L_end l hl)).embedUnitary U).1 *ᵥ
      workMemState (rmsPadState (rmsActiveWorkReg n m L_end l hl) ψ) (Pi.single μ 1) =
    workMemState (rmsPadState (rmsActiveWorkReg n m L_end l hl) (U.1 *ᵥ ψ)) (Pi.single μ 1) := by
  rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
    embedMatrix_lowBlock_mulVec_workMemState, QRegister.embedUnitary_val,
    rms_embedMatrix_mulVec_padState]
private lemma rms_wp_liftOracleList_vecQuad {Var : Type} [DecidableEq Var]
    {n m k l Q : ℕ} (rSeg : QRegister ((l * m) * (n + 1) + k * n) Q) (S : Finset (Fin (2 ^ n))) :
    ∀ (ls : List (Fin l)) (ψ : Fin (2 ^ ((l * m) * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
      (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var), rmsVecQuad
        (((wp ((mkrLiftCirc rSeg (rms_oracleList (Var := Var) n m k l ls)).compile qAssign
            (groverParallelMarkingOracle m S)) Θ) σ).1.1)
        (rmsPadState rSeg (workMemState ψ (Pi.single μ 1))) = rmsVecQuad ((Θ σ).1.1)
        (rmsPadState rSeg
          (workMemState ((permutationUnitary (rms_permList n m l S ls)).1 *ᵥ ψ) (Pi.single μ 1)))
  | [], ψ, _, _, _ => by
    have h1 : (permutationUnitary (1 : Equiv.Perm (Fin (2 ^ ((l * m) * (n + 1)))))).1 = 1 := by
      ext i j; simp
    dsimp only [rms_oracleList, mkrLiftCirc, rms_permList, compile]
    rw [wp_skip, h1, Matrix.one_mulVec]
  | c :: cs, ψ, μ, Θ, σ => by
    dsimp only [rms_oracleList, mkrLiftCirc, rms_permList, compile]
    rw [wp_qSeq, wp_qAssign, qhlQAssign_val, rmsVecQuad_conj,
      QRegister.embedUnitary_compose, QRegister.embedUnitary_val, rms_embedMatrix_mulVec_padState]
    have hemb :
        ((rms_oracleReg n m k l c).embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ
            workMemState ψ (Pi.single μ 1) = workMemState
            ((permutationUnitary (liftPerm (rms_groupReg n m l c) (parallelMarkPerm n m S))).1 *ᵥ ψ)
            (Pi.single μ 1) := by
      dsimp only [rms_oracleReg]
      rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_compose,
        fullReg_embedUnitary_eq_permutationUnitary S, embedUnitary_permutationUnitary,
        QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState]
    rw [hemb, rms_wp_liftOracleList_vecQuad rSeg S cs, mulVec_mulVec, ← Submonoid.coe_mul,
      ← permutationUnitary_mul]
private lemma rms_wp_segDeflatedOracle_vecQuad {Var : Type} [DecidableEq Var]
    {n m k L_end l : ℕ} (hl : l ≤ L_end) {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k))
    (ψ : Fin (2 ^ ((l * m) * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k active μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ ((L_end * m) * (n + 1) + k * n))) (σ : Store Var) : rmsVecQuad
      (((wp ((rms_segDeflatedOracle (Var := Var) n m k L_end l hl active).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState (rmsPadState (rmsActiveWorkReg n m L_end l hl) ψ) (Pi.single μ 1)) =
    rmsVecQuad ((Θ σ).1.1)
      (workMemState
        (rmsPadState (rmsActiveWorkReg n m L_end l hl)
          ((permutationUnitary (parallelMarkPerm n (l * m) (S \ memSeen n k active μ))).1 *ᵥ ψ))
        (Pi.single μ 1)) := by
  have hW : (l * m) * (n + 1) ≤ (L_end * m) * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) (Nat.mul_le_mul_right m hl)
  let rSeg := rmsSubReg ((l * m) * (n + 1)) ((L_end * m) * (n + 1)) (k * n) hW
  have hpad (φ : Fin (2 ^ ((l * m) * (n + 1))) → ℂ) :
      workMemState (rmsPadState (rmsActiveWorkReg n m L_end l hl) φ) (Pi.single μ 1) =
        rmsPadState rSeg (workMemState φ (Pi.single μ 1)) :=
    rms_workMemState_padState _ _ (k * n) hW φ μ
  unfold rms_segDeflatedOracle; dsimp only [compile]
  rw [hpad ψ, hpad, wp_qSeq, rms_wp_liftOracleList_vecQuad rSeg S (List.finRange l),
    rms_permList_finRange_eq_parallelMarkPerm, wp_qAssign, wp_phaseTag,
    qhlQAssign_val, rmsVecQuad_conj, QRegister.embedUnitary_val,
    rms_embedMatrix_mulVec_padState, permutationUnitary_unmarkPerm_mulVec_workMemState,
    mulVec_mulVec, ← Submonoid.coe_mul, ← permutationUnitary_mul,
    parallelMarkPerm_mul_of_subset hsub]
private lemma rms_wp_segOpsProg_vecQuad {Var : Type} [DecidableEq Var]
    {n m k L_end l s : ℕ} (hl : l ≤ L_end) {S : Finset (Fin (2 ^ n))}
    (ops : List (MuxSymOp (2 ^ n) (l * m)))
    (v : SymSubset (2 ^ n) (l * m) → ℝ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k (memPrefix k s) μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ ((L_end * m) * (n + 1) + k * n))) (σ : Store Var) : rmsVecQuad
      (((wp ((rms_segOpsProg (Var := Var) n m k L_end l s hl ops).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState (rmsPadState (rmsActiveWorkReg n m L_end l hl) (liftSymVec n (l * m) v))
        (Pi.single μ 1)) = rmsVecQuad ((Θ σ).1.1)
      (workMemState
        (rmsPadState (rmsActiveWorkReg n m L_end l hl)
          (liftSymVec n (l * m) (evalMuxSymOps (S \ memSeen n k (memPrefix k s) μ) ops v)))
        (Pi.single μ 1)) := by
  let R := S \ memSeen n k (memPrefix k s) μ
  have hiter (D : SymOrthogonal (2 ^ n) (l * m)) (u : SymSubset (2 ^ n) (l * m) → ℝ)
      (Ψ : CQAssertion (Store Var) (2 ^ ((L_end * m) * (n + 1) + k * n))) :
      rmsVecQuad (((wp ((rms_segSingleIter (Var := Var) n m k L_end l s hl D).compile qAssign
          (groverParallelMarkingOracle m S)) Ψ) σ).1.1)
        (workMemState (rmsPadState (rmsActiveWorkReg n m L_end l hl) (liftSymVec n (l * m) u))
          (Pi.single μ 1)) = rmsVecQuad ((Ψ σ).1.1)
        (workMemState
          (rmsPadState (rmsActiveWorkReg n m L_end l hl)
            (liftSymVec n (l * m) (D.1 *ᵥ symZVec R u)))
          (Pi.single μ 1)) := by
    unfold rms_segSingleIter; dsimp only [compile]
    rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      rmsVecQuad_conj, rms_embedWork_mulVec hl,
      rms_wp_segDeflatedOracle_vecQuad hl (memPrefix k s) _ μ hsub,
      wp_qAssign, wp_phaseTag, qhlQAssign_val, rmsVecQuad_conj,
      rms_embedWork_mulVec hl, ← fullReg_embedUnitary_eq_permutationUnitary,
      mulVec_mulVec, mulVec_mulVec, flagConj_mul_embed_mul_flagConj, sDiagM_mulVec_liftSymVec,
      wp_qAssign, wp_phaseTag, qhlQAssign_val, rmsVecQuad_conj,
      rms_embedWork_mulVec hl, liftSymOrthogonal_mulVec]
  have hloop (D : SymOrthogonal (2 ^ n) (l * m)) :
      ∀ (K : ℕ) (u : SymSubset (2 ^ n) (l * m) → ℝ)
        (Ψ : CQAssertion (Store Var) (2 ^ ((L_end * m) * (n + 1) + k * n))),
        rmsVecQuad (((wp ((rms_segStageLoop (Var := Var) n m k L_end l s hl D K).compile qAssign
            (groverParallelMarkingOracle m S)) Ψ) σ).1.1)
          (workMemState (rmsPadState (rmsActiveWorkReg n m L_end l hl) (liftSymVec n (l * m) u))
            (Pi.single μ 1)) = rmsVecQuad ((Ψ σ).1.1)
          (workMemState
            (rmsPadState (rmsActiveWorkReg n m L_end l hl)
              (liftSymVec n (l * m) (evalSymStage R D.1 K u)))
            (Pi.single μ 1)) := by
    intro K
    induction K with
    | zero => intro _ _; rfl
    | succ K ih =>
      intro u Ψ; unfold rms_segStageLoop; dsimp only [compile]
      rw [wp_qSeq, hiter D u _, ih, evalSymStage]
  induction ops generalizing v with
  | nil => rfl
  | cons op tl ih =>
    cases op with
    | walk K D =>
      unfold rms_segOpsProg; dsimp only [compile]; rw [wp_qSeq, hloop D K v _, ih, evalMuxSymOps]
    | prefixKick j0 =>
      unfold rms_segOpsProg; dsimp only [compile]
      rw [wp_qSeq, wp_qSeq, wp_qSeq, rms_wp_segDeflatedOracle_vecQuad hl (memPrefix k s) _ μ hsub,
        wp_qAssign, wp_phaseTag, qhlQAssign_val, rmsVecQuad_conj,
        rms_embedWork_mulVec hl, rms_wp_segDeflatedOracle_vecQuad hl (memPrefix k s) _ μ hsub,
        rmsTagWeightKick_conj_liftSymVec, ih, evalMuxSymOps]
private lemma rms_wp_stepUpCirc_vecQuad {Var : Type} [DecidableEq Var]
    {n m k L_end l₁ l₂ : ℕ} (hm_pos : 0 < m) (hl12 : l₁ ≤ l₂) (hl₂ : l₂ ≤ L_end)
    (h2Le : 2 * (L_end * m) ≤ 2 ^ n) (S : Finset (Fin (2 ^ n)))
    (v : SymSubset (2 ^ n) (l₁ * m) → ℝ) (μ : Fin (2 ^ (k * n)))
    (Θ : CQAssertion (Store Var) (2 ^ ((L_end * m) * (n + 1) + k * n))) (σ : Store Var) : rmsVecQuad
      (((wp ((rms_stepUpCirc (Var := Var) n m k L_end l₁ l₂ hm_pos hl12 hl₂ h2Le).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState
        (rmsPadState (rmsActiveWorkReg n m L_end l₁ (hl12.trans hl₂)) (liftSymVec n (l₁ * m) v))
        (Pi.single μ 1)) = rmsVecQuad ((Θ σ).1.1)
      (workMemState
        (rmsPadState (rmsActiveWorkReg n m L_end l₂ hl₂)
          (liftSymVec n (l₂ * m)
            (if h : l₁ = l₂ then h ▸ v else stepUpFrom (2 ^ n) (l₁ * m) (l₂ * m) *ᵥ v)))
        (Pi.single μ 1)) := by
  unfold rms_stepUpCirc
  by_cases hEq : l₁ = l₂
  · subst hEq
    rw [dite_eq_left rfl, dite_eq_left rfl]; dsimp only [compile]; rw [wp_skip]
  · rw [dite_eq_right hEq, dite_eq_right hEq]
    dsimp only [compile]
    have hlt : l₁ * m < l₂ * m := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hl12 hEq) hm_pos
    have h2M₂ : 2 * (l₂ * m) ≤ 2 ^ n :=
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right m hl₂)).trans h2Le
    have hpad :
        rmsPadState (rmsActiveWorkReg n m L_end l₁ (hl12.trans hl₂)) (liftSymVec n (l₁ * m) v) =
          rmsPadState (rmsActiveWorkReg n m L_end l₂ hl₂)
            (rmsPadState (rmsRelWorkReg n (l₁ * m) (l₂ * m) hlt.le) (liftSymVec n (l₁ * m) v)) := by
      rw [rms_padState_compose, rms_activeWorkReg_compose_relWorkReg hl12 hl₂]
    rw [wp_qAssign, wp_phaseTag, qhlQAssign_val, rmsVecQuad_conj, hpad,
      rms_embedWork_mulVec hl₂, rmsOrthSwapUnitary_mulVec_padState hlt h2M₂]
private lemma rms_wp_segsProg_vecQuad {Var : Type} [DecidableEq Var]
    {n m k L_end s : ℕ} (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k (memPrefix k s) μ ⊆ S) (σ : Store Var) :
    ∀ (segs : List (RampMuxSeg (2 ^ n) m)) (L₀ : ℕ) (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m)))
      (v : SymSubset (2 ^ n) (L₀ * m) → ℝ)
      (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end)
      (Θ : CQAssertion (Store Var) (2 ^ ((L_end * m) * (n + 1) + k * n))), rmsVecQuad
        (((wp ((rms_segsProg (Var := Var) n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd).compile
            qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1)
        (workMemState
          (rmsPadState (rmsActiveWorkReg n m L_end L₀ (hEnd ▸ rmsEndL_ge hmono))
            (liftSymVec n (L₀ * m) v))
          (Pi.single μ 1)) = rmsVecQuad ((Θ σ).1.1)
        (workMemState
          (liftSymVec n (L_end * m)
            (hEnd ▸ evalRampMuxSegs (S \ memSeen n k (memPrefix k s) μ) L₀ ops₀ segs v))
          (Pi.single μ 1))
  | [], L₀, ops₀, v, _, hEnd, Θ => by
    dsimp only [rmsEndL] at hEnd; subst hEnd
    refine (rms_wp_segOpsProg_vecQuad le_rfl ops₀ v μ hsub Θ σ).trans ?_
    dsimp only [rmsActiveWorkReg, evalRampMuxSegs]; rw [rms_padState_self]; rfl
  | seg :: rest, L₀, ops₀, v, hmono, hEnd, Θ => by
    unfold rms_segsProg; dsimp only [compile]
    rw [wp_qSeq, wp_qSeq, rms_wp_segOpsProg_vecQuad _ ops₀ v μ hsub,
      rms_wp_stepUpCirc_vecQuad hm_pos hmono.1 _ h2Le S _ μ,
      rms_wp_segsProg_vecQuad hm_pos h2Le μ hsub σ rest seg.lSeg seg.ops _ hmono.2 hEnd]
    rfl
private lemma rms_sum_sq_symInjMat_mulVec (n M : ℕ) (v : SymSubset (2 ^ n) M → ℝ) :
    (∑ z : Fin (2 ^ (M * (n + 1))), ((symInjMat n M *ᵥ v) z) ^ 2) =
      ∑ E : SymSubset (2 ^ n) M, (v E) ^ 2 := by
  let J := symInjMat n M
  have h1 : (∑ z, ((J *ᵥ v) z) ^ 2) = (J *ᵥ v) ⬝ᵥ (J *ᵥ v) := by simp [dotProduct, sq]
  have h2 : (J *ᵥ v) ⬝ᵥ (J *ᵥ v) = v ⬝ᵥ ((Jᵀ * J) *ᵥ v) := by
    rw [← mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h1, h2, symInjMat_transpose_mul_self, Matrix.one_mulVec]; simp [dotProduct, sq]
private lemma rms_markedSlotAddrs_length_lt_pow (n M : ℕ) (w : Fin (2 ^ (M * (n + 1)))) :
    (markedSlotAddrs n M w).length < 2 ^ (M * (n + 1)) := by
  have hdedup : ∀ l : List (Fin (2 ^ n)), l.dedup.length ≤ l.length := fun l ↦ by
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.dedup_cons]
      split_ifs <;> simp only [List.length_cons] <;> omega
  have h1 : (markedSlotAddrs n M w).length ≤ M := by
    unfold markedSlotAddrs
    calc ((((List.finRange M).filter _).map _).dedup).length
        ≤ (((List.finRange M).filter _).map _).length := hdedup _
      _ = ((List.finRange M).filter _).length := List.length_map _
      _ ≤ (List.finRange M).length := List.length_filter_le _ _
      _ = M := List.length_finRange
  have h2 : M < 2 ^ M := M.lt_two_pow_self
  have h3 : 2 ^ M ≤ 2 ^ (M * (n + 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right M (Nat.succ_pos n))
  omega
private def rmsHitCodeFn (n m_tot k : ℕ)
    (z : Fin (2 ^ (m_tot * (n + 1) + k * n))) : Fin (2 ^ (m_tot * (n + 1) + k * n)) :=
  let wm := lowHighEquiv (m_tot * (n + 1)) (k * n) z
  (lowHighEquiv (m_tot * (n + 1)) (k * n)).symm
    (⟨(markedSlotAddrs n m_tot wm.1).length,
      rms_markedSlotAddrs_length_lt_pow n m_tot wm.1⟩, wm.2)
private lemma rms_wp_mapAndMeasureLow {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M)))
    (oracle : Unitary (2 ^ O)) (H : ℤ → Operator (2 ^ (W + M)))
    (Φ : CQAssertion (Store Var) (2 ^ (W + M))) (hΦ : ∀ τ, (Φ τ).1.1 = H (τ res)) (σ : Store Var) :
    ((wp ((mapAndMeasureLow res W M O g).compile qAssign oracle) Φ) σ).1.1 =
      diagonal (fun z : Fin (2 ^ (W + M)) ↦
        H (Int.ofNat ((lowHighEquiv W M (g z)).1).val) (g z) (g z)) := by
  unfold mapAndMeasureLow; dsimp only [compile]; rw [wp_qSeq]
  let M_meas : Operator (2 ^ (W + M)) :=
    ∑ o : Fin (2 ^ W), (lowBlock W M).basisOutcomeProjector o * H (Int.ofNat o.val) *
        (lowBlock W M).basisOutcomeProjector o
  have hmeas (τ : Store Var) :
      ((wp (measureRegister res (lowBlock W M)) Φ) τ).1.1 = M_meas := by
    rw [wp_measureRegister]
    exact Finset.sum_congr rfl fun o _ ↦ by rw [hΦ]; simp [Store.subst]
  rw [wp_qMap res g oracle (fun _ ↦ M_meas) _ hmeas σ]
  refine congrArg diagonal (funext fun z ↦ ?_)
  dsimp only [M_meas]; rw [Matrix.sum_apply]
  let o₀ : Fin (2 ^ W) := (lowHighEquiv W M (g z)).1
  rw [sum_eq_single o₀ (fun o ho ↦ by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
      extractIndex_lowBlock, ite_eq_right (Ne.symm ho), mul_zero])]
  rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
    extractIndex_lowBlock, ite_eq_left rfl, one_mul, mul_one]
/-- Multi-segment width-ramped multiplexed pass front executing `(L₀, ops₀)` and `segs`
  inside
  `((L_end * m) * (n + 1) + k * n)` qubits (`+0` extra qubits) and recording up to
  `min (L_end * m) (k - s)` distinct hits into the `k * n`-qubit archive. -/
noncomputable def rmsPassFront {Var : Type} (res : Var) (n m k L_end s : ℕ)
    (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n)
    (L₀ : ℕ) (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m))) (segs : List (RampMuxSeg (2 ^ n) m))
    (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end) :
    OracleCirc Var ((L_end * m) * (n + 1) + k * n) ((n + 1) * m) :=
  let W := (L_end * m) * (n + 1)
  let M := k * n
  let O := (n + 1) * m
  have hl₀ : L₀ ≤ L_end := hEnd ▸ rmsEndL_ge hmono
  have hL₀N : L₀ * m ≤ 2 ^ n :=
    (Nat.mul_le_mul_right m hl₀).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans h2Le)
  let rW₀ := (lowBlock W M).compose (rmsActiveWorkReg n m L_end L₀ hl₀)
  .seq (workReset res W M O)
    (.seq (.step (phaseTag (rW₀.embedUnitary
        (householderPrepUnitary (symInjMat n (L₀ * m) *ᵥ u0Vec (2 ^ n) (L₀ * m))
          (by rw [rms_sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hL₀N)))))
      (.seq (rms_segsProg n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd)
        (.seq (rms_segDeflatedOracle n m k L_end L_end le_rfl (memPrefix k s))
          (.seq (.step (phaseTag (permutationUnitary
              (memWriteBatchPerm s (markedSlotAddrs n (L_end * m))))))
            (mapAndMeasureLow res W M O (rmsHitCodeFn n (L_end * m) k))))))
theorem mkrStaticOracleCalls_rmsPassFront {Var : Type} (res : Var) (n m k L_end s : ℕ)
    (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n)
    (L₀ : ℕ) (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m))) (segs : List (RampMuxSeg (2 ^ n) m))
    (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end) : mkrStaticOracleCalls
      (rmsPassFront (Var := Var) res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd) =
      some (rmsSegsQueryCount L₀ ops₀ segs + L_end) := by
  have horac :
      mkrStaticOracleCalls
        (rms_segDeflatedOracle (Var := Var) n m k L_end L_end le_rfl (memPrefix k s)) =
        some L_end := by
    unfold rms_segDeflatedOracle; dsimp only [mkrStaticOracleCalls]
    rw [rms_mkrStaticOracleCalls_liftOracleList]; simp
  unfold rmsPassFront workReset; dsimp only [mkrStaticOracleCalls]
  rw [mkrStaticOracleCalls_mapAndMeasureLow,
    rms_mkrStaticOracleCalls_segsProg hm_pos h2Le segs ops₀ hmono hEnd,
    horac, mkrStaticOracleCalls_mapAndMeasureLow]
  exact congrArg some (by ring)
private lemma wp_rmsPassFront_diag {Var : Type} [DecidableEq Var] (res : Var)
    {n m k s : ℕ} (hm_pos : 0 < m) {L₀ : ℕ} (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m)))
    (segs : List (RampMuxSeg (2 ^ n) m))
    (hmono : rmsSegsMono L₀ segs) (h2Le : 2 * (rmsEndL L₀ segs * m) ≤ 2 ^ n)
    (S : Finset (Fin (2 ^ n))) (G : ℤ → Fin (2 ^ (k * n)) → ℝ)
    (Φ : CQAssertion (Store Var) (2 ^ ((rmsEndL L₀ segs * m) * (n + 1) + k * n))) (hΦ : ∀ τ : Store
      Var,
      (Φ τ).1.1 = diagonal (fun z ↦
          (G (τ res) (lowHighEquiv ((rmsEndL L₀ segs * m) * (n + 1)) (k * n) z).2 : ℂ)))
    (σ : Store Var) : ∃ d_out : Fin (2 ^ ((rmsEndL L₀ segs * m) * (n + 1) + k * n)) → ℂ,
      ((wp ((rmsPassFront res n m k (rmsEndL L₀ segs) s hm_pos h2Le L₀ ops₀ segs hmono rfl).compile
          qAssign (groverParallelMarkingOracle m S)) Φ) σ).1.1 = diagonal d_out ∧
      ∀ z : Fin (2 ^ ((rmsEndL L₀ segs * m) * (n + 1) + k * n)),
        let μ := (lowHighEquiv ((rmsEndL L₀ segs * m) * (n + 1)) (k * n) z).2
        MemPrefixValid S s μ →
          let R := S \ memSeen n k (memPrefix k s) μ
          let v_fin := evalRampMuxSegs R L₀ ops₀ segs (u0Vec (2 ^ n) (L₀ * m))
          d_out z = ∑ E : SymSubset (2 ^ n) (rmsEndL L₀ segs * m), ((v_fin E : ℂ) ^ 2) *
            (G (Int.ofNat (E.1 ∩ R).card)
              ((addrEquiv n k).symm (addrEquiv n k μ +
                batchDelta s (markedSlotAddrs n (rmsEndL L₀ segs * m))
                  (parallelMarkPerm n (rmsEndL L₀ segs * m) R
                    (subsetWorkIdx n (rmsEndL L₀ segs * m) E)))) : ℂ) := by
  let L_f := rmsEndL L₀ segs
  let W := (L_f * m) * (n + 1)
  let M := k * n
  let O := (n + 1) * m
  let oracle := groverParallelMarkingOracle m S
  have hl₀ : L₀ ≤ L_f := rmsEndL_ge hmono
  have hL₀N : L₀ * m ≤ 2 ^ n :=
    (Nat.mul_le_mul_right m hl₀).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans h2Le)
  let rW₀ := (lowBlock W M).compose (rmsActiveWorkReg n m L_f L₀ hl₀)
  let P_ms : QProg Var (2 ^ (W + M)) :=
    (mapAndMeasureLow res W M O (rmsHitCodeFn n (L_f * m) k)).compile qAssign oracle
  let c_u : OracleCirc Var (W + M) O := .seq (.step (phaseTag (rW₀.embedUnitary
        (householderPrepUnitary (symInjMat n (L₀ * m) *ᵥ u0Vec (2 ^ n) (L₀ * m))
          (by rw [rms_sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hL₀N)))))
      (.seq (rms_segsProg n m k L_f s hm_pos h2Le L₀ ops₀ segs hmono rfl)
        (.seq (rms_segDeflatedOracle n m k L_f L_f le_rfl (memPrefix k s))
          (.step (phaseTag (permutationUnitary
            (memWriteBatchPerm (k := k) s (markedSlotAddrs n (L_f * m))))))))
  let d_ms : Fin (2 ^ (W + M)) → ℂ := fun z' ↦
    (G (Int.ofNat (markedSlotAddrs n (L_f * m) (lowHighEquiv W M z').1).length)
      (lowHighEquiv W M z').2 : ℂ)
  have hms_mat (τ : Store Var) : ((wp P_ms Φ) τ).1.1 = diagonal d_ms := by
    rw [rms_wp_mapAndMeasureLow res (rmsHitCodeFn n (L_f * m) k) oracle
      (fun r_val ↦ diagonal (fun z' ↦ (G r_val (lowHighEquiv W M z').2 : ℂ))) Φ hΦ τ]
    refine congrArg diagonal (funext fun z' ↦ ?_)
    rw [Matrix.diagonal_apply_eq]; dsimp only [rmsHitCodeFn, d_ms]; rw [Equiv.apply_symm_apply]
  have hc_u : rms_noMeas c_u := ⟨trivial, rms_noMeas_segsProg hm_pos h2Le ops₀ segs hmono rfl,
      ⟨rms_noMeas_liftOracleList _ (List.finRange _), trivial⟩, trivial⟩
  let M_in : Operator (2 ^ (W + M)) := ((wp (c_u.compile qAssign oracle) (wp P_ms Φ)) σ).1.1
  let c_tail : OracleCirc Var (W + M) O := .seq (.step (phaseTag (rW₀.embedUnitary
        (householderPrepUnitary (symInjMat n (L₀ * m) *ᵥ u0Vec (2 ^ n) (L₀ * m))
          (by rw [rms_sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hL₀N)))))
      (.seq (rms_segsProg n m k L_f s hm_pos h2Le L₀ ops₀ segs hmono rfl)
        (.seq (rms_segDeflatedOracle n m k L_f L_f le_rfl (memPrefix k s))
          (.seq (.step (phaseTag (permutationUnitary
              (memWriteBatchPerm (k := k) s (markedSlotAddrs n (L_f * m))))))
            (mapAndMeasureLow res W M O (rmsHitCodeFn n (L_f * m) k)))))
  have hinner (τ : Store Var) :
      ((wp (c_tail.compile qAssign oracle) Φ) τ).1.1 = M_in := by
    have hwp_eq :
        wp (c_tail.compile qAssign oracle) Φ = wp (c_u.compile qAssign oracle) (wp P_ms Φ) := by
      dsimp only [c_tail, c_u, P_ms, compile]; simp only [wp_qSeq]
    rw [hwp_eq]
    have heq_ms : wp P_ms Φ τ = wp P_ms Φ σ :=
      Subtype.ext (HermitianMat.ext ((hms_mat τ).trans (hms_mat σ).symm))
    exact congrArg (fun x ↦ x.1.1) (rms_wp_eq_of_noMeas hc_u oracle heq_ms)
  refine ⟨fun z ↦ M_in (resetWorkFn W M z) (resetWorkFn W M z), ?_, fun z hval ↦ ?_⟩
  · unfold rmsPassFront workReset
    change (((wp ((mapAndMeasureLow res W M O (resetWorkFn W M)).compile qAssign oracle ;;
      c_tail.compile qAssign oracle) Φ) σ).1.1) = _
    rw [wp_qSeq, rms_wp_mapAndMeasureLow res (resetWorkFn W M) oracle (fun _ ↦ M_in) _ hinner σ]
  · let μ := (lowHighEquiv W M z).2
    let R := S \ memSeen n k (memPrefix k s) μ
    let v_fin := evalRampMuxSegs R L₀ ops₀ segs (u0Vec (2 ^ n) (L₀ * m))
    have hsub : memSeen n k (memPrefix k s) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
    dsimp only [resetWorkFn]
    rw [rmsVecQuad_single M_in ((lowHighEquiv W M).symm (0, μ)), ← workMemState_single,
      ← rms_padState_single_zero (rmsActiveWorkReg n m L_f L₀ hl₀)]
    dsimp only [M_in, c_u, compile]
    rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      rmsVecQuad_conj, rms_embedWork_mulVec hl₀, householderPrepUnitary_mulVec_zero]
    change rmsVecQuad _
      (workMemState (rmsPadState (rmsActiveWorkReg n m L_f L₀ hl₀)
          (liftSymVec n (L₀ * m) (u0Vec (2 ^ n) (L₀ * m)))) (Pi.single μ 1)) = _
    rw [rms_wp_segsProg_vecQuad hm_pos h2Le μ hsub σ segs L₀ ops₀ _ hmono rfl]
    change rmsVecQuad _
      (workMemState (liftSymVec n (L_f * m) v_fin) (Pi.single μ 1)) = _
    rw [← rms_padState_self W (Nat.zero_add W).le (liftSymVec n (L_f * m) v_fin)]
    change rmsVecQuad _
      (workMemState (rmsPadState (rmsActiveWorkReg n m L_f L_f le_rfl)
          (liftSymVec n (L_f * m) v_fin)) (Pi.single μ 1)) = _
    rw [rms_wp_segDeflatedOracle_vecQuad le_rfl (memPrefix k s) _ μ hsub]
    dsimp only [rmsActiveWorkReg]; rw [rms_padState_self]
    change rmsVecQuad _
      (workMemState
        ((permutationUnitary (parallelMarkPerm n (L_f * m) R)).1 *ᵥ liftSymVec n (L_f * m) v_fin)
        (Pi.single μ 1)) = _
    let w_E (E : SymSubset (2 ^ n) (L_f * m)) : Fin (2 ^ W) :=
      parallelMarkPerm n (L_f * m) R (subsetWorkIdx n (L_f * m) E)
    let μ_E (E : SymSubset (2 ^ n) (L_f * m)) : Fin (2 ^ M) :=
      (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s (markedSlotAddrs n (L_f * m)) (w_E E))
    let idx (E : SymSubset (2 ^ n) (L_f * m)) : Fin (2 ^ (W + M)) :=
      (lowHighEquiv W M).symm (w_E E, μ_E E)
    have hinj : Function.Injective idx := fun E₁ E₂ h ↦ by
      have hw : w_E E₁ = w_E E₂ := congrArg Prod.fst ((lowHighEquiv W M).symm.injective h)
      exact subsetWorkIdx_injective n (L_f * m) ((parallelMarkPerm n (L_f * m) R).injective hw)
    have hvec_eq :
        (permutationUnitary (memWriteBatchPerm (k := k) s (markedSlotAddrs n (L_f * m)))).1 *ᵥ
          workMemState
            ((permutationUnitary (parallelMarkPerm n (L_f * m) R)).1 *ᵥ
              liftSymVec n (L_f * m) v_fin)
            (Pi.single μ 1) =
          ∑ E : SymSubset (2 ^ n) (L_f * m), (v_fin E : ℂ) • Pi.single (idx E) 1 := by
      rw [liftSymVec_eq_sum_single n (L_f * m) v_fin, Matrix.mulVec_sum, rmsWorkMemState_sum_left,
        Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun E _ ↦ ?_
      rw [Matrix.mulVec_smul, permutationUnitary_mulVec_single, rmsWorkMemState_smul_left,
        Matrix.mulVec_smul]
      congr 1
      exact (permutationUnitary_memAddPerm_mulVec_single
        (batchDelta s (markedSlotAddrs n (L_f * m))) (w_E E) μ).trans
        (workMemState_single (w_E E) (μ_E E))
    rw [wp_qAssign, wp_phaseTag, qhlQAssign_val, rmsVecQuad_conj, hvec_eq]
    change rmsVecQuad (((wp P_ms Φ) σ).1.1)
      (∑ E : SymSubset (2 ^ n) (L_f * m), (v_fin E : ℂ) • Pi.single (idx E) 1) = _
    rw [hms_mat σ, rmsVecQuad_diagonal_sum_single d_ms v_fin idx hinj]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    congr 1
    dsimp only [d_ms, idx]
    rw [Equiv.apply_symm_apply, (markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E).2]
theorem wp_rmsPassFront_dispPre {Var : Type} [DecidableEq Var] (res : Var)
    {n m k L_end s : ℕ} (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) (_hs : s ≤ k)
    {L₀ : ℕ} (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m))) (segs : List (RampMuxSeg (2 ^ n) m))
    (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) : validObs (Var := Var) n (L_end * m) k S s ≤
      wp ((rmsPassFront res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd).compile qAssign
          (groverParallelMarkingOracle m S))
        (mkrDispPre res n (L_end * m) k S s (min (L_end * m) (k - s))) := by
  subst hEnd; intro σ
  let L_f := rmsEndL L₀ segs
  let b := min (L_f * m) (k - s)
  let G (r_val : ℤ) (μ' : Fin (2 ^ (k * n))) : ℝ :=
    open Classical in
    if MemPrefixValid S (if 1 ≤ r_val ∧ r_val ≤ (b : ℤ) then s + r_val.toNat else s) μ'
    then 1 else 0
  have hΦ (τ : Store Var) :
      (mkrDispPre res n (L_f * m) k S s b τ).1.1 =
        diagonal (fun z ↦ (G (τ res) (lowHighEquiv ((L_f * m) * (n + 1)) (k * n) z).2 : ℂ)) := by
    dsimp only [mkrDispPre]
    split_ifs with h
    · dsimp only [validObs]; rw [realDiagObs_mat]
      refine congrArg diagonal (funext fun z ↦ ?_)
      dsimp only [validInd, G]; rw [ite_eq_left h]
    · dsimp only [validObs]; rw [realDiagObs_mat]
      refine congrArg diagonal (funext fun z ↦ ?_)
      dsimp only [validInd, G]; rw [ite_eq_right h]
  obtain ⟨d_out, hmat, hd_valid⟩ := wp_rmsPassFront_diag res hm_pos ops₀ segs hmono h2Le S G
      (mkrDispPre res n (L_f * m) k S s b) hΦ σ
  have hbnd := observable_diag_real_bounds _ d_out hmat
  have hmat_re :
      ((wp ((rmsPassFront res n m k L_f s hm_pos h2Le L₀ ops₀ segs hmono rfl).compile qAssign
          (groverParallelMarkingOracle m S)) (mkrDispPre res n (L_f * m) k S s b)) σ).1.1 =
        diagonal (fun z ↦ ((d_out z).re : ℂ)) := by
    rw [hmat]; exact congrArg diagonal (funext fun z ↦ (hbnd z).1)
  refine realDiagObs_le_of_mat (fun z ↦ (hbnd z).2.1) (fun z ↦ (hbnd z).2.2) hmat_re fun z ↦ ?_
  dsimp only [validInd]
  open Classical in
  by_cases hval : MemPrefixValid S s (lowHighEquiv ((L_f * m) * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hval]
    let μ := (lowHighEquiv ((L_f * m) * (n + 1)) (k * n) z).2
    let R := S \ memSeen n k (memPrefix k s) μ
    have hseen := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = k - s := by
      dsimp only [R, μ]; rw [Finset.card_sdiff_of_subset hseen.2, hcard, hseen.1]
    have h1 : d_out z = 1 := by
      rw [hd_valid z hval]
      have hterm (E : SymSubset (2 ^ n) (L_f * m)) :
          (G (Int.ofNat (E.1 ∩ R).card)
            ((addrEquiv n k).symm (addrEquiv n k μ +
              batchDelta s (markedSlotAddrs n (L_f * m))
                (parallelMarkPerm n (L_f * m) R (subsetWorkIdx n (L_f * m) E)))) : ℂ) = 1 := by
        have hm_mark := markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E
        have hc_m : (E.1 ∩ R).card ≤ L_f * m :=
          (Finset.card_le_card Finset.inter_subset_left).trans_eq E.2
        have hc_r : (E.1 ∩ R).card ≤ k - s :=
          (Finset.card_le_card Finset.inter_subset_right).trans_eq hR_card
        have hc_b : (E.1 ∩ R).card ≤ b := le_min hc_m hc_r
        have hidx_eq :
            (if 1 ≤ Int.ofNat (E.1 ∩ R).card ∧ Int.ofNat (E.1 ∩ R).card ≤ (b : ℤ)
              then s + (Int.ofNat (E.1 ∩ R).card).toNat else s) = s + (E.1 ∩ R).card := by
          by_cases hc0 : (E.1 ∩ R).card = 0
          · simp [hc0]
          · have hcond : 1 ≤ Int.ofNat (E.1 ∩ R).card ∧ Int.ofNat (E.1 ∩ R).card ≤ (b : ℤ) := by
              rw [Int.ofNat_eq_natCast]
              exact ⟨by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc0, by exact_mod_cast hc_b⟩
            rw [ite_eq_left hcond]; rfl
        have hadv := memPrefixValid_batchAdvance hval (markedSlotAddrs n (L_f * m))
          (parallelMarkPerm n (L_f * m) R (subsetWorkIdx n (L_f * m) E))
          (nodup_markedSlotAddrs n (L_f * m) _) (by rw [hm_mark.2]; omega) hm_mark.1
        rw [hm_mark.2] at hadv; dsimp only [G]; rw [hidx_eq, ite_eq_left hadv]
        exact Complex.ofReal_one
      rw [Finset.sum_congr rfl fun E _ ↦ by rw [hterm E, mul_one]]
      simp_rw [← Complex.ofReal_pow]
      have hL₀N : L₀ * m ≤ 2 ^ n := (Nat.mul_le_mul_right m (rmsEndL_ge hmono)).trans
          ((Nat.le_mul_of_pos_left _ (by omega)).trans h2Le)
      rw [← Complex.ofReal_sum, sum_sq_evalRampMuxSegs R ops₀ segs hmono h2Le,
        sum_sq_u0Vec hL₀N, Complex.ofReal_one]
    rw [h1, Complex.one_re]
  · rw [ite_eq_right hval]
    exact (hbnd z).2.1
theorem wp_rmsPassFront_hitProb {Var : Type} [DecidableEq Var] (res : Var)
    {n m k L_end s w : ℕ} (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) (_hs : s ≤ k)
    {L₀ : ℕ} (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m))) (segs : List (RampMuxSeg (2 ^ n) m))
    (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {c_lo : ℝ} (hc0 : 0 ≤ c_lo) (hc1 : c_lo ≤ 1)
    (hlo : ∀ R : Finset (Fin (2 ^ n)), R.card = k - s →
      c_lo ≤ symHitProb R (evalRampMuxSegs R L₀ ops₀ segs (u0Vec (2 ^ n) (L₀ * m))) w) :
    scaledValidObs (Var := Var) n (L_end * m) k S s c_lo hc0 hc1 ≤
      wp ((rmsPassFront res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd).compile qAssign
          (groverParallelMarkingOracle m S))
        (liftPureProp (mkrHitPred res w)) := by
  subst hEnd; intro σ
  let L_f := rmsEndL L₀ segs
  let G (r_val : ℤ) (_ : Fin (2 ^ (k * n))) : ℝ := if r_val = (w : ℤ) then 1 else 0
  have hΦ (τ : Store Var) :
      (liftPureProp (d := 2 ^ ((L_f * m) * (n + 1) + k * n)) (mkrHitPred res w) τ).1.1 =
        diagonal (fun z ↦ (G (τ res) (lowHighEquiv ((L_f * m) * (n + 1)) (k * n) z).2 : ℂ)) := by
    rw [liftPureProp_apply]
    by_cases hp : mkrHitPred res w τ
    · rw [ite_eq_left hp]; have hp' : τ res = (w : ℤ) := hp; simp [hp', G]
    · rw [ite_eq_right hp]; have hp' : τ res ≠ (w : ℤ) := hp; simp [hp', G]
  obtain ⟨d_out, hmat, hd_valid⟩ :=
    wp_rmsPassFront_diag res hm_pos ops₀ segs hmono h2Le S G (liftPureProp (mkrHitPred res w))
      hΦ σ
  have hbnd := observable_diag_real_bounds _ d_out hmat
  have hmat_re :
      ((wp ((rmsPassFront res n m k L_f s hm_pos h2Le L₀ ops₀ segs hmono rfl).compile qAssign
          (groverParallelMarkingOracle m S)) (liftPureProp (mkrHitPred res w))) σ).1.1 =
        diagonal (fun z ↦ ((d_out z).re : ℂ)) := by
    rw [hmat]; exact congrArg diagonal (funext fun z ↦ (hbnd z).1)
  refine realDiagObs_le_of_mat (fun z ↦ (hbnd z).2.1) (fun z ↦ (hbnd z).2.2) hmat_re fun z ↦ ?_
  dsimp only [validInd]
  open Classical in
  by_cases hval : MemPrefixValid S s (lowHighEquiv ((L_f * m) * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hval, mul_one]
    let μ := (lowHighEquiv ((L_f * m) * (n + 1)) (k * n) z).2
    let R := S \ memSeen n k (memPrefix k s) μ
    have hseen := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = k - s := by
      dsimp only [R, μ]; rw [Finset.card_sdiff_of_subset hseen.2, hcard, hseen.1]
    have hprob :
        d_out z =
          (symHitProb R (evalRampMuxSegs R L₀ ops₀ segs (u0Vec (2 ^ n) (L₀ * m))) w : ℂ) := by
      rw [hd_valid z hval]; unfold symHitProb; rw [Complex.ofReal_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun E _ ↦ ?_
      dsimp only [G]
      have heq_iff : (Int.ofNat (E.1 ∩ R).card = (w : ℤ)) ↔ ((E.1 ∩ R).card = w) := by simp
      by_cases hew : (E.1 ∩ R).card = w
      · rw [ite_eq_left (heq_iff.mpr hew), ite_eq_left hew]; push_cast; ring
      · rw [ite_eq_right (mt heq_iff.mp hew), ite_eq_right hew]; simp
    rw [hprob, Complex.ofReal_re]; exact hlo R hR_card
  · rw [ite_eq_right hval, mul_zero]
    exact (hbnd z).2.1
end
end QuantumComputation.Specs.DickeSol

namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation InnerProductSpace
@[expose] public section
/-- Width-ramped running-cap multiplexed Johnson renewal specification on `(m, k)` with
  workspace
  cap `L_max` (`1 ≤ L_max`, `L_max * m ≤ 65536`) and optional `r = 2` `MuxColdTail` handoff. -/
structure JohnsonRampMuxSparseWalkSpec (m k L_max : ℕ) where
  hL_max_pos : 1 ≤ L_max
  hL_max_hi : L_max * m ≤ 65536
  useWalk : ℕ → Bool
  useColdR2 : Bool
  hColdM2 : useColdR2 = true → 2 ≤ m
  hColdL2 : useColdR2 = true → 2 ≤ L_max
  lInit : ℕ → ℕ
  lEnd : ℕ → ℕ
  hlEnd_pos : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true → 1 ≤ lEnd r
  hlEnd_le : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true → lEnd r ≤ L_max
  n0 : ℕ
  hn0 : 600 ≤ n0
  ops0 : (n r : ℕ) → List (MuxSymOp (2 ^ n) (lInit r * m))
  segsTail : (n r : ℕ) → List (RampMuxSeg (2 ^ n) m)
  hsegs_mono : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    rmsSegsMono (lInit r) (segsTail n r)
  hlEnd_eq : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    rmsEndL (lInit r) (segsTail n r) = lEnd r
  V : ℕ → ℝ
  hV0 : V 0 = 0
  hV_nonneg : ∀ r : ℕ, r ≤ k → 0 ≤ V r
  vCap : ℕ → ℝ
  hvCap_ge : ∀ j r : ℕ, j ≤ r → r ≤ k → V j ≤ vCap r
  hV_cold2 : useColdR2 = true → 2 ≤ k →
    (((GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 +
        1 / (10 : ℝ) ^ 9) * ((π / 4) / √(m : ℝ))) ≤ V 2
  hV_eig : ∀ r : ℕ, 1 ≤ r → r ≤ k → (r = 1 ∨ (useWalk r = false ∧ ¬ (r = 2 ∧ useColdR2 = true))) →
    (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) < V r - V (r - 1)
  pLo : ℕ → ℕ → ℝ
  hpLo_nonneg : ∀ r w, 0 ≤ pLo r w
  hpLo_sum_pos : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true →
    0 < ∑ w ∈ Finset.Icc 1 (min (lEnd r * m) r), pLo r w
  tauWeighted : ℕ → ℝ
  C_step : ℝ
  hqcount_le : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    (rmsSegsQueryCount (lInit r) (ops0 n r) (segsTail n r) : ℝ) ≤
      tauWeighted r * √(2 ^ n : ℝ) + C_step
  hpLo_le : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    ∀ R : Finset (Fin (2 ^ n)), R.card = r → ∀ w ∈ Finset.Icc 1 (min (lEnd r * m) r),
      pLo r w ≤ symHitProb R
        (evalRampMuxSegs R (lInit r) (ops0 n r) (segsTail n r) (u0Vec (2 ^ n) (lInit r * m))) w
  hdrift_ramp_lt : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true → tauWeighted r +
      (∑ w ∈ Finset.Icc 1 (min (lEnd r * m) r), pLo r w * V (r - w)) +
      (1 - ∑ w ∈ Finset.Icc 1 (min (lEnd r * m) r), pLo r w) * vCap r < V r
/-- Real Bellman drift slack at rung `r` under running cap `vCap r` and weighted
  `tauWeighted r`. -/
noncomputable def rmsSlack {m k L_max : ℕ} (spec : JohnsonRampMuxSparseWalkSpec m k L_max) (r : ℕ)
  : ℝ :=
  let b := min (spec.lEnd r * m) r
  let c := ∑ w ∈ Finset.Icc 1 b, spec.pLo r w
  spec.V r - (spec.tauWeighted r +
    (∑ w ∈ Finset.Icc 1 b, spec.pLo r w * spec.V (r - w)) + (1 - c) * spec.vCap r)
/-- Per-rung `√(2 ^ n)` requirement covering walk rounding slack or passive fallback
  constant. -/
noncomputable def rmsStageReqC {m k L_max : ℕ} (spec : JohnsonRampMuxSparseWalkSpec m k L_max) (r :
  ℕ) : ℝ :=
  if _hwalk : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true then
    max 0 (spec.C_step + (spec.lEnd r : ℝ)) / (rmsSlack spec r / 2)
  else (if _hcold : r = 2 ∧ r ≤ k ∧ spec.useColdR2 = true then 0
    else (if _heig : 1 ≤ r ∧ r ≤ k then
      5 / ((spec.V r - spec.V (r - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)))
    else 0))
/-- Nonnegative prefix maximum `max_{0 ≤ i ≤ r} max(0, f i)` over finite stages. -/
noncomputable def rmsMaxUpTo (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => max 0 (f 0)
  | r + 1 => max (rmsMaxUpTo f r) (f (r + 1))
end
public section
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation InnerProductSpace
/- ## 2. Choice-Free Finite-Fuel Width-Ramped Renewal Analysis -/
private lemma rms_two_mul_le_two_pow {m L_max L n : ℕ} (hL_le : L ≤ L_max) (hL_hi : L_max * m ≤
  65536) (hn600 : 600 ≤ n) : 2 * (L * m) ≤ 2 ^ n := by
  calc 2 * (L * m) ≤ 2 * (L_max * m) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right m hL_le)
    _ ≤ 2 * 65536 := Nat.mul_le_mul_left 2 hL_hi
    _ = 2 ^ 17 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
private lemma rms_pLo_sum_le_one {m k L_max : ℕ} (hk_grid : k ∈ groverGrid) (spec :
  JohnsonRampMuxSparseWalkSpec m k L_max) {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k) (hwk : spec.useWalk r
  = true) : (∑ w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r), spec.pLo r w) ≤ 1 ∧ ∀ w ∈ Finset.Icc 1
  (min (spec.lEnd r * m) r), spec.pLo r w ≤ 1 := by
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  have hmono0 := spec.hsegs_mono spec.n0 r le_rfl hr2 hrk hwk
  have hEnd0 := spec.hlEnd_eq spec.n0 r le_rfl hr2 hrk hwk
  have h2Le0 : 2 * (rmsEndL (spec.lInit r) (spec.segsTail spec.n0 r) * m) ≤ 2 ^ spec.n0 := by
    rw [hEnd0]; exact rms_two_mul_le_two_pow (spec.hlEnd_le r hr2 hrk hwk) spec.hL_max_hi spec.hn0
  have hrN₀ : r ≤ 2 ^ spec.n0 := by
    have h1024 : 1024 ≤ 2 ^ 10 := by norm_num
    exact (hrk.trans hk_hi).trans
      (h1024.trans (Nat.pow_le_pow_right (by omega) (by have := spec.hn0; omega)))
  let R₀ : Finset (Fin (2 ^ spec.n0)) :=
    (Finset.range r).attach.image fun x ↦ ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hrN₀⟩
  have hR₀ : R₀.card = r := by
    rw [Finset.card_image_of_injective _ (fun a b h ↦ Subtype.ext (Fin.mk.inj h)),
      Finset.card_attach, Finset.card_range]
  let v₀ := evalRampMuxSegs R₀ (spec.lInit r) (spec.ops0 spec.n0 r)
    (spec.segsTail spec.n0 r) (u0Vec (2 ^ spec.n0) (spec.lInit r * m))
  have hsum_le : (∑ w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r), spec.pLo r w) ≤ 1 := by
    calc ∑ w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r), spec.pLo r w
        ≤ ∑ w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r), symHitProb R₀ v₀ w :=
          Finset.sum_le_sum fun w hw ↦ spec.hpLo_le spec.n0 r le_rfl hr2 hrk hwk R₀ hR₀ w hw
      _ ≤ ∑ w ∈ Finset.range
            (min (rmsEndL (spec.lInit r) (spec.segsTail spec.n0 r) * m) R₀.card + 1),
            symHitProb R₀ v₀ w := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw ↦ ?_)
            (fun w _ _ ↦ symHitProb_nonneg R₀ v₀ w)
          rcases Finset.mem_Icc.mp hw with ⟨_, hwb⟩; rw [Finset.mem_range, hEnd0, hR₀]; omega
      _ = 1 := sum_symHitProb_evalRampMuxSegs R₀ (spec.ops0 spec.n0 r)
          (spec.segsTail spec.n0 r) hmono0 h2Le0
  exact ⟨hsum_le, fun w hw ↦
    (Finset.single_le_sum (fun u _ ↦ spec.hpLo_nonneg r u) hw).trans hsum_le⟩
private noncomputable def rmsAutoFuel {m k L_max : ℕ} (spec : JohnsonRampMuxSparseWalkSpec m k
  L_max) (r : ℕ) : ℕ :=
  let c := ∑ w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r), spec.pLo r w
  Nat.ceil ((1 / ((rmsSlack spec r / 2) / (2 * (k : ℝ) + 1))) / c) + 1
private lemma rmsAutoFuel_spec {m k L_max : ℕ} (hk_grid : k ∈ groverGrid)
    (spec : JohnsonRampMuxSparseWalkSpec m k L_max) {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hwk : spec.useWalk r = true) :
    let c := ∑ w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r), spec.pLo r w
    ∃ F : ℕ, rmsAutoFuel spec r = F + 1 ∧ (1 - c) ^ F * (2 * (k : ℝ)) ≤ rmsSlack spec r / 2 := by
  intro c; have hc0 : 0 < c := spec.hpLo_sum_pos r hr2 hrk hwk
  have hc1 : c ≤ 1 := (rms_pLo_sum_le_one hk_grid spec hr2 hrk hwk).1
  have hslack : 0 < rmsSlack spec r := sub_pos.mpr (spec.hdrift_ramp_lt r hr2 hrk hwk)
  let ε := (rmsSlack spec r / 2) / (2 * (k : ℝ) + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  let F := Nat.ceil ((1 / ε) / c); have h1c : 0 < 1 + c := by linarith
  have hinv_le : 1 - c ≤ (1 + c)⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ h1c]; nlinarith
  have hbern : ∀ j : ℕ, 1 + (j : ℝ) * c ≤ (1 + c) ^ j := fun j ↦ by
    induction j with
    | zero => simp
    | succ j ih =>
      calc 1 + ((j + 1 : ℕ) : ℝ) * c = (1 + (j : ℝ) * c) + 1 * c := by push_cast; ring
        _ ≤ (1 + c) ^ j + (1 + c) ^ j * c :=
            add_le_add ih (mul_le_mul_of_nonneg_right (one_le_pow₀ (by linarith)) hc0.le)
        _ = (1 + c) ^ (j + 1) := by ring
  have hFc : 1 / ε ≤ (F : ℝ) * c := (div_le_iff₀ hc0).mp (Nat.le_ceil ((1 / ε) / c))
  have h1P : 1 / ε ≤ (1 + c) ^ F := (by linarith : 1 / ε ≤ 1 + (F : ℝ) * c).trans (hbern F)
  have hP_inv : ((1 + c) ^ F)⁻¹ ≤ ε := by
    rw [inv_eq_one_div, div_le_iff₀ (pow_pos h1c F)]
    have h2 := mul_le_mul_of_nonneg_right h1P hε.le; rw [one_div_mul_cancel hε.ne'] at h2; linarith
  have hF : (1 - c) ^ F ≤ ε := (pow_le_pow_left₀ (by linarith) hinv_le F).trans
    ((inv_pow (1 + c) F).symm ▸ hP_inv)
  refine ⟨F, rfl, ?_⟩
  have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 1)).mp hF
  have hqF0 : 0 ≤ (1 - c) ^ F := pow_nonneg (by linarith) F; nlinarith
private lemma rms_expect_of_wp {Var : Type} [DecidableEq Var] {Q : ℕ} {Pre Post : CQAssertion (Store
    Var)
  (2 ^ Q)} {P : QProg Var (2 ^ Q)} {Δ : CQState (Store Var) (2 ^ Q)} (hPre : 𝔼[Δ, Pre] = Δ.trace)
    (hwp :
  Pre ≤ wp P Post) : 𝔼[(interp P).toStateFun Δ, Post] = Δ.trace := by
  have h1 : (Δ.trace : ℝ) ≤ 𝔼[(interp P).toStateFun Δ, Post] := by
    rw [← hPre, ← wp_expectation_eq]; exact expect_mono le_rfl hwp
  have h2 : 𝔼[(interp P).toStateFun Δ, Post] ≤ (((interp P).toStateFun Δ).trace : ℝ) := by
    rw [← expect_top _]; exact expect_mono le_rfl le_top
  linarith [NNReal.coe_le_coe.mpr ((interp P).trace_toStateFun_le Δ)]
private lemma rms_expect_mkrDispHits {Var : Type} [DecidableEq Var] (res : Var) {Q O : ℕ} (oracle :
  Unitary (2 ^ O)) (onHit : ℕ → OracleCirc Var Q O) (onZero : OracleCirc Var Q O) (Θ : CQAssertion
  (Store Var) (2 ^ Q)) (u : ℕ) (Γ : CQState (Store Var) (2 ^ Q)) : 𝔼[(interp ((mkrDispHits res onHit
    onZero
  u).compile qAssign oracle)).toStateFun Γ, Θ] = 𝔼[(interp (onZero.compile qAssign
  oracle)).toStateFun (Γ.restrict (mkrMissPred res u)), Θ] + ∑ w ∈ Finset.Icc 1 u, 𝔼[(interp
  ((onHit w).compile qAssign oracle)).toStateFun (Γ.restrict (mkrHitPred res w)), Θ] := by
  induction u generalizing Γ with
  | zero =>
    have hmiss0 : Γ.restrict (mkrMissPred res 0) = Γ :=
      CQState.restrict_of_forall (fun _ w hw ↦ by simp at hw) Γ
    simp [mkrDispHits, hmiss0]
  | succ u ih =>
    let Γ' := Γ.restrict (¬ mkrHitPred res (u + 1) ·)
    have hmiss_eq : Γ'.restrict (mkrMissPred res u) = Γ.restrict (mkrMissPred res (u + 1)) := by
      apply Subtype.ext; funext σ; simp only [Γ', CQState.restrict_coe]
      by_cases h1 : mkrHitPred res (u + 1) σ
      · have hm : ¬ mkrMissPred res (u + 1) σ := fun hm ↦
          hm (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) h1
        rw [ite_eq_right (not_not.mpr h1), ite_self, ite_eq_right hm]
      · have heqv : mkrMissPred res u σ ↔ mkrMissPred res (u + 1) σ := by
          simp only [mkrMissPred, Finset.mem_Icc]
          refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ h w ⟨hw.1, by omega⟩⟩
          by_cases hwu : w = u + 1
          · subst hwu; exact h1
          · exact h w ⟨hw.1, by omega⟩
        by_cases h2 : mkrMissPred res u σ
        · rw [ite_eq_left h2, ite_eq_left h1, ite_eq_left (heqv.mp h2)]
        · rw [ite_eq_right h2, ite_eq_right (mt heqv.mpr h2)]
    have hhit_eq (w : ℕ) (hw : w ∈ Finset.Icc 1 u) :
        Γ'.restrict (mkrHitPred res w) = Γ.restrict (mkrHitPred res w) := by
      apply Subtype.ext; funext σ; simp only [Γ', CQState.restrict_coe]
      by_cases hw_p : mkrHitPred res w σ
      · have hne : ¬ mkrHitPred res (u + 1) σ := by
          rcases Finset.mem_Icc.mp hw with ⟨_, hwu⟩; dsimp only [mkrHitPred] at hw_p ⊢; omega
        rw [ite_eq_left hw_p, ite_eq_left hne, ite_eq_left hw_p]
      · rw [ite_eq_right hw_p, ite_eq_right hw_p]
    have hexp_ih := ih Γ'
    rw [hmiss_eq, Finset.sum_congr rfl fun w hw ↦ by rw [hhit_eq w hw]] at hexp_ih
    dsimp only [mkrDispHits, compile]
    rw [← wp_expectation_eq, wp_qIf, expect_ite_partition, wp_expectation_eq, wp_expectation_eq]
    change 𝔼[(interp ((onHit (u + 1)).compile qAssign oracle)).toStateFun
        (Γ.restrict (mkrHitPred res (u + 1))), Θ] +
      𝔼[(interp ((mkrDispHits res onHit onZero u).compile qAssign oracle)).toStateFun Γ', Θ] = _
    rw [hexp_ih, Finset.sum_Icc_succ_top (by omega)]; ring
private lemma rms_expectedCost_measure_highBlock {Var : Type} [DecidableEq Var] (res : Var) {n M k
  m : ℕ} (S : Finset (Fin (2 ^ n))) (Γ : CQState (Store Var) (2 ^ (M * (n + 1) + k * n))) :
    expectedCost
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (measureRegister res (highBlock (M
  * (n + 1)) (k * n))) Γ = 0 := by
  let model := CostModel.ofEmbeddedOracle (n := M * (n + 1) + k * n)
    (groverParallelMarkingOracle m S)
  have hm_cb : CostBound (Var := Var) model
      (measureRegister res (highBlock (M * (n + 1)) (k * n))) 0 := by
    simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) model res _
  exact nonpos_iff_eq_zero.mp (by simpa using hm_cb Γ)
private noncomputable def rmsStageFuel {Var : Type} (res : Var) (n m k L_max L_end : ℕ) (hL1 : 1 ≤
  L_max) (hL_le : L_end ≤ L_max) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200
  ≤ n) (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) (L₀ : ℕ) (ops₀ : List (MuxSymOp (2 ^ n)
  (L₀ * m))) (segs : List (RampMuxSeg (2 ^ n) m)) (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀
  segs = L_end) (s : ℕ) (solveNext : (w : ℕ) → 1 ≤ w → OracleCirc Var ((L_max * m) * (n + 1) + k *
  n) ((n + 1) * m)) : ℕ → OracleCirc Var ((L_max * m) * (n + 1) + k * n) ((n + 1) * m)
  | 0 => .seq (mkrLiftEigLockStagesFrom res n m k L_max hL1 hm_grid hk_grid hn200 s)
      (.measure res (highBlock ((L_max * m) * (n + 1)) (k * n)))
  | fuel + 1 => .seq
      (mkrLiftCirc (mkrSubRegL n m k L_max L_end hL_le)
        (rmsPassFront res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd))
      (mkrDispHits res (fun w ↦ if hw : 1 ≤ w then solveNext w hw else .skip)
        (rmsStageFuel res n m k L_max L_end hL1 hL_le hm_grid hk_grid hn200 hm_pos h2Le
          L₀ ops₀ segs hmono hEnd s solveNext fuel)
        (min (L_end * m) (k - s)))
private lemma expect_rmsStageFuel_eq_trace {Var : Type} [DecidableEq Var] {n m k L_max L_end s : ℕ}
  (res : Var) (hL1 : 1 ≤ L_max) (hL_le : L_end ≤ L_max) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈
  groverGrid) (hn200 : 200 ≤ n) (hm_pos : 0 < m) (h2Le : 2 * (L_end * m) ≤ 2 ^ n) (hs : s ≤ k) (L₀
  : ℕ) (ops₀ : List (MuxSymOp (2 ^ n) (L₀ * m))) (segs : List (RampMuxSeg (2 ^ n) m)) (hmono :
  rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end) {S : Finset (Fin (2 ^ n))} (hcard : S.card
  = k) (solveNext : (w : ℕ) → 1 ≤ w → OracleCirc Var ((L_max * m) * (n + 1) + k * n) ((n + 1) * m))
  (hnext : ∀ w (hw1 : 1 ≤ w), w ≤ min (L_end * m) (k - s) → ∀ Γ : CQState (Store Var) (2 ^ ((L_max *
    m) *
  (n + 1) + k * n)), 𝔼[Γ, validObs n (L_max * m) k S (s + w)] = Γ.trace → 𝔼[(interp ((solveNext w
  hw1).compile qAssign (groverParallelMarkingOracle m S))).toStateFun Γ, liftPureProp (fun τ ↦
  decodeTargets n k (τ res) = S)] = Γ.trace) : ∀ (fuel : ℕ) (Δ : CQState (Store Var) (2 ^ ((L_max *
    m) * (n
  + 1) + k * n))), 𝔼[Δ, validObs n (L_max * m) k S s] = Δ.trace → 𝔼[(interp ((rmsStageFuel res n m
  k L_max L_end hL1 hL_le hm_grid hk_grid hn200 hm_pos h2Le L₀ ops₀ segs hmono hEnd s solveNext
  fuel).compile qAssign (groverParallelMarkingOracle m S))).toStateFun Δ, liftPureProp (fun τ ↦
  decodeTargets n k (τ res) = S)] = Δ.trace
  | 0, Δ, hV => by
    unfold rmsStageFuel; dsimp only [compile]; refine rms_expect_of_wp hV ?_; rw [wp_qSeq]
    exact (wp_mkrLiftEigLockStagesFrom_ge res hL1 hm_grid hk_grid hn200 hcard (k - s) s rfl
      hs).trans (wp_mono _ (validObs_le_wp_measure_decodeTargets res hcard))
  | fuel + 1, Δ, hV => by
    let oracle := groverParallelMarkingOracle m S
    let post := liftPureProp (d := 2 ^ ((L_max * m) * (n + 1) + k * n))
      (fun τ : Store Var ↦ decodeTargets n k (τ res) = S)
    let b := min (L_end * m) (k - s); let rL := mkrSubRegL n m k L_max L_end hL_le
    let P_fr := (mkrLiftCirc rL
      (rmsPassFront (Var := Var) res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd)).compile
      qAssign oracle
    have hdisp_wp : validObs (Var := Var) n (L_max * m) k S s ≤
        wp P_fr (mkrDispPre res n (L_max * m) k S s b) := by
      dsimp only [P_fr, rL, b]
      rw [← mkrEmbedAssn_validObs (Var := Var) (mkrPadEq n m L_max L_end hL_le) S s,
        ← mkrEmbedAssn_dispPre res (mkrPadEq n m L_max L_end hL_le) S s (min (L_end * m) (k - s)),
        wp_mkrLiftCirc]
      exact mkrEmbedAssn_mono _
        (wp_rmsPassFront_dispPre res hm_pos h2Le hs ops₀ segs hmono hEnd hcard)
    let Δ₁ := (interp P_fr).toStateFun Δ
    have htr_eq : Δ₁.trace = Δ.trace := by
      have h1 : (Δ.trace : ℝ) ≤ 𝔼[Δ₁, mkrDispPre res n (L_max * m) k S s b] := by
        rw [← hV, ← wp_expectation_eq]; exact expect_mono le_rfl hdisp_wp
      have h2 : 𝔼[Δ₁, mkrDispPre res n (L_max * m) k S s b] ≤ (Δ₁.trace : ℝ) := by
        rw [← expect_top Δ₁]; exact expect_mono le_rfl le_top
      have h3 := NNReal.coe_le_coe.mpr ((interp P_fr).trace_toStateFun_le Δ)
      exact NNReal.coe_inj.mp (by linarith)
    have hdisp_tr : 𝔼[Δ₁, mkrDispPre res n (L_max * m) k S s b] = Δ₁.trace :=
      (rms_expect_of_wp hV hdisp_wp).trans (congrArg NNReal.toReal htr_eq.symm)
    have hbr := mkrExpect_restrict_valid_branches res hdisp_tr
    let onHit := fun w ↦ if hw : 1 ≤ w then solveNext w hw else .skip
    let onZero := rmsStageFuel res n m k L_max L_end hL1 hL_le hm_grid hk_grid hn200 hm_pos
      h2Le L₀ ops₀ segs hmono hEnd s solveNext fuel
    have hpart := (mkrDispHits_trace_and_cost res oracle
      (CostModel.ofEmbeddedOracle oracle) onHit onZero b Δ₁).1
    unfold rmsStageFuel
    change 𝔼[(interp (.qSeq P_fr ((mkrDispHits res onHit onZero b).compile qAssign
      oracle))).toStateFun Δ, post] = Δ.trace
    rw [← wp_expectation_eq, wp_qSeq, wp_expectation_eq, wp_expectation_eq]
    change 𝔼[(interp ((mkrDispHits res onHit onZero b).compile qAssign oracle)).toStateFun
      Δ₁, post] = Δ.trace
    rw [rms_expect_mkrDispHits res oracle onHit onZero post b Δ₁]
    have hz_eq := expect_rmsStageFuel_eq_trace res hL1 hL_le hm_grid hk_grid hn200 hm_pos h2Le
      hs L₀ ops₀ segs hmono hEnd hcard solveNext hnext fuel
      (Δ₁.restrict (mkrMissPred res b)) hbr.1
    have hh_eq (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
        𝔼[(interp ((onHit w).compile qAssign oracle)).toStateFun
          (Δ₁.restrict (mkrHitPred res w)), post] = (Δ₁.restrict (mkrHitPred res w)).trace := by
      rcases Finset.mem_Icc.mp hw with ⟨hw1, hwb⟩
      dsimp only [onHit]; rw [dite_eq_left hw1]; exact hnext w hw1 hwb _ (hbr.2 w hw)
    rw [hz_eq, Finset.sum_congr rfl hh_eq, ← NNReal.coe_sum, ← NNReal.coe_add, hpart, htr_eq]
private lemma expectedCost_rmsStageFuel_le {Var : Type} [DecidableEq Var] {n m k L_max s : ℕ} (res
  : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (spec :
  JohnsonRampMuxSparseWalkSpec m k L_max) (hn0 : spec.n0 ≤ n) (hs : s < k) (hr2 : 2 ≤ k - s) (hwk :
  spec.useWalk (k - s) = true) (hm_pos : 0 < m) (h2Le : 2 * (spec.lEnd (k - s) * m) ≤ 2 ^ n) {S :
  Finset (Fin (2 ^ n))} (hcard : S.card = k) (solveNext : (w : ℕ) → 1 ≤ w → OracleCirc Var ((L_max
  * m) * (n + 1) + k * n) ((n + 1) * m)) (hnext_cost : ∀ w (hw1 : 1 ≤ w), w ≤ min (spec.lEnd (k -
  s) * m) (k - s) → ∀ Γ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n)), 𝔼[Γ, validObs n
    (L_max
  * m) k S (s + w)] = Γ.trace → expectedCost (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle m S)) ((solveNext w hw1).compile qAssign
  (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ * ENNReal.ofReal (spec.V (k - s - w) * √(2 ^ n
  : ℝ))) (hc_step : max 0 (spec.C_step + (spec.lEnd (k - s) : ℝ)) ≤ (rmsSlack spec (k - s) / 2) *
  √(2 ^ n : ℝ)) (Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n))) (hV : 𝔼[Δ, validObs
    n
  (L_max * m) k S s] = Δ.trace) : expectedCost (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle m S)) ((rmsStageFuel res n m k L_max (spec.lEnd (k - s))
  spec.hL_max_pos (spec.hlEnd_le (k - s) hr2 (by omega) hwk) hm_grid hk_grid hn200 hm_pos h2Le
  (spec.lInit (k - s)) (spec.ops0 n (k - s)) (spec.segsTail n (k - s)) (spec.hsegs_mono n (k - s)
  hn0 hr2 (by omega) hwk) (spec.hlEnd_eq n (k - s) hn0 hr2 (by omega) hwk) s solveNext (rmsAutoFuel
  spec (k - s))).compile qAssign (groverParallelMarkingOracle m S)) Δ ≤ stateMass Δ *
  ENNReal.ofReal (spec.V (k - s) * √(2 ^ n : ℝ)) := by
  let r := k - s; let L_end := spec.lEnd r
  let b := min (L_end * m) r; let c := ∑ w ∈ Finset.Icc 1 b, spec.pLo r w
  let slack := rmsSlack spec r; let S₀ := √(2 ^ n : ℝ); have hS₀_pos : 0 < S₀ := by positivity
  let oracle := groverParallelMarkingOracle m S
  have hor := isRealMatrix_groverParallelMarkingOracle m S; let Q := (L_max * m) * (n + 1) + k * n
  let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle oracle
  have hrk : r ≤ k := Nat.sub_le k s; have hL_le : L_end ≤ L_max := spec.hlEnd_le r hr2 hrk hwk
  let L₀ := spec.lInit r; let ops₀ := spec.ops0 n r
  let segs := spec.segsTail n r; have hmono := spec.hsegs_mono n r hn0 hr2 hrk hwk
  have hEnd := spec.hlEnd_eq n r hn0 hr2 hrk hwk; let rL := mkrSubRegL n m k L_max L_end hL_le
  let stCirc := rmsStageFuel res n m k L_max L_end spec.hL_max_pos hL_le hm_grid hk_grid hn200
    hm_pos h2Le L₀ ops₀ segs hmono hEnd s solveNext
  have hp_le1 := rms_pLo_sum_le_one hk_grid spec hr2 hrk hwk; have hc_le1 : c ≤ 1 := hp_le1.1
  have hq0 : 0 ≤ 1 - c := by linarith
  have hstep : ∀ {fuel : ℕ} {E_f : ℝ}, 0 ≤ E_f →
      (∀ Γ : CQState (Store Var) (2 ^ Q), 𝔼[Γ, validObs n (L_max * m) k S s] = Γ.trace →
        expectedCost model ((stCirc fuel).compile qAssign oracle) Γ ≤
          stateMass Γ * ENNReal.ofReal ((spec.V r + E_f) * S₀)) →
      ∀ Γ₀ : CQState (Store Var) (2 ^ Q), 𝔼[Γ₀, validObs n (L_max * m) k S s] = Γ₀.trace →
        expectedCost model ((stCirc (fuel + 1)).compile qAssign oracle) Γ₀ ≤
          stateMass Γ₀ * ENNReal.ofReal ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by
    intro fuel E_f hE0 hfuel_cost Γ₀ hV₀
    let passC := mkrLiftCirc rL
      (rmsPassFront (Var := Var) res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd)
    have hdisp_wp : validObs (Var := Var) n (L_max * m) k S s ≤
        wp (passC.compile qAssign oracle) (mkrDispPre res n (L_max * m) k S s b) := by
      rw [← mkrEmbedAssn_validObs (Var := Var) (mkrPadEq n m L_max L_end hL_le) S s,
        ← mkrEmbedAssn_dispPre res (mkrPadEq n m L_max L_end hL_le) S s b, wp_mkrLiftCirc]
      exact mkrEmbedAssn_mono _
        (wp_rmsPassFront_dispPre res hm_pos h2Le hs.le ops₀ segs hmono hEnd hcard)
    have hhit_wp (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
        scaledValidObs (Var := Var) n (L_max * m) k S s (spec.pLo r w)
            (spec.hpLo_nonneg r w) (hp_le1.2 w hw) ≤
          wp (passC.compile qAssign oracle) (liftPureProp (mkrHitPred res w)) := by
      rw [← mkrEmbedAssn_scaledValidObs (Var := Var) (mkrPadEq n m L_max L_end hL_le) S s
          (spec.pLo r w) (spec.hpLo_nonneg r w) (hp_le1.2 w hw),
        ← mkrEmbedAssn_liftPureProp rL (mkrHitPred res w), wp_mkrLiftCirc]
      exact mkrEmbedAssn_mono _ (wp_rmsPassFront_hitProb res hm_pos h2Le hs.le ops₀ segs hmono
        hEnd hcard (spec.hpLo_nonneg r w) (hp_le1.2 w hw)
        (fun R hR ↦ spec.hpLo_le n r hn0 hr2 hrk hwk R hR w hw))
    let qPass := rmsSegsQueryCount L₀ ops₀ segs + L_end
    have hfr_cb := costBound_mkrLiftCirc_of_staticOracleCalls (Var := Var) rL hor
      (rmsPassFront res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd) qPass
      (mkrStaticOracleCalls_rmsPassFront res n m k L_end s hm_pos h2Le L₀ ops₀ segs hmono hEnd) Γ₀
    dsimp only [stCirc]; unfold rmsStageFuel; dsimp only [compile]
    change expectedCost model ((passC.compile qAssign oracle).qSeq _) Γ₀ ≤ _
    generalize passC.compile qAssign oracle = P_fr at hdisp_wp hhit_wp hfr_cb ⊢
    let Δ₁ := (interp P_fr).toStateFun Γ₀
    have htr_le : (Δ₁.trace : ℝ) ≤ Γ₀.trace := by
      exact_mod_cast (interp P_fr).trace_toStateFun_le Γ₀
    have hdisp_tr : 𝔼[Δ₁, mkrDispPre res n (L_max * m) k S s b] = Δ₁.trace := by
      have h1 : (Γ₀.trace : ℝ) ≤ 𝔼[Δ₁, mkrDispPre res n (L_max * m) k S s b] := by
        rw [← hV₀, ← wp_expectation_eq]; exact expect_mono le_rfl hdisp_wp
      have h2 : 𝔼[Δ₁, mkrDispPre res n (L_max * m) k S s b] ≤ Δ₁.trace := by
        rw [← expect_top Δ₁]; exact expect_mono le_rfl le_top
      linarith
    have hbr_val := mkrExpect_restrict_valid_branches res hdisp_tr
    let Δ_miss := Δ₁.restrict (mkrMissPred res b)
    let Δ_hit := fun w ↦ Δ₁.restrict (mkrHitPred res w); let m₀ : ℝ := Δ_miss.trace
    let mw : ℕ → ℝ := fun w ↦ (Δ_hit w).trace
    have hp_mass (w : ℕ) (hw : w ∈ Finset.Icc 1 b) : spec.pLo r w * Γ₀.trace ≤ mw w := by
      calc spec.pLo r w * Γ₀.trace
          = 𝔼[Γ₀, scaledValidObs n (L_max * m) k S s (spec.pLo r w)
              (spec.hpLo_nonneg r w) (hp_le1.2 w hw)] := by
            rw [expect_eq_mul_of_apply_eq_smul Γ₀ _
              (scaledValidObs_smul n (L_max * m) k S s _ _ _), hV₀]
        _ ≤ 𝔼[Γ₀, wp P_fr (liftPureProp (mkrHitPred res w))] := expect_mono le_rfl (hhit_wp w hw)
        _ = 𝔼[Δ₁, liftPureProp (mkrHitPred res w)] := wp_expectation_eq P_fr Γ₀ _
        _ = mw w := expect_liftPureProp (mkrHitPred res w) Δ₁
    let onHit := fun w ↦ if hw : 1 ≤ w then solveNext w hw else .skip; let onZero := stCirc fuel
    obtain ⟨htr_part, hcost_disp⟩ := mkrDispHits_trace_and_cost res oracle model onHit onZero b Δ₁
    rw [expectedCost_qSeq]
    change expectedCost model P_fr Γ₀ +
      expectedCost model ((mkrDispHits res onHit onZero b).compile qAssign oracle) Δ₁ ≤ _
    rw [hcost_disp]; have hL_pos : 1 ≤ L_end := spec.hlEnd_pos r hr2 hrk hwk
    have hfr_real : (qPass : ℝ) ≤ (spec.tauWeighted r + slack / 2) * S₀ := by
      have hlen := spec.hqcount_le n r hn0 hr2 hrk hwk
      have hc_le : spec.C_step + (L_end : ℝ) ≤ (slack / 2) * S₀ := (le_max_right 0 _).trans hc_step
      dsimp only [qPass]; push_cast; linarith
    have hfr_cost : expectedCost model P_fr Γ₀ ≤
        ENNReal.ofReal (Γ₀.trace * ((spec.tauWeighted r + slack / 2) * S₀)) := by
      calc expectedCost model P_fr Γ₀ ≤ stateMass Γ₀ * ((qPass : ℝ≥0) : ℝ≥0∞) := hfr_cb
        _ = ENNReal.ofReal Γ₀.trace * ENNReal.ofReal (qPass : ℝ) := by
            rw [stateMass_eq_ofReal_trace, ENNReal.coe_natCast, ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal Γ₀.trace * ENNReal.ofReal ((spec.tauWeighted r + slack / 2) * S₀) :=
            mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hfr_real) zero_le
        _ = ENNReal.ofReal (Γ₀.trace * ((spec.tauWeighted r + slack / 2) * S₀)) :=
            (ENNReal.ofReal_mul Γ₀.trace_nonneg).symm
    have hzero_cost : expectedCost model (onZero.compile qAssign oracle) Δ_miss ≤
        ENNReal.ofReal (m₀ * ((spec.V r + E_f) * S₀)) := by
      calc expectedCost model (onZero.compile qAssign oracle) Δ_miss
          ≤ stateMass Δ_miss * ENNReal.ofReal ((spec.V r + E_f) * S₀) := hfuel_cost _ hbr_val.1
        _ = ENNReal.ofReal (m₀ * ((spec.V r + E_f) * S₀)) := by
            rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_mul (CQState.trace_nonneg _)]
    have hhit_cost (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
        expectedCost model ((onHit w).compile qAssign oracle) (Δ_hit w) ≤
          ENNReal.ofReal (mw w * (spec.V (r - w) * S₀)) := by
      rcases Finset.mem_Icc.mp hw with ⟨hw1, hwb⟩; dsimp only [onHit]; rw [dite_eq_left hw1]
      calc expectedCost model ((solveNext w hw1).compile qAssign oracle) (Δ_hit w)
          ≤ stateMass (Δ_hit w) * ENNReal.ofReal (spec.V (r - w) * S₀) :=
            hnext_cost w hw1 hwb _ (hbr_val.2 w hw)
        _ = ENNReal.ofReal (mw w * (spec.V (r - w) * S₀)) := by
            rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_mul (CQState.trace_nonneg _)]
    have hsum_hit : (∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit w).compile qAssign oracle)
          (Δ_hit w)) ≤ ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀)) :=
      (Finset.sum_le_sum hhit_cost).trans_eq (ENNReal.ofReal_sum_of_nonneg fun w _ ↦
        mul_nonneg (CQState.trace_nonneg _)
          (mul_nonneg (spec.hV_nonneg (r - w) (by omega)) hS₀_pos.le)).symm
    have hfr_nn : 0 ≤ Γ₀.trace * ((spec.tauWeighted r + slack / 2) * S₀) := by
      have hpos : (0 : ℝ) < (qPass : ℕ) := by
        exact_mod_cast (show 0 < rmsSegsQueryCount L₀ ops₀ segs + L_end by omega)
      exact mul_nonneg Γ₀.trace_nonneg
        (mul_nonneg (nonneg_of_mul_nonneg_left (hpos.le.trans hfr_real) hS₀_pos) hS₀_pos.le)
    have hz_nn : 0 ≤ m₀ * ((spec.V r + E_f) * S₀) := mul_nonneg (CQState.trace_nonneg _)
        (mul_nonneg (add_nonneg (spec.hV_nonneg r hrk) hE0) hS₀_pos.le)
    have hs_nn : 0 ≤ ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀) :=
      Finset.sum_nonneg fun w _ ↦ mul_nonneg (CQState.trace_nonneg _)
        (mul_nonneg (spec.hV_nonneg (r - w) (by omega)) hS₀_pos.le)
    have halg : Γ₀.trace * ((spec.tauWeighted r + slack / 2) * S₀) +
        (m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀)) ≤
        Γ₀.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by
      let δ := fun w ↦ mw w - spec.pLo r w * Γ₀.trace
      have hm₀_nn : 0 ≤ m₀ := CQState.trace_nonneg _
      have hδ_nn (w : ℕ) (hw : w ∈ Finset.Icc 1 b) : 0 ≤ δ w := sub_nonneg.mpr (hp_mass w hw)
      have hsum_δ_nn : 0 ≤ ∑ w ∈ Finset.Icc 1 b, δ w := Finset.sum_nonneg hδ_nn
      have htr_part_r : m₀ + ∑ w ∈ Finset.Icc 1 b, mw w = Δ₁.trace := by
        dsimp only [m₀, mw, Δ_miss, Δ_hit]; rw [← NNReal.coe_sum, ← NNReal.coe_add, htr_part]
      have hm_tot : m₀ + ∑ w ∈ Finset.Icc 1 b, mw w ≤ Γ₀.trace := by linarith [htr_part_r, htr_le]
      have hsum_δ_eq : (∑ w ∈ Finset.Icc 1 b, δ w) =
          (∑ w ∈ Finset.Icc 1 b, mw w) - c * Γ₀.trace := by
        dsimp only [δ, c]; rw [Finset.sum_sub_distrib, Finset.sum_mul]
      have hrem_le : m₀ + ∑ w ∈ Finset.Icc 1 b, δ w ≤ (1 - c) * Γ₀.trace := by linarith
      have hm₀_le : m₀ ≤ (1 - c) * Γ₀.trace := by linarith
      have hvCap_nn : 0 ≤ spec.vCap r := by
        rw [← spec.hV0]; exact spec.hvCap_ge 0 r (Nat.zero_le r) hrk
      have hm₀_V : m₀ * spec.V r ≤ m₀ * spec.vCap r :=
        mul_le_mul_of_nonneg_left (spec.hvCap_ge r r le_rfl hrk) hm₀_nn
      have hδ_V : (∑ w ∈ Finset.Icc 1 b, δ w * spec.V (r - w)) ≤
          (∑ w ∈ Finset.Icc 1 b, δ w) * spec.vCap r := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun w hw ↦
          mul_le_mul_of_nonneg_left (spec.hvCap_ge (r - w) r (Nat.sub_le r w) hrk) (hδ_nn w hw)
      have hmw_decomp : (∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w)) =
          Γ₀.trace * (∑ w ∈ Finset.Icc 1 b, spec.pLo r w * spec.V (r - w)) +
            ∑ w ∈ Finset.Icc 1 b, δ w * spec.V (r - w) := by
        rw [show (∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w)) = ∑ w ∈ Finset.Icc 1 b,
            (Γ₀.trace * (spec.pLo r w * spec.V (r - w)) + δ w * spec.V (r - w)) from
          Finset.sum_congr rfl fun w _ ↦ by dsimp only [δ]; ring,
          Finset.sum_add_distrib, ← Finset.mul_sum]
      have hcap_tot : m₀ * spec.V r + ∑ w ∈ Finset.Icc 1 b, δ w * spec.V (r - w) ≤
          (1 - c) * Γ₀.trace * spec.vCap r := by
        calc m₀ * spec.V r + ∑ w ∈ Finset.Icc 1 b, δ w * spec.V (r - w)
            ≤ (m₀ + ∑ w ∈ Finset.Icc 1 b, δ w) * spec.vCap r := by linarith [hm₀_V, hδ_V]
          _ ≤ (1 - c) * Γ₀.trace * spec.vCap r := mul_le_mul_of_nonneg_right hrem_le hvCap_nn
      have hm₀_E : m₀ * E_f ≤ (1 - c) * Γ₀.trace * E_f := mul_le_mul_of_nonneg_right hm₀_le hE0
      have hsum_S0 : (∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀)) =
          (∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w)) * S₀ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      have hmid : Γ₀.trace * (spec.tauWeighted r + slack / 2) +
          (m₀ * (spec.V r + E_f) + ∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w)) ≤
          Γ₀.trace * (spec.V r - slack / 2 + (1 - c) * E_f) := by
        rw [hmw_decomp]; dsimp only [slack, rmsSlack, b, c, L_end] at hcap_tot ⊢; linarith
      rw [hsum_S0, show Γ₀.trace * ((spec.tauWeighted r + slack / 2) * S₀) +
          (m₀ * ((spec.V r + E_f) * S₀) + (∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w)) * S₀) =
        (Γ₀.trace * (spec.tauWeighted r + slack / 2) +
          (m₀ * (spec.V r + E_f) + ∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w))) * S₀ by ring,
        show Γ₀.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) =
          (Γ₀.trace * (spec.V r - slack / 2 + (1 - c) * E_f)) * S₀ by ring]
      exact mul_le_mul_of_nonneg_right hmid hS₀_pos.le
    calc expectedCost model P_fr Γ₀ + (expectedCost model (onZero.compile qAssign oracle) Δ_miss +
            ∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit w).compile qAssign oracle) (Δ_hit w))
        ≤ ENNReal.ofReal (Γ₀.trace * ((spec.tauWeighted r + slack / 2) * S₀)) +
            (ENNReal.ofReal (m₀ * ((spec.V r + E_f) * S₀)) +
              ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀))) :=
          add_le_add hfr_cost (add_le_add hzero_cost hsum_hit)
      _ = ENNReal.ofReal (Γ₀.trace * ((spec.tauWeighted r + slack / 2) * S₀) +
            (m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀))) :=
          by rw [← ENNReal.ofReal_add hz_nn hs_nn,
               ← ENNReal.ofReal_add hfr_nn (add_nonneg hz_nn hs_nn)]
      _ ≤ ENNReal.ofReal (Γ₀.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀)) :=
          ENNReal.ofReal_le_ofReal halg
      _ = stateMass Γ₀ * ENNReal.ofReal ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by
          rw [ENNReal.ofReal_mul Γ₀.trace_nonneg, ← stateMass_eq_ofReal_trace]
  have hind : ∀ f : ℕ, ∀ Γ : CQState (Store Var) (2 ^ Q), 𝔼[Γ, validObs n (L_max * m) k S s] =
    Γ.trace →
      expectedCost model ((stCirc f).compile qAssign oracle) Γ ≤
        stateMass Γ * ENNReal.ofReal ((spec.V r + (1 - c) ^ f * (2 * (k : ℝ))) * S₀) := by
    intro f; induction f with
    | zero =>
      intro Γ hΓ; dsimp only [stCirc]; unfold rmsStageFuel; dsimp only [compile]
      rw [expectedCost_qSeq, rms_expectedCost_measure_highBlock, add_zero]
      have h0 := expectedCost_mkrLiftEigLockStagesFrom_le res spec.hL_max_pos hm_grid hk_grid
        (spec.hn0.trans hn0) hcard r s rfl (by omega) Γ hΓ
      have hVr0 : 0 ≤ spec.V r := spec.hV_nonneg r hrk
      have hr_le_k : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
      have hlin : (2 * (r : ℝ)) * S₀ ≤ (spec.V r + (1 - c) ^ 0 * (2 * (k : ℝ))) * S₀ := by
        refine mul_le_mul_of_nonneg_right ?_ hS₀_pos.le; simp only [pow_zero, one_mul]; linarith
      exact h0.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hlin) zero_le)
    | succ f ih =>
      intro Γ hΓ
      have hEf0 : 0 ≤ (1 - c) ^ f * (2 * (k : ℝ)) := mul_nonneg (pow_nonneg hq0 f) (by positivity)
      have hslack : 0 < slack := sub_pos.mpr (spec.hdrift_ramp_lt r hr2 hrk hwk)
      have hle : (spec.V r - slack / 2 + (1 - c) * ((1 - c) ^ f * (2 * (k : ℝ)))) * S₀ ≤
          (spec.V r + (1 - c) ^ (f + 1) * (2 * (k : ℝ))) * S₀ := by
        refine mul_le_mul_of_nonneg_right ?_ hS₀_pos.le
        have hpow : (1 - c) * ((1 - c) ^ f * (2 * (k : ℝ))) =
            (1 - c) ^ (f + 1) * (2 * (k : ℝ)) := by ring
        linarith
      exact (hstep hEf0 ih Γ hΓ).trans
        (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle) zero_le)
  obtain ⟨F, hauto, hF_bound⟩ := rmsAutoFuel_spec hk_grid spec hr2 hrk hwk
  change (1 - c) ^ F * (2 * (k : ℝ)) ≤ slack / 2 at hF_bound
  change expectedCost model ((stCirc (rmsAutoFuel spec r)).compile qAssign oracle) Δ ≤ _
  rw [hauto]
  have hEF0 : 0 ≤ (1 - c) ^ F * (2 * (k : ℝ)) := mul_nonneg (pow_nonneg hq0 F) (by positivity)
  have hle_top : (spec.V r - slack / 2 + (1 - c) * ((1 - c) ^ F * (2 * (k : ℝ)))) * S₀ ≤
      spec.V r * S₀ := by
    refine mul_le_mul_of_nonneg_right ?_ hS₀_pos.le
    have hc_nn : 0 ≤ c := Finset.sum_nonneg fun w _ ↦ spec.hpLo_nonneg r w
    have hmul_le : (1 - c) * ((1 - c) ^ F * (2 * (k : ℝ))) ≤ 1 * ((1 - c) ^ F * (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right (sub_le_self 1 hc_nn) hEF0
    linarith
  exact (hstep hEF0 (hind F) Δ hV).trans
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle_top) zero_le)
/- ## 3. Multi-Stage Recursive Solver & Turnkey `GroverFindAll` Exports -/
private noncomputable def rmsSolveFrom {Var : Type} [DecidableEq Var] (res : Var) (n m k L_max : ℕ)
  (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonRampMuxSparseWalkSpec m k
  L_max) (hn0 : spec.n0 ≤ n) : (s : ℕ) → OracleCirc Var ((L_max * m) * (n + 1) + k * n) ((n + 1) *
  m)
  | s =>
      have hn600 : 600 ≤ n := spec.hn0.trans hn0
      have hn200 : 200 ≤ n := by omega
      if hs : s < k then
        if hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true then
          rmsStageFuel res n m k L_max (spec.lEnd (k - s)) spec.hL_max_pos
            (spec.hlEnd_le (k - s) hwalk.1 (by omega) hwalk.2) hm_grid hk_grid hn200
            (one_le_of_mem_groverGrid hm_grid)
            (rms_two_mul_le_two_pow (spec.hlEnd_le (k - s) hwalk.1 (by omega) hwalk.2)
              spec.hL_max_hi hn600)
            (spec.lInit (k - s)) (spec.ops0 n (k - s)) (spec.segsTail n (k - s))
            (spec.hsegs_mono n (k - s) hn0 hwalk.1 (by omega) hwalk.2)
            (spec.hlEnd_eq n (k - s) hn0 hwalk.1 (by omega) hwalk.2) s
            (fun w _hw ↦ rmsSolveFrom res n m k L_max hm_grid hk_grid spec hn0 (s + w))
            (rmsAutoFuel spec (k - s))
        else (if hcold : k - s = 2 ∧ spec.useColdR2 = true then
          GroverFindAll.MuxColdTail.muxColdValidObsR2Circuit res n m L_max k
            (rmsGroverGrid_eq ▸ hm_grid) (rmsGroverGrid_eq ▸ hk_grid)
            (spec.hColdM2 hcold.2) (spec.hColdL2 hcold.2) (by omega)
        else
          .seq (mkrLiftEigLockStage res n m k L_max spec.hL_max_pos hm_grid hk_grid hn200 ⟨s, hs⟩)
            (rmsSolveFrom res n m k L_max hm_grid hk_grid spec hn0 (s + 1)))
      else .measure res (highBlock ((L_max * m) * (n + 1)) (k * n))
termination_by s => k - s
decreasing_by all_goals omega
private lemma expect_rmsSolveFrom_eq_trace {Var : Type} [DecidableEq Var] {n m k L_max : ℕ} (res :
  Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonRampMuxSparseWalkSpec m
  k L_max) (hn0 : spec.n0 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) : ∀ B s : ℕ, k - s ≤
  B → s ≤ k → ∀ Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n)), 𝔼[Δ, validObs n
    (L_max * m)
  k S s] = Δ.trace → 𝔼[(interp ((rmsSolveFrom res n m k L_max hm_grid hk_grid spec hn0 s).compile
  qAssign (groverParallelMarkingOracle m S))).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargets n k
  (τ res) = S)] = Δ.trace
  | B, s, hB, hs_le, Δ, hV => by
    by_cases hs : s < k
    · cases B with
      | zero => exact absurd hs (by omega)
      | succ B =>
        have hn600 : 600 ≤ n := spec.hn0.trans hn0; have hn200 : 200 ≤ n := by omega
        rw [rmsSolveFrom, dite_eq_left hs]
        by_cases hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true
        · rw [dite_eq_left hwalk]
          exact expect_rmsStageFuel_eq_trace res spec.hL_max_pos
            (spec.hlEnd_le (k - s) hwalk.1 (by omega) hwalk.2) hm_grid hk_grid hn200
            (one_le_of_mem_groverGrid hm_grid)
            (rms_two_mul_le_two_pow (spec.hlEnd_le (k - s) hwalk.1 (by omega) hwalk.2)
              spec.hL_max_hi hn600) hs_le (spec.lInit (k - s)) (spec.ops0 n (k - s))
            (spec.segsTail n (k - s)) (spec.hsegs_mono n (k - s) hn0 hwalk.1 (by omega) hwalk.2)
            (spec.hlEnd_eq n (k - s) hn0 hwalk.1 (by omega) hwalk.2) hcard _
            (fun w _hw1 _hwb Γ hΓ ↦ expect_rmsSolveFrom_eq_trace res hm_grid hk_grid spec hn0
              hcard B (s + w) (by omega) (by omega) Γ hΓ)
            (rmsAutoFuel spec (k - s)) Δ hV
        · rw [dite_eq_right hwalk]
          by_cases hcold : k - s = 2 ∧ spec.useColdR2 = true
          · rw [dite_eq_left hcold]; rw [show s = k - 2 by omega] at hV
            exact rmsMuxColdValidObsR2_correct res hn600 (rmsGroverGrid_eq ▸ hm_grid)
              (rmsGroverGrid_eq ▸ hk_grid) (spec.hColdM2 hcold.2) (spec.hColdL2 hcold.2)
              (by omega) hcard hV
          · rw [dite_eq_right hcold]; dsimp only [compile]
            rw [← wp_expectation_eq, wp_qSeq, wp_expectation_eq, wp_expectation_eq]
            let stageP := (mkrLiftEigLockStage (Var := Var) res n m k L_max spec.hL_max_pos hm_grid
              hk_grid hn200 ⟨s, hs⟩).compile qAssign (groverParallelMarkingOracle m S)
            have hwp_st := wp_mkrLiftEigLockStage_ge (Var := Var) res spec.hL_max_pos hm_grid
              hk_grid hn200 hcard ⟨s, hs⟩
            have hstep_V := mkrValidState_step hV hwp_st
            have hih := expect_rmsSolveFrom_eq_trace res hm_grid hk_grid spec hn0 hcard B (s + 1)
              (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
            have htr_st : (((interp stageP).toStateFun Δ).trace : ℝ) = Δ.trace := by
              have h1 : (Δ.trace : ℝ) ≤ 𝔼[(interp stageP).toStateFun Δ,
                  validObs n (L_max * m) k S (s + 1)] := by
                rw [← hV, ← wp_expectation_eq]; exact expect_mono le_rfl hwp_st
              have h2 := NNReal.coe_le_coe.mpr ((interp stageP).trace_toStateFun_le Δ)
              linarith [h2, hstep_V.1]
            exact hih.trans htr_st
    · obtain rfl : s = k := by omega
      rw [rmsSolveFrom, dite_eq_right (lt_irrefl s)]
      exact rms_expect_of_wp hV (validObs_le_wp_measure_decodeTargets res hcard)
private lemma rms_le_maxUpTo (f : ℕ → ℝ) {r K : ℕ} (hr : r ≤ K) : f r ≤ rmsMaxUpTo f K := by
  induction K with
  | zero => rw [Nat.le_zero.mp hr]; exact le_max_right 0 (f 0)
  | succ K ih =>
    by_cases hlt : r ≤ K
    · exact (ih hlt).trans (le_max_left _ _)
    · rw [show r = K + 1 by omega]; exact le_max_right _ _
private lemma expectedCost_rmsSolveFrom_le {Var : Type} [DecidableEq Var] {n m k L_max : ℕ} (res :
  Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonRampMuxSparseWalkSpec m
  k L_max) (hn0 : spec.n0 ≤ n) (hreq : ∀ r : ℕ, 1 ≤ r → r ≤ k → rmsStageReqC spec r ≤ √(2 ^ n : ℝ))
  {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (hcold_cost : ∀ (hc2 : spec.useColdR2 = true)
  (hk2 : 2 ≤ k) (Γ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n))), 𝔼[Γ, validObs n
    (L_max *
  m) k S (k - 2)] = Γ.trace → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle
  m S)) ((GroverFindAll.MuxColdTail.muxColdValidObsR2Circuit res n m L_max k (rmsGroverGrid_eq ▸
  hm_grid) (rmsGroverGrid_eq ▸ hk_grid) (spec.hColdM2 hc2) (spec.hColdL2 hc2) hk2).compile qAssign
  (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ * ENNReal.ofReal (spec.V 2 * √(2 ^ n : ℝ))) :
  ∀ B s : ℕ, k - s ≤ B → s ≤ k → ∀ Δ : CQState (Store Var) (2 ^ ((L_max * m) * (n + 1) + k * n)),
    𝔼[Δ,
  validObs n (L_max * m) k S s] = Δ.trace → expectedCost (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle m S)) ((rmsSolveFrom res n m k L_max hm_grid hk_grid spec hn0
  s).compile qAssign (groverParallelMarkingOracle m S)) Δ ≤ stateMass Δ * ENNReal.ofReal (spec.V (k
  - s) * √(2 ^ n : ℝ))
  | B, s, hB, hs_le, Δ, hV => by
    by_cases hs : s < k
    · cases B with
      | zero => exact absurd hs (by omega)
      | succ B =>
        have hn600 : 600 ≤ n := spec.hn0.trans hn0; have hn200 : 200 ≤ n := by omega
        rw [rmsSolveFrom, dite_eq_left hs]; let r := k - s
        by_cases hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true
        · rw [dite_eq_left hwalk]; have hr_req := hreq r (by omega) (by omega)
          rw [rmsStageReqC, dite_eq_left (⟨hwalk.1, by omega, hwalk.2⟩ :
            2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true)] at hr_req
          have hsl_pos : 0 < rmsSlack spec r / 2 :=
            half_pos (sub_pos.mpr (spec.hdrift_ramp_lt r hwalk.1 (by omega) hwalk.2))
          exact expectedCost_rmsStageFuel_le res hm_grid hk_grid hn200 spec hn0 hs hwalk.1 hwalk.2
            (one_le_of_mem_groverGrid hm_grid)
            (rms_two_mul_le_two_pow (spec.hlEnd_le (k - s) hwalk.1 (by omega) hwalk.2)
              spec.hL_max_hi hn600) hcard _
            (fun w _hw1 _hwb Γ hΓ ↦ by
              have hih := expectedCost_rmsSolveFrom_le res hm_grid hk_grid spec hn0 hreq hcard
                hcold_cost B (s + w) (by omega) (by omega) Γ hΓ
              rwa [show k - (s + w) = k - s - w by omega] at hih)
            (((div_le_iff₀ hsl_pos).mp hr_req).trans_eq (mul_comm _ _)) Δ hV
        · rw [dite_eq_right hwalk]
          by_cases hcold : k - s = 2 ∧ spec.useColdR2 = true
          · rw [dite_eq_left hcold]; rw [show s = k - 2 by omega] at hV; rw [hcold.1]
            exact hcold_cost hcold.2 (by omega) Δ hV
          · rw [dite_eq_right hcold]; dsimp only [compile]; rw [expectedCost_qSeq]
            let stageP := (mkrLiftEigLockStage (Var := Var) res n m k L_max spec.hL_max_pos hm_grid
              hk_grid hn200 ⟨s, hs⟩).compile qAssign (groverParallelMarkingOracle m S)
            have hwp_st := wp_mkrLiftEigLockStage_ge (Var := Var) res spec.hL_max_pos hm_grid
              hk_grid hn200 hcard ⟨s, hs⟩
            have hstep_V := mkrValidState_step hV hwp_st
            have hcost_st := expectedCost_mkrLiftEigLockStage_le res spec.hL_max_pos hm_grid
              hk_grid hn200 hcard ⟨s, hs⟩ hV
            have hih := expectedCost_rmsSolveFrom_le res hm_grid hk_grid spec hn0 hreq hcard
              hcold_cost B (s + 1) (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
            rw [hstep_V.2, show k - (s + 1) = r - 1 by omega] at hih
            have hlin := mkrStageCostReal_le_linear_S0 (k := k) (r := r) hn600 hm_grid hk_grid
              (by omega) (by omega)
            have hor : r = 1 ∨ (spec.useWalk r = false ∧ ¬ (r = 2 ∧ spec.useColdR2 = true)) := by
              by_cases hr2 : 2 ≤ r
              · right; refine ⟨?_, fun hc ↦ hcold hc⟩
                cases hu : spec.useWalk r
                · rfl
                · exact False.elim (hwalk ⟨hr2, hu⟩)
              · left; omega
            have heig_lt := spec.hV_eig r (by omega) (by omega) hor
            have hr_req := hreq r (by omega) (by omega)
            rw [rmsStageReqC,
              dite_eq_right (fun h : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true ↦ hwalk ⟨h.1, h.2.2⟩),
              dite_eq_right (fun h : r = 2 ∧ r ≤ k ∧ spec.useColdR2 = true ↦ hcold ⟨h.1, h.2.2⟩),
              dite_eq_left (⟨by omega, by omega⟩ : 1 ≤ r ∧ r ≤ k)] at hr_req
            have h5_le := (div_le_iff₀ (sub_pos.mpr heig_lt)).mp hr_req
            have hst_le : stageCostReal n m r ≤ (spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ) := by
              have hlin2 := hlin.2
              rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n),
                show (π / 8 + 1 / 4) * (√(2 ^ n : ℝ) / √((m : ℝ) * (r : ℝ))) =
                  ((π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ))) * √(2 ^ n : ℝ) by ring] at hlin2
              linarith
            have hd_nn : 0 ≤ (spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ) := mul_nonneg
              (le_trans (div_nonneg (by linarith [Real.pi_pos]) (Real.sqrt_nonneg _)) heig_lt.le)
              (Real.sqrt_nonneg _)
            have hcont_nn : 0 ≤ spec.V (r - 1) * √(2 ^ n : ℝ) :=
              mul_nonneg (spec.hV_nonneg (r - 1) (by omega)) (Real.sqrt_nonneg _)
            calc expectedCost _ stageP Δ + expectedCost _ _ ((interp stageP).toStateFun Δ)
                ≤ stateMass Δ * ENNReal.ofReal ((spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ)) +
                    stateMass Δ * ENNReal.ofReal (spec.V (r - 1) * √(2 ^ n : ℝ)) :=
                  add_le_add (hcost_st.trans
                    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hst_le) zero_le)) hih
              _ = stateMass Δ * (ENNReal.ofReal ((spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ)) +
                    ENNReal.ofReal (spec.V (r - 1) * √(2 ^ n : ℝ))) := by ring
              _ = stateMass Δ * ENNReal.ofReal (spec.V r * √(2 ^ n : ℝ)) := by
                  congr 1; rw [← ENNReal.ofReal_add hd_nn hcont_nn]; congr 1; ring
    · obtain rfl : s = k := by omega
      rw [rmsSolveFrom, dite_eq_right (lt_irrefl s)]; dsimp only [compile]
      rw [rms_expectedCost_measure_highBlock, Nat.sub_self, spec.hV0, zero_mul, ENNReal.ofReal_zero,
        mul_zero]
/-- Turnkey parallel query-model circuit executing `JohnsonRampMuxSparseWalkSpec` for
  `spec.n0 ≤ n` and delegating to lifted `Stage1.circuit` for `n < spec.n0`. -/
noncomputable def johnsonRampMuxSparseCircuit {Var : Type} [DecidableEq Var] (res : Var) {m k L_max
  : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonRampMuxSparseWalkSpec m
  k L_max) (n : ℕ) : OracleCirc Var (Stage1.qubits n (L_max * m) k) ((n + 1) * m) :=
  if hn0 : spec.n0 ≤ n then rmsSolveFrom res n m k L_max hm_grid hk_grid spec hn0 0
  else mkrLiftCirc (mkrSubReg1 n m k L_max spec.hL_max_pos) (Stage1.circuit res n m k)
/-- Exact probability-`1` correctness of `johnsonRampMuxSparseCircuit` on `groverTargetSets
  n k`. -/
theorem johnsonRampMuxSparseCircuit_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k
  L_max : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec :
  JohnsonRampMuxSparseWalkSpec m k L_max) (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))}
  (hS : S ∈ groverTargetSets n k) : ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n (L_max * m)
    k)) ⦄
  (qset ;; (johnsonRampMuxSparseCircuit res hm_grid hk_grid spec n).compile qAssign
  (groverParallelMarkingOracle m S)) ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ := by
  by_cases hn0 : spec.n0 ≤ n
  · have hcirc_eq : johnsonRampMuxSparseCircuit (Var := Var) res hm_grid hk_grid spec n =
        rmsSolveFrom res n m k L_max hm_grid hk_grid spec hn0 0 := by
      unfold johnsonRampMuxSparseCircuit; exact dite_eq_left hn0
    rw [hcirc_eq]; unfold Stage1.qubits; intro state
    rw [expect_top, ← wp_expectation_eq, wp_qSeq, wp_expectation_eq, wp_expectation_eq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ ((L_max * m) * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n (L_max * m) k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]; rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
      exact congrArg NNReal.toReal (CQState.trace_qSet state).symm
    rw [expect_rmsSolveFrom_eq_trace res hm_grid hk_grid spec hn0 (Finset.mem_powersetCard.mp hS).2
      k 0 le_rfl (Nat.zero_le k) Δ₀ hV0]
    exact NNReal.coe_le_coe.mpr (CQState.trace_qSet state).symm.le
  · have hcirc_eq : johnsonRampMuxSparseCircuit (Var := Var) res hm_grid hk_grid spec n =
        mkrLiftCirc (mkrSubReg1 n m k L_max spec.hL_max_pos) (Stage1.circuit res n m k) := by
      unfold johnsonRampMuxSparseCircuit; exact dite_eq_right hn0
    rw [hcirc_eq]
    exact mkrTriple_liftCirc_qSet (mkrSubReg1 n m k L_max spec.hL_max_pos)
      (Stage1.circuit res n m k) (groverParallelMarkingOracle m S) _
      (Stage1.correctness res hn (by simp [Stage1.cells, gridCells, hm_grid, hk_grid]) hkN hS)
/-- Pointwise uniform-average parallel query cost bound for `johnsonRampMuxSparseCircuit` at
  any
  fixed `n ≥ spec.n0` satisfying `rmsStageReqC` and any optional `r = 2` cold-tail bound. -/
theorem johnsonRampMuxSparseCircuit_cost_of_req {Var : Type} [DecidableEq Var] (res : Var) {n m k
  L_max : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec :
  JohnsonRampMuxSparseWalkSpec m k L_max) {rel : ℝ} (hV_top : spec.V k ≤ rel * (π / 4) *
  groverHarmonicSqrtSum k / √(m : ℝ)) (hn0 : spec.n0 ≤ n) (hkN : k ≤ 2 ^ n) (hreq : ∀ r : ℕ, 1 ≤ r
  → r ≤ k → rmsStageReqC spec r ≤ √(2 ^ n : ℝ)) (hcold_cost : ∀ (hc2 : spec.useColdR2 = true) (hk2
  : 2 ≤ k) {S : Finset (Fin (2 ^ n))}, S.card = k → ∀ (Γ : CQState (Store Var) (2 ^ ((L_max * m) *
    (n + 1)
  + k * n))), 𝔼[Γ, validObs n (L_max * m) k S (k - 2)] = Γ.trace → expectedCost
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
  ((GroverFindAll.MuxColdTail.muxColdValidObsR2Circuit res n m L_max k (rmsGroverGrid_eq ▸ hm_grid)
  (rmsGroverGrid_eq ▸ hk_grid) (spec.hColdM2 hc2) (spec.hColdL2 hc2) hk2).compile qAssign
  (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ * ENNReal.ofReal (spec.V 2 * √(2 ^ n : ℝ))) :
  AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n (L_max * m) k) k (fun S ↦
  CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (fun S ↦ qset ;;
  (johnsonRampMuxSparseCircuit res hm_grid hk_grid spec n).compile qAssign
  (groverParallelMarkingOracle m S)) (rel * vanillaFindAllCost n m k) := by
  have hcirc_eq : johnsonRampMuxSparseCircuit (Var := Var) res hm_grid hk_grid spec n =
      rmsSolveFrom res n m k L_max hm_grid hk_grid spec hn0 0 := by
    unfold johnsonRampMuxSparseCircuit; exact dite_eq_left hn0
  let q_val : ℝ≥0 := Real.toNNReal (spec.V k * √(2 ^ n : ℝ))
  simp_rw [hcirc_eq]; unfold Stage1.qubits; refine ⟨fun _ ↦ q_val, fun S hS state ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    set model := CostModel.ofEmbeddedOracle (n := (L_max * m) * (n + 1) + k * n)
      (groverParallelMarkingOracle m S)
    rw [expectedCost_qSeq, expectedCost_qSet, show model.resetCost = 0 from rfl]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ ((L_max * m) * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n (L_max * m) k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]; rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
      exact congrArg NNReal.toReal (CQState.trace_qSet state).symm
    have hst := expectedCost_rmsSolveFrom_le res hm_grid hk_grid spec hn0 hreq hcard
      (fun hc2 hk2 Γ hΓ ↦ hcold_cost hc2 hk2 hcard Γ hΓ) k 0 le_rfl (Nat.zero_le k) Δ₀ hV0
    rwa [Nat.sub_zero, Lossless.qSet state] at hst
  · have hVk0 : 0 ≤ spec.V k * √(2 ^ n : ℝ) :=
      mul_nonneg (spec.hV_nonneg k le_rfl) (Real.sqrt_nonneg _)
    have hsum_le : (q_val : ℝ) ≤ rel * vanillaFindAllCost n m k := by
      calc (q_val : ℝ) = spec.V k * √(2 ^ n : ℝ) := Real.coe_toNNReal _ hVk0
        _ ≤ (rel * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ)) * √(2 ^ n : ℝ) :=
            mul_le_mul_of_nonneg_right hV_top (Real.sqrt_nonneg _)
        _ = rel * ((π / 4) * groverHarmonicSqrtSum k * (√(2 ^ n : ℝ) / √(m : ℝ))) := by ring
        _ = rel * vanillaFindAllCost n m k := by
            unfold vanillaFindAllCost; rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n)]
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      rw [show (groverTargetSets n k).card = Nat.choose (2 ^ n) k by simp [groverTargetSets]]
      exact_mod_cast Nat.choose_pos hkN
    rwa [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']
/-- Asymptotic uniform-average parallel query cost bound for `johnsonRampMuxSparseCircuit`
  (supporting both `useColdR2 = false` and `useColdR2 = true`). -/
theorem johnsonRampMuxSparseCircuit_rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k L_max
  : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonRampMuxSparseWalkSpec m
  k L_max) {rel : ℝ} (hV_top : spec.V k ≤ rel * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ)) : ∃
  n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n (L_max *
  m) k) k (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (fun S ↦ qset ;;
  (johnsonRampMuxSparseCircuit res hm_grid hk_grid spec n).compile qAssign
  (groverParallelMarkingOracle m S)) (rel * vanillaFindAllCost n m k) := by
  let M_req := rmsMaxUpTo (rmsStageReqC spec) k; let N_arch := Nat.ceil (M_req ^ 2)
  have hM_bound : ∀ {n : ℕ}, N_arch ≤ n → M_req ≤ √(2 ^ n : ℝ) := fun {n} hN ↦
    Real.le_sqrt_of_sq_le ((Nat.le_ceil (M_req ^ 2)).trans
      ((Nat.cast_le.mpr hN).trans (by exact_mod_cast n.lt_two_pow_self.le)))
  by_cases hcold2 : spec.useColdR2 = true ∧ 2 ≤ k
  · obtain ⟨hc2_eq, hk2⟩ := hcold2
    obtain ⟨n_cold, _, hcold_tr⟩ :=
      GroverFindAll.MuxColdTail.muxColdValidObsR2_transition (Var := Var) res (L_max := L_max)
        (rmsGroverGrid_eq ▸ hm_grid) (rmsGroverGrid_eq ▸ hk_grid)
        (spec.hColdM2 hc2_eq) (spec.hColdL2 hc2_eq) hk2
    refine ⟨max (max spec.n0 N_arch) n_cold, fun n hn hkN ↦ ?_⟩
    have hM_le := hM_bound (((le_max_right _ _).trans (le_max_left _ _)).trans hn)
    refine johnsonRampMuxSparseCircuit_cost_of_req res hm_grid hk_grid spec hV_top
      (((le_max_left _ _).trans (le_max_left _ _)).trans hn) hkN
      (fun r _ hrk ↦ (rms_le_maxUpTo (rmsStageReqC spec) hrk).trans hM_le)
      (fun hc2 hk2' {S} hcard Γ hΓ ↦ ?_)
    have hraw := (hcold_tr ((le_max_right _ _).trans hn) hcard hΓ).2
    have hprf : GroverFindAll.MuxColdTail.muxColdValidObsR2Circuit res n m L_max k
          (rmsGroverGrid_eq ▸ hm_grid) (rmsGroverGrid_eq ▸ hk_grid)
          (spec.hColdM2 hc2) (spec.hColdL2 hc2) hk2' =
        GroverFindAll.MuxColdTail.muxColdValidObsR2Circuit res n m L_max k
          (rmsGroverGrid_eq ▸ hm_grid) (rmsGroverGrid_eq ▸ hk_grid)
          (spec.hColdM2 hc2_eq) (spec.hColdL2 hc2_eq) hk2 := rfl
    rw [hprf, rmsOracle_eq_local]
    have hle_V2 : (((GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) *
          QuantumComputation.Specs.GroverSol.groverHarmonicSqrtSum 2 + 1 / 10 ^ 9) *
        ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ)))) ≤ spec.V 2 * √(2 ^ n : ℝ) := by
      rw [← rmsHarmonic_eq_sol 2, Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n)]
      have hrew : (((GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 +
            1 / 10 ^ 9) * ((π / 4) * (√(2 ^ n : ℝ) / √(m : ℝ)))) =
          (((GroverFindAll.MuxColdTail.muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 +
              1 / (10 : ℝ) ^ 9) * ((π / 4) / √(m : ℝ))) * √(2 ^ n : ℝ) := by ring
      rw [hrew]; exact mul_le_mul_of_nonneg_right (spec.hV_cold2 hc2_eq hk2) (Real.sqrt_nonneg _)
    exact hraw.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle_V2) zero_le)
  · refine ⟨max spec.n0 N_arch, fun n hn hkN ↦ ?_⟩
    have hM_le := hM_bound ((le_max_right _ _).trans hn)
    exact johnsonRampMuxSparseCircuit_cost_of_req res hm_grid hk_grid spec hV_top
      ((le_max_left _ _).trans hn) hkN
      (fun r _ hrk ↦ (rms_le_maxUpTo (rmsStageReqC spec) hrk).trans hM_le)
      (fun hc2 hk2 _ _ _ ↦ False.elim (hcold2 ⟨hc2, hk2⟩))
/-- Concrete `80000 ≤ n` uniform-average cost bound (choice-free threshold) whenever
  `spec.useColdR2 = false`, `spec.n0 ≤ 80000`, and `rmsStageReqC spec r ≤ 2 ^ 120`. -/
theorem johnsonRampMuxSparseCircuit_cost_ge_80000 {Var : Type} [DecidableEq Var] (res : Var) {n m k
  L_max : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec :
  JohnsonRampMuxSparseWalkSpec m k L_max) {rel : ℝ} (hV_top : spec.V k ≤ rel * (π / 4) *
  groverHarmonicSqrtSum k / √(m : ℝ)) (hnoCold : spec.useColdR2 = false) (hn0_80 : spec.n0 ≤ 80000)
  (hreq120 : ∀ r : ℕ, 1 ≤ r → r ≤ k → rmsStageReqC spec r ≤ (2 : ℝ) ^ 120) (hn : 80000 ≤ n) (hkN :
  k ≤ 2 ^ n) : AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n (L_max * m) k) k (fun S ↦
  CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (fun S ↦ qset ;;
  (johnsonRampMuxSparseCircuit res hm_grid hk_grid spec n).compile qAssign
  (groverParallelMarkingOracle m S)) (rel * vanillaFindAllCost n m k) := by
  have h120_le : (2 : ℝ) ^ 120 ≤ √(2 ^ n : ℝ) := Real.le_sqrt_of_sq_le <| by
    calc ((2 : ℝ) ^ 120) ^ 2 = (2 : ℝ) ^ 240 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  exact johnsonRampMuxSparseCircuit_cost_of_req res hm_grid hk_grid spec hV_top (hn0_80.trans hn)
    hkN (fun r hr1 hrk ↦ (hreq120 r hr1 hrk).trans h120_le)
    (fun hc2 _ _ _ _ ↦ Bool.noConfusion (hnoCold.symm.trans hc2))
end
end QuantumComputation.Specs.DickeSol

namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real QProg.Notation
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace
@[expose] public section
/-- Converts `RkmSeg` continuation segments into `RampMuxSeg` continuation segments. -/
def rkmToRmsSegs {N m : ℕ} : List (RkmSeg N m) → List (RampMuxSeg N m)
  | [] => []
  | s :: rest => ⟨s.lSeg, s.ops⟩ :: rkmToRmsSegs rest
end
public section
open Operator ResourceCounting Real QProg.Notation
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace
theorem rmsEndL_rkmToRmsSegs {N m : ℕ} : ∀ (segs : List (RkmSeg N m)) (L₀ : ℕ),
      rmsEndL L₀ (rkmToRmsSegs segs) = rkmEndL L₀ segs
  | [], _ => rfl
  | s :: rest, _ => rmsEndL_rkmToRmsSegs rest s.lSeg
theorem rmsSegsMono_rkmToRmsSegs {N m : ℕ} : ∀ (segs : List (RkmSeg N m)) (L₀ : ℕ),
      rmsSegsMono L₀ (rkmToRmsSegs segs) ↔ rkmSegsMono L₀ segs
  | [], _ => Iff.rfl
  | s :: rest, _ => and_congr_right fun _ ↦ rmsSegsMono_rkmToRmsSegs rest s.lSeg
theorem rmsSegsQueryCount_rkmToRmsSegs {N m : ℕ} :
    ∀ (segs : List (RkmSeg N m)) (L₀ : ℕ) (ops₀ : List (MuxSymOp N (L₀ * m))),
      rmsSegsQueryCount L₀ ops₀ (rkmToRmsSegs segs) = rkmSegsQueryCount L₀ ops₀ segs
  | [], _, _ => rfl
  | s :: rest, L₀, ops₀ =>
      congrArg (Nat.add (L₀ * muxOpsQueryCount ops₀))
        (rmsSegsQueryCount_rkmToRmsSegs rest s.lSeg s.ops)
theorem symHitProb_evalRampMuxSegs_rkmToRmsSegs {N m : ℕ} (R : Finset (Fin N)) (w : ℕ) :
    ∀ (segs : List (RkmSeg N m)) (L₀ : ℕ) (ops₀ : List (MuxSymOp N (L₀ * m)))
      (v : SymSubset N (L₀ * m) → ℝ),
      symHitProb R (evalRampMuxSegs R L₀ ops₀ (rkmToRmsSegs segs) v) w =
        symHitProb R (rkmEvalSegs R L₀ ops₀ segs v) w
  | [], _, _, _ => rfl
  | s :: rest, L₀, ops₀, v => by
    dsimp only [rkmToRmsSegs, evalRampMuxSegs, rkmEvalSegs]
    exact symHitProb_evalRampMuxSegs_rkmToRmsSegs R w rest s.lSeg s.ops _
private theorem rkmb2_ble_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkmb2_ble_true]
private theorem rkmb2_primBlt_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  unfold primNatBlt; rw [← Bool.not_eq_true, rkmb2_ble_true, Nat.add_eq]; omega
private theorem rkmb2_checkListLMax_iff (lMaxCell : ℕ) :
    ∀ xs : List ℕ, rkmCheckListLMax lMaxCell xs = true ↔ ∀ x ∈ xs, 1 ≤ x ∧ x ≤ lMaxCell
  | [] => by simp [rkmCheckListLMax]
  | x :: xs => by
    unfold rkmCheckListLMax
    cases hg : Bool.or (primNatBlt x 1) (primNatBlt lMaxCell x) with
    | true =>
      simp only [Bool.cond_true, Bool.false_eq_true, false_iff, List.mem_cons, not_forall]
      simp only [Bool.or_eq_true, primNatBlt, rkmb2_ble_true, Nat.add_eq] at hg
      exact ⟨x, Or.inl rfl, fun ⟨h1, h2⟩ ↦ by omega⟩
    | false =>
      simp only [Bool.cond_false, rkmb2_checkListLMax_iff lMaxCell xs, List.mem_cons]
      simp only [Bool.or_eq_false_iff, rkmb2_primBlt_false] at hg
      exact ⟨fun hall y hy ↦ hy.elim (fun h ↦ h ▸ hg) (hall y), fun hall y hy ↦ hall y (Or.inr hy)⟩
/-- Monotonicity of `rkmCheckAnchorsLMax` in `lMaxCell`. -/
theorem rkmCheckAnchorsLMax_mono {k l₁ l₂ : ℕ} (hle : l₁ ≤ l₂) : ∀ {anchors : List RampKickAnchor},
      rkmCheckAnchorsLMax k l₁ anchors = true → rkmCheckAnchorsLMax k l₂ anchors = true
  | [], _ => rfl
  | a :: rest, h => by
    unfold rkmCheckAnchorsLMax at h ⊢
    cases hble : Nat.ble a.rAct k with
    | false =>
      simp only [hble, Bool.cond_false, Bool.cond_true] at h ⊢
      exact rkmCheckAnchorsLMax_mono hle h
    | true =>
      simp only [hble, Bool.cond_true] at h ⊢
      cases hok : rkmCheckListLMax l₁ a.lSegs with
      | false => simp [hok] at h
      | true =>
        simp only [hok, Bool.cond_true] at h
        have hok2 : rkmCheckListLMax l₂ a.lSegs = true :=
          (rkmb2_checkListLMax_iff l₂ a.lSegs).mpr fun x hx ↦
            let ⟨hx1, hx2⟩ := (rkmb2_checkListLMax_iff l₁ a.lSegs).mp hok x hx
            ⟨hx1, hx2.trans hle⟩
        simp only [hok2, Bool.cond_true]; exact rkmCheckAnchorsLMax_mono hle h
private theorem rkmb2_findAnchor_mem {r : ℕ} :
    ∀ {anchors : List RampKickAnchor} {a : RampKickAnchor},
      rkmFindAnchor r anchors = some a → a ∈ anchors ∧ a.rAct = r
  | [], _, h => by simp [rkmFindAnchor] at h
  | b :: rest, a, h => by
    unfold rkmFindAnchor at h
    by_cases heq : b.rAct = r
    · rw [ite_eq_left heq] at h; cases Option.some.inj h; exact ⟨List.mem_cons_self, heq⟩
    · rw [ite_eq_right heq] at h; obtain ⟨hm, hr⟩ := rkmb2_findAnchor_mem h
      exact ⟨List.mem_cons_of_mem b hm, hr⟩
private theorem rkmb2_checkAnchorsLMax_mem {k lMaxCell : ℕ} :
    ∀ {anchors : List RampKickAnchor} {a : RampKickAnchor},
      rkmCheckAnchorsLMax k lMaxCell anchors = true →
      a ∈ anchors → a.rAct ≤ k → ∀ x ∈ a.lSegs, 1 ≤ x ∧ x ≤ lMaxCell
  | [], _, _, hm, _ => absurd hm List.not_mem_nil
  | b :: rest, a, h, hm, hrk => by
    unfold rkmCheckAnchorsLMax at h; dsimp only at h
    cases hok : (cond (Nat.ble b.rAct k) (rkmCheckListLMax lMaxCell b.lSegs) true) with
    | false => rw [hok] at h; cases h
    | true =>
      rw [hok, Bool.cond_true] at h
      rcases List.mem_cons.mp hm with rfl | hmem
      · rw [rkmb2_ble_true.mpr hrk, Bool.cond_true] at hok
        exact (rkmb2_checkListLMax_iff lMaxCell a.lSegs).mp hok
      · exact rkmb2_checkAnchorsLMax_mem h hmem hrk
private theorem rkmb2_lastNat_mem : ∀ (xs : List ℕ) (x : ℕ), rkmLastNat x xs ∈ x :: xs
  | [], _ => List.mem_cons_self
  | y :: ys, _ => List.mem_cons_of_mem _ (rkmb2_lastNat_mem ys y)
private theorem rkmb2_cond_fst_ne_zero {b : Bool} {x : ℕ × ℕ × List ℤ}
    (h : (cond b (0, 0, []) x).1 ≠ 0) : x.1 ≠ 0 := by cases b <;> simp_all
private theorem rkmb2_evalSegsLoop_lengths (m lTableMax r : ℕ) :
    ∀ (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool))
      (lPrev dEnd accPad : ℕ) (vec : List ℤ),
      (rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks lPrev dEnd accPad vec).1 ≠ 0 →
      lSegs.length = tauSegs.length ∧ lSegs.length = nsubSegs.length ∧ lSegs.length = masks.length
  | [], [], [], [], _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | [], [], _ :: _, _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | [], [], [], _ :: _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h => by simp [rkmEvalSegsLoop] at h
  | lS :: lRest, _ :: tauRest, _ :: nsubRest, _ :: maskRest, _, _, _, _, h => by
    unfold rkmEvalSegsLoop at h; dsimp only at h
    simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at h
    have hrec := rkmb2_cond_fst_ne_zero
      (rkmb2_cond_fst_ne_zero (rkmb2_cond_fst_ne_zero (rkmb2_cond_fst_ne_zero h)))
    obtain ⟨h1, h2, h3⟩ :=
      rkmb2_evalSegsLoop_lengths m lTableMax r lRest tauRest nsubRest maskRest lS _ _ _ hrec
    exact ⟨congrArg Nat.succ h1, congrArg Nat.succ h2, congrArg Nat.succ h3⟩
private theorem rkmb2_cond_ne_nil {α : Type} {b : Bool} {xs : List α}
    (h : cond b [] xs ≠ []) : b = false ∧ xs ≠ [] := by cases b <;> simp_all
private theorem rkmb2_evalT16Lo12_ne_nil_lengths {m lTableMax r : ℕ}
    {lSegs tauSegs nsubSegs : List ℕ} {masks : List (List Bool)}
    (hne : rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks ≠ []) :
    lSegs.length = tauSegs.length ∧ lSegs.length = nsubSegs.length ∧
      lSegs.length = masks.length := by
  unfold rkmEvalT16Lo12 at hne; dsimp only at hne
  obtain ⟨_, hne1⟩ := rkmb2_cond_ne_nil hne
  rcases hres : rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks
      1 0 0 [Int.ofNat wdScale] with ⟨dEnd, accPad, vecFinal⟩
  rw [hres] at hne1; dsimp only at hne1
  obtain ⟨hb, _⟩ := rkmb2_cond_ne_nil hne1
  have hd_ne : dEnd ≠ 0 := by
    intro hd0; subst hd0; rw [Bool.or_eq_false_iff] at hb; exact Bool.noConfusion hb.1
  exact rkmb2_evalSegsLoop_lengths m lTableMax r lSegs tauSegs nsubSegs masks
    1 0 0 [Int.ofNat wdScale] (by rw [hres]; exact hd_ne)
private theorem rkmb2_endL_buildTailSegs (n m r : ℕ) :
    ∀ (ls ts ss : List ℕ) (mks : List (List Bool)) (l0 : ℕ),
      ls.length = ts.length → ls.length = ss.length → ls.length = mks.length →
      rkmEndL l0 (rkmBuildTailSegs n m r ls ts ss mks) = rkmLastNat l0 ls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, _, h2, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h3 => by simp at h3
  | l1 :: ls, _ :: ts, _ :: ss, _ :: mks, _, h1, h2, h3 =>
      rkmb2_endL_buildTailSegs n m r ls ts ss mks l1
        (Nat.succ.inj h1) (Nat.succ.inj h2) (Nat.succ.inj h3)
private theorem rkmb2_segsMono_buildTailSegs (n m r lTableMax : ℕ) :
    ∀ (ls ts ss : List ℕ) (mks : List (List Bool)) (l0 : ℕ),
      rkmCheckSegBounds lTableMax ls ts l0 = true →
      rkmSegsMono l0 (rkmBuildTailSegs n m r ls ts ss mks)
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, h => by simp [rkmCheckSegBounds] at h
  | _ :: _, _ :: _, [], _, _, _ => by simp [rkmBuildTailSegs, rkmSegsMono]
  | _ :: _, _ :: _, _ :: _, [], _, _ => by simp [rkmBuildTailSegs, rkmSegsMono]
  | l1 :: ls, t1 :: ts, s1 :: ss, mk1 :: mks, l0, h => by
    unfold rkmCheckSegBounds at h
    cases hg : Bool.or (primNatBlt l1 1)
        (Bool.or (primNatBlt l1 l0)
        (Bool.or (primNatBlt lTableMax l1)
        (Bool.or (primNatBlt t1 1) (primNatBlt 4000000000 t1)))) with
    | true => simp [hg] at h
    | false =>
      simp only [hg, Bool.cond_false] at h
      simp only [Bool.or_eq_false_iff, rkmb2_primBlt_false] at hg
      exact ⟨hg.2.1, rkmb2_segsMono_buildTailSegs n m r lTableMax ls ts ss mks l1 h⟩
private theorem rkmb2_checkSegBounds_le (lTableMax : ℕ) : ∀ (ls ts : List ℕ) (lPrev : ℕ),
      rkmCheckSegBounds lTableMax ls ts lPrev = true → ∀ x ∈ ls, x ≤ lTableMax
  | [], [], _, _, _, hx => absurd hx List.not_mem_nil
  | [], _ :: _, _, h, _, _ => by simp [rkmCheckSegBounds] at h
  | _ :: _, [], _, h, _, _ => by simp [rkmCheckSegBounds] at h
  | lS :: lRest, tS :: tRest, lPrev, h, x, hx => by
    unfold rkmCheckSegBounds at h
    cases hg : Bool.or (primNatBlt lS 1)
        (Bool.or (primNatBlt lS lPrev)
        (Bool.or (primNatBlt lTableMax lS)
        (Bool.or (primNatBlt tS 1) (primNatBlt 4000000000 tS)))) with
    | true => simp [hg] at h
    | false =>
      simp only [hg, Bool.cond_false] at h
      simp only [Bool.or_eq_false_iff, rkmb2_primBlt_false] at hg
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hg.2.2.1
      · exact rkmb2_checkSegBounds_le lTableMax lRest tRest lS h x hmem
private theorem rkmb2_sum_range_succ_shift (f : ℕ → ℕ) :
    ∀ d : ℕ, (∑ j ∈ Finset.range (d + 1), f j) = f 0 + ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by simp
  | d + 1 => by
    rw [Finset.sum_range_succ, rkmb2_sum_range_succ_shift f d, Finset.sum_range_succ, add_assoc]
private theorem rkmb2_sum_Icc_one_eq_range (f : ℕ → ℝ) :
    ∀ d : ℕ, (∑ w ∈ Finset.Icc 1 d, f w) = ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by have hset : Finset.Icc (1 : ℕ) 0 = ∅ := by ext x; simp
            rw [hset]; simp
  | d + 1 => by
    have hset : Finset.Icc 1 (d + 1) = insert (d + 1) (Finset.Icc 1 d) := by ext x; simp; omega
    rw [hset, Finset.sum_insert (by simp), rkmb2_sum_Icc_one_eq_range f d, Finset.sum_range_succ]
    ring
private theorem rkmb2_altSumNat_eq_sum_range :
    ∀ (d : ℕ) (xs : List ℕ), xs.length = d → altSumNat xs = ∑ j ∈ Finset.range d, xs.getD j 0
  | 0, [], _ => by simp [altSumNat]
  | 0, _ :: _, hlen => by simp at hlen
  | _ + 1, [], hlen => by simp at hlen
  | d + 1, x :: xs, hlen => by
    rw [rkmb2_sum_range_succ_shift]
    simpa [altSumNat] using congrArg (Nat.add x)
      (rkmb2_altSumNat_eq_sum_range d xs (by simpa using hlen))
private theorem rkmb2_checkColdR2_eq (m v2 : ℕ) :
    rkmCheckColdR2Step m v2 = rmsCheckColdR2Step m v2 := rfl
private def rkmUseWalk (anchors : List RampKickAnchor) (r : ℕ) : Bool :=
  if r < 2 then false else (rkmFindAnchor r anchors).isSome
private def rkmAnchorAt (anchors : List RampKickAnchor) (r : ℕ) : RampKickAnchor :=
  match rkmFindAnchor r anchors with | some a => a | none => ⟨r, [1], [1], [1], [[]], []⟩
private theorem rkmb2_active_unpack {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    {vPot : List ℕ} {anchors : List RampKickAnchor} (hk_le : k ≤ kMax)
    (htab : RampKickTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkmCheckAnchorsLMax k lMaxCell anchors = true)
    {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k) (hwk : rkmUseWalk anchors r = true) :
    let a := rkmAnchorAt anchors r
    a.rAct = r ∧ rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks = a.rowLo12 ∧
      rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks ≠ [] ∧
      RampKickActiveValid m lTableMax r vPot a.lSegs a.tauSegs a.rowLo12 ∧
      1 ≤ rkmLastNat 0 a.lSegs ∧ rkmLastNat 0 a.lSegs ≤ lMaxCell := by
  intro a; have hnr2 : ¬ r < 2 := by omega
  unfold rkmUseWalk at hwk; rw [ite_eq_right hnr2] at hwk
  have hrow_r := htab.hrows r hr2 (hrk.trans hk_le)
  cases hfind : rkmFindAnchor r anchors with
  | none => simp [hfind] at hwk
  | some a0 =>
    rw [hfind] at hrow_r
    have ha_eq : a = a0 := by simp [a, rkmAnchorAt, hfind]
    rw [← ha_eq] at hrow_r; obtain ⟨har, heval, hact⟩ := hrow_r
    have hne : rkmEvalT16Lo12 m lTableMax r a.lSegs a.tauSegs a.nsubSegs a.masks ≠ [] := by
      rw [heval]; intro hnil; have hpos := hact.2.2.2.2.1
      rw [hnil] at hpos; simp [altSumNat] at hpos
    have hlast : 1 ≤ rkmLastNat 0 a.lSegs ∧ rkmLastNat 0 a.lSegs ≤ lMaxCell := by
      have hlen1 := hact.1
      rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
      · simp [hl_cons] at hlen1
      · have hmem_anc := (rkmb2_findAnchor_mem hfind).1; rw [← ha_eq] at hmem_anc
        have hall_l := rkmb2_checkAnchorsLMax_mem hlcell hmem_anc (har ▸ hrk)
        exact hall_l _ (by rw [hl_cons]; exact rkmb2_lastNat_mem lt lh)
    exact ⟨har, heval, hne, hact, hlast.1, hlast.2⟩
private theorem rkmb2_active_drift_lt {m lTableMax r : ℕ} {vPot lSegs tauSegs row : List ℕ}
    (hact : RampKickActiveValid m lTableMax r vPot lSegs tauSegs row) :
    let d := min (rkmLastNat 0 lSegs * m) r
    let pLo := fun w ↦ if 1 ≤ w ∧ w ≤ d then (row.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
    let c := ∑ w ∈ Finset.Icc 1 d, pLo w
    (rkmWeightedTau9 lSegs tauSegs : ℝ) / 1000000000 +
        (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) +
        (1 - c) * ((muxRunningCap vPot r : ℝ) / wdScaleR) <
      (vPot.getD r 0 : ℝ) / wdScaleR := by
  intro d pLo c
  obtain ⟨_, _, _, hr_len, _, htot_le, hlt_nat⟩ := hact
  have hc_eq : c = (altSumNat row : ℝ) / 1000000000000 := by
    dsimp only [c, pLo]
    rw [rkmb2_sum_Icc_one_eq_range, rkmb2_altSumNat_eq_sum_range d row hr_len,
      Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_lt : j < d := Finset.mem_range.mp hj
    have hcond : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
    rw [ite_eq_left hcond, Nat.add_sub_cancel]
  have hhit_eq : (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) =
        ((∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0 : ℕ) : ℝ) /
          (1000000000000 * wdScaleR) := by
    dsimp only [pLo]; rw [rkmb2_sum_Icc_one_eq_range, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_lt : j < d := Finset.mem_range.mp hj
    have hcond : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
    have hsub_idx : r - (j + 1) = r - 1 - j := by omega
    rw [ite_eq_left hcond, Nat.add_sub_cancel, hsub_idx, Nat.cast_mul]; ring
  have hdef_eq : 1 - c = ((1000000000000 - altSumNat row : ℕ) : ℝ) / 1000000000000 := by
    rw [hc_eq, Nat.cast_sub htot_le]; ring
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  rw [hhit_eq, hdef_eq]; set W9 : ℕ := rkmWeightedTau9 lSegs tauSegs
  set H27 : ℕ := ∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0
  set D12 : ℕ := 1000000000000 - altSumNat row; set C15 : ℕ := muxRunningCap vPot r
  set VPot : ℕ := vPot.getD r 0
  have hlt_R : (W9 : ℝ) * 1000000000000000000 + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) <
        1000000000000 * (VPot : ℝ) := by
    have hc_lt : ((W9 * 1000000000000000000 + H27 + D12 * C15 : ℕ) : ℝ) <
          ((1000000000000 * VPot : ℕ) : ℝ) := by exact_mod_cast hlt_nat
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hc_lt
  set S27 : ℝ := 1000000000000 * wdScaleR
  have hS27_pos : 0 < S27 := by rw [show S27 = 1000000000000 * wdScaleR from rfl, hB_eq]; positivity
  have hlhs_mul : ((W9 : ℝ) / 1000000000 + (H27 : ℝ) / (1000000000000 * wdScaleR) +
        ((D12 : ℝ) / 1000000000000) * ((C15 : ℝ) / wdScaleR)) * S27 =
      (W9 : ℝ) * 1000000000000000000 + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) := by
    dsimp only [S27]; rw [hB_eq]; ring
  have hrhs_mul : ((VPot : ℝ) / wdScaleR) * S27 = 1000000000000 * (VPot : ℝ) := by
    dsimp only [S27]; rw [hB_eq]; ring
  exact lt_of_mul_lt_mul_right (by linarith) hS27_pos.le
/-- Builds a `JohnsonRampMuxSparseWalkSpec m k lMaxCell` from `RampKickTableValid` and
  `rkmCheckAnchorsLMax`. -/
noncomputable def rkmWalkSpecOf {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    (hm_grid : m ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKickAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKickTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkmCheckAnchorsLMax k lMaxCell anchors = true) :
    JohnsonRampMuxSparseWalkSpec m k lMaxCell where
  hL_max_pos := hlcell_pos
  hL_max_hi := hlcell_hi
  useWalk := rkmUseWalk anchors
  useColdR2 := useColdR2 && !(rkmUseWalk anchors 2) && rkmCheckColdR2Step m (vPot.getD 2 0)
  hColdM2 := fun hc ↦ by
    simp only [Bool.and_eq_true] at hc
    exact hm2_cold hc.1.1
  hColdL2 := fun hc ↦ by
    simp only [Bool.and_eq_true] at hc
    exact hl2_cold hc.1.1
  lInit := fun r ↦ (rkmAnchorAt anchors r).lSegs.headD 1
  lEnd := fun r ↦ rkmLastNat 0 (rkmAnchorAt anchors r).lSegs
  hlEnd_pos := fun r hr2 hrk hwk ↦ (rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk).2.2.2.2.1
  hlEnd_le := fun r hr2 hrk hwk ↦ (rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk).2.2.2.2.2
  n0 := altN0
  hn0 := by unfold altN0; norm_num
  ops0 := fun n r ↦
    let a := rkmAnchorAt anchors r
    rkmSegOps n m r (a.lSegs.headD 1) (a.tauSegs.headD 0) (a.nsubSegs.headD 0) (a.masks.headD [])
  segsTail := fun n r ↦
    let a := rkmAnchorAt anchors r
    rkmToRmsSegs (rkmBuildTailSegs n m r a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail)
  hsegs_mono := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, _, _⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    have hlen1 := hact.1; have hsegB := hact.2.2.1; set a := rkmAnchorAt anchors r
    rw [rmsSegsMono_rkmToRmsSegs]
    rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
    · simp [hl_cons] at hlen1
    · rcases ht_cons : a.tauSegs with _ | ⟨th, tt⟩
      · simp [hl_cons, ht_cons] at hl_t
      · rw [hl_cons, ht_cons] at hsegB; unfold rkmCheckSegBounds at hsegB
        cases hg : Bool.or (primNatBlt lh 1) (Bool.or (primNatBlt lh 1)
            (Bool.or (primNatBlt lTableMax lh)
            (Bool.or (primNatBlt th 1) (primNatBlt 4000000000 th)))) with
        | true => simp [hg] at hsegB
        | false =>
          simp only [hg, Bool.cond_false] at hsegB; dsimp only [List.headD_cons, List.tail_cons]
          exact rkmb2_segsMono_buildTailSegs n m r lTableMax lt tt
            a.nsubSegs.tail a.masks.tail lh hsegB
  hlEnd_eq := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, hl_s, hl_m⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    have hlen1 := hact.1; set a := rkmAnchorAt anchors r; rw [rmsEndL_rkmToRmsSegs]
    rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
    · simp [hl_cons] at hlen1
    · dsimp only [List.headD_cons, List.tail_cons, rkmLastNat]
      exact rkmb2_endL_buildTailSegs n m r lt a.tauSegs.tail a.nsubSegs.tail a.masks.tail lh
        (by simp [← hl_t, hl_cons]) (by simp [← hl_s, hl_cons]) (by simp [← hl_m, hl_cons])
  V := fun r ↦ (vPot.getD r 0 : ℝ) / wdScaleR
  hV0 := by rw [htab.hv0, Nat.cast_zero, zero_div]
  hV_nonneg := fun r _ ↦ by unfold wdScaleR wdScale; positivity
  vCap := fun r ↦ (muxRunningCap vPot r : ℝ) / wdScaleR
  hvCap_ge := fun j r hjr _ ↦ by
    have hB : (0 : ℝ) ≤ wdScaleR := by unfold wdScaleR wdScale; positivity
    exact div_le_div_of_nonneg_right (by exact_mod_cast muxRunningCap_ge_of_le vPot hjr) hB
  hV_cold2 := fun hc _ ↦ by
    simp only [Bool.and_eq_true] at hc
    exact rmsCheckColdR2Step_sound hm_grid (hm2_cold hc.1.1)
      (rkmb2_checkColdR2_eq m (vPot.getD 2 0) ▸ hc.2)
  hV_eig := fun r hr1 hrk hor ↦ by
    refine checkEigStep_sound ?_
    rcases hor with rfl | ⟨huw, hncold⟩
    · exact htab.heig1
    · by_cases hr2 : r < 2
      · have hr_eq1 : r = 1 := by omega
        subst hr_eq1; exact htab.heig1
      · have hr2_ge : 2 ≤ r := by omega
        have huw' := huw; unfold rkmUseWalk at huw'; rw [ite_eq_right hr2] at huw'
        have hrow_r := htab.hrows r hr2_ge (hrk.trans hk_le)
        cases hfind : rkmFindAnchor r anchors with
        | some _ => simp [hfind] at huw'
        | none =>
          rw [hfind] at hrow_r
          rcases hrow_r with ⟨rfl, hc_true, hchk_c⟩ | heig
          · exfalso; apply hncold; refine ⟨rfl, ?_⟩; rw [hc_true, huw, hchk_c]; rfl
          · exact heig
  pLo := fun r w ↦
    let a := rkmAnchorAt anchors r; let d := min (rkmLastNat 0 a.lSegs * m) r
    if 1 ≤ w ∧ w ≤ d then (a.rowLo12.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
  hpLo_nonneg := fun r w ↦ by dsimp only; split_ifs <;> positivity
  hpLo_sum_pos := fun r hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨_, _, _, hr_len, hsum_pos, _, _⟩ := hact
    set a := rkmAnchorAt anchors r; set d := min (rkmLastNat 0 a.lSegs * m) r
    rw [rkmb2_sum_Icc_one_eq_range]
    have hcongr : (∑ j ∈ Finset.range d,
          (if 1 ≤ j + 1 ∧ j + 1 ≤ d then (a.rowLo12.getD ((j + 1) - 1) 0 : ℝ) / 1000000000000
           else 0)) = ((altSumNat a.rowLo12 : ℕ) : ℝ) / 1000000000000 := by
      rw [rkmb2_altSumNat_eq_sum_range d a.rowLo12 hr_len, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj_lt : j < d := Finset.mem_range.mp hj
      rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    rw [hcongr]; have hsumR : (0 : ℝ) < (altSumNat a.rowLo12 : ℝ) := by exact_mod_cast hsum_pos
    positivity
  tauWeighted := fun r ↦ (rkmWeightedTau9 (rkmAnchorAt anchors r).lSegs
    (rkmAnchorAt anchors r).tauSegs : ℝ) / 1000000000
  C_step := 134348800
  hqcount_le := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, _, _⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    obtain ⟨hlen1, hlen8, hsegB, _, _, _, _⟩ := hact
    dsimp only; set a := rkmAnchorAt anchors r; rw [rmsSegsQueryCount_rkmToRmsSegs]
    have hall_le := rkmb2_checkSegBounds_le lTableMax a.lSegs a.tauSegs 1 hsegB
    have hlTab_hi : lTableMax ≤ 8192 := by
      have h1 := Nat.mul_le_mul_left lTableMax htab.hm1; have hhi := htab.hlMax_hi; omega
    have hr1024 : r ≤ 1024 := (hrk.trans hk_le).trans htab.hkMax_hi
    have hC_nat : 2 * a.lSegs.length * lTableMax * (r + 1) ≤ 134348800 :=
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlen8) hlTab_hi)
        (Nat.succ_le_succ hr1024)).trans (by norm_num)
    have hC_real : 2 * (a.lSegs.length : ℝ) * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) ≤ 134348800 := by
      have hc : ((2 * a.lSegs.length * lTableMax * (r + 1) : ℕ) : ℝ) ≤ (134348800 : ℝ) := by
        exact_mod_cast hC_nat
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
    rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
    · simp [hl_cons] at hlen1
    · rcases ht_cons : a.tauSegs with _ | ⟨th, tt⟩
      · simp [hl_cons, ht_cons] at hl_t
      · rw [hl_cons] at hall_le hC_real
        dsimp only [List.headD_cons, List.tail_cons]
        have hbd := rkmSegsQueryCount_build_le n m r lTableMax lh th
          (a.nsubSegs.headD 0) (a.masks.headD []) lt tt a.nsubSegs.tail a.masks.tail
          (hall_le lh List.mem_cons_self)
          (fun x hx ↦ hall_le x (List.mem_cons_of_mem lh hx))
        linarith
  hpLo_le := fun n r hn0 hr2 hrk hwk R hR w hw ↦ by
    obtain ⟨_, heval, hne, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hl_t, hl_s, hl_m⟩ := rkmb2_evalT16Lo12_ne_nil_lengths hne
    have hlen1 := hact.1
    dsimp only; set a := rkmAnchorAt anchors r
    rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
    have hc : 1 ≤ w ∧ w ≤ min (rkmLastNat 0 a.lSegs * m) r := ⟨hw1, hwd⟩
    rw [ite_eq_left hc, symHitProb_evalRampMuxSegs_rkmToRmsSegs]
    have hsound := (rkmEvalT16Lo12_sound hn0 hne hR).2.2.2.2.2
    have hend_eq : rkmEndL (a.lSegs.headD 1)
          (rkmBuildTailSegs n m r a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail) =
        rkmLastNat 0 a.lSegs := by
      rcases hl_cons : a.lSegs with _ | ⟨lh, lt⟩
      · simp [hl_cons] at hlen1
      · dsimp only [List.headD_cons, List.tail_cons, rkmLastNat]
        exact rkmb2_endL_buildTailSegs n m r lt a.tauSegs.tail a.nsubSegs.tail a.masks.tail lh
          (by simp [← hl_t, hl_cons])
          (by simp [← hl_s, hl_cons])
          (by simp [← hl_m, hl_cons])
    rw [heval] at hsound
    exact hsound w (by rwa [hend_eq])
  hdrift_ramp_lt := fun r hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkmb2_active_unpack hk_le htab hlcell hr2 hrk hwk
    exact rkmb2_active_drift_lt hact
/-- Turnkey parallel query-model circuit for a certified `RampKickMux` `(m, k)` cell. -/
noncomputable def rkmCellCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKickAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKickTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkmCheckAnchorsLMax k lMaxCell anchors = true) (n : ℕ) :
    OracleCirc Var (Stage1.qubits n (lMaxCell * m) k) ((n + 1) * m) :=
  johnsonRampMuxSparseCircuit res hm_grid hk_grid
    (rkmWalkSpecOf hm_grid vPot anchors hk_le hm2_cold hl2_cold hlcell_pos hlcell_hi htab hlcell) n
/-- Exact probability-`1` correctness of `rkmCellCircuit` on `groverTargetSets n k`. -/
theorem rkmCell_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKickAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKickTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkmCheckAnchorsLMax k lMaxCell anchors = true)
    (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))}
    (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n (lMaxCell * m) k)) ⦄
    (qset ;;
      (rkmCellCircuit res hm_grid hk_grid vPot anchors hk_le hm2_cold hl2_cold
        hlcell_pos hlcell_hi htab hlcell n).compile qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ :=
  johnsonRampMuxSparseCircuit_correctness res hm_grid hk_grid _ hn hkN hS
/-- Asymptotic uniform-average relative-cost bound of `rkmCellCircuit` from
  `checkAltBound12`. -/
theorem rkmCell_rel_cost {Var : Type} [DecidableEq Var] (res : Var)
    {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool} {rel : ℚ≥0}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKickAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKickTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkmCheckAnchorsLMax k lMaxCell anchors = true)
    (hbnd : ∃ num den : ℕ,
      rel = NNRat.divNat num den ∧ checkAltBound12 m k (vPot.getD k 0) num den = true) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n →
      AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n (lMaxCell * m) k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ qset ;;
            (rkmCellCircuit res hm_grid hk_grid vPot anchors hk_le hm2_cold hl2_cold
              hlcell_pos hlcell_hi htab hlcell n).compile qAssign
              (groverParallelMarkingOracle m S))
        ((rel : ℝ) * vanillaFindAllCost n m k) := by
  obtain ⟨num, den, rfl, hb⟩ := hbnd
  exact johnsonRampMuxSparseCircuit_rel_cost res hm_grid hk_grid _
    (checkAltBound12_sound (one_le_of_mem_groverGrid hm_grid) hb)
end
end QuantumComputation.Specs.DickeSol
