module

public import Track2Weak.FlagRotation
public import Track2Weak.WeakWalk
import all Track2Grover.Engine.WeakDickeCore
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge
import all Track2Weak.FlagRotation

/-! A two-query exact weak measurement of the complete-intersection Johnson bin. -/
@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Matrix
open QProg (qAssign measureRegister)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal

abbrev weakOracleReg (n m M : ℕ) :=
  (lowBlock (m*(n+1)) M).compose (fullReg n m)

def weakComplete (n m r : ℕ) (w : Fin (2^(m*(n+1)))) : Bool :=
  decide ((markedSlotAddrs n m w).length = r)

/-- Compute marker bits, rotate the flag under a target-independent predicate, measure it,
and erase the marker bits with the second call. -/
noncomputable def weakProbe {Var : Type} (res : Var) (n m M r : ℕ) (hM : 1 ≤ M)
    (p : RealFlagPair) : OracleCirc Var (m*(n+1)+M) ((n+1)*m) :=
  .seq (.oracle (weakOracleReg n m M)) (.seq
    (.step (phaseTag (realFlagUnitary (m*(n+1)) M hM (weakComplete n m r) p)))
    (.seq (.measure res (topAncReg (m*(n+1)) M hM)) (.oracle (weakOracleReg n m M))))

theorem weakProbe_cost {Var : Type} [DecidableEq Var] (res : Var) {n m M r : ℕ} (hM : 1 ≤ M)
    (p : RealFlagPair) (S : Finset (Fin (2^n))) :
    CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((weakProbe res n m M r hM p).compile qAssign (groverParallelMarkingOracle m S)) 2 := by
  let model := CostModel.ofEmbeddedOracle (n := m*(n+1)+M) (groverParallelMarkingOracle m S)
  have hc := CostBound.qAssign (Var := Var) model
      ((weakOracleReg n m M).embedUnitary (groverParallelMarkingOracle m S))
  dsimp only [model] at hc
  rw [CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, Nat.cast_one] at hc
  have hr := costBound_qAssign_phaseTag (Var := Var) (isRealMatrix_groverParallelMarkingOracle m S)
    (realFlagUnitary (m*(n+1)) M hM (weakComplete n m r) p)
  have hm : CostBound (Var := Var) model (measureRegister res (topAncReg (m*(n+1)) M hM)) 0 := by
    simpa [model, measureRegister, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) model res
        ((topAncReg (m*(n+1)) M hM).computationalBasisMeasurement : Measurement (2^(m*(n+1)+M)) (2^1))
  convert hc.seq (hr.seq (hm.seq hc)) using 1 <;> norm_num [weakProbe, compile, model]

/-- Conjugating a workspace-diagonal operator by the opaque bit oracle reads the
intersection cardinality on every subset basis state. -/
theorem weak_diagonal_unmark {n m r : ℕ} (S : Finset (Fin (2^n))) (yes no : ℝ)
    (x : SymSubset (2^n) m → ℝ) :
    let U := (permutationUnitary (parallelMarkPerm n m S)).1
    U *ᵥ ((diagonal (fun z ↦ ((if weakComplete n m r z then yes else no : ℝ) : ℂ))) *ᵥ
      (U *ᵥ liftSymVec n m x)) = liftSymVec n m (weakSubset S r yes no x) := by
  dsimp only
  rw [liftSymVec_eq_sum_single, liftSymVec_eq_sum_single, mulVec_sum, mulVec_sum, mulVec_sum]
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  rw [mulVec_smul, mulVec_smul, mulVec_smul, permutationUnitary_mulVec_single]
  let j := parallelMarkPerm n m S (subsetWorkIdx n m E)
  let coeff := fun z ↦ ((if weakComplete n m r z then yes else no : ℝ) : ℂ)
  have hd : (diagonal coeff) *ᵥ Pi.single j 1 = Pi.single j (coeff j) := by
    funext z
    rw [mulVec_diagonal]
    by_cases h : z = j <;> simp [h]
  rw [hd, permutationUnitary_mulVec_single, show parallelMarkPerm n m S j = subsetWorkIdx n m E from
    parallelMarkPerm_involutive _ _]
  have hcoeff : coeff j = (if (E.1 ∩ S).card = r then (yes : ℂ) else no) := by
    by_cases h : (E.1 ∩ S).card = r <;>
      simp [coeff, j, weakComplete, (markedSlotAddrs_parallelMarkPerm_subsetWorkIdx S E).2, h]
  rw [hcoeff]
  funext z
  by_cases h : z = subsetWorkIdx n m E <;> by_cases hi : (E.1 ∩ S).card = r <;>
    simp [weakSubset, hi, h, mul_comm]

private theorem weak_quad_assign {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (U : Unitary d) (Θ : CQAssertion (Store Var) d) (σ : Store Var) (v : Fin d → ℂ) :
    rmsVecQuad ((wp (.qAssign U) Θ) σ).1.1 v = rmsVecQuad (Θ σ).1.1 (U.1 *ᵥ v) := by
  rw [wp_qAssign]
  have h : ((Θ.qAssign U σ).1.1) = U.1ᴴ * (Θ σ).1.1 * U.1 := by
    simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U Θ σ
  rw [h, rmsVecQuad_conj]

private theorem weak_quad_tag {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (U : Unitary d) (Θ : CQAssertion (Store Var) d) (σ : Store Var) (v : Fin d → ℂ) :
    rmsVecQuad ((wp (.qAssign (phaseTag U)) Θ) σ).1.1 v = rmsVecQuad (Θ σ).1.1 (U.1 *ᵥ v) := by
  simpa only [wp_qAssign, wp_phaseTag] using weak_quad_assign U Θ σ v

private theorem weak_quad_oracle {Var : Type} [DecidableEq Var] {n m M : ℕ}
    (S : Finset (Fin (2^n))) (Θ : CQAssertion (Store Var) (2^(m*(n+1)+M))) (σ : Store Var)
    (x : Fin (2^(m*(n+1))) → ℂ) (μ : Fin (2^M)) :
    rmsVecQuad ((wp (.qAssign ((weakOracleReg n m M).embedUnitary
      (groverParallelMarkingOracle m S))) Θ) σ).1.1 (workMemState x (Pi.single μ 1)) =
    rmsVecQuad (Θ σ).1.1 (workMemState ((permutationUnitary (parallelMarkPerm n m S)).1 *ᵥ x)
      (Pi.single μ 1)) := by
  rw [weak_quad_assign, weakOracleReg, QRegister.embedUnitary_compose,
    fullReg_embedUnitary_eq_permutationUnitary S, QRegister.embedUnitary_val,
    embedMatrix_lowBlock_mulVec_workMemState]

private theorem weak_quad_measure {Var : Type} [DecidableEq Var] {q : ℕ} (res : Var)
    (reg : QRegister 1 q) (Θ : CQAssertion (Store Var) (2^q)) (σ : Store Var) (v : Fin (2^q) → ℂ) :
    rmsVecQuad ((wp (measureRegister res reg) Θ) σ).1.1 v =
      rmsVecQuad (Θ (Store.subst σ res 0)).1.1 (reg.basisOutcomeProjector 0 *ᵥ v) +
      rmsVecQuad (Θ (Store.subst σ res 1)).1.1 (reg.basisOutcomeProjector 1 *ᵥ v) := by
  simpa [rmsVecQuad, quadForm] using
    (quadForm_wp_measureRegister res reg Θ σ v).trans (Fin.sum_univ_two _)

/-- Exact joint branch semantics, including the postmeasurement store and the clean or flipped
ancilla. The input vector may be subnormalized, as occurs after earlier no-click outcomes. -/
theorem weakProbe_wp {Var : Type} [DecidableEq Var] (res : Var) {n m M r : ℕ} (hM : 1 ≤ M)
    (p : RealFlagPair) (S : Finset (Fin (2^n))) (x : SymSubset (2^n) m → ℝ) {μ : Fin (2^M)}
    (hμ : μ.val < 2^(M-1)) (Θ : CQAssertion (Store Var) (2^(m*(n+1)+M))) (σ : Store Var) :
    rmsVecQuad ((wp ((weakProbe res n m M r hM p).compile qAssign (groverParallelMarkingOracle m S))
      Θ) σ).1.1 (workMemState (liftSymVec n m x) (Pi.single μ 1)) =
    rmsVecQuad (Θ (Store.subst σ res 0)).1.1
      (workMemState (liftSymVec n m (weakSubset S r p.cVal 1 x)) (Pi.single μ 1)) +
    rmsVecQuad (Θ (Store.subst σ res 1)).1.1
      (workMemState (liftSymVec n m (weakSubset S r p.sVal 0 x))
        (Pi.single (memWithTopOne hM μ hμ) 1)) := by
  let U := (permutationUnitary (parallelMarkPerm n m S)).1
  let y := U *ᵥ liftSymVec n m x
  have hno : (fun w ↦ if weakComplete n m r w then (p.cVal : ℂ)*y w else y w) =
      diagonal (fun z ↦ ((if weakComplete n m r z then p.cVal else 1 : ℝ) : ℂ)) *ᵥ y := by
    funext w
    rw [mulVec_diagonal]
    cases weakComplete n m r w <;> simp
  have hyes : (fun w ↦ if weakComplete n m r w then (p.sVal : ℂ)*y w else 0) =
      diagonal (fun z ↦ ((if weakComplete n m r z then p.sVal else 0 : ℝ) : ℂ)) *ᵥ y := by
    funext w
    rw [mulVec_diagonal]
    cases weakComplete n m r w <;> simp
  dsimp only [weakProbe, compile]
  rw [wp_qSeq, weak_quad_oracle, wp_qSeq, weak_quad_tag,
    show (realFlagUnitary (m*(n+1)) M hM (weakComplete n m r) p).1 =
      realFlagMat (m*(n+1)) M hM (weakComplete n m r) p from rfl,
    realFlagMat_mulVec_workMemState hM _ p y hμ, wp_qSeq, weak_quad_measure,
    topAncReg_projector_zero_mulVec hM _ _ hμ, topAncReg_projector_one_mulVec hM _ _ hμ,
    weak_quad_oracle, weak_quad_oracle, hno, hyes,
    weak_diagonal_unmark S p.cVal 1 x, weak_diagonal_unmark S p.sVal 0 x]

end QuantumComputation.Specs.DickeSol

#print axioms QuantumComputation.Specs.DickeSol.weakProbe_cost
#print axioms QuantumComputation.Specs.DickeSol.weakProbe_wp