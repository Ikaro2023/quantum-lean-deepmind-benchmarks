module
public import Track2Weak.TerminalRead
import all Track2Grover.Engine.WeakDickeBase
import all Track2Grover.Engine.FindAllJohnsonP01
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Matrix
open scoped Matrix NNReal

noncomputable def weakPrepGate (n m : ℕ) (hm : m ≤ 2^n) : Unitary (2^(m*(n+1))) :=
  householderPrepUnitary (symInjMat n m *ᵥ u0Vec (2^n) m)
    (by rw [sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hm)

/-- Full register reset including the result variable, followed by uniform subset preparation. -/
noncomputable def weakInitialize {Var : Type} (res : Var) (n m M : ℕ) (hm : m ≤ 2^n) :
    OracleCirc Var (m*(n+1)+M) ((n+1)*m) :=
  .seq (mapAndMeasureLow res _ M _ (fun _ ↦ 0))
    (.step (phaseTag ((lowBlock _ M).embedUnitary (weakPrepGate n m hm))))

theorem weakInitialize_cost {Var : Type} [DecidableEq Var] (res : Var) {n m M : ℕ}
    (hm : m ≤ 2^n) (S : Finset (Fin (2^n))) :
    CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((weakInitialize res n m M hm).compile QProg.qAssign (groverParallelMarkingOracle m S)) 0 := by
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  simpa [weakInitialize, OracleDynamicCircuit.compile] using
    (costBound_mapAndMeasureLow (Var := Var) res (W := m*(n+1)) (M := M) (fun _ ↦ 0) hor).seq
      (costBound_qAssign_phaseTag (Var := Var) hor ((lowBlock _ M).embedUnitary (weakPrepGate n m hm)))

theorem weakTerminalRead_cost {Var : Type} [DecidableEq Var] (res : Var) {n m k M : ℕ}
    (room : k*n < m*(n+1)) (S : Finset (Fin (2^n))) :
    CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((weakTerminalRead res n m k M room).compile QProg.qAssign (groverParallelMarkingOracle m S)) 1 := by
  have hq := CostBound.qAssign (Var := Var)
    (CostModel.ofEmbeddedOracle (n := m*(n+1)+M) (groverParallelMarkingOracle m S))
    (((lowBlock _ M).compose (fullReg n m)).embedUnitary (groverParallelMarkingOracle m S))
  rw [CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, Nat.cast_one] at hq
  simpa [weakTerminalRead, OracleDynamicCircuit.compile] using hq.seq
    (costBound_mapAndMeasureLow res (weakReadMap n m k M room) (isRealMatrix_groverParallelMarkingOracle m S))

theorem weakInitialize_wp {Var : Type} [DecidableEq Var] [Subsingleton Var] (res : Var)
    {n m M : ℕ} (hm : m ≤ 2^n) (S : Finset (Fin (2^n)))
    (Θ : CQAssertion (Store Var) (2^(m*(n+1)+M))) (σ : Store Var) :
    ((wp ((weakInitialize res n m M hm).compile QProg.qAssign (groverParallelMarkingOracle m S))
      Θ) σ).1.1 =
      rmsVecQuad (Θ (fun _ ↦ 0)).1.1
        (workMemState (liftSymVec n m (u0Vec (2^n) m)) (Pi.single (0 : Fin (2^M)) 1)) •
      (1 : Operator _) := by
  let U := (lowBlock _ M).embedUnitary (weakPrepGate n m hm)
  let Ψ := wp (QProg.qAssign (phaseTag U)) Θ
  have hΨ (τ : Store Var) : (Ψ τ).1.1 = (Ψ (fun _ ↦ τ res)).1.1 := by
    have h : τ = (fun _ ↦ τ res) := funext fun j ↦ congrArg τ (Subsingleton.elim j res)
    exact congrArg (fun σ ↦ (Ψ σ).1.1) h
  simp only [weakInitialize, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step, wp_qSeq]
  change ((wp _ Ψ) σ).1.1 = _
  rw [mkrWp_mapAndMeasureLow res _ _ (fun t ↦ (Ψ (fun _ ↦ t)).1.1) Ψ hΨ,
    lowHighEquiv_zero]
  have hdiag : ∀ c : ℂ, (diagonal (fun _ : Fin (2^(m*(n+1)+M)) ↦ c)) = c • 1 := by
    intro c
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hdiag]
  congr 1
  change (Ψ (fun _ ↦ 0)).1.1 0 0 = _
  rw [rmsVecQuad_single (Ψ (fun _ ↦ 0)).1.1 0, show (Pi.single (0 : Fin (2^(m*(n+1)+M))) (1:ℂ)) =
      workMemState (Pi.single (0 : Fin (2^(m*(n+1)))) 1) (Pi.single (0 : Fin (2^M)) 1) by
    rw [workMemState_single, ← lowHighEquiv_zero, Equiv.symm_apply_apply]]
  have hmat : (Ψ (fun _ ↦ 0)).1.1 = U.1ᴴ * (Θ (fun _ ↦ 0)).1.1 * U.1 := by
    dsimp only [Ψ]
    rw [wp_qAssign, wp_phaseTag]
    simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U Θ (fun _ ↦ 0)
  rw [hmat, rmsVecQuad_conj]
  dsimp only [U,weakPrepGate]
  rw [QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
    householderPrepUnitary_mulVec_zero]
  rfl

end QuantumComputation.Specs.DickeSol
