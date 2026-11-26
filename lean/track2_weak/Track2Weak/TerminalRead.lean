module

public import Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Matrix
open scoped Matrix

/-- The low work bits carry either the exact sorted tuple or an out-of-range retry code. -/
noncomputable def weakReadCode (n m k : ℕ) (room : k*n < m*(n+1))
    (w : Fin (2^(m*(n+1)))) : Fin (2^(m*(n+1))) :=
  let hits := (markedSlotAddrs n m w).toFinset
  if h : hits.card = k then
    let word := (addrEquiv n k).symm (hits.orderEmbOfFin h)
    ⟨word.val, lt_of_lt_of_le word.isLt (Nat.pow_le_pow_right (by decide) room.le)⟩
  else ⟨2^(k*n), Nat.pow_lt_pow_right (by decide) room⟩

theorem weakReadCode_spec {n m k : ℕ} (room : k*n < m*(n+1))
    (S : Finset (Fin (2^n))) (hS : S.card = k) (E : SymSubset (2^n) m) :
    let z := (weakReadCode n m k room (parallelMarkPerm n m S (subsetWorkIdx n m E))).val
    (z ≠ 2^(k*n) ↔ (E.1 ∩ S).card = k) ∧
      (z ≠ 2^(k*n) → decodeTargets n k (Int.ofNat z) = S) := by
  let w := parallelMarkPerm n m S (subsetWorkIdx n m E)
  let hits := (markedSlotAddrs n m w).toFinset
  have hx := markedSlotAddrs_parallelMarkPerm_subsetWorkIdx S E
  have hc : hits.card = (E.1 ∩ S).card :=
    (List.toFinset_card_of_nodup (nodup_markedSlotAddrs n m w)).trans hx.2
  have hsub : hits ⊆ S := fun x hx' ↦ hx.1 x (List.mem_toFinset.mp hx')
  dsimp only
  change ((weakReadCode n m k room w).val ≠ 2^(k*n) ↔ (E.1 ∩ S).card = k) ∧
    ((weakReadCode n m k room w).val ≠ 2^(k*n) →
    decodeTargets n k (Int.ofNat (weakReadCode n m k room w).val) = S)
  by_cases h : hits.card = k
  · have heq : hits = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    let word := (addrEquiv n k).symm (hits.orderEmbOfFin h)
    have hz : (weakReadCode n m k room w).val = word.val := by
      simp only [weakReadCode, show (markedSlotAddrs n m w).toFinset.card = k from h, ↓reduceDIte]
      rfl
    rw [hz]
    refine ⟨⟨fun _ ↦ hc.symm.trans h, fun _ ↦ word.isLt.ne⟩, fun _ ↦ ?_⟩
    apply decodeTargets_ofNat_eq_of_subset_of_injective hS
    · intro i
      simp only [word, Equiv.apply_symm_apply]
      exact hsub (Finset.orderEmbOfFin_mem hits h i)
    · simpa only [word, Equiv.apply_symm_apply] using (hits.orderEmbOfFin h).injective
  · have hz : (weakReadCode n m k room w).val = 2^(k*n) := by
      simp only [weakReadCode, show (markedSlotAddrs n m w).toFinset.card ≠ k from h, ↓reduceDIte]
    rw [hz]
    simp [← hc, h]

noncomputable def weakReadMap (n m k M : ℕ) (room : k*n < m*(n+1))
    (z : Fin (2^(m*(n+1)+M))) :=
  (lowHighEquiv (m*(n+1)) M).symm (weakReadCode n m k room ((lowHighEquiv _ _ z).1), 0)

noncomputable def weakTerminalRead {Var : Type} (res : Var) (n m k M : ℕ)
    (room : k*n < m*(n+1)) : OracleCirc Var (m*(n+1)+M) ((n+1)*m) :=
  .seq (.oracle ((lowBlock _ M).compose (fullReg n m)))
    (mapAndMeasureLow res _ M _ (weakReadMap n m k M room))

theorem weakTerminalRead_queries {Var : Type} (res : Var) (n m k M : ℕ)
    (room : k*n < m*(n+1)) : mkrStaticOracleCalls (weakTerminalRead res n m k M room) = some 1 := by
  unfold weakTerminalRead
  simp only [mkrStaticOracleCalls, mkrStaticOracleCalls_mapAndMeasureLow]

/-- Exact readout distribution tested against any scalar function of the returned integer.
The incoming real superposition may be subnormalized and the high flag may be set. -/
theorem weakTerminalRead_quadratic {Var : Type} [DecidableEq Var] (res : Var)
    {n m k M : ℕ} (room : k*n < m*(n+1)) (S : Finset (Fin (2^n)))
    (v : SymSubset (2^n) m → ℝ) (μ : Fin (2^M))
    (g : ℤ → ℂ) (Φ : CQAssertion (Store Var) (2^(m*(n+1)+M)))
    (hΦ : ∀ τ, (Φ τ).1.1 = g (τ res) • (1 : Operator _)) (σ : Store Var) :
    rmsVecQuad (((wp ((weakTerminalRead res n m k M room).compile QProg.qAssign
      (groverParallelMarkingOracle m S)) Φ) σ).1.1)
      (workMemState (liftSymVec n m v) (Pi.single μ 1)) =
      ∑ E, ((v E : ℂ)^2) * g (Int.ofNat
        (weakReadCode n m k room (parallelMarkPerm n m S (subsetWorkIdx n m E))).val) := by
  let idx (E : SymSubset (2^n) m) :=
    (lowHighEquiv (m*(n+1)) M).symm (parallelMarkPerm n m S (subsetWorkIdx n m E), μ)
  have hi : Function.Injective idx := fun i j h ↦ subsetWorkIdx_injective n m
    ((parallelMarkPerm n m S).injective (congrArg Prod.fst ((lowHighEquiv _ _).symm.injective h)))
  have hv : workMemState ((permutationUnitary (parallelMarkPerm n m S)).1 *ᵥ liftSymVec n m v)
        (Pi.single μ 1) = ∑ E, (v E : ℂ) • Pi.single (idx E) 1 := by
    rw [liftSymVec_eq_sum_single, Matrix.mulVec_sum, mkrWorkMemState_sum_left]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [Matrix.mulVec_smul, permutationUnitary_mulVec_single, mkrWorkMemState_smul_left,
      workMemState_single]
  have hassign (U : Unitary (2^(m*(n+1)+M))) (θ : CQAssertion (Store Var) _) :
      (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
    simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
  simp only [weakTerminalRead, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_oracle,
    wp_qSeq, wp_qAssign, hassign]
  rw [rmsVecQuad_conj, QRegister.embedUnitary_compose, fullReg_embedUnitary_eq_permutationUnitary,
    QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState, hv,
    mkrWp_mapAndMeasureLow res _ _ (fun t ↦ g t • (1 : Operator _)) Φ hΦ,
    rmsVecQuad_diagonal_sum_single _ v idx hi]
  apply Finset.sum_congr rfl
  intro E _
  simp [idx, weakReadMap]

end QuantumComputation.Specs.DickeSol
