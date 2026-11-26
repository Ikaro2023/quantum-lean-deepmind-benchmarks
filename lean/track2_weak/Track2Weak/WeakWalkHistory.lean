module

public import Track2Weak.WeakWalkStages
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

/-! Exact finite adaptive history of conditioned walk segments. -/
@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Matrix
open QProg (qAssign)
open scoped Matrix NNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable def weakNo (n : ℕ) (row : WeakRow) (x : Fin 513 → ℝ) :=
  weakKeep 512 row.2.cVal (weakOrbitStep n 512 row x)

noncomputable def weakYes (n : ℕ) (row : WeakRow) (x : Fin 513 → ℝ) :=
  weakClick 512 row.2.sVal (weakOrbitStep n 512 row x)

/-- Exact tracial weight of an unnormalized physical state in the Johnson chart. -/
theorem weakState_identity {n r : ℕ} (S : Finset (Fin (2^n))) (hS : S.card = r)
    (hNr : 1024+r ≤ 2^n) (x : Fin (orbDim 1024 r) → ℝ) (μ : Fin (2^(512*n))) :
    rmsVecQuad (1 : Operator _) (weakState S hS x μ) = (vecSqNorm x : ℂ) := by
  subst r
  let v := orbEmbedGen (2^n) 1024 S x
  let idx := fun E : SymSubset (2^n) 1024 ↦ (lowHighEquiv (1024*(n+1)) (512*n)).symm (subsetWorkIdx n 1024 E,μ)
  have hi : Function.Injective idx := fun i j h ↦ subsetWorkIdx_injective _ _
    (congrArg Prod.fst ((lowHighEquiv _ _).symm.injective h))
  have hv : workMemState (liftSymVec n 1024 v) (Pi.single μ 1) =
      ∑ E, (v E : ℂ) • Pi.single (idx E) 1 := by
    rw [liftSymVec_eq_sum_single, mkrWorkMemState_sum_left]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [mkrWorkMemState_smul_left, workMemState_single]
  change rmsVecQuad 1 (workMemState (liftSymVec n 1024 v) (Pi.single μ 1)) = _
  rw [hv, show (1 : Operator _) = diagonal (fun _ ↦ (1 : ℂ)) from Matrix.diagonal_one.symm,
    rmsVecQuad_diagonal_sum_single _ v idx hi]
  have hs := dot_orbEmbedGen hNr x x
  simpa [v, vecSqNorm, sq, ← Complex.ofReal_mul, ← Complex.ofReal_sum] using
    congrArg (fun a : ℝ ↦ (a : ℂ)) hs

/-- A no-click outcome is the only input to the next segment. -/
theorem weakStages_cons_wp {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ}
    (hn : 80000 ≤ n) (hM : 1 ≤ 512*n) (finish : WeakCellCirc Var n)
    (row : WeakRow) (tail : List WeakRow) (S : Finset (Fin (2^n))) (hS : S.card = 512)
    (x : Fin 513 → ℝ) (μ : Fin (2^(512*n))) (hμ : μ.val < 2^(512*n-1))
    (Θ : CQAssertion (Store Var) (2^(1024*(n+1)+512*n))) (σ : Store Var) :
    rmsVecQuad ((wp ((weakStages res n hM finish (row::tail)).compile qAssign
      (groverParallelMarkingOracle 1024 S)) Θ) σ).1.1 (weakState S hS x μ) =
    rmsVecQuad ((wp ((weakStages res n hM finish tail).compile qAssign
      (groverParallelMarkingOracle 1024 S)) Θ) (Store.subst σ res 0)).1.1
      (weakState S hS (weakNo n row x) μ) +
    rmsVecQuad ((wp (finish.compile qAssign (groverParallelMarkingOracle 1024 S)) Θ)
      (Store.subst σ res 1)).1.1 (weakState S hS (weakYes n row x) (memWithTopOne hM μ hμ)) := by
  simp only [weakStages, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_qIf, wp_qSeq]
  rw [weakStage_wp res hn hM row S hS x μ hμ]
  simp [wp_qIf, Store.subst, weakNo, weakYes]

/-- The terminal reward function acts on subnormalized orbital vectors. -/
noncomputable def weakPayoff (n : ℕ) (F : (Fin 513 → ℝ) → ℂ) : List WeakRow → (Fin 513 → ℝ) → ℂ
  | [], x => F x
  | row :: tail, x => weakPayoff n F tail (weakNo n row x) + F (weakYes n row x)

/-- The full circuit computes the adaptive sum of terminal branch rewards. -/
theorem weakStages_payoff {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ}
    (hn : 80000 ≤ n) (hM : 1 ≤ 512*n) (finish : WeakCellCirc Var n)
    (S : Finset (Fin (2^n))) (hS : S.card = 512)
    (Θ : CQAssertion (Store Var) (2^(1024*(n+1)+512*n))) (F : (Fin 513 → ℝ) → ℂ)
    (hF : ∀ x μ σ, rmsVecQuad ((wp (finish.compile qAssign (groverParallelMarkingOracle 1024 S))
      Θ) σ).1.1 (weakState S hS x μ) = F x) (rows : List WeakRow) (x : Fin 513 → ℝ)
    (μ : Fin (2^(512*n))) (hμ : μ.val < 2^(512*n-1)) (σ : Store Var) :
    rmsVecQuad ((wp ((weakStages res n hM finish rows).compile qAssign
      (groverParallelMarkingOracle 1024 S)) Θ) σ).1.1 (weakState S hS x μ) = weakPayoff n F rows x := by
  induction rows generalizing x σ with
  | nil => exact hF x μ σ
  | cons row tail ih =>
    rw [weakStages_cons_wp res hn hM finish row tail S hS x μ hμ, ih, hF]
    rfl

end QuantumComputation.Specs.DickeSol

#print axioms QuantumComputation.Specs.DickeSol.weakStages_payoff
#print axioms QuantumComputation.Specs.DickeSol.weakState_identity