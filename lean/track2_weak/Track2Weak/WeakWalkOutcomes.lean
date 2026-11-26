module

public import Track2Weak.WeakWalkHistory
public import Track2Weak.TerminalEffects

/-! Exact probability of success on any finite adaptive weak-filter schedule. -/
@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Matrix
open QProg (qAssign)
open scoped Matrix NNReal
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

abbrev weakTop : Fin 513 := ⟨512, by decide⟩

noncomputable def weakSurvivor (n : ℕ) : List WeakRow → (Fin 513 → ℝ) → (Fin 513 → ℝ)
  | [], x => x
  | row :: tail, x => weakSurvivor n tail (weakNo n row x)

/-- All clicks are recoverable. The only failure mass is in incomplete bins of the final survivor. -/
noncomputable def weakSuccessMass (n : ℕ) (rows : List WeakRow) (x : Fin 513 → ℝ) : ℝ :=
  vecSqNorm x - vecSqNorm (weakSurvivor n rows x) + (weakSurvivor n rows x weakTop)^2

theorem weakOrbitStep_isometry {n : ℕ} (hn : 80000 ≤ n) (row : WeakRow) (x : Fin 513 → ℝ) :
    vecSqNorm (weakOrbitStep n 512 row x) = vecSqNorm x := by
  have hN : 2^12 ≤ (2:ℕ)^n := Nat.pow_le_pow_right (by decide) (by omega)
  have hO := dAltStepOrbMat_orthogonal_two_pow (m:=1024) (r:=512) (n:=n) (by omega) (by omega) (by omega)
  rw [← sq_vecNorm, ← sq_vecNorm x]
  apply congrArg (fun a : ℝ ↦ a^2)
  unfold weakOrbitStep
  rw [vecNorm_rkmMaskSignVec]
  generalize altStepCount row.1.tau9 row.1.nSub (2^n) = k
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, ih, vecNorm_mulVec_of_orthogonal hO]

theorem weakRow_conservation {n : ℕ} (hn : 80000 ≤ n) (row : WeakRow) (x : Fin 513 → ℝ) :
    vecSqNorm (weakNo n row x) + (weakYes n row x weakTop)^2 = vecSqNorm x := by
  have h := weak_branch_mass 512 row.2.cVal_sq_add_sVal_sq (weakOrbitStep n 512 row x)
  rw [weak_click_mass weakTop, weakOrbitStep_isometry hn] at h
  simpa [weakNo, weakYes, weakClick, weakTop, mul_pow] using h

theorem weakPayoff_success {n : ℕ} (hn : 80000 ≤ n) (rows : List WeakRow) (x : Fin 513 → ℝ) :
    weakPayoff n (fun y ↦ ((y weakTop)^2 : ℝ)) rows x = (weakSuccessMass n rows x : ℂ) := by
  induction rows generalizing x with
  | nil => simp [weakPayoff, weakSuccessMass, weakSurvivor]
  | cons row tail ih =>
    rw [weakPayoff, ih, weakSuccessMass, weakSuccessMass, weakSurvivor]
    rw [← Complex.ofReal_add]
    apply congrArg Complex.ofReal
    linarith [weakRow_conservation hn row x]

theorem weakPayoff_zero (n : ℕ) (rows : List WeakRow) (x : Fin 513 → ℝ) :
    weakPayoff n (fun _ ↦ 0) rows x = 0 := by
  induction rows generalizing x with
  | nil => rfl
  | cons row tail ih => simp [weakPayoff, ih]

private theorem weak_full_prob {n r : ℕ} (S : Finset (Fin (2^n))) (hS : S.card = r)
    (hN : 1024+r ≤ 2^n) (x : Fin (orbDim 1024 r) → ℝ) (j : Fin (orbDim 1024 r)) :
    symHitProb S (weakOrbitLift S hS x) j.val = (x j)^2 := by
  subst r
  exact symHitProb_orbEmbedGen hN x j

theorem weakStages_exit {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ}
    (hn : 80000 ≤ n) (hM : 1 ≤ 512*n) (room : 512*n < 1024*(n+1)) (rows : List WeakRow)
    (S : Finset (Fin (2^n))) (hS : S.card = 512) (x : Fin 513 → ℝ)
    (μ : Fin (2^(512*n))) (hμ : μ.val < 2^(512*n-1)) (σ : Store Var) :
    rmsVecQuad ((wp ((weakStages res n hM (weakTerminalRead res n 1024 512 (512*n) room) rows).compile
      qAssign (groverParallelMarkingOracle 1024 S))
      (fun τ ↦ ⌜τ res ≠ ((2^(512*n) : ℕ) : ℤ)⌝)) σ).1.1 (weakState S hS x μ) =
      (weakSuccessMass n rows x : ℂ) := by
  have hN : 2^12 ≤ (2:ℕ)^n := Nat.pow_le_pow_right (by decide) (by omega)
  rw [← weakPayoff_success hn]
  apply weakStages_payoff res hn hM _ S hS <;> try assumption
  intro y ν τ
  rw [weakTerminal_exit res room S hS (weakOrbitLift S hS y) ν τ,
    weak_full_prob S hS (by omega) y weakTop]

theorem weakStages_bad {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ}
    (hn : 80000 ≤ n) (hM : 1 ≤ 512*n) (room : 512*n < 1024*(n+1)) (rows : List WeakRow)
    (S : Finset (Fin (2^n))) (hS : S.card = 512) (x : Fin 513 → ℝ)
    (μ : Fin (2^(512*n))) (hμ : μ.val < 2^(512*n-1)) (σ : Store Var) :
    rmsVecQuad ((wp ((weakStages res n hM (weakTerminalRead res n 1024 512 (512*n) room) rows).compile
      qAssign (groverParallelMarkingOracle 1024 S))
      (fun τ ↦ ⌜τ res ≠ ((2^(512*n) : ℕ) : ℤ) ∧ decodeTargets n 512 (τ res) ≠ S⌝)) σ).1.1
        (weakState S hS x μ) = 0 := by
  rw [← weakPayoff_zero n rows x]
  apply weakStages_payoff res hn hM _ S hS <;> try assumption
  intro y ν τ
  exact weakTerminal_bad res room S hS (weakOrbitLift S hS y) ν τ

end QuantumComputation.Specs.DickeSol

#print axioms QuantumComputation.Specs.DickeSol.weakStages_exit
#print axioms QuantumComputation.Specs.DickeSol.weakStages_bad