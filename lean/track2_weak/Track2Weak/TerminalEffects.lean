module
public import Track2Weak.TerminalRead

@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Matrix
open scoped Matrix

theorem weakPureEffect {Var : Type} {d : ℕ} (res : Var) (P : ℤ → Prop) [DecidablePred P]
    (τ : Store Var) :
    ((fun σ : Store Var ↦ (⌜P (σ res)⌝ : Observable (Fin d))) τ).1.1 =
      (if P (τ res) then (1 : ℂ) else 0) • (1 : Operator d) := by
  by_cases hp : P (τ res) <;> simp [hp]

theorem weakTerminal_exit {Var : Type} [DecidableEq Var] (res : Var) {n m k M : ℕ}
    (room : k*n < m*(n+1)) (S : Finset (Fin (2^n))) (hS : S.card = k)
    (v : SymSubset (2^n) m → ℝ) (μ : Fin (2^M)) (σ : Store Var) :
    rmsVecQuad ((wp ((weakTerminalRead res n m k M room).compile QProg.qAssign
      (groverParallelMarkingOracle m S)) (fun τ ↦ ⌜τ res ≠ ((2^(k*n) : ℕ) : ℤ)⌝)) σ).1.1
      (workMemState (liftSymVec n m v) (Pi.single μ 1)) = (symHitProb S v k : ℂ) := by
  classical
  let P (t : ℤ) := t ≠ ((2^(k*n) : ℕ) : ℤ)
  rw [weakTerminalRead_quadratic res room S v μ (fun t ↦ if P t then 1 else 0) _
    (weakPureEffect res P)]
  simp only [symHitProb, Complex.ofReal_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  have h := (weakReadCode_spec room S hS E).1
  dsimp only [P]
  by_cases he : (E.1 ∩ S).card = k
  · rw [ite_eq_left (show (Int.ofNat _ : ℤ) ≠ ((2^(k*n) : ℕ) : ℤ) from
      fun hh ↦ h.mpr he (Int.ofNat.inj hh)), ite_eq_left he, mul_one]
    norm_cast
  · have hno : ¬ (Int.ofNat (weakReadCode n m k room
        (parallelMarkPerm n m S (subsetWorkIdx n m E))).val ≠ ((2^(k*n) : ℕ) : ℤ)) :=
      fun hh ↦ he (h.mp (fun eq ↦ hh (congrArg Int.ofNat eq)))
    rw [ite_eq_right hno, ite_eq_right he, mul_zero]
    norm_num

theorem weakTerminal_bad {Var : Type} [DecidableEq Var] (res : Var) {n m k M : ℕ}
    (room : k*n < m*(n+1)) (S : Finset (Fin (2^n))) (hS : S.card = k)
    (v : SymSubset (2^n) m → ℝ) (μ : Fin (2^M)) (σ : Store Var) :
    rmsVecQuad ((wp ((weakTerminalRead res n m k M room).compile QProg.qAssign
      (groverParallelMarkingOracle m S)) (fun τ ↦
        ⌜τ res ≠ ((2^(k*n) : ℕ) : ℤ) ∧ decodeTargets n k (τ res) ≠ S⌝)) σ).1.1
      (workMemState (liftSymVec n m v) (Pi.single μ 1)) = 0 := by
  classical
  let P (t : ℤ) := t ≠ ((2^(k*n) : ℕ) : ℤ) ∧ decodeTargets n k t ≠ S
  rw [weakTerminalRead_quadratic res room S v μ (fun t ↦ if P t then 1 else 0) _
    (weakPureEffect res P)]
  apply Finset.sum_eq_zero
  intro E _
  have h := (weakReadCode_spec room S hS E).2
  have hf : ¬ P _ := fun ⟨hc, hb⟩ ↦ hb (h (fun he ↦ hc (congrArg Int.ofNat he)))
  rw [ite_eq_right hf, mul_zero]

end QuantumComputation.Specs.DickeSol
