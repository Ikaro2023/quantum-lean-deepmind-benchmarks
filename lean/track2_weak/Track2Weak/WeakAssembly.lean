module

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.Circuits.DynamicCircuit

/-! Independent restart for a complete-batch search. The first attempt is unconditional, so
the value in the input store cannot be mistaken for a previously measured success. -/

@[expose] public section

namespace Track2Weak

open Operator ResourceCounting QProg.Notation
open scoped NNReal ENNReal QHLExpectation

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- Run a fresh attempt and repeat it whenever its measured result requests a restart. -/
def restartCircuit {Step : Type} {Q w : ℕ} (guard : Store Var → Prop) [DecidablePred guard]
    (attempt : OracleDynamicCircuit Step Var Q w) : OracleDynamicCircuit Step Var Q w :=
  .seq attempt (.qWhile guard attempt)

/-- The physical costs, success probability, and soundness needed of one reset-and-measure
attempt. A successful run must output a store satisfying `good`. -/
structure AttemptBound (model : CostModel d) (attempt : QProg Var d)
    (guard good : Store Var → Prop) (p T : ℝ≥0) : Prop where
  positive : 0 < p
  prob_le_one : p ≤ 1
  lossless : QProg.Lossless attempt
  cost : CostBound model attempt T
  exit : wp attempt (fun σ ↦ ⌜¬ guard σ⌝) = .ofProb p
  noFalseSuccess : wp attempt (fun σ ↦ ⌜¬ guard σ ∧ ¬good σ⌝) = ⊥

variable {model : CostModel d} {attempt : QProg Var d} {guard good : Store Var → Prop}
  [DecidablePred guard] {p T : ℝ≥0}

private theorem loop_bad_le (h : AttemptBound model attempt guard good p T) :
    wp (.qWhile guard attempt) (fun σ ↦ ⌜¬good σ⌝) ≤ (fun σ ↦ ⌜¬guard σ ∧ ¬good σ⌝) := by
  rw [wp_qWhile]
  apply OmegaCompletePartialOrder.ωSup_le
  intro n
  change whileRecWP (wp attempt) guard n (fun σ ↦ ⌜¬good σ⌝) ≤ _
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    intro σ
    by_cases hg : guard σ
    · have hb := wp_mono attempt ih σ
      rw [h.noFalseSuccess] at hb
      simpa [whileRecWP, hg] using hb
    · simp [whileRecWP, hg]

/-- Exactness of the returned result after independent restart, for any initial classical
and quantum state. -/
theorem restart_correct (h : AttemptBound model attempt guard good p T) :
    ⦃ ⊤ ⦄ (attempt ;; .qWhile guard attempt) ⦃ fun σ ↦ ⌜good σ⌝ ⦄ := by
  classical
  have hloop : QProg.Lossless (.qWhile guard attempt) := h.lossless.qWhile fun state ↦ by
    rw [expectedIterations_eq_of_wp_eq h.prob_le_one h.lossless h.exit]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by simpa using h.positive.ne')
  let prog := attempt ;; .qWhile guard attempt
  have hbad : wp prog (fun σ ↦ ⌜¬good σ⌝) = ⊥ := by
    apply le_antisymm _ bot_le
    exact (wp_mono attempt (loop_bad_le h)).trans_eq h.noFalseSuccess
  intro Δ
  let out := (interp prog).toStateFun Δ
  have hz := expect_wp prog Δ (fun σ ↦ ⌜¬good σ⌝)
  rw [hbad, expect_bot, expect_ofProp] at hz
  have hzero : (out.restrict (fun σ ↦ ¬good σ)).trace = 0 := by exact_mod_cast hz.symm
  have hpart := out.trace_restrict_add_trace_restrict_not good
  rw [hzero, add_zero] at hpart
  rw [expect_top, expect_ofProp]
  exact_mod_cast (h.lossless.seq hloop).trace_eq Δ |>.symm.trans hpart.symm |>.le

/-- The first unconditional attempt plus the geometrically decreasing remaining query
cost is at most the one-attempt expectation divided by its success probability. -/
theorem restart_cost (h : AttemptBound model attempt guard good p T) :
    CostBound model (attempt ;; .qWhile guard attempt) (T / p) := by
  intro Δ
  rw [expectedCost_qSeq]
  let out := (interp attempt).toStateFun Δ
  have hiter := expectedCost_qWhile_le h.cost guard out
  rw [expectedIterations_eq_of_wp_eq h.prob_le_one h.lossless h.exit] at hiter
  have hfail := trace_restrict_interp_of_wp_eq h.prob_le_one h.lossless h.exit Δ
  change (out.restrict guard).trace = _ at hfail
  rw [hfail, ENNReal.coe_mul, ← ENNReal.coe_inv h.positive.ne'] at hiter
  refine (add_le_add (h.cost Δ) hiter).trans_eq ?_
  norm_cast
  rw [div_eq_mul_inv]
  have hp : p * p⁻¹ = 1 := mul_inv_cancel₀ h.positive.ne'
  calc Δ.trace * T + (1 - p) * Δ.trace * p⁻¹ * T =
      Δ.trace * ((p * p⁻¹) * T + (1 - p) * p⁻¹ * T) := by rw [hp]; ring
    _ = Δ.trace * (((1 - p) + p) * p⁻¹ * T) := by ring
    _ = Δ.trace * (T * p⁻¹) := by rw [tsub_add_cancel_of_le h.prob_le_one]; ring

end Track2Weak

#print axioms Track2Weak.restart_correct
#print axioms Track2Weak.restart_cost
