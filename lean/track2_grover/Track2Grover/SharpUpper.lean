import QuantumComputationSpecs.Algorithms.Grover
import Track2Grover.Any.FindAny
import Track2Grover.LowerAccounts

namespace Track2Grover.Upper
open QuantumComputation.Specs Real Operator
open scoped NNRat

/-- On each dyadic cell the same circuit realizes every strict upper approximation to
the sharp relative coefficient. The ratio is allowed to be real. -/
theorem arbitrarily_close {m k : ℕ} (hm : m ∈ groverGrid) (hk : k ∈ groverGrid)
    (R : ℝ) (hR : 1/2 + 1/π < R) :
    ∃ (w : ℕ → ℕ) (C : ∀ n, Lower.Circuit n m (w n)),
      (∀ n, 1 ≤ n → k ≤ 2^n → Lower.Correct (C n) k) ∧
      ∃ n₀, ∀ n ≥ n₀, k ≤ 2^n → Lower.AvgBound (C n) k (R * vanillaFindAnyCost n m k) := by
  have hcell : GroverSolution.FindAny.cells m k = true := by
    simp only [GroverSolution.FindAny.cells, GroverSolution.gridCells, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨hm, hk⟩
  refine ⟨fun n ↦ GroverSolution.FindAny.qubits n m k,
    fun n ↦ GroverSolution.FindAny.circuit Grover.Var.res n m k, ?_, ?_⟩
  · intro n hn hkn S hS
    exact GroverSolution.FindAny.correctness Grover.Var.res hn hcell hkn hS
  apply GroverSolution.FindAny.rel_cost_of_margin Grover.Var.res hcell R
  have h := mul_lt_mul_of_pos_right hR (show 0 < π/4 by positivity)
  have he : (1/2+1/π)*(π/4) = π/8+1/4 := by field_simp; ring
  linarith

#print axioms arbitrarily_close
end Track2Grover.Upper
