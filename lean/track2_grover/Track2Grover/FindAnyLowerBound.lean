import Track2Grover.UniversalFindAny
import Track2Grover.LowerActual
import Track2Grover.SharpUpper

/-! Sharp parallel FindAny bounds in the frozen model. A single circuit is fixed before
the hidden set is chosen. Its register layout, workspace and stopping time are unrestricted. -/
namespace Track2Grover.FindAnyLowerBound
open Real Filter Operator ResourceCounting QuantumComputation.Specs
open scoped NNRat

open QProg.Notation in
/-- An unconditional finite-instance lower bound on every semantic average cost certificate. -/
theorem finite {n m k w : ℕ}
    (C : OracleDynamicCircuit (Unitary (2^w)) Grover.Var w ((n+1)*m))
    (hm : 0 < m) (hk : 0 < k) (hkN : k ≤ 2^n)
    (correct : ∀ S ∈ groverTargetSets n k,
      ⦃ ⊤ ⦄ (qset ;; C.compile QProg.qAssign (groverParallelMarkingOracle m S))
      ⦃ fun σ ↦ ⌜∃ x ∈ S, σ Grover.Var.res = x.val⌝ ⦄)
    {q : ℝ} (cost : AvgOracleCostBound k
      (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      (fun S ↦ qset ;; C.compile QProg.qAssign (groverParallelMarkingOracle m S)) q) :
    ((π/4 + 1/2) * (1 - k/(2:ℝ)^n)) /
      (2 * arcsin (√((m:ℝ)*k/(2:ℝ)^n))) ≤ q :=
  Universal.finite hm hk hkN correct cost

open QProg.Notation in
/-- Expected oracle rounds, averaged over the hidden set for any fixed initial
classical store. Infinite expected cost is included in the extended-real comparison. -/
theorem actual_expected_rounds {n m k w : ℕ}
    (C : OracleDynamicCircuit (Unitary (2^w)) Grover.Var w ((n+1)*m))
    (hm : 0 < m) (hk : 0 < k) (hkN : k ≤ 2^n)
    (correct : Lower.Correct C k) (σ : Store Grover.Var) :
    ENNReal.ofReal (((π/4 + 1/2) * (1 - k/(2:ℝ)^n)) /
      (2 * arcsin (√((m:ℝ)*k/(2:ℝ)^n)))) ≤
    (∑ S ∈ groverTargetSets n k, expectedCost
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      (qset ;; C.compile QProg.qAssign (groverParallelMarkingOracle m S))
      (Track2Grover.Path.seed w σ)) / (groverTargetSets n k).card :=
  Actual.mean_lower_bound hm hk hkN correct σ

/-- Feasible eventual relative costs as the search space grows with fixed (m,k). -/
def Feasible (m k : ℕ) (R : ℝ) : Prop :=
  ∃ (w : ℕ → ℕ) (C : ∀ n, Lower.Circuit n m (w n)),
    (∀ n, 1 ≤ n → k ≤ 2^n → Lower.Correct (C n) k) ∧
    ∃ n₀, ∀ n ≥ n₀, k ≤ 2^n → Lower.AvgBound (C n) k (R * vanillaFindAnyCost n m k)

theorem asymptotic_real {m k : ℕ} (hm : 0 < m) (hk : 0 < k) {R : ℝ}
    (hR : Feasible m k R) : 1/2 + 1/π ≤ R := by
  obtain ⟨w,C,correct,n₀,upper⟩ := hR
  apply le_of_tendsto (Lower.tendsto_ratio m k hm hk)
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop 1,
    eventually_ge_atTop k] with n hn hn1 hnk
  have hkn : k ≤ 2^n := Nat.le_trans hnk (Nat.lt_two_pow_self (n := n)).le
  have h := Universal.finite (C := C n) hm hk hkn (correct n hn1 hkn) (upper n hn hkn)
  exact (div_le_iff₀ (by positivity)).mpr h

/-- No positive dyadic benchmark cell admits a submitted rational below the sharp boundary. -/
theorem no_smaller_rational {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (R : ℚ≥0)
    (h : (R:ℝ) < 1/2 + 1/π) : ¬ Feasible m k R := fun f ↦
  (not_lt_of_ge (asymptotic_real hm hk f)) h

/-- The matching upper and lower bounds determine the exact greatest lower bound on
each frozen grid cell. Arbitrarily close upper approximations use the same circuit. -/
theorem exact_infimum {m k : ℕ} (hm : m ∈ groverGrid) (hk : k ∈ groverGrid) :
    IsGLB {R : ℝ | Feasible m k R} (1/2 + 1/π) := by
  refine ⟨fun R hR ↦ asymptotic_real (GroverSolution.one_le_of_mem_groverGrid hm)
    (GroverSolution.one_le_of_mem_groverGrid hk) hR, ?_⟩
  intro x hx
  by_contra! h
  obtain ⟨a,ha,hax⟩ := exists_between h
  exact (not_le_of_gt hax) (hx (Upper.arbitrarily_close hm hk a ha))

#check @finite
#check @actual_expected_rounds
#check @asymptotic_real
#check @no_smaller_rational
#check @exact_infimum
#print axioms finite
#print axioms actual_expected_rounds
#print axioms asymptotic_real
#print axioms no_smaller_rational
#print axioms exact_infimum
end Track2Grover.FindAnyLowerBound
