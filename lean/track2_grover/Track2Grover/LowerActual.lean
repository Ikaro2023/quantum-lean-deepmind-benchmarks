import Track2Grover.CoupledOracle
import Track2Grover.CoupledLimit
import Track2Grover.LowerScoreBridge

/-! Direct bound on the actual uniform mean of the frozen expectedCost, including
infinite cost. The initial classical store is arbitrary and independent of the input. -/
namespace Track2Grover.Actual
open Operator ResourceCounting QuantumComputation.Specs Real Finset
open CoupledActions CoupledLabels CoupledPathBridge Lower Track2Grover.Path
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable def mean {n m w : ℕ} (C : Circuit n m w) (k : ℕ) (σ : Store Grover.Var) : ℝ≥0∞ :=
  (∑ S ∈ groverTargetSets n k, expectedCost (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) (program C S) (seed w σ)) / (groverTargetSets n k).card

/-- The target lower bound for the actual expected cost averaged over the uniform
size-k hidden set. There is no external resource bound in the hypotheses. -/
theorem mean_lower_bound {n m w k : ℕ} {C : Circuit n m w} (hm : 0<m) (hk : 0<k)
    (hkN : k ≤ 2^n) (cor : Correct C k) (σ : Store Grover.Var) :
    ENNReal.ofReal (finiteBound n m k) ≤ mean C k σ := by
  classical
  let L := groverTargetSets n k
  let e (S : Finset (Fin (2^n))) := expectedCost (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) (program C S) (seed w σ)
  change ENNReal.ofReal (finiteBound n m k) ≤ (∑ S ∈ L, e S) / L.card
  by_cases hi : ∑ S ∈ L, e S = ∞
  · rw [hi, ENNReal.top_div_of_ne_top (by finiteness)]
    exact le_top
  have hcard : 0<L.card := Finset.card_pos.mpr (by
    apply Finset.powersetCard_nonempty_of_le
    simpa using hkN)
  have hcard' : (0:ℝ≥0∞)<L.card := by exact_mod_cast hcard
  have he (S) (hS : S ∈ L) : e S ≠ ∞ := ENNReal.sum_ne_top.mp hi S hS
  let p : ℝ := (m:ℝ)*k/2^n
  let b := min p 1
  have hp : 0 < p := by unfold p; positivity
  have hangle : arcsin (√b) = arcsin (√p) := by
    by_cases h : p ≤ 1
    · simp [b,h]
    · have hs : 1 ≤ √p := Real.one_le_sqrt.mpr (le_of_not_ge h)
      simp [b, min_eq_right (le_of_not_ge h), arcsin_of_one_le hs]
  apply (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mpr
  rw [ENNReal.toReal_div, ENNReal.toReal_sum he]
  apply CoupledLimit.of_seed_semantics hk hkN σ b (lt_min hp (by norm_num))
    (min_le_right ..) hangle cor
  · refine ⟨fun S => (e S).toNNReal, fun S hS => ?_, ?_⟩
    · rw [ENNReal.coe_toNNReal (he S hS)]
    · simp [L, ENNReal.coe_toNNReal_eq_toReal]
  · exact fun r S => Physical.act_involution r S.1
  · intro r y
    by_cases h : p ≤ 1
    · simpa [b, min_eq_left h, p] using Physical.compressed hk r y
    · rw [show b = 1 from min_eq_right (le_of_not_ge h)]
      have hterm (S : Labels n k) : -(‖y‖^2) ≤ ⟪y, act
          (r.embedUnitary (groverParallelMarkingOracle m S.1)) y⟫ := by
        have hh := real_inner_le_norm (-y) (act (r.embedUnitary (groverParallelMarkingOracle m S.1)) y)
        rw [inner_neg_left, norm_neg, LinearIsometry.norm_map] at hh
        nlinarith
      rw [show (1:ℝ)-2*1 = -1 by norm_num]
      simpa [sum_const, card_univ, nsmul_eq_mul] using sum_le_sum (s := univ) (fun S _ => hterm S)
  · exact fun O F τ g _ => score_prob O F τ g
  · exact fun O F τ => score_calls_le_cost O F τ

#print axioms mean_lower_bound
end Track2Grover.Actual
