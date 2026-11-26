import Track2Grover.CoupledOracle
import Track2Grover.CoupledLimit
import Track2Grover.DenseFindAny
import Track2Grover.LowerScoreBridge

/-! Finite-size universal lower bound in the frozen adaptive parallel-oracle model. -/
namespace Track2Grover.Universal

theorem finite {n m k w : ℕ} {C : Lower.Circuit n m w} {bound : ℝ}
    (hm : 0 < m) (hk : 0 < k) (hkN : k ≤ 2^n)
    (cor : Lower.Correct C k) (cost : Lower.AvgBound C k bound) :
    Lower.finiteBound n m k ≤ bound := by
  by_cases hd : 2^n ≤ 2*m*k
  · exact Dense.finite_of_dense hk hkN hd cor cost
  · have hs : m*k ≤ 2^n := by nlinarith
    exact CoupledLimit.of_score_semantics hm hk hkN hs cor cost
      (fun r S ↦ Physical.act_involution r S.1)
      (fun r x ↦ Physical.compressed hk r x)
      (fun O F σ g _ ↦ Path.score_prob O F σ g)
      (fun O F σ ↦ Path.score_calls_le_cost O F σ)

#print axioms finite
end Track2Grover.Universal
