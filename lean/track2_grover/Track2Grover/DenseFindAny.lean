import Track2Grover.FirstQuery
import Track2Grover.LowerAccounts
import Track2Grover.LowerOutputAverage

/-! Unconditional first-query and dense-instance lower bounds for all frozen dynamic circuits. -/
namespace Track2Grover.Dense
open Real Operator QProg ResourceCounting QuantumComputation.Specs
open Lower (Circuit Correct AvgBound finiteBound c program)
open scoped NNReal ENNReal

private theorem unit_input (w : ℕ) : ∃ Δ : CQState (Store Grover.Var) (2^w), Δ.trace = 1 := by
  classical
  let σ₀ : Store Grover.Var := fun _ ↦ 0
  let f (σ : Store Grover.Var) : PartialDensityOperator (Fin (2^w)) :=
    if σ = σ₀ then PartialDensityOperator.single 0 1 else 0
  have ht (σ) : (f σ).trace = if σ = σ₀ then 1 else 0 := by
    by_cases h : σ = σ₀ <;> simp [f, h, PartialDensityOperator.trace_single]
  have h : HasSum (fun σ ↦ (f σ).trace) 1 := by simp_rw [ht]; exact hasSum_ite_eq _ _
  exact ⟨⟨f, 1, h, le_rfl⟩, h.tsum_eq⟩

theorem first_query_lower_bound {n m w k : ℕ} {C : Circuit n m w} {q : ℝ}
    (hk : 0 < k) (hkN : k ≤ 2^n) (cor : Correct C k) (cost : AvgBound C k q) :
    1 - k / (2:ℝ)^n ≤ q := by
  classical
  obtain ⟨Δ, hΔ⟩ := unit_input w
  let δ := (interp (.qSet : QProg Grover.Var (2^w))).toStateFun Δ
  let out := (interp (FirstQuery.cut C)).toStateFun δ
  let L := groverTargetSets n k
  let θ (S : Finset (Fin (2^n))) : CQAssertion (Store Grover.Var) (2^w) :=
    fun σ ↦ ⌜OutputAverage.good S σ⌝
  obtain ⟨b, hb, hq⟩ := cost
  have hpoint (S) (hS : S ∈ L) : (1:ℝ) ≤ expect out (θ S) + b S := by
    let O := groverParallelMarkingOracle m S
    have hh := cor S hS Δ
    change expect Δ ⊤ ≤ expect ((interp (program C S)).toStateFun Δ) (θ S) at hh
    rw [expect_top, hΔ] at hh
    have hcost := hb S hS Δ
    simp only [Lower.program, expectedCost_qSeq, expectedCost_qSet, CostModel.ofEmbeddedOracle,
      Nat.cast_zero, mul_zero, zero_add, hΔ, ENNReal.coe_one, one_mul] at hcost
    have hl := FirstQuery.cut_loss O C δ (θ S)
    rw [FirstQuery.mass_wp, FirstQuery.mass_wp] at hl
    have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (expect out (θ S)) + b S := by
      apply le_trans _ (hl.trans (add_le_add le_rfl hcost))
      simpa [FirstQuery.mass, Lower.program, O, δ] using ENNReal.ofReal_le_ofReal hh
    have hpos : 0 ≤ expect out (θ S) := by
      simpa using (expect_mono (Δ₁ := out) (Δ₂ := out) le_rfl (bot_le : ⊥ ≤ θ S))
    have hre := ENNReal.toReal_mono (by finiteness) he
    simpa [ENNReal.toReal_add, ENNReal.toReal_ofReal hpos] using hre
  have hcard : 0 < L.card := Finset.card_pos.mpr (by
    apply Finset.powersetCard_nonempty_of_le
    simpa using hkN)
  have hcr : (0:ℝ) < L.card := by exact_mod_cast hcard
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib] at hsum
  have hout : out.trace ≤ 1 := out.trace_le_one
  have hav := OutputAverage.shared_output (n := n) hk out
  change (2:ℝ)^n * (∑ S ∈ L, expect out (θ S)) ≤ (L.card:ℝ)*k*out.trace at hav
  have hav' : (2:ℝ)^n * (∑ S ∈ L, expect out (θ S)) ≤ (L.card:ℝ)*k := by
    apply hav.trans
    exact mul_le_of_le_one_right (by positivity) (by exact_mod_cast hout)
  change (∑ S ∈ L, (b S:ℝ)) / L.card ≤ q at hq
  have hbr := (div_le_iff₀ hcr).mp hq
  have hN : 0 < (2:ℝ)^n := by positivity
  apply (le_of_mul_le_mul_right _ hcr)
  apply (le_of_mul_le_mul_left _ hN)
  have hsum' := mul_le_mul_of_nonneg_left hsum hN.le
  have hb' := mul_le_mul_of_nonneg_left hbr hN.le
  field_simp [ne_of_gt hN]
  nlinarith

/-- The requested finite bound holds for all programs once the rotation allowance is at
least the initial potential. In particular this includes all mk/N ≥ 1/2. -/
theorem finite_of_large_angle {n m w k : ℕ} {C : Circuit n m w} {q : ℝ}
    (hk : 0 < k) (hkN : k ≤ 2^n) (cor : Correct C k) (cost : AvgBound C k q)
    (hd : c ≤ 2*arcsin (√((m:ℝ)*k/2^n))) : finiteBound n m k ≤ q := by
  apply le_trans _ (first_query_lower_bound hk hkN cor cost)
  have hc : 0 < c := by unfold c; positivity
  have h : 0 ≤ 1-(k:ℝ)/2^n := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast hkN
  unfold finiteBound
  rw [div_le_iff₀ (hc.trans_le hd)]
  simpa only [mul_comm c] using mul_le_mul_of_nonneg_left hd h

#print axioms first_query_lower_bound
#print axioms finite_of_large_angle

theorem finite_of_dense {n m w k : ℕ} {C : Circuit n m w} {q : ℝ}
    (hk : 0 < k) (hkN : k ≤ 2^n) (hd : 2^n ≤ 2*m*k)
    (cor : Correct C k) (cost : AvgBound C k q) : finiteBound n m k ≤ q := by
  apply finite_of_large_angle hk hkN cor cost
  have hp : (1/2:ℝ) ≤ (m:ℝ)*k/2^n := by
    rw [le_div_iff₀ (by positivity)]
    have H : (2:ℝ)^n ≤ 2*m*k := by exact_mod_cast hd
    linarith
  have hh : sin (π/4) ≤ √((m:ℝ)*k/2^n) := by
    rw [sin_pi_div_four]
    apply le_sqrt_of_sq_le
    nlinarith [sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hθ := arcsin_le_arcsin hh
  rw [arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])] at hθ
  unfold c
  linarith [two_le_pi]

#print axioms finite_of_dense
end Track2Grover.Dense
