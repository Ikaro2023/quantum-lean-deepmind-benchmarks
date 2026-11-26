import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The scalar normalization and cumulative accounting underlying the proposed lower bound. -/
namespace Track2Grover.Lower
open Real Filter
open scoped Topology BigOperators

noncomputable def c : ℝ := π / 4 + 1 / 2
noncomputable def finiteBound (n m k : ℕ) : ℝ :=
  c * (1 - k / (2:ℝ)^n) / (2 * arcsin (√((m:ℝ) * k / 2^n)))

/-- Passage from the finite angle to the exact constant at every fixed positive cell. -/
theorem tendsto_ratio (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    Tendsto (fun n : ℕ => finiteBound n m k /
      ((π / 4) * √((2:ℝ)^n / ((m:ℝ) * k)))) atTop (𝓝 (1/2 + 1/π)) := by
  let a : ℝ := (m:ℝ) * k
  have ha : 0 < a := by dsimp [a]; positivity
  let x (n : ℕ) : ℝ := √(a / 2 ^ n)
  have hx (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hp : Tendsto (fun n : ℕ => ((2:ℝ)^n)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2:ℝ)⁻¹)
        (by norm_num))
  have hx0 : Tendsto x atTop (𝓝 0) := by
    simpa [x, div_eq_mul_inv] using (tendsto_const_nhds (x := a) |>.mul hp).sqrt
  have hxne : Tendsto x atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx0, .of_forall fun n => (hx n).ne'⟩
  have hder : HasDerivAt arcsin 1 0 := by
    simpa using (hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num))
  have hangle : Tendsto (fun n => arcsin (x n) / x n) atTop (𝓝 1) := by
    simpa [Function.comp_def, slope_def_field] using hder.tendsto_slope.comp hxne
  have hfrac : Tendsto (fun n : ℕ => (k:ℝ)/2^n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (k:ℝ))).mul hp
  have hlim := ((tendsto_const_nhds (x := 2*c/π)).mul
    ((tendsto_const_nhds (x := (1:ℝ))).sub hfrac)).div hangle (by norm_num)
  have hconst : 2*c/π * (1-0) / 1 = 1/2 + 1/π := by
    unfold c
    field_simp
    ring
  rw [hconst] at hlim
  refine hlim.congr fun n => ?_
  have hrec : √((2:ℝ)^n / a) = (x n)⁻¹ := by
    rw [show (2:ℝ)^n / a = (a / 2^n)⁻¹ by rw [inv_div], Real.sqrt_inv]
  change 2*c/π * (1 - (k:ℝ)/2^n) / (arcsin (x n) / x n) =
    (c * (1 - (k:ℝ)/2^n) / (2 * arcsin (x n))) / ((π / 4) * √((2:ℝ)^n / a))
  rw [hrec]
  ring_nf

/-- A finite telescope with separate charges for query survival and discarded hidden mass. -/
theorem telescope (potential paid discarded : ℕ → ℝ) (v : ℝ)
    (hstep : ∀ t, potential t ≤ potential (t+1) + v * paid t + c * discarded t)
    (T : ℕ) : potential 0 ≤ potential T +
      v * ∑ t ∈ Finset.range T, paid t + c * ∑ t ∈ Finset.range T, discarded t := by
  induction T with
  | zero => simp
  | succ T ih =>
    simp only [Finset.sum_range_succ, mul_add]
    linarith [hstep T]

/-- Telescoping remains sound with infinitely many possible query rounds. The discarded
mass budget is taken separately at every finite cutoff, so its convergence is unnecessary. -/
theorem limit_accounting (potential paid discarded : ℕ → ℝ) (v q hit : ℝ)
    (hv : 0 < v) (hinit : potential 0 = c)
    (hstep : ∀ t, potential t ≤ potential (t+1) + v * paid t + c * discarded t)
    (hvanish : Tendsto potential atTop (𝓝 0))
    (hcost : ∀ T, ∑ t ∈ Finset.range T, paid t ≤ q)
    (hhalt : ∀ T, ∑ t ∈ Finset.range T, discarded t ≤ hit) :
    c * (1-hit) / v ≤ q := by
  have hc : 0 < c := by unfold c; positivity
  have hfinite (T : ℕ) : c ≤ potential T + v*q + c*hit := by
    have h := telescope potential paid discarded v hstep T
    rw [hinit] at h
    linarith [mul_le_mul_of_nonneg_left (hcost T) hv.le,
      mul_le_mul_of_nonneg_left (hhalt T) hc.le]
  have h := ge_of_tendsto'
    ((hvanish.add_const (v*q)).add_const (c*hit)) hfinite
  apply (div_le_iff₀ hv).2
  linarith

#print axioms tendsto_ratio
#print axioms telescope
#print axioms limit_accounting
end Track2Grover.Lower
