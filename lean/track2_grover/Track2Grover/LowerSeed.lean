import Track2Grover.LowerPath

namespace Track2Grover.Path
open Operator Matrix
open scoped Matrix RealInnerProductSpace NNReal
variable {V : Type} {w : ℕ}

/-- A normalized CQ input whose classical store is fixed. -/
noncomputable def seed (w : ℕ) (σ : Store V) : CQState (Store V) (2^w) := by
  classical
  let f (τ : Store V) : PartialDensityOperator (Fin (2^w)) :=
    if τ = σ then PartialDensityOperator.single 0 1 else 0
  have ht (τ) : (f τ).trace = if τ = σ then 1 else 0 := by
    by_cases hh : τ = σ <;> simp [f, hh, PartialDensityOperator.trace_single]
  exact ⟨f, 1, by simp_rw [ht]; exact hasSum_ite_eq _ _, le_rfl⟩

theorem seed_trace (w : ℕ) (σ : Store V) : (seed w σ).trace = 1 := by
  classical
  rw [CQState.trace_eq_tsum]
  have ht (τ) : ((seed w σ) τ).trace = if τ = σ then 1 else 0 := by
    by_cases hh : τ = σ <;> simp [seed, hh, PartialDensityOperator.trace_single]
  simp_rw [ht]; simp

theorem seed_reset (w : ℕ) (σ : Store V) : (seed w σ).qSet = seed w σ := by
  classical
  apply Subtype.ext
  funext τ
  change PartialDensityOperator.single 0 _ = (seed w σ) τ
  by_cases hh : τ = σ
  · subst τ; simp [seed, PartialDensityOperator.trace_single]
  · simp [seed, hh]

theorem expect_seed (σ : Store V) (θ : CQAssertion (Store V) (2^w)) :
    expect (seed w σ) θ = ((θ σ).1.mat 0 0).re := by
  classical
  rw [expect_eq_tsum]
  have hs (τ : Store V) :
      inner ℝ (θ τ).1 ((seed w σ) τ).1 =
        if τ=σ then ((θ σ).1.mat 0 0).re else 0 := by
    by_cases h : τ=σ
    · subst τ
      simp [seed, HermitianMat.inner_eq_re_trace, PartialDensityOperator.single,
        Matrix.trace_mul_single]
    · simp [seed,h]
  simp_rw [hs]; simp

#print axioms seed_reset
#print axioms expect_seed
end Track2Grover.Path
