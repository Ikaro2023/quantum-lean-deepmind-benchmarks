import Track2Grover.LowerPathEffects

namespace Track2Grover.Path
open Operator Matrix
open scoped Matrix
variable {V : Type} [DecidableEq V] {w h : ℕ}
abbrev Mat (w : ℕ) := Matrix (Fin (2^w)) (Fin (2^w)) ℂ
noncomputable def quad (A : Mat w) (ψ : Vec w) : ℝ := (A*pureStateDensity ψ).trace.re
noncomputable def value (θ : CQAssertion (Store V) (2^w)) (σ : Store V) (ψ : Vec w) : ℝ :=
  quad (θ σ).1.mat ψ
noncomputable def values (X : Effects V w) (σ : Store V) (ψ : Vec w) : ℝ :=
  (X.map (fun θ => value θ σ ψ)).sum

theorem quad_conj (A M : Mat w) (ψ : Vec w) : quad (Mᴴ*A*M) ψ = quad A (M *ᵥ ψ) := by
  unfold quad
  rw [← matrix_conj_pureStateDensity]
  congr 1
  rw [show Mᴴ*A*M*pureStateDensity ψ = Mᴴ*(A*(M*pureStateDensity ψ)) by simp [mul_assoc],
    Matrix.trace_mul_comm Mᴴ, mul_assoc, mul_assoc]

omit [DecidableEq V] in
theorem value_top (σ : Store V) (ψ : Vec w) : value ⊤ σ ψ = energy ψ := by
  change ((1 * pureStateDensity ψ).trace).re = _
  simp [trace_pureStateDensity, energy]

omit [DecidableEq V] in
private theorem value_bot (σ : Store V) (ψ : Vec w) : value ⊥ σ ψ = 0 := by
  change ((0 * pureStateDensity ψ).trace).re = _
  simp

private theorem unitary_values (U : Unitary (2^w)) (X : Effects V w) (σ : Store V) (ψ : Vec w) :
    values (X.map (wp (.qAssign U))) σ ψ = values X σ (U.1 *ᵥ ψ) := by
  induction X with
  | nil => rfl
  | cons θ X ih =>
    change value (wp (.qAssign U) θ) σ ψ + values (X.map (wp (.qAssign U))) σ ψ =
      value θ σ (U.1 *ᵥ ψ) + values X σ (U.1 *ᵥ ψ)
    rw [← ih]
    congr 1
    unfold value
    rw [wp_qAssign, CQAssertion.qAssign_apply_mat]
    exact quad_conj (θ σ).1.mat U.1 ψ

private theorem measure_value {k : ℕ} (r : QRegister k w) (x : V)
    (θ : CQAssertion (Store V) (2^w)) (σ : Store V) (ψ : Vec w) :
    value (wp (QProg.measureRegister x r) θ) σ ψ =
      ∑ i, value θ (σ.subst x (fun _ => (i.val:ℤ))) ((r.basisOutcomeProjector i) *ᵥ ψ) := by
  let M := r.basisOutcomeProjector
  have hm : (wp (QProg.measureRegister x r) θ σ).1.mat =
      ∑ i, (M i)ᴴ * (θ (σ.subst x (fun _ => (i.val:ℤ)))).1.mat * M i := by
    simp only [QProg.measureRegister, wp, CQAssertion.qMeasure_coe,
      HermitianMat.mat_finset_sum, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose]
    rfl
  unfold value
  rw [hm]
  calc
    _ = ∑ i, quad ((M i)ᴴ * (θ (σ.subst x (fun _ => (i.val:ℤ)))).1.mat * M i) ψ := by
      simp [quad, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    _ = _ := Finset.sum_congr rfl fun i _ => quad_conj _ _ _

private theorem measure_values {k : ℕ} (r : QRegister k w) (x : V)
    (X : Effects V w) (σ : Store V) (ψ : Vec w) :
    values (X.map (wp (QProg.measureRegister x r))) σ ψ =
      ∑ i, values X (σ.subst x (fun _ => (i.val:ℤ))) ((r.basisOutcomeProjector i) *ᵥ ψ) := by
  induction X with
  | nil => simp [values]
  | cons θ X ih =>
    change value _ σ ψ + values _ σ ψ =
      ∑ i, (value θ _ ((r.basisOutcomeProjector i) *ᵥ ψ) + values X _ _)
    rw [Finset.sum_add_distrib, measure_value, ih]

omit [DecidableEq V] in
private theorem mask_values (g : Store V → Prop) [DecidablePred g]
    (X : Effects V w) (σ : Store V) (ψ : Vec w) :
    values (X.map (mask g)) σ ψ = if g σ then values X σ ψ else 0 := by
  induction X with
  | nil => simp [values]
  | cons θ X ih =>
    change value (mask g θ) σ ψ + values (X.map (mask g)) σ ψ =
      if g σ then value θ σ ψ + values X σ ψ else 0
    rw [ih]
    by_cases hg : g σ
    · simp [value, mask, hg]
    · simpa [value, mask, hg] using value_bot σ ψ

/-- The path score for every finite control-flow tree equals the pullback of its list
of bounded quantum effects, even after joins and overwriting measurements. -/
theorem score_build (ask : Bool) (O : Unitary (2^h)) (C : Finite V w h)
    (H : Store V → Vec w → ℝ) (K : Store V → Tree V w h) (X : Effects V w)
    (hk : ∀ σ ψ, score O (if ask then 1 else 0) (fun _ => 0) H (K σ) ψ = values X σ ψ)
    (σ : Store V) (ψ : Vec w) :
    score O (if ask then 1 else 0) (fun _ => 0) H (build C σ K) ψ =
      values (tests ask O C X) σ ψ := by
  induction C generalizing σ ψ K X with
  | skip => exact hk ..
  | abort => simp [build, score, tests, values]
  | step U => simpa [build, score, tests, unitary_values] using hk σ (U.1 *ᵥ ψ)
  | measure x r =>
    simp only [build, score, tests, measure_values]
    exact Finset.sum_congr rfl fun i _ => hk .. 
  | oracle r =>
    simp only [build, score, hk, tests]
    cases ask
    · simp [unitary_values]
    · change 1 * energy ψ + _ = value ⊤ σ ψ + values (X.map (wp (.qAssign (r.embedUnitary O)))) σ ψ
      rw [value_top, unitary_values, one_mul]
  | seq C D ihC ihD =>
    exact ihC (fun τ => build D τ K) _ (fun τ φ => ihD K X hk τ φ) σ ψ
  | branch g C D ihC ihD =>
    simp only [build, tests, show ∀ (A B : Effects V w), values (A++B) σ ψ =
      values A σ ψ + values B σ ψ by simp [values], mask_values]
    by_cases hg : g σ
    · simpa [hg] using ihC K X hk σ ψ
    · simpa [hg] using ihD K X hk σ ψ

theorem score_tree (ask : Bool) (O : Unitary (2^h)) (C : Finite V w h)
    (X : Effects V w) (σ : Store V) (ψ : Vec w) :
    score O (if ask then 1 else 0) (fun _ => 0) (values X) (build C σ Tree.halt) ψ =
      values (tests ask O C X) σ ψ := score_build ask O C _ _ X (fun _ _ => rfl) σ ψ

#print axioms score_tree
end Track2Grover.Path
