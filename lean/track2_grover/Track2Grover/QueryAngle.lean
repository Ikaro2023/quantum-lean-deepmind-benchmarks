import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-! Realify the live Hilbert space and measure its angle from the uniform-label subspace. -/
namespace Track2Grover.QueryAngle
open Real InnerProductGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

noncomputable def alpha (x : E) := arccos (‖K.starProjection x‖ / ‖x‖)

theorem alpha_eq_angle (x : E) : alpha K x = angle x (K.starProjection x) := by
  have hi := K.starProjection_inner_eq_zero x _ (K.starProjection_apply_mem x)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hi
  unfold alpha angle
  rw [sub_eq_zero.mp hi]
  by_cases h : K.starProjection x = 0
  · simp [h]
  · congr 1
    field_simp [norm_ne_zero_iff.mpr h, show x ≠ 0 from fun hx ↦ h (by simp [hx])]

theorem alpha_le_angle (x y : E) (hy : y ∈ K) : alpha K x ≤ angle x y := by
  have hi := K.starProjection_inner_eq_zero x y hy
  rw [inner_sub_left] at hi
  unfold alpha angle
  apply arccos_le_arccos
  rw [sub_eq_zero.mp hi]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy' : y = 0
  · simp [hy', div_nonneg (norm_nonneg _) (norm_nonneg _)]
  rw [div_le_div_iff₀ (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy')) (norm_pos_iff.mpr hx)]
  calc
    _ ≤ (‖K.starProjection x‖ * ‖y‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (real_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

/-- A lower bound on the compressed oracle forms gives one-query angular displacement
for every live vector. The reverse inequality uses involutivity. -/
theorem one_query (O : E →ₗᵢ[ℝ] E) (hinv : Function.Involutive O)
    {v : ℝ} (hv : 0 ≤ v) (hvπ : v ≤ π)
    (compressed : ∀ y ∈ K, cos v * ‖y‖ ^ 2 ≤ ⟪y, O y⟫)
    (x : E) : |alpha K (O x) - alpha K x| ≤ v := by
  have upper (z : E) : alpha K (O z) ≤ alpha K z + v := by
    let y := K.starProjection z
    have hy : y ∈ K := K.starProjection_apply_mem _
    by_cases h0 : y = 0
    · have hu : alpha K (O z) ≤ π / 2 :=
        arccos_le_pi_div_two.mpr (div_nonneg (norm_nonneg _) (norm_nonneg _))
      have hz : alpha K z = π / 2 := by
        change arccos (‖y‖ / ‖z‖) = _
        simp [h0]
      linarith
    have hd : angle (O y) y ≤ v := by
      rw [angle_comm, angle, O.norm_map, ← arccos_cos hv hvπ]
      apply arccos_le_arccos
      apply (le_div_iff₀ (mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr h0))).mpr
      simpa [sq] using compressed y hy
    calc
      _ ≤ angle (O z) y := alpha_le_angle K _ _ hy
      _ ≤ angle (O z) (O y) + angle (O y) y := angle_le_angle_add_angle _ _ _
      _ ≤ alpha K z + v := by rw [O.angle_map, alpha_eq_angle]; gcongr
  have h₁ := upper x
  have h₂ := upper (O x)
  rw [hinv x] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem of_hit_fraction (O : E →ₗᵢ[ℝ] E) (hinv : Function.Involutive O)
    {p : ℝ} (hp : 0 ≤ p) (h1 : p ≤ 1)
    (compressed : ∀ y ∈ K, (1-2*p) * ‖y‖ ^ 2 ≤ ⟪y, O y⟫) (x : E) :
    |alpha K (O x) - alpha K x| ≤ 2 * arcsin (√p) := by
  have hs : √p ≤ 1 := (sqrt_le_one).mpr h1
  apply one_query K O hinv (mul_nonneg (by norm_num) (arcsin_nonneg.mpr (sqrt_nonneg p)))
    (by linarith [arcsin_le_pi_div_two (√p)])
  have hsin := sin_arcsin (show -1 ≤ √p by linarith [sqrt_nonneg p]) hs
  intro y hy
  rw [cos_two_mul, cos_sq', hsin, sq_sqrt hp]
  linarith [compressed y hy]

#print axioms alpha_eq_angle
#print axioms alpha_le_angle
#print axioms one_query
#print axioms of_hit_fraction
end Track2Grover.QueryAngle
