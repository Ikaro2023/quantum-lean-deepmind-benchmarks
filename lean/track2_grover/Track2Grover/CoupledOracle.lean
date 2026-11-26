import Track2Grover.PhysicalMatrix
import Track2Grover.CoupledActions

/-! One oracle in an arbitrary register of an arbitrary entangled workspace. -/
namespace Track2Grover.Physical
open QuantumComputation.Specs CoupledLabels CoupledActions Operator Finset
open scoped Matrix RealInnerProductSpace

theorem act_involution {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :
    Function.Involutive (act (r.embedUnitary (groverParallelMarkingOracle m S))) := by
  intro x
  ext i
  change ((O r S).1 *ᵥ ((O r S).1 *ᵥ x.ofLp)) i = _
  rw [Matrix.mulVec_mulVec, O_inv, Matrix.one_mulVec]

private theorem inner_oracle {n m q : ℕ} (r : QRegister ((n+1)*m) q)
    (S : Finset (Fin (2^n))) (x : Space q) :
    ⟪x, act (O r S) x⟫ =
      ∑ z, ‖act (B r) x z‖^2 * (eigenSign r S z : ℝ) := by
  have hprod : (B r).1 * (O r S).1 = D r S * (B r).1 := by
    rw [← conj_eq, Matrix.mul_assoc (_ * _), B_inv, Matrix.mul_one]
  have hcoord (i) : act (B r) (act (O r S) x) i =
      (eigenSign r S i : ℝ) • (act (B r) x i) := by
    change ((B r).1 *ᵥ ((O r S).1 *ᵥ x.ofLp)) i = _
    rw [Matrix.mulVec_mulVec, hprod, ← Matrix.mulVec_mulVec, diag_eq, Matrix.mulVec_diagonal]
    simp [act_apply, Complex.real_smul]
  rw [← (act (B r)).inner_map_map x (act (O r S) x), PiLp.inner_apply]
  apply sum_congr rfl
  intro i _
  rw [hcoord, real_inner_smul_right, real_inner_self_eq_norm_sq, mul_comm]

/-- The actual oracle quadratic form, uniformly summed over hidden target sets. -/
theorem compressed {n m k q : ℕ} (hk : 0 < k) (r : QRegister ((n+1)*m) q) (x : Space q) :
    (1-2*((m:ℝ)*k/2^n)) * (Fintype.card ↥(groverTargetSets n k) : ℝ) * ‖x‖^2 ≤
      ∑ S : ↥(groverTargetSets n k), ⟪x, act (r.embedUnitary (groverParallelMarkingOracle m S.1)) x⟫ := by
  let w (z : Fin (2^q)) := ‖act (B r) x z‖^2
  have h := Compression.embedded_weighted_bound hk (swapWidth r) w (fun z ↦ sq_nonneg _)
  simp_rw [swap_back] at h
  have hd (z) (S : Finset (Fin (2^n))) :
      (((B r).1 * (O r S).1 * (B r).1) z z).re = (eigenSign r S z : ℝ) := by
    rw [conj_eq,diag_eq]
    simp
  change ((2:ℝ)^n - 2*m*k) * (groverTargetSets n k).card * (∑ z, w z) ≤
    ∑ z, w z * ((2:ℝ)^n * ∑ S ∈ groverTargetSets n k, (((B r).1*(O r S).1*(B r).1) z z).re) at h
  simp_rw [hd] at h
  have hw : ∑ z, w z = ‖x‖^2 := by
    rw [← (act (B r)).norm_map x, EuclideanSpace.norm_sq_eq]
  rw [hw] at h
  have ht : ∑ S : ↥(groverTargetSets n k),
      ⟪x, act (r.embedUnitary (groverParallelMarkingOracle m S.1)) x⟫ =
      ∑ z, w z * ∑ S ∈ groverTargetSets n k, (eigenSign r S z : ℝ) := by
    change ∑ S : ↥(groverTargetSets n k), ⟪x, act (O r S.1) x⟫ = _
    simp_rw [inner_oracle]
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    rw [mul_sum]
    exact sum_attach _ (fun S ↦ w z * (eigenSign r S z : ℝ))
  rw [ht, Fintype.card_coe]
  have he (z) (a : ℝ) : w z * ((2:ℝ)^n * a) = (2:ℝ)^n * (w z * a) := by ring
  simp_rw [he, ← mul_sum] at h
  have hN : 0 < (2:ℝ)^n := by positivity
  apply le_of_mul_le_mul_left _ hN
  convert h using 1
  field_simp

#print axioms act_involution
#print axioms compressed
end Track2Grover.Physical
