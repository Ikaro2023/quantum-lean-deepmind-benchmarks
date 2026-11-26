import Track2Grover.CoupledLabels
import Track2Grover.LowerOutputAverage
import QuantumComputation.Maths.LinearAlgebra

namespace Track2Grover.CoupledActions
open Finset Operator CoupledLabels CoupledHistory Real QuantumComputation.Specs
open scoped BigOperators RealInnerProductSpace Matrix

noncomputable def act {q : ℕ} (U : Unitary (2^q)) : Space q →ₗᵢ[ℝ] Space q where
  toLinearMap := (Matrix.toEuclideanLin U.1).restrictScalars ℝ
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖(U.1 *ᵥ x.ofLp) i‖^2) = _
    simpa only [← Complex.sq_norm] using sum_normSq_unitary_mulVec U x.ofLp

theorem act_apply {q : ℕ} (U : Unitary (2^q)) (x : Space q) (z) :
    act U x z = (U.1 *ᵥ x.ofLp) z := rfl

variable (L : Type*) [Fintype L] [Nonempty L] {q : ℕ}

theorem fixed_node (U : Unitary (2^q)) (x : Family L (Space q))
    {p v t h f : ℝ} (next : Run (uniform L (Space q)) p v
      (lift L (Space q) (act U).toLinearMap x) t h f) :
    Run (uniform L (Space q)) p v x t h f := by
  simpa using Run.instrument (K := uniform L (Space q)) (l := 1) x
    (fun _ ↦ lift L (Space q) (act U).toLinearMap)
    (lift_complete L _ _ (fun y ↦ by simp))
    (fun _ ↦ commutes L _ _) (t := fun _ ↦ t) (h := fun _ ↦ h) (f := fun _ ↦ f) (fun _ ↦ next)

noncomputable def joint (O : L → Unitary (2^q)) : Family L (Space q) →ₗᵢ[ℝ] Family L (Space q) where
  toFun x := WithLp.toLp 2 (fun i ↦ act (O i) (x i))
  map_add' x y := by ext i; change act (O i) (x i+y i) _ = _; rw [map_add]; rfl
  map_smul' s x := by ext i; change act (O i) (s • x i) _ = _; rw [map_smul]; rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (fun i ↦ act (O i) (x i))‖^2 = ‖x‖^2
    simp only [PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply, LinearIsometry.norm_map]

theorem joint_apply (O : L → Unitary (2^q)) (x : Family L (Space q)) (i) :
    joint L O x i = act (O i) (x i) := rfl

theorem oracle_node (O : L → Unitary (2^q)) (hinv : ∀ i, Function.Involutive (act (O i)))
    {b : ℝ} (hb : b ∈ Set.Icc 0 1)
    (compressed : ∀ y : Space q, (1-2*b)*(Fintype.card L:ℝ)*‖y‖^2 ≤
      ∑ i, ⟪y,act (O i) y⟫)
    (x : Family L (Space q)) {p t h f : ℝ}
    (next : Run (uniform L (Space q)) p (2*arcsin (√b)) (joint L O x) t h f) :
    Run (uniform L (Space q)) p (2*arcsin (√b)) x (‖x‖^2+t) h f := by
  apply Run.query x (joint L O) _ _ next
  · intro z; ext i j; exact congrFun (congrArg WithLp.ofLp (hinv i (z i))) j
  · intro y hy
    obtain ⟨i₀⟩ := ‹Nonempty L›
    change ∀ i j, y i = y j at hy
    rw [PiLp.inner_apply, sum_energy]
    simp_rw [joint_apply, fun i ↦ hy i i₀]
    rw [sum_const, card_univ, nsmul_eq_mul, cos_two_mul, cos_sq',
      sin_arcsin (show -1 ≤ √b by linarith [sqrt_nonneg b]) (sqrt_le_one.mpr hb.2), sq_sqrt hb.1]
    linarith [compressed (y i₀)]

theorem projection_norm (x : Family L (Space q)) :
    ‖(uniform L (Space q)).starProjection x‖^2 =
      ‖∑ i, x i‖^2 / Fintype.card L := by
  rw [uniform_projection, sum_energy]
  change (∑ _ : L, ‖(Fintype.card L:ℝ)⁻¹ • ∑ i, x i‖^2) = _
  rw [sum_const, card_univ, nsmul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

theorem supported {n k q : ℕ} (hk : 0 < k)
    [Nonempty ↥(groverTargetSets n k)] (σ : Store Grover.Var)
    (x : Family ↥(groverTargetSets n k) (Space q))
    (hsupp : ∀ i, ¬ OutputAverage.good i.1 σ → x i=0) :
    ‖(uniform ↥(groverTargetSets n k) (Space q)).starProjection x‖^2 ≤
    (k/(2:ℝ)^n) * ‖x‖^2 := by
  classical
  let A := groverTargetSets n k
  let B := (univ : Finset ↥A).filter (fun S ↦ OutputAverage.good S.val σ)
  have hc : (B.card:ℝ) = ((A.filter (fun S ↦ OutputAverage.good S σ)).card:ℝ) := by
    change (((univ : Finset ↥A).filter _).card : ℝ) = _
    rw [← sum_boole, ← sum_boole (s := A)]
    exact Finset.sum_coe_sort A (fun S ↦ if OutputAverage.good S σ then (1:ℝ) else 0)
  have hcr : (2:ℝ)^n * B.card ≤ (Fintype.card ↥A:ℝ) * k := by
    rw [hc,Fintype.card_coe]; exact_mod_cast OutputAverage.store_count hk σ
  have hsum : ∑ i ∈ B, x i = ∑ i, x i :=
    sum_subset (subset_univ _) (fun i _ hi ↦ hsupp i (fun hg ↦ hi (mem_filter.mpr ⟨mem_univ _,hg⟩)))
  have hle : ‖∑ i, x i‖^2 ≤ (B.card:ℝ) * ‖x‖^2 := by
    rw [← hsum, sum_energy ↥A (Space q) x]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le B (fun i ↦ x i)) 2).trans
    exact (sq_sum_le_card_mul_sum_sq (s := B) (f := fun i ↦ ‖x i‖)).trans
      (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ B)
        (fun i _ _ ↦ sq_nonneg ‖x i‖)) (by positivity))
  rw [projection_norm, div_le_iff₀ (by positivity : (0:ℝ) < Fintype.card ↥A)]
  apply hle.trans
  have hm := mul_le_mul_of_nonneg_right hcr (sq_nonneg ‖x‖)
  have hN : 0 < (2:ℝ)^n := by positivity
  field_simp [hN.ne']
  nlinarith only [hm]

#print axioms fixed_node
#print axioms oracle_node
#print axioms supported
end Track2Grover.CoupledActions
