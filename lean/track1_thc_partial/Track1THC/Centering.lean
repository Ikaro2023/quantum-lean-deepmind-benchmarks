import Track1THC.JWAlgebra

/-!
# Exact THC centering identity (Lee et al. 2021, Eqs. 11–18)

For a THC factorization with `thcShiftedOneBody thc = ∑ ℓ, t ℓ • vecMulVec (u ℓ) (u ℓ)`,

`thcHamiltonian thc - c • 1 =
   ∑ σ ℓ, (-t ℓ / 2) • Z_{u ℓ, σ} + (1/8) • ∑ σ τ μ ν, ζ_{μν} • (Z_{χ^μ,σ} * Z_{χ^ν,τ})`

with `c = ∑ t - ζ_total / 2`, where `Z_{χ,σ} = 1 - 2 n_{χ,σ}` is `orbitalReflection`.  No
normalization of the leaves is needed for this identity (it is pure algebra in `n = (1 - Z)/2`).
The LCU 1-norm of the right-hand side is `∑|t| + (1/2)∑|ζ| = lamRep` of `IsRounded`.
-/

namespace Track1THC.Centering

open QuantumComputation.Specs Operator Matrix Track1THC.JW
open scoped Matrix

/-! ## Linearity of `oneBodyHamiltonian` -/

theorem OB_add {N : ℕ} (h k : Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (h + k) = oneBodyHamiltonian h + oneBodyHamiltonian k := by
  simp only [oneBodyHamiltonian, Matrix.add_apply, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]

theorem OB_zero {N : ℕ} : oneBodyHamiltonian (0 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  simp [oneBodyHamiltonian]

theorem OB_smul {N : ℕ} (c : ℝ) (h : Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (c • h) = (c : ℂ) • oneBodyHamiltonian h := by
  simp only [oneBodyHamiltonian, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul,
    Finset.smul_sum]

theorem OB_sub {N : ℕ} (h k : Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (h - k) = oneBodyHamiltonian h - oneBodyHamiltonian k := by
  have := OB_add (h - k) k
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem OB_sum {N : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Matrix (Fin N) (Fin N) ℝ) :
    oneBodyHamiltonian (∑ i ∈ s, f i) = ∑ i ∈ s, oneBodyHamiltonian (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [OB_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, OB_add, ih]

theorem orbitalNumberOp_expand (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    orbitalNumberOp N χ σ = ∑ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) •
      ((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ * jwAnnihilate (2 * N) (spinOrbital N q σ)) := by
  rw [orbitalNumberOp_eq_annihilate, orbitalAnnihilate_conjTranspose, orbitalAnnihilate,
    Finset.sum_mul]
  simp only [Finset.mul_sum, Matrix.smul_mul]
  simp only [Matrix.mul_smul, smul_smul]

/-- A rank-one one-body term is the sum of the two spin number operators. -/
theorem OB_vecMulVec {N : ℕ} (u : Fin N → ℝ) :
    oneBodyHamiltonian (vecMulVec u u) = ∑ σ : Fin 2, orbitalNumberOp N u σ := by
  unfold oneBodyHamiltonian
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [orbitalNumberOp_expand]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp [vecMulVec_apply]

/-! ## Pointwise product expansion of reflections -/

theorem Z_mul_Z {N : ℕ} (a b : Operator (2 ^ (2 * N))) :
    (1 - (2 : ℂ) • a) * (1 - (2 : ℂ) • b) =
      1 - (2 : ℂ) • a - (2 : ℂ) • b + (4 : ℂ) • (a * b) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  module

/-! ## The centering identity -/

theorem thc_centering {N M : ℕ} (thc : THCFactorization N M) (t : Fin N → ℝ)
    (u : Fin N → Fin N → ℝ)
    (hT : thcShiftedOneBody thc = ∑ ℓ, t ℓ • vecMulVec (u ℓ) (u ℓ)) :
    thcHamiltonian thc -
        (((∑ ℓ, t ℓ) - 2⁻¹ * ∑ μ, ∑ ν, thc.zeta μ ν : ℝ) : ℂ) • (1 : Operator (2 ^ (2 * N))) =
      ∑ σ : Fin 2, ∑ ℓ, ((-t ℓ / 2 : ℝ) : ℂ) • orbitalReflection N (u ℓ) σ +
        (8 : ℂ)⁻¹ • ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) •
          (orbitalReflection N (thc.chi μ) σ * orbitalReflection N (thc.chi ν) τ) := by
  set n : Fin M → Fin 2 → Operator (2 ^ (2 * N)) :=
    fun μ σ => orbitalNumberOp N (thc.chi μ) σ with hn
  set m : Fin N → Fin 2 → Operator (2 ^ (2 * N)) :=
    fun ℓ σ => orbitalNumberOp N (u ℓ) σ with hm
  set zl : Fin M → ℝ := fun μ => ∑ ν, thc.zeta μ ν with hzl
  -- Stage 1: the one-body part
  have hshift : thcShiftedOneBody thc =
      thc.h1eMod + ∑ μ, zl μ • vecMulVec (thc.chi μ) (thc.chi μ) := by
    ext p q
    simp only [thcShiftedOneBody, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul, hzl]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  have hh : thc.h1eMod = (∑ ℓ, t ℓ • vecMulVec (u ℓ) (u ℓ)) -
      ∑ μ, zl μ • vecMulVec (thc.chi μ) (thc.chi μ) := by
    rw [← hT]; rw [hshift]; abel
  have hOB : oneBodyHamiltonian thc.h1eMod =
      ∑ ℓ, (t ℓ : ℂ) • ∑ σ, m ℓ σ - ∑ μ, (zl μ : ℂ) • ∑ σ, n μ σ := by
    rw [hh, OB_sub, OB_sum, OB_sum]
    congr 1
    · refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [OB_smul, OB_vecMulVec]
    · refine Finset.sum_congr rfl fun μ _ => ?_
      rw [OB_smul, OB_vecMulVec]
  -- Stage 2: expand the reflections
  have hZ : ∀ (μ : Fin M) (ν : Fin M) (σ τ : Fin 2),
      orbitalReflection N (thc.chi μ) σ * orbitalReflection N (thc.chi ν) τ =
        1 - (2 : ℂ) • n μ σ - (2 : ℂ) • n ν τ + (4 : ℂ) • (n μ σ * n ν τ) := by
    intro μ ν σ τ
    exact Z_mul_Z (n μ σ) (n ν τ)
  have hsym : ∀ ν, ∑ μ, thc.zeta μ ν = zl ν := by
    intro ν
    simp only [hzl]
    refine Finset.sum_congr rfl fun μ _ => ?_
    exact thc.zeta_symm.apply ν μ
  have hzlc : ∀ μ, (zl μ : ℂ) = ∑ ν, (thc.zeta μ ν : ℂ) := by intro μ; simp [hzl]
  have hsymc : ∀ ν, ∑ μ, (thc.zeta μ ν : ℂ) = (zl ν : ℂ) := by
    intro ν; rw [hzlc]
    exact Finset.sum_congr rfl fun μ _ => by rw [thc.zeta_symm.apply ν μ]
  have hZℓ : ∀ ℓ σ, orbitalReflection N (u ℓ) σ = 1 - (2 : ℂ) • m ℓ σ := fun ℓ σ => rfl
  -- atoms
  set W : Operator (2 ^ (2 * N)) := ∑ σ : Fin 2, ∑ μ, (zl μ : ℂ) • n μ σ with hW
  set Q : Operator (2 ^ (2 * N)) := ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν,
    (thc.zeta μ ν : ℂ) • (n μ σ * n ν τ) with hQ
  set Zt : ℂ := ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) with hZt
  -- the four pieces of the two-body expansion
  have hS1 : ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) • (1 : Operator (2 ^ (2 * N))) =
      (4 * Zt) • (1 : Operator (2 ^ (2 * N))) := by
    simp only [← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← hZt]
    simp only [nsmul_eq_mul]
    congr 1
  have hS2 : ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) • ((2 : ℂ) • n μ σ) =
      (4 : ℂ) • W := by
    have h1 : ∀ σ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) • ((2 : ℂ) • n μ σ) =
        (2 : ℂ) • ∑ μ, (zl μ : ℂ) • n μ σ := by
      intro σ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← Finset.sum_smul, ← hzlc, smul_comm]
    simp only [h1, Fin.sum_univ_two, hW]
    module
  have hS3 : ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) • ((2 : ℂ) • n ν τ) =
      (4 : ℂ) • W := by
    have h1 : ∀ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) • ((2 : ℂ) • n ν τ) =
        (2 : ℂ) • ∑ ν, (zl ν : ℂ) • n ν τ := by
      intro τ
      rw [Finset.sum_comm, Finset.smul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [← Finset.sum_smul, hsymc, smul_comm]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hW]
    simp only [Fin.sum_univ_two]
    module
  have hS4 : ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) •
      ((4 : ℂ) • (n μ σ * n ν τ)) = (4 : ℂ) • Q := by
    simp only [hQ, Finset.smul_sum, smul_comm (4 : ℂ)]
  -- right-hand side two-body part
  have hRHS2 : (8 : ℂ)⁻¹ • ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) •
      (orbitalReflection N (thc.chi μ) σ * orbitalReflection N (thc.chi ν) τ) =
      (2 : ℂ)⁻¹ • (Zt • (1 : Operator (2 ^ (2 * N)))) - W + (2 : ℂ)⁻¹ • Q := by
    have hpt : ∀ σ τ μ ν, (thc.zeta μ ν : ℂ) •
        (orbitalReflection N (thc.chi μ) σ * orbitalReflection N (thc.chi ν) τ) =
        (thc.zeta μ ν : ℂ) • (1 : Operator (2 ^ (2 * N))) -
          (thc.zeta μ ν : ℂ) • ((2 : ℂ) • n μ σ) - (thc.zeta μ ν : ℂ) • ((2 : ℂ) • n ν τ) +
          (thc.zeta μ ν : ℂ) • ((4 : ℂ) • (n μ σ * n ν τ)) := by
      intro σ τ μ ν
      rw [hZ μ ν σ τ]
      module
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, hS1, hS2, hS3, hS4]
    module
  -- right-hand side one-body part
  have hRHS1 : ∑ σ : Fin 2, ∑ ℓ, ((-t ℓ / 2 : ℝ) : ℂ) • orbitalReflection N (u ℓ) σ =
      -((∑ ℓ, (t ℓ : ℂ)) • (1 : Operator (2 ^ (2 * N)))) +
        ∑ ℓ, (t ℓ : ℂ) • ∑ σ : Fin 2, m ℓ σ := by
    rw [Finset.sum_comm]
    have hpt : ∀ ℓ, ∑ σ : Fin 2, ((-t ℓ / 2 : ℝ) : ℂ) • orbitalReflection N (u ℓ) σ =
        -((t ℓ : ℂ) • (1 : Operator (2 ^ (2 * N)))) + (t ℓ : ℂ) • ∑ σ : Fin 2, m ℓ σ := by
      intro ℓ
      simp only [Fin.sum_univ_two, hZℓ]
      push_cast
      module
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_smul]
  rw [hRHS2, hRHS1, thcHamiltonian, hOB]
  have hLHS2 : (2 : ℂ)⁻¹ • ∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ, ∑ ν, (thc.zeta μ ν : ℂ) •
      (orbitalNumberOp N (thc.chi μ) σ * orbitalNumberOp N (thc.chi ν) τ) = (2 : ℂ)⁻¹ • Q := rfl
  have hWc : ∑ μ, (zl μ : ℂ) • ∑ σ, n μ σ = W := by
    simp only [hW, Finset.smul_sum]
    exact Finset.sum_comm
  rw [hLHS2, hWc]
  have hc : ((((∑ ℓ, t ℓ) - 2⁻¹ * ∑ μ, ∑ ν, thc.zeta μ ν : ℝ)) : ℂ) =
      (∑ ℓ, (t ℓ : ℂ)) - 2⁻¹ * Zt := by
    push_cast
    rfl
  rw [hc]
  module
end Track1THC.Centering
