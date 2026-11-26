/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Track2Grover.Engine.FindAllJohnsonAltStep

/-!
# Choice-Free Johnson Polar Step-Up & Zero-Padding Limit (`FindAllJohnsonRampLift`)

Constructs the choice-free Boolean-lattice polar step-up isometry `stepUpFrom N M₁ M₂` from
`P01Subset N M₁ → ℝ` to `P01Subset N M₂ → ℝ` (`M₁ ≤ M₂`, `2 * M₂ ≤ N`) and proves that on the
`(S_r × S_{N-r})`-invariant target-intersection basis `orbEmbedGen (2 ^ n) M R` it converges
to
exact zero-padding `zeroPadOrbVec` within `1 / (2 * 10 ^ 15)` for all `n ≥ altN0 = 80000`,
`1 ≤ M₁ ≤ M₂ ≤ 8192`, and `1 ≤ R.card ≤ 1024`:

1. **Boolean-Lattice Differential Poset Identities (`jDownGenMat_mul_succ`,
   `jDownGenMat_succ_mul_transpose`)**:
   Establishes `B_{w, M} * B_{M, M+1} = (M + 1 - w) • B_{w, M+1}` and the three-case
   intersection
   identity `B_{M+1, M+2} * B_{M+1, M+2}ᵀ = B_{M, M+1}ᵀ * B_{M, M+1} + (N - 2 * M - 2) • 1`.
2. **Choice-Free Spectral Projectors & Polar Step-Up (`eigProj`, `stepUpMat`, `stepUpFrom`,
   `stepUpFrom_transpose_mul_self`)**:
   Defines the Johnson eigenspace projectors `eigProj N M j` and polar step-up isometry
   `stepUpMat N M = B_{M, M+1}ᵀ * ∑_{j=0}^M ((M + 1 - j)(N - M - j))^{-1/2} • eigProj N M j`
   by elementary recursion on `M` without `Matrix.sqrt`, eigenvalues, or `Classical.choice`.
3. **Exact Harmonic Kernel Lift & `O(1 / √N)` Orbit Zero-Padding (`harmKerLift`,
   `stepUpFrom_mulVec_harmKerUnit`, `finVecNorm_stepUpFrom_orbEmbedGen_sub_le`)**:
   Constructs an explicit closed-form two-binomial harmonic vector `harmKerLift N R w M ∈ V_w`
   transported covariantly (`0` error across arbitrary `M₁ ≤ M₂`) by `stepUpFrom N M₁ M₂`, and
   bounds its Euclidean distance to `orbEmbedGen (2 ^ n) M R (Pi.single w 1)`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
open Real
open scoped Matrix

/-- Squared Euclidean `ℓ_2` norm `∑ i, (v i) ^ 2` on a `Fintype` index `ι`. -/
noncomputable def finVecSqNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ∑ i : ι, (v i) ^ 2

/-- Euclidean `ℓ_2` norm `√(∑ i, (v i) ^ 2)` on a `Fintype` index `ι`. -/
noncomputable def finVecNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  √(finVecSqNorm v)

/-- Zero-pad an orbit coordinate vector from multiplicity `M₁` to `M₂` (`M₁ ≤ M₂`). -/
def zeroPadOrbVec (M₁ M₂ r : ℕ) (x : Fin (orbDim M₁ r) → ℝ) : Fin (orbDim M₂ r) → ℝ :=
  fun w ↦ if hw : w.1 < orbDim M₁ r then x ⟨w.1, hw⟩ else 0

/-- Inverse-singular-value spectral combination on `P01Subset N M` for projector family `P`. -/
noncomputable def stepUpScaleOf (N M : ℕ)
    (P : ℕ → Matrix (P01Subset N M) (P01Subset N M) ℝ) :
    Matrix (P01Subset N M) (P01Subset N M) ℝ :=
  ∑ j ∈ Finset.range (M + 1),
    (1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ)) • P j

/-- Polar step-up matrix `B_{M, M+1}ᵀ * stepUpScaleOf N M P` associated with `P`. -/
noncomputable def stepUpMatOf (N M : ℕ)
    (P : ℕ → Matrix (P01Subset N M) (P01Subset N M) ℝ) :
    Matrix (P01Subset N (M + 1)) (P01Subset N M) ℝ :=
  (jDownGenMat N M (M + 1))ᵀ * stepUpScaleOf N M P

/-- Choice-free orthogonal projector onto the `j`-th Johnson eigenspace `V_j` of `P01Subset
  N M`. -/
noncomputable def eigProj (N : ℕ) :
    ∀ M : ℕ, ℕ → Matrix (P01Subset N M) (P01Subset N M) ℝ
  | 0, j => if j = 0 then 1 else 0
  | M + 1, j =>
      let Ψ := stepUpMatOf N M (eigProj N M)
      if j ≤ M then Ψ * eigProj N M j * Ψᵀ
      else if j = M + 1 then 1 - Ψ * Ψᵀ
      else 0

/-- Inverse-singular-value operator `(B_{M, M+1} * B_{M, M+1}ᵀ)^{-1/2}` on `P01Subset N M`. -/
noncomputable abbrev stepUpScale (N M : ℕ) :
    Matrix (P01Subset N M) (P01Subset N M) ℝ :=
  stepUpScaleOf N M (eigProj N M)

/-- Choice-free polar step-up isometry `P01Subset N M → ℝ` to `P01Subset N (M + 1) → ℝ`. -/
noncomputable abbrev stepUpMat (N M : ℕ) :
    Matrix (P01Subset N (M + 1)) (P01Subset N M) ℝ :=
  stepUpMatOf N M (eigProj N M)

/-- Iterated Johnson polar step-up isometry from `P01Subset N M₁` to `P01Subset N M₂`. -/
noncomputable def stepUpFrom (N M₁ : ℕ) :
    ∀ M₂ : ℕ, Matrix (P01Subset N M₂) (P01Subset N M₁) ℝ
  | 0 => if h : M₁ = 0 then h ▸ 1 else 0
  | M₂ + 1 =>
      if h : M₁ = M₂ + 1 then h ▸ 1
      else stepUpMat N M₂ * stepUpFrom N M₁ M₂

/-- Two-binomial `(S_r × S_{N-r})`-invariant harmonic kernel weight at intersection size
  `t`. -/
noncomputable def harmKerWeight (N r w t : ℕ) : ℝ :=
  (-1 : ℝ) ^ (w - t) * ((r - t).choose (w - t) : ℝ) / ((N - r).choose (w - t) : ℝ)

/-- Harmonic vector in `ker B_{w-1, w}` on `P01Subset N w` peaked on `U ⊆ R`. -/
noncomputable def harmKerBase (N : ℕ) (R : Finset (Fin N)) (w : ℕ) (U : P01Subset N w) : ℝ :=
  harmKerWeight N R.card w (U.1 ∩ R).card

/-- Covariant lift `(B_{w, M})ᵀ *ᵥ harmKerBase N R w` inside `V_w` on `P01Subset N M`. -/
noncomputable def harmKerLift (N : ℕ) (R : Finset (Fin N)) (w M : ℕ) : P01Subset N M → ℝ :=
  (jDownGenMat N w M)ᵀ *ᵥ harmKerBase N R w

end

public section
open Real
open scoped Matrix

/-! ## Section 1: Finite-Index Euclidean `ℓ_2` Norm & Orbit Helpers -/

theorem finVecSqNorm_eq_dot {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    finVecSqNorm v = v ⬝ᵥ v := by
  simp [finVecSqNorm, dotProduct, sq]

theorem finVecSqNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ finVecSqNorm v :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem finVecNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ finVecNorm v :=
  Real.sqrt_nonneg _

theorem sq_finVecNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (finVecNorm v) ^ 2 = finVecSqNorm v :=
  Real.sq_sqrt (finVecSqNorm_nonneg v)

theorem finVecNorm_zero {ι : Type*} [Fintype ι] :
    finVecNorm (0 : ι → ℝ) = 0 := by
  simp [finVecNorm, finVecSqNorm]

theorem finVecNorm_neg {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    finVecNorm (-v) = finVecNorm v := by
  simp [finVecNorm, finVecSqNorm]

theorem finVecNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    finVecNorm (c • v) = |c| * finVecNorm v := by
  have hsq : finVecSqNorm (c • v) = c ^ 2 * finVecSqNorm v := by
    unfold finVecSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow]
  unfold finVecNorm
  rw [hsq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

private lemma dot_le_finVecNorm_mul {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    u ⬝ᵥ v ≤ finVecNorm u * finVecNorm v := by
  set a := finVecNorm u
  set b := finVecNorm v
  have ha0 : 0 ≤ a := finVecNorm_nonneg u
  have hb0 : 0 ≤ b := finVecNorm_nonneg v
  have ha2 : a ^ 2 = finVecSqNorm u := sq_finVecNorm u
  have hb2 : b ^ 2 = finVecSqNorm v := sq_finVecNorm v
  by_cases hab : a * b = 0
  · rcases mul_eq_zero.mp hab with ha_eq | hb_eq
    · have hu_sq : finVecSqNorm u = 0 := by rw [← ha2, ha_eq]; ring
      have hu_zero : ∀ i : ι, u i = 0 := fun i ↦ by
        have hle : (u i) ^ 2 ≤ finVecSqNorm u :=
          Finset.single_le_sum (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)
        nlinarith [sq_nonneg (u i)]
      simp [dotProduct, hu_zero, hab]
    · have hv_sq : finVecSqNorm v = 0 := by rw [← hb2, hb_eq]; ring
      have hv_zero : ∀ i : ι, v i = 0 := fun i ↦ by
        have hle : (v i) ^ 2 ≤ finVecSqNorm v :=
          Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
        nlinarith [sq_nonneg (v i)]
      simp [dotProduct, hv_zero, hab]
  · have hsum : 0 ≤ ∑ i : ι, (b * u i - a * v i) ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    have hexp :
        (∑ i : ι, (b * u i - a * v i) ^ 2) =
          b ^ 2 * finVecSqNorm u + a ^ 2 * finVecSqNorm v - 2 * (a * b) * (u ⬝ᵥ v) := by
      have hterm : ∀ i : ι,
          (b * u i - a * v i) ^ 2 =
            b ^ 2 * (u i) ^ 2 + a ^ 2 * (v i) ^ 2 - 2 * (a * b) * (u i * v i) :=
        fun _ ↦ by ring
      simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    rw [hexp, ha2, hb2] at hsum
    have hprod : 0 ≤ 2 * (a * b) * (a * b - u ⬝ᵥ v) := by nlinarith
    have hab_pos : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha0 hb0) (Ne.symm hab)
    nlinarith

theorem finVecNorm_add_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    finVecNorm (u + v) ≤ finVecNorm u + finVecNorm v := by
  have hrhs : 0 ≤ finVecNorm u + finVecNorm v :=
    add_nonneg (finVecNorm_nonneg u) (finVecNorm_nonneg v)
  rw [finVecNorm, Real.sqrt_le_iff]
  refine ⟨hrhs, ?_⟩
  have hexp : finVecSqNorm (u + v) = finVecSqNorm u + 2 * (u ⬝ᵥ v) + finVecSqNorm v := by
    unfold finVecSqNorm dotProduct
    have hterm : ∀ i : ι, (u i + v i) ^ 2 = (u i) ^ 2 + 2 * (u i * v i) + (v i) ^ 2 :=
      fun _ ↦ by ring
    simp only [Pi.add_apply, hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp]
  nlinarith [dot_le_finVecNorm_mul u v, sq_finVecNorm u, sq_finVecNorm v]

theorem finVecNorm_sub_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    finVecNorm (u - v) ≤ finVecNorm u + finVecNorm v := by
  rw [sub_eq_add_neg, ← finVecNorm_neg v]
  exact finVecNorm_add_le u (-v)

theorem finVecNorm_sum_le {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℝ) :
    finVecNorm (∑ k ∈ s, f k) ≤ ∑ k ∈ s, finVecNorm (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finVecNorm_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (finVecNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem finVecNorm_mulVec_of_transpose_mul_self {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {A : Matrix κ ι ℝ} (hA : Aᵀ * A = 1) (v : ι → ℝ) :
    finVecNorm (A *ᵥ v) = finVecNorm v := by
  have hsq : finVecSqNorm (A *ᵥ v) = finVecSqNorm v := by
    rw [finVecSqNorm_eq_dot, finVecSqNorm_eq_dot, Matrix.dotProduct_mulVec]
    have hvm : (A *ᵥ v) ᵥ* A = Aᵀ *ᵥ (A *ᵥ v) := by
      funext j
      simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
    rw [hvm, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  unfold finVecNorm
  rw [hsq]

theorem symZVec_sub {N m : ℕ} (R : Finset (Fin N)) (u v : SymSubset N m → ℝ) :
    symZVec R (u - v) = symZVec R u - symZVec R v := by
  funext E
  simp only [symZVec, Pi.sub_apply]
  ring

theorem finVecNorm_symZVec {N m : ℕ} (R : Finset (Fin N)) (v : SymSubset N m → ℝ) :
    finVecNorm (symZVec R v) = finVecNorm v := by
  unfold finVecNorm finVecSqNorm
  rw [sum_sq_symZVec]

theorem finVecNorm_evalSymStage_sub {N m : ℕ} (R : Finset (Fin N))
    (D : SymOrthogonal N m) :
    ∀ (K : ℕ) (u v : SymSubset N m → ℝ),
      finVecNorm (evalSymStage R D.1 K u - evalSymStage R D.1 K v) = finVecNorm (u - v)
  | 0, _, _ => rfl
  | K + 1, u, v => by
    rw [evalSymStage, evalSymStage, finVecNorm_evalSymStage_sub R D K,
      ← Matrix.mulVec_sub, finVecNorm_mulVec_of_transpose_mul_self D.2,
      ← symZVec_sub, finVecNorm_symZVec]

theorem finVecNorm_evalSymStages_sub {N m : ℕ} (R : Finset (Fin N)) :
    ∀ (stages : List (ℕ × SymOrthogonal N m)) (u v : SymSubset N m → ℝ),
      finVecNorm (evalSymStages R stages u - evalSymStages R stages v) = finVecNorm (u - v)
  | [], _, _ => rfl
  | (K, D) :: rest, u, v => by
    rw [evalSymStages, evalSymStages, finVecNorm_evalSymStages_sub R rest,
      finVecNorm_evalSymStage_sub R D K]

theorem finVecNorm_orbEmbedGen {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    (x : Fin (orbDim m R.card) → ℝ) :
    finVecNorm (orbEmbedGen N m R x) = vecNorm x := by
  have hsq : finVecSqNorm (orbEmbedGen N m R x) = vecSqNorm x := by
    simpa only [finVecSqNorm, vecSqNorm, sq] using dot_orbEmbedGen hmrN x x
  unfold finVecNorm vecNorm
  rw [hsq]

theorem orbEmbedGen_add (N m : ℕ) (R : Finset (Fin N))
    (x y : Fin (orbDim m R.card) → ℝ) :
    orbEmbedGen N m R (x + y) = orbEmbedGen N m R x + orbEmbedGen N m R y := by
  funext E
  simp only [orbEmbedGen, Pi.add_apply, add_div]

theorem orbEmbedGen_smul (N m : ℕ) (R : Finset (Fin N))
    (c : ℝ) (x : Fin (orbDim m R.card) → ℝ) :
    orbEmbedGen N m R (c • x) = c • orbEmbedGen N m R x := by
  funext E
  simp only [orbEmbedGen, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

theorem orbEmbedGen_sum {κ : Type*} (N m : ℕ) (R : Finset (Fin N))
    (s : Finset κ) (f : κ → Fin (orbDim m R.card) → ℝ) :
    orbEmbedGen N m R (∑ k ∈ s, f k) = ∑ k ∈ s, orbEmbedGen N m R (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext E
    simp [orbEmbedGen]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, orbEmbedGen_add, ih, Finset.sum_insert ha]

theorem sqrt_symHitProb_ge_of_finVecNorm_sub_le {N m : ℕ} (R : Finset (Fin N))
    (u v : SymSubset N m → ℝ) (w : ℕ) :
    √(symHitProb R u w) - finVecNorm (v - u) ≤ √(symHitProb R v w) := by
  let S := Finset.univ.filter (fun E : SymSubset N m ↦ (E.1 ∩ R).card = w)
  let uS : { E : SymSubset N m // E ∈ S } → ℝ := fun e ↦ u e.1
  let vS : { E : SymSubset N m // E ∈ S } → ℝ := fun e ↦ v e.1
  have hu : finVecNorm uS = √(symHitProb R u w) := by
    unfold finVecNorm finVecSqNorm symHitProb uS
    rw [Finset.sum_coe_sort S (fun E ↦ (u E) ^ 2)]
  have hv : finVecNorm vS = √(symHitProb R v w) := by
    unfold finVecNorm finVecSqNorm symHitProb vS
    rw [Finset.sum_coe_sort S (fun E ↦ (v E) ^ 2)]
  have hdiff : finVecNorm (uS - vS) ≤ finVecNorm (v - u) := by
    apply Real.sqrt_le_sqrt
    unfold finVecSqNorm uS vS
    simp only [Pi.sub_apply]
    rw [Finset.sum_coe_sort S (fun E ↦ (u E - v E) ^ 2)]
    calc (∑ E ∈ S, (u E - v E) ^ 2)
        ≤ ∑ E ∈ Finset.univ, (u E - v E) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ ↦ sq_nonneg _)
      _ = ∑ E : SymSubset N m, (v E - u E) ^ 2 :=
          Finset.sum_congr rfl fun E _ ↦ by ring
  have heq : uS = vS + (uS - vS) := by funext e; simp
  have htri : finVecNorm uS ≤ finVecNorm vS + finVecNorm (uS - vS) :=
    calc finVecNorm uS = finVecNorm (vS + (uS - vS)) := congrArg finVecNorm heq
      _ ≤ finVecNorm vS + finVecNorm (uS - vS) := finVecNorm_add_le vS (uS - vS)
  linarith

theorem vecNorm_zeroPadOrbVec {M₁ M₂ r : ℕ} (h12 : M₁ ≤ M₂)
    (x : Fin (orbDim M₁ r) → ℝ) :
    vecNorm (zeroPadOrbVec M₁ M₂ r x) = vecNorm x := by
  have hdim : orbDim M₁ r ≤ orbDim M₂ r := by unfold orbDim; omega
  have hsq : vecSqNorm (zeroPadOrbVec M₁ M₂ r x) = vecSqNorm x := by
    unfold vecSqNorm zeroPadOrbVec
    have hsplit := (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin (orbDim M₂ r))))
      (p := fun w : Fin (orbDim M₂ r) ↦ w.1 < orbDim M₁ r)
      (f := fun w : Fin (orbDim M₂ r) ↦
        (if hw : w.1 < orbDim M₁ r then x ⟨w.1, hw⟩ else 0) ^ 2)).symm
    rw [hsplit]
    have hhi :
        (∑ w ∈ Finset.univ.filter (fun w : Fin (orbDim M₂ r) ↦ ¬ w.1 < orbDim M₁ r),
          (if hw : w.1 < orbDim M₁ r then x ⟨w.1, hw⟩ else 0) ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun w hw ↦ ?_
      have hnw : ¬ w.1 < orbDim M₁ r := (Finset.mem_filter.mp hw).2
      simp [hnw]
    rw [hhi, add_zero]
    symm
    refine Finset.sum_bij
      (fun (u : Fin (orbDim M₁ r)) _ ↦ (⟨u.1, u.2.trans_le hdim⟩ : Fin (orbDim M₂ r)))
      ?_ ?_ ?_ ?_
    · intro u _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩
    · intro u₁ _ u₂ _ h
      exact Fin.ext (Fin.mk.inj h)
    · intro w hw
      exact ⟨⟨w.1, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro u _
      dsimp only
      rw [dite_eq_left u.2]
  unfold vecNorm
  rw [hsq]

theorem zeroPadOrbVec_single {M₁ M₂ r : ℕ} (h12 : M₁ ≤ M₂) (w : Fin (orbDim M₁ r)) :
    zeroPadOrbVec M₁ M₂ r (Pi.single w 1) =
      Pi.single ⟨w.1, by unfold orbDim at *; omega⟩ 1 := by
  funext u
  unfold zeroPadOrbVec
  by_cases hu : u.1 < orbDim M₁ r
  · rw [dite_eq_left hu]
    by_cases heq : u.1 = w.1
    · have h1 : (⟨u.1, hu⟩ : Fin (orbDim M₁ r)) = w := Fin.ext heq
      have h2 : u = ⟨w.1, by unfold orbDim at *; omega⟩ := Fin.ext heq
      rw [h1, h2, Pi.single_eq_same, Pi.single_eq_same]
    · have h1 : (⟨u.1, hu⟩ : Fin (orbDim M₁ r)) ≠ w := fun h ↦ heq (congrArg Fin.val h)
      have h2 : u ≠ ⟨w.1, by unfold orbDim at *; omega⟩ := fun h ↦ heq (congrArg Fin.val h)
      rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  · rw [dite_eq_right hu]
    have hne : u ≠ ⟨w.1, by unfold orbDim at *; omega⟩ := fun h ↦ hu (by
      have hv : u.1 = w.1 := congrArg Fin.val h
      rw [hv]; exact w.2)
    rw [Pi.single_eq_of_ne hne]

theorem zeroPadOrbVec_add (M₁ M₂ r : ℕ) (x y : Fin (orbDim M₁ r) → ℝ) :
    zeroPadOrbVec M₁ M₂ r (x + y) = zeroPadOrbVec M₁ M₂ r x + zeroPadOrbVec M₁ M₂ r y := by
  funext u
  by_cases hu : u.1 < orbDim M₁ r <;> simp [zeroPadOrbVec, Pi.add_apply, hu]

theorem zeroPadOrbVec_smul (M₁ M₂ r : ℕ) (c : ℝ) (x : Fin (orbDim M₁ r) → ℝ) :
    zeroPadOrbVec M₁ M₂ r (c • x) = c • zeroPadOrbVec M₁ M₂ r x := by
  funext u
  by_cases hu : u.1 < orbDim M₁ r <;> simp [zeroPadOrbVec, Pi.smul_apply, hu]

theorem zeroPadOrbVec_sum {κ : Type*} (M₁ M₂ r : ℕ) (s : Finset κ)
    (f : κ → Fin (orbDim M₁ r) → ℝ) :
    zeroPadOrbVec M₁ M₂ r (∑ k ∈ s, f k) = ∑ k ∈ s, zeroPadOrbVec M₁ M₂ r (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext u
    simp [zeroPadOrbVec]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, zeroPadOrbVec_add, ih, Finset.sum_insert ha]

/-! ## Section 2: Subset Tower & Boolean-Lattice Differential Poset Identities -/

theorem jDownGenMat_self (N M : ℕ) : jDownGenMat N M M = 1 := by
  ext E F
  simp only [jDownGenMat, Matrix.of_apply, Matrix.one_apply]
  by_cases h : E = F
  · subst h; simp
  · have hnsub : ¬ E.1 ⊆ F.1 := fun hsub ↦
      h (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [E.2, F.2])))
    simp [h, hnsub]

theorem jDownGenMat_mul_succ {N w M : ℕ} (_hwM : w ≤ M) :
    jDownGenMat N w M * jDownGenMat N M (M + 1) =
      ((M + 1 - w : ℕ) : ℝ) • jDownGenMat N w (M + 1) := by
  ext U G
  simp only [Matrix.mul_apply, jDownGenMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hUG : U.1 ⊆ G.1
  · rw [ite_eq_left hUG, mul_one]
    have hcongr :
        (∑ E : P01Subset N M, (if U.1 ⊆ E.1 then (1 : ℝ) else 0) *
          (if E.1 ⊆ G.1 then 1 else 0)) =
        ∑ E ∈ Finset.univ.filter (fun E : P01Subset N M ↦ U.1 ⊆ E.1 ∧ E.1 ⊆ G.1), (1 : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun E _ ↦ ?_
      by_cases h1 : U.1 ⊆ E.1 <;> by_cases h2 : E.1 ⊆ G.1 <;> simp [h1, h2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard :
        (Finset.univ.filter (fun E : P01Subset N M ↦ U.1 ⊆ E.1 ∧ E.1 ⊆ G.1)).card =
          (G.1 \ U.1).card := by
      symm
      refine Finset.card_bij (fun y hy ↦ ⟨G.1.erase y, by
          rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp hy).1, G.2]; omega⟩)
        (fun y hy ↦ ?_)
        (fun y₁ hy₁ y₂ hy₂ heq ↦ ?_)
        (fun E hE ↦ ?_)
      · rcases Finset.mem_sdiff.mp hy with ⟨hyG, hyU⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, Finset.erase_subset y G.1⟩
        intro z hzU
        exact Finset.mem_erase.mpr ⟨fun hzy ↦ hyU (hzy ▸ hzU), hUG hzU⟩
      · have hset : G.1.erase y₁ = G.1.erase y₂ := Subtype.mk.inj heq
        by_contra hne
        have hy1 : y₁ ∈ G.1.erase y₂ := Finset.mem_erase.mpr ⟨hne, (Finset.mem_sdiff.mp hy₁).1⟩
        rw [← hset] at hy1
        exact (Finset.mem_erase.mp hy1).1 rfl
      · rcases (Finset.mem_filter.mp hE).2 with ⟨hUE, hEG⟩
        have hcd : (G.1 \ E.1).card = 1 := by
          rw [Finset.card_sdiff_of_subset hEG, G.2, E.2]; omega
        obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hcd
        have hy_mem : y ∈ G.1 \ E.1 := hy_eq ▸ Finset.mem_singleton_self y
        rcases Finset.mem_sdiff.mp hy_mem with ⟨hyG, hyE⟩
        refine ⟨y, Finset.mem_sdiff.mpr ⟨hyG, fun hyU ↦ hyE (hUE hyU)⟩, Subtype.ext ?_⟩
        ext z
        simp only [Finset.mem_erase]
        constructor
        · rintro ⟨hzy, hzG⟩
          by_cases hzE : z ∈ E.1
          · exact hzE
          · exfalso
            have hz_in : z ∈ G.1 \ E.1 := Finset.mem_sdiff.mpr ⟨hzG, hzE⟩
            rw [hy_eq, Finset.mem_singleton] at hz_in
            exact hzy hz_in
        · intro hzE
          exact ⟨fun hzy ↦ hyE (hzy ▸ hzE), hEG hzE⟩
    rw [hcard, Finset.card_sdiff_of_subset hUG, G.2, U.2]
  · rw [ite_eq_right hUG, mul_zero]
    refine Finset.sum_eq_zero fun E _ ↦ ?_
    by_cases h1 : U.1 ⊆ E.1
    · have h2 : ¬ E.1 ⊆ G.1 := fun hEG ↦ hUG (h1.trans hEG)
      simp [h1, h2]
    · simp [h1]

theorem jDownGenMat_zero_mul_transpose (N : ℕ) :
    jDownGenMat N 0 1 * (jDownGenMat N 0 1)ᵀ = (N : ℝ) • 1 := by
  ext E F
  have hE0 : E.1 = ∅ := Finset.card_eq_zero.mp E.2
  have hF0 : F.1 = ∅ := Finset.card_eq_zero.mp F.2
  have hEF : E = F := Subtype.ext (hE0.trans hF0.symm)
  subst hEF
  simp only [Matrix.mul_apply, jDownGenMat, Matrix.transpose_apply, Matrix.of_apply,
    hE0, Finset.empty_subset, ↓reduceIte, mul_one, Finset.sum_const, Finset.card_univ,
    card_symSubset, Nat.choose_one_right, nsmul_eq_mul, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul]

theorem jDownGenMat_succ_mul_transpose {N M : ℕ} (hN : 2 * M + 2 ≤ N) :
    jDownGenMat N (M + 1) (M + 2) * (jDownGenMat N (M + 1) (M + 2))ᵀ =
      (jDownGenMat N M (M + 1))ᵀ * jDownGenMat N M (M + 1) +
        ((N - 2 * M - 2 : ℕ) : ℝ) • 1 := by
  ext E F
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
    jDownGenMat, Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
  have hlhs :
      (∑ G : P01Subset N (M + 2),
        (if E.1 ⊆ G.1 then (1 : ℝ) else 0) * (if F.1 ⊆ G.1 then 1 else 0)) =
      ((Finset.univ.filter (fun G : P01Subset N (M + 2) ↦ E.1 ⊆ G.1 ∧ F.1 ⊆ G.1)).card : ℝ) := by
    rw [← nsmul_one, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun G _ ↦ ?_
    by_cases h1 : E.1 ⊆ G.1 <;> by_cases h2 : F.1 ⊆ G.1 <;> simp [h1, h2]
  have hrhs :
      (∑ T : P01Subset N M,
        (if T.1 ⊆ E.1 then (1 : ℝ) else 0) * (if T.1 ⊆ F.1 then 1 else 0)) =
      ((Finset.univ.filter (fun T : P01Subset N M ↦ T.1 ⊆ E.1 ∧ T.1 ⊆ F.1)).card : ℝ) := by
    rw [← nsmul_one, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ ↦ ?_
    by_cases h1 : T.1 ⊆ E.1 <;> by_cases h2 : T.1 ⊆ F.1 <;> simp [h1, h2]
  rw [hlhs, hrhs]
  by_cases hEF : E = F
  · subst hEF
    rw [ite_eq_left rfl, mul_one]
    have hc1 :
        (Finset.univ.filter (fun G : P01Subset N (M + 2) ↦ E.1 ⊆ G.1 ∧ E.1 ⊆ G.1)).card =
          E.1ᶜ.card := by
      symm
      refine Finset.card_bij (fun x hx ↦ ⟨insert x E.1, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hx), E.2]⟩)
        (fun x _ ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.subset_insert x E.1, Finset.subset_insert x E.1⟩)
        (fun x₁ hx₁ x₂ _ heq ↦ ?_)
        (fun G hG ↦ ?_)
      · have hset : insert x₁ E.1 = insert x₂ E.1 := Subtype.mk.inj heq
        have hx1 : x₁ ∈ insert x₂ E.1 := hset ▸ Finset.mem_insert_self x₁ E.1
        rcases Finset.mem_insert.mp hx1 with rfl | hxE
        · rfl
        · exact absurd hxE (Finset.mem_compl.mp hx₁)
      · have hsub : E.1 ⊆ G.1 := (Finset.mem_filter.mp hG).2.1
        have hcd : (G.1 \ E.1).card = 1 := by
          rw [Finset.card_sdiff_of_subset hsub, G.2, E.2]; omega
        obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hcd
        have hx_mem : x ∈ G.1 \ E.1 := hx_eq ▸ Finset.mem_singleton_self x
        rcases Finset.mem_sdiff.mp hx_mem with ⟨hxG, hxE⟩
        refine ⟨x, Finset.mem_compl.mpr hxE, Subtype.ext ?_⟩
        ext z
        simp only [Finset.mem_insert]
        exact ⟨fun h ↦ h.elim (fun hzx ↦ hzx ▸ hxG) (fun hzE ↦ hsub hzE),
          fun hzG ↦ by
            by_cases hzE : z ∈ E.1
            · exact Or.inr hzE
            · have hz_s : z ∈ G.1 \ E.1 := Finset.mem_sdiff.mpr ⟨hzG, hzE⟩
              rw [hx_eq, Finset.mem_singleton] at hz_s
              exact Or.inl hz_s⟩
    have hc2 :
        (Finset.univ.filter (fun T : P01Subset N M ↦ T.1 ⊆ E.1 ∧ T.1 ⊆ E.1)).card =
          E.1.card := by
      symm
      refine Finset.card_bij (fun y hy ↦ ⟨E.1.erase y, by
          rw [Finset.card_erase_of_mem hy, E.2]; omega⟩)
        (fun y _ ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.erase_subset y E.1, Finset.erase_subset y E.1⟩)
        (fun y₁ hy₁ y₂ _ heq ↦ ?_)
        (fun T hT ↦ ?_)
      · have hset : E.1.erase y₁ = E.1.erase y₂ := Subtype.mk.inj heq
        by_contra hne
        have hy1 : y₁ ∈ E.1.erase y₂ := Finset.mem_erase.mpr ⟨hne, hy₁⟩
        rw [← hset] at hy1
        exact (Finset.mem_erase.mp hy1).1 rfl
      · have hsub : T.1 ⊆ E.1 := (Finset.mem_filter.mp hT).2.1
        have hcd : (E.1 \ T.1).card = 1 := by
          rw [Finset.card_sdiff_of_subset hsub, E.2, T.2]; omega
        obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hcd
        have hy_mem : y ∈ E.1 \ T.1 := hy_eq ▸ Finset.mem_singleton_self y
        rcases Finset.mem_sdiff.mp hy_mem with ⟨hyE, hyT⟩
        refine ⟨y, hyE, Subtype.ext ?_⟩
        ext z
        simp only [Finset.mem_erase]
        exact ⟨fun ⟨hzy, hzE⟩ ↦ by
            by_cases hzT : z ∈ T.1
            · exact hzT
            · exfalso
              have hz_s : z ∈ E.1 \ T.1 := Finset.mem_sdiff.mpr ⟨hzE, hzT⟩
              rw [hy_eq, Finset.mem_singleton] at hz_s
              exact hzy hz_s,
          fun hzT ↦ ⟨fun hzy ↦ hyT (hzy ▸ hzT), hsub hzT⟩⟩
    have hcompl : E.1ᶜ.card = N - (M + 1) := by
      have hle : E.1.card ≤ N := E.1.card_le_univ.trans_eq (Fintype.card_fin N)
      rw [Finset.card_compl, Fintype.card_fin, E.2]
    rw [hc1, hc2, hcompl, E.2]
    exact_mod_cast (by omega : N - (M + 1) = (M + 1) + (N - 2 * M - 2))
  · rw [ite_eq_right hEF, mul_zero, add_zero]
    have hinter_le : (E.1 ∩ F.1).card ≤ M := by
      have hle1 : (E.1 ∩ F.1).card ≤ M + 1 :=
        (Finset.card_le_card Finset.inter_subset_left).trans_eq E.2
      by_contra hgt
      have heq_card : (E.1 ∩ F.1).card = M + 1 := by omega
      have h1 : E.1 ∩ F.1 = E.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [E.2, heq_card])
      have h2 : E.1 ∩ F.1 = F.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [F.2, heq_card])
      exact hEF (Subtype.ext (h1.symm.trans h2))
    by_cases hinter_eq : (E.1 ∩ F.1).card = M
    · have hunion_card : (E.1 ∪ F.1).card = M + 2 := by
        have h := Finset.card_union_add_card_inter E.1 F.1
        rw [E.2, F.2, hinter_eq] at h
        omega
      have hf1 :
          Finset.univ.filter (fun G : P01Subset N (M + 2) ↦ E.1 ⊆ G.1 ∧ F.1 ⊆ G.1) =
            {⟨E.1 ∪ F.1, hunion_card⟩} := by
        ext G
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hEG, hFG⟩
          exact Subtype.ext (Finset.eq_of_subset_of_card_le
            (Finset.union_subset hEG hFG) (by rw [G.2, hunion_card])).symm
        · rintro rfl
          exact ⟨Finset.subset_union_left, Finset.subset_union_right⟩
      have hf2 :
          Finset.univ.filter (fun T : P01Subset N M ↦ T.1 ⊆ E.1 ∧ T.1 ⊆ F.1) =
            {⟨E.1 ∩ F.1, hinter_eq⟩} := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hTE, hTF⟩
          exact Subtype.ext (Finset.eq_of_subset_of_card_le
            (Finset.subset_inter hTE hTF) (by rw [T.2, hinter_eq]))
        · rintro rfl
          exact ⟨Finset.inter_subset_left, Finset.inter_subset_right⟩
      rw [hf1, hf2, Finset.card_singleton, Finset.card_singleton]
    · have hinter_lt : (E.1 ∩ F.1).card < M := lt_of_le_of_ne hinter_le hinter_eq
      have hunion_gt : M + 2 < (E.1 ∪ F.1).card := by
        have h := Finset.card_union_add_card_inter E.1 F.1
        rw [E.2, F.2] at h
        omega
      have hf1 :
          Finset.univ.filter (fun G : P01Subset N (M + 2) ↦ E.1 ⊆ G.1 ∧ F.1 ⊆ G.1) = ∅ := by
        ext G
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hEG, hFG⟩
        have hle := (Finset.card_le_card (Finset.union_subset hEG hFG)).trans_eq G.2
        omega
      have hf2 :
          Finset.univ.filter (fun T : P01Subset N M ↦ T.1 ⊆ E.1 ∧ T.1 ⊆ F.1) = ∅ := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hTE, hTF⟩
        have hle := T.2.symm.le.trans (Finset.card_le_card (Finset.subset_inter hTE hTF))
        omega
      rw [hf1, hf2, Finset.card_empty, Finset.card_empty]

/-! ## Section 3: Spectral Projectors & Polar Step-Up Isometry `stepUpFrom` -/

private lemma matrix_sum_mul {ι₁ ι₂ ι₃ κ : Type*} [Fintype ι₂]
    (s : Finset κ) (f : κ → Matrix ι₁ ι₂ ℝ) (B : Matrix ι₂ ι₃ ℝ) :
    (∑ k ∈ s, f k) * B = ∑ k ∈ s, f k * B := by
  ext i l
  simp only [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private lemma matrix_mul_sum {ι₁ ι₂ ι₃ κ : Type*} [Fintype ι₂]
    (A : Matrix ι₁ ι₂ ℝ) (s : Finset κ) (f : κ → Matrix ι₂ ι₃ ℝ) :
    A * (∑ k ∈ s, f k) = ∑ k ∈ s, A * f k := by
  ext i l
  simp only [Matrix.mul_apply, Matrix.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

private lemma proj_sum_mul_sum {ι : Type*} [Fintype ι]
    {P : ℕ → Matrix ι ι ℝ}
    (horth : ∀ i j, P i * P j = if i = j then P i else 0)
    (K : ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ Finset.range K, a i • P i) * (∑ j ∈ Finset.range K, b j • P j) =
      ∑ i ∈ Finset.range K, (a i * b i) • P i := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mul_sum]
  have hsingle :
      (∑ j ∈ Finset.range K, (a i • P i) * (b j • P j)) =
        (a i • P i) * (b i • P i) := by
    refine Finset.sum_eq_single i (fun j _ hji ↦ ?_) (fun hni ↦ absurd hi hni)
    rw [Matrix.smul_mul, Matrix.mul_smul, horth i j, ite_eq_right hji.symm, smul_zero, smul_zero]
  rw [hsingle, Matrix.smul_mul, Matrix.mul_smul, horth i i, ite_eq_left rfl, smul_smul]

private structure EigProjInv (N M : ℕ) : Prop where
  sym : ∀ j, (eigProj N M j)ᵀ = eigProj N M j
  orth : ∀ i j, eigProj N M i * eigProj N M j = if i = j then eigProj N M i else 0
  vanish : ∀ j, M < j → eigProj N M j = 0
  sum_one : (∑ j ∈ Finset.range (M + 1), eigProj N M j) = 1
  b_cov : 2 * M + 2 ≤ N →
    jDownGenMat N M (M + 1) * (jDownGenMat N M (M + 1))ᵀ =
      ∑ j ∈ Finset.range (M + 1), (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) • eigProj N M j

private lemma stepUpScale_transpose_of_inv {N M : ℕ} (hinv : EigProjInv N M) :
    (stepUpScale N M)ᵀ = stepUpScale N M := by
  unfold stepUpScale stepUpScaleOf
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Matrix.transpose_smul, hinv.sym j]

private lemma stepUpMat_transpose_mul_self_of_inv {N M : ℕ}
    (hinv : EigProjInv N M) (hN : 2 * M + 2 ≤ N) :
    (stepUpMat N M)ᵀ * stepUpMat N M = 1 := by
  unfold stepUpMat stepUpMatOf
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, stepUpScale_transpose_of_inv hinv]
  have hassoc :
      stepUpScale N M * jDownGenMat N M (M + 1) *
          ((jDownGenMat N M (M + 1))ᵀ * stepUpScale N M) =
        (stepUpScale N M * (jDownGenMat N M (M + 1) * (jDownGenMat N M (M + 1))ᵀ)) *
          stepUpScale N M := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, hinv.b_cov hN]
  unfold stepUpScale stepUpScaleOf
  rw [proj_sum_mul_sum hinv.orth, proj_sum_mul_sum hinv.orth]
  have hcongr :
      (∑ j ∈ Finset.range (M + 1),
        (1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
            (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
          (1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ))) • eigProj N M j) =
      ∑ j ∈ Finset.range (M + 1), eigProj N M j := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpos : (0 : ℝ) < (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))
    have hsq : √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have h1 :
        1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
            (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
          (1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ)) = 1 := by
      calc 1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
              (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
            (1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ))
          = (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) /
              (√(((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
                √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ)) := by ring
        _ = 1 := by rw [Real.mul_self_sqrt hpos.le, div_self hpos.ne']
    rw [h1, one_smul]
  rw [hcongr, hinv.sum_one]

private lemma eigProjInv_zero (N : ℕ) : EigProjInv N 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    unfold eigProj
    by_cases hj : j = 0 <;> simp [hj]
  · intro i j
    rcases i with _ | i <;> rcases j with _ | j <;> simp [eigProj]
  · intro j hj
    unfold eigProj
    have hne : j ≠ 0 := by omega
    simp [hne]
  · simp [eigProj]
  · intro _
    rw [jDownGenMat_zero_mul_transpose]
    simp [eigProj]

private lemma eigProjInv_succ {N M : ℕ} (hN : 2 * (M + 1) ≤ N)
    (ih : EigProjInv N M) : EigProjInv N (M + 1) := by
  have hΨ : (stepUpMat N M)ᵀ * stepUpMat N M = 1 :=
    stepUpMat_transpose_mul_self_of_inv ih (by omega)
  set Ψ := stepUpMat N M
  have heig_le (j : ℕ) (hj : j ≤ M) : eigProj N (M + 1) j = Ψ * eigProj N M j * Ψᵀ := by
    rw [eigProj]
    exact ite_eq_left hj
  have heig_top : eigProj N (M + 1) (M + 1) = 1 - Ψ * Ψᵀ := by
    rw [eigProj]
    have hnot : ¬ M + 1 ≤ M := by omega
    rw [ite_eq_right hnot, ite_eq_left rfl]
  have heig_gt (j : ℕ) (hj : M + 1 < j) : eigProj N (M + 1) j = 0 := by
    rw [eigProj]
    have h1 : ¬ j ≤ M := by omega
    have h2 : j ≠ M + 1 := by omega
    rw [ite_eq_right h1, ite_eq_right h2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ≤ M
    · rw [heig_le j hj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        ih.sym j, Matrix.mul_assoc]
    · by_cases hj1 : j = M + 1
      · subst hj1
        rw [heig_top, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
          Matrix.transpose_transpose]
      · rw [heig_gt j (by omega), Matrix.transpose_zero]
  · intro i j
    by_cases hi : i ≤ M
    · by_cases hj : j ≤ M
      · rw [heig_le i hi, heig_le j hj]
        have hmid : (Ψ * eigProj N M i * Ψᵀ) * (Ψ * eigProj N M j * Ψᵀ) =
            Ψ * (eigProj N M i * eigProj N M j) * Ψᵀ := by
          calc (Ψ * eigProj N M i * Ψᵀ) * (Ψ * eigProj N M j * Ψᵀ)
              = (Ψ * eigProj N M i) * ((Ψᵀ * Ψ) * (eigProj N M j * Ψᵀ)) := by
                simp only [Matrix.mul_assoc]
            _ = Ψ * (eigProj N M i * eigProj N M j) * Ψᵀ := by
                rw [hΨ, Matrix.one_mul]; simp only [Matrix.mul_assoc]
        rw [hmid, ih.orth i j]
        by_cases hij : i = j
        · subst hij; rw [ite_eq_left rfl, ite_eq_left rfl]
        · rw [ite_eq_right hij, ite_eq_right hij, Matrix.mul_zero, Matrix.zero_mul]
      · by_cases hj1 : j = M + 1
        · subst hj1
          have hne : i ≠ M + 1 := by omega
          rw [ite_eq_right hne, heig_le i hi, heig_top, Matrix.mul_sub, Matrix.mul_one]
          have hcancel : (Ψ * eigProj N M i * Ψᵀ) * (Ψ * Ψᵀ) = Ψ * eigProj N M i * Ψᵀ := by
            calc (Ψ * eigProj N M i * Ψᵀ) * (Ψ * Ψᵀ)
                = (Ψ * eigProj N M i) * (Ψᵀ * Ψ) * Ψᵀ := by simp only [Matrix.mul_assoc]
              _ = Ψ * eigProj N M i * Ψᵀ := by rw [hΨ, Matrix.mul_one]
          rw [hcancel, sub_self]
        · have hne : i ≠ j := by omega
          rw [ite_eq_right hne, heig_gt j (by omega), Matrix.mul_zero]
    · by_cases hi1 : i = M + 1
      · subst hi1
        by_cases hj : j ≤ M
        · have hne : M + 1 ≠ j := by omega
          rw [ite_eq_right hne, heig_top, heig_le j hj, Matrix.sub_mul, Matrix.one_mul]
          have hcancel : (Ψ * Ψᵀ) * (Ψ * eigProj N M j * Ψᵀ) = Ψ * eigProj N M j * Ψᵀ := by
            calc (Ψ * Ψᵀ) * (Ψ * eigProj N M j * Ψᵀ)
                = Ψ * (Ψᵀ * Ψ) * (eigProj N M j * Ψᵀ) := by simp only [Matrix.mul_assoc]
              _ = Ψ * eigProj N M j * Ψᵀ := by
                rw [hΨ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          rw [hcancel, sub_self]
        · by_cases hj1 : j = M + 1
          · subst hj1
            rw [ite_eq_left rfl, heig_top, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
              Matrix.mul_one]
            have hcancel : (Ψ * Ψᵀ) * (Ψ * Ψᵀ) = Ψ * Ψᵀ := by
              calc (Ψ * Ψᵀ) * (Ψ * Ψᵀ)
                  = Ψ * (Ψᵀ * Ψ) * Ψᵀ := by simp only [Matrix.mul_assoc]
                _ = Ψ * Ψᵀ := by rw [hΨ, Matrix.mul_one]
            rw [hcancel]
            abel
          · have hne : M + 1 ≠ j := by omega
            rw [ite_eq_right hne, heig_gt j (by omega), Matrix.mul_zero]
      · by_cases hij : i = j
        · subst hij
          rw [heig_gt i (by omega), Matrix.zero_mul, ite_eq_left rfl]
        · rw [heig_gt i (by omega), Matrix.zero_mul, ite_eq_right hij]
  · intro j hj
    exact heig_gt j hj
  · have hsum_low :
        (∑ j ∈ Finset.range (M + 1), eigProj N (M + 1) j) = Ψ * Ψᵀ := by
      have hc :
          (∑ j ∈ Finset.range (M + 1), eigProj N (M + 1) j) =
            ∑ j ∈ Finset.range (M + 1), Ψ * eigProj N M j * Ψᵀ :=
        Finset.sum_congr rfl fun j hj ↦ heig_le j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      rw [hc, ← matrix_sum_mul, ← matrix_mul_sum, ih.sum_one, Matrix.mul_one]
    rw [Finset.sum_range_succ, hsum_low, heig_top, add_sub_cancel]
  · intro hN2
    let S_inv : Matrix (P01Subset N M) (P01Subset N M) ℝ :=
      ∑ j ∈ Finset.range (M + 1),
        √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ) • eigProj N M j
    have hSS : stepUpScale N M * S_inv = 1 := by
      dsimp only [stepUpScale, stepUpScaleOf, S_inv]
      rw [proj_sum_mul_sum ih.orth]
      have hc :
          (∑ j ∈ Finset.range (M + 1),
            (1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ) *
              √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ)) • eigProj N M j) =
          ∑ j ∈ Finset.range (M + 1), eigProj N M j := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hpos : (0 : ℝ) < (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))
        rw [one_div_mul_cancel (Real.sqrt_pos.mpr hpos).ne', one_smul]
      rw [hc, ih.sum_one]
    have hSinv_sym : S_invᵀ = S_inv := by
      dsimp only [S_inv]
      rw [Matrix.transpose_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [Matrix.transpose_smul, ih.sym j]
    have hBt_eq : (jDownGenMat N M (M + 1))ᵀ = Ψ * S_inv := by
      calc (jDownGenMat N M (M + 1))ᵀ
          = (jDownGenMat N M (M + 1))ᵀ * 1 := (Matrix.mul_one _).symm
        _ = (jDownGenMat N M (M + 1))ᵀ * (stepUpScale N M * S_inv) := by rw [hSS]
        _ = Ψ * S_inv := (Matrix.mul_assoc _ _ _).symm
    have hB_eq : jDownGenMat N M (M + 1) = S_inv * Ψᵀ := by
      calc jDownGenMat N M (M + 1)
          = ((jDownGenMat N M (M + 1))ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
        _ = (Ψ * S_inv)ᵀ := by rw [hBt_eq]
        _ = S_inv * Ψᵀ := by rw [Matrix.transpose_mul, hSinv_sym]
    have hBtB :
        (jDownGenMat N M (M + 1))ᵀ * jDownGenMat N M (M + 1) =
          ∑ j ∈ Finset.range (M + 1),
            (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) • eigProj N (M + 1) j := by
      rw [hBt_eq, hB_eq]
      have hassoc : (Ψ * S_inv) * (S_inv * Ψᵀ) = Ψ * (S_inv * S_inv) * Ψᵀ := by
        simp only [Matrix.mul_assoc]
      rw [hassoc]
      have hsq :
          S_inv * S_inv =
            ∑ j ∈ Finset.range (M + 1),
              (((M + 1 - j) * (N - M - j) : ℕ) : ℝ) • eigProj N M j := by
        dsimp only [S_inv]
        rw [proj_sum_mul_sum ih.orth]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
      rw [hsq, matrix_mul_sum, matrix_sum_mul]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Matrix.mul_smul, Matrix.smul_mul, heig_le j hjM]
    have hsum1 :
        (∑ j ∈ Finset.range (M + 2), eigProj N (M + 1) j) = 1 := by
      have hlow : (∑ j ∈ Finset.range (M + 1), eigProj N (M + 1) j) = Ψ * Ψᵀ := by
        have hc :
            (∑ j ∈ Finset.range (M + 1), eigProj N (M + 1) j) =
              ∑ j ∈ Finset.range (M + 1), Ψ * eigProj N M j * Ψᵀ :=
          Finset.sum_congr rfl fun j hj ↦ heig_le j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        rw [hc, ← matrix_sum_mul, ← matrix_mul_sum, ih.sum_one, Matrix.mul_one]
      rw [Finset.sum_range_succ, hlow, heig_top, add_sub_cancel]
    rw [jDownGenMat_succ_mul_transpose (by omega), hBtB, ← hsum1, Finset.smul_sum,
      Finset.sum_range_succ _ (M + 1), Finset.sum_range_succ _ (M + 1),
      ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [← add_smul]
      congr 1
      have hnat :
          (M + 1 - j) * (N - M - j) + (N - 2 * M - 2) =
            (M + 1 + 1 - j) * (N - (M + 1) - j) := by
        set a := M - j
        set b := N - 2 * M - 2
        have h1 : M + 1 - j = a + 1 := by omega
        have h2 : N - M - j = a + b + 2 := by omega
        have h3 : M + 1 + 1 - j = a + 2 := by omega
        have h4 : N - (M + 1) - j = a + b + 1 := by omega
        rw [h1, h2, h3, h4]
        ring
      exact_mod_cast hnat
    · congr 1
      have h1 : M + 1 + 1 - (M + 1) = 1 := by omega
      have hnat : N - 2 * M - 2 = (M + 1 + 1 - (M + 1)) * (N - (M + 1) - (M + 1)) := by
        rw [h1, one_mul]; omega
      exact_mod_cast hnat

private lemma eigProjInv_of_two_mul_le {N : ℕ} :
    ∀ {M : ℕ}, 2 * M ≤ N → EigProjInv N M
  | 0, _ => eigProjInv_zero N
  | M + 1, hN => eigProjInv_succ hN (eigProjInv_of_two_mul_le (by omega))

theorem eigProj_transpose {N M : ℕ} (hN : 2 * M ≤ N) (j : ℕ) :
    (eigProj N M j)ᵀ = eigProj N M j :=
  (eigProjInv_of_two_mul_le hN).sym j

theorem eigProj_mul_eigProj {N M : ℕ} (hN : 2 * M ≤ N) (i j : ℕ) :
    eigProj N M i * eigProj N M j = if i = j then eigProj N M i else 0 :=
  (eigProjInv_of_two_mul_le hN).orth i j

theorem stepUpMat_transpose_mul_self {N M : ℕ} (hN : 2 * (M + 1) ≤ N) :
    (stepUpMat N M)ᵀ * stepUpMat N M = 1 :=
  stepUpMat_transpose_mul_self_of_inv (eigProjInv_of_two_mul_le (by omega)) (by omega)

theorem stepUpFrom_self (N M : ℕ) : stepUpFrom N M M = 1 := by
  cases M <;> simp [stepUpFrom]

theorem stepUpFrom_succ {N M₁ M₂ : ℕ} (h12 : M₁ ≤ M₂) :
    stepUpFrom N M₁ (M₂ + 1) = stepUpMat N M₂ * stepUpFrom N M₁ M₂ := by
  have hne : M₁ ≠ M₂ + 1 := by omega
  rw [stepUpFrom, dite_eq_right hne]

theorem stepUpFrom_transpose_mul_self {N M₁ : ℕ} :
    ∀ {M₂ : ℕ}, M₁ ≤ M₂ → 2 * M₂ ≤ N →
      (stepUpFrom N M₁ M₂)ᵀ * stepUpFrom N M₁ M₂ = 1
  | 0, h12, _ => by
    obtain rfl : M₁ = 0 := by omega
    rw [stepUpFrom_self, Matrix.transpose_one, Matrix.one_mul]
  | M₂ + 1, h12, hN => by
    by_cases heq : M₁ = M₂ + 1
    · subst heq
      rw [stepUpFrom_self, Matrix.transpose_one, Matrix.one_mul]
    · have hle : M₁ ≤ M₂ := by omega
      rw [stepUpFrom_succ hle, Matrix.transpose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc _ (stepUpMat N M₂), stepUpMat_transpose_mul_self hN, Matrix.one_mul,
        stepUpFrom_transpose_mul_self hle (by omega)]

/-! ## Section 4: Closed-Form Harmonic Kernel Lift & Exact Step-Up Covariance -/

theorem jDownGenMat_mulVec_harmKerBase_zero {N k : ℕ} {R : Finset (Fin N)}
    (hkr : k + 1 ≤ R.card) (hN : k + 1 + R.card ≤ N) :
    jDownGenMat N k (k + 1) *ᵥ harmKerBase N R (k + 1) = 0 := by
  funext T
  simp only [Matrix.mulVec, dotProduct, jDownGenMat, Matrix.of_apply, harmKerBase, Pi.zero_apply,
    ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  set r := R.card
  set t := (T.1 ∩ R).card
  have htk : t ≤ k := (Finset.card_le_card Finset.inter_subset_left).trans_eq T.2
  have hbij :
      (∑ U ∈ Finset.univ.filter (fun U : P01Subset N (k + 1) ↦ T.1 ⊆ U.1),
        harmKerWeight N r (k + 1) (U.1 ∩ R).card) =
      ∑ x ∈ T.1ᶜ, harmKerWeight N r (k + 1) ((insert x T.1) ∩ R).card := by
    symm
    refine Finset.sum_bij (fun x hx ↦ ⟨insert x T.1, by
        rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hx), T.2]⟩)
      (fun x _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_insert x T.1⟩)
      (fun x₁ hx₁ x₂ _ heq ↦ ?_)
      (fun U hU ↦ ?_)
      (fun _ _ ↦ rfl)
    · have hset : insert x₁ T.1 = insert x₂ T.1 := Subtype.mk.inj heq
      have hx1 : x₁ ∈ insert x₂ T.1 := hset ▸ Finset.mem_insert_self x₁ T.1
      rcases Finset.mem_insert.mp hx1 with rfl | hxT
      · rfl
      · exact absurd hxT (Finset.mem_compl.mp hx₁)
    · have hsub : T.1 ⊆ U.1 := (Finset.mem_filter.mp hU).2
      have hcd : (U.1 \ T.1).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsub, U.2, T.2]; omega
      obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hcd
      have hx_mem : x ∈ U.1 \ T.1 := hx_eq ▸ Finset.mem_singleton_self x
      rcases Finset.mem_sdiff.mp hx_mem with ⟨hxU, hxT⟩
      refine ⟨x, Finset.mem_compl.mpr hxT, Subtype.ext ?_⟩
      ext z
      simp only [Finset.mem_insert]
      exact ⟨fun h ↦ h.elim (fun hzx ↦ hzx ▸ hxU) (fun hzT ↦ hsub hzT),
        fun hzU ↦ by
          by_cases hzT : z ∈ T.1
          · exact Or.inr hzT
          · have hz_s : z ∈ U.1 \ T.1 := Finset.mem_sdiff.mpr ⟨hzU, hzT⟩
            rw [hx_eq, Finset.mem_singleton] at hz_s
            exact Or.inl hz_s⟩
  rw [hbij, ← Finset.sum_filter_add_sum_filter_not (s := T.1ᶜ) (p := (· ∈ R))]
  have hf1 : T.1ᶜ.filter (· ∈ R) = R \ T.1 := by
    ext x; simp [Finset.mem_sdiff, and_comm]
  have hf2 : T.1ᶜ.filter (fun x ↦ x ∉ R) = (T.1 ∪ R)ᶜ := by
    ext x; simp
  rw [hf1, hf2]
  have hs1 :
      (∑ x ∈ R \ T.1, harmKerWeight N r (k + 1) ((insert x T.1) ∩ R).card) =
        ((r - t : ℕ) : ℝ) * harmKerWeight N r (k + 1) (t + 1) := by
    have hc :
        (∑ x ∈ R \ T.1, harmKerWeight N r (k + 1) ((insert x T.1) ∩ R).card) =
          ∑ _ ∈ R \ T.1, harmKerWeight N r (k + 1) (t + 1) := by
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      rcases Finset.mem_sdiff.mp hx with ⟨hxR, hxT⟩
      have hint : (insert x T.1) ∩ R = insert x (T.1 ∩ R) := by
        ext z; simp only [Finset.mem_inter, Finset.mem_insert]
        exact ⟨fun ⟨h, hzR⟩ ↦ h.elim Or.inl (fun hzT ↦ Or.inr ⟨hzT, hzR⟩),
          fun h ↦ h.elim (fun hzx ↦ ⟨Or.inl hzx, hzx ▸ hxR⟩) (fun ⟨hzT, hzR⟩ ↦ ⟨Or.inr hzT, hzR⟩)⟩
      have hx_nin : x ∉ T.1 ∩ R := fun h ↦ hxT (Finset.mem_inter.mp h).1
      rw [hint, Finset.card_insert_of_notMem hx_nin]
    have hcard_sdiff : (R \ T.1).card = r - t := by
      have h := Finset.card_sdiff_add_card_inter R T.1
      rw [Finset.inter_comm] at h
      omega
    rw [hc, Finset.sum_const, hcard_sdiff, nsmul_eq_mul]
  have hs2 :
      (∑ x ∈ (T.1 ∪ R)ᶜ, harmKerWeight N r (k + 1) ((insert x T.1) ∩ R).card) =
        ((N - r - (k - t) : ℕ) : ℝ) * harmKerWeight N r (k + 1) t := by
    have hc :
        (∑ x ∈ (T.1 ∪ R)ᶜ, harmKerWeight N r (k + 1) ((insert x T.1) ∩ R).card) =
          ∑ _ ∈ (T.1 ∪ R)ᶜ, harmKerWeight N r (k + 1) t := by
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hxR : x ∉ R := fun h ↦ Finset.mem_compl.mp hx (Finset.mem_union_right T.1 h)
      have hint : (insert x T.1) ∩ R = T.1 ∩ R := by
        ext z; simp only [Finset.mem_inter, Finset.mem_insert]
        exact ⟨fun ⟨h, hzR⟩ ↦ ⟨h.resolve_left (fun hzx ↦ hxR (hzx ▸ hzR)), hzR⟩,
          fun ⟨hzT, hzR⟩ ↦ ⟨Or.inr hzT, hzR⟩⟩
      rw [hint]
    have hu_card : (T.1 ∪ R).card = k + r - t := by
      have h := Finset.card_union_add_card_inter T.1 R
      rw [T.2] at h; omega
    have hc_card : (T.1 ∪ R)ᶜ.card = N - r - (k - t) := by
      have hle : (T.1 ∪ R).card ≤ N := (T.1 ∪ R).card_le_univ.trans_eq (Fintype.card_fin N)
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    rw [hc, Finset.sum_const, hc_card, nsmul_eq_mul]
  rw [hs1, hs2]
  set u := k - t
  have hu1 : k + 1 - (t + 1) = u := by omega
  have hu2 : k + 1 - t = u + 1 := by omega
  unfold harmKerWeight
  rw [hu1, hu2]
  have hd0_pos : (0 : ℝ) < ((N - r).choose u : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hd1_pos : (0 : ℝ) < ((N - r).choose (u + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hrel1 :
      ((N - r).choose (u + 1) : ℝ) * ((u + 1 : ℕ) : ℝ) =
        ((N - r).choose u : ℝ) * ((N - r - u : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq (N - r) u
  have hrel2 :
      ((r - t : ℕ) : ℝ) * ((r - (t + 1)).choose u : ℝ) =
        ((u + 1 : ℕ) : ℝ) * ((r - t).choose (u + 1) : ℝ) := by
    have hp := p01_choose_mul_succ (r - (t + 1)) u
    have hr1 : r - (t + 1) + 1 = r - t := by omega
    rw [hr1] at hp
    exact_mod_cast hp
  have hpow : (-1 : ℝ) ^ (u + 1) = - ((-1 : ℝ) ^ u) := by rw [pow_succ]; ring
  rw [hpow]
  rw [← mul_div_assoc, ← mul_div_assoc, div_add_div _ _ hd0_pos.ne' hd1_pos.ne', div_eq_zero_iff]
  left
  linear_combination
    ((-1 : ℝ) ^ u * ((N - r).choose (u + 1) : ℝ)) * hrel2 +
      ((-1 : ℝ) ^ u * ((r - t).choose (u + 1) : ℝ)) * hrel1

private lemma eigProj_mulVec_harmKerLift_base {N w : ℕ} {R : Finset (Fin N)}
    (hwr : w ≤ R.card) (hwN : w + R.card ≤ N) (h2w : 2 * w ≤ N) (j : ℕ) :
    eigProj N w j *ᵥ harmKerLift N R w w =
      if j = w then harmKerLift N R w w else 0 := by
  have hbase : harmKerLift N R w w = harmKerBase N R w := by
    unfold harmKerLift
    rw [jDownGenMat_self, Matrix.transpose_one, Matrix.one_mulVec]
  cases w with
  | zero =>
    unfold eigProj
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  | succ k =>
    have hker : jDownGenMat N k (k + 1) *ᵥ harmKerLift N R (k + 1) (k + 1) = 0 := by
      rw [hbase]
      exact jDownGenMat_mulVec_harmKerBase_zero hwr hwN
    have hΨt : (stepUpMat N k)ᵀ *ᵥ harmKerLift N R (k + 1) (k + 1) = 0 := by
      unfold stepUpMat stepUpMatOf
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec, hker,
        Matrix.mulVec_zero]
    unfold eigProj
    change (if j ≤ k then stepUpMat N k * eigProj N k j * (stepUpMat N k)ᵀ
      else if j = k + 1 then 1 - stepUpMat N k * (stepUpMat N k)ᵀ else 0) *ᵥ
        harmKerLift N R (k + 1) (k + 1) = _
    by_cases hj : j ≤ k
    · have hne : j ≠ k + 1 := by omega
      rw [ite_eq_left hj, ite_eq_right hne, ← Matrix.mulVec_mulVec, hΨt, Matrix.mulVec_zero]
    · rw [ite_eq_right hj]
      by_cases hj1 : j = k + 1
      · subst hj1
        rw [ite_eq_left rfl, ite_eq_left rfl, Matrix.sub_mulVec, Matrix.one_mulVec,
          ← Matrix.mulVec_mulVec, hΨt, Matrix.mulVec_zero, sub_zero]
      · rw [ite_eq_right hj1, ite_eq_right hj1, Matrix.zero_mulVec]

theorem eigProj_mulVec_harmKerLift {N w : ℕ} {R : Finset (Fin N)}
    (hwr : w ≤ R.card) :
    ∀ {M : ℕ}, w ≤ M → M + R.card ≤ N → 2 * M ≤ N →
      ∀ j : ℕ, eigProj N M j *ᵥ harmKerLift N R w M =
        if j = w then harmKerLift N R w M else 0
  | 0, hwM, hMrN, h2M, j => by
    obtain rfl : w = 0 := by omega
    exact eigProj_mulVec_harmKerLift_base hwr hMrN h2M j
  | M + 1, hwM, hMrN, h2M, j => by
    by_cases heq : w = M + 1
    · subst heq
      exact eigProj_mulVec_harmKerLift_base hwr hMrN h2M j
    · have hw_le : w ≤ M := by omega
      have ih := fun j' ↦ eigProj_mulVec_harmKerLift hwr hw_le (by omega) (by omega) j'
      have hΨ : (stepUpMat N M)ᵀ * stepUpMat N M = 1 := stepUpMat_transpose_mul_self h2M
      set c : ℝ := 1 / √(((M + 1 - w) * (N - M - w) : ℕ) : ℝ)
      have hc_pos : 0 < c := by
        dsimp only [c]
        exact one_div_pos.mpr
          (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))))
      have hscale :
          stepUpScale N M *ᵥ harmKerLift N R w M = c • harmKerLift N R w M := by
        unfold stepUpScale stepUpScaleOf
        rw [Matrix.sum_mulVec]
        have hsingle :
            (∑ j' ∈ Finset.range (M + 1),
              ((1 / √(((M + 1 - j') * (N - M - j') : ℕ) : ℝ)) • eigProj N M j') *ᵥ
                harmKerLift N R w M) =
            (c • eigProj N M w) *ᵥ harmKerLift N R w M := by
          refine Finset.sum_eq_single w (fun j' _ hj'w ↦ ?_)
            (fun hnw ↦ absurd (Finset.mem_range.mpr (by omega)) hnw)
          rw [Matrix.smul_mulVec, ih j', ite_eq_right hj'w, smul_zero]
        rw [hsingle, Matrix.smul_mulVec, ih w, ite_eq_left rfl]
      have hstep :
          stepUpMat N M *ᵥ harmKerLift N R w M =
            (c * ((M + 1 - w : ℕ) : ℝ)) • harmKerLift N R w (M + 1) := by
        unfold stepUpMat stepUpMatOf
        rw [← Matrix.mulVec_mulVec, hscale, Matrix.mulVec_smul]
        unfold harmKerLift
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, jDownGenMat_mul_succ hw_le,
          Matrix.transpose_smul, Matrix.smul_mulVec, smul_smul]
      set α : ℝ := c * ((M + 1 - w : ℕ) : ℝ)
      have hα_pos : 0 < α := mul_pos hc_pos (Nat.cast_pos.mpr (by omega))
      have hcov :
          eigProj N (M + 1) j *ᵥ (stepUpMat N M *ᵥ harmKerLift N R w M) =
            if j = w then stepUpMat N M *ᵥ harmKerLift N R w M else 0 := by
        unfold eigProj
        change (if j ≤ M then stepUpMat N M * eigProj N M j * (stepUpMat N M)ᵀ
          else if j = M + 1 then 1 - stepUpMat N M * (stepUpMat N M)ᵀ else 0) *ᵥ
            (stepUpMat N M *ᵥ harmKerLift N R w M) = _
        by_cases hjM : j ≤ M
        · rw [ite_eq_left hjM]
          have hmid :
              (stepUpMat N M * eigProj N M j * (stepUpMat N M)ᵀ) *ᵥ
                  (stepUpMat N M *ᵥ harmKerLift N R w M) =
                stepUpMat N M *ᵥ (eigProj N M j *ᵥ harmKerLift N R w M) := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ (stepUpMat N M)ᵀ (stepUpMat N M),
              hΨ, Matrix.mul_one, ← Matrix.mulVec_mulVec]
          rw [hmid, ih j]
          by_cases hjw : j = w
          · subst hjw; rw [ite_eq_left rfl, ite_eq_left rfl]
          · rw [ite_eq_right hjw, ite_eq_right hjw, Matrix.mulVec_zero]
        · rw [ite_eq_right hjM]
          have hjw : j ≠ w := by omega
          rw [ite_eq_right hjw]
          by_cases hj1 : j = M + 1
          · subst hj1
            rw [ite_eq_left rfl, Matrix.sub_mulVec, Matrix.one_mulVec,
              Matrix.mulVec_mulVec, Matrix.mul_assoc, hΨ, Matrix.mul_one, sub_self]
          · rw [ite_eq_right hj1, Matrix.zero_mulVec]
      rw [hstep, Matrix.mulVec_smul] at hcov
      have hsmul := congrArg ((α⁻¹ : ℝ) • ·) hcov
      rw [smul_smul, inv_mul_cancel₀ hα_pos.ne', one_smul] at hsmul
      rw [hsmul]
      by_cases hjw : j = w
      · subst hjw
        rw [ite_eq_left rfl, ite_eq_left rfl, smul_smul, inv_mul_cancel₀ hα_pos.ne', one_smul]
      · rw [ite_eq_right hjw, ite_eq_right hjw, smul_zero]

theorem stepUpMat_mulVec_harmKerLift {N w M : ℕ} {R : Finset (Fin N)}
    (hwr : w ≤ R.card) (hwM : w ≤ M) (hMrN : M + R.card ≤ N) (h2M : 2 * (M + 1) ≤ N) :
    stepUpMat N M *ᵥ harmKerLift N R w M =
      (((M + 1 - w : ℕ) : ℝ) / √(((M + 1 - w) * (N - M - w) : ℕ) : ℝ)) •
        harmKerLift N R w (M + 1) := by
  have heig := fun j ↦ eigProj_mulVec_harmKerLift hwr hwM hMrN (by omega) j
  have hscale :
      stepUpScale N M *ᵥ harmKerLift N R w M =
        (1 / √(((M + 1 - w) * (N - M - w) : ℕ) : ℝ)) • harmKerLift N R w M := by
    unfold stepUpScale stepUpScaleOf
    rw [Matrix.sum_mulVec]
    have hsingle :
        (∑ j ∈ Finset.range (M + 1),
          ((1 / √(((M + 1 - j) * (N - M - j) : ℕ) : ℝ)) • eigProj N M j) *ᵥ
            harmKerLift N R w M) =
        ((1 / √(((M + 1 - w) * (N - M - w) : ℕ) : ℝ)) • eigProj N M w) *ᵥ
          harmKerLift N R w M := by
      refine Finset.sum_eq_single w (fun j _ hjw ↦ ?_)
        (fun hnw ↦ absurd (Finset.mem_range.mpr (by omega)) hnw)
      rw [Matrix.smul_mulVec, heig j, ite_eq_right hjw, smul_zero]
    rw [hsingle, Matrix.smul_mulVec, heig w, ite_eq_left rfl]
  unfold stepUpMat stepUpMatOf
  rw [← Matrix.mulVec_mulVec, hscale, Matrix.mulVec_smul]
  unfold harmKerLift
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, jDownGenMat_mul_succ hwM,
    Matrix.transpose_smul, Matrix.smul_mulVec, smul_smul, one_div_mul_eq_div]

theorem stepUpFrom_mulVec_harmKerUnit {N w M₁ : ℕ} {R : Finset (Fin N)}
    (hwr : w ≤ R.card) (hw1 : w ≤ M₁)
    (hpos1 : 0 < finVecNorm (harmKerLift N R w M₁)) :
    ∀ {M₂ : ℕ}, M₁ ≤ M₂ → M₂ + R.card ≤ N → 2 * M₂ ≤ N →
      0 < finVecNorm (harmKerLift N R w M₂) ∧
      stepUpFrom N M₁ M₂ *ᵥ
          ((1 / finVecNorm (harmKerLift N R w M₁)) • harmKerLift N R w M₁) =
        (1 / finVecNorm (harmKerLift N R w M₂)) • harmKerLift N R w M₂
  | 0, h12, _, _ => by
    obtain rfl : M₁ = 0 := by omega
    exact ⟨hpos1, by rw [stepUpFrom_self, Matrix.one_mulVec]⟩
  | M₂ + 1, h12, hMrN, h2M => by
    by_cases heq : M₁ = M₂ + 1
    · subst heq
      exact ⟨hpos1, by rw [stepUpFrom_self, Matrix.one_mulVec]⟩
    · have hle : M₁ ≤ M₂ := by omega
      rcases stepUpFrom_mulVec_harmKerUnit hwr hw1 hpos1 hle (by omega) (by omega) with
        ⟨hpos2, ih_eq⟩
      set α : ℝ := ((M₂ + 1 - w : ℕ) : ℝ) / √(((M₂ + 1 - w) * (N - M₂ - w) : ℕ) : ℝ)
      have hα_pos : 0 < α :=
        div_pos (Nat.cast_pos.mpr (by omega))
          (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))))
      have hstep : stepUpMat N M₂ *ᵥ harmKerLift N R w M₂ = α • harmKerLift N R w (M₂ + 1) :=
        stepUpMat_mulVec_harmKerLift hwr (hw1.trans hle) (by omega) h2M
      have hnorm_eq :
          finVecNorm (harmKerLift N R w M₂) =
            α * finVecNorm (harmKerLift N R w (M₂ + 1)) := by
        have hiso := finVecNorm_mulVec_of_transpose_mul_self
          (stepUpMat_transpose_mul_self h2M) (harmKerLift N R w M₂)
        rw [hstep, finVecNorm_smul, abs_of_pos hα_pos] at hiso
        exact hiso.symm
      have hpos3 : 0 < finVecNorm (harmKerLift N R w (M₂ + 1)) := by
        by_contra hnp
        have h0 : finVecNorm (harmKerLift N R w (M₂ + 1)) = 0 :=
          le_antisymm (not_lt.mp hnp) (finVecNorm_nonneg _)
        rw [h0, mul_zero] at hnorm_eq
        linarith
      refine ⟨hpos3, ?_⟩
      rw [stepUpFrom_succ hle, ← Matrix.mulVec_mulVec, ih_eq, Matrix.mulVec_smul, hstep,
        smul_smul, hnorm_eq]
      congr 1
      field_simp [hα_pos.ne', hpos3.ne']

/-! ## Section 5: Asymptotic `O(1 / 10 ^ 15)` Orbit Zero-Padding Bound -/

private lemma choose_mono_of_two_mul_le {K q₁ : ℕ} :
    ∀ {q₂ : ℕ}, q₁ ≤ q₂ → 2 * q₂ ≤ K → K.choose q₁ ≤ K.choose q₂
  | 0, h12, _ => by
    have hq : q₁ = 0 := by omega
    rw [hq]
  | q₂ + 1, h12, h2K => by
    by_cases heq : q₁ = q₂ + 1
    · subst heq; exact le_rfl
    · have hle : q₁ ≤ q₂ := by omega
      have ih := choose_mono_of_two_mul_le (K := K) hle (by omega)
      have hstep : K.choose q₂ ≤ K.choose (q₂ + 1) := by
        have hrel := Nat.choose_succ_right_eq K q₂
        refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos q₂)
        calc K.choose q₂ * (q₂ + 1)
            ≤ K.choose q₂ * (K - q₂) := Nat.mul_le_mul_left _ (by omega)
          _ = K.choose (q₂ + 1) * (q₂ + 1) := hrel.symm
      exact ih.trans hstep

private lemma self_le_choose_of_pos {K q : ℕ} (hq1 : 1 ≤ q) (h2K : 2 * q ≤ K) :
    K ≤ K.choose q := by
  simpa only [Nat.choose_one_right] using choose_mono_of_two_mul_le hq1 h2K

private noncomputable def harmFiberVal (N M r w a : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (w + 1),
    (a.choose t * (M - a).choose (w - t) : ℝ) * harmKerWeight N r w t

private lemma harmKerLift_apply_eq_harmFiberVal {N w M : ℕ} (R : Finset (Fin N))
    (E : P01Subset N M) :
    harmKerLift N R w M E = harmFiberVal N M R.card w (E.1 ∩ R).card := by
  unfold harmKerLift jDownGenMat harmKerBase
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
    ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  have hbij :
      (∑ U ∈ Finset.univ.filter (fun U : P01Subset N w ↦ U.1 ⊆ E.1),
        harmKerWeight N R.card w (U.1 ∩ R).card) =
      ∑ S ∈ E.1.powersetCard w, harmKerWeight N R.card w (S ∩ (E.1 ∩ R)).card := by
    refine Finset.sum_bij (fun U _ ↦ U.1)
      (fun U hU ↦ Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp hU).2, U.2⟩)
      (fun _ _ _ _ h ↦ Subtype.ext h)
      (fun S hS ↦ ⟨⟨S, (Finset.mem_powersetCard.mp hS).2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_powersetCard.mp hS).1⟩, rfl⟩)
      (fun U hU ↦ ?_)
    have hUE : U.1 ⊆ E.1 := (Finset.mem_filter.mp hU).2
    have hint : U.1 ∩ (E.1 ∩ R) = U.1 ∩ R := by
      ext z; simp only [Finset.mem_inter]
      exact ⟨fun ⟨hzU, _, hzR⟩ ↦ ⟨hzU, hzR⟩, fun ⟨hzU, hzR⟩ ↦ ⟨hzU, hUE hzU, hzR⟩⟩
    rw [hint]
  rw [hbij, sum_powersetCard_inter_subset E.1 (E.1 ∩ R) Finset.inter_subset_left w, E.2]
  rfl

private lemma finVecNorm_scaled_harmKerLift_sub_orbSingle_le
    {N M : ℕ} (hN_ge : (2 : ℝ) ^ 30000 ≤ (N : ℝ)) (hN_nat : 1048576 ≤ N)
    (hM1 : 1 ≤ M) (hM : M ≤ 8192)
    {R : Finset (Fin N)} (hr1 : 1 ≤ R.card) (hr : R.card ≤ 1024)
    (w : Fin (orbDim M R.card)) :
    finVecNorm
        ((1 / √(orbCard N M R.card w.1 : ℝ)) • harmKerLift N R w.1 M -
          orbEmbedGen N M R (Pi.single w 1)) ≤
      1 / (512 * (wdScale : ℝ)) := by
  let K := N - R.card
  have hw_min : w.1 ≤ min M R.card := by
    have hw := w.2; unfold orbDim at hw; omega
  have hwM : w.1 ≤ M := hw_min.trans (Nat.min_le_left M R.card)
  have hwr : w.1 ≤ R.card := hw_min.trans (Nat.min_le_right M R.card)
  have hMrN : M + R.card ≤ N := by omega
  have hKM_pos : (0 : ℝ) < ((K - M : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hKM_ge : (2 : ℝ) ^ 29999 ≤ ((K - M : ℕ) : ℝ) := by
    have hrm : (R.card : ℝ) + (M : ℝ) ≤ (2 : ℝ) ^ 14 := by
      have hnat : R.card + M ≤ 16384 := by omega
      calc (R.card : ℝ) + (M : ℝ)
          = ((R.card + M : ℕ) : ℝ) := (Nat.cast_add _ _).symm
        _ ≤ (16384 : ℝ) := Nat.cast_le.mpr hnat
        _ = (2 : ℝ) ^ 14 := by norm_num
    have h2 : (2 : ℝ) ^ 14 ≤ (2 : ℝ) ^ 29999 := two_pow_le (a := 14) (b := 29999) (by omega)
    have hle_sum : (2 : ℝ) ^ 29999 + ((R.card : ℝ) + (M : ℝ)) ≤ (N : ℝ) :=
      calc (2 : ℝ) ^ 29999 + ((R.card : ℝ) + (M : ℝ))
          ≤ (2 : ℝ) ^ 29999 + (2 : ℝ) ^ 14 := add_le_add le_rfl hrm
        _ ≤ (2 : ℝ) ^ 29999 + (2 : ℝ) ^ 29999 := add_le_add le_rfl h2
        _ = (2 : ℝ) ^ 30000 := two_pow_add_self 29999
        _ ≤ (N : ℝ) := hN_ge
    have hsub : ((K - M : ℕ) : ℝ) = (N : ℝ) - ((R.card : ℝ) + (M : ℝ)) := by
      dsimp only [K]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), sub_sub]
    rw [hsub, le_sub_iff_add_le]
    exact hle_sum
  set c := √(orbCard N M R.card w.1 : ℝ)
  have hc2_pos : (0 : ℝ) < (orbCard N M R.card w.1 : ℝ) :=
    Nat.cast_pos.mpr (orbCard_pos_gen hMrN hw_min)
  have hc_pos : 0 < c := Real.sqrt_pos.mpr hc2_pos
  set u := (1 / c) • harmKerLift N R w.1 M
  set v := orbEmbedGen N M R (Pi.single w 1)
  have hfib_sum :
      finVecSqNorm (u - v) =
        ∑ a : Fin (orbDim M R.card),
          if a = w then (harmFiberVal N M R.card w.1 w.1 - 1) ^ 2
          else ((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) *
            (harmFiberVal N M R.card w.1 a.1) ^ 2 := by
    unfold finVecSqNorm
    let g : P01Subset N M → Fin (orbDim M R.card) :=
      fun E ↦ ⟨(E.1 ∩ R).card, inter_card_lt_orbDim R E⟩
    rw [(Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := g) (fun _ _ ↦ Finset.mem_univ _)
      (f := fun E ↦ ((u - v) E) ^ 2)).symm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have ha_min : a.1 ≤ min M R.card := by
      have ha := a.2; unfold orbDim at ha; omega
    have haM : a.1 ≤ M := ha_min.trans (Nat.min_le_left M R.card)
    have hflt :
        Finset.univ.filter (fun E : P01Subset N M ↦ g E = a) =
          Finset.univ.filter (fun E : P01Subset N M ↦ (E.1 ∩ R).card = a.1) := by
      ext E; simp [g, Fin.ext_iff]
    rw [hflt]
    by_cases haw : a = w
    · subst haw
      have hc_eq :
          (∑ E ∈ Finset.univ.filter (fun E : P01Subset N M ↦ (E.1 ∩ R).card = a.1),
            ((u - v) E) ^ 2) =
          ∑ _ ∈ Finset.univ.filter (fun E : P01Subset N M ↦ (E.1 ∩ R).card = a.1),
            (harmFiberVal N M R.card a.1 a.1 - 1) ^ 2 / (orbCard N M R.card a.1 : ℝ) := by
        refine Finset.sum_congr rfl fun E hE ↦ ?_
        have hEa : (E.1 ∩ R).card = a.1 := (Finset.mem_filter.mp hE).2
        have hfin : (⟨(E.1 ∩ R).card, inter_card_lt_orbDim R E⟩ : Fin (orbDim M R.card)) = a :=
          Fin.ext hEa
        dsimp only [u, v]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, orbEmbedGen, hfin,
          Pi.single_eq_same]
        rw [harmKerLift_apply_eq_harmFiberVal, hEa]
        change (1 / c * harmFiberVal N M R.card a.1 a.1 - 1 / c) ^ 2 = _
        have hcsq : c ^ 2 = (orbCard N M R.card a.1 : ℝ) := Real.sq_sqrt hc2_pos.le
        rw [← hcsq]
        field_simp [hc_pos.ne']
      rw [ite_eq_left rfl, hc_eq, Finset.sum_const, card_p01Subset_inter_eq R haM,
        nsmul_eq_mul, mul_div_cancel₀ _ hc2_pos.ne']
    · rw [ite_eq_right haw]
      have hc_eq :
          (∑ E ∈ Finset.univ.filter (fun E : P01Subset N M ↦ (E.1 ∩ R).card = a.1),
            ((u - v) E) ^ 2) =
          ∑ _ ∈ Finset.univ.filter (fun E : P01Subset N M ↦ (E.1 ∩ R).card = a.1),
            (harmFiberVal N M R.card w.1 a.1) ^ 2 / (orbCard N M R.card w.1 : ℝ) := by
        refine Finset.sum_congr rfl fun E hE ↦ ?_
        have hEa : (E.1 ∩ R).card = a.1 := (Finset.mem_filter.mp hE).2
        have hfin : (⟨(E.1 ∩ R).card, inter_card_lt_orbDim R E⟩ : Fin (orbDim M R.card)) = a :=
          Fin.ext hEa
        dsimp only [u, v]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, orbEmbedGen, hfin,
          Pi.single_eq_of_ne haw, zero_div, sub_zero]
        rw [harmKerLift_apply_eq_harmFiberVal, hEa]
        change (1 / c * harmFiberVal N M R.card w.1 a.1) ^ 2 = _
        have hcsq : c ^ 2 = (orbCard N M R.card w.1 : ℝ) := Real.sq_sqrt hc2_pos.le
        rw [← hcsq]
        field_simp [hc_pos.ne']
      rw [hc_eq, Finset.sum_const, card_p01Subset_inter_eq R haM, nsmul_eq_mul]
      ring
  have hterm_bound (a : Fin (orbDim M R.card)) :
      (if a = w then (harmFiberVal N M R.card w.1 w.1 - 1) ^ 2
        else ((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) *
          (harmFiberVal N M R.card w.1 a.1) ^ 2) ≤
        (2 : ℝ) ^ (2 * M + 5 * R.card + 40) / ((K - M : ℕ) : ℝ) := by
    have ha_min : a.1 ≤ min M R.card := by
      have ha := a.2; unfold orbDim at ha; omega
    have haM : a.1 ≤ M := ha_min.trans (Nat.min_le_left M R.card)
    have har : a.1 ≤ R.card := ha_min.trans (Nat.min_le_right M R.card)
    by_cases haw : a = w
    · subst haw
      rw [ite_eq_left rfl]
      have htop :
          harmFiberVal N M R.card a.1 a.1 - 1 =
            ∑ t ∈ Finset.range a.1,
              (a.1.choose t * (M - a.1).choose (a.1 - t) : ℝ) *
                harmKerWeight N R.card a.1 t := by
        unfold harmFiberVal
        rw [Finset.sum_range_succ]
        have hlast :
            (a.1.choose a.1 * (M - a.1).choose (a.1 - a.1) : ℝ) *
              harmKerWeight N R.card a.1 a.1 = 1 := by
          unfold harmKerWeight
          simp
        rw [hlast, add_sub_cancel_right]
      have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
      have habs :
          |harmFiberVal N M R.card a.1 a.1 - 1| ≤
            (2 : ℝ) ^ (M + 2 * R.card + 12) / (K : ℝ) := by
        rw [htop]
        calc |∑ t ∈ Finset.range a.1,
              (a.1.choose t * (M - a.1).choose (a.1 - t) : ℝ) *
                harmKerWeight N R.card a.1 t|
            ≤ ∑ t ∈ Finset.range a.1,
                |(a.1.choose t * (M - a.1).choose (a.1 - t) : ℝ) *
                  harmKerWeight N R.card a.1 t| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _t ∈ Finset.range a.1, (2 : ℝ) ^ (M + 2 * R.card) / (K : ℝ) := by
              refine Finset.sum_le_sum fun t ht ↦ ?_
              have hta : t < a.1 := Finset.mem_range.mp ht
              have hd_ge : (K : ℝ) ≤ (K.choose (a.1 - t) : ℝ) := by
                exact_mod_cast self_le_choose_of_pos (K := K) (q := a.1 - t)
                  (by omega) (by omega)
              unfold harmKerWeight
              change |(a.1.choose t * (M - a.1).choose (a.1 - t) : ℝ) *
                ((-1 : ℝ) ^ (a.1 - t) * ((R.card - t).choose (a.1 - t) : ℝ) /
                  (K.choose (a.1 - t) : ℝ))| ≤ _
              rw [abs_mul, abs_of_nonneg (by positivity), abs_div, abs_mul, abs_pow, abs_neg,
                abs_one, one_pow, one_mul, abs_of_nonneg (by positivity),
                abs_of_nonneg (by positivity), ← mul_div_assoc]
              have hn1 : (a.1.choose t : ℝ) ≤ (2 : ℝ) ^ R.card :=
                (choose_le_two_pow a.1 t).trans (two_pow_le (a := a.1) (b := R.card) har)
              have hn2 : ((M - a.1).choose (a.1 - t) : ℝ) ≤ (2 : ℝ) ^ M :=
                (choose_le_two_pow (M - a.1) (a.1 - t)).trans
                  (two_pow_le (a := M - a.1) (b := M) (by omega))
              have hn3 : ((R.card - t).choose (a.1 - t) : ℝ) ≤ (2 : ℝ) ^ R.card :=
                (choose_le_two_pow (R.card - t) (a.1 - t)).trans
                  (two_pow_le (a := R.card - t) (b := R.card) (by omega))
              have hnum :
                  (a.1.choose t * (M - a.1).choose (a.1 - t) : ℝ) *
                    ((R.card - t).choose (a.1 - t) : ℝ) ≤ (2 : ℝ) ^ (M + 2 * R.card) := by
                calc (a.1.choose t : ℝ) * ((M - a.1).choose (a.1 - t) : ℝ) *
                        ((R.card - t).choose (a.1 - t) : ℝ)
                    ≤ (2 : ℝ) ^ R.card * (2 : ℝ) ^ M * (2 : ℝ) ^ R.card := by gcongr
                  _ = (2 : ℝ) ^ (M + 2 * R.card) := by
                      rw [← pow_add, ← pow_add,
                        show R.card + M + R.card = M + 2 * R.card by omega]
              exact div_le_div₀ (by positivity) hnum hK_pos hd_ge
          _ = (a.1 : ℝ) * ((2 : ℝ) ^ (M + 2 * R.card) / (K : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 : ℝ) ^ 12 * ((2 : ℝ) ^ (M + 2 * R.card) / (K : ℝ)) := by
              have ha12 : (a.1 : ℝ) ≤ (2 : ℝ) ^ 12 := by
                have hnat : a.1 ≤ 4096 := by omega
                calc (a.1 : ℝ) ≤ (4096 : ℝ) := Nat.cast_le.mpr hnat
                  _ = (2 : ℝ) ^ 12 := by norm_num
              gcongr
          _ = (2 : ℝ) ^ (M + 2 * R.card + 12) / (K : ℝ) := by
              rw [← mul_div_assoc, ← pow_add,
                show 12 + (M + 2 * R.card) = M + 2 * R.card + 12 by omega]
      calc (harmFiberVal N M R.card a.1 a.1 - 1) ^ 2
          = |harmFiberVal N M R.card a.1 a.1 - 1| ^ 2 := (sq_abs _).symm
        _ ≤ ((2 : ℝ) ^ (M + 2 * R.card + 12) / (K : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = (2 : ℝ) ^ (2 * M + 4 * R.card + 24) / (K : ℝ) ^ 2 := by
            rw [div_pow, ← pow_mul,
              show (M + 2 * R.card + 12) * 2 = 2 * M + 4 * R.card + 24 by omega]
        _ ≤ (2 : ℝ) ^ (2 * M + 5 * R.card + 40) / ((K - M : ℕ) : ℝ) := by
            have hK2 : ((K - M : ℕ) : ℝ) ≤ (K : ℝ) ^ 2 := by
              have hnat : K - M ≤ K * K :=
                (Nat.sub_le K M).trans (Nat.le_mul_of_pos_right K (by omega))
              simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hnat
            have hpow :
                (2 : ℝ) ^ (2 * M + 4 * R.card + 24) ≤ (2 : ℝ) ^ (2 * M + 5 * R.card + 40) :=
              two_pow_le (a := 2 * M + 4 * R.card + 24) (b := 2 * M + 5 * R.card + 40) (by omega)
            exact div_le_div₀ (by positivity) hpow hKM_pos hK2
    · rw [ite_eq_right haw]
      have hne_val : a.1 ≠ w.1 := fun h ↦ haw (Fin.ext h)
      by_cases hgt : w.1 < a.1
      · -- Case w.1 < a.1: orbCard ratio is O(M / (K - M))
        have hfval_abs : |harmFiberVal N M R.card w.1 a.1| ≤ (2 : ℝ) ^ (M + 2 * R.card + 12) := by
          unfold harmFiberVal
          calc |∑ t ∈ Finset.range (w.1 + 1),
                (a.1.choose t * (M - a.1).choose (w.1 - t) : ℝ) *
                  harmKerWeight N R.card w.1 t|
              ≤ ∑ t ∈ Finset.range (w.1 + 1),
                  |(a.1.choose t * (M - a.1).choose (w.1 - t) : ℝ) *
                    harmKerWeight N R.card w.1 t| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _t ∈ Finset.range (w.1 + 1), (2 : ℝ) ^ (M + 2 * R.card) := by
                refine Finset.sum_le_sum fun t ht ↦ ?_
                have htw : t ≤ w.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
                unfold harmKerWeight
                change |(a.1.choose t * (M - a.1).choose (w.1 - t) : ℝ) *
                  ((-1 : ℝ) ^ (w.1 - t) * ((R.card - t).choose (w.1 - t) : ℝ) /
                    (K.choose (w.1 - t) : ℝ))| ≤ _
                rw [abs_mul, abs_of_nonneg (by positivity), abs_div, abs_mul, abs_pow, abs_neg,
                  abs_one, one_pow, one_mul, abs_of_nonneg (by positivity),
                  abs_of_nonneg (by positivity), ← mul_div_assoc]
                have hd1 : (1 : ℝ) ≤ (K.choose (w.1 - t) : ℝ) :=
                  Nat.one_le_cast.mpr (Nat.choose_pos (by omega))
                have hn1 : (a.1.choose t : ℝ) ≤ (2 : ℝ) ^ R.card :=
                  (choose_le_two_pow a.1 t).trans (two_pow_le (a := a.1) (b := R.card) har)
                have hn2 : ((M - a.1).choose (w.1 - t) : ℝ) ≤ (2 : ℝ) ^ M :=
                  (choose_le_two_pow (M - a.1) (w.1 - t)).trans
                    (two_pow_le (a := M - a.1) (b := M) (by omega))
                have hn3 : ((R.card - t).choose (w.1 - t) : ℝ) ≤ (2 : ℝ) ^ R.card :=
                  (choose_le_two_pow (R.card - t) (w.1 - t)).trans
                    (two_pow_le (a := R.card - t) (b := R.card) (by omega))
                calc (a.1.choose t : ℝ) * ((M - a.1).choose (w.1 - t) : ℝ) *
                        ((R.card - t).choose (w.1 - t) : ℝ) / (K.choose (w.1 - t) : ℝ)
                    ≤ (a.1.choose t : ℝ) * ((M - a.1).choose (w.1 - t) : ℝ) *
                        ((R.card - t).choose (w.1 - t) : ℝ) / 1 :=
                      div_le_div_of_nonneg_left (by positivity) zero_lt_one hd1
                  _ ≤ (2 : ℝ) ^ R.card * (2 : ℝ) ^ M * (2 : ℝ) ^ R.card := by rw [div_one]; gcongr
                  _ = (2 : ℝ) ^ (M + 2 * R.card) := by
                      rw [← pow_add, ← pow_add,
                        show R.card + M + R.card = M + 2 * R.card by omega]
            _ = ((w.1 + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (M + 2 * R.card) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (2 : ℝ) ^ 12 * (2 : ℝ) ^ (M + 2 * R.card) := by
                have hw12 : ((w.1 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 12 := by
                  have hnat : w.1 + 1 ≤ 4096 := by omega
                  calc ((w.1 + 1 : ℕ) : ℝ) ≤ (4096 : ℝ) := Nat.cast_le.mpr hnat
                    _ = (2 : ℝ) ^ 12 := by norm_num
                gcongr
            _ = (2 : ℝ) ^ (M + 2 * R.card + 12) := by
                rw [← pow_add, show 12 + (M + 2 * R.card) = M + 2 * R.card + 12 by omega]
        have horb_le :
            (orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ) ≤
              (2 : ℝ) ^ (R.card + 14) / ((K - M : ℕ) : ℝ) := by
          have hch_nat : (K - M) * K.choose (M - a.1) ≤ M * K.choose (M - w.1) := by
            have hrel := Nat.choose_succ_right_eq K (M - a.1)
            calc (K - M) * K.choose (M - a.1)
                ≤ (K - (M - a.1)) * K.choose (M - a.1) := Nat.mul_le_mul_right _ (by omega)
              _ = K.choose (M - a.1) * (K - (M - a.1)) := Nat.mul_comm _ _
              _ = K.choose (M - a.1 + 1) * (M - a.1 + 1) := hrel.symm
              _ ≤ K.choose (M - w.1) * M :=
                  Nat.mul_le_mul
                    (choose_mono_of_two_mul_le (K := K) (q₁ := M - a.1 + 1) (q₂ := M - w.1)
                      (by omega) (by omega))
                    (by omega)
              _ = M * K.choose (M - w.1) := Nat.mul_comm _ _
          have hchR :
              ((K - M : ℕ) : ℝ) * (K.choose (M - a.1) : ℝ) ≤
                (M : ℝ) * (K.choose (M - w.1) : ℝ) := by exact_mod_cast hch_nat
          have hr_ch : (R.card.choose a.1 : ℝ) ≤ (2 : ℝ) ^ R.card * (R.card.choose w.1 : ℝ) := by
            have h1 : (1 : ℝ) ≤ (R.card.choose w.1 : ℝ) :=
              Nat.one_le_cast.mpr (Nat.choose_pos hwr)
            calc (R.card.choose a.1 : ℝ)
                ≤ (2 : ℝ) ^ R.card * 1 := by rw [mul_one]; exact choose_le_two_pow R.card a.1
              _ ≤ (2 : ℝ) ^ R.card * (R.card.choose w.1 : ℝ) := by gcongr
          have hM14 : (M : ℝ) ≤ (2 : ℝ) ^ 14 := by
            have hnat : M ≤ 16384 := by omega
            calc (M : ℝ) ≤ (16384 : ℝ) := Nat.cast_le.mpr hnat
              _ = (2 : ℝ) ^ 14 := by norm_num
          rw [div_le_div_iff₀ hc2_pos hKM_pos]
          unfold orbCard
          change ((R.card.choose a.1 * K.choose (M - a.1) : ℕ) : ℝ) * ((K - M : ℕ) : ℝ) ≤
            (2 : ℝ) ^ (R.card + 14) * ((R.card.choose w.1 * K.choose (M - w.1) : ℕ) : ℝ)
          push_cast
          calc (R.card.choose a.1 : ℝ) * (K.choose (M - a.1) : ℝ) * ((K - M : ℕ) : ℝ)
              = (R.card.choose a.1 : ℝ) * (((K - M : ℕ) : ℝ) * (K.choose (M - a.1) : ℝ)) := by
                  ring
            _ ≤ ((2 : ℝ) ^ R.card * (R.card.choose w.1 : ℝ)) *
                  ((M : ℝ) * (K.choose (M - w.1) : ℝ)) :=
                mul_le_mul hr_ch hchR (by positivity) (by positivity)
            _ ≤ ((2 : ℝ) ^ R.card * (R.card.choose w.1 : ℝ)) *
                  ((2 : ℝ) ^ 14 * (K.choose (M - w.1) : ℝ)) := by gcongr
            _ = (2 : ℝ) ^ (R.card + 14) *
                  ((R.card.choose w.1 : ℝ) * (K.choose (M - w.1) : ℝ)) := by
                rw [pow_add]; ring
        have hsq_f :
            (harmFiberVal N M R.card w.1 a.1) ^ 2 ≤ (2 : ℝ) ^ (2 * M + 4 * R.card + 24) := by
          calc (harmFiberVal N M R.card w.1 a.1) ^ 2
              = |harmFiberVal N M R.card w.1 a.1| ^ 2 := (sq_abs _).symm
            _ ≤ ((2 : ℝ) ^ (M + 2 * R.card + 12)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfval_abs 2
            _ = (2 : ℝ) ^ (2 * M + 4 * R.card + 24) := by
                rw [← pow_mul, show (M + 2 * R.card + 12) * 2 = 2 * M + 4 * R.card + 24 by omega]
        have hpow_38 :
            (2 : ℝ) ^ (2 * M + 5 * R.card + 38) ≤ (2 : ℝ) ^ (2 * M + 5 * R.card + 40) :=
          two_pow_le (a := 2 * M + 5 * R.card + 38) (b := 2 * M + 5 * R.card + 40) (by omega)
        calc ((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) *
                (harmFiberVal N M R.card w.1 a.1) ^ 2
            ≤ ((2 : ℝ) ^ (R.card + 14) / ((K - M : ℕ) : ℝ)) *
                (2 : ℝ) ^ (2 * M + 4 * R.card + 24) :=
              mul_le_mul horb_le hsq_f (sq_nonneg _) (by positivity)
          _ = (2 : ℝ) ^ (2 * M + 5 * R.card + 38) / ((K - M : ℕ) : ℝ) := by
              rw [div_mul_eq_mul_div, ← pow_add,
                show R.card + 14 + (2 * M + 4 * R.card + 24) = 2 * M + 5 * R.card + 38 by omega]
          _ ≤ (2 : ℝ) ^ (2 * M + 5 * R.card + 40) / ((K - M : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hpow_38 hKM_pos.le
      · -- Case a.1 < w.1: every non-zero term has t ≤ a.1 so w.1 - t ≥ w.1 - a.1 ≥ 1
        have hlt : a.1 < w.1 := lt_of_le_of_ne (not_lt.mp hgt) hne_val
        let q := w.1 - a.1
        have hq_pos : (0 : ℝ) < (K.choose q : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
        have hfval_abs :
            |harmFiberVal N M R.card w.1 a.1| ≤
              (2 : ℝ) ^ (M + 2 * R.card + 12) / (K.choose q : ℝ) := by
          unfold harmFiberVal
          calc |∑ t ∈ Finset.range (w.1 + 1),
                (a.1.choose t * (M - a.1).choose (w.1 - t) : ℝ) *
                  harmKerWeight N R.card w.1 t|
              ≤ ∑ t ∈ Finset.range (w.1 + 1),
                  |(a.1.choose t * (M - a.1).choose (w.1 - t) : ℝ) *
                    harmKerWeight N R.card w.1 t| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _t ∈ Finset.range (w.1 + 1),
                  (2 : ℝ) ^ (M + 2 * R.card) / (K.choose q : ℝ) := by
                refine Finset.sum_le_sum fun t ht ↦ ?_
                have htw : t ≤ w.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
                by_cases hta : t ≤ a.1
                · have hq_le : (K.choose q : ℝ) ≤ (K.choose (w.1 - t) : ℝ) := by
                    exact_mod_cast choose_mono_of_two_mul_le (K := K) (q₁ := q) (q₂ := w.1 - t)
                      (by omega) (by omega)
                  unfold harmKerWeight
                  change |(a.1.choose t * (M - a.1).choose (w.1 - t) : ℝ) *
                    ((-1 : ℝ) ^ (w.1 - t) * ((R.card - t).choose (w.1 - t) : ℝ) /
                      (K.choose (w.1 - t) : ℝ))| ≤ _
                  rw [abs_mul, abs_of_nonneg (by positivity), abs_div, abs_mul, abs_pow, abs_neg,
                    abs_one, one_pow, one_mul, abs_of_nonneg (by positivity),
                    abs_of_nonneg (by positivity), ← mul_div_assoc]
                  have hn1 : (a.1.choose t : ℝ) ≤ (2 : ℝ) ^ R.card :=
                    (choose_le_two_pow a.1 t).trans (two_pow_le (a := a.1) (b := R.card) har)
                  have hn2 : ((M - a.1).choose (w.1 - t) : ℝ) ≤ (2 : ℝ) ^ M :=
                    (choose_le_two_pow (M - a.1) (w.1 - t)).trans
                      (two_pow_le (a := M - a.1) (b := M) (by omega))
                  have hn3 : ((R.card - t).choose (w.1 - t) : ℝ) ≤ (2 : ℝ) ^ R.card :=
                    (choose_le_two_pow (R.card - t) (w.1 - t)).trans
                      (two_pow_le (a := R.card - t) (b := R.card) (by omega))
                  have hnum :
                      (a.1.choose t * (M - a.1).choose (w.1 - t) : ℝ) *
                        ((R.card - t).choose (w.1 - t) : ℝ) ≤ (2 : ℝ) ^ (M + 2 * R.card) := by
                    calc (a.1.choose t : ℝ) * ((M - a.1).choose (w.1 - t) : ℝ) *
                            ((R.card - t).choose (w.1 - t) : ℝ)
                        ≤ (2 : ℝ) ^ R.card * (2 : ℝ) ^ M * (2 : ℝ) ^ R.card := by gcongr
                      _ = (2 : ℝ) ^ (M + 2 * R.card) := by
                          rw [← pow_add, ← pow_add,
                            show R.card + M + R.card = M + 2 * R.card by omega]
                  exact div_le_div₀ (by positivity) hnum hq_pos hq_le
                · have hgt_ta : a.1 < t := not_le.mp hta
                  rw [Nat.choose_eq_zero_of_lt hgt_ta]
                  simp only [Nat.cast_zero, zero_mul, abs_zero]
                  positivity
            _ = ((w.1 + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (M + 2 * R.card) / (K.choose q : ℝ)) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (2 : ℝ) ^ 12 * ((2 : ℝ) ^ (M + 2 * R.card) / (K.choose q : ℝ)) := by
                have hw12 : ((w.1 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 12 := by
                  have hnat : w.1 + 1 ≤ 4096 := by omega
                  calc ((w.1 + 1 : ℕ) : ℝ) ≤ (4096 : ℝ) := Nat.cast_le.mpr hnat
                    _ = (2 : ℝ) ^ 12 := by norm_num
                gcongr
            _ = (2 : ℝ) ^ (M + 2 * R.card + 12) / (K.choose q : ℝ) := by
                rw [← mul_div_assoc, ← pow_add,
                  show 12 + (M + 2 * R.card) = M + 2 * R.card + 12 by omega]
        have hch_prod : K.choose (M - a.1) ≤ K.choose (M - w.1) * K.choose q := by
          have hcm := choose_mul_choose (by omega : M - w.1 ≤ M - a.1) (by omega : M - a.1 ≤ K)
          have hsub : M - a.1 - (M - w.1) = q := by omega
          rw [hsub] at hcm
          have hpos_c : 1 ≤ (M - a.1).choose (M - w.1) := Nat.choose_pos (by omega)
          calc K.choose (M - a.1)
              ≤ K.choose (M - a.1) * (M - a.1).choose (M - w.1) :=
                Nat.le_mul_of_pos_right _ hpos_c
            _ = K.choose (M - w.1) * (K - (M - w.1)).choose q := hcm
            _ ≤ K.choose (M - w.1) * K.choose q :=
                Nat.mul_le_mul_left _ (Nat.choose_le_choose q (by omega))
        have horb_q :
            ((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) /
                (K.choose q : ℝ) ^ 2 ≤
              (2 : ℝ) ^ R.card / ((K - M : ℕ) : ℝ) := by
          have hKM_le_Kq : ((K - M : ℕ) : ℝ) ≤ (K.choose q : ℝ) := by
            have hnat : K - M ≤ K.choose q :=
              (Nat.sub_le K M).trans
                (self_le_choose_of_pos (K := K) (q := q) (by omega) (by omega))
            exact_mod_cast hnat
          have hr_ch : (R.card.choose a.1 : ℝ) ≤ (2 : ℝ) ^ R.card * (R.card.choose w.1 : ℝ) := by
            have h1 : (1 : ℝ) ≤ (R.card.choose w.1 : ℝ) :=
              Nat.one_le_cast.mpr (Nat.choose_pos hwr)
            calc (R.card.choose a.1 : ℝ)
                ≤ (2 : ℝ) ^ R.card * 1 := by rw [mul_one]; exact choose_le_two_pow R.card a.1
              _ ≤ (2 : ℝ) ^ R.card * (R.card.choose w.1 : ℝ) := by gcongr
          have hcpR : (K.choose (M - a.1) : ℝ) ≤ (K.choose (M - w.1) : ℝ) * (K.choose q : ℝ) := by
            exact_mod_cast hch_prod
          rw [div_div, div_le_div_iff₀ (mul_pos hc2_pos (pow_pos hq_pos 2)) hKM_pos]
          unfold orbCard
          change ((R.card.choose a.1 * K.choose (M - a.1) : ℕ) : ℝ) * ((K - M : ℕ) : ℝ) ≤
            (2 : ℝ) ^ R.card *
              (((R.card.choose w.1 * K.choose (M - w.1) : ℕ) : ℝ) * (K.choose q : ℝ) ^ 2)
          push_cast
          calc (R.card.choose a.1 : ℝ) * (K.choose (M - a.1) : ℝ) * ((K - M : ℕ) : ℝ)
              ≤ ((2 : ℝ) ^ R.card * (R.card.choose w.1 : ℝ)) *
                  ((K.choose (M - w.1) : ℝ) * (K.choose q : ℝ)) * (K.choose q : ℝ) := by
                gcongr
            _ = (2 : ℝ) ^ R.card *
                  (((R.card.choose w.1 : ℝ) * (K.choose (M - w.1) : ℝ)) *
                    (K.choose q : ℝ) ^ 2) := by
                ring
        have hsq_f :
            (harmFiberVal N M R.card w.1 a.1) ^ 2 ≤
              (2 : ℝ) ^ (2 * M + 4 * R.card + 24) / (K.choose q : ℝ) ^ 2 := by
          calc (harmFiberVal N M R.card w.1 a.1) ^ 2
              = |harmFiberVal N M R.card w.1 a.1| ^ 2 := (sq_abs _).symm
            _ ≤ ((2 : ℝ) ^ (M + 2 * R.card + 12) / (K.choose q : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) hfval_abs 2
            _ = (2 : ℝ) ^ (2 * M + 4 * R.card + 24) / (K.choose q : ℝ) ^ 2 := by
                rw [div_pow, ← pow_mul,
                  show (M + 2 * R.card + 12) * 2 = 2 * M + 4 * R.card + 24 by omega]
        have hpow_24 :
            (2 : ℝ) ^ (2 * M + 5 * R.card + 24) ≤ (2 : ℝ) ^ (2 * M + 5 * R.card + 40) :=
          two_pow_le (a := 2 * M + 5 * R.card + 24) (b := 2 * M + 5 * R.card + 40) (by omega)
        calc ((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) *
                (harmFiberVal N M R.card w.1 a.1) ^ 2
            ≤ ((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) *
                ((2 : ℝ) ^ (2 * M + 4 * R.card + 24) / (K.choose q : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hsq_f (by positivity)
          _ = (((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) /
                (K.choose q : ℝ) ^ 2) * (2 : ℝ) ^ (2 * M + 4 * R.card + 24) := by ring
          _ ≤ ((2 : ℝ) ^ R.card / ((K - M : ℕ) : ℝ)) * (2 : ℝ) ^ (2 * M + 4 * R.card + 24) :=
              mul_le_mul_of_nonneg_right horb_q (by positivity)
          _ = (2 : ℝ) ^ (2 * M + 5 * R.card + 24) / ((K - M : ℕ) : ℝ) := by
              rw [div_mul_eq_mul_div, ← pow_add,
                show R.card + (2 * M + 4 * R.card + 24) = 2 * M + 5 * R.card + 24 by omega]
          _ ≤ (2 : ℝ) ^ (2 * M + 5 * R.card + 40) / ((K - M : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hpow_24 hKM_pos.le
  have hsq_le : finVecSqNorm (u - v) ≤ (1 / (512 * (wdScale : ℝ))) ^ 2 := by
    have hsum_le :
        finVecSqNorm (u - v) ≤ (2 : ℝ) ^ 22000 / ((K - M : ℕ) : ℝ) := by
      have hpow_22000 :
          (2 : ℝ) ^ (12 + (2 * M + 5 * R.card + 40)) ≤ (2 : ℝ) ^ 22000 :=
        two_pow_le (a := 12 + (2 * M + 5 * R.card + 40)) (b := 22000) (by omega)
      rw [hfib_sum]
      calc (∑ a : Fin (orbDim M R.card),
            if a = w then (harmFiberVal N M R.card w.1 w.1 - 1) ^ 2
            else ((orbCard N M R.card a.1 : ℝ) / (orbCard N M R.card w.1 : ℝ)) *
              (harmFiberVal N M R.card w.1 a.1) ^ 2)
          ≤ ∑ _a : Fin (orbDim M R.card),
              (2 : ℝ) ^ (2 * M + 5 * R.card + 40) / ((K - M : ℕ) : ℝ) :=
            Finset.sum_le_sum fun a _ ↦ hterm_bound a
        _ = (orbDim M R.card : ℝ) *
              ((2 : ℝ) ^ (2 * M + 5 * R.card + 40) / ((K - M : ℕ) : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ 12 * ((2 : ℝ) ^ (2 * M + 5 * R.card + 40) / ((K - M : ℕ) : ℝ)) := by
            have hod : (orbDim M R.card : ℝ) ≤ (2 : ℝ) ^ 12 := by
              have hnat : orbDim M R.card ≤ 4096 := by unfold orbDim; omega
              calc (orbDim M R.card : ℝ) ≤ (4096 : ℝ) := Nat.cast_le.mpr hnat
                _ = (2 : ℝ) ^ 12 := by norm_num
            gcongr
        _ = (2 : ℝ) ^ (12 + (2 * M + 5 * R.card + 40)) / ((K - M : ℕ) : ℝ) := by
            rw [← mul_div_assoc, ← pow_add]
        _ ≤ (2 : ℝ) ^ 22000 / ((K - M : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hpow_22000 hKM_pos.le
    have hwd : (wdScale : ℝ) ≤ (2 : ℝ) ^ 50 := by unfold wdScale; norm_num
    have hden_pos : (0 : ℝ) < 512 * (wdScale : ℝ) := by unfold wdScale; positivity
    have h512 : (512 * (wdScale : ℝ)) ^ 2 ≤ (2 : ℝ) ^ 118 := by
      calc (512 * (wdScale : ℝ)) ^ 2
          ≤ (512 * (2 : ℝ) ^ 50) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ = (2 : ℝ) ^ 118 := by norm_num
    refine hsum_le.trans ?_
    rw [one_div_pow, div_le_div_iff₀ hKM_pos (pow_pos hden_pos 2)]
    calc (2 : ℝ) ^ 22000 * (512 * (wdScale : ℝ)) ^ 2
        ≤ (2 : ℝ) ^ 22000 * (2 : ℝ) ^ 118 := mul_le_mul_of_nonneg_left h512 (by positivity)
      _ = (2 : ℝ) ^ 22118 := by rw [← pow_add]
      _ ≤ (2 : ℝ) ^ 29999 := two_pow_le (a := 22118) (b := 29999) (by omega)
      _ ≤ 1 * ((K - M : ℕ) : ℝ) := by rw [one_mul]; exact hKM_ge
  unfold finVecNorm
  rw [Real.sqrt_le_iff]
  exact ⟨by unfold wdScale; positivity, hsq_le⟩

private lemma finVecNorm_harmKerUnit_sub_orbSingle_le
    {N M : ℕ} (hN_ge : (2 : ℝ) ^ 30000 ≤ (N : ℝ)) (hN_nat : 1048576 ≤ N)
    (hM1 : 1 ≤ M) (hM : M ≤ 8192)
    {R : Finset (Fin N)} (hr1 : 1 ≤ R.card) (hr : R.card ≤ 1024)
    (w : Fin (orbDim M R.card)) :
    0 < finVecNorm (harmKerLift N R w.1 M) ∧
    finVecNorm
        ((1 / finVecNorm (harmKerLift N R w.1 M)) • harmKerLift N R w.1 M -
          orbEmbedGen N M R (Pi.single w 1)) ≤
      1 / (256 * (wdScale : ℝ)) := by
  set c := √(orbCard N M R.card w.1 : ℝ)
  have hMrN : M + R.card ≤ N := by omega
  have hw_min : w.1 ≤ min M R.card := by
    have hw := w.2; unfold orbDim at hw; omega
  have hc_pos : 0 < c :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (orbCard_pos_gen hMrN hw_min))
  set z := harmKerLift N R w.1 M
  set u := (1 / c) • z
  set v := orbEmbedGen N M R (Pi.single w 1)
  set δ : ℝ := 1 / (512 * (wdScale : ℝ))
  have hδ_lt : δ < 1 / 2 := by unfold δ wdScale; norm_num
  have huv : finVecNorm (u - v) ≤ δ :=
    finVecNorm_scaled_harmKerLift_sub_orbSingle_le hN_ge hN_nat hM1 hM hr1 hr w
  have hv_norm : finVecNorm v = 1 := by
    dsimp only [v]
    rw [finVecNorm_orbEmbedGen hMrN]
    unfold vecNorm vecSqNorm
    rw [Fintype.sum_eq_single w (fun j hj ↦ by rw [Pi.single_eq_of_ne hj, zero_pow two_ne_zero])]
    rw [Pi.single_eq_same, one_pow, Real.sqrt_one]
  have hu_ge : 1 - δ ≤ finVecNorm u := by
    have htri : finVecNorm v ≤ finVecNorm u + finVecNorm (v - u) := by
      have heq : v = u + (v - u) := by funext E; simp
      conv_lhs => rw [heq]
      exact finVecNorm_add_le u (v - u)
    have hvu : finVecNorm (v - u) = finVecNorm (u - v) := by
      rw [← finVecNorm_neg (u - v), neg_sub]
    linarith
  have hu_le : finVecNorm u ≤ 1 + δ := by
    have htri : finVecNorm u ≤ finVecNorm v + finVecNorm (u - v) := by
      have heq : u = v + (u - v) := by funext E; simp
      conv_lhs => rw [heq]
      exact finVecNorm_add_le v (u - v)
    linarith
  have hu_pos : 0 < finVecNorm u := by linarith
  have hu_norm_eq : finVecNorm u = (1 / c) * finVecNorm z := by
    dsimp only [u]
    rw [finVecNorm_smul, abs_of_pos (one_div_pos.mpr hc_pos)]
  have hz_pos : 0 < finVecNorm z := by
    by_contra hnp
    have h0 : finVecNorm z = 0 := le_antisymm (not_lt.mp hnp) (finVecNorm_nonneg z)
    rw [h0, mul_zero] at hu_norm_eq
    linarith
  refine ⟨hz_pos, ?_⟩
  have hunit_eq : (1 / finVecNorm z) • z = (1 / finVecNorm u) • u := by
    dsimp only [u]
    rw [smul_smul, hu_norm_eq]
    congr 1
    field_simp [hc_pos.ne', hz_pos.ne']
  rw [hunit_eq]
  have hdiff :
      finVecNorm ((1 / finVecNorm u) • u - u) = |1 - finVecNorm u| := by
    have hsmul : (1 / finVecNorm u) • u - u = (1 / finVecNorm u - 1) • u := by
      funext E; simp [sub_mul]
    rw [hsmul, finVecNorm_smul]
    have h1 : 1 / finVecNorm u - 1 = (1 - finVecNorm u) / finVecNorm u := by
      field_simp [hu_pos.ne']
    rw [h1, abs_div, abs_of_pos hu_pos, div_mul_cancel₀ _ hu_pos.ne']
  have habs_le : |1 - finVecNorm u| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have htri :
      finVecNorm ((1 / finVecNorm u) • u - v) ≤
        finVecNorm ((1 / finVecNorm u) • u - u) + finVecNorm (u - v) := by
    have heq : (1 / finVecNorm u) • u - v = ((1 / finVecNorm u) • u - u) + (u - v) := by
      funext E; simp
    rw [heq]
    exact finVecNorm_add_le _ _
  have h2δ : 2 * δ = 1 / (256 * (wdScale : ℝ)) := by
    dsimp only [δ]; ring
  linarith

private lemma finVecNorm_stepUpFrom_orbEmbedGen_sub_le_aux
    {N M₁ M₂ : ℕ} (hN_ge : (2 : ℝ) ^ 30000 ≤ (N : ℝ)) (hN_nat : 1048576 ≤ N)
    (hM₁ : 1 ≤ M₁) (h12 : M₁ ≤ M₂) (hM₂ : M₂ ≤ 8192)
    {R : Finset (Fin N)} (hr1 : 1 ≤ R.card) (hr : R.card ≤ 1024)
    (x : Fin (orbDim M₁ R.card) → ℝ) :
    finVecNorm (stepUpFrom N M₁ M₂ *ᵥ orbEmbedGen N M₁ R x -
        orbEmbedGen N M₂ R (zeroPadOrbVec M₁ M₂ R.card x)) ≤
      (1 / (2 * (wdScale : ℝ))) * vecNorm x := by
  have hstep_single (w : Fin (orbDim M₁ R.card)) :
      finVecNorm (stepUpFrom N M₁ M₂ *ᵥ orbEmbedGen N M₁ R (Pi.single w 1) -
          orbEmbedGen N M₂ R (zeroPadOrbVec M₁ M₂ R.card (Pi.single w 1))) ≤
        1 / (128 * (wdScale : ℝ)) := by
    let w₂ : Fin (orbDim M₂ R.card) :=
      ⟨w.1, by unfold orbDim; have hw := w.2; unfold orbDim at hw; omega⟩
    have hw_min : w.1 ≤ min M₁ R.card := by
      have hw := w.2; unfold orbDim at hw; omega
    have hw1 : w.1 ≤ M₁ := hw_min.trans (Nat.min_le_left M₁ R.card)
    have hwr : w.1 ≤ R.card := hw_min.trans (Nat.min_le_right M₁ R.card)
    rcases finVecNorm_harmKerUnit_sub_orbSingle_le hN_ge hN_nat hM₁ (h12.trans hM₂) hr1 hr w with
      ⟨hp1, hb1⟩
    rcases finVecNorm_harmKerUnit_sub_orbSingle_le hN_ge hN_nat (hM₁.trans h12) hM₂ hr1 hr w₂ with
      ⟨_, hb2⟩
    have hcov := (stepUpFrom_mulVec_harmKerUnit hwr hw1 hp1 h12 (by omega) (by omega)).2
    set z₁ := (1 / finVecNorm (harmKerLift N R w.1 M₁)) • harmKerLift N R w.1 M₁
    set z₂ := (1 / finVecNorm (harmKerLift N R w.1 M₂)) • harmKerLift N R w.1 M₂
    set v₁ := orbEmbedGen N M₁ R (Pi.single w 1)
    set v₂ := orbEmbedGen N M₂ R (Pi.single w₂ 1)
    have hpad : zeroPadOrbVec M₁ M₂ R.card (Pi.single w 1) = Pi.single w₂ 1 :=
      zeroPadOrbVec_single h12 w
    rw [hpad]
    have hdecomp :
        stepUpFrom N M₁ M₂ *ᵥ v₁ - v₂ =
          stepUpFrom N M₁ M₂ *ᵥ (v₁ - z₁) + (z₂ - v₂) := by
      rw [Matrix.mulVec_sub, hcov]
      funext E; simp
    rw [hdecomp]
    have hiso :
        finVecNorm (stepUpFrom N M₁ M₂ *ᵥ (v₁ - z₁)) = finVecNorm (z₁ - v₁) := by
      rw [finVecNorm_mulVec_of_transpose_mul_self
        (stepUpFrom_transpose_mul_self h12 (by omega)), ← finVecNorm_neg (v₁ - z₁), neg_sub]
    have htri := finVecNorm_add_le (stepUpFrom N M₁ M₂ *ᵥ (v₁ - z₁)) (z₂ - v₂)
    rw [hiso] at htri
    have hsum :
        1 / (256 * (wdScale : ℝ)) + 1 / (256 * (wdScale : ℝ)) =
          1 / (128 * (wdScale : ℝ)) := by ring
    linarith
  have hx_sum : x = ∑ w : Fin (orbDim M₁ R.card), x w • Pi.single w 1 := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single u (fun w hwu ↦ by simp [hwu.symm])]
    simp
  have hlin :
      stepUpFrom N M₁ M₂ *ᵥ orbEmbedGen N M₁ R x -
          orbEmbedGen N M₂ R (zeroPadOrbVec M₁ M₂ R.card x) =
        ∑ w : Fin (orbDim M₁ R.card),
          x w • (stepUpFrom N M₁ M₂ *ᵥ orbEmbedGen N M₁ R (Pi.single w 1) -
            orbEmbedGen N M₂ R (zeroPadOrbVec M₁ M₂ R.card (Pi.single w 1))) := by
    conv_lhs => rw [hx_sum]
    rw [orbEmbedGen_sum, Matrix.mulVec_sum, zeroPadOrbVec_sum, orbEmbedGen_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [orbEmbedGen_smul, Matrix.mulVec_smul, zeroPadOrbVec_smul, orbEmbedGen_smul, smul_sub]
  rw [hlin]
  have hcs : (∑ w : Fin (orbDim M₁ R.card), |x w|) ≤ 33 * vecNorm x := by
    let ones : Fin (orbDim M₁ R.card) → ℝ := fun _ ↦ 1
    let absx : Fin (orbDim M₁ R.card) → ℝ := fun w ↦ |x w|
    have hdot : (∑ w : Fin (orbDim M₁ R.card), |x w|) = ones ⬝ᵥ absx := by
      simp [dotProduct, ones, absx]
    have hnorm_abs : vecNorm absx = vecNorm x := by
      simp [vecNorm, vecSqNorm, absx, sq_abs]
    have hnorm_ones : vecNorm ones ≤ 33 := by
      rw [vecNorm, Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      unfold vecSqNorm ones
      simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      have hnat : orbDim M₁ R.card ≤ 1089 := by unfold orbDim; omega
      calc (orbDim M₁ R.card : ℝ) ≤ (1089 : ℝ) := Nat.cast_le.mpr hnat
        _ = (33 : ℝ) ^ 2 := by norm_num
    calc (∑ w : Fin (orbDim M₁ R.card), |x w|)
        = ones ⬝ᵥ absx := hdot
      _ ≤ vecNorm ones * vecNorm absx := dot_le_vecNorm_mul ones absx
      _ = vecNorm ones * vecNorm x := by rw [hnorm_abs]
      _ ≤ 33 * vecNorm x := mul_le_mul_of_nonneg_right hnorm_ones (vecNorm_nonneg x)
  calc finVecNorm
        (∑ w : Fin (orbDim M₁ R.card),
          x w • (stepUpFrom N M₁ M₂ *ᵥ orbEmbedGen N M₁ R (Pi.single w 1) -
            orbEmbedGen N M₂ R (zeroPadOrbVec M₁ M₂ R.card (Pi.single w 1))))
      ≤ ∑ w : Fin (orbDim M₁ R.card),
          finVecNorm (x w • (stepUpFrom N M₁ M₂ *ᵥ orbEmbedGen N M₁ R (Pi.single w 1) -
            orbEmbedGen N M₂ R (zeroPadOrbVec M₁ M₂ R.card (Pi.single w 1)))) :=
        finVecNorm_sum_le Finset.univ _
    _ = ∑ w : Fin (orbDim M₁ R.card),
          |x w| * finVecNorm (stepUpFrom N M₁ M₂ *ᵥ orbEmbedGen N M₁ R (Pi.single w 1) -
            orbEmbedGen N M₂ R (zeroPadOrbVec M₁ M₂ R.card (Pi.single w 1))) :=
        Finset.sum_congr rfl fun w _ ↦ finVecNorm_smul _ _
    _ ≤ ∑ w : Fin (orbDim M₁ R.card), |x w| * (1 / (128 * (wdScale : ℝ))) :=
        Finset.sum_le_sum fun w _ ↦
          mul_le_mul_of_nonneg_left (hstep_single w) (abs_nonneg _)
    _ = (∑ w : Fin (orbDim M₁ R.card), |x w|) * (1 / (128 * (wdScale : ℝ))) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ (33 * vecNorm x) * (1 / (128 * (wdScale : ℝ))) :=
        mul_le_mul_of_nonneg_right hcs (by unfold wdScale; positivity)
    _ ≤ (1 / (2 * (wdScale : ℝ))) * vecNorm x := by
        have hfrac : 33 / (128 * (wdScale : ℝ)) ≤ 1 / (2 * (wdScale : ℝ)) := by
          unfold wdScale; norm_num
        rw [show (33 * vecNorm x) * (1 / (128 * (wdScale : ℝ))) =
            (33 / (128 * (wdScale : ℝ))) * vecNorm x by ring]
        exact mul_le_mul_of_nonneg_right hfrac (vecNorm_nonneg x)

theorem finVecNorm_stepUpFrom_orbEmbedGen_sub_le
    {n M₁ M₂ : ℕ} (hn : altN0 ≤ n) (hM₁ : 1 ≤ M₁) (h12 : M₁ ≤ M₂) (hM₂ : M₂ ≤ 8192)
    {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card) (hr : R.card ≤ 1024)
    (x : Fin (orbDim M₁ R.card) → ℝ) :
    finVecNorm (stepUpFrom (2 ^ n) M₁ M₂ *ᵥ orbEmbedGen (2 ^ n) M₁ R x -
        orbEmbedGen (2 ^ n) M₂ R (zeroPadOrbVec M₁ M₂ R.card x)) ≤
      (1 / (2 * (wdScale : ℝ))) * vecNorm x := by
  have hN_ge : (2 : ℝ) ^ 30000 ≤ ((2 ^ n : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact two_pow_le (a := 30000) (b := n) (by unfold altN0 at hn; omega)
  have hN_nat : 1048576 ≤ 2 ^ n :=
    calc 1048576 = 2 ^ 20 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by unfold altN0 at hn; omega)
  exact finVecNorm_stepUpFrom_orbEmbedGen_sub_le_aux hN_ge hN_nat hM₁ h12 hM₂ hr1 hr x

end
end QuantumComputation.Specs.DickeSol
