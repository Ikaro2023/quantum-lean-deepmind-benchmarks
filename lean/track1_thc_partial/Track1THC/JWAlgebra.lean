/- Adapted from DeepMind's JordanWignerOrbitalAlgebra.lean (Apache-2.0, Google LLC); the original
   is read-only and untouched. Parts 1-3 and 5 copied; new material is appended at the end. -/
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
import QuantumComputationSpecs.Primitives.THCFactorization

/-!
# Jordan–Wigner CAR, Orbital Reflections, & Electron-Sector Invariance

Self-contained algebraic bridge for Jordan–Wigner annihilation/creation operators (`jwAnnihilate`),
rotated spatial-orbital number operators (`orbitalNumberOp`), Hermitian unitary orbital reflections
(`1 - 2 • orbitalNumberOp`), rank-1 `oneBodyHamiltonian (vecMulVec u u)` decomposition, and exact
commutation with `electronSectorProjector`.
-/

namespace Track1THC.JW
open QuantumComputation.Specs

open Operator Matrix
open scoped Matrix

local instance (priority := 100000) instNeZeroTwoPowJW (k : Nat) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Part 1: Jordan–Wigner String & Step Decomposition -/

/-- Diagonal Jordan–Wigner Z-string `Z_0 ⋯ Z_{j-1}` on `k` wires. -/
noncomputable def jwString (k : ℕ) (j : Fin k) : Operator (2 ^ k) :=
  Matrix.diagonal fun i ↦ (-1 : ℂ) ^ ∑ q ∈ Finset.univ.filter (· < j), (basisBits k i q).val

/-- Local lowering operator `(|0⟩⟨1|)_j` embedded on wire `j` of `k` wires. -/
noncomputable def jwStep (k : ℕ) (j : Fin k) : Operator (2 ^ k) :=
  (QRegister.singleton j).embedMatrix (Matrix.single (0 : Fin 2) (1 : Fin 2) 1)

theorem jwAnnihilate_eq_mul (k : ℕ) (j : Fin k) :
    jwAnnihilate k j = jwString k j * jwStep k j := rfl

@[simp]
theorem jwString_conjTranspose (k : ℕ) (j : Fin k) :
    (jwString k j)ᴴ = jwString k j := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [jwString]
  · simp [jwString, hxy, Ne.symm hxy]

@[simp]
theorem jwString_mul_self (k : ℕ) (j : Fin k) :
    jwString k j * jwString k j = 1 := by
  rw [jwString, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 2
  ext x
  rw [← mul_pow]
  norm_num

theorem jwString_mul_comm (k : ℕ) (i j : Fin k) :
    jwString k i * jwString k j = jwString k j * jwString k i := by
  simp only [jwString, Matrix.diagonal_mul_diagonal, mul_comm]

private lemma single01_mul_self :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) *
      (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply]

@[simp]
theorem jwStep_mul_self (k : ℕ) (j : Fin k) :
    jwStep k j * jwStep k j = 0 := by
  rw [jwStep, ← QRegister.embedMatrix_mul, single01_mul_self, QRegister.embedMatrix_zero]

theorem jwStep_comm_of_ne {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    jwStep k i * jwStep k j = jwStep k j * jwStep k i :=
  QRegister.embedMatrix_comm_of_disjoint _ _ (QRegister.singleton_disjoint hij) _ _

/-- Nonzero entries of `jwStep k j` flip wire `j` from `0` to `1` and leave all other wires
fixed. -/
theorem jwStep_support {k : ℕ} {j : Fin k} {x y : Fin (2 ^ k)} (hxy : jwStep k j x y ≠ 0) :
    (∀ p : Fin k, p ≠ j → basisBits k x p = basisBits k y p) ∧
      (basisBits k x j).val = 0 ∧ (basisBits k y j).val = 1 := by
  rw [jwStep, QRegister.embedMatrix_apply_of_agreeOutside] at hxy
  have hagree : (QRegister.singleton j).AgreeOutside x y := by
    by_contra hnot
    simp [hnot] at hxy
  simp only [hagree, ↓reduceIte, mul_one] at hxy
  have hx0 : (QRegister.singleton j).extractIndex x = 0 := by
    by_contra hx
    have hx1 : (QRegister.singleton j).extractIndex x = 1 := by
      apply Fin.ext
      have hlt : ((QRegister.singleton j).extractIndex x).val < 2 :=
        ((QRegister.singleton j).extractIndex x).isLt
      have hxval : ((QRegister.singleton j).extractIndex x).val ≠ 0 :=
        fun h0 ↦ hx (Fin.ext h0)
      change ((QRegister.singleton j).extractIndex x).val = 1
      omega
    simp [hx1] at hxy
  have hy1 : (QRegister.singleton j).extractIndex y = 1 := by
    by_contra hy
    have hy0 : (QRegister.singleton j).extractIndex y = 0 := by
      apply Fin.ext
      have hlt : ((QRegister.singleton j).extractIndex y).val < 2 :=
        ((QRegister.singleton j).extractIndex y).isLt
      have hyval : ((QRegister.singleton j).extractIndex y).val ≠ 1 :=
        fun h1 ↦ hy (Fin.ext h1)
      change ((QRegister.singleton j).extractIndex y).val = 0
      omega
    simp [hx0, hy0] at hxy
  have hbx : basisBits k x j = basisBits 1 ((QRegister.singleton j).extractIndex x) 0 := by
    exact ((QRegister.singleton j).basisBits_extractIndex x 0).symm
  have hby : basisBits k y j = basisBits 1 ((QRegister.singleton j).extractIndex y) 0 := by
    exact ((QRegister.singleton j).basisBits_extractIndex y 0).symm
  rw [hx0] at hbx
  rw [hy1] at hby
  have hb0 : (basisBits 1 (0 : Fin 2) 0).val = 0 := by decide
  have hb1 : (basisBits 1 (1 : Fin 2) 0).val = 1 := by decide
  refine ⟨(QRegister.singleton_agreeOutside j x y).mp hagree, ?_, ?_⟩
  · rw [hbx, hb0]
  · rw [hby, hb1]

theorem jwStep_mul_jwString_of_le {k : ℕ} {j ℓ : Fin k} (h : ℓ ≤ j) :
    jwStep k j * jwString k ℓ = jwString k ℓ * jwStep k j := by
  ext x y
  rw [jwString, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hxy : jwStep k j x y = 0
  · simp [hxy]
  · obtain ⟨hother, _, _⟩ := jwStep_support hxy
    have hsum : ∑ q ∈ Finset.univ.filter (· < ℓ), (basisBits k x q).val =
        ∑ q ∈ Finset.univ.filter (· < ℓ), (basisBits k y q).val := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqlt : q < ℓ := (Finset.mem_filter.mp hq).2
      have hqne : q ≠ j := ne_of_lt (lt_of_lt_of_le hqlt h)
      rw [hother q hqne]
    rw [hsum, mul_comm]

theorem jwStep_mul_jwString_of_lt {k : ℕ} {j ℓ : Fin k} (h : j < ℓ) :
    jwStep k j * jwString k ℓ = -(jwString k ℓ * jwStep k j) := by
  ext x y
  rw [Matrix.neg_apply, jwString, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hxy : jwStep k j x y = 0
  · simp [hxy]
  · obtain ⟨hother, hx0, hy1⟩ := jwStep_support hxy
    have hjmem : j ∈ Finset.univ.filter (· < ℓ) := Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
    have herase : ∑ q ∈ (Finset.univ.filter (· < ℓ)).erase j, (basisBits k x q).val =
        ∑ q ∈ (Finset.univ.filter (· < ℓ)).erase j, (basisBits k y q).val := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hother q (Finset.ne_of_mem_erase hq)]
    have hsumx := (Finset.add_sum_erase (Finset.univ.filter (· < ℓ))
      (fun q ↦ (basisBits k x q).val) hjmem).symm
    have hsumy := (Finset.add_sum_erase (Finset.univ.filter (· < ℓ))
      (fun q ↦ (basisBits k y q).val) hjmem).symm
    rw [hsumx, hsumy, hx0, hy1, herase, zero_add, pow_add, pow_one]
    ring

/-! ## Part 2: Canonical Anticommutation Relations (CAR) -/

@[simp]
theorem jwAnnihilate_mul_self (k : ℕ) (j : Fin k) :
    jwAnnihilate k j * jwAnnihilate k j = 0 := by
  calc
    jwAnnihilate k j * jwAnnihilate k j
        = jwString k j * (jwStep k j * jwString k j * jwStep k j) := by
            simp only [jwAnnihilate_eq_mul, Matrix.mul_assoc]
    _ = jwString k j * (jwString k j * (jwStep k j * jwStep k j)) := by
            rw [jwStep_mul_jwString_of_le le_rfl, Matrix.mul_assoc]
    _ = 0 := by simp

private lemma jwAnnihilate_anticomm_of_lt {k : ℕ} {i j : Fin k} (hij : i < j) :
    jwAnnihilate k i * jwAnnihilate k j + jwAnnihilate k j * jwAnnihilate k i = 0 := by
  have h1 : jwAnnihilate k i * jwAnnihilate k j =
      -(jwString k i * (jwString k j * (jwStep k i * jwStep k j))) := by
    calc
      jwAnnihilate k i * jwAnnihilate k j
          = jwString k i * ((jwStep k i * jwString k j) * jwStep k j) := by
              simp only [jwAnnihilate_eq_mul, Matrix.mul_assoc]
      _ = -(jwString k i * (jwString k j * (jwStep k i * jwStep k j))) := by
              rw [jwStep_mul_jwString_of_lt hij]
              simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have h2 : jwAnnihilate k j * jwAnnihilate k i =
      jwString k i * (jwString k j * (jwStep k i * jwStep k j)) := by
    calc
      jwAnnihilate k j * jwAnnihilate k i
          = jwString k j * ((jwStep k j * jwString k i) * jwStep k i) := by
              simp only [jwAnnihilate_eq_mul, Matrix.mul_assoc]
      _ = (jwString k j * jwString k i) * (jwStep k j * jwStep k i) := by
              rw [jwStep_mul_jwString_of_le (le_of_lt hij)]
              simp only [Matrix.mul_assoc]
      _ = jwString k i * (jwString k j * (jwStep k i * jwStep k j)) := by
              rw [jwString_mul_comm, jwStep_comm_of_ne (ne_of_gt hij), Matrix.mul_assoc]
  rw [h1, h2, neg_add_cancel]

/-- Fermionic CAR `{a_i, a_j} = 0`. -/
theorem jwAnnihilate_anticomm (k : ℕ) (i j : Fin k) :
    jwAnnihilate k i * jwAnnihilate k j + jwAnnihilate k j * jwAnnihilate k i = 0 := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact jwAnnihilate_anticomm_of_lt hij
  · simp
  · rw [add_comm]
    exact jwAnnihilate_anticomm_of_lt hji

/-! ## Part 3: Rotated Orbital Number Operators & Reflections -/

@[simp]
theorem spinOrbital_eq_iff (N : ℕ) (p q : Fin N) (σ : Fin 2) :
    spinOrbital N p σ = spinOrbital N q σ ↔ p = q := by
  constructor
  · intro h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp [spinOrbital] at hval
    omega
  · rintro rfl
    rfl

/-- Rotated annihilation operator `b_{χ,σ} = ∑_p χ_p a_{p,σ}`. -/
noncomputable def orbitalAnnihilate (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    Operator (2 ^ (2 * N)) :=
  ∑ p : Fin N, (χ p : ℂ) • jwAnnihilate (2 * N) (spinOrbital N p σ)

theorem orbitalNumberOp_eq_annihilate (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    orbitalNumberOp N χ σ = (orbitalAnnihilate N χ σ)ᴴ * orbitalAnnihilate N χ σ := rfl

theorem orbitalAnnihilate_conjTranspose (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    (orbitalAnnihilate N χ σ)ᴴ =
      ∑ p : Fin N, (χ p : ℂ) • (jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ := by
  simp only [orbitalAnnihilate, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal]

@[simp]
theorem orbitalAnnihilate_mul_self (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    orbitalAnnihilate N χ σ * orbitalAnnihilate N χ σ = 0 := by
  let b := orbitalAnnihilate N χ σ
  have hexpand : b * b = ∑ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) •
      (jwAnnihilate (2 * N) (spinOrbital N p σ) *
        jwAnnihilate (2 * N) (spinOrbital N q σ)) := by
    dsimp only [b, orbitalAnnihilate]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, Matrix.smul_mul]
    simp only [Matrix.mul_smul, smul_smul]
  have hswap : b * b = ∑ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) •
      (jwAnnihilate (2 * N) (spinOrbital N q σ) *
        jwAnnihilate (2 * N) (spinOrbital N p σ)) := by
    rw [hexpand, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [mul_comm (χ q : ℂ) (χ p : ℂ)]
  have htwo : (2 : ℂ) • (b * b) = 0 := by
    rw [two_smul]
    nth_rw 1 [hexpand]
    rw [hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro q _
    rw [← smul_add, jwAnnihilate_anticomm, smul_zero]
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

@[simp]
theorem orbitalAnnihilate_conjTranspose_mul_self (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    (orbitalAnnihilate N χ σ)ᴴ * (orbitalAnnihilate N χ σ)ᴴ = 0 := by
  rw [← Matrix.conjTranspose_mul, orbitalAnnihilate_mul_self, Matrix.conjTranspose_zero]

@[simp]
theorem orbitalNumberOp_conjTranspose (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    (orbitalNumberOp N χ σ)ᴴ = orbitalNumberOp N χ σ := by
  simp [orbitalNumberOp_eq_annihilate, Matrix.conjTranspose_mul]

/-- Hermitian reflection `Z_{χ,σ} := 1 - 2 • orbitalNumberOp N χ σ` associated with orbital `χ`. -/
noncomputable def orbitalReflection (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    Operator (2 ^ (2 * N)) :=
  1 - (2 : ℂ) • orbitalNumberOp N χ σ

/-! ## Part 4: Linearity & Rank-1 Decomposition of `oneBodyHamiltonian` -/

/-! ## Part 5: Exact Commutation with `electronSectorProjector` -/

theorem mul_diagonal_comm_of_support {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (g : d → ℂ) (h : ∀ x z, M x z ≠ 0 → g x = g z) :
    M * Matrix.diagonal g = Matrix.diagonal g * M := by
  ext x z
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hxz : M x z = 0
  · simp [hxz]
  · rw [h x z hxz, mul_comm]

/-- Computational-basis Hamming weight (total particle number) on `k` spin-orbital wires. -/
def hammingWeight (k : ℕ) (x : Fin (2 ^ k)) : ℕ :=
  ∑ q : Fin k, (basisBits k x q).val

theorem jwAnnihilate_support_hammingWeight {k : ℕ} {j : Fin k} {x y : Fin (2 ^ k)}
    (hxy : jwAnnihilate k j x y ≠ 0) :
    hammingWeight k y = 1 + hammingWeight k x := by
  rw [jwAnnihilate_eq_mul, jwString, Matrix.diagonal_mul] at hxy
  have hstep : jwStep k j x y ≠ 0 := right_ne_zero_of_mul hxy
  obtain ⟨hother, hx0, hy1⟩ := jwStep_support hstep
  have hjmem : j ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ j
  have herase : ∑ q ∈ Finset.univ.erase j, (basisBits k x q).val =
      ∑ q ∈ Finset.univ.erase j, (basisBits k y q).val := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hother q (Finset.ne_of_mem_erase hq)]
  have hsumx := (Finset.add_sum_erase Finset.univ (fun q ↦ (basisBits k x q).val) hjmem).symm
  have hsumy := (Finset.add_sum_erase Finset.univ (fun q ↦ (basisBits k y q).val) hjmem).symm
  unfold hammingWeight
  rw [hsumx, hsumy, hx0, hy1, herase, zero_add]

@[simp]
theorem electronSectorProjector_conjTranspose (k η : ℕ) :
    (electronSectorProjector k η)ᴴ = electronSectorProjector k η := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases h : ∑ q, (basisBits k x q).val = η <;> simp [electronSectorProjector, h]
  · simp [electronSectorProjector, hxy, Ne.symm hxy]

@[simp]
theorem electronSectorProjector_mul_self (k η : ℕ) :
    electronSectorProjector k η * electronSectorProjector k η = electronSectorProjector k η := by
  rw [electronSectorProjector, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  ext x
  by_cases h : ∑ q, (basisBits k x q).val = η <;> simp [h]

theorem jwHop_comm_electronSectorProjector (k η : ℕ) (p q : Fin k) :
    ((jwAnnihilate k p)ᴴ * jwAnnihilate k q) * electronSectorProjector k η =
      electronSectorProjector k η * ((jwAnnihilate k p)ᴴ * jwAnnihilate k q) := by
  apply mul_diagonal_comm_of_support
  intro x z hxz
  rw [Matrix.mul_apply] at hxz
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxz
  have hyp : (jwAnnihilate k p)ᴴ x y ≠ 0 := left_ne_zero_of_mul hy
  have hyq : jwAnnihilate k q y z ≠ 0 := right_ne_zero_of_mul hy
  have hpy : jwAnnihilate k p y x ≠ 0 := by
    intro h0
    apply hyp
    simp [Matrix.conjTranspose_apply, h0]
  have hwx := jwAnnihilate_support_hammingWeight hpy
  have hwz := jwAnnihilate_support_hammingWeight hyq
  have heq : ∑ r, (basisBits k x r).val = ∑ r, (basisBits k z r).val := by
    change hammingWeight k x = hammingWeight k z
    omega
  rw [heq]

theorem orbitalNumberOp_comm_electronSectorProjector (N η : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    orbitalNumberOp N χ σ * electronSectorProjector (2 * N) η =
      electronSectorProjector (2 * N) η * orbitalNumberOp N χ σ := by
  have hexp : orbitalNumberOp N χ σ =
      ∑ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) •
        ((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ *
          jwAnnihilate (2 * N) (spinOrbital N q σ)) := by
    rw [orbitalNumberOp_eq_annihilate, orbitalAnnihilate_conjTranspose, orbitalAnnihilate,
      Finset.sum_mul]
    simp only [Finset.mul_sum, Matrix.smul_mul]
    simp only [Matrix.mul_smul, smul_smul]
  rw [hexp]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (((χ p : ℂ) * (χ q : ℂ)) • ·)
    (jwHop_comm_electronSectorProjector (2 * N) η (spinOrbital N p σ) (spinOrbital N q σ))

theorem orbitalReflection_comm_electronSectorProjector (N η : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    orbitalReflection N χ σ * electronSectorProjector (2 * N) η =
      electronSectorProjector (2 * N) η * orbitalReflection N χ σ := by
  simp only [orbitalReflection, sub_mul, mul_sub, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, orbitalNumberOp_comm_electronSectorProjector]


/-! ## Part 6 (new, Track 1): second CAR half `{a_i, a_j†} = δ_ij`, idempotent `n_χ`, `Z² = 1` -/

private lemma e01_conjTranspose :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))ᴴ = Matrix.single (1 : Fin 2) (0 : Fin 2) 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply, Matrix.single_apply]

private lemma e01_anticomm :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) * (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))ᴴ
      + (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))ᴴ * Matrix.single (0 : Fin 2) (1 : Fin 2) 1
      = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply, Fin.sum_univ_two]

theorem jwStep_anticomm_self (k : ℕ) (j : Fin k) :
    jwStep k j * (jwStep k j)ᴴ + (jwStep k j)ᴴ * jwStep k j = 1 := by
  unfold jwStep
  rw [← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul,
    ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_add, e01_anticomm,
    QRegister.embedMatrix_one]

theorem jwStep_comm_conjTranspose_of_ne {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    jwStep k i * (jwStep k j)ᴴ = (jwStep k j)ᴴ * jwStep k i := by
  unfold jwStep
  rw [← QRegister.embedMatrix_conjTranspose]
  exact QRegister.embedMatrix_comm_of_disjoint _ _ (QRegister.singleton_disjoint hij) _ _

theorem jwStepH_mul_jwString_of_le {k : ℕ} {j ℓ : Fin k} (h : ℓ ≤ j) :
    (jwStep k j)ᴴ * jwString k ℓ = jwString k ℓ * (jwStep k j)ᴴ := by
  have := congrArg Matrix.conjTranspose (jwStep_mul_jwString_of_le h)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jwString_conjTranspose] at this
  exact this.symm

theorem jwAnnihilate_conjTranspose_eq (k : ℕ) (j : Fin k) :
    (jwAnnihilate k j)ᴴ = (jwStep k j)ᴴ * jwString k j := by
  rw [jwAnnihilate_eq_mul, Matrix.conjTranspose_mul, jwString_conjTranspose]

theorem jwAnnihilate_anticomm_self (k : ℕ) (j : Fin k) :
    jwAnnihilate k j * (jwAnnihilate k j)ᴴ + (jwAnnihilate k j)ᴴ * jwAnnihilate k j = 1 := by
  have hc1 : jwStep k j * jwString k j = jwString k j * jwStep k j :=
    jwStep_mul_jwString_of_le le_rfl
  have hc2 : (jwStep k j)ᴴ * jwString k j = jwString k j * (jwStep k j)ᴴ :=
    jwStepH_mul_jwString_of_le le_rfl
  have hSS := jwString_mul_self k j
  have h1 : jwAnnihilate k j * (jwAnnihilate k j)ᴴ = jwStep k j * (jwStep k j)ᴴ := by
    rw [jwAnnihilate_conjTranspose_eq, jwAnnihilate_eq_mul]
    calc jwString k j * jwStep k j * ((jwStep k j)ᴴ * jwString k j)
        = jwString k j * (jwStep k j * ((jwStep k j)ᴴ * jwString k j)) := by
          simp only [Matrix.mul_assoc]
      _ = jwString k j * (jwStep k j * (jwString k j * (jwStep k j)ᴴ)) := by rw [hc2]
      _ = jwString k j * ((jwStep k j * jwString k j) * (jwStep k j)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = jwString k j * ((jwString k j * jwStep k j) * (jwStep k j)ᴴ) := by rw [hc1]
      _ = (jwString k j * jwString k j) * (jwStep k j * (jwStep k j)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = jwStep k j * (jwStep k j)ᴴ := by rw [hSS, Matrix.one_mul]
  have h2 : (jwAnnihilate k j)ᴴ * jwAnnihilate k j = (jwStep k j)ᴴ * jwStep k j := by
    rw [jwAnnihilate_conjTranspose_eq, jwAnnihilate_eq_mul]
    calc (jwStep k j)ᴴ * jwString k j * (jwString k j * jwStep k j)
        = (jwStep k j)ᴴ * ((jwString k j * jwString k j) * jwStep k j) := by
          simp only [Matrix.mul_assoc]
      _ = (jwStep k j)ᴴ * jwStep k j := by rw [hSS, Matrix.one_mul]
  rw [h1, h2]; exact jwStep_anticomm_self k j

private lemma jwAnnihilate_anticomm_conj_of_lt {k : ℕ} {i j : Fin k} (hij : i < j) :
    jwAnnihilate k i * (jwAnnihilate k j)ᴴ + (jwAnnihilate k j)ᴴ * jwAnnihilate k i = 0 := by
  have hne : i ≠ j := ne_of_lt hij
  have hSij : jwString k i * jwString k j = jwString k j * jwString k i := jwString_mul_comm k i j
  have hσiSj : jwStep k i * jwString k j = -(jwString k j * jwStep k i) :=
    jwStep_mul_jwString_of_lt hij
  have hσjHSi : (jwStep k j)ᴴ * jwString k i = jwString k i * (jwStep k j)ᴴ :=
    jwStepH_mul_jwString_of_le (le_of_lt hij)
  have hcomm := jwStep_comm_conjTranspose_of_ne hne
  have h1 : jwAnnihilate k i * (jwAnnihilate k j)ᴴ =
      -(jwString k i * ((jwStep k j)ᴴ * (jwString k j * jwStep k i))) := by
    rw [jwAnnihilate_conjTranspose_eq, jwAnnihilate_eq_mul]
    calc jwString k i * jwStep k i * ((jwStep k j)ᴴ * jwString k j)
        = jwString k i * ((jwStep k i * (jwStep k j)ᴴ) * jwString k j) := by
          simp only [Matrix.mul_assoc]
      _ = jwString k i * (((jwStep k j)ᴴ * jwStep k i) * jwString k j) := by rw [hcomm]
      _ = jwString k i * ((jwStep k j)ᴴ * (jwStep k i * jwString k j)) := by
          simp only [Matrix.mul_assoc]
      _ = -(jwString k i * ((jwStep k j)ᴴ * (jwString k j * jwStep k i))) := by
          rw [hσiSj]; simp only [Matrix.mul_neg]
  have h2 : (jwAnnihilate k j)ᴴ * jwAnnihilate k i =
      jwString k i * ((jwStep k j)ᴴ * (jwString k j * jwStep k i)) := by
    rw [jwAnnihilate_conjTranspose_eq, jwAnnihilate_eq_mul]
    calc (jwStep k j)ᴴ * jwString k j * (jwString k i * jwStep k i)
        = (jwStep k j)ᴴ * ((jwString k j * jwString k i) * jwStep k i) := by
          simp only [Matrix.mul_assoc]
      _ = (jwStep k j)ᴴ * ((jwString k i * jwString k j) * jwStep k i) := by rw [hSij]
      _ = ((jwStep k j)ᴴ * jwString k i) * (jwString k j * jwStep k i) := by
          simp only [Matrix.mul_assoc]
      _ = (jwString k i * (jwStep k j)ᴴ) * (jwString k j * jwStep k i) := by rw [hσjHSi]
      _ = jwString k i * ((jwStep k j)ᴴ * (jwString k j * jwStep k i)) := by
          simp only [Matrix.mul_assoc]
  rw [h1, h2, neg_add_cancel]

/-- Fermionic CAR `{a_i, a_j†} = δ_ij`. -/
theorem jwAnnihilate_anticomm_conj (k : ℕ) (i j : Fin k) :
    jwAnnihilate k i * (jwAnnihilate k j)ᴴ + (jwAnnihilate k j)ᴴ * jwAnnihilate k i =
      if i = j then 1 else 0 := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [if_neg (ne_of_lt hij)]; exact jwAnnihilate_anticomm_conj_of_lt hij
  · rw [if_pos rfl]; exact jwAnnihilate_anticomm_self k i
  · rw [if_neg (ne_of_gt hji)]
    have := congrArg Matrix.conjTranspose (jwAnnihilate_anticomm_conj_of_lt hji)
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at this
    exact this

/-- Rotated CAR: for a unit vector `χ`, `b b† + b† b = 1`. -/
theorem orbitalAnnihilate_anticomm {N : ℕ} (χ : Fin N → ℝ) (hχ : ∑ p, χ p ^ 2 = 1) (σ : Fin 2) :
    orbitalAnnihilate N χ σ * (orbitalAnnihilate N χ σ)ᴴ +
      (orbitalAnnihilate N χ σ)ᴴ * orbitalAnnihilate N χ σ = 1 := by
  set a : Fin N → Operator (2 ^ (2 * N)) := fun p => jwAnnihilate (2 * N) (spinOrbital N p σ)
    with ha
  have e1 : orbitalAnnihilate N χ σ * (orbitalAnnihilate N χ σ)ᴴ =
      ∑ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) • (a p * (a q)ᴴ) := by
    rw [orbitalAnnihilate_conjTranspose, orbitalAnnihilate, Finset.sum_mul]
    simp only [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by congr 1; ring
  have e2 : (orbitalAnnihilate N χ σ)ᴴ * orbitalAnnihilate N χ σ =
      ∑ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) • ((a q)ᴴ * a p) := by
    rw [orbitalAnnihilate_conjTranspose, orbitalAnnihilate, Finset.sum_mul, Finset.sum_comm]
    simp only [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha]
  rw [e1, e2, ← Finset.sum_add_distrib]
  have : ∀ p : Fin N, ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) • (a p * (a q)ᴴ) +
      ∑ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) • ((a q)ᴴ * a p) = ((χ p ^ 2 : ℝ) : ℂ) • (1 : Operator (2 ^ (2 * N))) := by
    intro p
    rw [← Finset.sum_add_distrib]
    have hq : ∀ q : Fin N, ((χ p : ℂ) * (χ q : ℂ)) • (a p * (a q)ᴴ) +
        ((χ p : ℂ) * (χ q : ℂ)) • ((a q)ᴴ * a p) =
        if q = p then ((χ p ^ 2 : ℝ) : ℂ) • (1 : Operator (2 ^ (2 * N))) else 0 := by
      intro q
      rw [← smul_add]
      have := jwAnnihilate_anticomm_conj (2 * N) (spinOrbital N p σ) (spinOrbital N q σ)
      simp only [ha]
      rw [this]
      by_cases hqp : q = p
      · subst hqp; simp [sq]
      · have : ¬ p = q := fun h => hqp h.symm
        simp [hqp, this]
    rw [Finset.sum_congr rfl (fun q _ => hq q)]
    simp
  rw [Finset.sum_congr rfl (fun p _ => this p), ← Finset.sum_smul]
  have hs : ∑ p : Fin N, ((χ p ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hχ]; simp
  rw [hs, one_smul]

theorem orbitalNumberOp_idem {N : ℕ} (χ : Fin N → ℝ) (hχ : ∑ p, χ p ^ 2 = 1) (σ : Fin 2) :
    orbitalNumberOp N χ σ * orbitalNumberOp N χ σ = orbitalNumberOp N χ σ := by
  set b := orbitalAnnihilate N χ σ with hb
  have hanti := orbitalAnnihilate_anticomm χ hχ σ
  have hbb : b * bᴴ = 1 - bᴴ * b := by rw [← hanti]; abel
  have h0 : bᴴ * bᴴ = 0 := orbitalAnnihilate_conjTranspose_mul_self N χ σ
  have h1 : b * b = 0 := orbitalAnnihilate_mul_self N χ σ
  rw [orbitalNumberOp_eq_annihilate]
  calc bᴴ * b * (bᴴ * b) = bᴴ * (b * bᴴ) * b := by simp only [Matrix.mul_assoc]
    _ = bᴴ * (1 - bᴴ * b) * b := by rw [hbb]
    _ = bᴴ * b - (bᴴ * bᴴ) * (b * b) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = bᴴ * b := by rw [h0, Matrix.zero_mul, sub_zero]

theorem orbitalReflection_conjTranspose (N : ℕ) (χ : Fin N → ℝ) (σ : Fin 2) :
    (orbitalReflection N χ σ)ᴴ = orbitalReflection N χ σ := by
  simp [orbitalReflection, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]

/-- The orbital reflection `Z_{χ,σ} = 1 - 2 n_{χ,σ}` is an involution for a unit vector `χ`. -/
theorem orbitalReflection_mul_self {N : ℕ} (χ : Fin N → ℝ) (hχ : ∑ p, χ p ^ 2 = 1) (σ : Fin 2) :
    orbitalReflection N χ σ * orbitalReflection N χ σ = 1 := by
  have h := orbitalNumberOp_idem χ hχ σ
  unfold orbitalReflection
  set n := orbitalNumberOp N χ σ
  calc (1 - (2 : ℂ) • n) * (1 - (2 : ℂ) • n)
      = 1 - (4 : ℂ) • n + (4 : ℂ) • (n * n) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        module
    _ = 1 := by rw [h]; abel

end Track1THC.JW
