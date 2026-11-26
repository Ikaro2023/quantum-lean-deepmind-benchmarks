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
public import Track2Grover.FindAllEvaluator
public import Track2Grover.Engine.FindAllJohnsonAltStep
/-
 # High-`d` `T_16` Polynomial, Walk Evaluator & Trajectory Checkpointing
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
open Real
open scoped Matrix

/- ## Section 1: 16-Term Triangle Helper & Degree-`16` Polynomial Contraction -/

private noncomputable def factInv : ℕ → ℝ
  | 0 => 1 | 1 => 1 | 2 => 1 / 2 | 3 => 1 / 6 | 4 => 1 / 24 | 5 => 1 / 120
  | 6 => 1 / 720 | 7 => 1 / 5040 | 8 => 1 / 40320 | 9 => 1 / 362880
  | 10 => 1 / 3628800 | 11 => 1 / 39916800 | 12 => 1 / 479001600
  | 13 => 1 / 6227020800 | 14 => 1 / 87178291200 | 15 => 1 / 1307674368000
  | 16 => 1 / 20922789888000 | _ + 17 => 0

private lemma factInv_nonneg : ∀ k, 0 ≤ factInv k
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | _ + 17 => by
    dsimp only [factInv]; norm_num

private noncomputable def sumUpTo {α : Type*} [AddCommMonoid α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => sumUpTo f n + f n

private lemma sumUpTo_le_sumUpTo {f g : ℕ → ℝ} :
    ∀ n, (∀ k < n, f k ≤ g k) → sumUpTo f n ≤ sumUpTo g n
  | 0, _ => le_rfl
  | n + 1, h => add_le_add (sumUpTo_le_sumUpTo n fun k hk ↦ h k (by omega)) (h n (by omega))

private lemma sumUpTo_nonneg {f : ℕ → ℝ} : ∀ n, (∀ k < n, 0 ≤ f k) → 0 ≤ sumUpTo f n
  | 0, _ => le_rfl
  | n + 1, h => add_nonneg (sumUpTo_nonneg n fun k hk ↦ h k (by omega)) (h n (by omega))

private lemma vecNorm_sumUpTo_smul_le {d : ℕ} (c w : ℕ → ℝ) (f : ℕ → Fin d → ℝ) (B : ℝ) :
    ∀ n, (∀ j < n, 0 ≤ c j) → (∀ j < n, c j * vecNorm (f j) ≤ w j * B) →
      vecNorm (sumUpTo (fun j ↦ c j • f j) n) ≤ sumUpTo w n * B
  | 0, _, _ => by simp [sumUpTo, vecNorm_zero]
  | n + 1, hc, hw => by
    dsimp only [sumUpTo]; rw [add_mul]
    refine (vecNorm_add_le _ _).trans (add_le_add
      (vecNorm_sumUpTo_smul_le c w f B n (fun j hj ↦ hc j (by omega))
        (fun j hj ↦ hw j (by omega))) ?_)
    rw [vecNorm_smul, abs_of_nonneg (hc n (by omega))]; exact hw n (by omega)

private lemma sumUpTo_apply_zero {d : ℕ} (f : ℕ → Fin d → ℝ) (j : Fin d) :
    ∀ n, (∀ k < n, f k j = 0) → (sumUpTo f n) j = 0
  | 0, _ => rfl
  | n + 1, h => by simp [sumUpTo, sumUpTo_apply_zero f j n fun k hk ↦ h k (by omega), h n]

private lemma vecNorm_smul_mulVec_le {d : ℕ} {η B : ℝ} {G : Matrix (Fin d) (Fin d) ℝ}
    (hη : 0 ≤ η) (hG : ∀ u, vecNorm (G *ᵥ u) ≤ B * vecNorm u) (u : Fin d → ℝ) :
    vecNorm ((η • G) *ᵥ u) ≤ (η * B) * vecNorm u := by
  rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg hη]
  exact (mul_le_mul_of_nonneg_left (hG u) hη).trans_eq (by ring)

/-- Degree-`16` truncated exponential `1 + X + X^2 / 2 +... + X^16 / 16` of a matrix `X`. -/
noncomputable def taylor16OfMat {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + X + (1 / 2 : ℝ) • X ^ 2 + (1 / 6 : ℝ) • X ^ 3 + (1 / 24 : ℝ) • X ^ 4
  + (1 / 120 : ℝ) • X ^ 5 + (1 / 720 : ℝ) • X ^ 6 + (1 / 5040 : ℝ) • X ^ 7
  + (1 / 40320 : ℝ) • X ^ 8 + (1 / 362880 : ℝ) • X ^ 9 + (1 / 3628800 : ℝ) • X ^ 10
  + (1 / 39916800 : ℝ) • X ^ 11 + (1 / 479001600 : ℝ) • X ^ 12 + (1 / 6227020800 : ℝ) • X ^ 13
  + (1 / 87178291200 : ℝ) • X ^ 14 + (1 / 1307674368000 : ℝ) • X ^ 15
  + (1 / 20922789888000 : ℝ) • X ^ 16

/-- Scaled degree-`16` truncated exponential `taylor16OfMat (t • G)`. -/
noncomputable abbrev taylor16Mat {d : ℕ} (t : ℝ) (G : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  taylor16OfMat (t • G)

theorem taylor16OfMat_zero {d : ℕ} : taylor16OfMat (0 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j; simp [taylor16OfMat]

private lemma taylor16OfMat_mulVec_eq_sum {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    taylor16OfMat X *ᵥ v = sumUpTo (fun k ↦ factInv k • ((X ^ k) *ᵥ v)) 17 := by
  dsimp only [sumUpTo, factInv]; ext i
  simp only [taylor16OfMat, pow_zero, pow_one, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem vecNorm_taylor16OfMat_mulVec_le {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ}
    (hX : Xᵀ = -X) (hB : ∀ u, vecNorm (X *ᵥ u) ≤ (3 / 2) * vecNorm u) (v : Fin d → ℝ) :
    vecNorm (taylor16OfMat X *ᵥ v) ≤ vecNorm v := by
  rw [vecNorm, Real.sqrt_le_iff]; refine ⟨vecNorm_nonneg v, ?_⟩; rw [sq_vecNorm]
  let x : ℕ → Fin d → ℝ := fun k ↦ (X ^ k) *ᵥ v
  let s : ℕ → ℝ := fun k ↦ vecSqNorm (x k)
  have hs_step (k : ℕ) : s (k + 1) ≤ (9 / 4) * s k := by
    have hx : x (k + 1) = X *ᵥ x k := by simp [x, pow_succ', Matrix.mulVec_mulVec]
    have hsq := pow_le_pow_left₀ (vecNorm_nonneg _) (hx ▸ hB (x k)) 2
    rw [sq_vecNorm, mul_pow, sq_vecNorm] at hsq; linarith
  have hneg_even (m : ℕ) : (-1 : ℝ) ^ (2 * m) = 1 := by simp [pow_mul]
  have heo (a b : ℕ) : x (2 * a) ⬝ᵥ x (2 * b + 1) = 0 := by
    dsimp only [x]
    rw [dot_pow_skew_shift hX v (2 * a) (2 * b + 1),
      show 2 * a + (2 * b + 1) = 2 * (a + b) + 1 by omega, dot_pow_skew_odd hX v (a + b), mul_zero]
  have hee (a b : ℕ) : x (2 * a) ⬝ᵥ x (2 * b) = (-1 : ℝ) ^ (a + b) * s (a + b) := by
    dsimp only [x, s]
    rw [dot_pow_skew_shift hX v (2 * a) (2 * b), show 2 * a + 2 * b = 2 * (a + b) by omega,
      dot_pow_skew_even hX v (a + b), hneg_even b, one_mul]
  have hoo (a b : ℕ) : x (2 * a + 1) ⬝ᵥ x (2 * b + 1) = (-1 : ℝ) ^ (a + b) * s (a + b + 1) := by
    dsimp only [x, s]
    rw [dot_pow_skew_shift hX v (2 * a + 1) (2 * b + 1),
      show (2 * a + 1) + (2 * b + 1) = 2 * (a + b + 1) by omega,
      dot_pow_skew_even hX v (a + b + 1), pow_add (-1 : ℝ) (2 * b) 1, hneg_even b, pow_one,
      pow_add (-1 : ℝ) (a + b) 1, pow_one]; ring
  let uE : Fin d → ℝ :=
    x 0 + (1 / 2 : ℝ) • x 2 + (1 / 24 : ℝ) • x 4 + (1 / 720 : ℝ) • x 6 + (1 / 40320 : ℝ) • x 8
    + (1 / 3628800 : ℝ) • x 10 + (1 / 479001600 : ℝ) • x 12 + (1 / 87178291200 : ℝ) • x 14
    + (1 / 20922789888000 : ℝ) • x 16
  let uO : Fin d → ℝ :=
    x 1 + (1 / 6 : ℝ) • x 3 + (1 / 120 : ℝ) • x 5 + (1 / 5040 : ℝ) • x 7
    + (1 / 362880 : ℝ) • x 9 + (1 / 39916800 : ℝ) • x 11 + (1 / 6227020800 : ℝ) • x 13
    + (1 / 1307674368000 : ℝ) • x 15
  have hsplit : taylor16OfMat X *ᵥ v = uE + uO := by
    ext i
    simp only [taylor16OfMat, uE, uO, x, pow_zero, pow_one, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcross : uE ⬝ᵥ uO = 0 := by
    dsimp only [uE, uO]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [heo 0 0, heo 0 1, heo 0 2, heo 0 3, heo 0 4, heo 0 5, heo 0 6, heo 0 7, heo 1 0, heo 1 1,
      heo 1 2, heo 1 3, heo 1 4, heo 1 5, heo 1 6, heo 1 7, heo 2 0, heo 2 1, heo 2 2, heo 2 3,
      heo 2 4, heo 2 5, heo 2 6, heo 2 7, heo 3 0, heo 3 1, heo 3 2, heo 3 3, heo 3 4, heo 3 5,
      heo 3 6, heo 3 7, heo 4 0, heo 4 1, heo 4 2, heo 4 3, heo 4 4, heo 4 5, heo 4 6, heo 4 7,
      heo 5 0, heo 5 1, heo 5 2, heo 5 3, heo 5 4, heo 5 5, heo 5 6, heo 5 7, heo 6 0, heo 6 1,
      heo 6 2, heo 6 3, heo 6 4, heo 6 5, heo 6 6, heo 6 7, heo 7 0, heo 7 1, heo 7 2, heo 7 3,
      heo 7 4, heo 7 5, heo 7 6, heo 7 7, heo 8 0, heo 8 1, heo 8 2, heo 8 3, heo 8 4, heo 8 5,
      heo 8 6, heo 8 7]; ring
  have hnorm_sum : vecSqNorm (uE + uO) = uE ⬝ᵥ uE + uO ⬝ᵥ uO := by
    simp only [vecSqNorm_eq_dot, add_dotProduct, dotProduct_add, hcross,
      dotProduct_comm uO uE ▸ hcross, add_zero, zero_add]
  have hpoly : uE ⬝ᵥ uE + uO ⬝ᵥ uO =
      s 0 - (s 9 / 188305108992000 - s 10 / 1255367393280000) -
        (s 11 / 27618082652160000 - s 12 / 1265410332426240000) -
        (s 13 / 98702005929246720000 - s 14 / 11692391471618457600000) -
        (s 15 / 1954299717399085056000000 - s 16 / 437763136697395052544000000) := by
    dsimp only [uE, uO]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hee 0 0, hee 0 1, hee 0 2, hee 0 3, hee 0 4, hee 0 5, hee 0 6, hee 0 7, hee 0 8, hee 1 0,
      hee 1 1, hee 1 2, hee 1 3, hee 1 4, hee 1 5, hee 1 6, hee 1 7, hee 1 8, hee 2 0, hee 2 1,
      hee 2 2, hee 2 3, hee 2 4, hee 2 5, hee 2 6, hee 2 7, hee 2 8, hee 3 0, hee 3 1, hee 3 2,
      hee 3 3, hee 3 4, hee 3 5, hee 3 6, hee 3 7, hee 3 8, hee 4 0, hee 4 1, hee 4 2, hee 4 3,
      hee 4 4, hee 4 5, hee 4 6, hee 4 7, hee 4 8, hee 5 0, hee 5 1, hee 5 2, hee 5 3, hee 5 4,
      hee 5 5, hee 5 6, hee 5 7, hee 5 8, hee 6 0, hee 6 1, hee 6 2, hee 6 3, hee 6 4, hee 6 5,
      hee 6 6, hee 6 7, hee 6 8, hee 7 0, hee 7 1, hee 7 2, hee 7 3, hee 7 4, hee 7 5, hee 7 6,
      hee 7 7, hee 7 8, hee 8 0, hee 8 1, hee 8 2, hee 8 3, hee 8 4, hee 8 5, hee 8 6, hee 8 7,
      hee 8 8, hoo 0 0, hoo 0 1, hoo 0 2, hoo 0 3, hoo 0 4, hoo 0 5, hoo 0 6, hoo 0 7, hoo 1 0,
      hoo 1 1, hoo 1 2, hoo 1 3, hoo 1 4, hoo 1 5, hoo 1 6, hoo 1 7, hoo 2 0, hoo 2 1, hoo 2 2,
      hoo 2 3, hoo 2 4, hoo 2 5, hoo 2 6, hoo 2 7, hoo 3 0, hoo 3 1, hoo 3 2, hoo 3 3, hoo 3 4,
      hoo 3 5, hoo 3 6, hoo 3 7, hoo 4 0, hoo 4 1, hoo 4 2, hoo 4 3, hoo 4 4, hoo 4 5, hoo 4 6,
      hoo 4 7, hoo 5 0, hoo 5 1, hoo 5 2, hoo 5 3, hoo 5 4, hoo 5 5, hoo 5 6, hoo 5 7, hoo 6 0,
      hoo 6 1, hoo 6 2, hoo 6 3, hoo 6 4, hoo 6 5, hoo 6 6, hoo 6 7, hoo 7 0, hoo 7 1, hoo 7 2,
      hoo 7 3, hoo 7 4, hoo 7 5, hoo 7 6, hoo 7 7]; norm_num; ring
  have hs0 : s 0 = vecSqNorm v := by simp [s, x]
  rw [hsplit, hnorm_sum, hpoly, hs0]
  linarith [hs_step 9, hs_step 11, hs_step 13, hs_step 15, vecSqNorm_nonneg (x 10),
    vecSqNorm_nonneg (x 12), vecSqNorm_nonneg (x 14), vecSqNorm_nonneg (x 16)]

theorem vecNorm_taylor16Mat_mulVec_le {d : ℕ} {t B : ℝ} {G : Matrix (Fin d) (Fin d) ℝ}
    (hG : Gᵀ = -G) (ht : 0 ≤ t) (_hB0 : 0 ≤ B)
    (hGB : ∀ u, vecNorm (G *ᵥ u) ≤ B * vecNorm u) (htB : t * B ≤ 3 / 2) (v : Fin d → ℝ) :
    vecNorm (taylor16Mat t G *ᵥ v) ≤ vecNorm v := by
  apply vecNorm_taylor16OfMat_mulVec_le
  · rw [Matrix.transpose_smul, hG, smul_neg]
  · intro u
    exact (vecNorm_smul_mulVec_le ht hGB u).trans
      (mul_le_mul_of_nonneg_right htB (vecNorm_nonneg u))

/- ## Section 2: Lipschitz Stability & 35-Monomial Bernstein Substep Grouping -/

theorem vecNorm_pow_sub_pow_mulVec_three_halves_le {d : ℕ} {X Y : Matrix (Fin d) (Fin d) ℝ} {δ : ℝ}
    (hX : ∀ u, vecNorm (X *ᵥ u) ≤ (3 / 2) * vecNorm u)
    (hY : ∀ u, vecNorm (Y *ᵥ u) ≤ (3 / 2) * vecNorm u) (hδ : 0 ≤ δ)
    (hXY : ∀ u, vecNorm ((X - Y) *ᵥ u) ≤ δ * vecNorm u) :
    ∀ (k : ℕ) (v : Fin d → ℝ),
      vecNorm ((X ^ k - Y ^ k) *ᵥ v) ≤ (k : ℝ) * (3 / 2 : ℝ) ^ (k - 1) * δ * vecNorm v
  | 0, _ => by simp [vecNorm_zero]
  | k + 1, v => by
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simpa using hXY v
    · have hsplit : (X ^ (k + 1) - Y ^ (k + 1)) *ᵥ v =
          X *ᵥ ((X ^ k - Y ^ k) *ᵥ v) + (X - Y) *ᵥ ((Y ^ k) *ᵥ v) := by
        rw [pow_succ', pow_succ', Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
        ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
      have hYk := vecNorm_pow_mulVec_le (by norm_num) hY k v
      have hih := vecNorm_pow_sub_pow_mulVec_three_halves_le hX hY hδ hXY k v
      have hpow_eq : (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ (k - 1) = (3 / 2 : ℝ) ^ k := by
        conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
      rw [hsplit, Nat.add_sub_cancel]
      refine (vecNorm_add_le _ _).trans ((add_le_add (hX _) (hXY _)).trans ?_)
      refine (add_le_add (mul_le_mul_of_nonneg_left hih (by norm_num))
        (mul_le_mul_of_nonneg_left hYk hδ)).trans_eq ?_
      push_cast; linear_combination ((k : ℝ) * δ * vecNorm v) * hpow_eq

theorem vecNorm_taylor16OfMat_sub_mulVec_le {d : ℕ} {X Y : Matrix (Fin d) (Fin d) ℝ} {δ : ℝ}
    (hX : ∀ u, vecNorm (X *ᵥ u) ≤ (3 / 2) * vecNorm u)
    (hY : ∀ u, vecNorm (Y *ᵥ u) ≤ (3 / 2) * vecNorm u) (hδ : 0 ≤ δ)
    (hXY : ∀ u, vecNorm ((X - Y) *ᵥ u) ≤ δ * vecNorm u) (v : Fin d → ℝ) :
    vecNorm ((taylor16OfMat X - taylor16OfMat Y) *ᵥ v) ≤ 5 * δ * vecNorm v := by
  let dVec : ℕ → Fin d → ℝ := fun k ↦ (X ^ k - Y ^ k) *ᵥ v
  have hdecomp : (taylor16OfMat X - taylor16OfMat Y) *ᵥ v =
      sumUpTo (fun j ↦ factInv (j + 1) • dVec (j + 1)) 16 := by
    ext i
    simp only [sumUpTo, factInv, dVec, Nat.reduceAdd, taylor16OfMat, pow_one, Matrix.sub_mulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.add_apply,
      Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomp]
  let w : ℕ → ℝ := fun j ↦ factInv (j + 1) * (((j + 1 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ j)
  have hsum := vecNorm_sumUpTo_smul_le (fun j ↦ factInv (j + 1)) w (fun j ↦ dVec (j + 1))
    (δ * vecNorm v) 16 (fun _ _ ↦ factInv_nonneg _) fun j _ ↦ by
      have hd := vecNorm_pow_sub_pow_mulVec_three_halves_le hX hY hδ hXY (j + 1) v
      rw [Nat.add_sub_cancel] at hd
      exact (mul_le_mul_of_nonneg_left hd (factInv_nonneg _)).trans_eq (by dsimp only [w]; ring)
  have hcoef : sumUpTo w 16 ≤ 5 := by
    dsimp only [w, sumUpTo, factInv]; norm_num
  exact hsum.trans
    ((mul_le_mul_of_nonneg_right hcoef (mul_nonneg hδ (vecNorm_nonneg v))).trans_eq (by ring))

private noncomputable def t16RemCoeff (s : ℝ) (r : ℕ) : ℝ :=
  sumUpTo (fun j ↦ factInv (r + 1 + j) * factInv (16 - j) * s ^ (16 - j)) (16 - r)

private lemma t16RemCoeff_nonneg {s : ℝ} (hs0 : 0 ≤ s) (r : ℕ) : 0 ≤ t16RemCoeff s r :=
  sumUpTo_nonneg _ fun _ _ ↦
    mul_nonneg (mul_nonneg (factInv_nonneg _) (factInv_nonneg _)) (pow_nonneg hs0 _)

private noncomputable def t16CapTerm (s x : ℝ) : ℕ → ℝ
  | 0 => t16RemCoeff s 0 * x ^ 17
  | r + 1 => t16RemCoeff s (r + 1) * ((3 / 2 : ℝ) ^ r * x ^ 18)

private lemma t16_rem_scalar_le {s x : ℝ} (hs0 : 0 ≤ s) (hx0 : 0 ≤ x)
    (hsx : (s + 1) * x ≤ 3 / 2) :
    sumUpTo (fun r ↦ t16RemCoeff s r * x ^ (17 + r)) 16 ≤
      (((s + 1) * x) ^ 17 - (s * x) ^ 17) / 300000000000000 := by
  have hx_32 : x ≤ 3 / 2 := by nlinarith
  have h1 : sumUpTo (fun r ↦ t16RemCoeff s r * x ^ (17 + r)) 16 ≤
      sumUpTo (t16CapTerm s x) 16 := sumUpTo_le_sumUpTo 16 fun r _ ↦ by
    cases r with
    | zero => dsimp only [t16CapTerm, Nat.add_zero]; exact le_rfl
    | succ r =>
      dsimp only [t16CapTerm]
      rw [show 17 + (r + 1) = 18 + r by omega, pow_add, mul_comm (x ^ 18)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx_32 r) (pow_nonneg hx0 18))
        (t16RemCoeff_nonneg hs0 (r + 1))
  let u : ℝ := s * x; let z : ℝ := 3 / 2 - (s + 1) * x
  have hu : 0 ≤ u := mul_nonneg hs0 hx0; have hz : 0 ≤ z := by dsimp only [z]; linarith
  have hid : (((s + 1) * x) ^ 17 - (s * x) ^ 17) / 300000000000000 -
      sumUpTo (t16CapTerm s x) 16 =
      (1 / 450000000000000 : ℝ) * (x ^ 17 * z + x ^ 18) + (9063709 : ℝ) * z *
        ((1 / 1532430900000000000000 : ℝ) * (u * x ^ 16 + u ^ 16 * x)
        + (1 / 191553862500000000000 : ℝ) * (u ^ 2 * x ^ 15 + u ^ 15 * x ^ 2)
        + (1 / 38310772500000000000 : ℝ) * (u ^ 3 * x ^ 14 + u ^ 14 * x ^ 3)
        + (1 / 10945935000000000000 : ℝ) * (u ^ 4 * x ^ 13 + u ^ 13 * x ^ 4)
        + (1 / 4209975000000000000 : ℝ) * (u ^ 5 * x ^ 12 + u ^ 12 * x ^ 5)
        + (1 / 2104987500000000000 : ℝ) * (u ^ 6 * x ^ 11 + u ^ 11 * x ^ 6)
        + (1 / 1339537500000000000 : ℝ) * (u ^ 7 * x ^ 10 + u ^ 10 * x ^ 7)
        + (1 / 1071630000000000000 : ℝ) * (u ^ 8 * x ^ 9 + u ^ 9 * x ^ 8))
      + (12469111 / 1532430900000000000000 : ℝ) * u * x ^ 17 +
      (4610491 / 157172400000000000000 : ℝ) * u ^ 2 * x ^ 16 +
      (1771479881 / 12259447200000000000000 : ℝ) * u ^ 3 * x ^ 15 +
      (3494131637 / 6538371840000000000000 : ℝ) * u ^ 4 * x ^ 14 +
      (97005607711 / 65383718400000000000000 : ℝ) * u ^ 5 * x ^ 13 +
      (2498854784861 / 784604620800000000000000 : ℝ) * u ^ 6 * x ^ 12 +
      (6590582160671 / 1220496076800000000000000 : ℝ) * u ^ 7 * x ^ 11 +
      (429183744869911 / 58583811686400000000000000 : ℝ) * u ^ 8 * x ^ 10 +
      (1688335731432769 / 210901722071040000000000000 : ℝ) * u ^ 9 * x ^ 9 +
      (9916532699143489 / 1406011480473600000000000000 : ℝ) * u ^ 10 * x ^ 8 +
      (17140625643746411 / 3436916952268800000000000000 : ℝ) * u ^ 11 * x ^ 7 +
      (692529737320552387 / 247458020563353600000000000000 : ℝ) * u ^ 12 * x ^ 6 +
      (2617262362241193923 / 2144636178215731200000000000000 : ℝ) * u ^ 13 * x ^ 5 +
      (4780516023863247221 / 12009962598008094720000000000000 : ℝ) * u ^ 14 * x ^ 4 +
      (32351137203864962143 / 360298877940242841600000000000000 : ℝ) * u ^ 15 * x ^ 3 +
      (14266016578501771637 / 1281062677120863436800000000000000 : ℝ) * u ^ 16 * x ^ 2 +
      (9063709 / 1532430900000000000000 : ℝ) * u ^ 17 * x := by
    simp only [u, z, t16CapTerm, t16RemCoeff, sumUpTo, factInv, Nat.reduceAdd, Nat.reduceSub]
    ring
  have hpos : 0 ≤ (((s + 1) * x) ^ 17 - (s * x) ^ 17) / 300000000000000 -
      sumUpTo (t16CapTerm s x) 16 := by rw [hid]; positivity
  linarith

private lemma t16_rem_expand {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (v : Fin d → ℝ) :
    (taylor16OfMat Y * taylor16OfMat (s • Y) - taylor16OfMat ((s + 1) • Y)) *ᵥ v =
      sumUpTo (fun r ↦ t16RemCoeff s r • ((Y ^ (17 + r)) *ᵥ v)) 16 := by
  let y : ℕ → Fin d → ℝ := fun k ↦ (Y ^ k) *ᵥ v
  have hy_smul (r : ℝ) (j : ℕ) : ((r • Y) ^ j) *ᵥ v = (r ^ j) • y j := by
    rw [smul_pow, Matrix.smul_mulVec]
  have hy_mul (i j : ℕ) (c : ℝ) : (Y ^ i) *ᵥ (c • y j) = c • y (i + j) := by
    dsimp only [y]; rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_add]
  have hY1 (u : Fin d → ℝ) : Y *ᵥ u = (Y ^ 1) *ᵥ u := by rw [pow_one]
  change (taylor16OfMat Y * taylor16OfMat (s • Y) - taylor16OfMat ((s + 1) • Y)) *ᵥ v =
    sumUpTo (fun r ↦ t16RemCoeff s r • y (17 + r)) 16
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    taylor16OfMat_mulVec_eq_sum (s • Y) v, taylor16OfMat_mulVec_eq_sum ((s + 1) • Y) v]
  simp only [sumUpTo, t16RemCoeff, factInv, Nat.reduceAdd, Nat.reduceSub, zero_add, hy_smul,
    smul_smul]
  unfold taylor16OfMat
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hY1, Matrix.mulVec_add,
    hy_mul, smul_smul, Nat.reduceAdd]
  ext idx
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem vecNorm_taylor16_mul_sub_succ_le {d : ℕ} {Y : Matrix (Fin d) (Fin d) ℝ} {x : ℝ}
    (hx0 : 0 ≤ x) (hY : ∀ u, vecNorm (Y *ᵥ u) ≤ x * vecNorm u)
    (s : ℝ) (hs0 : 0 ≤ s) (hsx : (s + 1) * x ≤ 3 / 2) (v : Fin d → ℝ) :
    vecNorm ((taylor16OfMat Y * taylor16OfMat (s • Y) - taylor16OfMat ((s + 1) • Y)) *ᵥ v) ≤
      (((s + 1) * x) ^ 17 - (s * x) ^ 17) / 300000000000000 * vecNorm v := by
  rw [t16_rem_expand Y s v]
  have hsum := vecNorm_sumUpTo_smul_le (t16RemCoeff s) (fun r ↦ t16RemCoeff s r * x ^ (17 + r))
    (fun r ↦ (Y ^ (17 + r)) *ᵥ v) (vecNorm v) 16 (fun r _ ↦ t16RemCoeff_nonneg hs0 r) fun r _ ↦
      (mul_le_mul_of_nonneg_left (vecNorm_pow_mulVec_le hx0 hY (17 + r) v)
        (t16RemCoeff_nonneg hs0 r)).trans_eq (by ring)
  exact hsum.trans (mul_le_mul_of_nonneg_right (t16_rem_scalar_le hs0 hx0 hsx) (vecNorm_nonneg v))

theorem vecNorm_taylor16Mat_substep_le {d : ℕ} {η B : ℝ} {G : Matrix (Fin d) (Fin d) ℝ}
    (hG : Gᵀ = -G) (hη : 0 ≤ η) (hB0 : 0 ≤ B) (hGB : ∀ u, vecNorm (G *ᵥ u) ≤ B * vecNorm u) :
    ∀ (q : ℕ), (q : ℝ) * η * B ≤ 3 / 2 → ∀ (v : Fin d → ℝ),
      vecNorm (((taylor16Mat η G) ^ q - taylor16Mat ((q : ℝ) * η) G) *ᵥ v) ≤
        ((q : ℝ) * η * B) ^ 17 / 300000000000000 * vecNorm v
  | 0, _, _ => by simp [taylor16Mat, taylor16OfMat_zero, vecNorm_zero]
  | q + 1, hq, v => by
    have hq' : ((q : ℝ) + 1) * (η * B) ≤ 3 / 2 := by push_cast at hq; linarith
    have hq_prev : (q : ℝ) * η * B ≤ 3 / 2 := by nlinarith [mul_nonneg hη hB0]
    have hηB_le : η * B ≤ 3 / 2 := by
      nlinarith [mul_nonneg hη hB0, (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    have hT_contr (w : Fin d → ℝ) : vecNorm (taylor16Mat η G *ᵥ w) ≤ vecNorm w :=
      vecNorm_taylor16Mat_mulVec_le hG hη hB0 hGB hηB_le w
    have hstep_split :
        ((taylor16Mat η G) ^ (q + 1) - taylor16Mat (((q + 1 : ℕ) : ℝ) * η) G) *ᵥ v =
          taylor16Mat η G *ᵥ (((taylor16Mat η G) ^ q - taylor16Mat ((q : ℝ) * η) G) *ᵥ v) +
          (taylor16OfMat (η • G) * taylor16OfMat ((q : ℝ) • (η • G)) -
            taylor16OfMat (((q : ℝ) + 1) • (η • G))) *ᵥ v := by
      dsimp only [taylor16Mat]; push_cast
      rw [pow_succ', ← smul_smul (q : ℝ) η G, ← smul_smul ((q : ℝ) + 1) η G,
        Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      ext idx; simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hsecond := vecNorm_taylor16_mul_sub_succ_le (mul_nonneg hη hB0)
      (vecNorm_smul_mulVec_le hη hGB) (q : ℝ) (Nat.cast_nonneg q) hq' v
    have hih := vecNorm_taylor16Mat_substep_le hG hη hB0 hGB q hq_prev v
    rw [hstep_split]
    refine (vecNorm_add_le _ _).trans ((add_le_add ((hT_contr _).trans hih) hsecond).trans_eq ?_)
    push_cast; ring

/- ## Section 3: 16-Stage Horner Operator Identity & Rounding Amplification -/

/-- Exact real Horner stage `v + (1 / deg) • (H *ᵥ cur)` for `taylor16OfMat H *ᵥ v`. -/
noncomputable def horner16Step {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (v cur : Fin d → ℝ) (deg : ℕ) : Fin d → ℝ :=
  v + (1 / (deg : ℝ)) • (H *ᵥ cur)

/-- Unrounded 16-stage Horner recursion from `k = 0` (`v`) to `k = 16` (`taylor16OfMat H *ᵥ
  v`). -/
noncomputable def horner16Ideal {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) : ℕ → Fin d → ℝ
  | 0 => v
  | k + 1 => horner16Step H v (horner16Ideal H v k) (16 - k)

theorem horner16Ideal_sixteen_eq {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    horner16Ideal H v 16 = taylor16OfMat H *ᵥ v := by
  let y : ℕ → Fin d → ℝ := fun k ↦ (H ^ k) *ᵥ v
  have hy0 : v = y 0 := by simp [y]
  have hy_step (k : ℕ) : H *ᵥ y k = y (k + 1) := by
    dsimp only [y]; rw [pow_succ', Matrix.mulVec_mulVec]
  have hy_smul (c : ℝ) (k : ℕ) : H *ᵥ (c • y k) = c • y (k + 1) := by
    rw [Matrix.mulVec_smul, hy_step]
  dsimp only [horner16Ideal, horner16Step]; rw [hy0]
  simp only [Matrix.mulVec_add, hy_step, hy_smul, smul_add, smul_smul]
  ext idx
  simp only [taylor16OfMat, y, pow_zero, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; norm_num; ring

theorem vecNorm_horner16Step_approx {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : ∀ u, vecNorm (H *ᵥ u) ≤ (3 / 2) * vecNorm u) {v cur ideal next : Fin d → ℝ}
    {deg : ℕ} (hdeg : 1 ≤ deg) {E ε : ℝ} (hcur : vecNorm (cur - ideal) ≤ E)
    (hnext : vecNorm (next - horner16Step H v cur deg) ≤ ε) :
    vecNorm (next - horner16Step H v ideal deg) ≤ ε + ((3 / 2 : ℝ) / (deg : ℝ)) * E := by
  have hd_pos : (0 : ℝ) < (deg : ℝ) := by exact_mod_cast (show 0 < deg by omega)
  have hsplit : next - horner16Step H v ideal deg =
      (next - horner16Step H v cur deg) + (1 / (deg : ℝ)) • (H *ᵥ (cur - ideal)) := by
    dsimp only [horner16Step]; rw [Matrix.mulVec_sub]; ext idx
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hsplit]
  refine (vecNorm_add_le _ _).trans ?_
  rw [vecNorm_smul, abs_of_nonneg (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left
    ((hH _).trans (mul_le_mul_of_nonneg_left hcur (by norm_num)))
    (by positivity : 0 ≤ 1 / (deg : ℝ))
  exact (add_le_add hnext h2).trans_eq (by ring)

theorem vecNorm_horner16_round_le {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : ∀ u, vecNorm (H *ᵥ u) ≤ (3 / 2) * vecNorm u) {v : Fin d → ℝ} {seq : ℕ → Fin d → ℝ}
    {ε : ℝ} (hε : 0 ≤ ε) (h0 : seq 0 = v)
    (hstep : ∀ k < 16, vecNorm (seq (k + 1) - horner16Step H v (seq k) (16 - k)) ≤ ε) :
    vecNorm (seq 16 - taylor16OfMat H *ᵥ v) ≤ (9 / 2) * ε := by
  rw [← horner16Ideal_sixteen_eq H v]
  have e0 : vecNorm (seq 0 - horner16Ideal H v 0) ≤ 0 := by simp [h0, horner16Ideal, vecNorm_zero]
  have step_at (k : ℕ) (hk : k < 16) {E : ℝ} (hE : vecNorm (seq k - horner16Ideal H v k) ≤ E) :
      vecNorm (seq (k + 1) - horner16Ideal H v (k + 1)) ≤
        ε + ((3 / 2 : ℝ) / ((16 - k : ℕ) : ℝ)) * E :=
    vecNorm_horner16Step_approx hH (by omega) hE (hstep k hk)
  have e1 := step_at 0 (by omega) e0; have e2 := step_at 1 (by omega) e1
  have e3 := step_at 2 (by omega) e2; have e4 := step_at 3 (by omega) e3
  have e5 := step_at 4 (by omega) e4; have e6 := step_at 5 (by omega) e5
  have e7 := step_at 6 (by omega) e6; have e8 := step_at 7 (by omega) e7
  have e9 := step_at 8 (by omega) e8; have e10 := step_at 9 (by omega) e9
  have e11 := step_at 10 (by omega) e10; have e12 := step_at 11 (by omega) e11
  have e13 := step_at 12 (by omega) e12; have e14 := step_at 13 (by omega) e13
  have e15 := step_at 14 (by omega) e14; have e16 := step_at 15 (by omega) e15
  norm_num at e16; linarith

/- ## Section 4: Tridiagonal Causal Window & Truncated-Band Substep Bound -/

/-- Truncated skew-symmetric tridiagonal matrix retaining couplings `w < dCap` and zeroing
  `w ≥ dCap`. -/
def tridiagCapMat (d dCap : ℕ) (γ : ℕ → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  tridiagSkewMat d (fun w ↦ if w < dCap then γ w else 0)

theorem tridiagSkewMat_mulVec_zero_of_ge {d L : ℕ} {γ : ℕ → ℝ} {v : Fin (d + 1) → ℝ}
    (hv : ∀ j : Fin (d + 1), L ≤ j.1 → v j = 0) :
    ∀ j : Fin (d + 1), L + 1 ≤ j.1 → (tridiagSkewMat d γ *ᵥ v) j = 0 := by
  intro j hj
  rw [tridiagSkewMat_mulVec_apply, dite_eq_left (by omega : 0 < j.1),
    hv ⟨j.1 - 1, by omega⟩ (by dsimp; omega), mul_zero, zero_add]
  by_cases hlt : j.1 < d
  · rw [dite_eq_left hlt, hv ⟨j.1 + 1, by omega⟩ (by dsimp; omega), mul_zero]
  · rw [dite_eq_right hlt]

theorem tridiagSkewMat_pow_mulVec_zero_of_ge {d : ℕ} (γ : ℕ → ℝ) :
    ∀ (k L : ℕ) (v : Fin (d + 1) → ℝ), (∀ j : Fin (d + 1), L ≤ j.1 → v j = 0) →
      ∀ j : Fin (d + 1), L + k ≤ j.1 → (((tridiagSkewMat d γ) ^ k) *ᵥ v) j = 0
  | 0, _, v, hv, j, hj => by simpa using hv j hj
  | k + 1, L, v, hv, j, hj => by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact tridiagSkewMat_mulVec_zero_of_ge
      (tridiagSkewMat_pow_mulVec_zero_of_ge γ k L v hv) j (by omega)

theorem taylor16Mat_tridiag_mulVec_zero_of_ge {d L : ℕ} (t : ℝ) (γ : ℕ → ℝ)
    {v : Fin (d + 1) → ℝ} (hv : ∀ j : Fin (d + 1), L ≤ j.1 → v j = 0) :
    ∀ j : Fin (d + 1), L + 16 ≤ j.1 → (taylor16Mat t (tridiagSkewMat d γ) *ᵥ v) j = 0 := by
  intro j hj
  rw [taylor16Mat, taylor16OfMat_mulVec_eq_sum]
  refine sumUpTo_apply_zero _ j 17 fun k hk ↦ ?_
  rw [Pi.smul_apply, smul_pow, Matrix.smul_mulVec, Pi.smul_apply,
    tridiagSkewMat_pow_mulVec_zero_of_ge γ k L v hv j (by omega), smul_zero, smul_zero]

theorem tridiagCapMat_mulVec_zero_above {d dCap : ℕ} (γ : ℕ → ℝ) {v : Fin (d + 1) → ℝ}
    (hv : ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → v j = 0) :
    ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → (tridiagCapMat d dCap γ *ᵥ v) j = 0 := by
  intro j hj
  unfold tridiagCapMat
  rw [tridiagSkewMat_mulVec_apply, dite_eq_left (by omega : 0 < j.1),
    ite_eq_right (by omega : ¬(j.1 - 1 < dCap)), zero_mul, zero_add]
  by_cases hlt : j.1 < d
  · rw [dite_eq_left hlt, hv ⟨j.1 + 1, by omega⟩ (by dsimp; omega), mul_zero]
  · rw [dite_eq_right hlt]

theorem tridiagCapMat_pow_mulVec_zero_above {d dCap : ℕ} (γ : ℕ → ℝ) :
    ∀ (k : ℕ) {v : Fin (d + 1) → ℝ}, (∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → v j = 0) →
      ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → (((tridiagCapMat d dCap γ) ^ k) *ᵥ v) j = 0
  | 0, _, hv, j, hj => by simpa using hv j hj
  | k + 1, _, hv, j, hj => by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact tridiagCapMat_mulVec_zero_above γ (tridiagCapMat_pow_mulVec_zero_above γ k hv) j hj

theorem taylor16Mat_cap_mulVec_zero_above {d dCap : ℕ} (t : ℝ) (γ : ℕ → ℝ)
    {v : Fin (d + 1) → ℝ} (hv : ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → v j = 0) :
    ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → (taylor16Mat t (tridiagCapMat d dCap γ) *ᵥ v) j = 0 := by
  intro j hj
  rw [taylor16Mat, taylor16OfMat_mulVec_eq_sum]
  refine sumUpTo_apply_zero _ j 17 fun k _ ↦ ?_
  rw [Pi.smul_apply, smul_pow, Matrix.smul_mulVec, Pi.smul_apply,
    tridiagCapMat_pow_mulVec_zero_above γ k hv j hj, smul_zero, smul_zero]

theorem taylor16Mat_cap_pow_mulVec_zero_above {d dCap : ℕ} (t : ℝ) (γ : ℕ → ℝ) :
    ∀ (q : ℕ) {v : Fin (d + 1) → ℝ}, (∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → v j = 0) →
      ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 →
        (((taylor16Mat t (tridiagCapMat d dCap γ)) ^ q) *ᵥ v) j = 0
  | 0, _, hv, j, hj => by simpa using hv j hj
  | q + 1, _, hv, j, hj => by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact taylor16Mat_cap_mulVec_zero_above t γ
      (taylor16Mat_cap_pow_mulVec_zero_above t γ q hv) j hj

theorem vecNorm_tridiag_sub_cap_mulVec_le {d dCap : ℕ} (hdCap : dCap < d) (γ : ℕ → ℝ)
    {z : Fin (d + 1) → ℝ} (hz : ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → z j = 0) :
    vecNorm ((tridiagSkewMat d γ - tridiagCapMat d dCap γ) *ᵥ z) ≤
      |γ dCap| * |z ⟨dCap, by omega⟩| := by
  have hdiff : tridiagSkewMat d γ - tridiagCapMat d dCap γ =
      tridiagSkewMat d (fun w ↦ if w < dCap then 0 else γ w) := by
    unfold tridiagCapMat
    have h := tridiagSkewMat_smul_sub d 1 γ (fun w ↦ if w < dCap then γ w else 0)
    rw [one_smul] at h; rw [h]; congr 1; ext w
    by_cases hw : w < dCap
    · rw [ite_eq_left hw, ite_eq_left hw]; ring
    · rw [ite_eq_right hw, ite_eq_right hw]; ring
  rw [hdiff]
  let idx1 : Fin (d + 1) := ⟨dCap + 1, by omega⟩
  have hzero (j : Fin (d + 1)) (hne : j ≠ idx1) :
      (tridiagSkewMat d (fun w ↦ if w < dCap then 0 else γ w) *ᵥ z) j = 0 := by
    have hj_ne : j.1 ≠ dCap + 1 := fun heq ↦ hne (Fin.ext heq)
    rw [tridiagSkewMat_mulVec_apply]
    have hleft : (if ha : 0 < j.1 then
        (if j.1 - 1 < dCap then 0 else γ (j.1 - 1)) * z ⟨j.1 - 1, by omega⟩ else 0) = 0 := by
      by_cases h0 : 0 < j.1
      · rw [dite_eq_left h0]
        by_cases hlt : j.1 - 1 < dCap
        · rw [ite_eq_left hlt, zero_mul]
        · rw [hz ⟨j.1 - 1, by omega⟩ (by dsimp [idx1] at hj_ne ⊢; omega), mul_zero]
      · rw [dite_eq_right h0]
    have hright : (if ha : j.1 < d then
        -(if j.1 < dCap then 0 else γ j.1) * z ⟨j.1 + 1, by omega⟩ else 0) = 0 := by
      by_cases hlt : j.1 < d
      · rw [dite_eq_left hlt]
        by_cases hc : j.1 < dCap
        · rw [ite_eq_left hc, neg_zero, zero_mul]
        · rw [hz ⟨j.1 + 1, by omega⟩ (by dsimp; omega), mul_zero]
      · rw [dite_eq_right hlt]
    rw [hleft, hright, add_zero]
  have hat : (tridiagSkewMat d (fun w ↦ if w < dCap then 0 else γ w) *ᵥ z) idx1 =
      γ dCap * z ⟨dCap, by omega⟩ := by
    rw [tridiagSkewMat_mulVec_apply, dite_eq_left (by dsimp [idx1]; omega),
      ite_eq_right (by dsimp [idx1]; omega)]
    have hright : (if ha : idx1.1 < d then
        -(if idx1.1 < dCap then 0 else γ idx1.1) * z ⟨idx1.1 + 1, by omega⟩ else 0) = 0 := by
      by_cases hlt : idx1.1 < d
      · rw [dite_eq_left hlt, hz ⟨idx1.1 + 1, by omega⟩ (by dsimp [idx1]; omega), mul_zero]
      · rw [dite_eq_right hlt]
    rw [hright, add_zero]
    have hsub : idx1.1 - 1 = dCap := rfl
    have harg2 : z ⟨idx1.1 - 1, by omega⟩ = z ⟨dCap, by omega⟩ := congrArg z (Fin.ext hsub)
    rw [congrArg γ hsub, harg2]
  rw [vecNorm, Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩; unfold vecSqNorm
  rw [Finset.sum_eq_single idx1]
  · exact le_of_eq (by rw [hat, mul_pow, mul_pow, sq_abs, sq_abs])
  · intro j _ hne; rw [hzero j hne, zero_pow (by omega)]
  · intro hmem; exact absurd (Finset.mem_univ idx1) hmem

private lemma pow_anti_le_one {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a b : ℕ) :
    c ^ (a + b) ≤ c ^ a := by
  rw [pow_add]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hc0 hc1) (pow_nonneg hc0 a)).trans_eq (mul_one _)

theorem vecNorm_taylor16OfMat_sub_linear_le {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hX : ∀ u, vecNorm (X *ᵥ u) ≤ c * vecNorm u) (v : Fin d → ℝ) :
    vecNorm ((taylor16OfMat X - (1 + X)) *ᵥ v) ≤ c ^ 2 * vecNorm v := by
  have hexp : (taylor16OfMat X - (1 + X)) *ᵥ v =
      sumUpTo (fun j ↦ factInv (j + 2) • ((X ^ (j + 2)) *ᵥ v)) 15 := by
    rw [Matrix.sub_mulVec, taylor16OfMat_mulVec_eq_sum]
    dsimp only [sumUpTo, factInv]; ext idx
    simp only [pow_zero, pow_one, Matrix.add_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hexp]
  have hsum := vecNorm_sumUpTo_smul_le (fun j ↦ factInv (j + 2)) (fun j ↦ factInv (j + 2))
    (fun j ↦ (X ^ (j + 2)) *ᵥ v) (c ^ 2 * vecNorm v) 15 (fun _ _ ↦ factInv_nonneg _) fun j _ ↦ by
      have hp : c ^ (j + 2) ≤ c ^ 2 := by rw [Nat.add_comm]; exact pow_anti_le_one hc0 hc1 2 j
      exact mul_le_mul_of_nonneg_left
        ((vecNorm_pow_mulVec_le hc0 hX (j + 2) v).trans
          (mul_le_mul_of_nonneg_right hp (vecNorm_nonneg v))) (factInv_nonneg _)
  have hcoef : sumUpTo (fun j ↦ factInv (j + 2)) 15 ≤ 1 := by
    dsimp only [sumUpTo, factInv]; norm_num
  exact hsum.trans
    ((mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sq_nonneg c) (vecNorm_nonneg v))).trans_eq
      (one_mul _))

theorem vecNorm_pow_sub_pow_sum_le {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, vecNorm (A *ᵥ x) ≤ vecNorm x) :
    ∀ (q : ℕ) (v : Fin d → ℝ),
      vecNorm (((A ^ q) - (B ^ q)) *ᵥ v) ≤ ∑ t ∈ Finset.range q, vecNorm ((A - B) *ᵥ ((B ^ t) *ᵥ v))
  | 0, _ => by simp [vecNorm_zero]
  | q + 1, v => by
    have hsplit : ((A ^ (q + 1)) - (B ^ (q + 1))) *ᵥ v =
        A *ᵥ (((A ^ q) - (B ^ q)) *ᵥ v) + (A - B) *ᵥ ((B ^ q) *ᵥ v) := by
      rw [pow_succ', pow_succ', Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      ext idx; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [hsplit, Finset.sum_range_succ]
    exact (vecNorm_add_le _ _).trans
      (add_le_add ((hA _).trans (vecNorm_pow_sub_pow_sum_le hA q v)) le_rfl)

private lemma eighteen_mul_pow17_le_sub_pow18 {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    18 * δ * a ^ 17 ≤ (a + δ) ^ 18 - a ^ 18 := by
  have hid : (a + δ) ^ 18 - a ^ 18 - 18 * δ * a ^ 17 =
      153 * (a ^ 16 * δ ^ 2 + a ^ 2 * δ ^ 16) + 816 * (a ^ 15 * δ ^ 3 + a ^ 3 * δ ^ 15) +
        3060 * (a ^ 14 * δ ^ 4 + a ^ 4 * δ ^ 14) + 8568 * (a ^ 13 * δ ^ 5 + a ^ 5 * δ ^ 13) +
        18564 * (a ^ 12 * δ ^ 6 + a ^ 6 * δ ^ 12) + 31824 * (a ^ 11 * δ ^ 7 + a ^ 7 * δ ^ 11) +
        43758 * (a ^ 10 * δ ^ 8 + a ^ 8 * δ ^ 10) + 48620 * a ^ 9 * δ ^ 9 +
        18 * a * δ ^ 17 + δ ^ 18 := by ring
  have hpos : 0 ≤ (a + δ) ^ 18 - a ^ 18 - 18 * δ * a ^ 17 := by
    rw [hid]; positivity
  linarith

private lemma sum_range_pow17_le (c : ℝ) (hc : 0 ≤ c) :
    ∀ q : ℕ, ∑ t ∈ Finset.range q, c * ((t : ℝ) * c) ^ 17 ≤ ((q : ℝ) * c) ^ 18 / 18
  | 0 => by simp
  | q + 1 => by
    rw [Finset.sum_range_succ]
    have hih := sum_range_pow17_le c hc q
    have hstep := eighteen_mul_pow17_le_sub_pow18 (mul_nonneg (Nat.cast_nonneg q) hc) hc
    rw [show (q : ℝ) * c + c = ((q + 1 : ℕ) : ℝ) * c by push_cast; ring] at hstep
    linarith

theorem vecNorm_taylor16Mat_cap_substep_le {d dCap : ℕ} (hd48 : 48 ≤ dCap) (hdlt : dCap < d)
    {η B_cap B_full : ℝ} {γ : ℕ → ℝ} (hη : 0 ≤ η) (hBc0 : 0 ≤ B_cap) (hBf0 : 0 ≤ B_full)
    (hG_full : ∀ u, vecNorm (tridiagSkewMat d γ *ᵥ u) ≤ B_full * vecNorm u) (hηBf : η * B_full ≤ 1)
    (hγ_cap : ∀ w < dCap, |γ w| ≤ (1 / 2) * B_cap) (hγ_at : |γ dCap| ≤ (3 / 4) * B_cap)
    (hηBc1 : η * B_cap ≤ 1) {q : ℕ} (hq : (q : ℝ) * η * B_cap ≤ 3 / 2)
    {v : Fin (d + 1) → ℝ} (hv : ∀ j : Fin (d + 1), dCap - 32 ≤ j.1 → v j = 0) :
    vecNorm (((taylor16Mat η (tridiagSkewMat d γ)) ^ q -
        taylor16Mat ((q : ℝ) * η) (tridiagCapMat d dCap γ)) *ᵥ v) ≤
      (((q : ℝ) * η * B_cap) ^ 17 / 300000000000000 +
        ((q : ℝ) * η * B_cap) ^ 18 / 7200000000000000 +
        (q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) * vecNorm v := by
  let G := tridiagSkewMat d γ
  let Gc := tridiagCapMat d dCap γ
  have hG_skew : Gᵀ = -G := tridiagSkewMat_transpose d γ
  have hGc_skew : Gcᵀ = -Gc := tridiagSkewMat_transpose d _
  have hGc_op : ∀ u, vecNorm (Gc *ᵥ u) ≤ B_cap * vecNorm u := by
    intro u
    have hb : ∀ w < d, |(if w < dCap then γ w else 0)| ≤ (1 / 2) * B_cap := by
      intro w _
      by_cases hw : w < dCap
      · rw [ite_eq_left hw]; exact hγ_cap w hw
      · rw [ite_eq_right hw, abs_zero]; linarith
    simpa [Gc, tridiagCapMat, ← mul_assoc] using vecNorm_tridiagSkewMat_mulVec_le (by linarith) hb u
  have hA_contr (u : Fin (d + 1) → ℝ) : vecNorm (taylor16Mat η G *ᵥ u) ≤ vecNorm u :=
    vecNorm_taylor16Mat_mulVec_le hG_skew hη hBf0 hG_full (by linarith) u
  have hB_contr (u : Fin (d + 1) → ℝ) : vecNorm (taylor16Mat η Gc *ᵥ u) ≤ vecNorm u :=
    vecNorm_taylor16Mat_mulVec_le hGc_skew hη hBc0 hGc_op (by linarith) u
  have hcap_sub := vecNorm_taylor16Mat_substep_le hGc_skew hη hBc0 hGc_op q hq v
  let z : ℕ → Fin (d + 1) → ℝ := fun t ↦ ((taylor16Mat η Gc) ^ t) *ᵥ v
  have hz_norm (t : ℕ) : vecNorm (z t) ≤ vecNorm v := by
    simpa [z] using vecNorm_pow_mulVec_le zero_le_one (fun u ↦ by simpa using hB_contr u) t v
  have hz_above (t : ℕ) : ∀ j : Fin (d + 1), dCap + 1 ≤ j.1 → (z t) j = 0 :=
    taylor16Mat_cap_pow_mulVec_zero_above η γ t fun j hj ↦ hv j (by omega)
  let stepMaj (t : ℕ) : ℝ :=
    ((η * B_cap) * (((t : ℝ) * (η * B_cap)) ^ 17) / 400000000000000 +
      ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) * vecNorm v
  have hterm_le (t : ℕ) (ht : t < q) :
      vecNorm ((taylor16Mat η G - taylor16Mat η Gc) *ᵥ z t) ≤ stepMaj t := by
    have ht_le : (t : ℝ) * η * B_cap ≤ 3 / 2 := by
      have h1 : (t : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.le_of_lt ht)
      linarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hη hBc0)]
    have hzt_approx := vecNorm_taylor16Mat_substep_le hGc_skew hη hBc0 hGc_op t ht_le v
    have hpoly_zero : (taylor16Mat ((t : ℝ) * η) Gc *ᵥ v) ⟨dCap, by omega⟩ = 0 :=
      taylor16Mat_tridiag_mulVec_zero_of_ge ((t : ℝ) * η) _ hv ⟨dCap, by omega⟩ (by dsimp; omega)
    have hzt_at :
        |(z t) ⟨dCap, by omega⟩| ≤ ((t : ℝ) * η * B_cap) ^ 17 / 300000000000000 * vecNorm v := by
      rw [show (z t) ⟨dCap, by omega⟩ = (((taylor16Mat η Gc) ^ t -
          taylor16Mat ((t : ℝ) * η) Gc) *ᵥ v) ⟨dCap, by omega⟩ by
        simp [z, Matrix.sub_mulVec, hpoly_zero]]
      exact (abs_apply_le_vecNorm _ _).trans hzt_approx
    have hlin_bd : vecNorm ((η • (G - Gc)) *ᵥ z t) ≤
        (η * B_cap) * (((t : ℝ) * (η * B_cap)) ^ 17) / 400000000000000 * vecNorm v := by
      rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg hη]
      exact ((mul_le_mul_of_nonneg_left (vecNorm_tridiag_sub_cap_mulVec_le hdlt γ (hz_above t))
        hη).trans (mul_le_mul_of_nonneg_left (mul_le_mul hγ_at hzt_at (abs_nonneg _) (by linarith))
        hη)).trans_eq (by ring)
    have htail1 := (vecNorm_taylor16OfMat_sub_linear_le (mul_nonneg hη hBf0) hηBf
      (vecNorm_smul_mulVec_le hη hG_full) (z t)).trans
      (mul_le_mul_of_nonneg_left (hz_norm t) (sq_nonneg _))
    have htail2 := (vecNorm_taylor16OfMat_sub_linear_le (mul_nonneg hη hBc0) hηBc1
      (vecNorm_smul_mulVec_le hη hGc_op) (z t)).trans
      (mul_le_mul_of_nonneg_left (hz_norm t) (sq_nonneg _))
    have hdecomp : (taylor16Mat η G - taylor16Mat η Gc) *ᵥ z t =
        (η • (G - Gc)) *ᵥ z t + ((taylor16OfMat (η • G) - (1 + η • G)) *ᵥ z t -
          (taylor16OfMat (η • Gc) - (1 + η • Gc)) *ᵥ z t) := by
      dsimp only [taylor16Mat]
      ext idx
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdecomp]
    refine (vecNorm_add_le _ _).trans ?_
    have hsub := vecNorm_sub_le ((taylor16OfMat (η • G) - (1 + η • G)) *ᵥ z t)
      ((taylor16OfMat (η • Gc) - (1 + η • Gc)) *ᵥ z t)
    dsimp only [stepMaj]
    linarith
  have hsum_diff : vecNorm (((taylor16Mat η G) ^ q - (taylor16Mat η Gc) ^ q) *ᵥ v) ≤
      (((q : ℝ) * η * B_cap) ^ 18 / 7200000000000000 +
        (q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) * vecNorm v := by
    have h1 := (vecNorm_pow_sub_pow_sum_le (B := taylor16Mat η Gc) hA_contr q v).trans
      (Finset.sum_le_sum fun t ht ↦ hterm_le t (Finset.mem_range.mp ht))
    have hsum_eval : ∑ t ∈ Finset.range q, stepMaj t =
        ((1 / 400000000000000 : ℝ) *
          (∑ t ∈ Finset.range q, (η * B_cap) * (((t : ℝ) * (η * B_cap)) ^ 17)) +
          (q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) * vecNorm v := by
      dsimp only [stepMaj]
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      congr 1
      simp_rw [div_eq_inv_mul, ← Finset.mul_sum]
      norm_num
    have h18 := (mul_le_mul_of_nonneg_left (sum_range_pow17_le (η * B_cap) (mul_nonneg hη hBc0) q)
      (by norm_num : (0 : ℝ) ≤ 1 / 400000000000000)).trans_eq (by ring :
        (1 / 400000000000000 : ℝ) * (((q : ℝ) * (η * B_cap)) ^ 18 / 18) =
          ((q : ℝ) * η * B_cap) ^ 18 / 7200000000000000)
    rw [hsum_eval] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (add_le_add h18 le_rfl) (vecNorm_nonneg v))
  have hsplit_main : ((taylor16Mat η G) ^ q - taylor16Mat ((q : ℝ) * η) Gc) *ᵥ v =
      ((taylor16Mat η G) ^ q - (taylor16Mat η Gc) ^ q) *ᵥ v +
        ((taylor16Mat η Gc) ^ q - taylor16Mat ((q : ℝ) * η) Gc) *ᵥ v := by
    rw [← Matrix.add_mulVec, sub_add_sub_cancel]
  rw [hsplit_main]
  exact (vecNorm_add_le _ _).trans (by linarith)

/- ## Section 5: `taylor8Mat ^ K` vs `taylor16Mat ^ K` Trajectory Bridge -/

theorem vecNorm_taylor8_sub_taylor16_pow_le {n m r K : ℕ} (hn : 80000 ≤ n) (_hm1 : 1 ≤ m)
    (hm : m ≤ 8192) (_hr1 : 1 ≤ r) (hr : r ≤ 1024) (hK : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ)) :
    let e0 : Fin (orbDim m r) → ℝ := Pi.single ⟨0, by unfold orbDim; omega⟩ 1
    vecNorm (((taylor8Mat (1 / √(2 ^ n : ℝ)) (dAltGenMat m r)) ^ K) *ᵥ e0 -
      ((taylor16Mat (1 / √(2 ^ n : ℝ)) (dAltGenMat m r)) ^ K) *ᵥ e0) ≤ 1 / (wdScale : ℝ) := by
  intro e0
  set η : ℝ := 1 / √(2 ^ n : ℝ)
  set G := dAltGenMat m r
  set B8 := taylor8Mat η G
  set B16 := taylor16Mat η G
  have hN_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have hsN_pos : 0 < √(2 ^ n : ℝ) := Real.sqrt_pos.mpr hN_pos
  have hG_bound : ∀ u, vecNorm (G *ᵥ u) ≤ (2 : ℝ) ^ 19 * vecNorm u := by
    intro u
    have hbd : dAltGenNormBound m r ≤ (2 : ℝ) ^ 19 := by
      unfold dAltGenNormBound
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [← pow_mul]
      have hmin : min m r ≤ 1024 := le_trans (Nat.min_le_right m r) hr
      have hmax : max m r ≤ 8192 := max_le hm (le_trans hr (by omega))
      exact_mod_cast (Nat.mul_le_mul (Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left (by omega) 2)) hmax).trans (by norm_num : 4 * 1025 ^ 2 * 8192 ≤ 2 ^ 38)
    exact (vecNorm_dAltGenMat_mulVec_le m r u).trans
      (mul_le_mul_of_nonneg_right hbd (vecNorm_nonneg u))
  have hηB_le1 : η * (2 : ℝ) ^ 19 ≤ 1 := by
    dsimp only [η]
    rw [one_div_mul_eq_div, div_le_one hsN_pos, Real.le_sqrt (by positivity) hN_pos.le, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hB8_contr : ∀ x, vecNorm (B8 *ᵥ x) ≤ vecNorm x := fun x ↦
    vecNorm_taylor8Mat_mulVec_le (dAltGenMat_transpose m r) (by positivity) (by positivity)
      hG_bound hηB_le1 x
  have hB16_contr : ∀ x, vecNorm (B16 *ᵥ x) ≤ vecNorm x := fun x ↦
    vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose m r) (by positivity) (by positivity)
      hG_bound (by linarith) x
  have hdiff_op : ∀ x, vecNorm ((B8 - B16) *ᵥ x) ≤ ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x := by
    intro x
    set X := η • G
    have hX_op := vecNorm_smul_mulVec_le (by positivity : 0 ≤ η) hG_bound
    have hc_sq : (η * (2 : ℝ) ^ 19) ^ 2 = (2 : ℝ) ^ 38 / (2 ^ n : ℝ) := by
      dsimp only [η]
      rw [one_div_mul_eq_div, div_pow, Real.sq_sqrt hN_pos.le, ← pow_mul]
    have hexp : (B8 - B16) *ᵥ x =
        -(sumUpTo (fun j ↦ factInv (j + 9) • ((X ^ (j + 9)) *ᵥ x)) 8) := by
      dsimp only [B8, B16, X, taylor8Mat, taylor16Mat]
      rw [Matrix.sub_mulVec, taylor16OfMat_mulVec_eq_sum]
      dsimp only [sumUpTo, factInv, taylor8OfMat]
      ext idx
      simp only [pow_zero, pow_one, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.sub_apply, Pi.neg_apply, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hexp, vecNorm_neg]
    have hsum := vecNorm_sumUpTo_smul_le (fun j ↦ factInv (j + 9)) (fun j ↦ factInv (j + 9))
      (fun j ↦ (X ^ (j + 9)) *ᵥ x) (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) 8
      (fun _ _ ↦ factInv_nonneg _) fun j _ ↦ by
        have h2 : (η * (2 : ℝ) ^ 19) ^ (j + 9) ≤ (2 : ℝ) ^ 38 / (2 ^ n : ℝ) := by
          rw [← hc_sq, show j + 9 = 2 + (j + 7) by omega]
          exact pow_anti_le_one (by positivity) hηB_le1 2 (j + 7)
        exact mul_le_mul_of_nonneg_left
          ((vecNorm_pow_mulVec_le (by positivity) hX_op (j + 9) x).trans
            (mul_le_mul_of_nonneg_right h2 (vecNorm_nonneg x))) (factInv_nonneg _)
    have hcoef : sumUpTo (fun j ↦ factInv (j + 9)) 8 ≤ 1 := by
      dsimp only [sumUpTo, factInv]
      norm_num
    exact hsum.trans ((mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (by positivity) (vecNorm_nonneg x))).trans_eq (one_mul _))
  have htel := vecNorm_pow_mulVec_sub_le hB8_contr hB16_contr
    (by positivity : 0 ≤ (2 : ℝ) ^ 38 / (2 ^ n : ℝ)) hdiff_op K e0 e0
  have he0_norm : vecNorm e0 = 1 := by
    unfold vecNorm vecSqNorm
    let z0 : Fin (orbDim m r) := ⟨0, by unfold orbDim; omega⟩
    rw [show e0 = Pi.single z0 1 from rfl, Finset.sum_eq_single z0]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hz
      exact absurd (Finset.mem_univ z0) hz
  rw [sub_self, vecNorm_zero, zero_add, he0_norm, mul_one] at htel
  have h1 : (K : ℝ) * ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) ≤
      (4 * √(2 ^ n : ℝ)) * ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  have hwd : (wdScale : ℝ) ≤ (2 : ℝ) ^ 50 := by unfold wdScale; norm_num
  have hwd_pos : (0 : ℝ) < (wdScale : ℝ) := by unfold wdScale; positivity
  have hsq_key : (4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 38 * (wdScale : ℝ)) ^ 2 ≤ ((2 ^ n : ℝ)) ^ 2 := by
    have hsq_lhs : (4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 38 * (wdScale : ℝ)) ^ 2 =
        (16 * (wdScale : ℝ) ^ 2 * (2 : ℝ) ^ 76) * (2 ^ n : ℝ) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hN_pos.le, ← pow_mul]; ring
    have hw2 : 16 * (wdScale : ℝ) ^ 2 ≤ (2 : ℝ) ^ 104 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hwd 2) (by norm_num)).trans_eq
        (by norm_num)
    have hcoeff_le : 16 * (wdScale : ℝ) ^ 2 * (2 : ℝ) ^ 76 ≤ (2 ^ n : ℝ) :=
      (mul_le_mul_of_nonneg_right hw2 (by positivity)).trans
        ((by rw [← pow_add] : (2 : ℝ) ^ 104 * (2 : ℝ) ^ 76 = (2 : ℝ) ^ 180).trans_le
          (pow_le_pow_right₀ (by norm_num) (by omega)))
    rw [hsq_lhs, sq (2 ^ n : ℝ)]
    exact mul_le_mul_of_nonneg_right hcoeff_le hN_pos.le
  have hkey : 4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 38 * (wdScale : ℝ) ≤ (2 ^ n : ℝ) := by
    nlinarith [sq_nonneg ((2 ^ n : ℝ) - 4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 38 * (wdScale : ℝ)),
      (by positivity : 0 ≤ 4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 38 * (wdScale : ℝ)), hN_pos]
  have h2 : (4 * √(2 ^ n : ℝ)) * ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) ≤ 1 / (wdScale : ℝ) := by
    rw [show (4 * √(2 ^ n : ℝ)) * ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) =
        (4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 38) / (2 ^ n : ℝ) by ring,
      div_le_div_iff₀ hN_pos hwd_pos, one_mul]
    exact hkey
  exact htel.trans (h1.trans h2)

open Real
open scoped Matrix NNRat NNReal ENNReal
/- ## Section 1: WHNF-Safe `T_16` Sliding-Window Kernel Evaluators -/
namespace HighDForce


end HighDForce

/-- Ceiling product `⌈a * b / 10 ^ 15⌉` with constant-first `Nat.add` for symbolic WHNF
  safety. -/
def highdMulCeil15 (a b : ℕ) : ℕ := Nat.div (Nat.add 999999999999999 (Nat.mul a b)) wdScale
/-- Iterated ceiling-product loop used by `altPow17Ceil15`. -/
def highdPowCeilLoop : ℕ → ℕ → ℕ → ℕ
  | 0, acc, _ => acc
  | k + 1, acc, x => highdPowCeilLoop k (highdMulCeil15 acc x) x


/-- Primitive truncating division `Int.tdiv x (Int.ofNat dNat)` (`0` closures). -/
def highdIntTdivNat (x : ℤ) (dNat : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => primOfNatForced (Nat.div m dNat)
  | Int.negSucc m => primNegOfNat (Nat.div (Nat.add m 1) dNat)
/-- Structural `O(outLen)` sliding-window Horner stage (`rem` first after `:`, `0`
  `Acc.rec`). -/
def hornerSlideLoopAux (dNat : ℕ) : ℕ → ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | 0, _, _, _, _ => []
  | rem + 1, prev, hb, vec, cur =>
    let vHead := match vec with | v :: _ => v | [] => Int.ofNat 0
    let vTail := match vec with | _ :: vt => vt | [] => []
    let c0 := match cur with | c :: _ => c | [] => Int.ofNat 0
    let c1 := match cur with | _ :: cn :: _ => cn | _ => Int.ofNat 0
    let cTail := match cur with | _ :: ct => ct | [] => []
    match hb with
    | b :: hbRest =>
      let right := primIntMul b c1
      let nextPrev := primIntMul b c0
      highdStrictConsInt (primIntAdd vHead (highdIntTdivNat (primIntSub prev right) dNat))
        (hornerSlideLoopAux dNat rem nextPrev hbRest vTail cTail)
    | [] =>
      highdStrictConsInt (primIntAdd vHead (highdIntTdivNat prev dNat))
        (hornerSlideLoopAux dNat rem (Int.ofNat 0) [] vTail cTail)
/-- Single-pass `O(outLen)` sliding-window Horner stage computing
  `vec[w] + Int.tdiv (left - right) (Int.ofNat dNat)` with primitive `Nat.*` arithmetic. -/
def hornerSlideLoop (dNat : ℕ) (prev : ℤ) (hb vec cur : List ℤ) (outLen : ℕ) : List ℤ :=
  hornerSlideLoopAux dNat outLen prev hb vec cur
/-- Degree-`deg` sliding-window `Int.tdiv` Horner stage of output length `outLen`. -/
def applyHgTdivSlide (deg outLen : ℕ) (hb vec cur : List ℤ) : List ℤ :=
  let dRaw := Nat.mul deg wdScale
  HighDForce.withForcedNat dRaw fun dNat =>
    hornerSlideLoop dNat (Int.ofNat 0) hb vec cur outLen
/-- Adaptive-length degree-`deg` Horner stage growing support up to `maxLen`. -/
def hornerStageSlide (deg maxLen : ℕ) (hb vec cur : List ℤ) : List ℤ :=
  let nxtRaw := highdNatMin maxLen (Nat.add (altIntLen cur) 1)
  HighDForce.withForcedNat nxtRaw fun nxtLen =>
    applyHgTdivSlide deg nxtLen hb vec cur
/-- Unrolled `16`-stage Horner step approximating `taylor16OfMat G_pt *ᵥ vec` on `List ℤ`. -/
def hornerT16SlideStep (maxLen : ℕ) (hb vec : List ℤ) : List ℤ :=
  let s15 := hornerStageSlide 16 maxLen hb vec vec
  HighDForce.withForcedList s15 fun c15 =>
  let s14 := hornerStageSlide 15 maxLen hb vec c15
  HighDForce.withForcedList s14 fun c14 =>
  let s13 := hornerStageSlide 14 maxLen hb vec c14
  HighDForce.withForcedList s13 fun c13 =>
  let s12 := hornerStageSlide 13 maxLen hb vec c13
  HighDForce.withForcedList s12 fun c12 =>
  let s11 := hornerStageSlide 12 maxLen hb vec c12
  HighDForce.withForcedList s11 fun c11 =>
  let s10 := hornerStageSlide 11 maxLen hb vec c11
  HighDForce.withForcedList s10 fun c10 =>
  let s9 := hornerStageSlide 10 maxLen hb vec c10
  HighDForce.withForcedList s9 fun c9 =>
  let s8 := hornerStageSlide 9 maxLen hb vec c9
  HighDForce.withForcedList s8 fun c8 =>
  let s7 := hornerStageSlide 8 maxLen hb vec c8
  HighDForce.withForcedList s7 fun c7 =>
  let s6 := hornerStageSlide 7 maxLen hb vec c7
  HighDForce.withForcedList s6 fun c6 =>
  let s5 := hornerStageSlide 6 maxLen hb vec c6
  HighDForce.withForcedList s5 fun c5 =>
  let s4 := hornerStageSlide 5 maxLen hb vec c5
  HighDForce.withForcedList s4 fun c4 =>
  let s3 := hornerStageSlide 4 maxLen hb vec c4
  HighDForce.withForcedList s3 fun c3 =>
  let s2 := hornerStageSlide 3 maxLen hb vec c3
  HighDForce.withForcedList s2 fun c2 =>
  let s1 := hornerStageSlide 2 maxLen hb vec c2
  HighDForce.withForcedList s1 fun c1 =>
  hornerStageSlide 1 maxLen hb vec c1
/-- Iterates `hornerT16SlideStep maxLen hb` across `nSub` full-band macro-steps. -/
def altIterFullT16 : ℕ → ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, _, vec => vec
  | k + 1, maxLen, hb, vec =>
    let stepVec := hornerT16SlideStep maxLen hb vec
    HighDForce.withForcedList stepVec fun vecNext =>
      altIterFullT16 k maxLen hb vecNext
/-- Primitive check that every `ℤ` entry of a list is identically `0`. -/
def altAllZeroInt : List ℤ → Bool
  | [] => true
  | z :: zs => cond (Nat.beq (primIntNatAbs z) 0) (altAllZeroInt zs) false
/-- Checks that every entry at index `≥ coreLen` of `xs` is identically `0` (`0` `Acc.rec`). -/
def altCheckDropZero : ℕ → List ℤ → Bool
  | 0, xs => altAllZeroInt xs
  | k + 1, xs =>
    match xs with
    | [] => true
    | _ :: rest => altCheckDropZero k rest
/-- Truncates `xs` to at most `coreLen` entries (`0` `Acc.rec`). -/
def altTakeMaxInt : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | k + 1, xs =>
    match xs with
    | [] => []
    | x :: rest => highdStrictConsInt x (altTakeMaxInt k rest)
/-- Iterates `hornerT16SlideStep (16 + coreLen) hb` across `nSub` causal-window macro-steps,
  returning `[]` immediately if any post-step entry at index `≥ coreLen` is nonzero. -/
def altIterCapT16 : ℕ → ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, _, vec => vec
  | k + 1, coreLen, hb, vec =>
    let stepVec := hornerT16SlideStep (Nat.add 16 coreLen) hb vec
    HighDForce.withForcedList stepVec fun cur =>
      cond (altCheckDropZero coreLen cur) (
          let trimmed := altTakeMaxInt coreLen cur
          HighDForce.withForcedList trimmed fun vecNext =>
            altIterCapT16 k coreLen hb vecNext)
        []



/-- Certified `10 ^ 15`-scaled upper bound on `(x / 10 ^ 15) ^ 17`. -/
def altPow17Ceil15 (x : ℕ) : ℕ := highdPowCeilLoop 16 x x
/-- Certified `10 ^ 12`-scaled hit-probability lower-bound prefix for `1`-stage
  `(D_{\text{alt}} Z_R)^K` using degree-`16` `Int.tdiv` Horner evaluation and causal window
  `dCap`. -/
def altEvalRowHighDLo12 (m r tau9 nSub dCap : ℕ) : List ℕ :=
  let dRaw := highdNatMin m r
  HighDForce.withForcedNat dRaw fun d =>
    cond (Bool.or (primNatBlt d 1) (Bool.or (primNatBlt dCap 1) (Bool.or (primNatBlt d dCap)
        (Bool.or (Bool.and (primNatBlt dCap d) (primNatBlt dCap 48))
        (Bool.or (primNatBlt r 2)
        (Bool.or (primNatBlt 8192 m)
        (Bool.or (primNatBlt 1024 r)
        (Bool.or (Nat.beq tau9 0)
        (Bool.or (primNatBlt 4000000000 tau9)
        (Bool.or (Nat.beq nSub 0) (primNatBlt 16384 nSub)))))))))))
      []
      (
        let hPtRaw := Nat.div (Nat.mul tau9 1000000) nSub
        HighDForce.withForcedNat hPtRaw fun hPt =>
          cond (primNatBlt hPt 1) [] (
              let maxBRaw := altMaxBHiFrom m r 0 dCap
              HighDForce.withForcedNat maxBRaw fun maxBHi15 =>
                let bCapHi15 := Nat.mul 2 maxBHi15
                let hgRaw := highdMulCeil15 (Nat.add 2 hPt) bCapHi15
                HighDForce.withForcedNat hgRaw fun hgHi15 =>
                  cond (Bool.or (primNatBlt 1500000000000000 hgHi15)
                      (Bool.not (altCheckHbTight m r 0 dCap)))
                    []
                    (
                      let hgPow := altPow17Ceil15 hgHi15
                      let truncPad15 :=
                        Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000
                      let bCapCeil := Nat.div (Nat.add 999999999999999 bCapHi15) wdScale
                      let roundPad15 :=
                        Nat.add 256 (Nat.mul nSub (Nat.add 256 (Nat.mul 10 bCapCeil)))
                      let padRaw := Nat.add truncPad15 roundPad15
                      HighDForce.withForcedNat padRaw fun totalPad15 =>
                        cond (Bool.or (primNatBlt 100000000000000 totalPad15)
                            (Nat.beq totalPad15 0))
                          []
                          (
                            let hbRaw := altBuildHbFrom m r hPt 0 dCap
                            HighDForce.withForcedList hbRaw fun hbPt =>
                              let vecInitRaw := highdStrictConsInt (Int.ofNat wdScale) []
                              HighDForce.withForcedList vecInitRaw fun vecInit =>
                                cond (Nat.beq dCap d) (
                                    let vecFinal := altIterFullT16 nSub (Nat.add d 1) hbPt vecInit
                                    let padded := altPadRightInts (Nat.add d 1) vecFinal
                                    match padded with
                                    | [] => []
                                    | _ :: tail => altVecTailToLo12 totalPad15 tail)
                                  (
                                    let coreRaw := Nat.sub dCap 32
                                    HighDForce.withForcedNat coreRaw fun coreLen =>
                                      let vecFinal := altIterCapT16 nSub coreLen hbPt vecInit
                                      match vecFinal with
                                      | [] => []
                                      | _ :: _ =>
                                        let padded := altPadRightInts coreLen vecFinal
                                        match padded with
                                        | [] => []
                                        | _ :: tail =>
                                          altVecTailToLo12 totalPad15 tail)))))
/-- Structural helper for `checkAltHighDBandLoop` (`vRem` first after `:`, `0` `Acc.rec`). -/
def checkAltHighDBandLoopAux (m : ℕ) : List ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], _, _, tauRem, nsubRem, dcapRem =>
    match tauRem with
    | [] =>
      match nsubRem with
      | [] =>
        match dcapRem with
        | [] => true
        | _ :: _ => false
      | _ :: _ => false
    | _ :: _ => false
  | vR :: vRest, r, vHist, tauRem, nsubRem, dcapRem =>
    match tauRem with
    | [] => false
    | tau9 :: tauRest =>
      match nsubRem with
      | [] => false
      | nSub :: nsubRest =>
        match dcapRem with
        | [] => false
        | dCap :: dcapRest =>
          cond (Bool.or (primNatBlt r 2) (primNatBlt 1024 r)) false (
              match vHist with
              | [] => false
              | vPrev :: _ =>
                cond (primNatBlt vR vPrev) false (
                    let stepOk :=
                      cond (Nat.beq tau9 0) (checkEigStep m r vR vPrev) (
                          let dRaw := highdNatMin m r
                          HighDForce.withForcedNat dRaw fun d =>
                            let rowRaw := altEvalRowHighDLo12 m r tau9 nSub dCap
                            HighDForce.withForcedList rowRaw fun rowLo12 =>
                              let rLen := altListLen rowLo12
                              cond (Bool.or (Nat.beq rLen 0) (Bool.or (primNatBlt d rLen)
                                    (Bool.or (Nat.beq (altSumNat rowLo12) 0)
                                      (primNatBlt (altListLen vHist) rLen))))
                                false
                                (
                                  let drift27 := altDriftSum27 vR rowLo12 vHist
                                  primNatBlt (Nat.mul tau9 1000000000000000000) drift27))
                    cond stepOk (checkAltHighDBandLoopAux m vRest (Nat.add r 1) (vR :: vHist)
                        tauRest nsubRest dcapRest)
                      false))
/-- Sub-band high-`d` Bellman drift checker over `r, r + 1,...` extending `vHist`. -/
def checkAltHighDBandLoop (m r : ℕ) (vHist vRem tauRem nsubRem dcapRem : List ℕ) : Bool :=
  checkAltHighDBandLoopAux m vRem r vHist tauRem nsubRem dcapRem
end
public section
open Real
open scoped Matrix NNRat NNReal ENNReal
/- ## Section 2: Primitive Bridge Lemmas & `Int.tdiv` Sliding-Window Horner Soundness -/
private theorem highd_cond_true {α : Type} (a b : α) : cond true a b = a := rfl
private theorem highd_cond_false {α : Type} (a b : α) : cond false a b = b := rfl
private theorem highd_1_le_of_altN0 {n : ℕ} (hn : altN0 ≤ n) : 1 ≤ n :=
  (by unfold altN0; norm_num : 1 ≤ altN0).trans hn
private theorem highd_15_le_of_altN0 {n : ℕ} (hn : altN0 ≤ n) : 15 ≤ n :=
  (by unfold altN0; norm_num : 15 ≤ altN0).trans hn
private theorem highd_200_le_of_altN0 {n : ℕ} (hn : altN0 ≤ n) : 200 ≤ n :=
  (by unfold altN0; norm_num : 200 ≤ altN0).trans hn
private theorem highd_80000_le_of_altN0 {n : ℕ} (hn : altN0 ≤ n) : 80000 ≤ n := hn
private theorem highdForceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]
private theorem highdForceList_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by
  cases xs <;> rfl
private theorem highdStrictConsInt_eq (x : ℤ) (xs : List ℤ) :
    highdStrictConsInt x xs = x :: xs := by cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.ofNat 0] | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t) =
      Int.ofNat n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.negSucc 0] | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t) =
      Int.negSucc n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl
private theorem highd_primNatBlt_eq (a b : ℕ) : primNatBlt a b = Nat.blt a b := rfl
private theorem highd_primIntNatAbs_eq (z : ℤ) : primIntNatAbs z = Int.natAbs z := by
  cases z <;> rfl
private theorem highd_nat_add_one (x : ℕ) : Nat.add x 1 = Nat.succ x := rfl
private theorem highd_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, highd_nat_ble_eq_true]
private theorem highd_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, highd_nat_ble_eq_true]; omega
private theorem highd_nat_blt_eq_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  unfold Nat.blt; exact highd_nat_ble_eq_true
private theorem highd_nat_blt_eq_false {a b : ℕ} : Nat.blt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, highd_nat_blt_eq_true]; omega
private theorem highd_to_beq {u : ℕ → ℕ → Bool}
    (h : ∀ {a b : ℕ}, (u a b = true) = (a = b)) (a b : ℕ) : u a b = (a == b) := by
  rw [Bool.eq_iff_iff, h, beq_iff_eq]
private theorem highd_nat_beq_eq_true {a b : ℕ} : (a == b) = true ↔ a = b :=
  beq_iff_eq
private theorem highd_nat_beq_eq_false {a b : ℕ} : (a == b) = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, highd_nat_beq_eq_true]
private theorem highd_natMin_eq (a b : ℕ) : highdNatMin a b = min a b := by
  unfold highdNatMin
  cases h : Nat.ble a b
  · simp [cond, Nat.min_eq_right (highd_nat_ble_eq_false.mp h).le]
  · simp [cond, Nat.min_eq_left (highd_nat_ble_eq_true.mp h)]
private theorem highd_altListLen_eq : ∀ xs : List ℕ, altListLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (highd_altListLen_eq xs)
private theorem highd_altIntLen_eq : ∀ xs : List ℤ, altIntLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (highd_altIntLen_eq xs)
private theorem highd_getD_eq_zero_of_le : ∀ (xs : List ℤ) (j : ℕ), xs.length ≤ j → xs.getD j 0 = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | _ :: xs, j + 1, h => highd_getD_eq_zero_of_le xs j (by simpa using h)
private theorem highd_tail_getD : ∀ (xs : List ℤ) (j : ℕ),
    (match xs with | _ :: xt => xt | [] => []).getD j 0 = xs.getD (j + 1) 0
  | [], _ => rfl
  | _ :: _, _ => rfl
private theorem highd_head_getD (xs : List ℤ) :
    (match xs with | x :: _ => x | [] => Int.ofNat 0) = xs.getD 0 0 := by
  cases xs <;> rfl
private theorem highd_second_getD (xs : List ℤ) :
    (match xs with | _ :: xn :: _ => xn | _ => Int.ofNat 0) = xs.getD 1 0 := by
  rcases xs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
private theorem highdIntTdivNat_eq (x : ℤ) (dNat : ℕ) :
    highdIntTdivNat x dNat = Int.tdiv x (Int.ofNat dNat) := by cases x with
  | ofNat m => dsimp only [highdIntTdivNat]; rw [primOfNatForced_eq]; rfl
  | negSucc m =>
    dsimp only [highdIntTdivNat]; rw [primNegOfNat_eq]
    change -(((m + 1) / dNat : ℕ) : ℤ) = -(Int.ofNat ((m + 1) / dNat)); rfl
private theorem highd_hornerSlideLoop_length (dNat : ℕ) :
    ∀ (outLen : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      (hornerSlideLoop dNat prev hb vec cur outLen).length = outLen
  | 0, _, _, _, _ => rfl
  | rem + 1, prev, hb, vec, cur => by
    unfold hornerSlideLoop hornerSlideLoopAux
    cases hb with
    | nil =>
      dsimp only; rw [highdStrictConsInt_eq]
      exact congrArg Nat.succ (highd_hornerSlideLoop_length dNat rem 0 [] _ _)
    | cons b hbRest =>
      dsimp only; rw [highdStrictConsInt_eq]
      exact congrArg Nat.succ (highd_hornerSlideLoop_length dNat rem _ hbRest _ _)
private theorem highd_hornerSlideLoop_getD (dNat : ℕ) :
    ∀ (outLen : ℕ) (prev : ℤ) (hb vec cur : List ℤ) (j : ℕ), j < outLen →
      (hornerSlideLoop dNat prev hb vec cur outLen).getD j 0 = vec.getD j 0 + Int.tdiv
            ((if j = 0 then prev else hb.getD (j - 1) 0 * cur.getD (j - 1) 0) -
              hb.getD j 0 * cur.getD (j + 1) 0) (Int.ofNat dNat)
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, prev, hb, vec, cur, 0, _ => by
    unfold hornerSlideLoop hornerSlideLoopAux
    cases hb with
    | nil =>
      dsimp only; rw [highdStrictConsInt_eq]; simp only [primIntAdd_eq, highdIntTdivNat_eq]
      change (match vec with | v :: _ => v | [] => Int.ofNat 0) +
        Int.tdiv prev (Int.ofNat dNat) = _
      rw [highd_head_getD]; simp
    | cons b hbRest =>
      dsimp only; rw [highdStrictConsInt_eq]
      simp only [primIntAdd_eq, primIntSub_eq, primIntMul_eq,
        highdIntTdivNat_eq]
      change (match vec with | v :: _ => v | [] => Int.ofNat 0) +
        Int.tdiv (prev - b * (match cur with | _ :: cn :: _ => cn | _ => Int.ofNat 0))
          (Int.ofNat dNat) = _
      rw [highd_head_getD, highd_second_getD]; simp
  | rem + 1, prev, hb, vec, cur, j + 1, hj => by
    unfold hornerSlideLoop hornerSlideLoopAux
    set vTail := match vec with | _ :: vt => vt | [] => ([] : List ℤ)
    set c0 := match cur with | c :: _ => c | [] => Int.ofNat 0
    set cTail := match cur with | _ :: ct => ct | [] => ([] : List ℤ)
    have hvT : vTail.getD j 0 = vec.getD (j + 1) 0 := highd_tail_getD vec j
    have hcT1 : cTail.getD (j + 1) 0 = cur.getD (j + 2) 0 := highd_tail_getD cur (j + 1)
    cases hb with
    | nil =>
      dsimp only; rw [highdStrictConsInt_eq]
      change (hornerSlideLoop dNat 0 [] vTail cTail rem).getD j 0 = _
      rw [highd_hornerSlideLoop_getD dNat rem 0 [] vTail cTail j (by omega), hvT]
      rcases j with _ | j' <;> simp
    | cons b hbRest =>
      dsimp only; rw [highdStrictConsInt_eq]
      change (hornerSlideLoop dNat (primIntMul b c0) hbRest vTail cTail rem).getD j 0 = _
      rw [primIntMul_eq,
        highd_hornerSlideLoop_getD dNat rem (b * c0) hbRest vTail cTail j (by omega),
        hvT, hcT1]
      congr 2
      rcases j with _ | j'
      · rw [show c0 = cur.getD 0 0 from highd_head_getD cur]; simp
      · have hcTj : cTail.getD j' 0 = cur.getD (j' + 1) 0 := highd_tail_getD cur j'
        have hj1 : j' + 1 ≠ 0 := Nat.succ_ne_zero j'
        have hj2 : j' + 1 + 1 ≠ 0 := Nat.succ_ne_zero _
        simp only [hj1, hj2, ↓reduceIte, Nat.add_sub_cancel, List.getD_cons_succ]; rw [hcTj]
private theorem highd_tdiv_diff_abs_le (num : ℤ) {dNat : ℕ} (hd : 1 ≤ dNat) :
    |((Int.tdiv num (Int.ofNat dNat) : ℤ) : ℝ) - (num : ℝ) / (dNat : ℝ)| ≤ 1 := by
  have hd_pos : (0 : ℝ) < (dNat : ℝ) := by exact_mod_cast hd
  have hcore (A : ℕ) : |((A / dNat : ℕ) : ℝ) - (A : ℝ) / (dNat : ℝ)| ≤ 1 := by
    set q := A / dNat
    have hlo_nat : q * dNat ≤ A := Nat.div_mul_le_self A dNat
    have hhi_nat : A < (q + 1) * dNat := by
      calc A < dNat * (q + 1) := Nat.lt_mul_div_succ A (by omega : 0 < dNat)
        _ = (q + 1) * dNat := Nat.mul_comm _ _
    have hloR : (q : ℝ) * (dNat : ℝ) ≤ (A : ℝ) := by exact_mod_cast hlo_nat
    have hhiR : (A : ℝ) ≤ ((q : ℝ) + 1) * (dNat : ℝ) := by
      have hc : (A : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * (dNat : ℝ) := by exact_mod_cast hhi_nat.le
      push_cast at hc; exact hc
    have hq_le : (q : ℝ) ≤ (A : ℝ) / (dNat : ℝ) := (le_div_iff₀ hd_pos).mpr hloR
    have hq_ge : (A : ℝ) / (dNat : ℝ) - (q : ℝ) ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ hd_pos]; linarith
    rw [abs_le]
    constructor <;> linarith
  cases num with
  | ofNat a =>
    have h1 : ((Int.tdiv (Int.ofNat a) (Int.ofNat dNat) : ℤ) : ℝ) = ((a / dNat : ℕ) : ℝ) := by
      change ((Int.ofNat (a / dNat) : ℤ) : ℝ) = ((a / dNat : ℕ) : ℝ)
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    have h2 : ((Int.ofNat a : ℤ) : ℝ) = (a : ℝ) := by
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [h1, h2]; exact hcore a
  | negSucc a =>
    have h1 : ((Int.tdiv (Int.negSucc a) (Int.ofNat dNat) : ℤ) : ℝ) =
        -(((a + 1) / dNat : ℕ) : ℝ) := by
      change ((-(Int.ofNat ((a + 1) / dNat)) : ℤ) : ℝ) = _
      simp only [Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast]
    have h2 : (Int.negSucc a : ℝ) = -((a + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h1, h2, neg_div,
      show -(((a + 1) / dNat : ℕ) : ℝ) - -(((a + 1 : ℕ) : ℝ) / (dNat : ℝ)) =
        -((((a + 1) / dNat : ℕ) : ℝ) - ((a + 1 : ℕ) : ℝ) / (dNat : ℝ)) by ring,
      abs_neg]
    exact hcore (a + 1)
private noncomputable def highd_listToOrbVec (d : ℕ) (xs : List ℤ) : Fin (d + 1) → ℝ :=
  fun a ↦ (xs.getD a.1 0 : ℝ) / wdScaleR
private noncomputable def highd_ptGenMat (d : ℕ) (hb : List ℤ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  tridiagSkewMat d (fun w ↦ (hb.getD w 0 : ℝ) / wdScaleR)
private theorem highd_hornerStageSlide_approx {deg maxLen d : ℕ} {hb vec cur : List ℤ}
    (hdeg : 1 ≤ deg) (hd : d ≤ 1024)
    (hhb : hb.length ≤ d) (_hmax : maxLen ≤ d + 1)
    (hvec_max : vec.length ≤ maxLen) (hvec_cur : vec.length ≤ cur.length + 1)
    (hcur_tail : ∀ j ≤ d, maxLen ≤ j → cur.getD (j - 1) 0 = 0 ∧ cur.getD (j + 1) 0 = 0) :
    let out := hornerStageSlide deg maxLen hb vec cur
    out.length = min maxLen (cur.length + 1) ∧ vec.length ≤ out.length ∧ out.length ≤ maxLen ∧
      vecNorm (highd_listToOrbVec d out - horner16Step (highd_ptGenMat d hb)
          (highd_listToOrbVec d vec) (highd_listToOrbVec d cur) deg) ≤ 33 / wdScaleR := by
  intro out
  have hB_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  have hout_def : out = applyHgTdivSlide deg (min maxLen (cur.length + 1)) hb vec cur := by
    dsimp [out, hornerStageSlide]; rw [highdForceNat_eq, highd_natMin_eq, highd_altIntLen_eq]
  set nxtLen := min maxLen (cur.length + 1)
  have hlen : out.length = nxtLen := by
    rw [hout_def]; unfold applyHgTdivSlide; rw [highdForceNat_eq]
    exact highd_hornerSlideLoop_length _ nxtLen 0 hb vec cur
  have hvec_out : vec.length ≤ out.length := by rw [hlen]; exact le_min hvec_max hvec_cur
  have hout_max : out.length ≤ maxLen := by rw [hlen]; exact Nat.min_le_left _ _
  refine ⟨hlen, hvec_out, hout_max, ?_⟩
  set diff := highd_listToOrbVec d out -
    horner16Step (highd_ptGenMat d hb) (highd_listToOrbVec d vec) (highd_listToOrbVec d cur) deg
  have hentry (a : Fin (d + 1)) : |diff a| ≤ 1 / wdScaleR := by
    have ha_le : a.1 ≤ d := by omega
    set num : ℤ :=
      (if a.1 = 0 then 0 else hb.getD (a.1 - 1) 0 * cur.getD (a.1 - 1) 0) -
        hb.getD a.1 0 * cur.getD (a.1 + 1) 0
    have hmat_eq : (highd_ptGenMat d hb *ᵥ highd_listToOrbVec d cur) a =
        (num : ℝ) / wdScaleR ^ 2 := by
      unfold highd_ptGenMat; rw [tridiagSkewMat_mulVec_apply]
      by_cases ha0 : 0 < a.1
      · have hne0 : a.1 ≠ 0 := by omega
        rw [dite_eq_left ha0]
        by_cases had : a.1 < d
        · rw [dite_eq_left had]; dsimp only [highd_listToOrbVec, num]; rw [ite_eq_right hne0]
          push_cast; field_simp [hB_pos.ne']; ring
        · rw [dite_eq_right had]; dsimp only [highd_listToOrbVec, num]
          rw [ite_eq_right hne0, highd_getD_eq_zero_of_le hb a.1 (by omega)]
          push_cast; field_simp [hB_pos.ne']; ring
      · have heq0 : a.1 = 0 := by omega
        rw [dite_eq_right ha0]
        by_cases had : a.1 < d
        · rw [dite_eq_left had]; dsimp only [highd_listToOrbVec, num]; rw [ite_eq_left heq0]
          push_cast; field_simp [hB_pos.ne']; ring
        · rw [dite_eq_right had]; dsimp only [highd_listToOrbVec, num]
          rw [ite_eq_left heq0, highd_getD_eq_zero_of_le hb a.1 (by omega)]
          push_cast; field_simp [hB_pos.ne']; ring
    by_cases hlt : a.1 < nxtLen
    · have hget : out.getD a.1 0 = vec.getD a.1 0 + Int.tdiv num (Int.ofNat (deg * wdScale)) := by
        rw [hout_def]; unfold applyHgTdivSlide; rw [highdForceNat_eq]
        exact highd_hornerSlideLoop_getD (deg * wdScale) nxtLen 0 hb vec cur a.1 hlt
      set dNat := deg * wdScale
      have hdNat1 : 1 ≤ dNat := by dsimp [dNat]; unfold wdScale; omega
      have hdNatR : (dNat : ℝ) = (deg : ℝ) * wdScaleR := by
        dsimp [dNat]; unfold wdScaleR; push_cast; rfl
      have hdeg_pos : (0 : ℝ) < (deg : ℝ) := by exact_mod_cast hdeg
      have hdiff_eq : diff a =
          (((Int.tdiv num (Int.ofNat dNat) : ℤ) : ℝ) - (num : ℝ) / (dNat : ℝ)) / wdScaleR := by
        dsimp [diff, highd_listToOrbVec, horner16Step]; simp only [Int.ofNat_eq_natCast] at hget ⊢
        rw [hget, hmat_eq, hdNatR]; push_cast
        field_simp [hB_pos.ne', hdeg_pos.ne']
        ring
      rw [hdiff_eq, abs_div, abs_of_pos hB_pos]
      exact div_le_div_of_nonneg_right (highd_tdiv_diff_abs_le num hdNat1) hB_pos.le
    · have hge : nxtLen ≤ a.1 := by omega
      have hout_z : out.getD a.1 0 = 0 := highd_getD_eq_zero_of_le out a.1 (by omega)
      have hvec_z : vec.getD a.1 0 = 0 := highd_getD_eq_zero_of_le vec a.1 (by omega)
      have hcur_z : cur.getD (a.1 - 1) 0 = 0 ∧ cur.getD (a.1 + 1) 0 = 0 := by
        by_cases hm : maxLen ≤ a.1
        · exact hcur_tail a.1 ha_le hm
        · have hc_le : cur.length + 1 ≤ a.1 := by
            have : nxtLen = min maxLen (cur.length + 1) := rfl; omega
          exact ⟨highd_getD_eq_zero_of_le cur (a.1 - 1) (by omega),
            highd_getD_eq_zero_of_le cur (a.1 + 1) (by omega)⟩
      have hnum0 : num = 0 := by
        dsimp [num]; rw [hcur_z.1, hcur_z.2]
        split_ifs <;> simp
      have hdiff0 : diff a = 0 := by
        dsimp [diff, highd_listToOrbVec, horner16Step]; rw [hout_z, hvec_z, hmat_eq, hnum0]; simp
      rw [hdiff0, abs_zero]
      positivity
  rw [vecNorm, Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
  have hsq_le (a : Fin (d + 1)) : (diff a) ^ 2 ≤ (1 / wdScaleR) ^ 2 := by
    rw [← sq_abs (diff a)]; exact pow_le_pow_left₀ (abs_nonneg _) (hentry a) 2
  calc vecSqNorm diff
      = ∑ a : Fin (d + 1), (diff a) ^ 2 := rfl
    _ ≤ ∑ _ : Fin (d + 1), (1 / wdScaleR) ^ 2 := Finset.sum_le_sum fun a _ ↦ hsq_le a
    _ = ((d + 1 : ℕ) : ℝ) * (1 / wdScaleR) ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (33 : ℝ) ^ 2 * (1 / wdScaleR) ^ 2 := by
        have hd33 : ((d + 1 : ℕ) : ℝ) ≤ (33 : ℝ) ^ 2 := by
          have : d + 1 ≤ 1089 := by omega
          calc ((d + 1 : ℕ) : ℝ) ≤ (1089 : ℝ) := by exact_mod_cast this
            _ = (33 : ℝ) ^ 2 := by norm_num
        exact mul_le_mul_of_nonneg_right hd33 (sq_nonneg _)
    _ = (33 / wdScaleR) ^ 2 := by ring
private theorem highd_hornerStageSlide_chain {deg maxLen d k : ℕ} {hb vec cur : List ℤ}
    (hdeg : 1 ≤ deg) (hk : k ≤ 15) (hd : d ≤ 1024) (hhb : hb.length ≤ d) (hmax : maxLen ≤ d + 1)
    (hvec_max : vec.length ≤ maxLen) (hcap : d < maxLen ∨ vec.length + 16 ≤ maxLen)
    (hcur_lo : vec.length ≤ cur.length) (hcur_hi : cur.length ≤ vec.length + k) :
    vec.length ≤ (hornerStageSlide deg maxLen hb vec cur).length ∧
      (hornerStageSlide deg maxLen hb vec cur).length ≤ maxLen ∧
      (hornerStageSlide deg maxLen hb vec cur).length ≤ vec.length + (k + 1) ∧
      vecNorm (highd_listToOrbVec d (hornerStageSlide deg maxLen hb vec cur) -
        horner16Step (highd_ptGenMat d hb)
          (highd_listToOrbVec d vec) (highd_listToOrbVec d cur) deg) ≤ 33 / wdScaleR := by
  have hcur_tail : ∀ j ≤ d, maxLen ≤ j → cur.getD (j - 1) 0 = 0 ∧ cur.getD (j + 1) 0 = 0 := by
    intro j hjd hmj
    rcases hcap with hlt | hle
    · omega
    · exact ⟨highd_getD_eq_zero_of_le cur (j - 1) (by omega),
        highd_getD_eq_zero_of_le cur (j + 1) (by omega)⟩
  obtain ⟨hlen, hv_out, hout_max, herr⟩ :=
    highd_hornerStageSlide_approx hdeg hd hhb hmax hvec_max (by omega) hcur_tail
  refine ⟨hv_out, hout_max, ?_, herr⟩; rw [hlen]; exact (Nat.min_le_right _ _).trans (by omega)
private theorem highd_hornerT16SlideStep_approx {maxLen d : ℕ} {hb vec : List ℤ}
    (hd : d ≤ 1024) (hhb : hb.length ≤ d) (hmax : maxLen ≤ d + 1) (hvec_max : vec.length ≤ maxLen)
    (hcap : d < maxLen ∨ vec.length + 16 ≤ maxLen)
    (hG : ∀ u, vecNorm (highd_ptGenMat d hb *ᵥ u) ≤ (3 / 2) * vecNorm u) :
    (hornerT16SlideStep maxLen hb vec).length ≤ maxLen ∧
      vecNorm (highd_listToOrbVec d (hornerT16SlideStep maxLen hb vec) -
        taylor16OfMat (highd_ptGenMat d hb) *ᵥ highd_listToOrbVec d vec) ≤
        (297 / 2) / wdScaleR := by
  unfold hornerT16SlideStep; simp only [highdForceList_eq]
  let c15 := hornerStageSlide 16 maxLen hb vec vec
  have st15 : vec.length ≤ c15.length ∧ c15.length ≤ maxLen ∧ c15.length ≤ vec.length + 1 ∧
      vecNorm (highd_listToOrbVec d c15 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d vec) 16) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 16) (by omega : 0 ≤ 15)
      hd hhb hmax hvec_max hcap le_rfl (by omega)
  let c14 := hornerStageSlide 15 maxLen hb vec c15
  have st14 : vec.length ≤ c14.length ∧ c14.length ≤ maxLen ∧ c14.length ≤ vec.length + 2 ∧
      vecNorm (highd_listToOrbVec d c14 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c15) 15) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 15) (by omega : 1 ≤ 15)
      hd hhb hmax hvec_max hcap st15.1 st15.2.2.1
  let c13 := hornerStageSlide 14 maxLen hb vec c14
  have st13 : vec.length ≤ c13.length ∧ c13.length ≤ maxLen ∧ c13.length ≤ vec.length + 3 ∧
      vecNorm (highd_listToOrbVec d c13 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c14) 14) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 14) (by omega : 2 ≤ 15)
      hd hhb hmax hvec_max hcap st14.1 st14.2.2.1
  let c12 := hornerStageSlide 13 maxLen hb vec c13
  have st12 : vec.length ≤ c12.length ∧ c12.length ≤ maxLen ∧ c12.length ≤ vec.length + 4 ∧
      vecNorm (highd_listToOrbVec d c12 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c13) 13) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 13) (by omega : 3 ≤ 15)
      hd hhb hmax hvec_max hcap st13.1 st13.2.2.1
  let c11 := hornerStageSlide 12 maxLen hb vec c12
  have st11 : vec.length ≤ c11.length ∧ c11.length ≤ maxLen ∧ c11.length ≤ vec.length + 5 ∧
      vecNorm (highd_listToOrbVec d c11 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c12) 12) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 12) (by omega : 4 ≤ 15)
      hd hhb hmax hvec_max hcap st12.1 st12.2.2.1
  let c10 := hornerStageSlide 11 maxLen hb vec c11
  have st10 : vec.length ≤ c10.length ∧ c10.length ≤ maxLen ∧ c10.length ≤ vec.length + 6 ∧
      vecNorm (highd_listToOrbVec d c10 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c11) 11) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 11) (by omega : 5 ≤ 15)
      hd hhb hmax hvec_max hcap st11.1 st11.2.2.1
  let c9 := hornerStageSlide 10 maxLen hb vec c10
  have st9 : vec.length ≤ c9.length ∧ c9.length ≤ maxLen ∧ c9.length ≤ vec.length + 7 ∧
      vecNorm (highd_listToOrbVec d c9 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c10) 10) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 10) (by omega : 6 ≤ 15)
      hd hhb hmax hvec_max hcap st10.1 st10.2.2.1
  let c8 := hornerStageSlide 9 maxLen hb vec c9
  have st8 : vec.length ≤ c8.length ∧ c8.length ≤ maxLen ∧ c8.length ≤ vec.length + 8 ∧
      vecNorm (highd_listToOrbVec d c8 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c9) 9) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 9) (by omega : 7 ≤ 15)
      hd hhb hmax hvec_max hcap st9.1 st9.2.2.1
  let c7 := hornerStageSlide 8 maxLen hb vec c8
  have st7 : vec.length ≤ c7.length ∧ c7.length ≤ maxLen ∧ c7.length ≤ vec.length + 9 ∧
      vecNorm (highd_listToOrbVec d c7 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c8) 8) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 8) (by omega : 8 ≤ 15)
      hd hhb hmax hvec_max hcap st8.1 st8.2.2.1
  let c6 := hornerStageSlide 7 maxLen hb vec c7
  have st6 : vec.length ≤ c6.length ∧ c6.length ≤ maxLen ∧ c6.length ≤ vec.length + 10 ∧
      vecNorm (highd_listToOrbVec d c6 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c7) 7) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 7) (by omega : 9 ≤ 15)
      hd hhb hmax hvec_max hcap st7.1 st7.2.2.1
  let c5 := hornerStageSlide 6 maxLen hb vec c6
  have st5 : vec.length ≤ c5.length ∧ c5.length ≤ maxLen ∧ c5.length ≤ vec.length + 11 ∧
      vecNorm (highd_listToOrbVec d c5 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c6) 6) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 6) (by omega : 10 ≤ 15)
      hd hhb hmax hvec_max hcap st6.1 st6.2.2.1
  let c4 := hornerStageSlide 5 maxLen hb vec c5
  have st4 : vec.length ≤ c4.length ∧ c4.length ≤ maxLen ∧ c4.length ≤ vec.length + 12 ∧
      vecNorm (highd_listToOrbVec d c4 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c5) 5) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 5) (by omega : 11 ≤ 15)
      hd hhb hmax hvec_max hcap st5.1 st5.2.2.1
  let c3 := hornerStageSlide 4 maxLen hb vec c4
  have st3 : vec.length ≤ c3.length ∧ c3.length ≤ maxLen ∧ c3.length ≤ vec.length + 13 ∧
      vecNorm (highd_listToOrbVec d c3 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c4) 4) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 4) (by omega : 12 ≤ 15)
      hd hhb hmax hvec_max hcap st4.1 st4.2.2.1
  let c2 := hornerStageSlide 3 maxLen hb vec c3
  have st2 : vec.length ≤ c2.length ∧ c2.length ≤ maxLen ∧ c2.length ≤ vec.length + 14 ∧
      vecNorm (highd_listToOrbVec d c2 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c3) 3) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 3) (by omega : 13 ≤ 15)
      hd hhb hmax hvec_max hcap st3.1 st3.2.2.1
  let c1 := hornerStageSlide 2 maxLen hb vec c2
  have st1 : vec.length ≤ c1.length ∧ c1.length ≤ maxLen ∧ c1.length ≤ vec.length + 15 ∧
      vecNorm (highd_listToOrbVec d c1 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c2) 2) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 2) (by omega : 14 ≤ 15)
      hd hhb hmax hvec_max hcap st2.1 st2.2.2.1
  let c0 := hornerStageSlide 1 maxLen hb vec c1
  have st0 : vec.length ≤ c0.length ∧ c0.length ≤ maxLen ∧ c0.length ≤ vec.length + 16 ∧
      vecNorm (highd_listToOrbVec d c0 - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (highd_listToOrbVec d c1) 1) ≤ 33 / wdScaleR :=
    highd_hornerStageSlide_chain (by omega : 1 ≤ 1) (by omega : 15 ≤ 15)
      hd hhb hmax hvec_max hcap st1.1 st1.2.2.1
  change c0.length ≤ maxLen ∧ vecNorm (highd_listToOrbVec d c0 -
      taylor16OfMat (highd_ptGenMat d hb) *ᵥ highd_listToOrbVec d vec) ≤ (297 / 2) / wdScaleR
  clear_value c15 c14 c13 c12 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0
  let seq : ℕ → Fin (d + 1) → ℝ := fun k ↦
    match k with
    | 0 => highd_listToOrbVec d vec
    | 1 => highd_listToOrbVec d c15
    | 2 => highd_listToOrbVec d c14
    | 3 => highd_listToOrbVec d c13
    | 4 => highd_listToOrbVec d c12
    | 5 => highd_listToOrbVec d c11
    | 6 => highd_listToOrbVec d c10
    | 7 => highd_listToOrbVec d c9
    | 8 => highd_listToOrbVec d c8
    | 9 => highd_listToOrbVec d c7
    | 10 => highd_listToOrbVec d c6
    | 11 => highd_listToOrbVec d c5
    | 12 => highd_listToOrbVec d c4
    | 13 => highd_listToOrbVec d c3
    | 14 => highd_listToOrbVec d c2
    | 15 => highd_listToOrbVec d c1
    | _ => highd_listToOrbVec d c0
  have hstep : ∀ k < 16, vecNorm (seq (k + 1) - horner16Step (highd_ptGenMat d hb)
        (highd_listToOrbVec d vec) (seq k) (16 - k)) ≤ 33 / wdScaleR := by
    intro k hk
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · dsimp only [seq]; exact st15.2.2.2
    · dsimp only [seq]; exact st14.2.2.2
    · dsimp only [seq]; exact st13.2.2.2
    · dsimp only [seq]; exact st12.2.2.2
    · dsimp only [seq]; exact st11.2.2.2
    · dsimp only [seq]; exact st10.2.2.2
    · dsimp only [seq]; exact st9.2.2.2
    · dsimp only [seq]; exact st8.2.2.2
    · dsimp only [seq]; exact st7.2.2.2
    · dsimp only [seq]; exact st6.2.2.2
    · dsimp only [seq]; exact st5.2.2.2
    · dsimp only [seq]; exact st4.2.2.2
    · dsimp only [seq]; exact st3.2.2.2
    · dsimp only [seq]; exact st2.2.2.2
    · dsimp only [seq]; exact st1.2.2.2
    · dsimp only [seq]; exact st0.2.2.2
    · omega
  have hε_nn : (0 : ℝ) ≤ 33 / wdScaleR := by unfold wdScaleR wdScale; positivity
  have hround := vecNorm_horner16_round_le hG hε_nn rfl hstep; refine ⟨st0.2.1, ?_⟩
  calc vecNorm (highd_listToOrbVec d c0 -
          taylor16OfMat (highd_ptGenMat d hb) *ᵥ highd_listToOrbVec d vec)
      ≤ (9 / 2) * (33 / wdScaleR) := hround
    _ = (297 / 2) / wdScaleR := by ring
private theorem highd_altIterFullT16_approx {d : ℕ} {hb : List ℤ}
    (hd : d ≤ 1024) (hhb : hb.length ≤ d)
    (hG : ∀ u, vecNorm (highd_ptGenMat d hb *ᵥ u) ≤ (3 / 2) * vecNorm u) :
    ∀ (s : ℕ) (vec : List ℤ), vec.length ≤ d + 1 →
      (altIterFullT16 s (d + 1) hb vec).length ≤ d + 1 ∧
        vecNorm (highd_listToOrbVec d (altIterFullT16 s (d + 1) hb vec) -
          ((taylor16OfMat (highd_ptGenMat d hb)) ^ s) *ᵥ highd_listToOrbVec d vec) ≤
          ((297 / 2) * (s : ℝ)) / wdScaleR
  | 0, vec, hvec => by simp [altIterFullT16, hvec, pow_zero, Matrix.one_mulVec, vecNorm_zero]
  | s + 1, vec, hvec => by
    unfold altIterFullT16; simp only [highdForceList_eq]; obtain ⟨hl1, he1⟩ :=
      highd_hornerT16SlideStep_approx hd hhb le_rfl hvec (Or.inl (Nat.lt_succ_self d)) hG
    obtain ⟨hls, hes⟩ :=
      highd_altIterFullT16_approx hd hhb hG s (hornerT16SlideStep (d + 1) hb vec) hl1
    refine ⟨hls, ?_⟩
    set B := taylor16OfMat (highd_ptGenMat d hb)
    have hskew : (highd_ptGenMat d hb)ᵀ = -highd_ptGenMat d hb := tridiagSkewMat_transpose d _
    have hBs_contr (w : Fin (d + 1) → ℝ) : vecNorm ((B ^ s) *ᵥ w) ≤ vecNorm w := by
      have hB_contr (u : Fin (d + 1) → ℝ) : vecNorm (B *ᵥ u) ≤ 1 * vecNorm u := by
        rw [one_mul]; exact vecNorm_taylor16OfMat_mulVec_le hskew hG u
      simpa using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) hB_contr s w
    have hsplit : highd_listToOrbVec d (altIterFullT16 s (d + 1) hb
          (hornerT16SlideStep (d + 1) hb vec)) - (B ^ (s + 1)) *ᵥ highd_listToOrbVec d vec =
        (highd_listToOrbVec d (altIterFullT16 s (d + 1) hb (hornerT16SlideStep (d + 1) hb vec)) -
          (B ^ s) *ᵥ highd_listToOrbVec d (hornerT16SlideStep (d + 1) hb vec)) +
        (B ^ s) *ᵥ (highd_listToOrbVec d (hornerT16SlideStep (d + 1) hb vec) -
          B *ᵥ highd_listToOrbVec d vec) := by
      rw [pow_succ, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [hsplit]
    calc vecNorm ((highd_listToOrbVec d (altIterFullT16 s (d + 1) hb
              (hornerT16SlideStep (d + 1) hb vec)) -
            (B ^ s) *ᵥ highd_listToOrbVec d (hornerT16SlideStep (d + 1) hb vec)) +
            (B ^ s) *ᵥ (highd_listToOrbVec d (hornerT16SlideStep (d + 1) hb vec) -
              B *ᵥ highd_listToOrbVec d vec))
        ≤ vecNorm (highd_listToOrbVec d (altIterFullT16 s (d + 1) hb
              (hornerT16SlideStep (d + 1) hb vec)) -
            (B ^ s) *ᵥ highd_listToOrbVec d (hornerT16SlideStep (d + 1) hb vec)) +
            vecNorm ((B ^ s) *ᵥ (highd_listToOrbVec d (hornerT16SlideStep (d + 1) hb vec) -
              B *ᵥ highd_listToOrbVec d vec)) := vecNorm_add_le _ _
      _ ≤ ((297 / 2) * (s : ℝ)) / wdScaleR + (297 / 2) / wdScaleR :=
          add_le_add hes ((hBs_contr _).trans he1)
      _ = ((297 / 2) * ((s + 1 : ℕ) : ℝ)) / wdScaleR := by push_cast; ring
/- ## Section 3: Causal-Window List Helpers, Ceiling Enclosures, & `altIterCapT16` Soundness -/
private theorem highd_altAllZeroInt_sound :
    ∀ (xs : List ℤ), altAllZeroInt xs = true → ∀ j : ℕ, xs.getD j 0 = 0
  | [], _, _ => rfl
  | z :: zs, h, j => by
    unfold altAllZeroInt at h; rw [highd_primIntNatAbs_eq] at h
    rw [highd_to_beq (fun {a b} ↦ Nat.beq_eq) (Int.natAbs z) 0] at h
    cases hb : (Int.natAbs z == 0) with
    | false => rw [hb, highd_cond_false] at h; exact Bool.noConfusion h
    | true =>
      rw [hb, highd_cond_true] at h
      have hz0 : z = 0 := Int.natAbs_eq_zero.mp (highd_nat_beq_eq_true.mp hb)
      rcases j with _ | j'
      · exact hz0
      · exact highd_altAllZeroInt_sound zs h j'
private theorem highd_altCheckDropZero_sound :
    ∀ (k : ℕ) (xs : List ℤ), altCheckDropZero k xs = true → ∀ j : ℕ, k ≤ j → xs.getD j 0 = 0
  | 0, xs, h, j, _ => highd_altAllZeroInt_sound xs h j
  | _ + 1, [], _, _, _ => rfl
  | k + 1, _ :: xs, h, j, hj => by
    rcases j with _ | j'
    · omega
    · exact highd_altCheckDropZero_sound k xs h j' (by omega)
private theorem highd_altTakeMaxInt_length :
    ∀ (k : ℕ) (xs : List ℤ), (altTakeMaxInt k xs).length ≤ k
  | 0, _ => le_rfl
  | _ + 1, [] => by simp [altTakeMaxInt]
  | k + 1, x :: xs => by
    dsimp only [altTakeMaxInt]; rw [highdStrictConsInt_eq]
    exact Nat.succ_le_succ (highd_altTakeMaxInt_length k xs)
private theorem highd_altTakeMaxInt_getD_of_dropZero :
    ∀ (k : ℕ) (xs : List ℤ), altCheckDropZero k xs = true →
      ∀ j : ℕ, (altTakeMaxInt k xs).getD j 0 = xs.getD j 0
  | 0, xs, h, j => (highd_altAllZeroInt_sound xs h j).symm
  | _ + 1, [], _, _ => rfl
  | k + 1, x :: xs, h, j => by
    dsimp only [altTakeMaxInt]; rw [highdStrictConsInt_eq]
    rcases j with _ | j'
    · rfl
    · exact highd_altTakeMaxInt_getD_of_dropZero k xs h j'
private theorem highd_altPadRightInts_length :
    ∀ (targetLen : ℕ) (xs : List ℤ), (altPadRightInts targetLen xs).length = targetLen
  | 0, _ => rfl
  | rem + 1, [] => by
    dsimp only [altPadRightInts]; rw [highdStrictConsInt_eq]
    exact congrArg Nat.succ (highd_altPadRightInts_length rem [])
  | rem + 1, _ :: xs => by
    dsimp only [altPadRightInts]; rw [highdStrictConsInt_eq]
    exact congrArg Nat.succ (highd_altPadRightInts_length rem xs)
private theorem highd_altPadRightInts_getD :
    ∀ (targetLen : ℕ) (xs : List ℤ), xs.length ≤ targetLen →
      ∀ j : ℕ, (altPadRightInts targetLen xs).getD j 0 = xs.getD j 0
  | 0, [], _, _ => rfl
  | 0, _ :: _, hlen, _ => absurd hlen (Nat.not_le_of_gt (Nat.succ_pos _))
  | rem + 1, [], _, j => by
    dsimp only [altPadRightInts]; rw [highdStrictConsInt_eq]
    rcases j with _ | j'
    · rfl
    · exact highd_altPadRightInts_getD rem [] (Nat.zero_le _) j'
  | rem + 1, x :: xs, hlen, j => by
    dsimp only [altPadRightInts]; rw [highdStrictConsInt_eq]
    rcases j with _ | j'
    · rfl
    · exact highd_altPadRightInts_getD rem xs (by simpa using hlen) j'
private theorem highd_ceil_div_mul_ge (n d : ℕ) (hd : 0 < d) : n ≤ (((d - 1) + n) / d) * d := by
  have h := Nat.lt_mul_div_succ ((d - 1) + n) hd; rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d] at h
  omega
private theorem highd_mulCeil15_ge (a b : ℕ) :
    ((a : ℝ) / wdScaleR) * ((b : ℝ) / wdScaleR) ≤ (highdMulCeil15 a b : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  have hnat : a * b ≤ highdMulCeil15 a b * wdScale := by
    have h := highd_ceil_div_mul_ge (a * b) wdScale (by unfold wdScale; positivity)
    have hsub : wdScale - 1 = 999999999999999 := by unfold wdScale; rfl
    rw [hsub] at h; exact h
  have hreal : (a : ℝ) * (b : ℝ) ≤ (highdMulCeil15 a b : ℝ) * wdScaleR := by
    unfold wdScaleR; exact_mod_cast hnat
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hB hB) hB]
  exact (mul_le_mul_of_nonneg_right hreal hB.le).trans_eq (by ring)
private theorem highd_altPowCeilLoop_ge (x : ℕ) :
    ∀ (k acc : ℕ) {p : ℝ}, 0 ≤ p → p ≤ (acc : ℝ) / wdScaleR →
      p * ((x : ℝ) / wdScaleR) ^ k ≤ (highdPowCeilLoop k acc x : ℝ) / wdScaleR := by
  intro k
  induction k with
  | zero =>
    intro acc p _ hacc
    dsimp only [highdPowCeilLoop]
    simpa only [pow_zero, mul_one] using hacc
  | succ k ih =>
    intro acc p hp0 hacc
    dsimp only [highdPowCeilLoop]
    have hx0 : 0 ≤ (x : ℝ) / wdScaleR := by unfold wdScaleR wdScale; positivity
    have hnext : p * ((x : ℝ) / wdScaleR) ≤ (highdMulCeil15 acc x : ℝ) / wdScaleR :=
      (mul_le_mul_of_nonneg_right hacc hx0).trans (highd_mulCeil15_ge acc x)
    have hrec := ih (highdMulCeil15 acc x) (mul_nonneg hp0 hx0) hnext
    simpa only [pow_succ', ← mul_assoc] using hrec
private theorem highd_altPow17Ceil15_ge (x : ℕ) :
    ((x : ℝ) / wdScaleR) ^ 17 ≤ (altPow17Ceil15 x : ℝ) / wdScaleR := by
  have hx0 : 0 ≤ (x : ℝ) / wdScaleR := by unfold wdScaleR wdScale; positivity
  have h := highd_altPowCeilLoop_ge x 16 x hx0 le_rfl; dsimp only [altPow17Ceil15]
  simpa only [pow_succ'] using h
private theorem highd_altMaxBHiFrom_ge (m r : ℕ) : ∀ (rem w j : ℕ), j < rem →
      (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤ altMaxBHiFrom m r w rem
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, j, hj => by
    unfold altMaxBHiFrom altMaxBHiFromAux; simp only [highdForceNat_eq, highd_primNatBlt_eq]
    set rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    set bHi := (altIsqrt15 rad).2
    set rMax := altMaxBHiFromAux m r rem (Nat.add w 1)
    rcases j with _ | j'
    · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) = rad := by
        change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) = 4 * (w + 1) * (m - w) * (r - w)
        simp
      have hb_eq : (altIsqrt15 (4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)))).2 = bHi := by
        rw [hrad]
      rw [hb_eq]
      cases hlt : Nat.blt rMax bHi
      · simp only [cond]; exact highd_nat_blt_eq_false.mp hlt
      · simp only [cond]; exact le_rfl
    · have ih : (altIsqrt15 (4 * (w + 1 + j' + 1) * (m - (w + 1 + j')) *
          (r - (w + 1 + j')))).2 ≤ rMax :=
        highd_altMaxBHiFrom_ge m r rem (w + 1) j' (by omega)
      have hidx : w + 1 + j' = w + (j' + 1) := by omega
      rw [hidx] at ih
      cases hlt : Nat.blt rMax bHi
      · simpa [cond] using ih
      · simp only [cond]; exact ih.trans (highd_nat_blt_eq_true.mp hlt).le
private theorem highd_altCheckHbTight_sound (m r : ℕ) :
    ∀ (rem w : ℕ), altCheckHbTight m r w rem = true → ∀ j < rem,
        (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤
          (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1 + 1
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, hchk, j, hj => by
    unfold altCheckHbTight altCheckHbTightAux at hchk; dsimp only at hchk
    generalize hp : altIsqrt15 (Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1))
      (Nat.sub m w)) (Nat.sub r w)) = p at hchk
    cases hble : Nat.ble p.2 (Nat.add p.1 1) with
    | false => rw [hble, highd_cond_false] at hchk; exact Bool.noConfusion hchk
    | true =>
      rw [hble, highd_cond_true] at hchk
      rcases j with _ | j'
      · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w) := by
          change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) = 4 * (w + 1) * (m - w) * (r - w)
          simp
        rw [hrad, hp]; exact highd_nat_ble_eq_true.mp hble
      · have ih := highd_altCheckHbTight_sound m r rem (w + 1) hchk j' (by omega)
        simpa [show w + 1 + j' = w + (j' + 1) by omega] using ih
private theorem highd_altBuildHbFrom_length (m r hPt : ℕ) :
    ∀ (rem w : ℕ), (altBuildHbFrom m r hPt w rem).length = rem
  | 0, _ => rfl
  | rem + 1, w => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    exact congrArg Nat.succ (highd_altBuildHbFrom_length m r hPt rem (w + 1))
private theorem highd_altBuildHbFrom_getD (m r hPt : ℕ) : ∀ (rem w j : ℕ), j < rem →
      (altBuildHbFrom m r hPt w rem).getD j 0 =
        (((hPt * (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1) /
          wdScale : ℕ) : ℤ)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, 0, _ => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    change (((hPt * (altIsqrt15 (4 * (w + 1) * (m - w) * (r - w))).1) / wdScale : ℕ) : ℤ) = _; simp
  | rem + 1, w, j + 1, hj => by
    dsimp only [altBuildHbFrom, altBuildHbFromAux]; rw [strictConsInt_eq, List.getD_cons_succ]
    have hw : Nat.add w 1 = w + 1 := rfl; rw [hw]
    have ih := highd_altBuildHbFrom_getD m r hPt rem (w + 1) j (by omega)
    dsimp only [altBuildHbFrom] at ih
    simpa [show w + 1 + j = w + (j + 1) by omega] using ih
private theorem highd_altMaxBHiFrom_le_of_tight {m r : ℕ} (hm : m ≤ 8192) (hr : r ≤ 1024) :
    ∀ (rem w : ℕ), altCheckHbTight m r w rem = true → w + rem ≤ r →
      altMaxBHiFrom m r w rem ≤ 200001 * wdScale
  | 0, _, _, _ => Nat.zero_le _
  | rem + 1, w, hchk, hwrem => by
    unfold altMaxBHiFrom altMaxBHiFromAux; simp only [highdForceNat_eq, highd_primNatBlt_eq]
    set rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    set sqLo := (altIsqrt15 rad).1
    set bHi := (altIsqrt15 rad).2
    set rMax := altMaxBHiFromAux m r rem (Nat.add w 1)
    have htight0 : bHi ≤ sqLo + 1 := by
      have h := highd_altCheckHbTight_sound m r (rem + 1) w hchk 0 (Nat.succ_pos _)
      have hrad_eq : rad = 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) := by
        change 4 * (w + 1) * (m - w) * (r - w) = _; simp
      simpa [bHi, sqLo, hrad_eq] using h
    have hchk_rest : altCheckHbTight m r (w + 1) rem = true := by
      unfold altCheckHbTight altCheckHbTightAux at hchk; dsimp only at hchk
      generalize hp : altIsqrt15 rad = p at hchk
      cases hb : Nat.ble p.2 (Nat.add p.1 1) with
      | false => rw [hb, highd_cond_false] at hchk; exact Bool.noConfusion hchk
      | true => rw [hb, highd_cond_true] at hchk; exact hchk
    have ih : rMax ≤ 200001 * wdScale :=
      highd_altMaxBHiFrom_le_of_tight hm hr rem (w + 1) hchk_rest (by omega)
    have hlo : (sqLo : ℝ) / wdScaleR ≤ √(rad : ℝ) := (altIsqrt15_sound rad).1
    clear_value sqLo bHi rMax
    have hrad_le : rad ≤ 200000 * 200000 := by
      have hw_lt : w < r := by omega
      have h1 : 4 * (w + 1) ≤ 4096 := by omega
      have h2 : m - w ≤ 8192 := by omega
      have h3 : r - w ≤ 1024 := by omega
      have hp : 4 * (w + 1) * (m - w) * (r - w) ≤ 4096 * 8192 * 1024 :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      change 4 * (w + 1) * (m - w) * (r - w) ≤ 200000 * 200000; exact hp.trans (by norm_num)
    have hbLo_le : sqLo ≤ 200000 * wdScale := by
      have hB : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
      have hsq : √(rad : ℝ) ≤ 200000 := by
        rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩
        have hc : (rad : ℝ) ≤ ((200000 * 200000 : ℕ) : ℝ) := by exact_mod_cast hrad_le
        exact hc.trans_eq (by norm_num)
      have hR : (sqLo : ℝ) ≤ (200000 : ℝ) * wdScaleR := (div_le_iff₀ hB).mp (hlo.trans hsq)
      have hR' : (sqLo : ℝ) ≤ ((200000 * wdScale : ℕ) : ℝ) := by
        unfold wdScaleR at hR; push_cast; exact hR
      exact_mod_cast hR'
    have hbHi_le : bHi ≤ 200001 * wdScale := by unfold wdScale at hbLo_le ⊢; omega
    cases hlt : Nat.blt rMax bHi
    · simpa [cond] using ih
    · simpa [cond] using hbHi_le
private theorem highd_substep_bounds {n tau9 nSub : ℕ}
    (hn : altN0 ≤ n) (htau : tau9 ≤ 4000000000) (hnsub1 : 1 ≤ nSub) (hnsub : nSub ≤ 16384) :
    0 ≤ (((tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000) : ℕ) : ℝ) / √(2 ^ n : ℝ) ∧
      (((tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000) : ℕ) : ℝ) / √(2 ^ n : ℝ) ≤
        ((2 + (tau9 * 1000000) / nSub : ℕ) : ℝ) / wdScaleR ∧
      |(((tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000) : ℕ) : ℝ) / √(2 ^ n : ℝ) -
          (((tau9 * 1000000) / nSub : ℕ) : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
  set q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
  set hPt := (tau9 * 1000000) / nSub
  set N := 2 ^ n
  have hN_cast : (2 : ℝ) ^ n = (N : ℝ) := by dsimp [N]; norm_cast
  rw [hN_cast]; have h200 : 200 ≤ n := highd_200_le_of_altN0 hn
  have hN_ge : (2 : ℝ) ^ 200 ≤ (N : ℝ) := by
    dsimp [N]; rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) h200
  have hsqrtN_ge : (2 : ℝ) ^ 100 ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hN_ge)
  have hsqrtN_pos : 0 < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsqrtN_ge
  have hnsub_pos : (0 : ℝ) < (nSub : ℝ) := by exact_mod_cast hnsub1
  have hB : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB]; positivity
  have hhPt_lo : (hPt : ℝ) / wdScaleR ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hnat : hPt * nSub ≤ tau9 * 1000000 := Nat.div_mul_le_self _ _
    have hR : (hPt : ℝ) * (nSub : ℝ) ≤ (tau9 : ℝ) * 1000000 := by exact_mod_cast hnat
    rw [hB, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hhPt_hi : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) ≤ ((hPt + 1 : ℕ) : ℝ) / wdScaleR := by
    have hnat : tau9 * 1000000 < (hPt + 1) * nSub :=
      calc tau9 * 1000000 < nSub * (hPt + 1) := Nat.lt_mul_div_succ _ (by omega : 0 < nSub)
        _ = (hPt + 1) * nSub := Nat.mul_comm _ _
    have hR : (tau9 : ℝ) * 1000000 ≤ ((hPt + 1 : ℕ) : ℝ) * (nSub : ℝ) := by
      exact_mod_cast hnat.le
    rw [hB, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq_hi : (q : ℝ) / √(N : ℝ) ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hnat : (nSub * 1000000000) * q ≤ tau9 * Nat.sqrt N := Nat.mul_div_le _ _
    have hR : ((nSub : ℝ) * 1000000000) * (q : ℝ) ≤ (tau9 : ℝ) * (Nat.sqrt N : ℝ) := by
      exact_mod_cast hnat
    have hsq : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_; have hn' := (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le N)
      simpa [sq, Nat.cast_mul] using hn'
    rw [div_le_div_iff₀ hsqrtN_pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg tau9)]
  have hq_lo : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) - (q : ℝ) / √(N : ℝ) ≤ 1 / wdScaleR := by
    set S_N := Nat.sqrt N
    have hS_gt : √(N : ℝ) ≤ (S_N : ℝ) + 1 := by
      rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
      have hlt := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N); push_cast at hlt; linarith
    have hdiv_lt : tau9 * S_N < (q + 1) * (nSub * 1000000000) :=
      calc tau9 * S_N < (nSub * 1000000000) * (q + 1) :=
            Nat.lt_mul_div_succ _ (by positivity : 0 < nSub * 1000000000)
        _ = (q + 1) * (nSub * 1000000000) := Nat.mul_comm _ _
    have hdivR : (tau9 : ℝ) * (S_N : ℝ) ≤ ((q : ℝ) + 1) * ((nSub : ℝ) * 1000000000) := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hdiv_lt.le; push_cast at hc; linarith
    have htauR : (tau9 : ℝ) ≤ 4000000000 := by exact_mod_cast htau
    have hnsubR : (nSub : ℝ) ≤ 16384 := by exact_mod_cast hnsub
    have hgap : (tau9 : ℝ) * √(N : ℝ) - (q : ℝ) * ((nSub : ℝ) * 1000000000) ≤ 20384000000000 := by
      nlinarith [mul_le_mul_of_nonneg_left hS_gt (Nat.cast_nonneg tau9)]
    have hbig : (20384000000000 : ℝ) * 1000000000000000 ≤ ((nSub : ℝ) * 1000000000) * √(N : ℝ) := by
      have h1 : (20384000000000 : ℝ) * 1000000000000000 ≤ 1000000000 * (2 : ℝ) ^ 100 := by norm_num
      have h2 : (1 : ℝ) ≤ (nSub : ℝ) := by exact_mod_cast hnsub1
      nlinarith
    rw [hB, div_sub_div _ _ (by positivity) hsqrtN_pos.ne',
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨div_nonneg (Nat.cast_nonneg q) hsqrtN_pos.le, ?_, ?_⟩
  · refine hq_hi.trans (hhPt_hi.trans ?_)
    exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : hPt + 1 ≤ 2 + hPt)) hB_pos.le
  · rw [abs_le]
    constructor
    · linarith [hhPt_lo, hq_lo]
    · have h1 : ((hPt + 1 : ℕ) : ℝ) / wdScaleR - (hPt : ℝ) / wdScaleR = 1 / wdScaleR := by
        push_cast; ring
      linarith [hq_hi, hhPt_hi, h1]
private theorem highd_altIterCapT16_approx {d coreLen : ℕ} {hb : List ℤ}
    {A_sub B_cap_mac : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {ε_sub ε_quant : ℝ}
    (hd : d ≤ 1024) (hhb : hb.length ≤ d) (hcore16 : 16 + coreLen ≤ d + 1)
    (hA_contr : ∀ u, vecNorm (A_sub *ᵥ u) ≤ vecNorm u)
    (hGpt : ∀ u, vecNorm (highd_ptGenMat d hb *ᵥ u) ≤ (3 / 2) * vecNorm u)
    (hεs : 0 ≤ ε_sub) (hεq : 0 ≤ ε_quant)
    (hsub_cap : ∀ v : Fin (d + 1) → ℝ, (∀ j : Fin (d + 1), coreLen ≤ j.1 → v j = 0) →
      vecNorm ((A_sub - B_cap_mac) *ᵥ v) ≤ ε_sub * vecNorm v)
    (hquant_cap : ∀ v : Fin (d + 1) → ℝ,
      vecNorm ((B_cap_mac - taylor16OfMat (highd_ptGenMat d hb)) *ᵥ v) ≤ ε_quant * vecNorm v) :
    let ε_step := (297 / 2) / wdScaleR + (11 / 10) * (ε_sub + ε_quant)
    ∀ (k : ℕ) (vec : List ℤ) (uExact : Fin (d + 1) → ℝ) (err : ℝ), vec.length ≤ coreLen →
      vecNorm uExact ≤ 1 →
      0 ≤ err →
      err + (k : ℝ) * ε_step ≤ 1 / 10 →
      vecNorm (highd_listToOrbVec d vec - uExact) ≤ err →
      altIterCapT16 k coreLen hb vec ≠ [] →
      (altIterCapT16 k coreLen hb vec).length ≤ coreLen ∧
        vecNorm (highd_listToOrbVec d (altIterCapT16 k coreLen hb vec) -
          (A_sub ^ k) *ᵥ uExact) ≤ err + (k : ℝ) * ε_step := by
  intro ε_step k
  have hε_step_nn : 0 ≤ ε_step := by dsimp [ε_step]; unfold wdScaleR wdScale; positivity
  induction k with
  | zero =>
    intro vec uExact err hlen _ _ _ herr _
    simpa [altIterCapT16, pow_zero, Matrix.one_mulVec] using ⟨hlen, herr⟩
  | succ k ih =>
    intro vec uExact err hlen hu1 herr0 htot herr hne
    set cur := hornerT16SlideStep (Nat.add 16 coreLen) hb vec
    cases hdrop : altCheckDropZero coreLen cur with
    | false =>
      unfold altIterCapT16 at hne; simp only [highdForceList_eq] at hne
      change (cond (altCheckDropZero coreLen cur) _ []) ≠ [] at hne
      rw [hdrop, highd_cond_false] at hne; exact False.elim (hne rfl)
    | true =>
      unfold altIterCapT16 at hne ⊢; simp only [highdForceList_eq] at hne ⊢
      change (cond (altCheckDropZero coreLen cur) _ []) ≠ [] at hne
      rw [hdrop, highd_cond_true] at hne
      change (cond (altCheckDropZero coreLen cur) _ []).length ≤ coreLen ∧
        vecNorm (highd_listToOrbVec d (cond (altCheckDropZero coreLen cur) _ []) -
          (A_sub ^ (k + 1)) *ᵥ uExact) ≤ err + ((k + 1 : ℕ) : ℝ) * ε_step
      rw [hdrop, highd_cond_true]
      set trimmed := altTakeMaxInt coreLen cur
      have htrim_len : trimmed.length ≤ coreLen := highd_altTakeMaxInt_length coreLen cur
      have htrim_vec : highd_listToOrbVec d trimmed = highd_listToOrbVec d cur := by
        ext a
        dsimp only [highd_listToOrbVec, trimmed]
        rw [highd_altTakeMaxInt_getD_of_dropZero coreLen cur hdrop]
      set vInt := highd_listToOrbVec d vec
      have hvInt_supp : ∀ j : Fin (d + 1), coreLen ≤ j.1 → vInt j = 0 := by
        intro j hj
        dsimp [vInt, highd_listToOrbVec]
        rw [highd_getD_eq_zero_of_le vec j.1 (hlen.trans hj), Int.cast_zero, zero_div]
      have herr_le10 : err ≤ 1 / 10 := by
        have hk_nn : 0 ≤ ((k + 1 : ℕ) : ℝ) * ε_step := mul_nonneg (Nat.cast_nonneg _) hε_step_nn
        linarith
      have hvInt_norm : vecNorm vInt ≤ 11 / 10 := by
        have hsplit_v : vInt = uExact + (vInt - uExact) := by ext i; simp
        rw [hsplit_v]; linarith [vecNorm_add_le uExact (vInt - uExact)]
      set B_pt := taylor16OfMat (highd_ptGenMat d hb)
      have hhorner : vecNorm (highd_listToOrbVec d cur - B_pt *ᵥ vInt) ≤ (297 / 2) / wdScaleR :=
        (highd_hornerT16SlideStep_approx hd hhb hcore16
          (hlen.trans (Nat.le_add_left _ _)) (Or.inr (by omega : vec.length + 16 ≤ 16 + coreLen))
          hGpt).2
      clear_value cur trimmed
      have hq_step : vecNorm ((B_pt - B_cap_mac) *ᵥ vInt) ≤ (11 / 10) * ε_quant := by
        have hneg : (B_pt - B_cap_mac) *ᵥ vInt = -((B_cap_mac - B_pt) *ᵥ vInt) := by
          ext i; simp [Matrix.sub_mulVec]
        rw [hneg, vecNorm_neg]
        calc vecNorm ((B_cap_mac - B_pt) *ᵥ vInt)
            ≤ ε_quant * vecNorm vInt := hquant_cap vInt
          _ ≤ ε_quant * (11 / 10) := mul_le_mul_of_nonneg_left hvInt_norm hεq
          _ = (11 / 10) * ε_quant := by ring
      have hs_step : vecNorm ((B_cap_mac - A_sub) *ᵥ vInt) ≤ (11 / 10) * ε_sub := by
        have hneg : (B_cap_mac - A_sub) *ᵥ vInt = -((A_sub - B_cap_mac) *ᵥ vInt) := by
          ext i; simp [Matrix.sub_mulVec]
        rw [hneg, vecNorm_neg]
        calc vecNorm ((A_sub - B_cap_mac) *ᵥ vInt)
            ≤ ε_sub * vecNorm vInt := hsub_cap vInt hvInt_supp
          _ ≤ ε_sub * (11 / 10) := mul_le_mul_of_nonneg_left hvInt_norm hεs
          _ = (11 / 10) * ε_sub := by ring
      have hprop : vecNorm (A_sub *ᵥ (vInt - uExact)) ≤ err := (hA_contr _).trans herr
      have hstep_err : vecNorm (highd_listToOrbVec d trimmed - A_sub *ᵥ uExact) ≤ err + ε_step := by
        rw [htrim_vec]; have hdecomp : highd_listToOrbVec d cur - A_sub *ᵥ uExact =
            (highd_listToOrbVec d cur - B_pt *ᵥ vInt) + ((B_pt - B_cap_mac) *ᵥ vInt +
              ((B_cap_mac - A_sub) *ᵥ vInt + A_sub *ᵥ (vInt - uExact))) := by
          ext i
          simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply]; ring
        rw [hdecomp]; have htri1 := vecNorm_add_le (highd_listToOrbVec d cur - B_pt *ᵥ vInt)
          ((B_pt - B_cap_mac) *ᵥ vInt + ((B_cap_mac - A_sub) *ᵥ vInt + A_sub *ᵥ (vInt - uExact)))
        have htri2 := vecNorm_add_le ((B_pt - B_cap_mac) *ᵥ vInt)
          ((B_cap_mac - A_sub) *ᵥ vInt + A_sub *ᵥ (vInt - uExact))
        have htri3 := vecNorm_add_le ((B_cap_mac - A_sub) *ᵥ vInt) (A_sub *ᵥ (vInt - uExact))
        dsimp only [ε_step]; linarith [hhorner, hq_step, hs_step, hprop, htri1, htri2, htri3]
      have htot' : (err + ε_step) + (k : ℝ) * ε_step ≤ 1 / 10 := by push_cast at htot; linarith
      obtain ⟨hfin_len, hfin_err⟩ := ih trimmed (A_sub *ᵥ uExact) (err + ε_step)
        htrim_len ((hA_contr uExact).trans hu1) (add_nonneg herr0 hε_step_nn)
        htot' hstep_err hne
      refine ⟨hfin_len, ?_⟩
      have hpow_assoc : (A_sub ^ (k + 1)) *ᵥ uExact = (A_sub ^ k) *ᵥ (A_sub *ᵥ uExact) := by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
      rw [hpow_assoc]
      calc vecNorm (highd_listToOrbVec d (altIterCapT16 k coreLen hb trimmed) -
              (A_sub ^ k) *ᵥ (A_sub *ᵥ uExact))
          ≤ (err + ε_step) + (k : ℝ) * ε_step := hfin_err
        _ = err + ((k + 1 : ℕ) : ℝ) * ε_step := by push_cast; ring
/- ## Section 4: Unified Soundness of `altEvalRowHighDLo12` (`dCap = d` and `48 ≤ dCap < d`) -/
private theorem highd_altVecTailToLo12_length (pad : ℕ) :
    ∀ zs : List ℤ, (altVecTailToLo12 pad zs).length = zs.length
  | [] => rfl
  | _ :: zs => by
    unfold altVecTailToLo12; rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact congrArg Nat.succ (highd_altVecTailToLo12_length pad zs)
private theorem highd_altVecTailToLo12_getD (pad : ℕ) : ∀ (zs : List ℤ) (j : ℕ), j < zs.length →
      (altVecTailToLo12 pad zs).getD j 0 =
        ((((Int.natAbs (zs.getD j 0) - pad) * (Int.natAbs (zs.getD j 0) - pad)) /
          wdScale) / 1000) - 1
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, _ => by
    unfold altVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq, highd_primIntNatAbs_eq]; rfl
  | _ :: zs, j + 1, hj => by
    unfold altVecTailToLo12; rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact highd_altVecTailToLo12_getD pad zs j (by simp at hj; omega)
private theorem highd_cast_natAbs_eq_abs (z : ℤ) : ((Int.natAbs z : ℕ) : ℝ) = |(z : ℝ)| := by
  cases z with
  | ofNat n =>
    change ((n : ℕ) : ℝ) = |((n : ℕ) : ℝ)|
    exact (abs_of_nonneg (Nat.cast_nonneg n)).symm
  | negSucc n =>
    have hneg : (Int.negSucc n : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hneg, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; rfl
private theorem highd_altVecTailToLo12_entry_le {pad : ℕ} {z : ℤ} {u : ℝ}
    (herr : |u - (z : ℝ) / wdScaleR| ≤ (pad : ℝ) / wdScaleR) :
    (((((Int.natAbs z - pad) * (Int.natAbs z - pad)) / wdScale) / 1000 - 1 : ℕ) : ℝ) /
        1000000000000 ≤ u ^ 2 := by
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  set aLo : ℕ := Int.natAbs z - pad
  set pLo15 : ℕ := (aLo * aLo) / wdScale
  set pLo12 : ℕ := pLo15 / 1000
  set out : ℕ := pLo12 - 1
  have haLo_le : (aLo : ℝ) / wdScaleR ≤ |u| := by
    by_cases hle : Int.natAbs z ≤ pad
    · have ha0 : aLo = 0 := Nat.sub_eq_zero_of_le hle; rw [ha0, Nat.cast_zero, zero_div]
      exact abs_nonneg u
    · have hgt : pad < Int.natAbs z := by omega
      have haR : (aLo : ℝ) = |(z : ℝ)| - (pad : ℝ) := by
        dsimp [aLo]; rw [Nat.cast_sub hgt.le, highd_cast_natAbs_eq_abs]
      have habs := abs_le.mp herr
      have hu_ge : |(z : ℝ)| / wdScaleR - (pad : ℝ) / wdScaleR ≤ |u| := by
        rcases le_total 0 (z : ℝ) with hz0 | hz0
        · rw [abs_of_nonneg hz0]
          have h1 : u ≤ |u| := le_abs_self u
          linarith [habs.1]
        · rw [abs_of_nonpos hz0]
          have h1 : -u ≤ |u| := neg_le_abs u
          have hneg_div : -(z : ℝ) / wdScaleR = -((z : ℝ) / wdScaleR) := neg_div _ _
          linarith [habs.2, hneg_div]
      rwa [haR, sub_div]
  have hsq_le : ((aLo : ℝ) / wdScaleR) ^ 2 ≤ u ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) haLo_le 2; rwa [sq_abs] at h1
  have hout_le : out ≤ pLo12 := Nat.sub_le _ _
  have hp12_le : pLo12 * 1000 ≤ pLo15 := Nat.div_mul_le_self _ _
  have hp15_le : pLo15 * wdScale ≤ aLo * aLo := Nat.div_mul_le_self _ _
  have hchain_nat : (out * 1000) * wdScale ≤ aLo * aLo := by
    calc (out * 1000) * wdScale
        ≤ (pLo12 * 1000) * wdScale := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hout_le)
      _ ≤ pLo15 * wdScale := Nat.mul_le_mul_right _ hp12_le
      _ ≤ aLo * aLo := hp15_le
  have hchainR : ((out : ℝ) * 1000) * wdScaleR ≤ (aLo : ℝ) ^ 2 := by
    have hc : (((out * 1000) * wdScale : ℕ) : ℝ) ≤ ((aLo * aLo : ℕ) : ℝ) := by
      exact_mod_cast hchain_nat
    unfold wdScaleR
    calc ((out : ℝ) * 1000) * (wdScale : ℝ)
        = (((out * 1000) * wdScale : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((aLo * aLo : ℕ) : ℝ) := hc
      _ = (aLo : ℝ) ^ 2 := by push_cast; ring
  have hdiv_le : (out : ℝ) / 1000000000000 ≤ ((aLo : ℝ) / wdScaleR) ^ 2 := by
    rw [div_pow, hB_eq, div_le_div_iff₀ (by norm_num) (by norm_num)]; rw [hB_eq] at hchainR
    linarith
  exact hdiv_le.trans hsq_le
private theorem highd_ptGenMat_bounds {m r hPt dCap bCapCeil hgHi15 : ℕ}
    {h_real B_cap : ℝ} {hbPt : List ℤ} (hhPt_le4 : (hPt : ℝ) / wdScaleR ≤ 4) (hh_nn : 0 ≤ h_real)
    (hh_diff : |h_real - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR) (hBc_nn : 0 ≤ B_cap)
    (hhBc_32 : h_real * B_cap ≤ 3 / 2)
    (hhBc_mul_ge : (((2 + hPt : ℕ) : ℝ) / wdScaleR) * B_cap ≤ (hgHi15 : ℝ) / wdScaleR)
    (hhg_32 : (hgHi15 : ℝ) / wdScaleR ≤ 3 / 2) (hbCapCeil_ge : B_cap ≤ (bCapCeil : ℝ))
    (hcoupl_cap : ∀ j < dCap, |dAltCoupling m r j| ≤ (1 / 2) * B_cap)
    (htight : altCheckHbTight m r 0 dCap = true) (hhb_len : hbPt.length = dCap)
    (hhb_get : ∀ j < dCap, hbPt.getD j 0 =
        (((hPt * (altIsqrt15 (4 * (j + 1) * (m - j) * (r - j))).1) / wdScale : ℕ) : ℤ)) :
    (∀ u : Fin (min m r + 1) → ℝ,
      vecNorm (tridiagCapMat (min m r) dCap (dAltCoupling m r) *ᵥ u) ≤ B_cap * vecNorm u) ∧
    (∀ u : Fin (min m r + 1) → ℝ,
      vecNorm (highd_ptGenMat (min m r) hbPt *ᵥ u) ≤ (3 / 2) * vecNorm u) ∧
    (∀ u : Fin (min m r + 1) → ℝ,
      vecNorm ((taylor16Mat h_real (tridiagCapMat (min m r) dCap (dAltCoupling m r)) -
        taylor16OfMat (highd_ptGenMat (min m r) hbPt)) *ᵥ u) ≤
        ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) * vecNorm u) := by
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  set d := min m r
  set Gc := tridiagCapMat d dCap (dAltCoupling m r)
  have hGc_op (u : Fin (d + 1) → ℝ) : vecNorm (Gc *ᵥ u) ≤ B_cap * vecNorm u := by
    have hb (j : ℕ) (_hj : j < d) :
        |(if j < dCap then dAltCoupling m r j else 0)| ≤ (1 / 2) * B_cap := by
      by_cases hjc : j < dCap
      · rw [ite_eq_left hjc]; exact hcoupl_cap j hjc
      · rw [ite_eq_right hjc, abs_zero]; exact mul_nonneg (by norm_num) hBc_nn
    simpa [Gc, tridiagCapMat, ← mul_assoc] using
      vecNorm_tridiagSkewMat_mulVec_le (mul_nonneg (by norm_num) hBc_nn) hb u
  have hGpt_op (u : Fin (d + 1) → ℝ) :
      vecNorm (highd_ptGenMat d hbPt *ᵥ u) ≤ (3 / 2) * vecNorm u := by
    have hb_le (j : ℕ) (_hj : j < d) : |(hbPt.getD j 0 : ℝ) / wdScaleR| ≤ 3 / 4 := by
      by_cases hjc : j < dCap
      · have hget' := hhb_get j hjc
        set rad := 4 * (j + 1) * (m - j) * (r - j)
        set sq := (altIsqrt15 rad).1
        have hget_sq : hbPt.getD j 0 = (((hPt * sq) / wdScale : ℕ) : ℤ) := hget'
        have hsq_le_c : (sq : ℝ) / wdScaleR ≤ dAltCoupling m r j := (altIsqrt15_sound rad).1
        clear_value rad sq
        set qProd := (hPt * sq) / wdScale
        have hget_q : hbPt.getD j 0 = (qProd : ℤ) := hget_sq
        have hnat : qProd * wdScale ≤ hPt * sq := Nat.div_mul_le_self _ _
        have hR : (qProd : ℝ) * wdScaleR ≤ (hPt : ℝ) * (sq : ℝ) := by
          unfold wdScaleR; exact_mod_cast hnat
        clear_value qProd; clear hget' hget_sq
        rw [hget_q, Int.cast_natCast, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hB_pos.le)]
        have h1 : (qProd : ℝ) / wdScaleR ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) := by
          rw [div_mul_div_comm, div_le_div_iff₀ hB_pos (mul_pos hB_pos hB_pos),
            show (qProd : ℝ) * (wdScaleR * wdScaleR) = ((qProd : ℝ) * wdScaleR) * wdScaleR by ring]
          exact mul_le_mul_of_nonneg_right hR hB_pos.le
        have hc_le : dAltCoupling m r j ≤ (1 / 2) * B_cap :=
          (le_abs_self _).trans (hcoupl_cap j hjc)
        have hhPt_le : (hPt : ℝ) / wdScaleR ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR :=
          div_le_div_of_nonneg_right (by exact_mod_cast (by omega : hPt ≤ 2 + hPt)) hB_pos.le
        calc (qProd : ℝ) / wdScaleR
            ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) := h1
          _ ≤ (((2 + hPt : ℕ) : ℝ) / wdScaleR) * ((1 / 2) * B_cap) :=
            mul_le_mul hhPt_le (hsq_le_c.trans hc_le) (div_nonneg (Nat.cast_nonneg _) hB_pos.le)
              (div_nonneg (Nat.cast_nonneg _) hB_pos.le)
          _ = (1 / 2) * ((((2 + hPt : ℕ) : ℝ) / wdScaleR) * B_cap) := by ring
          _ ≤ (1 / 2) * ((hgHi15 : ℝ) / wdScaleR) :=
            mul_le_mul_of_nonneg_left hhBc_mul_ge (by norm_num)
          _ ≤ (1 / 2) * (3 / 2) := mul_le_mul_of_nonneg_left hhg_32 (by norm_num)
          _ = 3 / 4 := by norm_num
      · rw [highd_getD_eq_zero_of_le hbPt j (by omega)]; simp; norm_num
    have h := vecNorm_tridiagSkewMat_mulVec_le (by norm_num : (0 : ℝ) ≤ 3 / 4) hb_le u
    refine (by simpa [highd_ptGenMat] using h :
      vecNorm (highd_ptGenMat d hbPt *ᵥ u) ≤ (2 * (3 / 4 : ℝ)) * vecNorm u).trans (le_of_eq ?_)
    ring
  have hGc_diff_op (u : Fin (d + 1) → ℝ) : vecNorm ((h_real • Gc - highd_ptGenMat d hbPt) *ᵥ u) ≤
        (((bCapCeil : ℝ) + 10) / wdScaleR) * vecNorm u := by
    have hsub_mat : h_real • Gc - highd_ptGenMat d hbPt = tridiagSkewMat d (fun j ↦
          h_real * (if j < dCap then dAltCoupling m r j else 0) - (hbPt.getD j 0 : ℝ) / wdScaleR) :=
      tridiagSkewMat_smul_sub d h_real _ _
    rw [hsub_mat]; have hcoupl_diff (j : ℕ) (_hj : j < d) :
        |h_real * (if j < dCap then dAltCoupling m r j else 0) - (hbPt.getD j 0 : ℝ) / wdScaleR| ≤
          ((1 / 2 : ℝ) * (bCapCeil : ℝ) + 5) / wdScaleR := by
      by_cases hjc : j < dCap
      · rw [ite_eq_left hjc]; have hget' := hhb_get j hjc
        set rad := 4 * (j + 1) * (m - j) * (r - j)
        set sq := (altIsqrt15 rad).1
        have hget_sq : hbPt.getD j 0 = (((hPt * sq) / wdScale : ℕ) : ℤ) := hget'
        have hc_nn : 0 ≤ dAltCoupling m r j := by unfold dAltCoupling; positivity
        have hc_le : dAltCoupling m r j ≤ (1 / 2) * (bCapCeil : ℝ) :=
          ((le_abs_self _).trans (hcoupl_cap j hjc)).trans
            (mul_le_mul_of_nonneg_left hbCapCeil_ge (by norm_num))
        have htight_j : (altIsqrt15 rad).2 ≤ sq + 1 := by
          simpa [rad, sq] using highd_altCheckHbTight_sound m r dCap 0 htight j hjc
        have hsq_sound := altIsqrt15_sound rad
        set sqHi := (altIsqrt15 rad).2
        have htight_j' : sqHi ≤ sq + 1 := htight_j
        have hsq_lo : (sq : ℝ) / wdScaleR ≤ dAltCoupling m r j := hsq_sound.1
        have hsq_hi : dAltCoupling m r j ≤ (sqHi : ℝ) / wdScaleR := hsq_sound.2
        clear_value rad sq sqHi
        set qProd := (hPt * sq) / wdScale
        have hget_q : hbPt.getD j 0 = (qProd : ℤ) := hget_sq
        have hlo_nat : qProd * wdScale ≤ hPt * sq := Nat.div_mul_le_self _ _
        have hhi_nat : hPt * sq < (qProd + 1) * wdScale :=
          calc hPt * sq < wdScale * (qProd + 1) :=
                Nat.lt_mul_div_succ _ (by unfold wdScale; positivity : 0 < wdScale)
            _ = (qProd + 1) * wdScale := Nat.mul_comm _ _
        have hloR : (qProd : ℝ) * wdScaleR ≤ (hPt : ℝ) * (sq : ℝ) := by
          unfold wdScaleR; exact_mod_cast hlo_nat
        have hhiR : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd + 1 : ℕ) : ℝ) * wdScaleR := by
          unfold wdScaleR; exact_mod_cast hhi_nat.le
        clear_value qProd; clear hget' hget_sq
        rw [hget_q, Int.cast_natCast]
        have hsq_diff : |dAltCoupling m r j - (sq : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
          have hlo : (sq : ℝ) / wdScaleR ≤ dAltCoupling m r j := hsq_lo
          have hhi : dAltCoupling m r j ≤ ((sq + 1 : ℕ) : ℝ) / wdScaleR :=
            hsq_hi.trans (div_le_div_of_nonneg_right (by exact_mod_cast htight_j') hB_pos.le)
          rw [abs_of_nonneg (by linarith)]
          have h1 : ((sq + 1 : ℕ) : ℝ) / wdScaleR - (sq : ℝ) / wdScaleR = 1 / wdScaleR := by
            push_cast; ring
          linarith
        have hdiv_err : |((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) -
            (qProd : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
          have hdiff_nn : 0 ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) -
              (qProd : ℝ) / wdScaleR := by
            rw [div_mul_div_comm, sub_nonneg, div_le_div_iff₀ hB_pos (mul_pos hB_pos hB_pos),
              show (qProd : ℝ) * (wdScaleR * wdScaleR) =
                ((qProd : ℝ) * wdScaleR) * wdScaleR by ring]
            exact mul_le_mul_of_nonneg_right hloR hB_pos.le
          rw [abs_of_nonneg hdiff_nn]
          have h1 : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd : ℝ) + 1) * wdScaleR := by
            simpa only [Nat.cast_add, Nat.cast_one] using hhiR
          calc ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR
              = ((hPt : ℝ) * (sq : ℝ)) / (wdScaleR * wdScaleR) - (qProd : ℝ) / wdScaleR :=
                  by rw [div_mul_div_comm]
            _ ≤ (((qProd : ℝ) + 1) * wdScaleR) / (wdScaleR * wdScaleR) - (qProd : ℝ) / wdScaleR :=
                  sub_le_sub_right
                    (div_le_div_of_nonneg_right h1 (mul_nonneg hB_pos.le hB_pos.le)) _
            _ = 1 / wdScaleR := by field_simp [hB_pos.ne']; ring
        set e1 : ℝ := (h_real - (hPt : ℝ) / wdScaleR) * dAltCoupling m r j
        set e2 : ℝ := ((hPt : ℝ) / wdScaleR) * (dAltCoupling m r j - (sq : ℝ) / wdScaleR)
        set e3 : ℝ := ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR
        have hsplit3 : h_real * dAltCoupling m r j - (qProd : ℝ) / wdScaleR = e1 + e2 + e3 := by
          dsimp [e1, e2, e3]; ring
        rw [hsplit3]
        have ht1 : |e1| ≤ (1 / wdScaleR) * ((1 / 2) * (bCapCeil : ℝ)) := by
          dsimp [e1]; rw [abs_mul, abs_of_nonneg hc_nn]
          exact mul_le_mul hh_diff hc_le hc_nn (div_nonneg (by norm_num) hB_pos.le)
        have ht2 : |e2| ≤ 4 * (1 / wdScaleR) := by
          dsimp [e2]; rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hB_pos.le)]
          exact mul_le_mul hhPt_le4 hsq_diff (abs_nonneg _) (by norm_num)
        have habs12 : |e1 + e2| ≤ |e1| + |e2| := abs_add_le e1 e2
        have habs123 : |e1 + e2 + e3| ≤ |e1 + e2| + |e3| := abs_add_le (e1 + e2) e3
        have hgoal_sum :
            (1 / wdScaleR) * ((1 / 2) * (bCapCeil : ℝ)) + 4 * (1 / wdScaleR) + 1 / wdScaleR =
              ((1 / 2 : ℝ) * (bCapCeil : ℝ) + 5) / wdScaleR := by ring
        linarith [habs12, habs123, ht1, ht2, hdiv_err, hgoal_sum]
      · rw [ite_eq_right hjc, highd_getD_eq_zero_of_le hbPt j (by omega)]
        simp only [mul_zero, Int.cast_zero, zero_div, sub_self, abs_zero, one_div]
        exact div_nonneg (by positivity) hB_pos.le
    have h := vecNorm_tridiagSkewMat_mulVec_le (div_nonneg (by positivity) hB_pos.le) hcoupl_diff u
    refine h.trans (le_of_eq ?_); ring
  have hhGc_32 (u : Fin (d + 1) → ℝ) : vecNorm ((h_real • Gc) *ᵥ u) ≤ (3 / 2) * vecNorm u := by
    rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg hh_nn]
    calc h_real * vecNorm (Gc *ᵥ u)
        ≤ h_real * (B_cap * vecNorm u) := mul_le_mul_of_nonneg_left (hGc_op u) hh_nn
      _ = (h_real * B_cap) * vecNorm u := by ring
      _ ≤ (3 / 2) * vecNorm u := mul_le_mul_of_nonneg_right hhBc_32 (vecNorm_nonneg u)
  have hquant_mac (u : Fin (d + 1) → ℝ) :
      vecNorm ((taylor16Mat h_real Gc - taylor16OfMat (highd_ptGenMat d hbPt)) *ᵥ u) ≤
        ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) * vecNorm u := by
    have h := vecNorm_taylor16OfMat_sub_mulVec_le hhGc_32 hGpt_op
      (div_nonneg (by positivity) hB_pos.le) hGc_diff_op u
    refine h.trans (le_of_eq ?_); ring
  exact ⟨hGc_op, hGpt_op, hquant_mac⟩
private theorem highd_evalRow_branch_full
    {m r tau9 nSub dCap K q truncPad15 bCapCeil totalPad15 w : ℕ}
    {η B_cap : ℝ} {hbPt vecInit : List ℤ}
    {uWalk e0 : Fin (orbDim m r) → ℝ}
    (hw1 : 1 ≤ w)
    (hw_lt : w - 1 < (altEvalRowHighDLo12 m r tau9 nSub dCap).length)
    (hd_hi : min m r ≤ 1024)
    (hdCap_eq_d : dCap = min m r)
    (hK_eq : K = nSub * q)
    (hη_nn : 0 ≤ η) (hBc_nn : 0 ≤ B_cap)
    (hηBf1 : η * dAltGenNormBound m r ≤ 1)
    (hhBc_32 : ((q : ℝ) * η) * B_cap ≤ 3 / 2)
    (he0_norm : vecNorm e0 = 1)
    (hvecInit_len : vecInit.length ≤ min m r + 1)
    (hvecInit_eq : highd_listToOrbVec (min m r) vecInit = e0)
    (hhb_le_d : hbPt.length ≤ min m r)
    (hGc_op : ∀ u : Fin (min m r + 1) → ℝ,
      vecNorm (tridiagCapMat (min m r) dCap (dAltCoupling m r) *ᵥ u) ≤ B_cap * vecNorm u)
    (hGpt_op : ∀ u : Fin (min m r + 1) → ℝ,
      vecNorm (highd_ptGenMat (min m r) hbPt *ᵥ u) ≤ (3 / 2) * vecNorm u)
    (hquant_mac : ∀ u : Fin (min m r + 1) → ℝ,
      vecNorm ((taylor16Mat ((q : ℝ) * η) (tridiagCapMat (min m r) dCap (dAltCoupling m r)) -
        taylor16OfMat (highd_ptGenMat (min m r) hbPt)) *ᵥ u) ≤
        ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) * vecNorm u)
    (hterm_cont : vecNorm (uWalk - ((taylor16Mat η (dAltGenMat m r)) ^ K) *ᵥ e0) ≤ 2 / wdScaleR)
    (htrunc_ge : (nSub : ℝ) * ((((q : ℝ) * η) * B_cap) ^ 17 / 300000000000000) ≤
      (truncPad15 : ℝ) / wdScaleR)
    (hpadR_eq : (totalPad15 : ℝ) = (truncPad15 : ℝ) +
      ((nSub : ℝ) * (10 * (bCapCeil : ℝ) + 256) + 256))
    (heval_full : altEvalRowHighDLo12 m r tau9 nSub dCap =
      (match altPadRightInts (min m r + 1) (altIterFullT16 nSub (min m r + 1) hbPt vecInit) with
       | [] => []
       | _ :: tail => altVecTailToLo12 totalPad15 tail)) :
    ∃ wFin : Fin (orbDim m r), wFin.1 = w ∧
      (((altEvalRowHighDLo12 m r tau9 nSub dCap).getD (w - 1) 0 : ℝ) / 1000000000000) ≤
        (uWalk wFin) ^ 2 := by
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  have hBf_nn : 0 ≤ dAltGenNormBound m r := by unfold dAltGenNormBound; positivity
  set d := min m r
  set h_real : ℝ := (q : ℝ) * η
  have hh_nn : 0 ≤ h_real := mul_nonneg (Nat.cast_nonneg _) hη_nn
  set G := dAltGenMat m r
  set Gc := tridiagCapMat d dCap (dAltCoupling m r)
  have hGc_eq_G : Gc = G := by
    dsimp [Gc, G, tridiagCapMat, dAltGenMat]
    ext a b
    simp only [tridiagSkewMat, Matrix.of_apply]
    by_cases h1 : a.1 = b.1 + 1
    · have hlt : b.1 < dCap := by rw [hdCap_eq_d]; have := a.2; omega
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left hlt]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : b.1 = a.1 + 1
      · have hlt : a.1 < dCap := by rw [hdCap_eq_d]; have := b.2; omega
        rw [ite_eq_left h2, ite_eq_left h2, ite_eq_left hlt]
      · rw [ite_eq_right h2, ite_eq_right h2]
  set A_sub := (taylor16Mat η G) ^ q
  have hA_sub_contr (u : Fin (d + 1) → ℝ) : vecNorm (A_sub *ᵥ u) ≤ vecNorm u := by
    have h1 (x : Fin (d + 1) → ℝ) : vecNorm (taylor16Mat η G *ᵥ x) ≤ 1 * vecNorm x := by
      rw [one_mul]; exact vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose m r) hη_nn hBf_nn
        (vecNorm_dAltGenMat_mulVec_le m r) (by linarith) x
    simpa [A_sub] using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) h1 q u
  have hA_pow : A_sub ^ nSub = (taylor16Mat η G) ^ K := by
    dsimp only [A_sub]; rw [hK_eq, mul_comm nSub q, pow_mul]
  set B_cap_mac := taylor16Mat h_real Gc
  set B_pt := taylor16OfMat (highd_ptGenMat d hbPt)
  have hB_mac_contr (u : Fin (d + 1) → ℝ) : vecNorm (B_cap_mac *ᵥ u) ≤ vecNorm u :=
    vecNorm_taylor16Mat_mulVec_le (tridiagSkewMat_transpose d _) hh_nn hBc_nn hGc_op hhBc_32 u
  have hB_pt_contr (u : Fin (d + 1) → ℝ) : vecNorm (B_pt *ᵥ u) ≤ vecNorm u :=
    vecNorm_taylor16OfMat_mulVec_le (tridiagSkewMat_transpose d _) hGpt_op u
  have hmac_diff (u : Fin (d + 1) → ℝ) : vecNorm ((A_sub - B_cap_mac) *ᵥ u) ≤
         ((h_real * B_cap) ^ 17 / 300000000000000) * vecNorm u := by
    have hG_op_cap (x : Fin (d + 1) → ℝ) : vecNorm (G *ᵥ x) ≤ B_cap * vecNorm x := by
      rw [← hGc_eq_G]; exact hGc_op x
    have hB_eq_G : B_cap_mac = taylor16Mat ((q : ℝ) * η) G := by
      dsimp only [B_cap_mac, h_real]; rw [hGc_eq_G]
    change vecNorm (((taylor16Mat η G) ^ q - B_cap_mac) *ᵥ u) ≤
      ((h_real * B_cap) ^ 17 / 300000000000000) * vecNorm u
    rw [hB_eq_G]; exact vecNorm_taylor16Mat_substep_le (dAltGenMat_transpose m r) hη_nn hBc_nn
      hG_op_cap q hhBc_32 u
  clear_value B_cap_mac A_sub Gc
  have hterm2 : vecNorm (((taylor16Mat η G) ^ K) *ᵥ e0 - (B_cap_mac ^ nSub) *ᵥ e0) ≤
      (truncPad15 : ℝ) / wdScaleR := by
    rw [← hA_pow]; have htel := vecNorm_pow_mulVec_sub_le hA_sub_contr hB_mac_contr
      (div_nonneg (pow_nonneg (mul_nonneg hh_nn hBc_nn) 17) (by norm_num))
      hmac_diff nSub e0 e0
    rw [sub_self, vecNorm_zero, zero_add, he0_norm, mul_one] at htel; exact htel.trans htrunc_ge
  have hterm3 : vecNorm ((B_cap_mac ^ nSub) *ᵥ e0 - (B_pt ^ nSub) *ᵥ e0) ≤
      ((nSub : ℝ) * (5 * (bCapCeil : ℝ) + 50)) / wdScaleR := by
    have htel := vecNorm_pow_mulVec_sub_le hB_mac_contr hB_pt_contr
      (div_nonneg (by positivity) hB_pos.le)
      hquant_mac nSub e0 e0
    rw [sub_self, vecNorm_zero, zero_add, he0_norm, mul_one] at htel
    refine htel.trans (le_of_eq ?_); ring
  set vecFinal := altIterFullT16 nSub (d + 1) hbPt vecInit
  obtain ⟨hvf_len, hterm4_raw⟩ :=
    highd_altIterFullT16_approx hd_hi hhb_le_d hGpt_op nSub vecInit hvecInit_len
  rw [hvecInit_eq] at hterm4_raw
  have hterm4 : vecNorm ((B_pt ^ nSub) *ᵥ e0 - highd_listToOrbVec d vecFinal) ≤
      ((297 / 2) * (nSub : ℝ)) / wdScaleR := by
    rw [← vecNorm_neg, neg_sub]; exact hterm4_raw
  clear_value B_pt
  set padded := altPadRightInts (d + 1) vecFinal
  have hpad_len : padded.length = d + 1 := highd_altPadRightInts_length (d + 1) vecFinal
  have hpad_vec : highd_listToOrbVec d padded = highd_listToOrbVec d vecFinal := by
    ext a
    dsimp only [highd_listToOrbVec, padded]
    rw [highd_altPadRightInts_getD (d + 1) vecFinal hvf_len]
  set uInt := highd_listToOrbVec d padded
  have htotal_norm : vecNorm (uWalk - uInt) ≤ (totalPad15 : ℝ) / wdScaleR := by
    rw [hpad_vec]
    set v1 : Fin (orbDim m r) → ℝ := uWalk - ((taylor16Mat η G) ^ K) *ᵥ e0
    set v2 : Fin (orbDim m r) → ℝ := ((taylor16Mat η G) ^ K) *ᵥ e0 - (B_cap_mac ^ nSub) *ᵥ e0
    set v3 : Fin (orbDim m r) → ℝ := (B_cap_mac ^ nSub) *ᵥ e0 - (B_pt ^ nSub) *ᵥ e0
    set v4 : Fin (orbDim m r) → ℝ := (B_pt ^ nSub) *ᵥ e0 - highd_listToOrbVec d vecFinal
    have hdecomp : uWalk - highd_listToOrbVec d vecFinal = v1 + v2 + v3 + v4 := by
      dsimp [v1, v2, v3, v4]
      ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [hdecomp]; have htri1 := vecNorm_add_le v1 v2; have htri2 := vecNorm_add_le (v1 + v2) v3
    have htri3 := vecNorm_add_le (v1 + v2 + v3) v4
    have hsum_le : 2 / wdScaleR + (truncPad15 : ℝ) / wdScaleR +
        ((nSub : ℝ) * (5 * (bCapCeil : ℝ) + 50)) / wdScaleR +
        ((297 / 2) * (nSub : ℝ)) / wdScaleR ≤ (totalPad15 : ℝ) / wdScaleR := by
      rw [← add_div, ← add_div, ← add_div]; refine div_le_div_of_nonneg_right ?_ hB_pos.le
      rw [hpadR_eq]; have hnSub0 : (0 : ℝ) ≤ (nSub : ℝ) := Nat.cast_nonneg nSub
      have hbCap0 : (0 : ℝ) ≤ (bCapCeil : ℝ) := Nat.cast_nonneg bCapCeil
      nlinarith [hnSub0, hbCap0]
    linarith [htri1, htri2, htri3, hterm_cont, hterm2, hterm3, hterm4, hsum_le]
  rcases hp_cases : padded with _ | ⟨_, tail⟩
  · rw [hp_cases] at hpad_len; simp at hpad_len
  · have htail_len : tail.length = d := by rw [hp_cases] at hpad_len; simpa using hpad_len
    have hrow_len : (altEvalRowHighDLo12 m r tau9 nSub dCap).length = d := by
      rw [heval_full, hp_cases]
      exact (highd_altVecTailToLo12_length totalPad15 tail).trans htail_len
    have hwd : w ≤ d := by omega
    let wFin : Fin (orbDim m r) := ⟨w, by unfold orbDim; omega⟩
    have hw_coord : |uWalk wFin - uInt wFin| ≤ (totalPad15 : ℝ) / wdScaleR :=
      (abs_apply_le_vecNorm (uWalk - uInt) wFin).trans htotal_norm
    have huInt_w : uInt wFin = (tail.getD (w - 1) 0 : ℝ) / wdScaleR := by
      dsimp [uInt, highd_listToOrbVec, wFin]; rw [hp_cases]
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      simp
    rw [huInt_w] at hw_coord
    have hget_row : (altEvalRowHighDLo12 m r tau9 nSub dCap).getD (w - 1) 0 =
        ((((Int.natAbs (tail.getD (w - 1) 0) - totalPad15) *
          (Int.natAbs (tail.getD (w - 1) 0) - totalPad15)) / wdScale) / 1000) - 1 := by
      rw [heval_full, hp_cases]
      exact highd_altVecTailToLo12_getD totalPad15 tail (w - 1) (by omega)
    have hprob_lo := highd_altVecTailToLo12_entry_le hw_coord; rw [← hget_row] at hprob_lo
    exact ⟨wFin, rfl, hprob_lo⟩
private theorem highd_evalRow_branch_cap
    {n m r tau9 nSub dCap K q maxBHi15 truncPad15 bCapCeil totalPad15 w : ℕ}
    {η B_cap : ℝ} {hbPt vecInit : List ℤ}
    {uWalk e0 : Fin (orbDim m r) → ℝ}
    (hsN_ge100 : (2 : ℝ) ^ 100 ≤ √(2 ^ n : ℝ))
    (hη_def : η = 1 / √(2 ^ n : ℝ))
    (hw1 : 1 ≤ w)
    (hw_lt : w - 1 < (altEvalRowHighDLo12 m r tau9 nSub dCap).length)
    (hd_hi : min m r ≤ 1024)
    (hdCap48 : 48 ≤ dCap)
    (hdCap_lt : dCap < min m r)
    (hK_eq : K = nSub * q)
    (hq_le_sqrt : (q : ℝ) ≤ 4 * √(2 ^ n : ℝ))
    (hη_nn : 0 ≤ η)
    (hBf_hi : dAltGenNormBound m r ≤ 200000)
    (hηBf1 : η * dAltGenNormBound m r ≤ 1)
    (hBc_nn : 0 ≤ B_cap) (hBc_hi : B_cap ≤ 400002) (hηBc1 : η * B_cap ≤ 1)
    (hhBc_32 : ((q : ℝ) * η) * B_cap ≤ 3 / 2)
    (hBcap_eq_2max : B_cap = 2 * ((maxBHi15 : ℝ) / wdScaleR))
    (hmax0_le : (altIsqrt15 (4 * m * r)).2 ≤ maxBHi15)
    (hbCapCeil_ge : B_cap ≤ (bCapCeil : ℝ))
    (hcoupl_cap : ∀ j < dCap, |dAltCoupling m r j| ≤ (1 / 2) * B_cap)
    (he0_norm : vecNorm e0 = 1)
    (hvecInit_len : vecInit.length ≤ dCap - 32)
    (hvecInit_eq : highd_listToOrbVec (min m r) vecInit = e0)
    (hhb_le_d : hbPt.length ≤ min m r)
    (hGpt_op : ∀ u : Fin (min m r + 1) → ℝ,
      vecNorm (highd_ptGenMat (min m r) hbPt *ᵥ u) ≤ (3 / 2) * vecNorm u)
    (hquant_mac : ∀ u : Fin (min m r + 1) → ℝ,
      vecNorm ((taylor16Mat ((q : ℝ) * η) (tridiagCapMat (min m r) dCap (dAltCoupling m r)) -
        taylor16OfMat (highd_ptGenMat (min m r) hbPt)) *ᵥ u) ≤
        ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) * vecNorm u)
    (hterm_cont : vecNorm (uWalk - ((taylor16Mat η (dAltGenMat m r)) ^ K) *ᵥ e0) ≤ 2 / wdScaleR)
    (htrunc_ge : (nSub : ℝ) * ((((q : ℝ) * η) * B_cap) ^ 17 / 300000000000000) ≤
      (truncPad15 : ℝ) / wdScaleR)
    (hpadR_eq : (totalPad15 : ℝ) = (truncPad15 : ℝ) +
      ((nSub : ℝ) * (10 * (bCapCeil : ℝ) + 256) + 256))
    (hpad_le : totalPad15 ≤ 100000000000000)
    (hvf_ne : altIterCapT16 nSub (dCap - 32) hbPt vecInit ≠ [])
    (heval_cap : altEvalRowHighDLo12 m r tau9 nSub dCap =
      (match altPadRightInts (dCap - 32) (altIterCapT16 nSub (dCap - 32) hbPt vecInit) with
       | [] => []
       | _ :: tail => altVecTailToLo12 totalPad15 tail)) :
    ∃ wFin : Fin (orbDim m r), wFin.1 = w ∧
      (((altEvalRowHighDLo12 m r tau9 nSub dCap).getD (w - 1) 0 : ℝ) / 1000000000000) ≤
        (uWalk wFin) ^ 2 := by
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge100
  set B_full := dAltGenNormBound m r
  have hBf_nn : 0 ≤ B_full := by unfold B_full dAltGenNormBound; positivity
  set d := min m r
  set coreLen := dCap - 32
  set h_real : ℝ := (q : ℝ) * η
  have hh_nn : 0 ≤ h_real := mul_nonneg (Nat.cast_nonneg _) hη_nn
  set G := dAltGenMat m r
  set Gc := tridiagCapMat d dCap (dAltCoupling m r)
  set A_sub : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := (taylor16Mat η G) ^ q
  have hA_sub_contr (u : Fin (d + 1) → ℝ) : vecNorm (A_sub *ᵥ u) ≤ vecNorm u := by
    have h1 (x : Fin (d + 1) → ℝ) : vecNorm (taylor16Mat η G *ᵥ x) ≤ 1 * vecNorm x := by
      rw [one_mul]; exact vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose m r) hη_nn hBf_nn
        (vecNorm_dAltGenMat_mulVec_le m r) (by linarith) x
    simpa [A_sub] using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) h1 q u
  have hA_pow : A_sub ^ nSub = (taylor16Mat η G) ^ K := by
    dsimp only [A_sub]; rw [hK_eq, mul_comm nSub q, pow_mul]
  have hbCapCeil_196 : (196 : ℝ) ≤ (bCapCeil : ℝ) := by
    have hm49 : 49 ≤ m := by have := Nat.min_le_left m r; omega
    have hr49 : 49 ≤ r := by have := Nat.min_le_right m r; omega
    have hrad0 : 98 * 98 ≤ 4 * m * r :=
      calc 98 * 98 = 4 * 49 * 49 := rfl
        _ ≤ 4 * m * r := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hm49) hr49
    have hsq98 : (98 : ℝ) ≤ √((4 * m * r : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
      have hc : ((98 * 98 : ℕ) : ℝ) ≤ ((4 * m * r : ℕ) : ℝ) := by exact_mod_cast hrad0
      exact (by norm_num : (98 : ℝ) ^ 2 ≤ ((98 * 98 : ℕ) : ℝ)).trans hc
    set sq0Hi := (altIsqrt15 (4 * m * r)).2
    have hsq0_ge : √((4 * m * r : ℕ) : ℝ) ≤ (sq0Hi : ℝ) / wdScaleR :=
      (altIsqrt15_sound (4 * m * r)).2
    have hmax0' : sq0Hi ≤ maxBHi15 := hmax0_le
    clear_value sq0Hi
    have hmax0R : (sq0Hi : ℝ) / wdScaleR ≤ (maxBHi15 : ℝ) / wdScaleR :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmax0') hB_pos.le
    have h98_max : (98 : ℝ) ≤ (maxBHi15 : ℝ) / wdScaleR := (hsq98.trans hsq0_ge).trans hmax0R
    have h196_Bc : (196 : ℝ) ≤ B_cap := by
      rw [hBcap_eq_2max]
      calc (196 : ℝ) = 2 * 98 := by norm_num
        _ ≤ 2 * ((maxBHi15 : ℝ) / wdScaleR) := mul_le_mul_of_nonneg_left h98_max (by norm_num)
    exact h196_Bc.trans hbCapCeil_ge
  have hγ_at : |dAltCoupling m r dCap| ≤ (3 / 4) * B_cap := by
    have hc0 : 0 ≤ dAltCoupling m r dCap := by unfold dAltCoupling; positivity
    rw [abs_of_nonneg hc0]; have hnat_prod : 4 * (4 * (dCap + 1) * (m - dCap) * (r - dCap)) ≤
        9 * (4 * (dCap - 1 + 1) * (m - (dCap - 1)) * (r - (dCap - 1))) := by
      have h1 : 4 * (4 * (dCap + 1)) ≤ 9 * (4 * (dCap - 1 + 1)) := by omega
      have h2 : m - dCap ≤ m - (dCap - 1) := by omega
      have h3 : r - dCap ≤ r - (dCap - 1) := by omega
      calc 4 * (4 * (dCap + 1) * (m - dCap) * (r - dCap))
          = (4 * (4 * (dCap + 1))) * (m - dCap) * (r - dCap) := by ring
        _ ≤ (9 * (4 * (dCap - 1 + 1))) * (m - (dCap - 1)) * (r - (dCap - 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
        _ = 9 * (4 * (dCap - 1 + 1) * (m - (dCap - 1)) * (r - (dCap - 1))) := by ring
    have hsq_le : 2 * dAltCoupling m r dCap ≤ 3 * dAltCoupling m r (dCap - 1) := by
      unfold dAltCoupling
      have h2 : (2 : ℝ) * √((4 * (dCap + 1) * (m - dCap) * (r - dCap) : ℕ) : ℝ) =
          √((4 * (4 * (dCap + 1) * (m - dCap) * (r - dCap)) : ℕ) : ℝ) := by
        set X := 4 * (dCap + 1) * (m - dCap) * (r - dCap)
        have h4 : √((4 : ℕ) : ℝ) = (2 : ℝ) := by
          rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [Nat.cast_mul 4 X, Real.sqrt_mul (by positivity), h4]
      have h3 : (3 : ℝ) * √((4 * (dCap - 1 + 1) * (m - (dCap - 1)) * (r - (dCap - 1)) : ℕ) : ℝ) =
          √((9 * (4 * (dCap - 1 + 1) * (m - (dCap - 1)) * (r - (dCap - 1))) : ℕ) : ℝ) := by
        set Y := 4 * (dCap - 1 + 1) * (m - (dCap - 1)) * (r - (dCap - 1))
        have h9 : √((9 : ℕ) : ℝ) = (3 : ℝ) := by
          rw [show ((9 : ℕ) : ℝ) = (3 : ℝ) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [Nat.cast_mul 9 Y, Real.sqrt_mul (by positivity), h9]
      rw [h2, h3]; exact Real.sqrt_le_sqrt (by exact_mod_cast hnat_prod)
    have hprev : dAltCoupling m r (dCap - 1) ≤ (1 / 2) * B_cap :=
      (le_abs_self _).trans (hcoupl_cap (dCap - 1) (by omega))
    calc dAltCoupling m r dCap
        = (1 / 2) * (2 * dAltCoupling m r dCap) := by ring
      _ ≤ (1 / 2) * (3 * dAltCoupling m r (dCap - 1)) :=
          mul_le_mul_of_nonneg_left hsq_le (by norm_num)
      _ ≤ (1 / 2) * (3 * ((1 / 2) * B_cap)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hprev (by norm_num)) (by norm_num)
      _ = (3 / 4) * B_cap := by ring
  set ε_sub : ℝ := (h_real * B_cap) ^ 17 / 300000000000000 +
    (h_real * B_cap) ^ 18 / 7200000000000000 + (q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)
  set ε_quant : ℝ := (5 * (bCapCeil : ℝ) + 50) / wdScaleR
  have hε_sub_nn : 0 ≤ ε_sub :=
    add_nonneg (add_nonneg
        (div_nonneg (pow_nonneg (mul_nonneg hh_nn hBc_nn) 17) (by norm_num))
        (div_nonneg (pow_nonneg (mul_nonneg hh_nn hBc_nn) 18) (by norm_num)))
      (mul_nonneg (Nat.cast_nonneg q) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hε_quant_nn : 0 ≤ ε_quant :=
    div_nonneg (add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num))
      hB_pos.le
  set B_cap_mac : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := taylor16Mat h_real Gc
  have hsub_cap (v : Fin (d + 1) → ℝ) (hv : ∀ j : Fin (d + 1), coreLen ≤ j.1 → v j = 0) :
      vecNorm ((A_sub - B_cap_mac) *ᵥ v) ≤ ε_sub * vecNorm v :=
    vecNorm_taylor16Mat_cap_substep_le hdCap48 hdCap_lt hη_nn hBc_nn hBf_nn
      (vecNorm_dAltGenMat_mulVec_le m r) hηBf1 hcoupl_cap hγ_at hηBc1 hhBc_32 hv
  have hquant_cap (v : Fin (d + 1) → ℝ) :
      vecNorm ((B_cap_mac - taylor16OfMat (highd_ptGenMat d hbPt)) *ᵥ v) ≤
        ε_quant * vecNorm v := hquant_mac v
  clear_value B_cap_mac A_sub Gc
  set ε_step : ℝ := (297 / 2) / wdScaleR + (11 / 10) * (ε_sub + ε_quant)
  have hstep_sum_le : (nSub : ℝ) * ε_step ≤
      ((truncPad15 : ℝ) + (nSub : ℝ) * (10 * (bCapCeil : ℝ) + 256)) / wdScaleR := by
    have hp17_32 : (h_real * B_cap) ^ 17 ≤ (3 / 2 : ℝ) ^ 17 :=
      pow_le_pow_left₀ (mul_nonneg hh_nn hBc_nn) hhBc_32 17
    have hp18_32 : (h_real * B_cap) ^ 18 ≤ (3 / 2 : ℝ) ^ 18 :=
      pow_le_pow_left₀ (mul_nonneg hh_nn hBc_nn) hhBc_32 18
    have he17_ex : (1 / 10 : ℝ) * ((h_real * B_cap) ^ 17 / 300000000000000) ≤ 329 / wdScaleR := by
      rw [hB_eq]; have : (1 / 10 : ℝ) * ((3 / 2 : ℝ) ^ 17 / 300000000000000) ≤
          329 / 1000000000000000 := by norm_num
      linarith
    have he18_bd : (11 / 10 : ℝ) * ((h_real * B_cap) ^ 18 / 7200000000000000) ≤ 226 / wdScaleR := by
      rw [hB_eq]; have : (11 / 10 : ℝ) * ((3 / 2 : ℝ) ^ 18 / 7200000000000000) ≤
          226 / 1000000000000000 := by norm_num
      linarith
    have hquad_bd : (11 / 10 : ℝ) * ((q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) ≤
        1 / wdScaleR := by
      have hsq_sum : (η * B_full) ^ 2 + (η * B_cap) ^ 2 ≤
          (200000 ^ 2 + 400002 ^ 2 : ℝ) / (√(2 ^ n : ℝ)) ^ 2 := by
        have h1 : (η * B_full) ^ 2 ≤ (200000 / √(2 ^ n : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hη_nn hBf_nn)
            (by rw [hη_def, one_div_mul_eq_div];
                exact div_le_div_of_nonneg_right hBf_hi hsN_pos.le) 2
        have h2 : (η * B_cap) ^ 2 ≤ (400002 / √(2 ^ n : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hη_nn hBc_nn)
            (by rw [hη_def, one_div_mul_eq_div];
                exact div_le_div_of_nonneg_right hBc_hi hsN_pos.le) 2
        rw [div_pow] at h1 h2
        linarith [add_div (200000 ^ 2 : ℝ) (400002 ^ 2 : ℝ) ((√(2 ^ n : ℝ)) ^ 2)]
      have hprod_q : (q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2) ≤
          (4 * (200000 ^ 2 + 400002 ^ 2 : ℝ)) / √(2 ^ n : ℝ) := by
        calc (q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)
            ≤ (4 * √(2 ^ n : ℝ)) * ((200000 ^ 2 + 400002 ^ 2 : ℝ) / (√(2 ^ n : ℝ)) ^ 2) :=
              mul_le_mul hq_le_sqrt hsq_sum
                (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
          _ = (4 * (200000 ^ 2 + 400002 ^ 2 : ℝ)) / √(2 ^ n : ℝ) := by
              field_simp [hsN_pos.ne']
      rw [hB_eq]
      have hnum : (11 / 10 : ℝ) * (4 * (200000 ^ 2 + 400002 ^ 2 : ℝ)) * 1000000000000000 ≤
          (2 : ℝ) ^ 100 := by norm_num
      have hdiv : (11 / 10 : ℝ) * ((4 * (200000 ^ 2 + 400002 ^ 2 : ℝ)) / √(2 ^ n : ℝ)) ≤
          1 / 1000000000000000 := by
        rw [mul_div_assoc', div_le_div_iff₀ hsN_pos (by norm_num)]; linarith
      linarith
    have hrem_per_step : (297 / 2) / wdScaleR +
        ((1 / 10) * ((h_real * B_cap) ^ 17 / 300000000000000) +
         (11 / 10) * ((h_real * B_cap) ^ 18 / 7200000000000000) +
         (11 / 10) * ((q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) + (11 / 10) * ε_quant) ≤
        (10 * (bCapCeil : ℝ) + 256) / wdScaleR := by
      have hq_exp : (11 / 10 : ℝ) * ε_quant = ((11 / 2 : ℝ) * (bCapCeil : ℝ) + 55) / wdScaleR := by
        dsimp [ε_quant]; ring
      have hsum_num : ((297 / 2 : ℝ) + 329 + 226 + 1 + ((11 / 2) * (bCapCeil : ℝ) + 55)) /
          wdScaleR ≤ (10 * (bCapCeil : ℝ) + 256) / wdScaleR := by
        refine div_le_div_of_nonneg_right ?_ hB_pos.le; linarith [hbCapCeil_196]
      have hadd5 : (297 / 2) / wdScaleR + ((1 / 10) * ((h_real * B_cap) ^ 17 / 300000000000000) +
           (11 / 10) * ((h_real * B_cap) ^ 18 / 7200000000000000) +
           (11 / 10) * ((q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) + (11 / 10) * ε_quant) ≤
          ((297 / 2 : ℝ) + 329 + 226 + 1 + ((11 / 2) * (bCapCeil : ℝ) + 55)) / wdScaleR := by
        rw [hq_exp]; have h1 := add_le_add (add_le_add (add_le_add he17_ex he18_bd) hquad_bd)
          (le_rfl : ((11 / 2 : ℝ) * (bCapCeil : ℝ) + 55) / wdScaleR ≤ _)
        have h2 := add_le_add (le_rfl : (297 / 2) / wdScaleR ≤ _) h1; refine h2.trans (le_of_eq ?_)
        ring
      exact hadd5.trans hsum_num
    have hsplit_step : ε_step = (h_real * B_cap) ^ 17 / 300000000000000 + ((297 / 2) / wdScaleR +
          ((1 / 10) * ((h_real * B_cap) ^ 17 / 300000000000000) +
           (11 / 10) * ((h_real * B_cap) ^ 18 / 7200000000000000) +
           (11 / 10) * ((q : ℝ) * ((η * B_full) ^ 2 + (η * B_cap) ^ 2)) +
           (11 / 10) * ε_quant)) := by
      dsimp [ε_step, ε_sub]; ring
    rw [hsplit_step, mul_add, add_div]; exact add_le_add htrunc_ge
      ((mul_le_mul_of_nonneg_left hrem_per_step (Nat.cast_nonneg nSub)).trans
        (le_of_eq (by ring)))
  have hstep_sum_10 : (0 : ℝ) + (nSub : ℝ) * ε_step ≤ 1 / 10 := by
    rw [zero_add]
    have hpadR : ((truncPad15 : ℝ) + (nSub : ℝ) * (10 * (bCapCeil : ℝ) + 256)) / wdScaleR ≤
        (totalPad15 : ℝ) / wdScaleR := by
      refine div_le_div_of_nonneg_right ?_ hB_pos.le; linarith [hpadR_eq]
    have h10 : (totalPad15 : ℝ) / wdScaleR ≤ 1 / 10 := by
      rw [hB_eq, div_le_div_iff₀ (by norm_num) (by norm_num)]
      have hc : (totalPad15 : ℝ) ≤ 100000000000000 := by exact_mod_cast hpad_le
      linarith
    exact (hstep_sum_le.trans hpadR).trans h10
  have hcore16 : 16 + coreLen ≤ d + 1 := by dsimp [coreLen, d]; omega
  let e0_d : Fin (d + 1) → ℝ := e0
  have he0_d_norm : vecNorm e0_d ≤ 1 := le_of_eq he0_norm
  have herr_init : vecNorm (highd_listToOrbVec d vecInit - e0_d) ≤ (0 : ℝ) := by
    change vecNorm (highd_listToOrbVec (min m r) vecInit - e0) ≤ 0
    rw [hvecInit_eq, sub_self, vecNorm_zero]
  set vecFinal := altIterCapT16 nSub coreLen hbPt vecInit
  obtain ⟨hvf_len, hvf_err⟩ := highd_altIterCapT16_approx hd_hi hhb_le_d
    hcore16 hA_sub_contr hGpt_op hε_sub_nn hε_quant_nn
    hsub_cap hquant_cap nSub vecInit e0_d (0 : ℝ)
    hvecInit_len he0_d_norm (le_rfl : (0 : ℝ) ≤ 0)
    hstep_sum_10 herr_init hvf_ne
  rw [hA_pow, zero_add] at hvf_err
  set padded := altPadRightInts coreLen vecFinal
  have hpad_len : padded.length = coreLen := highd_altPadRightInts_length coreLen vecFinal
  have hpad_vec : highd_listToOrbVec d padded = highd_listToOrbVec d vecFinal := by
    ext a
    dsimp only [highd_listToOrbVec, padded]
    rw [highd_altPadRightInts_getD coreLen vecFinal hvf_len]
  set uInt := highd_listToOrbVec d padded
  have htotal_norm : vecNorm (uWalk - uInt) ≤ (totalPad15 : ℝ) / wdScaleR := by
    rw [hpad_vec]
    have hsp : uWalk - highd_listToOrbVec d vecFinal = (uWalk - ((taylor16Mat η G) ^ K) *ᵥ e0) +
        (((taylor16Mat η G) ^ K) *ᵥ e0 - highd_listToOrbVec d vecFinal) := by
      ext i; simp
    have hvf_err' : vecNorm (((taylor16Mat η G) ^ K) *ᵥ e0 - highd_listToOrbVec d vecFinal) ≤
        (nSub : ℝ) * ε_step := by
      rw [← vecNorm_neg, neg_sub]; exact hvf_err
    rw [hsp]; have htri := vecNorm_add_le (uWalk - ((taylor16Mat η G) ^ K) *ᵥ e0)
      (((taylor16Mat η G) ^ K) *ᵥ e0 - highd_listToOrbVec d vecFinal)
    have hpadR : 2 / wdScaleR +
        ((truncPad15 : ℝ) + (nSub : ℝ) * (10 * (bCapCeil : ℝ) + 256)) / wdScaleR ≤
        (totalPad15 : ℝ) / wdScaleR := by
      rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hB_pos.le; linarith [hpadR_eq]
    linarith [htri, hterm_cont, hvf_err', hstep_sum_le, hpadR]
  rcases hp_cases : padded with _ | ⟨_, tail⟩
  · rw [hp_cases] at hpad_len; dsimp [coreLen] at hpad_len; omega
  · have htail_len : tail.length = coreLen - 1 := by
      rw [hp_cases] at hpad_len; simp at hpad_len; omega
    have hrow_len : (altEvalRowHighDLo12 m r tau9 nSub dCap).length = coreLen - 1 := by
      rw [heval_cap, hp_cases]
      exact (highd_altVecTailToLo12_length totalPad15 tail).trans htail_len
    have hwd : w ≤ d := by dsimp [coreLen] at hrow_len; omega
    let wFin : Fin (orbDim m r) := ⟨w, by unfold orbDim; omega⟩
    have hw_coord : |uWalk wFin - uInt wFin| ≤ (totalPad15 : ℝ) / wdScaleR :=
      (abs_apply_le_vecNorm (uWalk - uInt) wFin).trans htotal_norm
    have huInt_w : uInt wFin = (tail.getD (w - 1) 0 : ℝ) / wdScaleR := by
      dsimp [uInt, highd_listToOrbVec, wFin]; rw [hp_cases]
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      simp
    rw [huInt_w] at hw_coord
    have hget_row : (altEvalRowHighDLo12 m r tau9 nSub dCap).getD (w - 1) 0 =
        ((((Int.natAbs (tail.getD (w - 1) 0) - totalPad15) *
          (Int.natAbs (tail.getD (w - 1) 0) - totalPad15)) / wdScale) / 1000) - 1 := by
      rw [heval_cap, hp_cases]; exact highd_altVecTailToLo12_getD totalPad15 tail (w - 1) (by omega)
    have hprob_lo := highd_altVecTailToLo12_entry_le hw_coord; rw [← hget_row] at hprob_lo
    exact ⟨wFin, rfl, hprob_lo⟩
private theorem highd_bif_nil_ne {α : Type} {b : Bool} {xs : List α}
    (h : cond b [] xs ≠ []) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (h rfl)
/-- Unified soundness of `altEvalRowHighDLo12` across `1 ≤ m ≤ 8192`, `2 ≤ r ≤ 1024`, and
  both
  full-band (`dCap = min m r`) and `32`-zero causal-window (`48 ≤ dCap < min m r`) modes. -/
theorem altEvalRowHighDLo12_sound {n m r tau9 nSub dCap : ℕ} (hn : altN0 ≤ n)
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r) {w : ℕ} (hw1 : 1 ≤ w)
    (hw_lt : w - 1 < (altEvalRowHighDLo12 m r tau9 nSub dCap).length) :
    (((altEvalRowHighDLo12 m r tau9 nSub dCap).getD (w - 1) 0 : ℝ) / 1000000000000) ≤
      symHitProb R (evalSymStages R (altStages tau9 nSub m n) (u0Vec (2 ^ n) m)) w := by
  set d := min m r
  have hlen_pos : 0 < (altEvalRowHighDLo12 m r tau9 nSub dCap).length := by omega
  have hrow_ne : altEvalRowHighDLo12 m r tau9 nSub dCap ≠ [] := by
    intro hnil; rw [hnil] at hlen_pos; simp at hlen_pos
  generalize heval_eq : altEvalRowHighDLo12 m r tau9 nSub dCap = rowOut at hrow_ne
  have hrow_def : altEvalRowHighDLo12 m r tau9 nSub dCap = rowOut := heval_eq
  rw [← hrow_def]
  have hne : altEvalRowHighDLo12 m r tau9 nSub dCap ≠ [] := by
    rw [heval_eq]; exact hrow_ne
  unfold altEvalRowHighDLo12 at heval_eq hne
  simp only [highdForceNat_eq, highdForceList_eq, highdStrictConsInt_eq,
    highd_natMin_eq, highd_primNatBlt_eq, highd_to_beq (fun {a b} ↦ Nat.beq_eq)] at heval_eq hne
  have hd_raw : min m r = d := rfl
  rw [hd_raw] at heval_eq hne
  have hg1_str := highd_bif_nil_ne hne
  rw [hg1_str, highd_cond_false] at heval_eq hne
  have hg1_props := hg1_str
  simp only [Bool.or_eq_false_iff, highd_nat_blt_eq_false, highd_nat_beq_eq_false] at hg1_props
  obtain ⟨hd1, hdCap1, hdCap_le, hcap48_b, hr2, hm_hi, hr_hi, htau_ne, htau_hi,
    hnsub_ne, hnsub_hi⟩ := hg1_props
  have hcap48 : dCap < d → 48 ≤ dCap := by
    intro hlt
    have hlt_t : Nat.blt dCap d = true := highd_nat_blt_eq_true.mpr hlt
    rw [hlt_t, Bool.true_and] at hcap48_b; exact highd_nat_blt_eq_false.mp hcap48_b
  have hm1 : 1 ≤ m := hd1.trans (Nat.min_le_left m r)
  have hr1 : 1 ≤ r := by omega
  have hd_hi : d ≤ 1024 := (Nat.min_le_right m r).trans hr_hi
  set hPt := (tau9 * 1000000) / nSub
  have hhPt_raw : Nat.div (Nat.mul tau9 1000000) nSub = hPt := rfl
  rw [hhPt_raw] at heval_eq hne
  have hhPt_f : Nat.blt hPt 1 = false := highd_bif_nil_ne hne
  rw [hhPt_f, highd_cond_false] at heval_eq hne
  have hhPt1 : 1 ≤ hPt := highd_nat_blt_eq_false.mp hhPt_f
  set maxBHi15 := altMaxBHiFrom m r 0 dCap
  set bCapHi15 := 2 * maxBHi15
  have hbCap_raw : Nat.mul 2 maxBHi15 = bCapHi15 := rfl
  rw [hbCap_raw] at heval_eq hne
  set hgHi15 := highdMulCeil15 (2 + hPt) bCapHi15
  have hhg_raw : highdMulCeil15 (Nat.add 2 hPt) bCapHi15 = hgHi15 := rfl
  rw [hhg_raw] at heval_eq hne
  have hmid_f : Bool.or (Nat.blt 1500000000000000 hgHi15)
      (Bool.not (altCheckHbTight m r 0 dCap)) = false := highd_bif_nil_ne hne
  rw [hmid_f, highd_cond_false] at heval_eq hne
  have hmid_p := hmid_f
  simp only [Bool.or_eq_false_iff, highd_nat_blt_eq_false, Bool.not_eq_false'] at hmid_p
  obtain ⟨hhg_le, htight⟩ := hmid_p
  set hgPow := altPow17Ceil15 hgHi15
  set truncPad15 := (299999999999999 + nSub * hgPow) / 300000000000000
  have htrunc_raw :
      Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000 = truncPad15 := rfl
  set bCapCeil := (999999999999999 + bCapHi15) / wdScale
  have hbCeil_raw : Nat.div (Nat.add 999999999999999 bCapHi15) wdScale = bCapCeil := rfl
  rw [htrunc_raw, hbCeil_raw] at heval_eq hne
  set roundPad15 := 256 + nSub * (256 + 10 * bCapCeil)
  have hround_raw :
      Nat.add 256 (Nat.mul nSub (Nat.add 256 (Nat.mul 10 bCapCeil))) = roundPad15 := rfl
  rw [hround_raw] at heval_eq hne
  set totalPad15 := truncPad15 + roundPad15
  have hpad_raw : Nat.add truncPad15 roundPad15 = totalPad15 := rfl
  rw [hpad_raw] at heval_eq hne
  have hpad_f : Bool.or (Nat.blt 100000000000000 totalPad15) (totalPad15 == 0) = false :=
    highd_bif_nil_ne hne
  rw [hpad_f, highd_cond_false] at heval_eq hne
  have hpad_p := hpad_f
  simp only [Bool.or_eq_false_iff, highd_nat_blt_eq_false, highd_nat_beq_eq_false] at hpad_p
  have hpad_le : totalPad15 ≤ 100000000000000 := hpad_p.1
  set hbPt := altBuildHbFrom m r hPt 0 dCap
  set vecInit : List ℤ := [(wdScale : ℤ)]
  have hvi_raw : ([Int.ofNat wdScale] : List ℤ) = vecInit := rfl
  have hd1_raw : Nat.add d 1 = d + 1 := rfl
  have hcore_raw : Nat.sub dCap 32 = dCap - 32 := rfl
  rw [hvi_raw, hd1_raw, hcore_raw] at heval_eq hne
  -- Dimension & scale setup
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  have hn80 : 80000 ≤ n := hn; have hpow200 : (2 : ℝ) ^ 200 ≤ (2 ^ n : ℝ) :=
    pow_le_pow_right₀ (by norm_num) (by omega : 200 ≤ n)
  have hsN_ge100 : (2 : ℝ) ^ 100 ≤ √(2 ^ n : ℝ) :=
    Real.le_sqrt_of_sq_le ((by rw [← pow_mul] : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hpow200)
  have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge100
  have hpow15 : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2mN : 2 * m < 2 ^ n :=
    lt_of_le_of_lt (by omega : 2 * m ≤ 16384)
      (lt_of_lt_of_le (by norm_num : 16384 < 2 ^ 15) hpow15)
  have hmrN : m + r ≤ 2 ^ n :=
    le_trans (by omega : m + r ≤ 9216)
      (le_trans (by norm_num : 9216 ≤ 2 ^ 15) hpow15)
  set q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
  set K := altStepCount tau9 nSub (2 ^ n)
  have hK_eq : K = nSub * q := rfl
  have hK_le : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ) := by
    have h1 : (K : ℝ) ≤ ((tau9 : ℝ) / 1000000000) * √(2 ^ n : ℝ) := by
      simpa [K, Nat.cast_pow, Nat.cast_ofNat] using altStepCount_le_tau_sqrt tau9 nSub (2 ^ n)
    have htauR : (tau9 : ℝ) / 1000000000 ≤ 4 := by
      have hc : (tau9 : ℝ) ≤ 4000000000 := by exact_mod_cast htau_hi
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right htauR hsN_pos.le)
  have hq_le_K : q ≤ K := by dsimp [K, altStepCount]; exact Nat.le_mul_of_pos_left q (by omega)
  have hq_le_sqrt : (q : ℝ) ≤ 4 * √(2 ^ n : ℝ) :=
    (by exact_mod_cast hq_le_K : (q : ℝ) ≤ (K : ℝ)).trans hK_le
  -- Initial basis vector e0 = highd_listToOrbVec d vecInit
  let z0 : Fin (orbDim m r) := ⟨0, by unfold orbDim; omega⟩
  let e0 : Fin (orbDim m r) → ℝ := Pi.single z0 1
  have he0_norm : vecNorm e0 = 1 := by
    unfold vecNorm vecSqNorm; rw [Finset.sum_eq_single z0]
    · simp [e0, z0]
    · intro b _ hb; dsimp only [e0]; rw [Pi.single_eq_of_ne hb]; ring
    · intro hz; exact absurd (Finset.mem_univ z0) hz
  have hvecInit_eq : highd_listToOrbVec d vecInit = e0 := by
    funext (a : Fin (orbDim m r))
    rcases ha : a.1 with _ | j'
    · have haz : a = z0 := Fin.ext ha; dsimp only [e0]; rw [haz, Pi.single_eq_same]
      change ((vecInit.getD 0 0 : ℝ) / wdScaleR) = 1
      have hget0 : vecInit.getD 0 0 = (wdScale : ℤ) := rfl
      have hwR : ((wdScale : ℤ) : ℝ) = wdScaleR := by unfold wdScaleR; push_cast; rfl
      rw [hget0, hwR]; exact div_self hB_pos.ne'
    · have hne : a ≠ z0 := fun h ↦ by
        have hv : a.1 = 0 := congrArg Fin.val h; omega
      dsimp only [e0]; rw [Pi.single_eq_of_ne hne]; change ((vecInit.getD a.1 0 : ℝ) / wdScaleR) = 0
      rw [ha]; have hgetS : vecInit.getD (j' + 1) 0 = 0 := rfl; rw [hgetS, Int.cast_zero, zero_div]
  -- Continuum + T_8 -> T_16 trajectory bridge
  set η : ℝ := 1 / √(2 ^ n : ℝ)
  have hη_nn : 0 ≤ η := by positivity
  set G := dAltGenMat m r
  set uWalk := ((dAltStepOrbMat (2 ^ n) m r) ^ K) *ᵥ u0OrbVecGen (2 ^ n) m r
  have hterm_cont : vecNorm (uWalk - ((taylor16Mat η G) ^ K) *ᵥ e0) ≤ 2 / wdScaleR := by
    have ht8 : vecNorm (uWalk - ((taylor8Mat η G) ^ K) *ᵥ e0) ≤ 1 / wdScaleR := by
      simpa [wdScaleR, η, G, z0, e0, uWalk] using
        vecNorm_dAltStepOrbMat_pow_sub_taylor8_le hn hm1 hm_hi hr1 hr_hi hK_le
    have ht16 : vecNorm (((taylor8Mat η G) ^ K) *ᵥ e0 -
        ((taylor16Mat η G) ^ K) *ᵥ e0) ≤ 1 / wdScaleR := by
      simpa [wdScaleR, η, G, z0, e0] using
        vecNorm_taylor8_sub_taylor16_pow_le hn80 hm1 hm_hi hr1 hr_hi hK_le
    have hsp : uWalk - ((taylor16Mat η G) ^ K) *ᵥ e0 = (uWalk - ((taylor8Mat η G) ^ K) *ᵥ e0) +
        (((taylor8Mat η G) ^ K) *ᵥ e0 - ((taylor16Mat η G) ^ K) *ᵥ e0) := by
      ext i; simp
    rw [hsp]
    calc vecNorm ((uWalk - ((taylor8Mat η G) ^ K) *ᵥ e0) +
            (((taylor8Mat η G) ^ K) *ᵥ e0 - ((taylor16Mat η G) ^ K) *ᵥ e0))
        ≤ vecNorm (uWalk - ((taylor8Mat η G) ^ K) *ᵥ e0) +
            vecNorm (((taylor8Mat η G) ^ K) *ᵥ e0 - ((taylor16Mat η G) ^ K) *ᵥ e0) :=
          vecNorm_add_le _ _
      _ ≤ 1 / wdScaleR + 1 / wdScaleR := add_le_add ht8 ht16
      _ = 2 / wdScaleR := by ring
  -- Operator bounds on G, Gc, and quantized highd_ptGenMat
  set B_full := dAltGenNormBound m r
  have hBf_nn : 0 ≤ B_full := by unfold B_full dAltGenNormBound; positivity
  have hBf_hi : B_full ≤ 200000 := by
    unfold B_full dAltGenNormBound; rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩
    have hd1_le : min m r + 1 ≤ 1025 := by omega
    have hmx_le : max m r ≤ 8192 := Nat.max_le.mpr ⟨hm_hi, by omega⟩
    have hp : 4 * (min m r + 1) ^ 2 * max m r ≤ 4 * 1025 ^ 2 * 8192 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hd1_le 2)) hmx_le
    have hc : ((4 * (min m r + 1) ^ 2 * max m r : ℕ) : ℝ) ≤
        ((4 * 1025 ^ 2 * 8192 : ℕ) : ℝ) := by exact_mod_cast hp
    exact hc.trans (by norm_num)
  have hG_full (u : Fin (orbDim m r) → ℝ) : vecNorm (G *ᵥ u) ≤ B_full * vecNorm u :=
    vecNorm_dAltGenMat_mulVec_le m r u
  have hηBf1 : η * B_full ≤ 1 := by
    dsimp [η]; rw [one_div_mul_eq_div, div_le_one hsN_pos]
    exact hBf_hi.trans (le_trans (by norm_num : (200000 : ℝ) ≤ (2 : ℝ) ^ 100) hsN_ge100)
  set B_cap := (bCapHi15 : ℝ) / wdScaleR
  have hBc_nn : 0 ≤ B_cap := div_nonneg (Nat.cast_nonneg _) hB_pos.le
  have hBc_hi : B_cap ≤ 400002 := by
    have hm_nat : maxBHi15 ≤ 200001 * wdScale :=
      highd_altMaxBHiFrom_le_of_tight hm_hi hr_hi dCap 0 htight
        (by have := Nat.min_le_right m r; omega)
    have hb_nat : bCapHi15 ≤ 400002 * wdScale := by dsimp [bCapHi15]; omega
    have hbR : (bCapHi15 : ℝ) ≤ (400002 : ℝ) * wdScaleR := by unfold wdScaleR; exact_mod_cast hb_nat
    exact (div_le_iff₀ hB_pos).mpr hbR
  have hηBc1 : η * B_cap ≤ 1 := by
    dsimp [η]; rw [one_div_mul_eq_div, div_le_one hsN_pos]
    exact hBc_hi.trans (le_trans (by norm_num : (400002 : ℝ) ≤ (2 : ℝ) ^ 100) hsN_ge100)
  have hcoupl_cap (j : ℕ) (hj : j < dCap) : |dAltCoupling m r j| ≤ (1 / 2) * B_cap := by
    have hc0 : 0 ≤ dAltCoupling m r j := by unfold dAltCoupling; positivity
    rw [abs_of_nonneg hc0]; have hmax_j := highd_altMaxBHiFrom_ge m r dCap 0 j hj
    set rad := 4 * (j + 1) * (m - j) * (r - j)
    have hsq : dAltCoupling m r j ≤ ((altIsqrt15 rad).2 : ℝ) / wdScaleR := (altIsqrt15_sound rad).2
    have hmaxR : ((altIsqrt15 rad).2 : ℝ) ≤ (maxBHi15 : ℝ) := by
      have : 4 * (0 + j + 1) * (m - (0 + j)) * (r - (0 + j)) = rad := by simp [rad]
      rw [this] at hmax_j
      exact_mod_cast hmax_j
    clear_value rad
    calc dAltCoupling m r j
        ≤ ((altIsqrt15 rad).2 : ℝ) / wdScaleR := hsq
      _ ≤ (maxBHi15 : ℝ) / wdScaleR := div_le_div_of_nonneg_right hmaxR hB_pos.le
      _ = (1 / 2) * B_cap := by dsimp [B_cap, bCapHi15]; push_cast; ring
  have hbCapCeil_ge : B_cap ≤ (bCapCeil : ℝ) := by
    have hnat : bCapHi15 ≤ bCapCeil * wdScale := by
      have h := highd_ceil_div_mul_ge bCapHi15 wdScale (by unfold wdScale; positivity)
      have hsub : wdScale - 1 = 999999999999999 := by unfold wdScale; rfl
      rw [hsub] at h; exact h
    have hR : (bCapHi15 : ℝ) ≤ (bCapCeil : ℝ) * wdScaleR := by unfold wdScaleR; exact_mod_cast hnat
    exact (div_le_iff₀ hB_pos).mpr hR
  -- Substep size h_real = q * η
  set h_real : ℝ := (q : ℝ) * η
  have hsub_bds := highd_substep_bounds hn htau_hi (by omega) hnsub_hi
  have hh_nn : 0 ≤ h_real := mul_nonneg (Nat.cast_nonneg _) hη_nn
  have hh_hi : h_real ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR := by
    dsimp [h_real, η, q, hPt]; simpa [div_eq_mul_inv] using hsub_bds.2.1
  have hh_diff : |h_real - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
    dsimp [h_real, η, q, hPt]; simpa [div_eq_mul_inv] using hsub_bds.2.2
  have hhBc_le_hg : h_real * B_cap ≤ (hgHi15 : ℝ) / wdScaleR :=
    (mul_le_mul_of_nonneg_right hh_hi hBc_nn).trans (highd_mulCeil15_ge (2 + hPt) bCapHi15)
  have hhBc_mul_ge : (((2 + hPt : ℕ) : ℝ) / wdScaleR) * B_cap ≤ (hgHi15 : ℝ) / wdScaleR :=
    highd_mulCeil15_ge (2 + hPt) bCapHi15
  have hhg_32 : (hgHi15 : ℝ) / wdScaleR ≤ 3 / 2 := by
    rw [hB_eq, div_le_div_iff₀ (by norm_num) (by norm_num)]
    have hc : (hgHi15 : ℝ) ≤ 1500000000000000 := by exact_mod_cast hhg_le
    linarith
  have hhBc_32 : h_real * B_cap ≤ 3 / 2 := hhBc_le_hg.trans hhg_32
  have hhPt_le4 : (hPt : ℝ) / wdScaleR ≤ 4 := by
    have hnat : hPt ≤ 4000000000 * 1000000 := by
      dsimp [hPt]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _ htau_hi)
    rw [hB_eq, div_le_iff₀ (by norm_num)]
    have hR : (hPt : ℝ) ≤ 4000000000000000 := by exact_mod_cast hnat
    linarith
  have hpow17_le : (h_real * B_cap) ^ 17 ≤ (hgPow : ℝ) / wdScaleR :=
    (pow_le_pow_left₀ (mul_nonneg hh_nn hBc_nn) hhBc_le_hg 17).trans
      (highd_altPow17Ceil15_ge hgHi15)
  have htrunc_ge : (nSub : ℝ) * ((h_real * B_cap) ^ 17 / 300000000000000) ≤
      (truncPad15 : ℝ) / wdScaleR := by
    have hnat : nSub * hgPow ≤ truncPad15 * 300000000000000 :=
      highd_ceil_div_mul_ge (nSub * hgPow) 300000000000000 (by norm_num)
    have hR : (nSub : ℝ) * (hgPow : ℝ) ≤ (truncPad15 : ℝ) * 300000000000000 := by
      exact_mod_cast hnat
    clear_value hgPow truncPad15
    have hdiv17 : (h_real * B_cap) ^ 17 / 300000000000000 ≤
        (hgPow : ℝ) / (300000000000000 * wdScaleR) := by
      have h1 := div_le_div_of_nonneg_right hpow17_le (by norm_num : (0 : ℝ) ≤ 300000000000000)
      rwa [div_div, mul_comm wdScaleR 300000000000000] at h1
    calc (nSub : ℝ) * ((h_real * B_cap) ^ 17 / 300000000000000)
        ≤ (nSub : ℝ) * ((hgPow : ℝ) / (300000000000000 * wdScaleR)) :=
          mul_le_mul_of_nonneg_left hdiv17 (Nat.cast_nonneg nSub)
      _ ≤ (truncPad15 : ℝ) / wdScaleR := by
          rw [show (nSub : ℝ) * ((hgPow : ℝ) / (300000000000000 * wdScaleR)) =
              ((nSub : ℝ) * (hgPow : ℝ)) / (300000000000000 * wdScaleR) by ring,
            div_le_div_iff₀ (mul_pos (by norm_num) hB_pos) hB_pos,
            show (truncPad15 : ℝ) * (300000000000000 * wdScaleR) =
              ((truncPad15 : ℝ) * 300000000000000) * wdScaleR by ring]
          exact mul_le_mul_of_nonneg_right hR hB_pos.le
  have hBcap_eq_2max : B_cap = 2 * ((maxBHi15 : ℝ) / wdScaleR) := by
    dsimp [B_cap, bCapHi15]; push_cast; ring
  have hpadR_eq : (totalPad15 : ℝ) = (truncPad15 : ℝ) +
      ((nSub : ℝ) * (10 * (bCapCeil : ℝ) + 256) + 256) := by
    dsimp [totalPad15, roundPad15]; push_cast; ring
  have hhb_len : hbPt.length = dCap := highd_altBuildHbFrom_length m r hPt dCap 0
  have hhb_le_d : hbPt.length ≤ d := hhb_len.trans_le hdCap_le
  have hhb_get (j : ℕ) (hjc : j < dCap) : hbPt.getD j 0 =
        (((hPt * (altIsqrt15 (4 * (j + 1) * (m - j) * (r - j))).1) / wdScale : ℕ) : ℤ) := by
    simpa using highd_altBuildHbFrom_getD m r hPt dCap 0 j hjc
  have hmax0_le : (altIsqrt15 (4 * m * r)).2 ≤ maxBHi15 := by
    have h0 := highd_altMaxBHiFrom_ge m r dCap 0 0 (by omega)
    have heq : 4 * (0 + 0 + 1) * (m - (0 + 0)) * (r - (0 + 0)) = 4 * m * r := by simp
    rwa [heq] at h0
  clear_value hPt maxBHi15 bCapHi15 hgHi15 hgPow truncPad15 bCapCeil roundPad15 totalPad15 hbPt
    B_cap
  obtain ⟨hGc_op, hGpt_op, hquant_mac⟩ :=
    highd_ptGenMat_bounds hhPt_le4 hh_nn hh_diff hBc_nn hhBc_32 hhBc_mul_ge hhg_32
      hbCapCeil_ge hcoupl_cap htight hhb_len hhb_get
  have hbranch : ∃ wFin : Fin (orbDim m r), wFin.1 = w ∧
        (((altEvalRowHighDLo12 m r tau9 nSub dCap).getD (w - 1) 0 : ℝ) / 1000000000000) ≤
          (uWalk wFin) ^ 2 := by
    cases hcap_eq : (dCap == d) with
    | true =>
      have hdCap_eq_d : dCap = d := highd_nat_beq_eq_true.mp hcap_eq
      rw [hcap_eq, highd_cond_true] at heval_eq
      have heval_full : altEvalRowHighDLo12 m r tau9 nSub dCap =
          (match altPadRightInts (d + 1) (altIterFullT16 nSub (d + 1) hbPt vecInit) with
           | [] => []
           | _ :: tail => altVecTailToLo12 totalPad15 tail) :=
        hrow_def.trans heval_eq.symm
      exact highd_evalRow_branch_full hw1 hw_lt hd_hi hdCap_eq_d hK_eq hη_nn hBc_nn hηBf1
        hhBc_32 he0_norm (by simp [vecInit]) hvecInit_eq hhb_le_d hGc_op hGpt_op hquant_mac
        hterm_cont htrunc_ge hpadR_eq heval_full
    | false =>
      have hdCap_ne : dCap ≠ d := highd_nat_beq_eq_false.mp hcap_eq
      have hdCap_lt : dCap < d := by omega
      have hdCap48 : 48 ≤ dCap := hcap48 hdCap_lt
      rw [hcap_eq, highd_cond_false] at heval_eq hne
      have hvf_ne : altIterCapT16 nSub (dCap - 32) hbPt vecInit ≠ [] := by
        intro hnil
        have hne' : (match altIterCapT16 nSub (dCap - 32) hbPt vecInit with
          | [] => ([] : List ℕ)
          | _ :: _ =>
            match altPadRightInts (dCap - 32) (altIterCapT16 nSub (dCap - 32) hbPt vecInit) with
            | [] => []
            | _ :: tail => altVecTailToLo12 totalPad15 tail) ≠ [] := hne
        rw [hnil] at hne'
        exact hne' rfl
      have heval_cap : altEvalRowHighDLo12 m r tau9 nSub dCap =
          (match altPadRightInts (dCap - 32) (altIterCapT16 nSub (dCap - 32) hbPt vecInit) with
           | [] => []
           | _ :: tail => altVecTailToLo12 totalPad15 tail) := by
        have heq' : (match altIterCapT16 nSub (dCap - 32) hbPt vecInit with
          | [] => ([] : List ℕ)
          | _ :: _ =>
            match altPadRightInts (dCap - 32) (altIterCapT16 nSub (dCap - 32) hbPt vecInit) with
            | [] => []
            | _ :: tail => altVecTailToLo12 totalPad15 tail) = rowOut := heval_eq
        rw [hrow_def, ← heq']
        rcases hv_c : altIterCapT16 nSub (dCap - 32) hbPt vecInit with _ | ⟨_, _⟩
        · exact absurd hv_c hvf_ne
        · rfl
      exact highd_evalRow_branch_cap hsN_ge100 rfl hw1 hw_lt hd_hi hdCap48 hdCap_lt hK_eq
        hq_le_sqrt hη_nn hBf_hi hηBf1 hBc_nn hBc_hi hηBc1 hhBc_32 hBcap_eq_2max hmax0_le
        hbCapCeil_ge hcoupl_cap he0_norm (by simp [vecInit]; omega) hvecInit_eq hhb_le_d
        hGpt_op hquant_mac hterm_cont htrunc_ge hpadR_eq hpad_le hvf_ne heval_cap
  obtain ⟨wFin, hwFin_val, hprob_lo⟩ := hbranch
  have hstage_prob : symHitProb R (evalSymStages R (altStages tau9 nSub m n) (u0Vec (2 ^ n) m)) w =
        (uWalk wFin) ^ 2 := by
    have hm_cond : 1 ≤ n ∧ 2 * m < 2 ^ n := ⟨by omega, h2mN⟩; unfold altStages
    rw [dite_eq_left hm_cond]; dsimp only [evalSymStages, SymOrthogonal.ofSymmInvolution]
    subst hR
    rw [← hwFin_val]; exact symHitProb_evalSymStage_dAlt hmrN K wFin
  rwa [hstage_prob]
/- ## Section 5: Banded Bellman Loop Chaining, `altHighDWalkSpecOf`, & Circuit Wrappers -/
private theorem highd_checkAltHighDBandLoop_cons (m r vPrev vR tau9 nSub dCap : ℕ)
    (vhRest vRest tauRest nsubRest dcapRest : List ℕ) :
    checkAltHighDBandLoop m r (vPrev :: vhRest) (vR :: vRest) (tau9 :: tauRest)
        (nSub :: nsubRest) (dCap :: dcapRest) =
      (cond (Bool.or (Nat.blt r 2) (Nat.blt 1024 r)) false ( cond (Nat.blt vR vPrev) false (
              let stepOk :=
                cond (tau9 == 0) (checkEigStep m r vR vPrev) (
                    let d := highdNatMin m r
                    let rowLo12 := altEvalRowHighDLo12 m r tau9 nSub dCap
                    let rLen := altListLen rowLo12
                    cond (Bool.or (rLen == 0) (Bool.or (Nat.blt d rLen)
                          (Bool.or (altSumNat rowLo12 == 0)
                            (Nat.blt (altListLen (vPrev :: vhRest)) rLen))))
                      false
                      (
                        let drift27 := altDriftSum27 vR rowLo12 (vPrev :: vhRest)
                        Nat.blt (Nat.mul tau9 1000000000000000000) drift27))
              cond stepOk (checkAltHighDBandLoop m (Nat.succ r) (vR :: vPrev :: vhRest)
                  vRest tauRest nsubRest dcapRest)
                false))) := by
  conv_lhs =>
    unfold checkAltHighDBandLoop checkAltHighDBandLoopAux
    simp only [highdForceNat_eq, highdForceList_eq, highd_primNatBlt_eq,
      highd_to_beq (fun {a b} ↦ Nat.beq_eq)]
  rfl
/-- Composes two certified `checkAltHighDBandLoop` sub-bands into a single band check,
  enabling
  `width = 1` per-part `decide +kernel` decomposition across `r = 129.. 1024`. -/
theorem checkAltHighDBandLoop_append (m r : ℕ) (vHist v1 v2 t1 t2 n1 n2 c1 c2 : List ℕ)
    (ht : t1.length = v1.length) (hn : n1.length = v1.length) (hc : c1.length = v1.length)
    (h1 : checkAltHighDBandLoop m r vHist v1 t1 n1 c1 = true)
    (h2 : checkAltHighDBandLoop m (r + v1.length) (v1.reverse ++ vHist) v2 t2 n2 c2 = true) :
    checkAltHighDBandLoop m r vHist (v1 ++ v2) (t1 ++ t2) (n1 ++ n2) (c1 ++ c2) = true := by
  induction v1 generalizing r vHist t1 n1 c1 with
  | nil =>
    cases t1 with
    | nil =>
      cases n1 with
      | nil =>
        cases c1 with
        | nil => simpa using h2
        | cons _ _ => simp at hc
      | cons _ _ => simp at hn
    | cons _ _ => simp at ht
  | cons vR vRest ih =>
    cases t1 with
    | nil => simp at ht
    | cons tau9 tauRest =>
      cases n1 with
      | nil => simp at hn
      | cons nSub nsubRest =>
        cases c1 with
        | nil => simp at hc
        | cons dCap dcapRest =>
          cases vHist with
          | nil =>
            unfold checkAltHighDBandLoop checkAltHighDBandLoopAux at h1
            simp only [highd_primNatBlt_eq] at h1
            cases hg : Bool.or (Nat.blt r 2) (Nat.blt 1024 r) <;>
              simp [hg, cond] at h1
          | cons vPrev vhRest =>
            simp only [List.cons_append]; rw [highd_checkAltHighDBandLoop_cons] at h1 ⊢
            dsimp only at h1 ⊢
            cases hrg : Bool.or (Nat.blt r 2) (Nat.blt 1024 r) with
            | true => rw [hrg, highd_cond_true] at h1; exact Bool.noConfusion h1
            | false =>
              rw [hrg, highd_cond_false] at h1; rw [highd_cond_false]
              cases hlt : Nat.blt vR vPrev with
              | true => rw [hlt, highd_cond_true] at h1; exact Bool.noConfusion h1
              | false =>
                rw [hlt, highd_cond_false] at h1; rw [highd_cond_false]
                revert h1
                set stepOk : Bool := cond (tau9 == 0) (checkEigStep m r vR vPrev) (
                      let d := highdNatMin m r
                      let rowLo12 := altEvalRowHighDLo12 m r tau9 nSub dCap
                      let rLen := altListLen rowLo12
                      cond (Bool.or (rLen == 0) (Bool.or (Nat.blt d rLen)
                            (Bool.or (altSumNat rowLo12 == 0)
                              (Nat.blt (altListLen (vPrev :: vhRest)) rLen))))
                        false
                        (
                          let drift27 := altDriftSum27 vR rowLo12 (vPrev :: vhRest)
                          Nat.blt (Nat.mul tau9 1000000000000000000) drift27))
                intro h1
                cases hs : stepOk with
                | false => rw [hs, highd_cond_false] at h1; exact Bool.noConfusion h1
                | true =>
                  rw [hs, highd_cond_true] at h1; rw [highd_cond_true]
                  have hrev : (vR :: vRest).reverse ++ (vPrev :: vhRest) =
                      vRest.reverse ++ (vR :: vPrev :: vhRest) := by simp [List.reverse_cons]
                  have hr_add : r + (vR :: vRest).length = Nat.succ r + vRest.length := by
                    simp; omega
                  rw [hrev, hr_add] at h2
                  exact ih (Nat.succ r) (vR :: vPrev :: vhRest) tauRest nsubRest dcapRest
                    (by simpa using ht) (by simpa using hn) (by simpa using hc) h1 h2
/-- Tail-recursive `xs.reverse ++ acc` over `ℕ` for kernel-evaluated `checkAltHighDBandLoop`
  sub-band chaining without elaborator recursion on `v1.reverse ++ vHist`. -/
def highdBandRevAppend : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | x :: xs, acc => highdBandRevAppend xs (x :: acc)
private theorem highdBandRevAppend_eq :
    ∀ (xs acc : List ℕ), highdBandRevAppend xs acc = xs.reverse ++ acc
  | [], acc => by simp [highdBandRevAppend]
  | x :: xs, acc => by
    unfold highdBandRevAppend; rw [highdBandRevAppend_eq xs (x :: acc)]; simp [List.append_assoc]
/-- Kernel-evaluated boolean list equality on `List ℕ` for sub-band chaining. -/
def highdBandListEq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Bool.and (Nat.beq x y) (highdBandListEq xs ys)
  | _, _ => false
private theorem highdBandListEq_eq_true : ∀ {xs ys : List ℕ}, highdBandListEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h => Bool.noConfusion h
  | [], _ :: _, h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    dsimp only [highdBandListEq] at h; rw [highd_to_beq (fun {a b} ↦ Nat.beq_eq) x y] at h
    have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [highd_nat_beq_eq_true.mp h1, highdBandListEq_eq_true h2]
/-- Boolean-guarded wrapper around `checkAltHighDBandLoop_append` avoiding elaborator `rfl`
  on long `vHist` and output lists. -/
theorem checkAltHighDBandLoop_chain (m r r' : ℕ)
    (vHist vHist' v1 v2 t1 t2 n1 n2 c1 c2 vt tt nt ct : List ℕ) (hguard :
      Bool.and (Nat.beq t1.length v1.length) (Bool.and (Nat.beq n1.length v1.length)
      (Bool.and (Nat.beq c1.length v1.length) (Bool.and (Nat.beq (Nat.add r v1.length) r')
      (Bool.and (highdBandListEq (highdBandRevAppend v1 vHist) vHist')
      (Bool.and (highdBandListEq (v1 ++ v2) vt) (Bool.and (highdBandListEq (t1 ++ t2) tt)
      (Bool.and (highdBandListEq (n1 ++ n2) nt) (highdBandListEq (c1 ++ c2) ct)))))))) = true)
    (h1 : checkAltHighDBandLoop m r vHist v1 t1 n1 c1 = true)
    (h2 : checkAltHighDBandLoop m r' vHist' v2 t2 n2 c2 = true) :
    checkAltHighDBandLoop m r vHist vt tt nt ct = true := by
  rw [highd_to_beq (fun {a b} ↦ Nat.beq_eq) t1.length v1.length,
    highd_to_beq (fun {a b} ↦ Nat.beq_eq) n1.length v1.length,
    highd_to_beq (fun {a b} ↦ Nat.beq_eq) c1.length v1.length,
    highd_to_beq (fun {a b} ↦ Nat.beq_eq) (Nat.add r v1.length) r'] at hguard
  have ⟨ht, g1⟩ := (Bool.and_eq_true _ _).mp hguard; have ⟨hn, g2⟩ := (Bool.and_eq_true _ _).mp g1
  have ⟨hc, g3⟩ := (Bool.and_eq_true _ _).mp g2; have ⟨hr', g4⟩ := (Bool.and_eq_true _ _).mp g3
  have ⟨hvh, g5⟩ := (Bool.and_eq_true _ _).mp g4; have ⟨hvt, g6⟩ := (Bool.and_eq_true _ _).mp g5
  have ⟨htt, g7⟩ := (Bool.and_eq_true _ _).mp g6; have ⟨hnt, hct⟩ := (Bool.and_eq_true _ _).mp g7
  have ht' : t1.length = v1.length := highd_nat_beq_eq_true.mp ht
  have hn' : n1.length = v1.length := highd_nat_beq_eq_true.mp hn
  have hc' : c1.length = v1.length := highd_nat_beq_eq_true.mp hc
  have hr_eq : r + v1.length = r' := highd_nat_beq_eq_true.mp hr'
  have hvh_eq : v1.reverse ++ vHist = vHist' := by
    rw [← highdBandRevAppend_eq]; exact highdBandListEq_eq_true hvh
  rw [← hr_eq, ← hvh_eq] at h2
  rw [← highdBandListEq_eq_true hvt, ← highdBandListEq_eq_true htt,
    ← highdBandListEq_eq_true hnt, ← highdBandListEq_eq_true hct]
  exact checkAltHighDBandLoop_append m r vHist v1 v2 t1 t2 n1 n2 c1 c2 ht' hn' hc' h1 h2
private theorem highd_getD_nat_zero_of_le : ∀ (xs : List ℕ) (j : ℕ), xs.length ≤ j → xs.getD j 0 = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | _ :: xs, j + 1, h => highd_getD_nat_zero_of_le xs j (by simpa using h)
private theorem highd_append_getD_left :
    ∀ (xs ys : List ℕ) (j : ℕ), j < xs.length → (xs ++ ys).getD j 0 = xs.getD j 0
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, j + 1, hj =>
    highd_append_getD_left xs ys j (by simp at hj; omega)
private theorem highd_append_getD_right :
    ∀ (xs ys : List ℕ) (j : ℕ), xs.length ≤ j → (xs ++ ys).getD j 0 = ys.getD (j - xs.length) 0
  | [], ys, j, _ => by simp
  | _ :: _, _, 0, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | _ :: xs, ys, j + 1, h => by
    have ih := highd_append_getD_right xs ys j (by simpa using h)
    simpa [Nat.succ_sub_succ_eq_sub] using ih
private theorem highd_reverse_getD :
    ∀ (xs : List ℕ) (j : ℕ), j < xs.length → xs.reverse.getD j 0 = xs.getD (xs.length - 1 - j) 0
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | x :: xs, j, hj => by
    simp only [List.reverse_cons]; have hrlen : xs.reverse.length = xs.length := List.length_reverse
    by_cases hlt : j < xs.length
    · rw [highd_append_getD_left xs.reverse [x] j (by omega),
        highd_reverse_getD xs j hlt]
      have hidx : (x :: xs).length - 1 - j = (xs.length - 1 - j) + 1 := by simp; omega
      rw [hidx]; rfl
    · have hjeq : j = xs.length := by simp at hj; omega
      subst hjeq
      rw [highd_append_getD_right xs.reverse [x] xs.length (by omega)]; simp [hrlen]
private theorem highd_sum_range_succ_shift (f : ℕ → ℕ) :
    ∀ d : ℕ, (∑ j ∈ Finset.range (d + 1), f j) = f 0 + ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by simp
  | d + 1 => by
    rw [Finset.sum_range_succ, highd_sum_range_succ_shift f d, Finset.sum_range_succ, add_assoc]
private theorem highd_sum_Icc_one_succ (f : ℕ → ℝ) (d : ℕ) :
    (∑ w ∈ Finset.Icc 1 (d + 1), f w) = (∑ w ∈ Finset.Icc 1 d, f w) + f (d + 1) := by
  have hdisj : Disjoint (Finset.Icc 1 d) ({d + 1} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_Icc]; omega
  have hunion : Finset.Icc 1 (d + 1) = Finset.Icc 1 d ∪ {d + 1} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
  rw [hunion, Finset.sum_union hdisj, Finset.sum_singleton]
private theorem highd_altSumNat_eq_sum_range_len : ∀ (rLen : ℕ) (xs : List ℕ), xs.length = rLen →
      altSumNat xs = ∑ j ∈ Finset.range rLen, xs.getD j 0
  | 0, [], _ => by simp [altSumNat]
  | rLen + 1, x :: xs, hlen => by
    rw [highd_sum_range_succ_shift]
    have ih := highd_altSumNat_eq_sum_range_len rLen xs (by simpa using hlen)
    simpa [altSumNat] using congrArg (Nat.add x) ih
private theorem highd_altSumNat_eq_sum_range_le {d : ℕ} {xs : List ℕ} (hle : xs.length ≤ d) :
    altSumNat xs = ∑ j ∈ Finset.range d, xs.getD j 0 := by
  rw [highd_altSumNat_eq_sum_range_len xs.length xs rfl]
  refine Finset.sum_subset (Finset.range_mono hle) fun j hj hnot ↦ ?_
  have hge : xs.length ≤ j := Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hnot)
  exact highd_getD_nat_zero_of_le xs j hge
private theorem highd_altDriftSum27_eq_sum_range_len (vR : ℕ) :
    ∀ (rLen : ℕ) (ps vhs : List ℕ), ps.length = rLen → rLen ≤ vhs.length → altDriftSum27 vR ps vhs =
        ∑ j ∈ Finset.range rLen, ps.getD j 0 * (vR - vhs.getD j 0)
  | 0, [], _, _, _ => by simp [altDriftSum27]
  | rLen + 1, p :: ps, vh :: vhs, hps, hvhs => by
    rw [highd_sum_range_succ_shift]; have ih := highd_altDriftSum27_eq_sum_range_len vR rLen ps vhs
      (by simpa using hps) (by simpa using hvhs)
    simpa [altDriftSum27] using congrArg (Nat.add (p * (vR - vh))) ih
private theorem highd_checkAltHighDBandLoop_lengths (m : ℕ) :
    ∀ (vRem tauRem nsubRem dcapRem vHist : List ℕ) (r : ℕ),
      checkAltHighDBandLoop m r vHist vRem tauRem nsubRem dcapRem = true →
      tauRem.length = vRem.length ∧ nsubRem.length = vRem.length ∧ dcapRem.length = vRem.length
  | [], [], [], [], _, _, _ => ⟨rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, h => by simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at h
  | [], [], _ :: _, _, _, _, h => by simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at h
  | [], [], [], _ :: _, _, _, h => by simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at h
  | _ :: _, [], _, _, _, _, h => by simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at h
  | _ :: _, _ :: _, [], _, _, _, h => by simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, h => by
    simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at h
  | vR :: vRest, tau9 :: tauRest, nSub :: nsubRest, dCap :: dcapRest, [], r, h => by
    unfold checkAltHighDBandLoop checkAltHighDBandLoopAux at h; simp only [highd_primNatBlt_eq] at h
    cases hg : Bool.or (Nat.blt r 2) (Nat.blt 1024 r) <;> simp [hg, cond] at h
  | vR :: vRest, tau9 :: tauRest, nSub :: nsubRest, dCap :: dcapRest, vPrev :: vhRest, r, h => by
    rw [highd_checkAltHighDBandLoop_cons] at h; dsimp only at h
    cases hrg : Bool.or (Nat.blt r 2) (Nat.blt 1024 r) with
    | true => rw [hrg, highd_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hrg, highd_cond_false] at h
      cases hlt : Nat.blt vR vPrev with
      | true => rw [hlt, highd_cond_true] at h; exact Bool.noConfusion h
      | false =>
        rw [hlt, highd_cond_false] at h
        revert h
        set stepOk : Bool := cond (tau9 == 0) (checkEigStep m r vR vPrev) (
              let d := highdNatMin m r
              let rowLo12 := altEvalRowHighDLo12 m r tau9 nSub dCap
              let rLen := altListLen rowLo12
              cond (Bool.or (rLen == 0) (Bool.or (Nat.blt d rLen)
                    (Bool.or (altSumNat rowLo12 == 0)
                      (Nat.blt (altListLen (vPrev :: vhRest)) rLen))))
                false
                (
                  let drift27 := altDriftSum27 vR rowLo12 (vPrev :: vhRest)
                  Nat.blt (Nat.mul tau9 1000000000000000000) drift27))
        intro h
        cases hs : stepOk with
        | false => rw [hs, highd_cond_false] at h; exact Bool.noConfusion h
        | true =>
          rw [hs, highd_cond_true] at h
          obtain ⟨ht, hn, hc⟩ := highd_checkAltHighDBandLoop_lengths m
            vRest tauRest nsubRest dcapRest (vR :: vPrev :: vhRest) (Nat.succ r) h
          exact ⟨congrArg Nat.succ ht, congrArg Nat.succ hn, congrArg Nat.succ hc⟩
private theorem highd_checkAltHighDBandLoop_step_props (m rBase : ℕ)
    (vAll tauAll nsubAll dcapExt : List ℕ) :
    ∀ (vRem tauRem nsubRem dcapRem vHist : List ℕ) (r : ℕ), rBase ≤ r → 2 ≤ r → vHist.length = r →
      (∀ j < r, vHist.getD j 0 = vAll.getD (r - 1 - j) 0) →
      (∀ j < vRem.length, vRem.getD j 0 = vAll.getD (r + j) 0) →
      (∀ j < tauRem.length, tauRem.getD j 0 = tauAll.getD (r - 2 + j) 0) →
      (∀ j < nsubRem.length, nsubRem.getD j 0 = nsubAll.getD (r - 2 + j) 0) →
      (∀ j < dcapRem.length, dcapRem.getD j 0 = dcapExt.getD (r - rBase + j) 0) →
      checkAltHighDBandLoop m r vHist vRem tauRem nsubRem dcapRem = true →
      ∀ s : ℕ, r ≤ s → s < r + vRem.length → vAll.getD (s - 1) 0 ≤ vAll.getD s 0 ∧
        (tauAll.getD (s - 2) 0 = 0 →
          checkEigStep m s (vAll.getD s 0) (vAll.getD (s - 1) 0) = true) ∧
        (0 < tauAll.getD (s - 2) 0 →
          let d := min m s
          let row := altEvalRowHighDLo12 m s (tauAll.getD (s - 2) 0)
            (nsubAll.getD (s - 2) 0) (dcapExt.getD (s - rBase) 0)
          1 ≤ row.length ∧ row.length ≤ d ∧ 0 < altSumNat row ∧
            tauAll.getD (s - 2) 0 * 1000000000000000000 <
              ∑ j ∈ Finset.range d, row.getD j 0 * (vAll.getD s 0 - vAll.getD (s - 1 - j) 0))
  | [], _, _, _, _, r, _, _, _, _, _, _, _, _, _, s, hrs, hslt => by simp at hslt; omega
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, hchk, _, _, _ => by
    simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at hchk
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, hchk, _, _, _ => by
    simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at hchk
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, hchk, _, _, _ => by
    simp [checkAltHighDBandLoop, checkAltHighDBandLoopAux] at hchk
  | _ :: _, _ :: _, _ :: _, _ :: _, [], r, _, hr2, hvh_len, _, _, _, _, _, _, _, _, _ => by
    simp at hvh_len; omega
  | vR :: vRest, tau9 :: tauRest, nSub :: nsubRest, dCap :: dcapRest, vPrev :: vhRest, r,
      hrBase, hr2, hvh_len, hvh_eq, hv_eq, ht_eq, hn_eq, hdc_eq, hchk, s, hrs, hslt => by
    have hvR_eq : vR = vAll.getD r 0 := by simpa using hv_eq 0 (Nat.succ_pos _)
    have hvPrev_eq : vPrev = vAll.getD (r - 1) 0 := by simpa using hvh_eq 0 (by omega)
    have htau_eq : tau9 = tauAll.getD (r - 2) 0 := by simpa using ht_eq 0 (Nat.succ_pos _)
    have hnsub_eq : nSub = nsubAll.getD (r - 2) 0 := by simpa using hn_eq 0 (Nat.succ_pos _)
    have hdcap_eq : dCap = dcapExt.getD (r - rBase) 0 := by simpa using hdc_eq 0 (Nat.succ_pos _)
    rw [highd_checkAltHighDBandLoop_cons] at hchk; dsimp only at hchk
    cases hrg : Bool.or (Nat.blt r 2) (Nat.blt 1024 r) with
    | true => rw [hrg, highd_cond_true] at hchk; exact Bool.noConfusion hchk
    | false =>
      rw [hrg, highd_cond_false] at hchk
      cases hblt : Nat.blt vR vPrev with
      | true => rw [hblt, highd_cond_true] at hchk; exact Bool.noConfusion hchk
      | false =>
        rw [hblt, highd_cond_false] at hchk
        have hv_mono : vPrev ≤ vR := highd_nat_blt_eq_false.mp hblt
        revert hchk
        set stepOk : Bool := cond (tau9 == 0) (checkEigStep m r vR vPrev) (
              let d := highdNatMin m r
              let rowLo12 := altEvalRowHighDLo12 m r tau9 nSub dCap
              let rLen := altListLen rowLo12
              cond (Bool.or (rLen == 0) (Bool.or (Nat.blt d rLen)
                    (Bool.or (altSumNat rowLo12 == 0)
                      (Nat.blt (altListLen (vPrev :: vhRest)) rLen))))
                false
                (
                  let drift27 := altDriftSum27 vR rowLo12 (vPrev :: vhRest)
                  Nat.blt (Nat.mul tau9 1000000000000000000) drift27))
        intro hchk
        cases hs_ok : stepOk with
        | false => rw [hs_ok, highd_cond_false] at hchk; exact Bool.noConfusion hchk
        | true =>
          rw [hs_ok, highd_cond_true] at hchk
          by_cases hsr : s = r
          · subst hsr
            rw [← hvR_eq, ← hvPrev_eq, ← htau_eq, ← hnsub_eq, ← hdcap_eq]
            refine ⟨hv_mono, fun ht0 ↦ ?_, fun ht_pos ↦ ?_⟩
            · dsimp only [stepOk] at hs_ok; rw [ht0] at hs_ok; have hz : (0 == 0) = true := rfl
              rw [hz, highd_cond_true] at hs_ok; exact hs_ok
            · dsimp only [stepOk] at hs_ok
              have ht_f : (tau9 == 0) = false := highd_nat_beq_eq_false.mpr (Nat.ne_of_gt ht_pos)
              rw [ht_f, highd_cond_false, highd_natMin_eq] at hs_ok
              set d := min m s
              set rowLo12 := altEvalRowHighDLo12 m s tau9 nSub dCap
              cases hbad : Bool.or (altListLen rowLo12 == 0)
                  (Bool.or (Nat.blt d (altListLen rowLo12)) (Bool.or (altSumNat rowLo12 == 0)
                      (Nat.blt (altListLen (vPrev :: vhRest)) (altListLen rowLo12)))) with
              | true => rw [hbad, highd_cond_true] at hs_ok; exact Bool.noConfusion hs_ok
              | false =>
                rw [hbad, highd_cond_false] at hs_ok
                clear_value rowLo12
                simp only [Bool.or_eq_false_iff, highd_nat_beq_eq_false,
                  highd_nat_blt_eq_false, highd_altListLen_eq] at hbad
                obtain ⟨hr_ne0, hr_le_d, hsum_ne, hvh_ge⟩ := hbad
                have hdrift_lt := highd_nat_blt_eq_true.mp hs_ok
                rw [highd_altDriftSum27_eq_sum_range_len vR rowLo12.length rowLo12
                  (vPrev :: vhRest) rfl hvh_ge] at hdrift_lt
                have hsum_ext : (∑ j ∈ Finset.range rowLo12.length,
                      rowLo12.getD j 0 * (vR - (vPrev :: vhRest).getD j 0)) = (∑ j ∈ Finset.range d,
                      rowLo12.getD j 0 * (vR - vAll.getD (s - 1 - j) 0)) := by
                  have h1 : (∑ j ∈ Finset.range rowLo12.length,
                        rowLo12.getD j 0 * (vR - (vPrev :: vhRest).getD j 0)) =
                      (∑ j ∈ Finset.range rowLo12.length,
                        rowLo12.getD j 0 * (vR - vAll.getD (s - 1 - j) 0)) := by
                    refine Finset.sum_congr rfl fun j hj ↦ ?_; have hj_lt : j < s :=
                      (Finset.mem_range.mp hj).trans_le (hr_le_d.trans (Nat.min_le_right m s))
                    rw [hvh_eq j hj_lt]
                  rw [h1]
                  refine Finset.sum_subset (Finset.range_mono hr_le_d) fun j _ hnot ↦ ?_
                  have hge : rowLo12.length ≤ j :=
                    Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hnot)
                  rw [highd_getD_nat_zero_of_le rowLo12 j hge, Nat.zero_mul]
                rw [hsum_ext] at hdrift_lt
                exact ⟨Nat.pos_of_ne_zero hr_ne0, hr_le_d, Nat.pos_of_ne_zero hsum_ne, hdrift_lt⟩
          · have hs_ge : r + 1 ≤ s := by omega
            have hs_lt' : s < (r + 1) + vRest.length := by simp at hslt; omega
            exact highd_checkAltHighDBandLoop_step_props m rBase vAll tauAll nsubAll dcapExt
              vRest tauRest nsubRest dcapRest (vR :: vPrev :: vhRest) (r + 1)
              (by omega) (by omega)
              (by simp [hvh_len])
              (fun j hj ↦ by
                rcases j with _ | j'
                · rw [List.getD_cons_zero, show r + 1 - 1 - 0 = r by omega]
                  exact hvR_eq
                · rw [List.getD_cons_succ, show r + 1 - 1 - (j' + 1) = r - 1 - j' by omega]
                  exact hvh_eq j' (by omega))
              (fun j hj ↦ by
                have h1 := hv_eq (j + 1) (by simp; omega)
                rw [List.getD_cons_succ, show r + (j + 1) = (r + 1) + j by omega] at h1
                exact h1)
              (fun j hj ↦ by
                have h1 := ht_eq (j + 1) (by simp; omega)
                rw [List.getD_cons_succ, show r - 2 + (j + 1) = (r + 1) - 2 + j by omega] at h1
                exact h1)
              (fun j hj ↦ by
                have h1 := hn_eq (j + 1) (by simp; omega)
                rw [List.getD_cons_succ, show r - 2 + (j + 1) = (r + 1) - 2 + j by omega] at h1
                exact h1)
              (fun j hj ↦ by
                have h1 := hdc_eq (j + 1) (by simp; omega)
                rw [List.getD_cons_succ, show r - rBase + (j + 1) = (r + 1) - rBase + j by omega]
                  at h1
                exact h1)
              hchk s hs_ge hs_lt'
private theorem highd_checkAltDirectTable12_header {m rSplit : ℕ} {vPref tauPref nsubPref : List ℕ}
    (h : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true) :
    1 ≤ m ∧ m ≤ 8192 ∧ 2 ≤ rSplit ∧ rSplit ≤ 1024 ∧
      vPref.length = rSplit + 1 ∧ tauPref.length = rSplit - 1 ∧ nsubPref.length = rSplit - 1 := by
  unfold checkAltDirectTable12 at h
  cases hg1 : Bool.or (primNatBlt m 1)
      (Bool.or (primNatBlt 8192 m) (Bool.or (primNatBlt rSplit 2) (primNatBlt 1024 rSplit))) with
  | true => rw [hg1, highd_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg1, highd_cond_false] at h
    simp only [Bool.or_eq_false_iff, highd_primNatBlt_eq, highd_nat_blt_eq_false] at hg1
    obtain ⟨hm1, hm8, hr2, hr10⟩ := hg1
    rw [highd_to_beq (fun {a b} ↦ Nat.beq_eq) (altListLen vPref) (Nat.add rSplit 1),
      highd_to_beq (fun {a b} ↦ Nat.beq_eq) (altListLen tauPref) (Nat.sub rSplit 1),
      highd_to_beq (fun {a b} ↦ Nat.beq_eq) (altListLen nsubPref) (Nat.sub rSplit 1)] at h
    cases hg2 : Bool.or (Bool.not (altListLen vPref == Nat.add rSplit 1))
        (Bool.or (Bool.not (altListLen tauPref == Nat.sub rSplit 1))
          (Bool.not (altListLen nsubPref == Nat.sub rSplit 1))) with
    | true => rw [hg2, highd_cond_true] at h; exact Bool.noConfusion h
    | false =>
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', highd_nat_beq_eq_true,
        highd_altListLen_eq] at hg2
      exact ⟨hm1, hm8, hr2, hr10, hg2.1, hg2.2.1, hg2.2.2⟩
private theorem highd_combined_props {m rSplit kMax : ℕ}
    {vPref tauPref nsubPref vExt tauExt nsubExt dcapExt : List ℕ}
    (hrSplit_le : rSplit ≤ kMax)
    (hpref : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true)
    (hext : checkAltHighDBandLoop m (rSplit + 1) vPref.reverse vExt tauExt nsubExt dcapExt = true)
    (hlen_ext : vExt.length = kMax - rSplit) :
    let vAll := vPref ++ vExt
    let tauAll := tauPref ++ tauExt
    let nsubAll := nsubPref ++ nsubExt
    1 ≤ m ∧ m ≤ 8192 ∧ 2 ≤ rSplit ∧ (∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ kMax →
        (vAll.getD r₁ 0 : ℝ) / wdScaleR ≤ (vAll.getD r₂ 0 : ℝ) / wdScaleR) ∧
      (∀ s : ℕ, rSplit + 1 ≤ s → s ≤ kMax → (tauAll.getD (s - 2) 0 = 0 →
          checkEigStep m s (vAll.getD s 0) (vAll.getD (s - 1) 0) = true) ∧
        (0 < tauAll.getD (s - 2) 0 →
          let d := min m s
          let row := altEvalRowHighDLo12 m s (tauAll.getD (s - 2) 0)
            (nsubAll.getD (s - 2) 0) (dcapExt.getD (s - (rSplit + 1)) 0)
          1 ≤ row.length ∧ row.length ≤ d ∧ 0 < altSumNat row ∧
            tauAll.getD (s - 2) 0 * 1000000000000000000 <
              ∑ j ∈ Finset.range d, row.getD j 0 * (vAll.getD s 0 - vAll.getD (s - 1 - j) 0))) := by
  intro vAll tauAll nsubAll
  obtain ⟨hm1, hm8, hr2, _, hvP, htP, hnP⟩ := highd_checkAltDirectTable12_header hpref
  obtain ⟨htE, hnE, hcE⟩ := highd_checkAltHighDBandLoop_lengths m
    vExt tauExt nsubExt dcapExt vPref.reverse (rSplit + 1) hext
  let SP := altWalkSpecOf m rSplit rSplit vPref tauPref nsubPref hr2 le_rfl hpref
  have hloop := highd_checkAltHighDBandLoop_step_props m (rSplit + 1)
    vAll tauAll nsubAll dcapExt vExt tauExt nsubExt dcapExt vPref.reverse (rSplit + 1)
    le_rfl (by omega)
    (by rw [List.length_reverse, hvP])
    (fun j hj ↦ by
      rw [highd_reverse_getD vPref j (by omega), hvP]
      have hidx : rSplit + 1 - 1 - j < vPref.length := by rw [hvP]; omega
      exact (highd_append_getD_left vPref vExt _ hidx).symm)
    (fun j _ ↦ by
      rw [highd_append_getD_right vPref vExt (rSplit + 1 + j) (by omega)]
      simp [hvP])
    (fun j _ ↦ by
      have hidx : rSplit - 1 ≤ (rSplit + 1) - 2 + j := by omega
      rw [highd_append_getD_right tauPref tauExt ((rSplit + 1) - 2 + j) (by omega)]
      have hsub : (rSplit + 1) - 2 + j - tauPref.length = j := by rw [htP]; omega
      rw [hsub])
    (fun j _ ↦ by
      rw [highd_append_getD_right nsubPref nsubExt ((rSplit + 1) - 2 + j) (by omega)]
      have hsub : (rSplit + 1) - 2 + j - nsubPref.length = j := by rw [hnP]; omega
      rw [hsub])
    (fun j _ ↦ by simp)
    hext
  have hstep_mono : ∀ s : ℕ, 1 ≤ s → s ≤ kMax →
      (vAll.getD (s - 1) 0 : ℝ) / wdScaleR ≤ (vAll.getD s 0 : ℝ) / wdScaleR := by
    intro s hs1 hsk
    by_cases hle : s ≤ rSplit
    · have hv1 : vAll.getD (s - 1) 0 = vPref.getD (s - 1) 0 :=
        highd_append_getD_left vPref vExt (s - 1) (by omega)
      have hv2 : vAll.getD s 0 = vPref.getD s 0 :=
        highd_append_getD_left vPref vExt s (by omega)
      rw [hv1, hv2]; exact SP.hV_mono (by omega) hle
    · have hB_nn : (0 : ℝ) ≤ wdScaleR := by unfold wdScaleR wdScale; positivity
      have hm_nat := (hloop s (by omega) (by omega)).1
      exact div_le_div_of_nonneg_right (by exact_mod_cast hm_nat) hB_nn
  have hmono : ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ kMax →
      (vAll.getD r₁ 0 : ℝ) / wdScaleR ≤ (vAll.getD r₂ 0 : ℝ) / wdScaleR := by
    intro r₁ r₂ h12 h2k
    induction h12 with
    | refl => exact le_rfl
    | @step b _ ih => exact (ih (by omega)).trans (hstep_mono (b + 1) (by omega) h2k)
  exact ⟨hm1, hm8, hr2, hmono, fun s hs_lo hs_hi ↦ (hloop s hs_lo (by omega)).2⟩
private theorem highd_sum_Icc_one_eq_range (f : ℕ → ℝ) :
    ∀ d : ℕ, (∑ w ∈ Finset.Icc 1 d, f w) = ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by
    have hset : Finset.Icc (1 : ℕ) 0 = ∅ := by ext x; simp
    rw [hset]; simp
  | d + 1 => by rw [highd_sum_Icc_one_succ, highd_sum_Icc_one_eq_range f d, Finset.sum_range_succ]
/-- Unified `JohnsonWalkSpec m k` (`n0 = altN0 = 80000`) chaining a `T_8` direct table
  `checkAltDirectTable12 m rSplit` (`r ≤ rSplit`) with a `T_16` causal-window band
  `checkAltHighDBandLoop m (rSplit + 1)` (`r = rSplit + 1.. kMax`). -/
noncomputable def altHighDWalkSpecOf (m k rSplit kMax : ℕ)
    (vPref tauPref nsubPref vExt tauExt nsubExt dcapExt : List ℕ)
    (_hk2 : 2 ≤ k) (hk_le : k ≤ kMax) (hrSplit_le : rSplit ≤ kMax)
    (hpref : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true)
    (hext : checkAltHighDBandLoop m (rSplit + 1) vPref.reverse vExt tauExt nsubExt dcapExt = true)
    (hlen_ext : vExt.length = kMax - rSplit) : JohnsonWalkSpec m k :=
  let vAll := vPref ++ vExt
  let tauAll := tauPref ++ tauExt
  let nsubAll := nsubPref ++ nsubExt
  let rowAt := fun r : ℕ ↦
    if r ≤ rSplit then altEvalRowLo12 m r (tauAll.getD (r - 2) 0) (nsubAll.getD (r - 2) 0)
    else
      altEvalRowHighDLo12 m r (tauAll.getD (r - 2) 0)
        (nsubAll.getD (r - 2) 0) (dcapExt.getD (r - (rSplit + 1)) 0)
  { useWalk := fun r ↦ decide (2 ≤ r ∧ 0 < tauAll.getD (r - 2) 0)
    n0 := altN0
    hn0 := by unfold altN0; omega
    stages := fun n r ↦ altStages (tauAll.getD (r - 2) 0) (nsubAll.getD (r - 2) 0) m n
    V := fun r ↦ (vAll.getD r 0 : ℝ) / wdScaleR
    hV0 := by
      obtain ⟨_, _, hr2, _, hvP, _, _⟩ := highd_checkAltDirectTable12_header hpref
      let SP := altWalkSpecOf m rSplit rSplit vPref tauPref nsubPref hr2 le_rfl hpref
      have h0 : vAll.getD 0 0 = vPref.getD 0 0 :=
        highd_append_getD_left vPref vExt 0 (by omega)
      dsimp only [vAll] at h0 ⊢; rw [h0]; exact SP.hV0
    hV_mono := fun {r₁ r₂} h12 h2k ↦
      (highd_combined_props hrSplit_le hpref hext hlen_ext).2.2.2.1 h12 (h2k.trans hk_le)
    hV_eig := fun r hr1 hrk hcase ↦ by
      obtain ⟨_, _, hr2, _, hvP, htP, _⟩ := highd_checkAltDirectTable12_header hpref
      let SP := altWalkSpecOf m rSplit rSplit vPref tauPref nsubPref hr2 le_rfl hpref
      by_cases hrs : r ≤ rSplit
      · have hvR : vAll.getD r 0 = vPref.getD r 0 :=
          highd_append_getD_left vPref vExt r (by omega)
        have hvP1 : vAll.getD (r - 1) 0 = vPref.getD (r - 1) 0 :=
          highd_append_getD_left vPref vExt (r - 1) (by omega)
        have hcase' : r = 1 ∨ SP.useWalk r = false := by
          rcases hcase with rfl | hf
          · exact Or.inl rfl
          · by_cases hr_eq1 : r = 1
            · exact Or.inl hr_eq1
            · right
              have ht_eq : tauAll.getD (r - 2) 0 = tauPref.getD (r - 2) 0 :=
                highd_append_getD_left tauPref tauExt (r - 2) (by omega)
              dsimp only [SP, altWalkSpecOf]; rw [decide_eq_false_iff_not] at hf ⊢
              intro ⟨hr2', hpos⟩
              rw [← ht_eq] at hpos; exact hf ⟨hr2', hpos⟩
        dsimp only [vAll] at hvR hvP1 ⊢; rw [hvR, hvP1]; exact SP.hV_eig r hr1 hrs hcase'
      · have hgt : rSplit + 1 ≤ r := by omega
        have ht0 : tauAll.getD (r - 2) 0 = 0 := by
          rcases hcase with rfl | hf
          · omega
          · simp only [decide_eq_false_iff_not, not_and, not_lt, Nat.le_zero] at hf
            exact hf (by omega)
        have heig :=
          ((highd_combined_props hrSplit_le hpref hext hlen_ext).2.2.2.2 r hgt
            (hrk.trans hk_le)).1 ht0
        exact checkEigStep_sound heig
    pLo := fun r w ↦
      if 1 ≤ w ∧ w ≤ min m r then (((rowAt r).getD (w - 1) 0 : ℝ) / 1000000000000) else 0
    hpLo_nonneg := fun r w ↦ by
      split_ifs <;> positivity
    hpLo_sum_pos := fun r hr2_r hrk huse ↦ by
      simp only [decide_eq_true_eq] at huse
      obtain ⟨_, _, hr2, _, _, htP, hnP⟩ := highd_checkAltDirectTable12_header hpref
      let SP := altWalkSpecOf m rSplit rSplit vPref tauPref nsubPref hr2 le_rfl hpref
      by_cases hrs : r ≤ rSplit
      · have ht_eq : tauAll.getD (r - 2) 0 = tauPref.getD (r - 2) 0 :=
          highd_append_getD_left tauPref tauExt (r - 2) (by omega)
        have hn_eq : nsubAll.getD (r - 2) 0 = nsubPref.getD (r - 2) 0 :=
          highd_append_getD_left nsubPref nsubExt (r - 2) (by omega)
        have huseP : SP.useWalk r = true := by
          dsimp only [SP, altWalkSpecOf]; rw [decide_eq_true_eq]; exact ⟨hr2_r, ht_eq ▸ huse.2⟩
        have hsp := SP.hpLo_sum_pos r hr2_r hrs huseP
        refine hsp.trans_eq (Finset.sum_congr rfl fun w _ ↦ ?_)
        dsimp only [SP, altWalkSpecOf, rowAt]; rw [ite_eq_left hrs, ht_eq, hn_eq]
      · have hgt : rSplit + 1 ≤ r := by omega
        obtain ⟨_, hr_le_d, hsum_pos, _⟩ :=
          ((highd_combined_props hrSplit_le hpref hext hlen_ext).2.2.2.2 r hgt
            (hrk.trans hk_le)).2 huse.2
        set d := min m r
        have hrow_eq : rowAt r = altEvalRowHighDLo12 m r (tauAll.getD (r - 2) 0)
            (nsubAll.getD (r - 2) 0) (dcapExt.getD (r - (rSplit + 1)) 0) := by
          dsimp only [rowAt]; rw [ite_eq_right hrs]
        set row := rowAt r
        rw [← hrow_eq] at hr_le_d hsum_pos
        clear_value row
        rw [highd_altSumNat_eq_sum_range_le hr_le_d] at hsum_pos
        have hsumR : (0 : ℝ) < ∑ j ∈ Finset.range d, (row.getD j 0 : ℝ) := by
          exact_mod_cast hsum_pos
        rw [highd_sum_Icc_one_eq_range]
        have hcongr : (∑ j ∈ Finset.range d, (if 1 ≤ j + 1 ∧ j + 1 ≤ d then
                (row.getD ((j + 1) - 1) 0 : ℝ) / 1000000000000 else 0)) =
            (∑ j ∈ Finset.range d, (row.getD j 0 : ℝ)) / 1000000000000 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j hj ↦ ?_; have hj_lt : j < d := Finset.mem_range.mp hj
          have hc : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
          rw [ite_eq_left hc]; simp
        rw [hcongr]
        positivity
    tauSum := fun r ↦ (tauAll.getD (r - 2) 0 : ℝ) / 1000000000
    C_step := 0
    hstages_len := fun n r hn0 _ _ _ ↦ by
      obtain ⟨_, hm_hi, _, _, _, _, _⟩ := highd_checkAltDirectTable12_header hpref
      have hn80 : 80000 ≤ n := hn0
      have hpow15 : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2mN : 2 * m < 2 ^ n :=
        lt_of_le_of_lt (by omega : 2 * m ≤ 16384)
          (lt_of_lt_of_le (by norm_num : 16384 < 2 ^ 15) hpow15)
      rw [stagesQueryCount_altStages (by omega) h2mN, add_zero]
      simpa [Nat.cast_pow, Nat.cast_ofNat] using altStepCount_le_tau_sqrt _ _ (2 ^ n)
    hpLo_le := fun n r hn0 hr2_r hrk huse R hR w hw ↦ by
      simp only [decide_eq_true_eq] at huse
      obtain ⟨_, _, hr2, _, _, htP, hnP⟩ := highd_checkAltDirectTable12_header hpref
      let SP := altWalkSpecOf m rSplit rSplit vPref tauPref nsubPref hr2 le_rfl hpref
      by_cases hrs : r ≤ rSplit
      · have ht_eq : tauAll.getD (r - 2) 0 = tauPref.getD (r - 2) 0 :=
          highd_append_getD_left tauPref tauExt (r - 2) (by omega)
        have hn_eq : nsubAll.getD (r - 2) 0 = nsubPref.getD (r - 2) 0 :=
          highd_append_getD_left nsubPref nsubExt (r - 2) (by omega)
        have huseP : SP.useWalk r = true := by
          dsimp only [SP, altWalkSpecOf]; rw [decide_eq_true_eq]; exact ⟨hr2_r, ht_eq ▸ huse.2⟩
        have hleP := SP.hpLo_le n r hn0 hr2_r hrs huseP R hR w hw
        dsimp only [SP, altWalkSpecOf] at hleP; dsimp only [rowAt]
        rw [ite_eq_left hrs, ht_eq, hn_eq]; exact hleP
      · rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩; have hc : 1 ≤ w ∧ w ≤ min m r := ⟨hw1, hwd⟩
        dsimp only [rowAt]; rw [ite_eq_left hc, ite_eq_right hrs]
        set row := altEvalRowHighDLo12 m r (tauAll.getD (r - 2) 0)
          (nsubAll.getD (r - 2) 0) (dcapExt.getD (r - (rSplit + 1)) 0)
        by_cases hw_lt : w - 1 < row.length
        · exact altEvalRowHighDLo12_sound hn0 hR hw1 hw_lt
        · have hge : row.length ≤ w - 1 := by omega
          rw [highd_getD_nat_zero_of_le row (w - 1) hge, Nat.cast_zero, zero_div]
          exact symHitProb_nonneg R _ w
    hdrift_lt := fun r hr2_r hrk huse ↦ by
      simp only [decide_eq_true_eq] at huse
      obtain ⟨_, _, hr2, _, hvP, htP, hnP⟩ := highd_checkAltDirectTable12_header hpref
      let SP := altWalkSpecOf m rSplit rSplit vPref tauPref nsubPref hr2 le_rfl hpref
      by_cases hrs : r ≤ rSplit
      · have ht_eq : tauAll.getD (r - 2) 0 = tauPref.getD (r - 2) 0 :=
          highd_append_getD_left tauPref tauExt (r - 2) (by omega)
        have hn_eq : nsubAll.getD (r - 2) 0 = nsubPref.getD (r - 2) 0 :=
          highd_append_getD_left nsubPref nsubExt (r - 2) (by omega)
        have huseP : SP.useWalk r = true := by
          dsimp only [SP, altWalkSpecOf]; rw [decide_eq_true_eq]; exact ⟨hr2_r, ht_eq ▸ huse.2⟩
        have hdrP := SP.hdrift_lt r hr2_r hrs huseP; dsimp only [SP, altWalkSpecOf] at hdrP
        have hvR : vAll.getD r 0 = vPref.getD r 0 :=
          highd_append_getD_left vPref vExt r (by omega)
        dsimp only [rowAt]; rw [ite_eq_left hrs, ht_eq, hn_eq]
        refine hdrP.trans_eq (Finset.sum_congr rfl fun w hw ↦ ?_)
        have hvW : vAll.getD (r - w) 0 = vPref.getD (r - w) 0 :=
          highd_append_getD_left vPref vExt (r - w) (by omega)
        dsimp only [vAll] at hvR hvW ⊢; rw [hvR, hvW]
      · have hgt : rSplit + 1 ≤ r := by omega
        have hcomb := highd_combined_props hrSplit_le hpref hext hlen_ext
        obtain ⟨_, _, _, hmonoR, hrows⟩ := hcomb
        obtain ⟨_, _, _, hdrift_nat⟩ := (hrows r hgt (hrk.trans hk_le)).2 huse.2
        set d := min m r
        dsimp only [rowAt]; rw [ite_eq_right hrs]
        set row := altEvalRowHighDLo12 m r (tauAll.getD (r - 2) 0)
          (nsubAll.getD (r - 2) 0) (dcapExt.getD (r - (rSplit + 1)) 0)
        clear_value row
        have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
        have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
        rw [highd_sum_Icc_one_eq_range]
        have hcongr : (∑ j ∈ Finset.range d, (if 1 ≤ j + 1 ∧ j + 1 ≤ d then
                (row.getD ((j + 1) - 1) 0 : ℝ) / 1000000000000 else 0) *
              ((vAll.getD r 0 : ℝ) / wdScaleR - (vAll.getD (r - (j + 1)) 0 : ℝ) / wdScaleR)) =
            (∑ j ∈ Finset.range d, (row.getD j 0 : ℝ) *
                ((vAll.getD r 0 - vAll.getD (r - 1 - j) 0 : ℕ) : ℝ)) /
              (1000000000000 * wdScaleR) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j hj ↦ ?_; have hj_lt : j < d := Finset.mem_range.mp hj
          have hc : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
          rw [ite_eq_left hc]
          have hsub_idx : r - (j + 1) = r - 1 - j := by omega
          have hv_le_R : (vAll.getD (r - 1 - j) 0 : ℝ) / wdScaleR ≤
              (vAll.getD r 0 : ℝ) / wdScaleR :=
            hmonoR (by omega) (hrk.trans hk_le)
          have hv_le : vAll.getD (r - 1 - j) 0 ≤ vAll.getD r 0 := by
            have hmul := (div_le_div_iff_of_pos_right hB_pos).mp hv_le_R
            exact_mod_cast hmul
          rw [hsub_idx, Nat.cast_sub hv_le]; simp only [Nat.add_sub_cancel]; ring
        rw [hcongr, hB_eq]
        have hdriftR : (tauAll.getD (r - 2) 0 : ℝ) * 1000000000000000000 < ∑ j ∈ Finset.range d,
              (row.getD j 0 : ℝ) * ((vAll.getD r 0 - vAll.getD (r - 1 - j) 0 : ℕ) : ℝ) := by
          exact_mod_cast hdrift_nat
        linarith }
/-- Definitional potential projection for `altHighDWalkSpecOf`. -/
theorem altHighDWalkSpecOf_V (m k rSplit kMax : ℕ)
    (vPref tauPref nsubPref vExt tauExt nsubExt dcapExt : List ℕ)
    (hk2 : 2 ≤ k) (hk_le : k ≤ kMax) (hrSplit_le : rSplit ≤ kMax)
    (hpref : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true)
    (hext : checkAltHighDBandLoop m (rSplit + 1) vPref.reverse vExt tauExt nsubExt dcapExt = true)
    (hlen_ext : vExt.length = kMax - rSplit) (r : ℕ) :
    (altHighDWalkSpecOf m k rSplit kMax vPref tauPref nsubPref
      vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext).V r =
      ((vPref ++ vExt).getD r 0 : ℝ) / wdScaleR := by rfl
/-- Definitional threshold projection for `altHighDWalkSpecOf`. -/
theorem altHighDWalkSpecOf_n0 (m k rSplit kMax : ℕ)
    (vPref tauPref nsubPref vExt tauExt nsubExt dcapExt : List ℕ)
    (hk2 : 2 ≤ k) (hk_le : k ≤ kMax) (hrSplit_le : rSplit ≤ kMax)
    (hpref : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true)
    (hext : checkAltHighDBandLoop m (rSplit + 1) vPref.reverse vExt tauExt nsubExt dcapExt = true)
    (hlen_ext : vExt.length = kMax - rSplit) :
    (altHighDWalkSpecOf m k rSplit kMax vPref tauPref nsubPref
      vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext).n0 = altN0 := by rfl
end
public section
open Operator ResourceCounting Real QProg.Notation
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal
/-- Turnkey parallel query-model circuit for a certified high-`d` `D_{\text{alt}}` cell. -/
noncomputable def altHighDCellCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k rSplit kMax : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPref tauPref nsubPref vExt tauExt nsubExt dcapExt : List ℕ)
    (hk2 : 2 ≤ k) (hk_le : k ≤ kMax) (hrSplit_le : rSplit ≤ kMax)
    (hpref : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true)
    (hext : checkAltHighDBandLoop m (rSplit + 1) vPref.reverse vExt tauExt nsubExt dcapExt = true)
    (hlen_ext : vExt.length = kMax - rSplit) (n : ℕ) :
    OracleCirc Var (Stage1.qubits n m k) ((n + 1) * m) :=
  johnsonCircuit res hm_grid hk_grid (altHighDWalkSpecOf m k rSplit kMax vPref tauPref nsubPref
      vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext) n
/-- Exact probability-`1` correctness of `altHighDCellCircuit` on `groverTargetSets n k`. -/
theorem altHighDCell_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k rSplit kMax : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPref tauPref nsubPref vExt tauExt nsubExt dcapExt : List ℕ)
    (hk2 : 2 ≤ k) (hk_le : k ≤ kMax) (hrSplit_le : rSplit ≤ kMax)
    (hpref : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true)
    (hext : checkAltHighDBandLoop m (rSplit + 1) vPref.reverse vExt tauExt nsubExt dcapExt = true)
    (hlen_ext : vExt.length = kMax - rSplit)
    (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))}
    (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;;
      (altHighDCellCircuit res hm_grid hk_grid vPref tauPref nsubPref
        vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext n).compile
        qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ :=
  johnsonCircuit_correctness res hm_grid hk_grid
    (altHighDWalkSpecOf m k rSplit kMax vPref tauPref nsubPref
      vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext) hn hkN hS
/-- Asymptotic relative-cost bound of `altHighDCellCircuit` from `checkAltBound12`. -/
theorem altHighDCell_rel_cost {Var : Type} [DecidableEq Var] (res : Var)
    {m k rSplit kMax num den : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPref tauPref nsubPref vExt tauExt nsubExt dcapExt : List ℕ)
    (hk2 : 2 ≤ k) (hk_le : k ≤ kMax) (hrSplit_le : rSplit ≤ kMax)
    (hpref : checkAltDirectTable12 m rSplit vPref tauPref nsubPref = true)
    (hext : checkAltHighDBandLoop m (rSplit + 1) vPref.reverse vExt tauExt nsubExt dcapExt = true)
    (hlen_ext : vExt.length = kMax - rSplit)
    (hbnd : checkAltBound12 m k ((vPref ++ vExt).getD k 0) num den = true) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ qset ;;
          (altHighDCellCircuit res hm_grid hk_grid vPref tauPref nsubPref
            vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext n).compile
            qAssign (groverParallelMarkingOracle m S))
        ((NNRat.divNat num den : ℝ) * vanillaFindAllCost n m k) := by
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have htop : (altHighDWalkSpecOf m k rSplit kMax vPref tauPref nsubPref
      vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext).V k ≤
      (NNRat.divNat num den : ℝ) * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ) :=
    checkAltBound12_sound hm1 hbnd
  exact johnsonCircuit_rel_cost res hm_grid hk_grid
    (altHighDWalkSpecOf m k rSplit kMax vPref tauPref nsubPref
      vExt tauExt nsubExt dcapExt hk2 hk_le hrSplit_le hpref hext hlen_ext) htop
end

@[expose] public section

open Real
open scoped Matrix NNRat NNReal ENNReal

/- ## Section 1: Primitive Equality & Fast 1-Force-Per-Coordinate `T_16` Evaluator -/

/-- Primitive `ℤ` equality avoiding typeclass synthesis inside `decide +kernel`. -/
def muxIntEq : ℤ → ℤ → Bool
  | Int.ofNat a, Int.ofNat b => Nat.beq a b
  | Int.negSucc a, Int.negSucc b => Nat.beq a b
  | _, _ => false

/-- Primitive `List ℤ` equality avoiding typeclass synthesis inside `decide +kernel`. -/
def muxIntListEq : List ℤ → List ℤ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (muxIntEq x y) (muxIntListEq xs ys) false
  | _, _ => false

/-- Primitive `List ℕ` equality avoiding typeclass synthesis inside `decide +kernel`. -/
def muxNatListEq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (Nat.beq x y) (muxNatListEq xs ys) false
  | _, _ => false










/-- Fast unrolled `16`-stage Horner step equivalent to `hornerT16SlideStep`. -/
def muxFastHornerT16Step (maxLen : ℕ) (hb vec : List ℤ) : List ℤ :=
  let s15 := muxFastHornerStage 16 maxLen hb vec vec
  HighDForce.withForcedList s15 fun c15 =>
  let s14 := muxFastHornerStage 15 maxLen hb vec c15
  HighDForce.withForcedList s14 fun c14 =>
  let s13 := muxFastHornerStage 14 maxLen hb vec c14
  HighDForce.withForcedList s13 fun c13 =>
  let s12 := muxFastHornerStage 13 maxLen hb vec c13
  HighDForce.withForcedList s12 fun c12 =>
  let s11 := muxFastHornerStage 12 maxLen hb vec c12
  HighDForce.withForcedList s11 fun c11 =>
  let s10 := muxFastHornerStage 11 maxLen hb vec c11
  HighDForce.withForcedList s10 fun c10 =>
  let s9 := muxFastHornerStage 10 maxLen hb vec c10
  HighDForce.withForcedList s9 fun c9 =>
  let s8 := muxFastHornerStage 9 maxLen hb vec c9
  HighDForce.withForcedList s8 fun c8 =>
  let s7 := muxFastHornerStage 8 maxLen hb vec c8
  HighDForce.withForcedList s7 fun c7 =>
  let s6 := muxFastHornerStage 7 maxLen hb vec c7
  HighDForce.withForcedList s6 fun c6 =>
  let s5 := muxFastHornerStage 6 maxLen hb vec c6
  HighDForce.withForcedList s5 fun c5 =>
  let s4 := muxFastHornerStage 5 maxLen hb vec c5
  HighDForce.withForcedList s4 fun c4 =>
  let s3 := muxFastHornerStage 4 maxLen hb vec c4
  HighDForce.withForcedList s3 fun c3 =>
  let s2 := muxFastHornerStage 3 maxLen hb vec c3
  HighDForce.withForcedList s2 fun c2 =>
  let s1 := muxFastHornerStage 2 maxLen hb vec c2
  HighDForce.withForcedList s1 fun c1 =>
  muxFastHornerStage 1 maxLen hb vec c1

/-- Fast `nSub`-step full-band `T_16` iterator equivalent to `altIterFullT16`. -/
def muxFastIterFullT16 : ℕ → ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, _, vec => vec
  | k + 1, maxLen, hb, vec =>
    let stepVec := muxFastHornerT16Step maxLen hb vec
    HighDForce.withForcedList stepVec fun vecNext =>
      muxFastIterFullT16 k maxLen hb vecNext

/-- Verifies one bounded `steps`-substep chunk of a full-band `T_16` trajectory. -/
def muxCheckT16Chunk (maxLen steps : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  muxIntListEq (muxFastIterFullT16 steps maxLen hb vecIn) vecOut

/-- Evaluates the post-walk `10 ^ 12`-scaled hit-probability row from a pre-iterated
  `vecFinal`
  after checking `altEvalRowHighDLo12` preamble guards (`dCap = r ≤ mEff`) and `hbPt =
  hbExpect`. -/
def muxEvalT16FromVec (mEff r tau9 nSub : ℕ) (hbExpect vecFinal : List ℤ) : List ℕ :=
  cond (primNatBlt mEff r) []
    (cond
      (Bool.or (primNatBlt r 1)
        (Bool.or (primNatBlt r 2)
        (Bool.or (primNatBlt 8192 mEff)
        (Bool.or (primNatBlt 1024 r)
        (Bool.or (Nat.beq tau9 0)
        (Bool.or (primNatBlt 4000000000 tau9)
        (Bool.or (Nat.beq nSub 0) (primNatBlt 16384 nSub))))))))
      []
      (let hPtRaw := Nat.div (Nat.mul tau9 1000000) nSub
      HighDForce.withForcedNat hPtRaw fun hPt =>
        cond (primNatBlt hPt 1) []
          (let maxBRaw := altMaxBHiFrom mEff r 0 r
          HighDForce.withForcedNat maxBRaw fun maxBHi15 =>
            let bCapHi15 := Nat.mul 2 maxBHi15
            let hgRaw := highdMulCeil15 (Nat.add 2 hPt) bCapHi15
            HighDForce.withForcedNat hgRaw fun hgHi15 =>
              cond
                (Bool.or (primNatBlt 1500000000000000 hgHi15)
                  (Bool.not (altCheckHbTight mEff r 0 r)))
                []
                (let hgPow := altPow17Ceil15 hgHi15
                let truncPad15 :=
                  Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000
                let bCapCeil := Nat.div (Nat.add 999999999999999 bCapHi15) wdScale
                let roundPad15 :=
                  Nat.add 256 (Nat.mul nSub (Nat.add 256 (Nat.mul 10 bCapCeil)))
                let padRaw := Nat.add truncPad15 roundPad15
                HighDForce.withForcedNat padRaw fun totalPad15 =>
                  cond
                    (Bool.or (primNatBlt 100000000000000 totalPad15)
                      (Nat.beq totalPad15 0))
                    []
                    (let hbRaw := altBuildHbFrom mEff r hPt 0 r
                    HighDForce.withForcedList hbRaw fun hbPt =>
                      cond (muxIntListEq hbPt hbExpect)
                        (let padded := altPadRightInts (Nat.add r 1) vecFinal
                        match padded with
                        | [] => []
                        | _ :: tail => altVecTailToLo12 totalPad15 tail)
                        [])))))

/-- Final row checker certifying `hbExpect`, preamble guards, and `rowOut` for a `T_16`
  trajectory. -/
def muxCheckT16FinalRow (mEff r tau9 nSub : ℕ) (hbExpect vecFinal : List ℤ)
    (rowOut : List ℕ) : Bool :=
  cond (Nat.beq (altListLen rowOut) 0) false
    (muxNatListEq (muxEvalT16FromVec mEff r tau9 nSub hbExpect vecFinal) rowOut)

end

public section

open Real
open scoped Matrix NNRat NNReal ENNReal

/- ## Section 2: Equivalence & Trajectory Checkpoint Soundness -/

private theorem mft_cond_true {α : Type} (a b : α) : cond true a b = a := rfl
private theorem mft_cond_false {α : Type} (a b : α) : cond false a b = b := rfl

private theorem mft_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, mft_nat_ble_eq_true]

private theorem mft_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, mft_nat_ble_eq_true]; omega

private theorem mft_primNatBlt_eq_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  unfold primNatBlt
  rw [mft_nat_ble_eq_true]
  change a + 1 ≤ b ↔ a < b
  omega

private theorem mft_primNatBlt_eq_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, mft_primNatBlt_eq_true]; omega

private theorem mft_bool_eq {u v : Bool} (h : (u = true) = (v = true)) : u = v := by
  cases u <;> cases v <;> simp at h ⊢

private theorem mft_to_beq (a b : ℕ) {u : Bool} (h : (u = true) = (a = b)) :
    u = (a == b) :=
  mft_bool_eq (h.trans (Nat.beq_eq_true_eq a b).symm)

private theorem mft_natMin_eq (a b : ℕ) : highdNatMin a b = min a b := by
  unfold highdNatMin
  cases h : Nat.ble a b
  · simp [cond, Nat.min_eq_right (Nat.le_of_lt (mft_nat_ble_eq_false.mp h))]
  · simp [cond, Nat.min_eq_left (mft_nat_ble_eq_true.mp h)]

private theorem mft_forceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat
  rw [show Nat.add 1 x = x + 1 from Nat.one_add x]

private theorem mft_forceList_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by
  cases xs <;> rfl

private theorem mft_strictConsInt_eq (x : ℤ) (xs : List ℤ) :
    highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.ofNat 0] | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t) =
      Int.ofNat n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.negSucc 0] | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t) =
      Int.negSucc n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl

private theorem muxIntEq_eq_true {x y : ℤ} : muxIntEq x y = true ↔ x = y := by
  cases x <;> cases y <;> simp [muxIntEq]

theorem muxIntListEq_eq_true : ∀ {xs ys : List ℤ}, muxIntListEq xs ys = true ↔ xs = ys
  | [], [] => by simp [muxIntListEq]
  | [], _ :: _ => by simp [muxIntListEq]
  | _ :: _, [] => by simp [muxIntListEq]
  | x :: xs, y :: ys => by
    unfold muxIntListEq
    cases hxy : muxIntEq x y
    · have hne : x ≠ y := mt muxIntEq_eq_true.mpr (Bool.eq_false_iff.mp hxy)
      simp [hne]
    · rw [mft_cond_true, muxIntListEq_eq_true]
      simp [muxIntEq_eq_true.mp hxy]

theorem muxNatListEq_eq_true : ∀ {xs ys : List ℕ}, muxNatListEq xs ys = true ↔ xs = ys
  | [], [] => by simp [muxNatListEq]
  | [], _ :: _ => by simp [muxNatListEq]
  | _ :: _, [] => by simp [muxNatListEq]
  | x :: xs, y :: ys => by
    unfold muxNatListEq
    rw [mft_to_beq x y Nat.beq_eq]
    cases hxy : (x == y)
    · simp [beq_eq_false_iff_ne.mp hxy]
    · rw [mft_cond_true, muxNatListEq_eq_true]
      simp [beq_iff_eq.mp hxy]

private theorem muxRawNegOfNat_eq (x : ℕ) : muxRawNegOfNat x = primNegOfNat x := by
  cases x with
  | zero => rfl
  | succ k => simp [muxRawNegOfNat, primNegOfNat, primNegSuccForced, Nat.one_add]

private theorem muxRawSubNatNat_eq (m n : ℕ) : muxRawSubNatNat m n = primSubNatNat m n := by
  unfold muxRawSubNatNat primSubNatNat
  cases Nat.sub n m <;> simp [primOfNatForced, primNegSuccForced, Nat.one_add]

private theorem muxRawIntAdd_eq (a b : ℤ) : muxRawIntAdd a b = primIntAdd a b := by
  cases a <;> cases b <;>
    simp [muxRawIntAdd, primIntAdd, primOfNatForced, primNegSuccForced,
      muxRawSubNatNat_eq, Nat.one_add]

private theorem muxRawIntNeg_eq (a : ℤ) : muxRawIntNeg a = primIntNeg a := by
  cases a <;> simp [muxRawIntNeg, primIntNeg, primOfNatForced, muxRawNegOfNat_eq, Nat.one_add]

private theorem muxRawIntSub_eq (a b : ℤ) : muxRawIntSub a b = primIntSub a b := by
  unfold muxRawIntSub primIntSub
  rw [muxRawIntNeg_eq, muxRawIntAdd_eq]

private theorem muxRawIntMul_eq (a b : ℤ) : muxRawIntMul a b = primIntMul a b := by
  cases a <;> cases b <;>
    simp [muxRawIntMul, primIntMul, primOfNatForced, muxRawNegOfNat_eq, Nat.one_add]

private theorem muxRawIntTdivNat_eq (x : ℤ) (dNat : ℕ) :
    muxRawIntTdivNat x dNat = highdIntTdivNat x dNat := by
  cases x <;>
    simp [muxRawIntTdivNat, highdIntTdivNat, primOfNatForced, muxRawNegOfNat_eq, Nat.one_add]

theorem muxFastSlideLoopAux_eq (dNat : ℕ) :
    ∀ (rem : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      muxFastSlideLoopAux dNat rem prev hb vec cur = hornerSlideLoopAux dNat rem prev hb vec cur
  | 0, _, _, _, _ => rfl
  | rem + 1, prev, hb, vec, cur => by
    cases hb with
    | nil =>
      cases vec <;> cases cur <;>
        simp only [muxFastSlideLoopAux, hornerSlideLoopAux, muxRawIntAdd_eq, muxRawIntTdivNat_eq,
          muxFastSlideLoopAux_eq dNat rem]
    | cons b hbRest =>
      cases vec with
      | nil =>
        cases cur with
        | nil =>
          simp only [muxFastSlideLoopAux, hornerSlideLoopAux, muxRawIntAdd_eq, muxRawIntSub_eq,
            muxRawIntMul_eq, muxRawIntTdivNat_eq, muxFastSlideLoopAux_eq dNat rem]
        | cons c0 cTail =>
          cases cTail <;>
            simp only [muxFastSlideLoopAux, hornerSlideLoopAux, muxRawIntAdd_eq, muxRawIntSub_eq,
              muxRawIntMul_eq, muxRawIntTdivNat_eq, muxFastSlideLoopAux_eq dNat rem]
      | cons v vTail =>
        cases cur with
        | nil =>
          simp only [muxFastSlideLoopAux, hornerSlideLoopAux, muxRawIntAdd_eq, muxRawIntSub_eq,
            muxRawIntMul_eq, muxRawIntTdivNat_eq, muxFastSlideLoopAux_eq dNat rem]
        | cons c0 cTail =>
          cases cTail <;>
            simp only [muxFastSlideLoopAux, hornerSlideLoopAux, muxRawIntAdd_eq, muxRawIntSub_eq,
              muxRawIntMul_eq, muxRawIntTdivNat_eq, muxFastSlideLoopAux_eq dNat rem]

theorem muxFastHornerStage_eq (deg maxLen : ℕ) (hb vec cur : List ℤ) :
    muxFastHornerStage deg maxLen hb vec cur = hornerStageSlide deg maxLen hb vec cur := by
  unfold muxFastHornerStage hornerStageSlide applyHgTdivSlide hornerSlideLoop
  simp only [mft_forceNat_eq, muxFastSlideLoopAux_eq]

theorem muxFastHornerT16Step_eq (maxLen : ℕ) (hb vec : List ℤ) :
    muxFastHornerT16Step maxLen hb vec = hornerT16SlideStep maxLen hb vec := by
  unfold muxFastHornerT16Step hornerT16SlideStep
  simp only [mft_forceList_eq, muxFastHornerStage_eq]

/-- Exact equivalence between the fast 1-force-per-coordinate iterator and `altIterFullT16`. -/
theorem muxFastIterFullT16_eq :
    ∀ (k maxLen : ℕ) (hb vec : List ℤ),
      muxFastIterFullT16 k maxLen hb vec = altIterFullT16 k maxLen hb vec
  | 0, _, _, _ => rfl
  | k + 1, maxLen, hb, vec => by
    unfold muxFastIterFullT16 altIterFullT16
    simp only [mft_forceList_eq, muxFastHornerT16Step_eq, muxFastIterFullT16_eq k]

/-- Additive step composition for `altIterFullT16` across trajectory checkpoints. -/
theorem altIterFullT16_add (k₁ k₂ maxLen : ℕ) (hb vec : List ℤ) :
    altIterFullT16 (k₁ + k₂) maxLen hb vec =
      altIterFullT16 k₂ maxLen hb (altIterFullT16 k₁ maxLen hb vec) := by
  have hstep (k : ℕ) (w : List ℤ) :
      altIterFullT16 (k + 1) maxLen hb w =
        altIterFullT16 k maxLen hb (hornerT16SlideStep maxLen hb w) := by
    conv_lhs => unfold altIterFullT16
    rw [mft_forceList_eq]
  induction k₁ generalizing vec with
  | zero => simp [altIterFullT16]
  | succ k₁ ih =>
    rw [Nat.succ_add, hstep, hstep]
    exact ih _

/-- Soundness of one `muxCheckT16Chunk` `decide +kernel` step. -/
theorem muxCheckT16Chunk_sound {maxLen steps : ℕ} {hb vecIn vecOut : List ℤ}
    (h : muxCheckT16Chunk maxLen steps hb vecIn vecOut = true) :
    altIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold muxCheckT16Chunk at h
  rw [← muxFastIterFullT16_eq]
  exact muxIntListEq_eq_true.mp h

/-- Transitive checkpoint chaining lemma for `altIterFullT16`. -/
theorem muxIterFullT16_chain {k₁ k₂ kTot maxLen : ℕ} {hb v₀ v₁ v₂ : List ℤ}
    (hk : k₁ + k₂ = kTot)
    (h1 : altIterFullT16 k₁ maxLen hb v₀ = v₁)
    (h2 : altIterFullT16 k₂ maxLen hb v₁ = v₂) :
    altIterFullT16 kTot maxLen hb v₀ = v₂ := by
  subst hk
  rw [altIterFullT16_add, h1, h2]

private theorem mft_bif_nil_ne {α : Type} {b : Bool} {xs : List α}
    (h : cond b [] xs ≠ []) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (h rfl)

/-- Certifies `altEvalRowHighDLo12 mEff r tau9 nSub r = rowOut` from a chained
  `altIterFullT16`
  trajectory equality and `muxCheckT16FinalRow`. -/
theorem muxCertT16Row_of_iter {mEff r tau9 nSub : ℕ} {hbExpect vecFinal : List ℤ}
    {rowOut : List ℕ}
    (hiter : altIterFullT16 nSub (Nat.add r 1) hbExpect [Int.ofNat wdScale] = vecFinal)
    (hfin : muxCheckT16FinalRow mEff r tau9 nSub hbExpect vecFinal rowOut = true) :
    altEvalRowHighDLo12 mEff r tau9 nSub r = rowOut ∧ r = min mEff r := by
  unfold muxCheckT16FinalRow at hfin
  rw [mft_to_beq (altListLen rowOut) 0 Nat.beq_eq] at hfin
  cases hlen0 : (altListLen rowOut == 0) with
  | true => rw [hlen0, mft_cond_true] at hfin; exact Bool.noConfusion hfin
  | false =>
    rw [hlen0, mft_cond_false] at hfin
    have hrow_ne : rowOut ≠ [] := by
      intro hnil; subst hnil; simp [altListLen] at hlen0
    have heval_eq : muxEvalT16FromVec mEff r tau9 nSub hbExpect vecFinal = rowOut :=
      muxNatListEq_eq_true.mp hfin
    have hne : muxEvalT16FromVec mEff r tau9 nSub hbExpect vecFinal ≠ [] := by
      rw [heval_eq]; exact hrow_ne
    unfold muxEvalT16FromVec at heval_eq hne
    simp only [mft_forceNat_eq, mft_forceList_eq] at heval_eq hne
    have hrm_f : primNatBlt mEff r = false := mft_bif_nil_ne hne
    have hr_le_m : r ≤ mEff := mft_primNatBlt_eq_false.mp hrm_f
    have hd_min : min mEff r = r := Nat.min_eq_right hr_le_m
    have hdRaw_eq : highdNatMin mEff r = r := (mft_natMin_eq mEff r).trans hd_min
    rw [hrm_f, mft_cond_false] at heval_eq hne
    have hg1_f := mft_bif_nil_ne hne
    rw [hg1_f, mft_cond_false] at heval_eq hne
    set hPt := Nat.div (Nat.mul tau9 1000000) nSub
    have hhPt_f := mft_bif_nil_ne hne
    rw [hhPt_f, mft_cond_false] at heval_eq hne
    set maxBHi15 := altMaxBHiFrom mEff r 0 r
    set bCapHi15 := Nat.mul 2 maxBHi15
    set hgHi15 := highdMulCeil15 (Nat.add 2 hPt) bCapHi15
    have hmid_f := mft_bif_nil_ne hne
    rw [hmid_f, mft_cond_false] at heval_eq hne
    set hgPow := altPow17Ceil15 hgHi15
    set truncPad15 := Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000
    set bCapCeil := Nat.div (Nat.add 999999999999999 bCapHi15) wdScale
    set roundPad15 := Nat.add 256 (Nat.mul nSub (Nat.add 256 (Nat.mul 10 bCapCeil)))
    set totalPad15 := Nat.add truncPad15 roundPad15
    have hpad_f := mft_bif_nil_ne hne
    rw [hpad_f, mft_cond_false] at heval_eq hne
    set hbPt := altBuildHbFrom mEff r hPt 0 r
    cases hhb_b : muxIntListEq hbPt hbExpect with
    | false => rw [hhb_b, mft_cond_false] at hne; exact False.elim (hne rfl)
    | true =>
      rw [hhb_b, mft_cond_true] at heval_eq
      have hhb_eq : hbPt = hbExpect := muxIntListEq_eq_true.mp hhb_b
      refine ⟨?_, hd_min.symm⟩
      unfold altEvalRowHighDLo12
      simp only [mft_forceNat_eq, mft_forceList_eq, mft_strictConsInt_eq]
      rw [hdRaw_eq]
      have hrr_f : primNatBlt r r = false := mft_primNatBlt_eq_false.mpr le_rfl
      have step_f : ∀ {b : Bool} {x y : List ℕ}, b = false → cond b x y = y := by
        rintro _ _ _ rfl; rfl
      have step_t : ∀ {b : Bool} {x y : List ℕ}, b = true → cond b x y = x := by
        rintro _ _ _ rfl; rfl
      have hg_full : ∀ {rest : Bool}, Bool.or (primNatBlt r 1) rest = false →
          Bool.or (primNatBlt r 1) (Bool.or (primNatBlt r 1) (Bool.or (primNatBlt r r)
          (Bool.or (Bool.and (primNatBlt r r) (primNatBlt r 48)) rest))) = false := by
        intro rest hg; rcases Bool.or_eq_false_iff.mp hg with ⟨hr1, hrst⟩
        simp [hr1, hrr_f, hrst]
      refine (step_f (hg_full hg1_f)).trans ?_
      refine (step_f hhPt_f).trans ?_
      refine (step_f hmid_f).trans ?_
      refine (step_f hpad_f).trans ?_
      refine (step_t (Nat.beq_refl r)).trans ?_
      dsimp only [hbPt, hPt] at hhb_eq
      rw [hhb_eq, hiter]
      exact heval_eq

end
end QuantumComputation.Specs.DickeSol
