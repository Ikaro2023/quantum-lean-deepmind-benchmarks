import Track1THC.LCU

/-!
# LCU from an involutive family of unitaries (Track 1, Round 2)

Given unitaries `V x` indexed by `x : Fin (2^m)` together with an involution `π` such that
`V (π x) = (V x)ᴴ`, the "swap-select" `S = ∑ₓ |π x⟩⟨x| ⊗ V x` is a Hermitian involution, and for a
`π`-symmetric probability vector `p`, `W† S W` block-encodes `α ∑ₓ pₓ Vₓ`.  (The swap is what makes
`S` Hermitian even when `V x` is not, e.g. for products `Z_a Z_b` of non-commuting reflections.)
-/

namespace Track1THC.LCU

open QuantumComputation.Specs Operator Matrix
open scoped Matrix

variable {k m : ℕ}

/-- Swap-select matrix `S = ∑ₓ V x ⊗ |π x⟩⟨x|`. -/
noncomputable def swapSelect (V : Fin (2 ^ m) → Operator (2 ^ k)) (π : Fin (2 ^ m) → Fin (2 ^ m)) :
    Operator (2 ^ (k + m)) :=
  Matrix.of fun g h =>
    if ancIdx k m g = π (ancIdx k m h) then V (ancIdx k m h) (sysIdx k m g) (sysIdx k m h) else 0

theorem swapSelect_symm_apply (V : Fin (2 ^ m) → Operator (2 ^ k)) (π : Fin (2 ^ m) → Fin (2 ^ m))
    (i j : Fin (2 ^ k)) (x y : Fin (2 ^ m)) :
    swapSelect V π ((split k m).symm (i, x)) ((split k m).symm (j, y)) =
      if x = π y then V y i j else 0 := by
  simp [swapSelect]

theorem swapSelect_conjTranspose (V : Fin (2 ^ m) → Operator (2 ^ k))
    (π : Fin (2 ^ m) → Fin (2 ^ m)) (hπ : ∀ x, π (π x) = x) (hVπ : ∀ x, V (π x) = (V x)ᴴ) :
    (swapSelect V π)ᴴ = swapSelect V π := by
  ext g h
  simp only [Matrix.conjTranspose_apply, swapSelect, Matrix.of_apply]
  by_cases hc : ancIdx k m h = π (ancIdx k m g)
  · have hc' : ancIdx k m g = π (ancIdx k m h) := by rw [hc, hπ]
    rw [if_pos hc, if_pos hc', hc, hVπ]
    simp [Matrix.conjTranspose_apply]
  · have hc' : ¬ ancIdx k m g = π (ancIdx k m h) := by
      intro h'; apply hc; rw [h', hπ]
    rw [if_neg hc, if_neg hc']
    simp

theorem swapSelect_mul_self (V : Fin (2 ^ m) → Operator (2 ^ k)) (π : Fin (2 ^ m) → Fin (2 ^ m))
    (hπ : ∀ x, π (π x) = x) (hV2 : ∀ x, (V x)ᴴ * V x = 1) (hVπ : ∀ x, V (π x) = (V x)ᴴ) :
    swapSelect V π * swapSelect V π = 1 := by
  ext g h
  obtain ⟨⟨i, x⟩, rfl⟩ := (split k m).symm.surjective g
  obtain ⟨⟨j, y⟩, rfl⟩ := (split k m).symm.surjective h
  rw [Matrix.mul_apply, sum_split k m]
  simp only [swapSelect_symm_apply]
  have hz : ∀ l : Fin (2 ^ k),
      ∑ z : Fin (2 ^ m), (if x = π z then V z i l else 0) * (if z = π y then V y l j else 0) =
        if x = y then V (π y) i l * V y l j else 0 := by
    intro l
    rw [Finset.sum_eq_single (π y)]
    · by_cases hxy : x = y
      · simp [hxy, hπ]
      · have : ¬ x = π (π y) := by rw [hπ]; exact hxy
        simp [this, hxy]
    · intro z _ hz
      simp [hz]
    · simp
  simp only [hz]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte]
    rw [← Matrix.mul_apply, hVπ, hV2]
    simp [Matrix.one_apply]
  · simp [hxy, Matrix.one_apply]

/-- **LCU for an involutive family.**  `W† S W` block-encodes `α ∑ₓ pₓ Vₓ`. -/
theorem lcu_of_involutive_family (V : Fin (2 ^ m) → Operator (2 ^ k))
    (π : Fin (2 ^ m) → Fin (2 ^ m)) (hπ : ∀ x, π (π x) = x)
    (hV2 : ∀ x, (V x)ᴴ * V x = 1) (hVπ : ∀ x, V (π x) = (V x)ᴴ)
    (p : Fin (2 ^ m) → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hpπ : ∀ x, p (π x) = p x)
    (α : ℝ) (hα : 0 < α) (A : Operator (2 ^ k))
    (hA : A = (α : ℂ) • ∑ x, (p x : ℂ) • V x) :
    ∃ U : Unitary (2 ^ (k + m)), IsQubitizedBlockEncodingUnitary α A U := by
  obtain ⟨H, hH, hcol⟩ := exists_unitary_first_col (0 : Fin (2 ^ m)) (fun x => Real.sqrt (p x))
    (by simpa [Real.sq_sqrt (hp0 _)] using hp1)
  refine lcu_blockEncoding (swapSelect V π) (swapSelect_conjTranspose V π hπ hVπ)
    (swapSelect_mul_self V π hπ hV2 hVπ) ⟨H, hH⟩ (fun x => Real.sqrt (p x)) hcol α hα A ?_
  intro i j
  rw [hA]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  simp_rw [swapSelect_symm_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (π y)]
  · simp only [↓reduceIte, hpπ]
    have : ((Real.sqrt (p y) : ℝ) : ℂ) * (Real.sqrt (p y) : ℂ) = (p y : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp0 y)]
    rw [mul_assoc, ← mul_assoc ((Real.sqrt (p y) : ℝ) : ℂ), this]
  · intro x _ hx
    simp [hx]
  · simp

end Track1THC.LCU
