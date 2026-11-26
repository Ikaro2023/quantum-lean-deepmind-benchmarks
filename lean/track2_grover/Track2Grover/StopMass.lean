module

public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Fintype.Fin

/-! Incidence bounds for the uniform hidden set, including vector-valued output transcripts. -/

@[expose] public section
open Finset
namespace Track2Grover.HiddenSet

def labels (N k : ℕ) := (univ : Finset (Fin N)).powersetCard k

def containing {N : ℕ} (k : ℕ) (x : Fin N) := (labels N k).filter (x ∈ ·)

theorem incidence {N k : ℕ} (x : Fin N) (hk : 0 < k) :
    N * (containing k x).card = (labels N k).card * k := by
  have h := card_filter_powersetCard_subset ({x} : Finset (Fin N)) univ k
    (subset_univ _) (by simp only [card_singleton]; omega)
  have hc : (containing k x).card = (N - 1).choose (k - 1) := by
    simpa [containing, labels] using h
  rw [hc, labels, card_powersetCard, card_univ, Fintype.card_fin]
  have hN := x.isLt
  have he := Nat.add_one_mul_choose_eq (N-1) (k-1)
  rwa [show N - 1 + 1 = N by omega, show k - 1 + 1 = k by omega] at he

/-- Repeated addresses and idle slots cannot increase the number of hit labels. -/
theorem tuple_hit {N k m : ℕ} (hk : 0 < k) (xs : Fin m → Fin N) :
    N * (univ.biUnion (fun j ↦ containing k (xs j))).card ≤ (labels N k).card * (m*k) := by
  calc
    _ ≤ N * ∑ j : Fin m, (containing k (xs j)).card :=
      Nat.mul_le_mul_left _ card_biUnion_le
    _ = ∑ j : Fin m, (labels N k).card * k := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ ↦ incidence (xs j) hk
    _ = _ := by simp [mul_assoc, mul_left_comm, mul_comm]

/-- Square norm of the sum of supported hidden-label amplitudes, in the scaled form
equivalent to projected mass ≤ (k/N) times the transcript's mass. -/
theorem stopped_mass {N k : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (hk : 0 < k) (x : Fin N) (ψ : Finset (Fin N) → E)
    (support : ∀ S ∈ labels N k, x ∉ S → ψ S = 0) :
    (N : ℝ) * ‖∑ S ∈ labels N k, ψ S‖ ^ 2 ≤
    ((labels N k).card : ℝ) * k * (∑ S ∈ labels N k, ‖ψ S‖ ^ 2) := by
  classical
  let A := containing k x
  have hsum : ∑ S ∈ A, ψ S = ∑ S ∈ labels N k, ψ S :=
    sum_subset (filter_subset _ _) (fun S hS hA ↦ support S hS (by
      intro hx
      exact hA (mem_filter.mpr ⟨hS, hx⟩)))
  have hinc : (N : ℝ) * (A.card : ℝ) = ((labels N k).card : ℝ) * k := by
    exact_mod_cast incidence x hk
  have hn := norm_sum_le A ψ
  have h2 : ‖∑ S ∈ A, ψ S‖ ^ 2 ≤ (A.card : ℝ) * ∑ S ∈ A, ‖ψ S‖ ^ 2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
      (sq_sum_le_card_mul_sum_sq (s := A) (f := fun S ↦ ‖ψ S‖))
  rw [← hsum, ← hinc, mul_assoc]
  gcongr
  exact h2.trans <| mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)) (by positivity)

#print axioms incidence
#print axioms tuple_hit
#print axioms stopped_mass
end Track2Grover.HiddenSet
