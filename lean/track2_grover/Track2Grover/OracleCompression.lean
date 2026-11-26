import QuantumComputationSpecs.Algorithms.Grover
import Track2Grover.Any.OddParityBridge
import Track2Grover.StopMass

/-! The exact frozen parallel oracle in a fixed flag basis, averaged over hidden labels.
Arbitrary nonnegative weights on basis tuples include marginal weights after tracing out
an entangled workspace. -/
open QuantumComputation.Specs
open scoped BigOperators
namespace Track2Grover.Compression
open GroverSolution (flagConj fullReg slotAddr slotFlag sDiagM)
open HiddenSet
open Finset

noncomputable def conjugated {n : ℕ} (m : ℕ) (S : Finset (Fin (2^n))) :=
  (flagConj n m).1 * ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 *
    (flagConj n m).1

theorem diagonal_form {n m : ℕ} (S : Finset (Fin (2^n))) :
    conjugated m S = sDiagM n m S :=
  GroverSolution.flagConj_mul_embed_mul_flagConj S

private def sign {n m : ℕ} (S : Finset (Fin (2^n))) (z : Fin (2^(m*(n+1)))) : ℤ :=
  ∏ j : Fin m, if slotAddr n m z j ∈ S ∧ slotFlag n m z j = 0 then -1 else 1

private theorem diagonal_sign {n m : ℕ} (S : Finset (Fin (2^n))) (z : Fin (2^(m*(n+1)))) :
    (conjugated m S z z).re = (sign S z : ℝ) := by
  rw [diagonal_form]
  simp only [sDiagM, Matrix.diagonal_apply_eq]
  have he : (∏ j : Fin m, GroverSolution.slotDiag n S ((GroverSolution.slotReg n m j).extractIndex z))
      = (sign S z : ℂ) := by
    unfold sign
    push_cast
    apply prod_congr rfl
    intro j _
    unfold GroverSolution.slotDiag
    split <;> simp_all
  rw [he]
  simp

/-- Scaled lower bound for each entry on the diagonal of the compressed oracle. -/
theorem basis_bound {n m k : ℕ} (hk : 0 < k) (z : Fin (2^(m*(n+1)))) :
    (((2:ℝ)^n - 2*m*k) * (groverTargetSets n k).card) ≤
    (2:ℝ)^n * ∑ S ∈ groverTargetSets n k, (conjugated m S z z).re := by
  classical
  let L := labels (2^n) k
  let B := univ.biUnion fun j : Fin m ↦ containing k (slotAddr n m z j)
  have hBL : B ⊆ L := by
    intro S hS
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hS
    exact (mem_filter.mp hj).1
  have hcount : (2:ℝ)^n * B.card ≤ L.card * ((m:ℝ)*k) := by
    exact_mod_cast tuple_hit hk (slotAddr n m z)
  have hsign (S) (hS : S ∈ L) :
      (1:ℝ) - 2*(if S ∈ B then 1 else 0) ≤ (conjugated m S z z).re := by
    rw [diagonal_sign]
    by_cases hb : S ∈ B
    · rcases GroverSolution.prod_ite_neg_one_or_one univ
        (fun j : Fin m ↦ slotAddr n m z j ∈ S ∧ slotFlag n m z j = 0) with h|h <;>
        norm_num [sign, h, hb]
    · have hn (j : Fin m) : slotAddr n m z j ∉ S := fun ht ↦
        hb (mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨hS, ht⟩⟩)
      simp [sign, hn, hb]
  have hs := sum_le_sum hsign
  have hf : L.filter (· ∈ B) = B := by rw [filter_mem_eq_inter, inter_eq_right.mpr hBL]
  simp only [sum_sub_distrib, ← mul_sum, sum_const, sum_boole, nsmul_eq_mul, mul_one, hf] at hs
  change _ ≤ (2:ℝ)^n * ∑ S ∈ L, _
  change (((2:ℝ)^n - 2*m*k) * L.card) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (2:ℝ)^n)]

theorem weighted_bound {n m k : ℕ} (hk : 0 < k)
    (w : Fin (2^(m*(n+1))) → ℝ) (hw : ∀ z, 0 ≤ w z) :
    (((2:ℝ)^n - 2*m*k) * (groverTargetSets n k).card) * ∑ z, w z ≤
    ∑ z, w z * ((2:ℝ)^n * ∑ S ∈ groverTargetSets n k, (conjugated m S z z).re) := by
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  simpa only [mul_comm (w z)] using mul_le_mul_of_nonneg_right (basis_bound hk z) (hw z)

#print axioms diagonal_form
#print axioms basis_bound
#print axioms weighted_bound

/-- The identical bound on any routed oracle register in an arbitrarily large workspace.
The global basis weights are unrestricted, so need not factor across the slots. -/
theorem embedded_weighted_bound {n m k q : ℕ} (hk : 0 < k)
    (r : QRegister (m*(n+1)) q) (w : Fin (2^q) → ℝ) (hw : ∀ z, 0 ≤ w z) :
    (((2:ℝ)^n - 2*m*k) * (groverTargetSets n k).card) * ∑ z, w z ≤
    ∑ z, w z * ((2:ℝ)^n * ∑ S ∈ groverTargetSets n k,
      (((r.embedUnitary (flagConj n m)).1 *
        ((r.compose (fullReg n m)).embedUnitary (groverParallelMarkingOracle m S)).1 *
        (r.embedUnitary (flagConj n m)).1) z z).re) := by
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  have h (S : Finset (Fin (2^n))) :
      ((r.embedUnitary (flagConj n m)).1 *
          ((r.compose (fullReg n m)).embedUnitary (groverParallelMarkingOracle m S)).1 *
          (r.embedUnitary (flagConj n m)).1) z z =
        conjugated m S (r.extractIndex z) (r.extractIndex z) := by
    rw [QRegister.embedUnitary_compose]
    change (r.embedMatrix _ * r.embedMatrix _ * r.embedMatrix _) z z = _
    rw [← r.embedMatrix_mul, ← r.embedMatrix_mul]
    change (r.embedMatrix (conjugated m S)) z z = _
    rw [diagonal_form, sDiagM, r.embedMatrix_diagonal]
    simp
  simp_rw [h]
  simpa only [mul_comm (w z)] using
    mul_le_mul_of_nonneg_right (basis_bound hk (r.extractIndex z)) (hw z)

#print axioms embedded_weighted_bound
end Track2Grover.Compression
