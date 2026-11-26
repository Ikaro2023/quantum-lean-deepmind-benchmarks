import Track2Grover.CoupledHistory
import Track2Grover.StopMass
import QuantumComputation.Registers.Measurement
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Uniform hidden-label subspace and the actual frozen register-measurement
instrument, retaining arbitrary complex workspace amplitudes at every label. -/
namespace Track2Grover.CoupledLabels
open Finset Operator
open scoped BigOperators RealInnerProductSpace Matrix

variable (L : Type*) [Fintype L] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev Family := PiLp 2 (fun _ : L ↦ E)

def uniform : Submodule ℝ (Family L E) where
  carrier := {u | ∀ i j : L, u i = u j}
  zero_mem' := by intro i j; rfl
  add_mem' := by intro a b ha hb i j; change a i+b i=a j+b j; rw [ha i j,hb i j]
  smul_mem' := by intro s a ha i j; change s • a i = s • a j; rw [ha i j]

noncomputable def copy (v : E) : Family L E := WithLp.toLp 2 (fun _ ↦ v)

theorem sum_energy (x : Family L E) : ‖x‖^2 = ∑ i, ‖x i‖^2 :=
  PiLp.norm_sq_eq_of_L2 _ _

variable [Nonempty L] [FiniteDimensional ℝ E]

theorem uniform_projection (x : Family L E) :
    (uniform L E).starProjection x = copy L E ((Fintype.card L:ℝ)⁻¹ • ∑ i, x i) := by
  classical
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · intro i j; rfl
  · intro u hu
    obtain ⟨i₀⟩ := ‹Nonempty L›
    change ∀ i j, u i = u j at hu
    rw [PiLp.inner_apply]
    simp_rw [PiLp.sub_apply, inner_sub_left, Finset.sum_sub_distrib, fun i ↦ hu i i₀]
    change (∑ i : L, ⟪x i, u i₀⟫) - (∑ _ : L, ⟪(Fintype.card L : ℝ)⁻¹ • ∑ i, x i, u i₀⟫) = 0
    rw [real_inner_smul_left, ← sum_inner, sum_const, nsmul_eq_mul, card_univ]
    field_simp; ring

noncomputable def lift (A : E →ₗ[ℝ] E) : Family L E →ₗ[ℝ] Family L E where
  toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ A (x i))
  map_add' x y := by ext i; change A (x i+y i) = A (x i)+A (y i); rw [map_add]
  map_smul' s x := by ext i; change A (s • x i) = s • A (x i); rw [map_smul]

theorem commutes (A : E →ₗ[ℝ] E) (x : Family L E) :
    (uniform L E).starProjection (lift L E A x) = lift L E A ((uniform L E).starProjection x) := by
  rw [uniform_projection,uniform_projection]
  ext i
  change (Fintype.card L:ℝ)⁻¹ • ∑ i, A (x i) = A ((Fintype.card L:ℝ)⁻¹ • ∑ i, x i)
  rw [map_smul,map_sum]

theorem lift_complete {l : ℕ} (M : Fin l → E →ₗ[ℝ] E)
    (complete : ∀ x, ∑ j, ‖M j x‖^2 = ‖x‖^2) (x : Family L E) :
    ∑ j, ‖lift L E (M j) x‖^2 = ‖x‖^2 := by
  simp_rw [sum_energy]
  change (∑ j : Fin l, ∑ i : L, ‖M j (x i)‖^2) = _
  rw [sum_comm]; simp_rw [complete]

abbrev Space (q : ℕ) := EuclideanSpace ℂ (Fin (2^q))

/-- Workspace Kraus map of a frozen register measurement, regarded as real-linear. -/
noncomputable def read {k q : ℕ} (r : QRegister k q) (o : Fin (2^k)) :
    Space q →ₗ[ℝ] Space q where
  toFun x := WithLp.toLp 2 (fun z ↦ if r.extractIndex z = o then x z else 0)
  map_add' x y := by ext z; change (if _ then x z+y z else 0) = _+_; by_cases h : r.extractIndex z=o <;> simp [h]
  map_smul' s x := by ext z; change (if _ then s • x z else 0) = s • _; by_cases h : r.extractIndex z=o <;> simp [h]

theorem read_exact {k q : ℕ} (r : QRegister k q) (o : Fin (2^k)) (x : Space q) (z) :
    read r o x z = (r.basisOutcomeProjector o *ᵥ (fun j ↦ x j)) z := by
  rw [r.basisOutcomeProjector_eq_diagonal,Matrix.mulVec_diagonal]
  change (if r.extractIndex z = o then x z else 0) = _ * _
  by_cases h : r.extractIndex z=o <;> simp [h]

theorem read_complete {k q : ℕ} (r : QRegister k q) (x : Space q) :
    ∑ o, ‖read r o x‖^2 = ‖x‖^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  change ∑ o, ‖if r.extractIndex z=o then x z else 0‖^2 = ‖x z‖^2
  rw [sum_eq_single (r.extractIndex z)]
  · simp
  · intro o _ ho; simp [Ne.symm ho]
  · simp

/-- The actual register measurement can branch into distinct continuations at no
query cost, retaining the two energy sums on the joint hidden-label amplitudes. -/
theorem measure_node {k q : ℕ} (r : QRegister k q) (x : Family L (Space q))
    {p v : ℝ} {t h f : Fin (2^k) → ℝ}
    (branches : ∀ o, CoupledHistory.Run (uniform L (Space q)) p v
      (lift L (Space q) (read r o) x) (t o) (h o) (f o)) :
    CoupledHistory.Run (uniform L (Space q)) p v x (∑ o, t o) (∑ o, h o) (∑ o, f o) :=
  .instrument x _ (lift_complete L _ _ (read_complete r)) (fun o ↦ commutes L _ _) branches

#print axioms uniform_projection
#print axioms commutes
#print axioms read_exact
#print axioms measure_node
end Track2Grover.CoupledLabels
