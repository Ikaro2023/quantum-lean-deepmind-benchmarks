import Track2Grover.LowerBorn
import Track2Grover.LowerSeed

/-! Link finite-tree amplitudes to frozen program correctness and cost on one common
normalized CQ input, allowing finite trees to be fed to the angular certificate. -/
namespace Track2Grover.Path
open Operator Matrix ResourceCounting
open scoped ENNReal Matrix
variable {V : Type} [DecidableEq V] {w h : ℕ}

private theorem quad_basis (A : Mat w) (i : Fin (2^w)) :
    quad A (basisState i) = (A i i).re := by
  have hρ : pureStateDensity (basisState i) = Matrix.single i i 1 := by
    ext u v
    by_cases hu : u = i <;> by_cases hv : v = i <;>
      simp [pureStateDensity,basisState,Matrix.vecMulVec,Matrix.single_apply,
        Pi.single_apply,hu,hv,eq_comm] <;> grind
  simp [quad,hρ,Matrix.trace_mul_single]

omit [DecidableEq V] in
private theorem expect_seed_value (σ : Store V) (θ : CQAssertion (Store V) (2^w)) :
    expect (seed w σ) θ = value θ σ (basisState 0) := by rw [expect_seed, value, quad_basis]

private theorem values_seed (σ : Store V) (X : Effects V w) :
    ENNReal.ofReal (values X σ (basisState 0)) = testMass (seed w σ) X := by
  have pos (Y : Effects V w) : 0 ≤ values Y σ (basisState 0) := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨θ, _, rfl⟩ := List.mem_map.mp hx
    rw [← expect_seed_value]
    exact FirstQuery.pos_expect _ _
  induction X with
  | nil => simp [values,testMass]
  | cons θ X ih =>
    change ENNReal.ofReal (value θ σ (basisState 0) + values X σ (basisState 0)) =
      FirstQuery.mass (seed w σ) θ + testMass (seed w σ) X
    rw [← expect_seed_value, ENNReal.ofReal_add (FirstQuery.pos_expect ..) (pos X), ih]
    rfl

theorem score_prob (O : Unitary (2^h)) (C : Finite V w h) (σ : Store V)
    (g : Store V → Prop) [DecidablePred g] :
    ENNReal.ofReal (score O 0 (fun _ => 0) (fun τ ψ => if g τ then energy ψ else 0)
      (build C σ Tree.halt) (basisState 0)) =
      Fuel.obs (compile O C) (seed w σ) (fun τ => ⌜g τ⌝) := by
  let θ : CQAssertion (Store V) (2^w) := fun τ => ⌜g τ⌝
  have he (τ : Store V) (ψ : Vec w) : values [θ] τ ψ = if g τ then energy ψ else 0 := by
    by_cases h : g τ
    · simpa [values, value, θ, h] using value_top τ ψ
    · simp [values, value, θ, h, quad]
  rw [show (fun τ (ψ : Vec w) => if g τ then energy ψ else 0) = values [θ] by
    funext τ ψ; exact (he τ ψ).symm]
  have hb := score_tree false O C [θ] σ (basisState 0)
  change score O 0 _ _ _ _ = _ at hb
  rw [hb, values_seed, tests_sound]
  simp [testMass, Fuel.obs, FirstQuery.mass_wp, θ]

theorem score_calls_le_cost (O : Unitary (2^h)) (C : Finite V w h) (σ : Store V) :
    ENNReal.ofReal (score O 1 (fun _ => 0) (fun _ _ => 0) (build C σ Tree.halt) (basisState 0)) ≤
      expectedCost (CostModel.ofEmbeddedOracle O) (compile O C) (seed w σ) := by
  have hb := score_tree true O C [] σ (basisState 0)
  change score O 1 (fun _ => 0) (fun _ _ => 0) _ _ = _ at hb
  rw [hb, values_seed, tests_sound]
  simpa [testMass] using number_le_expected O C (seed w σ)

#print axioms score_prob
#print axioms score_calls_le_cost
end Track2Grover.Path
