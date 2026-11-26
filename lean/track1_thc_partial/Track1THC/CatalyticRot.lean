import QuantumComputationSpecs.Primitives.THCFactorization
import Track1THC.CleanOps

/-!
# Exact phase-gradient kickback (Track 1, Round 3)

The algebraic core of the catalytic rotation `RealizesCatalyticSubroutine … (diag e^{2πi k/2^β}) P`:

* `cycShift_phaseGradient`: the cyclic shift by `j` on `Fin (2^b)` has the frozen
  `phaseGradientState b` as an *exact* eigenvector with eigenvalue `exp (2π i j / 2^b)`.
* `controlledAdd_kick`: the controlled adder `|t⟩|c⟩ ↦ |t⟩|c + t⟩` sends `|t⟩ ⊗ φ_b` to
  `exp (2π i t / 2^b) • (|t⟩ ⊗ φ_b)`, so on a catalyst in `φ_b` it implements the rotation
  `diag(exp(2π i t / 2^b))` on the target *exactly* (no approximation) and returns the catalyst intact.
* `catalytic_of_net_action`: bridge to `RealizesCatalyticSubroutine`: a single unitary assignment
  `Wp` is a catalytic realization of `U` as soon as `V⁻¹ · Wp · V` acts as the target-embedded `U` on
  clean inputs.
-/

open QuantumComputation.Specs Complex Matrix

namespace Track1THC.CatalyticRot

/-- Cyclic shift `e_y ↦ e_{y+j}` on `Fin (2^b)`. -/
def cycShift (b : ℕ) (j : Fin (2 ^ b)) : Matrix (Fin (2 ^ b)) (Fin (2 ^ b)) ℂ :=
  Matrix.of fun x y ↦ if x = y + j then 1 else 0

theorem exp_two_pi_sub_mod (N : ℕ) (hN : 0 < N) (a : ℕ) (c : ℕ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (((a + (N - c % N)) % N : ℕ) : ℂ)) / N) =
      Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ)) / N) *
        Complex.exp ((2 * Real.pi * Complex.I * (c : ℂ)) / N) := by
  set s : ℕ := (a + (N - c % N)) % N with hs
  have hcl : c % N < N := Nat.mod_lt _ hN
  have e1 : a + (N - c % N) = N * ((a + (N - c % N)) / N) + s := (Nat.div_add_mod _ _).symm
  have e2 : c = N * (c / N) + c % N := (Nat.div_add_mod _ _).symm
  have hsub : ((N - c % N : ℕ) : ℤ) = (N : ℤ) - ((c % N : ℕ) : ℤ) := by
    rw [Nat.cast_sub hcl.le]
  have e1' : (a : ℤ) + ((N : ℤ) - ((c % N : ℕ) : ℤ)) =
      (N : ℤ) * (((a + (N - c % N)) / N : ℕ) : ℤ) + (s : ℤ) := by
    have := congrArg (fun t : ℕ => (t : ℤ)) e1
    simpa [hsub] using this
  have e2' : (c : ℤ) = (N : ℤ) * ((c / N : ℕ) : ℤ) + ((c % N : ℕ) : ℤ) := by
    have := congrArg (fun t : ℕ => (t : ℤ)) e2
    simpa using this
  set m : ℤ := (((a + (N - c % N)) / N : ℕ) : ℤ) - 1 - ((c / N : ℕ) : ℤ) with hm
  have hmz : (a : ℤ) - c - s = (N : ℤ) * m := by
    rw [hm]; linear_combination e1' - e2'
  have hmc : (a : ℂ) - c - s = (N : ℂ) * m := by exact_mod_cast hmz
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Complex.exp_add]
  have hx : -(2 * Real.pi * Complex.I * (s : ℂ)) / N =
      (-(2 * Real.pi * Complex.I * (a : ℂ)) / N + (2 * Real.pi * Complex.I * (c : ℂ)) / N) +
        (m : ℂ) * (2 * Real.pi * Complex.I) := by
    have hs' : (s : ℂ) = (a : ℂ) - c - N * m := by linear_combination (-1 : ℂ) * hmc
    rw [hs']
    field_simp
    ring
  rw [hx, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]


theorem fin_sub_val (b : ℕ) (x j : Fin (2 ^ b)) :
    (x - j).val = (x.val + (2 ^ b - j.val % 2 ^ b)) % 2 ^ b := by
  rw [Fin.sub_def]
  simp only
  rw [Nat.mod_eq_of_lt j.isLt, Nat.add_comm]

/-- The frozen phase-gradient state is an exact eigenvector of every cyclic shift. -/
theorem cycShift_phaseGradient (b : ℕ) (j : Fin (2 ^ b)) :
    (cycShift b j) *ᵥ (phaseGradientState b) =
      Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / 2 ^ b) • phaseGradientState b := by
  funext x
  have hN : 0 < 2 ^ b := Nat.two_pow_pos b
  have hsum : ((cycShift b j) *ᵥ (phaseGradientState b)) x = phaseGradientState b (x - j) := by
    simp only [Matrix.mulVec, dotProduct, cycShift, Matrix.of_apply]
    have : ∀ y : Fin (2 ^ b), (if x = y + j then (1 : ℂ) else 0) * phaseGradientState b y =
        if y = x - j then phaseGradientState b y else 0 := by
      intro y
      by_cases hy : y = x - j
      · subst hy; simp
      · have : ¬ x = y + j := fun h ↦ hy (by rw [h]; simp)
        simp [hy, this]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum]
  simp only [phaseGradientState, Pi.smul_apply, smul_eq_mul]
  have key := exp_two_pi_sub_mod (2 ^ b) hN x.val j.val
  rw [fin_sub_val]
  push_cast at key ⊢
  rw [key]
  ring


/-- Controlled modular adder `|t⟩|c⟩ ↦ |t⟩|c + t⟩` on (target value, catalyst value). -/
def ctrlAdd (b : ℕ) : Matrix (Fin (2 ^ b) × Fin (2 ^ b)) (Fin (2 ^ b) × Fin (2 ^ b)) ℂ :=
  Matrix.of fun p q ↦ if p.1 = q.1 ∧ p.2 = q.2 + q.1 then 1 else 0

/-- Phase kickback, exact: the controlled adder maps `|t⟩ ⊗ φ_b` to
`exp (2π i t / 2^b) • (|t⟩ ⊗ φ_b)`. -/
theorem controlledAdd_kick (b : ℕ) (t : Fin (2 ^ b)) :
    (ctrlAdd b) *ᵥ (fun p : Fin (2 ^ b) × Fin (2 ^ b) ↦
        if p.1 = t then phaseGradientState b p.2 else 0) =
      Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / 2 ^ b) •
        (fun p : Fin (2 ^ b) × Fin (2 ^ b) ↦
          if p.1 = t then phaseGradientState b p.2 else 0) := by
  funext p
  obtain ⟨x, c⟩ := p
  have hshift := congrFun (cycShift_phaseGradient b t) c
  by_cases hx : x = t
  · subst hx
    simp only [Matrix.mulVec, dotProduct, ctrlAdd, Matrix.of_apply, Fintype.sum_prod_type,
      Pi.smul_apply, smul_eq_mul, if_true]
    have h1 : ∀ (x' c' : Fin (2 ^ b)),
        (if x = x' ∧ c = c' + x' then (1 : ℂ) else 0) * (if x' = x then phaseGradientState b c' else 0) =
        if x' = x then (if c = c' + x then phaseGradientState b c' else 0) else 0 := by
      intro x' c'
      by_cases h : x' = x
      · subst h; simp
      · have : ¬ (x = x' ∧ c = c' + x') := fun hh ↦ h hh.1.symm
        simp [h, this]
    simp only [h1]
    rw [Finset.sum_eq_single x (fun x1 _ hne ↦ by simp [hne])
      (fun h ↦ absurd (Finset.mem_univ x) h)]
    simp only [if_true]
    have h2 := hshift
    simp only [Matrix.mulVec, dotProduct, cycShift, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul] at h2
    have h3 : ∀ c' : Fin (2 ^ b), (if c = c' + x then phaseGradientState b c' else 0) =
        (if c = c' + x then (1 : ℂ) else 0) * phaseGradientState b c' := by
      intro c'; split_ifs <;> simp
    simp only [h3]
    exact h2
  · simp only [Matrix.mulVec, dotProduct, ctrlAdd, Matrix.of_apply, Fintype.sum_prod_type,
      Pi.smul_apply, smul_eq_mul, hx, if_false, mul_zero]
    apply Finset.sum_eq_zero
    intro x' _
    apply Finset.sum_eq_zero
    intro c' _
    by_cases h : x' = t
    · have : ¬ (x = x' ∧ c = c' + x') := fun hh ↦ hx (hh.1.trans h)
      simp [this]
    · simp [h]


section bridge
open Operator QProg Track1THC.CleanOps

variable {Var : Type} [DecidableEq Var] {n k m b : ℕ}
  {rT : QRegister k n} {rS : QRegister m n} {rC : QRegister b n}
  {hsc : rS.DisjointWires rC} {hdisj : rT.DisjointWires (rS.concat rC hsc)}

/-- Bridge to the frozen `RealizesCatalyticSubroutine`: a single unitary assignment `Wp` (e.g. a
controlled phase-gradient adder) is a catalytic realization of `U` on `rT` as soon as, for every
`V` preparing the phase-gradient state, the net unitary `V⁻¹ · Wp · V` (on the catalyst) acts on the
clean-ancilla subspace (scratch and catalyst zero) exactly as the target-embedded `U`. -/
theorem catalytic_of_net_action (U : Unitary (2 ^ k)) (Wp : Unitary (2 ^ n))
    (hnet : ∀ V : Unitary (2 ^ b), (∀ i, V.1 i 0 = phaseGradientState b i) →
      ((rC.embedUnitary V⁻¹) * Wp * (rC.embedUnitary V)).1 *
          (rS.concat rC hsc).basisOutcomeProjector 0 =
        (rT.embedUnitary U).1 * (rS.concat rC hsc).basisOutcomeProjector 0) :
    RealizesCatalyticSubroutine rT rS rC hsc hdisj U (QProg.qAssign Wp : QProg Var (2 ^ n)) := by
  intro V hV
  refine realizesClean_congr
    (P := (QProg.qAssign ((rC.embedUnitary V⁻¹) * Wp * (rC.embedUnitary V)) : QProg Var (2 ^ n)))
    ?_ (realizesClean_of_clean_action U _ (hnet V hV))
  intro Θ
  simp only [wp_qSeq, wp_qAssign, CQAssertion.qAssign_qAssign]

end bridge

end Track1THC.CatalyticRot
