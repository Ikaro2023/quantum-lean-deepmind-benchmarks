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

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.PowerLawCost
public import QuantumComputation.Circuits.DynamicCircuit
public import Mathlib.Data.Finset.Powerset
public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Maths.Trigonometry
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.Primitives.Hadamard
public import QuantumComputation.Primitives.Measure
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.BitVec
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.NumberTheory.Niven

/-!
# Shared Definitions and Cost-Tagging Helpers for Parallel Grover Search

Mirrors the non-hole definitions of `QuantumComputationSpecs.Algorithms.Grover` with identical
bodies (unifying by `rfl` in the solution file), proves shared grid-selector lemmas on
`groverGrid`, and provides global-phase tagging (`phaseTag`) so non-oracle unitary steps have
cost `0` under `CostModel.ofEmbeddedOracle` for real marking oracles.
-/

section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

@[expose] public section

namespace QuantumComputation.Specs.GroverSolution

open Operator ResourceCounting Real
open scoped Matrix NNReal NNRat

open Classical in
/-- Lift a classical predicate to a zero-one quantum assertion. -/
noncomputable def liftPureProp {Var : Type} {d : ℕ} (p : Store Var → Prop) :
    CQAssertion (Store Var) d :=
  fun σ ↦ if p σ then (1 : Observable (Fin d)) else 0

open Classical in
/-- Pointwise evaluation of `liftPureProp`. -/
@[simp, grind =]
lemma liftPureProp_apply {Var : Type} {d : ℕ} (p : Store Var → Prop) (σ : Store Var) :
    liftPureProp (d := d) p σ = if p σ then 1 else 0 := rfl

/-! ## Exact Spec Mirrors (`rfl` bridge with `QuantumComputation.Specs`) -/

/-- Marking oracle for a subset `S ⊆ Fin (2 ^ n)` acting on `n + 1` qubits. -/
noncomputable def groverSetMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  permutationUnitary (tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)

/-- Synchronous `m`-slot parallel marking oracle for `S ⊆ Fin (2 ^ n)` on `(n + 1) * m` qubits. -/
noncomputable def groverParallelMarkingOracle {n : ℕ} (m : ℕ)
    (S : Finset (Fin (2 ^ n))) : Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])).embedUnitary
      (groverSetMarkingOracle S)).prod

/-- All `k`-element target subsets of `Fin (2 ^ n)`. -/
def groverTargetSets (n k : ℕ) : Finset (Finset (Fin (2 ^ n))) :=
  (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k

/-- Uniform-average expected oracle cost bound across all `S ∈ groverTargetSets n k`. -/
def AvgOracleCostBound {Var : Type} [DecidableEq Var] {d n : ℕ} [NeZero d] (k : ℕ)
    (costModel : Finset (Fin (2 ^ n)) → CostModel d)
    (prog : Finset (Fin (2 ^ n)) → QProg Var d) (bound : ℝ) : Prop :=
  ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
    (∀ S ∈ groverTargetSets n k, CostBound (costModel S) (prog S) (q S)) ∧
    (∑ S ∈ groverTargetSets n k, (q S : ℝ)) / (groverTargetSets n k).card ≤ bound

/-- Reference parallel single-find query scale `(π / 4) * √(2 ^ n / (m * k))`. -/
noncomputable def vanillaFindAnyCost (n m k : ℕ) : ℝ :=
  (π / 4) * √((2 ^ n : ℝ) / (m * k))

/-- Dyadic parameter grid `{1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024}`. -/
def groverGrid : Finset ℕ :=
  (Finset.range 11).image (fun i : ℕ ↦ 2 ^ i)

/-! ## Dyadic Grid Selectors and Membership Lemmas -/

/-- Full `11 × 11` dyadic grid selector claiming every `(m, k) ∈ groverGrid × groverGrid`. -/
def gridCells (m k : ℕ) : Bool :=
  decide (m ∈ groverGrid) && decide (k ∈ groverGrid)

theorem one_le_of_mem_groverGrid {x : ℕ} (hx : x ∈ groverGrid) : 1 ≤ x := by
  simp only [groverGrid, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Nat.one_le_two_pow

theorem gridCells_nonempty : ∃ m k, gridCells m k = true :=
  ⟨1, 1, by decide⟩

theorem gridCells_mem_grid {m k : ℕ} (hmk : gridCells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid := by
  simpa [gridCells] using hmk

/-! ## Global-Phase Unitary Tagging for `CostModel.ofEmbeddedOracle` -/

/-- Every entry of `A` has zero imaginary part. -/
abbrev IsRealMatrix {d : ℕ} (A : Operator d) : Prop :=
  ∀ i j : Fin d, (A i j).im = 0

/-- Multiply real unitaries by global phase `Complex.I` so they never coincide matrix-wise with
a real embedded marking oracle while acting identically under `wp`. -/
noncomputable def phaseTag {d : ℕ} (V : Unitary d) : Unitary d :=
  open Classical in
  if IsRealMatrix V.1 then
    ⟨Complex.I • V.1, by
      rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm,
        show (Complex.I : ℂ) * star Complex.I = 1 by simp, one_smul]
      exact V.2.2⟩
  else V

@[simp]
theorem wp_phaseTag {Var : Type} {d : ℕ} (V : Unitary d) (θ : CQAssertion (Store Var) d) :
    CQAssertion.qAssign (phaseTag V) θ = CQAssertion.qAssign V θ := by
  unfold phaseTag
  split_ifs
  · funext σ
    refine Subtype.ext (Subtype.ext ?_)
    rw [qhlQAssign_val, qhlQAssign_val]
    change (Complex.I • V.1)ᴴ * (θ σ).1.1 * (Complex.I • V.1) = _
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show star (Complex.I : ℂ) * Complex.I = 1 by simp, one_smul]
  · rfl

theorem permutationUnitary_apply {d : ℕ} (e : Equiv.Perm (Fin d)) (i j : Fin d) :
    (permutationUnitary e).1 i j = if i = e j then 1 else 0 := by
  have h := congrFun (permutationUnitary_smul_col e j 1) i
  simpa [Matrix.col_apply, Pi.single_apply] using h

theorem isRealMatrix_permutationUnitary {d : ℕ} (e : Equiv.Perm (Fin d)) :
    IsRealMatrix (permutationUnitary e).1 := fun i j ↦ by
  rw [permutationUnitary_apply]
  split_ifs <;> simp

theorem isRealMatrix_embedMatrix {w q : ℕ} (r : QRegister w q) {A : Operator (2 ^ w)}
    (hA : IsRealMatrix A) : IsRealMatrix (r.embedMatrix A) := fun i j ↦ by
  rw [QRegister.embedMatrix_apply]
  split_ifs <;> simp [hA (r.extractIndex i) (r.extractIndex j)]

theorem isRealMatrix_groverSetMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    IsRealMatrix (groverSetMarkingOracle S).1 :=
  isRealMatrix_permutationUnitary _

theorem isRealMatrix_listProd {d : ℕ} {l : List (Unitary d)}
    (hl : ∀ U ∈ l, IsRealMatrix U.1) : IsRealMatrix l.prod.1 := by
  induction l with
  | nil =>
    intro i j
    by_cases h : i = j <;> simp [h]
  | cons U Us ih =>
    intro i j
    rw [List.prod_cons, Submonoid.coe_mul]
    simp only [Matrix.mul_apply, Complex.im_sum]
    exact Finset.sum_eq_zero fun k _ ↦ by
      rw [Complex.mul_im, hl U List.mem_cons_self i k,
        ih (fun V hV ↦ hl V (List.mem_cons_of_mem U hV)) k j]
      ring

theorem isRealMatrix_groverParallelMarkingOracle {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    IsRealMatrix (groverParallelMarkingOracle m S).1 := by
  refine isRealMatrix_listProd fun U hU ↦ ?_
  rw [List.mem_ofFn] at hU
  obtain ⟨i, rfl⟩ := hU
  rw [QRegister.embedUnitary_val]
  exact isRealMatrix_embedMatrix _ (isRealMatrix_groverSetMarkingOracle S)

theorem ofEmbeddedOracle_unitaryCost_phaseTag_eq_zero {w q : ℕ}
    {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1)
    (V : Unitary (2 ^ q)) :
    (CostModel.ofEmbeddedOracle oracle).unitaryCost (phaseTag V) = 0 := by
  unfold CostModel.ofEmbeddedOracle
  dsimp only
  refine ite_eq_right fun ⟨r, hr⟩ ↦ ?_
  have hR : IsRealMatrix (phaseTag V).1 := by
    rw [hr, QRegister.embedUnitary_val]
    exact isRealMatrix_embedMatrix r horacle
  unfold phaseTag at hR
  split_ifs at hR with hV
  · have hV0 : V.1 = 0 := Matrix.ext fun i j ↦
      Complex.ext (by simpa using hR i j) (by simpa using hV i j)
    have hun := congrFun (congrFun V.2.2 (0 : Fin (2 ^ q))) (0 : Fin (2 ^ q))
    simp [hV0] at hun
  · exact hV hR

theorem costBound_qAssign_phaseTag {Var : Type} [DecidableEq Var] {w q : ℕ}
    {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1)
    (V : Unitary (2 ^ q)) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle) (.qAssign (phaseTag V)) 0 := by
  simpa [ofEmbeddedOracle_unitaryCost_phaseTag_eq_zero horacle V] using
    CostBound.qAssign (Var := Var) (CostModel.ofEmbeddedOracle oracle) (phaseTag V)

end QuantumComputation.Specs.GroverSolution
