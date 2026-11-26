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
public import Track2Grover.Engine.StageLoop
public import QuantumComputation.Maths.Trigonometry

/-!
# Cellwise Cost Profile and Compositional Family Specification (`BaselineRouter`)
Provides `FindAllCostProfile`, `dispatchFindAllCircuit`, and `ValidFindAllFamily` on the
shared `(n + 1) * m + n * k + 1`-qubit register layout (`findAllQubits n m k`).
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal NNRat ENNReal
/-! ## 1. Computable Cost Profiles and Cellwise Minimum Selector -/
/-- Computable cellwise cost profile for a `GroverFindAll` construction family. -/
structure FindAllCostProfile where
  /-- Computable predicate selecting the `(m, k)` cells supported by this family. -/
  validCell : ℕ → ℕ → Bool
  /-- Claimed asymptotic relative cost `ℚ≥0` at cell `(m, k)`. -/
  relCost : ℕ → ℕ → ℚ≥0
  /-- Asymptotic threshold `n₀(m, k)` above which the uniform cost bound holds. -/
  n0 : ℕ → ℕ → ℕ
/-- Computable cellwise selector choosing `p₁` over `p₂` at `(m, k)` whenever `p₁` supports
  `(m, k)` and either `p₂` does not support `(m, k)` or `p₁.relCost m k ≤ p₂.relCost m k`. -/
def FindAllCostProfile.selectLeft (p₁ p₂ : FindAllCostProfile) (m k : ℕ) : Bool :=
  p₁.validCell m k && (!p₂.validCell m k || decide (p₁.relCost m k ≤ p₂.relCost m k))
/-- Pointwise minimum combination of two `FindAllCostProfile`s across supported cells. -/
def FindAllCostProfile.combine (p₁ p₂ : FindAllCostProfile) : FindAllCostProfile where
  validCell m k := p₁.validCell m k || p₂.validCell m k
  relCost m k := if p₁.selectLeft p₂ m k then p₁.relCost m k else p₂.relCost m k
  n0 m k := if p₁.selectLeft p₂ m k then p₁.n0 m k else p₂.n0 m k
@[simp]
theorem FindAllCostProfile.combine_validCell_of_left {p₁ p₂ : FindAllCostProfile} {m k : ℕ}
    (hv₁ : p₁.validCell m k = true) :
    (p₁.combine p₂).validCell m k = true := by
  simp [FindAllCostProfile.combine, hv₁]
theorem FindAllCostProfile.validCell_left_of_selectLeft {p₁ p₂ : FindAllCostProfile} {m k : ℕ}
    (hsel : p₁.selectLeft p₂ m k = true) :
    p₁.validCell m k = true := by
  rw [FindAllCostProfile.selectLeft, Bool.and_eq_true] at hsel
  exact hsel.1
theorem FindAllCostProfile.validCell_right_of_not_selectLeft {p₁ p₂ : FindAllCostProfile} {m k : ℕ}
    (hcomb : (p₁.combine p₂).validCell m k = true)
    (hsel : p₁.selectLeft p₂ m k = false) :
    p₂.validCell m k = true := by
  dsimp only [FindAllCostProfile.combine] at hcomb
  cases hv₂ : p₂.validCell m k
  · rw [hv₂, Bool.or_false] at hcomb
    rw [FindAllCostProfile.selectLeft, hcomb, hv₂] at hsel
    cases hsel
  · rfl
theorem FindAllCostProfile.combine_relCost_le_left {p₁ p₂ : FindAllCostProfile} {m k : ℕ}
    (hv₁ : p₁.validCell m k = true) :
    (p₁.combine p₂).relCost m k ≤ p₁.relCost m k := by
  dsimp only [FindAllCostProfile.combine]
  cases hsel : p₁.selectLeft p₂ m k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hv₂ : p₂.validCell m k
    · rw [FindAllCostProfile.selectLeft, hv₁, hv₂] at hsel
      cases hsel
    · rw [FindAllCostProfile.selectLeft, hv₁, hv₂, Bool.true_and, Bool.not_true, Bool.false_or,
        decide_eq_false_iff_not] at hsel
      exact le_of_not_ge hsel
  · simp only [↓reduceIte]
    exact le_rfl
theorem FindAllCostProfile.combine_relCost_le_right {p₁ p₂ : FindAllCostProfile} {m k : ℕ}
    (hv₂ : p₂.validCell m k = true) :
    (p₁.combine p₂).relCost m k ≤ p₂.relCost m k := by
  dsimp only [FindAllCostProfile.combine]
  cases hsel : p₁.selectLeft p₂ m k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact le_rfl
  · simp only [↓reduceIte]
    rw [FindAllCostProfile.selectLeft, hv₂, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hsel
    exact hsel.2
theorem FindAllCostProfile.combine_relCost_eq_min {p₁ p₂ : FindAllCostProfile} {m k : ℕ}
    (hv₁ : p₁.validCell m k = true) (hv₂ : p₂.validCell m k = true) :
    (p₁.combine p₂).relCost m k = min (p₁.relCost m k) (p₂.relCost m k) := by
  apply le_antisymm
  · exact le_min (p₁.combine_relCost_le_left hv₁) (p₁.combine_relCost_le_right hv₂)
  · dsimp only [FindAllCostProfile.combine]
    cases p₁.selectLeft p₂ m k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact min_le_right _ _
    · simp only [↓reduceIte]
      exact min_le_left _ _
/-! ## 2. Circuit Dispatcher and Compositional Family Specification -/
/-- Cellwise circuit dispatcher (`noncomputable abbrev` preserving kernel
  reducibility-hint height). -/
noncomputable abbrev dispatchFindAllCircuit {Var : Type}
    (useLeft : ℕ → ℕ → Bool)
    (c₁ c₂ : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m))
    (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  if useLeft m k then c₁ n m k else c₂ n m k
/-- Specification that `circuit` is a zero-error `GroverFindAll` construction on supported
  grid
  cells (`p.validCell m k = true`) achieving uniform asymptotic relative cost `p.relCost m
  k` for all
  `n ≥ p.n0 m k`. -/
structure ValidFindAllFamily {Var : Type} [DecidableEq Var] (res : Var)
    (p : FindAllCostProfile)
    (circuit : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)) : Prop where
  correctness :
    ∀ {n m k : ℕ} {S : Finset (Fin (2 ^ n))},
      1 ≤ n → isGridCell m k = true → p.validCell m k = true → k ≤ 2 ^ n →
        S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k →
        ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) ⦄
        (QProg.qSet ;; (circuit n m k).compile QProg.qAssign (parallelMarkingOracle m S))
        ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄
  costBound_uniform :
    ∀ {m k : ℕ}, isGridCell m k = true → p.validCell m k = true →
      ∀ n ≥ p.n0 m k, k ≤ 2 ^ n →
        ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
          (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
            CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
              (QProg.qSet ;; (circuit n m k).compile QProg.qAssign
                (parallelMarkingOracle m S))
              (q S)) ∧
          (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
              ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
            ((p.relCost m k : ℚ≥0) : ℝ) *
              ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m))
theorem ValidFindAllFamily.combine {Var : Type} [DecidableEq Var] {res : Var}
    {p₁ p₂ : FindAllCostProfile}
    {c₁ c₂ : ∀ n m k : ℕ,
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)}
    (h₁ : ValidFindAllFamily res p₁ c₁)
    (h₂ : ValidFindAllFamily res p₂ c₂) :
    ValidFindAllFamily res (p₁.combine p₂)
      (dispatchFindAllCircuit (p₁.selectLeft p₂) c₁ c₂) where
  correctness hn hmk hvalid hkN hS := by
    dsimp only [dispatchFindAllCircuit]
    cases hsel : p₁.selectLeft p₂ _ _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact h₂.correctness hn hmk (p₁.validCell_right_of_not_selectLeft hvalid hsel) hkN hS
    · simp only [↓reduceIte]
      exact h₁.correctness hn hmk (p₁.validCell_left_of_selectLeft hsel) hkN hS
  costBound_uniform hmk hvalid := by
    dsimp only [FindAllCostProfile.combine, dispatchFindAllCircuit]
    cases hsel : p₁.selectLeft p₂ _ _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact h₂.costBound_uniform hmk (p₁.validCell_right_of_not_selectLeft hvalid hsel)
    · simp only [↓reduceIte]
      exact h₁.costBound_uniform hmk (p₁.validCell_left_of_selectLeft hsel)
end QuantumComputation.Specs.GroverFindAll
