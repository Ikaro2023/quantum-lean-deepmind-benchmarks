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
public import Track2Grover.FindAll
public import Track2Grover.Any.FindAny

/-! Historical sign-only FindAll and FindAny positive control for the frozen interface. -/
@[expose] public section
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped NNReal NNRat
open Grover (Var)
open Grover.Var (res)

/-- Selects which cells `(m, k)` of `groverGrid` a solution claims for `groverFindAny`;
the theorems below are required on those cells. -/
def groverFindAnyCells (m k : ℕ) : Bool :=
  GroverSolution.FindAny.cells m k

/-- `groverFindAnyCells` claims at least one cell of `groverGrid`. -/
theorem groverFindAnyCells_nonempty : ∃ m k, groverFindAnyCells m k = true :=
  GroverSolution.FindAny.cells_nonempty

/-- Every cell claimed by `groverFindAnyCells` lies on `groverGrid`. -/
theorem groverFindAnyCells_mem_grid {m k : ℕ} (hmk : groverFindAnyCells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid :=
  GroverSolution.FindAny.cells_mem_grid hmk

/-- Total number of qubits used by `groverFindAnyCircuit`. -/
def groverFindAnyQubits (n m k : ℕ) : ℕ :=
  GroverSolution.FindAny.qubits n m k

/-- Parallel query-model circuit on `groverFindAnyQubits n m k` qubits with `m`-slot parallel
marking-oracle rounds that writes at least one marked element of `S` into `res`. -/
noncomputable def groverFindAnyCircuit (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ groverFindAnyQubits n m k)) Var
      (groverFindAnyQubits n m k) ((n + 1) * m) :=
  GroverSolution.FindAny.circuit res n m k

open QProg.Notation in
/-- Reset all qubits, then run `groverFindAnyCircuit` compiled with `oracle`. -/
noncomputable def groverFindAnyProgram (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : QProg Var (2 ^ groverFindAnyQubits n m k) :=
  qset ;; (groverFindAnyCircuit n m k).compile QProg.qAssign oracle

/-- `groverFindAnyProgram` writes some marked element `x ∈ S` into `res` with probability `1` for
every `k`-element target set `S` on each claimed cell `(m, k)` of `groverGrid`. -/
theorem groverFindAny_correctness {n m k : ℕ} (hn : 1 ≤ n)
    (hmk : groverFindAnyCells m k = true) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ ⊤ ⦄
    groverFindAnyProgram n m k (groverParallelMarkingOracle m S)
    ⦃ fun σ ↦ ⌜∃ x ∈ S, σ res = x.val⌝ ⦄ :=
  GroverSolution.FindAny.correctness res hn hmk hkN hS

/-- Claimed asymptotic expected parallel-round cost ratio of `groverFindAnyProgram` relative to
`vanillaFindAnyCost` at a claimed cell `(m, k)` for large `n`. -/
def groverFindAnyRelCost (m k : ℕ) : ℚ≥0 :=
  GroverSolution.FindAny.relCost m k

/-- Asymptotic uniform-average expected parallel-round cost bound for `groverFindAnyProgram`
relative to `vanillaFindAnyCost` for all sufficiently large `n`. -/
theorem groverFindAny_rel_cost {m k : ℕ} (hmk : groverFindAnyCells m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ groverFindAnyProgram n m k (groverParallelMarkingOracle m S))
        (groverFindAnyRelCost m k * vanillaFindAnyCost n m k) :=
  GroverSolution.FindAny.rel_cost res hmk


#print axioms groverFindAnyCells_nonempty
#print axioms groverFindAnyCells_mem_grid
#print axioms groverFindAny_correctness
#print axioms groverFindAny_rel_cost
#print axioms groverFindAllCells_nonempty
#print axioms groverFindAllCells_mem_grid
#print axioms groverFindAll_correctness
#print axioms groverFindAll_rel_cost
end QuantumComputation.Specs
