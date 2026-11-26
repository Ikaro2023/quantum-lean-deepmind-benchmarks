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
public import QuantumComputation.Circuits.DynamicCircuit
public import Mathlib.Data.Finset.Powerset
public import QuantumComputation.QuantumHoareLogic.WP
public import Track2Grover.Any.FindAny

/-!
# Grover Search Specifications

Query-model specifications for parallel multi-target marking-oracle search on a domain of size
`2 ^ n`, using adaptive dynamic circuits (allowing mid-circuit measurements, `.qIf`, and `.qWhile`)
in Zalka's shared-memory synchronous parallel query model (`m` disjoint `(n + 1)`-qubit
marking-oracle slots per round via `groverParallelMarkingOracle m S` on an unconstrained shared
qubit register), succeeding with probability `1` on claimed cells `(m, k)` of `groverGrid`:

1. **Find any marked item** (`groverFindAny*`): return some `x ∈ S`, with uniform-average expected
   parallel oracle rounds bounded relative to `vanillaFindAnyCost`.
2. **Find all marked items** (`groverFindAll*`): recover the full target set `S` via
   `decodeTargets`, with uniform-average expected parallel oracle rounds bounded relative to
   `vanillaFindAllCost`.

Expected query costs are evaluated semantically on the compiled programs via
`CostModel.ofEmbeddedOracle`, charging `1` per oracle call and `0` for all other operations (except
any unitary step whose matrix happens to coincide with an embedded oracle call; see
`CostModel.ofEmbeddedOracle`).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator ResourceCounting Real
open scoped NNReal NNRat

/-- By default we allow only a single variable. -/
inductive Grover.Var where | res deriving DecidableEq, Inhabited

open Grover (Var)
open Grover.Var (res)

/-! ## Parallel and multi-target search with a marking oracle -/

/-- Marking oracle for a subset `S ⊆ Fin (2 ^ n)` acting on `n + 1` qubits.

Under `tableAddPerm` (`finProdFinEquiv : (x, b) ↦ b + 2 * x`) and the little-endian `QRegister`
convention, logical wire `0` is the marker bit `b` and logical wires `1..n` hold the `n`-bit index
`x`, mapping basis state `(b, x)` to `(b ⊕ [x ∈ S], x)`. A phase flip (`b` in `|−⟩`), a candidate
check, and a weak measurement each take one call, without uncomputation. -/
noncomputable def groverSetMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  permutationUnitary (tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)

/-- Synchronous `m`-slot parallel marking oracle for `S ⊆ Fin (2 ^ n)` on `(n + 1) * m` qubits
(`n + 1` wires at `m = 1`), representing one parallel query round of `m` independent copies of
`groverSetMarkingOracle S` on pairwise disjoint `(n + 1)`-qubit subregisters of a shared quantum
state (Zalka's parallel query model).

Within the `((n + 1) * m)`-wire oracle register, slot `i : Fin m` occupies logical wires
`i * (n + 1) .. i * (n + 1) + n`: logical wire `i * (n + 1)` is the marker bit `b_i` and the next
`n` wires are `x_i`. Rounds using fewer than `m` active queries route unused marker wires to
ancillas in `|+⟩`, on which `groverSetMarkingOracle S` acts as the identity for every `S`. -/
noncomputable def groverParallelMarkingOracle {n : ℕ} (m : ℕ)
    (S : Finset (Fin (2 ^ n))) : Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])).embedUnitary
      (groverSetMarkingOracle S)).prod

/-- All `k`-element target subsets of `Fin (2 ^ n)`. -/
def groverTargetSets (n k : ℕ) : Finset (Finset (Fin (2 ^ n))) :=
  (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k

/-- Decode up to `k` indices in `Fin (2 ^ n)` from the first `k` base-`2 ^ n` digits (`n`-bit
chunks) of `z.toNat`. -/
def decodeTargets (n k : ℕ) (z : ℤ) : Finset (Fin (2 ^ n)) :=
  (Finset.range k).image fun i ↦
    ⟨(z.toNat / (2 ^ n) ^ i) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩

/-- The predicate that `bound` is the uniform-average expected oracle cost bound across all
`S ∈ groverTargetSets n k`. -/
def AvgOracleCostBound {Var : Type} [DecidableEq Var] {d n : ℕ} [NeZero d] (k : ℕ)
    (costModel : Finset (Fin (2 ^ n)) → CostModel d)
    (prog : Finset (Fin (2 ^ n)) → QProg Var d) (bound : ℝ) : Prop :=
  ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
    (∀ S ∈ groverTargetSets n k, CostBound (costModel S) (prog S) (q S)) ∧
    (∑ S ∈ groverTargetSets n k, (q S : ℝ)) / (groverTargetSets n k).card ≤ bound

/-- Harmonic inverse-square-root sum `∑_{r=1}^k 1 / √r` appearing in sequential coupon-collecting
multi-target Grover search. -/
noncomputable def groverHarmonicSqrtSum (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 k, 1 / √r

/-- Reference parallel single-find query scale `(π / 4) * √(2 ^ n / (m * k))` for finding any one
of `k` marked items with `m` parallel queries per round. -/
noncomputable def vanillaFindAnyCost (n m k : ℕ) : ℝ :=
  (π / 4) * √((2 ^ n : ℝ) / (m * k))

/-- Reference unpartitioned coupon-collecting parallel query scale
`(π / 4) * (∑_{r=1}^k 1 / √r) * √(2 ^ n / m)` for finding all `k` marked items sequentially across
`k` stages with `m` parallel queries per round. -/
noncomputable def vanillaFindAllCost (n m k : ℕ) : ℝ :=
  (π / 4) * groverHarmonicSqrtSum k * √((2 ^ n : ℝ) / m)

/-! ### Finding at least one marked item (`groverFindAny`) -/

/-- Dyadic parameter grid `{1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024}` (`2 ^ 0 .. 2 ^ 10`)
for parallel oracle slots `m` and marked target count `k`. -/
def groverGrid : Finset ℕ :=
  (Finset.range 11).image (fun i : ℕ ↦ 2 ^ i)

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


theorem track2FindAny_strict (m k : ℕ) :
    groverFindAnyRelCost m k < 514159265358979323847 / 628318530717958647692 := by
  norm_num [groverFindAnyRelCost, GroverSolution.FindAny.relCost]

#print axioms groverFindAnyCells_nonempty
#print axioms groverFindAnyCells_mem_grid
#print axioms groverFindAny_correctness
#print axioms groverFindAny_rel_cost
#print axioms track2FindAny_strict

end QuantumComputation.Specs
