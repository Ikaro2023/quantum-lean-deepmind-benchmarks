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
public import Track2Grover.Engine.Rk128kEngine
public import Track2Grover.FindAllRow
public import QuantumComputation.Circuits.DynamicCircuit
public import Mathlib.Data.Finset.Powerset
public import QuantumComputation.QuantumHoareLogic.WP

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

/-! ### Finding all marked items (`groverFindAll`) -/

/-- Selects which cells `(m, k)` of `groverGrid` a solution claims for `groverFindAll`;
the theorems below are required on those cells. -/
def groverFindAllCells (m k : ℕ) : Bool := decide (m = 1024 ∧ k = 512)

private theorem cell_eq {m k : ℕ} (h : groverFindAllCells m k = true) : m = 1024 ∧ k = 512 :=
  of_decide_eq_true h

private theorem grid1024 : 1024 ∈ groverGrid :=
  Finset.mem_image.mpr ⟨10, by decide, by decide⟩

private theorem grid512 : 512 ∈ groverGrid :=
  Finset.mem_image.mpr ⟨9, by decide, by decide⟩

open Track2Grover.FindAllCell

private theorem valid : DickeSol.RampKick128kTableValid 1024 512 2 true values anchors :=
  DickeSol.rkm128kCheckTable_sound ⟨rowChecked, trivial⟩ tableChecked

structure Track2CellProps (m k : ℕ) : Prop where
  mem_m : m ∈ DickeSol.groverGrid
  mem_k : k ∈ DickeSol.groverGrid
  k_le : k ≤ 512
  m_ge : 2 ≤ m
  width : 2 * m ≤ 65536
  table : DickeSol.RampKick128kTableValid m 512 2 true values anchors
  widths : DickeSol.rkm128kCheckAnchorsLMax k 2 anchors = true
  bound : DickeSol.checkAltBound12 m k (values.getD k 0) numerator 1000000000000 = true

theorem track2CellProperties {m k : ℕ} (h : groverFindAllCells m k = true) : Track2CellProps m k := by
  obtain ⟨rfl, rfl⟩ := cell_eq h
  exact ⟨grid1024, grid512, by decide, by decide, by decide, valid, widthsChecked, normalized⟩


/-- `groverFindAllCells` claims at least one cell of `groverGrid`. -/
theorem groverFindAllCells_nonempty : ∃ m k, groverFindAllCells m k = true := by
  exact ⟨1024, 512, rfl⟩

/-- Every cell claimed by `groverFindAllCells` lies on `groverGrid`. -/
theorem groverFindAllCells_mem_grid {m k : ℕ} (hmk : groverFindAllCells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid := by
  obtain ⟨rfl, rfl⟩ := cell_eq hmk
  exact ⟨grid1024, grid512⟩

/-- Total number of qubits used by `groverFindAllCircuit`. -/
def groverFindAllQubits (n m k : ℕ) : ℕ := DickeSol.Stage1.qubits n (2 * m) k

/-- Parallel query-model circuit on `groverFindAllQubits n m k` qubits with `m`-slot parallel
marking-oracle rounds that encodes all `k` marked elements of `S` into `res`. -/
noncomputable def groverFindAllCircuit (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ groverFindAllQubits n m k)) Var
      (groverFindAllQubits n m k) ((n + 1) * m) :=
  if h : groverFindAllCells m k = true then
    let p := track2CellProperties h
    DickeSol.rkm128kCellCircuit res p.mem_m p.mem_k values anchors p.k_le
      (fun _ ↦ p.m_ge) (fun _ ↦ by decide) (by decide) p.width p.table p.widths n
  else .skip

private theorem cellCircuit_eq {n m k : ℕ} (h : groverFindAllCells m k = true) :
    groverFindAllCircuit n m k =
      let p := track2CellProperties h
      DickeSol.rkm128kCellCircuit res p.mem_m p.mem_k values anchors p.k_le
        (fun _ ↦ p.m_ge) (fun _ ↦ by decide) (by decide) p.width p.table p.widths n := by
  unfold groverFindAllCircuit
  exact dite_eq_left h

open QProg.Notation in
/-- Reset all qubits, then run `groverFindAllCircuit` compiled with `oracle`. -/
noncomputable def groverFindAllProgram (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : QProg Var (2 ^ groverFindAllQubits n m k) :=
  qset ;; (groverFindAllCircuit n m k).compile QProg.qAssign oracle

/-- `groverFindAllProgram` recovers the full marked set `S` via `decodeTargets n k (σ res) = S`
with probability `1` for every `k`-element target set `S` on each claimed cell `(m, k)` of
`groverGrid`. -/
theorem groverFindAll_correctness {n m k : ℕ} (hn : 1 ≤ n)
    (hmk : groverFindAllCells m k = true) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ ⊤ ⦄
    groverFindAllProgram n m k (groverParallelMarkingOracle m S)
    ⦃ fun σ ↦ ⌜decodeTargets n k (σ res) = S⌝ ⦄ := by
  let p := track2CellProperties hmk
  unfold groverFindAllProgram
  rw [cellCircuit_eq hmk]
  exact DickeSol.rkm128kCell_correctness res p.mem_m p.mem_k values anchors p.k_le
    (fun _ ↦ p.m_ge) (fun _ ↦ by decide) (by decide) p.width p.table p.widths hn hkN hS

/-- Claimed asymptotic expected parallel-round cost ratio of `groverFindAllProgram` relative to
`vanillaFindAllCost` at a claimed cell `(m, k)` for large `n`. -/
def groverFindAllRelCost (m k : ℕ) : ℚ≥0 := NNRat.divNat numerator 1000000000000

/-- Asymptotic uniform-average expected parallel-round cost bound for `groverFindAllProgram`
relative to `vanillaFindAllCost` for all sufficiently large `n`. -/
theorem groverFindAll_rel_cost {m k : ℕ} (hmk : groverFindAllCells m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ groverFindAllProgram n m k (groverParallelMarkingOracle m S))
        (groverFindAllRelCost m k * vanillaFindAllCost n m k) := by
  let p := track2CellProperties hmk
  simp only [groverFindAllProgram, cellCircuit_eq hmk]
  exact DickeSol.rkm128kCell_rel_cost res p.mem_m p.mem_k values anchors p.k_le
    (fun _ ↦ p.m_ge) (fun _ ↦ by decide) (by decide) p.width p.table p.widths
    ⟨numerator, 1000000000000, rfl, p.bound⟩

theorem groverFindAllRelCost_improves : groverFindAllRelCost 1024 512 <
    NNRat.divNat 6756116497 250000000000 := by decide +kernel

end QuantumComputation.Specs

#print axioms QuantumComputation.Specs.groverFindAllCells_nonempty
#print axioms QuantumComputation.Specs.groverFindAllCells_mem_grid
#print axioms QuantumComputation.Specs.groverFindAll_correctness
#print axioms QuantumComputation.Specs.groverFindAll_rel_cost
#print axioms QuantumComputation.Specs.groverFindAllRelCost_improves
