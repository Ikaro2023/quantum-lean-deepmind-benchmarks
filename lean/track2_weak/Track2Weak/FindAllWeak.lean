module

public import Track2Grover.TighterFindAny
public import Track2Weak.WeakBatch

/-! Frozen FindAll interface, with a finite-size fallback and complete-batch weak measurements
on the 1024-slot, 512-target cell. Common model declarations and FindAny come from the
independently verified FindAny implementation of the same frozen schema. -/

@[expose] public section
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped NNReal NNRat
open _root_.QuantumComputation.Specs.Grover (Var)
open _root_.QuantumComputation.Specs.Grover.Var (res)

private instance : Subsingleton Var := ⟨fun a b ↦ by cases a; cases b; rfl⟩

def groverFindAllCells (m k : ℕ) : Bool := decide (m = 1024 ∧ k = 512)

theorem groverFindAllCells_nonempty : ∃ m k, groverFindAllCells m k = true :=
  ⟨1024, 512, rfl⟩

theorem groverFindAllCells_mem_grid {m k : ℕ} (hmk : groverFindAllCells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid := by
  obtain ⟨rfl,rfl⟩ : m = 1024 ∧ k = 512 := of_decide_eq_true hmk
  exact ⟨Finset.mem_image.mpr ⟨10, by decide, by decide⟩,
    Finset.mem_image.mpr ⟨9, by decide, by decide⟩⟩

noncomputable abbrev weakChosenBatch (n : ℕ) :=
  Track2Weak.routedBatch res Track2Weak.weakQubits 80000
    (Track2Weak.weakTrial res Track2Weak.Cert.certRows) n

noncomputable def groverFindAllQubits (n m k : ℕ) : ℕ := (weakChosenBatch n).1

noncomputable def groverFindAllCircuit (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ groverFindAllQubits n m k)) Var
      (groverFindAllQubits n m k) ((n + 1) * m) :=
  if h : m = 1024 ∧ k = 512 then by
    obtain ⟨rfl,rfl⟩ := h
    exact (weakChosenBatch n).2
  else .skip

private theorem circuit_eq (n : ℕ) : groverFindAllCircuit n 1024 512 = (weakChosenBatch n).2 := by
  unfold groverFindAllCircuit
  rw [dite_eq_left (show 1024 = 1024 ∧ 512 = 512 from ⟨rfl,rfl⟩)]

open QProg.Notation in
noncomputable def groverFindAllProgram (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : QProg Var (2 ^ groverFindAllQubits n m k) :=
  qset ;; (groverFindAllCircuit n m k).compile QProg.qAssign oracle

theorem groverFindAll_correctness {n m k : ℕ} (hn : 1 ≤ n)
    (hmk : groverFindAllCells m k = true) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ ⊤ ⦄
    groverFindAllProgram n m k (groverParallelMarkingOracle m S)
    ⦃ fun σ ↦ ⌜decodeTargets n k (σ res) = S⌝ ⦄ := by
  obtain ⟨rfl,rfl⟩ : m = 1024 ∧ k = 512 := of_decide_eq_true hmk
  unfold groverFindAllProgram
  rw [circuit_eq]
  exact Track2Weak.routedBatch_correctness (Track2Weak.weakBatchBound res) hn hkN hS

def groverFindAllRelCost (m k : ℕ) : ℚ≥0 := NNRat.divNat 26768771052 1000000000000

theorem groverFindAll_rel_cost {m k : ℕ} (hmk : groverFindAllCells m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ groverFindAllProgram n m k (groverParallelMarkingOracle m S))
        (groverFindAllRelCost m k * vanillaFindAllCost n m k) := by
  obtain ⟨rfl,rfl⟩ : m = 1024 ∧ k = 512 := of_decide_eq_true hmk
  simp only [groverFindAllProgram, circuit_eq]
  exact Track2Weak.routedBatch_rel_cost (Track2Weak.weakBatchBound res)

theorem groverFindAllRelCost_target :
    groverFindAllRelCost 1024 512 ≤ NNRat.divNat 26770000000 1000000000000 := by decide +kernel

end QuantumComputation.Specs

#print axioms QuantumComputation.Specs.groverFindAllCells_nonempty
#print axioms QuantumComputation.Specs.groverFindAllCells_mem_grid
#print axioms QuantumComputation.Specs.groverFindAll_correctness
#print axioms QuantumComputation.Specs.groverFindAll_rel_cost
#print axioms QuantumComputation.Specs.groverFindAllRelCost_target
