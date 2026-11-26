import Track1THC.CleanOps

/-!
# Clifford gadgets as clean subroutines (Track 1, Round 3)

`TOFF = 0`, `T = 0` building blocks with exact clean realizations, assembled with the
`CleanOps` composition algebra:

* `realizesClean_gate1`: any single-qubit primitive gate on wire `t` realizes its unitary.
* `czCircuit` (`H t ; CNOT c t ; H t`, the library's `CZ`) realizes `H₁ · CNOT · H₁` on `pair c t`
  and has `CostBound 0`.
* `ccz`: Toffoli sandwiched by Hadamards on the target (Jones-AND `T = 4`, `TOFF = 0`).
-/

open QuantumComputation.Specs Operator QProg Track1THC.CleanOps

namespace Track1THC.CliffordGadgets

variable {Var : Type} [DecidableEq Var] {n m : ℕ}

theorem realizesClean_gate1 (g : PrimitiveGate 1) (t : Wire n) (rA : QRegister m n)
    (h : (QRegister.singleton t).DisjointWires rA) :
    RealizesCleanSubroutine (Var := Var) (QRegister.singleton t) rA h g.eval
      (Circuit.single g t).compile := by
  exact realizesClean_qAssign g.eval

theorem pair_compose_singleton_one (c t : Wire n) (hct : c ≠ t) :
    (QRegister.pair c t hct).compose (QRegister.singleton (1 : Fin 2)) = QRegister.singleton t := by
  ext i
  fin_cases i
  rfl

/-- Hadamard on the second wire of a two-wire register, as a `4 × 4` unitary. -/
noncomputable def hOnSecond : Unitary (2 ^ 2) :=
  (QRegister.singleton (1 : Fin 2)).embedUnitary PrimitiveGate.h.eval

/-- The library's `CZ` gadget `H t ; CNOT c t ; H t` (no `T`, no `TOFF`, no ancilla). -/
def czCircuit (c t : Wire n) (hct : c ≠ t) : Circuit n :=
  Circuit.seq (Circuit.single PrimitiveGate.h t)
    (Circuit.seq (Circuit.CNOT c t hct) (Circuit.single PrimitiveGate.h t))

/-- The unitary realized by `czCircuit`, as an operator on the `(c, t)` pair. -/
noncomputable def czUnitary : Unitary (2 ^ 2) :=
  hOnSecond * PrimitiveGate.cnot.eval * hOnSecond

theorem realizesClean_cz (c t : Wire n) (hct : c ≠ t) (rA : QRegister m n)
    (hd : (QRegister.pair c t hct).DisjointWires rA) :
    RealizesCleanSubroutine (Var := Var) (QRegister.pair c t hct) rA hd czUnitary
      (czCircuit c t hct).compile := by
  have hsing : (QRegister.singleton t).DisjointWires rA := by
    have := hd.compose_left (QRegister.singleton (1 : Fin 2))
    rwa [pair_compose_singleton_one c t hct] at this
  have hH : RealizesCleanSubroutine (Var := Var) (QRegister.pair c t hct) rA hd hOnSecond
      (Circuit.single PrimitiveGate.h t).compile := by
    refine realizesClean_of_embed_eq ?_ (realizesClean_gate1 PrimitiveGate.h t rA hsing)
    rw [hOnSecond, ← QRegister.embedUnitary_compose, pair_compose_singleton_one c t hct]
  have hC : RealizesCleanSubroutine (Var := Var) (QRegister.pair c t hct) rA hd PrimitiveGate.cnot.eval
      (Circuit.CNOT c t hct).compile := realizesClean_qAssign _
  have e := realizesClean_seq hH (realizesClean_seq hC hH)
  simpa [czCircuit, czUnitary, mul_assoc] using e

theorem czCircuit_cost {V : Type} (c t : Wire n) (hct : c ≠ t) :
    CostBound (DynamicCircuit.circuit (czCircuit c t hct) : DynamicCircuit V n) 0 := by
  refine ⟨?_, ?_⟩ <;> simp [czCircuit, Circuit.CNOT, Circuit.single]


/-- A chain of `L.length` Toffoli gates on arbitrary triples `sub` of a common target `rT`, all
sharing one clean ancilla wire `anc`: exact clean realization of the product of the Toffoli
unitaries, with `TOFF = 0` and `T ≤ 4 · L.length`. -/
theorem exists_toffoli_chain {k' : ℕ} (v : Var) (rT : QRegister k' n) (anc : Wire n)
    (hanc : ∀ i, rT i ≠ anc) (hbig : rT.DisjointWires (QRegister.singleton anc)) :
    ∀ L : List (QRegister 3 k'), ∃ P : DynamicCircuit Var n, CostBound P (4 * L.length) ∧
      RealizesCleanSubroutine rT (QRegister.singleton anc) hbig
        (chainU (L.map fun sub ↦ sub.embedUnitary PrimitiveGate.toffoli.eval)) P.compile
  | [] => ⟨DynamicCircuit.identity, by simpa using CostBound.identity,
      by simpa [chainU] using realizesClean_skip⟩
  | sub :: L => by
      obtain ⟨P₁, c₁, r₁⟩ := exists_jonesToffoli_on_target v rT sub anc hanc hbig
      obtain ⟨P₂, c₂, r₂⟩ := exists_toffoli_chain v rT anc hanc hbig L
      refine ⟨DynamicCircuit.seq P₁ P₂, ?_, ?_⟩
      · have := CostBound.seq c₁ c₂
        exact this.mono (by simp [List.length_cons]; omega)
      · simpa [chainU] using realizesClean_seq r₁ r₂

end Track1THC.CliffordGadgets
