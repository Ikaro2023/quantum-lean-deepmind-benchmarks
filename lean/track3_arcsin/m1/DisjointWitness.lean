module

public import ExactPublic

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl.ExactAudit

/-- Canonical disjoint placement of the 50 data wires (`0..49`) and 50 clean ancilla wires
(`50..99`) on a 100-qubit register, witnessing non-vacuity of `exactPublicK25`. -/
noncomputable def canonicalK25Data : QRegister (2 * ArcsinPrec.k25.k) 100 :=
  QRegister.block 0 (2 * ArcsinPrec.k25.k) (by decide)

noncomputable def canonicalK25Anc : QRegister (arcsinAncillas .k25) 100 :=
  QRegister.block 50 (arcsinAncillas .k25) (by
    classical
    have hb : isBenchRegime ArcsinPrec.k25.k ArcsinPrec.k25.eps := ⟨rfl, le_rfl⟩
    have ha : arcsinAncillas .k25 = 50 := ite_eq_left hb
    omega)

theorem canonicalK25_disjoint : canonicalK25Data.DisjointWires canonicalK25Anc := by
  unfold canonicalK25Data canonicalK25Anc
  exact QRegister.block_disjoint_of_le 0 (2 * ArcsinPrec.k25.k) 50 (arcsinAncillas .k25)
    _ _ (by decide)

/-- Non-vacuity witness for `exactPublicK25`: the canonical 100-qubit placement is disjoint and
attains exact compiled counts `T = 3662`, `TOFF = 0`, and spacetime `366200`. -/
theorem exactPublicK25_nonvacuous :
    ∃ (rd : QRegister (2 * ArcsinPrec.k25.k) 100) (ra : QRegister (arcsinAncillas .k25) 100),
      rd.DisjointWires ra ∧
      (arcsinProgram .k25 rd ra).count PrimitiveGate.T = 3662 ∧
      (arcsinProgram .k25 rd ra).count PrimitiveGate.TOFF = 0 ∧
      arcsinSpacetime .k25 rd ra = 366200 := by
  refine ⟨canonicalK25Data, canonicalK25Anc, canonicalK25_disjoint, ?_⟩
  exact exactPublicK25 canonicalK25Data canonicalK25Anc canonicalK25_disjoint

#print axioms canonicalK25_disjoint
#print axioms exactPublicK25_nonvacuous

end QuantumComputation.Specs.ArcsinImpl.ExactAudit
