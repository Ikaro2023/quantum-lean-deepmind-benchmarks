module

public import QuantumComputationDiscoveries.Primitives.Arcsin
public import ExactCount

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl.ExactAudit

private theorem disjointCast {n a b c d : ℕ} (h₁ : a = b) (h₂ : c = d)
    (rd : QRegister a n) (ra : QRegister c n) (hd : rd.DisjointWires ra) :
    (castReg h₁ rd).DisjointWires (castReg h₂ ra) := by
  subst b
  subst d
  simpa only [castReg_rfl] using hd

/-- The frozen public benchmark on all disjoint placements has exact gate and spacetime counts. -/
theorem exactPublicK25 {n : ℕ} (rd : QRegister (2 * ArcsinPrec.k25.k) n)
    (ra : QRegister (arcsinAncillas .k25) n) (hd : rd.DisjointWires ra) :
    (arcsinProgram .k25 rd ra).count PrimitiveGate.T = 3662 ∧
      (arcsinProgram .k25 rd ra).count PrimitiveGate.TOFF = 0 ∧
      arcsinSpacetime .k25 rd ra = 366200 := by
  classical
  have hb : isBenchRegime ArcsinPrec.k25.k ArcsinPrec.k25.eps := ⟨rfl, le_rfl⟩
  have ha : arcsinAncillas .k25 = 50 := ite_eq_left hb
  have hdata : 2 * ArcsinPrec.k25.k = 50 := rfl
  have hp : arcsinProgram .k25 rd ra =
      k25DynCircuit Arcsin.Var.v (castReg hdata rd) (castReg ha ra) := dite_eq_left hb
  have ht : (arcsinProgram .k25 rd ra).count PrimitiveGate.T = 3662 := by
    rw [hp]
    exact count_T_k25DynCircuit_eq _ _ _ (disjointCast hdata ha rd ra hd)
  refine ⟨ht, ?_, ?_⟩
  · rw [hp]
    exact count_TOFF_k25DynCircuit _ _ _
  · change (arcsinProgram .k25 rd ra).count PrimitiveGate.T *
        (2 * ArcsinPrec.k25.k + arcsinAncillas .k25) = 366200
    rw [ht, hdata, ha]

#print axioms exactPublicK25

end QuantumComputation.Specs.ArcsinImpl.ExactAudit
