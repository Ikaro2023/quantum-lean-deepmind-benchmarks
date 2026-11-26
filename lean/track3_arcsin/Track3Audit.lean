module

public import QuantumComputationDiscoveries.Primitives.Arcsin

public section

namespace Track3Audit
open QuantumComputation.Specs

theorem strictly_improved : arcsinK25ConstCost < 369800 := by decide +kernel

theorem k25_toff_free {n : ℕ} (rData : QRegister (2 * ArcsinPrec.k25.k) n)
    (rAnc : QRegister (arcsinAncillas ArcsinPrec.k25) n) :
    (arcsinProgram ArcsinPrec.k25 rData rAnc).count PrimitiveGate.TOFF = 0 :=
  (arcsin_k25_const_cost rData rAnc).1

#print axioms QuantumComputation.Specs.arcsin_correctness
#print axioms QuantumComputation.Specs.arcsin_k25_const_cost
#print axioms QuantumComputation.Specs.arcsinAncillas
#print axioms QuantumComputation.Specs.arcsinProgram
#print axioms QuantumComputation.Specs.arcsinK25ConstCost
#print axioms Track3Audit.strictly_improved
#print axioms Track3Audit.k25_toff_free
#reduce arcsinK25ConstCost

end Track3Audit
