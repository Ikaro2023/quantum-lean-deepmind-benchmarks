module
public import Track2Grover.FindAllEvaluator

namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol
@[expose] public section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

def weightedCost21 : Nat := 28787568698601335334

def success12 : Nat := 999995956520

def retryUpper15 : Nat := 28787685101031

def certifiedNumerator : Nat := 26768771052

theorem restartArithmetic : weightedCost21 * 1000000000000000 ≤ retryUpper15 * 1000000000 * success12 := by decide +kernel

theorem normalized : checkAltBound12 1024 512 retryUpper15 certifiedNumerator 1000000000000 = true := by decide +kernel

theorem meetsTarget : certifiedNumerator ≤ 26770000000 := by decide +kernel

#print axioms normalized

end
end Track2Weak.Cert
