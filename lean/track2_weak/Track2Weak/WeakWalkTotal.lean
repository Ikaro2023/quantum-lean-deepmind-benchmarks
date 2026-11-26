module
public import Track2Weak.WeakAttempt
import all Track2Weak.WeakWalkStages
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

/-! Finite physical trials terminate even when their final result requests a restart. -/
public section
namespace Track2Weak
open Operator ResourceCounting Matrix QuantumComputation.Specs.DickeSol
open QProg (qAssign)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem circuitLossless {Var : Type} [DecidableEq Var] {q O : ℕ}
    (oracle : Unitary (2^O)) (c : OracleCirc Var q O) {z : ℕ}
    (h : mkrStaticOracleCalls c = some z) : QProg.Lossless (c.compile qAssign oracle) := by
  induction c generalizing z with
  | «skip» => exact QProg.Lossless.skip
  | step U => exact QProg.Lossless.qAssign _
  | oracle reg => exact QProg.Lossless.qAssign _
  | measure a reg => exact QProg.Lossless.qMeasure a reg.computationalBasisMeasurement
  | qWhile => cases h
  | seq c₁ c₂ ih₁ ih₂ =>
    dsimp only [mkrStaticOracleCalls] at h
    cases h₁ : mkrStaticOracleCalls c₁ with
    | none => simp [h₁] at h
    | some n₁ =>
      cases h₂ : mkrStaticOracleCalls c₂ with
      | none => simp [h₁,h₂] at h
      | some n₂ => exact (ih₁ h₁).seq (ih₂ h₂)
  | qIf b c₁ c₂ ih₁ ih₂ =>
    dsimp only [mkrStaticOracleCalls] at h
    cases h₁ : mkrStaticOracleCalls c₁ with
    | none => simp [h₁] at h
    | some n₁ =>
      cases h₂ : mkrStaticOracleCalls c₂ with
      | none => simp [h₁,h₂] at h
      | some n₂ => exact QProg.Lossless.qIf b (ih₁ h₁) (ih₂ h₂)

private theorem static_lift {Var : Type} {q Q O : ℕ} (reg : QRegister q Q) (c : OracleCirc Var q O) :
    mkrStaticOracleCalls (mkrLiftCirc reg c) = mkrStaticOracleCalls c := by
  induction c <;> simp_all [mkrLiftCirc, mkrStaticOracleCalls]

theorem weakStages_lossless {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ} (hM : 1 ≤ 512*n)
    (S : Finset (Fin (2^n))) (finish : WeakCellCirc Var n)
    (hf : QProg.Lossless (finish.compile qAssign (groverParallelMarkingOracle 1024 S)))
    (rows : List WeakRow) :
    QProg.Lossless ((weakStages res n hM finish rows).compile qAssign (groverParallelMarkingOracle 1024 S)) := by
  induction rows with
  | nil => exact hf
  | cons row tail ih =>
    apply QProg.Lossless.seq
    · apply QProg.Lossless.seq
      · apply circuitLossless
        unfold weakSegment
        rw [static_lift, weak_ops_calls]
      · exact circuitLossless _ _ (z:=2) rfl
    · exact QProg.Lossless.qIf _ hf ih

theorem weakTrial_lossless {Var : Type} [DecidableEq Var] (res : Var) (qs : List Cert.Row)
    {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) :
    QProg.Lossless ((weakTrial res qs n).compile qAssign (groverParallelMarkingOracle 1024 S)) := by
  rw [weakTrial, dite_eq_left hn, OracleDynamicCircuit.compile_seq]
  apply QProg.Lossless.seq
  · apply circuitLossless (z:=0)
    unfold weakInitialize
    simp [mkrStaticOracleCalls, mkrStaticOracleCalls_mapAndMeasureLow]
  · apply weakStages_lossless
    exact circuitLossless _ _ (weakTerminalRead_queries res n 1024 512 (512*n) (weakRoom n))

end Track2Weak

#print axioms Track2Weak.weakTrial_lossless