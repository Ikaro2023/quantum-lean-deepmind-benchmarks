import QuantumComputationSpecs.Algorithms.Grover

/-! Expected number of explicit oracle calls in the frozen oracle circuit syntax. -/
namespace Track2Grover.Lower
open Operator ResourceCounting QProg
open scoped ENNReal

variable {w h : ℕ} {Var : Type} [DecidableEq Var]
abbrev OracleCircuit (Var : Type) (w h : ℕ) :=
  OracleDynamicCircuit (Unitary (2^w)) Var w h

/-- Only the oracle syntax node costs a query. Restriction, composition and loop
unrolling use the denotation of the frozen compiled circuit on the supplied oracle. -/
noncomputable def syntacticCost (O : Unitary (2^h)) :
    OracleCircuit Var w h → CQState (Store Var) (2^w) → ℝ≥0∞
  | .skip, _ | .step _, _ | .measure _ _, _ => 0
  | .oracle _, Δ => Δ.trace
  | .seq C D, Δ => syntacticCost O C Δ +
    syntacticCost O D ((interp (C.compile QProg.qAssign O)).toStateFun Δ)
  | @OracleDynamicCircuit.qIf _ _ _ _ guard _ C D, Δ => syntacticCost O C (Δ.restrict guard) +
    syntacticCost O D (Δ.restrict (fun σ => ¬guard σ))
  | @OracleDynamicCircuit.qWhile _ _ _ _ guard _ C, Δ => ⨆ t, whileRecCost (syntacticCost O C)
    ((interp (C.compile QProg.qAssign O)).toStateFun) guard t Δ

private theorem while_mono {State : Type*} {d : ℕ}
    (f g : CQState State d → ℝ≥0∞) (step : CQState State d → CQState State d)
    (guard : State → Prop) [DecidablePred guard] (hfg : ∀ Δ, f Δ ≤ g Δ) (t : ℕ)
    (Δ : CQState State d) : whileRecCost f step guard t Δ ≤ whileRecCost g step guard t Δ := by
  induction t generalizing Δ with
  | zero => rfl
  | succ t ih => exact add_le_add (hfg _) (ih _)

/-- Actual explicit-call cost is dominated for every circuit, register routing, input
state and oracle, including nested adaptive while loops. Free gates coinciding with an
oracle may incur an additional charge in the frozen model. -/
theorem syntacticCost_le_expected (O : Unitary (2^h)) (C : OracleCircuit Var w h)
    (Δ : CQState (Store Var) (2^w)) :
    syntacticCost O C Δ ≤ expectedCost (CostModel.ofEmbeddedOracle O) (C.compile QProg.qAssign O) Δ := by
  induction C generalizing Δ with
  | skip => rfl
  | step => apply zero_le
  | measure => apply zero_le
  | oracle =>
    simp [syntacticCost, CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary]
  | seq C D ihC ihD => exact add_le_add (ihC _) (ihD _)
  | qIf guard C D ihC ihD => exact add_le_add (ihC _) (ihD _)
  | qWhile guard C ih =>
    exact iSup_mono fun t => while_mono _ _ _ guard ih t Δ

#print axioms syntacticCost_le_expected
end Track2Grover.Lower
