import QuantumComputationSpecs.Algorithms.Grover

/-! Abort at the first oracle. The loss of any terminal effect is bounded by the frozen
expected query cost, including nested unbounded loops. The aborted program is common to
all possible oracles. -/
namespace Track2Grover.FirstQuery
open Operator ResourceCounting QProg Filter
open scoped ENNReal Topology

variable {V : Type} [DecidableEq V] {q h : ℕ}
abbrev Circ (V : Type) (q h : ℕ) := OracleDynamicCircuit (Unitary (2^q)) V q h

noncomputable def cut : Circ V q h → QProg V (2^q)
  | .skip => .skip
  | .step U => .qAssign U
  | .measure x r => QProg.measureRegister x r
  | .oracle _ => .abort
  | .seq C D => .qSeq (cut C) (cut D)
  | @OracleDynamicCircuit.qIf _ _ _ _ g _ C D => .qIf g (cut C) (cut D)
  | @OracleDynamicCircuit.qWhile _ _ _ _ g _ C => .qWhile g (cut C)

variable {d : ℕ} [NeZero d]
noncomputable def mass (Δ : CQState (Store V) d) (θ : CQAssertion (Store V) d) : ℝ≥0∞ :=
  ENNReal.ofReal (expect Δ θ)

omit [DecidableEq V] [NeZero d] in
theorem pos_expect (Δ : CQState (Store V) d) (θ : CQAssertion (Store V) d) :
    0 ≤ expect Δ θ := by
  simpa using (expect_mono (Δ₁ := Δ) (Δ₂ := Δ) le_rfl (bot_le : ⊥ ≤ θ))

theorem mass_wp (P : QProg V d) (Δ : CQState (Store V) d) (θ : CQAssertion (Store V) d) :
    mass Δ (wp P θ) = mass ((interp P).toStateFun Δ) θ := by simp [mass, expect_wp]

theorem mass_ite (g : Store V → Prop) [DecidablePred g] (Δ : CQState (Store V) d)
    (θ φ : CQAssertion (Store V) d) :
    mass Δ (fun s ↦ if g s then θ s else φ s) =
    mass (Δ.restrict g) θ + mass (Δ.restrict (¬g ·)) φ := by
  simp only [mass, expect_ite_partition, ENNReal.ofReal_add (pos_expect ..) (pos_expect ..)]

omit [DecidableEq V] [NeZero d] in
private theorem mass_top (Δ : CQState (Store V) d) (θ : CQAssertion (Store V) d) :
    mass Δ θ ≤ Δ.trace := by
  have h := expect_mono (Δ₁ := Δ) (Δ₂ := Δ) le_rfl (le_top : θ ≤ ⊤)
  simpa [mass, expect_top] using ENNReal.ofReal_le_ofReal h

private theorem while_cut (p b : QProg V d) (M : CostModel d)
    (g : Store V → Prop) [DecidablePred g]
    (body : ∀ Δ θ, mass Δ (wp p θ) ≤ mass Δ (wp b θ) + expectedCost M p Δ)
    (Δ : CQState (Store V) d) (θ : CQAssertion (Store V) d) :
    mass Δ (wp (.qWhile g p) θ) ≤ mass Δ (wp (.qWhile g b) θ) + expectedCost M (.qWhile g p) Δ := by
  have finite (t : ℕ) (δ : CQState (Store V) d) :
      mass δ (whileRecWP (wp p) g t θ) ≤ mass δ (whileRecWP (wp b) g t θ) +
        whileRecCost (expectedCost M p) (interp p).toStateFun g t δ := by
    induction t generalizing δ with
    | zero => simp [whileRecCost, whileRecWP]
    | succ t ih =>
      simp only [whileRecWP, mass_ite, whileRecCost_succ]
      have h := ih ((interp p).toStateFun (δ.restrict g))
      rw [← mass_wp, ← mass_wp] at h
      have h' := body (δ.restrict g) (whileRecWP (wp b) g t θ)
      calc
        _ ≤ (mass (δ.restrict g) (wp b (whileRecWP (wp b) g t θ)) +
              expectedCost M p (δ.restrict g) +
              whileRecCost (expectedCost M p) (interp p).toStateFun g t
                ((interp p).toStateFun (δ.restrict g))) + mass (δ.restrict (¬g ·)) θ :=
          add_le_add (h.trans (add_le_add h' le_rfl)) le_rfl
        _ = _ := by ac_rfl
  have limit := (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_expect_assertion_ωSup (whileRecWP.chain (wp p) (wp_mono p) g θ) Δ)
  rw [wp_qWhile]
  apply le_of_tendsto (show Tendsto (fun t ↦ mass Δ (whileRecWP (wp p) g t θ)) atTop _ from limit)
  apply Eventually.of_forall
  intro t
  rw [expectedCost_qWhile]
  apply (finite t Δ).trans (add_le_add _
    (le_iSup (fun i : ℕ ↦ whileRecCost (expectedCost M p) (interp p).toStateFun g i Δ) t))
  exact ENNReal.ofReal_le_ofReal (expect_mono le_rfl (whileRecWP_le_wp_qWhile g b t θ))

/-- A universal comparison on each actual oracle and input. -/
theorem cut_loss (O : Unitary (2^h)) (C : Circ V q h) (Δ : CQState (Store V) (2^q))
    (θ : CQAssertion (Store V) (2^q)) :
    mass Δ (wp (C.compile QProg.qAssign O) θ) ≤ mass Δ (wp (cut C) θ) +
    expectedCost (CostModel.ofEmbeddedOracle O) (C.compile QProg.qAssign O) Δ := by
  induction C generalizing Δ θ with
  | skip => simp [cut, OracleDynamicCircuit.compile]
  | step => exact le_self_add
  | measure => exact le_self_add
  | oracle r =>
    simp only [cut, OracleDynamicCircuit.compile, wp_abort, expectedCost_qAssign,
      CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, Nat.cast_one, mul_one]
    exact (mass_top _ _).trans (le_add_self)
  | seq C D ihC ihD =>
    simp only [cut, OracleDynamicCircuit.compile, wp_qSeq, expectedCost_qSeq]
    rw [mass_wp (C.compile _ _) Δ]
    have h := ihD ((interp (C.compile QProg.qAssign O)).toStateFun Δ) θ
    rw [← mass_wp (C.compile QProg.qAssign O) Δ (wp (cut D) θ)] at h
    exact h.trans <| by
      grw [ihC Δ (wp (cut D) θ)]
      rw [add_assoc]
  | qIf g C D ihC ihD =>
    simp only [cut, OracleDynamicCircuit.compile, wp_qIf, mass_ite, expectedCost_qIf]
    exact (add_le_add (ihC _ _) (ihD _ _)).trans_eq (by ac_rfl)
  | qWhile g C ih => exact while_cut _ _ _ g ih _ _

#print axioms cut_loss
end Track2Grover.FirstQuery
