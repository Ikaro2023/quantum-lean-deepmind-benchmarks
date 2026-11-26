import Track2Grover.LowerPath

/-! A finite list of ordinary bounded effects represents both terminal tests and
one unit of reward for each oracle visit. This avoids treating an unbounded cost
operator as a valid quantum observable. -/
namespace Track2Grover.Path
open Operator ResourceCounting FirstQuery
open scoped ENNReal
variable {V : Type} [DecidableEq V] {w h : ℕ}
abbrev Effects (V : Type) (w : ℕ) := List (CQAssertion (Store V) (2^w))

noncomputable def mask (g : Store V → Prop) [DecidablePred g]
    (θ : CQAssertion (Store V) (2^w)) : CQAssertion (Store V) (2^w) :=
  fun σ => if g σ then θ σ else ⊥

noncomputable def tests (ask : Bool) (O : Unitary (2^h)) : Finite V w h → Effects V w → Effects V w
  | .skip, X => X
  | .abort, _ => []
  | .step U, X => X.map (wp (.qAssign U))
  | .oracle r, X =>
    (if ask then [⊤] else []) ++ X.map (wp (.qAssign (r.embedUnitary O)))
  | .measure x r, X => X.map (wp (QProg.measureRegister x r))
  | .seq C D, X => tests ask O C (tests ask O D X)
  | @Finite.branch _ _ _ g _ C D, X =>
    (tests ask O C X).map (mask g) ++ (tests ask O D X).map (mask (fun σ => ¬g σ))

noncomputable def testMass (Δ : CQState (Store V) (2^w)) (X : Effects V w) : ℝ≥0∞ :=
  (X.map (mass Δ)).sum

private theorem map_wp_mass (p : QProg V (2^w)) (Δ : CQState (Store V) (2^w)) (X : Effects V w) :
    testMass Δ (X.map (wp p)) = testMass ((interp p).toStateFun Δ) X := by
  induction X with
  | nil => rfl
  | cons θ X ih =>
    change mass Δ (wp p θ) + testMass Δ (X.map (wp p)) =
      mass ((interp p).toStateFun Δ) θ + testMass ((interp p).toStateFun Δ) X
    rw [mass_wp, ih]

private theorem map_mask_mass (g : Store V → Prop) [DecidablePred g]
    (Δ : CQState (Store V) (2^w)) (X : Effects V w) :
    testMass Δ (X.map (mask g)) = testMass (Δ.restrict g) X := by
  induction X with
  | nil => rfl
  | cons θ X ih =>
    change mass Δ (mask g θ) + testMass Δ (X.map (mask g)) =
      mass (Δ.restrict g) θ + testMass (Δ.restrict g) X
    rw [ih]
    congr 1
    change mass Δ (fun σ => if g σ then θ σ else ⊥) = _
    simpa [mass] using mass_ite g Δ θ ⊥

omit [DecidableEq V] in
private theorem plus_mass {Δ Γ : CQState (Store V) (2^w)} (H : Δ.trace+Γ.trace ≤ 1)
    (X : Effects V w) : testMass (Δ.add Γ H) X = testMass Δ X + testMass Γ X := by
  induction X with
  | nil => simp [testMass]
  | cons θ X ih =>
    change mass (Δ.add Γ H) θ + testMass (Δ.add Γ H) X =
      (mass Δ θ + testMass Δ X) + (mass Γ θ + testMass Γ X)
    rw [ih, show mass (Δ.add Γ H) θ = mass Δ θ + mass Γ θ by
      simp [mass, ENNReal.ofReal_add (pos_expect ..) (pos_expect ..)]]
    ac_rfl

noncomputable def number (O : Unitary (2^h)) :
    Finite V w h → CQState (Store V) (2^w) → ℝ≥0∞
  | .skip, _ | .abort, _ | .measure _ _, _ | .step _, _ => 0
  | .oracle _, Δ => Δ.trace
  | .seq C D, Δ => number O C Δ + number O D ((interp (compile O C)).toStateFun Δ)
  | @Finite.branch _ _ _ g _ C D, Δ =>
    number O C (Δ.restrict g) + number O D (Δ.restrict (fun σ => ¬g σ))

theorem number_le_expected (O : Unitary (2^h)) (C : Finite V w h) (Δ : CQState (Store V) (2^w)) :
    number O C Δ ≤ expectedCost (CostModel.ofEmbeddedOracle O) (compile O C) Δ := by
  induction C generalizing Δ with
  | skip | abort | step | measure => exact zero_le
  | oracle r => simp [number,compile]
  | seq C D ihC ihD | branch _ C D ihC ihD => exact add_le_add (ihC _) (ihD _)

theorem tests_sound (ask : Bool) (O : Unitary (2^h)) (C : Finite V w h) (Δ : CQState (Store V) (2^w))
    (X : Effects V w) : testMass Δ (tests ask O C X) =
      (if ask then number O C Δ else 0) + testMass ((interp (compile O C)).toStateFun Δ) X := by
  induction C generalizing Δ X with
  | skip => cases ask <;> simp [tests,number,compile]
  | abort =>
    suffices ∀ X : Effects V w, testMass (0 : CQState (Store V) (2^w)) X = 0 by
      cases ask <;> change (0:ℝ≥0∞) = 0 + testMass 0 X <;> simp [this]
    intro X
    induction X with
    | nil => rfl
    | cons θ X ih =>
      change mass 0 θ + testMass 0 X = 0
      simp [mass, ih]
  | step U => cases ask <;> simp [tests,number,compile,map_wp_mass]
  | measure x r => cases ask <;> simp [tests,number,compile,map_wp_mass]
  | oracle r =>
    cases ask
    · simp [tests,compile,map_wp_mass]
    · change mass Δ ⊤ + testMass Δ (X.map (wp (.qAssign (r.embedUnitary O)))) =
        (Δ.trace:ℝ≥0∞) + _
      rw [map_wp_mass, show mass Δ ⊤ = Δ.trace by simp [mass, expect_top]]
      rfl
  | seq C D ihC ihD =>
    rw [tests, ihC, ihD]
    change _ = (if ask then number O C Δ + number O D _ else 0) + _
    cases ask <;> simp [compile, add_assoc]
  | branch g C D ihC ihD =>
    rw [tests, show ∀ (A B : Effects V w), testMass Δ (A++B) = testMass Δ A + testMass Δ B by
      simp [testMass]]
    rw [map_mask_mass, map_mask_mass, ihC, ihD]
    simp only [compile, interp_qIf, QMonad.Q.toStateFun_cqIf, plus_mass, number]
    cases ask <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] <;> ac_rfl

#print axioms number_le_expected
#print axioms tests_sound
end Track2Grover.Path
