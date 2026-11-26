/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module
public import Track2Grover.Engine.StageLoop
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.List.GetD

/-!
# Oracle Deflation Functor, Symbolic Bit Dispatcher, and Clean-State Readout
Provides three modular building blocks on `findAllQubits n m k` (reusing 100% of `StageLoop`):
1. `deflateCirc n m T c`: replaces every `.oracle reg` with `.oracle reg` followed by the
zero-cost
   classical-`T` unmarking unitary `phaseI (reg.embedUnitary (parallelMarkingOracle m T))`.
   For any
   `T ⊆ S`, compiling `deflateCirc n m T c` against `parallelMarkingOracle m S` has the
   **exact**
   same `QMonad` denotational semantics (`interp`) and expected oracle cost (`expectedCost`)
   as
   compiling `c` against `parallelMarkingOracle m (S \ T)`.
2. `dispBits res W off f`: symbolic `O(1)`-AST binary `.qIf` tree dispatching on `W` bits of
   `(σ res).toNat` starting at bit `off`, with exact `wp` and `expectedCost` decomposition.
3. `writeFinsetCircuit res n m k T`: prepares the computational basis state encoding `T` in
   `memAllReg n m k` from `|0⟩` at zero oracle cost and measures `memAllReg n m k` into `res`.
-/

section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

section
open Operator
open scoped InnerProductSpace
private theorem qcExpectEqTsumStore {Var : Type} {d : ℕ}
    (Δ : CQState (Store Var) d) (θ : CQAssertion (Store Var) d) :
    expect Δ θ = ∑' σ : Store Var, ⟪(θ σ).1, (Δ.1 σ).1⟫_ℝ :=
  rfl
private theorem qcTraceEqTsumStore {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) :
    (Δ.trace : ℝ) = ∑' σ : Store Var, (Δ.1 σ).1.trace :=
  CQState.coe_trace_eq_tsum Δ
private theorem qcSummableExpectStore {Var : Type} {d : ℕ}
    (Δ : CQState (Store Var) d) (θ : CQAssertion (Store Var) d) :
    Summable (fun σ : Store Var ↦ ⟪(θ σ).1, (Δ.1 σ).1⟫_ℝ) :=
  summable_expect Δ θ
end

@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal ENNReal InnerProductSpace QHLExpectation
/-! ## 1. Subset deflation of `setMarkingOracle` and `parallelMarkingOracle` -/
theorem slotMarkPerm_mul_of_subset {n : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) :
    slotMarkPerm T * slotMarkPerm S = slotMarkPerm (S \ T) := by
  ext u : 1
  obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  have hstep (A : Finset (Fin (2 ^ n))) (b' : Fin (2 ^ 1)) :
      slotMarkPerm A ((splitBasisEquiv n 1).symm (x, b')) =
        (splitBasisEquiv n 1).symm (x, b' + if x ∈ A then 1 else 0) := by
    simp [slotMarkPerm, tableAddPerm, addRightShear]
  rw [Equiv.Perm.mul_apply, hstep S b, hstep T _, hstep (S \ T) b]
  congr 1
  ext
  · rfl
  · simp only [Finset.mem_sdiff]
    by_cases hxT : x ∈ T
    · have hxS : x ∈ S := hTS hxT
      simp only [hxT, hxS, not_true_eq_false, and_false, ↓reduceIte, add_zero]
      fin_cases b <;> rfl
    · by_cases hxS : x ∈ S <;> simp [hxT, hxS]
theorem setMarkingOracle_mul_of_subset {n : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) :
    setMarkingOracle T * setMarkingOracle S = setMarkingOracle (S \ T) := by
  rw [setMarkingOracle, setMarkingOracle, setMarkingOracle, permutationUnitary_mul,
    slotMarkPerm_mul_of_subset hTS]
theorem parallelMarkingOracle_mul_of_subset {n m : ℕ} {S T : Finset (Fin (2 ^ n))}
    (hTS : T ⊆ S) :
    parallelMarkingOracle m T * parallelMarkingOracle m S =
      parallelMarkingOracle m (S \ T) := by
  change parallelSlotProd m (setMarkingOracle T) * parallelSlotProd m (setMarkingOracle S) =
    parallelSlotProd m (setMarkingOracle (S \ T))
  rw [parallelSlotProd_mul, setMarkingOracle_mul_of_subset hTS]
/-! ## 2. `QMonad` identity for `qAssign U;; qAssign (phaseI V)` and `deflateCirc` -/
theorem qMonad_ext {Var : Type} {d : ℕ} {x y : QMonad.Q (Store Var) d Unit}
    (h : ∀ Δ : CQState (Store Var) d, x.toStateFun Δ = y.toStateFun Δ) : x = y := by
  apply Subtype.ext
  funext Δ
  exact Prod.ext (Subsingleton.elim _ _) (h Δ)
theorem cqState_qAssign_phaseI {Var : Type} {d : ℕ} (U : Unitary d) (Δ : CQState (Store Var) d) :
    CQState.qAssign (phaseI U) Δ = CQState.qAssign U Δ := by
  apply Subtype.ext
  funext σ
  apply Subtype.ext
  ext1
  change ((Δ.1 σ).1.conj (phaseI U).1).mat = ((Δ.1 σ).1.conj U.1).mat
  rw [phaseI_conj]
theorem cqState_qAssign_comp {Var : Type} {d : ℕ} (U V : Unitary d) (Δ : CQState (Store Var) d) :
    CQState.qAssign V (CQState.qAssign U Δ) = CQState.qAssign (V * U) Δ := by
  apply Subtype.ext
  funext σ
  apply Subtype.ext
  ext1
  change (((Δ.1 σ).1.conj U.1).conj V.1).mat = ((Δ.1 σ).1.conj (V * U).1).mat
  simp only [HermitianMat.conj_apply_mat, Submonoid.coe_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
theorem interp_qAssign_seq_phaseI {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (U V : Unitary d) :
    interp (QProg.qAssign U ;; QProg.qAssign (phaseI V) : QProg Var d) =
      interp (QProg.qAssign (V * U) : QProg Var d) := by
  apply qMonad_ext
  intro Δ
  rw [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qAssign, interp_qAssign, interp_qAssign]
  change CQState.qAssign (phaseI V) (CQState.qAssign U Δ) = CQState.qAssign (V * U) Δ
  rw [cqState_qAssign_phaseI, cqState_qAssign_comp]
/-- Syntactic predicate that every `.step U` in `c` has zero cost under
  `CostModel.ofEmbeddedOracle`
  for every real oracle matrix (in particular, all `phaseI`-wrapped real unitaries). -/
def ZeroStepCost {Var : Type} {Q w : ℕ} :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w → Prop
  | .skip => True
  | .step U =>
      ∀ ⦃oracle : Unitary (2 ^ w)⦄, IsRealMatrix oracle.1 →
        (CostModel.ofEmbeddedOracle (n := Q) oracle).unitaryCost U = 0
  | .oracle _ => True
  | .measure _ _ => True
  | .seq c₁ c₂ => ZeroStepCost c₁ ∧ ZeroStepCost c₂
  | @OracleDynamicCircuit.qIf _ _ _ _ _ _ c₁ c₂ => ZeroStepCost c₁ ∧ ZeroStepCost c₂
  | @OracleDynamicCircuit.qWhile _ _ _ _ _ _ b => ZeroStepCost b
theorem zeroStepCost_step_phaseI {Var : Type} {Q w : ℕ} {U : Unitary (2 ^ Q)}
    (hU : IsRealMatrix U.1) :
    ZeroStepCost (.step (phaseI U) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) := by
  intro oracle horacle
  exact ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle hU
theorem zeroStepCost_sequence {Var : Type} {Q w : ℕ}
    (cs : List (OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w))
    (hcs : ∀ c ∈ cs, ZeroStepCost c) :
    ZeroStepCost (OracleDynamicCircuit.sequence cs) := by
  induction cs with
  | nil => simp [OracleDynamicCircuit.sequence, ZeroStepCost]
  | cons c cs ih =>
      simp only [OracleDynamicCircuit.sequence_cons, ZeroStepCost]
      exact ⟨hcs c List.mem_cons_self, ih fun c' hc' ↦ hcs c' (List.mem_cons_of_mem c hc')⟩
theorem zeroStepCost_xorRegCircuit {Var : Type} {W Q w : ℕ}
    (res : Var) (extractMask : ℤ → ℕ) (r : QRegister W Q) :
    ZeroStepCost (xorRegCircuit (oracleWidth := w) res extractMask r) := by
  refine zeroStepCost_sequence _ ?_
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨_, _, rfl⟩ := hc
  exact ⟨zeroStepCost_step_phaseI (isRealMatrix_permutationUnitary _), trivial⟩
theorem zeroStepCost_resetRegCircuit {Var : Type} {W Q w : ℕ}
    (res : Var) (r : QRegister W Q) :
    ZeroStepCost (resetRegCircuit (oracleWidth := w) res r) :=
  ⟨trivial, zeroStepCost_xorRegCircuit res Int.toNat r⟩
/-- Functorial circuit deflation: follows every `.oracle reg` with zero-cost unmarking of
  `T`. -/
noncomputable def deflateCirc {Var : Type} {Q : ℕ} (n m : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | .skip => .skip
  | .step U => .step U
  | .oracle reg =>
      .seq (.oracle reg) (.step (phaseI (reg.embedUnitary (parallelMarkingOracle m T))))
  | .measure v reg => .measure v reg
  | .seq c₁ c₂ => .seq (deflateCirc n m T c₁) (deflateCirc n m T c₂)
  | @OracleDynamicCircuit.qIf _ _ _ _ b inst c₁ c₂ =>
      @OracleDynamicCircuit.qIf _ _ _ _ b inst (deflateCirc n m T c₁) (deflateCirc n m T c₂)
  | @OracleDynamicCircuit.qWhile _ _ _ _ b inst c =>
      @OracleDynamicCircuit.qWhile _ _ _ _ b inst (deflateCirc n m T c)
theorem zeroStepCost_deflateCirc {Var : Type} {Q : ℕ} (n m : ℕ) (T : Finset (Fin (2 ^ n)))
    {c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)} (hc : ZeroStepCost c) :
    ZeroStepCost (deflateCirc n m T c) := by
  induction c with
  | «skip» => trivial
  | «step» _ => exact hc
  | «oracle» reg =>
      exact ⟨trivial,
        zeroStepCost_step_phaseI (isRealMatrix_embedMatrix reg
          (isRealMatrix_parallelMarkingOracle T))⟩
  | «measure» _ _ => trivial
  | «seq» _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | «qIf» _ _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | «qWhile» _ _ ih => exact ih hc
theorem interp_deflateCirc {Var : Type} [DecidableEq Var] {Q : ℕ}
    (n m : ℕ) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) :
    interp ((deflateCirc n m T c).compile QProg.qAssign (parallelMarkingOracle m S)) =
      interp (c.compile QProg.qAssign (parallelMarkingOracle m (S \ T))) := by
  induction c with
  | «skip» =>
      simp only [deflateCirc, OracleDynamicCircuit.compile_skip]
  | «step» _ =>
      simp only [deflateCirc, OracleDynamicCircuit.compile_step]
  | «oracle» reg =>
      simp only [deflateCirc, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step]
      rw [interp_qAssign_seq_phaseI, ← reg.embedUnitary_mul,
        parallelMarkingOracle_mul_of_subset hTS]
  | «measure» _ _ =>
      simp only [deflateCirc, OracleDynamicCircuit.compile_measure]
  | «seq» _ _ ih₁ ih₂ =>
      simp only [deflateCirc, OracleDynamicCircuit.compile_seq, interp_qSeq, ih₁, ih₂]
  | «qIf» _ _ _ ih₁ ih₂ =>
      simp only [deflateCirc, OracleDynamicCircuit.compile_qIf, interp_qIf, ih₁, ih₂]
  | «qWhile» _ _ ih =>
      simp only [deflateCirc, OracleDynamicCircuit.compile_qWhile, interp_qWhile, ih]
theorem expectedCost_deflateCirc {Var : Type} [DecidableEq Var] {Q : ℕ}
    (n m : ℕ) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S)
    {c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)} (hc : ZeroStepCost c) :
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
        ((deflateCirc n m T c).compile QProg.qAssign (parallelMarkingOracle m S)) =
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m (S \ T)))
        (c.compile QProg.qAssign (parallelMarkingOracle m (S \ T))) := by
  induction c with
  | «skip» =>
      funext Δ
      simp [deflateCirc]
  | «step» _ =>
      funext Δ
      simp only [deflateCirc, OracleDynamicCircuit.compile_step, expectedCost_qAssign]
      rw [hc (isRealMatrix_parallelMarkingOracle S),
        hc (isRealMatrix_parallelMarkingOracle (S \ T))]
  | «oracle» reg =>
      funext Δ
      simp only [deflateCirc, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step,
        expectedCost_qSeq, expectedCost_qAssign]
      have h1 : (CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m S)).unitaryCost
          (reg.embedUnitary (parallelMarkingOracle m S)) = 1 := by
        have hex : ∃ r : QRegister ((n + 1) * m) Q,
            reg.embedUnitary (parallelMarkingOracle m S) =
              r.embedUnitary (parallelMarkingOracle m S) := ⟨reg, rfl⟩
        simp [CostModel.ofEmbeddedOracle, hex]
      have h2 : (CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m (S \ T))).unitaryCost
          (reg.embedUnitary (parallelMarkingOracle m (S \ T))) = 1 := by
        have hex : ∃ r : QRegister ((n + 1) * m) Q,
            reg.embedUnitary (parallelMarkingOracle m (S \ T)) =
              r.embedUnitary (parallelMarkingOracle m (S \ T)) := ⟨reg, rfl⟩
        simp [CostModel.ofEmbeddedOracle, hex]
      have h0 : (CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m S)).unitaryCost
          (phaseI (reg.embedUnitary (parallelMarkingOracle m T))) = 0 :=
        ofEmbeddedOracle_unitaryCost_phaseI_eq_zero
          (isRealMatrix_parallelMarkingOracle S)
          (isRealMatrix_embedMatrix reg (isRealMatrix_parallelMarkingOracle T))
      rw [h1, h2, h0]
      simp
  | «measure» _ _ =>
      funext Δ
      simp only [deflateCirc, OracleDynamicCircuit.compile_measure, QProg.measureRegister,
        expectedCost_qMeasure, CostModel.ofEmbeddedOracle]
  | «seq» c₁ _ ih₁ ih₂ =>
      funext Δ
      simp only [deflateCirc, OracleDynamicCircuit.compile_seq, expectedCost_qSeq,
        ih₁ hc.1, ih₂ hc.2, interp_deflateCirc n m hTS c₁]
  | «qIf» _ _ _ ih₁ ih₂ =>
      funext Δ
      simp only [deflateCirc, OracleDynamicCircuit.compile_qIf, cqExpectedCostIf,
        ih₁ hc.1, ih₂ hc.2]
  | «qWhile» _ c ih =>
      funext Δ
      simp only [deflateCirc, OracleDynamicCircuit.compile_qWhile, expectedCost_qWhile,
        ih hc, interp_deflateCirc n m hTS c]
/-! ## 3. Symbolic `O(1)`-AST binary bit dispatcher `dispBits` -/
/-- Branch on bits `off.. off + W - 1` of `(σ res).toNat` and pass the decoded `W`-bit
  natural
  number `v < 2 ^ W` to `f v`. Has `O(1)` Lean AST size for symbolic `W`. -/
noncomputable def dispBits {Var : Type} {Q w : ℕ} (res : Var) :
    ℕ → ℕ → (ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w
  | 0, _, f => f 0
  | W + 1, off, f =>
      .qIf (fun σ ↦ (σ res).toNat.testBit off = true)
        (dispBits res W (off + 1) fun v ↦ f (2 * v + 1))
        (dispBits res W (off + 1) fun v ↦ f (2 * v))
theorem zeroStepCost_dispBits {Var : Type} {Q w : ℕ} (res : Var) (W off : ℕ)
    (f : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    (hf : ∀ v < 2 ^ W, ZeroStepCost (f v)) :
    ZeroStepCost (dispBits res W off f) := by
  induction W generalizing off f with
  | zero => exact hf 0 (by norm_num)
  | succ W ih =>
      simp only [dispBits, ZeroStepCost]
      refine ⟨ih (off + 1) _ fun v hv ↦ hf (2 * v + 1) ?_,
        ih (off + 1) _ fun v hv ↦ hf (2 * v) ?_⟩ <;>
      · rw [pow_succ']
        omega
theorem div_pow_succ_mod_two_mul_add {x off W : ℕ} :
    2 * ((x / 2 ^ (off + 1)) % 2 ^ W) + (x / 2 ^ off) % 2 = (x / 2 ^ off) % 2 ^ (W + 1) := by
  have hdiv : x / 2 ^ (off + 1) = (x / 2 ^ off) / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv, pow_succ']
  set y := x / 2 ^ off
  have h1 : y = 2 * (y / 2) + y % 2 := (Nat.div_add_mod y 2).symm
  have h2 : y / 2 = 2 ^ W * ((y / 2) / 2 ^ W) + (y / 2) % 2 ^ W :=
    (Nat.div_add_mod (y / 2) (2 ^ W)).symm
  have hlt : 2 * ((y / 2) % 2 ^ W) + y % 2 < 2 * 2 ^ W := by
    have hm1 : (y / 2) % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by positivity)
    have hm2 : y % 2 < 2 := Nat.mod_lt _ (by positivity)
    omega
  have hy : y = (2 * 2 ^ W) * ((y / 2) / 2 ^ W) + (2 * ((y / 2) % 2 ^ W) + y % 2) := by
    linear_combination h1 + 2 * h2
  conv_rhs => rw [hy]
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]
theorem wp_dispBits {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var)
    (oracle : Unitary (2 ^ w)) (W off : ℕ)
    (f : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    wp ((dispBits res W off f).compile QProg.qAssign oracle) Θ σ =
      wp ((f (((σ res).toNat / 2 ^ off) % 2 ^ W)).compile QProg.qAssign oracle) Θ σ := by
  induction W generalizing off f with
  | zero =>
      simp only [dispBits, pow_zero, Nat.mod_one]
  | succ W ih =>
      simp only [dispBits, OracleDynamicCircuit.compile_qIf, wp_qIf]
      have hbit := Nat.testBit_eq_decide_div_mod_eq (x := (σ res).toNat) (i := off)
      cases hb : (σ res).toNat.testBit off
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
        have hm0 : ((σ res).toNat / 2 ^ off) % 2 = 0 := by
          rw [hbit, decide_eq_false_iff_not] at hb
          omega
        have heq : 2 * (((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W) =
            ((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) := by
          have h0 := div_pow_succ_mod_two_mul_add (x := (σ res).toNat) (off := off) (W := W)
          omega
        rw [heq]
      · simp only [↓reduceIte, ih]
        have hm1 : ((σ res).toNat / 2 ^ off) % 2 = 1 := by
          rw [hbit, decide_eq_true_iff] at hb
          exact hb
        have heq : 2 * (((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W) + 1 =
            ((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) := by
          have h0 := div_pow_succ_mod_two_mul_add (x := (σ res).toNat) (off := off) (W := W)
          omega
        rw [heq]
/-- Store-sliced `CQState` keeping only stores with `((σ res).toNat / 2 ^ off) % 2 ^ W = v`. -/
noncomputable def sliceState {Var : Type} {d : ℕ} (res : Var) (off W v : ℕ) (Δ : CQState (Store Var)
    d) :
    CQState (Store Var) d :=
  CQState.cqTrueSt (fun σ ↦ ((σ res).toNat / 2 ^ off) % 2 ^ W = v) Δ
theorem sliceState_zero {Var : Type} {d : ℕ} (res : Var) (off : ℕ) (Δ : CQState (Store Var) d) :
    sliceState res off 0 0 Δ = Δ := by
  apply Subtype.ext
  funext σ
  simp [sliceState, CQState.cqTrueSt, Nat.mod_one]
theorem sliceState_succ_odd {Var : Type} {d : ℕ} (res : Var) (off W v : ℕ)
    (Δ : CQState (Store Var) d) :
    sliceState res (off + 1) W v
        (CQState.cqTrueSt (fun σ ↦ (σ res).toNat.testBit off = true) Δ) =
      sliceState res off (W + 1) (2 * v + 1) Δ := by
  apply Subtype.ext
  funext σ
  change (if ((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W = v then
      if (σ res).toNat.testBit off = true then Δ.1 σ else 0 else 0) =
    if ((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v + 1 then Δ.1 σ else 0
  have hbit := Nat.testBit_eq_decide_div_mod_eq (x := (σ res).toNat) (i := off)
  have hmod := div_pow_succ_mod_two_mul_add (x := (σ res).toNat) (off := off) (W := W)
  cases hb : (σ res).toNat.testBit off
  · have hm0 : ((σ res).toNat / 2 ^ off) % 2 = 0 := by
      rw [hbit, decide_eq_false_iff_not] at hb; omega
    have hnv : ¬ (((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v + 1) := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, ite_self, hnv]
  · have hm1 : ((σ res).toNat / 2 ^ off) % 2 = 1 := by
      rw [hbit, decide_eq_true_iff] at hb; exact hb
    have hiff : (((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W = v) ↔
        (((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v + 1) := by
      omega
    by_cases hv : ((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W = v
    · have hv' : ((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v + 1 := hiff.1 hv
      simp only [hv, hv', ↓reduceIte]
    · have hnv : ¬ (((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v + 1) :=
        fun h ↦ hv (hiff.2 h)
      simp only [hv, hnv, ↓reduceIte]
theorem sliceState_succ_even {Var : Type} {d : ℕ} (res : Var) (off W v : ℕ)
    (Δ : CQState (Store Var) d) :
    sliceState res (off + 1) W v
        (CQState.cqFalseSt (fun σ ↦ (σ res).toNat.testBit off = true) Δ) =
      sliceState res off (W + 1) (2 * v) Δ := by
  apply Subtype.ext
  funext σ
  change (if ((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W = v then
      if (σ res).toNat.testBit off = true then 0 else Δ.1 σ else 0) =
    if ((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v then Δ.1 σ else 0
  have hbit := Nat.testBit_eq_decide_div_mod_eq (x := (σ res).toNat) (i := off)
  have hmod := div_pow_succ_mod_two_mul_add (x := (σ res).toNat) (off := off) (W := W)
  cases hb : (σ res).toNat.testBit off
  · have hm0 : ((σ res).toNat / 2 ^ off) % 2 = 0 := by
      rw [hbit, decide_eq_false_iff_not] at hb; omega
    have hiff : (((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W = v) ↔
        (((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v) := by
      omega
    by_cases hv : ((σ res).toNat / 2 ^ (off + 1)) % 2 ^ W = v
    · have hv' : ((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v := hiff.1 hv
      simp only [hv, Bool.false_eq_true, hv', ↓reduceIte]
    · have hnv : ¬ (((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v) :=
        fun h ↦ hv (hiff.2 h)
      simp only [hv, hnv, ↓reduceIte]
  · have hm1 : ((σ res).toNat / 2 ^ off) % 2 = 1 := by
      rw [hbit, decide_eq_true_iff] at hb; exact hb
    have hnv : ¬ (((σ res).toNat / 2 ^ off) % 2 ^ (W + 1) = 2 * v) := by omega
    simp only [↓reduceIte, ite_self, hnv]
theorem sum_range_two_mul_even_odd {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    (∑ v ∈ Finset.range N, g (2 * v + 1)) + (∑ v ∈ Finset.range N, g (2 * v)) =
      ∑ u ∈ Finset.range (2 * N), g u := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
      calc (∑ x ∈ Finset.range N, g (2 * x + 1) + g (2 * N + 1)) +
            (∑ x ∈ Finset.range N, g (2 * x) + g (2 * N))
          = ((∑ x ∈ Finset.range N, g (2 * x + 1)) + (∑ x ∈ Finset.range N, g (2 * x))) +
              g (2 * N) + g (2 * N + 1) := by abel
        _ = (∑ u ∈ Finset.range (2 * N), g u) + g (2 * N) + g (2 * N + 1) := by rw [ih]
theorem expectedCost_dispBits {Var : Type} [DecidableEq Var] {Q w : ℕ}
    (model : CostModel (2 ^ Q)) (oracle : Unitary (2 ^ w)) (res : Var)
    (W off : ℕ) (f : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    (Δ : CQState (Store Var) (2 ^ Q)) :
    expectedCost model ((dispBits res W off f).compile QProg.qAssign oracle) Δ =
      ∑ v ∈ Finset.range (2 ^ W),
        expectedCost model ((f v).compile QProg.qAssign oracle) (sliceState res off W v Δ) := by
  induction W generalizing off f Δ with
  | zero =>
      simp [dispBits, sliceState_zero]
  | succ W ih =>
      simp only [dispBits, OracleDynamicCircuit.compile_qIf, cqExpectedCostIf, ih]
      simp_rw [sliceState_succ_odd, sliceState_succ_even]
      rw [pow_succ', ← sum_range_two_mul_even_odd (2 ^ W)
        (fun u ↦ expectedCost model ((f u).compile QProg.qAssign oracle)
          (sliceState res off (W + 1) u Δ))]
/-! ## 4. Clean-state `Finset` readout circuit `writeFinsetCircuit` -/
/-- Basis state in `Fin (2 ^ findAllQubits n m k)` writing the first `t` elements of `L`
  into
  `memSlotReg 0.. memSlotReg (t - 1)` starting from `z = 0`. -/
noncomputable def encodeListBasis (n m k : ℕ) (L : List (Fin (2 ^ n))) :
    ℕ → Fin (2 ^ findAllQubits n m k)
  | 0 => 0
  | t + 1 =>
      if h : t < k then
        (memSlotReg n m k ⟨t, h⟩).replaceIndex (encodeListBasis n m k L t) (L.getD t 0)
      else
        encodeListBasis n m k L t
theorem validStageBasis_encodeListBasis {n m k : ℕ} {S : Finset (Fin (2 ^ n))}
    {L : List (Fin (2 ^ n))} (hmem : ∀ x ∈ L, x ∈ S) (hnd : L.Nodup) (hlen : L.length = k) :
    ∀ t ≤ k,
      ValidStageBasis n m k S t (encodeListBasis n m k L t) ∧
        ∀ l : Fin k, l.val < t →
          (memSlotReg n m k l).extractIndex (encodeListBasis n m k L t) = L.getD l.val 0 := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨validStageBasis_zero n m k S, fun l hl ↦ by omega⟩
  | succ t ih =>
      intro htk
      have ht_lt : t < k := by omega
      obtain ⟨hvalid_t, hex_t⟩ := ih (by omega)
      simp only [encodeListBasis, ht_lt, ↓reduceDIte]
      let j : Fin k := ⟨t, ht_lt⟩
      have ht_len : t < L.length := by omega
      have hget_eq : L.getD t 0 = L[t] := List.getD_eq_getElem _ _ ht_len
      have hx_in_S : L.getD t 0 ∈ S := by
        rw [hget_eq]
        exact hmem _ (List.getElem_mem ht_len)
      have hx_not_mem : L.getD t 0 ∉ memFoundSet n m k (activeMemSlots k t)
          (encodeListBasis n m k L t) := by
        rw [memFoundSet, Finset.mem_image]
        rintro ⟨l, hl, heq⟩
        have hl_lt : l.val < t := mem_activeMemSlots.1 hl
        have hl_len : l.val < L.length := by omega
        rw [hex_t l hl_lt, List.getD_eq_getElem _ _ hl_len, hget_eq] at heq
        have hfin : (⟨l.val, hl_len⟩ : Fin L.length) = ⟨t, ht_len⟩ :=
          (List.nodup_iff_injective_getElem.1 hnd) heq
        have hidx_eq : l.val = t := congrArg Fin.val hfin
        omega
      have hvalid_succ : ValidStageBasis n m k S (t + 1)
          ((memSlotReg n m k j).replaceIndex (encodeListBasis n m k L t) (L.getD t 0)) :=
        validStageBasis_write_succ j hvalid_t (Finset.mem_sdiff.2 ⟨hx_in_S, hx_not_mem⟩)
      refine ⟨hvalid_succ, ?_⟩
      intro l hl
      by_cases hlj : l = j
      · subst l
        rw [QRegister.extractIndex_replaceIndex]
      · have hl_lt : l.val < t := by
          have hne : l.val ≠ t := fun h ↦ hlj (Fin.ext h)
          omega
        rw [(memSlotReg n m k l).extractIndex_replaceIndex_of_disjoint _
          (memSlotReg_disjoint hlj)]
        exact hex_t l hl_lt
/-- Noncomputable target basis state encoding `T: Finset (Fin (2 ^ n))` in `memAllReg`. -/
noncomputable def encodeFinsetBasis (n m k : ℕ) (T : Finset (Fin (2 ^ n))) :
    Fin (2 ^ findAllQubits n m k) :=
  encodeListBasis n m k T.toList k
theorem validStageBasis_encodeFinsetBasis {n m k : ℕ} {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) :
    ValidStageBasis n m k S k (encodeFinsetBasis n m k S) := by
  have hmem : ∀ x ∈ S.toList, x ∈ S := fun x hx ↦ Finset.mem_toList.1 hx
  have hnd : S.toList.Nodup := Finset.nodup_toList S
  have hlen : S.toList.length = k := by rw [Finset.length_toList, hScard]
  exact (validStageBasis_encodeListBasis hmem hnd hlen k le_rfl).1
/-- Zero-oracle-cost readout circuit from clean `|0⟩` for an already-determined `Finset`
  `T`. -/
noncomputable def writeFinsetCircuit {Var : Type} (res : Var) (n m k : ℕ)
    (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (.step (phaseI (permutationUnitary (Equiv.swap 0 (encodeFinsetBasis n m k T)))))
    (.measure res (memAllReg n m k))
theorem zeroStepCost_writeFinsetCircuit {Var : Type} (res : Var) (n m k : ℕ)
    (T : Finset (Fin (2 ^ n))) :
    ZeroStepCost (writeFinsetCircuit res n m k T) :=
  ⟨zeroStepCost_step_phaseI (isRealMatrix_permutationUnitary _), trivial⟩
theorem expectedCost_writeFinsetCircuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ)
    (T : Finset (Fin (2 ^ n))) {oracle : Unitary (2 ^ ((n + 1) * m))}
    (horacle : IsRealMatrix oracle.1) (Δ : CQState (Store Var) (2 ^ findAllQubits n m k)) :
    expectedCost (CostModel.ofEmbeddedOracle oracle)
      ((writeFinsetCircuit res n m k T).compile QProg.qAssign oracle) Δ = 0 := by
  simp only [writeFinsetCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_measure,
    QProg.measureRegister, expectedCost_qSeq, expectedCost_qAssign, expectedCost_qMeasure]
  have h0 := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle
    (isRealMatrix_permutationUnitary (Equiv.swap 0 (encodeFinsetBasis n m k T)))
  rw [h0]
  simp [CostModel.ofEmbeddedOracle]
theorem diagProj_zero_wp_writeFinsetCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hScard : S.card = k)
    (oracle : Unitary (2 ^ ((n + 1) * m))) (σ : Store Var) :
    diagProj (· = (0 : Fin (2 ^ findAllQubits n m k))) *
        (wp ((writeFinsetCircuit res n m k S).compile QProg.qAssign oracle)
          (liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)) σ).1.mat *
        diagProj (· = (0 : Fin (2 ^ findAllQubits n m k))) =
      ((1 : ℝ) : ℂ) • diagProj (· = (0 : Fin (2 ^ findAllQubits n m k))) := by
  set zS := encodeFinsetBasis n m k S
  have hzS : ValidStageBasis n m k S k zS := validStageBasis_encodeFinsetBasis hScard
  have hread := congrFun (congrFun (diagProj_wp_finalReadout res hScard σ) zS) zS
  rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply, diagProj, Matrix.diagonal_apply] at hread
  simp only [hzS, and_self, ↓reduceIte, Complex.ofReal_one, smul_eq_mul, one_mul] at hread
  simp only [writeFinsetCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_measure,
    wp_qSeq, wp_qAssign, qAssign_phaseI]
  ext a b
  rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]
  by_cases hab0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab0
    simp only [and_self, ↓reduceIte, diagProj, Matrix.diagonal_apply, Complex.ofReal_one,
      smul_eq_mul, one_mul]
    rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
      conjTranspose_mul_mul_apply_single, permutationUnitary_mulVec_single,
      Equiv.swap_apply_left]
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, dotProduct, Pi.single_apply] using hread
  · simp only [hab0, ↓reduceIte, diagProj, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      have hne : a ≠ 0 := fun h ↦ hab0 ⟨h, h⟩
      simp [hne]
    · simp [hab]
/-! ## 4. Trace-zero, `sliceState` partition, and `Finset` sum helpers -/
theorem expect_eq_zero_of_trace_eq_zero {Var : Type} {d : ℕ}
    {Ξ : CQState (Store Var) d} (hΞ : Ξ.trace = 0) (Θ : CQAssertion (Store Var) d) :
    𝔼[Ξ, Θ] = 0 := by
  apply le_antisymm
  · calc 𝔼[Ξ, Θ] ≤ 𝔼[Ξ, ⊤] := expect_mono le_rfl le_top
      _ = Ξ.trace := expect_top Ξ
      _ = 0 := by simp [hΞ]
  · rw [qcExpectEqTsumStore]
    exact tsum_nonneg fun σ ↦ expect_term_nonneg Ξ Θ σ
theorem trueState_trace_le {Var : Type} {d : ℕ} (b : Store Var → Prop) [DecidablePred b]
    (Ξ : CQState (Store Var) d) :
    (CQState.cqTrueSt b Ξ).trace ≤ Ξ.trace := by
  rw [← NNReal.coe_le_coe, ← expect_top (CQState.cqTrueSt b Ξ), ← expect_top Ξ,
    qcExpectEqTsumStore, qcExpectEqTsumStore]
  refine Summable.tsum_le_tsum (fun σ ↦ ?_)
    (qcSummableExpectStore (CQState.cqTrueSt b Ξ) ⊤) (qcSummableExpectStore Ξ ⊤)
  have hnn : 0 ≤ (Ξ.1 σ).1.trace := by
    have h0 := expect_term_nonneg Ξ ⊤ σ
    change 0 ≤ ⟪(1 : HermitianMat (Fin d) ℂ), (Ξ.1 σ).1⟫_ℝ at h0
    rwa [HermitianMat.one_inner] at h0
  change ⟪(1 : HermitianMat (Fin d) ℂ), ((CQState.cqTrueSt b Ξ).1 σ).1⟫_ℝ ≤
    ⟪(1 : HermitianMat (Fin d) ℂ), (Ξ.1 σ).1⟫_ℝ
  rw [HermitianMat.one_inner, HermitianMat.one_inner]
  change (if b σ then Ξ.1 σ else 0).1.trace ≤ (Ξ.1 σ).1.trace
  by_cases hb : b σ
  · simp [hb]
  · simp [hb, hnn]
theorem falseState_trace_le {Var : Type} {d : ℕ} (b : Store Var → Prop) [DecidablePred b]
    (Ξ : CQState (Store Var) d) :
    (CQState.cqFalseSt b Ξ).trace ≤ Ξ.trace := by
  rw [← NNReal.coe_le_coe, ← expect_top (CQState.cqFalseSt b Ξ), ← expect_top Ξ,
    qcExpectEqTsumStore, qcExpectEqTsumStore]
  refine Summable.tsum_le_tsum (fun σ ↦ ?_)
    (qcSummableExpectStore (CQState.cqFalseSt b Ξ) ⊤) (qcSummableExpectStore Ξ ⊤)
  have hnn : 0 ≤ (Ξ.1 σ).1.trace := by
    have h0 := expect_term_nonneg Ξ ⊤ σ
    change 0 ≤ ⟪(1 : HermitianMat (Fin d) ℂ), (Ξ.1 σ).1⟫_ℝ at h0
    rwa [HermitianMat.one_inner] at h0
  change ⟪(1 : HermitianMat (Fin d) ℂ), ((CQState.cqFalseSt b Ξ).1 σ).1⟫_ℝ ≤
    ⟪(1 : HermitianMat (Fin d) ℂ), (Ξ.1 σ).1⟫_ℝ
  rw [HermitianMat.one_inner, HermitianMat.one_inner]
  change (if b σ then 0 else Ξ.1 σ).1.trace ≤ (Ξ.1 σ).1.trace
  by_cases hb : b σ
  · simp [hb, hnn]
  · simp [hb]
theorem expectedCost_eq_zero_of_trace_eq_zero {Var : Type} [DecidableEq Var] {Q w : ℕ}
    (model : CostModel (2 ^ Q)) (oracle : Unitary (2 ^ w))
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    {Ξ : CQState (Store Var) (2 ^ Q)} (hΞ : Ξ.trace = 0) :
    expectedCost model (c.compile QProg.qAssign oracle) Ξ = 0 := by
  have hmass : ∀ {Υ : CQState (Store Var) (2 ^ Q)}, Υ.trace = 0 → stateMass Υ = 0 := by
    intro Υ hΥ
    simp [stateMass, hΥ]
  have hto : ∀ (p : QProg Var (2 ^ Q)) {Υ : CQState (Store Var) (2 ^ Q)},
      Υ.trace = 0 → ((interp p).toStateFun Υ).trace = 0 := by
    intro p Υ hΥ
    exact le_antisymm (((interp p).trace_toStateFun_le Υ).trans_eq hΥ) zero_le
  induction c generalizing Ξ with
  | «skip» => simp
  | «step» _ =>
      simp only [OracleDynamicCircuit.compile_step, expectedCost_qAssign, hmass hΞ, zero_mul]
  | «oracle» _ =>
      simp only [OracleDynamicCircuit.compile_oracle, expectedCost_qAssign, hmass hΞ, zero_mul]
  | «measure» _ _ =>
      simp only [OracleDynamicCircuit.compile_measure, QProg.measureRegister,
        expectedCost_qMeasure, hmass hΞ, zero_mul]
  | «seq» c₁ _ ih₁ ih₂ =>
      simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
      rw [ih₁ hΞ, ih₂ (hto _ hΞ), add_zero]
  | «qIf» b _ _ ih₁ ih₂ =>
      simp only [OracleDynamicCircuit.compile_qIf, cqExpectedCostIf]
      have ht : (CQState.cqTrueSt b Ξ).trace = 0 :=
        le_antisymm ((trueState_trace_le b Ξ).trans_eq hΞ) zero_le
      have hf : (CQState.cqFalseSt b Ξ).trace = 0 :=
        le_antisymm ((falseState_trace_le b Ξ).trans_eq hΞ) zero_le
      rw [ih₁ ht, ih₂ hf, add_zero]
  | «qWhile» b body ih =>
      simp only [OracleDynamicCircuit.compile_qWhile, expectedCost_qWhile]
      have hrec (t : ℕ) : ∀ {Υ : CQState (Store Var) (2 ^ Q)}, Υ.trace = 0 →
          whileRecCost (expectedCost model (body.compile QProg.qAssign oracle))
            (interp (body.compile QProg.qAssign oracle)).toStateFun b t Υ = 0 := by
        induction t with
        | zero => intro _ _; simp [whileRecCost]
        | succ t iht =>
            intro Υ hΥ
            have ht : (CQState.cqTrueSt b Υ).trace = 0 :=
              le_antisymm ((trueState_trace_le b Υ).trans_eq hΥ) zero_le
            simp only [cqWhileRecCostSuc, ih ht, iht (hto _ ht), add_zero]
      simp [hrec _ hΞ]
theorem sum_sliceState_expect {Var : Type} {d : ℕ} (res : Var) (W : ℕ)
    (Ξ : CQState (Store Var) d) (Φ : ℕ → CQAssertion (Store Var) d) :
    (∑ v ∈ Finset.range (2 ^ W), 𝔼[sliceState res 0 W v Ξ, Φ v]) =
      𝔼[Ξ, fun σ ↦ Φ ((σ res).toNat % 2 ^ W) σ] := by
  simp_rw [qcExpectEqTsumStore]
  rw [← Summable.tsum_finsetSum (fun v _ ↦ qcSummableExpectStore (sliceState res 0 W v Ξ) (Φ v))]
  refine tsum_congr fun σ ↦ ?_
  have hmem : (σ res).toNat % 2 ^ W ∈ Finset.range (2 ^ W) :=
    Finset.mem_range.2 (Nat.mod_lt _ (by positivity))
  rw [Finset.sum_eq_single ((σ res).toNat % 2 ^ W)]
  · change ⟪(Φ ((σ res).toNat % 2 ^ W) σ).1,
        (if ((σ res).toNat / 2 ^ 0) % 2 ^ W = (σ res).toNat % 2 ^ W then Ξ.1 σ else 0).1⟫_ℝ = _
    simp
  · intro v _ hne
    change ⟪(Φ v σ).1, (if ((σ res).toNat / 2 ^ 0) % 2 ^ W = v then Ξ.1 σ else 0).1⟫_ℝ = 0
    simp [Ne.symm hne]
  · intro habs; exact (habs hmem).elim
theorem sum_sliceState_trace {Var : Type} {d : ℕ} (res : Var) (W : ℕ) (Ξ : CQState (Store Var) d) :
    (∑ v ∈ Finset.range (2 ^ W), (sliceState res 0 W v Ξ).trace) = Ξ.trace := by
  rw [← NNReal.coe_inj, NNReal.coe_sum]
  simp_rw [← expect_top]
  exact sum_sliceState_expect res W Ξ (fun _ ↦ ⊤)
theorem expect_dispBits {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var)
    (oracle : Unitary (2 ^ w)) (W : ℕ)
    (f : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    (Ξ : CQState (Store Var) (2 ^ Q)) (Θ : CQAssertion (Store Var) (2 ^ Q)) :
    𝔼[(interp ((dispBits res W 0 f).compile QProg.qAssign oracle)).toStateFun Ξ, Θ] =
      ∑ v ∈ Finset.range (2 ^ W),
        𝔼[(interp ((f v).compile QProg.qAssign oracle)).toStateFun
          (sliceState res 0 W v Ξ), Θ] := by
  simp_rw [← wp_expectation_eq]
  rw [sum_sliceState_expect]
  congr 1
  funext σ
  have hwp := wp_dispBits res oracle W 0 f Θ σ
  simpa using hwp
theorem eq_of_le_of_finset_sum_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (hle : ∀ i ∈ s, a i ≤ b i) (hsum : ∑ i ∈ s, b i ≤ ∑ i ∈ s, a i) :
    ∀ i ∈ s, a i = b i := by
  intro i hi
  by_contra hne
  have hlt : a i < b i := lt_of_le_of_ne (hle i hi) hne
  have hstrict : ∑ j ∈ s, a j < ∑ j ∈ s, b j :=
    Finset.sum_lt_sum hle ⟨i, hi, hlt⟩
  linarith
end QuantumComputation.Specs.GroverFindAll
