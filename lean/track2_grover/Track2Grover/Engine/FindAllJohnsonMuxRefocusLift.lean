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
public import Track2Grover.Engine.FindAllJohnsonP01
/-!
# Subsystem Lifting & Multiplexed Kick Spec (`FindAllJohnsonMuxRefocusLift`)

Provides:
1. Elementary symmetric-subspace operations (`MuxSymOp`: walk segments `.walk K D` and exact
   prefix-intersection weight kicks `.prefixKick j0`), `symPrefixKickVec`, `evalMuxSymOps`,
   `muxOpsQueryCount`, and norm preservation (`sum_sq_evalMuxSymOps`).
2. `JohnsonMuxKickSpec m k L_max`: stage-adaptive `L_r`-block multiplexed renewal
specification
   supporting interspersed `2 * L_r`-query exact finite-`N` prefix-weight phase kicks.
3. Subsystem observable, assertion, and `OracleCirc` lifting (`mkrEmbedObs`, `mkrEmbedAssn`,
   `mkrLiftCirc`, `mkrTopSliceReg`, `mkrTriple_liftCirc_qSet`) with induction-based proofs
   free of
   equation-compiler `whnf` blowups.
-/
section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
private lemma qhlQSet_val {Var : Type} {d : ℕ} [NeZero d]
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qSet σ).1.1 =
      (θ σ).1.1 0 0 • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qSet_apply_mat θ σ
end

namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace
@[expose] public section
/-! ## 1. Symmetric-Subspace Operations with Prefix-Weight Phase Kicks -/
/-- Elementary symmetric-subspace operation on `SymSubset N M`: either `K` steps of a
  symmetric
  orthogonal walk `D *ᵥ symZVec R`, or an exact prefix-intersection phase kick `-R_{≤ j0}`. -/
inductive MuxSymOp (N M : ℕ) : Type
  | walk (K : ℕ) (D : SymOrthogonal N M)
  | prefixKick (j0 : ℕ)
/-- Exact symmetric-subspace prefix-weight phase kick negating subsets with `|E ∩ R| ≤ j0`. -/
def symPrefixKickVec {N M : ℕ} (R : Finset (Fin N)) (j0 : ℕ)
    (v : SymSubset N M → ℝ) : SymSubset N M → ℝ :=
  fun E ↦ if (E.1 ∩ R).card ≤ j0 then -v E else v E
/-- Sequential action of `ops: List (MuxSymOp N M)` on `v: SymSubset N M → ℝ`. -/
noncomputable def evalMuxSymOps {N M : ℕ} (R : Finset (Fin N)) :
    List (MuxSymOp N M) → (SymSubset N M → ℝ) → (SymSubset N M → ℝ)
  | [], v => v
  | .walk K D :: rest, v => evalMuxSymOps R rest (evalSymStage R D.1 K v)
  | .prefixKick j0 :: rest, v => evalMuxSymOps R rest (symPrefixKickVec R j0 v)
/-- Unmultiplexed oracle-step count of `ops` (`K` per `.walk K D`, `2` per `.prefixKick
  j0`). -/
def muxOpsQueryCount {N M : ℕ} : List (MuxSymOp N M) → ℕ
  | [] => 0
  | .walk K _ :: rest => K + muxOpsQueryCount rest
  | .prefixKick _ :: rest => 2 + muxOpsQueryCount rest
theorem sum_sq_symPrefixKickVec {N M : ℕ} (R : Finset (Fin N)) (j0 : ℕ)
    (v : SymSubset N M → ℝ) :
    (∑ E : SymSubset N M, (symPrefixKickVec R j0 v E) ^ 2) =
      ∑ E : SymSubset N M, (v E) ^ 2 := by
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  dsimp only [symPrefixKickVec]
  split_ifs <;> ring
theorem sum_sq_evalMuxSymOps {N M : ℕ} (R : Finset (Fin N))
    (ops : List (MuxSymOp N M)) (v : SymSubset N M → ℝ) :
    (∑ E : SymSubset N M, (evalMuxSymOps R ops v E) ^ 2) =
      ∑ E : SymSubset N M, (v E) ^ 2 := by
  have hstage (D : SymOrthogonal N M) :
      ∀ (K : ℕ) (u : SymSubset N M → ℝ),
        (∑ E, (evalSymStage R D.1 K u E) ^ 2) = ∑ E, (u E) ^ 2 := by
    intro K
    induction K with
    | zero => intro u; rfl
    | succ K ih =>
      intro u; rw [evalSymStage, ih, sum_sq_symOrthogonal_mulVec D, sum_sq_symZVec]
  induction ops generalizing v with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | walk K D => rw [evalMuxSymOps, ih, hstage D K v]
    | prefixKick j0 => rw [evalMuxSymOps, ih, sum_sq_symPrefixKickVec]
theorem sum_symHitProb_evalMuxSymOps {N M : ℕ} (hMN : M ≤ N) (R : Finset (Fin N))
    (ops : List (MuxSymOp N M)) :
    (∑ w ∈ Finset.range (min M R.card + 1),
      symHitProb R (evalMuxSymOps R ops (u0Vec N M)) w) = 1 := by
  rw [sum_symHitProb_eq_sum_sq, sum_sq_evalMuxSymOps, sum_sq_u0Vec hMN]
/-- Stage-adaptive `L_r`-block multiplexed Johnson renewal specification on `(m, k)` with
  workspace
  cap `L_max` (`1 ≤ L_max`, `L_max * m ≤ 65536`) and interspersed `2 * L_r`-query prefix
  kicks. -/
structure JohnsonMuxKickSpec (m k L_max : ℕ) where
  hL_max_pos : 1 ≤ L_max
  hL_max_hi : L_max * m ≤ 65536
  useWalk : ℕ → Bool
  lMult : ℕ → ℕ
  hlMult_pos : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true → 1 ≤ lMult r
  hlMult_le : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true → lMult r ≤ L_max
  n0 : ℕ
  hn0 : 600 ≤ n0
  ops : (n r : ℕ) → List (MuxSymOp (2 ^ n) (lMult r * m))
  V : ℕ → ℝ
  hV0 : V 0 = 0
  hV_mono : ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ k → V r₁ ≤ V r₂
  hV_eig : ∀ r : ℕ, 1 ≤ r → r ≤ k → (r = 1 ∨ useWalk r = false) →
    (Real.pi / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) < V r - V (r - 1)
  pLo : ℕ → ℕ → ℝ
  hpLo_nonneg : ∀ r w, 0 ≤ pLo r w
  hpLo_sum_pos : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true →
    0 < ∑ w ∈ Finset.Icc 1 (min (lMult r * m) r), pLo r w
  tauSum : ℕ → ℝ
  C_step : ℝ
  hops_len : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    (muxOpsQueryCount (ops n r) : ℝ) ≤ tauSum r * √(2 ^ n : ℝ) + C_step
  hpLo_le : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    ∀ R : Finset (Fin (2 ^ n)), R.card = r →
    ∀ w ∈ Finset.Icc 1 (min (lMult r * m) r),
      pLo r w ≤ symHitProb R (evalMuxSymOps R (ops n r) (u0Vec (2 ^ n) (lMult r * m))) w
  hdrift_lt : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true →
    (lMult r : ℝ) * tauSum r <
      ∑ w ∈ Finset.Icc 1 (min (lMult r * m) r), pLo r w * (V r - V (r - w))
end
public section
/-! ## 2. Subsystem Observable, Assertion, and `OracleCirc` Lifting -/
private noncomputable def mkrSliceIso {q Q : ℕ} (r : QRegister q Q)
    (e : r.Environment → ZMod 2) : Matrix (Fin (2 ^ Q)) (Fin (2 ^ q)) ℂ :=
  Matrix.of fun z z₀ ↦ if r.basisSplitEquiv z = (z₀, e) then 1 else 0
private lemma mkrSliceIso_mul_conjTranspose_apply {q Q : ℕ} (r : QRegister q Q)
    (e : r.Environment → ZMod 2) (B : Operator (2 ^ q)) (i j : Fin (2 ^ Q)) :
    (mkrSliceIso r e * B * (mkrSliceIso r e)ᴴ) i j =
      if (r.basisSplitEquiv i).2 = e ∧ (r.basisSplitEquiv j).2 = e then
        B (r.extractIndex i) (r.extractIndex j)
      else 0 := by
  have hsplit (z : Fin (2 ^ Q)) (z₀ : Fin (2 ^ q)) :
      r.basisSplitEquiv z = (z₀, e) ↔
        z₀ = r.extractIndex z ∧ (r.basisSplitEquiv z).2 = e := by
    rw [Prod.ext_iff, QRegister.basisSplitEquiv_apply_fst, eq_comm (a := r.extractIndex z)]
  have hmul (a : Fin (2 ^ q)) :
      (mkrSliceIso r e * B) i a =
        if (r.basisSplitEquiv i).2 = e then B (r.extractIndex i) a else 0 := by
    rw [Matrix.mul_apply, sum_eq_single (r.extractIndex i) (fun z₀ hz₀ ↦ by
      simp [mkrSliceIso, hsplit, hz₀])]
    by_cases hi : (r.basisSplitEquiv i).2 = e <;> simp [mkrSliceIso, hsplit, hi]
  rw [Matrix.mul_apply, sum_eq_single (r.extractIndex j) (fun z₀ hz₀ ↦ by
    simp [conjTranspose_apply, mkrSliceIso, hsplit, hz₀])]
  rw [hmul, conjTranspose_apply]
  by_cases hi : (r.basisSplitEquiv i).2 = e <;>
    by_cases hj : (r.basisSplitEquiv j).2 = e <;>
    simp [mkrSliceIso, hsplit, hi, hj]
private lemma sum_mkrSliceIso_mul_conjTranspose {q Q : ℕ} (r : QRegister q Q)
    (B : Operator (2 ^ q)) :
    (∑ e : r.Environment → ZMod 2, mkrSliceIso r e * B * (mkrSliceIso r e)ᴴ) =
      r.embedMatrix B := by
  ext i j
  rw [Matrix.sum_apply, QRegister.embedMatrix_apply,
    sum_eq_single (r.basisSplitEquiv i).2 (fun e he ↦ by
      rw [mkrSliceIso_mul_conjTranspose_apply, ite_eq_right (fun h ↦ he h.1.symm)]),
    mkrSliceIso_mul_conjTranspose_apply]
  by_cases h : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
  · rw [ite_eq_left ⟨rfl, h.symm⟩, ite_eq_left h, mul_one]
  · rw [ite_eq_right (fun h' ↦ h h'.2.symm), ite_eq_right h, mul_zero]
private noncomputable def mkrEmbedHerm {q Q : ℕ} (r : QRegister q Q)
    (H : HermitianMat (Fin (2 ^ q)) ℂ) : HermitianMat (Fin (2 ^ Q)) ℂ :=
  ∑ e : r.Environment → ZMod 2, HermitianMat.conj (mkrSliceIso r e) H
private lemma mkrEmbedHerm_mat {q Q : ℕ} (r : QRegister q Q)
    (H : HermitianMat (Fin (2 ^ q)) ℂ) :
    (mkrEmbedHerm r H).1 = r.embedMatrix H.1 := by
  rw [mkrEmbedHerm, HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum]
  have hterm (e : r.Environment → ZMod 2) :
      (HermitianMat.conj (mkrSliceIso r e) H).mat =
        mkrSliceIso r e * H.1 * (mkrSliceIso r e)ᴴ := by
    rw [HermitianMat.conj_apply_mat, HermitianMat.val_eq_coe]
  simp_rw [hterm]; exact sum_mkrSliceIso_mul_conjTranspose r H.1
private lemma mkrEmbedHerm_one {q Q : ℕ} (r : QRegister q Q) :
    mkrEmbedHerm r 1 = 1 :=
  HermitianMat.ext ((mkrEmbedHerm_mat r 1).trans r.embedMatrix_one)
/-- Embed a `q`-qubit observable on subregister `r: QRegister q Q` into `Observable (2 ^
  Q)`. -/
noncomputable def mkrEmbedObs {q Q : ℕ} (r : QRegister q Q)
    (o : Observable (Fin (2 ^ q))) : Observable (Fin (2 ^ Q)) :=
  ⟨mkrEmbedHerm r o.1,
    Finset.sum_nonneg fun e _ ↦ o.1.conj_nonneg (mkrSliceIso r e) o.2.1,
    (Finset.sum_le_sum fun _ _ ↦ HermitianMat.conj_mono o.2.2).trans_eq (mkrEmbedHerm_one r)⟩
theorem mkrEmbedObs_mat {q Q : ℕ} (r : QRegister q Q) (o : Observable (Fin (2 ^ q))) :
    (mkrEmbedObs r o).1.1 = r.embedMatrix o.1.1 :=
  mkrEmbedHerm_mat r o.1
theorem mkrEmbedObs_mono {q Q : ℕ} (r : QRegister q Q) {o₁ o₂ : Observable (Fin (2 ^ q))}
    (h : o₁ ≤ o₂) : mkrEmbedObs r o₁ ≤ mkrEmbedObs r o₂ :=
  Subtype.coe_le_coe.mp <|
    Finset.sum_le_sum fun _ _ ↦ HermitianMat.conj_mono (Subtype.coe_le_coe.mpr h)
private lemma mkrEmbedObs_ωSup {q Q : ℕ} (r : QRegister q Q)
    (c : OmegaCompletePartialOrder.Chain (Observable (Fin (2 ^ q)))) :
    mkrEmbedObs r (OmegaCompletePartialOrder.ωSup c) =
      OmegaCompletePartialOrder.ωSup (c.map ⟨mkrEmbedObs r, fun _ _ h ↦ mkrEmbedObs_mono r h⟩) := by
  let c' := c.map ⟨mkrEmbedObs r, fun _ _ h ↦ mkrEmbedObs_mono r h⟩
  apply Subtype.ext
  suffices hinner : ∀ X : HermitianMat (Fin (2 ^ Q)) ℂ,
      ⟪(mkrEmbedObs r (OmegaCompletePartialOrder.ωSup c)).1, X⟫_ℝ =
        ⟪(OmegaCompletePartialOrder.ωSup c').1, X⟫_ℝ by
    let D := (mkrEmbedObs r (OmegaCompletePartialOrder.ωSup c)).1 -
      (OmegaCompletePartialOrder.ωSup c').1
    have hD : ⟪D, D⟫_ℝ = 0 := by dsimp only [D]; rw [inner_sub_left, hinner]; ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hD)
  intro X
  have heq (o : Observable (Fin (2 ^ q))) :
      ⟪(mkrEmbedObs r o).1, X⟫_ℝ =
        ∑ e : r.Environment → ZMod 2, ⟪o.1, HermitianMat.conj (mkrSliceIso r e)ᴴ X⟫_ℝ := by
    dsimp only [mkrEmbedObs, mkrEmbedHerm]; rw [sum_inner]
    exact Finset.sum_congr rfl fun e _ ↦ HermitianMat.inner_conj_left _ _ _
  have hcont₁ : Continuous (fun o : Observable (Fin (2 ^ q)) ↦
      ∑ e : r.Environment → ZMod 2, ⟪o.1, HermitianMat.conj (mkrSliceIso r e)ᴴ X⟫_ℝ) :=
    continuous_finsetSum _ fun e _ ↦ by fun_prop
  have hcont₂ : Continuous (fun o : Observable (Fin (2 ^ Q)) ↦ ⟪o.1, X⟫_ℝ) := by fun_prop
  have ht₁ := (hcont₁.tendsto (OmegaCompletePartialOrder.ωSup c)).comp
    (OmegaCompletePartialOrder.tendsto_ωSup c)
  have ht₂ := (hcont₂.tendsto (OmegaCompletePartialOrder.ωSup c')).comp
    (OmegaCompletePartialOrder.tendsto_ωSup c')
  change Filter.Tendsto (fun n ↦ ∑ e : r.Environment → ZMod 2,
      ⟪(c n).1, HermitianMat.conj (mkrSliceIso r e)ᴴ X⟫_ℝ) _ _ at ht₁
  change Filter.Tendsto (fun n ↦ ⟪(c' n).1, X⟫_ℝ) _ _ at ht₂
  have hfn : (fun n ↦ ⟪(c' n).1, X⟫_ℝ) =
      fun n ↦ ∑ e : r.Environment → ZMod 2,
        ⟪(c n).1, HermitianMat.conj (mkrSliceIso r e)ᴴ X⟫_ℝ :=
    funext fun n ↦ heq (c n)
  rw [hfn] at ht₂; rw [heq]; exact tendsto_nhds_unique ht₁ ht₂
end
@[expose] public section
/-- Pointwise store lift of a `q`-qubit `CQAssertion` along `r: QRegister q Q`. -/
noncomputable def mkrEmbedAssn {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (Θ : CQAssertion (Store Var) (2 ^ q)) : CQAssertion (Store Var) (2 ^ Q) :=
  fun σ ↦ mkrEmbedObs r (Θ σ)
/-- Lift an `OracleCirc Var q O` to `Q` qubits along subregister `r: QRegister q Q`. -/
noncomputable def mkrLiftCirc {Var : Type} {q Q O : ℕ} (r : QRegister q Q) :
    OracleCirc Var q O → OracleCirc Var Q O
  | .skip => .skip
  | .step U => .step (phaseTag (r.embedUnitary U))
  | .oracle reg => .oracle (r.compose reg)
  | .measure x reg => .measure x (r.compose reg)
  | @OracleDynamicCircuit.qIf _ _ _ _ b _ t f => .qIf b (mkrLiftCirc r t) (mkrLiftCirc r f)
  | @OracleDynamicCircuit.qWhile _ _ _ _ b _ body => .qWhile b (mkrLiftCirc r body)
  | .seq c₁ c₂ => .seq (mkrLiftCirc r c₁) (mkrLiftCirc r c₂)
/-- Syntactic static oracle-call count for `qWhile`-free `OracleCirc` programs. -/
noncomputable def mkrStaticOracleCalls {Var : Type} {q O : ℕ} : OracleCirc Var q O → Option ℕ
  | .skip => some 0
  | .step _ => some 0
  | .oracle _ => some 1
  | .measure _ _ => some 0
  | @OracleDynamicCircuit.qIf _ _ _ _ _ _ t f =>
      match mkrStaticOracleCalls t, mkrStaticOracleCalls f with
      | some c₁, some c₂ => if c₁ = c₂ then some c₁ else none
      | _, _ => none
  | @OracleDynamicCircuit.qWhile _ _ _ _ _ _ _ => none
  | .seq c₁ c₂ =>
      match mkrStaticOracleCalls c₁, mkrStaticOracleCalls c₂ with
      | some a, some b => some (a + b)
      | _, _ => none
/-- Contiguous top-slice register `[W_pad, W_pad + W_sub + M)` sharing the `M`-qubit
  archive. -/
abbrev mkrTopSliceReg (W_pad W_sub W_tot M : ℕ) (hW : W_pad + W_sub = W_tot) :
    QRegister (W_sub + M) (W_tot + M) :=
  QRegister.block W_pad (W_sub + M) (by omega)
end
public section
theorem mkrEmbedAssn_mat {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (Θ : CQAssertion (Store Var) (2 ^ q)) (σ : Store Var) :
    (mkrEmbedAssn r Θ σ).1.1 = r.embedMatrix (Θ σ).1.1 :=
  mkrEmbedObs_mat r (Θ σ)
theorem mkrEmbedAssn_mono {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    {Θ₁ Θ₂ : CQAssertion (Store Var) (2 ^ q)} (h : Θ₁ ≤ Θ₂) :
    mkrEmbedAssn r Θ₁ ≤ mkrEmbedAssn r Θ₂ :=
  fun σ ↦ mkrEmbedObs_mono r (h σ)
theorem mkrEmbedAssn_bot {Var : Type} {q Q : ℕ} (r : QRegister q Q) :
    mkrEmbedAssn (Var := Var) r ⊥ = ⊥ := by
  funext σ
  refine Subtype.ext (HermitianMat.ext ?_)
  change (mkrEmbedObs r 0).1.1 = 0; rw [mkrEmbedObs_mat]; exact r.embedMatrix_zero
theorem mkrEmbedAssn_top {Var : Type} {q Q : ℕ} (r : QRegister q Q) :
    mkrEmbedAssn (Var := Var) r ⊤ = ⊤ := by
  funext σ
  refine Subtype.ext ?_
  exact mkrEmbedHerm_one r
theorem mkrEmbedAssn_add {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (Θ₁ Θ₂ : CQAssertion (Store Var) (2 ^ q)) (h_le : ∀ σ, (Θ₁ σ).1 + (Θ₂ σ).1 ≤ 1) :
    mkrEmbedAssn r (Θ₁.add Θ₂ h_le) =
      (mkrEmbedAssn r Θ₁).add (mkrEmbedAssn r Θ₂) (fun σ ↦ by
        dsimp only [mkrEmbedAssn]
        have hsum : (mkrEmbedObs r (Θ₁ σ)).1 + (mkrEmbedObs r (Θ₂ σ)).1 =
            (mkrEmbedObs r ((Θ₁.add Θ₂ h_le) σ)).1 := by
          apply HermitianMat.ext
          change (mkrEmbedObs r (Θ₁ σ)).1.1 + (mkrEmbedObs r (Θ₂ σ)).1.1 =
            (mkrEmbedObs r ((Θ₁.add Θ₂ h_le) σ)).1.1
          rw [mkrEmbedObs_mat, mkrEmbedObs_mat, mkrEmbedObs_mat]
          exact (r.embedMatrix_add (Θ₁ σ).1.1 (Θ₂ σ).1.1).symm
        rw [hsum]
        exact (mkrEmbedObs r ((Θ₁.add Θ₂ h_le) σ)).2.2) := by
  funext σ
  refine Subtype.ext (HermitianMat.ext ?_)
  change (mkrEmbedObs r ((Θ₁.add Θ₂ h_le) σ)).1.1 =
    (mkrEmbedObs r (Θ₁ σ)).1.1 + (mkrEmbedObs r (Θ₂ σ)).1.1
  rw [mkrEmbedObs_mat, mkrEmbedObs_mat, mkrEmbedObs_mat]
  exact r.embedMatrix_add (Θ₁ σ).1.1 (Θ₂ σ).1.1
private lemma mkrExtractIndex_zero_eq {q Q : ℕ} (r : QRegister q Q) :
    r.extractIndex 0 = 0 := by
  apply (basisBits q).injective
  funext i
  rw [QRegister.basisBits_extractIndex]; simp [basisBits_eq_testBit]
theorem wp_qSet_mkrEmbedAssn {Var : Type} [DecidableEq Var] {q Q : ℕ}
    (r : QRegister q Q) (Θ : CQAssertion (Store Var) (2 ^ q)) :
    wp (.qSet : QProg Var (2 ^ Q)) (mkrEmbedAssn r Θ) =
      mkrEmbedAssn r (wp (.qSet : QProg Var (2 ^ q)) Θ) := by
  funext σ
  refine Subtype.ext (HermitianMat.ext ?_)
  change ((wp (.qSet : QProg Var (2 ^ Q)) (mkrEmbedAssn r Θ)) σ).1.1 =
    (mkrEmbedObs r ((wp (.qSet : QProg Var (2 ^ q)) Θ) σ)).1.1
  rw [wp_qSet, wp_qSet, qhlQSet_val, mkrEmbedObs_mat, qhlQSet_val,
    r.embedMatrix_smul, r.embedMatrix_one, mkrEmbedAssn, mkrEmbedObs_mat,
    QRegister.embedMatrix_apply, mkrExtractIndex_zero_eq, ite_eq_left rfl, mul_one]
theorem wp_mkrLiftCirc {Var : Type} [DecidableEq Var] {q Q O : ℕ}
    (r : QRegister q Q) (oracle : Unitary (2 ^ O))
    (c : OracleCirc Var q O) (Θ : CQAssertion (Store Var) (2 ^ q)) :
    wp ((mkrLiftCirc r c).compile qAssign oracle) (mkrEmbedAssn r Θ) =
      mkrEmbedAssn r (wp (c.compile qAssign oracle) Θ) := by
  induction c generalizing Θ with
  | «skip» => rfl
  | «step» U =>
    dsimp only [mkrLiftCirc, compile]; rw [wp_qAssign, wp_phaseTag, wp_qAssign]
    funext σ
    refine Subtype.ext (Subtype.ext ?_)
    rw [qhlQAssign_val, mkrEmbedAssn_mat, mkrEmbedAssn_mat,
      qhlQAssign_val, QRegister.embedUnitary_val,
      r.embedMatrix_mul, r.embedMatrix_mul, r.embedMatrix_conjTranspose]
  | oracle reg =>
    dsimp only [mkrLiftCirc, compile]; rw [wp_qAssign, wp_qAssign]
    funext σ
    refine Subtype.ext (Subtype.ext ?_)
    rw [qhlQAssign_val, mkrEmbedAssn_mat, mkrEmbedAssn_mat,
      qhlQAssign_val, QRegister.embedUnitary_compose,
      r.embedUnitary_val (reg.embedUnitary oracle),
      r.embedMatrix_mul, r.embedMatrix_mul, r.embedMatrix_conjTranspose]
  | measure x reg =>
    dsimp only [mkrLiftCirc, compile]
    funext σ
    refine Subtype.ext (Subtype.ext ?_)
    rw [wp_measureRegister, mkrEmbedAssn_mat, wp_measureRegister, r.embedMatrix_sum]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    have hproj : (r.compose reg).basisOutcomeProjector o =
        r.embedMatrix (reg.basisOutcomeProjector o) :=
      QRegister.embedMatrix_compose r reg (compProj o)
    rw [hproj, mkrEmbedAssn_mat, r.embedMatrix_mul, r.embedMatrix_mul]
  | qIf b t f iht ihf =>
    funext σ
    dsimp only [mkrLiftCirc, compile, mkrEmbedAssn]; rw [wp_qIf, wp_qIf]
    by_cases hb : b σ
    · simp only [hb, ↓reduceIte]; exact congrFun (iht Θ) σ
    · simp only [hb, ↓reduceIte]; exact congrFun (ihf Θ) σ
  | qWhile b body ih =>
    dsimp only [mkrLiftCirc, compile]
    have hrec : ∀ t : ℕ,
        whileRecWP (wp ((mkrLiftCirc r body).compile qAssign oracle)) b t (mkrEmbedAssn r Θ) =
          mkrEmbedAssn r (whileRecWP (wp (body.compile qAssign oracle)) b t Θ) := by
      intro t
      induction t with
      | zero =>
        change (⊥ : CQAssertion (Store Var) (2 ^ Q)) = mkrEmbedAssn r ⊥; exact (mkrEmbedAssn_bot
          r).symm
      | succ t iht =>
        funext σ
        dsimp only [whileRecWP]
        by_cases hb : b σ
        · rw [ite_eq_left hb, iht, ih]; dsimp only [mkrEmbedAssn]; rw [ite_eq_left hb]
        · rw [ite_eq_right hb]; dsimp only [mkrEmbedAssn]; rw [ite_eq_right hb]
    funext σ
    rw [wp_qWhile, OmegaCompletePartialOrder.Pi.ωSup_apply]; dsimp only [mkrEmbedAssn]
    rw [wp_qWhile, OmegaCompletePartialOrder.Pi.ωSup_apply, mkrEmbedObs_ωSup]; apply le_antisymm
    · refine OmegaCompletePartialOrder.ωSup_le_ωSup_of_le fun t ↦ ⟨t, ?_⟩
      exact (congrFun (hrec t) σ).le
    · refine OmegaCompletePartialOrder.ωSup_le_ωSup_of_le fun t ↦ ⟨t, ?_⟩
      exact (congrFun (hrec t) σ).ge
  | seq c₁ c₂ ih₁ ih₂ =>
    dsimp only [mkrLiftCirc, compile]; rw [wp_qSeq, wp_qSeq, ih₂, ih₁]
theorem whileActiveWP_mkrLiftCirc {Var : Type} [DecidableEq Var] {q Q O : ℕ}
    (r : QRegister q Q) (oracle : Unitary (2 ^ O))
    (body : OracleCirc Var q O) (b : Store Var → Prop) [DecidablePred b] (t : ℕ) :
    whileActiveWP (wp ((mkrLiftCirc r body).compile qAssign oracle)) b t =
      mkrEmbedAssn r (whileActiveWP (wp (body.compile qAssign oracle)) b t) := by
  induction t with
  | zero =>
    funext σ
    dsimp only [whileActiveWP, mkrEmbedAssn]
    by_cases hb : b σ
    · rw [ite_eq_left hb, ite_eq_left hb]; exact (congrFun (mkrEmbedAssn_top (Var := Var) r) σ).symm
    · rw [ite_eq_right hb, ite_eq_right hb]
      exact (congrFun (mkrEmbedAssn_bot (Var := Var) r) σ).symm
  | succ t ih =>
    funext σ
    dsimp only [whileActiveWP]
    by_cases hb : b σ
    · rw [ite_eq_left hb, ih, wp_mkrLiftCirc]; dsimp only [mkrEmbedAssn]; rw [ite_eq_left hb]
    · rw [ite_eq_right hb]; dsimp only [mkrEmbedAssn]
      rw [ite_eq_right hb]; exact (congrFun (mkrEmbedAssn_bot (Var := Var) r) σ).symm
theorem costBound_mkrLiftCirc_of_staticOracleCalls {Var : Type} [DecidableEq Var]
    {q Q O : ℕ} (r : QRegister q Q) {oracle : Unitary (2 ^ O)}
    (hor : IsRealMatrix oracle.1) (c : OracleCirc Var q O) (cnt : ℕ)
    (h : mkrStaticOracleCalls c = some cnt) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
      ((mkrLiftCirc r c).compile qAssign oracle) (cnt : ℝ≥0) := by
  induction c generalizing cnt with
  | «skip» =>
    obtain rfl : cnt = 0 := Option.some.inj h.symm
    simpa [mkrLiftCirc, compile] using
      CostBound.skip_zero (Var := Var) (d := 2 ^ Q) (CostModel.ofEmbeddedOracle oracle)
  | «step» U =>
    obtain rfl : cnt = 0 := Option.some.inj h.symm
    simpa [mkrLiftCirc, compile] using
      costBound_qAssign_phaseTag (Var := Var) hor (r.embedUnitary U)
  | oracle reg =>
    obtain rfl : cnt = 1 := Option.some.inj h.symm
    have hcost := CostBound.qAssign (Var := Var)
      (CostModel.ofEmbeddedOracle (n := Q) oracle) ((r.compose reg).embedUnitary oracle)
    rw [CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary] at hcost; exact hcost
  | measure x reg =>
    obtain rfl : cnt = 0 := Option.some.inj h.symm
    simpa [mkrLiftCirc, compile, measureRegister, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) (CostModel.ofEmbeddedOracle oracle) x _
  | qIf cond t f iht ihf =>
    dsimp only [mkrStaticOracleCalls] at h
    cases ht : mkrStaticOracleCalls t with
    | none => simp [ht] at h
    | some c₁ =>
      cases hf : mkrStaticOracleCalls f with
      | none => simp [ht, hf] at h
      | some c₂ =>
        rw [ht, hf] at h; dsimp only at h
        by_cases heq : c₁ = c₂
        · subst heq
          rw [ite_eq_left rfl] at h; obtain rfl : cnt = c₁ := Option.some.inj h.symm
          simpa [mkrLiftCirc, compile] using CostBound.qIf cond (iht cnt ht) (ihf cnt hf)
        · rw [ite_eq_right heq] at h
          cases h
  | qWhile _ _ _ => cases h
  | seq c₁ c₂ ih₁ ih₂ =>
    dsimp only [mkrStaticOracleCalls] at h
    cases h₁ : mkrStaticOracleCalls c₁ with
    | none => simp [h₁] at h
    | some a =>
      cases h₂ : mkrStaticOracleCalls c₂ with
      | none => simp [h₁, h₂] at h
      | some b =>
        rw [h₁, h₂] at h; obtain rfl : cnt = a + b := Option.some.inj h.symm
        simpa [mkrLiftCirc, compile, Nat.cast_add] using (ih₁ a h₁).seq (ih₂ b h₂)
/-! ## 3. Top-Slice Register Embedding & Cross-Dimension `qSet` Bridge -/
private lemma mkrTopSliceReg_compose_highBlock (W_pad W_sub W_tot M : ℕ)
    (hW : W_pad + W_sub = W_tot) :
    (mkrTopSliceReg W_pad W_sub W_tot M hW).compose (highBlock W_sub M) =
      highBlock W_tot M := by
  ext w
  simp only [mkrTopSliceReg, highBlock, QRegister.compose, Function.Embedding.trans_apply,
    QRegister.block_apply_val]
  omega
private lemma lowHighEquiv_snd_extractIndex_mkrTopSliceReg (W_pad W_sub W_tot M : ℕ)
    (hW : W_pad + W_sub = W_tot) (z : Fin (2 ^ (W_tot + M))) :
    (lowHighEquiv W_sub M ((mkrTopSliceReg W_pad W_sub W_tot M hW).extractIndex z)).2 =
      (lowHighEquiv W_tot M z).2 := by
  rw [← extractIndex_highBlock, ← QRegister.extractIndex_compose,
    mkrTopSliceReg_compose_highBlock, extractIndex_highBlock]
private lemma mkrEmbedObs_realDiagObs {q Q : ℕ} (r : QRegister q Q)
    (f : Fin (2 ^ q) → ℝ) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1) :
    mkrEmbedObs r (realDiagObs f hf0 hf1) =
      realDiagObs (fun z ↦ f (r.extractIndex z))
        (fun z ↦ hf0 (r.extractIndex z)) (fun z ↦ hf1 (r.extractIndex z)) := by
  refine Subtype.ext (HermitianMat.ext ?_)
  rw [← HermitianMat.val_eq_coe, ← HermitianMat.val_eq_coe,
    mkrEmbedObs_mat, realDiagObs_mat, r.embedMatrix_diagonal, realDiagObs_mat]
theorem mkrEmbedAssn_validObs {Var : Type} {n m_sub m_tot k W_pad : ℕ}
    (hW : W_pad + m_sub * (n + 1) = m_tot * (n + 1)) (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    mkrEmbedAssn (Var := Var)
        (mkrTopSliceReg W_pad (m_sub * (n + 1)) (m_tot * (n + 1)) (k * n) hW)
        (validObs n m_sub k S j) =
      validObs n m_tot k S j := by
  funext σ
  dsimp only [mkrEmbedAssn, validObs]; rw [mkrEmbedObs_realDiagObs]
  refine Subtype.ext (HermitianMat.ext ?_)
  rw [← HermitianMat.val_eq_coe, ← HermitianMat.val_eq_coe, realDiagObs_mat, realDiagObs_mat]
  refine congrArg diagonal (funext fun z ↦ ?_)
  dsimp only [validInd]; rw [lowHighEquiv_snd_extractIndex_mkrTopSliceReg]
theorem mkrEmbedAssn_invalidObs {Var : Type} {n m_sub m_tot k W_pad : ℕ}
    (hW : W_pad + m_sub * (n + 1) = m_tot * (n + 1)) (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    mkrEmbedAssn (Var := Var)
        (mkrTopSliceReg W_pad (m_sub * (n + 1)) (m_tot * (n + 1)) (k * n) hW)
        (invalidObs n m_sub k S j) =
      invalidObs n m_tot k S j := by
  funext σ
  dsimp only [mkrEmbedAssn, invalidObs]; rw [mkrEmbedObs_realDiagObs]
  refine Subtype.ext (HermitianMat.ext ?_)
  rw [← HermitianMat.val_eq_coe, ← HermitianMat.val_eq_coe, realDiagObs_mat, realDiagObs_mat]
  refine congrArg diagonal (funext fun z ↦ ?_)
  dsimp only [invalidInd]; rw [lowHighEquiv_snd_extractIndex_mkrTopSliceReg]
theorem mkrEmbedAssn_scaledValidObs {Var : Type} {n m_sub m_tot k W_pad : ℕ}
    (hW : W_pad + m_sub * (n + 1) = m_tot * (n + 1)) (S : Finset (Fin (2 ^ n)))
    (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    mkrEmbedAssn (Var := Var)
        (mkrTopSliceReg W_pad (m_sub * (n + 1)) (m_tot * (n + 1)) (k * n) hW)
        (scaledValidObs n m_sub k S j c hc0 hc1) =
      scaledValidObs n m_tot k S j c hc0 hc1 := by
  funext σ
  dsimp only [mkrEmbedAssn, scaledValidObs]; rw [mkrEmbedObs_realDiagObs]
  refine Subtype.ext (HermitianMat.ext ?_)
  rw [← HermitianMat.val_eq_coe, ← HermitianMat.val_eq_coe, realDiagObs_mat, realDiagObs_mat]
  refine congrArg diagonal (funext fun z ↦ ?_)
  dsimp only [validInd]; rw [lowHighEquiv_snd_extractIndex_mkrTopSliceReg]
theorem mkrEmbedAssn_liftPureProp {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (P : Store Var → Prop) :
    mkrEmbedAssn r (liftPureProp P) = liftPureProp P := by
  funext σ
  unfold mkrEmbedAssn liftPureProp
  split_ifs
  · exact congrFun (mkrEmbedAssn_top (Var := Var) r) σ
  · exact congrFun (mkrEmbedAssn_bot (Var := Var) r) σ
private noncomputable def mkrResetCrossMat {d₁ d₂ : ℕ} [NeZero d₂] (ρ : 𝒟 (Fin d₁)) :
    HermitianMat (Fin d₂) ℂ :=
  ⟨Matrix.single 0 0 (ρ.1.trace : ℂ),
    show (Matrix.single (0 : Fin d₂) 0 (ρ.1.trace : ℂ)).IsHermitian by
      simp [Matrix.IsHermitian, Matrix.conjTranspose_single, RCLike.star_def]⟩
private lemma mkrResetCrossMat_mat {d₁ d₂ : ℕ} [NeZero d₂] (ρ : 𝒟 (Fin d₁)) :
    (mkrResetCrossMat (d₂ := d₂) ρ).mat = Matrix.single 0 0 (ρ.1.trace : ℂ) := rfl
private lemma mkrTrace_resetCrossMat {d₁ d₂ : ℕ} [NeZero d₂] (ρ : 𝒟 (Fin d₁)) :
    (mkrResetCrossMat (d₂ := d₂) ρ).trace = ρ.1.trace := by
  simp [HermitianMat.trace_eq_re_trace, mkrResetCrossMat_mat]
private noncomputable def mkrResetCrossPDO {d₁ d₂ : ℕ} [NeZero d₂] (ρ : 𝒟 (Fin d₁)) : 𝒟 (Fin d₂) :=
  ⟨mkrResetCrossMat ρ,
    by
      rw [HermitianMat.zero_le_iff]
      change (Matrix.single (0 : Fin d₂) 0 (ρ.1.trace : ℂ)).PosSemidef
      rw [← Matrix.diagonal_single, Matrix.posSemidef_diagonal_iff]
      intro i
      rcases eq_or_ne i 0 with rfl | hi
      · simp [HermitianMat.trace_nonneg ρ.2.1]
      · simp [hi],
    (mkrTrace_resetCrossMat ρ).trans_le ρ.2.2⟩
private noncomputable def mkrResetCrossState {Var : Type} {d₁ d₂ : ℕ} [NeZero d₂]
    (Δ : CQState (Store Var) d₁) : CQState (Store Var) d₂ :=
  ⟨fun σ ↦ mkrResetCrossPDO (Δ.1 σ),
    by
      obtain ⟨c, hc, hc1⟩ := Δ.2
      have htr : (fun σ ↦ (mkrResetCrossPDO (d₂ := d₂) (Δ.1 σ)).trace) =
          fun σ ↦ (Δ.1 σ).trace :=
        funext fun σ ↦ NNReal.coe_inj.mp (mkrTrace_resetCrossMat (Δ.1 σ))
      exact ⟨c, htr ▸ hc, hc1⟩⟩
private lemma mkrResetCrossState_trace {Var : Type} {d₁ d₂ : ℕ} [NeZero d₂]
    (Δ : CQState (Store Var) d₁) :
    (mkrResetCrossState (d₂ := d₂) Δ).trace = Δ.trace := by
  rw [CQState.trace_eq_tsum, CQState.trace_eq_tsum]
  exact tsum_congr fun σ ↦ NNReal.coe_inj.mp (mkrTrace_resetCrossMat (Δ.1 σ))
private lemma mkrExpect_qSet_resetCrossState {Var : Type} [DecidableEq Var] {q Q : ℕ}
    (r : QRegister q Q) (Δ : CQState (Store Var) (2 ^ Q)) (Θ : CQAssertion (Store Var) (2 ^ q)) :
    𝔼[mkrResetCrossState (d₂ := 2 ^ q) Δ, wp (.qSet : QProg Var (2 ^ q)) Θ] =
      𝔼[Δ, wp (.qSet : QProg Var (2 ^ Q)) (mkrEmbedAssn r Θ)] := by
  rw [wp_qSet_mkrEmbedAssn, expect_eq_tsum, expect_eq_tsum]
  refine tsum_congr fun σ ↦ ?_
  let o := (wp (.qSet : QProg Var (2 ^ q)) Θ) σ
  let c : ℂ := (Θ σ).1.1 0 0
  have ho_mat : o.1.1 = diagonal (fun _ : Fin (2 ^ q) ↦ c) := by
    dsimp only [o, c]; rw [wp_qSet, qhlQSet_val]
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij]
  have hc_re : c = (c.re : ℂ) := (observable_diag_real_bounds o _ ho_mat 0).1
  have hc1 : o.1.1 = (c.re : ℂ) • (1 : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ) := by
    dsimp only [o]; rw [wp_qSet, qhlQSet_val]
    change c • (1 : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ) = _; rw [← hc_re]
  have ho_herm : o.1 = c.re • (1 : HermitianMat (Fin (2 ^ q)) ℂ) := by
    apply HermitianMat.ext; change o.1.1 = (c.re • (1 : HermitianMat (Fin (2 ^ q)) ℂ)).mat
    rw [hc1, HermitianMat.mat_smul, HermitianMat.mat_one]
    ext i j
    simp
  have hemb_herm : (mkrEmbedAssn r (wp (.qSet : QProg Var (2 ^ q)) Θ) σ).1 =
      c.re • (1 : HermitianMat (Fin (2 ^ Q)) ℂ) := by
    change (mkrEmbedObs r o).1 = _; apply HermitianMat.ext
    change (mkrEmbedObs r o).1.1 = (c.re • (1 : HermitianMat (Fin (2 ^ Q)) ℂ)).mat
    rw [mkrEmbedObs_mat, hc1, r.embedMatrix_smul, r.embedMatrix_one,
      HermitianMat.mat_smul, HermitianMat.mat_one]
    ext i j
    simp
  change ⟪o.1, ((mkrResetCrossState (d₂ := 2 ^ q) Δ).1 σ).1⟫_ℝ =
    ⟪(mkrEmbedAssn r (wp (.qSet : QProg Var (2 ^ q)) Θ) σ).1, (Δ.1 σ).1⟫_ℝ
  rw [ho_herm, hemb_herm, inner_smul_left, inner_smul_left, RCLike.conj_to_real,
    HermitianMat.one_inner, HermitianMat.one_inner]
  dsimp only [mkrResetCrossState, mkrResetCrossPDO]; rw [mkrTrace_resetCrossMat]
theorem mkrTriple_liftCirc_qSet {Var : Type} [DecidableEq Var] {q Q O : ℕ}
    (r : QRegister q Q) (c : OracleCirc Var q O) (oracle : Unitary (2 ^ O))
    (P : Store Var → Prop)
    (htr : ⦃ (⊤ : CQAssertion (Store Var) (2 ^ q)) ⦄
      (qset ;; c.compile qAssign oracle) ⦃ liftPureProp P ⦄) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Q)) ⦄
      (qset ;; (mkrLiftCirc r c).compile qAssign oracle) ⦃ liftPureProp P ⦄ := fun Δ ↦ by
  let Δ' := mkrResetCrossState (d₂ := 2 ^ q) Δ
  calc 𝔼[Δ, ⊤]
      = Δ.trace := expect_top Δ
    _ = Δ'.trace := congrArg NNReal.toReal (mkrResetCrossState_trace Δ).symm
    _ = 𝔼[Δ', ⊤] := (expect_top Δ').symm
    _ ≤ 𝔼[(interp (qset ;; c.compile qAssign oracle)).toStateFun Δ', liftPureProp P] := htr Δ'
    _ = 𝔼[Δ', wp (.qSet : QProg Var (2 ^ q))
          (wp (c.compile qAssign oracle) (liftPureProp P))] := by
          rw [← wp_expectation_eq, wp_qSeq]
    _ = 𝔼[Δ, wp (.qSet : QProg Var (2 ^ Q))
          (mkrEmbedAssn r (wp (c.compile qAssign oracle) (liftPureProp P)))] :=
          mkrExpect_qSet_resetCrossState r Δ _
    _ = 𝔼[Δ, wp (.qSet : QProg Var (2 ^ Q))
          (wp ((mkrLiftCirc r c).compile qAssign oracle) (liftPureProp P))] := by
          rw [← wp_mkrLiftCirc, mkrEmbedAssn_liftPureProp]
    _ = 𝔼[(interp (qset ;; (mkrLiftCirc r c).compile qAssign oracle)).toStateFun Δ,
          liftPureProp P] := by
          rw [← wp_qSeq, wp_expectation_eq]
end
end QuantumComputation.Specs.DickeSol
