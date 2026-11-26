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
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.IrreducibleDef
public import Track2Grover.Engine.BaselineRouter
public import Track2Grover.Engine.WeakDickeBase
public import Track2Grover.Engine.WeakDickeCore
/-!
Single-file formalization of the 2-stage Johnson-scheme eigenspace reflection walk
`(R_{V_1})^{K_1}` followed by `(R_{V_0 ⊕ V_1})^{K_2}` on `m`-element subsets of
`Fin (2 ^ n)` for the three selected `k = 2` cells `(2, 2), (4, 2), (8, 2)`. Lifts schedule
times to `10 ^ 12`, potentials and hit-probability lower bounds to `10 ^ 15`, interval
rounding pads to `1` (`n ≥ 200`), and rational relative costs to `10 ^ 12`.
-/
section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

namespace QuantumComputation.Specs.DickeSol
@[expose] public section
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation InnerProductSpace
/-! ## 1. `SymSubset` Pure-Real Walk Algebra -/
/-- Fintype of `m`-element subsets `E ⊆ Fin N` (`card = N.choose m`). -/
abbrev SymSubset (N m : ℕ) : Type := { E : Finset (Fin N) // E.card = m }
theorem card_symSubset (N m : ℕ) : Fintype.card (SymSubset N m) = N.choose m := by
  have hbij : Fintype.card (SymSubset N m) =
      ((Finset.univ : Finset (Fin N)).powersetCard m).card := by
    rw [← Fintype.card_coe]; refine Fintype.card_congr
      { toFun := fun E ↦ ⟨E.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, E.2⟩⟩
        invFun := fun E ↦ ⟨E.1, (Finset.mem_powersetCard.mp E.2).2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
/-- Normalized uniform vector on `SymSubset N m`. -/
noncomputable def u0Vec (N m : ℕ) : SymSubset N m → ℝ := fun _ ↦ 1 / √(N.choose m : ℝ)
/-- Deflated odd-intersection phase sign `|[E]⟩ ↦ (-1)^{|E ∩ R|} |[E]⟩`. -/
noncomputable def symZVec {N m : ℕ} (R : Finset (Fin N))
    (v : SymSubset N m → ℝ) : SymSubset N m → ℝ :=
  fun E ↦ (-1 : ℝ) ^ (E.1 ∩ R).card * v E
/-- Real orthogonal operator `Dᵀ * D = 1` on `SymSubset N m`. -/
def SymOrthogonal (N m : ℕ) : Type := { D : Matrix (SymSubset N m) (SymSubset N m) ℝ // Dᵀ * D = 1 }
/-- Constructor for symmetric involutive reflections (`Dᵀ = D` and `D * D = 1`). -/
def SymOrthogonal.ofSymmInvolution {N m : ℕ} (D : Matrix (SymSubset N m) (SymSubset N m) ℝ)
    (hsym : Dᵀ = D) (hinv : D * D = 1) : SymOrthogonal N m :=
  ⟨D, by rw [hsym, hinv]⟩
/-- Iterate `(D ∘ symZVec R)` `K` times on `SymSubset N m`. -/
noncomputable def evalSymStage {N m : ℕ} (R : Finset (Fin N))
    (D : Matrix (SymSubset N m) (SymSubset N m) ℝ) :
    ℕ → (SymSubset N m → ℝ) → (SymSubset N m → ℝ)
  | 0, v => v
  | K + 1, v => evalSymStage R D K (D *ᵥ symZVec R v)
/-- Sequential multi-stage evolution `[(K_1, D_1), (K_2, D_2),...]`. -/
noncomputable def evalSymStages {N m : ℕ} (R : Finset (Fin N)) :
    List (ℕ × SymOrthogonal N m) → (SymSubset N m → ℝ) → (SymSubset N m → ℝ)
  | [], v => v
  | (K, D) :: rest, v => evalSymStages R rest (evalSymStage R D.1 K v)
/-- Total query steps across a multi-stage list (`+1` readout added in pass). -/
def stagesQueryCount {α : Type*} (stages : List (ℕ × α)) : ℕ := (stages.map Prod.fst).sum
/-- Total probability mass of discovering exactly `w` targets in `R`. -/
noncomputable def symHitProb {N m : ℕ} (R : Finset (Fin N)) (v : SymSubset N m → ℝ) (w : ℕ) : ℝ :=
  ∑ E ∈ Finset.univ.filter (fun E : SymSubset N m ↦ (E.1 ∩ R).card = w), (v E) ^ 2
theorem symHitProb_nonneg {N m : ℕ} (R : Finset (Fin N))
    (v : SymSubset N m → ℝ) (w : ℕ) : 0 ≤ symHitProb R v w :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
theorem sum_sq_u0Vec {N m : ℕ} (hmN : m ≤ N) : (∑ E : SymSubset N m, (u0Vec N m E) ^ 2) = 1 := by
  have hc_pos : (0 : ℝ) < (N.choose m : ℝ) := (by exact_mod_cast Nat.choose_pos hmN)
  simp only [u0Vec, Finset.sum_const, Finset.card_univ, card_symSubset, nsmul_eq_mul, one_div,
    inv_pow, Real.sq_sqrt hc_pos.le]; exact mul_inv_cancel₀ hc_pos.ne'
theorem sum_sq_symZVec {N m : ℕ} (R : Finset (Fin N)) (v : SymSubset N m → ℝ) :
    (∑ E : SymSubset N m, (symZVec R v E) ^ 2) = ∑ E : SymSubset N m, (v E) ^ 2 := by
  refine Finset.sum_congr rfl fun E _ ↦ ?_; dsimp only [symZVec]
  rw [mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow, one_mul]
theorem sum_sq_symOrthogonal_mulVec {N m : ℕ} (D : SymOrthogonal N m) (v : SymSubset N m → ℝ) :
    (∑ E : SymSubset N m, ((D.1 *ᵥ v) E) ^ 2) = ∑ E : SymSubset N m, (v E) ^ 2 := by
  have hdot : ∀ u : SymSubset N m → ℝ, (∑ E, (u E) ^ 2) = u ⬝ᵥ u := fun u ↦ by simp [dotProduct, sq]
  have hvm : (D.1 *ᵥ v) ᵥ* D.1 = D.1ᵀ *ᵥ (D.1 *ᵥ v) := by
    funext j; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [hdot, hdot, Matrix.dotProduct_mulVec, hvm, Matrix.mulVec_mulVec, D.2, Matrix.one_mulVec]
theorem sum_sq_evalSymStages {N m : ℕ} (R : Finset (Fin N)) (stages : List (ℕ × SymOrthogonal N
    m)) (v : SymSubset N m → ℝ) : (∑ E : SymSubset N m, (evalSymStages R stages v E) ^ 2) = ∑ E :
    SymSubset N m, (v E) ^ 2 := by
  have hstage (D : SymOrthogonal N m) : ∀ (K : ℕ) (u : SymSubset N m → ℝ),
        (∑ E, (evalSymStage R D.1 K u E) ^ 2) = ∑ E, (u E) ^ 2 := by
    intro K
    induction K with
    | zero => intro u; rfl
    | succ K ih => intro u; rw [evalSymStage, ih, sum_sq_symOrthogonal_mulVec D, sum_sq_symZVec]
  induction stages generalizing v with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨K, D⟩; rw [evalSymStages, ih, hstage D K v]
theorem sum_symHitProb_eq_sum_sq {N m : ℕ} (R : Finset (Fin N)) (v : SymSubset N m → ℝ) : (∑ w ∈
    Finset.range (min m R.card + 1), symHitProb R v w) = ∑ E : SymSubset N m, (v E) ^ 2 := by
  unfold symHitProb; rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ ↦ rfl; ext E
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ ↦ trivial, fun _ ↦ ⟨(E.1 ∩ R).card, ?_, rfl⟩⟩
    have h1 : (E.1 ∩ R).card ≤ m := (Finset.card_le_card Finset.inter_subset_left).trans_eq E.2
    have h2 : (E.1 ∩ R).card ≤ R.card := Finset.card_le_card Finset.inter_subset_right
    exact Nat.lt_succ_of_le (le_min h1 h2)
  · intro w₁ _ w₂ _ hne; refine Finset.disjoint_left.mpr fun E h₁ h₂ ↦ hne ?_
    exact (Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2
theorem sum_symHitProb_evalSymStages {N m : ℕ} (hmN : m ≤ N) (R : Finset (Fin N))
    (stages : List (ℕ × SymOrthogonal N m)) : (∑ w ∈ Finset.range (min m R.card + 1),
      symHitProb R (evalSymStages R stages (u0Vec N m)) w) = 1 := by
  rw [sum_symHitProb_eq_sum_sq, sum_sq_evalSymStages, sum_sq_u0Vec hmN]
/-! ## 2. Isometric Basis Embedding, Householder Prep, & Orthogonal Lift -/
/-- Strictly-increasing `m`-tuple address index for `E: SymSubset (2 ^ n) m`. -/
def subsetAddrIdx (n m : ℕ) (E : SymSubset (2 ^ n) m) : Fin (2 ^ (m * n)) :=
  (addrEquiv n m).symm (fun j : Fin m ↦ E.1.orderEmbOfFin E.2 j)
/-- Work-register basis state (`flag = 0`, strictly sorted slot addresses) for `E`. -/
noncomputable def subsetWorkIdx (n m : ℕ) (E : SymSubset (2 ^ n) m) : Fin (2 ^ (m * (n + 1))) :=
  (addrReg n m).basisSplitEquiv.symm (subsetAddrIdx n m E, 0)
theorem image_orderEmbOfFin_symSubset {N m : ℕ} (E : SymSubset N m) :
    Finset.univ.image (E.1.orderEmbOfFin E.2) = E.1 := by
  refine Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.mpr fun j _ ↦ Finset.orderEmbOfFin_mem E.1 E.2 j) ?_
  rw [Finset.card_image_of_injective _ (E.1.orderEmbOfFin E.2).injective,
    Finset.card_univ, Fintype.card_fin, E.2]
theorem subsetWorkIdx_injective (n m : ℕ) : Function.Injective (subsetWorkIdx n m) := by
  intro E₁ E₂ h; have h1 := congrArg Prod.fst ((addrReg n m).basisSplitEquiv.symm.injective h)
  have h2 : ⇑(E₁.1.orderEmbOfFin E₁.2) = ⇑(E₂.1.orderEmbOfFin E₂.2) :=
    (addrEquiv n m).symm.injective h1
  apply Subtype.ext; rw [← image_orderEmbOfFin_symSubset E₁, ← image_orderEmbOfFin_symSubset E₂, h2]
theorem slotAddr_subsetWorkIdx (n m : ℕ) (E : SymSubset (2 ^ n) m) (j : Fin m) :
    slotAddr n m (subsetWorkIdx n m E) j = E.1.orderEmbOfFin E.2 j := by
  rw [← addrEquiv_extractIndex]
  have hex : (addrReg n m).extractIndex (subsetWorkIdx n m E) = subsetAddrIdx n m E := by
    rw [← QRegister.basisSplitEquiv_apply_fst]; simp [subsetWorkIdx]
  rw [hex, subsetAddrIdx, Equiv.apply_symm_apply]
theorem env_subsetWorkIdx (n m : ℕ) (E : SymSubset (2 ^ n) m) :
    ((addrReg n m).basisSplitEquiv (subsetWorkIdx n m E)).2 = 0 := by
  simp [subsetWorkIdx]
/-- Real isometric injection `J: Matrix (Fin (2 ^ (m * (n + 1)))) (SymSubset (2 ^ n) m) ℝ`. -/
noncomputable def symInjMat (n m : ℕ) : Matrix (Fin (2 ^ (m * (n + 1)))) (SymSubset (2 ^ n) m) ℝ :=
  fun z E ↦ if z = subsetWorkIdx n m E then 1 else 0
theorem symInjMat_transpose_mul_self (n m : ℕ) : (symInjMat n m)ᵀ * symInjMat n m = 1 := by
  ext E₁ E₂; rw [Matrix.mul_apply, Matrix.one_apply]; by_cases h : E₁ = E₂
  · subst h
    rw [ite_eq_left rfl, sum_eq_single (subsetWorkIdx n m E₁) (fun z hz ↦ by simp [symInjMat, hz])]
    simp [symInjMat]
  · rw [ite_eq_right h]; refine Finset.sum_eq_zero fun z _ ↦ ?_
    simp only [Matrix.transpose_apply, symInjMat]; by_cases hz : z = subsetWorkIdx n m E₁
    · subst hz
      have hne : subsetWorkIdx n m E₁ ≠ subsetWorkIdx n m E₂ :=
        fun h2 ↦ h (subsetWorkIdx_injective n m h2)
      simp [hne]
    · simp [hz]
/-- Complex amplitude vector on `workReg` corresponding to `v: SymSubset (2 ^ n) m → ℝ`. -/
noncomputable def liftSymVec (n m : ℕ) (v : SymSubset (2 ^ n) m → ℝ) :
    Fin (2 ^ (m * (n + 1))) → ℂ :=
  fun z ↦ (((symInjMat n m *ᵥ v) z : ℝ) : ℂ)
theorem liftSymVec_eq_sum_single (n m : ℕ) (v : SymSubset (2 ^ n) m → ℝ) : liftSymVec n m v =
      ∑ E : SymSubset (2 ^ n) m, (v E : ℂ) • Pi.single (subsetWorkIdx n m E) 1 := by
  funext z
  simp only [liftSymVec, Matrix.mulVec, dotProduct, symInjMat, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  by_cases hz : z = subsetWorkIdx n m E <;> simp [hz]
/-- Real block-lift `1 + J * (D - 1) * Jᵀ` of `D: SymOrthogonal (2 ^ n) m`. -/
noncomputable def liftSymRealMat (n m : ℕ) (D : SymOrthogonal (2 ^ n) m) :
    Matrix (Fin (2 ^ (m * (n + 1)))) (Fin (2 ^ (m * (n + 1)))) ℝ :=
  let J := symInjMat n m
  1 + J * (D.1 - 1) * Jᵀ
/-- Lift `D: SymOrthogonal (2 ^ n) m` to a `Unitary (2 ^ (m * (n + 1)))`. -/
noncomputable def liftSymOrthogonal (n m : ℕ) (D : SymOrthogonal (2 ^ n) m) :
    Unitary (2 ^ (m * (n + 1))) :=
  ⟨(liftSymRealMat n m D).map Complex.ofRealHom, by
    let J := symInjMat n m
    let A := D.1 - 1
    let L := liftSymRealMat n m D
    have hJtJ : Jᵀ * J = 1 := symInjMat_transpose_mul_self n m
    have hAA : Aᵀ + A + Aᵀ * A = 0 := by
      dsimp only [A]
      simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, D.2]
      abel
    have hLt : Lᵀ = 1 + J * Aᵀ * Jᵀ := by
      dsimp only [L, liftSymRealMat, J, A]
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    have hmid : (J * Aᵀ * Jᵀ) * (J * A * Jᵀ) = J * (Aᵀ * A) * Jᵀ := by
      calc (J * Aᵀ * Jᵀ) * (J * A * Jᵀ)
          = (J * Aᵀ) * ((Jᵀ * J) * (A * Jᵀ)) := by simp only [Matrix.mul_assoc]
        _ = J * (Aᵀ * A) * Jᵀ := by rw [hJtJ, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    have hLtL : Lᵀ * L = 1 := by
      change Lᵀ * (1 + J * A * Jᵀ) = 1
      rw [hLt, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hmid]
      have hsum : J * A * Jᵀ + (J * Aᵀ * Jᵀ + J * (Aᵀ * A) * Jᵀ) =
          J * (Aᵀ + A + Aᵀ * A) * Jᵀ := by
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
      rw [add_assoc (1 : Matrix _ _ ℝ), hsum, hAA, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar : star (L.map Complex.ofRealHom) = Lᵀ.map Complex.ofRealHom := by
      ext i j
      simp
    rw [hstar, ← Matrix.map_mul, hLtL]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]⟩
theorem liftSymOrthogonal_mulVec (n m : ℕ) (D : SymOrthogonal (2 ^ n) m) (v : SymSubset (2 ^ n) m
    → ℝ) : (liftSymOrthogonal n m D).1 *ᵥ liftSymVec n m v = liftSymVec n m (D.1 *ᵥ v) := by
  let J := symInjMat n m; let L := liftSymRealMat n m D
  have hLJ : L * J = J * D.1 := by
    dsimp only [L, liftSymRealMat, J]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (J * (D.1 - 1)) Jᵀ J,
      symInjMat_transpose_mul_self, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
  have hreal : L *ᵥ (J *ᵥ v) = J *ᵥ (D.1 *ᵥ v) := (by rw [mulVec_mulVec, hLJ, ← mulVec_mulVec])
  funext z; have hmap : ((L.map Complex.ofRealHom) *ᵥ (fun y ↦ Complex.ofRealHom ((J *ᵥ v) y))) z =
        Complex.ofRealHom ((L *ᵥ (J *ᵥ v)) z) :=
    (RingHom.map_mulVec Complex.ofRealHom L (J *ᵥ v) z).symm
  exact hmap.trans (congrArg Complex.ofRealHom (congrFun hreal z))
/-- Real Householder reflection matrix mapping `|0⟩` to real unit vector `u: Fin d → ℝ`. -/
noncomputable def householderRealMat {d : ℕ} [NeZero d] (u : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  open Classical in
  let e₀ : Fin d → ℝ := Pi.single 0 1
  let w : Fin d → ℝ := fun i ↦ e₀ i - u i
  let s : ℝ := ∑ i : Fin d, (w i) ^ 2
  if s = 0 then 1
  else Matrix.of fun i j ↦ (if i = j then 1 else 0) - (2 / s) * w i * w j
/-- Real Householder unitary mapping `|0⟩` to any real unit vector `u: Fin d → ℝ`. -/
noncomputable def householderPrepUnitary {d : ℕ} [NeZero d] (u : Fin d → ℝ)
    (_hu : (∑ i : Fin d, (u i) ^ 2) = 1) : Unitary d :=
  ⟨(householderRealMat u).map Complex.ofRealHom, by open Classical in
    let e₀ : Fin d → ℝ := Pi.single 0 1
    let w : Fin d → ℝ := fun i ↦ e₀ i - u i
    let s : ℝ := ∑ i : Fin d, (w i) ^ 2
    let H := householderRealMat u
    have hsym : Hᵀ = H := by
      ext i j
      dsimp only [H, householderRealMat, Matrix.transpose_apply]
      split_ifs with hs
      · simp [Matrix.one_apply, eq_comm]
      · simp only [Matrix.of_apply]
        by_cases hij : j = i
        · subst hij; simp
        · have hij' : i ≠ j := Ne.symm hij
          simp [hij, hij']
          ring
    have hHH : H * H = 1 := by
      dsimp only [H, householderRealMat]
      split_ifs with hs
      · exact Matrix.one_mul 1
      · ext i k
        rw [Matrix.mul_apply, Matrix.one_apply]
        simp only [Matrix.of_apply]
        have hexp (j : Fin d) :
            ((if i = j then 1 else 0) - 2 / s * w i * w j) *
                ((if j = k then 1 else 0) - 2 / s * w j * w k) =
              (if i = j then if j = k then 1 else 0 else 0) -
                (if i = j then 2 / s * w j * w k else 0) -
                (if j = k then 2 / s * w i * w j else 0) +
                (4 / s ^ 2 * w i * w k) * (w j) ^ 2 := by
          by_cases hij : i = j
          · subst hij
            by_cases hjk : i = k
            · subst hjk; simp only [↓reduceIte]; ring
            · simp only [hjk, ↓reduceIte]; ring
          · by_cases hjk : j = k
            · subst hjk; simp only [hij, ↓reduceIte]; ring
            · simp only [hij, hjk, ↓reduceIte]; ring
        rw [Finset.sum_congr rfl fun j _ ↦ hexp j, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hs1 : (∑ j : Fin d, if i = j then if j = k then (1 : ℝ) else 0 else 0) =
            if i = k then 1 else 0 := by
          rw [sum_eq_single i (fun j hj ↦ ite_eq_right (Ne.symm hj)), ite_eq_left rfl]
        have hs2 : (∑ j : Fin d, if i = j then 2 / s * w j * w k else 0) =
            2 / s * w i * w k := by
          rw [sum_eq_single i (fun j hj ↦ ite_eq_right (Ne.symm hj)), ite_eq_left rfl]
        have hs3 : (∑ j : Fin d, if j = k then 2 / s * w i * w j else 0) =
            2 / s * w i * w k := by
          rw [sum_eq_single k (fun j hj ↦ ite_eq_right hj), ite_eq_left rfl]
        rw [hs1, hs2, hs3]
        change (if i = k then 1 else 0) - 2 / s * w i * w k - 2 / s * w i * w k +
          4 / s ^ 2 * w i * w k * s = if i = k then 1 else 0
        field_simp [hs]
        ring
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar : star (H.map Complex.ofRealHom) = Hᵀ.map Complex.ofRealHom := by
      ext i j
      simp
    rw [hstar, hsym, ← Matrix.map_mul, hHH]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]⟩
theorem householderPrepUnitary_mulVec_zero {d : ℕ} [NeZero d] (u : Fin d → ℝ) (hu : (∑ i : Fin d,
    (u i) ^ 2) = 1) : (householderPrepUnitary u hu).1 *ᵥ Pi.single 0 1 = fun i ↦ (u i : ℂ) := by
  open Classical in
  let e₀ : Fin d → ℝ := Pi.single 0 1; let w : Fin d → ℝ := fun i ↦ e₀ i - u i
  let s : ℝ := ∑ i : Fin d, (w i) ^ 2
  have hs_eq : s = 2 * w 0 := by
    have he0_sq : (∑ i : Fin d, (e₀ i) ^ 2) = 1 := by
      rw [sum_eq_single 0 (fun i hi ↦ by simp [e₀, hi])]; simp [e₀]
    have he0_u : (∑ i : Fin d, 2 * e₀ i * u i) = 2 * u 0 := by
      rw [sum_eq_single 0 (fun i hi ↦ by simp [e₀, hi])]; simp [e₀]
    have hexp : s = (∑ i, (e₀ i) ^ 2) - (∑ i, 2 * e₀ i * u i) + (∑ i, (u i) ^ 2) := by
      dsimp only [s, w]; rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hexp, he0_sq, he0_u, hu]; dsimp only [w, e₀]; rw [Pi.single_eq_same]; ring
  funext i; rw [Matrix.mulVec_single_one]
  dsimp only [householderPrepUnitary, Matrix.col_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe]
  congr 1; unfold householderRealMat
  change (if s = 0 then (1 : Matrix (Fin d) (Fin d) ℝ)
    else Matrix.of fun a b ↦ (if a = b then 1 else 0) - 2 / s * w a * w b) i 0 = u i
  by_cases hs : s = 0
  · rw [ite_eq_left hs]
    have hw0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (w j))).mp hs
    have hwi : w i = 0 := sq_eq_zero_iff.mp (hw0 i (Finset.mem_univ i))
    have hui : u i = e₀ i := (by dsimp only [w] at hwi; linarith); rw [hui]
    by_cases hi : i = 0 <;> simp [e₀, Matrix.one_apply, hi]
  · rw [ite_eq_right hs, Matrix.of_apply]
    have hei : (if i = (0 : Fin d) then (1 : ℝ) else 0) = e₀ i := by
      by_cases hi : i = 0 <;> simp [e₀, hi]
    rw [hei]
    have h1 : 2 / s * w i * w 0 = w i := by
      have hw0_ne : w 0 ≠ 0 := fun h0 ↦ hs (by rw [hs_eq, h0, mul_zero]); rw [hs_eq]
      field_simp [hw0_ne]
    rw [h1]; dsimp only [w]; ring
/-! ## 3. Deflated Phase Action & Parallel Multi-Hit Readout on `workReg` -/
theorem sDiagM_mulVec_liftSymVec {n m : ℕ} (R : Finset (Fin (2 ^ n))) (v : SymSubset (2 ^ n) m →
    ℝ) : sDiagM n m R *ᵥ liftSymVec n m v = liftSymVec n m (symZVec R v) := by
  rw [liftSymVec_eq_sum_single, liftSymVec_eq_sum_single]
  have hsingle (E : SymSubset (2 ^ n) m) : sDiagM n m R *ᵥ Pi.single (subsetWorkIdx n m E) 1 =
        ((-1 : ℂ) ^ (E.1 ∩ R).card) • Pi.single (subsetWorkIdx n m E) 1 := by
    funext z; rw [sDiagM, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hz : z = subsetWorkIdx n m E
    · subst hz; rw [Pi.single_eq_same, mul_one, mul_one]
      have hflag (j : Fin m) : (splitBasisEquiv n 1 ((slotReg n m j).extractIndex (subsetWorkIdx n
        m E))).2 = 0 := slotFlag_eq_zero _ (env_subsetWorkIdx n m E) j
      have had (j : Fin m) : (splitBasisEquiv n 1 ((slotReg n m j).extractIndex (subsetWorkIdx n m
        E))).1 = E.1.orderEmbOfFin E.2 j := slotAddr_subsetWorkIdx n m E j
      have hprod : (∏ j : Fin m, slotDiag n R ((slotReg n m j).extractIndex (subsetWorkIdx n m
        E))) = ∏ j : Fin m, if E.1.orderEmbOfFin E.2 j ∈ R then (-1 : ℂ) else 1 := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_; dsimp only [slotDiag]; rw [had j, hflag j]; simp
      rw [hprod]
      have himg : (∏ j : Fin m, if E.1.orderEmbOfFin E.2 j ∈ R then (-1 : ℂ) else 1) = ∏ x ∈ E.1,
        if x ∈ R then (-1 : ℂ) else 1 := by
        conv_rhs => rw [← image_orderEmbOfFin_symSubset E]
        rw [Finset.prod_image (fun i _ j _ hij ↦ (E.1.orderEmbOfFin E.2).injective hij)]
      rw [himg, ← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.prod_const]
    · simp [Pi.single_eq_of_ne hz]
  rw [Matrix.mulVec_sum]; refine Finset.sum_congr rfl fun E _ ↦ ?_
  rw [Matrix.mulVec_smul, hsingle E, smul_smul]; congr 1; dsimp only [symZVec]; push_cast; ring
/-- Distinct marked addresses read out from all `m` parallel slots of `w`. -/
def markedSlotAddrs (n m : ℕ) (w : Fin (2 ^ (m * (n + 1)))) : List (Fin (2 ^ n)) :=
  (((List.finRange m).filter fun j ↦ slotFlag n m w j = 1).map (slotAddr n m w)).dedup
theorem nodup_markedSlotAddrs (n m : ℕ) (w : Fin (2 ^ (m * (n + 1)))) :
    (markedSlotAddrs n m w).Nodup :=
  List.nodup_dedup _
theorem markedSlotAddrs_parallelMarkPerm_subsetWorkIdx {n m : ℕ}
    (R : Finset (Fin (2 ^ n))) (E : SymSubset (2 ^ n) m) :
    let w' := parallelMarkPerm n m R (subsetWorkIdx n m E)
    (∀ x ∈ markedSlotAddrs n m w', x ∈ R) ∧ (markedSlotAddrs n m w').length = (E.1 ∩ R).card := by
  intro w'; let f := E.1.orderEmbOfFin E.2
  have hslt (j : Fin m) : splitBasisEquiv n 1 ((slotReg n m j).extractIndex w') =
        (f j, if f j ∈ R then 1 else 0) := by
    rw [extractIndex_slotReg_parallelMarkPerm, splitBasisEquiv_markPerm, show (splitBasisEquiv n 1
      ((slotReg n m j).extractIndex (subsetWorkIdx n m E))).1 = f j from slotAddr_subsetWorkIdx n
      m E j, show (splitBasisEquiv n 1 ((slotReg n m j).extractIndex (subsetWorkIdx n m E))).2 = 0
      from slotFlag_eq_zero _ (env_subsetWorkIdx n m E) j, zero_add]
  have hfl (j : Fin m) : (slotFlag n m w' j = 1) ↔ f j ∈ R := (by simp [slotFlag, hslt j])
  have had (j : Fin m) : slotAddr n m w' j = f j := (by simp [slotAddr, hslt j])
  let L := ((List.finRange m).filter fun j ↦ decide (slotFlag n m w' j = 1)).map (slotAddr n m w')
  have hmark_eq : markedSlotAddrs n m w' = L.dedup := rfl
  have hL_nodup : L.Nodup := by
    refine ((List.nodup_finRange m).filter _).map ?_; intro j₁ j₂ hj; rw [had j₁, had j₂] at hj
    exact f.injective hj
  have hmem_L (x : Fin (2 ^ n)) : x ∈ L ↔ x ∈ E.1 ∩ R := by
    simp only [L, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, hfl, had, Finset.mem_inter]
    constructor
    · rintro ⟨j, hjR, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem E.1 E.2 j, hjR⟩
    · rintro ⟨hxE, hxR⟩
      rw [← image_orderEmbOfFin_symSubset E, Finset.mem_image] at hxE; rcases hxE with ⟨j, _, rfl⟩
      exact ⟨j, hxR, rfl⟩
  have hcard_nodup (l : List (Fin (2 ^ n))) (hl : l.Nodup) : l.toFinset.card = l.length := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rcases List.nodup_cons.mp hl with ⟨ha, hl'⟩; simp [ha, ih hl']
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · rw [hmark_eq, List.mem_dedup, hmem_L] at hx; exact (Finset.mem_inter.mp hx).2
  · rw [hmark_eq, hL_nodup.dedup, ← hcard_nodup L hL_nodup]; congr 1
    ext x; rw [List.mem_toFinset, hmem_L]
/-! ## 4. Turnkey Renewal Specification & Single-Pass Walk Engine -/
/-- QHL-free multi-stage Johnson walk renewal specification on `groverGrid` cell `(m, k)`. -/
structure JohnsonWalkSpec (m k : ℕ) where
  useWalk : ℕ → Bool
  n0 : ℕ
  hn0 : 600 ≤ n0
  stages : (n r : ℕ) → List (ℕ × SymOrthogonal (2 ^ n) m)
  V : ℕ → ℝ
  hV0 : V 0 = 0
  hV_mono : ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ k → V r₁ ≤ V r₂
  hV_eig : ∀ r : ℕ, 1 ≤ r → r ≤ k → (r = 1 ∨ useWalk r = false) →
    (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) < V r - V (r - 1)
  pLo : ℕ → ℕ → ℝ
  hpLo_nonneg : ∀ r w, 0 ≤ pLo r w
  hpLo_sum_pos : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true →
    0 < ∑ w ∈ Finset.Icc 1 (min m r), pLo r w
  tauSum : ℕ → ℝ
  C_step : ℝ
  hstages_len : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    (stagesQueryCount (stages n r) : ℝ) ≤ tauSum r * √(2 ^ n : ℝ) + C_step
  hpLo_le : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    ∀ R : Finset (Fin (2 ^ n)), R.card = r →
    ∀ w ∈ Finset.Icc 1 (min m r),
      pLo r w ≤ symHitProb R (evalSymStages R (stages n r) (u0Vec (2 ^ n) m)) w
  hdrift_lt : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true →
    tauSum r < ∑ w ∈ Finset.Icc 1 (min m r), pLo r w * (V r - V (r - w))
/-- QHL-free sparse-anchor multi-stage Johnson walk renewal specification on `groverGrid`
  cell
  `(m, k)` using a global upper cap `V_max` without requiring monotonicity of `V`. -/
structure JohnsonWalkSparseSpec (m k : ℕ) where
  useWalk : ℕ → Bool
  n0 : ℕ
  hn0 : 600 ≤ n0
  stages : (n r : ℕ) → List (ℕ × SymOrthogonal (2 ^ n) m)
  V : ℕ → ℝ
  V_max : ℝ
  hV0 : V 0 = 0
  hV_bounds : ∀ r : ℕ, r ≤ k → 0 ≤ V r ∧ V r ≤ V_max
  hV_eig : ∀ r : ℕ, 1 ≤ r → r ≤ k → (r = 1 ∨ useWalk r = false) →
    (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) < V r - V (r - 1)
  pLo : ℕ → ℕ → ℝ
  hpLo_nonneg : ∀ r w, 0 ≤ pLo r w
  hpLo_sum_pos : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true →
    0 < ∑ w ∈ Finset.Icc 1 (min m r), pLo r w
  tauSum : ℕ → ℝ
  C_step : ℝ
  hstages_len : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    (stagesQueryCount (stages n r) : ℝ) ≤ tauSum r * √(2 ^ n : ℝ) + C_step
  hpLo_le : ∀ n r : ℕ, n0 ≤ n → 2 ≤ r → r ≤ k → useWalk r = true →
    ∀ R : Finset (Fin (2 ^ n)), R.card = r →
    ∀ w ∈ Finset.Icc 0 (min m r),
      pLo r w ≤ symHitProb R (evalSymStages R (stages n r) (u0Vec (2 ^ n) m)) w
  hdrift_sparse_lt : ∀ r : ℕ, 2 ≤ r → r ≤ k → useWalk r = true →
    tauSum r + ∑ w ∈ Finset.Icc 0 (min m r), pLo r w * V (r - w) +
      (1 - ∑ w ∈ Finset.Icc 0 (min m r), pLo r w) * V_max < V r
end
public section
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation InnerProductSpace
private lemma jp01_validState_step {Var : Type} [DecidableEq Var] {n m k j j' : ℕ}
    {S : Finset (Fin (2 ^ n))} {P : QProg Var (2 ^ (m * (n + 1) + k * n))}
    {Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))} (hV : 𝔼[Δ, validObs n m k S j] = Δ.trace)
    (hwp : validObs n m k S j ≤ wp P (validObs n m k S j')) :
    let Δ' := (interp P).toStateFun Δ
    𝔼[Δ', validObs n m k S j'] = Δ'.trace ∧ stateMass Δ' = stateMass Δ := by
  intro Δ'
  have h1 : (Δ.trace : ℝ) ≤ 𝔼[Δ', validObs n m k S j'] := by
    rw [← hV, ← wp_expectation_eq]; exact expect_mono le_rfl hwp
  have h2 : 𝔼[Δ', validObs n m k S j'] ≤ (Δ'.trace : ℝ) := by
    rw [← expect_top Δ']; exact expect_mono le_rfl le_top
  have h3 : (Δ'.trace : ℝ) ≤ (Δ.trace : ℝ) := (by exact_mod_cast (interp P).trace_toStateFun_le Δ)
  refine ⟨by linarith, ?_⟩
  rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace,
    show (Δ'.trace : ℝ) = Δ.trace by linarith]
private theorem jp01_stageCostReal_le_linear_S0 {n m k r : ℕ} (hn : 600 ≤ n) (hm_grid : m ∈
    groverGrid) (hk_grid : k ∈ groverGrid) (hr1 : 1 ≤ r) (hrk : r ≤ k) : 0 ≤ stageCostReal n m r ∧
    stageCostReal n m r ≤ (π / 8 + 1 / 4) * √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) + 5 := by
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  have hr_hi : r ≤ 1024 := hrk.trans hk_hi
  have h2r_le : 2 * r ≤ 2 ^ n := by
    calc 2 * r ≤ 2 * 1024 := by omega
      _ ≤ 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hr_lt : r < 2 ^ n := (by omega); set p := oddFrac n m r; set K := subSchedule p
  have hp_pos : 0 < p := (oddFrac_pos_lt_one hm1 hr1 hr_lt).1
  set p₀ : ℝ := ((m : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)
  set S₀ : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))
  have hmr_pos : (0 : ℝ) < (m : ℝ) * (r : ℝ) := (by positivity)
  have hmr_le : (m : ℝ) * (r : ℝ) ≤ 16 ^ 5 := by
    have : m * r ≤ 1024 * 1024 := Nat.mul_le_mul hm_hi hr_hi
    calc (m : ℝ) * (r : ℝ) = ((m * r : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((1024 * 1024 : ℕ) : ℝ) := by exact_mod_cast this
      _ = 16 ^ 5 := by norm_num
  have h2n_ge : (16 ^ 150 : ℝ) ≤ (2 ^ n : ℝ) := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hS0_sq : S₀ ^ 2 = (2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)) := Real.sq_sqrt (by positivity)
  have hS0_sq_ge : (16 : ℝ) ^ 145 ≤ S₀ ^ 2 := by
    rw [hS0_sq, le_div_iff₀ hmr_pos]
    calc (16 : ℝ) ^ 145 * ((m : ℝ) * (r : ℝ))
        ≤ (16 : ℝ) ^ 145 * (16 : ℝ) ^ 5 := mul_le_mul_of_nonneg_left hmr_le (by positivity)
      _ = (16 : ℝ) ^ 150 := by norm_num
      _ ≤ (2 ^ n : ℝ) := h2n_ge
  have hS0_ge : (4 : ℝ) ^ 145 ≤ S₀ := by
    have h145 : ((4 : ℝ) ^ 145) ^ 2 = (16 : ℝ) ^ 145 := (by norm_num)
    nlinarith [Real.sqrt_nonneg ((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))]
  rcases oddFrac_sandwich (m := m) h2r_le with ⟨hp_lo, hp_hi⟩; change p₀ * (1 - p₀) ≤ p at hp_lo
  change p ≤ p₀ at hp_hi
  have hp0_inv : p₀ * S₀ ^ 2 = 1 := (by rw [hS0_sq]; dsimp only [p₀]; field_simp [hmr_pos.ne'])
  have h1_div_sqrt_ge : S₀ ≤ 1 / √p := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hp_pos)]; have hle : √p ≤ √p₀ := Real.sqrt_le_sqrt hp_hi
    have hmul : S₀ * √p₀ = 1 := by
      have hsq : (S₀ * √p₀) ^ 2 = 1 := by
        rw [mul_pow, hS0_sq, Real.sq_sqrt (by positivity)]; dsimp only [p₀]
        field_simp [hmr_pos.ne']
      nlinarith [show 0 ≤ S₀ * √p₀ by positivity]
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq hmul
  have hs16 : 16 ≤ 1 / √p := by
    calc (16 : ℝ) ≤ (4 : ℝ) ^ 145 := by norm_num
      _ ≤ S₀ := hS0_ge
      _ ≤ 1 / √p := h1_div_sqrt_ge
  have h1_div_sqrt_le : 1 / √p ≤ S₀ + 1 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hp_pos)]
    suffices hsq : 1 ≤ ((S₀ + 1) * √p) ^ 2 by nlinarith [show 0 ≤ (S₀ + 1) * √p by positivity]
    rw [mul_pow, Real.sq_sqrt hp_pos.le]
    have hp0_eq : p₀ = 1 / S₀ ^ 2 := (by rw [eq_div_iff (by positivity)]; exact hp0_inv)
    have hpoly : 1 ≤ (S₀ + 1) ^ 2 * (p₀ * (1 - p₀)) := by
      rw [hp0_eq, ← sub_nonneg]; have hS4 : (0 : ℝ) < S₀ ^ 4 := (by positivity)
      have hnum : (S₀ + 1) ^ 2 * (1 / S₀ ^ 2 * (1 - 1 / S₀ ^ 2)) - 1 =
            (2 * S₀ ^ 3 - 2 * S₀ - 1) / S₀ ^ 4 := by
        field_simp [show S₀ ≠ 0 by positivity]; ring
      rw [hnum]; refine div_nonneg ?_ hS4.le
      have hS2 : (2 : ℝ) ≤ S₀ := le_trans (by norm_num) hS0_ge
      have hdecomp : 2 * S₀ ^ 3 - 2 * S₀ - 1 =
          (S₀ - 2) * (2 * S₀ ^ 2 + 4 * S₀ + 6) + 11 := by ring
      rw [hdecomp]; have hsub : 0 ≤ S₀ - 2 := (by linarith); positivity
    exact hpoly.trans (mul_le_mul_of_nonneg_left hp_lo (sq_nonneg _))
  obtain ⟨hhyps, hqbound⟩ := subSchedule_hyps_le hp_pos hs16
  have h1q_pos : 0 < 1 - subFailProb p K := sub_pos.mpr hhyps.2.2.2.2
  have hnn : 0 ≤ stageCostReal n m r := (by dsimp only [stageCostReal, p, K]; positivity)
  refine ⟨hnn, ?_⟩; have hπ_hi : π < 4 := Real.pi_lt_four; dsimp only [stageCostReal, p, K]
  have h1 : (π / 8 + 1 / 4) * (1 / √p) ≤ (π / 8 + 1 / 4) * (S₀ + 1) :=
    mul_le_mul_of_nonneg_left h1_div_sqrt_le (by positivity)
  linarith
private noncomputable def vecQuad {d : ℕ} (A : Operator d) (ψ : Fin d → ℂ) : ℂ := star ψ ⬝ᵥ (A *ᵥ ψ)
private lemma vecQuad_single {d : ℕ} (A : Operator d) (z : Fin d) :
    A z z = vecQuad A (Pi.single z 1) := by
  simp [vecQuad]
private lemma vecQuad_conj {d : ℕ} (U A : Operator d) (ψ : Fin d → ℂ) :
    vecQuad (Uᴴ * A * U) ψ = vecQuad A (U *ᵥ ψ) := by
  unfold vecQuad; rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]; set v := A *ᵥ (U *ᵥ ψ)
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
private lemma vecQuad_diagonal_sum_single {d : ℕ} {ι : Type*} [Fintype ι] (g : Fin d → ℂ) (v : ι →
    ℝ) (idx : ι → Fin d) (hinj : Function.Injective idx) : vecQuad (diagonal g) (∑ i : ι, (v i :
    ℂ) • Pi.single (idx i) 1) = ∑ i : ι, ((v i) ^ 2 : ℂ) * g (idx i) := by
  classical
  let ψ : Fin d → ℂ := ∑ i : ι, (v i : ℂ) • Pi.single (idx i) 1
  have hψ_at (i : ι) : ψ (idx i) = (v i : ℂ) := by
    simp only [ψ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [sum_eq_single i (fun j hj ↦ by simp [hinj.ne hj.symm])]; simp
  have hψ_out (z : Fin d) (hz : z ∉ Finset.univ.image idx) : ψ z = 0 := by
    simp only [ψ, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hne : z ≠ idx i := fun h ↦ hz (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩)
    simp [hne]
  unfold vecQuad; change ∑ z : Fin d, star (ψ z) * (diagonal g *ᵥ ψ) z = _
  simp only [mulVec_diagonal]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image idx))
    (fun z _ hz ↦ by simp [hψ_out z hz]), Finset.sum_image (fun i _ j _ h ↦ hinj h)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [hψ_at i, Complex.star_def, Complex.conj_ofReal]
  ring
private lemma workMemState_sum_left {W M : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin (2 ^ W) → ℂ)
    (φ : Fin (2 ^ M) → ℂ) : workMemState (∑ i ∈ s, f i) φ = ∑ i ∈ s, workMemState (f i) φ := by
  funext z; simp [workMemState, Finset.sum_apply, Finset.sum_mul]
private lemma workMemState_smul_left {W M : ℕ} (c : ℂ) (ψ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (c • ψ) φ = c • workMemState ψ φ := by
  funext z; dsimp only [workMemState, Pi.smul_apply, smul_eq_mul]; ring
private lemma workReg_eq_lowBlock (n m k : ℕ) :
    workReg n m (m * (n + 1) + k * n) (by omega) = lowBlock (m * (n + 1)) (k * n) := by
  ext i; simp
private lemma workMemReg_eq_whole (n m k : ℕ) :
    workMemReg n m k (m * (n + 1) + k * n) le_rfl = QRegister.whole (m * (n + 1) + k * n) := by
  ext i; simp
private lemma wp_deflatedOracle_vecQuad {Var : Type} [DecidableEq Var] {n m k : ℕ} {S : Finset
    (Fin (2 ^ n))} (active : Finset (Fin k)) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k *
    n))) (hsub : memSeen n k active μ ⊆ S) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)))
      (σ :
    Store Var) : vecQuad (((wp ((deflatedOracle (Var := Var) (n := n) (m := m) (k := k) (Q := m *
    (n + 1) + k * n) le_rfl active).compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1)
    (workMemState ψ (Pi.single μ 1)) = vecQuad ((Θ σ).1.1) (workMemState ((permutationUnitary
    (parallelMarkPerm n m (S \ memSeen n k active μ))).1 *ᵥ ψ) (Pi.single μ 1)) := by
  unfold deflatedOracle; dsimp only [compile]
  rw [wp_qSeq, wp_qAssign, wp_qAssign, wp_phaseTag, qhlQAssign_val,
    qhlQAssign_val, vecQuad_conj, vecQuad_conj]
  simp only [workFullReg, workReg_eq_lowBlock, workMemReg_eq_whole,
    QRegister.embedUnitary_compose, QRegister.whole_embedUnitary]
  rw [QRegister.embedUnitary_val (lowBlock (m * (n + 1)) (k * n)),
    unmark_mul_parallelOracle_workMemState active ψ μ hsub,
    fullReg_embedUnitary_eq_permutationUnitary]
private lemma wp_deflatedPhaseStep_vecQuad {Var : Type} [DecidableEq Var] {n m k : ℕ} {S : Finset
    (Fin (2 ^ n))} (active : Finset (Fin k)) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k *
    n))) (hsub : memSeen n k active μ ⊆ S) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)))
      (σ :
    Store Var) : vecQuad (((wp ((deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k) (Q :=
    m * (n + 1) + k * n) le_rfl active).compile qAssign (groverParallelMarkingOracle m S)) Θ)
    σ).1.1) (workMemState ψ (Pi.single μ 1)) = vecQuad ((Θ σ).1.1) (workMemState (sDiagM n m (S \
    memSeen n k active μ) *ᵥ ψ) (Pi.single μ 1)) := by
  unfold deflatedPhaseStep deflatedOracle; dsimp only [compile]
  rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qAssign, wp_qAssign, wp_qAssign, wp_qAssign,
    wp_phaseTag, wp_phaseTag, wp_phaseTag]
  simp only [qhlQAssign_val, vecQuad_conj, workFullReg, workReg_eq_lowBlock,
    workMemReg_eq_whole, QRegister.embedUnitary_compose, QRegister.whole_embedUnitary]
  rw [QRegister.embedUnitary_val (lowBlock (m * (n + 1)) (k * n)),
    QRegister.embedUnitary_val (lowBlock (m * (n + 1)) (k * n))]
  have hmat := deflatedPhaseMat_mulVec_workMemState active ψ μ hsub; dsimp only at hmat
  rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmat]
private lemma costBound_mapAndMeasureLow {Var : Type} [DecidableEq Var] (res : Var) {W M O : ℕ} (g
    : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M))) {oracle : Unitary (2 ^ O)} (hor : IsRealMatrix
    oracle.1) : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle) ((mapAndMeasureLow res
    W M O g).compile qAssign oracle) 0 := by
  unfold mapAndMeasureLow; dsimp only [compile]
  have hmeas : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
      (measureRegister res (lowBlock W M)) 0 := by
    simpa [measureRegister, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) (CostModel.ofEmbeddedOracle oracle) res _
  simpa using (costBound_qMap (Var := Var) res g hor).seq hmeas
private lemma wp_mapAndMeasureLow {Var : Type} [DecidableEq Var] (res : Var) {W M O : ℕ} (g : Fin
    (2 ^ (W + M)) → Fin (2 ^ (W + M))) (oracle : Unitary (2 ^ O)) (H : ℤ → Operator (2 ^ (W + M)))
    (Φ : CQAssertion (Store Var) (2 ^ (W + M))) (hΦ : ∀ τ, (Φ τ).1.1 = H (τ res)) (σ : Store Var) :
      ((wp
    ((mapAndMeasureLow res W M O g).compile qAssign oracle) Φ) σ).1.1 = diagonal (fun z : Fin (2 ^
    (W + M)) ↦ H (Int.ofNat ((lowHighEquiv W M (g z)).1).val) (g z) (g z)) := by
  unfold mapAndMeasureLow; dsimp only [compile]; rw [wp_qSeq]
  let M_meas : Operator (2 ^ (W + M)) := ∑ o : Fin (2 ^ W), (lowBlock W M).basisOutcomeProjector
    o * H (Int.ofNat o.val) * (lowBlock W M).basisOutcomeProjector o
  have hmeas (τ : Store Var) : ((wp (measureRegister res (lowBlock W M)) Φ) τ).1.1 = M_meas := by
    rw [wp_measureRegister]; exact Finset.sum_congr rfl fun o _ ↦ by rw [hΦ]; simp [Store.subst]
  rw [wp_qMap res g oracle (fun _ ↦ M_meas) _ hmeas σ]; refine congrArg diagonal (funext fun z ↦ ?_)
  dsimp only [M_meas]; rw [Matrix.sum_apply]; let o₀ : Fin (2 ^ W) := (lowHighEquiv W M (g z)).1
  rw [sum_eq_single o₀ (fun o ho ↦ by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
      extractIndex_lowBlock, ite_eq_right (Ne.symm ho), mul_zero])]
  rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
    extractIndex_lowBlock, ite_eq_left rfl, one_mul, mul_one]
private def PureUnitaryProg {Var : Type} {d : ℕ} : QProg Var d → Prop
  | .skip => True
  | .qAssign _ => True
  | .qSeq c₁ c₂ => PureUnitaryProg c₁ ∧ PureUnitaryProg c₂
  | _ => False
private lemma wp_eq_of_pureUnitary {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {P : QProg
    Var d} (hP : PureUnitaryProg P) {Θ₁ Θ₂ : CQAssertion (Store Var) d} {σ₁ σ₂ : Store Var} (h : Θ₁
      σ₁ =
    Θ₂ σ₂) : wp P Θ₁ σ₁ = wp P Θ₂ σ₂ := by
  induction P generalizing Θ₁ Θ₂ with
  | «skip» => exact h
  | qAssign U =>
    rw [wp_qAssign, wp_qAssign, CQAssertion.qAssign_apply, CQAssertion.qAssign_apply, h]
  | qSeq c₁ c₂ ih₁ ih₂ => rw [wp_qSeq, wp_qSeq]; exact ih₁ hP.1 (ih₂ hP.2 h)
  | _ => cases hP
private lemma sum_sq_symInjMat_mulVec (n m : ℕ) (v : SymSubset (2 ^ n) m → ℝ) : (∑ z : Fin (2 ^
    (m * (n + 1))), ((symInjMat n m *ᵥ v) z) ^ 2) = ∑ E : SymSubset (2 ^ n) m, (v E) ^ 2 := by
  let J := symInjMat n m
  have h1 : (∑ z, ((J *ᵥ v) z) ^ 2) = (J *ᵥ v) ⬝ᵥ (J *ᵥ v) := (by simp [dotProduct, sq])
  have h2 : (J *ᵥ v) ⬝ᵥ (J *ᵥ v) = v ⬝ᵥ ((Jᵀ * J) *ᵥ v) := by
    rw [← mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h1, h2, symInjMat_transpose_mul_self, Matrix.one_mulVec]; simp [dotProduct, sq]
private noncomputable def johnsonSingleIter {Var : Type} (n m k s : ℕ)
    (D : SymOrthogonal (2 ^ n) m) : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedPhaseStep le_rfl (memPrefix k s))
    (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (liftSymOrthogonal n m D))))
private noncomputable def johnsonStageLoop {Var : Type} (n m k s : ℕ)
    (D : SymOrthogonal (2 ^ n) m) : ℕ → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | 0 => .skip
  | K + 1 => .seq (johnsonSingleIter n m k s D) (johnsonStageLoop n m k s D K)
private noncomputable def johnsonStagesProg {Var : Type} (n m k s : ℕ) :
    List (ℕ × SymOrthogonal (2 ^ n) m) → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | (K, D) :: rest => .seq (johnsonStageLoop n m k s D K) (johnsonStagesProg n m k s rest)
private lemma pureUnitary_deflatedOracle {Var : Type} {n m k : ℕ}
    (active : Finset (Fin k)) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    PureUnitaryProg ((deflatedOracle (Var := Var) (n := n) (m := m) (k := k)
      (Q := m * (n + 1) + k * n) le_rfl active).compile qAssign oracle) :=
  ⟨trivial, trivial⟩
private lemma pureUnitary_deflatedPhaseStep {Var : Type} {n m k : ℕ}
    (active : Finset (Fin k)) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    PureUnitaryProg ((deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
      (Q := m * (n + 1) + k * n) le_rfl active).compile qAssign oracle) :=
  ⟨trivial, pureUnitary_deflatedOracle active oracle, trivial⟩
private lemma pureUnitary_johnsonStagesProg {Var : Type} {n m k s : ℕ}
    (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    PureUnitaryProg ((johnsonStagesProg (Var := Var) n m k s stages).compile qAssign oracle) := by
  have hloop (D : SymOrthogonal (2 ^ n) m) : ∀ K : ℕ,
      PureUnitaryProg ((johnsonStageLoop (Var := Var) n m k s D K).compile qAssign oracle) := by
    intro K
    induction K with
    | zero => trivial
    | succ K ih => exact ⟨⟨pureUnitary_deflatedPhaseStep _ oracle, trivial⟩, ih⟩
  induction stages with
  | nil => trivial
  | cons hd tl ih => exact ⟨hloop hd.2 hd.1, ih⟩
private lemma costBound_johnsonStagesProg {Var : Type} [DecidableEq Var] {n m k s : ℕ} (stages :
    List (ℕ × SymOrthogonal (2 ^ n) m)) (S : Finset (Fin (2 ^ n))) : CostBound (Var := Var)
    (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) ((johnsonStagesProg n m k s
    stages).compile qAssign (groverParallelMarkingOracle m S)) (stagesQueryCount stages) := by
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hiter (D : SymOrthogonal (2 ^ n) m) :
      CostBound (Var := Var) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        ((johnsonSingleIter n m k s D).compile qAssign (groverParallelMarkingOracle m S)) 1 := by
    unfold johnsonSingleIter; dsimp only [compile]
    simpa using (costBound_deflatedPhaseStep le_rfl (memPrefix k s) S).seq
      (costBound_qAssign_phaseTag hor
        ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (liftSymOrthogonal n m D)))
  have hloop (D : SymOrthogonal (2 ^ n) m) : ∀ K : ℕ,
      CostBound (Var := Var) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        ((johnsonStageLoop n m k s D K).compile qAssign (groverParallelMarkingOracle m S)) K := by
    intro K
    induction K with
    | zero => intro state; simp [johnsonStageLoop]
    | succ K ih =>
      unfold johnsonStageLoop; dsimp only [compile]
      simpa [Nat.cast_add, add_comm] using (hiter D).seq ih
  induction stages with
  | nil => intro state; simp [johnsonStagesProg, stagesQueryCount]
  | cons hd tl ih =>
    rcases hd with ⟨K, D⟩
    have hcnt : stagesQueryCount ((K, D) :: tl) = K + stagesQueryCount tl := rfl
    unfold johnsonStagesProg; dsimp only [compile]; rw [hcnt, Nat.cast_add]
    exact (hloop D K).seq ih
private lemma wp_johnsonStagesProg_vecQuad {Var : Type} [DecidableEq Var] {n m k s : ℕ} {S :
    Finset (Fin (2 ^ n))} (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) (v : SymSubset (2 ^ n) m →
    ℝ) (μ : Fin (2 ^ (k * n))) (hsub : memSeen n k (memPrefix k s) μ ⊆ S) (Θ : CQAssertion (Store
      Var) (2
    ^ (m * (n + 1) + k * n))) (σ : Store Var) : vecQuad (((wp ((johnsonStagesProg (Var := Var) n m
    k s stages).compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1) (workMemState
    (liftSymVec n m v) (Pi.single μ 1)) = vecQuad ((Θ σ).1.1) (workMemState (liftSymVec n m
    (evalSymStages (S \ memSeen n k (memPrefix k s) μ) stages v)) (Pi.single μ 1)) := by
  let R := S \ memSeen n k (memPrefix k s) μ
  have hiter (D : SymOrthogonal (2 ^ n) m) (u : SymSubset (2 ^ n) m → ℝ) (Ψ : CQAssertion (Store
    Var) (2 ^
    (m * (n + 1) + k * n))) : vecQuad (((wp ((johnsonSingleIter (Var := Var) n m k s D).compile
    qAssign (groverParallelMarkingOracle m S)) Ψ) σ).1.1) (workMemState (liftSymVec n m u)
    (Pi.single μ 1)) = vecQuad ((Ψ σ).1.1) (workMemState (liftSymVec n m (D.1 *ᵥ symZVec R u))
    (Pi.single μ 1)) := by
    unfold johnsonSingleIter; dsimp only [compile]
    rw [wp_qSeq, wp_deflatedPhaseStep_vecQuad (memPrefix k s) _ μ hsub,
      sDiagM_mulVec_liftSymVec, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      vecQuad_conj, QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      liftSymOrthogonal_mulVec]
  have hloop (D : SymOrthogonal (2 ^ n) m) : ∀ (K : ℕ) (u : SymSubset (2 ^ n) m → ℝ) (Ψ :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))), vecQuad (((wp ((johnsonStageLoop (Var :=
      Var) n
    m k s D K).compile qAssign (groverParallelMarkingOracle m S)) Ψ) σ).1.1) (workMemState
    (liftSymVec n m u) (Pi.single μ 1)) = vecQuad ((Ψ σ).1.1) (workMemState (liftSymVec n m
    (evalSymStage R D.1 K u)) (Pi.single μ 1)) := by
    intro K
    induction K with
    | zero => intro u Ψ; rfl
    | succ K ih =>
      intro u Ψ; unfold johnsonStageLoop; dsimp only [compile]
      rw [wp_qSeq, hiter D u _, ih, evalSymStage]
  induction stages generalizing v with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨K, D⟩; unfold johnsonStagesProg; dsimp only [compile]
    rw [wp_qSeq, hloop D K v _, ih, evalSymStages]
private lemma markedSlotAddrs_length_lt_pow (n m : ℕ) (w : Fin (2 ^ (m * (n + 1)))) :
    (markedSlotAddrs n m w).length < 2 ^ (m * (n + 1)) := by
  have hdedup : ∀ l : List (Fin (2 ^ n)), l.dedup.length ≤ l.length := fun l ↦ by
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.dedup_cons]; split_ifs <;> simp only [List.length_cons] <;> omega
  have h1 : (markedSlotAddrs n m w).length ≤ m := by
    unfold markedSlotAddrs
    calc ((((List.finRange m).filter _).map _).dedup).length
        ≤ (((List.finRange m).filter _).map _).length := hdedup _
      _ = ((List.finRange m).filter _).length := List.length_map _
      _ ≤ (List.finRange m).length := List.length_filter_le _ _
      _ = m := List.length_finRange
  have hpow : ∀ a : ℕ, a < 2 ^ a := fun a ↦ by
    induction a with
    | zero => norm_num
    | succ a ih =>
      calc a + 1 < 2 ^ a + 2 ^ a := by omega
        _ = 2 ^ (a + 1) := by ring
  have h2 : m < 2 ^ m := hpow m
  have h3 : 2 ^ m ≤ 2 ^ (m * (n + 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right m (Nat.succ_pos n))
  omega
private def hitCodeFn (n m k : ℕ)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) : Fin (2 ^ (m * (n + 1) + k * n)) :=
  let wm := lowHighEquiv (m * (n + 1)) (k * n) z
  (lowHighEquiv (m * (n + 1)) (k * n)).symm
    (⟨(markedSlotAddrs n m wm.1).length, markedSlotAddrs_length_lt_pow n m wm.1⟩, wm.2)
private noncomputable def johnsonPassFront {Var : Type} (res : Var) (n m k s : ℕ)
    (hmN : m ≤ 2 ^ n) (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  let O := (n + 1) * m
  .seq (workReset res W M O) (.seq (.step (phaseTag ((lowBlock W M).embedUnitary
        (householderPrepUnitary (symInjMat n m *ᵥ u0Vec (2 ^ n) m)
          (by rw [sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hmN)))))
      (.seq (johnsonStagesProg n m k s stages) (.seq (deflatedOracle le_rfl (memPrefix k s))
          (.seq (.step (phaseTag (permutationUnitary (memWriteBatchPerm s (markedSlotAddrs n m)))))
            (mapAndMeasureLow res W M O (hitCodeFn n m k))))))
private lemma costBound_johnsonPassFront {Var : Type} [DecidableEq Var] (res : Var) {n m k s : ℕ}
    (hmN : m ≤ 2 ^ n) (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    ((johnsonPassFront res n m k s hmN stages).compile qAssign (groverParallelMarkingOracle m S))
    (stagesQueryCount stages + 1) := by
  have hor := isRealMatrix_groverParallelMarkingOracle m S; unfold johnsonPassFront workReset
  dsimp only [compile]
  have h0_rst := costBound_mapAndMeasureLow (Var := Var) res (resetWorkFn (m * (n + 1)) (k * n)) hor
  have h0_prep := costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
      (householderPrepUnitary (symInjMat n m *ᵥ u0Vec (2 ^ n) m)
        (by rw [sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hmN)))
  have h_st := costBound_johnsonStagesProg (Var := Var) (k := k) (s := s) stages S
  have h_or := costBound_deflatedOracle (Var := Var)
    (Q := m * (n + 1) + k * n) le_rfl (memPrefix k s) S
  have h0_wr := costBound_qAssign_phaseTag (Var := Var) hor
    (permutationUnitary (memWriteBatchPerm (k := k) s (markedSlotAddrs n m)))
  have h0_ms := costBound_mapAndMeasureLow (Var := Var) res (hitCodeFn n m k) hor
  simpa [Nat.cast_add] using h0_rst.seq (h0_prep.seq (h_st.seq (h_or.seq (h0_wr.seq h0_ms))))
private lemma wp_johnsonPassFront_diag {Var : Type} [DecidableEq Var] (res : Var) {n m k s : ℕ}
    (hmN : m ≤ 2 ^ n) (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) (S : Finset (Fin (2 ^ n))) (G
    : ℤ → Fin (2 ^ (k * n)) → ℝ) (Φ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (hΦ : ∀ τ
      :
    Store Var, (Φ τ).1.1 = diagonal (fun z ↦ (G (τ res) (lowHighEquiv (m * (n + 1)) (k * n) z).2 :
    ℂ))) (σ : Store Var) : ∃ d_out : Fin (2 ^ (m * (n + 1) + k * n)) → ℂ, ((wp ((johnsonPassFront
    res n m k s hmN stages).compile qAssign (groverParallelMarkingOracle m S)) Φ) σ).1.1 =
    diagonal d_out ∧ ∀ z : Fin (2 ^ (m * (n + 1) + k * n)),
        let μ := (lowHighEquiv (m * (n + 1)) (k * n) z).2
        MemPrefixValid S s μ →
          let R := S \ memSeen n k (memPrefix k s) μ
          let v_fin := evalSymStages R stages (u0Vec (2 ^ n) m)
          d_out z = ∑ E : SymSubset (2 ^ n) m, ((v_fin E) ^ 2 : ℂ) * (G (Int.ofNat (E.1 ∩ R).card)
              ((addrEquiv n k).symm (addrEquiv n k μ + batchDelta s (markedSlotAddrs n m)
                  (parallelMarkPerm n m R (subsetWorkIdx n m E)))) : ℂ) := by
  let W := m * (n + 1); let M := k * n; let O := (n + 1) * m
  let oracle := groverParallelMarkingOracle m S
  let P_ms : QProg Var (2 ^ (W + M)) :=
    (mapAndMeasureLow res W M O (hitCodeFn n m k)).compile qAssign oracle
  let c_u : OracleCirc Var (W + M) O :=
    .seq (.step (phaseTag ((lowBlock W M).embedUnitary
        (householderPrepUnitary (symInjMat n m *ᵥ u0Vec (2 ^ n) m)
          (by rw [sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hmN)))))
      (.seq (johnsonStagesProg n m k s stages) (.seq (deflatedOracle le_rfl (memPrefix k s))
          (.step (phaseTag (permutationUnitary
            (memWriteBatchPerm (k := k) s (markedSlotAddrs n m)))))))
  let P_u : QProg Var (2 ^ (W + M)) := c_u.compile qAssign oracle
  let d_ms : Fin (2 ^ (W + M)) → ℂ := fun z' ↦
    (G (Int.ofNat (markedSlotAddrs n m (lowHighEquiv W M z').1).length) (lowHighEquiv W M z').2 : ℂ)
  have hms_mat (τ : Store Var) : ((wp P_ms Φ) τ).1.1 = diagonal d_ms := by
    rw [wp_mapAndMeasureLow res (hitCodeFn n m k) oracle
      (fun r_val ↦ diagonal (fun z' ↦ (G r_val (lowHighEquiv W M z').2 : ℂ))) Φ hΦ τ]
    refine congrArg diagonal (funext fun z' ↦ ?_); rw [Matrix.diagonal_apply_eq]
    dsimp only [hitCodeFn, d_ms]; rw [Equiv.apply_symm_apply]
  have hPu : PureUnitaryProg P_u := by
    dsimp only [P_u, c_u, compile]
    exact ⟨trivial, pureUnitary_johnsonStagesProg stages oracle,
      pureUnitary_deflatedOracle _ oracle, trivial⟩
  let M_in : Operator (2 ^ (W + M)) := ((wp P_u (wp P_ms Φ)) σ).1.1
  let c_tail : OracleCirc Var (W + M) O :=
    .seq (.step (phaseTag ((lowBlock W M).embedUnitary
        (householderPrepUnitary (symInjMat n m *ᵥ u0Vec (2 ^ n) m)
          (by rw [sum_sq_symInjMat_mulVec]; exact sum_sq_u0Vec hmN)))))
      (.seq (johnsonStagesProg n m k s stages) (.seq (deflatedOracle le_rfl (memPrefix k s))
          (.seq (.step (phaseTag (permutationUnitary
              (memWriteBatchPerm (k := k) s (markedSlotAddrs n m)))))
            (mapAndMeasureLow res W M O (hitCodeFn n m k)))))
  have hinner (τ : Store Var) : ((wp (c_tail.compile qAssign oracle) Φ) τ).1.1 = M_in := by
    have hwp_eq : wp (c_tail.compile qAssign oracle) Φ = wp P_u (wp P_ms Φ) := by
      dsimp only [c_tail, P_u, c_u, P_ms, compile]; simp only [wp_qSeq]
    rw [hwp_eq]
    have heq_ms : wp P_ms Φ τ = wp P_ms Φ σ :=
      Subtype.ext (HermitianMat.ext ((hms_mat τ).trans (hms_mat σ).symm))
    exact congrArg (fun x ↦ x.1.1) (wp_eq_of_pureUnitary hPu heq_ms)
  refine ⟨fun z ↦ M_in (resetWorkFn W M z) (resetWorkFn W M z), ?_, fun z hval ↦ ?_⟩
  · unfold johnsonPassFront workReset
    change (((wp ((mapAndMeasureLow res W M O (resetWorkFn W M)).compile qAssign oracle ;;
      c_tail.compile qAssign oracle) Φ) σ).1.1) = _
    rw [wp_qSeq, wp_mapAndMeasureLow res (resetWorkFn W M) oracle (fun _ ↦ M_in) _ hinner σ]
  · let μ := (lowHighEquiv W M z).2; let R := S \ memSeen n k (memPrefix k s) μ
    let v_fin := evalSymStages R stages (u0Vec (2 ^ n) m)
    have hsub : memSeen n k (memPrefix k s) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
    dsimp only [resetWorkFn]
    rw [vecQuad_single M_in ((lowHighEquiv W M).symm (0, μ)), ← workMemState_single]
    dsimp only [M_in, P_u, c_u, compile]
    rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      vecQuad_conj, QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      householderPrepUnitary_mulVec_zero]
    change vecQuad _ (workMemState (liftSymVec n m (u0Vec (2 ^ n) m)) (Pi.single μ 1)) = _
    rw [wp_johnsonStagesProg_vecQuad stages _ μ hsub,
      wp_deflatedOracle_vecQuad (memPrefix k s) _ μ hsub]
    change vecQuad _ (workMemState ((permutationUnitary (parallelMarkPerm n m R)).1 *ᵥ liftSymVec
      n m v_fin) (Pi.single μ 1)) = _
    let w_E (E : SymSubset (2 ^ n) m) : Fin (2 ^ W) :=
      parallelMarkPerm n m R (subsetWorkIdx n m E)
    let μ_E (E : SymSubset (2 ^ n) m) : Fin (2 ^ M) :=
      (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s (markedSlotAddrs n m) (w_E E))
    let idx (E : SymSubset (2 ^ n) m) : Fin (2 ^ (W + M)) :=
      (lowHighEquiv W M).symm (w_E E, μ_E E)
    have hinj : Function.Injective idx := fun E₁ E₂ h ↦ by
      have hw : w_E E₁ = w_E E₂ := congrArg Prod.fst ((lowHighEquiv W M).symm.injective h)
      exact subsetWorkIdx_injective n m ((parallelMarkPerm n m R).injective hw)
    have hvec_eq : (permutationUnitary (memWriteBatchPerm (k := k) s (markedSlotAddrs n m))).1 *ᵥ
      workMemState ((permutationUnitary (parallelMarkPerm n m R)).1 *ᵥ liftSymVec n m v_fin)
      (Pi.single μ 1) = ∑ E : SymSubset (2 ^ n) m, (v_fin E : ℂ) • Pi.single (idx E) 1 := by
      rw [liftSymVec_eq_sum_single n m v_fin, Matrix.mulVec_sum, workMemState_sum_left,
        Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun E _ ↦ ?_
      rw [Matrix.mulVec_smul, permutationUnitary_mulVec_single, workMemState_smul_left,
        Matrix.mulVec_smul]
      congr 1
      exact (permutationUnitary_memAddPerm_mulVec_single (batchDelta s (markedSlotAddrs n m))
        (w_E E) μ).trans (workMemState_single (w_E E) (μ_E E))
    rw [wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj, hvec_eq]
    change vecQuad (((wp P_ms Φ) σ).1.1)
      (∑ E : SymSubset (2 ^ n) m, (v_fin E : ℂ) • Pi.single (idx E) 1) = _
    rw [hms_mat σ, vecQuad_diagonal_sum_single d_ms v_fin idx hinj]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    congr 1; dsimp only [d_ms, idx]
    rw [Equiv.apply_symm_apply, (markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E).2]
private noncomputable def dispPre {Var : Type} (res : Var) (n m k : ℕ)
    (S : Finset (Fin (2 ^ n))) (s u : ℕ) :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
  fun τ ↦ if 1 ≤ τ res ∧ τ res ≤ (u : ℤ) then
    validObs n m k S (s + (τ res).toNat) τ
  else
    validObs n m k S s τ
private lemma wp_johnsonPassFront_dispPre {Var : Type} [DecidableEq Var] (res : Var) {n m k s : ℕ}
    (hmN : m ≤ 2 ^ n) (hs : s ≤ k) (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) {S : Finset (Fin
    (2 ^ n))} (hcard : S.card = k) : validObs (Var := Var) n m k S s ≤ wp ((johnsonPassFront res n
    m k s hmN stages).compile qAssign (groverParallelMarkingOracle m S)) (dispPre res n m k S s
    (min m (k - s))) := by
  intro σ; let b := min m (k - s)
  let G (r_val : ℤ) (μ' : Fin (2 ^ (k * n))) : ℝ := open Classical in if MemPrefixValid S (if 1 ≤
    r_val ∧ r_val ≤ (b : ℤ) then s + r_val.toNat else s) μ' then 1 else 0
  have hΦ (τ : Store Var) : (dispPre res n m k S s b τ).1.1 =
        diagonal (fun z ↦ (G (τ res) (lowHighEquiv (m * (n + 1)) (k * n) z).2 : ℂ)) := by
    dsimp only [dispPre]; split_ifs with h
    · dsimp only [validObs]; rw [realDiagObs_mat]; refine congrArg diagonal (funext fun z ↦ ?_)
      dsimp only [validInd, G]; rw [ite_eq_left h]
    · dsimp only [validObs]; rw [realDiagObs_mat]; refine congrArg diagonal (funext fun z ↦ ?_)
      dsimp only [validInd, G]; rw [ite_eq_right h]
  obtain ⟨d_out, hmat, hd_valid⟩ :=
    wp_johnsonPassFront_diag res hmN stages S G (dispPre res n m k S s b) hΦ σ
  have hbnd := observable_diag_real_bounds _ d_out hmat
  have hmat_re : ((wp ((johnsonPassFront res n m k s hmN stages).compile qAssign
      (groverParallelMarkingOracle m S)) (dispPre res n m k S s b)) σ).1.1 =
      diagonal (fun z ↦ ((d_out z).re : ℂ)) := by
    rw [hmat]; exact congrArg diagonal (funext fun z ↦ (hbnd z).1)
  refine realDiagObs_le_of_mat (fun z ↦ (hbnd z).2.1) (fun z ↦ (hbnd z).2.2) hmat_re fun z ↦ ?_
  dsimp only [validInd]
  open Classical in
  by_cases hval : MemPrefixValid S s (lowHighEquiv (m * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hval]; let μ := (lowHighEquiv (m * (n + 1)) (k * n) z).2
    let R := S \ memSeen n k (memPrefix k s) μ; have hseen := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = k - s := by
      dsimp only [R, μ]; rw [Finset.card_sdiff_of_subset hseen.2, hcard, hseen.1]
    have h1 : d_out z = 1 := by
      rw [hd_valid z hval]
      have hterm (E : SymSubset (2 ^ n) m) : (G (Int.ofNat (E.1 ∩ R).card)
            ((addrEquiv n k).symm (addrEquiv n k μ + batchDelta s (markedSlotAddrs n m)
                (parallelMarkPerm n m R (subsetWorkIdx n m E)))) : ℂ) = 1 := by
        have hm_mark := markedSlotAddrs_parallelMarkPerm_subsetWorkIdx R E
        have hc_m : (E.1 ∩ R).card ≤ m :=
          (Finset.card_le_card Finset.inter_subset_left).trans_eq E.2
        have hc_r : (E.1 ∩ R).card ≤ k - s :=
          (Finset.card_le_card Finset.inter_subset_right).trans_eq hR_card
        have hc_b : (E.1 ∩ R).card ≤ b := le_min hc_m hc_r
        have hidx_eq : (if 1 ≤ Int.ofNat (E.1 ∩ R).card ∧ Int.ofNat (E.1 ∩ R).card ≤ (b : ℤ) then
          s + (Int.ofNat (E.1 ∩ R).card).toNat else s) = s + (E.1 ∩ R).card := by
          by_cases hc0 : (E.1 ∩ R).card = 0
          · simp [hc0]
          · have hcond : 1 ≤ Int.ofNat (E.1 ∩ R).card ∧ Int.ofNat (E.1 ∩ R).card ≤ (b : ℤ) := by
              rw [Int.ofNat_eq_natCast]
              exact ⟨by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc0, by exact_mod_cast hc_b⟩
            rw [ite_eq_left hcond]; rfl
        have hadv := memPrefixValid_batchAdvance hval (markedSlotAddrs n m) (parallelMarkPerm n m
          R (subsetWorkIdx n m E)) (nodup_markedSlotAddrs n m _) (by rw [hm_mark.2]; omega)
          hm_mark.1
        rw [hm_mark.2] at hadv; dsimp only [G]; rw [hidx_eq, ite_eq_left hadv]
        exact Complex.ofReal_one
      rw [Finset.sum_congr rfl fun E _ ↦ by rw [hterm E, mul_one]]; simp_rw [← Complex.ofReal_pow]
      rw [← Complex.ofReal_sum, sum_sq_evalSymStages, sum_sq_u0Vec hmN, Complex.ofReal_one]
    rw [h1, Complex.one_re]
  · rw [ite_eq_right hval]; exact (hbnd z).2.1
private def hitPred {Var : Type} (res : Var) (w : ℕ) (σ : Store Var) : Prop := σ res = (w : ℤ)
private instance {Var : Type} (res : Var) (w : ℕ) : DecidablePred (hitPred res w) :=
  fun σ ↦ inferInstanceAs (Decidable (σ res = (w : ℤ)))
private def missPred {Var : Type} (res : Var) (u : ℕ) (σ : Store Var) : Prop :=
  ∀ w ∈ Finset.Icc 1 u, σ res ≠ (w : ℤ)
private instance {Var : Type} (res : Var) (u : ℕ) : DecidablePred (missPred res u) :=
  fun σ ↦ inferInstanceAs (Decidable (∀ w ∈ Finset.Icc 1 u, σ res ≠ (w : ℤ)))
private lemma wp_johnsonPassFront_hitProb {Var : Type} [DecidableEq Var] (res : Var) {n m k s w :
    ℕ} (hmN : m ≤ 2 ^ n) (_hs : s ≤ k) (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) {S : Finset
    (Fin (2 ^ n))} (hcard : S.card = k) {c_lo : ℝ} (hc0 : 0 ≤ c_lo) (hc1 : c_lo ≤ 1) (hlo : ∀ R :
    Finset (Fin (2 ^ n)), R.card = k - s → c_lo ≤ symHitProb R (evalSymStages R stages (u0Vec (2 ^
    n) m)) w) : scaledValidObs (Var := Var) n m k S s c_lo hc0 hc1 ≤ wp ((johnsonPassFront res n m
    k s hmN stages).compile qAssign (groverParallelMarkingOracle m S)) (liftPureProp (hitPred res
    w)) := by
  intro σ; let G (r_val : ℤ) (_ : Fin (2 ^ (k * n))) : ℝ := if r_val = (w : ℤ) then 1 else 0
  have hΦ (τ : Store Var) : (liftPureProp (d := 2 ^ (m * (n + 1) + k * n)) (hitPred res w) τ).1.1 =
        diagonal (fun z ↦ (G (τ res) (lowHighEquiv (m * (n + 1)) (k * n) z).2 : ℂ)) := by
    rw [liftPureProp_apply]; by_cases hp : hitPred res w τ
    · have hp' : τ res = (w : ℤ) := hp; simp [hp, hp', G]
    · have hp' : τ res ≠ (w : ℤ) := hp; simp [hp, hp', G]
  obtain ⟨d_out, hmat, hd_valid⟩ :=
    wp_johnsonPassFront_diag res hmN stages S G (liftPureProp (hitPred res w)) hΦ σ
  have hbnd := observable_diag_real_bounds _ d_out hmat
  have hmat_re : ((wp ((johnsonPassFront res n m k s hmN stages).compile qAssign
      (groverParallelMarkingOracle m S)) (liftPureProp (hitPred res w))) σ).1.1 =
      diagonal (fun z ↦ ((d_out z).re : ℂ)) := by
    rw [hmat]; exact congrArg diagonal (funext fun z ↦ (hbnd z).1)
  refine realDiagObs_le_of_mat (fun z ↦ (hbnd z).2.1) (fun z ↦ (hbnd z).2.2) hmat_re fun z ↦ ?_
  dsimp only [validInd]
  open Classical in
  by_cases hval : MemPrefixValid S s (lowHighEquiv (m * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hval, mul_one]; let μ := (lowHighEquiv (m * (n + 1)) (k * n) z).2
    let R := S \ memSeen n k (memPrefix k s) μ; have hseen := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = k - s := by
      dsimp only [R, μ]; rw [Finset.card_sdiff_of_subset hseen.2, hcard, hseen.1]
    have hprob : d_out z = (symHitProb R (evalSymStages R stages (u0Vec (2 ^ n) m)) w : ℂ) := by
      rw [hd_valid z hval]; unfold symHitProb; rw [Complex.ofReal_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun E _ ↦ ?_; dsimp only [G]
      have heq_iff : (Int.ofNat (E.1 ∩ R).card = (w : ℤ)) ↔ ((E.1 ∩ R).card = w) := (by simp)
      by_cases hew : (E.1 ∩ R).card = w
      · rw [ite_eq_left (heq_iff.mpr hew), ite_eq_left hew]; push_cast; ring
      · rw [ite_eq_right (mt heq_iff.mp hew), ite_eq_right hew]; simp
    rw [hprob, Complex.ofReal_re]; exact hlo R hR_card
  · rw [ite_eq_right hval, mul_zero]; exact (hbnd z).2.1
private noncomputable def dispHits {Var : Type} (res : Var) {Q O : ℕ}
    (onHit : ℕ → OracleCirc Var Q O) (onZero : OracleCirc Var Q O) :
    ℕ → OracleCirc Var Q O
  | 0 => onZero
  | u + 1 => .qIf (hitPred res (u + 1)) (onHit (u + 1)) (dispHits res onHit onZero u)
private lemma wp_dispHits_ge {Var : Type} [DecidableEq Var] (res : Var) {n m k s : ℕ} {S : Finset
    (Fin (2 ^ n))} (onHit : ℕ → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (onZero :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (Θ : CQAssertion (Store Var) (2 ^ (m * (n +
      1) +
    k * n))) (honZero : validObs n m k S s ≤ wp (onZero.compile qAssign
    (groverParallelMarkingOracle m S)) Θ) (u : ℕ) (honHit : ∀ w ∈ Finset.Icc 1 u, validObs n m k S
    (s + w) ≤ wp ((onHit w).compile qAssign (groverParallelMarkingOracle m S)) Θ) : dispPre res n
    m k S s u ≤ wp ((dispHits res onHit onZero u).compile qAssign (groverParallelMarkingOracle m
    S)) Θ := by
  induction u with
  | zero =>
    intro σ; have hf : ¬ (1 ≤ σ res ∧ σ res ≤ ((0 : ℕ) : ℤ)) := (by omega)
    dsimp only [dispPre, dispHits]; rw [ite_eq_right hf]; exact honZero σ
  | succ u ih =>
    intro σ; dsimp only [dispHits, compile]; rw [wp_qIf]; dsimp only
    by_cases hh : hitPred res (u + 1) σ
    · rw [ite_eq_left hh]
      have h1 : 1 ≤ σ res ∧ σ res ≤ ((u + 1 : ℕ) : ℤ) := (by dsimp only [hitPred] at hh; omega)
      have hnat : (σ res).toNat = u + 1 := (by dsimp only [hitPred] at hh; omega)
      dsimp only [dispPre]; rw [ite_eq_left h1, hnat]
      exact honHit (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) σ
    · rw [ite_eq_right hh]
      have heqv : (1 ≤ σ res ∧ σ res ≤ ((u + 1 : ℕ) : ℤ)) ↔ (1 ≤ σ res ∧ σ res ≤ (u : ℤ)) := by
        dsimp only [hitPred] at hh; omega
      have hpre : dispPre res n m k S s (u + 1) σ = dispPre res n m k S s u σ := by
        dsimp only [dispPre]; exact if_congr heqv rfl rfl
      rw [hpre]; exact ih (fun w hw ↦ honHit w (Finset.Icc_subset_Icc_right (Nat.le_succ u) hw)) σ
private lemma dispHits_trace_and_cost {Var : Type} [DecidableEq Var] (res : Var) {Q O : ℕ} (oracle
    : Unitary (2 ^ O)) (model : CostModel (2 ^ Q)) (onHit : ℕ → OracleCirc Var Q O) (onZero :
    OracleCirc Var Q O) (u : ℕ) (Γ : CQState (Store Var) (2 ^ Q)) : (Γ.restrict (missPred res
      u)).trace +
    ∑ w ∈ Finset.Icc 1 u, (Γ.restrict (hitPred res w)).trace = Γ.trace ∧ expectedCost model
    ((dispHits res onHit onZero u).compile qAssign oracle) Γ = expectedCost model (onZero.compile
    qAssign oracle) (Γ.restrict (missPred res u)) + ∑ w ∈ Finset.Icc 1 u, expectedCost model
    ((onHit w).compile qAssign oracle) (Γ.restrict (hitPred res w)) := by
  induction u generalizing Γ with
  | zero =>
    have hmiss0 : Γ.restrict (missPred res 0) = Γ :=
      CQState.restrict_of_forall (fun σ w hw ↦ by simp at hw) Γ
    simp [dispHits, hmiss0]
  | succ u ih =>
    let Γ' := Γ.restrict (¬ hitPred res (u + 1) ·)
    have hmiss_eq : Γ'.restrict (missPred res u) = Γ.restrict (missPred res (u + 1)) := by
      apply Subtype.ext; funext σ; simp only [Γ', CQState.restrict_coe]
      by_cases h1 : hitPred res (u + 1) σ
      · have hm : ¬ missPred res (u + 1) σ := fun hm ↦
          hm (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) h1
        simp [h1, hm]
      · have heqv : missPred res u σ ↔ missPred res (u + 1) σ := by
          simp only [missPred, Finset.mem_Icc]
          refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ h w ⟨hw.1, by omega⟩⟩
          by_cases hwu : w = u + 1
          · subst hwu; exact h1
          · exact h w ⟨hw.1, by omega⟩
        by_cases h2 : missPred res u σ <;> simp [h1, h2, heqv.mp, mt heqv.mpr]
    have hhit_eq (w : ℕ) (hw : w ∈ Finset.Icc 1 u) :
        Γ'.restrict (hitPred res w) = Γ.restrict (hitPred res w) := by
      apply Subtype.ext; funext σ; simp only [Γ', CQState.restrict_coe]
      by_cases hw_p : hitPred res w σ
      · have hne : ¬ hitPred res (u + 1) σ := by
          rcases Finset.mem_Icc.mp hw with ⟨_, hwu⟩; dsimp only [hitPred] at hw_p ⊢; omega
        simp [hw_p, hne]
      · simp [hw_p]
    obtain ⟨htr_ih, hcost_ih⟩ := ih Γ'
    rw [hmiss_eq, Finset.sum_congr rfl fun w hw ↦ by rw [hhit_eq w hw]] at htr_ih hcost_ih
    have htr_top := Γ.trace_restrict_add_trace_restrict_not (hitPred res (u + 1))
    dsimp only [dispHits, compile]; rw [expectedCost_qIf]
    change _ ∧ expectedCost model ((onHit (u + 1)).compile qAssign oracle)
        (Γ.restrict (hitPred res (u + 1))) +
        expectedCost model ((dispHits res onHit onZero u).compile qAssign oracle) Γ' = _
    rw [hcost_ih]
    have hsucc_tr : (∑ w ∈ Finset.Icc 1 (u + 1), (Γ.restrict (hitPred res w)).trace) = (∑ w ∈
      Finset.Icc 1 u, (Γ.restrict (hitPred res w)).trace) + (Γ.restrict (hitPred res (u +
      1))).trace := Finset.sum_Icc_succ_top (by omega) _
    have hsucc_c : (∑ w ∈ Finset.Icc 1 (u + 1), expectedCost model ((onHit w).compile qAssign
      oracle) (Γ.restrict (hitPred res w))) = (∑ w ∈ Finset.Icc 1 u, expectedCost model ((onHit
      w).compile qAssign oracle) (Γ.restrict (hitPred res w))) + expectedCost model ((onHit (u +
      1)).compile qAssign oracle) (Γ.restrict (hitPred res (u + 1))) := Finset.sum_Icc_succ_top
      (by omega) _
    refine ⟨by rw [hsucc_tr, ← add_assoc, htr_ih, add_comm]; exact htr_top, ?_⟩; rw [hsucc_c]
    abel
private lemma expect_restrict_valid_branches {Var : Type} {n m k s b : ℕ} (res : Var) {S : Finset
    (Fin (2 ^ n))} {Δ₁ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))} (hdisp : 𝔼[Δ₁, dispPre res
      n m k
    S s b] = Δ₁.trace) : 𝔼[Δ₁.restrict (missPred res b), validObs n m k S s] = (Δ₁.restrict
    (missPred res b)).trace ∧ ∀ w ∈ Finset.Icc 1 b, 𝔼[Δ₁.restrict (hitPred res w), validObs n m k
    S (s + w)] = (Δ₁.restrict (hitPred res w)).trace := by
  have hexp_part (p : Store Var → Prop) [DecidablePred p] :
      𝔼[Δ₁.restrict p, dispPre res n m k S s b] = (Δ₁.restrict p).trace := by
    have hpart : 𝔼[Δ₁, dispPre res n m k S s b] = 𝔼[Δ₁.restrict p, dispPre res n m k S s b] +
          𝔼[Δ₁.restrict (¬ p ·), dispPre res n m k S s b] := by
      simpa using expect_ite_partition p Δ₁ (dispPre res n m k S s b) (dispPre res n m k S s b)
    have h1 : 𝔼[Δ₁.restrict p, dispPre res n m k S s b] ≤ (Δ₁.restrict p).trace := by
      rw [← expect_top (Δ₁.restrict p)]; exact expect_mono le_rfl le_top
    have h2 : 𝔼[Δ₁.restrict (¬ p ·), dispPre res n m k S s b] ≤
        (Δ₁.restrict (¬ p ·)).trace := by
      rw [← expect_top (Δ₁.restrict (¬ p ·))]; exact expect_mono le_rfl le_top
    have htr : ((Δ₁.restrict p).trace : ℝ) + (Δ₁.restrict (¬ p ·)).trace = Δ₁.trace := by
      exact_mod_cast Δ₁.trace_restrict_add_trace_restrict_not p
    linarith
  have hcongr (p : Store Var → Prop) [DecidablePred p] (Θ : CQAssertion (Store Var) (2 ^ (m * (n +
    1) +
    k * n))) (hσ : ∀ σ, p σ → dispPre res n m k S s b σ = Θ σ) : 𝔼[Δ₁.restrict p, Θ] =
    𝔼[Δ₁.restrict p, dispPre res n m k S s b] := by
    rw [expect_eq_tsum, expect_eq_tsum]; refine tsum_congr fun σ ↦ ?_
    by_cases hp : p σ
    · simp [CQState.restrict_coe, hp, hσ σ hp]
    · simp [CQState.restrict_coe, hp]
  refine ⟨?_, fun w hw ↦ ?_⟩
  · rw [hcongr (missPred res b) _ fun σ hp ↦ by
      have hf : ¬ (1 ≤ σ res ∧ σ res ≤ (b : ℤ)) := fun h1b ↦ by
        let w₀ := (σ res).toNat
        have hw₀ : w₀ ∈ Finset.Icc 1 b := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact hp w₀ hw₀ (by omega)
      dsimp only [dispPre]; rw [ite_eq_right hf]]
    exact hexp_part (missPred res b)
  · rw [hcongr (hitPred res w) _ fun σ hp ↦ by
      rcases Finset.mem_Icc.mp hw with ⟨hw1, hwb⟩; dsimp only [hitPred] at hp
      have ht : 1 ≤ σ res ∧ σ res ≤ (b : ℤ) := (by omega)
      have hnat : (σ res).toNat = w := (by omega); dsimp only [dispPre]; rw [ite_eq_left ht, hnat]]
    exact hexp_part (hitPred res w)
private noncomputable def eigLockStagesFrom {Var : Type} (res : Var) (n m k : ℕ)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) :
    (j : ℕ) → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | j =>
      if hj : j < k then
        .seq (eigLockStage res n m k hm_grid hk_grid hn200 ⟨j, hj⟩)
          (eigLockStagesFrom res n m k hm_grid hk_grid hn200 (j + 1))
      else .skip
termination_by j => k - j
private lemma wp_eigLockStagesFrom_ge {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k → validObs (Var := Var) n m k S j ≤
        wp ((eigLockStagesFrom res n m k hm_grid hk_grid hn200 j).compile qAssign
            (groverParallelMarkingOracle m S))
          (validObs n m k S k)
  | 0, j, hd, _ => by
    have hjeq : j = k := (by omega); subst hjeq; rw [eigLockStagesFrom]; simp
  | d + 1, j, hd, _ => by
    have hj : j < k := (by omega); rw [eigLockStagesFrom, dite_eq_left hj]; dsimp only [compile]
    rw [wp_qSeq]
    have hih := wp_eigLockStagesFrom_ge res hm_grid hk_grid hn200 hcard d (j + 1)
      (by omega) (by omega)
    exact ((eigLockStage_wp_and_active res hm_grid hk_grid hn200 hcard ⟨j, hj⟩).1).trans
      (wp_mono _ hih)
private lemma expectedCost_eigLockStagesFrom_le {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn600 : 600 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k → ∀ Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
        𝔼[Δ, validObs n m k S j] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          ((eigLockStagesFrom res n m k hm_grid hk_grid (by omega) j).compile qAssign
            (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ * ENNReal.ofReal ((2 * (d : ℝ)) * √(2 ^ n : ℝ))
  | 0, j, hd, _, Δ, _ => by
    have hjeq : j = k := (by omega); subst hjeq; rw [eigLockStagesFrom]; simp
  | d + 1, j, hd, _, Δ, hV => by
    have hj : j < k := (by omega); have hn200 : 200 ≤ n := (by omega)
    rw [eigLockStagesFrom, dite_eq_left hj]; dsimp only [compile]; rw [expectedCost_qSeq]
    let stageP := (eigLockStage (Var := Var) res n m k hm_grid hk_grid hn200 ⟨j, hj⟩).compile
      qAssign (groverParallelMarkingOracle m S)
    have hwp_st := (eigLockStage_wp_and_active (Var := Var) res hm_grid hk_grid hn200 hcard
      ⟨j, hj⟩).1
    have hstep_V := jp01_validState_step hV hwp_st
    have hcost_st := expectedCost_eigLockStage_le res hm_grid hk_grid hn200 hcard ⟨j, hj⟩ hV
    have hih := expectedCost_eigLockStagesFrom_le res hm_grid hk_grid hn600 hcard d (j + 1)
      (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
    rw [hstep_V.2] at hih
    have hlin := jp01_stageCostReal_le_linear_S0 (k := k) (r := k - j) hn600 hm_grid hk_grid
      (by omega) (by omega)
    have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    have hmr1 : (1 : ℝ) ≤ (m : ℝ) * ((k - j : ℕ) : ℝ) := by
      have : 1 ≤ m * (k - j) := (by simpa using Nat.mul_le_mul hm1 (by omega : 1 ≤ k - j))
      exact_mod_cast this
    have hdiv_le : (2 ^ n : ℝ) / ((m : ℝ) * ((k - j : ℕ) : ℝ)) ≤ (2 ^ n : ℝ) :=
      div_le_self (by positivity) hmr1
    have hsq_le : √((2 ^ n : ℝ) / ((m : ℝ) * ((k - j : ℕ) : ℝ))) ≤ √(2 ^ n : ℝ) :=
      Real.sqrt_le_sqrt hdiv_le
    have h5_le : (5 : ℝ) ≤ √(2 ^ n : ℝ) := by
      have h25 : (25 : ℝ) ≤ (2 ^ n : ℝ) := by
        calc (25 : ℝ) ≤ (2 : ℝ) ^ 5 := by norm_num
          _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      calc (5 : ℝ) = √(25 : ℝ) := by norm_num
        _ ≤ √(2 ^ n : ℝ) := Real.sqrt_le_sqrt h25
    have hcoef_le : (π / 8 + 1 / 4) ≤ 1 := (by linarith [Real.pi_lt_four])
    have hst_bound : stageCostReal n m (k - j) ≤ 2 * √(2 ^ n : ℝ) := by
      calc stageCostReal n m (k - j)
          ≤ (π / 8 + 1 / 4) * √((2 ^ n : ℝ) / ((m : ℝ) * ((k - j : ℕ) : ℝ))) + 5 := hlin.2
        _ ≤ 1 * √(2 ^ n : ℝ) + √(2 ^ n : ℝ) :=
            add_le_add (mul_le_mul hcoef_le hsq_le (Real.sqrt_nonneg _) zero_le_one) h5_le
        _ = 2 * √(2 ^ n : ℝ) := by ring
    calc expectedCost _ stageP Δ + expectedCost _ _ ((interp stageP).toStateFun Δ)
        ≤ stateMass Δ * ENNReal.ofReal (2 * √(2 ^ n : ℝ)) +
            stateMass Δ * ENNReal.ofReal ((2 * (d : ℝ)) * √(2 ^ n : ℝ)) :=
          add_le_add (hcost_st.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hst_bound)
              zero_le))
            hih
      _ = stateMass Δ * (ENNReal.ofReal (2 * √(2 ^ n : ℝ)) +
              ENNReal.ofReal ((2 * (d : ℝ)) * √(2 ^ n : ℝ))) := by ring
      _ = stateMass Δ * ENNReal.ofReal ((2 * ((d + 1 : ℕ) : ℝ)) * √(2 ^ n : ℝ)) := by
          congr 1
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast; ring
private lemma spec_V_nonneg {m k : ℕ} (spec : JohnsonWalkSpec m k) {r : ℕ} (hr : r ≤ k) :
    0 ≤ spec.V r := by
  rw [← spec.hV0]; exact spec.hV_mono (Nat.zero_le r) hr
private lemma spec_pLo_sum_le_one {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSpec m k) {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k) (hwk : spec.useWalk r = true) :
    (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w) ≤ 1 ∧
      ∀ w ∈ Finset.Icc 1 (min m r), spec.pLo r w ≤ 1 := by
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid; have hn0 : 600 ≤ spec.n0 := spec.hn0
  have h1024 : 1024 ≤ 2 ^ spec.n0 := by
    calc 1024 ≤ 2 ^ 10 := by norm_num
      _ ≤ 2 ^ spec.n0 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmN₀ : m ≤ 2 ^ spec.n0 := hm_hi.trans h1024
  have hrN₀ : r ≤ 2 ^ spec.n0 := (hrk.trans hk_hi).trans h1024
  let R₀ : Finset (Fin (2 ^ spec.n0)) :=
    (Finset.range r).attach.image fun x ↦ ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hrN₀⟩
  have hR₀ : R₀.card = r := by
    rw [Finset.card_image_of_injective _ (fun a b h ↦ Subtype.ext (Fin.mk.inj h)),
      Finset.card_attach, Finset.card_range]
  let v₀ := evalSymStages R₀ (spec.stages spec.n0 r) (u0Vec (2 ^ spec.n0) m)
  have hsum_le : (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w) ≤ 1 := by
    calc ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
        ≤ ∑ w ∈ Finset.Icc 1 (min m r), symHitProb R₀ v₀ w :=
          Finset.sum_le_sum fun w hw ↦ spec.hpLo_le spec.n0 r le_rfl hr2 hrk hwk R₀ hR₀ w hw
      _ ≤ ∑ w ∈ Finset.range (min m R₀.card + 1), symHitProb R₀ v₀ w := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw ↦ ?_)
            (fun w _ _ ↦ symHitProb_nonneg R₀ v₀ w)
          rcases Finset.mem_Icc.mp hw with ⟨_, hwb⟩; rw [Finset.mem_range, hR₀]; omega
      _ = 1 := sum_symHitProb_evalSymStages hmN₀ R₀ _
  refine ⟨hsum_le, fun w hw ↦ ?_⟩
  exact (Finset.single_le_sum (fun u _ ↦ spec.hpLo_nonneg r u) hw).trans hsum_le
private lemma pow_small_of_pos_lt_one {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 < ε) :
    ∃ F : ℕ, q ^ F ≤ ε := by
  by_cases hq_zero : q = 0
  · subst hq_zero; exact ⟨1, by simpa using hε.le⟩
  · have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq_zero); let d := q⁻¹ - 1
    have hd : 0 < d := (by dsimp only [d]; rw [sub_pos, one_lt_inv₀ hqp]; exact hq1)
    have hbern : ∀ F : ℕ, 1 + (F : ℝ) * d ≤ (1 + d) ^ F := fun F ↦ by
      induction F with
      | zero => simp
      | succ F ih =>
        have h1d : (1 : ℝ) ≤ (1 + d) ^ F := one_le_pow₀ (by linarith)
        calc 1 + ((F + 1 : ℕ) : ℝ) * d = (1 + (F : ℝ) * d) + 1 * d := by push_cast; ring
          _ ≤ (1 + d) ^ F + (1 + d) ^ F * d := add_le_add ih (mul_le_mul_of_nonneg_right h1d hd.le)
          _ = (1 + d) ^ (F + 1) := by ring
    obtain ⟨F, hF⟩ := exists_nat_ge ((1 / ε) / d); refine ⟨F, ?_⟩
    have h1 : 1 / ε ≤ (F : ℝ) * d := (div_le_iff₀ hd).mp hF
    have hqd : 1 + d = q⁻¹ := (by dsimp only [d]; ring)
    have h2 : 1 / ε ≤ (q ^ F)⁻¹ := by
      calc 1 / ε ≤ 1 + (F : ℝ) * d := by linarith
        _ ≤ (1 + d) ^ F := hbern F
        _ = (q ^ F)⁻¹ := by rw [hqd, inv_pow]
    have hqF_pos : 0 < q ^ F := pow_pos hqp F; have hprod : 0 < ε * q ^ F := mul_pos hε hqF_pos
    have h3 : (1 / ε) * (ε * q ^ F) ≤ (q ^ F)⁻¹ * (ε * q ^ F) :=
      mul_le_mul_of_nonneg_right h2 hprod.le
    field_simp [hε.ne', hqF_pos.ne'] at h3; exact h3
private noncomputable def autoFuel {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSpec m k) (r : ℕ) : ℕ :=
  open Classical in
  if h : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true then
    let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
    let slack :=
      (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w * (spec.V r - spec.V (r - w))) - spec.tauSum r
    have hc_pos : 0 < c := spec.hpLo_sum_pos r h.1 h.2.1 h.2.2
    have hc_le1 : c ≤ 1 := (spec_pLo_sum_le_one hm_grid hk_grid spec h.1 h.2.1 h.2.2).1
    have hslack : 0 < slack := sub_pos.mpr (spec.hdrift_lt r h.1 h.2.1 h.2.2)
    have hq0 : 0 ≤ 1 - c := by linarith
    have hq1 : 1 - c < 1 := by linarith
    have heps : 0 < (slack / 2) / (2 * (k : ℝ) + 1) := by positivity
    (Classical.choose (pow_small_of_pos_lt_one hq0 hq1 heps)) + 1
  else 1
private lemma autoFuel_spec {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSpec m k) {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k) (hwk : spec.useWalk r = true) :
    let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
    let slack :=
      (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w * (spec.V r - spec.V (r - w))) - spec.tauSum r
    ∃ F : ℕ, autoFuel hm_grid hk_grid spec r = F + 1 ∧
      (1 - c) ^ F * (2 * (k : ℝ)) ≤ slack / 2 := by
  intro c slack; have hcond : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true := ⟨hr2, hrk, hwk⟩
  have hc_pos : 0 < c := spec.hpLo_sum_pos r hr2 hrk hwk
  have hc_le1 : c ≤ 1 := (spec_pLo_sum_le_one hm_grid hk_grid spec hr2 hrk hwk).1
  have hslack : 0 < slack := sub_pos.mpr (spec.hdrift_lt r hr2 hrk hwk)
  have hq0 : 0 ≤ 1 - c := (by linarith); have hq1 : 1 - c < 1 := (by linarith)
  have heps : 0 < (slack / 2) / (2 * (k : ℝ) + 1) := (by positivity)
  let F := Classical.choose (pow_small_of_pos_lt_one hq0 hq1 heps)
  have hF : (1 - c) ^ F ≤ (slack / 2) / (2 * (k : ℝ) + 1) :=
    Classical.choose_spec (pow_small_of_pos_lt_one hq0 hq1 heps)
  refine ⟨F, ?_, ?_⟩
  · unfold autoFuel; rw [dite_eq_left hcond]
  · have hden_pos : (0 : ℝ) < 2 * (k : ℝ) + 1 := (by positivity)
    have h1 : (1 - c) ^ F * (2 * (k : ℝ) + 1) ≤ slack / 2 := (le_div_iff₀ hden_pos).mp hF
    have hqF0 : 0 ≤ (1 - c) ^ F := pow_nonneg hq0 F; nlinarith
private noncomputable def johnsonStageFuel {Var : Type} (res : Var) (n m k : ℕ)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n)
    (hmN : m ≤ 2 ^ n) (stages : List (ℕ × SymOrthogonal (2 ^ n) m)) (s : ℕ)
    (solveNext : (w : ℕ) → 1 ≤ w → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) :
    ℕ → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | 0 => eigLockStagesFrom res n m k hm_grid hk_grid hn200 s
  | fuel + 1 =>
      .seq (johnsonPassFront res n m k s hmN stages)
        (dispHits res (fun w ↦ if hw : 1 ≤ w then solveNext w hw else .skip)
          (johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN stages s solveNext fuel)
          (min m (k - s)))
private lemma wp_johnsonStageFuel_ge {Var : Type} [DecidableEq Var] {n m k s : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) (hmN : m ≤ 2 ^ n) (hs : s ≤ k) (stages : List (ℕ × SymOrthogonal (2 ^ n) m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (solveNext : (w : ℕ) → 1 ≤ w → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    (hnext : ∀ w (hw1 : 1 ≤ w), w ≤ min m (k - s) → validObs (Var := Var) n m k S (s + w) ≤
        wp ((solveNext w hw1).compile qAssign (groverParallelMarkingOracle m S))
          (validObs n m k S k)) :
    ∀ fuel : ℕ, validObs (Var := Var) n m k S s ≤
        wp ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN stages s solveNext fuel).compile
            qAssign (groverParallelMarkingOracle m S))
          (validObs n m k S k)
  | 0 => wp_eigLockStagesFrom_ge res hm_grid hk_grid hn200 hcard (k - s) s rfl hs
  | fuel + 1 => by
    unfold johnsonStageFuel; dsimp only [compile]; rw [wp_qSeq]
    have hih := wp_johnsonStageFuel_ge res hm_grid hk_grid hn200 hmN hs stages hcard
      solveNext hnext fuel
    have hdisp := wp_dispHits_ge res
      (fun w ↦ if hw : 1 ≤ w then solveNext w hw else .skip)
      (johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN stages s solveNext fuel)
      (validObs n m k S k) hih (min m (k - s)) (fun w hw ↦ by
        rcases Finset.mem_Icc.mp hw with ⟨hw1, hwb⟩; rw [dite_eq_left hw1]; exact hnext w hw1 hwb)
    exact (wp_johnsonPassFront_dispPre res hmN hs stages hcard).trans (wp_mono _ hdisp)
private lemma expectedCost_johnsonStageFuel_step {Var : Type} [DecidableEq Var] {n m k s : ℕ} (res
    : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hmN : m ≤ 2 ^
    n) (spec : JohnsonWalkSpec m k) (hn0 : spec.n0 ≤ n) (hs : s < k) (hr2 : 2 ≤ k - s) (hwk :
    spec.useWalk (k - s) = true) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (solveNext : (w :
    ℕ) → 1 ≤ w → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (hnext_cost : ∀ w (hw1 : 1 ≤
    w), w ≤ min m (k - s) → ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)), 𝔼[Γ, validObs n m
      k S
    (s + w)] = Γ.trace → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m
    S)) ((solveNext w hw1).compile qAssign (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ *
    ENNReal.ofReal (spec.V (k - s - w) * √(2 ^ n : ℝ))) (hc_step : max 0 (spec.C_step + 1) ≤ (((∑
    w ∈ Finset.Icc 1 (min m (k - s)), spec.pLo (k - s) w * (spec.V (k - s) - spec.V (k - s -
    w))) - spec.tauSum (k - s)) / 2) * √(2 ^ n : ℝ)) {fuel : ℕ} {E_f : ℝ} (hE0 : 0 ≤ E_f)
    (hfuel_cost : ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)), 𝔼[Γ, validObs n m k S s] =
    Γ.trace → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN (spec.stages n (k - s)) s solveNext
    fuel).compile qAssign (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ * ENNReal.ofReal
    ((spec.V (k - s) + E_f) * √(2 ^ n : ℝ))) (Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)))
      (hV :
    𝔼[Δ, validObs n m k S s] = Δ.trace) :
    let r := k - s; let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
    let slack :=
      (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w * (spec.V r - spec.V (r - w))) - spec.tauSum r
    expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN (spec.stages n r) s
        solveNext (fuel + 1)).compile qAssign (groverParallelMarkingOracle m S)) Δ ≤
      stateMass Δ * ENNReal.ofReal ((spec.V r - slack / 2 + (1 - c) * E_f) * √(2 ^ n : ℝ)) := by
  intro r c slack; let b := min m r; let S₀ := √(2 ^ n : ℝ)
  have hS₀_pos : 0 < S₀ := (by positivity); let oracle := groverParallelMarkingOracle m S
  let model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
  let stages := spec.stages n r; have hrk : r ≤ k := Nat.sub_le k s
  have hp_le1 := spec_pLo_sum_le_one hm_grid hk_grid spec hr2 hrk hwk
  have hdisp_wp := wp_johnsonPassFront_dispPre (Var := Var) res (k := k) (s := s) hmN hs.le
    stages hcard
  have hhit_wp (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :=
    wp_johnsonPassFront_hitProb (Var := Var) res (k := k) (s := s) (w := w) hmN hs.le
      stages hcard (spec.hpLo_nonneg r w) (hp_le1.2 w hw)
      (fun R hR ↦ spec.hpLo_le n r hn0 hr2 hrk hwk R hR w hw)
  have hfr_cb := costBound_johnsonPassFront (Var := Var) res (k := k) (s := s) hmN stages S Δ
  unfold johnsonStageFuel; dsimp only [compile]
  generalize (johnsonPassFront (Var := Var) res n m k s hmN stages).compile qAssign oracle = P_fr
    at hdisp_wp hhit_wp hfr_cb ⊢
  let Δ₁ := (interp P_fr).toStateFun Δ
  have htr_le : (Δ₁.trace : ℝ) ≤ Δ.trace := (by exact_mod_cast (interp P_fr).trace_toStateFun_le Δ)
  have hdisp_tr : 𝔼[Δ₁, dispPre res n m k S s b] = Δ₁.trace := by
    have h1 : (Δ.trace : ℝ) ≤ 𝔼[Δ₁, dispPre res n m k S s b] := by
      rw [← hV, ← wp_expectation_eq]; exact expect_mono le_rfl hdisp_wp
    have h2 : 𝔼[Δ₁, dispPre res n m k S s b] ≤ Δ₁.trace := by
      rw [← expect_top Δ₁]; exact expect_mono le_rfl le_top
    linarith
  have hbr_val := expect_restrict_valid_branches res hdisp_tr
  have hp_mass (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
      spec.pLo r w * Δ.trace ≤ (Δ₁.restrict (hitPred res w)).trace := by
    have hwp_p := hhit_wp w hw
    calc spec.pLo r w * Δ.trace = 𝔼[Δ, scaledValidObs n m k S s (spec.pLo r w) (spec.hpLo_nonneg r
          w) (hp_le1.2 w hw)] := by
          rw [expect_eq_mul_of_apply_eq_smul Δ _ (scaledValidObs_smul n m k S s _ _ _), hV]
      _ ≤ 𝔼[Δ, wp P_fr (liftPureProp (hitPred res w))] := expect_mono le_rfl hwp_p
      _ = 𝔼[Δ₁, liftPureProp (hitPred res w)] := wp_expectation_eq P_fr Δ _
      _ = (Δ₁.restrict (hitPred res w)).trace := expect_liftPureProp (hitPred res w) Δ₁
  let onHit := fun w ↦ if hw : 1 ≤ w then solveNext w hw else .skip
  let onZero := johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN stages s solveNext fuel
  obtain ⟨htr_part, hcost_disp⟩ := dispHits_trace_and_cost res oracle model onHit onZero b Δ₁
  rw [expectedCost_qSeq]; change expectedCost model P_fr Δ +
    expectedCost model ((dispHits res onHit onZero b).compile qAssign oracle) Δ₁ ≤ _
  rw [hcost_disp]
  have hfr_real : ((stagesQueryCount stages + 1 : ℕ) : ℝ) ≤ (spec.tauSum r + slack / 2) * S₀ := by
    have hlen := spec.hstages_len n r hn0 hr2 hrk hwk
    have hc_le : spec.C_step + 1 ≤ (slack / 2) * S₀ := (le_max_right 0 _).trans hc_step; push_cast
    linarith
  have hfr_cost : expectedCost model P_fr Δ ≤
      ENNReal.ofReal (Δ.trace * ((spec.tauSum r + slack / 2) * S₀)) := by
    calc expectedCost model P_fr Δ
        ≤ stateMass Δ * (((stagesQueryCount stages : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) := hfr_cb
      _ = ENNReal.ofReal Δ.trace * ENNReal.ofReal ((stagesQueryCount stages + 1 : ℕ) : ℝ) := by
          rw [stateMass_eq_ofReal_trace, ENNReal.ofReal_natCast]; push_cast; rfl
      _ ≤ ENNReal.ofReal Δ.trace * ENNReal.ofReal ((spec.tauSum r + slack / 2) * S₀) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hfr_real) zero_le
      _ = ENNReal.ofReal (Δ.trace * ((spec.tauSum r + slack / 2) * S₀)) :=
          (ENNReal.ofReal_mul Δ.trace_nonneg).symm
  have hzero_cost : expectedCost model (onZero.compile qAssign oracle) (Δ₁.restrict (missPred res
    b)) ≤ ENNReal.ofReal ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀)) := by
    calc expectedCost model (onZero.compile qAssign oracle) (Δ₁.restrict (missPred res b))
        ≤ stateMass (Δ₁.restrict (missPred res b)) * ENNReal.ofReal ((spec.V r + E_f) * S₀) :=
          hfuel_cost _ hbr_val.1
      _ = ENNReal.ofReal ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀)) := by
          rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_mul (CQState.trace_nonneg _)]
  have hhit_cost (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
      expectedCost model ((onHit w).compile qAssign oracle) (Δ₁.restrict (hitPred res w)) ≤
        ENNReal.ofReal ((Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) := by
    rcases Finset.mem_Icc.mp hw with ⟨hw1, hwb⟩; dsimp only [onHit]; rw [dite_eq_left hw1]
    calc expectedCost model ((solveNext w hw1).compile qAssign oracle) (Δ₁.restrict (hitPred res
          w)) ≤ stateMass (Δ₁.restrict (hitPred res w)) * ENNReal.ofReal (spec.V (r - w) * S₀) :=
          hnext_cost w hw1 hwb _ (hbr_val.2 w hw)
      _ = ENNReal.ofReal ((Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) := by
          rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_mul (CQState.trace_nonneg _)]
  have hsum_hit : (∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit w).compile qAssign oracle)
    (Δ₁.restrict (hitPred res w))) ≤ ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict (hitPred
    res w)).trace * (spec.V (r - w) * S₀)) := by
    calc ∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit w).compile qAssign oracle) (Δ₁.restrict
          (hitPred res w)) ≤ ∑ w ∈ Finset.Icc 1 b, ENNReal.ofReal ((Δ₁.restrict (hitPred res
          w)).trace * (spec.V (r - w) * S₀)) := Finset.sum_le_sum hhit_cost
      _ = ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b,
            (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun w hw ↦ mul_nonneg (CQState.trace_nonneg _)
            (mul_nonneg (spec_V_nonneg spec (by omega)) hS₀_pos.le)]
  have hfr_nn : 0 ≤ Δ.trace * ((spec.tauSum r + slack / 2) * S₀) := by
    have htau_sl : 0 ≤ spec.tauSum r + slack / 2 := by
      have hpos : (0 : ℝ) < (stagesQueryCount stages + 1 : ℕ) := (by positivity)
      exact nonneg_of_mul_nonneg_left (hpos.le.trans hfr_real) hS₀_pos
    exact mul_nonneg Δ.trace_nonneg (mul_nonneg htau_sl hS₀_pos.le)
  have hz_nn : 0 ≤ (Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀) :=
    mul_nonneg (CQState.trace_nonneg _)
      (mul_nonneg (add_nonneg (spec_V_nonneg spec (by omega)) hE0) hS₀_pos.le)
  have hs_nn : 0 ≤ ∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) *
    S₀) := Finset.sum_nonneg fun w _ ↦ mul_nonneg (CQState.trace_nonneg _) (mul_nonneg
    (spec_V_nonneg spec (by omega)) hS₀_pos.le)
  have halg : Δ.trace * ((spec.tauSum r + slack / 2) * S₀) +
        ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀) +
          ∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) ≤
      Δ.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by
    let m₀ : ℝ := (Δ₁.restrict (missPred res b)).trace
    let mw : ℕ → ℝ := fun w ↦ (Δ₁.restrict (hitPred res w)).trace
    have htr_part_r : m₀ + ∑ w ∈ Finset.Icc 1 b, mw w = Δ₁.trace := by
      dsimp only [m₀, mw]; exact_mod_cast htr_part
    have hm_tot : m₀ + ∑ w ∈ Finset.Icc 1 b, mw w ≤ Δ.trace := htr_part_r.trans_le htr_le
    have hc_mass : c * Δ.trace ≤ ∑ w ∈ Finset.Icc 1 b, mw w := by
      dsimp only [c]; rw [Finset.sum_mul]; exact Finset.sum_le_sum hp_mass
    have hm0_le : m₀ ≤ (1 - c) * Δ.trace := (by linarith)
    have hdrop : (∑ w ∈ Finset.Icc 1 b, spec.pLo r w * (spec.V r - spec.V (r - w))) * Δ.trace ≤
          ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V r - spec.V (r - w)) := by
      rw [Finset.sum_mul]; refine Finset.sum_le_sum fun w hw ↦ ?_
      rcases Finset.mem_Icc.mp hw with ⟨_, hwb⟩
      have hd_nn : 0 ≤ spec.V r - spec.V (r - w) :=
        sub_nonneg.mpr (spec.hV_mono (by omega) (by omega))
      calc spec.pLo r w * (spec.V r - spec.V (r - w)) * Δ.trace
          = (spec.pLo r w * Δ.trace) * (spec.V r - spec.V (r - w)) := by ring
        _ ≤ mw w * (spec.V r - spec.V (r - w)) := mul_le_mul_of_nonneg_right (hp_mass w hw) hd_nn
    have hid : m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀) =
          ((m₀ + ∑ w ∈ Finset.Icc 1 b, mw w) * spec.V r -
            (∑ w ∈ Finset.Icc 1 b, mw w * (spec.V r - spec.V (r - w))) + m₀ * E_f) * S₀ := by
      have hsum_split : ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀) = ((∑ w ∈ Finset.Icc 1
        b, mw w) * spec.V r - ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V r - spec.V (r - w))) * S₀ := by
        calc ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀)
            = (∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w)) * S₀ := by
                rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun w _ ↦ by ring
          _ = (∑ w ∈ Finset.Icc 1 b,
                (mw w * spec.V r - mw w * (spec.V r - spec.V (r - w)))) * S₀ := by
                congr 1; exact Finset.sum_congr rfl fun w _ ↦ by ring
          _ = ((∑ w ∈ Finset.Icc 1 b, mw w) * spec.V r -
                ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V r - spec.V (r - w))) * S₀ := by
                rw [Finset.sum_sub_distrib, Finset.sum_mul]
      change m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀) = _
      rw [hsum_split]; ring
    change Δ.trace * ((spec.tauSum r + slack / 2) * S₀) +
      (m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀)) ≤ _
    rw [hid]; have hVr0 : 0 ≤ spec.V r := spec_V_nonneg spec (by omega)
    have h1 : (m₀ + ∑ w ∈ Finset.Icc 1 b, mw w) * spec.V r ≤ Δ.trace * spec.V r :=
      mul_le_mul_of_nonneg_right hm_tot hVr0
    have h2 : m₀ * E_f ≤ (1 - c) * Δ.trace * E_f := mul_le_mul_of_nonneg_right hm0_le hE0
    have hmid : Δ.trace * (spec.tauSum r + slack / 2) + ((m₀ + ∑ w ∈ Finset.Icc 1 b, mw w) *
      spec.V r - (∑ w ∈ Finset.Icc 1 b, mw w * (spec.V r - spec.V (r - w))) + m₀ * E_f) ≤
      Δ.trace * (spec.V r - slack / 2 + (1 - c) * E_f) := by
      dsimp only [slack] at h1 hdrop ⊢; linarith
    calc Δ.trace * ((spec.tauSum r + slack / 2) * S₀) + (((m₀ + ∑ w ∈ Finset.Icc 1 b, mw w) *
          spec.V r - (∑ w ∈ Finset.Icc 1 b, mw w * (spec.V r - spec.V (r - w))) + m₀ * E_f) * S₀)
          = (Δ.trace * (spec.tauSum r + slack / 2) + ((m₀ + ∑ w ∈ Finset.Icc 1 b, mw w) * spec.V
          r - (∑ w ∈ Finset.Icc 1 b, mw w * (spec.V r - spec.V (r - w))) + m₀ * E_f)) * S₀ := by
          ring
      _ ≤ (Δ.trace * (spec.V r - slack / 2 + (1 - c) * E_f)) * S₀ :=
          mul_le_mul_of_nonneg_right hmid hS₀_pos.le
      _ = Δ.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by ring
  calc expectedCost model P_fr Δ + (expectedCost model (onZero.compile qAssign oracle)
        (Δ₁.restrict (missPred res b)) + ∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit
        w).compile qAssign oracle) (Δ₁.restrict (hitPred res w))) ≤ ENNReal.ofReal (Δ.trace *
        ((spec.tauSum r + slack / 2) * S₀)) + (ENNReal.ofReal ((Δ₁.restrict (missPred res
        b)).trace * ((spec.V r + E_f) * S₀)) + ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict
        (hitPred res w)).trace * (spec.V (r - w) * S₀))) := add_le_add hfr_cost (add_le_add
        hzero_cost hsum_hit)
    _ = ENNReal.ofReal (Δ.trace * ((spec.tauSum r + slack / 2) * S₀) +
          ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b,
              (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀))) := by
        rw [← ENNReal.ofReal_add hz_nn hs_nn, ← ENNReal.ofReal_add hfr_nn (add_nonneg hz_nn hs_nn)]
    _ ≤ ENNReal.ofReal (Δ.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀)) :=
        ENNReal.ofReal_le_ofReal halg
    _ = stateMass Δ * ENNReal.ofReal ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by
        rw [ENNReal.ofReal_mul Δ.trace_nonneg, ← stateMass_eq_ofReal_trace]
private lemma expectedCost_johnsonStageFuel_le {Var : Type} [DecidableEq Var] {n m k s : ℕ} (res :
    Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hmN : m ≤ 2 ^ n)
    (spec : JohnsonWalkSpec m k) (hn0 : spec.n0 ≤ n) (hs : s < k) (hr2 : 2 ≤ k - s) (hwk :
    spec.useWalk (k - s) = true) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (solveNext : (w :
    ℕ) → 1 ≤ w → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (hnext_cost : ∀ w (hw1 : 1 ≤
    w), w ≤ min m (k - s) → ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)), 𝔼[Γ, validObs n m
      k S
    (s + w)] = Γ.trace → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m
    S)) ((solveNext w hw1).compile qAssign (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ *
    ENNReal.ofReal (spec.V (k - s - w) * √(2 ^ n : ℝ))) (hc_step : max 0 (spec.C_step + 1) ≤ (((∑
    w ∈ Finset.Icc 1 (min m (k - s)), spec.pLo (k - s) w * (spec.V (k - s) - spec.V (k - s -
    w))) - spec.tauSum (k - s)) / 2) * √(2 ^ n : ℝ)) (Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k
      * n)))
    (hV : 𝔼[Δ, validObs n m k S s] = Δ.trace) : expectedCost (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN
    (spec.stages n (k - s)) s solveNext (autoFuel hm_grid hk_grid spec (k - s))).compile qAssign
    (groverParallelMarkingOracle m S)) Δ ≤ stateMass Δ * ENNReal.ofReal (spec.V (k - s) * √(2 ^ n
    : ℝ)) := by
  let r := k - s; let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
  let slack :=
    (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w * (spec.V r - spec.V (r - w))) - spec.tauSum r
  let S₀ := √(2 ^ n : ℝ); have hc_pos : 0 < c := spec.hpLo_sum_pos r hr2 (by omega) hwk
  have hc_le1 : c ≤ 1 := (spec_pLo_sum_le_one hm_grid hk_grid spec hr2 (by omega) hwk).1
  have hslack : 0 < slack := sub_pos.mpr (spec.hdrift_lt r hr2 (by omega) hwk)
  have hq0 : 0 ≤ 1 - c := (by linarith)
  have hind : ∀ f : ℕ, ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)), 𝔼[Γ, validObs n m k S
    s] =
    Γ.trace → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN (spec.stages n r) s solveNext
    f).compile qAssign (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ * ENNReal.ofReal
    ((spec.V r + (1 - c) ^ f * (2 * (k : ℝ))) * S₀) := by
    intro f
    induction f with
    | zero =>
      intro Γ hΓ; have hn600 : 600 ≤ n := spec.hn0.trans hn0
      have h0 := expectedCost_eigLockStagesFrom_le res hm_grid hk_grid hn600 hcard r s rfl
        (by omega) Γ hΓ
      have hVr0 : 0 ≤ spec.V r := spec_V_nonneg spec (by omega)
      have hr_le_k : (r : ℝ) ≤ (k : ℝ) := (by exact_mod_cast (show r ≤ k by omega))
      have hlin : (2 * (r : ℝ)) * S₀ ≤ (spec.V r + (1 - c) ^ 0 * (2 * (k : ℝ))) * S₀ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity); simp only [pow_zero, one_mul]
        linarith
      exact h0.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hlin) zero_le)
    | succ f ih =>
      intro Γ hΓ
      have hEf0 : 0 ≤ (1 - c) ^ f * (2 * (k : ℝ)) := mul_nonneg (pow_nonneg hq0 f) (by positivity)
      have hstep := expectedCost_johnsonStageFuel_step res hm_grid hk_grid hn200 hmN spec hn0 hs
        hr2 hwk hcard solveNext hnext_cost hc_step hEf0 ih Γ hΓ
      have hle : (spec.V r - slack / 2 + (1 - c) * ((1 - c) ^ f * (2 * (k : ℝ)))) * S₀ ≤
          (spec.V r + (1 - c) ^ (f + 1) * (2 * (k : ℝ))) * S₀ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hpow : (1 - c) * ((1 - c) ^ f * (2 * (k : ℝ))) = (1 - c) ^ (f + 1) * (2 * (k : ℝ)) :=
          by ring
        linarith
      exact hstep.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle) zero_le)
  obtain ⟨F, hauto, hF_bound⟩ := autoFuel_spec hm_grid hk_grid spec hr2 (by omega) hwk
  change (1 - c) ^ F * (2 * (k : ℝ)) ≤ slack / 2 at hF_bound
  change expectedCost _ ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN (spec.stages n r) s
    solveNext (autoFuel hm_grid hk_grid spec r)).compile qAssign _) Δ ≤ _
  rw [hauto]
  have hEF0 : 0 ≤ (1 - c) ^ F * (2 * (k : ℝ)) := mul_nonneg (pow_nonneg hq0 F) (by positivity)
  have hfinal := expectedCost_johnsonStageFuel_step res hm_grid hk_grid hn200 hmN spec hn0 hs
    hr2 hwk hcard solveNext hnext_cost hc_step hEF0 (hind F) Δ hV
  have hle_top : (spec.V r - slack / 2 + (1 - c) * ((1 - c) ^ F * (2 * (k : ℝ)))) * S₀ ≤
      spec.V r * S₀ := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hmul_le : (1 - c) * ((1 - c) ^ F * (2 * (k : ℝ))) ≤ 1 * ((1 - c) ^ F * (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right (by linarith) hEF0
    linarith
  exact hfinal.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle_top) zero_le)
private lemma m_le_two_pow_of_hn200 {m n : ℕ} (hm_grid : m ∈ groverGrid) (hn200 : 200 ≤ n) :
    m ≤ 2 ^ n := by
  calc m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
    _ ≤ 2 ^ 10 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
private noncomputable def johnsonSolveFrom {Var : Type} (res : Var) (n m k : ℕ)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n)
    (spec : JohnsonWalkSpec m k) : (s : ℕ) → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | s =>
      if hs : s < k then
        if _hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true then
          johnsonStageFuel res n m k hm_grid hk_grid hn200
            (m_le_two_pow_of_hn200 hm_grid hn200) (spec.stages n (k - s)) s
            (fun w _hw ↦ johnsonSolveFrom res n m k hm_grid hk_grid hn200 spec (s + w))
            (autoFuel hm_grid hk_grid spec (k - s))
        else
          .seq (eigLockStage res n m k hm_grid hk_grid hn200 ⟨s, hs⟩)
            (johnsonSolveFrom res n m k hm_grid hk_grid hn200 spec (s + 1))
      else .skip
termination_by s => k - s
decreasing_by all_goals omega
private lemma wp_johnsonSolveFrom_ge {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) (spec : JohnsonWalkSpec m k) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ B : ℕ, ∀ s : ℕ, k - s ≤ B → s ≤ k → validObs (Var := Var) n m k S s ≤
        wp ((johnsonSolveFrom res n m k hm_grid hk_grid hn200 spec s).compile qAssign
            (groverParallelMarkingOracle m S))
          (validObs n m k S k)
  | 0, s, hB, _ => by
    have hseq : s = k := (by omega); subst hseq; rw [johnsonSolveFrom, dite_eq_right (lt_irrefl s)]
    simp [compile]
  | B + 1, s, hB, hs_le => by
    by_cases hs : s < k
    · rw [johnsonSolveFrom, dite_eq_left hs]
      by_cases hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true
      · rw [dite_eq_left hwalk]
        exact wp_johnsonStageFuel_ge res hm_grid hk_grid hn200
          (m_le_two_pow_of_hn200 hm_grid hn200) hs_le (spec.stages n (k - s)) hcard _
          (fun w _hw1 hwb ↦ wp_johnsonSolveFrom_ge res hm_grid hk_grid hn200 spec hcard
            B (s + w) (by omega) (by omega))
          (autoFuel hm_grid hk_grid spec (k - s))
      · rw [dite_eq_right hwalk]; dsimp only [compile]; rw [wp_qSeq]
        have hih := wp_johnsonSolveFrom_ge res hm_grid hk_grid hn200 spec hcard
          B (s + 1) (by omega) (by omega)
        exact ((eigLockStage_wp_and_active res hm_grid hk_grid hn200 hcard ⟨s, hs⟩).1).trans
          (wp_mono _ hih)
    · have hseq : s = k := by omega
      subst hseq; rw [johnsonSolveFrom, dite_eq_right (lt_irrefl s)]; simp [compile]
private noncomputable def stageReqC {m k : ℕ} (spec : JohnsonWalkSpec m k) (r : ℕ) : ℝ :=
  if _hwalk : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true then
    let slack :=
      (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w * (spec.V r - spec.V (r - w))) - spec.tauSum r
    max 0 (spec.C_step + 1) / (slack / 2)
  else if _heig : 1 ≤ r ∧ r ≤ k then
    let gap := (spec.V r - spec.V (r - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ))
    5 / gap
  else 0
private noncomputable def maxUpTo (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => max 0 (f 0)
  | r + 1 => max (maxUpTo f r) (f (r + 1))
private lemma le_maxUpTo (f : ℕ → ℝ) {r K : ℕ} (hr : r ≤ K) : f r ≤ maxUpTo f K := by
  induction K with
  | zero => have hr0 : r = 0 := (by omega); subst hr0; exact le_max_right 0 (f 0)
  | succ K ih =>
    by_cases hlt : r ≤ K
    · exact (ih hlt).trans (le_max_left _ _)
    · have hreq : r = K + 1 := (by omega); subst hreq; exact le_max_right _ _
private lemma expectedCost_johnsonSolveFrom_le {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) (spec : JohnsonWalkSpec m k) (hn0 : spec.n0 ≤ n)
    (hreq : ∀ r : ℕ, 1 ≤ r → r ≤ k → stageReqC spec r ≤ √(2 ^ n : ℝ))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ B : ℕ, ∀ s : ℕ, k - s ≤ B → s ≤ k → ∀ Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
        𝔼[Δ, validObs n m k S s] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          ((johnsonSolveFrom res n m k hm_grid hk_grid hn200 spec s).compile qAssign
            (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ * ENNReal.ofReal (spec.V (k - s) * √(2 ^ n : ℝ))
  | 0, s, hB, _, Δ, _ => by
    have hseq : s = k := (by omega); subst hseq; rw [johnsonSolveFrom, dite_eq_right (lt_irrefl s)]
    simp [compile, spec.hV0]
  | B + 1, s, hB, hs_le, Δ, hV => by
    by_cases hs : s < k
    · rw [johnsonSolveFrom, dite_eq_left hs]
      by_cases hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true
      · rw [dite_eq_left hwalk]; have hr_req := hreq (k - s) (by omega) (by omega)
        have hwalk3 : 2 ≤ k - s ∧ k - s ≤ k ∧ spec.useWalk (k - s) = true :=
          ⟨hwalk.1, by omega, hwalk.2⟩
        rw [stageReqC, dite_eq_left hwalk3] at hr_req
        have hslack : 0 < (∑ w ∈ Finset.Icc 1 (min m (k - s)),
            spec.pLo (k - s) w * (spec.V (k - s) - spec.V (k - s - w))) - spec.tauSum (k - s) :=
          sub_pos.mpr (spec.hdrift_lt (k - s) hwalk.1 (by omega) hwalk.2)
        have hc_step : max 0 (spec.C_step + 1) ≤ (((∑ w ∈ Finset.Icc 1 (min m (k - s)),
                spec.pLo (k - s) w * (spec.V (k - s) - spec.V (k - s - w))) -
              spec.tauSum (k - s)) / 2) * √(2 ^ n : ℝ) := by
          linarith [(div_le_iff₀ (half_pos hslack)).mp hr_req]
        exact expectedCost_johnsonStageFuel_le res hm_grid hk_grid hn200
          (m_le_two_pow_of_hn200 hm_grid hn200) spec hn0 hs hwalk.1 hwalk.2 hcard _
          (fun w _hw1 hwb Γ hΓ ↦ by
            have hih := expectedCost_johnsonSolveFrom_le res hm_grid hk_grid hn200 spec hn0 hreq
              hcard B (s + w) (by omega) (by omega) Γ hΓ
            rwa [show k - (s + w) = k - s - w by omega] at hih)
          hc_step Δ hV
      · rw [dite_eq_right hwalk]; dsimp only [compile]; rw [expectedCost_qSeq]
        let r := k - s
        let stageP := (eigLockStage (Var := Var) res n m k hm_grid hk_grid hn200 ⟨s, hs⟩).compile
          qAssign (groverParallelMarkingOracle m S)
        have hwp_st := (eigLockStage_wp_and_active (Var := Var) res hm_grid hk_grid hn200 hcard
          ⟨s, hs⟩).1
        have hstep_V := jp01_validState_step hV hwp_st
        have hcost_st := expectedCost_eigLockStage_le res hm_grid hk_grid hn200 hcard ⟨s, hs⟩ hV
        have hih := expectedCost_johnsonSolveFrom_le res hm_grid hk_grid hn200 spec hn0 hreq
          hcard B (s + 1) (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
        rw [hstep_V.2, show k - (s + 1) = r - 1 by omega] at hih
        have hn600 : 600 ≤ n := spec.hn0.trans hn0
        have hlin := jp01_stageCostReal_le_linear_S0 (k := k) (r := r) hn600 hm_grid hk_grid
          (by omega) (by omega)
        have hor : r = 1 ∨ spec.useWalk r = false := by
          by_cases hr2 : 2 ≤ r
          · right
            cases h : spec.useWalk r
            · rfl
            · exact False.elim (hwalk ⟨hr2, h⟩)
          · left; omega
        have hgap_pos : 0 < (spec.V r - spec.V (r - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) :=
          sub_pos.mpr (spec.hV_eig r (by omega) (by omega) hor)
        have hr_req := hreq r (by omega) (by omega)
        have hnwalk3 : ¬ (2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true) := fun h ↦ hwalk ⟨h.1, h.2.2⟩
        have heig2 : 1 ≤ r ∧ r ≤ k := ⟨by omega, by omega⟩
        rw [stageReqC, dite_eq_right hnwalk3, dite_eq_left heig2] at hr_req
        have h5_le := (div_le_iff₀ hgap_pos).mp hr_req
        have hst_le : stageCostReal n m r ≤ (spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ) := by
          have hsqrt_div : √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) =
              √(2 ^ n : ℝ) / √((m : ℝ) * (r : ℝ)) := Real.sqrt_div (by positivity) _
          have hrew : (π / 8 + 1 / 4) * (√(2 ^ n : ℝ) / √((m : ℝ) * (r : ℝ))) =
              ((π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ))) * √(2 ^ n : ℝ) := by ring
          have hlin2 := hlin.2; rw [hsqrt_div, hrew] at hlin2; linarith
        have hd_nn : 0 ≤ (spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ) :=
          mul_nonneg (sub_nonneg.mpr (spec.hV_mono (by omega) (by omega))) (Real.sqrt_nonneg _)
        have hcont_nn : 0 ≤ spec.V (r - 1) * √(2 ^ n : ℝ) :=
          mul_nonneg (spec_V_nonneg spec (by omega)) (Real.sqrt_nonneg _)
        calc expectedCost _ stageP Δ + expectedCost _ _ ((interp stageP).toStateFun Δ)
            ≤ stateMass Δ * ENNReal.ofReal ((spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ)) +
                stateMass Δ * ENNReal.ofReal (spec.V (r - 1) * √(2 ^ n : ℝ)) :=
              add_le_add
                (hcost_st.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hst_le)
                  zero_le))
                hih
          _ = stateMass Δ * (ENNReal.ofReal ((spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ)) +
                  ENNReal.ofReal (spec.V (r - 1) * √(2 ^ n : ℝ))) := by ring
          _ = stateMass Δ * ENNReal.ofReal (spec.V r * √(2 ^ n : ℝ)) := by
              congr 1
              rw [← ENNReal.ofReal_add hd_nn hcont_nn]
              congr 1
              ring
    · have hseq : s = k := by omega
      subst hseq; rw [johnsonSolveFrom, dite_eq_right (lt_irrefl s)]; simp [compile, spec.hV0]
/-- Turnkey parallel query-model circuit executing `JohnsonWalkSpec` with finite-fuel
  renewal for
  `200 ≤ n` and delegating to `Stage1.circuit` for `n < 200`. -/
noncomputable def johnsonCircuit {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonWalkSpec m k) (n : ℕ) :
    OracleCirc Var (Stage1.qubits n m k) ((n + 1) * m) :=
  if hn200 : 200 ≤ n then
    .seq (johnsonSolveFrom res n m k hm_grid hk_grid hn200 spec 0)
      (.measure res (highBlock (m * (n + 1)) (k * n)))
  else
    Stage1.circuit res n m k
/-- `johnsonCircuit` recovers the full marked set `S` via `decodeTargets n k (σ res) = S`
  with
  probability `1` for every `1 ≤ n`, `k ≤ 2 ^ n`, and `S ∈ groverTargetSets n k`. -/
theorem johnsonCircuit_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSpec m k) (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;; (johnsonCircuit res hm_grid hk_grid spec n).compile qAssign
      (groverParallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ := by
  by_cases hn200 : 200 ≤ n
  · unfold johnsonCircuit; rw [dite_eq_left hn200]; unfold Stage1.qubits
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
      liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)
    refine Triple.of_eq_wp ?_
    symm
    dsimp only [compile]; rw [wp_qSeq, wp_qSeq]; have hmeas_ge : validObs (Var := Var) n m k S k ≤
        wp (measureRegister res (highBlock (m * (n + 1)) (k * n))) post :=
      validObs_le_wp_measure_decodeTargets res hcard
    have hst_ge := wp_johnsonSolveFrom_ge (Var := Var) res hm_grid hk_grid hn200 spec hcard
      k 0 le_rfl (Nat.zero_le k)
    have htot_ge := hst_ge.trans (wp_mono _ hmeas_ge)
    have hqset_ge := (wp_qSet_validObs_zero (Var := Var) n m k S).symm.le.trans
      (wp_mono .qSet htot_ge)
    exact top_unique hqset_ge
  · unfold johnsonCircuit; rw [dite_eq_right hn200]
    have hcells : Stage1.cells m k = true := (by simp [Stage1.cells, gridCells, hm_grid, hk_grid])
    exact Stage1.correctness res hn hcells hkN hS
/-- Asymptotic uniform-average expected parallel-round cost bound for `johnsonCircuit`
  relative to
  `vanillaFindAllCost` from `spec.V k ≤ rel * (π / 4) * groverHarmonicSqrtSum k / √m`. -/
theorem johnsonCircuit_rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonWalkSpec m k) {rel : ℝ}
    (hV_top : spec.V k ≤ rel * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ)) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (fun S ↦
          qset ;; (johnsonCircuit res hm_grid hk_grid spec n).compile qAssign
            (groverParallelMarkingOracle m S))
        (rel * vanillaFindAllCost n m k) := by
  let M_req := maxUpTo (stageReqC spec) k; obtain ⟨N_arch, hN_arch⟩ := exists_nat_ge (M_req ^ 2)
  refine ⟨max spec.n0 N_arch, fun n hn hkN ↦ ?_⟩
  have hn0 : spec.n0 ≤ n := (le_max_left _ _).trans hn
  have hN : N_arch ≤ n := (le_max_right _ _).trans hn
  have hn200 : 200 ≤ n := (by have := spec.hn0; omega)
  have hM_le : M_req ≤ √(2 ^ n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc M_req ^ 2 ≤ (N_arch : ℝ) := hN_arch
      _ ≤ (n : ℝ) := by exact_mod_cast hN
      _ ≤ (2 ^ n : ℝ) := by exact_mod_cast n.lt_two_pow_self.le
  have hreq : ∀ r : ℕ, 1 ≤ r → r ≤ k → stageReqC spec r ≤ √(2 ^ n : ℝ) :=
    fun r _ hrk ↦ (le_maxUpTo (stageReqC spec) hrk).trans hM_le
  have hcirc_eq : johnsonCircuit (Var := Var) res hm_grid hk_grid spec n = .seq (johnsonSolveFrom
    res n m k hm_grid hk_grid hn200 spec 0) (.measure res (highBlock (m * (n + 1)) (k * n))) := by
    unfold johnsonCircuit; exact dite_eq_left hn200
  let q_val : ℝ≥0 := Real.toNNReal (spec.V k * √(2 ^ n : ℝ))
  simp_rw [hcirc_eq]; unfold Stage1.qubits; refine ⟨fun _ ↦ q_val, fun S hS state ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    set oracle := groverParallelMarkingOracle m S
    set model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
    dsimp only [compile]; rw [expectedCost_qSeq, expectedCost_qSet]
    have hreset0 : model.resetCost = 0 := rfl; rw [hreset0]
    simp only [Nat.cast_zero, mul_zero, zero_add]; rw [expectedCost_qSeq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n m k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]; rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
      exact congrArg NNReal.toReal (CQState.trace_qSet state).symm
    have hmass0 : stateMass Δ₀ = stateMass state := Lossless.qSet state
    have hmeas0 : expectedCost model (measureRegister res (highBlock (m * (n + 1)) (k * n)))
        ((interp ((johnsonSolveFrom res n m k hm_grid hk_grid hn200 spec 0).compile qAssign
            oracle)).toStateFun Δ₀) = 0 := by
      have hm_cb : CostBound (Var := Var) model
          (measureRegister res (highBlock (m * (n + 1)) (k * n))) 0 := by
        simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
          CostBound.qMeasure (Var := Var) model res _
      exact nonpos_iff_eq_zero.mp (by simpa using hm_cb _)
    rw [hmeas0, add_zero]
    have hst := expectedCost_johnsonSolveFrom_le res hm_grid hk_grid hn200 spec hn0 hreq hcard
      k 0 le_rfl (Nat.zero_le k) Δ₀ hV0
    rw [Nat.sub_zero, hmass0] at hst; exact hst
  · have hVk0 : 0 ≤ spec.V k * √(2 ^ n : ℝ) :=
      mul_nonneg (spec_V_nonneg spec le_rfl) (Real.sqrt_nonneg _)
    have hsum_le : (q_val : ℝ) ≤ rel * vanillaFindAllCost n m k := by
      calc (q_val : ℝ) = spec.V k * √(2 ^ n : ℝ) := Real.coe_toNNReal _ hVk0
        _ ≤ (rel * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ)) * √(2 ^ n : ℝ) :=
            mul_le_mul_of_nonneg_right hV_top (Real.sqrt_nonneg _)
        _ = rel * ((π / 4) * groverHarmonicSqrtSum k * (√(2 ^ n : ℝ) / √(m : ℝ))) := by ring
        _ = rel * vanillaFindAllCost n m k := by
            unfold vanillaFindAllCost; rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n)]
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      have hc : (groverTargetSets n k).card = Nat.choose (2 ^ n) k := (by simp [groverTargetSets])
      rw [hc]; exact_mod_cast Nat.choose_pos hkN
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']; exact hsum_le
/-! ## 5. Sparse-Anchor Renewal Engine (`JohnsonWalkSparseSpec`) -/
private noncomputable def sparseSlack {m k : ℕ} (spec : JohnsonWalkSparseSpec m k) (r : ℕ) : ℝ :=
  spec.V r - (spec.tauSum r + ∑ w ∈ Finset.Icc 0 (min m r), spec.pLo r w * spec.V (r - w) +
    (1 - ∑ w ∈ Finset.Icc 0 (min m r), spec.pLo r w) * spec.V_max)
private lemma sparse_pLo_sum_le_one {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSparseSpec m k) {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hwk : spec.useWalk r = true) : (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w) ≤ 1 ∧
      ∀ w ∈ Finset.Icc 0 (min m r), spec.pLo r w ≤ 1 := by
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid; have hn0 : 600 ≤ spec.n0 := spec.hn0
  have h1024 : 1024 ≤ 2 ^ spec.n0 := by
    calc 1024 ≤ 2 ^ 10 := by norm_num
      _ ≤ 2 ^ spec.n0 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmN₀ : m ≤ 2 ^ spec.n0 := hm_hi.trans h1024
  have hrN₀ : r ≤ 2 ^ spec.n0 := (hrk.trans hk_hi).trans h1024
  let R₀ : Finset (Fin (2 ^ spec.n0)) :=
    (Finset.range r).attach.image fun x ↦ ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hrN₀⟩
  have hR₀ : R₀.card = r := by
    rw [Finset.card_image_of_injective _ (fun a b h ↦ Subtype.ext (Fin.mk.inj h)),
      Finset.card_attach, Finset.card_range]
  let v₀ := evalSymStages R₀ (spec.stages spec.n0 r) (u0Vec (2 ^ spec.n0) m)
  have hsum0_le : (∑ w ∈ Finset.Icc 0 (min m r), spec.pLo r w) ≤ 1 := by
    calc ∑ w ∈ Finset.Icc 0 (min m r), spec.pLo r w
        ≤ ∑ w ∈ Finset.Icc 0 (min m r), symHitProb R₀ v₀ w :=
          Finset.sum_le_sum fun w hw ↦ spec.hpLo_le spec.n0 r le_rfl hr2 hrk hwk R₀ hR₀ w hw
      _ ≤ ∑ w ∈ Finset.range (min m R₀.card + 1), symHitProb R₀ v₀ w := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw ↦ ?_)
            (fun w _ _ ↦ symHitProb_nonneg R₀ v₀ w)
          rcases Finset.mem_Icc.mp hw with ⟨_, hwb⟩; rw [Finset.mem_range, hR₀]; omega
      _ = 1 := sum_symHitProb_evalSymStages hmN₀ R₀ _
  have hsum1_le : (∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w) ≤ 1 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (Nat.zero_le 1))
      (fun w _ _ ↦ spec.hpLo_nonneg r w)).trans hsum0_le
  refine ⟨hsum1_le, fun w hw ↦ ?_⟩
  exact (Finset.single_le_sum (fun u _ ↦ spec.hpLo_nonneg r u) hw).trans hsum0_le
private noncomputable def sparseAutoFuel {m k : ℕ} (hm_grid : m ∈ groverGrid)
    (hk_grid : k ∈ groverGrid) (spec : JohnsonWalkSparseSpec m k) (r : ℕ) : ℕ :=
  open Classical in
  if h : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true then
    let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
    let slack := sparseSlack spec r
    have hc_pos : 0 < c := spec.hpLo_sum_pos r h.1 h.2.1 h.2.2
    have hc_le1 : c ≤ 1 := (sparse_pLo_sum_le_one hm_grid hk_grid spec h.1 h.2.1 h.2.2).1
    have hslack : 0 < slack := sub_pos.mpr (spec.hdrift_sparse_lt r h.1 h.2.1 h.2.2)
    have hq0 : 0 ≤ 1 - c := by linarith
    have hq1 : 1 - c < 1 := by linarith
    have heps : 0 < (slack / 2) / (2 * (k : ℝ) + 1) := by positivity
    (Classical.choose (pow_small_of_pos_lt_one hq0 hq1 heps)) + 1
  else 1
private lemma sparseAutoFuel_spec {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSparseSpec m k) {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hwk : spec.useWalk r = true) :
    let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
    ∃ F : ℕ, sparseAutoFuel hm_grid hk_grid spec r = F + 1 ∧
      (1 - c) ^ F * (2 * (k : ℝ)) ≤ sparseSlack spec r / 2 := by
  intro c; let slack := sparseSlack spec r
  have hcond : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true := ⟨hr2, hrk, hwk⟩
  have hc_pos : 0 < c := spec.hpLo_sum_pos r hr2 hrk hwk
  have hc_le1 : c ≤ 1 := (sparse_pLo_sum_le_one hm_grid hk_grid spec hr2 hrk hwk).1
  have hslack : 0 < slack := sub_pos.mpr (spec.hdrift_sparse_lt r hr2 hrk hwk)
  have hq0 : 0 ≤ 1 - c := (by linarith); have hq1 : 1 - c < 1 := (by linarith)
  have heps : 0 < (slack / 2) / (2 * (k : ℝ) + 1) := (by positivity)
  let F := Classical.choose (pow_small_of_pos_lt_one hq0 hq1 heps)
  have hF : (1 - c) ^ F ≤ (slack / 2) / (2 * (k : ℝ) + 1) :=
    Classical.choose_spec (pow_small_of_pos_lt_one hq0 hq1 heps)
  refine ⟨F, ?_, ?_⟩
  · unfold sparseAutoFuel; rw [dite_eq_left hcond]
  · have hden_pos : (0 : ℝ) < 2 * (k : ℝ) + 1 := (by positivity)
    have h1 : (1 - c) ^ F * (2 * (k : ℝ) + 1) ≤ slack / 2 := (le_div_iff₀ hden_pos).mp hF
    have hqF0 : 0 ≤ (1 - c) ^ F := pow_nonneg hq0 F; nlinarith
private lemma expectedCost_johnsonStageFuel_sparse_step {Var : Type} [DecidableEq Var] {n m k s :
    ℕ} (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hmN :
    m ≤ 2 ^ n) (spec : JohnsonWalkSparseSpec m k) (hn0 : spec.n0 ≤ n) (hs : s < k) (hr2 : 2 ≤ k -
    s) (hwk : spec.useWalk (k - s) = true) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (solveNext : (w : ℕ) → 1 ≤ w → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (hnext_cost
    : ∀ w (hw1 : 1 ≤ w), w ≤ min m (k - s) → ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
      𝔼[Γ,
    validObs n m k S (s + w)] = Γ.trace → expectedCost (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((solveNext w hw1).compile qAssign
    (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ * ENNReal.ofReal (spec.V (k - s - w) * √(2
    ^ n : ℝ))) (hc_step : max 0 (spec.C_step + 1) ≤ (sparseSlack spec (k - s) / 2) * √(2 ^ n : ℝ))
    {fuel : ℕ} {E_f : ℝ} (hE0 : 0 ≤ E_f) (hfuel_cost : ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) +
      k *
    n)), 𝔼[Γ, validObs n m k S s] = Γ.trace → expectedCost (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN
    (spec.stages n (k - s)) s solveNext fuel).compile qAssign (groverParallelMarkingOracle m S)) Γ
    ≤ stateMass Γ * ENNReal.ofReal ((spec.V (k - s) + E_f) * √(2 ^ n : ℝ))) (Δ : CQState (Store Var)
      (2 ^
    (m * (n + 1) + k * n))) (hV : 𝔼[Δ, validObs n m k S s] = Δ.trace) :
    let r := k - s; let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
    expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) ((johnsonStageFuel
      res n m k hm_grid hk_grid hn200 hmN (spec.stages n r) s solveNext (fuel + 1)).compile
      qAssign (groverParallelMarkingOracle m S)) Δ ≤ stateMass Δ * ENNReal.ofReal ((spec.V r -
      sparseSlack spec r / 2 + (1 - c) * E_f) * √(2 ^ n : ℝ)) := by
  intro r c; let slack := sparseSlack spec r; let b := min m r; let S₀ := √(2 ^ n : ℝ)
  have hS₀_pos : 0 < S₀ := (by positivity); let oracle := groverParallelMarkingOracle m S
  let model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
  let stages := spec.stages n r; have hrk : r ≤ k := Nat.sub_le k s
  have hp_le1 := sparse_pLo_sum_le_one hm_grid hk_grid spec hr2 hrk hwk
  have h0_mem : 0 ∈ Finset.Icc 0 b := Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le b⟩
  have hdisp_wp := wp_johnsonPassFront_dispPre (Var := Var) res (k := k) (s := s) hmN hs.le
    stages hcard
  have h0_wp := wp_johnsonPassFront_hitProb (Var := Var) res (k := k) (s := s) (w := 0) hmN hs.le
    stages hcard (spec.hpLo_nonneg r 0) (hp_le1.2 0 h0_mem)
    (fun R hR ↦ spec.hpLo_le n r hn0 hr2 hrk hwk R hR 0 h0_mem)
  have hhit_wp (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :=
    wp_johnsonPassFront_hitProb (Var := Var) res (k := k) (s := s) (w := w) hmN hs.le
      stages hcard (spec.hpLo_nonneg r w)
      (hp_le1.2 w (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hw))
      (fun R hR ↦ spec.hpLo_le n r hn0 hr2 hrk hwk R hR w
        (Finset.Icc_subset_Icc_left (Nat.zero_le 1) hw))
  have hfr_cb := costBound_johnsonPassFront (Var := Var) res (k := k) (s := s) hmN stages S Δ
  unfold johnsonStageFuel; dsimp only [compile]
  generalize (johnsonPassFront (Var := Var) res n m k s hmN stages).compile qAssign oracle = P_fr
    at hdisp_wp h0_wp hhit_wp hfr_cb ⊢
  let Δ₁ := (interp P_fr).toStateFun Δ
  have htr_le : (Δ₁.trace : ℝ) ≤ Δ.trace := (by exact_mod_cast (interp P_fr).trace_toStateFun_le Δ)
  have hdisp_tr : 𝔼[Δ₁, dispPre res n m k S s b] = Δ₁.trace := by
    have h1 : (Δ.trace : ℝ) ≤ 𝔼[Δ₁, dispPre res n m k S s b] := by
      rw [← hV, ← wp_expectation_eq]; exact expect_mono le_rfl hdisp_wp
    have h2 : 𝔼[Δ₁, dispPre res n m k S s b] ≤ Δ₁.trace := by
      rw [← expect_top Δ₁]; exact expect_mono le_rfl le_top
    linarith
  have hbr_val := expect_restrict_valid_branches res hdisp_tr
  have hp0_mass : spec.pLo r 0 * Δ.trace ≤ (Δ₁.restrict (hitPred res 0)).trace := by
    calc spec.pLo r 0 * Δ.trace = 𝔼[Δ, scaledValidObs n m k S s (spec.pLo r 0) (spec.hpLo_nonneg r
          0) (hp_le1.2 0 h0_mem)] := by
          rw [expect_eq_mul_of_apply_eq_smul Δ _ (scaledValidObs_smul n m k S s _ _ _), hV]
      _ ≤ 𝔼[Δ, wp P_fr (liftPureProp (hitPred res 0))] := expect_mono le_rfl h0_wp
      _ = 𝔼[Δ₁, liftPureProp (hitPred res 0)] := wp_expectation_eq P_fr Δ _
      _ = (Δ₁.restrict (hitPred res 0)).trace := expect_liftPureProp (hitPred res 0) Δ₁
  have h0_le_m0 :
      ((Δ₁.restrict (hitPred res 0)).trace : ℝ) ≤ (Δ₁.restrict (missPred res b)).trace := by
    have h0_sub : (Δ₁.restrict (missPred res b)).restrict (hitPred res 0) =
        Δ₁.restrict (hitPred res 0) := by
      apply Subtype.ext; funext σ; simp only [CQState.restrict_coe]; by_cases h0 : hitPred res 0 σ
      · have hm : missPred res b σ := fun w hw ↦ by
          rcases Finset.mem_Icc.mp hw with ⟨hw1, _⟩; dsimp only [hitPred] at h0; omega
        simp [h0, hm]
      · simp [h0]
    have hsplit := (Δ₁.restrict (missPred res b)).trace_restrict_add_trace_restrict_not
      (hitPred res 0)
    rw [h0_sub] at hsplit
    exact NNReal.coe_le_coe.mpr (le_self_add.trans_eq hsplit)
  have hp_mass (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
      spec.pLo r w * Δ.trace ≤ (Δ₁.restrict (hitPred res w)).trace := by
    have hwp_p := hhit_wp w hw
    have hw0 : w ∈ Finset.Icc 0 b := Finset.Icc_subset_Icc_left (Nat.zero_le 1) hw
    calc spec.pLo r w * Δ.trace = 𝔼[Δ, scaledValidObs n m k S s (spec.pLo r w) (spec.hpLo_nonneg r
          w) (hp_le1.2 w hw0)] := by
          rw [expect_eq_mul_of_apply_eq_smul Δ _ (scaledValidObs_smul n m k S s _ _ _), hV]
      _ ≤ 𝔼[Δ, wp P_fr (liftPureProp (hitPred res w))] := expect_mono le_rfl hwp_p
      _ = 𝔼[Δ₁, liftPureProp (hitPred res w)] := wp_expectation_eq P_fr Δ _
      _ = (Δ₁.restrict (hitPred res w)).trace := expect_liftPureProp (hitPred res w) Δ₁
  let onHit := fun w ↦ if hw : 1 ≤ w then solveNext w hw else .skip
  let onZero := johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN stages s solveNext fuel
  obtain ⟨htr_part, hcost_disp⟩ := dispHits_trace_and_cost res oracle model onHit onZero b Δ₁
  rw [expectedCost_qSeq]; change expectedCost model P_fr Δ +
    expectedCost model ((dispHits res onHit onZero b).compile qAssign oracle) Δ₁ ≤ _
  rw [hcost_disp]
  have hfr_real : ((stagesQueryCount stages + 1 : ℕ) : ℝ) ≤ (spec.tauSum r + slack / 2) * S₀ := by
    have hlen := spec.hstages_len n r hn0 hr2 hrk hwk
    have hc_le : spec.C_step + 1 ≤ (slack / 2) * S₀ := (le_max_right 0 _).trans hc_step; push_cast
    linarith
  have hfr_cost : expectedCost model P_fr Δ ≤
      ENNReal.ofReal (Δ.trace * ((spec.tauSum r + slack / 2) * S₀)) := by
    calc expectedCost model P_fr Δ
        ≤ stateMass Δ * (((stagesQueryCount stages : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) := hfr_cb
      _ = ENNReal.ofReal Δ.trace * ENNReal.ofReal ((stagesQueryCount stages + 1 : ℕ) : ℝ) := by
          rw [stateMass_eq_ofReal_trace, ENNReal.ofReal_natCast]; push_cast; rfl
      _ ≤ ENNReal.ofReal Δ.trace * ENNReal.ofReal ((spec.tauSum r + slack / 2) * S₀) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hfr_real) zero_le
      _ = ENNReal.ofReal (Δ.trace * ((spec.tauSum r + slack / 2) * S₀)) :=
          (ENNReal.ofReal_mul Δ.trace_nonneg).symm
  have hzero_cost : expectedCost model (onZero.compile qAssign oracle) (Δ₁.restrict (missPred res
    b)) ≤ ENNReal.ofReal ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀)) := by
    calc expectedCost model (onZero.compile qAssign oracle) (Δ₁.restrict (missPred res b))
        ≤ stateMass (Δ₁.restrict (missPred res b)) * ENNReal.ofReal ((spec.V r + E_f) * S₀) :=
          hfuel_cost _ hbr_val.1
      _ = ENNReal.ofReal ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀)) := by
          rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_mul (CQState.trace_nonneg _)]
  have hhit_cost (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
      expectedCost model ((onHit w).compile qAssign oracle) (Δ₁.restrict (hitPred res w)) ≤
        ENNReal.ofReal ((Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) := by
    rcases Finset.mem_Icc.mp hw with ⟨hw1, hwb⟩; dsimp only [onHit]; rw [dite_eq_left hw1]
    calc expectedCost model ((solveNext w hw1).compile qAssign oracle) (Δ₁.restrict (hitPred res
          w)) ≤ stateMass (Δ₁.restrict (hitPred res w)) * ENNReal.ofReal (spec.V (r - w) * S₀) :=
          hnext_cost w hw1 hwb _ (hbr_val.2 w hw)
      _ = ENNReal.ofReal ((Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) := by
          rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_mul (CQState.trace_nonneg _)]
  have hsum_hit : (∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit w).compile qAssign oracle)
    (Δ₁.restrict (hitPred res w))) ≤ ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict (hitPred
    res w)).trace * (spec.V (r - w) * S₀)) := by
    calc ∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit w).compile qAssign oracle) (Δ₁.restrict
          (hitPred res w)) ≤ ∑ w ∈ Finset.Icc 1 b, ENNReal.ofReal ((Δ₁.restrict (hitPred res
          w)).trace * (spec.V (r - w) * S₀)) := Finset.sum_le_sum hhit_cost
      _ = ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b,
            (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun w _ ↦ mul_nonneg (CQState.trace_nonneg _)
            (mul_nonneg (spec.hV_bounds (r - w) (by omega)).1 hS₀_pos.le)]
  have hfr_nn : 0 ≤ Δ.trace * ((spec.tauSum r + slack / 2) * S₀) := by
    have htau_sl : 0 ≤ spec.tauSum r + slack / 2 := by
      have hpos : (0 : ℝ) < (stagesQueryCount stages + 1 : ℕ) := (by positivity)
      exact nonneg_of_mul_nonneg_left (hpos.le.trans hfr_real) hS₀_pos
    exact mul_nonneg Δ.trace_nonneg (mul_nonneg htau_sl hS₀_pos.le)
  have hz_nn : 0 ≤ (Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀) := mul_nonneg
    (CQState.trace_nonneg _) (mul_nonneg (add_nonneg (spec.hV_bounds r hrk).1 hE0) hS₀_pos.le)
  have hs_nn : 0 ≤ ∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) *
    S₀) := Finset.sum_nonneg fun w _ ↦ mul_nonneg (CQState.trace_nonneg _) (mul_nonneg
    (spec.hV_bounds (r - w) (by omega)).1 hS₀_pos.le)
  have halg : Δ.trace * ((spec.tauSum r + slack / 2) * S₀) +
        ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀) +
          ∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀)) ≤
      Δ.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by
    let m₀ : ℝ := (Δ₁.restrict (missPred res b)).trace
    let mw : ℕ → ℝ := fun w ↦ (Δ₁.restrict (hitPred res w)).trace
    let pAct : ℕ → ℝ := fun w ↦ if w = 0 then m₀ else mw w
    have hIcc0_eq : Finset.Icc 0 b = insert 0 (Finset.Icc 1 b) := by
      ext w; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h0_not : (0 : ℕ) ∉ Finset.Icc 1 b := (by simp)
    have htr_part_r : m₀ + ∑ w ∈ Finset.Icc 1 b, mw w = Δ₁.trace := by
      dsimp only [m₀, mw]; exact_mod_cast htr_part
    have hm_tot : m₀ + ∑ w ∈ Finset.Icc 1 b, mw w ≤ Δ.trace := htr_part_r.trans_le htr_le
    have hpAct_tot : ∑ w ∈ Finset.Icc 0 b, pAct w ≤ Δ.trace := by
      rw [hIcc0_eq, Finset.sum_insert h0_not]
      have htail : ∑ w ∈ Finset.Icc 1 b, pAct w = ∑ w ∈ Finset.Icc 1 b, mw w := by
        refine Finset.sum_congr rfl fun w hw ↦ ?_
        have hw0 : w ≠ 0 := (by rcases Finset.mem_Icc.mp hw with ⟨hw1, _⟩; omega); simp [pAct, hw0]
      dsimp only [pAct]; rw [ite_eq_left rfl, htail]; exact hm_tot
    have hpAct_ge (w : ℕ) (hw : w ∈ Finset.Icc 0 b) : spec.pLo r w * Δ.trace ≤ pAct w := by
      by_cases hw0 : w = 0
      · subst hw0; simp only [pAct, ite_true]; exact hp0_mass.trans h0_le_m0
      · simp only [pAct, hw0, ite_false]
        exact hp_mass w (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hw).2⟩)
    have hc_mass : c * Δ.trace ≤ ∑ w ∈ Finset.Icc 1 b, mw w := by
      dsimp only [c]; rw [Finset.sum_mul]; exact Finset.sum_le_sum hp_mass
    have hm0_le : m₀ ≤ (1 - c) * Δ.trace := (by linarith)
    have hVmax0 : 0 ≤ spec.V_max :=
      (spec.hV_bounds 0 (Nat.zero_le k)).1.trans (spec.hV_bounds 0 (Nat.zero_le k)).2
    have hdrop : (∑ w ∈ Finset.Icc 0 b, spec.pLo r w * (spec.V_max - spec.V (r - w))) * Δ.trace ≤
          ∑ w ∈ Finset.Icc 0 b, pAct w * (spec.V_max - spec.V (r - w)) := by
      rw [Finset.sum_mul]; refine Finset.sum_le_sum fun w hw ↦ ?_
      have hd_nn : 0 ≤ spec.V_max - spec.V (r - w) :=
        sub_nonneg.mpr (spec.hV_bounds (r - w) (by omega)).2
      calc spec.pLo r w * (spec.V_max - spec.V (r - w)) * Δ.trace
          = (spec.pLo r w * Δ.trace) * (spec.V_max - spec.V (r - w)) := by ring
        _ ≤ pAct w * (spec.V_max - spec.V (r - w)) :=
            mul_le_mul_of_nonneg_right (hpAct_ge w hw) hd_nn
    have hid : m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀) =
          ((∑ w ∈ Finset.Icc 0 b, pAct w) * spec.V_max -
            (∑ w ∈ Finset.Icc 0 b, pAct w * (spec.V_max - spec.V (r - w))) + m₀ * E_f) * S₀ := by
      have hp_split : ∑ w ∈ Finset.Icc 0 b, pAct w * spec.V (r - w) =
            m₀ * spec.V r + ∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w) := by
        rw [hIcc0_eq, Finset.sum_insert h0_not]
        have htail : ∑ w ∈ Finset.Icc 1 b, pAct w * spec.V (r - w) =
            ∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w) := by
          refine Finset.sum_congr rfl fun w hw ↦ ?_
          have hw0 : w ≠ 0 := (by rcases Finset.mem_Icc.mp hw with ⟨hw1, _⟩; omega)
          simp [pAct, hw0]
        dsimp only [pAct]; rw [ite_eq_left rfl, Nat.sub_zero, htail]
      have hcap_split : ∑ w ∈ Finset.Icc 0 b, pAct w * spec.V (r - w) = (∑ w ∈ Finset.Icc 0 b,
        pAct w) * spec.V_max - ∑ w ∈ Finset.Icc 0 b, pAct w * (spec.V_max - spec.V (r - w)) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun w _ ↦ by ring
      have hmul_s0 : ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀) =
            (∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w)) * S₀ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun w _ ↦ by ring
      change m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀) = _
      rw [hmul_s0]
      have hp_eq : m₀ * spec.V r + ∑ w ∈ Finset.Icc 1 b, mw w * spec.V (r - w) = (∑ w ∈ Finset.Icc
        0 b, pAct w) * spec.V_max - ∑ w ∈ Finset.Icc 0 b, pAct w * (spec.V_max - spec.V (r - w))
        := hp_split.symm.trans hcap_split
      linarith [congrArg (· * S₀) hp_eq]
    change Δ.trace * ((spec.tauSum r + slack / 2) * S₀) +
      (m₀ * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b, mw w * (spec.V (r - w) * S₀)) ≤ _
    rw [hid]
    have h1 : (∑ w ∈ Finset.Icc 0 b, pAct w) * spec.V_max ≤ Δ.trace * spec.V_max :=
      mul_le_mul_of_nonneg_right hpAct_tot hVmax0
    have h2 : m₀ * E_f ≤ (1 - c) * Δ.trace * E_f := mul_le_mul_of_nonneg_right hm0_le hE0
    have hpLo_id : ∑ w ∈ Finset.Icc 0 b, spec.pLo r w * (spec.V_max - spec.V (r - w)) =
          (∑ w ∈ Finset.Icc 0 b, spec.pLo r w) * spec.V_max -
            ∑ w ∈ Finset.Icc 0 b, spec.pLo r w * spec.V (r - w) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun w _ ↦ by ring
    have hslack_def : slack = spec.V r - (spec.tauSum r + ∑ w ∈ Finset.Icc 0 b, spec.pLo r w *
      spec.V (r - w) + (1 - ∑ w ∈ Finset.Icc 0 b, spec.pLo r w) * spec.V_max) := rfl
    have hmid : Δ.trace * (spec.tauSum r + slack / 2) + ((∑ w ∈ Finset.Icc 0 b, pAct w) *
      spec.V_max - (∑ w ∈ Finset.Icc 0 b, pAct w * (spec.V_max - spec.V (r - w))) + m₀ * E_f) ≤
      Δ.trace * (spec.V r - slack / 2 + (1 - c) * E_f) := by
      have hlin_id : Δ.trace * (spec.tauSum r + slack / 2) + Δ.trace * spec.V_max - (∑ w ∈
        Finset.Icc 0 b, spec.pLo r w * (spec.V_max - spec.V (r - w))) * Δ.trace + (1 - c) *
        Δ.trace * E_f = Δ.trace * (spec.V r - slack / 2 + (1 - c) * E_f) := by
        rw [hpLo_id, hslack_def]; ring
      linarith [h1, h2, hdrop, hlin_id]
    calc Δ.trace * ((spec.tauSum r + slack / 2) * S₀) +
          (((∑ w ∈ Finset.Icc 0 b, pAct w) * spec.V_max -
            (∑ w ∈ Finset.Icc 0 b, pAct w * (spec.V_max - spec.V (r - w))) + m₀ * E_f) * S₀)
        = (Δ.trace * (spec.tauSum r + slack / 2) + ((∑ w ∈ Finset.Icc 0 b, pAct w) * spec.V_max -
              (∑ w ∈ Finset.Icc 0 b, pAct w * (spec.V_max - spec.V (r - w))) + m₀ * E_f)) * S₀ :=
            by ring
      _ ≤ (Δ.trace * (spec.V r - slack / 2 + (1 - c) * E_f)) * S₀ :=
          mul_le_mul_of_nonneg_right hmid hS₀_pos.le
      _ = Δ.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by ring
  calc expectedCost model P_fr Δ + (expectedCost model (onZero.compile qAssign oracle)
        (Δ₁.restrict (missPred res b)) + ∑ w ∈ Finset.Icc 1 b, expectedCost model ((onHit
        w).compile qAssign oracle) (Δ₁.restrict (hitPred res w))) ≤ ENNReal.ofReal (Δ.trace *
        ((spec.tauSum r + slack / 2) * S₀)) + (ENNReal.ofReal ((Δ₁.restrict (missPred res
        b)).trace * ((spec.V r + E_f) * S₀)) + ENNReal.ofReal (∑ w ∈ Finset.Icc 1 b, (Δ₁.restrict
        (hitPred res w)).trace * (spec.V (r - w) * S₀))) := add_le_add hfr_cost (add_le_add
        hzero_cost hsum_hit)
    _ = ENNReal.ofReal (Δ.trace * ((spec.tauSum r + slack / 2) * S₀) +
          ((Δ₁.restrict (missPred res b)).trace * ((spec.V r + E_f) * S₀) + ∑ w ∈ Finset.Icc 1 b,
              (Δ₁.restrict (hitPred res w)).trace * (spec.V (r - w) * S₀))) := by
        rw [← ENNReal.ofReal_add hz_nn hs_nn, ← ENNReal.ofReal_add hfr_nn (add_nonneg hz_nn hs_nn)]
    _ ≤ ENNReal.ofReal (Δ.trace * ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀)) :=
        ENNReal.ofReal_le_ofReal halg
    _ = stateMass Δ * ENNReal.ofReal ((spec.V r - slack / 2 + (1 - c) * E_f) * S₀) := by
        rw [ENNReal.ofReal_mul Δ.trace_nonneg, stateMass_eq_ofReal_trace]
private lemma expectedCost_johnsonStageFuel_sparse_le {Var : Type} [DecidableEq Var] {n m k s : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hmN : m ≤
    2 ^ n) (spec : JohnsonWalkSparseSpec m k) (hn0 : spec.n0 ≤ n) (hs : s < k) (hr2 : 2 ≤ k - s)
    (hwk : spec.useWalk (k - s) = true) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (solveNext
    : (w : ℕ) → 1 ≤ w → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (hnext_cost : ∀ w (hw1
    : 1 ≤ w), w ≤ min m (k - s) → ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)), 𝔼[Γ,
      validObs n m
    k S (s + w)] = Γ.trace → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle
    m S)) ((solveNext w hw1).compile qAssign (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ *
    ENNReal.ofReal (spec.V (k - s - w) * √(2 ^ n : ℝ))) (hc_step : max 0 (spec.C_step + 1) ≤
    (sparseSlack spec (k - s) / 2) * √(2 ^ n : ℝ)) (Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k *
      n)))
    (hV : 𝔼[Δ, validObs n m k S s] = Δ.trace) : expectedCost (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN
    (spec.stages n (k - s)) s solveNext (sparseAutoFuel hm_grid hk_grid spec (k - s))).compile
    qAssign (groverParallelMarkingOracle m S)) Δ ≤ stateMass Δ * ENNReal.ofReal (spec.V (k - s) *
    √(2 ^ n : ℝ)) := by
  let r := k - s; let c := ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w
  let slack := sparseSlack spec r; let S₀ := √(2 ^ n : ℝ)
  have hc_pos : 0 < c := spec.hpLo_sum_pos r hr2 (by omega) hwk
  have hc_le1 : c ≤ 1 := (sparse_pLo_sum_le_one hm_grid hk_grid spec hr2 (by omega) hwk).1
  have hslack : 0 < slack := sub_pos.mpr (spec.hdrift_sparse_lt r hr2 (by omega) hwk)
  have hq0 : 0 ≤ 1 - c := (by linarith)
  have hind : ∀ f : ℕ, ∀ Γ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)), 𝔼[Γ, validObs n m k S
    s] =
    Γ.trace → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN (spec.stages n r) s solveNext
    f).compile qAssign (groverParallelMarkingOracle m S)) Γ ≤ stateMass Γ * ENNReal.ofReal
    ((spec.V r + (1 - c) ^ f * (2 * (k : ℝ))) * S₀) := by
    intro f
    induction f with
    | zero =>
      intro Γ hΓ; have hn600 : 600 ≤ n := spec.hn0.trans hn0
      have h0 := expectedCost_eigLockStagesFrom_le res hm_grid hk_grid hn600 hcard r s rfl
        (by omega) Γ hΓ
      have hVr0 : 0 ≤ spec.V r := (spec.hV_bounds r (by omega)).1
      have hr_le_k : (r : ℝ) ≤ (k : ℝ) := (by exact_mod_cast (show r ≤ k by omega))
      have hlin : (2 * (r : ℝ)) * S₀ ≤ (spec.V r + (1 - c) ^ 0 * (2 * (k : ℝ))) * S₀ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity); simp only [pow_zero, one_mul]
        linarith
      exact h0.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hlin) zero_le)
    | succ f ih =>
      intro Γ hΓ
      have hEf0 : 0 ≤ (1 - c) ^ f * (2 * (k : ℝ)) := mul_nonneg (pow_nonneg hq0 f) (by positivity)
      have hstep := expectedCost_johnsonStageFuel_sparse_step res hm_grid hk_grid hn200 hmN spec
        hn0 hs hr2 hwk hcard solveNext hnext_cost hc_step hEf0 ih Γ hΓ
      have hle : (spec.V r - slack / 2 + (1 - c) * ((1 - c) ^ f * (2 * (k : ℝ)))) * S₀ ≤
          (spec.V r + (1 - c) ^ (f + 1) * (2 * (k : ℝ))) * S₀ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hpow : (1 - c) * ((1 - c) ^ f * (2 * (k : ℝ))) = (1 - c) ^ (f + 1) * (2 * (k : ℝ)) :=
          by ring
        linarith
      exact hstep.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle) zero_le)
  obtain ⟨F, hauto, hF_bound⟩ := sparseAutoFuel_spec hm_grid hk_grid spec hr2 (by omega) hwk
  change (1 - c) ^ F * (2 * (k : ℝ)) ≤ slack / 2 at hF_bound
  change expectedCost _ ((johnsonStageFuel res n m k hm_grid hk_grid hn200 hmN (spec.stages n r) s
    solveNext (sparseAutoFuel hm_grid hk_grid spec r)).compile qAssign _) Δ ≤ _
  rw [hauto]
  have hEF0 : 0 ≤ (1 - c) ^ F * (2 * (k : ℝ)) := mul_nonneg (pow_nonneg hq0 F) (by positivity)
  have hfinal := expectedCost_johnsonStageFuel_sparse_step res hm_grid hk_grid hn200 hmN spec hn0
    hs hr2 hwk hcard solveNext hnext_cost hc_step hEF0 (hind F) Δ hV
  have hle_top : (spec.V r - slack / 2 + (1 - c) * ((1 - c) ^ F * (2 * (k : ℝ)))) * S₀ ≤
      spec.V r * S₀ := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hmul_le : (1 - c) * ((1 - c) ^ F * (2 * (k : ℝ))) ≤ 1 * ((1 - c) ^ F * (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right (by linarith) hEF0
    linarith
  exact hfinal.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle_top) zero_le)
private noncomputable def johnsonSolveFromSparse {Var : Type} (res : Var) (n m k : ℕ)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n)
    (spec : JohnsonWalkSparseSpec m k) :
    (s : ℕ) → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | s =>
      if hs : s < k then
        if _hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true then
          johnsonStageFuel res n m k hm_grid hk_grid hn200
            (m_le_two_pow_of_hn200 hm_grid hn200) (spec.stages n (k - s)) s
            (fun w _hw ↦ johnsonSolveFromSparse res n m k hm_grid hk_grid hn200 spec (s + w))
            (sparseAutoFuel hm_grid hk_grid spec (k - s))
        else
          .seq (eigLockStage res n m k hm_grid hk_grid hn200 ⟨s, hs⟩)
            (johnsonSolveFromSparse res n m k hm_grid hk_grid hn200 spec (s + 1))
      else .skip
termination_by s => k - s
decreasing_by all_goals omega
private lemma wp_johnsonSolveFromSparse_ge {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) (spec : JohnsonWalkSparseSpec m k)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ B : ℕ, ∀ s : ℕ, k - s ≤ B → s ≤ k → validObs (Var := Var) n m k S s ≤
        wp ((johnsonSolveFromSparse res n m k hm_grid hk_grid hn200 spec s).compile qAssign
            (groverParallelMarkingOracle m S))
          (validObs n m k S k)
  | 0, s, hB, _ => by
    have hseq : s = k := (by omega); subst hseq
    rw [johnsonSolveFromSparse, dite_eq_right (lt_irrefl s)]; simp [compile]
  | B + 1, s, hB, hs_le => by
    by_cases hs : s < k
    · rw [johnsonSolveFromSparse, dite_eq_left hs]
      by_cases hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true
      · rw [dite_eq_left hwalk]
        exact wp_johnsonStageFuel_ge res hm_grid hk_grid hn200
          (m_le_two_pow_of_hn200 hm_grid hn200) hs_le (spec.stages n (k - s)) hcard _
          (fun w _hw1 hwb ↦ wp_johnsonSolveFromSparse_ge res hm_grid hk_grid hn200 spec hcard
            B (s + w) (by omega) (by omega))
          (sparseAutoFuel hm_grid hk_grid spec (k - s))
      · rw [dite_eq_right hwalk]; dsimp only [compile]; rw [wp_qSeq]
        have hih := wp_johnsonSolveFromSparse_ge res hm_grid hk_grid hn200 spec hcard
          B (s + 1) (by omega) (by omega)
        exact ((eigLockStage_wp_and_active res hm_grid hk_grid hn200 hcard ⟨s, hs⟩).1).trans
          (wp_mono _ hih)
    · have hseq : s = k := by omega
      subst hseq; rw [johnsonSolveFromSparse, dite_eq_right (lt_irrefl s)]; simp [compile]
private noncomputable def sparseStageReqC {m k : ℕ} (spec : JohnsonWalkSparseSpec m k)
    (r : ℕ) : ℝ :=
  if _hwalk : 2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true then
    max 0 (spec.C_step + 1) / (sparseSlack spec r / 2)
  else if _heig : 1 ≤ r ∧ r ≤ k then
    let gap := (spec.V r - spec.V (r - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ))
    5 / gap
  else 0
private lemma expectedCost_johnsonSolveFromSparse_le {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) (spec : JohnsonWalkSparseSpec m k) (hn0 : spec.n0 ≤ n)
    (hreq : ∀ r : ℕ, 1 ≤ r → r ≤ k → sparseStageReqC spec r ≤ √(2 ^ n : ℝ))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ B : ℕ, ∀ s : ℕ, k - s ≤ B → s ≤ k → ∀ Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
        𝔼[Δ, validObs n m k S s] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          ((johnsonSolveFromSparse res n m k hm_grid hk_grid hn200 spec s).compile qAssign
            (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ * ENNReal.ofReal (spec.V (k - s) * √(2 ^ n : ℝ))
  | 0, s, hB, _, Δ, _ => by
    have hseq : s = k := (by omega); subst hseq
    rw [johnsonSolveFromSparse, dite_eq_right (lt_irrefl s)]; simp [compile, spec.hV0]
  | B + 1, s, hB, hs_le, Δ, hV => by
    by_cases hs : s < k
    · rw [johnsonSolveFromSparse, dite_eq_left hs]
      by_cases hwalk : 2 ≤ k - s ∧ spec.useWalk (k - s) = true
      · rw [dite_eq_left hwalk]; have hr_req := hreq (k - s) (by omega) (by omega)
        have hwalk3 : 2 ≤ k - s ∧ k - s ≤ k ∧ spec.useWalk (k - s) = true :=
          ⟨hwalk.1, by omega, hwalk.2⟩
        rw [sparseStageReqC, dite_eq_left hwalk3] at hr_req
        have hslack : 0 < sparseSlack spec (k - s) :=
          sub_pos.mpr (spec.hdrift_sparse_lt (k - s) hwalk.1 (by omega) hwalk.2)
        have hc_step : max 0 (spec.C_step + 1) ≤
            (sparseSlack spec (k - s) / 2) * √(2 ^ n : ℝ) := by
          linarith [(div_le_iff₀ (half_pos hslack)).mp hr_req]
        exact expectedCost_johnsonStageFuel_sparse_le res hm_grid hk_grid hn200
          (m_le_two_pow_of_hn200 hm_grid hn200) spec hn0 hs hwalk.1 hwalk.2 hcard _
          (fun w _hw1 hwb Γ hΓ ↦ by
            have hih := expectedCost_johnsonSolveFromSparse_le res hm_grid hk_grid hn200 spec hn0
              hreq hcard B (s + w) (by omega) (by omega) Γ hΓ
            rwa [show k - (s + w) = k - s - w by omega] at hih)
          hc_step Δ hV
      · rw [dite_eq_right hwalk]; dsimp only [compile]; rw [expectedCost_qSeq]
        let r := k - s
        let stageP := (eigLockStage (Var := Var) res n m k hm_grid hk_grid hn200 ⟨s, hs⟩).compile
          qAssign (groverParallelMarkingOracle m S)
        have hwp_st := (eigLockStage_wp_and_active (Var := Var) res hm_grid hk_grid hn200 hcard
          ⟨s, hs⟩).1
        have hstep_V := jp01_validState_step hV hwp_st
        have hcost_st := expectedCost_eigLockStage_le res hm_grid hk_grid hn200 hcard ⟨s, hs⟩ hV
        have hih := expectedCost_johnsonSolveFromSparse_le res hm_grid hk_grid hn200 spec hn0 hreq
          hcard B (s + 1) (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
        rw [hstep_V.2, show k - (s + 1) = r - 1 by omega] at hih
        have hn600 : 600 ≤ n := spec.hn0.trans hn0
        have hlin := jp01_stageCostReal_le_linear_S0 (k := k) (r := r) hn600 hm_grid hk_grid
          (by omega) (by omega)
        have hor : r = 1 ∨ spec.useWalk r = false := by
          by_cases hr2 : 2 ≤ r
          · right
            cases h : spec.useWalk r
            · rfl
            · exact False.elim (hwalk ⟨hr2, h⟩)
          · left; omega
        have heig_lt := spec.hV_eig r (by omega) (by omega) hor
        have hgap_pos : 0 < (spec.V r - spec.V (r - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) :=
          sub_pos.mpr heig_lt
        have hr_req := hreq r (by omega) (by omega)
        have hnwalk3 : ¬ (2 ≤ r ∧ r ≤ k ∧ spec.useWalk r = true) := fun h ↦ hwalk ⟨h.1, h.2.2⟩
        have heig2 : 1 ≤ r ∧ r ≤ k := ⟨by omega, by omega⟩
        rw [sparseStageReqC, dite_eq_right hnwalk3, dite_eq_left heig2] at hr_req
        have h5_le := (div_le_iff₀ hgap_pos).mp hr_req
        have hst_le : stageCostReal n m r ≤ (spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ) := by
          have hsqrt_div : √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) =
              √(2 ^ n : ℝ) / √((m : ℝ) * (r : ℝ)) := Real.sqrt_div (by positivity) _
          have hrew : (π / 8 + 1 / 4) * (√(2 ^ n : ℝ) / √((m : ℝ) * (r : ℝ))) =
              ((π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ))) * √(2 ^ n : ℝ) := by ring
          have hlin2 := hlin.2; rw [hsqrt_div, hrew] at hlin2; linarith
        have hc1_pos : 0 < (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) := by
          have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid; have hm_pos : 0 < m := (by omega)
          have hr_pos : 0 < r := (by omega); positivity
        have hd_nn : 0 ≤ (spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ) :=
          mul_nonneg (by linarith) (Real.sqrt_nonneg _)
        have hcont_nn : 0 ≤ spec.V (r - 1) * √(2 ^ n : ℝ) :=
          mul_nonneg (spec.hV_bounds (r - 1) (by omega)).1 (Real.sqrt_nonneg _)
        calc expectedCost _ stageP Δ + expectedCost _ _ ((interp stageP).toStateFun Δ)
            ≤ stateMass Δ * ENNReal.ofReal ((spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ)) +
                stateMass Δ * ENNReal.ofReal (spec.V (r - 1) * √(2 ^ n : ℝ)) :=
              add_le_add
                (hcost_st.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hst_le)
                  zero_le))
                hih
          _ = stateMass Δ * (ENNReal.ofReal ((spec.V r - spec.V (r - 1)) * √(2 ^ n : ℝ)) +
                  ENNReal.ofReal (spec.V (r - 1) * √(2 ^ n : ℝ))) := by ring
          _ = stateMass Δ * ENNReal.ofReal (spec.V r * √(2 ^ n : ℝ)) := by
              congr 1
              rw [← ENNReal.ofReal_add hd_nn hcont_nn]
              congr 1
              ring
    · have hseq : s = k := by omega
      subst hseq; rw [johnsonSolveFromSparse, dite_eq_right (lt_irrefl s)]; simp [compile, spec.hV0]
/-- Turnkey parallel query-model circuit executing `JohnsonWalkSparseSpec` with finite-fuel
  renewal
  for `200 ≤ n` and delegating to `Stage1.circuit` for `n < 200`. -/
noncomputable def johnsonCircuitSparse {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSparseSpec m k) (n : ℕ) :
    OracleCirc Var (Stage1.qubits n m k) ((n + 1) * m) :=
  if hn200 : 200 ≤ n then
    .seq (johnsonSolveFromSparse res n m k hm_grid hk_grid hn200 spec 0)
      (.measure res (highBlock (m * (n + 1)) (k * n)))
  else
    Stage1.circuit res n m k
/-- `johnsonCircuitSparse` recovers the full marked set `S` via `decodeTargets n k (σ res) =
  S`
  with probability `1` for every `1 ≤ n`, `k ≤ 2 ^ n`, and `S ∈ groverTargetSets n k`. -/
theorem johnsonCircuitSparse_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSparseSpec m k) (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;; (johnsonCircuitSparse res hm_grid hk_grid spec n).compile qAssign
      (groverParallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ := by
  by_cases hn200 : 200 ≤ n
  · unfold johnsonCircuitSparse; rw [dite_eq_left hn200]; unfold Stage1.qubits
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
      liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)
    refine Triple.of_eq_wp ?_
    symm
    dsimp only [compile]; rw [wp_qSeq, wp_qSeq]; have hmeas_ge : validObs (Var := Var) n m k S k ≤
        wp (measureRegister res (highBlock (m * (n + 1)) (k * n))) post :=
      validObs_le_wp_measure_decodeTargets res hcard
    have hst_ge := wp_johnsonSolveFromSparse_ge (Var := Var) res hm_grid hk_grid hn200 spec hcard
      k 0 le_rfl (Nat.zero_le k)
    have htot_ge := hst_ge.trans (wp_mono _ hmeas_ge)
    have hqset_ge := (wp_qSet_validObs_zero (Var := Var) n m k S).symm.le.trans
      (wp_mono .qSet htot_ge)
    exact top_unique hqset_ge
  · unfold johnsonCircuitSparse; rw [dite_eq_right hn200]
    have hcells : Stage1.cells m k = true := (by simp [Stage1.cells, gridCells, hm_grid, hk_grid])
    exact Stage1.correctness res hn hcells hkN hS
/-- Asymptotic uniform-average expected parallel-round cost bound for `johnsonCircuitSparse`
  relative to `vanillaFindAllCost` from `spec.V k ≤ rel * (π / 4) * groverHarmonicSqrtSum k
  / √m`. -/
theorem johnsonCircuitSparse_rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSparseSpec m k) {rel : ℝ}
    (hV_top : spec.V k ≤ rel * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ)) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (fun S ↦
          qset ;; (johnsonCircuitSparse res hm_grid hk_grid spec n).compile qAssign
            (groverParallelMarkingOracle m S))
        (rel * vanillaFindAllCost n m k) := by
  let M_req := maxUpTo (sparseStageReqC spec) k
  obtain ⟨N_arch, hN_arch⟩ := exists_nat_ge (M_req ^ 2)
  refine ⟨max spec.n0 N_arch, fun n hn hkN ↦ ?_⟩
  have hn0 : spec.n0 ≤ n := (le_max_left _ _).trans hn
  have hN : N_arch ≤ n := (le_max_right _ _).trans hn
  have hn200 : 200 ≤ n := (by have := spec.hn0; omega)
  have hM_le : M_req ≤ √(2 ^ n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc M_req ^ 2 ≤ (N_arch : ℝ) := hN_arch
      _ ≤ (n : ℝ) := by exact_mod_cast hN
      _ ≤ (2 ^ n : ℝ) := by exact_mod_cast n.lt_two_pow_self.le
  have hreq : ∀ r : ℕ, 1 ≤ r → r ≤ k → sparseStageReqC spec r ≤ √(2 ^ n : ℝ) :=
    fun r _ hrk ↦ (le_maxUpTo (sparseStageReqC spec) hrk).trans hM_le
  have hcirc_eq : johnsonCircuitSparse (Var := Var) res hm_grid hk_grid spec n =
        .seq (johnsonSolveFromSparse res n m k hm_grid hk_grid hn200 spec 0)
          (.measure res (highBlock (m * (n + 1)) (k * n))) := by
    unfold johnsonCircuitSparse; exact dite_eq_left hn200
  let q_val : ℝ≥0 := Real.toNNReal (spec.V k * √(2 ^ n : ℝ))
  simp_rw [hcirc_eq]; unfold Stage1.qubits; refine ⟨fun _ ↦ q_val, fun S hS state ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    set oracle := groverParallelMarkingOracle m S
    set model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
    dsimp only [compile]; rw [expectedCost_qSeq, expectedCost_qSet]
    have hreset0 : model.resetCost = 0 := rfl; rw [hreset0]
    simp only [Nat.cast_zero, mul_zero, zero_add]; rw [expectedCost_qSeq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n m k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]; rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
      exact congrArg NNReal.toReal (CQState.trace_qSet state).symm
    have hmass0 : stateMass Δ₀ = stateMass state := Lossless.qSet state
    have hmeas0 : expectedCost model (measureRegister res (highBlock (m * (n + 1)) (k * n)))
        ((interp ((johnsonSolveFromSparse res n m k hm_grid hk_grid hn200 spec 0).compile qAssign
            oracle)).toStateFun Δ₀) = 0 := by
      have hm_cb : CostBound (Var := Var) model
          (measureRegister res (highBlock (m * (n + 1)) (k * n))) 0 := by
        simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
          CostBound.qMeasure (Var := Var) model res _
      exact nonpos_iff_eq_zero.mp (by simpa using hm_cb _)
    rw [hmeas0, add_zero]
    have hst := expectedCost_johnsonSolveFromSparse_le res hm_grid hk_grid hn200 spec hn0 hreq
      hcard k 0 le_rfl (Nat.zero_le k) Δ₀ hV0
    rw [Nat.sub_zero, hmass0] at hst; exact hst
  · have hVk0 : 0 ≤ spec.V k * √(2 ^ n : ℝ) :=
      mul_nonneg (spec.hV_bounds k le_rfl).1 (Real.sqrt_nonneg _)
    have hsum_le : (q_val : ℝ) ≤ rel * vanillaFindAllCost n m k := by
      calc (q_val : ℝ) = spec.V k * √(2 ^ n : ℝ) := Real.coe_toNNReal _ hVk0
        _ ≤ (rel * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ)) * √(2 ^ n : ℝ) :=
            mul_le_mul_of_nonneg_right hV_top (Real.sqrt_nonneg _)
        _ = rel * ((π / 4) * groverHarmonicSqrtSum k * (√(2 ^ n : ℝ) / √(m : ℝ))) := by ring
        _ = rel * vanillaFindAllCost n m k := by
            unfold vanillaFindAllCost; rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n)]
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      have hc : (groverTargetSets n k).card = Nat.choose (2 ^ n) k := (by simp [groverTargetSets])
      rw [hc]; exact_mod_cast Nat.choose_pos hkN
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']; exact hsum_le
end
@[expose] public section
section Sec_P01Alg
open Real
open scoped Matrix
/-! ## Section 1: `m`-Subset Combinatorics & Binomial Absorption -/
/-- The type of `m`-element subsets of `Fin N` (definitionally equal to `SymSubset N m`). -/
abbrev P01Subset (N m : ℕ) : Type := { E : Finset (Fin N) // E.card = m }
theorem card_p01Subset_filter (N m : ℕ) (P : Finset (Fin N) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun E : P01Subset N m ↦ P E.1)).card =
      (((Finset.univ : Finset (Fin N)).powersetCard m).filter P).card := by
  refine Finset.card_bij (fun E _ ↦ E.1) (fun E hE ↦ ?_) (fun E₁ _ E₂ _ h ↦ Subtype.ext h)
    (fun S hS ↦ ?_)
  · rcases Finset.mem_filter.mp hE with ⟨_, hPE⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, E.2⟩, hPE⟩
  · rcases Finset.mem_filter.mp hS with ⟨hSm, hPS⟩
    exact ⟨⟨S, (Finset.mem_powersetCard.mp hSm).2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPS⟩,
      rfl⟩
theorem card_p01Subset (N m : ℕ) : Fintype.card (P01Subset N m) = N.choose m := by
  rw [← Finset.card_univ]; have h := card_p01Subset_filter N m (fun _ ↦ True)
  simp only [Finset.filter_true_of_mem (fun _ _ ↦ trivial)] at h
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
theorem card_powersetCard_inter_eq {α : Type*} [DecidableEq α] [Fintype α] (U : Finset α) (m w :
    ℕ) (hw : w ≤ m) : (((Finset.univ : Finset α).powersetCard m).filter (fun E ↦ (E ∩ U).card =
    w)).card = U.card.choose w * (Fintype.card α - U.card).choose (m - w) := by
  have hbij : (((Finset.univ : Finset α).powersetCard m).filter (fun E ↦ (E ∩ U).card = w)).card =
        (U.powersetCard w ×ˢ Uᶜ.powersetCard (m - w)).card := by
    symm
    refine Finset.card_bij (fun p _ ↦ p.1 ∪ p.2) (fun p hp ↦ ?_) (fun p₁ hp₁ p₂ hp₂ heq ↦ ?_)
      (fun S hS ↦ ?_)
    · rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      rcases Finset.mem_powersetCard.mp hp1 with ⟨hsub1, hcard1⟩
      rcases Finset.mem_powersetCard.mp hp2 with ⟨hsub2, hcard2⟩
      have hdisj : Disjoint p.1 p.2 := Disjoint.mono hsub1 hsub2 disjoint_compl_right
      have hu_card : (p.1 ∪ p.2).card = m := by
        rw [Finset.card_union_of_disjoint hdisj, hcard1, hcard2]; omega
      have hinter : (p.1 ∪ p.2) ∩ U = p.1 := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union]
        exact ⟨fun ⟨h, hxU⟩ ↦ h.elim id fun hx2 ↦ absurd hxU (Finset.mem_compl.mp (hsub2 hx2)),
          fun hx1 ↦ ⟨Or.inl hx1, hsub1 hx1⟩⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hu_card⟩, by rw [hinter, hcard1]⟩
    · rcases Finset.mem_product.mp hp₁ with ⟨hp11, hp12⟩
      rcases Finset.mem_product.mp hp₂ with ⟨hp21, hp22⟩
      have hsub11 := (Finset.mem_powersetCard.mp hp11).1
      have hsub12 := (Finset.mem_powersetCard.mp hp12).1
      have hsub21 := (Finset.mem_powersetCard.mp hp21).1
      have hsub22 := (Finset.mem_powersetCard.mp hp22).1
      have hinterU (A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ Uᶜ) : (A ∪ B) ∩ U = A := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union]
        exact ⟨fun ⟨h, hxU⟩ ↦ h.elim id fun hxB ↦ absurd hxU (Finset.mem_compl.mp (hB hxB)),
          fun hxA ↦ ⟨Or.inl hxA, hA hxA⟩⟩
      have hinterUc (A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ Uᶜ) : (A ∪ B) ∩ Uᶜ = B := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
        exact ⟨fun ⟨h, hxUc⟩ ↦ h.elim (fun hxA ↦ absurd (hA hxA) hxUc) id,
          fun hxB ↦ ⟨Or.inr hxB, Finset.mem_compl.mp (hB hxB)⟩⟩
      exact Prod.ext
        (by rw [← hinterU p₁.1 p₁.2 hsub11 hsub12, heq, hinterU p₂.1 p₂.2 hsub21 hsub22])
        (by rw [← hinterUc p₁.1 p₁.2 hsub11 hsub12, heq, hinterUc p₂.1 p₂.2 hsub21 hsub22])
    · rcases Finset.mem_filter.mp hS with ⟨hSm_mem, hSU_card⟩
      have hSm : S.card = m := (Finset.mem_powersetCard.mp hSm_mem).2
      have hunion : (S ∩ U) ∪ (S ∩ Uᶜ) = S := (by ext x; by_cases hx : x ∈ U <;> simp [hx])
      have hdisj : Disjoint (S ∩ U) (S ∩ Uᶜ) :=
        Disjoint.mono inf_le_right inf_le_right disjoint_compl_right
      have hSUc_card : (S ∩ Uᶜ).card = m - w := by
        have hc := Finset.card_union_of_disjoint hdisj; rw [hunion, hSm, hSU_card] at hc; omega
      exact ⟨(S ∩ U, S ∩ Uᶜ), Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨inf_le_right,
        hSU_card⟩, Finset.mem_powersetCard.mpr ⟨inf_le_right, hSUc_card⟩⟩, hunion⟩
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_compl]
theorem card_powersetCard_mem {α : Type*} [DecidableEq α] (S : Finset α) {k : ℕ} {x : α}
    (hx : x ∈ S) (hk : 1 ≤ k) :
    ((S.powersetCard k).filter (x ∈ ·)).card = (S.card - 1).choose (k - 1) := by
  have hbij : ((S.powersetCard k).filter (x ∈ ·)).card =
      ((S.erase x).powersetCard (k - 1)).card := by
    refine Finset.card_bij (fun E _ ↦ E.erase x) (fun E hE ↦ ?_) (fun E₁ hE₁ E₂ hE₂ heq ↦ ?_)
      (fun F hF ↦ ?_)
    · rcases Finset.mem_filter.mp hE with ⟨hEk, hxE⟩
      rcases Finset.mem_powersetCard.mp hEk with ⟨hES, hcard⟩; exact Finset.mem_powersetCard.mpr
        ⟨Finset.erase_subset_erase x hES, by rw [Finset.card_erase_of_mem hxE, hcard]⟩
    · have hx1 := (Finset.mem_filter.mp hE₁).2; have hx2 := (Finset.mem_filter.mp hE₂).2
      rw [← Finset.insert_erase hx1, heq, Finset.insert_erase hx2]
    · rcases Finset.mem_powersetCard.mp hF with ⟨hFS, hFcard⟩
      have hxF : x ∉ F := fun h ↦ (Finset.mem_erase.mp (hFS h)).1 rfl
      have hsub : insert x F ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hx, hFS.trans (Finset.erase_subset x S)⟩
      have hcard : (insert x F).card = k := by rw [Finset.card_insert_of_notMem hxF, hFcard]; omega
      exact ⟨insert x F, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩,
        Finset.mem_insert_self x F⟩, Finset.erase_insert hxF⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hx]
lemma p01_choose_mul_succ : ∀ n k : ℕ, (n + 1) * n.choose k = (k + 1) * (n + 1).choose (k + 1)
  | 0, 0 => by simp
  | 0, k + 1 => by
      rw [Nat.choose_zero_succ, mul_zero, Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  | _ + 1, 0 => by simp [Nat.choose_one_right]
  | n + 1, k + 1 => by
      have h1 := p01_choose_mul_succ n k; have h2 := p01_choose_mul_succ n (k + 1)
      have hp1 : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) := Nat.choose_succ_succ n k
      have hp2 : (n + 2).choose (k + 2) = (n + 1).choose (k + 1) + (n + 1).choose (k + 2) :=
        Nat.choose_succ_succ (n + 1) (k + 1)
      calc (n + 2) * (n + 1).choose (k + 1)
          = (n + 1) * n.choose k + (n + 1) * n.choose (k + 1) + (n + 1).choose (k + 1) := by
              rw [hp1]; ring
        _ = (k + 1) * (n + 1).choose (k + 1) + (k + 2) * (n + 1).choose (k + 2) +
              (n + 1).choose (k + 1) := by rw [h1, h2]
        _ = (k + 2) * (n + 2).choose (k + 2) := by rw [hp2]; ring
/-! ## Section 2: `pV0Mat`, `phi1Mat`, `pV1Mat`, and Involution Identities -/
/-- Orthogonal projector onto the `1`-dimensional uniform subspace `V_0`. -/
noncomputable def pV0Mat (N m : ℕ) : Matrix (P01Subset N m) (P01Subset N m) ℝ :=
  Matrix.of fun _ _ ↦ 1 / (N.choose m : ℝ)
/-- Centered subset-element incidence operator `Φ_1: ℝ^N → ℝ^{P01Subset N m}`. -/
noncomputable def phi1Mat (N m : ℕ) : Matrix (P01Subset N m) (Fin N) ℝ := Matrix.of fun E x ↦
    ((if x ∈ E.1 then (1 : ℝ) else 0) - (m : ℝ) / (N : ℝ)) / √((N - 2).choose (m - 1) : ℝ)
/-- Orthogonal projector onto the `(N - 1)`-dimensional degree-`1` Johnson eigenspace `V_1`. -/
noncomputable def pV1Mat (N m : ℕ) : Matrix (P01Subset N m) (P01Subset N m) ℝ :=
  phi1Mat N m * (phi1Mat N m)ᵀ
/-- Real symmetric reflection `I - 2 P_{V_1}` across `V_1^⊥`. -/
noncomputable def r1SymMat (N m : ℕ) : Matrix (P01Subset N m) (P01Subset N m) ℝ :=
  1 - (2 : ℝ) • pV1Mat N m
/-- Real symmetric reflection `I - 2 P_{V_0} - 2 P_{V_1}` across `(V_0 ⊕ V_1)^⊥`. -/
noncomputable def r01SymMat (N m : ℕ) : Matrix (P01Subset N m) (P01Subset N m) ℝ :=
  1 - (2 : ℝ) • pV0Mat N m - (2 : ℝ) • pV1Mat N m
theorem pV0Mat_transpose (N m : ℕ) : (pV0Mat N m)ᵀ = pV0Mat N m := by ext E F; rfl
theorem pV0Mat_mul_self {N m : ℕ} (hmN : m ≤ N) : pV0Mat N m * pV0Mat N m = pV0Mat N m := by
  have hc_pos : (0 : ℝ) < (N.choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hmN); ext E F
  simp only [Matrix.mul_apply, pV0Mat, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    card_p01Subset, nsmul_eq_mul]
  field_simp
theorem phi1Mat_row_sum {N m : ℕ} (hN : 0 < N) (E : P01Subset N m) :
    ∑ x : Fin N, phi1Mat N m E x = 0 := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [phi1Mat, Matrix.of_apply, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hind : (∑ x : Fin N, if x ∈ E.1 then (1 : ℝ) else 0) = (m : ℝ) := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, E.2]
  rw [hind, div_eq_zero_iff]; left; field_simp; ring
private lemma card_p01Subset_mem {N m : ℕ} (hm1 : 1 ≤ m) (_hN1 : 1 ≤ N) (x : Fin N) :
    (Finset.univ.filter (fun E : P01Subset N m ↦ x ∈ E.1)).card = (N - 1).choose (m - 1) := by
  rw [card_p01Subset_filter N m (fun S ↦ x ∈ S),
    card_powersetCard_mem Finset.univ (Finset.mem_univ x) hm1, Finset.card_univ, Fintype.card_fin]
private lemma card_p01Subset_mem_pair {N m : ℕ} (hm2 : 2 ≤ m) {x y : Fin N} (hxy : x ≠ y) :
    (Finset.univ.filter (fun E : P01Subset N m ↦ x ∈ E.1 ∧ y ∈ E.1)).card =
      (N - 2).choose (m - 2) := by
  rw [card_p01Subset_filter N m (fun S ↦ x ∈ S ∧ y ∈ S)]
  have hflt : (((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun E ↦ x ∈ E ∧ y ∈ E)) =
      ((((Finset.univ : Finset (Fin N)).powersetCard m).filter (x ∈ ·)).filter (y ∈ ·)) := by
    ext E; simp [and_assoc]
  rw [hflt]; have hbij :
      ((((Finset.univ : Finset (Fin N)).powersetCard m).filter (x ∈ ·)).filter (y ∈ ·)).card =
        ((((Finset.univ : Finset (Fin N)).erase x).powersetCard (m - 1)).filter (y ∈ ·)).card := by
    refine Finset.card_bij (fun E _ ↦ E.erase x) (fun E hE ↦ ?_) (fun E₁ hE₁ E₂ hE₂ heq ↦ ?_)
      (fun F hF ↦ ?_)
    · rcases Finset.mem_filter.mp hE with ⟨hEx, hyE⟩
      rcases Finset.mem_filter.mp hEx with ⟨hEm, hxE⟩
      rcases Finset.mem_powersetCard.mp hEm with ⟨hES, hcard⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.erase_subset_erase x hES,
        by rw [Finset.card_erase_of_mem hxE, hcard]⟩, Finset.mem_erase.mpr ⟨hxy.symm, hyE⟩⟩
    · have hx1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₁).1).2
      have hx2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hE₂).1).2
      rw [← Finset.insert_erase hx1, heq, Finset.insert_erase hx2]
    · rcases Finset.mem_filter.mp hF with ⟨hFm, hyF⟩
      rcases Finset.mem_powersetCard.mp hFm with ⟨hFS, hFcard⟩
      have hxF : x ∉ F := fun h ↦ (Finset.mem_erase.mp (hFS h)).1 rfl
      have hcard : (insert x F).card = m := by rw [Finset.card_insert_of_notMem hxF, hFcard]; omega
      exact ⟨insert x F, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, Finset.mem_insert_self x F⟩,
        Finset.mem_insert_of_mem hyF⟩, Finset.erase_insert hxF⟩
  have hy_er : y ∈ (Finset.univ : Finset (Fin N)).erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
  rw [hbij, card_powersetCard_mem _ hy_er (by omega), Finset.card_erase_of_mem (Finset.mem_univ
    x), Finset.card_univ, Fintype.card_fin, Nat.sub_sub, Nat.sub_sub]
theorem phi1Mat_transpose_mul_self {N m : ℕ} (hm1 : 1 ≤ m) (h2m : 2 * m < N) :
    (phi1Mat N m)ᵀ * phi1Mat N m = 1 - (1 / (N : ℝ)) • Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  have hN3 : 3 ≤ N := (by omega); have hNR : (N : ℝ) ≠ 0 := (by positivity)
  have hD_pos : (0 : ℝ) < ((N - 2).choose (m - 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have habs0 : (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) = (m : ℝ) * (N.choose m : ℝ) := by
    have h := p01_choose_mul_succ (N - 1) (m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ N), Nat.sub_add_cancel hm1] at h; exact_mod_cast h
  have habs1 : ((N - m : ℕ) : ℝ) * ((N - 1).choose (m - 1) : ℝ) =
      ((N - 1 : ℕ) : ℝ) * ((N - 2).choose (m - 1) : ℝ) := by
    have hc_eq : (N - 1).choose (m - 1) = (N - 1).choose (N - m) := by
      rw [← Nat.choose_symm (by omega : m - 1 ≤ N - 1)]; congr 1; omega
    have hd_eq : (N - 2).choose (m - 1) = (N - 2).choose (N - m - 1) := by
      rw [← Nat.choose_symm (by omega : m - 1 ≤ N - 2)]; congr 1; omega
    have h := p01_choose_mul_succ (N - 2) (N - m - 1); have hN21 : N - 2 + 1 = N - 1 := (by omega)
    have hNm1 : N - m - 1 + 1 = N - m := (by omega); rw [hN21, hNm1, ← hc_eq, ← hd_eq] at h
    exact_mod_cast h.symm
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, phi1Mat, Matrix.of_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  have hsq : ∀ E : P01Subset N m, (((if x ∈ E.1 then (1 : ℝ) else 0) - (m : ℝ) / (N : ℝ)) / √((N -
    2).choose (m - 1) : ℝ)) * (((if y ∈ E.1 then (1 : ℝ) else 0) - (m : ℝ) / (N : ℝ)) / √((N -
    2).choose (m - 1) : ℝ)) = ((if x ∈ E.1 ∧ y ∈ E.1 then (1 : ℝ) else 0) - ((m : ℝ) / (N : ℝ)) *
    (if x ∈ E.1 then (1 : ℝ) else 0) - ((m : ℝ) / (N : ℝ)) * (if y ∈ E.1 then (1 : ℝ) else 0) +
    ((m : ℝ) / (N : ℝ)) ^ 2) / ((N - 2).choose (m - 1) : ℝ) := by
    intro E; rw [div_mul_div_comm, Real.mul_self_sqrt hD_pos.le]; congr 1
    by_cases hx : x ∈ E.1 <;> by_cases hy : y ∈ E.1 <;>
      simp only [hx, hy, and_self, and_false, false_and, ↓reduceIte] <;> ring
  simp_rw [hsq, ← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum_x : (∑ E : P01Subset N m, if x ∈ E.1 then (1 : ℝ) else 0) =
      ((N - 1).choose (m - 1) : ℝ) := by
    rw [Finset.sum_boole, card_p01Subset_mem hm1 (by omega) x]
  have hsum_y : (∑ E : P01Subset N m, if y ∈ E.1 then (1 : ℝ) else 0) =
      ((N - 1).choose (m - 1) : ℝ) := by
    rw [Finset.sum_boole, card_p01Subset_mem hm1 (by omega) y]
  have hsum_c : (∑ _ : P01Subset N m, ((m : ℝ) / (N : ℝ)) ^ 2) =
      (N.choose m : ℝ) * ((m : ℝ) / (N : ℝ)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, card_p01Subset, nsmul_eq_mul]
  rw [hsum_x, hsum_y, hsum_c]; have habs1' : ((N : ℝ) - (m : ℝ)) * ((N - 1).choose (m - 1) : ℝ) =
      ((N : ℝ) - 1) * ((N - 2).choose (m - 1) : ℝ) := by
    have hsubm : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := Nat.cast_sub (by omega : m ≤ N)
    have hsub1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    rw [← hsubm, ← hsub1, habs1]
  by_cases hxy : x = y
  · subst hxy; have hdiag : (∑ E : P01Subset N m, if x ∈ E.1 ∧ x ∈ E.1 then (1 : ℝ) else 0) =
        ((N - 1).choose (m - 1) : ℝ) := by
      simp_rw [and_self]; exact hsum_x
    rw [hdiag]; simp only [↓reduceIte]; rw [div_eq_iff hD_pos.ne']
    calc ((N - 1).choose (m - 1) : ℝ) - (m : ℝ) / (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) - (m : ℝ)
          / (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) + (N.choose m : ℝ) * ((m : ℝ) / (N : ℝ)) ^ 2 =
          (((N : ℝ) - (m : ℝ)) * ((N - 1).choose (m - 1) : ℝ) + ((m : ℝ) / (N : ℝ)) * ((m : ℝ) *
          (N.choose m : ℝ) - (N : ℝ) * ((N - 1).choose (m - 1) : ℝ))) / (N : ℝ) := by
          field_simp; ring
      _ = ((N : ℝ) - 1) * ((N - 2).choose (m - 1) : ℝ) / (N : ℝ) := by
          rw [habs0, sub_self, mul_zero, add_zero, habs1']
      _ = (1 - 1 / (N : ℝ) * 1) * ((N - 2).choose (m - 1) : ℝ) := by field_simp
  · simp only [hxy, ↓reduceIte]; rcases hm1.eq_or_lt with rfl | hm2
    · have hemp : (∑ E : P01Subset N 1, if x ∈ E.1 ∧ y ∈ E.1 then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun E _ ↦ ?_
        have hnot : ¬ (x ∈ E.1 ∧ y ∈ E.1) := by
          rintro ⟨hxE, hyE⟩
          have hle : 2 ≤ E.1.card := by
            have hsub : ({x, y} : Finset (Fin N)) ⊆ E.1 :=
              Finset.insert_subset_iff.mpr ⟨hxE, Finset.singleton_subset_iff.mpr hyE⟩
            have hc2 : ({x, y} : Finset (Fin N)).card = 2 := Finset.card_pair hxy
            rw [← hc2]; exact Finset.card_le_card hsub
          linarith [E.2]
        simp [hnot]
      rw [hemp]; simp only [Nat.sub_self, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one]
      field_simp; ring
    · have hoff : (∑ E : P01Subset N m, if x ∈ E.1 ∧ y ∈ E.1 then (1 : ℝ) else 0) =
          ((N - 2).choose (m - 2) : ℝ) := by
        rw [Finset.sum_boole, card_p01Subset_mem_pair hm2 hxy]
      have hpasc : ((N - 2).choose (m - 2) : ℝ) =
          ((N - 1).choose (m - 1) : ℝ) - ((N - 2).choose (m - 1) : ℝ) := by
        have hp := Nat.choose_succ_succ (N - 2) (m - 2)
        have hs1 : (N - 2).succ = N - 1 := (by omega); have hs2 : (m - 2).succ = m - 1 := (by omega)
        rw [hs1, hs2] at hp; have hpR : ((N - 1).choose (m - 1) : ℝ) =
            ((N - 2).choose (m - 2) : ℝ) + ((N - 2).choose (m - 1) : ℝ) := by
          exact_mod_cast hp
        linarith
      rw [hoff, div_eq_iff hD_pos.ne']
      calc ((N - 2).choose (m - 2) : ℝ) - (m : ℝ) / (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) - (m :
            ℝ) / (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) + (N.choose m : ℝ) * ((m : ℝ) / (N : ℝ)) ^
            2 = ((N : ℝ) * ((N - 2).choose (m - 2) : ℝ) - (m : ℝ) * ((N - 1).choose (m - 1) : ℝ) +
            ((m : ℝ) / (N : ℝ)) * ((m : ℝ) * (N.choose m : ℝ) - (N : ℝ) * ((N - 1).choose (m - 1)
            : ℝ))) / (N : ℝ) := by
            field_simp; ring
        _ = ((N : ℝ) * (((N - 1).choose (m - 1) : ℝ) - ((N - 2).choose (m - 1) : ℝ)) -
              (m : ℝ) * ((N - 1).choose (m - 1) : ℝ)) / (N : ℝ) := by
            rw [habs0, sub_self, mul_zero, add_zero, hpasc]
        _ = ((((N : ℝ) - (m : ℝ)) * ((N - 1).choose (m - 1) : ℝ) -
              (N : ℝ) * ((N - 2).choose (m - 1) : ℝ))) / (N : ℝ) := by ring
        _ = (0 - 1 / (N : ℝ) * 1) * ((N - 2).choose (m - 1) : ℝ) := by rw [habs1']; field_simp; ring
theorem pV1Mat_transpose (N m : ℕ) : (pV1Mat N m)ᵀ = pV1Mat N m := by
  simp [pV1Mat, Matrix.transpose_mul]
theorem pV0Mat_mul_pV1Mat {N m : ℕ} (hN : 0 < N) : pV0Mat N m * pV1Mat N m = 0 := by
  have hzero : pV0Mat N m * phi1Mat N m = 0 := by
    ext E x; simp only [Matrix.mul_apply, pV0Mat, Matrix.of_apply, Matrix.zero_apply]
    have hsum : (∑ F : P01Subset N m, phi1Mat N m F x) = ∑ F : P01Subset N m, ((if x ∈ F.1 then (1
      : ℝ) else 0) - (m : ℝ) / (N : ℝ)) / √((N - 2).choose (m - 1) : ℝ) := rfl
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · simp only [phi1Mat, Matrix.of_apply, Nat.cast_zero, zero_div, sub_zero]
      refine Finset.sum_eq_zero fun F _ ↦ ?_
      have hx : x ∉ F.1 := (by rw [Finset.card_eq_zero.mp F.2]; simp); simp [hx]
    · by_cases hmN : m ≤ N
      · have habs : (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) = (m : ℝ) * (N.choose m : ℝ) := by
          have h := p01_choose_mul_succ (N - 1) (m - 1)
          rw [Nat.sub_add_cancel hN, Nat.sub_add_cancel hm1] at h; exact_mod_cast h
        have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
        rw [← Finset.mul_sum, hsum, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_boole,
          card_p01Subset_mem hm1 hN x, Finset.sum_const, Finset.card_univ, card_p01Subset,
          nsmul_eq_mul]
        have hnum : ((N - 1).choose (m - 1) : ℝ) - (N.choose m : ℝ) * ((m : ℝ) / (N : ℝ)) = 0 := by
          field_simp; linarith
        rw [hnum, zero_div, mul_zero]
      · have hemp : IsEmpty (P01Subset N m) :=
          ⟨fun F ↦ hmN (F.2 ▸ F.1.card_le_univ.trans (by simp))⟩
        simp
  rw [pV1Mat, ← Matrix.mul_assoc, hzero, Matrix.zero_mul]
theorem pV1Mat_mul_pV0Mat {N m : ℕ} (hN : 0 < N) : pV1Mat N m * pV0Mat N m = 0 := by
  rw [← pV1Mat_transpose, ← pV0Mat_transpose, ← Matrix.transpose_mul, pV0Mat_mul_pV1Mat hN,
    Matrix.transpose_zero]
theorem pV1Mat_mul_self {N m : ℕ} (hm1 : 1 ≤ m) (h2m : 2 * m < N) :
    pV1Mat N m * pV1Mat N m = pV1Mat N m := by
  have hN : 0 < N := (by omega)
  have hJ : phi1Mat N m * Matrix.of (fun _ _ : Fin N ↦ (1 : ℝ)) = 0 := by
    ext E y; simp only [Matrix.mul_apply, Matrix.of_apply, mul_one, Matrix.zero_apply]
    exact phi1Mat_row_sum hN E
  have hgram : (phi1Mat N m)ᵀ * phi1Mat N m = (1 : Matrix (Fin N) (Fin N) ℝ) - (1 / (N : ℝ)) •
    Matrix.of (fun _ _ : Fin N ↦ (1 : ℝ)) := phi1Mat_transpose_mul_self hm1 h2m
  have hmid : phi1Mat N m * ((phi1Mat N m)ᵀ * phi1Mat N m) = phi1Mat N m := by
    rw [hgram, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hJ, smul_zero, sub_zero]
  calc pV1Mat N m * pV1Mat N m
      = (phi1Mat N m * ((phi1Mat N m)ᵀ * phi1Mat N m)) * (phi1Mat N m)ᵀ := by
          simp only [pV1Mat, Matrix.mul_assoc]
    _ = pV1Mat N m := by rw [hmid, pV1Mat]
theorem r1SymMat_transpose (N m : ℕ) : (r1SymMat N m)ᵀ = r1SymMat N m := by
  simp [r1SymMat, pV1Mat_transpose]
theorem r1SymMat_mul_self {N m : ℕ} (hm1 : 1 ≤ m) (h2m : 2 * m < N) :
    r1SymMat N m * r1SymMat N m = 1 := by
  simp only [r1SymMat, sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, pV1Mat_mul_self hm1 h2m]
  ext E F; simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]; ring
theorem r01SymMat_transpose (N m : ℕ) : (r01SymMat N m)ᵀ = r01SymMat N m := by
  simp [r01SymMat, pV0Mat_transpose, pV1Mat_transpose]
theorem r01SymMat_mul_self {N m : ℕ} (hm1 : 1 ≤ m) (h2m : 2 * m < N) :
    r01SymMat N m * r01SymMat N m = 1 := by
  have hN : 0 < N := (by omega); have hmN : m ≤ N := (by omega)
  simp only [r01SymMat, sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, pV0Mat_mul_self hmN, pV1Mat_mul_self hm1 h2m,
    pV0Mat_mul_pV1Mat hN, pV1Mat_mul_pV0Mat hN, smul_zero, sub_zero]
  ext E F; simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]; ring
/-! ## Section 3: `10 ^ 15`-Scaled Square-Root Interval Enclosure (`wdSqrt`) -/
/-- `10 ^ 15`-scaled square-root enclosure on non-negative `WDIVal` intervals via
  `Nat.sqrt`. -/
def wdSqrt (iv : WDIVal) : WDIVal :=
  ((Nat.sqrt (iv.1.toNat * wdScale) : ℤ), (Nat.sqrt (iv.2.toNat * wdScale) + 1 : ℤ))
theorem wdMem_sqrt {x : ℝ} {iv : WDIVal} (hx0 : 0 ≤ x) (h : wdMem x iv) :
    wdMem (√x) (wdSqrt iv) := by
  have hB : 0 < wdScaleR := (by unfold wdScaleR wdScale; norm_num); unfold wdMem wdSqrt at *
  dsimp only; constructor
  · by_cases hlo : iv.1 ≤ 0
    · have h0 : iv.1.toNat = 0 := Int.toNat_of_nonpos hlo
      rw [h0, Nat.zero_mul, Nat.sqrt_zero, Int.ofNat_zero, Int.cast_zero, zero_div]
      exact Real.sqrt_nonneg x
    · have hlo' : 0 < iv.1 := not_le.mp hlo; set s : ℕ := Nat.sqrt (iv.1.toNat * wdScale)
      have hs_sq : s * s ≤ iv.1.toNat * wdScale := Nat.sqrt_le _
      have hs1 : (s : ℝ) * (s : ℝ) ≤ (iv.1 : ℝ) * wdScaleR := by
        have hiv : (iv.1.toNat : ℝ) = (iv.1 : ℝ) := (by exact_mod_cast Int.toNat_of_nonneg hlo'.le)
        rw [← hiv]; unfold wdScaleR; exact_mod_cast hs_sq
      have hs2 : ((s : ℝ) / wdScaleR) ^ 2 ≤ (iv.1 : ℝ) / wdScaleR := by
        rw [div_pow, sq (s : ℝ), sq wdScaleR, ← div_div]
        exact div_le_div_of_nonneg_right ((div_le_iff₀ hB).mpr hs1) hB.le
      have hsq := Real.sqrt_le_sqrt (hs2.trans h.1)
      rw [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg s) hB.le)] at hsq
      simpa only [Int.cast_natCast] using hsq
  · have hhi_nn : 0 ≤ iv.2 := by
      have hdiv : 0 ≤ (iv.2 : ℝ) / wdScaleR := hx0.trans h.2; have hm := mul_nonneg hdiv hB.le
      rw [div_mul_cancel₀ _ hB.ne'] at hm; exact_mod_cast hm
    set t : ℕ := Nat.sqrt (iv.2.toNat * wdScale) + 1
    have ht_sq : iv.2.toNat * wdScale < t * t := Nat.lt_succ_sqrt _
    have ht1 : (iv.2 : ℝ) * wdScaleR ≤ (t : ℝ) * (t : ℝ) := by
      have hiv : (iv.2.toNat : ℝ) = (iv.2 : ℝ) := (by exact_mod_cast Int.toNat_of_nonneg hhi_nn)
      rw [← hiv]; unfold wdScaleR; exact_mod_cast ht_sq.le
    have ht2 : (iv.2 : ℝ) / wdScaleR ≤ ((t : ℝ) / wdScaleR) ^ 2 := by
      rw [div_pow, sq (t : ℝ), sq wdScaleR, ← div_div]
      exact div_le_div_of_nonneg_right ((le_div_iff₀ hB).mpr ht1) hB.le
    have hsq := Real.sqrt_le_sqrt (h.2.trans ht2)
    rw [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg t) hB.le)] at hsq
    have hcast : (((Nat.sqrt (iv.2.toNat * wdScale) : ℤ) + 1 : ℤ) : ℝ) = (t : ℝ) := by
      dsimp only [t]; push_cast; rfl
    rwa [hcast]
/-- `10 ^ 15`-scaled exact integer square-root interval matching `isqrt_lo_15` /
  `isqrt_hi_15`. -/
def p01Isqrt15 (val : ℕ) : WDIVal :=
  let target := val * (wdScale * wdScale)
  let rt := Nat.sqrt target
  ((rt : ℤ), if rt * rt = target then (rt : ℤ) else (rt : ℤ) + 1)
theorem wdMem_p01Isqrt15 (val : ℕ) : wdMem (√(val : ℝ)) (p01Isqrt15 val) := by
  have hB : 0 < wdScaleR := (by unfold wdScaleR wdScale; norm_num); unfold wdMem p01Isqrt15
  dsimp only; set target : ℕ := val * (wdScale * wdScale); set rt : ℕ := Nat.sqrt target
  constructor
  · have hle : rt * rt ≤ target := Nat.sqrt_le target
    have hleR : ((rt : ℝ) / wdScaleR) ^ 2 ≤ (val : ℝ) := by
      rw [div_pow, sq (rt : ℝ), sq wdScaleR, div_le_iff₀ (mul_pos hB hB)]
      dsimp only [target] at hle; unfold wdScaleR; exact_mod_cast hle
    have hsq := Real.sqrt_le_sqrt hleR
    rw [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg rt) hB.le)] at hsq
    simpa only [Int.cast_natCast] using hsq
  · split_ifs with heq
    · have heqR : (val : ℝ) = ((rt : ℝ) / wdScaleR) ^ 2 := by
        rw [div_pow, sq (rt : ℝ), sq wdScaleR, eq_div_iff (mul_pos hB hB).ne']
        dsimp only [target] at heq; unfold wdScaleR; exact_mod_cast heq.symm
      rw [heqR, Real.sqrt_sq (div_nonneg (Nat.cast_nonneg rt) hB.le)]
      simp only [Int.cast_natCast, le_rfl]
    · have hlt : target < (rt + 1) * (rt + 1) := Nat.lt_succ_sqrt target
      have hleR : (val : ℝ) ≤ (((rt + 1 : ℕ) : ℝ) / wdScaleR) ^ 2 := by
        rw [div_pow, sq ((rt + 1 : ℕ) : ℝ), sq wdScaleR, le_div_iff₀ (mul_pos hB hB)]
        dsimp only [target] at hlt; unfold wdScaleR; exact_mod_cast hlt.le
      have hsq := Real.sqrt_le_sqrt hleR
      rw [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg (rt + 1)) hB.le)] at hsq
      have hcast : (((rt : ℤ) + 1 : ℤ) : ℝ) = ((rt + 1 : ℕ) : ℝ) := (by push_cast; rfl); rwa [hcast]
end Sec_P01Alg
section Sec_P01Orb
open Real
open scoped Matrix
/-! ## Section 1: Orbit Cardinalities & Exact Ratio Identities -/
/-- Number of `m`-subsets of `Fin N` having intersection size `w` with a fixed `r`-subset. -/
noncomputable def orbCard (N m r w : ℕ) : ℕ := r.choose w * (N - r).choose (m - w)
theorem orbCard_pos {N m r w : ℕ} (hm2 : 2 ≤ m) (hr2 : 2 ≤ r) (hmrN : m + r < N) (hw2 : w ≤ 2) :
    0 < orbCard N m r w := by
  unfold orbCard; exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
theorem orbCard_rel1 {N m r : ℕ} (hm1 : 1 ≤ m) (hmrN : m + r ≤ N) :
    orbCard N m r 0 * (r * m) = orbCard N m r 1 * (N - r - m + 1) := by
  unfold orbCard; simp only [Nat.choose_zero_right, Nat.choose_one_right, one_mul, Nat.sub_zero]
  have h := Nat.choose_succ_right_eq (N - r) (m - 1); have hm1' : m - 1 + 1 = m := (by omega)
  have hsub : N - r - (m - 1) = N - r - m + 1 := (by omega); rw [hm1', hsub] at h
  calc (N - r).choose m * (r * m)
      = r * ((N - r).choose m * m) := by ring
    _ = r * ((N - r).choose (m - 1) * (N - r - m + 1)) := by rw [h]
    _ = r * (N - r).choose (m - 1) * (N - r - m + 1) := by ring
theorem orbCard_rel2 {N m r : ℕ} (hm2 : 2 ≤ m) (hr2 : 2 ≤ r) (hmrN : m + r ≤ N) :
    orbCard N m r 1 * ((r - 1) * (m - 1)) = 2 * orbCard N m r 2 * (N - r - m + 2) := by
  unfold orbCard; simp only [Nat.choose_one_right]
  have hr_ch : 2 * r.choose 2 = r * (r - 1) := by
    have h1 := p01_choose_mul_succ (r - 1) 1; have hr1 : r - 1 + 1 = r := (by omega)
    rw [hr1, Nat.choose_one_right] at h1; linarith
  have hm_ch := Nat.choose_succ_right_eq (N - r) (m - 2)
  have hm2' : m - 2 + 1 = m - 1 := (by omega)
  have hsub : N - r - (m - 2) = N - r - m + 2 := (by omega); rw [hm2', hsub] at hm_ch
  calc r * (N - r).choose (m - 1) * ((r - 1) * (m - 1))
      = (r * (r - 1)) * ((N - r).choose (m - 1) * (m - 1)) := by ring
    _ = (2 * r.choose 2) * ((N - r).choose (m - 2) * (N - r - m + 2)) := by rw [← hr_ch, hm_ch]
    _ = 2 * (r.choose 2 * (N - r).choose (m - 2)) * (N - r - m + 2) := by ring
theorem choose_rel_p01 {N m : ℕ} (hm1 : 1 ≤ m) (h2m : 2 * m < N) :
    m * (N - m) * N.choose m = N * (N - 1) * (N - 2).choose (m - 1) := by
  have h0 := p01_choose_mul_succ (N - 1) (m - 1); have hN1 : N - 1 + 1 = N := (by omega)
  have hm1' : m - 1 + 1 = m := (by omega); rw [hN1, hm1'] at h0
  have hc_eq : (N - 1).choose (m - 1) = (N - 1).choose (N - m) := by
    rw [← Nat.choose_symm (by omega : m - 1 ≤ N - 1)]; congr 1; omega
  have hd_eq : (N - 2).choose (m - 1) = (N - 2).choose (N - m - 1) := by
    rw [← Nat.choose_symm (by omega : m - 1 ≤ N - 2)]; congr 1; omega
  have h1 := p01_choose_mul_succ (N - 2) (N - m - 1); have hN21 : N - 2 + 1 = N - 1 := (by omega)
  have hNm1 : N - m - 1 + 1 = N - m := (by omega); rw [hN21, hNm1, ← hc_eq, ← hd_eq] at h1
  calc m * (N - m) * N.choose m
      = (N - m) * (m * N.choose m) := by ring
    _ = (N - m) * (N * (N - 1).choose (m - 1)) := by rw [← h0]
    _ = N * ((N - m) * (N - 1).choose (m - 1)) := by ring
    _ = N * ((N - 1) * (N - 2).choose (m - 1)) := by rw [← h1]
    _ = N * (N - 1) * (N - 2).choose (m - 1) := by ring
/-! ## Section 2: Isometric 3D Orbit Embedding `orbEmbed3` -/
/-- Explicit 3-vector constructor on `Fin 3 → ℝ`. -/
def vec3 (a b c : ℝ) (i : Fin 3) : ℝ :=
  match i.1 with
  | 0 => a
  | 1 => b
  | _ => c
@[simp] theorem vec3_zero (a b c : ℝ) : vec3 a b c 0 = a := rfl
@[simp] theorem vec3_one (a b c : ℝ) : vec3 a b c 1 = b := rfl
@[simp] theorem vec3_two (a b c : ℝ) : vec3 a b c 2 = c := rfl
theorem fin3_ext {x y : Fin 3 → ℝ} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) :
    x = y := by
  ext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2
/-- Euclidean dot product on `Fin 3 → ℝ`. -/
def dot3 (a b : Fin 3 → ℝ) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
/-- Euclidean cross product on `Fin 3 → ℝ`. -/
def cross3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  vec3 (a 1 * b 2 - a 2 * b 1) (a 2 * b 0 - a 0 * b 2) (a 0 * b 1 - a 1 * b 0)
/-- Householder reflection `I - 2 u uᵀ` on `Fin 3 → ℝ`. -/
def refl3 (u x : Fin 3 → ℝ) : Fin 3 → ℝ := fun i ↦ x i - 2 * dot3 u x * u i
/-- Parity reflection `diag(1, -1, 1)` on `Fin 3 → ℝ`. -/
def zOrb3 (x : Fin 3 → ℝ) : Fin 3 → ℝ := vec3 (x 0) (- x 1) (x 2)
theorem inter_card_lt_three {N m : ℕ} {R : Finset (Fin N)} (hmin : min m R.card ≤ 2)
    (E : P01Subset N m) : (E.1 ∩ R).card < 3 := by
  have h1 : (E.1 ∩ R).card ≤ m := (Finset.card_le_card Finset.inter_subset_left).trans E.2.le
  have h2 : (E.1 ∩ R).card ≤ R.card := Finset.card_le_card Finset.inter_subset_right
  have hle : (E.1 ∩ R).card ≤ min m R.card := le_min h1 h2; omega
/-- Isometric embedding of `Fin 3 → ℝ` onto the `(S_r × S_{N-r})`-orbit basis of `P01Subset
  N m`. -/
noncomputable def orbEmbed3 (N m : ℕ) (R : Finset (Fin N)) (x : Fin 3 → ℝ)
    (E : P01Subset N m) : ℝ :=
  let w := (E.1 ∩ R).card
  if hw : w < 3 then x ⟨w, hw⟩ / √(orbCard N m R.card w : ℝ) else 0
theorem card_p01Subset_inter_eq {N m : ℕ} (R : Finset (Fin N)) {w : ℕ} (hw : w ≤ m) :
    (Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w)).card =
      orbCard N m R.card w := by
  rw [card_p01Subset_filter N m (fun S ↦ (S ∩ R).card = w), card_powersetCard_inter_eq R m w hw,
    Fintype.card_fin]; rfl
theorem sum_mul_orbEmbed3_filter {N m : ℕ} {R : Finset (Fin N)}
    (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card) (hmrN : m + R.card < N) (x y : Fin 3 → ℝ) (w : Fin 3) :
    (∑ E ∈ Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w.1),
      orbEmbed3 N m R x E * orbEmbed3 N m R y E) = x w * y w := by
  have hw2 : w.1 ≤ 2 := (by omega)
  have hpos : (0 : ℝ) < (orbCard N m R.card w.1 : ℝ) :=
    Nat.cast_pos.mpr (orbCard_pos hm2 hr2 hmrN hw2)
  have hcongr : (∑ E ∈ Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w.1),
    orbEmbed3 N m R x E * orbEmbed3 N m R y E) = ∑ _ ∈ Finset.univ.filter (fun E : P01Subset N m ↦
    (E.1 ∩ R).card = w.1), (x w * y w) / (orbCard N m R.card w.1 : ℝ) := by
    refine Finset.sum_congr rfl fun E hE ↦ ?_
    have hwE : (E.1 ∩ R).card = w.1 := (Finset.mem_filter.mp hE).2; unfold orbEmbed3; dsimp only
    split_ifs with hlt
    · have hfin : (⟨(E.1 ∩ R).card, hlt⟩ : Fin 3) = w := Fin.ext hwE
      rw [hfin, hwE, div_mul_div_comm, Real.mul_self_sqrt hpos.le]
    · exact absurd (hwE ▸ w.2) hlt
  rw [hcongr, Finset.sum_const, card_p01Subset_inter_eq R (by omega), nsmul_eq_mul,
    mul_div_cancel₀ _ hpos.ne']
theorem sum_sq_orbEmbed3_filter {N m : ℕ} {R : Finset (Fin N)} (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card)
    (hmrN : m + R.card < N) (x : Fin 3 → ℝ) (w : Fin 3) : (∑ E ∈ Finset.univ.filter (fun E :
    P01Subset N m ↦ (E.1 ∩ R).card = w.1), (orbEmbed3 N m R x E) ^ 2) = (x w) ^ 2 := by
  simpa only [sq] using sum_mul_orbEmbed3_filter hm2 hr2 hmrN x x w
theorem dot_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)} (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card) (hmin : min
    m R.card ≤ 2) (hmrN : m + R.card < N) (x y : Fin 3 → ℝ) : (∑ E : P01Subset N m, orbEmbed3 N m
    R x E * orbEmbed3 N m R y E) = dot3 x y := by
  let f : P01Subset N m → Fin 3 := fun E ↦ ⟨(E.1 ∩ R).card, inter_card_lt_three hmin E⟩
  have hpart := (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := f) (fun _ _ ↦ Finset.mem_univ _)
    (f := fun E ↦ orbEmbed3 N m R x E * orbEmbed3 N m R y E)).symm
  rw [hpart, Fin.sum_univ_three]
  have hfib : ∀ w : Fin 3, Finset.univ.filter (fun E : P01Subset N m ↦ f E = w) =
        Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w.1) := by
    intro w; ext E; simp [f, Fin.ext_iff]
  rw [hfib 0, hfib 1, hfib 2, sum_mul_orbEmbed3_filter hm2 hr2 hmrN x y 0,
    sum_mul_orbEmbed3_filter hm2 hr2 hmrN x y 1, sum_mul_orbEmbed3_filter hm2 hr2 hmrN x y 2]; rfl
/-! ## Section 3: Orthonormal Basis `{u0OrbVec, u1OrbVec, u2OrbVec}` & Intertwining -/
/-- Orbit coordinates of the uniform subset state `|u_0⟩`. -/
noncomputable def u0OrbVec (N m r : ℕ) : Fin 3 → ℝ :=
  fun w ↦ √((orbCard N m r w.1 : ℝ) / (N.choose m : ℝ))
/-- Orbit coordinates of `Φ_1 |e_R⟩`. -/
noncomputable def u1OrbVec (N m r : ℕ) : Fin 3 → ℝ :=
  fun w ↦ ((w.1 : ℝ) * (N : ℝ) - (m : ℝ) * (r : ℝ)) * √((orbCard N m r w.1 : ℝ) /
      (((N - 2).choose (m - 1) : ℝ) * (r : ℝ) * ((N - r : ℕ) : ℝ) * (N : ℝ)))
/-- Orthogonal complement basis vector `u0OrbVec ×₃ u1OrbVec` in `Fin 3 → ℝ`. -/
noncomputable def u2OrbVec (N m r : ℕ) : Fin 3 → ℝ := cross3 (u0OrbVec N m r) (u1OrbVec N m r)
theorem orbEmbed3_u0OrbVec {N m : ℕ} {R : Finset (Fin N)}
    (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card) (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) :
    orbEmbed3 N m R (u0OrbVec N m R.card) = fun _ ↦ 1 / √(N.choose m : ℝ) := by
  ext E; have hlt := inter_card_lt_three hmin E
  have hc_pos : (0 : ℝ) < (orbCard N m R.card (E.1 ∩ R).card : ℝ) :=
    Nat.cast_pos.mpr (orbCard_pos hm2 hr2 hmrN (by omega))
  unfold orbEmbed3 u0OrbVec; simp only [hlt, ↓reduceDIte]
  rw [Real.sqrt_div hc_pos.le, div_right_comm, div_self (Real.sqrt_pos.mpr hc_pos).ne']
/-- Unique `(S_r × S_{N-r})`-invariant zero-sum unit vector in `ℝ^N`. -/
noncomputable def eRVec {N : ℕ} (R : Finset (Fin N)) : Fin N → ℝ := fun y ↦
    if y ∈ R then √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ)))
    else - √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ)))
private lemma eRVec_sum_zero {N : ℕ} {R : Finset (Fin N)} (hr : 0 < R.card) (hrN : R.card < N) :
    ∑ y : Fin N, eRVec R y = 0 := by
  have hrR : (0 : ℝ) < (R.card : ℝ) := Nat.cast_pos.mpr hr
  have hnrR : (0 : ℝ) < ((N - R.card : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsplit := (Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· ∈ R))
    (f := eRVec R)).symm
  rw [hsplit]; have h1 : (∑ y ∈ Finset.univ.filter (· ∈ R), eRVec R y) =
      (R.card : ℝ) * √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) := by
    have hcongr : (∑ y ∈ Finset.univ.filter (· ∈ R), eRVec R y) =
        ∑ _ ∈ R, √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.sum_congr rfl fun y hy ↦ by simp [eRVec, hy]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have h2 : (∑ y ∈ Finset.univ.filter (fun y ↦ y ∉ R), eRVec R y) =
      - ((N - R.card : ℕ) : ℝ) * √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ))) := by
    have hflt : Finset.univ.filter (fun y : Fin N ↦ y ∉ R) = Rᶜ := (by ext y; simp)
    have hcongr : (∑ y ∈ Rᶜ, eRVec R y) =
        ∑ _ ∈ Rᶜ, (- √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ)))) :=
      Finset.sum_congr rfl fun y hy ↦ by simp [eRVec, Finset.mem_compl.mp hy]
    rw [hflt, hcongr, Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [h1, h2]; have hsq_eq : (R.card : ℝ) * √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) =
        ((N - R.card : ℕ) : ℝ) * √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ))) := by
    have hnn1 : 0 ≤ (R.card : ℝ) * √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) := by
      positivity
    have hnn2 :
        0 ≤ ((N - R.card : ℕ) : ℝ) * √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ))) := by
      positivity
    rw [← Real.sqrt_sq hnn1, ← Real.sqrt_sq hnn2]; congr 1
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; field_simp
  linarith
private lemma eRVec_dot_self {N : ℕ} {R : Finset (Fin N)} (hr : 0 < R.card) (hrN : R.card < N) :
    (∑ y : Fin N, eRVec R y * eRVec R y) = 1 := by
  have hrR : (0 : ℝ) < (R.card : ℝ) := Nat.cast_pos.mpr hr
  have hnrR : (0 : ℝ) < ((N - R.card : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· ∈ R))]
  have h1 : (∑ y ∈ Finset.univ.filter (· ∈ R), eRVec R y * eRVec R y) =
      ((N - R.card : ℕ) : ℝ) / (N : ℝ) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]; have hc : (∑ y ∈ R, eRVec R y * eRVec R y) =
        ∑ _ ∈ R, ((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ)) := by
      refine Finset.sum_congr rfl fun y hy ↦ ?_; simp only [eRVec, hy, ↓reduceIte]
      exact Real.mul_self_sqrt (by positivity)
    rw [hc, Finset.sum_const, nsmul_eq_mul]; field_simp
  have h2 : (∑ y ∈ Finset.univ.filter (fun y ↦ y ∉ R), eRVec R y * eRVec R y) =
      (R.card : ℝ) / (N : ℝ) := by
    have hflt : Finset.univ.filter (fun y : Fin N ↦ y ∉ R) = Rᶜ := (by ext y; simp)
    have hc : (∑ y ∈ Rᶜ, eRVec R y * eRVec R y) =
        ∑ _ ∈ Rᶜ, (R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ)) := by
      refine Finset.sum_congr rfl fun y hy ↦ ?_; have hyn : y ∉ R := Finset.mem_compl.mp hy
      simp only [eRVec, hyn, ↓reduceIte, neg_mul_neg]; exact Real.mul_self_sqrt (by positivity)
    rw [hflt, hc, Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]; field_simp
  rw [h1, h2, ← add_div, Nat.cast_sub hrN.le, sub_add_cancel, div_self hNR.ne']
theorem phi1Mat_mulVec_eRVec {N m : ℕ} {R : Finset (Fin N)}
    (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card) (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) :
    phi1Mat N m *ᵥ eRVec R = orbEmbed3 N m R (u1OrbVec N m R.card) := by
  have hr : 0 < R.card := (by omega); have hrN : R.card < N := (by omega)
  have hrR : (0 : ℝ) < (R.card : ℝ) := Nat.cast_pos.mpr hr
  have hnrR : (0 : ℝ) < ((N - R.card : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hD_pos : (0 : ℝ) < ((N - 2).choose (m - 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  ext E; simp only [Matrix.mulVec, dotProduct, phi1Mat, Matrix.of_apply]
  have hterm : ∀ y : Fin N, (((if y ∈ E.1 then (1 : ℝ) else 0) - (m : ℝ) / (N : ℝ)) / √((N -
    2).choose (m - 1) : ℝ)) * eRVec R y = ((if y ∈ E.1 then eRVec R y else 0) - ((m : ℝ) / (N :
    ℝ)) * eRVec R y) / √((N - 2).choose (m - 1) : ℝ) := by
    intro y; by_cases hy : y ∈ E.1 <;> simp only [hy, ↓reduceIte] <;> ring
  simp_rw [hterm, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    eRVec_sum_zero hr hrN, mul_zero, sub_zero]
  have hsumE : (∑ y : Fin N, if y ∈ E.1 then eRVec R y else 0) = ∑ y ∈ E.1, eRVec R y := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hsumE, ← Finset.sum_filter_add_sum_filter_not (s := E.1) (p := (· ∈ R))]
  set w := (E.1 ∩ R).card; have hw_lt : w < 3 := inter_card_lt_three hmin E
  have hw_le_m : w ≤ m := (Finset.card_le_card Finset.inter_subset_left).trans E.2.le
  have hc_pos : (0 : ℝ) < (orbCard N m R.card w : ℝ) :=
    Nat.cast_pos.mpr (orbCard_pos hm2 hr2 hmrN (by omega))
  have hE1 : (∑ y ∈ E.1.filter (· ∈ R), eRVec R y) =
      (w : ℝ) * √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) := by
    rw [Finset.filter_mem_eq_inter]; have hc : (∑ y ∈ E.1 ∩ R, eRVec R y) =
        ∑ _ ∈ E.1 ∩ R, √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) :=
      Finset.sum_congr rfl fun y hy ↦ by simp [eRVec, (Finset.mem_inter.mp hy).2]
    rw [hc, Finset.sum_const, nsmul_eq_mul]
  have hE2 : (∑ y ∈ E.1.filter (fun y ↦ y ∉ R), eRVec R y) =
      - ((m - w : ℕ) : ℝ) * √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ))) := by
    have hc : (∑ y ∈ E.1.filter (fun y ↦ y ∉ R), eRVec R y) = ∑ _ ∈ E.1.filter (fun y ↦ y ∉ R),
          (- √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ)))) :=
      Finset.sum_congr rfl fun y hy ↦ by simp [eRVec, (Finset.mem_filter.mp hy).2]
    have hcard_not : (E.1.filter (fun y ↦ y ∉ R)).card = m - w := by
      have htot := Finset.sum_filter_add_sum_filter_not (s := E.1) (p := (· ∈ R))
        (f := fun _ ↦ (1 : ℕ))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.filter_mem_eq_inter, E.2] at htot
      omega
    rw [hc, Finset.sum_const, hcard_not, nsmul_eq_mul]; ring
  rw [hE1, hE2]; unfold orbEmbed3 u1OrbVec; dsimp only; split_ifs with hlt
  · have hw_eq : (E.1 ∩ R).card = w := rfl
    have ha : √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) =
        ((N - R.card : ℕ) : ℝ) / √((R.card : ℝ) * ((N - R.card : ℕ) : ℝ) * (N : ℝ)) := by
      rw [Real.sqrt_div hnrR.le, eq_div_iff (by positivity)]
      calc √((N - R.card : ℕ) : ℝ) / √((R.card : ℝ) * (N : ℝ)) * √((R.card : ℝ) * ((N - R.card :
            ℕ) : ℝ) * (N : ℝ)) = √((N - R.card : ℕ) : ℝ) * √((N - R.card : ℕ) : ℝ) * (√((R.card :
            ℝ) * (N : ℝ)) / √((R.card : ℝ) * (N : ℝ))) := by
            rw [show (R.card : ℝ) * ((N - R.card : ℕ) : ℝ) * (N : ℝ) =
              ((N - R.card : ℕ) : ℝ) * ((R.card : ℝ) * (N : ℝ)) by ring,
              Real.sqrt_mul hnrR.le]
            ring
        _ = ((N - R.card : ℕ) : ℝ) := by
            rw [Real.mul_self_sqrt hnrR.le, div_self (by positivity), mul_one]
    have hb : √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ))) =
        (R.card : ℝ) / √((R.card : ℝ) * ((N - R.card : ℕ) : ℝ) * (N : ℝ)) := by
      rw [Real.sqrt_div hrR.le, eq_div_iff (by positivity)]
      calc √(R.card : ℝ) / √(((N - R.card : ℕ) : ℝ) * (N : ℝ)) * √((R.card : ℝ) * ((N - R.card :
            ℕ) : ℝ) * (N : ℝ)) = √(R.card : ℝ) * √(R.card : ℝ) * (√(((N - R.card : ℕ) : ℝ) * (N :
            ℝ)) / √(((N - R.card : ℕ) : ℝ) * (N : ℝ))) := by
            rw [mul_assoc, Real.sqrt_mul hrR.le]; ring
        _ = (R.card : ℝ) := by rw [Real.mul_self_sqrt hrR.le, div_self (by positivity), mul_one]
    simp only [hw_eq]; rw [ha, hb, Nat.cast_sub hrN.le, Nat.cast_sub hw_le_m]
    have hden_eq : √((orbCard N m R.card w : ℝ) / (((N - 2).choose (m - 1) : ℝ) * (R.card : ℝ) *
      ((N : ℝ) - (R.card : ℝ)) * (N : ℝ))) / √(orbCard N m R.card w : ℝ) = 1 / (√((R.card : ℝ) *
      ((N : ℝ) - (R.card : ℝ)) * (N : ℝ)) * √((N - 2).choose (m - 1) : ℝ)) := by
      have hsub_pos : 0 < (N : ℝ) - (R.card : ℝ) := (by rw [← Nat.cast_sub hrN.le]; exact hnrR)
      have hmul_den :
          ((N - 2).choose (m - 1) : ℝ) * (R.card : ℝ) * ((N : ℝ) - (R.card : ℝ)) * (N : ℝ) =
            ((R.card : ℝ) * ((N : ℝ) - (R.card : ℝ)) * (N : ℝ)) *
              ((N - 2).choose (m - 1) : ℝ) := by ring
      rw [Real.sqrt_div hc_pos.le, div_right_comm, div_self (Real.sqrt_pos.mpr hc_pos).ne',
        hmul_den, Real.sqrt_mul (by positivity)]
    rw [Nat.cast_sub hrN.le] at *; rw [mul_div_assoc, hden_eq]; field_simp; ring
  · exact absurd hw_lt hlt
private lemma phi1Mat_transpose_mulVec_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)} (hm2 : 2 ≤ m) (hr2
    : 2 ≤ R.card) (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) (x : Fin 3 → ℝ) : (phi1Mat N
    m)ᵀ *ᵥ orbEmbed3 N m R x = dot3 (u1OrbVec N m R.card) x • eRVec R := by
  have hr : 0 < R.card := (by omega); have hrN : R.card < N := (by omega)
  have hrR : (0 : ℝ) < (R.card : ℝ) := Nat.cast_pos.mpr hr
  have hnrR : (0 : ℝ) < ((N - R.card : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  set g : Fin N → ℝ := (phi1Mat N m)ᵀ *ᵥ orbEmbed3 N m R x
  have hg_sum : ∑ y : Fin N, g y = 0 := by
    dsimp only [g, Matrix.mulVec, dotProduct, Matrix.transpose_apply]; rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun E _ ↦ ?_
    rw [← Finset.sum_mul, phi1Mat_row_sum (by omega) E, zero_mul]
  have hg_inv : ∀ y₁ y₂ : Fin N, (y₁ ∈ R ↔ y₂ ∈ R) → g y₁ = g y₂ := by
    intro y₁ y₂ hiff; let σ : Fin N ≃ Fin N := Equiv.swap y₁ y₂
    have hinv : ∀ E : P01Subset N m, (⟨(E.1.image σ).image σ,
          (Finset.card_image_of_injective _ σ.injective).trans
            ((Finset.card_image_of_injective _ σ.injective).trans E.2)⟩ : P01Subset N m) = E := by
      intro E; apply Subtype.ext; ext z; simp only [Finset.mem_image]; constructor
      · rintro ⟨a, ⟨b, hb, hba⟩, haz⟩
        rw [← haz, ← hba]; simpa [σ, Equiv.swap_apply_self] using hb
      · intro hz; exact ⟨σ z, ⟨z, hz, rfl⟩, Equiv.swap_apply_self y₁ y₂ z⟩
    let eSub : P01Subset N m ≃ P01Subset N m :=
      { toFun := fun E ↦ ⟨E.1.image σ, (Finset.card_image_of_injective E.1 σ.injective).trans E.2⟩
        invFun := fun E ↦ ⟨E.1.image σ, (Finset.card_image_of_injective E.1 σ.injective).trans E.2⟩
        left_inv := hinv
        right_inv := hinv }
    have heSub_val : ∀ E : P01Subset N m, (eSub E).1 = E.1.image σ := fun _ ↦ rfl
    have hσR : ∀ z : Fin N, σ z ∈ R ↔ z ∈ R := by
      intro z; by_cases hz1 : z = y₁
      · subst hz1; simpa [σ, Equiv.swap_apply_left] using hiff.symm
      · by_cases hz2 : z = y₂
        · subst hz2; simpa [σ, Equiv.swap_apply_right] using hiff
        · simp [σ, Equiv.swap_apply_of_ne_of_ne hz1 hz2]
    dsimp only [g, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    refine Fintype.sum_equiv eSub _ _ fun E ↦ ?_
    have hcard_eq : ((eSub E).1 ∩ R).card = (E.1 ∩ R).card := by
      have himg : (eSub E).1 ∩ R = (E.1 ∩ R).image σ := by
        rw [heSub_val E]; ext z; simp only [Finset.mem_inter, Finset.mem_image]; constructor
        · rintro ⟨⟨a, haE, rfl⟩, hσaR⟩
          exact ⟨a, ⟨haE, (hσR a).mp hσaR⟩, rfl⟩
        · rintro ⟨a, ⟨haE, haR⟩, rfl⟩
          exact ⟨⟨a, haE, rfl⟩, (hσR a).mpr haR⟩
      rw [himg, Finset.card_image_of_injective _ σ.injective]
    have horb_eq : orbEmbed3 N m R x (eSub E) = orbEmbed3 N m R x E := by
      unfold orbEmbed3; simp only [hcard_eq]
    have hmem_eq : (y₂ ∈ (eSub E).1) ↔ (y₁ ∈ E.1) := by
      rw [heSub_val E, Finset.mem_image]; constructor
      · rintro ⟨a, haE, ha2⟩
        have hay1 : a = y₁ := by
          have := congrArg σ ha2
          simpa [σ, Equiv.swap_apply_self, Equiv.swap_apply_right] using this
        rwa [← hay1]
      · intro hy1E; exact ⟨y₁, hy1E, Equiv.swap_apply_left y₁ y₂⟩
    rw [horb_eq]; congr 1; simp only [phi1Mat, Matrix.of_apply, hmem_eq]
  obtain ⟨yR, hyR⟩ := Finset.card_pos.mp hr
  have hrc_pos : 0 < Rᶜ.card := (by rw [Finset.card_compl, Fintype.card_fin]; omega)
  obtain ⟨yC, hyC_mem⟩ := Finset.card_pos.mp hrc_pos
  have hyC : yC ∉ R := Finset.mem_compl.mp hyC_mem
  have hg_R : ∀ y ∈ R, g y = g yR := fun y hy ↦ hg_inv y yR ⟨fun _ ↦ hyR, fun _ ↦ hy⟩
  have hg_C : ∀ y ∉ R, g y = g yC := fun y hy ↦
    hg_inv y yC ⟨fun h ↦ absurd h hy, fun h ↦ absurd h hyC⟩
  have hlin : (R.card : ℝ) * g yR + ((N - R.card : ℕ) : ℝ) * g yC = 0 := by
    have hsp := (Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· ∈ R))
      (f := g)).symm
    rw [hg_sum] at hsp
    have h1 : (∑ y ∈ Finset.univ.filter (· ∈ R), g y) = (R.card : ℝ) * g yR := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_congr rfl (fun y hy ↦ hg_R y hy), Finset.sum_const, nsmul_eq_mul]
    have h2 : (∑ y ∈ Finset.univ.filter (fun y ↦ y ∉ R), g y) =
        ((N - R.card : ℕ) : ℝ) * g yC := by
      have hflt : Finset.univ.filter (fun y : Fin N ↦ y ∉ R) = Rᶜ := (by ext y; simp)
      rw [hflt, Finset.sum_congr rfl (fun y hy ↦ hg_C y (Finset.mem_compl.mp hy)),
        Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hdot : (∑ y : Fin N, eRVec R y * g y) = dot3 (u1OrbVec N m R.card) x := by
    calc (∑ y : Fin N, eRVec R y * g y)
        = ∑ y : Fin N, eRVec R y * ∑ E : P01Subset N m, phi1Mat N m E y * orbEmbed3 N m R x E := rfl
      _ = ∑ E : P01Subset N m, (phi1Mat N m *ᵥ eRVec R) E * orbEmbed3 N m R x E := by
            simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun E _ ↦ ?_
            simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
            refine Finset.sum_congr rfl fun y _ ↦ by ring
      _ = dot3 (u1OrbVec N m R.card) x := by
            rw [phi1Mat_mulVec_eRVec hm2 hr2 hmin hmrN, dot_orbEmbed3 hm2 hr2 hmin hmrN]
  have hsmul : ∀ y : Fin N, g y = (∑ z : Fin N, eRVec R z * g z) * eRVec R y := by
    set sA : ℝ := √(((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ)))
    set sB : ℝ := √((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ)))
    have hsA_sq : sA * sA = ((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ)) :=
      Real.mul_self_sqrt (by positivity)
    have hsB_sq : sB * sB = (R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ)) :=
      Real.mul_self_sqrt (by positivity)
    have hsAB : sA * sB = 1 / (N : ℝ) := by
      dsimp only [sA, sB]; rw [← Real.sqrt_mul (by positivity)]
      have harg : (((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) *
          ((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ))) = (1 / (N : ℝ)) ^ 2 := by
        field_simp
      rw [harg, Real.sqrt_sq (by positivity)]
    have hsum_eg : (∑ z : Fin N, eRVec R z * g z) =
        (R.card : ℝ) * sA * g yR - ((N - R.card : ℕ) : ℝ) * sB * g yC := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· ∈ R))]
      have h1 : (∑ z ∈ Finset.univ.filter (· ∈ R), eRVec R z * g z) =
          (R.card : ℝ) * sA * g yR := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        have hc : (∑ z ∈ R, eRVec R z * g z) = ∑ _ ∈ R, sA * g yR :=
          Finset.sum_congr rfl fun z hz ↦ by simp [eRVec, hz, hg_R z hz, sA]
        rw [hc, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      have h2 : (∑ z ∈ Finset.univ.filter (fun z ↦ z ∉ R), eRVec R z * g z) =
          - (((N - R.card : ℕ) : ℝ) * sB * g yC) := by
        have hflt : Finset.univ.filter (fun z : Fin N ↦ z ∉ R) = Rᶜ := (by ext z; simp)
        have hc : (∑ z ∈ Rᶜ, eRVec R z * g z) = ∑ _ ∈ Rᶜ, (- sB) * g yC :=
          Finset.sum_congr rfl fun z hz ↦ by
            have hzn := Finset.mem_compl.mp hz; simp [eRVec, hzn, hg_C z hzn, sB]
        rw [hflt, hc, Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]; ring
      rw [h1, h2]; ring
    have h1_lin : ((N - R.card : ℕ) : ℝ) * g yC = - ((R.card : ℝ) * g yR) := (by linarith)
    have h2_lin : (R.card : ℝ) * g yR = - (((N - R.card : ℕ) : ℝ) * g yC) := (by linarith)
    have hnrN : ((N - R.card : ℕ) : ℝ) + (R.card : ℝ) = (N : ℝ) := by
      rw [Nat.cast_sub hrN.le, sub_add_cancel]
    have hrnN : (R.card : ℝ) + ((N - R.card : ℕ) : ℝ) = (N : ℝ) := (by linarith); intro y
    rw [hsum_eg]; by_cases hy : y ∈ R
    · rw [hg_R y hy]; have heR : eRVec R y = sA := (by unfold eRVec; rw [ite_eq_left hy]); rw [heR]
      have h1 : (R.card : ℝ) * g yR * (((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) =
          g yR * (((N - R.card : ℕ) : ℝ) / (N : ℝ)) := by
        calc (R.card : ℝ) * g yR * (((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ)))
            = g yR * ((((N - R.card : ℕ) : ℝ) * (R.card : ℝ)) /
                ((N : ℝ) * (R.card : ℝ))) := by ring
          _ = g yR * (((N - R.card : ℕ) : ℝ) / (N : ℝ)) := by rw [mul_div_mul_right _ _ hrR.ne']
      calc g yR = g yR * ((((N - R.card : ℕ) : ℝ) + (R.card : ℝ)) / (N : ℝ)) := by
              rw [hnrN, div_self hNR.ne', mul_one]
        _ = g yR * (((N - R.card : ℕ) : ℝ) / (N : ℝ)) -
              (- ((R.card : ℝ) * g yR)) * (1 / (N : ℝ)) := by ring
        _ = (R.card : ℝ) * g yR * (((N - R.card : ℕ) : ℝ) / ((R.card : ℝ) * (N : ℝ))) -
              (- ((R.card : ℝ) * g yR)) * (1 / (N : ℝ)) := by rw [h1]
        _ = (R.card : ℝ) * g yR * (sA * sA) -
              (((N - R.card : ℕ) : ℝ) * g yC) * (sA * sB) := by
              rw [hsA_sq, hsAB, h1_lin]
        _ = ((R.card : ℝ) * sA * g yR - ((N - R.card : ℕ) : ℝ) * sB * g yC) * sA := by ring
    · rw [hg_C y hy]; have heC : eRVec R y = - sB := (by unfold eRVec; rw [ite_eq_right hy])
      rw [heC]
      have h1 : ((N - R.card : ℕ) : ℝ) * g yC * ((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N :
        ℝ))) = g yC * ((R.card : ℝ) / (N : ℝ)) := by
        calc ((N - R.card : ℕ) : ℝ) * g yC *
              ((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ)))
            = g yC * (((R.card : ℝ) * ((N - R.card : ℕ) : ℝ)) /
                ((N : ℝ) * ((N - R.card : ℕ) : ℝ))) := by ring
          _ = g yC * ((R.card : ℝ) / (N : ℝ)) := by rw [mul_div_mul_right _ _ hnrR.ne']
      calc g yC = g yC * (((R.card : ℝ) + ((N - R.card : ℕ) : ℝ)) / (N : ℝ)) := by
              rw [hrnN, div_self hNR.ne', mul_one]
        _ = (((N - R.card : ℕ) : ℝ) * g yC) * (1 / (N : ℝ)) +
              g yC * ((R.card : ℝ) / (N : ℝ)) := by ring
        _ = (((N - R.card : ℕ) : ℝ) * g yC) * (1 / (N : ℝ)) + ((N - R.card : ℕ) : ℝ) * g yC *
                ((R.card : ℝ) / (((N - R.card : ℕ) : ℝ) * (N : ℝ))) := by rw [h1]
        _ = (- ((R.card : ℝ) * g yR)) * (sA * sB) +
              ((N - R.card : ℕ) : ℝ) * g yC * (sB * sB) := by
              rw [hsAB, hsB_sq, h2_lin]; ring
        _ = ((R.card : ℝ) * sA * g yR - ((N - R.card : ℕ) : ℝ) * sB * g yC) * (- sB) := by ring
  ext y; rw [Pi.smul_apply, smul_eq_mul, ← hdot]; exact hsmul y
private lemma smul_mulVec_eq {α β : Type*} [Fintype β] (c : ℝ) (M : Matrix α β ℝ)
    (v : β → ℝ) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
theorem dot3_u0_self {N m r : ℕ} (hm2 : 2 ≤ m) (hr2 : 2 ≤ r) (hmin : min m r ≤ 2)
    (hmrN : m + r < N) : dot3 (u0OrbVec N m r) (u0OrbVec N m r) = 1 := by
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N), R.card = r := Finset.exists_subset_card_eq
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega :
        r ≤ (Finset.univ : Finset (Fin N)).card)
      |>.imp fun R ⟨_, hc⟩ ↦ hc
  subst hR; rw [← dot_orbEmbed3 hm2 hr2 hmin hmrN, orbEmbed3_u0OrbVec hm2 hr2 hmin hmrN]
  have hc_pos : (0 : ℝ) < (N.choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  simp only [Finset.sum_const, Finset.card_univ, card_p01Subset, nsmul_eq_mul,
    div_mul_div_comm, one_mul, Real.mul_self_sqrt hc_pos.le, mul_div_cancel₀ _ hc_pos.ne']
theorem dot3_u1_self {N m r : ℕ} (hm2 : 2 ≤ m) (hr2 : 2 ≤ r) (hmin : min m r ≤ 2) (hmrN : m + r <
    N) (h2m : 2 * m < N) : dot3 (u1OrbVec N m r) (u1OrbVec N m r) = 1 := by
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N), R.card = r := Finset.exists_subset_card_eq
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega :
        r ≤ (Finset.univ : Finset (Fin N)).card)
      |>.imp fun R ⟨_, hc⟩ ↦ hc
  subst hR; rw [← dot_orbEmbed3 hm2 hr2 hmin hmrN, ← phi1Mat_mulVec_eRVec hm2 hr2 hmin hmrN]
  have hgram := congrArg (· *ᵥ eRVec R) (phi1Mat_transpose_mul_self (by omega : 1 ≤ m) h2m)
  have hlhs : ((phi1Mat N m)ᵀ * phi1Mat N m) *ᵥ eRVec R =
      (phi1Mat N m)ᵀ *ᵥ (phi1Mat N m *ᵥ eRVec R) := (Matrix.mulVec_mulVec _ _ _).symm
  have he0 : ∑ i : Fin N, eRVec R i = 0 := eRVec_sum_zero (by omega) (by omega)
  have hJ : Matrix.of (fun _ _ : Fin N ↦ (1 : ℝ)) *ᵥ eRVec R = 0 := by
    ext y; simp [Matrix.mulVec, dotProduct, he0]
  rw [hlhs, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec_eq, hJ, smul_zero, sub_zero] at hgram
  set v := phi1Mat N m *ᵥ eRVec R; have hv_eq : (∑ E : P01Subset N m, v E * v E) =
      ∑ y : Fin N, eRVec R y * ((phi1Mat N m)ᵀ *ᵥ v) y := by
    have hexp : ∀ E : P01Subset N m, v E * v E =
        ∑ y : Fin N, phi1Mat N m E y * eRVec R y * v E := by
      intro E; simp [v, Matrix.mulVec, dotProduct, Finset.sum_mul]
    simp_rw [hexp]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun E _ ↦ by ring
  rw [hv_eq, hgram, eRVec_dot_self (by omega) (by omega)]
theorem dot3_u0_u1 {N m r : ℕ} (hm2 : 2 ≤ m) (hr2 : 2 ≤ r) (hmin : min m r ≤ 2)
    (hmrN : m + r < N) : dot3 (u0OrbVec N m r) (u1OrbVec N m r) = 0 := by
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N), R.card = r := Finset.exists_subset_card_eq
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega :
        r ≤ (Finset.univ : Finset (Fin N)).card)
      |>.imp fun R ⟨_, hc⟩ ↦ hc
  subst hR
  rw [← dot_orbEmbed3 hm2 hr2 hmin hmrN, orbEmbed3_u0OrbVec hm2 hr2 hmin hmrN,
    ← phi1Mat_mulVec_eRVec hm2 hr2 hmin hmrN, ← Finset.mul_sum]
  have hsum0 : (∑ E : P01Subset N m, (phi1Mat N m *ᵥ eRVec R) E) = 0 := by
    have hcol : ∀ y : Fin N, (∑ E : P01Subset N m, phi1Mat N m E y) = 0 := by
      intro y
      have habs : (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) = (m : ℝ) * (N.choose m : ℝ) := by
        have h := p01_choose_mul_succ (N - 1) (m - 1); have hN1 : N - 1 + 1 = N := (by omega)
        have hm1 : m - 1 + 1 = m := (by omega); rw [hN1, hm1] at h; exact_mod_cast h
      have hNR : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega : 0 < N)).ne'; have hmem_card :
          ((Finset.univ : Finset (Fin N)).powersetCard m |>.filter (fun S ↦ y ∈ S)).card =
            (N - 1).choose (m - 1) := by
        simpa [Finset.card_univ, Fintype.card_fin] using card_powersetCard_mem (Finset.univ :
          Finset (Fin N)) (Finset.mem_univ y) (by omega : 1 ≤ m)
      simp only [phi1Mat, Matrix.of_apply, ← Finset.sum_div, Finset.sum_sub_distrib,
        Finset.sum_boole, card_p01Subset_filter N m (fun S ↦ y ∈ S), hmem_card,
        Finset.sum_const, Finset.card_univ, card_p01Subset, nsmul_eq_mul]
      rw [div_eq_zero_iff]; left; field_simp; linarith
    simp only [Matrix.mulVec, dotProduct]; rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y _ ↦ ?_; rw [← Finset.sum_mul, hcol y, zero_mul]
  rw [hsum0, mul_zero]
private lemma lagrange_vec3 (u0 u1 x : Fin 3 → ℝ) : (fun i ↦ (cross3 u0 u1) i * dot3 (cross3 u0
    u1) x + dot3 u1 u1 * u0 i * dot3 u0 x + dot3 u0 u0 * u1 i * dot3 u1 x - dot3 u0 u1 * (u0 i *
    dot3 u1 x + u1 i * dot3 u0 x)) = fun i ↦ (dot3 u0 u0 * dot3 u1 u1 - (dot3 u0 u1) ^ 2) * x
    i := by
  refine fin3_ext ?_ ?_ ?_ <;> simp only [cross3, dot3, vec3_zero, vec3_one, vec3_two] <;> ring
theorem parseval_cross3 {u0 u1 : Fin 3 → ℝ} (h0 : dot3 u0 u0 = 1) (h1 : dot3 u1 u1 = 1) (h01 :
    dot3 u0 u1 = 0) (x : Fin 3 → ℝ) : (fun i ↦ dot3 u0 x * u0 i + dot3 u1 x * u1 i + dot3 (cross3
    u0 u1) x * (cross3 u0 u1) i) = x := by
  refine fin3_ext ?_ ?_ ?_
  · have hid := congrFun (lagrange_vec3 u0 u1 x) 0; rw [h0, h1, h01] at hid; linarith
  · have hid := congrFun (lagrange_vec3 u0 u1 x) 1; rw [h0, h1, h01] at hid; linarith
  · have hid := congrFun (lagrange_vec3 u0 u1 x) 2; rw [h0, h1, h01] at hid; linarith
theorem dot3_cross3_self {u0 u1 : Fin 3 → ℝ} (h0 : dot3 u0 u0 = 1) (h1 : dot3 u1 u1 = 1)
    (h01 : dot3 u0 u1 = 0) : dot3 (cross3 u0 u1) (cross3 u0 u1) = 1 := by
  have hid : dot3 (cross3 u0 u1) (cross3 u0 u1) = dot3 u0 u0 * dot3 u1 u1 - (dot3 u0 u1) ^ 2 := by
    simp only [cross3, dot3, vec3_zero, vec3_one, vec3_two]; ring
  rw [hid, h0, h1, h01]; ring
theorem r1SymMat_mulVec_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)} (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card)
    (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) (x : Fin 3 → ℝ) : r1SymMat N m *ᵥ orbEmbed3
    N m R x = orbEmbed3 N m R (refl3 (u1OrbVec N m R.card) x) := by
  have hp1 : pV1Mat N m *ᵥ orbEmbed3 N m R x =
      dot3 (u1OrbVec N m R.card) x • orbEmbed3 N m R (u1OrbVec N m R.card) := by
    rw [pV1Mat, ← Matrix.mulVec_mulVec, phi1Mat_transpose_mulVec_orbEmbed3 hm2 hr2 hmin hmrN,
      Matrix.mulVec_smul, phi1Mat_mulVec_eRVec hm2 hr2 hmin hmrN]
  ext E
  simp only [r1SymMat, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec_eq, hp1,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  unfold orbEmbed3 refl3; dsimp only; split_ifs with hlt <;> ring
theorem r01SymMat_mulVec_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)} (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card)
    (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) (h2m : 2 * m < N) (x : Fin 3 → ℝ) :
    r01SymMat N m *ᵥ orbEmbed3 N m R x = orbEmbed3 N m R (- refl3 (u2OrbVec N m R.card) x) := by
  have hp0 : pV0Mat N m *ᵥ orbEmbed3 N m R x =
      dot3 (u0OrbVec N m R.card) x • orbEmbed3 N m R (u0OrbVec N m R.card) := by
    have hc_pos : (0 : ℝ) < (N.choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hdot0 : dot3 (u0OrbVec N m R.card) x =
        ∑ F : P01Subset N m, (1 / √(N.choose m : ℝ)) * orbEmbed3 N m R x F := by
      rw [← dot_orbEmbed3 hm2 hr2 hmin hmrN, orbEmbed3_u0OrbVec hm2 hr2 hmin hmrN]
    rw [orbEmbed3_u0OrbVec hm2 hr2 hmin hmrN]; ext E
    simp only [pV0Mat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
      hdot0, ← Finset.mul_sum]
    have hsq : 1 / (N.choose m : ℝ) = (1 / √(N.choose m : ℝ)) * (1 / √(N.choose m : ℝ)) := by
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hc_pos.le]
    rw [hsq]; ring
  have hp1 : pV1Mat N m *ᵥ orbEmbed3 N m R x =
      dot3 (u1OrbVec N m R.card) x • orbEmbed3 N m R (u1OrbVec N m R.card) := by
    rw [pV1Mat, ← Matrix.mulVec_mulVec, phi1Mat_transpose_mulVec_orbEmbed3 hm2 hr2 hmin hmrN,
      Matrix.mulVec_smul, phi1Mat_mulVec_eRVec hm2 hr2 hmin hmrN]
  have hpars := parseval_cross3 (dot3_u0_self hm2 hr2 hmin hmrN)
    (dot3_u1_self hm2 hr2 hmin hmrN h2m) (dot3_u0_u1 hm2 hr2 hmin hmrN) x
  have hrefl_eq : (fun i ↦ x i - 2 * dot3 (u0OrbVec N m R.card) x * u0OrbVec N m R.card i - 2 *
    dot3 (u1OrbVec N m R.card) x * u1OrbVec N m R.card i) = - refl3 (u2OrbVec N m R.card) x := by
    ext i; have hi := congrFun hpars i; simp only [Pi.neg_apply, refl3, u2OrbVec]; linarith
  ext E
  simp only [r01SymMat, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec_eq, hp0, hp1,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hrefl_eq]; unfold orbEmbed3; dsimp only; split_ifs with hlt <;> ring
theorem symZ_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)} (hmin : min m R.card ≤ 2) (x : Fin 3 → ℝ) :
    (fun E : P01Subset N m ↦ (-1 : ℝ) ^ (E.1 ∩ R).card * orbEmbed3 N m R x E) =
      orbEmbed3 N m R (zOrb3 x) := by
  ext E; have hlt := inter_card_lt_three hmin E; unfold orbEmbed3; dsimp only
  simp only [hlt, ↓reduceDIte]
  rcases (by omega : (E.1 ∩ R).card = 0 ∨ (E.1 ∩ R).card = 1 ∨ (E.1 ∩ R).card = 2) with
    h0 | h1 | h2
  · have hw : (⟨(E.1 ∩ R).card, hlt⟩ : Fin 3) = 0 := Fin.ext h0; rw [hw, h0]; simp [zOrb3]
  · have hw : (⟨(E.1 ∩ R).card, hlt⟩ : Fin 3) = 1 := Fin.ext h1
    rw [hw, h1, pow_one]; simp only [zOrb3, vec3_one]; ring
  · have hw : (⟨(E.1 ∩ R).card, hlt⟩ : Fin 3) = 2 := Fin.ext h2; rw [hw, h2]; simp [zOrb3]
/-! ## Section 4: Closed-Form `K`-Step 3D 2-Reflection Formulas -/
/-- Positive-branch 3D walk step `(I - 2 u uᵀ) ∘ diag(1, -1, 1)`. -/
def rot3Pos (u x : Fin 3 → ℝ) : Fin 3 → ℝ := refl3 u (zOrb3 x)
/-- Negative-branch 3D walk step `-(I - 2 u uᵀ) ∘ diag(1, -1, 1)`. -/
def rot3Neg (u x : Fin 3 → ℝ) : Fin 3 → ℝ := - refl3 u (zOrb3 x)
theorem iter_lin_2d_3d (T : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hlin : ∀ a b : ℝ, ∀ x y : Fin 3 → ℝ, T (a
    • x + b • y) = a • T x + b • T y) (b1 b2 b3 : Fin 3 → ℝ) (α ε : ℝ) (hb1 : T b1 = Real.cos α •
    b1 + Real.sin α • b2) (hb2 : T b2 = (- Real.sin α) • b1 + Real.cos α • b2) (hb3 : T b3 = ε •
    b3) (K : ℕ) (x1 x2 x3 : ℝ) : (T^[K]) (x1 • b1 + x2 • b2 + x3 • b3) = (x1 * Real.cos ((K : ℝ) *
    α) - x2 * Real.sin ((K : ℝ) * α)) • b1 + (x1 * Real.sin ((K : ℝ) * α) + x2 * Real.cos ((K :
    ℝ) * α)) • b2 + (ε ^ K * x3) • b3 := by
  induction K generalizing x1 x2 x3 with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply]
    have hstep : T (x1 • b1 + x2 • b2 + x3 • b3) = (x1 * Real.cos α - x2 * Real.sin α) • b1 +
            (x1 * Real.sin α + x2 * Real.cos α) • b2 + (ε * x3) • b3 := by
      have h12 := hlin 1 1 (x1 • b1 + x2 • b2) (x3 • b3); simp only [one_smul] at h12
      rw [h12, hlin x1 x2 b1 b2, show x3 • b3 = x3 • b3 + (0 : ℝ) • b3 by simp,
        hlin x3 0 b3 b3, zero_smul, add_zero, hb1, hb2, hb3]
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hstep, ih]; have hc : Real.cos (((K + 1 : ℕ) : ℝ) * α) =
        Real.cos ((K : ℝ) * α) * Real.cos α - Real.sin ((K : ℝ) * α) * Real.sin α := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.cos_add]
    have hs : Real.sin (((K + 1 : ℕ) : ℝ) * α) =
        Real.sin ((K : ℝ) * α) * Real.cos α + Real.cos ((K : ℝ) * α) * Real.sin α := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.sin_add]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ, hc, hs]; ring
theorem rot3Pos_iter_closed {u : Fin 3 → ℝ} (hu : dot3 u u = 1) (hu1 : 0 ≤ u 1)
    (hs : 0 < √((u 0) ^ 2 + (u 2) ^ 2)) (K : ℕ) (x : Fin 3 → ℝ) :
    let s := √((u 0) ^ 2 + (u 2) ^ 2); let θ := Real.arcsin s; let x1 := x 1
    let x2 := (u 0 * x 0 + u 2 * x 2) / s; let x3 := (u 2 * x 0 - u 0 * x 2) / s
    let y1 := x1 * Real.cos (2 * (K : ℝ) * θ) - x2 * Real.sin (2 * (K : ℝ) * θ)
    let y2 := x1 * Real.sin (2 * (K : ℝ) * θ) + x2 * Real.cos (2 * (K : ℝ) * θ)
    ((rot3Pos u)^[K]) x =
      vec3 (y2 * (u 0 / s) + x3 * (u 2 / s)) y1 (y2 * (u 2 / s) - x3 * (u 0 / s)) := by
  dsimp only; set s := √((u 0) ^ 2 + (u 2) ^ 2); set θ := Real.arcsin s
  let b1 : Fin 3 → ℝ := vec3 0 1 0; let b2 : Fin 3 → ℝ := vec3 (u 0 / s) 0 (u 2 / s)
  let b3 : Fin 3 → ℝ := vec3 (u 2 / s) 0 (- u 0 / s)
  have hs_sq : s ^ 2 = (u 0) ^ 2 + (u 2) ^ 2 := Real.sq_sqrt (by positivity)
  have hu1_sq : (u 1) ^ 2 + s ^ 2 = 1 := (by rw [hs_sq]; unfold dot3 at hu; nlinarith)
  have hs_le1 : s ≤ 1 := by
    have hle : s ^ 2 ≤ 1 ^ 2 := (by nlinarith [sq_nonneg (u 1)])
    simpa [Real.sqrt_sq hs.le] using Real.sqrt_le_sqrt hle
  have hsin : Real.sin θ = s := Real.sin_arcsin (by linarith [hs.le]) hs_le1
  have hcos : Real.cos θ = u 1 := by
    rw [Real.cos_arcsin]; have h1 : 1 - s ^ 2 = (u 1) ^ 2 := (by linarith)
    rw [h1, Real.sqrt_sq hu1]
  have hx_dec : x = x 1 • b1 + ((u 0 * x 0 + u 2 * x 2) / s) • b2 +
      ((u 2 * x 0 - u 0 * x 2) / s) • b3 := by
    refine fin3_ext ?_ ?_ ?_
    · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_zero]
      field_simp [hs.ne']; rw [hs_sq]; ring
    · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_one]; ring
    · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_two]
      field_simp [hs.ne']; rw [hs_sq]; ring
  have hlin : ∀ a b : ℝ, ∀ v w : Fin 3 → ℝ,
      rot3Pos u (a • v + b • w) = a • rot3Pos u v + b • rot3Pos u w := by
    intro a b v w
    refine fin3_ext ?_ ?_ ?_ <;>
      simp only [rot3Pos, refl3, dot3, zOrb3, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        vec3_zero, vec3_one, vec3_two] <;> ring
  have hb1 : rot3Pos u b1 = Real.cos (2 * θ) • b1 + Real.sin (2 * θ) • b2 := by
    have hc2 : Real.cos (2 * θ) = 2 * (u 1) ^ 2 - 1 := (by rw [Real.cos_two_mul, hcos])
    have hs2 : Real.sin (2 * θ) = 2 * s * u 1 := (by rw [Real.sin_two_mul, hsin, hcos])
    refine fin3_ext ?_ ?_ ?_ <;>
      simp only [rot3Pos, refl3, dot3, zOrb3, b1, b2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        vec3_zero, vec3_one, vec3_two, hc2, hs2] <;>
      field_simp [hs.ne'] <;> ring
  have hdot_b2 : dot3 u (zOrb3 b2) = s := by
    simp only [dot3, zOrb3, b2, vec3_zero, vec3_one, vec3_two]
    calc u 0 * (u 0 / s) + u 1 * -0 + u 2 * (u 2 / s)
        = ((u 0) ^ 2 + (u 2) ^ 2) / s := by ring
      _ = s ^ 2 / s := by rw [hs_sq]
      _ = s := by field_simp [hs.ne']
  have hb2 : rot3Pos u b2 = (- Real.sin (2 * θ)) • b1 + Real.cos (2 * θ) • b2 := by
    have hc2 : Real.cos (2 * θ) = 1 - 2 * s ^ 2 := by rw [Real.cos_two_mul, hcos]; linarith [hu1_sq]
    have hs2 : Real.sin (2 * θ) = 2 * s * u 1 := (by rw [Real.sin_two_mul, hsin, hcos])
    unfold rot3Pos refl3; rw [hdot_b2]
    refine fin3_ext ?_ ?_ ?_ <;> simp only [zOrb3, b1, b2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        vec3_zero, vec3_one, vec3_two, hc2, hs2] <;>
      field_simp [hs.ne'] <;> ring
  have hb3 : rot3Pos u b3 = (1 : ℝ) • b3 := by
    refine fin3_ext ?_ ?_ ?_ <;>
      simp only [rot3Pos, refl3, dot3, zOrb3, b3, one_smul, vec3_zero, vec3_one, vec3_two] <;>
      field_simp [hs.ne'] <;> ring
  have hit := iter_lin_2d_3d (rot3Pos u) hlin b1 b2 b3 (2 * θ) 1 hb1 hb2 hb3 K
    (x 1) ((u 0 * x 0 + u 2 * x 2) / s) ((u 2 * x 0 - u 0 * x 2) / s)
  have hmul : (K : ℝ) * (2 * θ) = 2 * (K : ℝ) * θ := (by ring); rw [hmul, one_pow, one_mul] at hit
  conv_lhs => rw [hx_dec]
  rw [hit]; refine fin3_ext ?_ ?_ ?_
  · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_zero]; ring
  · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_one]; ring
  · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_two]; ring
theorem rot3Neg_iter_closed {u : Fin 3 → ℝ} (hu : dot3 u u = 1) (hu1 : u 1 ≤ 0)
    (hs : 0 < √((u 0) ^ 2 + (u 2) ^ 2)) (K : ℕ) (x : Fin 3 → ℝ) :
    let s := √((u 0) ^ 2 + (u 2) ^ 2); let φ := Real.arcsin (- u 1); let x1 := x 1
    let x2 := (u 0 * x 0 + u 2 * x 2) / s; let x3 := (u 2 * x 0 - u 0 * x 2) / s
    let y1 := x1 * Real.cos (2 * (K : ℝ) * φ) - x2 * Real.sin (2 * (K : ℝ) * φ)
    let y2 := x1 * Real.sin (2 * (K : ℝ) * φ) + x2 * Real.cos (2 * (K : ℝ) * φ)
    let y3 := (-1 : ℝ) ^ K * x3
    ((rot3Neg u)^[K]) x =
      vec3 (y2 * (u 0 / s) + y3 * (u 2 / s)) y1 (y2 * (u 2 / s) - y3 * (u 0 / s)) := by
  dsimp only; set s := √((u 0) ^ 2 + (u 2) ^ 2); set φ := Real.arcsin (- u 1)
  let b1 : Fin 3 → ℝ := vec3 0 1 0; let b2 : Fin 3 → ℝ := vec3 (u 0 / s) 0 (u 2 / s)
  let b3 : Fin 3 → ℝ := vec3 (u 2 / s) 0 (- u 0 / s)
  have hs_sq : s ^ 2 = (u 0) ^ 2 + (u 2) ^ 2 := Real.sq_sqrt (by positivity)
  have hu1_sq : (u 1) ^ 2 + s ^ 2 = 1 := (by rw [hs_sq]; unfold dot3 at hu; nlinarith)
  have hu1_le1 : - u 1 ≤ 1 := by
    have hsq : (- u 1) ^ 2 ≤ 1 ^ 2 := (by nlinarith [sq_nonneg s]); nlinarith
  have hsin : Real.sin φ = - u 1 := Real.sin_arcsin (by linarith) hu1_le1
  have hcos : Real.cos φ = s := by
    rw [Real.cos_arcsin]; have h1 : 1 - (- u 1) ^ 2 = s ^ 2 := (by nlinarith [hu1_sq])
    rw [h1, Real.sqrt_sq hs.le]
  have hx_dec : x = x 1 • b1 + ((u 0 * x 0 + u 2 * x 2) / s) • b2 +
      ((u 2 * x 0 - u 0 * x 2) / s) • b3 := by
    refine fin3_ext ?_ ?_ ?_
    · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_zero]
      field_simp [hs.ne']; rw [hs_sq]; ring
    · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_one]; ring
    · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_two]
      field_simp [hs.ne']; rw [hs_sq]; ring
  have hlin : ∀ a b : ℝ, ∀ v w : Fin 3 → ℝ,
      rot3Neg u (a • v + b • w) = a • rot3Neg u v + b • rot3Neg u w := by
    intro a b v w
    refine fin3_ext ?_ ?_ ?_ <;>
      simp only [rot3Neg, refl3, dot3, zOrb3, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, vec3_zero, vec3_one, vec3_two] <;> ring
  have hb1 : rot3Neg u b1 = Real.cos (2 * φ) • b1 + Real.sin (2 * φ) • b2 := by
    have hc2 : Real.cos (2 * φ) = 1 - 2 * (u 1) ^ 2 := by
      rw [Real.cos_two_mul, hcos]; linarith [hu1_sq]
    have hs2 : Real.sin (2 * φ) = - 2 * u 1 * s := (by rw [Real.sin_two_mul, hsin, hcos]; ring)
    refine fin3_ext ?_ ?_ ?_ <;>
      simp only [rot3Neg, refl3, dot3, zOrb3, b1, b2, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, vec3_zero, vec3_one, vec3_two, hc2, hs2] <;>
      field_simp [hs.ne'] <;> ring
  have hdot_b2 : dot3 u (zOrb3 b2) = s := by
    simp only [dot3, zOrb3, b2, vec3_zero, vec3_one, vec3_two]
    calc u 0 * (u 0 / s) + u 1 * -0 + u 2 * (u 2 / s)
        = ((u 0) ^ 2 + (u 2) ^ 2) / s := by ring
      _ = s ^ 2 / s := by rw [hs_sq]
      _ = s := by field_simp [hs.ne']
  have hb2 : rot3Neg u b2 = (- Real.sin (2 * φ)) • b1 + Real.cos (2 * φ) • b2 := by
    have hc2 : Real.cos (2 * φ) = 2 * s ^ 2 - 1 := (by rw [Real.cos_two_mul, hcos])
    have hs2 : Real.sin (2 * φ) = - 2 * u 1 * s := (by rw [Real.sin_two_mul, hsin, hcos]; ring)
    unfold rot3Neg refl3; rw [hdot_b2]
    refine fin3_ext ?_ ?_ ?_ <;>
      simp only [zOrb3, b1, b2, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, vec3_zero, vec3_one, vec3_two, hc2, hs2] <;>
      field_simp [hs.ne'] <;> ring
  have hb3 : rot3Neg u b3 = (-1 : ℝ) • b3 := by
    refine fin3_ext ?_ ?_ ?_ <;>
      simp only [rot3Neg, refl3, dot3, zOrb3, b3, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
        vec3_zero, vec3_one, vec3_two] <;>
      field_simp [hs.ne'] <;> ring
  have hit := iter_lin_2d_3d (rot3Neg u) hlin b1 b2 b3 (2 * φ) (-1) hb1 hb2 hb3 K
    (x 1) ((u 0 * x 0 + u 2 * x 2) / s) ((u 2 * x 0 - u 0 * x 2) / s)
  have hmul : (K : ℝ) * (2 * φ) = 2 * (K : ℝ) * φ := (by ring); rw [hmul] at hit
  conv_lhs => rw [hx_dec]
  rw [hit]; refine fin3_ext ?_ ?_ ?_
  · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_zero]; ring
  · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_one]; ring
  · simp only [b1, b2, b3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vec3_two]; ring
end Sec_P01Orb
section Sec_P01Rot
open Real
open scoped Matrix
/-! ## Section 1: `10 ^ 12` Even Step Counts & `π / 4` Certificate Bridges -/
/-- Even walk-step count `2 * ((tau_12 * Nat.sqrt N) / (2 * 10 ^ 12))`. -/
def p01StepCount (tau_12 N : ℕ) : ℕ := 2 * ((tau_12 * Nat.sqrt N) / 2000000000000)
@[simp] theorem p01StepCount_zero_left (N : ℕ) : p01StepCount 0 N = 0 := by simp [p01StepCount]
theorem p01StepCount_even (tau_12 N : ℕ) : (-1 : ℝ) ^ p01StepCount tau_12 N = 1 := by
  unfold p01StepCount; rw [pow_mul, neg_one_sq, one_pow]
theorem p01StepCount_mul_le (tau_12 N : ℕ) :
    p01StepCount tau_12 N * 1000000000000 ≤ tau_12 * Nat.sqrt N := by
  unfold p01StepCount; have h := Nat.mul_div_le (tau_12 * Nat.sqrt N) 2000000000000; omega
theorem p01StepCount_le_tau_sqrt (tau_12 N : ℕ) :
    (p01StepCount tau_12 N : ℝ) ≤ ((tau_12 : ℝ) / 1000000000000) * √(N : ℝ) := by
  have hm := p01StepCount_mul_le tau_12 N
  have hmR : (p01StepCount tau_12 N : ℝ) * 1000000000000 ≤ (tau_12 : ℝ) * (Nat.sqrt N : ℝ) := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hm; simpa [Nat.cast_mul] using hc
  have hsq : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_; have hn := (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le N)
    simpa [sq, Nat.cast_mul] using hn
  have hmul : (tau_12 : ℝ) * (Nat.sqrt N : ℝ) ≤ (tau_12 : ℝ) * √(N : ℝ) :=
    mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg tau_12)
  linarith [hmR.trans hmul]
theorem p01StepCount_div_sqrt_mem {n tau_12 : ℕ} (hn : 200 ≤ n) (htau : tau_12 ≤ 4000000000000) :
    wdMem ((p01StepCount tau_12 (2 ^ n) : ℝ) / √((2 ^ n : ℕ) : ℝ))
      (max 0 ((tau_12 : ℤ) * 1000 - 1), (tau_12 : ℤ) * 1000 + 1) := by
  set N : ℕ := 2 ^ n
  have hN_ge : ((2 : ℝ) ^ 200) ≤ (N : ℝ) := by
    dsimp only [N]; rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) hn
  have hsqrtN_ge : ((2 : ℝ) ^ 100) ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hN_ge)
  have hsqrtN_pos : (0 : ℝ) < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsqrtN_ge
  have hB : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num); unfold wdMem
  dsimp only; constructor
  · have hnn : 0 ≤ (p01StepCount tau_12 N : ℝ) / √(N : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hsqrtN_pos.le
    rcases le_total 0 ((tau_12 : ℤ) * 1000 - 1) with hmax | hmax
    · rw [max_eq_right hmax, hB]; set S := Nat.sqrt N
      have hS_gt : √(N : ℝ) ≤ (S : ℝ) + 1 := by
        rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
        have hlt := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N); push_cast at hlt; linarith
      have hdiv_lt : tau_12 * S < (p01StepCount tau_12 N + 2) * 1000000000000 := by
        dsimp only [S]; unfold p01StepCount
        have h := Nat.lt_mul_div_succ (tau_12 * Nat.sqrt N) (by omega : 0 < 2000000000000); omega
      have hdivR : (tau_12 : ℝ) * (S : ℝ) ≤
          ((p01StepCount tau_12 N : ℝ) + 2) * 1000000000000 := by
        have hc := (Nat.cast_le (α := ℝ)).mpr hdiv_lt.le; push_cast at hc; linarith
      have htauR : (tau_12 : ℝ) ≤ 4000000000000 := (by exact_mod_cast htau)
      have hgap : (tau_12 : ℝ) * √(N : ℝ) - (p01StepCount tau_12 N : ℝ) * 1000000000000 ≤
          6000000000000 := by
        nlinarith [mul_le_mul_of_nonneg_left hS_gt (Nat.cast_nonneg tau_12)]
      have h6_le : (6000000000000000 : ℝ) ≤ √(N : ℝ) :=
        (by norm_num : (6000000000000000 : ℝ) ≤ (2 : ℝ) ^ 100).trans hsqrtN_ge
      rw [div_le_div_iff₀ (by norm_num) hsqrtN_pos]; push_cast; linarith
    · rw [max_eq_left hmax, Int.cast_zero, zero_div]; exact hnn
  · rw [hB]; have hle := p01StepCount_le_tau_sqrt tau_12 N
    have hdiv : (p01StepCount tau_12 N : ℝ) / √(N : ℝ) ≤ (tau_12 : ℝ) / 1000000000000 := by
      rwa [div_le_iff₀ hsqrtN_pos]
    refine hdiv.trans ?_; push_cast; linarith
/-- Certified `10 ^ 15`-scaled lower bound on `π / 4`. -/
theorem pi4_gt_p01 : (785398163397448 : ℝ) / wdScaleR < π / 4 := by
  unfold wdScaleR wdScale; linarith [Real.pi_gt_d20]
/-- Certified `10 ^ 15`-scaled upper bound on `π / 4`. -/
theorem pi4_lt_p01 : π / 4 < (785398163397449 : ℝ) / wdScaleR := by
  unfold wdScaleR wdScale; linarith [Real.pi_lt_d20]
theorem p01Isqrt15_pos {val : ℕ} (hv : 1 ≤ val) :
    0 < (p01Isqrt15 val).1 ∧ (p01Isqrt15 val).1 ≤ (p01Isqrt15 val).2 := by
  unfold p01Isqrt15; dsimp only
  have ht : 1 ≤ val * (wdScale * wdScale) := (by unfold wdScale; omega)
  have hrt : 1 ≤ Nat.sqrt (val * (wdScale * wdScale)) := Nat.le_sqrt.mpr (by omega); constructor
  · exact_mod_cast (by omega : 0 < Nat.sqrt (val * (wdScale * wdScale)))
  · split_ifs <;> omega
/-! ## Section 2: Interval Division / Padding Helpers & `arcsin` Enclosure -/
private lemma p01_arcsin_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    s ≤ Real.arcsin s ∧ Real.arcsin s ≤ s + s ^ 2 := by
  refine ⟨self_le_arcsin hs0 (hs1.trans (by norm_num)), ?_⟩; rcases hs0.eq_or_lt with rfl | hpos
  · simp
  have h3 : s * (1 + s) ^ 3 ≤ 2 := by
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ 1 + s) (by linarith : 1 + s ≤ 3 / 2) 3]
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
    ⟨by nlinarith [Real.pi_gt_three], by nlinarith [Real.pi_gt_three]⟩]
  nlinarith [Real.sin_gt_sub_cube (by positivity : 0 < s + s ^ 2),
    mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]
private lemma wdMem_pad_nonneg {x y : ℝ} {iv : WDIVal} {pad : ℤ}
    (hx0 : 0 ≤ x) (hy : wdMem y iv) (hd : |x - y| ≤ (pad : ℝ) / wdScaleR) :
    wdMem x (max 0 (iv.1 - pad), iv.2 + pad) := by
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd; unfold wdMem at hy ⊢; dsimp only; constructor
  · rcases le_total 0 (iv.1 - pad) with hm | hm
    · rw [max_eq_right hm]; push_cast; rw [sub_div]; linarith [hy.1]
    · rw [max_eq_left hm, Int.cast_zero, zero_div]; exact hx0
  · push_cast; rw [add_div]; linarith [hy.2]
private lemma wdMem_pad {x y : ℝ} {iv : WDIVal} {pad : ℤ}
    (hy : wdMem y iv) (hd : |x - y| ≤ (pad : ℝ) / wdScaleR) :
    wdMem x (iv.1 - pad, iv.2 + pad) := by
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd; unfold wdMem at hy ⊢; dsimp only; constructor
  · push_cast; rw [sub_div]; linarith [hy.1]
  · push_cast; rw [add_div]; linarith [hy.2]
private lemma wdMem_div_pos {x y : ℝ} {ix iy : WDIVal} (hy_pos : 0 < y) (hix0 : 0 ≤ ix.1) (hiy1 :
    0 < iy.1) (hiy_le : iy.1 ≤ iy.2) (hx : wdMem x ix) (hy : wdMem y iy) : wdMem (x / y)
    (wdDivFloor (ix.1 * (wdScale : ℤ)) iy.2, wdDivCeil (ix.2 * (wdScale : ℤ)) iy.1) := by
  have hB : 0 < wdScaleR := (by unfold wdScaleR wdScale; norm_num)
  have hiy2 : 0 < iy.2 := hiy1.trans_le hiy_le
  have hiy1R : (0 : ℝ) < (iy.1 : ℝ) := (by exact_mod_cast hiy1)
  have hiy2R : (0 : ℝ) < (iy.2 : ℝ) := (by exact_mod_cast hiy2)
  have hix0R : (0 : ℝ) ≤ (ix.1 : ℝ) := (by exact_mod_cast hix0); unfold wdMem; dsimp only
  constructor
  · have hfl := wdDivFloor_le (a := ix.1 * (wdScale : ℤ)) hiy2; push_cast at hfl
    have hfl_div : (wdDivFloor (ix.1 * (wdScale : ℤ)) iy.2 : ℝ) / wdScaleR ≤
        (ix.1 : ℝ) / (iy.2 : ℝ) := by
      have h1 := div_le_div_of_nonneg_right hfl hB.le; unfold wdScaleR at h1 ⊢
      rwa [mul_div_right_comm, mul_div_cancel_right₀ _ hB.ne'] at h1
    refine hfl_div.trans ?_
    have heq : (ix.1 : ℝ) / (iy.2 : ℝ) = ((ix.1 : ℝ) / wdScaleR) / ((iy.2 : ℝ) / wdScaleR) := by
      rw [div_div_div_cancel_right₀ hB.ne']
    rw [heq]; exact div_le_div₀ (div_nonneg hix0R hB.le |>.trans hx.1) hx.1 hy_pos hy.2
  · have hcl := le_wdDivCeil (a := ix.2 * (wdScale : ℤ)) hiy1; push_cast at hcl
    have hcl_div : (ix.2 : ℝ) / (iy.1 : ℝ) ≤
        (wdDivCeil (ix.2 * (wdScale : ℤ)) iy.1 : ℝ) / wdScaleR := by
      have h1 := div_le_div_of_nonneg_right hcl hB.le; unfold wdScaleR at h1 ⊢
      rwa [mul_div_right_comm, mul_div_cancel_right₀ _ hB.ne'] at h1
    refine le_trans ?_ hcl_div
    have heq : (ix.2 : ℝ) / (iy.1 : ℝ) = ((ix.2 : ℝ) / wdScaleR) / ((iy.1 : ℝ) / wdScaleR) := by
      rw [div_div_div_cancel_right₀ hB.ne']
    rw [heq]
    have hx2_nn : 0 ≤ (ix.2 : ℝ) / wdScaleR := (div_nonneg hix0R hB.le).trans (hx.1.trans hx.2)
    exact div_le_div₀ hx2_nn hx.2 (div_pos hiy1R hB) hy.1
private lemma wdMem_div_nat {x : ℝ} {ix : WDIVal} {d : ℕ} (hd : 0 < d) (hx : wdMem x ix) :
    wdMem (x / (d : ℝ)) (wdDivFloor ix.1 (d : ℤ), wdDivCeil ix.2 (d : ℤ)) := by
  have hB : 0 < wdScaleR := (by unfold wdScaleR wdScale; norm_num)
  have hdZ : (0 : ℤ) < (d : ℤ) := (by exact_mod_cast hd)
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd; unfold wdMem; dsimp only; constructor
  · have hfl := div_le_div_of_nonneg_right (wdDivFloor_le (a := ix.1) hdZ) hB.le; push_cast at hfl
    rw [div_right_comm] at hfl; exact hfl.trans (div_le_div_of_nonneg_right hx.1 hdR.le)
  · have hcl := div_le_div_of_nonneg_right (le_wdDivCeil (a := ix.2) hdZ) hB.le; push_cast at hcl
    rw [div_right_comm] at hcl; exact (div_le_div_of_nonneg_right hx.2 hdR.le).trans hcl
private lemma wdMem_aff_div_nat {c : ℝ} {ic : WDIVal} {a2 b2 ab2 : ℕ} (hab : 0 < ab2) (hc : wdMem
    c ic) : wdMem (((b2 : ℝ) + (a2 : ℝ) * c) / (ab2 : ℝ)) (wdDivFloor ((b2 : ℤ) * (wdScale : ℤ) +
    (a2 : ℤ) * ic.1) (ab2 : ℤ), wdDivCeil ((b2 : ℤ) * (wdScale : ℤ) + (a2 : ℤ) * ic.2) (ab2 :
    ℤ)) := by
  have hmem : wdMem ((b2 : ℝ) + (a2 : ℝ) * c) ((b2 : ℤ) * (wdScale : ℤ) + (a2 : ℤ) * ic.1,
        (b2 : ℤ) * (wdScale : ℤ) + (a2 : ℤ) * ic.2) := by
    have hb : wdMem ((b2 : ℝ) * 1) (wdScaleNat b2 ((wdScale : ℤ), (wdScale : ℤ))) :=
      wdMem_scaleNat b2 wdMem_one
    rw [mul_one] at hb; exact wdMem_add hb (wdMem_scaleNat a2 hc)
  exact wdMem_div_nat hab hmem
/-! ## Section 3: Finite-`N` Basis Perturbation Bounds (`200 ≤ n`) -/
private lemma sq_sub_one_bounds {x ε : ℝ} (hx : 0 ≤ x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (hlo : 1 -
    ε ≤ x ^ 2) (hhi : x ^ 2 ≤ 1 + ε) : 1 - ε ≤ x ∧ x ≤ 1 + ε := by
  constructor
  · have h1 : (1 - ε) ^ 2 ≤ x ^ 2 := (by nlinarith); nlinarith
  · have h2 : x ^ 2 ≤ (1 + ε) ^ 2 := (by nlinarith); nlinarith
private lemma ratio_near_one {A B ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 8)
    (hAlo : 1 - ε ≤ A) (hAhi : A ≤ 1 + ε) (hBlo : 1 - ε ≤ B) (hBhi : B ≤ 1 + ε) :
    1 - 4 * ε ≤ A / B ∧ A / B ≤ 1 + 4 * ε := by
  have hB_pos : 0 < B := (by linarith)
  exact ⟨(le_div_iff₀ hB_pos).mpr (by nlinarith), (div_le_iff₀ hB_pos).mpr (by nlinarith)⟩
private lemma abs_sub_of_div_near_one {x t ε : ℝ} (hx : 0 ≤ x) (ht : 0 < t)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (hlo : 1 - ε ≤ (x / t) ^ 2) (hhi : (x / t) ^ 2 ≤ 1 + ε) :
    |x - t| ≤ ε * t := by
  obtain ⟨h1, h2⟩ := sq_sub_one_bounds (div_nonneg hx ht.le) hε0 hε1 hlo hhi
  have h1' : (1 - ε) * t ≤ x := (le_div_iff₀ ht).mp h1
  have h2' : x ≤ (1 + ε) * t := (div_le_iff₀ ht).mp h2; exact abs_le.mpr ⟨by linarith, by linarith⟩
private lemma p01_u0_bounds {N a2 b2 D1 D2 u0_0 u0_1 u0_2 δ : ℝ}
    (hN_pos : 0 < N) (hsqrtN_pos : 0 < √N) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 8)
    (hsqrt_δ : 1024 / √N ≤ δ) (hN_δ : 100000000 / N ≤ δ) (ha2_pos : 0 < a2) (ha2_hi : a2 ≤ 2048)
    (hb2_pos : 0 < b2) (hb2_hi : b2 ≤ 2046) (hD1_lo : N / 2 ≤ D1) (hD2_lo : N / 2 ≤ D2)
    (hu0_0_pos : 0 < u0_0) (hu0_1_pos : 0 < u0_1) (hu0_2_pos : 0 < u0_2)
    (hc_sum : u0_0 ^ 2 + u0_1 ^ 2 + u0_2 ^ 2 = 1) (hrel1 : u0_0 ^ 2 * a2 = u0_1 ^ 2 * D1)
    (hrel2 : u0_1 ^ 2 * b2 = 4 * u0_2 ^ 2 * D2) : (|u0_0 - 1| ≤ δ ∧ |u0_1| ≤ δ ∧ |u0_2| ≤ δ) ∧
      u0_2 ≤ 64 / √N ∧ 1 - 8192 / N ≤ u0_0 ^ 2 ∧ u0_0 ^ 2 ≤ 1 ∧
      4 * D1 * D2 * u0_2 ^ 2 = u0_0 ^ 2 * a2 * b2 := by
  have hc0_nn : 0 ≤ u0_0 ^ 2 := sq_nonneg u0_0; have hc1_nn : 0 ≤ u0_1 ^ 2 := sq_nonneg u0_1
  have hc2_nn : 0 ≤ u0_2 ^ 2 := sq_nonneg u0_2; have hc0_le1 : u0_0 ^ 2 ≤ 1 := (by linarith)
  have hc1_le1 : u0_1 ^ 2 ≤ 1 := (by linarith)
  have hrel02 : 4 * D1 * D2 * u0_2 ^ 2 = u0_0 ^ 2 * a2 * b2 := by
    calc 4 * D1 * D2 * u0_2 ^ 2 = D1 * (4 * u0_2 ^ 2 * D2) := by ring
      _ = D1 * (u0_1 ^ 2 * b2) := by rw [← hrel2]
      _ = (u0_1 ^ 2 * D1) * b2 := by ring
      _ = u0_0 ^ 2 * a2 * b2 := by rw [← hrel1]
  have hc1_hi : u0_1 ^ 2 ≤ 4096 / N := by
    rw [le_div_iff₀ hN_pos]
    have h1 : u0_1 ^ 2 * (N / 2) ≤ u0_1 ^ 2 * D1 := mul_le_mul_of_nonneg_left hD1_lo hc1_nn
    have h1' : (u0_1 ^ 2 * N) / 2 = u0_1 ^ 2 * (N / 2) := (by ring)
    have h2 : u0_0 ^ 2 * a2 ≤ 1 * 2048 := mul_le_mul hc0_le1 ha2_hi ha2_pos.le zero_le_one; linarith
  have hc2_hi : u0_2 ^ 2 ≤ 4096 / N := by
    rw [le_div_iff₀ hN_pos]
    have h1 : (4 * u0_2 ^ 2) * (N / 2) ≤ (4 * u0_2 ^ 2) * D2 :=
      mul_le_mul_of_nonneg_left hD2_lo (by positivity)
    have h1' : 2 * (u0_2 ^ 2 * N) = (4 * u0_2 ^ 2) * (N / 2) := (by ring)
    have h2 : u0_1 ^ 2 * b2 ≤ 1 * 2046 := mul_le_mul hc1_le1 hb2_hi hb2_pos.le zero_le_one; linarith
  have hc0_lo : 1 - 8192 / N ≤ u0_0 ^ 2 := by
    linarith [show (4096 : ℝ) / N + 4096 / N = 8192 / N by ring]
  have hu0_0_bd : |u0_0 - 1| ≤ δ := by
    have h8 : 8192 / N ≤ δ :=
      (div_le_div_of_nonneg_right (by norm_num : (8192 : ℝ) ≤ 100000000) hN_pos.le).trans hN_δ
    have h1 := abs_sub_of_div_near_one hu0_0_pos.le zero_lt_one hδ_pos.le (by linarith)
      (by rw [div_one]; linarith) (by rw [div_one]; linarith)
    simpa only [mul_one] using h1
  have hu0_1_bd : |u0_1| ≤ δ := by
    have h64 : u0_1 ≤ 64 / √N := by
      have hsq : u0_1 ^ 2 ≤ (64 / √N) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hN_pos.le]; norm_num; exact hc1_hi
      have hrt := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hu0_1_pos.le, Real.sqrt_sq (by positivity)] at hrt
    rw [abs_of_pos hu0_1_pos]
    exact h64.trans ((div_le_div_of_nonneg_right (by norm_num) hsqrtN_pos.le).trans hsqrt_δ)
  have hu0_2_64 : u0_2 ≤ 64 / √N := by
    have hsq : u0_2 ^ 2 ≤ (64 / √N) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hN_pos.le]; norm_num; exact hc2_hi
    have hrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hu0_2_pos.le, Real.sqrt_sq (by positivity)] at hrt
  have hu0_2_bd : |u0_2| ≤ δ := by
    rw [abs_of_pos hu0_2_pos]
    exact hu0_2_64.trans ((div_le_div_of_nonneg_right (by norm_num) hsqrtN_pos.le).trans hsqrt_δ)
  exact ⟨⟨hu0_0_bd, hu0_1_bd, hu0_2_bd⟩, hu0_2_64, hc0_lo, hc0_le1, hrel02⟩
private lemma p01_Q_R2_R3_bounds {N m r a2 D1 D2 c0 : ℝ} (hN_big : 100000000 ≤ N) (hm_lo : 2 ≤ m)
    (hm_hi : m ≤ 1024) (hr_lo : 2 ≤ r) (hr_hi : r ≤ 1024) (ha2_pos : 0 < a2) (ha2_hi : a2 ≤ 2048)
    (hD1_def : D1 = N - r - m + 1) (hD2_def : D2 = N - r - m + 2) (hc0_nn : 0 ≤ c0) (hc0_lo : 1 -
    8192 / N ≤ c0) (hc0_le1 : c0 ≤ 1) :
    let Q := (N * (N - 1)) / ((N - m) * (N - r)); let R2 := (2 * N - a2) ^ 2 / (4 * D1 * D2)
    let R3 := N ^ 2 / (D1 * D2); let ε1 := 32768 / N
    (1 - ε1 ≤ c0 * Q ∧ c0 * Q ≤ 1 + ε1) ∧ (1 - ε1 ≤ c0 * Q * R2 ∧ c0 * Q * R2 ≤ 1 + ε1) ∧
      (1 - ε1 ≤ c0 ^ 2 * Q * R3 ∧ c0 ^ 2 * Q * R3 ≤ 1 + ε1) := by
  dsimp only; have hN_pos : 0 < N := (by linarith); have hm_pos : 0 < m := (by linarith)
  have hr_pos : 0 < r := (by linarith); have hNm_pos : 0 < N - m := (by linarith)
  have hNr_pos : 0 < N - r := (by linarith); have hD1_lo : N / 2 ≤ D1 := (by linarith)
  have hD2_lo : N / 2 ≤ D2 := (by linarith); have hD1_pos : 0 < D1 := (by linarith)
  have hD2_pos : 0 < D2 := (by linarith); set Q : ℝ := (N * (N - 1)) / ((N - m) * (N - r))
  set R2 : ℝ := (2 * N - a2) ^ 2 / (4 * D1 * D2); set R3 : ℝ := N ^ 2 / (D1 * D2)
  set ε1 : ℝ := 32768 / N
  have hQ_lo : 1 ≤ Q := by
    dsimp only [Q]; rw [le_div_iff₀ (by positivity)]
    have hmr_hi : m * r ≤ 1048576 :=
      (mul_le_mul hm_hi hr_hi hr_pos.le (by norm_num)).trans (by norm_num)
    have h3N : 3 * N ≤ (m + r - 1) * N := mul_le_mul_of_nonneg_right (by linarith) hN_pos.le
    have hexp : N * (N - 1) - 1 * ((N - m) * (N - r)) = (m + r - 1) * N - m * r := (by ring)
    linarith
  have hQ_pos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ_lo
  have hQ_hi : Q ≤ 1 + 4096 / N := by
    dsimp only [Q]; have h34m : (3 / 4) * N ≤ N - m := (by linarith)
    have h34r : (3 / 4) * N ≤ N - r := (by linarith)
    have hden1 : ((3 / 4) * N) * ((3 / 4) * N) ≤ (N - m) * (N - r) :=
      mul_le_mul h34m h34r (by positivity) hNm_pos.le
    have hden_ge : N ^ 2 / 2 ≤ (N - m) * (N - r) := by
      linarith [sq_nonneg N, show ((3 / 4) * N) * ((3 / 4) * N) = (9 / 16) * N ^ 2 by ring]
    rw [div_le_iff₀ (by positivity), one_add_mul]
    have h1 : 2048 * N ≤ (4096 / N) * ((N - m) * (N - r)) := by
      have hmul := mul_le_mul_of_nonneg_left hden_ge (by positivity : (0 : ℝ) ≤ 4096 / N)
      have hsimp : (4096 / N) * (N ^ 2 / 2) = 2048 * N := by
        rw [div_mul_div_comm, div_eq_iff (by positivity)]; ring
      linarith
    have hmr_nn : 0 ≤ m * r := mul_nonneg hm_pos.le hr_pos.le
    have hmr_sum : (m + r) * N ≤ 2048 * N := mul_le_mul_of_nonneg_right (by linarith) hN_pos.le
    have hexp : (N - m) * (N - r) = N ^ 2 - (m + r) * N + m * r := (by ring)
    have hexpL : N * (N - 1) = N ^ 2 - N := (by ring); linarith
  have hc0Q_lo8 : 1 - 8192 / N ≤ c0 * Q := by
    calc 1 - 8192 / N = (1 - 8192 / N) * 1 := (mul_one _).symm
      _ ≤ c0 * Q := mul_le_mul hc0_lo hQ_lo zero_le_one hc0_nn
  have hc0Q_lo : 1 - ε1 ≤ c0 * Q := by
    dsimp only [ε1]
    linarith [div_le_div_of_nonneg_right (by norm_num : (8192 : ℝ) ≤ 32768) hN_pos.le]
  have hc0Q_hi1 : c0 * Q ≤ 1 + 4096 / N :=
    (mul_le_mul_of_nonneg_right hc0_le1 hQ_pos.le).trans (by rw [one_mul]; exact hQ_hi)
  have hc0Q_hi : c0 * Q ≤ 1 + ε1 := by
    dsimp only [ε1]
    linarith [div_le_div_of_nonneg_right (by norm_num : (4096 : ℝ) ≤ 32768) hN_pos.le]
  have hDD_ge : N ^ 2 / 4 ≤ D1 * D2 := by
    have hm := mul_le_mul hD1_lo hD2_lo (by positivity) hD1_pos.le
    linarith [show (N / 2) * (N / 2) = N ^ 2 / 4 by ring]
  have h4D_ge : N ^ 2 ≤ 4 * D1 * D2 := (by linarith [show 4 * (D1 * D2) = 4 * D1 * D2 by ring])
  have hD1_le : D1 ≤ N := (by linarith); have hD2_le : D2 ≤ N := (by linarith)
  have hDD_le : D1 * D2 ≤ N ^ 2 := (by rw [sq]; exact mul_le_mul hD1_le hD2_le hD2_pos.le hN_pos.le)
  have hD1_lo2 : N - 2048 ≤ D1 := (by linarith); have hD2_lo2 : N - 2048 ≤ D2 := (by linarith)
  have hDD_lo2 : (N - 2048) ^ 2 ≤ D1 * D2 := by
    rw [sq]; exact mul_le_mul hD1_lo2 hD2_lo2 (by linarith) hD1_pos.le
  have hR2_lo : 1 - 8192 / N ≤ R2 := by
    dsimp only [R2]; rw [le_div_iff₀ (by positivity), sub_mul, one_mul]
    have hsub : 8192 * N ≤ (8192 / N) * (4 * D1 * D2) := by
      have hm := mul_le_mul_of_nonneg_left h4D_ge (by positivity : (0 : ℝ) ≤ 8192 / N)
      have hs : (8192 / N) * N ^ 2 = 8192 * N := by
        rw [div_mul_eq_mul_div, div_eq_iff hN_pos.ne']; ring
      linarith
    have h4D_hi : 4 * D1 * D2 ≤ 4 * N ^ 2 := by linarith [show 4 * (D1 * D2) = 4 * D1 * D2 by ring]
    have ha2N : a2 * N ≤ 2048 * N := mul_le_mul_of_nonneg_right ha2_hi hN_pos.le
    have hexp : (2 * N - a2) ^ 2 = 4 * N ^ 2 - 4 * (a2 * N) + a2 ^ 2 := (by ring)
    linarith [sq_nonneg a2]
  have hR2_pos : 0 < R2 := by
    have : 8192 / N ≤ 1 / 2 := (div_le_iff₀ hN_pos).mpr (by linarith); linarith
  have hR2_hi : R2 ≤ 1 + 16384 / N := by
    dsimp only [R2]; rw [div_le_iff₀ (by positivity), one_add_mul]
    have hadd : 16384 * N ≤ (16384 / N) * (4 * D1 * D2) := by
      have hm := mul_le_mul_of_nonneg_left h4D_ge (by positivity : (0 : ℝ) ≤ 16384 / N)
      have hs : (16384 / N) * N ^ 2 = 16384 * N := by
        rw [div_mul_eq_mul_div, div_eq_iff hN_pos.ne']; ring
      linarith
    have h4D_lo2 : 4 * (N - 2048) ^ 2 ≤ 4 * D1 * D2 := by
      linarith [show 4 * (D1 * D2) = 4 * D1 * D2 by ring]
    have ha2_sq : a2 ^ 2 ≤ 2048 ^ 2 := pow_le_pow_left₀ ha2_pos.le ha2_hi 2
    have ha2N_nn : 0 ≤ a2 * N := mul_nonneg ha2_pos.le hN_pos.le
    have hexp : 4 * (N - 2048) ^ 2 + 16384 * N - (2 * N - a2) ^ 2 =
        (4 * 2048 ^ 2 - a2 ^ 2) + 4 * (a2 * N) := by ring
    linarith
  have hprod_err : (4096 / N) * (16384 / N) ≤ 12288 / N := by
    rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hN_pos hN_pos) hN_pos]
    linarith [mul_le_mul_of_nonneg_right hN_big hN_pos.le]
  have hc0QR2_lo : 1 - ε1 ≤ c0 * Q * R2 := by
    have h1 : 0 ≤ 1 - 8192 / N := (by rw [sub_nonneg, div_le_iff₀ hN_pos]; linarith)
    have h2 : (1 - 8192 / N) * (1 - 8192 / N) ≤ c0 * Q * R2 :=
      mul_le_mul hc0Q_lo8 hR2_lo h1 (mul_nonneg hc0_nn hQ_pos.le)
    have hexp : (1 - 8192 / N) * (1 - 8192 / N) = 1 - 16384 / N + (8192 / N) ^ 2 := (by ring)
    have hlin := div_le_div_of_nonneg_right (by norm_num : (16384 : ℝ) ≤ 32768) hN_pos.le
    dsimp only [ε1]; linarith [sq_nonneg (8192 / N)]
  have hc0QR2_hi : c0 * Q * R2 ≤ 1 + ε1 := by
    have h2 : c0 * Q * R2 ≤ (1 + 4096 / N) * (1 + 16384 / N) :=
      mul_le_mul hc0Q_hi1 hR2_hi hR2_pos.le (by positivity)
    have hexp : (1 + 4096 / N) * (1 + 16384 / N) =
        1 + 20480 / N + (4096 / N) * (16384 / N) := by ring
    have hsum : 20480 / N + 12288 / N = ε1 := (by dsimp only [ε1]; ring); linarith
  have hR3_lo : 1 ≤ R3 := (by dsimp only [R3]; rw [le_div_iff₀ (by positivity)]; linarith)
  have hR3_pos : 0 < R3 := lt_of_lt_of_le zero_lt_one hR3_lo
  have hR3_hi : R3 ≤ 1 + 16384 / N := by
    dsimp only [R3]; rw [div_le_iff₀ (by positivity), one_add_mul]
    have hm := mul_le_mul_of_nonneg_left hDD_ge (by positivity : (0 : ℝ) ≤ 16384 / N)
    have hs : (16384 / N) * (N ^ 2 / 4) = 4096 * N := by
      rw [div_mul_div_comm, div_eq_iff (by positivity)]; ring
    have hexp : (N - 2048) ^ 2 + 4096 * N - N ^ 2 = 2048 ^ 2 := (by ring); linarith
  have hc02QR3_lo : 1 - ε1 ≤ c0 ^ 2 * Q * R3 := by
    have h1 : 0 ≤ 1 - 8192 / N := (by rw [sub_nonneg, div_le_iff₀ hN_pos]; linarith)
    have hc02 : (1 - 8192 / N) ^ 2 ≤ c0 ^ 2 := pow_le_pow_left₀ h1 hc0_lo 2
    have hQR3_lo : 1 ≤ Q * R3 := by
      calc (1 : ℝ) = 1 * 1 := (mul_one _).symm
        _ ≤ Q * R3 := mul_le_mul hQ_lo hR3_lo zero_le_one hQ_pos.le
    have hprod : (1 - 8192 / N) ^ 2 * 1 ≤ c0 ^ 2 * (Q * R3) :=
      mul_le_mul hc02 hQR3_lo zero_le_one (sq_nonneg c0)
    have hexp : (1 - 8192 / N) ^ 2 * 1 = 1 - 16384 / N + (8192 / N) ^ 2 := (by ring)
    have hassoc : c0 ^ 2 * Q * R3 = c0 ^ 2 * (Q * R3) := (by ring)
    have hlin := div_le_div_of_nonneg_right (by norm_num : (16384 : ℝ) ≤ 32768) hN_pos.le
    dsimp only [ε1]; linarith [sq_nonneg (8192 / N)]
  have hc02QR3_hi : c0 ^ 2 * Q * R3 ≤ 1 + ε1 := by
    have hc02 : c0 ^ 2 ≤ 1 := by
      calc c0 ^ 2 = c0 * c0 := sq c0
        _ ≤ 1 * 1 := mul_le_mul hc0_le1 hc0_le1 hc0_nn zero_le_one
        _ = 1 := one_mul 1
    have hQR3 : Q * R3 ≤ (1 + 4096 / N) * (1 + 16384 / N) :=
      mul_le_mul hQ_hi hR3_hi hR3_pos.le (by positivity)
    have hprod : c0 ^ 2 * (Q * R3) ≤ 1 * ((1 + 4096 / N) * (1 + 16384 / N)) :=
      mul_le_mul hc02 hQR3 (mul_nonneg hQ_pos.le hR3_pos.le) zero_le_one
    have hexp : 1 * ((1 + 4096 / N) * (1 + 16384 / N)) =
        1 + 20480 / N + (4096 / N) * (16384 / N) := by ring
    have hsum : 20480 / N + 12288 / N = ε1 := (by dsimp only [ε1]; ring)
    have hassoc : c0 ^ 2 * Q * R3 = c0 ^ 2 * (Q * R3) := (by ring); linarith
  exact ⟨⟨hc0Q_lo, hc0Q_hi⟩, ⟨hc0QR2_lo, hc0QR2_hi⟩, ⟨hc02QR3_lo, hc02QR3_hi⟩⟩
private lemma p01_s1_s2_bounds {N a2 b2 ab2 c0 Q R2 R3 ε1 δ u0_0 u0_2 u1_0 u1_2 u2_0 u2_1 u2_2 : ℝ}
    (hN_pos : 0 < N) (hsqrtN_pos : 0 < √N)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 8) (hsqrt_δ : 1024 / √N ≤ δ)
    (hε1_pos : 0 < ε1) (hε1_δ : 64 * ε1 ≤ δ)
    (ha2_pos : 0 < a2) (hb2_pos : 0 < b2) (hb2_hi : b2 ≤ 2046)
    (hab2_eq : ab2 = a2 + b2) (hab2_hi : ab2 ≤ 4094) (hu0_0_bd : |u0_0 - 1| ≤ δ)
    (hu0_2_pos : 0 < u0_2) (hu0_2_64 : u0_2 ≤ 64 / √N) (hu1_0_neg : u1_0 < 0) (hu1_2_pos : 0 < u1_2)
    (hu1_0_sq : N * u1_0 ^ 2 = a2 * (c0 * Q)) (hu1_2_sq : N * u1_2 ^ 2 = b2 * (c0 * Q * R2))
    (hu2_0_pos : 0 < u2_0) (hu2_1_neg : u2_1 < 0) (hu2_2_pos : 0 < u2_2)
    (hu2_1_sq : N * (-u2_1) ^ 2 = b2 * (c0 ^ 2 * Q * R3)) (hrel_u2 : u2_0 * u0_0 = u0_2 * u2_2)
    (hc0Q : 1 - ε1 ≤ c0 * Q ∧ c0 * Q ≤ 1 + ε1)
    (hc0QR2 : 1 - ε1 ≤ c0 * Q * R2 ∧ c0 * Q * R2 ≤ 1 + ε1)
    (hc02QR3 : 1 - ε1 ≤ c0 ^ 2 * Q * R3 ∧ c0 ^ 2 * Q * R3 ≤ 1 + ε1) :
    let s1 := √(u1_0 ^ 2 + u1_2 ^ 2); let s2 := √(u2_0 ^ 2 + u2_2 ^ 2)
    0 < s1 ∧ 0 < s2 ∧ (0 ≤ s1 ∧ s1 ≤ 65 / √N ∧ |s1 - √ab2 / √N| ≤ δ / √N) ∧
      (|u1_0 / s1 - (- √a2 / √ab2)| ≤ δ ∧ |u1_2 / s1 - √b2 / √ab2| ≤ δ) ∧
      (0 ≤ - u2_1 ∧ - u2_1 ≤ 65 / √N ∧ |- u2_1 - √b2 / √N| ≤ δ / √N) ∧
      (|u2_0 / s2| ≤ δ ∧ |u2_2 / s2 - 1| ≤ δ) := by
  dsimp only; have hab2_pos : 0 < ab2 := (by linarith); set s1 : ℝ := √(u1_0 ^ 2 + u1_2 ^ 2)
  set s2 : ℝ := √(u2_0 ^ 2 + u2_2 ^ 2)
  have hu10_sq_pos : 0 < u1_0 ^ 2 := (by rw [sq]; exact mul_pos_of_neg_of_neg hu1_0_neg hu1_0_neg)
  have hs1_pos : 0 < s1 := Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg hu10_sq_pos (sq_nonneg _))
  have hs1_sq : s1 ^ 2 = u1_0 ^ 2 + u1_2 ^ 2 := Real.sq_sqrt (by positivity)
  have hs2_pos : 0 < s2 := Real.sqrt_pos.mpr (by positivity)
  have hs2_sq : s2 ^ 2 = u2_0 ^ 2 + u2_2 ^ 2 := Real.sq_sqrt (by positivity)
  have hNs1_lo : (1 - ε1) * ab2 ≤ N * s1 ^ 2 := by
    rw [hs1_sq, mul_add, hu1_0_sq, hu1_2_sq, hab2_eq]
    have h1 := mul_le_mul_of_nonneg_left hc0Q.1 ha2_pos.le
    have h2 := mul_le_mul_of_nonneg_left hc0QR2.1 hb2_pos.le
    linarith [show (1 - ε1) * (a2 + b2) = a2 * (1 - ε1) + b2 * (1 - ε1) by ring]
  have hNs1_hi : N * s1 ^ 2 ≤ (1 + ε1) * ab2 := by
    rw [hs1_sq, mul_add, hu1_0_sq, hu1_2_sq, hab2_eq]
    have h1 := mul_le_mul_of_nonneg_left hc0Q.2 ha2_pos.le
    have h2 := mul_le_mul_of_nonneg_left hc0QR2.2 hb2_pos.le
    linarith [show (1 + ε1) * (a2 + b2) = a2 * (1 + ε1) + b2 * (1 + ε1) by ring]
  have hs1_rat_sq : (s1 / (√ab2 / √N)) ^ 2 = (N * s1 ^ 2) / ab2 := by
    rw [div_pow, div_pow, Real.sq_sqrt hN_pos.le, Real.sq_sqrt hab2_pos.le]
    field_simp [hN_pos.ne', hab2_pos.ne']
  have hsqrt_ab2_64 : √ab2 ≤ 64 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hs1_err : |s1 - √ab2 / √N| ≤ δ / √N := by
    have h1 := abs_sub_of_div_near_one hs1_pos.le (div_pos (Real.sqrt_pos.mpr hab2_pos) hsqrtN_pos)
      hε1_pos.le (by linarith)
      (by rw [hs1_rat_sq, le_div_iff₀ hab2_pos]; exact hNs1_lo)
      (by rw [hs1_rat_sq, div_le_iff₀ hab2_pos]; exact hNs1_hi)
    refine h1.trans ?_; rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hsqrt_ab2_64 hε1_pos.le).trans (by linarith)) hsqrtN_pos.le
  have hs1_65 : s1 ≤ 65 / √N := by
    have h2 := (abs_le.mp hs1_err).2
    have hsum : √ab2 / √N + δ / √N ≤ 65 / √N := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hsqrtN_pos.le
    linarith
  have hu1_0_s1 : |u1_0 / s1 - (- √a2 / √ab2)| ≤ δ := by
    have hneg_eq : |u1_0 / s1 - (- √a2 / √ab2)| = |(- u1_0 / s1) - (√a2 / √ab2)| := by
      rw [← abs_neg]; congr 1; ring
    rw [hneg_eq]
    have hsq_eq : ((- u1_0 / s1) / (√a2 / √ab2)) ^ 2 = (c0 * Q) / ((N * s1 ^ 2) / ab2) := by
      have hu10 : u1_0 ^ 2 = (a2 * (c0 * Q)) / N := by
        rw [← hu1_0_sq, mul_div_cancel_left₀ _ hN_pos.ne']
      rw [div_pow, div_pow, div_pow, neg_sq, Real.sq_sqrt ha2_pos.le, Real.sq_sqrt hab2_pos.le,
        hu10]
      field_simp [hs1_pos.ne', ha2_pos.ne', hab2_pos.ne', hN_pos.ne']
    obtain ⟨hr1, hr2⟩ := ratio_near_one hε1_pos.le (by linarith) hc0Q.1 hc0Q.2
      ((le_div_iff₀ hab2_pos).mpr hNs1_lo) ((div_le_iff₀ hab2_pos).mpr hNs1_hi)
    have h1 := abs_sub_of_div_near_one (x := - u1_0 / s1) (t := √a2 / √ab2) (ε := 4 * ε1)
      (div_nonneg (neg_nonneg.mpr hu1_0_neg.le) hs1_pos.le)
      (div_pos (Real.sqrt_pos.mpr ha2_pos) (Real.sqrt_pos.mpr hab2_pos))
      (by positivity) (by linarith) (by rw [hsq_eq]; exact hr1) (by rw [hsq_eq]; exact hr2)
    have ht_le1 : √a2 / √ab2 ≤ 1 :=
      (div_le_one (Real.sqrt_pos.mpr hab2_pos)).mpr (Real.sqrt_le_sqrt (by linarith))
    have hm : (4 * ε1) * (√a2 / √ab2) ≤ 4 * ε1 :=
      (mul_le_mul_of_nonneg_left ht_le1 (by positivity)).trans_eq (mul_one _)
    linarith
  have hu1_2_s1 : |u1_2 / s1 - √b2 / √ab2| ≤ δ := by
    have hsq_eq : ((u1_2 / s1) / (√b2 / √ab2)) ^ 2 = (c0 * Q * R2) / ((N * s1 ^ 2) / ab2) := by
      have hu12 : u1_2 ^ 2 = (b2 * (c0 * Q * R2)) / N := by
        rw [← hu1_2_sq, mul_div_cancel_left₀ _ hN_pos.ne']
      rw [div_pow, div_pow, div_pow, Real.sq_sqrt hb2_pos.le, Real.sq_sqrt hab2_pos.le, hu12]
      field_simp [hs1_pos.ne', hb2_pos.ne', hab2_pos.ne', hN_pos.ne']
    obtain ⟨hr1, hr2⟩ := ratio_near_one hε1_pos.le (by linarith) hc0QR2.1 hc0QR2.2
      ((le_div_iff₀ hab2_pos).mpr hNs1_lo) ((div_le_iff₀ hab2_pos).mpr hNs1_hi)
    have h1 := abs_sub_of_div_near_one (x := u1_2 / s1) (t := √b2 / √ab2) (ε := 4 * ε1)
      (div_nonneg hu1_2_pos.le hs1_pos.le)
      (div_pos (Real.sqrt_pos.mpr hb2_pos) (Real.sqrt_pos.mpr hab2_pos))
      (by positivity) (by linarith) (by rw [hsq_eq]; exact hr1) (by rw [hsq_eq]; exact hr2)
    have ht_le1 : √b2 / √ab2 ≤ 1 :=
      (div_le_one (Real.sqrt_pos.mpr hab2_pos)).mpr (Real.sqrt_le_sqrt (by linarith))
    have hm : (4 * ε1) * (√b2 / √ab2) ≤ 4 * ε1 :=
      (mul_le_mul_of_nonneg_left ht_le1 (by positivity)).trans_eq (mul_one _)
    linarith
  have hu2_1_rat_sq : ((- u2_1) / (√b2 / √N)) ^ 2 = c0 ^ 2 * Q * R3 := by
    have hu21 : (- u2_1) ^ 2 = (b2 * (c0 ^ 2 * Q * R3)) / N := by
      rw [← hu2_1_sq, mul_div_cancel_left₀ _ hN_pos.ne']
    rw [div_pow, div_pow, Real.sq_sqrt hN_pos.le, Real.sq_sqrt hb2_pos.le, hu21]
    field_simp [hN_pos.ne', hb2_pos.ne']
  have hsqrt_b2_64 : √b2 ≤ 64 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hu2_1_err : |- u2_1 - √b2 / √N| ≤ δ / √N := by
    have h1 := abs_sub_of_div_near_one (x := - u2_1) (t := √b2 / √N) (ε := ε1)
      (neg_nonneg.mpr hu2_1_neg.le)
      (div_pos (Real.sqrt_pos.mpr hb2_pos) hsqrtN_pos) hε1_pos.le (by linarith)
      (by rw [hu2_1_rat_sq]; exact hc02QR3.1) (by rw [hu2_1_rat_sq]; exact hc02QR3.2)
    refine h1.trans ?_; rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hsqrt_b2_64 hε1_pos.le).trans (by linarith)) hsqrtN_pos.le
  have hu2_1_65 : - u2_1 ≤ 65 / √N := by
    have h2 := (abs_le.mp hu2_1_err).2
    have hsum : √b2 / √N + δ / √N ≤ 65 / √N := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hsqrtN_pos.le
    linarith
  have hu2_0_s2 : |u2_0 / s2| ≤ δ := by
    have hu22_le : u2_2 ≤ s2 := Real.le_sqrt_of_sq_le (by linarith [sq_nonneg u2_0])
    have hu00_half : 1 / 2 ≤ u0_0 := (by have h1 := (abs_le.mp hu0_0_bd).1; linarith)
    have hle : u2_0 / s2 ≤ 128 / √N := by
      rw [div_le_iff₀ hs2_pos]
      have h1 : u2_0 * (1 / 2) ≤ u0_2 * s2 :=
        (mul_le_mul_of_nonneg_left hu00_half hu2_0_pos.le).trans
          (by rw [hrel_u2]; exact mul_le_mul_of_nonneg_left hu22_le hu0_2_pos.le)
      have h2 : u2_0 ≤ 2 * (u0_2 * s2) := (by linarith)
      have h3 := mul_le_mul_of_nonneg_right hu0_2_64 hs2_pos.le
      have h4 : 2 * ((64 / √N) * s2) = (128 / √N) * s2 := (by ring); linarith
    rw [abs_of_pos (div_pos hu2_0_pos hs2_pos)]
    exact hle.trans ((div_le_div_of_nonneg_right (by norm_num) hsqrtN_pos.le).trans hsqrt_δ)
  have hu2_2_s2 : |u2_2 / s2 - 1| ≤ δ := by
    have hpyth : (u2_0 / s2) ^ 2 + (u2_2 / s2) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, ← hs2_sq, div_self (pow_ne_zero 2 hs2_pos.ne')]
    have h0_sq : (u2_0 / s2) ^ 2 ≤ δ := by
      have habs : u2_0 / s2 ≤ δ := (by rwa [abs_of_pos (div_pos hu2_0_pos hs2_pos)] at hu2_0_s2)
      have hle1 : u2_0 / s2 ≤ 1 := (by linarith)
      calc (u2_0 / s2) ^ 2 = (u2_0 / s2) * (u2_0 / s2) := sq _
        _ ≤ 1 * δ := mul_le_mul hle1 habs (div_nonneg hu2_0_pos.le hs2_pos.le) zero_le_one
        _ = δ := one_mul δ
    have h1 := abs_sub_of_div_near_one (div_nonneg hu2_2_pos.le hs2_pos.le) zero_lt_one
      hδ_pos.le (by linarith)
      (by rw [div_one]; linarith) (by rw [div_one]; linarith [sq_nonneg (u2_0 / s2)])
    simpa only [mul_one] using h1
  exact ⟨hs1_pos, hs2_pos, ⟨hs1_pos.le, hs1_65, hs1_err⟩, ⟨hu1_0_s1, hu1_2_s1⟩,
    ⟨by linarith, hu2_1_65, hu2_1_err⟩, ⟨hu2_0_s2, hu2_2_s2⟩⟩
private lemma p01_basis_enclosures {n m r : ℕ} (hn : 200 ≤ n)
    (hm2 : 2 ≤ m) (hm_hi : m ≤ 1024) (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024) (hmin : min m r ≤ 2) :
    let N := 2 ^ n; let a2 := m * r; let b2 := 2 * (m - 1) * (r - 1); let ab2 := a2 + b2
    let u0 := u0OrbVec N m r; let u1 := u1OrbVec N m r; let u2 := u2OrbVec N m r
    let s1 := √((u1 0) ^ 2 + (u1 2) ^ 2); let s2 := √((u2 0) ^ 2 + (u2 2) ^ 2)
    let δ : ℝ := 1 / (2 : ℝ) ^ 90
    (0 ≤ u1 1 ∧ 0 < s1 ∧ u2 1 ≤ 0 ∧ 0 < s2) ∧ (|u0 0 - 1| ≤ δ ∧ |u0 1| ≤ δ ∧ |u0 2| ≤ δ) ∧
      (0 ≤ s1 ∧ s1 ≤ 65 / √(N : ℝ) ∧ |s1 - √(ab2 : ℝ) / √(N : ℝ)| ≤ δ / √(N : ℝ)) ∧
      (|u1 0 / s1 - (- √(a2 : ℝ) / √(ab2 : ℝ))| ≤ δ ∧
        |u1 2 / s1 - √(b2 : ℝ) / √(ab2 : ℝ)| ≤ δ) ∧
      (0 ≤ - u2 1 ∧ - u2 1 ≤ 65 / √(N : ℝ) ∧
        |- u2 1 - √(b2 : ℝ) / √(N : ℝ)| ≤ δ / √(N : ℝ)) ∧
      (|u2 0 / s2| ≤ δ ∧ |u2 2 / s2 - 1| ≤ δ) := by
  dsimp only; set N : ℕ := 2 ^ n
  have hN_ge : (2 : ℝ) ^ 200 ≤ (N : ℝ) := by
    dsimp only [N]; rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) hn
  have hN_big : (100000000 : ℝ) ≤ (N : ℝ) := (by norm_num : (100000000 : ℝ) ≤ (2 : ℝ) ^ 200).trans
    hN_ge
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hN_big
  have hsqrtN_ge : (2 : ℝ) ^ 100 ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hN_ge)
  have hsqrtN_pos : (0 : ℝ) < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsqrtN_ge
  have hN12 : 4096 ≤ N :=
    (by norm_num : 4096 ≤ 2 ^ 12).trans (Nat.pow_le_pow_right (by omega) (by omega : 12 ≤ n))
  have hmr_lt : m + r < N := (by omega); have h2m_lt : 2 * m < N := (by omega)
  have hmr_cases : m = 2 ∨ r = 2 := (by omega); set a2 : ℕ := m * r
  set b2 : ℕ := 2 * (m - 1) * (r - 1); set ab2 : ℕ := a2 + b2; set δ : ℝ := 1 / (2 : ℝ) ^ 90
  have hδ_pos : 0 < δ := (by positivity); have hδ_le : δ ≤ 1 / 8 := (by dsimp only [δ]; norm_num)
  have hsqrt_δ : 1024 / √(N : ℝ) ≤ δ := by
    rw [div_le_iff₀ hsqrtN_pos]
    calc (1024 : ℝ) ≤ δ * (2 : ℝ) ^ 100 := by dsimp only [δ]; norm_num
      _ ≤ δ * √(N : ℝ) := mul_le_mul_of_nonneg_left hsqrtN_ge hδ_pos.le
  have hN_δ : 100000000 / (N : ℝ) ≤ δ := by
    rw [div_le_iff₀ hN_pos]
    calc (100000000 : ℝ) ≤ δ * (2 : ℝ) ^ 200 := by dsimp only [δ]; norm_num
      _ ≤ δ * (N : ℝ) := mul_le_mul_of_nonneg_left hN_ge hδ_pos.le
  have ha2_hi : a2 ≤ 2048 := (by dsimp only [a2]; rcases hmr_cases with rfl | rfl <;> omega)
  have hb2_hi : b2 ≤ 2046 := (by dsimp only [b2]; rcases hmr_cases with rfl | rfl <;> omega)
  have ha2_pos : 0 < a2 := Nat.mul_pos (by omega) (by omega)
  have hb2_pos : 0 < b2 := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have ha2R_pos : (0 : ℝ) < (a2 : ℝ) := Nat.cast_pos.mpr ha2_pos
  have hb2R_pos : (0 : ℝ) < (b2 : ℝ) := Nat.cast_pos.mpr hb2_pos
  have ha2R_hi : (a2 : ℝ) ≤ 2048 := (by exact_mod_cast ha2_hi)
  have hb2R_hi : (b2 : ℝ) ≤ 2046 := (by exact_mod_cast hb2_hi)
  have hab2R_eq : (ab2 : ℝ) = (a2 : ℝ) + (b2 : ℝ) := (by dsimp only [ab2]; push_cast; rfl)
  have hab2R_hi : (ab2 : ℝ) ≤ 4094 := (by rw [hab2R_eq]; linarith)
  have hmR_lo : (2 : ℝ) ≤ (m : ℝ) := (by exact_mod_cast hm2)
  have hmR_hi : (m : ℝ) ≤ 1024 := (by exact_mod_cast hm_hi)
  have hrR_lo : (2 : ℝ) ≤ (r : ℝ) := (by exact_mod_cast hr2)
  have hrR_hi : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr_hi)
  have hrR_pos : (0 : ℝ) < (r : ℝ) := (by linarith); set u0 := u0OrbVec N m r
  set u1 := u1OrbVec N m r; set u2 := u2OrbVec N m r
  have hch_pos : (0 : ℝ) < (N.choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hu0_pos : ∀ w : Fin 3, 0 < u0 w := fun w ↦
    Real.sqrt_pos.mpr (div_pos (Nat.cast_pos.mpr (orbCard_pos hm2 hr2 hmr_lt (by omega))) hch_pos)
  have hu0_0_pos : 0 < u0 0 := hu0_pos 0; have hu0_1_pos : 0 < u0 1 := hu0_pos 1
  have hu0_2_pos : 0 < u0 2 := hu0_pos 2
  have hu0_sq : ∀ w : Fin 3, (u0 w) ^ 2 = (orbCard N m r w.1 : ℝ) / (N.choose m : ℝ) := fun w ↦
    Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hch_pos.le)
  have hc_sum : (u0 0) ^ 2 + (u0 1) ^ 2 + (u0 2) ^ 2 = 1 := by
    have h := dot3_u0_self hm2 hr2 hmin hmr_lt; unfold dot3 at h
    linarith [sq (u0 0), sq (u0 1), sq (u0 2)]
  set D1 : ℝ := (N : ℝ) - (r : ℝ) - (m : ℝ) + 1; set D2 : ℝ := (N : ℝ) - (r : ℝ) - (m : ℝ) + 2
  have hD1_cast : ((N - r - m + 1 : ℕ) : ℝ) = D1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have hD2_cast : ((N - r - m + 2 : ℕ) : ℝ) = D2 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_ofNat]
  have hrel1 : (u0 0) ^ 2 * (a2 : ℝ) = (u0 1) ^ 2 * D1 := by
    have hR : (orbCard N m r 0 : ℝ) * ((r : ℝ) * (m : ℝ)) = (orbCard N m r 1 : ℝ) * D1 := by
      rw [← hD1_cast]; exact_mod_cast orbCard_rel1 (by omega) hmr_lt.le
    dsimp only [a2]; rw [hu0_sq 0, hu0_sq 1]
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_mul, div_mul_eq_mul_div]; congr 1
    calc (orbCard N m r 0 : ℝ) * ((m : ℝ) * (r : ℝ))
        = (orbCard N m r 0 : ℝ) * ((r : ℝ) * (m : ℝ)) := by ring
      _ = (orbCard N m r 1 : ℝ) * D1 := hR
  have hrel2 : (u0 1) ^ 2 * (b2 : ℝ) = 4 * (u0 2) ^ 2 * D2 := by
    have hR : (orbCard N m r 1 : ℝ) * (((r - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) =
        2 * (orbCard N m r 2 : ℝ) * D2 := by
      rw [← hD2_cast]; exact_mod_cast orbCard_rel2 hm2 hr2 hmr_lt.le
    have hb2_cast : (b2 : ℝ) = 2 * (((m - 1 : ℕ) : ℝ) * ((r - 1 : ℕ) : ℝ)) := by
      dsimp only [b2]; push_cast; ring
    rw [hu0_sq 1, hu0_sq 2, hb2_cast]; simp only [Fin.val_one, Fin.val_two, div_mul_eq_mul_div]
    have hrhs : 4 * ((orbCard N m r 2 : ℝ) / (N.choose m : ℝ)) * D2 =
        (2 * (2 * (orbCard N m r 2 : ℝ) * D2)) / (N.choose m : ℝ) := by ring
    rw [hrhs]; congr 1
    calc (orbCard N m r 1 : ℝ) * (2 * (((m - 1 : ℕ) : ℝ) * ((r - 1 : ℕ) : ℝ)))
        = 2 * ((orbCard N m r 1 : ℝ) * (((r - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ))) := by ring
      _ = 2 * (2 * (orbCard N m r 2 : ℝ) * D2) := by rw [hR]
  have hD1_lo : (N : ℝ) / 2 ≤ D1 := (by dsimp only [D1]; linarith)
  have hD2_lo : (N : ℝ) / 2 ≤ D2 := (by dsimp only [D2]; linarith)
  have hD1_pos : 0 < D1 := (by linarith); have hD2_pos : 0 < D2 := (by linarith)
  obtain ⟨hu0_bds, hu0_2_64, hc0_lo, hc0_le1, hrel02⟩ :=
    p01_u0_bounds hN_pos hsqrtN_pos hδ_pos hδ_le hsqrt_δ hN_δ ha2R_pos ha2R_hi hb2R_pos hb2R_hi
      hD1_lo hD2_lo hu0_0_pos hu0_1_pos hu0_2_pos hc_sum hrel1 hrel2
  set G : ℝ := √(((N : ℝ) - 1) / ((a2 : ℝ) * ((N : ℝ) - (m : ℝ)) * ((N : ℝ) - (r : ℝ))))
  have hNm_pos : 0 < (N : ℝ) - (m : ℝ) := (by linarith)
  have hNr_pos : 0 < (N : ℝ) - (r : ℝ) := (by linarith)
  have hG_pos : 0 < G := Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
  have hG_sq : G ^ 2 = ((N : ℝ) - 1) / ((a2 : ℝ) * ((N : ℝ) - (m : ℝ)) * ((N : ℝ) - (r : ℝ))) :=
    Real.sq_sqrt (div_nonneg (by linarith) (by positivity))
  have hch_rel : (m : ℝ) * ((N : ℝ) - (m : ℝ)) * (N.choose m : ℝ) =
      (N : ℝ) * ((N : ℝ) - 1) * ((N - 2).choose (m - 1) : ℝ) := by
    have h := choose_rel_p01 (by omega : 1 ≤ m) h2m_lt; have hc := (Nat.cast_inj (R := ℝ)).mpr h
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : m ≤ N),
      Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hc; exact hc
  have ha2_cast : (a2 : ℝ) = (m : ℝ) * (r : ℝ) := (by dsimp only [a2]; push_cast; rfl)
  have hu1_eq : ∀ w : Fin 3, u1 w = ((w.1 : ℝ) * (N : ℝ) - (a2 : ℝ)) * u0 w * G := by
    intro w; dsimp only [u1, u1OrbVec, u0, u0OrbVec, G]
    have hNr_cast : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) := Nat.cast_sub (by omega)
    have hD_pos : (0 : ℝ) < ((N - 2).choose (m - 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    rw [← ha2_cast, hNr_cast, mul_assoc ((w.1 : ℝ) * (N : ℝ) - (a2 : ℝ)),
      ← Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hch_pos.le)]
    congr 2; rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]; rw [ha2_cast]
    linear_combination (orbCard N m r w.1 : ℝ) * (r : ℝ) * ((N : ℝ) - (r : ℝ)) * hch_rel
  have hu1_0_neg : u1 0 < 0 := by
    rw [hu1_eq 0]; simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_sub]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ha2R_pos) hu0_0_pos) hG_pos
  have hu1_1_pos : 0 < u1 1 := by
    rw [hu1_eq 1]; simp only [Fin.val_one, Nat.cast_one, one_mul]
    exact mul_pos (mul_pos (by linarith) hu0_1_pos) hG_pos
  have hu1_2_pos : 0 < u1 2 := by
    rw [hu1_eq 2]; simp only [Fin.val_two, Nat.cast_ofNat]
    exact mul_pos (mul_pos (by linarith) hu0_2_pos) hG_pos
  set Q : ℝ := ((N : ℝ) * ((N : ℝ) - 1)) / (((N : ℝ) - (m : ℝ)) * ((N : ℝ) - (r : ℝ)))
  set R2 : ℝ := (2 * (N : ℝ) - (a2 : ℝ)) ^ 2 / (4 * D1 * D2); set R3 : ℝ := (N : ℝ) ^ 2 / (D1 * D2)
  set ε1 : ℝ := 32768 / (N : ℝ)
  have hQ_eq : (a2 : ℝ) * (N : ℝ) * G ^ 2 = Q := by
    rw [hG_sq]; dsimp only [Q]
    rw [← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]; ring
  have hε1_pos : 0 < ε1 := (by positivity)
  have hε1_hi : ε1 ≤ 1 / 32 := (by dsimp only [ε1]; rw [div_le_iff₀ hN_pos]; linarith)
  have hε1_δ : 64 * ε1 ≤ δ := by
    refine (?_ : 64 * ε1 ≤ 100000000 / (N : ℝ)).trans hN_δ; dsimp only [ε1]; rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by norm_num) hN_pos.le
  have hu1_0_sq : (N : ℝ) * (u1 0) ^ 2 = (a2 : ℝ) * ((u0 0) ^ 2 * Q) := by
    rw [hu1_eq 0]; simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_sub]
    calc (N : ℝ) * (- (a2 : ℝ) * u0 0 * G) ^ 2
        = (a2 : ℝ) * (u0 0) ^ 2 * ((a2 : ℝ) * (N : ℝ) * G ^ 2) := by ring
      _ = (a2 : ℝ) * ((u0 0) ^ 2 * Q) := by rw [hQ_eq]; ring
  have hu1_2_sq : (N : ℝ) * (u1 2) ^ 2 = (b2 : ℝ) * ((u0 0) ^ 2 * Q * R2) := by
    rw [hu1_eq 2]; simp only [Fin.val_two, Nat.cast_ofNat]
    have h4D : 0 < 4 * D1 * D2 := (by positivity); rw [eq_comm]; dsimp only [R2]
    rw [← mul_div_assoc, ← mul_div_assoc, div_eq_iff h4D.ne']
    calc (b2 : ℝ) * ((u0 0) ^ 2 * Q * (2 * (N : ℝ) - (a2 : ℝ)) ^ 2)
        = ((u0 0) ^ 2 * (a2 : ℝ) * (b2 : ℝ)) * (2 * (N : ℝ) - (a2 : ℝ)) ^ 2 *
            ((N : ℝ) * G ^ 2) := by rw [← hQ_eq]; ring
      _ = (4 * D1 * D2 * (u0 2) ^ 2) * (2 * (N : ℝ) - (a2 : ℝ)) ^ 2 * ((N : ℝ) * G ^ 2) := by
            rw [← hrel02]
      _ = (N : ℝ) * ((2 * (N : ℝ) - (a2 : ℝ)) * u0 2 * G) ^ 2 * (4 * D1 * D2) := by ring
  have hu2_0_eq : u2 0 = (N : ℝ) * u0 1 * u0 2 * G := by
    change (cross3 u0 u1) 0 = _; dsimp only [cross3]; rw [vec3_zero, hu1_eq 1, hu1_eq 2]
    simp only [Fin.val_one, Fin.val_two, Nat.cast_one, Nat.cast_ofNat]; ring
  have hu2_1_eq : u2 1 = - 2 * (N : ℝ) * u0 0 * u0 2 * G := by
    change (cross3 u0 u1) 1 = _; dsimp only [cross3]; rw [vec3_one, hu1_eq 0, hu1_eq 2]
    simp only [Fin.val_zero, Fin.val_two, Nat.cast_zero, Nat.cast_ofNat]; ring
  have hu2_2_eq : u2 2 = (N : ℝ) * u0 0 * u0 1 * G := by
    change (cross3 u0 u1) 2 = _; dsimp only [cross3]; rw [vec3_two, hu1_eq 0, hu1_eq 1]
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]; ring
  have hu2_0_pos : 0 < u2 0 := (by rw [hu2_0_eq]; positivity)
  have hu2_1_neg : u2 1 < 0 := by
    rw [hu2_1_eq]; have : 0 < 2 * (N : ℝ) * u0 0 * u0 2 * G := (by positivity); linarith
  have hu2_2_pos : 0 < u2 2 := (by rw [hu2_2_eq]; positivity)
  have hrel_u2 : u2 0 * u0 0 = u0 2 * u2 2 := (by rw [hu2_0_eq, hu2_2_eq]; ring)
  have hu2_1_sq : (N : ℝ) * (- u2 1) ^ 2 = (b2 : ℝ) * (((u0 0) ^ 2) ^ 2 * Q * R3) := by
    rw [hu2_1_eq, eq_comm]; dsimp only [R3]; have hDD_pos : 0 < D1 * D2 := (by positivity)
    rw [← mul_div_assoc, ← mul_div_assoc, div_eq_iff hDD_pos.ne']
    calc (b2 : ℝ) * (((u0 0) ^ 2) ^ 2 * Q * (N : ℝ) ^ 2)
        = (u0 0) ^ 2 * ((u0 0) ^ 2 * (a2 : ℝ) * (b2 : ℝ)) * (N : ℝ) ^ 2 *
            ((N : ℝ) * G ^ 2) := by rw [← hQ_eq]; ring
      _ = (u0 0) ^ 2 * (4 * D1 * D2 * (u0 2) ^ 2) * (N : ℝ) ^ 2 * ((N : ℝ) * G ^ 2) := by
            rw [← hrel02]
      _ = (N : ℝ) * (- (- 2 * (N : ℝ) * u0 0 * u0 2 * G)) ^ 2 * (D1 * D2) := by ring
  have hqr_bds := p01_Q_R2_R3_bounds hN_big hmR_lo hmR_hi hrR_lo hrR_hi ha2R_pos ha2R_hi
    rfl rfl (sq_nonneg (u0 0)) hc0_lo hc0_le1
  dsimp only at hqr_bds; obtain ⟨hc0Q, hc0QR2, hc02QR3⟩ := hqr_bds
  have hs_bds := p01_s1_s2_bounds hN_pos hsqrtN_pos hδ_pos hδ_le hsqrt_δ hε1_pos hε1_δ ha2R_pos
    hb2R_pos hb2R_hi hab2R_eq hab2R_hi hu0_bds.1 hu0_2_pos hu0_2_64 hu1_0_neg hu1_2_pos hu1_0_sq
    hu1_2_sq hu2_0_pos hu2_1_neg hu2_2_pos hu2_1_sq hrel_u2 hc0Q hc0QR2 hc02QR3
  dsimp only at hs_bds
  obtain ⟨hs1_pos, hs2_pos, hs1_bds, hu1_s1_bds, hu2_1_bds, hu2_s2_bds⟩ := hs_bds
  exact ⟨⟨hu1_1_pos.le, hs1_pos, hu2_1_neg.le, hs2_pos⟩,
    hu0_bds, hs1_bds, hu1_s1_bds, hu2_1_bds, hu2_s2_bds⟩
/-! ## Section 4: Pure-Integer 2-Stage Jordan Evaluator & Finite-`N` Soundness -/
/-- `10 ^ 15`-scaled interval and hit-probability lower-bound output of `p01EvalRowIV15`. -/
structure P01RowEvalResult where
  th1_iv : WDIVal
  th2_iv : WDIVal
  p0_iv : WDIVal
  p1_iv : WDIVal
  p2_iv : WDIVal
  p1_lo_15 : ℕ
  p2_lo_15 : ℕ
  deriving DecidableEq
/-- Parameterized `10 ^ 15`-scaled 2-stage Jordan rotation evaluator (`n ≥ 200`, `pad = 1`). -/
def p01EvalRowWith (isqrtFn : ℕ → WDIVal) (m r tau1_12 tau2_12 : ℕ) : Option P01RowEvalResult :=
  if min m r != 2 || m < 2 || r < 2 then none
  else if 4000000000000 < tau1_12 || 4000000000000 < tau2_12 then none
  else if tau1_12 == 0 && tau2_12 == 0 then none
  else
    let B : ℤ := wdScale
    let a2 : ℕ := m * r
    let b2 : ℕ := 2 * (m - 1) * (r - 1)
    let ab2 : ℕ := a2 + b2
    let a_iv := isqrtFn a2
    let b_iv := isqrtFn b2
    let w_iv := isqrtFn ab2
    let om1_iv : WDIVal := (2 * w_iv.1, 2 * w_iv.2)
    let om2_iv : WDIVal := (2 * b_iv.1, 2 * b_iv.2)
    let dt_pad : ℤ := 1
    let dth_pad : ℤ := 1
    let dpsi_pad : ℤ := 1
    let t1_iv : WDIVal :=
      (max 0 ((tau1_12 : ℤ) * 1000 - dt_pad), (tau1_12 : ℤ) * 1000 + dt_pad)
    let t2_iv : WDIVal :=
      (max 0 ((tau2_12 : ℤ) * 1000 - dt_pad), (tau2_12 : ℤ) * 1000 + dt_pad)
    let th1_raw := wdMul om1_iv t1_iv
    let th1_iv : WDIVal := (max 0 (th1_raw.1 - dth_pad), th1_raw.2 + dth_pad)
    let th2_iv : WDIVal :=
      if 0 < tau2_12 then
        let th2_raw := wdMul om2_iv t2_iv
        (max 0 (th2_raw.1 - dth_pad), th2_raw.2 + dth_pad)
      else (0, 0)
    if 1024 * B < th1_iv.2 || 1024 * B < th2_iv.2 then none
    else
      let cs1 := wdTrig th1_iv
      let c1_iv := cs1.1
      let s1_iv := cs1.2
      let cs2 := if 0 < tau2_12 then wdTrig th2_iv else ((B, B), (0, 0))
      let c2_iv := cs2.1
      let s2_iv := cs2.2
      let x0_lo := wdDivFloor ((b2 : ℤ) * B + (a2 : ℤ) * c1_iv.1) (ab2 : ℤ)
      let x0_hi := wdDivCeil ((b2 : ℤ) * B + (a2 : ℤ) * c1_iv.2) (ab2 : ℤ)
      let a_div_w : WDIVal := (wdDivFloor (a_iv.1 * B) w_iv.2, wdDivCeil (a_iv.2 * B) w_iv.1)
      let ab_prod := wdMul a_iv b_iv
      let ab_div : WDIVal := (wdDivFloor ab_prod.1 (ab2 : ℤ), wdDivCeil ab_prod.2 (ab2 : ℤ))
      let x1_s1 := wdMul a_div_w s1_iv
      let one_m_c1 : WDIVal := (B - c1_iv.2, B - c1_iv.1)
      let x2_s1 := wdMul ab_div one_m_c1
      let y_pair :=
        if 0 < tau2_12 then
          (wdSub (wdMul c2_iv x1_s1) (wdMul s2_iv x2_s1),
            wdAdd (wdMul s2_iv x1_s1) (wdMul c2_iv x2_s1))
        else (x1_s1, x2_s1)
      let f0_iv : WDIVal := (x0_lo - dpsi_pad, x0_hi + dpsi_pad)
      let f1_iv : WDIVal := (y_pair.1.1 - dpsi_pad, y_pair.1.2 + dpsi_pad)
      let f2_iv : WDIVal := (y_pair.2.1 - dpsi_pad, y_pair.2.2 + dpsi_pad)
      let p0_iv := wdSq f0_iv
      let p1_iv := wdSq f1_iv
      let p2_iv := wdSq f2_iv
      let p1_lo_15 : ℕ := (max 0 p1_iv.1).toNat
      let p2_lo_15 : ℕ := (max 0 p2_iv.1).toNat
      if p1_lo_15 + p2_lo_15 == 0 then none
      else some ⟨th1_iv, th2_iv, p0_iv, p1_iv, p2_iv, p1_lo_15, p2_lo_15⟩
/-- Exact `10 ^ 15`-scaled 2-stage Jordan rotation evaluator using `p01Isqrt15`. -/
def p01EvalRowIV15 (m r tau1_12 tau2_12 : ℕ) : Option P01RowEvalResult :=
  p01EvalRowWith p01Isqrt15 m r tau1_12 tau2_12
/-- `10 ^ 15`-scaled hit-probability lower bounds `(p1_lo_15, p2_lo_15)` from
  `p01EvalRowIV15`. -/
def p01EvalRowLo15 (m r tau1_12 tau2_12 : ℕ) : Option (ℕ × ℕ) :=
  (p01EvalRowIV15 m r tau1_12 tau2_12).map fun iv ↦ (iv.p1_lo_15, iv.p2_lo_15)
private lemma abs_le_one_of_sq_add_le {a rest : ℝ} (hr : 0 ≤ rest) (h : a ^ 2 + rest ≤ 1) :
    |a| ≤ 1 :=
  abs_le.mpr ⟨by nlinarith [sq_nonneg (a + 1)], by nlinarith [sq_nonneg (a - 1)]⟩
private lemma abs_mul_le_of_left_le_one {a b : ℝ} (ha : |a| ≤ 1) : |a * b| ≤ |b| := by
  rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg b) ha
private lemma abs_mul_le_of_right_le_one {a b : ℝ} (hb : |b| ≤ 1) : |a * b| ≤ |a| := by
  rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) hb
private lemma p01_stage2_amp_errors {u0_0 u0_1 u0_2 q0 q2 q0_id q2_id r0 r2 c1 s1_tr c2 s2_tr δ : ℝ}
    (hu0 : u0_0 ^ 2 + u0_1 ^ 2 + u0_2 ^ 2 = 1)
    (hq : q0 ^ 2 + q2 ^ 2 = 1) (hq_id : q0_id ^ 2 + q2_id ^ 2 = 1) (hr : r0 ^ 2 + r2 ^ 2 = 1)
    (ht1 : c1 ^ 2 + s1_tr ^ 2 = 1) (ht2 : c2 ^ 2 + s2_tr ^ 2 = 1)
    (hu0_0 : |u0_0 - 1| ≤ δ) (hu0_1 : |u0_1| ≤ δ) (hu0_2 : |u0_2| ≤ δ)
    (hq0 : |q0 - q0_id| ≤ δ) (hq2 : |q2 - q2_id| ≤ δ) (hr0 : |r0| ≤ δ) (hr2 : |r2 - 1| ≤ δ) :
    let x1_rot := u0_1; let x2_rot := q0 * u0_0 + q2 * u0_2; let x3_rot := q2 * u0_0 - q0 * u0_2
    let y1_rot := x1_rot * c1 - x2_rot * s1_tr; let y2_rot := x1_rot * s1_tr + x2_rot * c1
    let psi1_0 := y2_rot * q0 + x3_rot * q2; let psi1_1 := y1_rot
    let psi1_2 := y2_rot * q2 - x3_rot * q0; let z2_rot := r0 * psi1_0 + r2 * psi1_2
    let z3_rot := r2 * psi1_0 - r0 * psi1_2; let w1_rot := psi1_1 * c2 - z2_rot * s2_tr
    let w2_rot := psi1_1 * s2_tr + z2_rot * c2; let psi2_0 := w2_rot * r0 + z3_rot * r2
    let psi2_1 := w1_rot; let psi2_2 := w2_rot * r2 - z3_rot * r0
    let x0_id := q2_id ^ 2 + q0_id ^ 2 * c1; let x1_id := (- q0_id) * s1_tr
    let x2_id := (- q0_id * q2_id) * (1 - c1); let y1_id := c2 * x1_id - s2_tr * x2_id
    let y2_id := s2_tr * x1_id + c2 * x2_id
    |psi2_0 - x0_id| ≤ 13 * δ ∧ |psi2_1 - y1_id| ≤ 15 * δ ∧ |psi2_2 - y2_id| ≤ 17 * δ := by
  dsimp only; have hq0_1 : |q0| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg q2) hq.le
  have hq2_1 : |q2| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg q0) (by linarith)
  have hq0i_1 : |q0_id| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg q2_id) hq_id.le
  have hq2i_1 : |q2_id| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg q0_id) (by linarith)
  have hr2_1 : |r2| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg r0) (by linarith)
  have hc1_1 : |c1| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg s1_tr) ht1.le
  have hs1_1 : |s1_tr| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg c1) (by linarith)
  have hc2_1 : |c2| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg s2_tr) ht2.le
  have hs2_1 : |s2_tr| ≤ 1 := abs_le_one_of_sq_add_le (sq_nonneg c2) (by linarith)
  set x2_rot := q0 * u0_0 + q2 * u0_2; set x3_rot := q2 * u0_0 - q0 * u0_2
  set y1_rot := u0_1 * c1 - x2_rot * s1_tr; set y2_rot := u0_1 * s1_tr + x2_rot * c1
  set psi1_0 := y2_rot * q0 + x3_rot * q2; set psi1_2 := y2_rot * q2 - x3_rot * q0
  set z2_rot := r0 * psi1_0 + r2 * psi1_2; set z3_rot := r2 * psi1_0 - r0 * psi1_2
  set w1_rot := y1_rot * c2 - z2_rot * s2_tr; set w2_rot := y1_rot * s2_tr + z2_rot * c2
  have hx_norm : u0_1 ^ 2 + x2_rot ^ 2 + x3_rot ^ 2 = 1 := by
    have hid : x2_rot ^ 2 + x3_rot ^ 2 = (q0 ^ 2 + q2 ^ 2) * (u0_0 ^ 2 + u0_2 ^ 2) := by
      dsimp only [x2_rot, x3_rot]; ring
    rw [add_assoc, hid, hq, one_mul]; linarith
  have hy_norm : y1_rot ^ 2 + y2_rot ^ 2 + x3_rot ^ 2 = 1 := by
    have hid : y1_rot ^ 2 + y2_rot ^ 2 = (c1 ^ 2 + s1_tr ^ 2) * (u0_1 ^ 2 + x2_rot ^ 2) := by
      dsimp only [y1_rot, y2_rot]; ring
    rw [hid, ht1, one_mul]; exact hx_norm
  have hpsi1_norm : psi1_0 ^ 2 + y1_rot ^ 2 + psi1_2 ^ 2 = 1 := by
    have hid : psi1_0 ^ 2 + psi1_2 ^ 2 = (q0 ^ 2 + q2 ^ 2) * (y2_rot ^ 2 + x3_rot ^ 2) := by
      dsimp only [psi1_0, psi1_2]; ring
    have hcomm : psi1_0 ^ 2 + y1_rot ^ 2 + psi1_2 ^ 2 = y1_rot ^ 2 + (psi1_0 ^ 2 + psi1_2 ^ 2) :=
      by ring
    rw [hcomm, hid, hq, one_mul]; linarith
  have hz_norm : y1_rot ^ 2 + z2_rot ^ 2 + z3_rot ^ 2 = 1 := by
    have hid : z2_rot ^ 2 + z3_rot ^ 2 = (r0 ^ 2 + r2 ^ 2) * (psi1_0 ^ 2 + psi1_2 ^ 2) := by
      dsimp only [z2_rot, z3_rot]; ring
    rw [add_assoc, hid, hr, one_mul]; linarith
  have hw_norm : w1_rot ^ 2 + w2_rot ^ 2 + z3_rot ^ 2 = 1 := by
    have hid : w1_rot ^ 2 + w2_rot ^ 2 = (c2 ^ 2 + s2_tr ^ 2) * (y1_rot ^ 2 + z2_rot ^ 2) := by
      dsimp only [w1_rot, w2_rot]; ring
    rw [hid, ht2, one_mul]; exact hz_norm
  have hp10_1 : |psi1_0| ≤ 1 :=
    abs_le_one_of_sq_add_le (rest := y1_rot ^ 2 + psi1_2 ^ 2) (by positivity)
      (by linarith [hpsi1_norm])
  have hp12_1 : |psi1_2| ≤ 1 :=
    abs_le_one_of_sq_add_le (rest := psi1_0 ^ 2 + y1_rot ^ 2) (by positivity)
      (by linarith [hpsi1_norm])
  have hz3_1 : |z3_rot| ≤ 1 :=
    abs_le_one_of_sq_add_le (rest := y1_rot ^ 2 + z2_rot ^ 2) (by positivity)
      (by linarith [hz_norm])
  have hw2_1 : |w2_rot| ≤ 1 :=
    abs_le_one_of_sq_add_le (rest := w1_rot ^ 2 + z3_rot ^ 2) (by positivity)
      (by linarith [hw_norm])
  have hx2_err : |x2_rot - q0_id| ≤ 3 * δ := by
    have hid : x2_rot - q0_id = q0 * (u0_0 - 1) + (q0 - q0_id) + q2 * u0_2 := by
      dsimp only [x2_rot]; ring
    rw [hid]
    linarith [abs_add_le (q0 * (u0_0 - 1) + (q0 - q0_id)) (q2 * u0_2),
      abs_add_le (q0 * (u0_0 - 1)) (q0 - q0_id), abs_mul_le_of_left_le_one hq0_1 (b := u0_0 - 1),
      abs_mul_le_of_left_le_one hq2_1 (b := u0_2)]
  have hx3_err : |x3_rot - q2_id| ≤ 3 * δ := by
    have hid : x3_rot - q2_id = q2 * (u0_0 - 1) + (q2 - q2_id) + (- q0) * u0_2 := by
      dsimp only [x3_rot]; ring
    rw [hid]; have hnq0 : |- q0| ≤ 1 := (by rwa [abs_neg])
    linarith [abs_add_le (q2 * (u0_0 - 1) + (q2 - q2_id)) ((- q0) * u0_2),
      abs_add_le (q2 * (u0_0 - 1)) (q2 - q2_id), abs_mul_le_of_left_le_one hq2_1 (b := u0_0 - 1),
      abs_mul_le_of_left_le_one hnq0 (b := u0_2)]
  have hy1_err : |y1_rot - (- q0_id) * s1_tr| ≤ 4 * δ := by
    have hid : y1_rot - (- q0_id) * s1_tr = c1 * u0_1 + (- s1_tr) * (x2_rot - q0_id) := by
      dsimp only [y1_rot]; ring
    rw [hid]; have hns1 : |- s1_tr| ≤ 1 := (by rwa [abs_neg])
    linarith [abs_add_le (c1 * u0_1) ((- s1_tr) * (x2_rot - q0_id)),
      abs_mul_le_of_left_le_one hc1_1 (b := u0_1),
      abs_mul_le_of_left_le_one hns1 (b := x2_rot - q0_id)]
  have hy2_err : |y2_rot - q0_id * c1| ≤ 4 * δ := by
    have hid : y2_rot - q0_id * c1 = s1_tr * u0_1 + c1 * (x2_rot - q0_id) := by
      dsimp only [y2_rot]; ring
    rw [hid]
    linarith [abs_add_le (s1_tr * u0_1) (c1 * (x2_rot - q0_id)),
      abs_mul_le_of_left_le_one hs1_1 (b := u0_1),
      abs_mul_le_of_left_le_one hc1_1 (b := x2_rot - q0_id)]
  have hqc1_1 : |q0_id * c1| ≤ 1 := (abs_mul_le_of_right_le_one hc1_1).trans hq0i_1
  have hp10_err : |psi1_0 - (q2_id ^ 2 + q0_id ^ 2 * c1)| ≤ 9 * δ := by
    have hid : psi1_0 - (q2_id ^ 2 + q0_id ^ 2 * c1) = q0 * (y2_rot - q0_id * c1) + (q0_id * c1) *
      (q0 - q0_id) + (q2 * (x3_rot - q2_id) + q2_id * (q2 - q2_id)) := by
      dsimp only [psi1_0]; ring
    rw [hid]
    linarith [abs_add_le (q0 * (y2_rot - q0_id * c1) + (q0_id * c1) * (q0 - q0_id))
        (q2 * (x3_rot - q2_id) + q2_id * (q2 - q2_id)),
      abs_add_le (q0 * (y2_rot - q0_id * c1)) ((q0_id * c1) * (q0 - q0_id)),
      abs_add_le (q2 * (x3_rot - q2_id)) (q2_id * (q2 - q2_id)),
      abs_mul_le_of_left_le_one hq0_1 (b := y2_rot - q0_id * c1),
      abs_mul_le_of_left_le_one hqc1_1 (b := q0 - q0_id),
      abs_mul_le_of_left_le_one hq2_1 (b := x3_rot - q2_id),
      abs_mul_le_of_left_le_one hq2i_1 (b := q2 - q2_id)]
  have hp12_err : |psi1_2 - (- q0_id * q2_id) * (1 - c1)| ≤ 9 * δ := by
    have hid : psi1_2 - (- q0_id * q2_id) * (1 - c1) = q2 * (y2_rot - q0_id * c1) + (q0_id * c1) *
      (q2 - q2_id) + ((- q0) * (x3_rot - q2_id) + (- q2_id) * (q0 - q0_id)) := by
      dsimp only [psi1_2]; ring
    rw [hid]; have hnq0 : |- q0| ≤ 1 := (by rwa [abs_neg])
    have hnq2i : |- q2_id| ≤ 1 := (by rwa [abs_neg])
    linarith [abs_add_le (q2 * (y2_rot - q0_id * c1) + (q0_id * c1) * (q2 - q2_id))
        ((- q0) * (x3_rot - q2_id) + (- q2_id) * (q0 - q0_id)),
      abs_add_le (q2 * (y2_rot - q0_id * c1)) ((q0_id * c1) * (q2 - q2_id)),
      abs_add_le ((- q0) * (x3_rot - q2_id)) ((- q2_id) * (q0 - q0_id)),
      abs_mul_le_of_left_le_one hq2_1 (b := y2_rot - q0_id * c1),
      abs_mul_le_of_left_le_one hqc1_1 (b := q2 - q2_id),
      abs_mul_le_of_left_le_one hnq0 (b := x3_rot - q2_id),
      abs_mul_le_of_left_le_one hnq2i (b := q0 - q0_id)]
  have hz2_err : |z2_rot - (- q0_id * q2_id) * (1 - c1)| ≤ 11 * δ := by
    have hid : z2_rot - (- q0_id * q2_id) * (1 - c1) =
        psi1_0 * r0 + psi1_2 * (r2 - 1) + (psi1_2 - (- q0_id * q2_id) * (1 - c1)) := by
      dsimp only [z2_rot]; ring
    rw [hid]
    linarith [abs_add_le (psi1_0 * r0 + psi1_2 * (r2 - 1)) (psi1_2 - (- q0_id * q2_id) * (1 - c1)),
      abs_add_le (psi1_0 * r0) (psi1_2 * (r2 - 1)), abs_mul_le_of_left_le_one hp10_1 (b := r0),
      abs_mul_le_of_left_le_one hp12_1 (b := r2 - 1)]
  have hz3_err : |z3_rot - (q2_id ^ 2 + q0_id ^ 2 * c1)| ≤ 11 * δ := by
    have hid : z3_rot - (q2_id ^ 2 + q0_id ^ 2 * c1) =
        psi1_0 * (r2 - 1) + (- psi1_2) * r0 + (psi1_0 - (q2_id ^ 2 + q0_id ^ 2 * c1)) := by
      dsimp only [z3_rot]; ring
    rw [hid]; have hnp12 : |- psi1_2| ≤ 1 := (by rwa [abs_neg])
    linarith [abs_add_le (psi1_0 * (r2 - 1) + (- psi1_2) * r0)
        (psi1_0 - (q2_id ^ 2 + q0_id ^ 2 * c1)),
      abs_add_le (psi1_0 * (r2 - 1)) ((- psi1_2) * r0),
      abs_mul_le_of_left_le_one hp10_1 (b := r2 - 1), abs_mul_le_of_left_le_one hnp12 (b := r0)]
  set x1_id := (- q0_id) * s1_tr; set x2_id := (- q0_id * q2_id) * (1 - c1)
  have hw1_err : |w1_rot - (c2 * x1_id - s2_tr * x2_id)| ≤ 15 * δ := by
    have hid : w1_rot - (c2 * x1_id - s2_tr * x2_id) =
        c2 * (y1_rot - x1_id) + (- s2_tr) * (z2_rot - x2_id) := by
      dsimp only [w1_rot]; ring
    rw [hid]; have hns2 : |- s2_tr| ≤ 1 := (by rwa [abs_neg])
    linarith [abs_add_le (c2 * (y1_rot - x1_id)) ((- s2_tr) * (z2_rot - x2_id)),
      abs_mul_le_of_left_le_one hc2_1 (b := y1_rot - x1_id),
      abs_mul_le_of_left_le_one hns2 (b := z2_rot - x2_id)]
  have hw2_err : |w2_rot - (s2_tr * x1_id + c2 * x2_id)| ≤ 15 * δ := by
    have hid : w2_rot - (s2_tr * x1_id + c2 * x2_id) =
        s2_tr * (y1_rot - x1_id) + c2 * (z2_rot - x2_id) := by
      dsimp only [w2_rot]; ring
    rw [hid]
    linarith [abs_add_le (s2_tr * (y1_rot - x1_id)) (c2 * (z2_rot - x2_id)),
      abs_mul_le_of_left_le_one hs2_1 (b := y1_rot - x1_id),
      abs_mul_le_of_left_le_one hc2_1 (b := z2_rot - x2_id)]
  have hp20_err : |w2_rot * r0 + z3_rot * r2 - (q2_id ^ 2 + q0_id ^ 2 * c1)| ≤ 13 * δ := by
    have hid : w2_rot * r0 + z3_rot * r2 - (q2_id ^ 2 + q0_id ^ 2 * c1) =
        w2_rot * r0 + z3_rot * (r2 - 1) + (z3_rot - (q2_id ^ 2 + q0_id ^ 2 * c1)) := by ring
    rw [hid]
    linarith [abs_add_le (w2_rot * r0 + z3_rot * (r2 - 1)) (z3_rot - (q2_id ^ 2 + q0_id ^ 2 * c1)),
      abs_add_le (w2_rot * r0) (z3_rot * (r2 - 1)), abs_mul_le_of_left_le_one hw2_1 (b := r0),
      abs_mul_le_of_left_le_one hz3_1 (b := r2 - 1)]
  have hp22_err : |w2_rot * r2 - z3_rot * r0 - (s2_tr * x1_id + c2 * x2_id)| ≤ 17 * δ := by
    have hid : w2_rot * r2 - z3_rot * r0 - (s2_tr * x1_id + c2 * x2_id) =
        w2_rot * (r2 - 1) + (- z3_rot) * r0 + (w2_rot - (s2_tr * x1_id + c2 * x2_id)) := by ring
    rw [hid]; have hnz3 : |- z3_rot| ≤ 1 := (by rwa [abs_neg])
    linarith [abs_add_le (w2_rot * (r2 - 1) + (- z3_rot) * r0)
        (w2_rot - (s2_tr * x1_id + c2 * x2_id)),
      abs_add_le (w2_rot * (r2 - 1)) ((- z3_rot) * r0),
      abs_mul_le_of_left_le_one hw2_1 (b := r2 - 1), abs_mul_le_of_left_le_one hnz3 (b := r0)]
  exact ⟨hp20_err, hw1_err, hp22_err⟩
private lemma p01_angle_enclosure {n val tau_12 : ℕ} {s : ℝ}
    (hn : 200 ≤ n) (htau : tau_12 ≤ 4000000000000)
    (hs0 : 0 ≤ s) (hs65 : s ≤ 65 / √((2 ^ n : ℕ) : ℝ))
    (hserr : |s - √(val : ℝ) / √((2 ^ n : ℕ) : ℝ)| ≤ (1 / (2 : ℝ) ^ 90) / √((2 ^ n : ℕ) : ℝ)) :
    let w_iv := p01Isqrt15 val; let om_iv : WDIVal := (2 * w_iv.1, 2 * w_iv.2)
    let t_iv : WDIVal :=
      (max 0 ((tau_12 : ℤ) * 1000 - 1), (tau_12 : ℤ) * 1000 + 1)
    let th_raw := wdMul om_iv t_iv
    wdMem (2 * (p01StepCount tau_12 (2 ^ n) : ℝ) * Real.arcsin s)
      (max 0 (th_raw.1 - 1), th_raw.2 + 1) := by
  dsimp only; set N : ℕ := 2 ^ n
  have hN_ge : (2 : ℝ) ^ 200 ≤ (N : ℝ) := by
    dsimp only [N]; rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) hn
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hN_ge
  have hsqrtN_ge : (2 : ℝ) ^ 100 ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hN_ge)
  have hsqrtN_pos : (0 : ℝ) < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsqrtN_ge
  set δ : ℝ := 1 / (2 : ℝ) ^ 90
  have hs_half : s ≤ 1 / 2 := hs65.trans ((div_le_iff₀ hsqrtN_pos).mpr (by linarith))
  obtain ⟨harc_lo, harc_hi⟩ := p01_arcsin_bounds hs0 hs_half
  have harc_nn : 0 ≤ Real.arcsin s := hs0.trans harc_lo
  have hs_sq_δ : s ^ 2 ≤ 5 * δ / √(N : ℝ) := by
    have hs_sq : s ^ 2 ≤ 4225 / (N : ℝ) := by
      have h1 : s ^ 2 ≤ (65 / √(N : ℝ)) ^ 2 := pow_le_pow_left₀ hs0 hs65 2
      rw [div_pow, Real.sq_sqrt hN_pos.le] at h1; norm_num at h1; exact h1
    refine hs_sq.trans ?_; rw [div_le_div_iff₀ hN_pos hsqrtN_pos]
    have h1 : (4225 : ℝ) ≤ 5 * δ * (2 : ℝ) ^ 100 := (by dsimp only [δ]; norm_num)
    have h2 : √(N : ℝ) * √(N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
    calc (4225 : ℝ) * √(N : ℝ)
        ≤ (5 * δ * (2 : ℝ) ^ 100) * √(N : ℝ) := mul_le_mul_of_nonneg_right h1 hsqrtN_pos.le
      _ = (5 * δ) * ((2 : ℝ) ^ 100 * √(N : ℝ)) := by ring
      _ ≤ (5 * δ) * (√(N : ℝ) * √(N : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrtN_ge hsqrtN_pos.le)
            (by positivity)
      _ = 5 * δ * (N : ℝ) := by rw [h2]
  have harc_err : |Real.arcsin s - √(val : ℝ) / √(N : ℝ)| ≤ 6 * δ / √(N : ℝ) := by
    have ha : |Real.arcsin s - s| ≤ s ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have htri := abs_add_le (Real.arcsin s - s) (s - √(val : ℝ) / √(N : ℝ))
    rw [sub_add_sub_cancel] at htri
    linarith [show 5 * δ / √(N : ℝ) + δ / √(N : ℝ) = 6 * δ / √(N : ℝ) by ring]
  have hK_le : (p01StepCount tau_12 N : ℝ) ≤ 4 * √(N : ℝ) := by
    have h1 := p01StepCount_le_tau_sqrt tau_12 N
    have htauR : (tau_12 : ℝ) / 1000000000000 ≤ 4 := by
      have hc : (tau_12 : ℝ) ≤ 4000000000000 := (by exact_mod_cast htau); linarith
    exact h1.trans (mul_le_mul_of_nonneg_right htauR hsqrtN_pos.le)
  have hid_mem : wdMem ((2 * √(val : ℝ)) * ((p01StepCount tau_12 N : ℝ) / √(N : ℝ)))
      (wdMul (2 * (p01Isqrt15 val).1, 2 * (p01Isqrt15 val).2)
        (max 0 ((tau_12 : ℤ) * 1000 - 1), (tau_12 : ℤ) * 1000 + 1)) :=
    wdMem_mul (wdMem_scaleNat 2 (wdMem_p01Isqrt15 val)) (p01StepCount_div_sqrt_mem hn htau)
  refine wdMem_pad_nonneg (pad := 1) (by positivity) hid_mem ?_
  have hdiff : |2 * (p01StepCount tau_12 N : ℝ) * Real.arcsin s -
      (2 * √(val : ℝ)) * ((p01StepCount tau_12 N : ℝ) / √(N : ℝ))| ≤ 48 * δ := by
    have heq : 2 * (p01StepCount tau_12 N : ℝ) * Real.arcsin s -
        (2 * √(val : ℝ)) * ((p01StepCount tau_12 N : ℝ) / √(N : ℝ)) =
        (2 * (p01StepCount tau_12 N : ℝ)) * (Real.arcsin s - √(val : ℝ) / √(N : ℝ)) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity)]
    calc (2 * (p01StepCount tau_12 N : ℝ)) * |Real.arcsin s - √(val : ℝ) / √(N : ℝ)|
        ≤ (8 * √(N : ℝ)) * (6 * δ / √(N : ℝ)) :=
          mul_le_mul (by linarith) harc_err (abs_nonneg _) (by positivity)
      _ = 48 * δ := by rw [← mul_div_assoc, div_eq_iff hsqrtN_pos.ne']; ring
  refine hdiff.trans ?_; unfold wdScaleR wdScale; dsimp only [δ]; push_cast; norm_num
private lemma p01_lo15_le_of_wdMem {p : ℝ} {piv : WDIVal} (hp0 : 0 ≤ p) (hmem : wdMem p piv) :
    (((max 0 piv.1).toNat : ℕ) : ℝ) / wdScaleR ≤ p := by
  have hnn : 0 ≤ max 0 piv.1 := le_max_left _ _
  have hcast : (((max 0 piv.1).toNat : ℕ) : ℝ) = ((max 0 piv.1 : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnn
  rw [hcast]; rcases le_total 0 piv.1 with hm | hm
  · rw [max_eq_right hm]; exact hmem.1
  · rw [max_eq_left hm, Int.cast_zero, zero_div]; exact hp0
private lemma ite_none_eq_some {α : Type*} {P : Prop} [Decidable P] {x : Option α} {v : α}
    (h : (if P then none else x) = some v) : ¬ P ∧ x = some v := by
  by_cases hp : P
  · simp only [hp, ↓reduceIte] at h; cases h
  · simp only [hp, ↓reduceIte] at h; exact ⟨hp, h⟩
/-- Full `10 ^ 15`-scaled interval soundness of `p01EvalRowIV15` for all `200 ≤ n`. -/
theorem p01EvalRowIV15_sound {n m r tau1_12 tau2_12 : ℕ} {res : P01RowEvalResult}
    (hn : 200 ≤ n) (hm_hi : m ≤ 1024) (hr_hi : r ≤ 1024)
    (heval : p01EvalRowIV15 m r tau1_12 tau2_12 = some res) :
    let N := 2 ^ n; let K1 := p01StepCount tau1_12 N; let K2 := p01StepCount tau2_12 N
    let psi1 := ((rot3Pos (u1OrbVec N m r))^[K1]) (u0OrbVec N m r)
    let psi2 := ((rot3Neg (u2OrbVec N m r))^[K2]) psi1
    wdMem ((psi2 0) ^ 2) res.p0_iv ∧ wdMem ((psi2 1) ^ 2) res.p1_iv ∧ wdMem ((psi2 2) ^ 2)
      res.p2_iv ∧ (res.p1_lo_15 : ℝ) / wdScaleR ≤ (psi2 1) ^ 2 ∧ (res.p2_lo_15 : ℝ) / wdScaleR ≤
      (psi2 2) ^ 2 := by
  unfold p01EvalRowIV15 p01EvalRowWith at heval; obtain ⟨hg1, heval⟩ := ite_none_eq_some heval
  obtain ⟨hg2, heval⟩ := ite_none_eq_some heval; obtain ⟨hg3, heval⟩ := ite_none_eq_some heval
  dsimp only at heval; obtain ⟨hg4, heval⟩ := ite_none_eq_some heval
  obtain ⟨hg5, heval⟩ := ite_none_eq_some heval
  simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, not_or, Decidable.not_not, not_lt,
    and_assoc] at hg1 hg2 hg4
  rcases hg1 with ⟨hmin_eq, hm2, hr2⟩; rcases hg2 with ⟨htau1, htau2⟩
  rcases hg4 with ⟨hth1_hi, hth2_hi⟩; set N : ℕ := 2 ^ n
  have hN12 : 4096 ≤ N :=
    (by norm_num : 4096 ≤ 2 ^ 12).trans (Nat.pow_le_pow_right (by omega) (by omega : 12 ≤ n))
  have hmr_lt : m + r < N := (by omega); have h2m_lt : 2 * m < N := (by omega)
  have ha2_pos : 1 ≤ m * r := Nat.mul_pos (by omega) (by omega)
  have hb2_pos : 1 ≤ 2 * (m - 1) * (r - 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hab2_pos : 1 ≤ m * r + 2 * (m - 1) * (r - 1) := (by omega)
  obtain ⟨⟨hu1_1_nn, hs1_pos, hu2_1_np, hs2_pos⟩, ⟨hu0_0_bd, hu0_1_bd, hu0_2_bd⟩,
    ⟨hs1_nn, hs1_65, hs1_err⟩, ⟨hu1_0_s1, hu1_2_s1⟩, ⟨hu2_1_nn, hu2_1_65, hu2_1_err⟩,
    ⟨hu2_0_s2, hu2_2_s2⟩⟩ := p01_basis_enclosures hn hm2 hm_hi hr2 hr_hi hmin_eq.le
  set u0 := u0OrbVec N m r; set u1 := u1OrbVec N m r; set u2 := u2OrbVec N m r
  set K1 := p01StepCount tau1_12 N; set K2 := p01StepCount tau2_12 N
  set s1 := √((u1 0) ^ 2 + (u1 2) ^ 2); set s2 := √((u2 0) ^ 2 + (u2 2) ^ 2)
  set Θ1 := 2 * (K1 : ℝ) * Real.arcsin s1; set Θ2 := 2 * (K2 : ℝ) * Real.arcsin (- u2 1)
  have hth1_mem := p01_angle_enclosure hn htau1 hs1_nn hs1_65 hs1_err
  have hc1_s1 := wdTrig_mem (le_max_left 0 _) hth1_hi hth1_mem
  set th2_iv_full : WDIVal := if 0 < tau2_12 then (max 0 ((wdMul (2 * (p01Isqrt15 (2 * (m - 1) *
    (r - 1))).1, 2 * (p01Isqrt15 (2 * (m - 1) * (r - 1))).2) (max 0 ((tau2_12 : ℤ) * 1000 - 1),
    (tau2_12 : ℤ) * 1000 + 1)).1 - 1), (wdMul (2 * (p01Isqrt15 (2 * (m - 1) * (r - 1))).1, 2 *
    (p01Isqrt15 (2 * (m - 1) * (r - 1))).2) (max 0 ((tau2_12 : ℤ) * 1000 - 1), (tau2_12 : ℤ) *
    1000 + 1)).2 + 1) else (0, 0)
  have hcs2_mem :
      let cs2 : WDIVal × WDIVal :=
        if 0 < tau2_12 then wdTrig th2_iv_full else (((wdScale : ℤ), (wdScale : ℤ)), (0, 0))
      wdMem (Real.cos Θ2) cs2.1 ∧ wdMem (Real.sin Θ2) cs2.2 := by
    dsimp only; split_ifs with htau2_pos
    · have hth2_mem := p01_angle_enclosure hn htau2 hu2_1_nn hu2_1_65 hu2_1_err
      dsimp only [th2_iv_full] at hth2_hi ⊢; simp only [htau2_pos, ↓reduceIte] at hth2_hi ⊢
      exact wdTrig_mem (le_max_left 0 _) hth2_hi hth2_mem
    · have htau2_zero : tau2_12 = 0 := (by omega)
      have hΘ2_zero : Θ2 = 0 := by
        dsimp only [Θ2, K2]; rw [htau2_zero, p01StepCount_zero_left]; simp
      rw [hΘ2_zero, Real.cos_zero, Real.sin_zero]; exact ⟨wdMem_one, wdMem_zero⟩
  dsimp only at hcs2_mem; have ha_mem := wdMem_p01Isqrt15 (m * r)
  have hb_mem := wdMem_p01Isqrt15 (2 * (m - 1) * (r - 1))
  have hw_mem := wdMem_p01Isqrt15 (m * r + 2 * (m - 1) * (r - 1))
  have ha_pos := p01Isqrt15_pos ha2_pos; have hw_pos := p01Isqrt15_pos hab2_pos
  generalize wdTrig (max 0 ((wdMul (2 * (p01Isqrt15 (m * r + 2 * (m - 1) * (r - 1))).1,
      2 * (p01Isqrt15 (m * r + 2 * (m - 1) * (r - 1))).2)
      (max 0 ((tau1_12 : ℤ) * 1000 - 1), (tau1_12 : ℤ) * 1000 + 1)).1 - 1),
    (wdMul (2 * (p01Isqrt15 (m * r + 2 * (m - 1) * (r - 1))).1,
      2 * (p01Isqrt15 (m * r + 2 * (m - 1) * (r - 1))).2)
      (max 0 ((tau1_12 : ℤ) * 1000 - 1), (tau1_12 : ℤ) * 1000 + 1)).2 + 1) = cs1 at heval hc1_s1
  generalize (if 0 < tau2_12 then wdTrig th2_iv_full
    else (((wdScale : ℤ), (wdScale : ℤ)), (0, 0))) = cs2 at heval hcs2_mem
  generalize p01Isqrt15 (m * r + 2 * (m - 1) * (r - 1)) = w_iv at heval hw_mem hw_pos
  generalize p01Isqrt15 (2 * (m - 1) * (r - 1)) = b_iv at heval hb_mem
  generalize p01Isqrt15 (m * r) = a_iv at heval ha_mem ha_pos
  rcases cs1 with ⟨c1_iv, s1_iv⟩; rcases cs2 with ⟨c2_iv, s2_iv⟩; dsimp only at hc1_s1 hcs2_mem
  obtain ⟨hc1_mem, hs1_mem⟩ := hc1_s1
  injection heval with hres
  subst hres; dsimp only; set a2 : ℕ := m * r; set b2 : ℕ := 2 * (m - 1) * (r - 1)
  set ab2 : ℕ := a2 + b2; set q0_id : ℝ := - √(a2 : ℝ) / √(ab2 : ℝ)
  set q2_id : ℝ := √(b2 : ℝ) / √(ab2 : ℝ); set x0_id : ℝ := q2_id ^ 2 + q0_id ^ 2 * Real.cos Θ1
  set x1_id : ℝ := (- q0_id) * Real.sin Θ1; set x2_id : ℝ := (- q0_id * q2_id) * (1 - Real.cos Θ1)
  set y1_id : ℝ := Real.cos Θ2 * x1_id - Real.sin Θ2 * x2_id
  set y2_id : ℝ := Real.sin Θ2 * x1_id + Real.cos Θ2 * x2_id
  have ha2R_pos : (0 : ℝ) < (a2 : ℝ) := Nat.cast_pos.mpr ha2_pos
  have hb2R_pos : (0 : ℝ) < (b2 : ℝ) := Nat.cast_pos.mpr hb2_pos
  have hab2R_pos : (0 : ℝ) < (ab2 : ℝ) := Nat.cast_pos.mpr hab2_pos
  have hx0_eq : x0_id = ((b2 : ℝ) + (a2 : ℝ) * Real.cos Θ1) / (ab2 : ℝ) := by
    dsimp only [x0_id, q0_id, q2_id]
    rw [div_pow, div_pow, neg_sq, Real.sq_sqrt ha2R_pos.le, Real.sq_sqrt hb2R_pos.le, Real.sq_sqrt
      hab2R_pos.le]; ring
  have hx0_mem : wdMem x0_id (wdDivFloor ((b2 : ℤ) * (wdScale : ℤ) + (a2 : ℤ) * c1_iv.1) (ab2 : ℤ),
        wdDivCeil ((b2 : ℤ) * (wdScale : ℤ) + (a2 : ℤ) * c1_iv.2) (ab2 : ℤ)) := by
    rw [hx0_eq]; exact wdMem_aff_div_nat hab2_pos hc1_mem
  have ha_div_w_mem : wdMem (- q0_id) (wdDivFloor (a_iv.1 * (wdScale : ℤ)) w_iv.2,
        wdDivCeil (a_iv.2 * (wdScale : ℤ)) w_iv.1) := by
    have hneg : - q0_id = √(a2 : ℝ) / √(ab2 : ℝ) := (by dsimp only [q0_id]; ring); rw [hneg]
    exact wdMem_div_pos (Real.sqrt_pos.mpr hab2R_pos) ha_pos.1.le hw_pos.1 hw_pos.2 ha_mem hw_mem
  have hx1_mem : wdMem x1_id (wdMul (wdDivFloor (a_iv.1 * (wdScale : ℤ)) w_iv.2, wdDivCeil
    (a_iv.2 * (wdScale : ℤ)) w_iv.1) s1_iv) := wdMem_mul ha_div_w_mem hs1_mem
  have hab_div_mem : wdMem (- q0_id * q2_id) (wdDivFloor (wdMul a_iv b_iv).1 (ab2 : ℤ),
        wdDivCeil (wdMul a_iv b_iv).2 (ab2 : ℤ)) := by
    have hprod_eq : - q0_id * q2_id = (√(a2 : ℝ) * √(b2 : ℝ)) / (ab2 : ℝ) := by
      dsimp only [q0_id, q2_id]
      rw [neg_div, neg_neg, div_mul_div_comm, Real.mul_self_sqrt hab2R_pos.le]
    rw [hprod_eq]; exact wdMem_div_nat hab2_pos (wdMem_mul ha_mem hb_mem)
  have hone_m_c1 : wdMem (1 - Real.cos Θ1) ((wdScale : ℤ) - c1_iv.2, (wdScale : ℤ) - c1_iv.1) :=
    wdMem_sub wdMem_one hc1_mem
  have hx2_mem : wdMem x2_id (wdMul (wdDivFloor (wdMul a_iv b_iv).1 (ab2 : ℤ), wdDivCeil (wdMul
    a_iv b_iv).2 (ab2 : ℤ)) ((wdScale : ℤ) - c1_iv.2, (wdScale : ℤ) - c1_iv.1)) := wdMem_mul
    hab_div_mem hone_m_c1
  set x1_s1 := wdMul (wdDivFloor (a_iv.1 * (wdScale : ℤ)) w_iv.2,
    wdDivCeil (a_iv.2 * (wdScale : ℤ)) w_iv.1) s1_iv
  set x2_s1 := wdMul (wdDivFloor (wdMul a_iv b_iv).1 (ab2 : ℤ), wdDivCeil (wdMul a_iv b_iv).2 (ab2
    : ℤ)) ((wdScale : ℤ) - c1_iv.2, (wdScale : ℤ) - c1_iv.1)
  set y_pair : WDIVal × WDIVal := if 0 < tau2_12 then (wdSub (wdMul c2_iv x1_s1) (wdMul s2_iv
    x2_s1), wdAdd (wdMul s2_iv x1_s1) (wdMul c2_iv x2_s1)) else (x1_s1, x2_s1)
  have hy_mem : wdMem y1_id y_pair.1 ∧ wdMem y2_id y_pair.2 := by
    dsimp only [y_pair]; split_ifs with htau2_pos
    · exact ⟨wdMem_sub (wdMem_mul hcs2_mem.1 hx1_mem) (wdMem_mul hcs2_mem.2 hx2_mem),
        wdMem_add (wdMem_mul hcs2_mem.2 hx1_mem) (wdMem_mul hcs2_mem.1 hx2_mem)⟩
    · have htau2_zero : tau2_12 = 0 := (by omega)
      have hΘ2_zero : Θ2 = 0 := by
        dsimp only [Θ2, K2]; rw [htau2_zero, p01StepCount_zero_left]; simp
      dsimp only [y1_id, y2_id]; rw [hΘ2_zero, Real.cos_zero, Real.sin_zero]
      simpa only [one_mul, zero_mul, sub_zero, zero_add] using And.intro hx1_mem hx2_mem
  have hdot0 := dot3_u0_self hm2 hr2 hmin_eq.le hmr_lt
  have hdot1 := dot3_u1_self hm2 hr2 hmin_eq.le hmr_lt h2m_lt
  have hdot01 := dot3_u0_u1 hm2 hr2 hmin_eq.le hmr_lt
  have hdot2 : dot3 u2 u2 = 1 := dot3_cross3_self hdot0 hdot1 hdot01
  set psi1 := ((rot3Pos u1)^[K1]) u0; set psi2 := ((rot3Neg u2)^[K2]) psi1
  have hpsi1_eq := rot3Pos_iter_closed hdot1 hu1_1_nn hs1_pos K1 u0
  have hpsi2_eq := rot3Neg_iter_closed hdot2 hu2_1_np hs2_pos K2 psi1
  dsimp only at hpsi1_eq hpsi2_eq; have heven2 : (-1 : ℝ) ^ K2 = 1 := p01StepCount_even tau2_12 N
  have hq_pyth : (u1 0 / s1) ^ 2 + (u1 2 / s1) ^ 2 = 1 := by
    have hs1_sq : (u1 0) ^ 2 + (u1 2) ^ 2 = s1 ^ 2 := (Real.sq_sqrt (by positivity)).symm
    rw [div_pow, div_pow, ← add_div, hs1_sq, div_self (pow_ne_zero 2 hs1_pos.ne')]
  have hqid_pyth : q0_id ^ 2 + q2_id ^ 2 = 1 := by
    dsimp only [q0_id, q2_id]
    rw [div_pow, div_pow, neg_sq, Real.sq_sqrt ha2R_pos.le, Real.sq_sqrt hb2R_pos.le,
      Real.sq_sqrt hab2R_pos.le, ← add_div]
    have hab_cast : (a2 : ℝ) + (b2 : ℝ) = (ab2 : ℝ) := (by dsimp only [ab2]; push_cast; rfl)
    rw [hab_cast, div_self hab2R_pos.ne']
  have hr_pyth : (u2 0 / s2) ^ 2 + (u2 2 / s2) ^ 2 = 1 := by
    have hs2_sq : (u2 0) ^ 2 + (u2 2) ^ 2 = s2 ^ 2 := (Real.sq_sqrt (by positivity)).symm
    rw [div_pow, div_pow, ← add_div, hs2_sq, div_self (pow_ne_zero 2 hs2_pos.ne')]
  have hu0_pyth : (u0 0) ^ 2 + (u0 1) ^ 2 + (u0 2) ^ 2 = 1 := by
    unfold dot3 at hdot0; linarith [sq (u0 0), sq (u0 1), sq (u0 2)]
  have herr_all := p01_stage2_amp_errors hu0_pyth hq_pyth hqid_pyth hr_pyth
    (Real.cos_sq_add_sin_sq Θ1) (Real.cos_sq_add_sin_sq Θ2)
    hu0_0_bd hu0_1_bd hu0_2_bd hu1_0_s1 hu1_2_s1 hu2_0_s2 hu2_2_s2
  dsimp only at herr_all; obtain ⟨herr0, herr1, herr2⟩ := herr_all
  have hpsi1_coords : psi1 0 = ((u0 1) * Real.sin Θ1 + ((u1 0 / s1) * u0 0 + (u1 2 / s1) * u0 2) *
    Real.cos Θ1) * (u1 0 / s1) + ((u1 2 / s1) * u0 0 - (u1 0 / s1) * u0 2) * (u1 2 / s1) ∧ psi1 1
    = (u0 1) * Real.cos Θ1 - ((u1 0 / s1) * u0 0 + (u1 2 / s1) * u0 2) * Real.sin Θ1 ∧ psi1 2 =
    ((u0 1) * Real.sin Θ1 + ((u1 0 / s1) * u0 0 + (u1 2 / s1) * u0 2) * Real.cos Θ1) * (u1 2 /
    s1) - ((u1 2 / s1) * u0 0 - (u1 0 / s1) * u0 2) * (u1 0 / s1) := by
    refine ⟨?_, ?_, ?_⟩
    · have h := congrFun hpsi1_eq 0; dsimp only [psi1, Θ1, s1] at h ⊢; rw [h, vec3_zero]; ring
    · have h := congrFun hpsi1_eq 1; dsimp only [psi1, Θ1, s1] at h ⊢; rw [h, vec3_one]; ring
    · have h := congrFun hpsi1_eq 2; dsimp only [psi1, Θ1, s1] at h ⊢; rw [h, vec3_two]; ring
  have hpsi2_0_eq : psi2 0 = ((psi1 1) * Real.sin Θ2 + ((u2 0 / s2) * psi1 0 + (u2 2 / s2) * psi1
    2) * Real.cos Θ2) * (u2 0 / s2) + ((u2 2 / s2) * psi1 0 - (u2 0 / s2) * psi1 2) * (u2 2 /
    s2) := by
    have h := congrFun hpsi2_eq 0; dsimp only [psi2, Θ2, s2] at h ⊢
    rw [h, vec3_zero, heven2, one_mul]; ring
  have hpsi2_1_eq : psi2 1 = (psi1 1) * Real.cos Θ2 - ((u2 0 / s2) * psi1 0 + (u2 2 / s2) * psi1
    2) * Real.sin Θ2 := by
    have h := congrFun hpsi2_eq 1; dsimp only [psi2, Θ2, s2] at h ⊢; rw [h, vec3_one]; ring
  have hpsi2_2_eq : psi2 2 = ((psi1 1) * Real.sin Θ2 + ((u2 0 / s2) * psi1 0 + (u2 2 / s2) * psi1
    2) * Real.cos Θ2) * (u2 2 / s2) - ((u2 2 / s2) * psi1 0 - (u2 0 / s2) * psi1 2) * (u2 0 /
    s2) := by
    have h := congrFun hpsi2_eq 2; dsimp only [psi2, Θ2, s2] at h ⊢
    rw [h, vec3_two, heven2, one_mul]; ring
  rw [← hpsi1_coords.1, ← hpsi1_coords.2.1, ← hpsi1_coords.2.2] at herr0 herr1 herr2
  rw [← hpsi2_0_eq] at herr0; rw [← hpsi2_1_eq] at herr1; rw [← hpsi2_2_eq] at herr2
  have h17_pad : 17 * (1 / (2 : ℝ) ^ 90) ≤ ((1 : ℤ) : ℝ) / wdScaleR := by
    unfold wdScaleR wdScale; push_cast; norm_num
  have h15_pad : 15 * (1 / (2 : ℝ) ^ 90) ≤ ((1 : ℤ) : ℝ) / wdScaleR := (by linarith)
  have h13_pad : 13 * (1 / (2 : ℝ) ^ 90) ≤ ((1 : ℤ) : ℝ) / wdScaleR := (by linarith)
  have hf0_mem := wdMem_pad (pad := 1) hx0_mem (herr0.trans h13_pad)
  have hf1_mem := wdMem_pad (pad := 1) hy_mem.1 (herr1.trans h15_pad)
  have hf2_mem := wdMem_pad (pad := 1) hy_mem.2 (herr2.trans h17_pad)
  have hp0_mem := wdMem_sq hf0_mem; have hp1_mem := wdMem_sq hf1_mem
  have hp2_mem := wdMem_sq hf2_mem
  exact ⟨hp0_mem, hp1_mem, hp2_mem, p01_lo15_le_of_wdMem (sq_nonneg _) hp1_mem,
    p01_lo15_le_of_wdMem (sq_nonneg _) hp2_mem⟩
/-- Direct `10 ^ 12`-scaled hit-probability lower-bound soundness for all `200 ≤ n`. -/
theorem p01EvalRowLo15_sound {n m r tau1_12 tau2_12 p1_lo_15 p2_lo_15 : ℕ}
    (hn : 200 ≤ n) (hm_hi : m ≤ 1024) (hr_hi : r ≤ 1024)
    (heval : p01EvalRowLo15 m r tau1_12 tau2_12 = some (p1_lo_15, p2_lo_15)) :
    let N := 2 ^ n; let K1 := p01StepCount tau1_12 N; let K2 := p01StepCount tau2_12 N
    let psi1 := ((rot3Pos (u1OrbVec N m r))^[K1]) (u0OrbVec N m r)
    let psi2 := ((rot3Neg (u2OrbVec N m r))^[K2]) psi1
    (p1_lo_15 : ℝ) / wdScaleR ≤ (psi2 1) ^ 2 ∧ (p2_lo_15 : ℝ) / wdScaleR ≤ (psi2 2) ^ 2 := by
  unfold p01EvalRowLo15 at heval; rcases Option.mem_map.mp heval with ⟨res, hres, hp⟩
  injection hp with hp1 hp2
  subst hp1 hp2; have hs := p01EvalRowIV15_sound hn hm_hi hr_hi hres; exact ⟨hs.2.2.2.1, hs.2.2.2.2⟩
/-- Single-step intertwining of `(r1SymMat ∘ symZ)` with `rot3Pos` on `P01Subset N m`. -/
theorem r1SymMat_step_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)} (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card)
    (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) (x : Fin 3 → ℝ) : r1SymMat N m *ᵥ (fun E :
    P01Subset N m ↦ (-1 : ℝ) ^ (E.1 ∩ R).card * orbEmbed3 N m R x E) = orbEmbed3 N m R (rot3Pos
    (u1OrbVec N m R.card) x) := by
  rw [symZ_orbEmbed3 hmin, r1SymMat_mulVec_orbEmbed3 hm2 hr2 hmin hmrN]; rfl
/-- Single-step intertwining of `(r01SymMat ∘ symZ)` with `rot3Neg` on `P01Subset N m`. -/
theorem r01SymMat_step_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)} (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card)
    (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) (h2m : 2 * m < N) (x : Fin 3 → ℝ) :
    r01SymMat N m *ᵥ (fun E : P01Subset N m ↦ (-1 : ℝ) ^ (E.1 ∩ R).card * orbEmbed3 N m R x E) =
    orbEmbed3 N m R (rot3Neg (u2OrbVec N m R.card) x) := by
  rw [symZ_orbEmbed3 hmin, r01SymMat_mulVec_orbEmbed3 hm2 hr2 hmin hmrN h2m]; rfl
end Sec_P01Rot
section Sec_P01CertAndWrapper
open QuantumComputation.Specs Operator ResourceCounting Real QProg.Notation
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat
/-! ## Section 5: `10 ^ 15` Certificate Verifier & Certified `k = 2` Portfolio -/
/-- Certified 2-stage Jordan-walk `10 ^ 12` schedule and `10 ^ 15` potential row. -/
structure P01CertRow where
  r : ℕ
  tau1_12 : ℕ
  tau2_12 : ℕ
  tauSum_12 : ℕ
  v_15 : ℕ
  iv : P01RowEvalResult
  deriving DecidableEq
/-- Bounded-fuel integer Newton `isqrt` loop. -/
def p01NewtonLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, target, g =>
    if g = 0 then 0
    else
      let next := (g + target / g) / 2
      if next < g then p01NewtonLoop fuel target next else g
/-- Fast `10 ^ 15`-scaled integer square root seed. -/
def p01FastSqrt (val : ℕ) : ℕ :=
  if val = 0 then 0
  else p01NewtonLoop 20 (val * (wdScale * wdScale)) ((val + 1) * wdScale)
/-- Fast `10 ^ 15`-scaled square-root interval enclosure. -/
def p01FastIsqrt15 (val : ℕ) : WDIVal :=
  let target := val * (wdScale * wdScale)
  let rt := p01FastSqrt val
  ((rt : ℤ), if rt * rt = target then (rt : ℤ) else (rt : ℤ) + 1)
/-- Kernel witness certifying `p01FastSqrt val`. -/
def p01CheckFastIsqrt (val : ℕ) : Bool :=
  let target := val * (wdScale * wdScale)
  let rt := p01FastSqrt val
  decide (rt * rt ≤ target) && decide (target < (rt + 1) * (rt + 1))
private lemma p01FastIsqrt15_eq {val : ℕ} (h : p01CheckFastIsqrt val = true) :
    p01FastIsqrt15 val = p01Isqrt15 val := by
  simp only [p01CheckFastIsqrt, Bool.and_eq_true, decide_eq_true_eq] at h
  set target := val * (wdScale * wdScale); set rt := p01FastSqrt val; set s := Nat.sqrt target
  have hs1 : s * s ≤ target := Nat.sqrt_le target
  have hs2 : target < (s + 1) * (s + 1) := Nat.lt_succ_sqrt target
  have hrt_lt : rt < s + 1 := (by nlinarith [h.1, hs2])
  have hs_lt : s < rt + 1 := (by nlinarith [hs1, h.2]); have heq : rt = s := (by omega)
  unfold p01FastIsqrt15 p01Isqrt15; dsimp only
  change ((rt : ℤ), if rt * rt = target then (rt : ℤ) else (rt : ℤ) + 1) =
    ((s : ℤ), if s * s = target then (s : ℤ) else (s : ℤ) + 1)
  rw [heq]
/-- Fast Newton-`isqrt` Jordan rotation row evaluator. -/
def p01FastEvalRow (m r tau1_12 tau2_12 : ℕ) : Option P01RowEvalResult :=
  p01EvalRowWith p01FastIsqrt15 m r tau1_12 tau2_12
private lemma p01FastEvalRow_eq {m r tau1_12 tau2_12 : ℕ} (ha : p01CheckFastIsqrt (m * r) = true)
    (hb : p01CheckFastIsqrt (2 * (m - 1) * (r - 1)) = true)
    (hab : p01CheckFastIsqrt (m * r + 2 * (m - 1) * (r - 1)) = true) :
    p01FastEvalRow m r tau1_12 tau2_12 = p01EvalRowIV15 m r tau1_12 tau2_12 := by
  unfold p01FastEvalRow p01EvalRowIV15 p01EvalRowWith; dsimp only
  rw [p01FastIsqrt15_eq ha, p01FastIsqrt15_eq hb, p01FastIsqrt15_eq hab]
/-- Certified `r = 2` row for `(2, 2)` (`10 ^ 12` `tau`, `10 ^ 15` `V`). -/
def p01RowM2R2 : P01CertRow := ⟨2, 427516603413, 120096640202, 547613243615, 632073517091934,
    ⟨(2094395069859288, 2094395069859302), (339684594738216, 339684594738225),
     (0, 1), (185848815028156, 185848815925097),
     (814151183316794, 814151184740589), 185848815028156, 814151183316794⟩⟩
/-- Certified `r = 2` row for `(4, 2)` (`10 ^ 12` `tau`, `10 ^ 15` `V`). -/
def p01RowM4R2 : P01CertRow := ⟨2, 323233426409, 36632000017, 359865426426, 396444684288751,
    ⟨(2418857475150963, 2418857475150981), (179459416598543, 179459416598556),
     (123, 125), (113830120274435, 113830121406197),
     (886169877259312, 886169879549013), 113830120274435, 886169877259312⟩⟩
/-- Certified `r = 2` row for `(8, 2)` (`10 ^ 12` `tau`, `10 ^ 15` `V`). -/
def p01RowM8R2 : P01CertRow := ⟨2, 240653479807, 6283720263, 246937200070, 268660763361777,
    ⟨(2636226788648145, 2636226788648171), (47023056676941, 47023056676959),
     (1910, 1915), (95602304587427, 95602305889682),
     (904397692393730, 904397695135094), 95602304587427, 904397692393730⟩⟩
/-- Certified `10 ^ 15`-scaled potential `V(m, r)` on `m ∈ {2, 4, 8}`, `r ∈ {0, 1, 2}`. -/
def p01CertVPot (m r : ℕ) : ℕ :=
  if m = 2 then (if r = 0 then 0 else if r = 1 then 454456878931536 else 632073517091934)
  else if m = 4 then (if r = 0 then 0 else if r = 1 then 321349540849363 else 396444684288751)
  else if m = 8 then (if r = 0 then 0 else if r = 1 then 227228439465768 else 268660763361777)
  else 0
/-- Certified `r = 2` row lookup for `m ∈ {2, 4, 8}`. -/
def p01CertGetRow (m _r : ℕ) : P01CertRow :=
  if m = 2 then p01RowM2R2
  else if m = 4 then p01RowM4R2
  else p01RowM8R2
/-- Selected `k = 2` degree-`0, 1` Johnson-walk cells `(2, 2)`, `(4, 2)`, and `(8, 2)`. -/
def isSw32Cell (m k : ℕ) : Prop := k = 2 ∧ (m = 2 ∨ m = 4 ∨ m = 8)
/-- Coprime `10 ^ 16`-scale `(num, den)` relative-cost pairs on `(2, 2), (4, 2), (8, 2)`. -/
def p01RelCostPair (m k : ℕ) : ℕ × ℕ :=
  if m = 2 ∧ k = 2 then (6667024075121291, 10000000000000000)
  else if m = 4 ∧ k = 2 then (2956868632351389, 5000000000000000)
  else if m = 8 ∧ k = 2 then (2833796590014241, 5000000000000000)
  else (1, 1)
/-- Exact rational relative cost `num / den` on `(2, 2)`, `(4, 2)`, and `(8, 2)`. -/
def p01CertRelCost (m k : ℕ) : ℚ≥0 := NNRat.divNat (p01RelCostPair m k).1 (p01RelCostPair m k).2
/-- Newton-`isqrt` soundness sub-check (`2` `&&`s, `WHNF19`-safe). -/
def p01CheckRowIsqrt (m r : ℕ) : Bool := p01CheckFastIsqrt (m * r) &&
  p01CheckFastIsqrt (2 * (m - 1) * (r - 1)) && p01CheckFastIsqrt (m * r + 2 * (m - 1) * (r - 1))
/-- Schedule and potential monotonicity sub-check (`2` `&&`s, `WHNF19`-safe). -/
def p01CheckRowMeta (r v1 v2 : ℕ) (row : P01CertRow) : Bool :=
  decide (row.r = r ∧ row.tau1_12 ≤ 4000000000000) &&
  decide (row.tau2_12 ≤ 4000000000000 ∧ row.tau1_12 + row.tau2_12 = row.tauSum_12) &&
  decide (v1 ≤ row.v_15 ∧ v2 ≤ row.v_15)
/-- Drift inequality and `10 ^ 15` interval-evaluator sub-check (`3` `&&`s, `WHNF19`-safe). -/
def p01CheckRowEval (m r v1 v2 : ℕ) (row : P01CertRow) : Bool :=
  decide (p01CertVPot m r = row.v_15) && decide (0 < row.iv.p1_lo_15 + row.iv.p2_lo_15) &&
  decide (row.tauSum_12 * 1000000000000000000 <
    row.iv.p1_lo_15 * (row.v_15 - v1) + row.iv.p2_lo_15 * (row.v_15 - v2)) &&
  decide (p01FastEvalRow m r row.tau1_12 row.tau2_12 = some row.iv)
/-- Base `r = 1` fallback drift check (`2` `&&`s, `WHNF19`-safe). -/
def p01CheckEigOne (m : ℕ) : Bool := p01CheckFastIsqrt m && decide (0 < (p01FastIsqrt15 m).1) &&
  decide (1285398163397449 * 1000000000000000 ≤ 2 * p01CertVPot m 1 * (p01FastIsqrt15 m).1.toNat)
/-- Top-level `k = 2` relative-cost cap check (`3` `&&`s, `WHNF19`-safe). -/
def p01CheckCellTop (m k : ℕ) : Bool :=
  let nd := p01RelCostPair m k
  p01CheckFastIsqrt m && decide (0 < nd.2) && decide (0 < (p01FastIsqrt15 m).1) &&
  decide (2 * p01CertVPot m k * nd.2 * (p01FastIsqrt15 m).2.toNat ≤
    nd.1 * 785398163397448 * 3414213562373095)
private def p01CertRestOk : Bool :=
  (((p01CheckRowMeta 2 (p01CertVPot 2 1) (p01CertVPot 2 0) (p01CertGetRow 2 2) &&
  (p01CheckRowEval 2 2 (p01CertVPot 2 1) (p01CertVPot 2 0) (p01CertGetRow 2 2) &&
  p01CheckRowIsqrt 4 2)) &&
  ((p01CheckRowMeta 2 (p01CertVPot 4 1) (p01CertVPot 4 0) (p01CertGetRow 4 2) &&
  p01CheckRowEval 4 2 (p01CertVPot 4 1) (p01CertVPot 4 0) (p01CertGetRow 4 2)) &&
  (p01CheckRowIsqrt 8 2 &&
  p01CheckRowMeta 2 (p01CertVPot 8 1) (p01CertVPot 8 0) (p01CertGetRow 8 2)))) &&
  ((p01CheckRowEval 8 2 (p01CertVPot 8 1) (p01CertVPot 8 0) (p01CertGetRow 8 2) &&
  (p01CheckEigOne 2 && p01CheckEigOne 4)) && ((p01CheckEigOne 8 && p01CheckCellTop 2 2) &&
  (p01CheckCellTop 4 2 && p01CheckCellTop 8 2))))
private theorem p01Row_eval_pair :
    (p01CheckRowIsqrt 2 2 && p01CertRestOk) = true := by decide +kernel
private lemma p01Band {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  (Bool.and_eq_true a b).mp h
private theorem p01Row_2_2_isqrt : p01CheckRowIsqrt 2 2 = true := (p01Band p01Row_eval_pair).1
private theorem p01Cert_rest : p01CertRestOk = true := (p01Band p01Row_eval_pair).2
private theorem p01Row_2_2_meta :
    p01CheckRowMeta 2 (p01CertVPot 2 1) (p01CertVPot 2 0) (p01CertGetRow 2 2) = true :=
  (p01Band (p01Band (p01Band p01Cert_rest).1).1).1
private theorem p01Row_2_2_eval :
    p01CheckRowEval 2 2 (p01CertVPot 2 1) (p01CertVPot 2 0) (p01CertGetRow 2 2) = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).1).1).2).1
private theorem p01Row_4_2_isqrt : p01CheckRowIsqrt 4 2 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).1).1).2).2
private theorem p01Row_4_2_meta :
    p01CheckRowMeta 2 (p01CertVPot 4 1) (p01CertVPot 4 0) (p01CertGetRow 4 2) = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).1).2).1).1
private theorem p01Row_4_2_eval :
    p01CheckRowEval 4 2 (p01CertVPot 4 1) (p01CertVPot 4 0) (p01CertGetRow 4 2) = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).1).2).1).2
private theorem p01Row_8_2_isqrt : p01CheckRowIsqrt 8 2 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).1).2).2).1
private theorem p01Row_8_2_meta :
    p01CheckRowMeta 2 (p01CertVPot 8 1) (p01CertVPot 8 0) (p01CertGetRow 8 2) = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).1).2).2).2
private theorem p01Row_8_2_eval :
    p01CheckRowEval 8 2 (p01CertVPot 8 1) (p01CertVPot 8 0) (p01CertGetRow 8 2) = true :=
  (p01Band (p01Band (p01Band p01Cert_rest).2).1).1
private theorem p01CheckEig_2_true : p01CheckEigOne 2 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).2).1).2).1
private theorem p01CheckEig_4_true : p01CheckEigOne 4 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).2).1).2).2
private theorem p01CheckEig_8_true : p01CheckEigOne 8 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).2).2).1).1
private theorem p01CheckTop_2_2_true : p01CheckCellTop 2 2 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).2).2).1).2
private theorem p01CheckTop_4_2_true : p01CheckCellTop 4 2 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).2).2).2).1
private theorem p01CheckTop_8_2_true : p01CheckCellTop 8 2 = true :=
  (p01Band (p01Band (p01Band (p01Band p01Cert_rest).2).2).2).2
private lemma p01CertVPot_zero_all (m : ℕ) : p01CertVPot m 0 = 0 := by
  unfold p01CertVPot; split_ifs <;> omega
private lemma p01CertVPot_mono_m2 {r₁ r₂ : ℕ} (h12 : r₁ ≤ r₂) :
    p01CertVPot 2 r₁ ≤ p01CertVPot 2 r₂ := by
  unfold p01CertVPot; norm_num; split_ifs <;> omega
private lemma p01CertVPot_mono_m4 {r₁ r₂ : ℕ} (h12 : r₁ ≤ r₂) :
    p01CertVPot 4 r₁ ≤ p01CertVPot 4 r₂ := by
  unfold p01CertVPot; norm_num; split_ifs <;> omega
private lemma p01CertVPot_mono_m8 {r₁ r₂ : ℕ} (h12 : r₁ ≤ r₂) :
    p01CertVPot 8 r₁ ≤ p01CertVPot 8 r₂ := by
  unfold p01CertVPot; norm_num; split_ifs <;> omega
attribute [irreducible] p01NewtonLoop p01CertVPot p01CertGetRow
/-- Real potential `V(m, r) = p01CertVPot m r / wdScaleR`. -/
noncomputable def p01CertV (m r : ℕ) : ℝ := (p01CertVPot m r : ℝ) / wdScaleR
/-- Real stage time sum `tauSum(m, r) = (p01CertGetRow m r).tauSum_12 / 10 ^ 12`. -/
noncomputable def p01CertTauSum (m r : ℕ) : ℝ := ((p01CertGetRow m r).tauSum_12 : ℝ) / 1000000000000
/-- Real hit-probability lower bounds `pLo(m, r, w)` for `w ∈ {1, 2}`. -/
noncomputable def p01CertPLo (m r w : ℕ) : ℝ :=
  let row := p01CertGetRow m r
  if w = 1 then (row.iv.p1_lo_15 : ℝ) / wdScaleR
  else if w = 2 then (row.iv.p2_lo_15 : ℝ) / wdScaleR
  else 0
theorem p01CertV_zero (m : ℕ) : p01CertV m 0 = 0 := by simp [p01CertV, p01CertVPot_zero_all]
theorem p01CertV_mono {m k r₁ r₂ : ℕ} (hcell : isSw32Cell m k)
    (h12 : r₁ ≤ r₂) (_h2k : r₂ ≤ k) : p01CertV m r₁ ≤ p01CertV m r₂ := by
  have hB : (0 : ℝ) ≤ wdScaleR := (by unfold wdScaleR wdScale; positivity); unfold p01CertV
  refine div_le_div_of_nonneg_right ?_ hB; rcases hcell with ⟨_, rfl | rfl | rfl⟩
  · exact_mod_cast p01CertVPot_mono_m2 h12
  · exact_mod_cast p01CertVPot_mono_m4 h12
  · exact_mod_cast p01CertVPot_mono_m8 h12
theorem p01Cert_hV_eig {m k : ℕ} (hcell : isSw32Cell m k) :
    (π / 8 + 1 / 4) / √((m : ℝ) * (1 : ℝ)) < p01CertV m 1 - p01CertV m 0 := by
  have heig : p01CheckEigOne m = true := by
    rcases hcell with ⟨_, rfl | rfl | rfl⟩
    · exact p01CheckEig_2_true
    · exact p01CheckEig_4_true
    · exact p01CheckEig_8_true
  simp only [p01CheckEigOne, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at heig
  rcases heig with ⟨hchk, hsq1_pos, hineqN⟩; rw [p01FastIsqrt15_eq hchk] at hsq1_pos hineqN
  have hmem := wdMem_p01Isqrt15 m; set sqLoNat : ℕ := (p01Isqrt15 m).1.toNat
  have hsqLo_eq : (sqLoNat : ℝ) = ((p01Isqrt15 m).1 : ℝ) := by
    dsimp only [sqLoNat]; exact_mod_cast Int.toNat_of_nonneg hsq1_pos.le
  have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have hB : (0 : ℝ) < wdScaleR := (by rw [hB_eq]; positivity)
  have hsqLo_pos : (0 : ℝ) < (sqLoNat : ℝ) := (by rw [hsqLo_eq]; exact_mod_cast hsq1_pos)
  have hsqLo_le : (sqLoNat : ℝ) / wdScaleR ≤ √(m : ℝ) := (by rw [hsqLo_eq]; exact hmem.1)
  have hm_sqrt_pos : 0 < √(m : ℝ) := lt_of_lt_of_le (div_pos hsqLo_pos hB) hsqLo_le
  have hpi8 : π / 8 + 1 / 4 < (1285398163397449 : ℝ) / (2 * wdScaleR) := by
    have hp := pi4_lt_p01; rw [hB_eq] at hp ⊢; linarith
  rw [mul_one, p01CertV_zero, sub_zero, p01CertV, div_lt_iff₀ hm_sqrt_pos]
  have hineqR : (1285398163397449 : ℝ) * 1000000000000000 ≤
      2 * (p01CertVPot m 1 : ℝ) * (sqLoNat : ℝ) := by exact_mod_cast hineqN
  have hv_nn : (0 : ℝ) ≤ (p01CertVPot m 1 : ℝ) / wdScaleR := div_nonneg (Nat.cast_nonneg _) hB.le
  calc π / 8 + 1 / 4 < (1285398163397449 : ℝ) / (2 * wdScaleR) := hpi8
    _ ≤ ((p01CertVPot m 1 : ℝ) / wdScaleR) * ((sqLoNat : ℝ) / wdScaleR) := by
        rw [hB_eq, div_mul_div_comm, div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [hineqR]
    _ ≤ ((p01CertVPot m 1 : ℝ) / wdScaleR) * √(m : ℝ) := mul_le_mul_of_nonneg_left hsqLo_le hv_nn
private lemma isSw32Cell_min_eq_two {m k r : ℕ} (hcell : isSw32Cell m k)
    (hr2 : 2 ≤ r) (hrk : r ≤ k) : min m r = 2 := by
  rcases hcell with ⟨rfl, rfl | rfl | rfl⟩ <;> omega
private lemma p01CertGetRow_props {m k r : ℕ} (hcell : isSw32Cell m k) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    let row := p01CertGetRow m r
    p01CertVPot m r = row.v_15 ∧ row.r = r ∧ row.tau1_12 ≤ 4000000000000 ∧ row.tau2_12 ≤
      4000000000000 ∧ row.tau1_12 + row.tau2_12 = row.tauSum_12 ∧ p01CertVPot m (r - 1) ≤ row.v_15
      ∧ p01CertVPot m (r - 2) ≤ row.v_15 ∧ 0 < row.iv.p1_lo_15 + row.iv.p2_lo_15 ∧ row.tauSum_12 *
      1000000000000000000 < row.iv.p1_lo_15 * (row.v_15 - p01CertVPot m (r - 1)) +
      row.iv.p2_lo_15 * (row.v_15 - p01CertVPot m (r - 2)) ∧ p01EvalRowIV15 m r row.tau1_12
      row.tau2_12 = some row.iv := by
  rcases hcell with ⟨rfl, hm⟩; have hr_eq : r = 2 := (by omega); subst hr_eq
  have htriple : p01CheckRowIsqrt m 2 = true ∧
      p01CheckRowMeta 2 (p01CertVPot m 1) (p01CertVPot m 0) (p01CertGetRow m 2) = true ∧
      p01CheckRowEval m 2 (p01CertVPot m 1) (p01CertVPot m 0) (p01CertGetRow m 2) = true := by
    rcases hm with rfl | rfl | rfl
    · exact ⟨p01Row_2_2_isqrt, p01Row_2_2_meta, p01Row_2_2_eval⟩
    · exact ⟨p01Row_4_2_isqrt, p01Row_4_2_meta, p01Row_4_2_eval⟩
    · exact ⟨p01Row_8_2_isqrt, p01Row_8_2_meta, p01Row_8_2_eval⟩
  rcases htriple with ⟨hisq, hmeta, hev⟩; simp only [p01CheckRowIsqrt, Bool.and_eq_true] at hisq
  simp only [p01CheckRowMeta, Bool.and_eq_true, decide_eq_true_eq] at hmeta
  simp only [p01CheckRowEval, Bool.and_eq_true, decide_eq_true_eq] at hev
  rcases hisq with ⟨⟨ha, hb⟩, hab⟩; rcases hmeta with ⟨⟨⟨hr, ht1⟩, ⟨ht2, hts⟩⟩, ⟨hv1, hv2⟩⟩
  rcases hev with ⟨⟨⟨hv_eq, hp⟩, hdr⟩, hfev⟩; rw [p01FastEvalRow_eq ha hb hab] at hfev
  exact ⟨hv_eq, hr, ht1, ht2, hts, hv1, hv2, hp, hdr, hfev⟩
theorem p01CertGetRow_valid {m k r : ℕ} (hcell : isSw32Cell m k) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    let row := p01CertGetRow m r
    row.r = r ∧ row.tau1_12 ≤ 4000000000000 ∧ row.tau2_12 ≤ 4000000000000 ∧ row.tau1_12 +
      row.tau2_12 = row.tauSum_12 ∧ p01EvalRowIV15 m r row.tau1_12 row.tau2_12 = some row.iv ∧
      p01EvalRowLo15 m r row.tau1_12 row.tau2_12 = some (row.iv.p1_lo_15, row.iv.p2_lo_15) := by
  obtain ⟨_, hr_eq, ht1, ht2, htsum, _, _, _, _, heval⟩ := p01CertGetRow_props hcell hr2 hrk
  refine ⟨hr_eq, ht1, ht2, htsum, heval, ?_⟩; simp [p01EvalRowLo15, heval]
theorem p01CertPLo_nonneg (m r w : ℕ) : 0 ≤ p01CertPLo m r w := by
  have hB : (0 : ℝ) < wdScaleR := (by unfold wdScaleR wdScale; positivity)
  unfold p01CertPLo; dsimp only; split_ifs <;> positivity
private lemma sum_Icc_one_two (f : ℕ → ℝ) : ∑ w ∈ Finset.Icc 1 2, f w = f 1 + f 2 := by
  have hset : Finset.Icc (1 : ℕ) 2 = {1, 2} := (by ext x; simp; omega)
  rw [hset, Finset.sum_pair (by omega)]
theorem p01CertPLo_sum_pos {m k r : ℕ} (hcell : isSw32Cell m k) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    0 < ∑ w ∈ Finset.Icc 1 (min m r), p01CertPLo m r w := by
  rw [isSw32Cell_min_eq_two hcell hr2 hrk, sum_Icc_one_two]
  obtain ⟨_, _, _, _, _, _, _, hp_pos, _, _⟩ := p01CertGetRow_props hcell hr2 hrk
  have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have h1 : p01CertPLo m r 1 = ((p01CertGetRow m r).iv.p1_lo_15 : ℝ) / wdScaleR := by
    unfold p01CertPLo; norm_num
  have h2 : p01CertPLo m r 2 = ((p01CertGetRow m r).iv.p2_lo_15 : ℝ) / wdScaleR := by
    unfold p01CertPLo; norm_num
  have hpR : (0 : ℝ) < ((p01CertGetRow m r).iv.p1_lo_15 : ℝ) +
      ((p01CertGetRow m r).iv.p2_lo_15 : ℝ) := by exact_mod_cast hp_pos
  rw [h1, h2, hB_eq]; linarith
theorem p01Cert_hstages_len {m k r : ℕ} (hcell : isSw32Cell m k)
    (hr2 : 2 ≤ r) (hrk : r ≤ k) (N : ℕ) :
    let row := p01CertGetRow m r
    ((p01StepCount row.tau1_12 N + p01StepCount row.tau2_12 N : ℕ) : ℝ) ≤
      p01CertTauSum m r * √(N : ℝ) := by
  dsimp only; set row := p01CertGetRow m r
  have htsum : row.tau1_12 + row.tau2_12 = row.tauSum_12 :=
    (p01CertGetRow_valid hcell hr2 hrk).2.2.2.1
  have h1 := p01StepCount_le_tau_sqrt row.tau1_12 N
  have h2 := p01StepCount_le_tau_sqrt row.tau2_12 N; unfold p01CertTauSum
  have hsumR : (row.tauSum_12 : ℝ) = (row.tau1_12 : ℝ) + (row.tau2_12 : ℝ) := by
    exact_mod_cast htsum.symm
  push_cast; rw [show p01CertGetRow m r = row from rfl, hsumR]; linarith
theorem p01Cert_hdrift_lt {m k r : ℕ} (hcell : isSw32Cell m k) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    p01CertTauSum m r < ∑ w ∈ Finset.Icc 1 (min m r),
        p01CertPLo m r w * (p01CertV m r - p01CertV m (r - w)) := by
  rw [isSw32Cell_min_eq_two hcell hr2 hrk, sum_Icc_one_two]
  obtain ⟨hv_eq, _, _, _, _, hv1, hv2, _, hdriftN, _⟩ := p01CertGetRow_props hcell hr2 hrk
  set row := p01CertGetRow m r
  have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have h1 : p01CertPLo m r 1 = (row.iv.p1_lo_15 : ℝ) / wdScaleR := by
    unfold p01CertPLo; rw [show p01CertGetRow m r = row from rfl]; norm_num
  have h2 : p01CertPLo m r 2 = (row.iv.p2_lo_15 : ℝ) / wdScaleR := by
    unfold p01CertPLo; rw [show p01CertGetRow m r = row from rfl]; norm_num
  have hdrR : (row.tauSum_12 : ℝ) * 1000000000000000000 <
      (row.iv.p1_lo_15 : ℝ) * ((p01CertVPot m r : ℝ) - (p01CertVPot m (r - 1) : ℝ)) +
        (row.iv.p2_lo_15 : ℝ) * ((p01CertVPot m r : ℝ) - (p01CertVPot m (r - 2) : ℝ)) := by
    have hcast : ((row.tauSum_12 * 1000000000000000000 : ℕ) : ℝ) < ((row.iv.p1_lo_15 * (row.v_15 -
      p01CertVPot m (r - 1)) + row.iv.p2_lo_15 * (row.v_15 - p01CertVPot m (r - 2)) : ℕ) : ℝ) := by
      exact_mod_cast hdriftN
    push_cast at hcast; rw [Nat.cast_sub hv1, Nat.cast_sub hv2, ← hv_eq] at hcast; exact hcast
  rw [h1, h2]; unfold p01CertTauSum p01CertV; rw [show p01CertGetRow m r = row from rfl, hB_eq]
  linarith
private lemma harmSum2_lo15 :
    (3414213562373095 : ℝ) / (2 * wdScaleR) ≤ groverHarmonicSqrtSum 2 := by
  unfold groverHarmonicSqrtSum wdScaleR wdScale; rw [sum_Icc_one_two]
  have h2 : (1414213562373095 : ℝ) / 2000000000000000 ≤ 1 / √(2 : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < √(2 : ℝ))]
    have hsq : ((1414213562373095 : ℝ) / 2000000000000000 * √(2 : ℝ)) ^ 2 ≤ 1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    nlinarith [show (0 : ℝ) ≤
      (1414213562373095 : ℝ) / 2000000000000000 * √(2 : ℝ) by positivity]
  have h1 : (1 : ℝ) / √((1 : ℕ) : ℝ) = 1 := (by norm_num)
  have hc2 : ((2 : ℕ) : ℝ) = 2 := (by norm_num); rw [h1, hc2]; push_cast; linarith
theorem p01Cert_hV_top {m k : ℕ} (hcell : isSw32Cell m k) : p01CertV m k ≤
      (p01CertRelCost m k : ℝ) * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ) := by
  rcases hcell with ⟨rfl, hm⟩
  have htop : p01CheckCellTop m 2 = true := by
    rcases hm with rfl | rfl | rfl
    · exact p01CheckTop_2_2_true
    · exact p01CheckTop_4_2_true
    · exact p01CheckTop_8_2_true
  simp only [p01CheckCellTop, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at htop
  rcases htop with ⟨hchk, hden_posN, hsqLo_posN, hineqN⟩
  rw [p01FastIsqrt15_eq hchk] at hsqLo_posN hineqN; set nd := p01RelCostPair m 2
  set hsum : ℕ := 3414213562373095
  have hsum_le : (hsum : ℝ) / (2 * wdScaleR) ≤ groverHarmonicSqrtSum 2 := harmSum2_lo15
  have hB : (0 : ℝ) < wdScaleR := (by unfold wdScaleR wdScale; norm_num)
  have hmem := wdMem_p01Isqrt15 m
  have hm_sqrt_pos : 0 < √(m : ℝ) := by
    have hlo_pos : (0 : ℝ) < ((p01Isqrt15 m).1 : ℝ) := (by exact_mod_cast hsqLo_posN)
    exact lt_of_lt_of_le (div_pos hlo_pos hB) hmem.1
  have hhi_posZ : 0 < (p01Isqrt15 m).2 := by
    have hdiv_pos : 0 < ((p01Isqrt15 m).2 : ℝ) / wdScaleR := lt_of_lt_of_le hm_sqrt_pos hmem.2
    have hm_pos : 0 < ((p01Isqrt15 m).2 : ℝ) := by
      have := mul_pos hdiv_pos hB; rwa [div_mul_cancel₀ _ hB.ne'] at this
    exact_mod_cast hm_pos
  set sqHiNat : ℕ := (p01Isqrt15 m).2.toNat
  have hsqHi_eq : (sqHiNat : ℝ) = ((p01Isqrt15 m).2 : ℝ) := by
    dsimp only [sqHiNat]; exact_mod_cast Int.toNat_of_nonneg hhi_posZ.le
  have hsqHi_pos : (0 : ℝ) < (sqHiNat : ℝ) := (by rw [hsqHi_eq]; exact_mod_cast hhi_posZ)
  have hsqHi_ge : √(m : ℝ) ≤ (sqHiNat : ℝ) / wdScaleR := (by rw [hsqHi_eq]; exact hmem.2)
  have hden_pos : (0 : ℝ) < (nd.2 : ℝ) := (by exact_mod_cast hden_posN)
  have hpi_ge : (785398163397448 : ℝ) / wdScaleR ≤ π / 4 := pi4_gt_p01.le
  have hrel_eq : (p01CertRelCost m 2 : ℝ) = (nd.1 : ℝ) / (nd.2 : ℝ) := by
    unfold p01CertRelCost; rw [NNRat.divNat_eq_div]; push_cast; rfl
  have hineqR : 2 * (p01CertVPot m 2 : ℝ) * (nd.2 : ℝ) * (sqHiNat : ℝ) ≤
      (nd.1 : ℝ) * 785398163397448 * (hsum : ℝ) := by exact_mod_cast hineqN
  have hstep1 : p01CertV m 2 ≤ ((nd.1 : ℝ) / (nd.2 : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) *
        ((hsum : ℝ) / (2 * wdScaleR)) / ((sqHiNat : ℝ) / wdScaleR) := by
    unfold p01CertV
    have hrhs_eq : ((nd.1 : ℝ) / (nd.2 : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) * ((hsum : ℝ) /
      (2 * wdScaleR)) / ((sqHiNat : ℝ) / wdScaleR) = ((nd.1 : ℝ) * 785398163397448 * (hsum : ℝ)) /
      (2 * wdScaleR * (nd.2 : ℝ) * (sqHiNat : ℝ)) := by
      field_simp [hden_pos.ne', hsqHi_pos.ne', hB.ne']
    rw [hrhs_eq, div_le_div_iff₀ hB (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hineqR hB.le]
  have hnum_le : ((nd.1 : ℝ) / (nd.2 : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) * ((hsum : ℝ) /
    (2 * wdScaleR)) ≤ (p01CertRelCost m 2 : ℝ) * (π / 4) * groverHarmonicSqrtSum 2 := by
    rw [hrel_eq]
    have ha : ((nd.1 : ℝ) / (nd.2 : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) ≤ ((nd.1 : ℝ) / (nd.2
      : ℝ)) * (π / 4) := mul_le_mul_of_nonneg_left hpi_ge (by positivity)
    exact mul_le_mul ha hsum_le (by positivity) (by positivity)
  have hstep2 : ((nd.1 : ℝ) / (nd.2 : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) *
        ((hsum : ℝ) / (2 * wdScaleR)) / ((sqHiNat : ℝ) / wdScaleR) ≤
        (p01CertRelCost m 2 : ℝ) * (π / 4) * groverHarmonicSqrtSum 2 / ((sqHiNat : ℝ) / wdScaleR) :=
    div_le_div_of_nonneg_right hnum_le (div_pos hsqHi_pos hB).le
  have hnum_nn : 0 ≤ (p01CertRelCost m 2 : ℝ) * (π / 4) * groverHarmonicSqrtSum 2 :=
    le_trans (by positivity) hnum_le
  have hstep3 : (p01CertRelCost m 2 : ℝ) * (π / 4) * groverHarmonicSqrtSum 2 / ((sqHiNat : ℝ) /
    wdScaleR) ≤ (p01CertRelCost m 2 : ℝ) * (π / 4) * groverHarmonicSqrtSum 2 / √(m : ℝ) :=
    div_le_div_of_nonneg_left hnum_nn hm_sqrt_pos hsqHi_ge
  exact (hstep1.trans hstep2).trans hstep3
/-! ## Section 6: `DickeSol.JohnsonP01` Walk Spec & Circuit Wrapper -/
private lemma evalSymStage_r1_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)}
    (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card) (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N) :
    ∀ (K : ℕ) (x : Fin 3 → ℝ), evalSymStage R (r1SymMat N m) K (orbEmbed3 N m R x) =
        orbEmbed3 N m R (((rot3Pos (u1OrbVec N m R.card))^[K]) x)
  | 0, x => rfl
  | K + 1, x => by
    unfold evalSymStage
    have hstep : r1SymMat N m *ᵥ symZVec R (orbEmbed3 N m R x) =
        orbEmbed3 N m R (rot3Pos (u1OrbVec N m R.card) x) :=
      r1SymMat_step_orbEmbed3 hm2 hr2 hmin hmrN x
    rw [hstep, evalSymStage_r1_orbEmbed3 hm2 hr2 hmin hmrN K, ← Function.iterate_succ_apply]
private lemma evalSymStage_r01_orbEmbed3 {N m : ℕ} {R : Finset (Fin N)}
    (hm2 : 2 ≤ m) (hr2 : 2 ≤ R.card) (hmin : min m R.card ≤ 2) (hmrN : m + R.card < N)
    (h2m : 2 * m < N) :
    ∀ (K : ℕ) (x : Fin 3 → ℝ), evalSymStage R (r01SymMat N m) K (orbEmbed3 N m R x) =
        orbEmbed3 N m R (((rot3Neg (u2OrbVec N m R.card))^[K]) x)
  | 0, x => rfl
  | K + 1, x => by
    unfold evalSymStage
    have hstep : r01SymMat N m *ᵥ symZVec R (orbEmbed3 N m R x) =
        orbEmbed3 N m R (rot3Neg (u2OrbVec N m R.card) x) :=
      r01SymMat_step_orbEmbed3 hm2 hr2 hmin hmrN h2m x
    rw [hstep, evalSymStage_r01_orbEmbed3 hm2 hr2 hmin hmrN h2m K, ← Function.iterate_succ_apply]
/-- Two-stage `(R_{V_1})^{K_1}` then `(R_{V_0 ⊕ V_1})^{K_2}` symmetric walk stage list. -/
noncomputable def p01StagesFrom (tau1Fn tau2Fn : ℕ → ℕ) (m n r : ℕ) :
    List (ℕ × SymOrthogonal (2 ^ n) m) :=
  if hm : 1 ≤ m ∧ 2 * m < 2 ^ n then
    [(p01StepCount (tau1Fn r) (2 ^ n), SymOrthogonal.ofSymmInvolution (r1SymMat (2 ^ n) m)
        (r1SymMat_transpose (2 ^ n) m) (r1SymMat_mul_self hm.1 hm.2)),
     (p01StepCount (tau2Fn r) (2 ^ n), SymOrthogonal.ofSymmInvolution (r01SymMat (2 ^ n) m)
        (r01SymMat_transpose (2 ^ n) m) (r01SymMat_mul_self hm.1 hm.2))]
  else []
theorem p01StagesFrom_queryCount {tau1Fn tau2Fn : ℕ → ℕ} {m n r : ℕ} (hm1 : 1 ≤ m) (h2m : 2 * m <
    2 ^ n) : stagesQueryCount (p01StagesFrom tau1Fn tau2Fn m n r) = p01StepCount (tau1Fn r) (2 ^
    n) + p01StepCount (tau2Fn r) (2 ^ n) := by
  have hm_cond : 1 ≤ m ∧ 2 * m < 2 ^ n := ⟨hm1, h2m⟩; unfold p01StagesFrom
  rw [dite_eq_left hm_cond]; simp [stagesQueryCount]
theorem p01StagesFrom_hitProb_bounds {tau1Fn tau2Fn : ℕ → ℕ} {n m r p1_lo_15 p2_lo_15 : ℕ} (hn200
    : 200 ≤ n) (hm2 : 2 ≤ m) (hm_hi : m ≤ 1024) (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024) (hmin_eq : min m
    r = 2) (heval : p01EvalRowLo15 m r (tau1Fn r) (tau2Fn r) = some (p1_lo_15, p2_lo_15)) {R :
    Finset (Fin (2 ^ n))} (hR : R.card = r) : (p1_lo_15 : ℝ) / wdScaleR ≤ symHitProb R
    (evalSymStages R (p01StagesFrom tau1Fn tau2Fn m n r) (u0Vec (2 ^ n) m)) 1 ∧ (p2_lo_15 : ℝ) /
    wdScaleR ≤ symHitProb R (evalSymStages R (p01StagesFrom tau1Fn tau2Fn m n r) (u0Vec (2 ^ n)
    m)) 2 := by
  have hpow : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have h2048 : 2048 < 2 ^ 12 := (by norm_num); have hmrN : m + r < 2 ^ n := (by omega)
  have h2m : 2 * m < 2 ^ n := (by omega); have hm_cond : 1 ≤ m ∧ 2 * m < 2 ^ n := ⟨by omega, h2m⟩
  obtain ⟨hp1_le, hp2_le⟩ := p01EvalRowLo15_sound hn200 hm_hi hr_hi heval; unfold p01StagesFrom
  rw [dite_eq_left hm_cond]; dsimp only [evalSymStages, SymOrthogonal.ofSymmInvolution]
  have hu0 : u0Vec (2 ^ n) m = orbEmbed3 (2 ^ n) m R (u0OrbVec (2 ^ n) m R.card) :=
    (orbEmbed3_u0OrbVec hm2 (hR ▸ hr2) (hR ▸ hmin_eq.le) (hR ▸ hmrN)).symm
  rw [hu0, evalSymStage_r1_orbEmbed3 hm2 (hR ▸ hr2) (hR ▸ hmin_eq.le) (hR ▸ hmrN),
    evalSymStage_r01_orbEmbed3 hm2 (hR ▸ hr2) (hR ▸ hmin_eq.le) (hR ▸ hmrN) h2m]
  subst hR
  have hprob1 := sum_sq_orbEmbed3_filter hm2 hr2 hmrN (((rot3Neg (u2OrbVec (2 ^ n) m
    R.card))^[p01StepCount (tau2Fn R.card) (2 ^ n)]) (((rot3Pos (u1OrbVec (2 ^ n) m
    R.card))^[p01StepCount (tau1Fn R.card) (2 ^ n)]) (u0OrbVec (2 ^ n) m R.card))) (1 : Fin 3)
  have hprob2 := sum_sq_orbEmbed3_filter hm2 hr2 hmrN (((rot3Neg (u2OrbVec (2 ^ n) m
    R.card))^[p01StepCount (tau2Fn R.card) (2 ^ n)]) (((rot3Pos (u1OrbVec (2 ^ n) m
    R.card))^[p01StepCount (tau1Fn R.card) (2 ^ n)]) (u0OrbVec (2 ^ n) m R.card))) (2 : Fin 3)
  unfold symHitProb; exact ⟨hp1_le.trans_eq hprob1.symm, hp2_le.trans_eq hprob2.symm⟩
lemma isSw32Cell_bounds {m k : ℕ} (hcell : isSw32Cell m k) :
    m ∈ groverGrid ∧ k ∈ groverGrid ∧ 2 ≤ m ∧ m ≤ 8 ∧ 2 ≤ k ∧ k ≤ 1024 := by
  have h2 : (2 : ℕ) ∈ groverGrid := by
    unfold groverGrid; exact Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), rfl⟩
  have h4 : (4 : ℕ) ∈ groverGrid := by
    unfold groverGrid; exact Finset.mem_image.mpr ⟨2, Finset.mem_range.mpr (by omega), rfl⟩
  have h8 : (8 : ℕ) ∈ groverGrid := by
    unfold groverGrid; exact Finset.mem_image.mpr ⟨3, Finset.mem_range.mpr (by omega), rfl⟩
  rcases hcell with ⟨rfl, rfl | rfl | rfl⟩
  · exact ⟨h2, h2, by omega, by omega, by omega, by omega⟩
  · exact ⟨h4, h2, by omega, by omega, by omega, by omega⟩
  · exact ⟨h8, h2, by omega, by omega, by omega, by omega⟩
/-- Certified `JohnsonWalkSpec` instance for `isSw32Cell m k`. -/
noncomputable def p01WalkSpec (m k : ℕ) (hcell : isSw32Cell m k) : JohnsonWalkSpec m k where
  useWalk := fun r ↦ decide (2 ≤ r)
  n0 := 600
  hn0 := le_rfl
  stages := p01StagesFrom (fun r ↦ (p01CertGetRow m r).tau1_12)
    (fun r ↦ (p01CertGetRow m r).tau2_12) m
  V := p01CertV m
  hV0 := p01CertV_zero m
  hV_mono := fun h12 h2k ↦ p01CertV_mono hcell h12 h2k
  hV_eig := fun r hr1 _ hcase ↦ by
    have hr_eq : r = 1 := by
      rcases hcase with rfl | hf
      · rfl
      · simp only [decide_eq_false_iff_not] at hf; omega
    subst hr_eq
    simpa using p01Cert_hV_eig hcell
  pLo := p01CertPLo m
  hpLo_nonneg := p01CertPLo_nonneg m
  hpLo_sum_pos := fun r hr2 hrk _ ↦ p01CertPLo_sum_pos hcell hr2 hrk
  tauSum := p01CertTauSum m
  C_step := 0
  hstages_len := fun n r hn0 hr2 hrk _ ↦ by
    obtain ⟨_, _, hm2, hm8, _, _⟩ := isSw32Cell_bounds hcell
    have h16 : 16 < 2 ^ 10 := by norm_num
    have hpow : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have h2m : 2 * m < 2 ^ n := by omega
    rw [p01StagesFrom_queryCount (by omega) h2m]
    simpa using p01Cert_hstages_len hcell hr2 hrk (2 ^ n)
  hpLo_le := fun n r hn0 hr2 hrk _ R hR w hw ↦ by
    obtain ⟨_, _, hm2, hm8, _, hk1024⟩ := isSw32Cell_bounds hcell
    have hmin_eq : min m r = 2 := by
      rcases hcell with ⟨rfl, rfl | rfl | rfl⟩ <;> omega
    set row := p01CertGetRow m r
    have hval := p01CertGetRow_valid hcell hr2 hrk
    have heval : p01EvalRowLo15 m r row.tau1_12 row.tau2_12 =
        some (row.iv.p1_lo_15, row.iv.p2_lo_15) := hval.2.2.2.2.2
    obtain ⟨hp1_le, hp2_le⟩ := p01StagesFrom_hitProb_bounds
      (tau1Fn := fun r' ↦ (p01CertGetRow m r').tau1_12)
      (tau2Fn := fun r' ↦ (p01CertGetRow m r').tau2_12)
      (by omega) hm2 (by omega) hr2 (by omega) hmin_eq heval hR
    rw [hmin_eq] at hw
    rcases Finset.mem_Icc.mp hw with ⟨hw1, hw2⟩
    rcases (by omega : w = 1 ∨ w = 2) with rfl | rfl
    · have hp1 : p01CertPLo m r 1 = (row.iv.p1_lo_15 : ℝ) / wdScaleR := by
        unfold p01CertPLo; rw [show p01CertGetRow m r = row from rfl]; norm_num
      rwa [hp1]
    · have hp2 : p01CertPLo m r 2 = (row.iv.p2_lo_15 : ℝ) / wdScaleR := by
        unfold p01CertPLo; rw [show p01CertGetRow m r = row from rfl]; norm_num
      rwa [hp2]
  hdrift_lt := fun r hr2 hrk _ ↦ p01Cert_hdrift_lt hcell hr2 hrk
namespace JohnsonP01
/-- Parallel query-model circuit executing `p01WalkSpec` on `isSw32Cell m k`. -/
noncomputable def circuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Stage1.qubits n m k)) Var
      (Stage1.qubits n m k) ((n + 1) * m) :=
  open Classical in
  if hcell : isSw32Cell m k then
    johnsonCircuit res (isSw32Cell_bounds hcell).1 (isSw32Cell_bounds hcell).2.1
      (p01WalkSpec m k hcell) n
  else .skip
/-- Compiled `QProg` resetting all qubits and running `JohnsonP01.circuit`. -/
noncomputable def program {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) :
    QProg Var (2 ^ Stage1.qubits n m k) :=
  qset ;; (circuit res n m k).compile qAssign oracle
theorem correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hcell : isSw32Cell m
    k) (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄ program res n m k
    (groverParallelMarkingOracle m S) ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)
    ⦄ := by
  unfold program circuit; rw [dite_eq_left hcell]
  exact johnsonCircuit_correctness res (isSw32Cell_bounds hcell).1
    (isSw32Cell_bounds hcell).2.1 (p01WalkSpec m k hcell) hn hkN hS
/-- Claimed asymptotic relative parallel-round cost ratio on `isSw32Cell m k`. -/
abbrev relCost (m k : ℕ) : ℚ≥0 := p01CertRelCost m k
theorem rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ} (hcell : isSw32Cell m k) : ∃
    n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
    (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (fun S ↦ program res n
    m k (groverParallelMarkingOracle m S)) ((relCost m k : ℝ) * vanillaFindAllCost n m k) := by
  have htop : (p01WalkSpec m k hcell).V k ≤ (relCost m k : ℝ) * (π / 4) * groverHarmonicSqrtSum k
    / √(m : ℝ) := p01Cert_hV_top hcell
  obtain ⟨n₀, hn₀⟩ := johnsonCircuit_rel_cost (Var := Var) res
    (isSw32Cell_bounds hcell).1 (isSw32Cell_bounds hcell).2.1 (p01WalkSpec m k hcell) htop
  refine ⟨n₀, fun n hn hkN ↦ ?_⟩
  have hprog : (fun S ↦ program (Var := Var) res n m k (groverParallelMarkingOracle m S)) = (fun S
    ↦ qset ;; (johnsonCircuit res (isSw32Cell_bounds hcell).1 (isSw32Cell_bounds hcell).2.1
    (p01WalkSpec m k hcell) n).compile qAssign (groverParallelMarkingOracle m S)) := by
    funext S; unfold program circuit; rw [dite_eq_left hcell]
  rw [hprog]; exact hn₀ n hn hkN
end JohnsonP01
end Sec_P01CertAndWrapper
end
end QuantumComputation.Specs.DickeSol
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.FindAllJohnsonP01
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs
/-- Boolean guard for the `3` selected `k = 2` Johnson-walk cells `(2, 2), (4, 2), (8, 2)`. -/
def isJohnsonP01K2Cell (m k : ℕ) : Bool := (k == 2) && ((m == 2) || (m == 4) || (m == 8))
/-- Register width `m * (n + 1) + k * n` matching `masterWDZoomQubits`. -/
abbrev johnsonP01K2Qubits (n m k : ℕ) : ℕ := m * (n + 1) + k * n
/-- Coprime `10 ^ 16`-scale rational relative cost on `(2, 2), (4, 2), (8, 2)`. -/
def relCostJohnsonP01K2 (m k : ℕ) : ℚ≥0 :=
  if m == 2 && k == 2 then NNRat.divNat 6667024075121291 10000000000000000
  else if m == 4 && k == 2 then NNRat.divNat 2956868632351389 5000000000000000
  else if m == 8 && k == 2 then NNRat.divNat 2833796590014241 5000000000000000
  else 1
end QuantumComputation.Specs.GroverFindAll.FindAllJohnsonP01
end
public section
namespace QuantumComputation.Specs.GroverFindAll.FindAllJohnsonP01
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs
private lemma isSw32Cell_of_bool {m k : ℕ} (h : isJohnsonP01K2Cell m k = true) :
    DickeSol.isSw32Cell m k := by
  unfold isJohnsonP01K2Cell at h; simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, (rfl | rfl) | rfl⟩
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨rfl, Or.inr (Or.inr rfl)⟩
private lemma relCost_eq_dicke {m k : ℕ} (h : isJohnsonP01K2Cell m k = true) :
    relCostJohnsonP01K2 m k = DickeSol.JohnsonP01.relCost m k := by
  unfold isJohnsonP01K2Cell at h; simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, (rfl | rfl) | rfl⟩ <;> rfl
private lemma jp01_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl
private lemma jp01_targetSets_eq (n k : ℕ) : DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k :=
  rfl
private lemma jp01_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
      (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) :=
  rfl
/-- Dynamic circuit dispatching `(2, 2), (4, 2), (8, 2)` to `DickeSol.JohnsonP01.circuit`. -/
noncomputable def findAllJohnsonP01K2Circuit {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ johnsonP01K2Qubits n m k)) Var
      (johnsonP01K2Qubits n m k) ((n + 1) * m) :=
  DickeSol.JohnsonP01.circuit res n m k
/-- Exact probability-`1` recovery of `S` on every certified `JohnsonP01K2` cell. -/
theorem johnsonP01K2_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isJohnsonP01K2Cell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ johnsonP01K2Qubits n m k)) ⦄
    (QProg.qSet ;; (findAllJohnsonP01K2Circuit res n m k).compile QProg.qAssign
      (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  have hS' : S ∈ DickeSol.groverTargetSets n k := (by rwa [jp01_targetSets_eq])
  have hcorr := DickeSol.JohnsonP01.correctness res (isSw32Cell_of_bool hcell) hn hkN hS'
  unfold findAllJohnsonP01K2Circuit; rw [← jp01_oracle_eq]
  dsimp only [DickeSol.JohnsonP01.program, johnsonP01K2Qubits, DickeSol.Stage1.qubits] at hcorr ⊢
  exact hcorr
/-- Asymptotic uniform-average relative cost bound on `(2, 2), (4, 2), (8, 2)`. -/
theorem johnsonP01K2_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isJohnsonP01K2Cell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;; (findAllJohnsonP01K2Circuit res n m k).compile QProg.qAssign
              (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostJohnsonP01K2 m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  obtain ⟨n₀, hn₀⟩ := DickeSol.JohnsonP01.rel_cost (Var := Var) res (isSw32Cell_of_bool hcell)
  refine ⟨n₀, fun n hn hkN ↦ ?_⟩; obtain ⟨q, hq, hsum⟩ := hn₀ n hn hkN
  refine ⟨q, fun S hS ↦ ?_, ?_⟩
  · unfold findAllJohnsonP01K2Circuit; rw [← jp01_oracle_eq]
    have hqS := hq S (by rwa [jp01_targetSets_eq])
    dsimp only [DickeSol.JohnsonP01.program, johnsonP01K2Qubits, DickeSol.Stage1.qubits] at hqS ⊢
    exact hqS
  · rw [← jp01_targetSets_eq, ← jp01_vanilla_eq, relCost_eq_dicke hcell]; exact hsum
end QuantumComputation.Specs.GroverFindAll.FindAllJohnsonP01
end
public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation InnerProductSpace
/-! ## `FromSet` Renewal Bridge -/
private noncomputable def extendSpecV {m K : ℕ} (spec : JohnsonWalkSpec m K) (r : ℕ) : ℝ :=
  if r ≤ K then spec.V r else spec.V K + ((r - K : ℕ) : ℝ) * (π / 8 + 21 / 4)
private lemma extendSpecV_of_le {m K : ℕ} (spec : JohnsonWalkSpec m K) {r : ℕ} (hr : r ≤ K) :
    extendSpecV spec r = spec.V r :=
  ite_eq_left hr
private lemma extendSpecV_of_ge {m K : ℕ} (spec : JohnsonWalkSpec m K) {r : ℕ} (hr : K ≤ r) :
    extendSpecV spec r = spec.V K + ((r - K : ℕ) : ℝ) * (π / 8 + 21 / 4) := by
  by_cases hle : r ≤ K
  · have hreq : r = K := (by omega); subst hreq; unfold extendSpecV
    rw [ite_eq_left le_rfl, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  · unfold extendSpecV; exact ite_eq_right hle
private lemma extendSpecV_sub_pred_of_gt {m K : ℕ} (spec : JohnsonWalkSpec m K) {r : ℕ}
    (hr : K < r) : extendSpecV spec r - extendSpecV spec (r - 1) = π / 8 + 21 / 4 := by
  rw [extendSpecV_of_ge spec (by omega : K ≤ r), extendSpecV_of_ge spec (by omega : K ≤ r - 1)]
  have hsub : (r - K : ℕ) = (r - 1 - K) + 1 := (by omega); rw [hsub, Nat.cast_add, Nat.cast_one]
  ring
private lemma eig_slope_gap_ge_five {m r : ℕ} (hm1 : 1 ≤ m) (hr1 : 1 ≤ r) :
    (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) + 5 ≤ π / 8 + 21 / 4 := by
  have hmr1 : (1 : ℝ) ≤ (m : ℝ) * (r : ℝ) := (by exact_mod_cast Nat.mul_pos hm1 hr1)
  have hsq1 : (1 : ℝ) ≤ √((m : ℝ) * (r : ℝ)) := Real.one_le_sqrt.mpr hmr1
  have hnum0 : 0 ≤ π / 8 + 1 / 4 := (by have := Real.pi_pos; positivity)
  have hdiv : (π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ)) ≤ π / 8 + 1 / 4 := div_le_self hnum0 hsq1
  linarith
/-- Extend a `JohnsonWalkSpec m K` to arbitrary target count `k` by disabling walk stages
  above
  `K` (`useWalk r = false` for `r > K`) and continuing `V` with slope `π / 8 + 21 / 4`. -/
noncomputable def JohnsonWalkSpec.extendTo {m K : ℕ} (spec : JohnsonWalkSpec m K)
    (hm1 : 1 ≤ m) (k : ℕ) : JohnsonWalkSpec m k where
  useWalk r := decide (r ≤ K) && spec.useWalk r
  n0 := spec.n0
  hn0 := spec.hn0
  stages := spec.stages
  V := extendSpecV spec
  hV0 := by rw [extendSpecV_of_le spec (Nat.zero_le K), spec.hV0]
  hV_mono := fun {r₁ r₂} h12 _ ↦ by
    have hpos : 0 ≤ π / 8 + 21 / 4 := by have := Real.pi_pos; positivity
    by_cases hr2 : r₂ ≤ K
    · rw [extendSpecV_of_le spec (h12.trans hr2), extendSpecV_of_le spec hr2]
      exact spec.hV_mono h12 hr2
    · by_cases hr1 : r₁ ≤ K
      · rw [extendSpecV_of_le spec hr1, extendSpecV_of_ge spec (by omega : K ≤ r₂)]
        have h1K := spec.hV_mono hr1 le_rfl
        have hnn : 0 ≤ ((r₂ - K : ℕ) : ℝ) * (π / 8 + 21 / 4) := mul_nonneg (Nat.cast_nonneg _) hpos
        linarith
      · rw [extendSpecV_of_ge spec (by omega : K ≤ r₁), extendSpecV_of_ge spec (by omega : K ≤ r₂)]
        have hsub : ((r₁ - K : ℕ) : ℝ) ≤ ((r₂ - K : ℕ) : ℝ) := by exact_mod_cast (by omega)
        linarith [mul_le_mul_of_nonneg_right hsub hpos]
  hV_eig := fun r hr1 _ hcase ↦ by
    by_cases hrK : r ≤ K
    · rw [extendSpecV_of_le spec hrK, extendSpecV_of_le spec (by omega : r - 1 ≤ K)]
      have hor : r = 1 ∨ spec.useWalk r = false := by
        rcases hcase with rfl | hf
        · exact Or.inl rfl
        · rw [decide_eq_true hrK, Bool.true_and] at hf
          exact Or.inr hf
      exact spec.hV_eig r hr1 hrK hor
    · rw [extendSpecV_sub_pred_of_gt spec (by omega : K < r)]
      linarith [eig_slope_gap_ge_five hm1 hr1]
  pLo := spec.pLo
  hpLo_nonneg := spec.hpLo_nonneg
  hpLo_sum_pos := fun r hr2 _ hwk ↦ by
    rw [Bool.and_eq_true, decide_eq_true_eq] at hwk
    exact spec.hpLo_sum_pos r hr2 hwk.1 hwk.2
  tauSum := spec.tauSum
  C_step := spec.C_step
  hstages_len := fun n r hn0 hr2 _ hwk ↦ by
    rw [Bool.and_eq_true, decide_eq_true_eq] at hwk
    exact spec.hstages_len n r hn0 hr2 hwk.1 hwk.2
  hpLo_le := fun n r hn0 hr2 _ hwk R hR w hw ↦ by
    rw [Bool.and_eq_true, decide_eq_true_eq] at hwk
    exact spec.hpLo_le n r hn0 hr2 hwk.1 hwk.2 R hR w hw
  hdrift_lt := fun r hr2 _ hwk ↦ by
    rw [Bool.and_eq_true, decide_eq_true_eq] at hwk
    have hsum_eq : (∑ w ∈ Finset.Icc 1 (min m r),
          spec.pLo r w * (extendSpecV spec r - extendSpecV spec (r - w))) =
        ∑ w ∈ Finset.Icc 1 (min m r), spec.pLo r w * (spec.V r - spec.V (r - w)) := by
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [extendSpecV_of_le spec hwk.1, extendSpecV_of_le spec (by omega : r - w ≤ K)]
    rw [hsum_eq]
    exact spec.hdrift_lt r hr2 hwk.1 hwk.2
theorem extendTo_V_eq {m K : ℕ} (spec : JohnsonWalkSpec m K) (hm1 : 1 ≤ m) (k : ℕ)
    {r : ℕ} (hr : r ≤ K) : (spec.extendTo hm1 k).V r = spec.V r :=
  extendSpecV_of_le spec hr
/-- Memory-register state storing `T` in sorted order in the first `T.card` slots and `0`
  above. -/
noncomputable def memPrefixOfFinset (n k : ℕ) (T : Finset (Fin (2 ^ n))) : Fin (2 ^ (k * n)) :=
  (addrEquiv n k).symm fun i : Fin k ↦
    if hi : i.val < T.card then T.orderEmbOfFin rfl ⟨i.val, hi⟩ else 0
/-- Basis state on `Stage1.qubits n m k` with clean workspace `0` and `memPrefixOfFinset n k
  T`. -/
noncomputable def memPrefixBasisIdx (n m k : ℕ) (T : Finset (Fin (2 ^ n))) :
    Fin (2 ^ (m * (n + 1) + k * n)) :=
  (lowHighEquiv (m * (n + 1)) (k * n)).symm (0, memPrefixOfFinset n k T)
theorem memPrefixValid_memPrefixOfFinset {n k r : ℕ} {S T : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r) :
    MemPrefixValid S (k - r) (memPrefixOfFinset n k T) := by
  have hsum := Finset.card_sdiff_add_card_eq_card hTS; have hTc : T.card = k - r := (by omega)
  refine ⟨Nat.sub_le k r, ?_, ?_, ?_⟩
  · intro i hi; unfold memPrefixOfFinset; rw [Equiv.apply_symm_apply]
    have hiT : i.val < T.card := (by omega); rw [dite_eq_left hiT]
    exact hTS (Finset.orderEmbOfFin_mem T rfl ⟨i.val, hiT⟩)
  · intro i j hi hj hij; unfold memPrefixOfFinset at hij; rw [Equiv.apply_symm_apply] at hij
    have hiT : i.val < T.card := (by omega); have hjT : j.val < T.card := (by omega)
    rw [dite_eq_left hiT, dite_eq_left hjT] at hij; have heq := (T.orderEmbOfFin rfl).injective hij
    have hval : i.val = j.val := congrArg (fun x : Fin T.card ↦ x.val) heq; exact Fin.ext hval
  · intro i hi; unfold memPrefixOfFinset; rw [Equiv.apply_symm_apply]
    have hni : ¬ (i.val < T.card) := (by omega); exact dite_eq_right hni
private lemma validInd_memPrefixBasisIdx {n m k r : ℕ} {S T : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r) :
    validInd n m k S (k - r) (memPrefixBasisIdx n m k T) = 1 := by
  unfold validInd memPrefixBasisIdx; rw [Equiv.apply_symm_apply]
  exact ite_eq_left (memPrefixValid_memPrefixOfFinset hScard hTS hrem)
/-- Parallel query-model `FromSet` circuit executing `JohnsonWalkSpec` from `T ⊆ S` (`|S \
  T| = r`)
  on `Stage1.qubits n m k = m * (n + 1) + k * n` qubits. -/
noncomputable def johnsonFromSetCircuit {Var : Type} (res : Var) {m K k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (spec : JohnsonWalkSpec m K) (n r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Stage1.qubits n m k)) Var
      (Stage1.qubits n m k) ((n + 1) * m) :=
  if hn200 : 200 ≤ n then
    .seq (.step (phaseTag (permutationUnitary (Equiv.swap 0 (memPrefixBasisIdx n m k T)))))
      (.seq (johnsonSolveFrom res n m k hm_grid hk_grid hn200
          (spec.extendTo (one_le_of_mem_groverGrid hm_grid) k) (k - r))
        (.measure res (highBlock (m * (n + 1)) (k * n))))
  else
    .skip
private lemma stageReqC_extendTo_le {m K k n : ℕ} (hm1 : 1 ≤ m) (spec : JohnsonWalkSpec m K)
    (hwalk_req : ∀ r' : ℕ, 2 ≤ r' → r' ≤ K → spec.useWalk r' = true → max 0 (spec.C_step + 1) ≤
    (((∑ w ∈ Finset.Icc 1 (min m r'), spec.pLo r' w * (spec.V r' - spec.V (r' - w))) - spec.tauSum
    r') / 2) * √(2 ^ n : ℝ)) (heig_req : ∀ r' : ℕ, 1 ≤ r' → r' ≤ K → (r' = 1 ∨ spec.useWalk r' =
    false) → 5 ≤ ((spec.V r' - spec.V (r' - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r' : ℝ))) * √(2 ^
    n : ℝ)) : ∀ r' : ℕ, 1 ≤ r' → r' ≤ k → stageReqC (spec.extendTo hm1 k) r' ≤ √(2 ^ n : ℝ) := by
  intro r' hr1 hrk; set spec' := spec.extendTo hm1 k; by_cases hrK : r' ≤ K
  · by_cases hwk : 2 ≤ r' ∧ spec.useWalk r' = true
    · have hwk' : 2 ≤ r' ∧ r' ≤ k ∧ spec'.useWalk r' = true := by
        refine ⟨hwk.1, hrk, ?_⟩; dsimp only [spec', JohnsonWalkSpec.extendTo]
        rw [decide_eq_true hrK, Bool.true_and, hwk.2]
      rw [stageReqC, dite_eq_left hwk']
      have hsum_eq : (∑ w ∈ Finset.Icc 1 (min m r'), spec'.pLo r' w * (spec'.V r' - spec'.V (r' -
        w))) = ∑ w ∈ Finset.Icc 1 (min m r'), spec.pLo r' w * (spec.V r' - spec.V (r' - w)) := by
        refine Finset.sum_congr rfl fun w _ ↦ ?_; dsimp only [spec', JohnsonWalkSpec.extendTo]
        rw [extendSpecV_of_le spec hrK, extendSpecV_of_le spec (by omega : r' - w ≤ K)]
      dsimp only [spec']; rw [hsum_eq]
      have hchg : spec'.tauSum r' = spec.tauSum r' ∧ spec'.C_step = spec.C_step := ⟨rfl, rfl⟩
      rw [hchg.1, hchg.2]
      have hslack : 0 < (∑ w ∈ Finset.Icc 1 (min m r'), spec.pLo r' w * (spec.V r' - spec.V (r' -
        w))) - spec.tauSum r' := sub_pos.mpr (spec.hdrift_lt r' hwk.1 hrK hwk.2)
      rw [div_le_iff₀ (half_pos hslack)]; linarith [hwalk_req r' hwk.1 hrK hwk.2]
    · have hnwk' : ¬ (2 ≤ r' ∧ r' ≤ k ∧ spec'.useWalk r' = true) := by
        intro h; apply hwk; refine ⟨h.1, ?_⟩; dsimp only [spec', JohnsonWalkSpec.extendTo] at h
        rw [decide_eq_true hrK, Bool.true_and] at h; exact h.2.2
      rw [stageReqC, dite_eq_right hnwk', dite_eq_left ⟨hr1, hrk⟩]
      have hor : r' = 1 ∨ spec.useWalk r' = false := by
        by_cases hr2 : 2 ≤ r'
        · right
          cases h : spec.useWalk r'
          · rfl
          · exact False.elim (hwk ⟨hr2, h⟩)
        · left; omega
      have hV_eq : spec'.V r' - spec'.V (r' - 1) = spec.V r' - spec.V (r' - 1) := by
        dsimp only [spec', JohnsonWalkSpec.extendTo]
        rw [extendSpecV_of_le spec hrK, extendSpecV_of_le spec (by omega : r' - 1 ≤ K)]
      rw [hV_eq]
      have hgap : 0 < (spec.V r' - spec.V (r' - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r' : ℝ)) :=
        sub_pos.mpr (spec.hV_eig r' hr1 hrK hor)
      rw [div_le_iff₀ hgap]; linarith [heig_req r' hr1 hrK hor]
  · have hnwk' : ¬ (2 ≤ r' ∧ r' ≤ k ∧ spec'.useWalk r' = true) := by
      intro h; dsimp only [spec', JohnsonWalkSpec.extendTo] at h
      rw [decide_eq_false hrK, Bool.false_and] at h; exact Bool.false_ne_true h.2.2
    rw [stageReqC, dite_eq_right hnwk', dite_eq_left ⟨hr1, hrk⟩]
    have hV_eq : spec'.V r' - spec'.V (r' - 1) = π / 8 + 21 / 4 :=
      extendSpecV_sub_pred_of_gt spec (by omega : K < r')
    rw [hV_eq]; have hgap5 := eig_slope_gap_ge_five hm1 hr1
    have hgap_pos : 0 < (π / 8 + 21 / 4) - (π / 8 + 1 / 4) / √((m : ℝ) * (r' : ℝ)) := (by linarith)
    have hle1 : 5 / ((π / 8 + 21 / 4) - (π / 8 + 1 / 4) / √((m : ℝ) * (r' : ℝ))) ≤ 1 :=
      (div_le_one hgap_pos).mpr (by linarith)
    have h1_sqrt : (1 : ℝ) ≤ √(2 ^ n : ℝ) := Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num))
    exact hle1.trans h1_sqrt
private lemma jp01_oracle_eq_wd {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold groverParallelMarkingOracle groverSetMarkingOracle GroverFindAll.parallelMarkingOracle
    GroverFindAll.setMarkingOracle; rfl
/-- Exact probability-`1` recovery and expected query-cost bound for `johnsonFromSetCircuit`
  from
  any clean `SupportedOn (· = 0)` state `Δ` on `Stage1.qubits n m k`. -/
theorem johnsonFromSet_transition {Var : Type} [DecidableEq Var] (res : Var) {m K k n r : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (spec : JohnsonWalkSpec m K) (hn0 :
    spec.n0 ≤ n) (hr1 : 1 ≤ r) (hrK : r ≤ K) (hrk : r ≤ k) (hwalk_req : ∀ r' : ℕ, 2 ≤ r' → r' ≤ K
    → spec.useWalk r' = true → max 0 (spec.C_step + 1) ≤ (((∑ w ∈ Finset.Icc 1 (min m r'),
    spec.pLo r' w * (spec.V r' - spec.V (r' - w))) - spec.tauSum r') / 2) * √(2 ^ n : ℝ))
    (heig_req : ∀ r' : ℕ, 1 ≤ r' → r' ≤ K → (r' = 1 ∨ spec.useWalk r' = false) → 5 ≤ ((spec.V r' -
    spec.V (r' - 1)) - (π / 8 + 1 / 4) / √((m : ℝ) * (r' : ℝ))) * √(2 ^ n : ℝ)) {S T : Finset (Fin
    (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r) {Δ : CQState (Store Var)
      (2 ^
    Stage1.qubits n m k)} (hΔ : GroverFindAll.SupportedOn (· = 0) Δ) :
    let prog := (johnsonFromSetCircuit res hm_grid hk_grid spec n r T).compile qAssign
      (GroverFindAll.parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ,
      liftPureProp (fun τ ↦ GroverFindAll.decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
    expectedCost (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (spec.V r * √(2 ^ n : ℝ)) := by
  intro prog; have hn200 : 200 ≤ n := (by have := spec.hn0; omega)
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hcirc : johnsonFromSetCircuit (Var := Var) res hm_grid hk_grid spec n r T =
        .seq (.step (phaseTag (permutationUnitary (Equiv.swap 0 (memPrefixBasisIdx n m k T)))))
          (.seq (johnsonSolveFrom res n m k hm_grid hk_grid hn200 (spec.extendTo hm1 k) (k - r))
            (.measure res (highBlock (m * (n + 1)) (k * n)))) := by
    unfold johnsonFromSetCircuit; exact dite_eq_left hn200
  dsimp only [prog]; rw [hcirc, ← jp01_oracle_eq_wd]; unfold Stage1.qubits at Δ hΔ ⊢
  set oracle := groverParallelMarkingOracle m S
  set model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
  set zT := memPrefixBasisIdx n m k T; set U_init := phaseTag (permutationUnitary (Equiv.swap 0 zT))
  set spec' := spec.extendTo hm1 k
  set P_solve :=
    (johnsonSolveFrom (Var := Var) res n m k hm_grid hk_grid hn200 spec' (k - r)).compile
      qAssign oracle
  set P_meas : QProg Var (2 ^ (m * (n + 1) + k * n)) :=
    measureRegister res (highBlock (m * (n + 1)) (k * n))
  set Δ_init := (interp (.qAssign U_init : QProg Var (2 ^ (m * (n + 1) + k * n)))).toStateFun Δ
  have hV_eq_tr : 𝔼[Δ_init, validObs n m k S (k - r)] = Δ.trace := by
    dsimp only [Δ_init]; rw [← wp_expectation_eq (.qAssign U_init) Δ]
    have hexp := GroverFindAll.expect_of_supportedOn hΔ
      (Θ := wp (.qAssign U_init) (validObs n m k S (k - r))) (c := 1) (fun σ ↦ by
        set M_conj := (wp (.qAssign U_init) (validObs n m k S (k - r)) σ).1.1
        have h00 : M_conj 0 0 = 1 := by
          rw [vecQuad_single M_conj 0]; dsimp only [M_conj]
          rw [wp_qAssign, wp_phaseTag, qhlQAssign_val,
            vecQuad_conj, permutationUnitary_mulVec_single, Equiv.swap_apply_left,
            ← vecQuad_single ((validObs n m k S (k - r) σ).1.1) zT]
          dsimp only [validObs]
          rw [realDiagObs_mat, Matrix.diagonal_apply_eq,
            validInd_memPrefixBasisIdx hScard hTS hrem, Complex.ofReal_one]
        ext a b; rw [GroverFindAll.diagProj_mul_mul_diagProj_apply, Complex.ofReal_one, one_smul]
        by_cases ha : a = 0
        · subst ha; by_cases hb : b = 0
          · subst hb
            simp only [and_self, ↓reduceIte, GroverFindAll.diagProj, Matrix.diagonal_apply_eq]
            exact h00
          · simp only [hb, and_false, ↓reduceIte, GroverFindAll.diagProj,
              Matrix.diagonal_apply_ne _ (Ne.symm hb)]
        · simp only [ha, false_and, ↓reduceIte, GroverFindAll.diagProj]; by_cases hab : a = b
          · subst hab; simp only [Matrix.diagonal_apply_eq, ha, ↓reduceIte]
          · rw [Matrix.diagonal_apply_ne _ hab])
    rw [one_mul] at hexp; exact hexp
  have htr_le1 : (Δ_init.trace : ℝ) ≤ Δ.trace := by
    exact_mod_cast
      (interp (.qAssign U_init : QProg Var (2 ^ (m * (n + 1) + k * n)))).trace_toStateFun_le Δ
  have htr_le2 : (Δ.trace : ℝ) ≤ Δ_init.trace := by
    rw [← hV_eq_tr, ← expect_top Δ_init]; exact expect_mono le_rfl le_top
  have htr_init : Δ_init.trace = Δ.trace := (by exact_mod_cast le_antisymm htr_le1 htr_le2)
  have hmass_init : stateMass Δ_init = stateMass Δ := by
    rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_init]
  have hV_init : 𝔼[Δ_init, validObs n m k S (k - r)] = Δ_init.trace := by
    linarith [hV_eq_tr, htr_le1, htr_le2]
  refine ⟨?_, ?_⟩
  · dsimp only [compile]
    let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
      liftPureProp (fun τ ↦ decodeTargets n k (τ res) = S)
    change 𝔼[(interp (.qAssign U_init ;; (P_solve ;; P_meas))).toStateFun Δ, post] = Δ.trace
    have hseq_state : (interp (.qAssign U_init ;; (P_solve ;; P_meas))).toStateFun Δ =
          (interp (P_solve ;; P_meas)).toStateFun Δ_init := by
      rw [interp_qSeq, QMonad.Q.toStateFun_bind]
    rw [hseq_state]
    have hwp_sm : validObs (Var := Var) n m k S (k - r) ≤ wp (P_solve ;; P_meas) post := by
      rw [wp_qSeq]
      have hst := wp_johnsonSolveFrom_ge (Var := Var) res hm_grid hk_grid hn200 spec' hScard
        r (k - r) (by omega) (Nat.sub_le k r)
      exact hst.trans (wp_mono _ (validObs_le_wp_measure_decodeTargets res hScard))
    have h1 : (Δ_init.trace : ℝ) ≤ 𝔼[(interp (P_solve ;; P_meas)).toStateFun Δ_init, post] := by
      rw [← hV_init, ← wp_expectation_eq (P_solve ;; P_meas) Δ_init]
      exact expect_mono le_rfl hwp_sm
    have h2 : 𝔼[(interp (P_solve ;; P_meas)).toStateFun Δ_init, post] ≤
        (((interp (P_solve ;; P_meas)).toStateFun Δ_init).trace : ℝ) := by
      rw [← expect_top ((interp (P_solve ;; P_meas)).toStateFun Δ_init)]
      exact expect_mono le_rfl le_top
    have h3 : (((interp (P_solve ;; P_meas)).toStateFun Δ_init).trace : ℝ) ≤
        (Δ_init.trace : ℝ) := by
      exact_mod_cast (interp (P_solve ;; P_meas)).trace_toStateFun_le Δ_init
    linarith [htr_le1, htr_le2]
  · dsimp only [compile]; change expectedCost model (.qAssign U_init ;; (P_solve ;; P_meas)) Δ ≤ _
    rw [expectedCost_qSeq]
    have hcost_init : expectedCost model (.qAssign U_init) Δ = 0 := by
      have hcb := costBound_qAssign_phaseTag (Var := Var)
        (isRealMatrix_groverParallelMarkingOracle m S) (permutationUnitary (Equiv.swap 0 zT)) Δ
      exact nonpos_iff_eq_zero.mp (by simpa using hcb)
    rw [hcost_init, zero_add]; change expectedCost model (P_solve ;; P_meas) Δ_init ≤ _
    rw [expectedCost_qSeq]
    have hmeas0 : expectedCost model P_meas ((interp P_solve).toStateFun Δ_init) = 0 := by
      have hm_cb : CostBound (Var := Var) model P_meas 0 := by
        simpa [P_meas, measureRegister, model, CostModel.ofEmbeddedOracle] using
          CostBound.qMeasure (Var := Var) model res _
      exact nonpos_iff_eq_zero.mp (by simpa using hm_cb _)
    rw [hmeas0, add_zero]
    have hreq := stageReqC_extendTo_le (k := k) (n := n) hm1 spec hwalk_req heig_req
    have hst := expectedCost_johnsonSolveFrom_le res hm_grid hk_grid hn200 spec' hn0 hreq hScard
      r (k - r) (by omega) (Nat.sub_le k r) Δ_init hV_init
    have hkr : k - (k - r) = r := (by omega)
    rw [hkr, extendTo_V_eq spec hm1 k hrK, hmass_init] at hst; exact hst
/-- Turnkey `P01` `FromSet` circuit for `m ∈ {2, 4, 8}` and `1 ≤ r ≤ 2` on `Stage1.qubits`. -/
noncomputable def p01FromSetCircuit {Var : Type} (res : Var) {m k : ℕ}
    (hm : m = 2 ∨ m = 4 ∨ m = 8) (hk_grid : k ∈ groverGrid) (n r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Stage1.qubits n m k)) Var
      (Stage1.qubits n m k) ((n + 1) * m) :=
  johnsonFromSetCircuit res (isSw32Cell_bounds (k := 2) ⟨rfl, hm⟩).1 hk_grid
    (p01WalkSpec m 2 ⟨rfl, hm⟩) n r T
/-- Turnkey `P01` `FromSet` transition for `m ∈ {2, 4, 8}`, `r ∈ {1, 2}`, and `600 ≤ n`. -/
theorem p01FromSet_transition {Var : Type} [DecidableEq Var] (res : Var) {m k n r : ℕ} (hm : m = 2
    ∨ m = 4 ∨ m = 8) (hk_grid : k ∈ groverGrid) (hn600 : 600 ≤ n) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hrk
    : r ≤ k) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card
    = r) {Δ : CQState (Store Var) (2 ^ Stage1.qubits n m k)} (hΔ : GroverFindAll.SupportedOn (· = 0)
      Δ) :
    let prog := (p01FromSetCircuit res hm hk_grid n r T).compile qAssign
      (GroverFindAll.parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ,
      liftPureProp (fun τ ↦ GroverFindAll.decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
    expectedCost (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (p01CertV m r * √(2 ^ n : ℝ)) := by
  have hcell : isSw32Cell m 2 := ⟨rfl, hm⟩
  have hS0_ge : ((2 : ℝ) ^ 105) ≤ √(2 ^ n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc ((2 : ℝ) ^ 105) ^ 2 = (2 : ℝ) ^ 210 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  exact johnsonFromSet_transition res
    (isSw32Cell_bounds hcell).1 hk_grid (p01WalkSpec m 2 hcell) hn600 hr1 hr2 hrk
    (fun r' hr2' hrK' _ ↦ by
      have hr_eq : r' = 2 := (by omega); subst hr_eq; dsimp only [p01WalkSpec]
      rw [isSw32Cell_min_eq_two hcell le_rfl le_rfl, sum_Icc_one_two]
      obtain ⟨hv_eq, _, _, _, _, hv1, hv2, _, hdriftN, _⟩ := p01CertGetRow_props hcell le_rfl le_rfl
      set row := p01CertGetRow m 2
      have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
      have h1 : p01CertPLo m 2 1 = (row.iv.p1_lo_15 : ℝ) / wdScaleR := by
        unfold p01CertPLo; rw [show p01CertGetRow m 2 = row from rfl]; norm_num
      have h2 : p01CertPLo m 2 2 = (row.iv.p2_lo_15 : ℝ) / wdScaleR := by
        unfold p01CertPLo; rw [show p01CertGetRow m 2 = row from rfl]; norm_num
      have hdr1 : row.tauSum_12 * 1000000000000000000 + 1 ≤ row.iv.p1_lo_15 * (row.v_15 -
        p01CertVPot m 1) + row.iv.p2_lo_15 * (row.v_15 - p01CertVPot m 0) := Nat.add_one_le_iff.mpr
        hdriftN
      have hdrR : (row.tauSum_12 : ℝ) * 1000000000000000000 + 1 ≤
          (row.iv.p1_lo_15 : ℝ) * ((p01CertVPot m 2 : ℝ) - (p01CertVPot m 1 : ℝ)) +
            (row.iv.p2_lo_15 : ℝ) * ((p01CertVPot m 2 : ℝ) - (p01CertVPot m 0 : ℝ)) := by
        have hcast : ((row.tauSum_12 * 1000000000000000000 + 1 : ℕ) : ℝ) ≤
            ((row.iv.p1_lo_15 * (row.v_15 - p01CertVPot m 1) +
              row.iv.p2_lo_15 * (row.v_15 - p01CertVPot m 0) : ℕ) : ℝ) := by
          exact_mod_cast hdr1
        push_cast at hcast; rw [Nat.cast_sub hv1, Nat.cast_sub hv2, ← hv_eq] at hcast; exact hcast
      have hslack_lo : (1 : ℝ) / 1000000000000000000000000000000 ≤
          (p01CertPLo m 2 1 * (p01CertV m 2 - p01CertV m 1) +
            p01CertPLo m 2 2 * (p01CertV m 2 - p01CertV m 0)) - p01CertTauSum m 2 := by
        rw [h1, h2]; unfold p01CertTauSum p01CertV
        rw [show p01CertGetRow m 2 = row from rfl, hB_eq]; linarith
      have hmax1 : max (0 : ℝ) ((0 : ℝ) + 1) = 1 := (by norm_num); rw [hmax1]
      have hpow : (2000000000000000000000000000000 : ℝ) ≤ (2 : ℝ) ^ 105 := (by norm_num)
      nlinarith [hslack_lo, hS0_ge, hpow])
    (fun r' hr1' hrK' hcase ↦ by
      have hr_eq : r' = 1 := by
        rcases hcase with rfl | hf
        · rfl
        · dsimp only [p01WalkSpec] at hf; simp only [decide_eq_false_iff_not] at hf; omega
      subst hr_eq; dsimp only [p01WalkSpec]
      have heig : p01CheckEigOne m = true := by
        rcases hm with rfl | rfl | rfl
        · exact p01CheckEig_2_true
        · exact p01CheckEig_4_true
        · exact p01CheckEig_8_true
      simp only [p01CheckEigOne, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at heig
      rcases heig with ⟨hchk, hsq1_pos, hineqN⟩; rw [p01FastIsqrt15_eq hchk] at hsq1_pos hineqN
      have hmem := wdMem_p01Isqrt15 m; set sqLoNat : ℕ := (p01Isqrt15 m).1.toNat
      have hsqLo_eq : (sqLoNat : ℝ) = ((p01Isqrt15 m).1 : ℝ) := by
        dsimp only [sqLoNat]; exact_mod_cast Int.toNat_of_nonneg hsq1_pos.le
      have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
      have hB : (0 : ℝ) < wdScaleR := (by rw [hB_eq]; positivity)
      have hsqLo_pos : (0 : ℝ) < (sqLoNat : ℝ) := (by rw [hsqLo_eq]; exact_mod_cast hsq1_pos)
      have hsqLo_le : (sqLoNat : ℝ) / wdScaleR ≤ √(m : ℝ) := (by rw [hsqLo_eq]; exact hmem.1)
      have hm_sqrt_pos : 0 < √(m : ℝ) := lt_of_lt_of_le (div_pos hsqLo_pos hB) hsqLo_le
      have hm_sqrt_le3 : √(m : ℝ) ≤ 3 := by
        have hm9 : (m : ℝ) ≤ 9 := (by rcases hm with rfl | rfl | rfl <;> norm_num)
        calc √(m : ℝ) ≤ √(9 : ℝ) := Real.sqrt_le_sqrt hm9
          _ = 3 := by norm_num
      have hpi_gap : π / 8 + 1 / 4 + (1 : ℝ) / 10000000000000000 ≤
          (1285398163397449 : ℝ) / (2 * wdScaleR) := by
        rw [hB_eq]; linarith [Real.pi_lt_d20]
      have hineqR : (1285398163397449 : ℝ) * 1000000000000000 ≤
          2 * (p01CertVPot m 1 : ℝ) * (sqLoNat : ℝ) := by exact_mod_cast hineqN
      have hv_nn : (0 : ℝ) ≤ (p01CertVPot m 1 : ℝ) / wdScaleR := div_nonneg (Nat.cast_nonneg _)
        hB.le
      have hmul_lo : (1285398163397449 : ℝ) / (2 * wdScaleR) ≤ p01CertV m 1 * √(m : ℝ) := by
        unfold p01CertV
        calc (1285398163397449 : ℝ) / (2 * wdScaleR)
            ≤ ((p01CertVPot m 1 : ℝ) / wdScaleR) * ((sqLoNat : ℝ) / wdScaleR) := by
                rw [hB_eq, div_mul_div_comm, div_le_div_iff₀ (by norm_num) (by norm_num)]
                nlinarith [hineqR]
          _ ≤ ((p01CertVPot m 1 : ℝ) / wdScaleR) * √(m : ℝ) :=
              mul_le_mul_of_nonneg_left hsqLo_le hv_nn
      have hgap_mul : (1 : ℝ) / 10000000000000000 ≤
          (p01CertV m 1 - (π / 8 + 1 / 4) / √(m : ℝ)) * √(m : ℝ) := by
        have hsub : (p01CertV m 1 - (π / 8 + 1 / 4) / √(m : ℝ)) * √(m : ℝ) =
            p01CertV m 1 * √(m : ℝ) - (π / 8 + 1 / 4) := by
          rw [sub_mul, div_mul_cancel₀ _ hm_sqrt_pos.ne']
        linarith
      have hgap_nn : 0 ≤ p01CertV m 1 - (π / 8 + 1 / 4) / √(m : ℝ) :=
        nonneg_of_mul_nonneg_left (le_trans (by norm_num) hgap_mul) hm_sqrt_pos
      have hgap_lo : (1 : ℝ) / 30000000000000000 ≤ p01CertV m 1 - (π / 8 + 1 / 4) / √(m : ℝ) := by
        have h3 := mul_le_mul_of_nonneg_left hm_sqrt_le3 hgap_nn; linarith
      rw [show (1 - 1 : ℕ) = 0 from rfl, Nat.cast_one, mul_one, p01CertV_zero, sub_zero]
      have hpow : (150000000000000000 : ℝ) ≤ (2 : ℝ) ^ 105 := (by norm_num)
      nlinarith [hgap_lo, hS0_ge, hpow])
    hScard hTS hrem hΔ
end QuantumComputation.Specs.DickeSol
end
