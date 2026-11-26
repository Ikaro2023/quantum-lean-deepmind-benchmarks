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
public import Track2Grover.Engine.WeakDickeCore

namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val tensorState)
open Matrix (mulVec_mulVec mulVec_diagonal mulVec_single_one col_apply diagonal)
open Complex (normSq)
open List (mem_finRange prod_cons finRange map_cons)
open Fintype (sum_eq_single sum_prod_type)
open Equiv (swap)
open Pi (single)
open scoped Matrix NNReal ENNReal NNRat ComplexOrder MatrixOrder QProg.Notation QHLExpectation
@[expose] public section

/-- Real flag rotation, including exact rational cosines with irrational sine. -/
structure RealFlagPair where
  cVal : ℝ
  sVal : ℝ
  cVal_sq_add_sVal_sq : cVal ^ 2 + sVal ^ 2 = 1

noncomputable def RealFlagPair.ofAmplitude (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : RealFlagPair where
  cVal := a
  sVal := Real.sqrt (1 - a^2)
  cVal_sq_add_sVal_sq := by
    rw [Real.sq_sqrt (by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)])]
    ring

/-- Generic `(W + M)`-qubit weak rotation matrix controlled by `cond: Fin (2 ^ W) → Bool` on
  the
  low `W` qubits and acting by `(p.cVal, p.sVal)` on the top ancilla bit `W + M - 1`. -/
noncomputable def realFlagMat (W M : ℕ) (hM : 1 ≤ M) (cond : Fin (2 ^ W) → Bool)
    (p : RealFlagPair) : Matrix (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ :=
  Matrix.of fun z₁ z₂ ↦
    let bq₁ := topAncEquiv W M hM z₁
    let bq₂ := topAncEquiv W M hM z₂
    if bq₁.1 = bq₂.1 then
      if cond (topAncBaseWork bq₁.1) then
        match bq₁.2.val, bq₂.2.val with
        | 0, 0 => (p.cVal : ℂ)
        | 0, 1 => (-p.sVal : ℂ)
        | 1, 0 => (p.sVal : ℂ)
        | _, _ => (p.cVal : ℂ)
      else if bq₁.2 = bq₂.2 then 1 else 0
    else 0
private lemma flagBitCases (q : Fin (2 ^ 1)) : q = 0 ∨ q = 1 := by
  rcases q with ⟨v, hv⟩; interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl
/-- Unitary wrapper around `realFlagMat`. -/
noncomputable def realFlagUnitary (W M : ℕ) (hM : 1 ≤ M) (cond : Fin (2 ^ W) → Bool)
    (p : RealFlagPair) : Unitary (2 ^ (W + M)) :=
  ⟨realFlagMat W M hM cond p, by
    let U := realFlagMat W M hM cond p
    have hpyth_c : (p.cVal : ℂ) ^ 2 + (p.sVal : ℂ) ^ 2 = 1 := by
      exact_mod_cast p.cVal_sq_add_sVal_sq
    rw [Matrix.mem_unitaryGroup_iff]
    ext z₁ z₂
    rw [Matrix.mul_apply, Matrix.one_apply]
    let g (z : Fin (2 ^ (W + M))) : ℂ := U z₁ z * (Uᴴ) z z₂
    change ∑ z, g z = _
    rw [← (topAncEquiv W M hM).symm.sum_comp g, sum_prod_type]
    set bq₁ := topAncEquiv W M hM z₁
    set bq₂ := topAncEquiv W M hM z₂
    by_cases hb : bq₁.1 = bq₂.1
    · rw [sum_eq_single bq₁.1 (fun b hne ↦ by
        refine Finset.sum_eq_zero fun q _ ↦ ?_
        dsimp only [g, U, realFlagMat]
        rw [Matrix.of_apply, Equiv.apply_symm_apply]
        change (if bq₁.1 = b then _ else 0) * _ = 0
        rw [ite_eq_right (Ne.symm hne), zero_mul])]
      have hz_eq : z₁ = z₂ ↔ bq₁.2 = bq₂.2 :=
        ⟨fun h ↦ by subst h; rfl,
         fun hq ↦ (topAncEquiv W M hM).injective (Prod.ext hb hq)⟩
      rw [if_congr hz_eq rfl rfl]
      have hsum2 (f : Fin (2 ^ 1) → ℂ) : (∑ q : Fin (2 ^ 1), f q) = f 0 + f 1 :=
        Fin.sum_univ_two f
      rw [hsum2]
      dsimp only [g, U, realFlagMat, Matrix.conjTranspose_apply]
      simp only [Matrix.of_apply]
      have hsymm0 : topAncEquiv W M hM ((topAncEquiv W M hM).symm (bq₁.1, 0)) = (bq₁.1, 0) :=
        Equiv.apply_symm_apply _ _
      have hsymm1 : topAncEquiv W M hM ((topAncEquiv W M hM).symm (bq₁.1, 1)) = (bq₁.1, 1) :=
        Equiv.apply_symm_apply _ _
      have hbq1_def : topAncEquiv W M hM z₁ = bq₁ := rfl
      have hbq2_def : topAncEquiv W M hM z₂ = bq₂ := rfl
      rw [hsymm0, hsymm1, hbq1_def, hbq2_def]
      simp only [← hb, ite_true]
      cases hfl : cond (topAncBaseWork bq₁.1)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rcases flagBitCases bq₁.2 with h1 | h1 <;> rcases flagBitCases bq₂.2 with h2 | h2 <;>
          rw [h1, h2] <;> simp
      · simp only [↓reduceIte]
        rcases flagBitCases bq₁.2 with h1 | h1 <;> rcases flagBitCases bq₂.2 with h2 | h2 <;>
          rw [h1, h2] <;> simp only [Fin.val_zero, Fin.val_one, star_neg, RCLike.star_def,
            Complex.conj_ofReal]
        · simp; linear_combination hpyth_c
        · simp; ring
        · simp; ring
        · simp; linear_combination hpyth_c
    · have hne_z : z₁ ≠ z₂ := fun h ↦ hb (by subst h; rfl)
      rw [ite_eq_right hne_z]
      refine Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun q _ ↦ ?_
      dsimp only [g, U, realFlagMat, Matrix.conjTranspose_apply]
      simp only [Matrix.of_apply]
      have hsymm : topAncEquiv W M hM ((topAncEquiv W M hM).symm (b, q)) = (b, q) :=
        Equiv.apply_symm_apply _ _
      rw [hsymm]
      change (if bq₁.1 = b then _ else 0) * star (if bq₂.1 = b then _ else 0) = 0
      by_cases hb1 : bq₁.1 = b
      · have hb2 : bq₂.1 ≠ b := fun h2 ↦ hb (hb1.trans h2.symm)
        rw [ite_eq_right hb2, star_zero, mul_zero]
      · rw [ite_eq_right hb1, zero_mul]⟩
theorem realFlagMat_mulVec_workMemState {W M : ℕ} (hM : 1 ≤ M) (cond : Fin (2 ^ W) → Bool) (p :
  RealFlagPair) (ψ : Fin (2 ^ W) → ℂ) {μ : Fin (2 ^ M)} (hμ : μ.val < 2 ^ (M - 1)) : realFlagMat W
  M hM cond p *ᵥ workMemState ψ (single μ 1) = workMemState (fun w ↦ if cond w then (p.cVal : ℂ) * ψ
  w else ψ w) (single μ 1) + workMemState (fun w ↦ if cond w then (p.sVal : ℂ) * ψ w else 0) (single
  (memWithTopOne hM μ hμ) 1) := by
  funext z; rw [Matrix.mulVec, dotProduct]; dsimp only [Pi.add_apply, workMemState]
  let eμ : Fin (2 ^ M) → ℂ := Pi.single μ 1
  let f (y : Fin (2 ^ (W + M))) : ℂ :=
    realFlagMat W M hM cond p z y * (ψ (lowHighEquiv W M y).1 * eμ (lowHighEquiv W M y).2)
  change ∑ y, f y = _; rw [← (lowHighEquiv W M).symm.sum_comp f, sum_prod_type]
  have hsum_μ (w : Fin (2 ^ W)) : (∑ ν : Fin (2 ^ M), f ((lowHighEquiv W M).symm (w, ν))) =
    realFlagMat W M hM cond p z ((lowHighEquiv W M).symm (w, μ)) * ψ w := by
    rw [sum_eq_single μ (fun ν hν ↦ by
      dsimp only [f, eμ]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hν, mul_zero, mul_zero])]
    dsimp only [f, eμ]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  simp_rw [hsum_μ]; set w_z := (lowHighEquiv W M z).1; set ν_z := (lowHighEquiv W M z).2
  have hz_symm : (lowHighEquiv W M).symm (w_z, ν_z) = z := Equiv.symm_apply_apply _ z
  rw [sum_eq_single w_z (fun w hw ↦ by
    dsimp only [realFlagMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w hμ]
    have hne_b : (topAncEquiv W M hM z).1 ≠ topAncBase hM w hμ := by
      intro heq; apply hw
      have h1 := lowHigh_fst_topAncEquiv_symm W M hM (topAncEquiv W M hM z).1 (topAncEquiv W M hM
        z).2; rw [Equiv.symm_apply_apply] at h1; have hval := congrArg Fin.val h1; rw [heq] at hval;
        dsimp only [topAncBase] at hval
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w.isLt] at hval; exact Fin.ext hval.symm
    change (if (topAncEquiv W M hM z).1 = topAncBase hM w hμ then _ else 0) * ψ w = 0
    rw [ite_eq_right hne_b, zero_mul])]
  have hmod_wz : topAncBaseWork (topAncBase hM w_z hμ) = w_z := by
    ext
    dsimp only [topAncBaseWork, topAncBase]; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt
      w_z.isLt]
  by_cases hν0 : ν_z = μ
  · have hν1 : ν_z ≠ memWithTopOne hM μ hμ := by
      rw [hν0]; intro h; have hv := congrArg Fin.val h; dsimp only [memWithTopOne] at hv; have :=
        Nat.two_pow_pos (M - 1); omega
    rw [Pi.single_eq_of_ne hν1, mul_zero, add_zero, hν0, Pi.single_eq_same, mul_one, ← hz_symm, hν0]
    dsimp only [realFlagMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w_z hμ]
    simp only [ite_true, Fin.val_zero]; rw [hmod_wz]; cases cond w_z <;> simp
  · by_cases hν1 : ν_z = memWithTopOne hM μ hμ
    · rw [Pi.single_eq_of_ne hν0, mul_zero, zero_add, hν1, Pi.single_eq_same, mul_one, ← hz_symm,
        hν1]; dsimp only [realFlagMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_one hM w_z hμ,
        topAncEquiv_lowHigh_zero hM w_z hμ]
      simp only [ite_true, Fin.val_one, Fin.val_zero]; rw [hmod_wz]; cases cond w_z
      · have h10 : (1 : Fin (2 ^ 1)) ≠ 0 := fun h ↦ by have v := congrArg Fin.val h; simp at v
        simp [h10]
      · simp
    · rw [Pi.single_eq_of_ne hν0, Pi.single_eq_of_ne hν1, mul_zero, mul_zero, add_zero]
      dsimp only [realFlagMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w_z hμ]
      by_cases hb : (topAncEquiv W M hM z).1 = topAncBase hM w_z hμ
      · exfalso; rcases flagBitCases (topAncEquiv W M hM z).2 with hq0 | hq1
        · have heq : topAncEquiv W M hM z = topAncEquiv W M hM ((lowHighEquiv W M).symm (w_z, μ)) :=
            (by rw [topAncEquiv_lowHigh_zero hM w_z hμ]; exact Prod.ext hb hq0); have hp_eq :=
            congrArg (lowHighEquiv W M) ((topAncEquiv W M hM).injective heq)
          rw [Equiv.apply_symm_apply] at hp_eq; exact hν0 (congrArg Prod.snd hp_eq)
        · have heq : topAncEquiv W M hM z = topAncEquiv W M hM ((lowHighEquiv W M).symm (w_z,
            memWithTopOne hM μ hμ)) :=
            (by rw [topAncEquiv_lowHigh_one hM w_z hμ]; exact Prod.ext hb hq1); have hp_eq :=
            congrArg (lowHighEquiv W M) ((topAncEquiv W M hM).injective heq)
          rw [Equiv.apply_symm_apply] at hp_eq; exact hν1 (congrArg Prod.snd hp_eq)
      · change (if (topAncEquiv W M hM z).1 = topAncBase hM w_z hμ then _ else 0) * ψ w_z = 0
        rw [ite_eq_right hb, zero_mul]
end
end QuantumComputation.Specs.DickeSol
