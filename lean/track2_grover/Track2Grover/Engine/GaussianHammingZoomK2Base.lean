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
public import Mathlib.Data.Fintype.CardEmbedding
public import Track2Grover.Engine.BaselineRouter
public import Track2Grover.Engine.WeakDickeCore
/-!
# Gaussian-Hamming Weak-Dicke Clicked-Subcube Zoom Base (`GaussianHammingZoomK2Base`)

Shared `k = 2` Gaussian-Hamming + Clicked-Subcube Zoom QHL (`DickeSol.ghZoom*`), `10 ^
15`-scaled
complex-interval evaluator (`DickeSol.WDCVal`, `dickeStepCIVVec`, `stepHas2CIVVecCPS`), and
`9`
certified `k = 2` cells (`m ∈ {4.. 1024}`), privately imported (`pubSh = 0`) by
`GaussianHammingZoomK2Certs` and exposing a turnkey 9-cell `GaussianHammingZoomK2Base` API.
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

section GHZoomQHL
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val tensorState)
open Matrix (diagonal mulVec_mulVec mulVec_diagonal mulVec_single_one col_apply)
open Complex (normSq)
open List (finRange map_cons mem_finRange prod_cons)
open Fintype (sum_eq_single sum_prod_type)
open Equiv (swap)
open Pi (single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QProg.Notation QHLExpectation
@[expose] public section
/-! ## Section 1: Gaussian-Rational Phases, Hamming-Weight Probe Gate, & 1D Certified Step -/
/-- Exact integer Gaussian-Pythagorean witness `(aNum, bNum, den)` parametrizing a
  unit-modulus
  complex phase `(aNum + i * bNum) / den` with `0 < den` and `aNum ^ 2 + bNum ^ 2 = (den: ℤ)
  ^ 2`. -/
structure GaussPyth where
  /-- Real-part numerator. -/
  aNum : ℤ
  /-- Imaginary-part numerator. -/
  bNum : ℤ
  /-- Positive integer denominator. -/
  den : ℕ
  /-- Positivity of `den`. -/
  hDen : 0 < den
  /-- Exact Pythagorean norm-1 identity. -/
  hPyth : aNum ^ 2 + bNum ^ 2 = (den : ℤ) ^ 2
  deriving DecidableEq, Repr
/-- Complex unit-circle phase `(aNum / den) + I * (bNum / den)` of a `GaussPyth` witness. -/
noncomputable def GaussPyth.val (g : GaussPyth) : ℂ :=
  ((g.aNum : ℝ) / (g.den : ℝ) : ℂ) + Complex.I * ((g.bNum : ℝ) / (g.den : ℝ) : ℂ)
theorem GaussPyth.normSq_val (g : GaussPyth) : normSq g.val = 1 := by
  have hden_ne : (g.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr g.hDen.ne'
  have hpyth_r : (g.aNum : ℝ) ^ 2 + (g.bNum : ℝ) ^ 2 = (g.den : ℝ) ^ 2 := by
    exact_mod_cast g.hPyth
  have hre : g.val.re = (g.aNum : ℝ) / (g.den : ℝ) := by simp [GaussPyth.val]
  have him : g.val.im = (g.bNum : ℝ) / (g.den : ℝ) := by simp [GaussPyth.val]
  rw [Complex.normSq_apply, hre, him]
  have hsq :
      (g.aNum : ℝ) / (g.den : ℝ) * ((g.aNum : ℝ) / (g.den : ℝ)) +
        (g.bNum : ℝ) / (g.den : ℝ) * ((g.bNum : ℝ) / (g.den : ℝ)) =
      ((g.aNum : ℝ) ^ 2 + (g.bNum : ℝ) ^ 2) / (g.den : ℝ) ^ 2 := by
    ring
  rw [hsq, hpyth_r, div_self (pow_ne_zero 2 hden_ne)]
theorem GaussPyth.val_mul_star (g : GaussPyth) : g.val * star g.val = 1 := by
  rw [mul_comm, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, g.normSq_val,
    Complex.ofReal_one]
/-- Identity Gaussian-rational phase `1 + 0i`. -/
def gaussOne : GaussPyth := ⟨1, 0, 1, by decide, by decide⟩
theorem gaussOne_val : gaussOne.val = 1 := by
  simp [gaussOne, GaussPyth.val]
/-- Identity Pythagorean rotation `(cos, sin) = (1, 0)` (zero-click branch). -/
def pythOne : PythPair := ⟨1, 0, 1, by decide, by decide⟩
theorem pythOne_cVal : pythOne.cVal = 1 := by
  simp [pythOne, PythPair.cVal]
theorem pythOne_sVal : pythOne.sVal = 0 := by
  simp [pythOne, PythPair.sVal]
lemma gh_fin2_cases (q : Fin (2 ^ 1)) : q = 0 ∨ q = 1 := by
  rcases q with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl
/-- Generic `(W + M)`-qubit `0`-query phase-and-weak-rotation matrix controlled by `wt` on
  the
  low `W` qubits and acting on the clean top ancilla bit `W + M - 1` (`1 ≤ M`). -/
noncomputable def gaussianHammingGenMat (W M : ℕ) (hM : 1 ≤ M)
    (wt : Fin (2 ^ W) → GaussPyth × PythPair) :
    Matrix (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ :=
  Matrix.of fun z₁ z₂ ↦
    let bq₁ := topAncEquiv W M hM z₁
    let bq₂ := topAncEquiv W M hM z₂
    if bq₁.1 = bq₂.1 then
      let gp := wt (topAncBaseWork bq₁.1)
      match bq₁.2.val, bq₂.2.val with
      | 0, 0 => (gp.2.cVal : ℂ) * gp.1.val
      | 0, 1 => (-gp.2.sVal : ℂ)
      | 1, 0 => (gp.2.sVal : ℂ) * gp.1.val
      | _, _ => (gp.2.cVal : ℂ)
    else 0
/-- Unitary wrapper around `gaussianHammingGenMat`. -/
noncomputable def gaussianHammingGenUnitary (W M : ℕ) (hM : 1 ≤ M)
    (wt : Fin (2 ^ W) → GaussPyth × PythPair) : Unitary (2 ^ (W + M)) :=
  ⟨gaussianHammingGenMat W M hM wt, by
    let U := gaussianHammingGenMat W M hM wt
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
        dsimp only [g, U, gaussianHammingGenMat]
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
      dsimp only [g, U, gaussianHammingGenMat, Matrix.conjTranspose_apply]
      simp only [Matrix.of_apply]
      have hsymm0 : topAncEquiv W M hM ((topAncEquiv W M hM).symm (bq₁.1, 0)) = (bq₁.1, 0) :=
        Equiv.apply_symm_apply _ _
      have hsymm1 : topAncEquiv W M hM ((topAncEquiv W M hM).symm (bq₁.1, 1)) = (bq₁.1, 1) :=
        Equiv.apply_symm_apply _ _
      have hbq1_def : topAncEquiv W M hM z₁ = bq₁ := rfl
      have hbq2_def : topAncEquiv W M hM z₂ = bq₂ := rfl
      rw [hsymm0, hsymm1, hbq1_def, hbq2_def]
      simp only [← hb, ite_true]
      set gp := wt (topAncBaseWork bq₁.1)
      have hpyth_c : (gp.2.cVal : ℂ) ^ 2 + (gp.2.sVal : ℂ) ^ 2 = 1 := by
        exact_mod_cast gp.2.cVal_sq_add_sVal_sq
      have hg_star : gp.1.val * star gp.1.val = 1 := gp.1.val_mul_star
      rcases gh_fin2_cases bq₁.2 with h1 | h1 <;> rcases gh_fin2_cases bq₂.2 with h2 | h2 <;>
        rw [h1, h2] <;>
        simp only [Fin.val_zero, Fin.val_one, star_mul', star_neg, RCLike.star_def,
          Complex.conj_ofReal]
      · simp only [↓reduceIte]
        have hgs : gp.1.val * (starRingEnd ℂ) gp.1.val = 1 := hg_star
        linear_combination (gp.2.cVal : ℂ) ^ 2 * hgs + hpyth_c
      · have h01 : (0 : Fin (2 ^ 1)) ≠ 1 := fun h ↦ by have v := congrArg Fin.val h; simp at v
        rw [ite_eq_right h01]
        have hgs : gp.1.val * (starRingEnd ℂ) gp.1.val = 1 := hg_star
        linear_combination (gp.2.cVal : ℂ) * (gp.2.sVal : ℂ) * hgs
      · have h10 : (1 : Fin (2 ^ 1)) ≠ 0 := fun h ↦ by have v := congrArg Fin.val h; simp at v
        rw [ite_eq_right h10]
        have hgs : gp.1.val * (starRingEnd ℂ) gp.1.val = 1 := hg_star
        linear_combination (gp.2.sVal : ℂ) * (gp.2.cVal : ℂ) * hgs
      · simp only [↓reduceIte]
        have hgs : gp.1.val * (starRingEnd ℂ) gp.1.val = 1 := hg_star
        linear_combination (gp.2.sVal : ℂ) ^ 2 * hgs + hpyth_c
    · have hne_z : z₁ ≠ z₂ := fun h ↦ hb (by subst h; rfl)
      rw [ite_eq_right hne_z]
      refine Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun q _ ↦ ?_
      dsimp only [g, U, gaussianHammingGenMat, Matrix.conjTranspose_apply]
      simp only [Matrix.of_apply]
      have hsymm : topAncEquiv W M hM ((topAncEquiv W M hM).symm (b, q)) = (b, q) :=
        Equiv.apply_symm_apply _ _
      rw [hsymm]
      change (if bq₁.1 = b then _ else 0) * star (if bq₂.1 = b then _ else 0) = 0
      by_cases hb1 : bq₁.1 = b
      · have hb2 : bq₂.1 ≠ b := fun h2 ↦ hb (hb1.trans h2.symm)
        rw [ite_eq_right hb2, star_zero, mul_zero]
      · rw [ite_eq_right hb1, zero_mul]⟩
/-- Hamming-weight controlled Gaussian-phase + weak-rotation matrix indexed by `wdHitCount n
  m`. -/
noncomputable abbrev gaussianHammingAllHitMat (n m M : ℕ) (hM : 1 ≤ M)
    (wSpec : ℕ → GaussPyth × PythPair) :
    Matrix (Fin (2 ^ (m * (n + 1) + M))) (Fin (2 ^ (m * (n + 1) + M))) ℂ :=
  gaussianHammingGenMat (m * (n + 1)) M hM (fun w ↦ wSpec (wdHitCount n m w))
/-- Unitary wrapper around `gaussianHammingAllHitMat`, polymorphic in
  `wSpec: ℕ → GaussPyth × PythPair` for any target cardinality `r`. -/
noncomputable abbrev gaussianHammingAllHitUnitary (n m M : ℕ) (hM : 1 ≤ M)
    (wSpec : ℕ → GaussPyth × PythPair) :
    Unitary (2 ^ (m * (n + 1) + M)) :=
  gaussianHammingGenUnitary (m * (n + 1)) M hM (fun w ↦ wSpec (wdHitCount n m w))
/-- No-click `workReg` vector under `wSpec`: scales weight `b = wdHitCount n m w` by
  `(wSpec b).2.cVal * (wSpec b).1.val`. -/
noncomputable def ghDampVec (n m : ℕ) (wSpec : ℕ → GaussPyth × PythPair)
    (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  let gp := wSpec (wdHitCount n m w)
  (gp.2.cVal : ℂ) * gp.1.val * ψ w
/-- Click `workReg` vector under `wSpec`: scales weight `b = wdHitCount n m w` by
  `(wSpec b).2.sVal * (wSpec b).1.val`. -/
noncomputable def ghClickVec (n m : ℕ) (wSpec : ℕ → GaussPyth × PythPair)
    (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  let gp := wSpec (wdHitCount n m w)
  (gp.2.sVal : ℂ) * gp.1.val * ψ w
theorem gaussianHammingGenMat_mulVec_workMemState {W M : ℕ} (hM : 1 ≤ M)
    (wt : Fin (2 ^ W) → GaussPyth × PythPair)
    (ψ : Fin (2 ^ W) → ℂ) {μ : Fin (2 ^ M)} (hμ : μ.val < 2 ^ (M - 1)) :
    gaussianHammingGenMat W M hM wt *ᵥ workMemState ψ (single μ 1) =
      workMemState (fun w ↦ ((wt w).2.cVal : ℂ) * (wt w).1.val * ψ w) (single μ 1) +
        workMemState (fun w ↦ ((wt w).2.sVal : ℂ) * (wt w).1.val * ψ w)
          (single (memWithTopOne hM μ hμ) 1) := by
  funext z
  rw [Matrix.mulVec, dotProduct]
  dsimp only [Pi.add_apply, workMemState]
  let eμ : Fin (2 ^ M) → ℂ := Pi.single μ 1
  let f (y : Fin (2 ^ (W + M))) : ℂ :=
    gaussianHammingGenMat W M hM wt z y *
      (ψ (lowHighEquiv W M y).1 * eμ (lowHighEquiv W M y).2)
  change ∑ y, f y = _
  rw [← (lowHighEquiv W M).symm.sum_comp f, sum_prod_type]
  have hsum_μ (w : Fin (2 ^ W)) :
      (∑ ν : Fin (2 ^ M), f ((lowHighEquiv W M).symm (w, ν))) =
        gaussianHammingGenMat W M hM wt z ((lowHighEquiv W M).symm (w, μ)) * ψ w := by
    rw [sum_eq_single μ (fun ν hν ↦ by
      dsimp only [f, eμ]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hν, mul_zero, mul_zero])]
    dsimp only [f, eμ]
    rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  simp_rw [hsum_μ]
  set w_z := (lowHighEquiv W M z).1
  set ν_z := (lowHighEquiv W M z).2
  have hz_symm : (lowHighEquiv W M).symm (w_z, ν_z) = z := Equiv.symm_apply_apply _ z
  rw [sum_eq_single w_z (fun w hw ↦ by
    dsimp only [gaussianHammingGenMat]
    rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w hμ]
    have hne_b : (topAncEquiv W M hM z).1 ≠ topAncBase hM w hμ := by
      intro heq
      apply hw
      have h1 := lowHigh_fst_topAncEquiv_symm W M hM (topAncEquiv W M hM z).1
        (topAncEquiv W M hM z).2
      rw [Equiv.symm_apply_apply] at h1
      have hval := congrArg Fin.val h1
      rw [heq] at hval
      dsimp only [topAncBase] at hval
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w.isLt] at hval
      exact Fin.ext hval.symm
    change (if (topAncEquiv W M hM z).1 = topAncBase hM w hμ then _ else 0) * ψ w = 0
    rw [ite_eq_right hne_b, zero_mul])]
  have hmod_wz : topAncBaseWork (topAncBase hM w_z hμ) = w_z := by
    ext
    dsimp only [topAncBaseWork, topAncBase]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w_z.isLt]
  by_cases hν0 : ν_z = μ
  · have hν1 : ν_z ≠ memWithTopOne hM μ hμ := by
      rw [hν0]
      intro h
      have hv := congrArg Fin.val h
      dsimp only [memWithTopOne] at hv
      have := Nat.two_pow_pos (M - 1)
      omega
    rw [Pi.single_eq_of_ne hν1, mul_zero, add_zero, hν0, Pi.single_eq_same, mul_one,
      ← hz_symm, hν0]
    dsimp only [gaussianHammingGenMat]
    rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w_z hμ]
    simp only [ite_true, Fin.val_zero]
    rw [hmod_wz]
  · by_cases hν1 : ν_z = memWithTopOne hM μ hμ
    · rw [Pi.single_eq_of_ne hν0, mul_zero, zero_add, hν1, Pi.single_eq_same, mul_one,
        ← hz_symm, hν1]
      dsimp only [gaussianHammingGenMat]
      rw [Matrix.of_apply, topAncEquiv_lowHigh_one hM w_z hμ, topAncEquiv_lowHigh_zero hM w_z hμ]
      simp only [ite_true, Fin.val_one, Fin.val_zero]
      rw [hmod_wz]
    · rw [Pi.single_eq_of_ne hν0, Pi.single_eq_of_ne hν1, mul_zero, mul_zero, add_zero]
      dsimp only [gaussianHammingGenMat]
      rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w_z hμ]
      by_cases hb : (topAncEquiv W M hM z).1 = topAncBase hM w_z hμ
      · exfalso
        rcases gh_fin2_cases (topAncEquiv W M hM z).2 with hq0 | hq1
        · have heq : topAncEquiv W M hM z =
              topAncEquiv W M hM ((lowHighEquiv W M).symm (w_z, μ)) := by
            rw [topAncEquiv_lowHigh_zero hM w_z hμ]
            exact Prod.ext hb hq0
          have hp_eq := congrArg (lowHighEquiv W M) ((topAncEquiv W M hM).injective heq)
          rw [Equiv.apply_symm_apply] at hp_eq
          exact hν0 (congrArg Prod.snd hp_eq)
        · have heq : topAncEquiv W M hM z =
              topAncEquiv W M hM ((lowHighEquiv W M).symm (w_z, memWithTopOne hM μ hμ)) := by
            rw [topAncEquiv_lowHigh_one hM w_z hμ]
            exact Prod.ext hb hq1
          have hp_eq := congrArg (lowHighEquiv W M) ((topAncEquiv W M hM).injective heq)
          rw [Equiv.apply_symm_apply] at hp_eq
          exact hν1 (congrArg Prod.snd hp_eq)
      · change (if (topAncEquiv W M hM z).1 = topAncBase hM w_z hμ then _ else 0) * ψ w_z = 0
        rw [ite_eq_right hb, zero_mul]
theorem gaussianHammingAllHitMat_mulVec_workMemState {n m M : ℕ} (hM : 1 ≤ M)
    (wSpec : ℕ → GaussPyth × PythPair)
    (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) {μ : Fin (2 ^ M)} (hμ : μ.val < 2 ^ (M - 1)) :
    gaussianHammingAllHitMat n m M hM wSpec *ᵥ workMemState ψ (single μ 1) =
      workMemState (ghDampVec n m wSpec ψ) (single μ 1) +
        workMemState (ghClickVec n m wSpec ψ) (single (memWithTopOne hM μ hμ) 1) := by
  rw [gaussianHammingAllHitMat, gaussianHammingGenMat_mulVec_workMemState hM _ ψ hμ]
  rfl
/-- One `r = 2` Gaussian-Hamming probe `(g₁, g₂, rot₂, kNext)`: applies unit-modulus phase
  `g₁` on
  `wdHitCount = 1` (`0`-click `pythOne`) and phase `g₂` + weak rotation `rot₂` on
  `wdHitCount = 2`,
  followed on no-click by `kNext` deflated subcube Grover steps. -/
abbrev GHZoomProbe : Type := GaussPyth × GaussPyth × PythPair × ℕ
/-- Schedule specification `(kInit, probes, kZoom)` for `r = 2` Gaussian-Hamming + Zoom. -/
abbrev GHZoomSpec : Type := Option (ℕ × List GHZoomProbe × ℕ)
/-- Subcube-dimension-parameterized pass function (`subN` -> `r` -> `GHZoomSpec`). -/
abbrev GHZoomPassFn : Type := ℕ → ℕ → GHZoomSpec
/-- Hamming-weight table `wSpec: ℕ → GaussPyth × PythPair` associated to a `GHZoomProbe`. -/
def ghProbeWSpec2 (p : GHZoomProbe) : ℕ → GaussPyth × PythPair
  | 1 => (p.1, pythOne)
  | 2 => (p.2.1, p.2.2.1)
  | _ => (gaussOne, pythOne)
/-- Worst-case parallel oracle queries consumed by `(kInit, probes)` prior to zoom. -/
def ghMaxQueries (kInit : ℕ) (probes : List GHZoomProbe) : ℕ :=
  (kInit + 1) + (probes.map fun p ↦ p.2.2.2 + 2).sum
/-- Worst-case parallel oracle queries consumed by `(kInit, probes, kZoom)` including zoom. -/
def ghZoomMaxQueries (kInit : ℕ) (probes : List GHZoomProbe) (kZoom : ℕ) : ℕ :=
  ghMaxQueries kInit probes + (kZoom + 1)
/-- Initial `r = 2` per-subset complex Dicke amplitude after `kInit` Grover steps + marking. -/
noncomputable def ghInitAmp2 (θ₁ : ℝ) (kInit : ℕ) : ℕ → ℂ :=
  dickeStep 2 (Real.cos ((2 * (kInit : ℝ) + 1) * θ₁) : ℂ)
    (Real.sin ((2 * (kInit : ℝ) + 1) * θ₁) : ℂ)
    (fun b ↦ if b = 0 then 1 else 0)
/-- No-click `r = 2` complex Dicke damping step under `(g₁, g₂, rot₂)`. -/
noncomputable def ghDampAmp2 (g₁ g₂ : GaussPyth) (rot₂ : PythPair) (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => u 0
  | 1 => g₁.val * u 1
  | 2 => (rot₂.cVal : ℂ) * g₂.val * u 2
  | _ => 0
/-- Next `r = 2` complex Dicke amplitude after one `GHZoomProbe` on the no-click branch. -/
noncomputable def ghProbeNextAmp2 (θ₁ : ℝ) (p : GHZoomProbe) (u : ℕ → ℂ) : ℕ → ℂ :=
  dickeStep 2 (Real.cos (2 * (p.2.2.2 : ℝ) * θ₁) : ℂ)
    (Real.sin (2 * (p.2.2.2 : ℝ) * θ₁) : ℂ)
    (ghDampAmp2 p.1 p.2.1 p.2.2.1 u)
/-- Final `r = 2` complex Dicke amplitude at readout when no probe clicks. -/
noncomputable def ghChainFinalAmp2 (θ₁ : ℝ) : List GHZoomProbe → (ℕ → ℂ) → (ℕ → ℂ)
  | [], u => u
  | p :: rest, u => ghChainFinalAmp2 θ₁ rest (ghProbeNextAmp2 θ₁ p u)
/-- Total `r = 2` all-hit click probability accumulated along `probes`. -/
noncomputable def ghChainClickProb2 (θ₁ : ℝ) : List GHZoomProbe → (ℕ → ℂ) → ℝ
  | [], _ => 0
  | p :: rest, u =>
      (p.2.2.1.sVal : ℝ) ^ 2 * Complex.normSq (u 2) +
        ghChainClickProb2 θ₁ rest (ghProbeNextAmp2 θ₁ p u)
/-- Expected extra parallel oracle queries along `probes` on collision-free `r = 2`. -/
noncomputable def ghChainExtraQueries2 (θ₁ : ℝ) : List GHZoomProbe → (ℕ → ℂ) → ℝ
  | [], _ => 0
  | p :: rest, u =>
      let uD := ghDampAmp2 p.1 p.2.1 p.2.2.1 u
      (Complex.normSq (uD 0) + 2 * Complex.normSq (uD 1) + Complex.normSq (uD 2)) *
          ((p.2.2.2 + 2 : ℕ) : ℝ) +
        ghChainExtraQueries2 θ₁ rest (ghProbeNextAmp2 θ₁ p u)
/-- Initial 2D pair-collision state `(z₀, z₁)` after `kInit` Grover steps at angle `θ₂`. -/
noncomputable def ghInitColl2 (θ₂ : ℝ) (kInit : ℕ) : ℂ × ℂ :=
  ((Real.cos ((2 * (kInit : ℝ) + 1) * θ₂) : ℂ),
    (Real.sin ((2 * (kInit : ℝ) + 1) * θ₂) : ℂ))
/-- Next 2D pair-collision state `(z₀, z₁)` after `g₁` phase on `z₁` and `kNext` Grover
  steps. -/
noncomputable def ghProbeNextColl2 (θ₂ : ℝ) (p : GHZoomProbe) (z : ℂ × ℂ) : ℂ × ℂ :=
  let c := (Real.cos (2 * (p.2.2.2 : ℝ) * θ₂) : ℂ)
  let s := (Real.sin (2 * (p.2.2.2 : ℝ) * θ₂) : ℂ)
  let z1D := p.1.val * z.2
  (c * z.1 - s * z1D, s * z.1 + c * z1D)
/-- Final 2D pair-collision state `(z₀, z₁)` after `probes` (`0` clicks occur on `¬ InjOn`). -/
noncomputable def ghChainFinalColl2 (θ₂ : ℝ) : List GHZoomProbe → (ℂ × ℂ) → (ℂ × ℂ)
  | [], z => z
  | p :: rest, z => ghChainFinalColl2 θ₂ rest (ghProbeNextColl2 θ₂ p z)
/-- Certified 1D upper-bound step for `r = 2` Gaussian-Hamming Weak-Dicke + Clicked-Subcube
  Zoom
  at subcube exponent `subN`, slice bit-width `p`, and parallelism `m = 2 ^ p`. -/
noncomputable def ghZoomOneDimUpper (subN p m : ℕ)
    (spec : GHZoomSpec) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0
  else
    match spec with
    | none => f r
    | some (kInit, probes, kZoom) =>
        if r = 2 then
          let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
          let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
          let u₀ := ghInitAmp2 θ₁ kInit
          let uf := ghChainFinalAmp2 θ₁ probes u₀
          let z₀ := ghInitColl2 θ₂ kInit
          let zf := ghChainFinalColl2 θ₂ probes z₀
          let pZoom := p_succ_frac kZoom 1 (2 ^ (subN - p))
          rotCfProb m 2 *
            (((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes u₀ +
              Complex.normSq (uf 0) * f 2 +
              2 * Complex.normSq (uf 1) * (((kZoom + 1 : ℕ) : ℝ) + f 1)) +
            (1 - rotCfProb m 2) *
              ((ghMaxQueries kInit probes : ℝ) +
                Complex.normSq zf.1 * f 2 +
                Complex.normSq zf.2 * (((kZoom + 1 : ℕ) : ℝ) + (1 - pZoom) * f 1))
        else f r
/-! ## Section 2: Unified Subcube/Sub-Subcube Evolution, `wdAmpStateC`, & `ghCollState` -/
/-- Combine inner sub-subcube index `j₂: Fin m` and outer subcube index `j₁: Fin m` into
  `Fin (m * m)`. -/
def zoomCombine {m : ℕ} (j₂ j₁ : Fin m) : Fin (m * m) :=
  ⟨j₂.val + m * j₁.val, by
    have h1 := j₂.isLt
    have h2 := j₁.isLt
    calc j₂.val + m * j₁.val
        < m + m * j₁.val := Nat.add_lt_add_right h1 _
      _ = m * (j₁.val + 1) := by ring
      _ ≤ m * m := Nat.mul_le_mul_left m h2⟩
private lemma zoomCombine_div_mod {m : ℕ} (hm1 : 1 ≤ m) (j₂ j₁ : Fin m) :
    (zoomCombine j₂ j₁).val / m = j₁.val ∧ (zoomCombine j₂ j₁).val % m = j₂.val := by
  have hm_pos : 0 < m := by omega
  dsimp only [zoomCombine]
  constructor
  · rw [Nat.add_mul_div_left _ _ hm_pos, Nat.div_eq_of_lt j₂.isLt, zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j₂.isLt]
private lemma zoomCombine_injective_left {m : ℕ} (hm1 : 1 ≤ m) (j₁ : Fin m) :
    Function.Injective fun j₂ : Fin m ↦ zoomCombine j₂ j₁ := by
  intro a b hab
  dsimp only at hab
  apply Fin.ext
  have ha := (zoomCombine_div_mod hm1 a j₁).2
  have hb := (zoomCombine_div_mod hm1 b j₁).2
  rw [← ha, ← hb, hab]
private lemma subcubePref_val_eq_div {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (z : Fin (2 ^ n)) :
    (subcubePref hp hm z).val = z.val / 2 ^ (n - p) := by
  unfold subcubePref subcubeSplit
  simp [Equiv.trans_apply]
private lemma subcubePref2_div_eq_subcubePref {n p m : ℕ} (_hm1 : 1 ≤ m)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (z : Fin (2 ^ n)) :
    (subcubePref hp2 hm2_pow z).val / m = (subcubePref hp hm z).val := by
  rw [subcubePref_val_eq_div hp2 hm2_pow, subcubePref_val_eq_div hp hm, Nat.div_div_eq_div_mul]
  have hpow : 2 ^ (n - 2 * p) * m = 2 ^ (n - p) := by
    rw [hm, ← pow_add]
    congr 1
    omega
  rw [hpow]
private lemma subcubePref2_eq_zoomCombine_iff {n p m : ℕ} (hm1 : 1 ≤ m)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (z : Fin (2 ^ n)) (j₂ j₁ : Fin m) :
    subcubePref hp2 hm2_pow z = zoomCombine j₂ j₁ ↔
      subcubePref hp hm z = j₁ ∧ (subcubePref hp2 hm2_pow z).val % m = j₂.val := by
  constructor
  · intro heq
    have hdm := zoomCombine_div_mod hm1 j₂ j₁
    have hdiv := subcubePref2_div_eq_subcubePref hm1 hp hm hp2 hm2_pow z
    rw [heq] at hdiv ⊢
    exact ⟨Fin.ext (hdiv.symm.trans hdm.1), hdm.2⟩
  · rintro ⟨hj₁, hmod⟩
    apply Fin.ext
    have hdiv := subcubePref2_div_eq_subcubePref hm1 hp hm hp2 hm2_pow z
    rw [hj₁] at hdiv
    dsimp only [zoomCombine]
    rw [← hmod, ← hdiv, Nat.mod_add_div]
/-- Exported helper `zoomCast1nEquiv`. -/
abbrev zoomCast1nEquiv {n q : ℕ} (hq : q ≤ n) :
    Fin (2 ^ (1 * n)) ≃ Fin (2 ^ ((n - q) + q)) :=
  finCongr (by congr 1; omega)
private lemma extractIndex_wdCast1nReg_zoom {n q : ℕ} (hq : q ≤ n) (u : Fin (2 ^ (1 * n))) :
    (wdCast1nReg hq).extractIndex u = zoomCast1nEquiv hq u := by
  apply (basisBits ((n - q) + q)).injective
  funext r
  rw [basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit]
  simp [wdCast1nReg, zoomCast1nEquiv]
private lemma agreeOutside_wdCast1nReg_zoom {n q : ℕ} (hq : q ≤ n) (i j : Fin (2 ^ (1 * n))) :
    (wdCast1nReg hq).AgreeOutside i j := by
  intro r hr
  exact False.elim (hr ⟨⟨r.val, by omega⟩, Fin.ext (by simp [wdCast1nReg])⟩)
private lemma embedMatrix_wdCast1nReg_mulVec_comp_zoom {n q : ℕ} (hq : q ≤ n)
    (B : Operator (2 ^ ((n - q) + q))) (ψ : Fin (2 ^ ((n - q) + q)) → ℂ) :
    (wdCast1nReg hq).embedMatrix B *ᵥ (ψ ∘ zoomCast1nEquiv hq) = (B *ᵥ ψ) ∘ zoomCast1nEquiv hq := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  simp_rw [QRegister.embedMatrix_apply_of_agreeOutside, extractIndex_wdCast1nReg_zoom,
    agreeOutside_wdCast1nReg_zoom, ite_true, mul_one]
  exact (zoomCast1nEquiv hq).sum_comp (fun y ↦ B (zoomCast1nEquiv hq i) y * ψ y)
private lemma subcubeSplit_addrEquiv_one_zoom {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (u : Fin (2 ^ (1 * n))) :
    subcubeSplit hq hM (addrEquiv n 1 u 0) =
      ((lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).1,
        finCongr hM.symm (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).2) := by
  have hcast : finCongr (by congr 1; omega) (addrEquiv n 1 u 0) = zoomCast1nEquiv hq u := by
    ext
    rw [finCongr_apply, Fin.val_cast, addrEquiv_eq_div_pow_mod]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, finCongr_apply, Fin.val_cast]
    exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using u.isLt)
  unfold subcubeSplit
  rw [Equiv.trans_apply, Equiv.trans_apply, hcast]
  rfl
private lemma mem_oddSet_one_iff_zoom {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) :
    u ∈ oddSet n 1 S ↔ addrEquiv n 1 u 0 ∈ S := by
  rw [oddSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Fin.prod_univ_one]
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h1 ↦ absurd h1 (by norm_num), fun hm ↦ absurd hm h⟩
private lemma firstTupleHit_one_eq_zoom {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) :
    firstTupleHit n 1 S u = if addrEquiv n 1 u 0 ∈ S then some (addrEquiv n 1 u 0) else none := by
  unfold firstTupleHit
  by_cases hu : u ∈ oddSet n 1 S
  · have hmem : addrEquiv n 1 u 0 ∈ S := (mem_oddSet_one_iff_zoom S u).mp hu
    rw [dite_eq_left hu, ite_eq_left hmem]
    exact congrArg (fun j : Fin 1 ↦ some (addrEquiv n 1 u j)) (Subsingleton.elim _ _)
  · have hnmem : addrEquiv n 1 u 0 ∉ S := mt (mem_oddSet_one_iff_zoom S u).mpr hu
    rw [dite_eq_right hu, ite_eq_right hnmem]
private lemma wdPerm1n_symm_zoom {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) :
    (wdPerm1n perm).symm = wdPerm1n perm.symm := by
  ext u; simp [wdPerm1n]
private lemma addrEquiv_wdPerm1n_zero_zoom {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n)))
    (u : Fin (2 ^ (1 * n))) :
    addrEquiv n 1 (wdPerm1n perm u) 0 = perm (addrEquiv n 1 u 0) := by
  have he1n (v : Fin (2 ^ (1 * n))) :
      addrEquiv n 1 v 0 = finCongr (by rw [Nat.one_mul]) v := by
    ext
    rw [addrEquiv_eq_div_pow_mod, finCongr_apply, Fin.val_cast]
    simp only [Fin.val_zero, pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using v.isLt)
  rw [he1n, he1n]
  simp [wdPerm1n]
private lemma permUnitary_mulVec_comp_zoom {d : ℕ} (σ : Equiv.Perm (Fin d)) (ψ : Fin d → ℂ) :
    (permutationUnitary σ).1 *ᵥ ψ = ψ ∘ σ.symm := by
  funext i
  rw [Matrix.mulVec, dotProduct, sum_eq_single (σ.symm i) (fun j hj ↦ by
      have hne : i ≠ σ j := fun h ↦ hj ((σ.symm_apply_eq).mpr h).symm
      rw [permutationUnitary_apply, ite_eq_right hne, zero_mul])]
  rw [permutationUnitary_apply, ite_eq_left (σ.apply_symm_apply i).symm, one_mul]
  rfl
private lemma permUnitary_parallelMarkPerm_mulVec_apply_zoom {n m : ℕ}
    (R : Finset (Fin (2 ^ n))) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ)
    (w : Fin (2 ^ (m * (n + 1)))) :
    ((permutationUnitary (parallelMarkPerm n m R)).1 *ᵥ ψ) w =
      ψ (parallelMarkPerm n m R w) := by
  rw [permUnitary_mulVec_comp_zoom]
  dsimp only [Function.comp_apply]
  congr 1
  exact Equiv.symm_apply_eq _ |>.mpr (parallelMarkPerm_involutive R w).symm
/-- Embeds a `(n - q)`-qubit local subcube state `φ` at prefix `j_sub` under `perm`
  with `0` flag. -/
noncomputable def zoomSlotWrap {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (perm : Equiv.Perm (Fin (2 ^ n))) (j_sub : Fin M_sub) (φ : Fin (2 ^ (n - q)) → ℂ) :
    Fin (2 ^ (1 * (n + 1))) → ℂ :=
  (addrReg n 1).tensorState
    ((workMemState φ (single (finCongr hM j_sub) 1) ∘ zoomCast1nEquiv hq) ∘ wdPerm1n perm)
    (single 0 1)
/-- Tensor product of `m` single-slot states across `groupReg (Nat.mul_one m)`. -/
noncomputable def zoomProdState {n m : ℕ}
    (ξ : Fin m → Fin (2 ^ (1 * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  ∏ j : Fin m, ξ j ((groupReg (Nat.mul_one m) j).extractIndex w)
private lemma zoomSlotWrap_eq_linear {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (perm : Equiv.Perm (Fin (2 ^ n))) (j_sub : Fin M_sub)
    (c s : ℂ) (φ₀ φ₁ : Fin (2 ^ (n - q)) → ℂ) (z : Fin (2 ^ (1 * (n + 1)))) :
    zoomSlotWrap hq hM perm j_sub (c • φ₀ + s • φ₁) z =
      c * zoomSlotWrap hq hM perm j_sub φ₀ z + s * zoomSlotWrap hq hM perm j_sub φ₁ z := by
  dsimp only [zoomSlotWrap, tensorState, workMemState, Function.comp_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
private lemma prod_groupReg_embedMatrix_mulVec_zoom {n m b g : ℕ} (hbg : b * g = m)
    (A : Fin b → Matrix (Fin (2 ^ (g * (n + 1)))) (Fin (2 ^ (g * (n + 1)))) ℂ)
    (f : Fin b → Fin (2 ^ (g * (n + 1))) → ℂ) :
    ((finRange b).map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod *ᵥ
        (fun w ↦ ∏ c : Fin b, f c ((groupReg hbg c).extractIndex w)) =
      fun w ↦ ∏ c : Fin b, (A c *ᵥ f c) ((groupReg hbg c).extractIndex w) := by
  suffices ∀ l : List (Fin b), l.Nodup →
      ((l.map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod) *ᵥ
          (fun w ↦ ∏ c : Fin b, f c ((groupReg hbg c).extractIndex w)) =
        fun w ↦ ∏ c : Fin b,
          (if c ∈ l then A c *ᵥ f c else f c) ((groupReg hbg c).extractIndex w) by
    rw [this (finRange b) (List.nodup_finRange b)]
    funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_left (mem_finRange c)]
  intro l hl
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]
    funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_right List.not_mem_nil]
  | cons c₀ l ih =>
    rcases List.nodup_cons.mp hl with ⟨hc₀, hl'⟩
    rw [map_cons, prod_cons, ← mulVec_mulVec, ih hl', embedMatrix_groupReg_mulVec_prod]
    funext w
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    by_cases h : c = c₀
    · subst h
      rw [ite_eq_left rfl, ite_eq_right hc₀, ite_eq_left List.mem_cons_self]
    · have hmem : c ∈ c₀ :: l ↔ c ∈ l := by simp [List.mem_cons, h]
      by_cases hl_mem : c ∈ l
      · rw [ite_eq_left (hmem.mpr hl_mem), ite_eq_right h, ite_eq_left hl_mem]
      · rw [ite_eq_right (mt hmem.mp hl_mem), ite_eq_right h, ite_eq_right hl_mem]
/-- Single-slot prefix swap loading `j_sub` into the high `q` address qubits. -/
noncomputable def zoomSlotPrefixPerm {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (j_sub : Fin M_sub) : Equiv.Perm (Fin (2 ^ (1 * (n + 1)))) :=
  (addrReg n 1).basisSplitEquiv.trans
    ((Equiv.prodCongr
      ((zoomCast1nEquiv hq).trans
        (((lowHighEquiv (n - q) q).trans
          (Equiv.prodCongr (.refl _) (swap 0 (finCongr hM j_sub)))).trans
          (lowHighEquiv (n - q) q).symm) |>.trans (zoomCast1nEquiv hq).symm)
      (.refl _)).trans (addrReg n 1).basisSplitEquiv.symm)
/-- Parallel `workReg` prefix permutation loading `zoomCombine j₂ j_hit` across all `m`
  slots. -/
noncomputable def zoomWorkPrefixPerm {n p m : ℕ}
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p)) (j_hit : Fin m) :
    Equiv.Perm (Fin (2 ^ (m * (n + 1)))) :=
  (groupSplitEquiv (Nat.mul_one m)).trans
    ((Equiv.piCongrRight fun j₂ : Fin m ↦
        zoomSlotPrefixPerm hp2 hm2_pow (zoomCombine j₂ j_hit)).trans
      (groupSplitEquiv (Nat.mul_one m)).symm)
/-- Archive-controlled `workReg` prefix permutation reading `j_hit` from archive slot
  `slot`. -/
noncomputable def zoomCtrlPrefixPermSlot {n p m k : ℕ} (slot : Fin k)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (perm : Equiv.Perm (Fin (2 ^ n))) :
    Equiv.Perm (Fin (2 ^ (m * (n + 1) + k * n))) :=
  let W := m * (n + 1)
  let M := k * n
  let jHitOf (μ : Fin (2 ^ M)) : Fin m :=
    subcubePref hp hm (perm (addrEquiv n k μ slot))
  let mid : Equiv.Perm (Fin (2 ^ W) × Fin (2 ^ M)) :=
    { toFun := fun p_wm ↦ (zoomWorkPrefixPerm hp2 hm2_pow (jHitOf p_wm.2) p_wm.1, p_wm.2)
      invFun := fun p_wm ↦ ((zoomWorkPrefixPerm hp2 hm2_pow (jHitOf p_wm.2)).symm p_wm.1, p_wm.2)
      left_inv := fun ⟨w, μ⟩ ↦ by simp
      right_inv := fun ⟨w, μ⟩ ↦ by simp }
  (lowHighEquiv W M).trans (mid.trans (lowHighEquiv W M).symm)
/-- Single-slot Hadamard + `perm.symm` unitary on the low `n - q` qubits. -/
noncomputable def zoomSlotHadPerm {n q : ℕ} (hq : q ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) : Unitary (2 ^ (1 * (n + 1))) :=
  (addrReg n 1).embedUnitary (permutationUnitary (wdPerm1n perm.symm)) *
    (addrReg n 1).embedUnitary ((wdCast1nReg hq).embedUnitary
      ((lowBlock (n - q) q).embedUnitary hadamardUnitary))
/-- Parallel `m`-slot Hadamard + `perm.symm` unitary for sub-subcube preparation. -/
noncomputable def zoomHadPermUnitary {n q m : ℕ} (hq : q ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) : Unitary (2 ^ (m * (n + 1))) :=
  ((finRange m).map fun j₂ ↦
    (groupReg (Nat.mul_one m) j₂).embedUnitary (zoomSlotHadPerm hq perm)).prod
/-- Coherent sub-subcube zoom round parameterized by archive control `slot: Fin k` and
  current
  archive count `act1`: searches the `m` sub-subcubes `zoomCombine j₂ (pref
  (archive[slot]))` for
  `kZoom` Grover steps and appends any newly hit target at `act1`. -/
noncomputable def wdZoomSubcubeRoundSlot {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (slot : Fin k) (act1 kZoom : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  .seq (.step (phaseTag (permutationUnitary (zoomCtrlPrefixPermSlot slot hp hm hp2 hm2_pow perm))))
    (.seq (.step (phaseTag ((lowBlock W M).embedUnitary (zoomHadPermUnitary (m := m) hp2 perm))))
      (.seq (wdDeflatedGroverLoop (m := m) (k := k) hp2 perm act1 kZoom)
        (.seq (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k act1))
          (wdReadoutWrite res hm1 hkN act1))))
private lemma zoomSlotPrefixPerm_zero {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (j_sub : Fin M_sub) :
    single (zoomSlotPrefixPerm hq hM j_sub 0) (1 : ℂ) =
      (addrReg n 1).tensorState
        (workMemState (single (0 : Fin (2 ^ (n - q))) 1) (single (finCongr hM j_sub) 1) ∘
          zoomCast1nEquiv hq)
        (single 0 1) := by
  have hbs0 : (addrReg n 1).basisSplitEquiv 0 = (0, 0) := by
    apply Prod.ext
    · apply (basisBits (1 * n)).injective
      funext r; simp [QRegister.basisSplitEquiv]
    · funext e; simp [QRegister.basisSplitEquiv]
  have hc0 : zoomCast1nEquiv hq 0 = 0 := Fin.ext (by simp [zoomCast1nEquiv])
  have hlh0 : lowHighEquiv (n - q) q 0 = (0, 0) :=
    Prod.ext (Fin.ext (by simp [lowHighEquiv])) (Fin.ext (by simp [lowHighEquiv]))
  let u_sub : Fin (2 ^ (1 * n)) :=
    (zoomCast1nEquiv hq).symm ((lowHighEquiv (n - q) q).symm (0, finCongr hM j_sub))
  have hz_eq : zoomSlotPrefixPerm hq hM j_sub 0 =
      (addrReg n 1).basisSplitEquiv.symm (u_sub, 0) := by
    unfold zoomSlotPrefixPerm
    simp only [Equiv.trans_apply, hbs0, Equiv.prodCongr_apply, Prod.map_apply, hc0, hlh0,
      Equiv.refl_apply, Equiv.swap_apply_left]
    rfl
  have hsingle_u :
      (single u_sub (1 : ℂ) : Fin (2 ^ (1 * n)) → ℂ) =
        workMemState (single (0 : Fin (2 ^ (n - q))) 1) (single (finCongr hM j_sub) 1) ∘
          zoomCast1nEquiv hq := by
    funext u
    dsimp only [Function.comp_apply, workMemState]
    by_cases hu : u = u_sub
    · subst hu
      dsimp only [u_sub]
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Pi.single_eq_same,
        Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hu]
      have hne_pair : lowHighEquiv (n - q) q (zoomCast1nEquiv hq u) ≠ (0, finCongr hM j_sub) := by
        intro heq
        apply hu
        dsimp only [u_sub]
        rw [← heq, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      by_cases h1 : (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).1 = 0
      · have h2 : (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).2 ≠ finCongr hM j_sub :=
          fun h2 ↦ hne_pair (Prod.ext h1 h2)
        rw [Pi.single_eq_of_ne h2, mul_zero]
      · rw [Pi.single_eq_of_ne h1, zero_mul]
  rw [hz_eq]
  funext z
  unfold QRegister.tensorState
  by_cases hz : z = (addrReg n 1).basisSplitEquiv.symm (u_sub, 0)
  · subst hz
    rw [Pi.single_eq_same, ← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply,
      ← hsingle_u, Pi.single_eq_same, Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne hz, ← hsingle_u]
    have hne : (addrReg n 1).basisSplitEquiv z ≠ (u_sub, 0) :=
      fun h ↦ hz (by rw [← h, Equiv.symm_apply_apply])
    by_cases h1 : ((addrReg n 1).basisSplitEquiv z).1 = u_sub
    · have h2 : ((addrReg n 1).basisSplitEquiv z).2 ≠ 0 := fun h2 ↦ hne (Prod.ext h1 h2)
      rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [← QRegister.basisSplitEquiv_apply_fst, Pi.single_eq_of_ne h1, zero_mul]
private lemma zoomPrep_mulVec_workMemIdx_slot {n p m k : ℕ} (slot : Fin k)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (μ : Fin (2 ^ (k * n))) :
    let W := m * (n + 1)
    let M := k * n
    let j_hit := subcubePref hp hm (perm (addrEquiv n k μ slot))
    (lowBlock W M).embedMatrix (zoomHadPermUnitary (m := m) hp2 perm).1 *ᵥ
      ((permutationUnitary (zoomCtrlPrefixPermSlot slot hp hm hp2 hm2_pow perm)).1 *ᵥ
        single (workMemIdx n m k 0 μ) 1) =
      workMemState
        (zoomProdState fun j₂ ↦
          zoomSlotWrap hp2 hm2_pow perm (zoomCombine j₂ j_hit)
            (hadamardMatrix (n - 2 * p) *ᵥ single 0 1))
        (single μ 1) := by
  intro W M j_hit
  let hbg1 : m * 1 = m := Nat.mul_one m
  let w_pref := zoomWorkPrefixPerm hp2 hm2_pow j_hit 0
  have hctrl :
      (permutationUnitary (zoomCtrlPrefixPermSlot slot hp hm hp2 hm2_pow perm)).1 *ᵥ
          single (workMemIdx n m k 0 μ) 1 =
        workMemState (single w_pref 1) (single μ 1) := by
    rw [permutationUnitary_mulVec_single]
    have hidx : zoomCtrlPrefixPermSlot slot hp hm hp2 hm2_pow perm (workMemIdx n m k 0 μ) =
        workMemIdx n m k w_pref μ := by
      unfold zoomCtrlPrefixPermSlot workMemIdx
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    rw [hidx, workMemIdx, ← workMemState_single]
  have hw_factor :
      (single w_pref (1 : ℂ) : Fin (2 ^ W) → ℂ) =
        fun w ↦ ∏ j₂ : Fin m,
          (single (zoomSlotPrefixPerm hp2 hm2_pow (zoomCombine j₂ j_hit) 0) (1 : ℂ) :
            Fin (2 ^ (1 * (n + 1))) → ℂ) ((groupReg hbg1 j₂).extractIndex w) := by
    have hex0 (j₂ : Fin m) : (groupReg (n := n) hbg1 j₂).extractIndex 0 = 0 := by
      apply (basisBits (1 * (n + 1))).injective
      funext r; simp [basisBits_extractIndex]
    have hex_wp (j₂ : Fin m) :
        (groupReg hbg1 j₂).extractIndex w_pref =
          zoomSlotPrefixPerm hp2 hm2_pow (zoomCombine j₂ j_hit) 0 := by
      dsimp only [w_pref, zoomWorkPrefixPerm]
      rw [← groupSplitEquiv_apply hbg1, Equiv.trans_apply, Equiv.trans_apply,
        Equiv.apply_symm_apply]
      simp [groupSplitEquiv_apply, hex0 j₂]
    funext w
    by_cases hw : w = w_pref
    · subst hw
      rw [Pi.single_eq_same]
      symm
      refine Finset.prod_eq_one fun j₂ _ ↦ ?_
      rw [hex_wp j₂, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hw]
      symm
      have hne : ∃ j₂ : Fin m,
          (groupReg hbg1 j₂).extractIndex w ≠
            zoomSlotPrefixPerm hp2 hm2_pow (zoomCombine j₂ j_hit) 0 := by
        by_contra hall; push Not at hall
        apply hw
        apply (groupSplitEquiv hbg1).injective
        funext j₂
        rw [groupSplitEquiv_apply, groupSplitEquiv_apply, hall j₂, hex_wp j₂]
      rcases hne with ⟨j₂, hj₂⟩
      exact Finset.prod_eq_zero (Finset.mem_univ j₂) (Pi.single_eq_of_ne hj₂ 1)
  have hslot_had (j₂ : Fin m) :
      (zoomSlotHadPerm hp2 perm).1 *ᵥ
          single (zoomSlotPrefixPerm hp2 hm2_pow (zoomCombine j₂ j_hit) 0) 1 =
        zoomSlotWrap hp2 hm2_pow perm (zoomCombine j₂ j_hit)
          (hadamardMatrix (n - 2 * p) *ᵥ single 0 1) := by
    rw [zoomSlotPrefixPerm_zero]
    unfold zoomSlotHadPerm zoomSlotWrap
    rw [Submonoid.coe_mul, embedUnitary_val, embedUnitary_val, ← mulVec_mulVec,
      QRegister.embedMatrix_mulVec_tensorState, embedUnitary_val,
      embedMatrix_wdCast1nReg_mulVec_comp_zoom, embedUnitary_val,
      embedMatrix_lowBlock_mulVec_workMemState,
      QRegister.embedMatrix_mulVec_tensorState, permUnitary_mulVec_comp_zoom,
      wdPerm1n_symm_zoom, Equiv.symm_symm]
    rfl
  have hcoe : (zoomHadPermUnitary (m := m) hp2 perm).1 =
      ((finRange m).map fun j₂ ↦
        (groupReg hbg1 j₂).embedMatrix (zoomSlotHadPerm hp2 perm).1).prod := by
    unfold zoomHadPermUnitary
    rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  rw [hctrl, embedMatrix_lowBlock_mulVec_workMemState, hw_factor, hcoe,
    prod_groupReg_embedMatrix_mulVec_zoom hbg1]
  congr 1
  funext w
  unfold zoomProdState
  exact Finset.prod_congr rfl fun j₂ _ ↦ by rw [hslot_had j₂]
private lemma wdPrepUnitary_mulVec_workMemIdx_gh {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n))) (μ : Fin (2 ^ (k * n))) :
    (lowBlock (m * (n + 1)) (k * n)).embedMatrix (wdPrepUnitary hp hm perm).1 *ᵥ
        single (workMemIdx n m k 0 μ) 1 =
      workMemState
        (zoomProdState fun j ↦ zoomSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0 1))
        (single μ 1) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hex0 : (addrReg n 1).extractIndex 0 = 0 := by
    apply (basisBits (1 * n)).injective
    funext r; simp [basisBits_extractIndex]
  have henv0 : ((addrReg n 1).basisSplitEquiv 0).2 = 0 := by
    funext e; simp [QRegister.basisSplitEquiv]
  have hzero_comp :
      (single (0 : Fin (2 ^ (1 * n))) (1 : ℂ)) =
        workMemState (single (0 : Fin (2 ^ (n - p))) 1) (single (0 : Fin (2 ^ p)) 1) ∘
          zoomCast1nEquiv hp := by
    rw [workMemState_zero]
    funext u
    dsimp only [Function.comp_apply]
    by_cases hu : u = 0
    · subst hu
      have hc0 : zoomCast1nEquiv hp 0 = 0 := Fin.ext (by simp [zoomCast1nEquiv])
      rw [hc0, Pi.single_eq_same, Pi.single_eq_same]
    · have hcne : zoomCast1nEquiv hp u ≠ 0 := fun h ↦
        hu ((zoomCast1nEquiv hp).injective
          (h.trans (Fin.ext (by simp [zoomCast1nEquiv])).symm))
      rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hcne]
  have hprep_slot (j : Fin m) :
      (wdSlotPrep hp hm perm j).1 *ᵥ single (0 : Fin (2 ^ (1 * (n + 1)))) 1 =
        zoomSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0 1) := by
    unfold wdSlotPrep zoomSlotWrap
    rw [Submonoid.coe_mul, embedUnitary_val, embedUnitary_val, ← mulVec_mulVec,
      QRegister.embedMatrix_mulVec_single_factors, hex0, henv0,
      embedUnitary_val, Submonoid.coe_mul, embedUnitary_val, embedUnitary_val,
      hzero_comp, embedMatrix_wdCast1nReg_mulVec_comp_zoom, ← mulVec_mulVec,
      embedMatrix_highBlock_mulVec_workMemState, permutationUnitary_mulVec_single,
      Equiv.swap_apply_left, embedMatrix_lowBlock_mulVec_workMemState,
      QRegister.embedMatrix_mulVec_tensorState, permUnitary_mulVec_comp_zoom,
      wdPerm1n_symm_zoom, Equiv.symm_symm]
    rfl
  have hsub0 : zoomProdState (n := n) (fun _ : Fin m ↦ single 0 1) = single 0 1 := by
    have hex_g0 (c : Fin m) : (groupReg (n := n) hbg1 c).extractIndex 0 = 0 := by
      apply (basisBits (1 * (n + 1))).injective
      funext r; simp [basisBits_extractIndex]
    funext w
    unfold zoomProdState
    by_cases hw : w = 0
    · subst hw; simp [hex_g0]
    · rw [Pi.single_eq_of_ne hw]
      have hne : ∃ c : Fin m, (groupReg hbg1 c).extractIndex w ≠ 0 := by
        by_contra hall; push Not at hall
        apply hw
        apply (groupSplitEquiv hbg1).injective
        funext c
        rw [groupSplitEquiv_apply, groupSplitEquiv_apply, hall c, hex_g0 c]
      obtain ⟨c, hc⟩ := hne
      exact Finset.prod_eq_zero (Finset.mem_univ c) (Pi.single_eq_of_ne hc 1)
  rw [workMemIdx, ← workMemState_single, embedMatrix_lowBlock_mulVec_workMemState, ← hsub0]
  have hcoe : (wdPrepUnitary hp hm perm).1 =
      ((finRange m).map fun j ↦
        (groupReg hbg1 j).embedMatrix (wdSlotPrep hp hm perm j).1).prod := by
    unfold wdPrepUnitary
    rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  unfold zoomProdState
  rw [hcoe, prod_groupReg_embedMatrix_mulVec_zoom hbg1 _ (fun _ ↦ single 0 1)]
  simp_rw [hprep_slot]
private lemma oracleMat_oddSet_one_mulVec_wdPerm1n_zoom {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n)))
    (R : Finset (Fin (2 ^ n))) (ψ : Fin (2 ^ (1 * n)) → ℂ) :
    oracleMat (oddSet n 1 R) *ᵥ (ψ ∘ wdPerm1n perm) =
      (oracleMat (oddSet n 1 (R.image perm)) *ᵥ ψ) ∘ wdPerm1n perm := by
  funext u
  rw [oracleMat, mulVec_diagonal]
  dsimp only [Function.comp_apply]
  rw [oracleMat, mulVec_diagonal]
  have hiff : u ∈ oddSet n 1 R ↔ wdPerm1n perm u ∈ oddSet n 1 (R.image perm) := by
    rw [mem_oddSet_one_iff_zoom, mem_oddSet_one_iff_zoom, addrEquiv_wdPerm1n_zero_zoom]
    refine ⟨Finset.mem_image_of_mem perm, fun h ↦ ?_⟩
    rcases Finset.mem_image.mp h with ⟨y, hy, heq⟩
    rwa [← perm.injective heq]
  rw [if_congr hiff rfl rfl]
private lemma oracleMat_oddSet_one_mulVec_subcube_zoom {n q M_sub : ℕ}
    (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (T : Finset (Fin (2 ^ n))) (j_sub : Fin M_sub) (ψ : Fin (2 ^ (n - q)) → ℂ) :
    oracleMat (oddSet n 1 T) *ᵥ
        (workMemState ψ (single (finCongr hM j_sub) 1) ∘ zoomCast1nEquiv hq) =
      workMemState (oracleMat (subcubeLocalSet hq hM T j_sub) *ᵥ ψ)
        (single (finCongr hM j_sub) 1) ∘ zoomCast1nEquiv hq := by
  funext u
  rw [oracleMat, mulVec_diagonal]
  dsimp only [Function.comp_apply, workMemState]
  rw [oracleMat, mulVec_diagonal]
  by_cases hj : (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).2 = finCongr hM j_sub
  · have hsp := subcubeSplit_addrEquiv_one_zoom hq hM u
    have hfc : finCongr hM.symm (finCongr hM j_sub) = j_sub := by ext; simp
    rw [hj, hfc] at hsp
    have hiff : u ∈ oddSet n 1 T ↔
        (lowHighEquiv (n - q) q (zoomCast1nEquiv hq u)).1 ∈ subcubeLocalSet hq hM T j_sub := by
      rw [mem_oddSet_one_iff_zoom, mem_subcubeLocalSet_iff, ← hsp, Equiv.symm_apply_apply]
    rw [hj, Pi.single_eq_same, mul_one, mul_one, if_congr hiff rfl rfl]
  · rw [Pi.single_eq_of_ne hj]
    ring
private lemma wdDiffuser_mulVec_sDiagM_zoomProdState {n q M_sub m : ℕ}
    (hq : q ≤ n) (hM : M_sub = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n)))
    (R : Finset (Fin (2 ^ n))) (jSub : Fin m → Fin M_sub)
    (φ : Fin m → Fin (2 ^ (n - q)) → ℂ) :
    (wdDiffuserUnitary (m := m) hq perm).1 *ᵥ
        (sDiagM n m R *ᵥ zoomProdState (fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂) (φ j₂))) =
      zoomProdState (fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂)
        (Grover.diffuserMatrix *ᵥ
          (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂))) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hdiff_coe : (wdDiffuserUnitary (m := m) hq perm).1 =
      ((finRange m).map fun j₂ ↦
        (groupReg hbg1 j₂).embedMatrix (wdSlotDiffuser hq perm).1).prod := by
    unfold wdDiffuserUnitary
    rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  rw [sDiagM_eq_prod_groupReg hbg1 R]
  unfold zoomProdState
  rw [prod_groupReg_embedMatrix_mulVec_zoom hbg1]
  have hslot_p (j₂ : Fin m) :
      sDiagM n 1 R *ᵥ zoomSlotWrap hq hM perm (jSub j₂) (φ j₂) =
        (addrReg n 1).tensorState
          ((workMemState
            (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂)
            (single (finCongr hM (jSub j₂)) 1) ∘ zoomCast1nEquiv hq) ∘ wdPerm1n perm)
          (single 0 1) := by
    unfold zoomSlotWrap
    rw [sDiagM_mulVec_tensorState_zero, oracleMat_oddSet_one_mulVec_wdPerm1n_zoom,
      oracleMat_oddSet_one_mulVec_subcube_zoom]
  simp_rw [hslot_p]
  rw [hdiff_coe, prod_groupReg_embedMatrix_mulVec_zoom hbg1]
  have hslot_d (j₂ : Fin m) :
      (wdSlotDiffuser hq perm).1 *ᵥ
          (addrReg n 1).tensorState
            ((workMemState
              (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂)
              (single (finCongr hM (jSub j₂)) 1) ∘ zoomCast1nEquiv hq) ∘ wdPerm1n perm)
            (single 0 1) =
        zoomSlotWrap hq hM perm (jSub j₂)
          (Grover.diffuserMatrix *ᵥ
            (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂)) := by
    unfold wdSlotDiffuser zoomSlotWrap
    rw [Submonoid.coe_mul, Submonoid.coe_mul,
      (addrReg n 1).embedUnitary_val, (addrReg n 1).embedUnitary_val,
      (addrReg n 1).embedUnitary_val, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
      QRegister.embedMatrix_mulVec_tensorState, permUnitary_mulVec_comp_zoom]
    have hcancel :
        (((workMemState
            (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂)
            (single (finCongr hM (jSub j₂)) 1) ∘ zoomCast1nEquiv hq) ∘ wdPerm1n perm) ∘
          (wdPerm1n perm).symm) =
          workMemState
            (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ φ j₂)
            (single (finCongr hM (jSub j₂)) 1) ∘ zoomCast1nEquiv hq := by
      funext v; simp
    rw [hcancel, QRegister.embedMatrix_mulVec_tensorState,
      embedUnitary_val, embedMatrix_wdCast1nReg_mulVec_comp_zoom,
      embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      QRegister.embedMatrix_mulVec_tensorState,
      permUnitary_mulVec_comp_zoom, wdPerm1n_symm_zoom, Equiv.symm_symm]
    rfl
  simp_rw [hslot_d]
private lemma ghDeflatedGrover_iter_zoomProdState {n q M_sub m k : ℕ}
    (hq : q ≤ n) (hM : M_sub = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n)))
    {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^ (k * n))}
    (hsub : memSeen n k (memPrefix k active) μ ⊆ S)
    (jSub : Fin m → Fin M_sub) (φ : Fin m → Fin (2 ^ (n - q)) → ℂ) (t : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let R := S \ memSeen n k (memPrefix k active) μ
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hq perm).1
    ((diffOp * phaseOp) ^ t) *ᵥ
        workMemState (zoomProdState fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂) (φ j₂))
          (single μ 1) =
      workMemState
        (zoomProdState fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂)
          ((fun ψ ↦ Grover.diffuserMatrix *ᵥ
            (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ ψ))^[t] (φ j₂)))
        (single μ 1) := by
  intro W M R fc orac unm phaseOp diffOp
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, ih]
    have hp_step :
        phaseOp *ᵥ
          workMemState
            (zoomProdState fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂)
              ((fun ψ ↦ Grover.diffuserMatrix *ᵥ
                (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ ψ))^[t]
                  (φ j₂)))
            (single μ 1) =
        workMemState
          (sDiagM n m R *ᵥ
            zoomProdState fun j₂ ↦ zoomSlotWrap hq hM perm (jSub j₂)
              ((fun ψ ↦ Grover.diffuserMatrix *ᵥ
                (oracleMat (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) *ᵥ ψ))^[t]
                  (φ j₂)))
          (single μ 1) := by
      simpa [phaseOp, fc, unm, orac, R, Matrix.mul_assoc] using
        deflatedPhaseMat_mulVec_workMemState (memPrefix k active) _ μ hsub
    rw [hp_step]
    dsimp only [diffOp]
    rw [embedMatrix_lowBlock_mulVec_workMemState, wdDiffuser_mulVec_sDiagM_zoomProdState]
    simp only [Function.iterate_succ_apply']
private lemma zoomDeflatedGrover_iter {n q M_sub m k : ℕ}
    (hq : q ≤ n) (hM : M_sub = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n)))
    {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^ (k * n))}
    (hsub : memSeen n k (memPrefix k active) μ ⊆ S)
    (jSub : Fin m → Fin M_sub) (t : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let R := S \ memSeen n k (memPrefix k active) μ
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hq perm).1
    ((diffOp * phaseOp) ^ t) *ᵥ
        workMemState
          (zoomProdState fun j₂ ↦
            zoomSlotWrap hq hM perm (jSub j₂) (hadamardMatrix (n - q) *ᵥ single 0 1))
          (single μ 1) =
      workMemState
        (zoomProdState fun j₂ ↦
          zoomSlotWrap hq hM perm (jSub j₂)
            (groverMultiState (subcubeLocalSet hq hM (R.image perm) (jSub j₂)) t))
        (single μ 1) := by
  intro W M R fc orac unm phaseOp diffOp
  rw [ghDeflatedGrover_iter_zoomProdState hq hM perm hsub jSub _ t]
  congr 1; funext w; unfold zoomProdState
  refine Finset.prod_congr rfl fun j₂ _ ↦ ?_
  dsimp only
  rw [← groverMultiState_zero_eq_hadamard_mulVec (subcubeLocalSet hq hM (R.image perm) (jSub j₂))]
  have hgm (M_loc : Finset (Fin (2 ^ (n - q)))) (s : ℕ) :
      (fun ψ ↦ Grover.diffuserMatrix *ᵥ (oracleMat M_loc *ᵥ ψ))^[s] (groverMultiState M_loc 0) =
        groverMultiState M_loc s := by
    induction s with
    | zero => rfl
    | succ s ihs =>
      rw [Function.iterate_succ_apply', ihs]
      exact (groverMultiState_succ M_loc s).symm
  rw [hgm]
private lemma zoomSlotWrap_support_firstMarkedAddr {n q M_sub : ℕ}
    (hq : q ≤ n) (hM : M_sub = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n)))
    (R : Finset (Fin (2 ^ n))) (j_sub : Fin M_sub)
    (φ : Fin (2 ^ (n - q)) → ℂ) (z : Fin (2 ^ (1 * (n + 1))))
    (hz : zoomSlotWrap hq hM perm j_sub φ z ≠ 0) :
    let u := (addrReg n 1).extractIndex z
    let w_loc := (lowHighEquiv (n - q) q (zoomCast1nEquiv hq (wdPerm1n perm u))).1
    ((addrReg n 1).basisSplitEquiv z).2 = 0 ∧
      φ w_loc ≠ 0 ∧
      (lowHighEquiv (n - q) q (zoomCast1nEquiv hq (wdPerm1n perm u))).2 = finCongr hM j_sub ∧
      firstMarkedAddr n 1 (parallelMarkPerm n 1 R z) =
        if w_loc ∈ subcubeLocalSet hq hM (R.image perm) j_sub then
          some (perm.symm ((subcubeSplit hq hM).symm (w_loc, j_sub)))
        else none := by
  intro u w_loc
  have hE : ((addrReg n 1).basisSplitEquiv z).2 = 0 := by
    by_contra hne
    apply hz
    dsimp only [zoomSlotWrap, tensorState]
    rw [Pi.single_eq_of_ne hne, mul_zero]
  have hy : (lowHighEquiv (n - q) q (zoomCast1nEquiv hq (wdPerm1n perm u))).2 =
      finCongr hM j_sub := by
    by_contra hne
    apply hz
    dsimp only [zoomSlotWrap, tensorState, workMemState, Function.comp_apply]
    rw [Pi.single_eq_of_ne hne, mul_zero, zero_mul]
  have hφ : φ w_loc ≠ 0 := by
    intro h0
    apply hz
    dsimp only [zoomSlotWrap, tensorState, workMemState, Function.comp_apply]
    rw [h0, zero_mul, zero_mul]
  refine ⟨hE, hφ, hy, ?_⟩
  rw [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R z hE, firstTupleHit_one_eq_zoom]
  set v := wdPerm1n perm u
  have hu_eq : u = (wdPerm1n perm).symm v := (Equiv.symm_apply_apply _ u).symm
  have hsp := subcubeSplit_addrEquiv_one_zoom hq hM v
  have hfc : finCongr hM.symm (finCongr hM j_sub) = j_sub := by ext; simp
  rw [hy, hfc] at hsp
  have hv_addr : addrEquiv n 1 v 0 = (subcubeSplit hq hM).symm (w_loc, j_sub) := by
    rw [← hsp, Equiv.symm_apply_apply]
  have hu_addr : addrEquiv n 1 u 0 = perm.symm ((subcubeSplit hq hM).symm (w_loc, j_sub)) := by
    rw [hu_eq, wdPerm1n_symm_zoom, addrEquiv_wdPerm1n_zero_zoom, hv_addr]
  have hmem_iff : addrEquiv n 1 u 0 ∈ R ↔ w_loc ∈ subcubeLocalSet hq hM (R.image perm) j_sub := by
    rw [hu_addr, mem_subcubeLocalSet_iff]
    constructor
    · intro hxR
      simpa using Finset.mem_image_of_mem perm hxR
    · intro himg
      rcases Finset.mem_image.mp himg with ⟨x, hxR, hx_perm⟩
      have hxeq : x = perm.symm ((subcubeSplit hq hM).symm (w_loc, j_sub)) := by
        rw [← hx_perm, Equiv.symm_apply_apply]
      rwa [← hxeq]
  rw [if_congr hmem_iff rfl rfl, hu_addr]
private lemma groupHits_of_zoomSlotWrap {n q M_sub m : ℕ}
    (hq : q ≤ n) (hM : M_sub = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n)))
    (R : Finset (Fin (2 ^ n))) (jSub : Fin m → Fin M_sub)
    (φ : Fin m → Fin (2 ^ (n - q)) → ℂ) (o : Fin (2 ^ (m * (n + 1))))
    (hslot_nz : ∀ j₂ : Fin m,
      zoomSlotWrap hq hM perm (jSub j₂) (φ j₂)
        ((groupReg (Nat.mul_one m) j₂).extractIndex (parallelMarkPerm n m R o)) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∀ (j₂ : Fin m) (x : Fin (2 ^ n)),
      firstMarkedAddr n 1 ((groupReg hbg1 j₂).extractIndex o) = some x →
        x ∈ R ∧ subcubePref hq hM (perm x) = jSub j₂) ∧
    (groupHits hbg1 o).toFinset =
      ((finRange m).filterMap fun j₂ ↦
        firstMarkedAddr n 1 ((groupReg hbg1 j₂).extractIndex o)).toFinset := by
  intro hbg1
  have hmem_sub (j₂ : Fin m) (x : Fin (2 ^ n))
      (hx : firstMarkedAddr n 1 ((groupReg hbg1 j₂).extractIndex o) = some x) :
      x ∈ R ∧ subcubePref hq hM (perm x) = jSub j₂ := by
    set w := parallelMarkPerm n m R o
    have ho_eq : o = parallelMarkPerm n m R w := (parallelMarkPerm_involutive R o).symm
    have hsp := zoomSlotWrap_support_firstMarkedAddr hq hM perm R (jSub j₂) (φ j₂) _ (hslot_nz j₂)
    have hex_o : (groupReg hbg1 j₂).extractIndex o =
        parallelMarkPerm n 1 R ((groupReg hbg1 j₂).extractIndex w) := by
      rw [ho_eq, extractIndex_groupReg_parallelMarkPerm]
    rw [hex_o, hsp.2.2.2] at hx
    set w_loc := (lowHighEquiv (n - q) q
      (zoomCast1nEquiv hq (wdPerm1n perm
        ((addrReg n 1).extractIndex ((groupReg hbg1 j₂).extractIndex w))))).1
    by_cases hmem : w_loc ∈ subcubeLocalSet hq hM (R.image perm) (jSub j₂)
    · rw [ite_eq_left hmem, Option.some.injEq] at hx
      subst hx
      have h_perm := (mem_subcubeLocalSet_iff hq hM (R.image perm) (jSub j₂) w_loc).mp hmem
      rcases Finset.mem_image.mp h_perm with ⟨y, hyR, hy_perm⟩
      have hyeq : y = perm.symm ((subcubeSplit hq hM).symm (w_loc, jSub j₂)) := by
        rw [← hy_perm, Equiv.symm_apply_apply]
      refine ⟨hyeq ▸ hyR, ?_⟩
      dsimp only [subcubePref]
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · rw [ite_eq_right hmem] at hx
      cases hx
  refine ⟨hmem_sub, ?_⟩
  unfold groupHits
  exact List.toFinset_dedup
private lemma groupHits_eq_filterMap_of_zoomSlotWrap {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n)))
    (φ : Fin m → Fin (2 ^ (n - p)) → ℂ) (o : Fin (2 ^ (m * (n + 1))))
    (hslot_nz : ∀ j : Fin m,
      zoomSlotWrap hp hm perm j (φ j)
        ((groupReg (Nat.mul_one m) j).extractIndex (parallelMarkPerm n m R o)) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∀ (j : Fin m) (x : Fin (2 ^ n)),
      firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) = some x →
        x ∈ R ∧ subcubePref hp hm (perm x) = j) ∧
      groupHits hbg1 o =
        (finRange m).filterMap fun j ↦ firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) := by
  intro hbg1
  have hhit_sub := (groupHits_of_zoomSlotWrap hp hm perm R id φ o hslot_nz).1
  have hfm_nodup : ∀ (l : List (Fin m)), l.Nodup →
      (l.filterMap fun j ↦ firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).Nodup := by
    intro l hl
    induction l with
    | nil => exact List.nodup_nil
    | cons j js ih =>
      rcases List.nodup_cons.mp hl with ⟨hj_not, hjs_nd⟩
      cases hfa : firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) with
      | none =>
        simp only [List.filterMap_cons, hfa]
        exact ih hjs_nd
      | some x =>
        simp only [List.filterMap_cons, hfa, List.nodup_cons]
        refine ⟨fun hmem ↦ ?_, ih hjs_nd⟩
        rcases List.mem_filterMap.mp hmem with ⟨j', hj'mem, hj'eq⟩
        have hjeq : j = j' := (hhit_sub j x hfa).2.symm.trans (hhit_sub j' x hj'eq).2
        exact hj_not (hjeq ▸ hj'mem)
  refine ⟨hhit_sub, ?_⟩
  unfold groupHits
  exact List.dedup_eq_self.mpr (hfm_nodup (finRange m) (List.nodup_finRange m))
private lemma zoom_groverMultiState_eq_of_mem {q : ℕ} {M : Finset (Fin (2 ^ q))} (t : ℕ)
    {u₁ u₂ : Fin (2 ^ q)} (h₁ : u₁ ∈ M) (h₂ : u₂ ∈ M) :
    groverMultiState M t u₁ = groverMultiState M t u₂ := by
  induction t with
  | zero =>
    rw [groverMultiState_zero_eq_hadamard_mulVec, mulVec_single_one,
      col_apply, col_apply, hadamardMatrix_apply_zero, hadamardMatrix_apply_zero]
  | succ t ih =>
    rw [groverMultiState_succ]
    set w := oracleMat M *ᵥ groverMultiState M t
    have hw : w u₁ = w u₂ := by
      dsimp only [w]
      rw [oracleMat, mulVec_diagonal, mulVec_diagonal, ite_eq_left h₁, ite_eq_left h₂, ih]
    rw [Grover.diffuserMatrix, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hw]
private lemma zoom_normSq_groverMultiState_of_mem_eq {d : ℕ}
    {M_loc : Finset (Fin (2 ^ d))} (K_sub : ℕ) {w : Fin (2 ^ d)} (hw : w ∈ M_loc) :
    normSq (groverMultiState M_loc K_sub w) * (M_loc.card : ℝ) =
      p_succ_frac K_sub M_loc.card (2 ^ d) := by
  have hconst : ∀ u ∈ M_loc,
      normSq (groverMultiState M_loc K_sub u) = normSq (groverMultiState M_loc K_sub w) := by
    intro u hu
    rw [zoom_groverMultiState_eq_of_mem K_sub hu hw]
  have hsum := sum_mem_normSq_groverMultiState_eq_p_succ_frac M_loc K_sub
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm] at hsum
  exact hsum
private lemma sum_normSq_zoomSlotWrap_of_norm {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (perm : Equiv.Perm (Fin (2 ^ n))) (j_sub : Fin M_sub) (φ : Fin (2 ^ (n - q)) → ℂ)
    (S_norm : ℝ) (hφ : (∑ u : Fin (2 ^ (n - q)), normSq (φ u)) = S_norm) :
    (∑ z : Fin (2 ^ (1 * (n + 1))), normSq (zoomSlotWrap hq hM perm j_sub φ z)) = S_norm := by
  rw [← (addrReg n 1).basisSplitEquiv.symm.sum_comp, sum_prod_type]
  have hflag (u : Fin (2 ^ (1 * n))) :
      (∑ e, normSq (zoomSlotWrap hq hM perm j_sub φ
        ((addrReg n 1).basisSplitEquiv.symm (u, e)))) =
        normSq (((workMemState φ (single (finCongr hM j_sub) 1) ∘
          zoomCast1nEquiv hq) ∘ wdPerm1n perm) u) := by
    rw [sum_eq_single 0 (fun e he ↦ by
      dsimp only [zoomSlotWrap, tensorState]
      rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
      dsimp only
      rw [Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero])]
    dsimp only [zoomSlotWrap, tensorState]
    rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    dsimp only
    rw [Pi.single_eq_same, mul_one]
  simp_rw [hflag]
  rw [← (wdPerm1n perm).symm.sum_comp]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [← (zoomCast1nEquiv hq).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [← (lowHighEquiv (n - q) q).symm.sum_comp, sum_prod_type]
  have hhigh (w_loc : Fin (2 ^ (n - q))) :
      (∑ y : Fin (2 ^ q), normSq (workMemState φ (single (finCongr hM j_sub) 1)
        ((lowHighEquiv (n - q) q).symm (w_loc, y)))) = normSq (φ w_loc) := by
    rw [sum_eq_single (finCongr hM j_sub) (fun y hy ↦ by
      dsimp only [workMemState]
      rw [Equiv.apply_symm_apply]
      dsimp only
      rw [Pi.single_eq_of_ne hy, mul_zero, Complex.normSq_zero])]
    dsimp only [workMemState]
    rw [Equiv.apply_symm_apply]
    dsimp only
    rw [Pi.single_eq_same, mul_one]
  simp_rw [hhigh]
  exact hφ
private lemma sum_normSq_zoomProdState {n m : ℕ}
    (ξ : Fin m → Fin (2 ^ (1 * (n + 1))) → ℂ) :
    (∑ w : Fin (2 ^ (m * (n + 1))), normSq (zoomProdState ξ w)) =
      ∏ j : Fin m, ∑ z : Fin (2 ^ (1 * (n + 1))), normSq (ξ j z) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  rw [← (groupSplitEquiv hbg1).symm.sum_comp]
  have hex (g : Fin m → Fin (2 ^ (1 * (n + 1)))) :
      normSq (zoomProdState ξ ((groupSplitEquiv hbg1).symm g)) =
        ∏ j : Fin m, normSq (ξ j (g j)) := by
    unfold zoomProdState
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
  simp_rw [hex]
  exact (Fintype.prod_sum fun j z ↦ normSq (ξ j z)).symm
private lemma sum_normSq_zoomSlotWrap_total {n q M_sub : ℕ} (hq : q ≤ n) (hM : M_sub = 2 ^ q)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (K_sub : ℕ) (j_sub : Fin M_sub) :
    (∑ z : Fin (2 ^ (1 * (n + 1))),
      (normSq (zoomSlotWrap hq hM perm j_sub
        (groverMultiState (subcubeLocalSet hq hM (R.image perm) j_sub) K_sub) z) : ℂ)) = 1 := by
  rw [← Complex.ofReal_sum,
    sum_normSq_zoomSlotWrap_of_norm hq hM perm j_sub _ 1 (sum_normSq_groverMultiState_eq_one _ _),
    Complex.ofReal_one]
private lemma sum_normSq_zoomSlotWrap_hit_singleton {n q M_sub : ℕ}
    (hq : q ≤ n) (hM : M_sub = 2 ^ q) (perm : Equiv.Perm (Fin (2 ^ n)))
    (y : Fin (2 ^ n)) (K_sub : ℕ) (j_sub : Fin M_sub)
    (hy_pref : subcubePref hq hM (perm y) = j_sub) :
    let R : Finset (Fin (2 ^ n)) := {y}
    let ξ := zoomSlotWrap hq hM perm j_sub
      (groverMultiState (subcubeLocalSet hq hM (R.image perm) j_sub) K_sub)
    (∑ z : Fin (2 ^ (1 * (n + 1))),
      if firstMarkedAddr n 1 (parallelMarkPerm n 1 R z) = some y then
        (normSq (ξ z) : ℂ)
      else 0) = (p_succ_frac K_sub 1 (2 ^ (n - q)) : ℂ) := by
  intro R ξ
  let M_loc := subcubeLocalSet hq hM (R.image perm) j_sub
  have hM_card : M_loc.card = 1 := by
    dsimp only [M_loc, R]
    rw [card_subcubeLocalSet_eq]
    have hfilt : (({y} : Finset (Fin (2 ^ n))).image perm).filter
        (fun x ↦ subcubePref hq hM x = j_sub) = {perm y} := by
      ext z
      simp only [Finset.image_singleton, Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ hy_pref⟩⟩
    rw [hfilt, Finset.card_singleton]
  let w₀ : Fin (2 ^ (n - q)) := (subcubeSplit hq hM (perm y)).1
  have hpair : (subcubeSplit hq hM).symm (w₀, j_sub) = perm y := by
    have hsp : subcubeSplit hq hM (perm y) = (w₀, j_sub) := Prod.ext rfl hy_pref
    rw [← hsp, Equiv.symm_apply_apply]
  have hw₀_mem : w₀ ∈ M_loc := by
    dsimp only [M_loc, R]
    rw [mem_subcubeLocalSet_iff, hpair]
    exact Finset.mem_image_of_mem perm (Finset.mem_singleton_self y)
  rw [← (addrReg n 1).basisSplitEquiv.symm.sum_comp, sum_prod_type]
  have hf_zero (u : Fin (2 ^ (1 * n))) :
      (∑ f : (addrReg n 1).Environment → ZMod 2,
        if firstMarkedAddr n 1 (parallelMarkPerm n 1 R
            ((addrReg n 1).basisSplitEquiv.symm (u, f))) = some y then
          (normSq (ξ ((addrReg n 1).basisSplitEquiv.symm (u, f))) : ℂ)
        else 0) =
      if firstTupleHit n 1 R u = some y then
        (normSq (((workMemState (groverMultiState M_loc K_sub)
          (single (finCongr hM j_sub) 1) ∘ zoomCast1nEquiv hq) ∘ wdPerm1n perm) u) : ℂ)
      else 0 := by
    rw [sum_eq_single 0 (fun f hf ↦ by
      dsimp only [ξ]
      unfold zoomSlotWrap QRegister.tensorState
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hf, mul_zero,
        Complex.normSq_zero, Complex.ofReal_zero, ite_self])]
    set z₀ := (addrReg n 1).basisSplitEquiv.symm (u, 0)
    have hf0 : ((addrReg n 1).basisSplitEquiv z₀).2 = 0 := by
      dsimp only [z₀]; rw [Equiv.apply_symm_apply]
    have hhit := firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R z₀ hf0
    have hex : (addrReg n 1).extractIndex z₀ = u := by
      dsimp only [z₀]; rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    rw [hhit, hex]
    dsimp only [ξ]
    unfold zoomSlotWrap QRegister.tensorState
    rw [hf0, hex, Pi.single_eq_same, mul_one]
  simp_rw [hf_zero]
  rw [← (wdPerm1n perm).symm.sum_comp]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [← (zoomCast1nEquiv hq).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [← (lowHighEquiv (n - q) q).symm.sum_comp, sum_prod_type]
  have hprod_sum (w_loc : Fin (2 ^ (n - q))) :
      (∑ j' : Fin (2 ^ q),
        if firstTupleHit n 1 R ((wdPerm1n perm).symm ((zoomCast1nEquiv hq).symm
            ((lowHighEquiv (n - q) q).symm (w_loc, j')))) = some y then
          (normSq (workMemState (groverMultiState M_loc K_sub) (single (finCongr hM j_sub) 1)
            ((lowHighEquiv (n - q) q).symm (w_loc, j'))) : ℂ)
        else 0) =
      if w_loc = w₀ then (normSq (groverMultiState M_loc K_sub w_loc) : ℂ) else 0 := by
    rw [sum_eq_single (finCongr hM j_sub) (fun j' hj' ↦ by
      dsimp only [workMemState]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hj', mul_zero,
        Complex.normSq_zero, Complex.ofReal_zero, ite_self])]
    set u₀ := (wdPerm1n perm).symm ((zoomCast1nEquiv hq).symm
      ((lowHighEquiv (n - q) q).symm (w_loc, finCongr hM j_sub)))
    have hsp := subcubeSplit_addrEquiv_one_zoom hq hM (wdPerm1n perm u₀)
    have hfc : finCongr hM.symm (finCongr hM j_sub) = j_sub := by ext; simp
    have hlh : lowHighEquiv (n - q) q (zoomCast1nEquiv hq (wdPerm1n perm u₀)) =
        (w_loc, finCongr hM j_sub) := by dsimp only [u₀]; simp
    rw [addrEquiv_wdPerm1n_zero_zoom, hlh, hfc] at hsp
    have hu₀_addr : addrEquiv n 1 u₀ 0 =
        perm.symm ((subcubeSplit hq hM).symm (w_loc, j_sub)) := by
      apply perm.injective
      rw [Equiv.apply_symm_apply, ← hsp, Equiv.symm_apply_apply]
    have hiff : firstTupleHit n 1 R u₀ = some y ↔ w_loc = w₀ := by
      rw [firstTupleHit_one_eq_zoom, hu₀_addr]
      constructor
      · intro h
        have hmem : perm.symm ((subcubeSplit hq hM).symm (w_loc, j_sub)) ∈ R := by
          by_contra hnmem; rw [ite_eq_right hnmem] at h; cases h
        have heq : perm.symm ((subcubeSplit hq hM).symm (w_loc, j_sub)) = y :=
          Finset.mem_singleton.mp hmem
        have hp : (subcubeSplit hq hM).symm (w_loc, j_sub) =
            (subcubeSplit hq hM).symm (w₀, j_sub) := by
          rw [hpair, ← heq, Equiv.apply_symm_apply]
        exact congrArg Prod.fst ((subcubeSplit hq hM).symm.injective hp)
      · rintro rfl
        have heq : perm.symm ((subcubeSplit hq hM).symm (w₀, j_sub)) = y := by
          rw [hpair, Equiv.symm_apply_apply]
        have hmem : perm.symm ((subcubeSplit hq hM).symm (w₀, j_sub)) ∈ R :=
          heq ▸ Finset.mem_singleton_self y
        rw [ite_eq_left hmem, heq]
    dsimp only [workMemState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one, if_congr hiff rfl rfl]
  simp_rw [hprod_sum]
  rw [sum_eq_single w₀ (fun w hw ↦ ite_eq_right hw), ite_eq_left rfl]
  have hnsq := zoom_normSq_groverMultiState_of_mem_eq K_sub hw₀_mem
  rw [hM_card, Nat.cast_one, mul_one] at hnsq
  exact congrArg Complex.ofReal hnsq
private lemma sum_normSq_zoomReadout_singleton {n p m : ℕ} (hm1 : 1 ≤ m)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (y : Fin (2 ^ n)) (j_hit : Fin m)
    (kZoom : ℕ) (G : Finset (Fin (2 ^ n)) → ℂ) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    let R : Finset (Fin (2 ^ n)) := {y}
    let jSub (j₂ : Fin m) : Fin (m * m) := zoomCombine j₂ j_hit
    let ξ (j₂ : Fin m) := zoomSlotWrap hp2 hm2_pow perm (jSub j₂)
      (groverMultiState (subcubeLocalSet hp2 hm2_pow (R.image perm) (jSub j₂)) kZoom)
    let pZoom := p_succ_frac kZoom 1 (2 ^ (n - 2 * p))
    (∑ o : Fin (2 ^ (m * (n + 1))),
      (normSq (zoomProdState ξ (parallelMarkPerm n m R o)) : ℂ) *
        G (R \ (groupHits hbg1 o).toFinset)) =
      if subcubePref hp hm (perm y) = j_hit then
        (pZoom : ℂ) * G ∅ + ((1 - pZoom : ℝ) : ℂ) * G R
      else
        G R := by
  intro hbg1 R jSub ξ pZoom
  let hitZ (z : Fin (2 ^ (1 * (n + 1)))) : Option (Fin (2 ^ n)) :=
    firstMarkedAddr n 1 (parallelMarkPerm n 1 R z)
  have h1 :
      (∑ o : Fin (2 ^ (m * (n + 1))),
        (normSq (zoomProdState ξ (parallelMarkPerm n m R o)) : ℂ) *
          G (R \ (groupHits hbg1 o).toFinset)) =
      ∑ zs : Fin m → Fin (2 ^ (1 * (n + 1))),
        (∏ j₂ : Fin m, (normSq (ξ j₂ (zs j₂)) : ℂ)) *
          G (R \ (groupHits hbg1
            (parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs))).toFinset) := by
    rw [← Equiv.sum_comp (parallelMarkPerm n m R)]
    simp_rw [parallelMarkPerm_involutive]
    rw [← (groupSplitEquiv hbg1).symm.sum_comp]
    refine Finset.sum_congr rfl fun zs _ ↦ ?_
    have hex (j₂ : Fin m) :
        (groupReg hbg1 j₂).extractIndex ((groupSplitEquiv hbg1).symm zs) = zs j₂ := by
      rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
    congr 1
    unfold zoomProdState
    simp_rw [hex, map_prod, Complex.ofReal_prod]
  rw [h1]
  have htot_one (j₂ : Fin m) :
      (∑ z : Fin (2 ^ (1 * (n + 1))), (normSq (ξ j₂ z) : ℂ)) = 1 :=
    sum_normSq_zoomSlotWrap_total hp2 hm2_pow perm R kZoom (jSub j₂)
  by_cases hy_hit : subcubePref hp hm (perm y) = j_hit
  · rw [ite_eq_left hy_hit]
    let j₂_star : Fin m := ⟨(subcubePref hp2 hm2_pow (perm y)).val % m,
      Nat.mod_lt _ (by omega)⟩
    have hy_sub : subcubePref hp2 hm2_pow (perm y) = jSub j₂_star :=
      (subcubePref2_eq_zoomCombine_iff hm1 hp hm hp2 hm2_pow (perm y) j₂_star j_hit).mpr
        ⟨hy_hit, rfl⟩
    have hterm_simplify (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) :
        (∏ j₂ : Fin m, (normSq (ξ j₂ (zs j₂)) : ℂ)) *
            G (R \ (groupHits hbg1
              (parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs))).toFinset) =
          (∏ j₂ : Fin m, (normSq (ξ j₂ (zs j₂)) : ℂ)) *
            (if hitZ (zs j₂_star) = some y then G ∅ else G R) := by
      by_cases hzero : (∏ j₂ : Fin m, (normSq (ξ j₂ (zs j₂)) : ℂ)) = 0
      · rw [hzero, zero_mul, zero_mul]
      · congr 1
        have hnz (j₂ : Fin m) : ξ j₂ (zs j₂) ≠ 0 := fun hj0 ↦ hzero
          (Finset.prod_eq_zero (Finset.mem_univ j₂)
            (by rw [hj0, Complex.normSq_zero, Complex.ofReal_zero]))
        have hex (j₂ : Fin m) :
            (groupReg hbg1 j₂).extractIndex ((groupSplitEquiv hbg1).symm zs) = zs j₂ := by
          rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
        set o_zs := parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs)
        have hslot_nz (j₂ : Fin m) :
            ξ j₂ ((groupReg hbg1 j₂).extractIndex (parallelMarkPerm n m R o_zs)) ≠ 0 := by
          dsimp only [o_zs]; rw [parallelMarkPerm_involutive, hex]; exact hnz j₂
        rcases groupHits_of_zoomSlotWrap hp2 hm2_pow perm R jSub _ o_zs hslot_nz with
          ⟨hmem_sub, htoFin⟩
        have hhit_iff (j₂ : Fin m) (x : Fin (2 ^ n)) :
            firstMarkedAddr n 1 ((groupReg hbg1 j₂).extractIndex o_zs) = some x ↔
              j₂ = j₂_star ∧ x = y ∧ hitZ (zs j₂_star) = some y := by
          constructor
          · intro hx
            rcases hmem_sub j₂ x hx with ⟨hxR, hx_sub⟩
            have hxy : x = y := Finset.mem_singleton.mp hxR
            subst hxy
            have hj_eq : j₂ = j₂_star :=
              zoomCombine_injective_left hm1 j_hit (hx_sub.symm.trans hy_sub)
            subst hj_eq
            refine ⟨rfl, rfl, ?_⟩
            dsimp only [o_zs, hitZ] at hx ⊢
            rwa [extractIndex_groupReg_parallelMarkPerm, hex] at hx
          · rintro ⟨rfl, rfl, hst⟩
            dsimp only [o_zs]
            rwa [extractIndex_groupReg_parallelMarkPerm, hex]
        by_cases hst : hitZ (zs j₂_star) = some y
        · rw [ite_eq_left hst]
          have htf : (groupHits hbg1 o_zs).toFinset = {y} := by
            rw [htoFin]
            ext x
            simp only [List.mem_toFinset, List.mem_filterMap, mem_finRange, true_and,
              Finset.mem_singleton, hhit_iff]
            exact ⟨fun ⟨_, _, hxy, _⟩ ↦ hxy, fun hxy ↦ ⟨j₂_star, rfl, hxy, hst⟩⟩
          rw [htf]; dsimp only [R]; rw [Finset.sdiff_self]
        · rw [ite_eq_right hst]
          have htf : (groupHits hbg1 o_zs).toFinset = ∅ := by
            rw [htoFin]
            ext x
            simp only [List.mem_toFinset, List.mem_filterMap, mem_finRange, true_and,
              Finset.notMem_empty, iff_false, not_exists, hhit_iff]
            rintro j₂ ⟨rfl, rfl, h⟩
            exact hst h
          rw [htf, Finset.sdiff_empty]
    simp_rw [hterm_simplify]
    let splitStar := Equiv.piSplitAt j₂_star (fun _ : Fin m ↦ Fin (2 ^ (1 * (n + 1))))
    rw [← splitStar.symm.sum_comp, sum_prod_type]
    have hfactor (z_star : Fin (2 ^ (1 * (n + 1))))
        (rest : ({j₂ : Fin m // j₂ ≠ j₂_star}) → Fin (2 ^ (1 * (n + 1)))) :
        (∏ j₂ : Fin m, (normSq (ξ j₂ (splitStar.symm (z_star, rest) j₂)) : ℂ)) *
            (if hitZ (splitStar.symm (z_star, rest) j₂_star) = some y then G ∅ else G R) =
          ((normSq (ξ j₂_star z_star) : ℂ) *
              (if hitZ z_star = some y then G ∅ else G R)) *
            ∏ j₂ : {j₂ : Fin m // j₂ ≠ j₂_star}, (normSq (ξ j₂.1 (rest j₂)) : ℂ) := by
      have hst_apply : splitStar.symm (z_star, rest) j₂_star = z_star := by simp [splitStar]
      have hprod_split :
          (∏ j₂ : Fin m, (normSq (ξ j₂ (splitStar.symm (z_star, rest) j₂)) : ℂ)) =
            (normSq (ξ j₂_star z_star) : ℂ) *
              ∏ j₂ : {j₂ : Fin m // j₂ ≠ j₂_star}, (normSq (ξ j₂.1 (rest j₂)) : ℂ) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₂_star), hst_apply]
        congr 1
        refine Finset.prod_bij (fun j₂ hj₂ ↦ ⟨j₂, (Finset.mem_erase.mp hj₂).1⟩)
          (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ congrArg Subtype.val h)
          (fun j₂ _ ↦ ⟨j₂.1, Finset.mem_erase.mpr ⟨j₂.2, Finset.mem_univ _⟩, rfl⟩)
          (fun j₂ hj₂ ↦ ?_)
        have hne : j₂ ≠ j₂_star := (Finset.mem_erase.mp hj₂).1
        simp [splitStar, hne]
      rw [hprod_split, hst_apply]
      ring
    simp_rw [hfactor, ← Finset.mul_sum, ← Fintype.prod_sum
        (fun (j₂ : {j₂ : Fin m // j₂ ≠ j₂_star}) z ↦ (normSq (ξ j₂.1 z) : ℂ)),
      htot_one, Finset.prod_const_one, mul_one]
    have hsplit_z :
        (∑ z_star : Fin (2 ^ (1 * (n + 1))),
          (normSq (ξ j₂_star z_star) : ℂ) * (if hitZ z_star = some y then G ∅ else G R)) =
        (∑ z_star : Fin (2 ^ (1 * (n + 1))),
          if hitZ z_star = some y then (normSq (ξ j₂_star z_star) : ℂ) else 0) * G ∅ +
        ((∑ z_star : Fin (2 ^ (1 * (n + 1))), (normSq (ξ j₂_star z_star) : ℂ)) -
          ∑ z_star : Fin (2 ^ (1 * (n + 1))),
            if hitZ z_star = some y then (normSq (ξ j₂_star z_star) : ℂ) else 0) * G R := by
      rw [sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z_star _ ↦ ?_
      by_cases h : hitZ z_star = some y <;> simp [h]
    rw [hsplit_z, sum_normSq_zoomSlotWrap_hit_singleton hp2 hm2_pow perm y kZoom
      (jSub j₂_star) hy_sub, htot_one j₂_star]
    push_cast
    ring
  · rw [ite_eq_right hy_hit]
    have hterm_miss (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) :
        (∏ j₂ : Fin m, (normSq (ξ j₂ (zs j₂)) : ℂ)) *
            G (R \ (groupHits hbg1
              (parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs))).toFinset) =
          (∏ j₂ : Fin m, (normSq (ξ j₂ (zs j₂)) : ℂ)) * G R := by
      by_cases hzero : (∏ j₂ : Fin m, (normSq (ξ j₂ (zs j₂)) : ℂ)) = 0
      · rw [hzero, zero_mul, zero_mul]
      · congr 1
        have hnz (j₂ : Fin m) : ξ j₂ (zs j₂) ≠ 0 := fun hj0 ↦ hzero
          (Finset.prod_eq_zero (Finset.mem_univ j₂)
            (by rw [hj0, Complex.normSq_zero, Complex.ofReal_zero]))
        have hex (j₂ : Fin m) :
            (groupReg hbg1 j₂).extractIndex ((groupSplitEquiv hbg1).symm zs) = zs j₂ := by
          rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
        set o_zs := parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs)
        have hslot_nz (j₂ : Fin m) :
            ξ j₂ ((groupReg hbg1 j₂).extractIndex (parallelMarkPerm n m R o_zs)) ≠ 0 := by
          dsimp only [o_zs]; rw [parallelMarkPerm_involutive, hex]; exact hnz j₂
        rcases groupHits_of_zoomSlotWrap hp2 hm2_pow perm R jSub _ o_zs hslot_nz with
          ⟨hmem_sub, htoFin⟩
        have htf : (groupHits hbg1 o_zs).toFinset = ∅ := by
          rw [htoFin]
          ext x
          simp only [List.mem_toFinset, List.mem_filterMap, mem_finRange, true_and,
            Finset.notMem_empty, iff_false, not_exists]
          intro j₂ hx
          rcases hmem_sub j₂ x hx with ⟨hxR, hx_sub⟩
          have hxy : x = y := Finset.mem_singleton.mp hxR
          subst hxy
          exact hy_hit ((subcubePref2_eq_zoomCombine_iff hm1 hp hm hp2 hm2_pow (perm x)
            j₂ j_hit).mp hx_sub).1
        rw [htf, Finset.sdiff_empty]
    simp_rw [hterm_miss, ← Finset.sum_mul,
      ← Fintype.prod_sum (fun (j₂ : Fin m) z ↦ (normSq (ξ j₂ z) : ℂ)),
      htot_one, Finset.prod_const_one, one_mul]
private lemma card_subcubeLocalSet_image_perm_gh {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (j : Fin m) :
    (subcubeLocalSet hp hm (R.image perm) j).card =
      (R.filter fun x ↦ subcubePref hp hm (perm x) = j).card := by
  rw [card_subcubeLocalSet_eq]
  have himg :
      ((R.image perm).filter fun y ↦ subcubePref hp hm y = j) =
        (R.filter fun x ↦ subcubePref hp hm (perm x) = j).image perm := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    exact ⟨fun ⟨⟨x, hxR, hxp⟩, hj⟩ ↦ ⟨x, ⟨hxR, hxp ▸ hj⟩, hxp⟩,
      fun ⟨x, ⟨hxR, hj⟩, hxp⟩ ↦ ⟨⟨x, hxR, hxp⟩, hxp ▸ hj⟩⟩
  rw [himg, Finset.card_image_of_injective _ perm.injective]
private lemma ghSlotLocalCard_of_injOn {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))}
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (j : Fin m) :
    (subcubeLocalSet hp hm (R.image perm) j).card =
      if j ∈ R.image (fun x ↦ subcubePref hp hm (perm x)) then 1 else 0 := by
  rw [card_subcubeLocalSet_image_perm_gh]
  by_cases hj : j ∈ R.image (fun x ↦ subcubePref hp hm (perm x))
  · rw [ite_eq_left hj]
    rcases Finset.mem_image.mp hj with ⟨x₀, hx₀, rfl⟩
    have hsing :
        (R.filter fun x ↦ subcubePref hp hm (perm x) = subcubePref hp hm (perm x₀)) = {x₀} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun ⟨hxR, heq⟩ ↦ hInj hxR hx₀ heq, fun h ↦ ⟨h ▸ hx₀, by rw [h]⟩⟩
    rw [hsing, Finset.card_singleton]
  · rw [ite_eq_right hj, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hxR heq
    exact hj (heq ▸ Finset.mem_image_of_mem _ hxR)
/-- Disjoint-support product Dicke basis vector for `A ⊆ R.image (subcubePref ∘ perm)`. -/
noncomputable def ghBasisVec {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (A : Finset (Fin m)) :
    Fin (2 ^ (m * (n + 1))) → ℂ :=
  let pref := fun x ↦ subcubePref hp hm (perm x)
  zoomProdState fun j ↦
    zoomSlotWrap hp hm perm j
      (if j ∈ R.image pref then
        if j ∈ A then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1
        else grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0
      else groverMultiState ∅ 0)
/-- Complex-amplitude symmetric Dicke state over `A ∈ (R.image pref).powerset` weighted by
  `u A.card: ℂ` (for arbitrary `R.card`). -/
noncomputable def wdAmpStateC {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (u : ℕ → ℂ) :
    Fin (2 ^ (m * (n + 1))) → ℂ :=
  let pref := fun x ↦ subcubePref hp hm (perm x)
  fun w ↦ ∑ A ∈ (R.image pref).powerset, u A.card * ghBasisVec hp hm perm R A w
private lemma ghPrep_grover_eq_wdAmpStateC {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))}
    {active : ℕ} {μ : Fin (2 ^ (k * n))}
    (hsub : memSeen n k (memPrefix k active) μ ⊆ S)
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x))
      ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))))
    (kInit : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let R := S \ memSeen n k (memPrefix k active) μ
    let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let prepOp := (lowBlock W M).embedMatrix (wdPrepUnitary hp hm perm).1
    let u₀ := dickeStep R.card (Real.cos ((2 * (kInit : ℝ) + 1) * θ₁) : ℂ)
      (Real.sin ((2 * (kInit : ℝ) + 1) * θ₁) : ℂ) (fun b ↦ if b = 0 then 1 else 0)
    ((diffOp * phaseOp) ^ kInit) *ᵥ (prepOp *ᵥ single (workMemIdx n m k 0 μ) 1) =
      workMemState (wdAmpStateC hp hm perm R u₀) (single μ 1) := by
  dsimp only
  rw [wdPrepUnitary_mulVec_workMemIdx_gh hp hm perm μ,
    ghDeflatedGrover_iter_zoomProdState hp hm perm hsub (fun j ↦ j) _ kInit]
  set R := S \ memSeen n k (memPrefix k active) μ
  set θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
  set u₀ := dickeStep R.card (Real.cos ((2 * (kInit : ℝ) + 1) * θ₁) : ℂ)
    (Real.sin ((2 * (kInit : ℝ) + 1) * θ₁) : ℂ) (fun b ↦ if b = 0 then 1 else 0)
  congr 1
  funext w
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj
  set c₀ := Real.cos ((2 * (kInit : ℝ) + 1) * θ₁)
  set s₀ := Real.sin ((2 * (kInit : ℝ) + 1) * θ₁)
  let x₀ (j : Fin m) : ℂ :=
    zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0)
      ((groupReg (Nat.mul_one m) j).extractIndex w)
  let x₁ (j : Fin m) : ℂ :=
    zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1)
      ((groupReg (Nat.mul_one m) j).extractIndex w)
  let z (j : Fin m) : ℂ :=
    zoomSlotWrap hp hm perm j (groverMultiState ∅ 0)
      ((groupReg (Nat.mul_one m) j).extractIndex w)
  have hprod_lhs :
      zoomProdState
          (fun j ↦ zoomSlotWrap hp hm perm j
            ((fun ψ ↦ Grover.diffuserMatrix *ᵥ
              (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ ψ))^[kInit]
                (hadamardMatrix (n - p) *ᵥ single 0 1))) w =
        ∏ j : Fin m, if j ∈ J then (c₀ : ℂ) * x₀ j + (s₀ : ℂ) * x₁ j else z j := by
    unfold zoomProdState
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    dsimp only
    have hcard := ghSlotLocalCard_of_injOn hp hm perm hInj j
    by_cases hj : j ∈ J
    · rw [ite_eq_left hj]
      have hc1 : (subcubeLocalSet hp hm (R.image perm) j).card = 1 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_left hj] at hcard
      have h0 : 0 < (subcubeLocalSet hp hm (R.image perm) j).card := by omega
      have hlt : (subcubeLocalSet hp hm (R.image perm) j).card < 2 ^ (n - p) := by omega
      have hθ : Real.arcsin (√(((subcubeLocalSet hp hm (R.image perm) j).card : ℝ) /
          (2 ^ (n - p) : ℝ))) = θ₁ := by
        rw [hc1, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]
      have hinit := hadamard_zero_eq_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0 hlt
      have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm (R.image perm) j)
        h0 hlt kInit (Real.cos θ₁) (Real.sin θ₁)
      have hc_add :
          Real.cos (2 * (kInit : ℝ) * θ₁) * Real.cos θ₁ -
            Real.sin (2 * (kInit : ℝ) * θ₁) * Real.sin θ₁ = c₀ := by
        rw [← Real.cos_add]; exact congrArg Real.cos (by ring)
      have hs_add :
          Real.sin (2 * (kInit : ℝ) * θ₁) * Real.cos θ₁ +
            Real.cos (2 * (kInit : ℝ) * θ₁) * Real.sin θ₁ = s₀ := by
        rw [← Real.sin_add]; exact congrArg Real.sin (by ring)
      rw [hθ] at hinit hiter
      dsimp only at hinit hiter
      rw [hc_add, hs_add] at hiter
      rw [hinit, hiter, grover2DVec_linear, zoomSlotWrap_eq_linear]
    · rw [ite_eq_right hj]
      have hc0_card : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_right hj] at hcard
      have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0_card
      rw [hemp, ← groverMultiState_zero_eq_hadamard_mulVec ∅,
        Function.iterate_fixed diffuser_oracle_empty_groverMultiState_zero]
  let uInit : ℕ → ℂ := fun b ↦ if b = 0 then 1 else 0
  have hlhs_pow :
      (∏ j : Fin m, if j ∈ J then (c₀ : ℂ) * x₀ j + (s₀ : ℂ) * x₁ j else z j) =
        ∑ A ∈ J.powerset,
          uInit A.card *
            ∏ j : Fin m,
              if j ∈ J then
                if j ∈ A then -(s₀ : ℂ) * x₀ j + (c₀ : ℂ) * x₁ j
                else (c₀ : ℂ) * x₀ j + (s₀ : ℂ) * x₁ j
              else z j := by
    rw [Finset.sum_eq_single ∅ (fun A _ hne ↦ by
      have hc_ne : A.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      simp [uInit, hc_ne]) (fun hnot ↦ absurd (Finset.empty_mem_powerset J) hnot)]
    simp only [Finset.card_empty, uInit, ↓reduceIte, one_mul, Finset.notMem_empty]
  rw [hprod_lhs, hlhs_pow, prod_dickeStep_powerset J (c₀ : ℂ) (s₀ : ℂ) x₀ x₁ z uInit]
  unfold wdAmpStateC ghBasisVec zoomProdState
  dsimp only [u₀]
  refine Finset.sum_congr rfl fun B _ ↦ ?_
  rw [hJ_card]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ J
  · rw [ite_eq_left hj]
    by_cases hjB : j ∈ B
    · simp [J, hj, hjB, x₁]
    · simp [J, hj, hjB, x₀]
  · simp [J, hj, z]
private lemma ghGrover_iter_wdAmpStateC {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))}
    {active : ℕ} {μ : Fin (2 ^ (k * n))}
    (hsub : memSeen n k (memPrefix k active) μ ⊆ S)
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x))
      ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))))
    (u : ℕ → ℂ) (kNext : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let R := S \ memSeen n k (memPrefix k active) μ
    let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let uNext := dickeStep R.card (Real.cos (2 * (kNext : ℝ) * θ₁) : ℂ)
      (Real.sin (2 * (kNext : ℝ) * θ₁) : ℂ) u
    ((diffOp * phaseOp) ^ kNext) *ᵥ workMemState (wdAmpStateC hp hm perm R u) (single μ 1) =
      workMemState (wdAmpStateC hp hm perm R uNext) (single μ 1) := by
  dsimp only
  let W := m * (n + 1)
  let M := k * n
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1
  let orac := (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
  let R := S \ memSeen n k (memPrefix k active) μ
  let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj
  have hlin_ws (F : Finset (Fin m) → Fin (2 ^ W) → ℂ) :
      workMemState (W := W) (M := M) (fun w ↦ ∑ A ∈ J.powerset, F A w) (single μ 1) =
        ∑ A ∈ J.powerset, workMemState (W := W) (M := M) (F A) (single μ 1) := by
    funext z; rw [Finset.sum_apply]; dsimp only [workMemState]; rw [Finset.sum_mul]
  have hlin_smul (c : ℂ) (v : Fin (2 ^ (m * (n + 1))) → ℂ) :
      workMemState (fun w ↦ c * v w) (single μ 1) = c • workMemState v (single μ 1) := by
    funext z; dsimp only [workMemState, Pi.smul_apply, smul_eq_mul]; ring
  change ((diffOp * phaseOp) ^ kNext) *ᵥ
      workMemState (W := W) (M := M)
        (fun w ↦ ∑ A ∈ J.powerset, u A.card * ghBasisVec hp hm perm R A w)
        (single μ 1) = _
  rw [hlin_ws (fun A w ↦ u A.card * ghBasisVec hp hm perm R A w), Matrix.mulVec_sum]
  set ck := Real.cos (2 * (kNext : ℝ) * θ₁)
  set sk := Real.sin (2 * (kNext : ℝ) * θ₁)
  let slotAfter (A : Finset (Fin m)) (w : Fin (2 ^ W)) (j : Fin m) : ℂ :=
    if j ∈ J then
      if j ∈ A then
        -(sk : ℂ) * zoomSlotWrap hp hm perm j
            (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0)
            ((groupReg (Nat.mul_one m) j).extractIndex w) +
          (ck : ℂ) * zoomSlotWrap hp hm perm j
            (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1)
            ((groupReg (Nat.mul_one m) j).extractIndex w)
      else
        (ck : ℂ) * zoomSlotWrap hp hm perm j
            (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0)
            ((groupReg (Nat.mul_one m) j).extractIndex w) +
          (sk : ℂ) * zoomSlotWrap hp hm perm j
            (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1)
            ((groupReg (Nat.mul_one m) j).extractIndex w)
    else
      zoomSlotWrap hp hm perm j (groverMultiState ∅ 0)
        ((groupReg (Nat.mul_one m) j).extractIndex w)
  have h_sub_sum (A : Finset (Fin m)) :
      ((diffOp * phaseOp) ^ kNext) *ᵥ
          workMemState (W := W) (M := M)
            (fun w ↦ u A.card * ghBasisVec hp hm perm R A w) (single μ 1) =
        workMemState (W := W) (M := M)
          (fun w ↦ u A.card * ∏ j : Fin m, slotAfter A w j) (single μ 1) := by
    dsimp only [slotAfter, W, M, R, fc, orac, unm, phaseOp, diffOp]
    rw [hlin_smul (u A.card) _, Matrix.mulVec_smul]
    unfold ghBasisVec
    rw [ghDeflatedGrover_iter_zoomProdState hp hm perm hsub (fun j ↦ j) _ kNext,
      ← hlin_smul (u A.card) _]
    congr 1; funext w; congr 1
    unfold zoomProdState
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    dsimp only
    have hcard := ghSlotLocalCard_of_injOn hp hm perm hInj j
    by_cases hj : j ∈ J
    · have hc1 : (subcubeLocalSet hp hm (R.image perm) j).card = 1 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_left hj] at hcard
      dsimp only [J, R] at hj ⊢
      rw [ite_eq_left hj, ite_eq_left hj]
      have h0 : 0 < (subcubeLocalSet hp hm
          ((S \ memSeen n k (memPrefix k active) μ).image perm) j).card := by
        dsimp only [R] at hc1; omega
      have hlt : (subcubeLocalSet hp hm
          ((S \ memSeen n k (memPrefix k active) μ).image perm) j).card < 2 ^ (n - p) := by
        dsimp only [R] at hc1; omega
      have hθ : Real.arcsin (√(((subcubeLocalSet hp hm
          ((S \ memSeen n k (memPrefix k active) μ).image perm) j).card : ℝ) /
          (2 ^ (n - p) : ℝ))) = θ₁ := by
        dsimp only [R] at hc1
        rw [hc1, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]
      by_cases hjA : j ∈ A
      · rw [ite_eq_left hjA, ite_eq_left hjA]
        have hiter := diffuser_oracle_iter_grover2DVec
          (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm) j)
          h0 hlt kNext 0 1
        rw [hθ] at hiter; dsimp only at hiter
        have hc_tr : Real.cos (2 * (kNext : ℝ) * θ₁) * 0 -
            Real.sin (2 * (kNext : ℝ) * θ₁) * 1 = -sk := by dsimp only [sk]; ring
        have hs_tr : Real.sin (2 * (kNext : ℝ) * θ₁) * 0 +
            Real.cos (2 * (kNext : ℝ) * θ₁) * 1 = ck := by dsimp only [ck]; ring
        rw [hc_tr, hs_tr] at hiter
        rw [hiter, grover2DVec_linear, zoomSlotWrap_eq_linear, Complex.ofReal_neg]
      · rw [ite_eq_right hjA, ite_eq_right hjA]
        have hiter := diffuser_oracle_iter_grover2DVec
          (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm) j)
          h0 hlt kNext 1 0
        rw [hθ] at hiter; dsimp only at hiter
        have hc_tr : Real.cos (2 * (kNext : ℝ) * θ₁) * 1 -
            Real.sin (2 * (kNext : ℝ) * θ₁) * 0 = ck := by dsimp only [ck]; ring
        have hs_tr : Real.sin (2 * (kNext : ℝ) * θ₁) * 1 +
            Real.cos (2 * (kNext : ℝ) * θ₁) * 0 = sk := by dsimp only [sk]; ring
        rw [hc_tr, hs_tr] at hiter
        rw [hiter, grover2DVec_linear, zoomSlotWrap_eq_linear]
    · have hc0_card : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_right hj] at hcard
      dsimp only [J, R] at hj hc0_card ⊢
      rw [ite_eq_right hj, ite_eq_right hj]
      have hemp : subcubeLocalSet hp hm
          ((S \ memSeen n k (memPrefix k active) μ).image perm) j = ∅ :=
        Finset.card_eq_zero.mp hc0_card
      rw [hemp, Function.iterate_fixed diffuser_oracle_empty_groverMultiState_zero]
  simp_rw [h_sub_sum]
  rw [← hlin_ws (fun A w ↦ u A.card * ∏ j : Fin m, slotAfter A w j)]
  congr 1; funext w
  dsimp only [slotAfter]
  rw [prod_dickeStep_powerset J (ck : ℂ) (sk : ℂ)
    (fun j ↦ zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0)
      ((groupReg (Nat.mul_one m) j).extractIndex w))
    (fun j ↦ zoomSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1)
      ((groupReg (Nat.mul_one m) j).extractIndex w))
    (fun j ↦ zoomSlotWrap hp hm perm j (groverMultiState ∅ 0)
      ((groupReg (Nat.mul_one m) j).extractIndex w))
    u]
  unfold wdAmpStateC
  dsimp only [J, R, ck, sk, θ₁] at hJ_card ⊢
  refine Finset.sum_congr rfl fun B _ ↦ ?_
  rw [hJ_card]
  congr 1
  unfold ghBasisVec zoomProdState
  dsimp only
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  split_ifs <;> rfl
private lemma gh_length_filterMap_fin_eq_length_filter {m d : ℕ}
    (p : Fin m → Option (Fin d)) (l : List (Fin m)) :
    (l.filterMap p).length = (l.filter fun a ↦ (p a).isSome).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hpa : p a <;> simp [List.filterMap_cons_none, List.filterMap_cons_some, hpa, ih]
private lemma ghBasisVec_support_props {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n)))
    {A : Finset (Fin m)} (hA : A ⊆ R.image fun x ↦ subcubePref hp hm (perm x))
    (o : Fin (2 ^ (m * (n + 1))))
    (hamp : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∀ j : Fin m,
      ((addrReg n 1).basisSplitEquiv
        ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o))).2 = 0) ∧
    (∀ j : Fin m,
      (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome =
        (if j ∈ A then true else false)) ∧
    (∀ x ∈ groupHits hbg1 o, x ∈ R) ∧
    wdHitCount n m o = A.card := by
  intro hbg1
  set w := parallelMarkPerm n m R o
  have ho_eq : o = parallelMarkPerm n m R w := (parallelMarkPerm_involutive R o).symm
  have hslot_nz (j : Fin m) :
      zoomSlotWrap hp hm perm j
        (if j ∈ R.image (fun x ↦ subcubePref hp hm (perm x)) then
          if j ∈ A then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1
          else grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0
        else groverMultiState ∅ 0)
        ((groupReg hbg1 j).extractIndex w) ≠ 0 :=
    fun h0 ↦ hamp (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  have hflags (j : Fin m) :
      ((addrReg n 1).basisSplitEquiv ((groupReg hbg1 j).extractIndex w)).2 = 0 :=
    (zoomSlotWrap_support_firstMarkedAddr hp hm perm R j _ _ (hslot_nz j)).1
  have hisSome (j : Fin m) :
      (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome =
        (if j ∈ A then true else false) := by
    have hsp := zoomSlotWrap_support_firstMarkedAddr hp hm perm R j _ _ (hslot_nz j)
    have hex_o : (groupReg hbg1 j).extractIndex o =
        parallelMarkPerm n 1 R ((groupReg hbg1 j).extractIndex w) := by
      rw [ho_eq, extractIndex_groupReg_parallelMarkPerm]
    rw [hex_o, hsp.2.2.2]
    have hφ := hsp.2.1
    set w_loc := (lowHighEquiv (n - p) p
      (zoomCast1nEquiv hp (wdPerm1n perm
        ((addrReg n 1).extractIndex ((groupReg hbg1 j).extractIndex w))))).1
    change _ ≠ 0 at hφ
    by_cases hjA : j ∈ A
    · have hjR : j ∈ R.image (fun x ↦ subcubePref hp hm (perm x)) := hA hjA
      rw [ite_eq_left hjR, ite_eq_left hjA] at hφ
      have hw_mem : w_loc ∈ subcubeLocalSet hp hm (R.image perm) j := by
        by_contra hnot; apply hφ
        unfold grover2DVec; rw [ite_eq_right hnot, zero_div, Complex.ofReal_zero]
      rw [ite_eq_left hw_mem, ite_eq_left hjA]; rfl
    · by_cases hjR : j ∈ R.image (fun x ↦ subcubePref hp hm (perm x))
      · rw [ite_eq_left hjR, ite_eq_right hjA] at hφ
        have hw_not : w_loc ∉ subcubeLocalSet hp hm (R.image perm) j := by
          intro hmem; apply hφ
          unfold grover2DVec; rw [ite_eq_left hmem, zero_div, Complex.ofReal_zero]
        rw [ite_eq_right hw_not, ite_eq_right hjA]; rfl
      · have hc0 : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
          rw [card_subcubeLocalSet_image_perm_gh, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x hxR heq; exact hjR (heq ▸ Finset.mem_image_of_mem _ hxR)
        have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0
        rw [hemp, ite_eq_right (Finset.notMem_empty w_loc), ite_eq_right hjA]; rfl
  have hnew : ∀ x ∈ groupHits hbg1 o, x ∈ R := by
    intro x hx; rw [ho_eq] at hx
    exact mem_of_mem_groupHits_parallelMarkPerm hbg1 hflags hx
  have hgh_eq := (groupHits_eq_filterMap_of_zoomSlotWrap hp hm perm R _ o hslot_nz).2
  have hhit_card : wdHitCount n m o = A.card := by
    unfold wdHitCount
    change (groupHits hbg1 o).length = A.card
    rw [hgh_eq, gh_length_filterMap_fin_eq_length_filter]
    have hfilt_eq :
        ((finRange m).filter fun j ↦
          (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome) =
        (finRange m).filter (fun j ↦ if j ∈ A then true else false) :=
      List.filter_congr fun j _ ↦ hisSome j
    rw [hfilt_eq, ← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
    congr 1; ext j; by_cases h : j ∈ A <;> simp [h]
  exact ⟨hflags, hisSome, hnew, hhit_card⟩
private lemma ghBasisVec_mul_eq_zero_of_ne {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n)))
    {A₁ A₂ : Finset (Fin m)}
    (hA₁ : A₁ ⊆ R.image fun x ↦ subcubePref hp hm (perm x))
    (hA₂ : A₂ ⊆ R.image fun x ↦ subcubePref hp hm (perm x))
    (hne : A₁ ≠ A₂) (w : Fin (2 ^ (m * (n + 1)))) :
    ghBasisVec hp hm perm R A₁ w = 0 ∨ ghBasisVec hp hm perm R A₂ w = 0 := by
  by_contra hboth; push Not at hboth
  set o := parallelMarkPerm n m R w
  have hw : w = parallelMarkPerm n m R o := (parallelMarkPerm_involutive R w).symm
  rw [hw] at hboth
  have h1 := (ghBasisVec_support_props hp hm perm R hA₁ o hboth.1).2.1
  have h2 := (ghBasisVec_support_props hp hm perm R hA₂ o hboth.2).2.1
  apply hne; ext j
  have hj := (h1 j).symm.trans (h2 j)
  by_cases hA1 : j ∈ A₁ <;> by_cases hA2 : j ∈ A₂ <;> simp [hA1, hA2] at hj ⊢
private lemma sum_normSq_ghBasisVec {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (hsub2 : 2 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n)))
    {R : Finset (Fin (2 ^ n))}
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (A : Finset (Fin m)) :
    (∑ w : Fin (2 ^ (m * (n + 1))), normSq (ghBasisVec hp hm perm R A w)) = 1 := by
  unfold ghBasisVec
  rw [sum_normSq_zoomProdState]
  refine Finset.prod_eq_one fun j _ ↦ sum_normSq_zoomSlotWrap_of_norm hp hm perm j _ 1 ?_
  have hcard := ghSlotLocalCard_of_injOn hp hm perm hInj j
  by_cases hj : j ∈ R.image (fun x ↦ subcubePref hp hm (perm x))
  · rw [ite_eq_left hj]
    have hc1 : (subcubeLocalSet hp hm (R.image perm) j).card = 1 := by simpa [hj] using hcard
    have h0 : 0 < (subcubeLocalSet hp hm (R.image perm) j).card := by omega
    have hlt : (subcubeLocalSet hp hm (R.image perm) j).card < 2 ^ (n - p) := by omega
    by_cases hjA : j ∈ A
    · rw [ite_eq_left hjA]; exact sum_normSq_grover2DVec_zero_one _ h0
    · rw [ite_eq_right hjA]; exact sum_normSq_grover2DVec_one_zero _ hlt
  · rw [ite_eq_right hj]; exact sum_normSq_groverMultiState_eq_one ∅ 0
private lemma sum_normSq_wdAmpStateC_mul_card {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (hsub2 : 2 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n)))
    {R : Finset (Fin (2 ^ n))}
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (u : ℕ → ℂ) (g : ℕ → ℂ) :
    (∑ o : Fin (2 ^ (m * (n + 1))),
      (normSq (wdAmpStateC hp hm perm R u (parallelMarkPerm n m R o)) : ℂ) *
        g (wdHitCount n m o)) =
      ∑ w ∈ Finset.range (R.card + 1),
        (((R.card.choose w : ℝ) * normSq (u w) : ℝ) : ℂ) * g w := by
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj
  have hpt (o : Fin (2 ^ (m * (n + 1)))) :
      (normSq (wdAmpStateC hp hm perm R u (parallelMarkPerm n m R o)) : ℂ) * g (wdHitCount n m o) =
        ∑ A ∈ J.powerset,
          ((normSq (u A.card) *
            normSq (ghBasisVec hp hm perm R A (parallelMarkPerm n m R o)) : ℝ) : ℂ) *
            g A.card := by
    unfold wdAmpStateC
    set w := parallelMarkPerm n m R o
    by_cases hex : ∃ A₀ ∈ J.powerset, ghBasisVec hp hm perm R A₀ w ≠ 0
    · rcases hex with ⟨A₀, hA₀, hnz⟩
      have hzero (A : Finset (Fin m)) (hA : A ∈ J.powerset) (hne : A ≠ A₀) :
          ghBasisVec hp hm perm R A w = 0 := by
        rcases ghBasisVec_mul_eq_zero_of_ne hp hm perm R
          (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hA₀) hne w with h1 | h2
        · exact h1
        · exact absurd h2 hnz
      rw [Finset.sum_eq_single A₀ (fun A hA hne ↦ by rw [hzero A hA hne, mul_zero])
          (fun hnot ↦ absurd hA₀ hnot), Finset.sum_eq_single A₀ (fun A hA hne ↦ by
          rw [hzero A hA hne, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])
          (fun hnot ↦ absurd hA₀ hnot)]
      have hhit := (ghBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA₀) o hnz).2.2.2
      rw [hhit, map_mul]
    · simp only [not_exists, not_and, not_not] at hex
      rw [Finset.sum_eq_zero (fun A hA ↦ by rw [hex A hA, mul_zero]),
        Complex.normSq_zero, Complex.ofReal_zero, zero_mul, Finset.sum_eq_zero (fun A hA ↦ by
          rw [hex A hA, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  have hsum_A (A : Finset (Fin m)) (_hA : A ∈ J.powerset) :
      (∑ o : Fin (2 ^ (m * (n + 1))),
        ((normSq (u A.card) * normSq (ghBasisVec hp hm perm R A (parallelMarkPerm n m R o)) : ℝ) :
          ℂ) * g A.card) =
        (normSq (u A.card) : ℂ) * g A.card := by
    simp_rw [Complex.ofReal_mul, mul_assoc]
    rw [← Finset.mul_sum]
    have hnorm1 :
        (∑ o : Fin (2 ^ (m * (n + 1))),
          (normSq (ghBasisVec hp hm perm R A (parallelMarkPerm n m R o)) : ℂ)) = 1 := by
      rw [← Complex.ofReal_sum,
        Equiv.sum_comp (parallelMarkPerm n m R) (fun w ↦ normSq (ghBasisVec hp hm perm R A w)),
        sum_normSq_ghBasisVec hp hm hsub2 perm hInj A, Complex.ofReal_one]
    rw [← Finset.sum_mul, hnorm1, one_mul]
  rw [Finset.sum_congr rfl hsum_A]
  have hpow_union :
      J.powerset = (Finset.range (J.card + 1)).biUnion fun w ↦ J.powersetCard w := by
    ext A
    simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨fun h ↦ ⟨A.card, Nat.lt_succ_of_le (Finset.card_le_card h), h, rfl⟩,
      fun ⟨_, _, h, _⟩ ↦ h⟩
  have hdisj :
      Set.PairwiseDisjoint (Finset.range (J.card + 1) : Set ℕ) (fun w ↦ J.powersetCard w) :=
    fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun A h1 h2 ↦
      hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
  rw [hpow_union, Finset.sum_biUnion hdisj, hJ_card]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hcongr :
      ∀ A ∈ J.powersetCard w,
        (normSq (u A.card) : ℂ) * g A.card = (normSq (u w) : ℂ) * g w :=
    fun A hA ↦ by rw [(Finset.mem_powersetCard.mp hA).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard, hJ_card,
    nsmul_eq_mul, ← mul_assoc]
  push_cast; rfl
/-- Action of `ghDampVec` and `ghClickVec` on `P_R *ᵥ wdAmpStateC hp hm perm R u` whenever
  `wSpec b` has `sVal = 0` for all `b < R.card` (zero sub-maximal clicks, arbitrary
  `R.card`). -/
private lemma ghDamp_and_click_marked_wdAmpStateC {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))}
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (wSpec : ℕ → GaussPyth × PythPair)
    (hZeroClick : ∀ b < R.card, (wSpec b).2.sVal = 0)
    (u : ℕ → ℂ) :
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    ghDampVec n m wSpec (P_R *ᵥ wdAmpStateC hp hm perm R u) =
        P_R *ᵥ wdAmpStateC hp hm perm R
          (fun b ↦ ((wSpec b).2.cVal : ℂ) * (wSpec b).1.val * u b) ∧
      ghClickVec n m wSpec (P_R *ᵥ wdAmpStateC hp hm perm R u) =
        (((wSpec R.card).2.sVal : ℂ) * (wSpec R.card).1.val * u R.card) •
          (P_R *ᵥ ghBasisVec hp hm perm R (R.image fun x ↦ subcubePref hp hm (perm x))) := by
  intro P_R
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj
  constructor
  · funext o
    dsimp only [ghDampVec, P_R]
    rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom,
      permUnitary_parallelMarkPerm_mulVec_apply_zoom]
    unfold wdAmpStateC
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    by_cases hnz : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
    · simp [hnz]
    · have hcardA :=
        (ghBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA) o hnz).2.2.2
      rw [hcardA]; ring
  · funext o
    dsimp only [ghClickVec, P_R, Pi.smul_apply, smul_eq_mul]
    rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom,
      permUnitary_parallelMarkPerm_mulVec_apply_zoom]
    unfold wdAmpStateC
    by_cases hhit : wdHitCount n m o = R.card
    · rw [hhit, Finset.mul_sum, Finset.sum_eq_single J (fun A hA hne ↦ ?_)
          (fun hnot ↦ absurd (Finset.mem_powerset_self J) hnot)]
      · rw [hJ_card]; ring
      · by_cases hnz : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
        · simp [hnz]
        · have hcardA :=
            (ghBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA) o hnz).2.2.2
          have hAJ : A = J := Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hA)
            (by rw [hJ_card, ← hhit, hcardA])
          exact absurd hAJ hne
    · symm
      have hrhs0 :
          (((wSpec R.card).2.sVal : ℂ) * (wSpec R.card).1.val * u R.card) *
            ghBasisVec hp hm perm R J (parallelMarkPerm n m R o) = 0 := by
        by_cases hnz : ghBasisVec hp hm perm R J (parallelMarkPerm n m R o) = 0
        · dsimp only [J] at hnz; rw [hnz, mul_zero]
        · have hcardJ :=
            (ghBasisVec_support_props hp hm perm R Finset.Subset.rfl o hnz).2.2.2
          exact absurd (hcardJ.trans hJ_card) hhit
      rw [hrhs0]
      symm
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun A hA ↦ ?_
      by_cases hnz : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
      · simp [hnz]
      · have hcardA :=
          (ghBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA) o hnz).2.2.2
        have hle : A.card ≤ R.card :=
          hJ_card ▸ Finset.card_le_card (Finset.mem_powerset.mp hA)
        have hlt : wdHitCount n m o < R.card := by omega
        rw [hZeroClick _ hlt]; simp
private lemma ghBasisVec_groupHits_toFinset_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) {R B : Finset (Fin (2 ^ n))}
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (hB : B ⊆ R) (o : Fin (2 ^ (m * (n + 1))))
    (hamp : ghBasisVec hp hm perm R
      (B.image fun x ↦ subcubePref hp hm (perm x)) (parallelMarkPerm n m R o) ≠ 0) :
    (groupHits (Nat.mul_one m) o).toFinset = B := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hA : B.image pref ⊆ R.image pref := Finset.image_subset_image hB
  have hprops := ghBasisVec_support_props hp hm perm R hA o hamp
  have hslot_nz (j : Fin m) :
      zoomSlotWrap hp hm perm j
        (if j ∈ R.image pref then
          if j ∈ B.image pref then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1
          else grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0
        else groverMultiState ∅ 0)
        ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o)) ≠ 0 :=
    fun h0 ↦ hamp (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  rcases groupHits_eq_filterMap_of_zoomSlotWrap hp hm perm R _ o hslot_nz with ⟨hhit_sub, hgh_eq⟩
  have hsub_B : (groupHits hbg1 o).toFinset ⊆ B := by
    intro x hx
    have hx_l : x ∈ groupHits hbg1 o := List.mem_toFinset.mp hx
    rw [hgh_eq] at hx_l
    rcases List.mem_filterMap.mp hx_l with ⟨j, _, hj⟩
    rcases hhit_sub j x hj with ⟨hxR, hpref_x⟩
    have his : (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome = true := by
      simp [hj]
    rw [hprops.2.1 j] at his
    have hjB : j ∈ B.image pref := by
      by_contra hnb; rw [ite_eq_right hnb] at his; cases his
    rcases Finset.mem_image.mp hjB with ⟨y, hyB, hpref_y⟩
    have hxy : x = y := hInj hxR (hB hyB) (hpref_x.trans hpref_y.symm)
    exact hxy ▸ hyB
  have hcard_eq : (groupHits hbg1 o).toFinset.card = B.card := by
    rw [List.toFinset_card_of_nodup (nodup_groupHits hbg1 o)]
    exact hprops.2.2.2.trans (Finset.card_image_of_injOn (hInj.mono hB))
  exact Finset.eq_of_subset_of_card_le hsub_B hcard_eq.ge
private lemma sum_normSq_wdAmpStateC_readout {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (hsub2 : 2 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n)))
    {R : Finset (Fin (2 ^ n))}
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (u : ℕ → ℂ) (G : Finset (Fin (2 ^ n)) → ℂ) :
    (∑ o : Fin (2 ^ (m * (n + 1))),
      (normSq (wdAmpStateC hp hm perm R u (parallelMarkPerm n m R o)) : ℂ) *
        G (R \ (groupHits (Nat.mul_one m) o).toFinset)) =
      ∑ B ∈ R.powerset, (normSq (u B.card) : ℂ) * G (R \ B) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hpow_img :
      (R.image pref).powerset = R.powerset.image (fun B ↦ B.image pref) :=
    Finset.powerset_image
  have hinj_pow :
      Set.InjOn (fun B : Finset (Fin (2 ^ n)) ↦ B.image pref)
        (R.powerset : Set (Finset (Fin (2 ^ n)))) := by
    intro B₁ hB₁ B₂ hB₂ heq
    have heq' : B₁.image pref = B₂.image pref := heq
    have hB₁R := Finset.mem_powerset.mp hB₁
    have hB₂R := Finset.mem_powerset.mp hB₂
    ext x
    constructor
    · intro hx1
      have himg : pref x ∈ B₂.image pref := by
        rw [← heq']; exact Finset.mem_image_of_mem pref hx1
      rcases Finset.mem_image.mp himg with ⟨y, hy2, hyx⟩
      exact hInj (hB₁R hx1) (hB₂R hy2) hyx.symm ▸ hy2
    · intro hx2
      have himg : pref x ∈ B₁.image pref := by
        rw [heq']; exact Finset.mem_image_of_mem pref hx2
      rcases Finset.mem_image.mp himg with ⟨y, hy1, hyx⟩
      exact hInj (hB₂R hx2) (hB₁R hy1) hyx.symm ▸ hy1
  have hamp_rew (w : Fin (2 ^ (m * (n + 1)))) :
      wdAmpStateC hp hm perm R u w =
        ∑ B ∈ R.powerset, u B.card * ghBasisVec hp hm perm R (B.image pref) w := by
    unfold wdAmpStateC
    rw [hpow_img, Finset.sum_image hinj_pow]
    refine Finset.sum_congr rfl fun B hB ↦ ?_
    rw [Finset.card_image_of_injOn (hInj.mono (Finset.mem_powerset.mp hB))]
  have hpt (o : Fin (2 ^ (m * (n + 1)))) :
      (normSq (wdAmpStateC hp hm perm R u (parallelMarkPerm n m R o)) : ℂ) *
          G (R \ (groupHits hbg1 o).toFinset) =
        ∑ B ∈ R.powerset,
          ((normSq (u B.card) *
            normSq (ghBasisVec hp hm perm R (B.image pref)
              (parallelMarkPerm n m R o)) : ℝ) : ℂ) * G (R \ B) := by
    rw [hamp_rew]
    set w := parallelMarkPerm n m R o
    by_cases hex : ∃ B₀ ∈ R.powerset, ghBasisVec hp hm perm R (B₀.image pref) w ≠ 0
    · rcases hex with ⟨B₀, hB₀, hnz⟩
      have hzero (B : Finset (Fin (2 ^ n))) (hB : B ∈ R.powerset) (hne : B ≠ B₀) :
          ghBasisVec hp hm perm R (B.image pref) w = 0 := by
        have hne_img : B.image pref ≠ B₀.image pref := fun heq ↦ hne (hinj_pow hB hB₀ heq)
        rcases ghBasisVec_mul_eq_zero_of_ne hp hm perm R
          (Finset.image_subset_image (Finset.mem_powerset.mp hB))
          (Finset.image_subset_image (Finset.mem_powerset.mp hB₀)) hne_img w with h1 | h2
        · exact h1
        · exact absurd h2 hnz
      rw [Finset.sum_eq_single B₀ (fun B hB hne ↦ by rw [hzero B hB hne, mul_zero])
          (fun hnot ↦ absurd hB₀ hnot), Finset.sum_eq_single B₀ (fun B hB hne ↦ by
          rw [hzero B hB hne, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])
          (fun hnot ↦ absurd hB₀ hnot),
        ghBasisVec_groupHits_toFinset_eq hp hm perm hInj (Finset.mem_powerset.mp hB₀) o hnz,
        map_mul]
    · simp only [not_exists, not_and, not_not] at hex
      rw [Finset.sum_eq_zero (fun B hB ↦ by rw [hex B hB, mul_zero]),
        Complex.normSq_zero, Complex.ofReal_zero, zero_mul, Finset.sum_eq_zero (fun B hB ↦ by
          rw [hex B hB, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ ↦ ?_
  simp_rw [Complex.ofReal_mul, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.sum_mul, ← Complex.ofReal_sum,
    Equiv.sum_comp (parallelMarkPerm n m R)
      (fun w ↦ normSq (ghBasisVec hp hm perm R (B.image pref) w)),
    sum_normSq_ghBasisVec hp hm hsub2 perm hInj (B.image pref), Complex.ofReal_one, one_mul]
/-! ### Section 2b: Pair-Collision `ghCollState` Algebra (`R.card = 2`, `¬ InjOn`) -/
private noncomputable def grover2DVecC {q : ℕ} (M : Finset (Fin (2 ^ q))) (z₀ z₁ : ℂ) :
    Fin (2 ^ q) → ℂ :=
  z₀ • grover2DVec M 1 0 + z₁ • grover2DVec M 0 1
private lemma diffuser_oracle_iter_grover2DVecC {q : ℕ} (M : Finset (Fin (2 ^ q)))
    (h0 : 0 < M.card) (hlt : M.card < 2 ^ q) (t : ℕ) (z₀ z₁ : ℂ) :
    let θ := Real.arcsin √((M.card : ℝ) / (2 ^ q : ℝ))
    let ck := (Real.cos (2 * (t : ℝ) * θ) : ℂ)
    let sk := (Real.sin (2 * (t : ℝ) * θ) : ℂ)
    (fun v ↦ Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ v))^[t] (grover2DVecC M z₀ z₁) =
      grover2DVecC M (ck * z₀ - sk * z₁) (sk * z₀ + ck * z₁) := by
  intro θ ck sk
  let gStep : (Fin (2 ^ q) → ℂ) → (Fin (2 ^ q) → ℂ) :=
    fun v ↦ Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ v)
  have hlin : ∀ (s : ℕ) (a b : ℂ) (u v : Fin (2 ^ q) → ℂ),
      gStep^[s] (a • u + b • v) = a • gStep^[s] u + b • gStep^[s] v := by
    intro s a b u v
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      dsimp only [gStep]
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_smul, Matrix.mulVec_smul]
  change gStep^[t] (z₀ • grover2DVec M 1 0 + z₁ • grover2DVec M 0 1) = _
  rw [hlin]
  have h10 := diffuser_oracle_iter_grover2DVec M h0 hlt t 1 0
  have h01 := diffuser_oracle_iter_grover2DVec M h0 hlt t 0 1
  dsimp only at h10 h01
  change gStep^[t] (grover2DVec M 1 0) = _ at h10
  change gStep^[t] (grover2DVec M 0 1) = _ at h01
  have h10' := h10.trans (grover2DVec_linear M _ _)
  have h01' := h01.trans (grover2DVec_linear M _ _)
  rw [h10', h01']
  funext w
  dsimp only [grover2DVecC, ck, sk, θ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
private lemma ghCollSlot_exists {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hR2 : R.card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n)))) :
    let pref := fun x ↦ subcubePref hp hm (perm x)
    ∃ j₀ : Fin m,
      R.image pref = {j₀} ∧
      (subcubeLocalSet hp hm (R.image perm) j₀).card = 2 ∧
      (∀ j : Fin m, j ≠ j₀ → subcubeLocalSet hp hm (R.image perm) j = ∅) := by
  intro pref
  obtain ⟨x₁, x₂, hne, hR_eq⟩ := Finset.card_eq_two.mp hR2
  have hpref_eq : pref x₁ = pref x₂ := by
    by_contra hne_p
    apply hNotInj
    intro a ha b hb hab
    rw [hR_eq] at ha hb
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha) with rfl | ha' <;>
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hb) with rfl | hb'
    · rfl
    · rw [Finset.mem_singleton.mp hb'] at hab
      exact absurd hab hne_p
    · rw [Finset.mem_singleton.mp ha'] at hab
      exact absurd hab.symm hne_p
    · rw [Finset.mem_singleton.mp ha', Finset.mem_singleton.mp hb']
  refine ⟨pref x₁, ?_, ?_, ?_⟩
  · rw [hR_eq, Finset.image_insert, Finset.image_singleton, hpref_eq,
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
  · rw [card_subcubeLocalSet_image_perm_gh]
    have hfilt : (R.filter fun x ↦ pref x = pref x₁) = R := by
      refine Finset.filter_eq_self.mpr fun x hx ↦ ?_
      rw [hR_eq] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rfl
      · rw [Finset.mem_singleton.mp hx', hpref_eq]
    rw [hfilt, hR2]
  · intro j hj
    rw [← Finset.card_eq_zero, card_subcubeLocalSet_image_perm_gh,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx heq
    rw [hR_eq] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hj heq.symm
    · dsimp only [pref] at hpref_eq hj
      rw [Finset.mem_singleton.mp hx', ← hpref_eq] at heq
      exact hj heq.symm
/-- Pair-collision `r = 2` state `z.1 |0⟩_G + z.2 |1⟩_G` supported on the unique collision
  slot
  `R.image (subcubePref hp hm ∘ perm) = {j₀}`. -/
private noncomputable def ghCollState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (z : ℂ × ℂ)
    (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  z.1 * ghBasisVec hp hm perm R ∅ w + z.2 * ghBasisVec hp hm perm R J w
private lemma ghCollState_eq_zoomProdState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} {j₀ : Fin m}
    (hj₀ : R.image (fun x ↦ subcubePref hp hm (perm x)) = {j₀}) (z : ℂ × ℂ) :
    ghCollState hp hm perm R z =
      zoomProdState fun j ↦ zoomSlotWrap hp hm perm j
        (if j = j₀ then grover2DVecC (subcubeLocalSet hp hm (R.image perm) j₀) z.1 z.2
         else groverMultiState ∅ 0) := by
  funext w
  unfold ghCollState ghBasisVec zoomProdState
  dsimp only
  simp_rw [hj₀]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
  have her1 :
      (∏ x ∈ Finset.univ.erase j₀,
        zoomSlotWrap hp hm perm x
          (if x ∈ ({j₀} : Finset (Fin m)) then
            if x ∈ (∅ : Finset (Fin m)) then
              grover2DVec (subcubeLocalSet hp hm (R.image perm) x) 0 1
            else grover2DVec (subcubeLocalSet hp hm (R.image perm) x) 1 0
          else groverMultiState ∅ 0)
          ((groupReg (Nat.mul_one m) x).extractIndex w)) =
      ∏ x ∈ Finset.univ.erase j₀,
        zoomSlotWrap hp hm perm x (groverMultiState ∅ 0)
          ((groupReg (Nat.mul_one m) x).extractIndex w) := by
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    have hne : x ≠ j₀ := (Finset.mem_erase.mp hx).1
    simp [hne]
  have her2 :
      (∏ x ∈ Finset.univ.erase j₀,
        zoomSlotWrap hp hm perm x
          (if x ∈ ({j₀} : Finset (Fin m)) then
            if x ∈ ({j₀} : Finset (Fin m)) then
              grover2DVec (subcubeLocalSet hp hm (R.image perm) x) 0 1
            else grover2DVec (subcubeLocalSet hp hm (R.image perm) x) 1 0
          else groverMultiState ∅ 0)
          ((groupReg (Nat.mul_one m) x).extractIndex w)) =
      ∏ x ∈ Finset.univ.erase j₀,
        zoomSlotWrap hp hm perm x (groverMultiState ∅ 0)
          ((groupReg (Nat.mul_one m) x).extractIndex w) := by
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    have hne : x ≠ j₀ := (Finset.mem_erase.mp hx).1
    simp [hne]
  have her3 :
      (∏ x ∈ Finset.univ.erase j₀,
        zoomSlotWrap hp hm perm x
          (if x = j₀ then grover2DVecC (subcubeLocalSet hp hm (R.image perm) j₀) z.1 z.2
           else groverMultiState ∅ 0)
          ((groupReg (Nat.mul_one m) x).extractIndex w)) =
      ∏ x ∈ Finset.univ.erase j₀,
        zoomSlotWrap hp hm perm x (groverMultiState ∅ 0)
          ((groupReg (Nat.mul_one m) x).extractIndex w) := by
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    have hne : x ≠ j₀ := (Finset.mem_erase.mp hx).1
    simp [hne]
  rw [her1, her2, her3]
  simp only [Finset.mem_singleton, Finset.notMem_empty, ↓reduceIte]
  unfold grover2DVecC
  rw [zoomSlotWrap_eq_linear]
  ring
private lemma sum_normSq_ghBasisVec_coll {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (hsub3 : 3 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n)))
    {R : Finset (Fin (2 ^ n))} (hR2 : R.card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n)))) :
    let J := R.image fun x ↦ subcubePref hp hm (perm x)
    (∑ w : Fin (2 ^ (m * (n + 1))), normSq (ghBasisVec hp hm perm R ∅ w)) = 1 ∧
      (∑ w : Fin (2 ^ (m * (n + 1))), normSq (ghBasisVec hp hm perm R J w)) = 1 := by
  intro J
  obtain ⟨j₀, hj₀_img, hj₀_card, _⟩ := ghCollSlot_exists hp hm perm hR2 hNotInj
  constructor
  · unfold ghBasisVec
    rw [sum_normSq_zoomProdState]
    refine Finset.prod_eq_one fun j _ ↦ ?_
    refine sum_normSq_zoomSlotWrap_of_norm hp hm perm j _ 1 ?_
    by_cases hj : j = j₀
    · subst hj
      simp only [hj₀_img, Finset.mem_singleton, Finset.notMem_empty, ↓reduceIte]
      exact sum_normSq_grover2DVec_one_zero _ (by omega)
    · simp only [hj₀_img, Finset.mem_singleton, hj, ↓reduceIte]
      exact sum_normSq_groverMultiState_eq_one ∅ 0
  · dsimp only [J]
    unfold ghBasisVec
    rw [sum_normSq_zoomProdState]
    refine Finset.prod_eq_one fun j _ ↦ ?_
    refine sum_normSq_zoomSlotWrap_of_norm hp hm perm j _ 1 ?_
    by_cases hj : j = j₀
    · subst hj
      simp only [hj₀_img, Finset.mem_singleton, ↓reduceIte]
      exact sum_normSq_grover2DVec_zero_one _ (by omega)
    · simp only [hj₀_img, Finset.mem_singleton, hj, ↓reduceIte]
      exact sum_normSq_groverMultiState_eq_one ∅ 0
private lemma sum_normSq_ghCollState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (hsub3 : 3 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n)))
    {R : Finset (Fin (2 ^ n))} (hR2 : R.card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (z : ℂ × ℂ) :
    (∑ w : Fin (2 ^ (m * (n + 1))), normSq (ghCollState hp hm perm R z w)) =
      normSq z.1 + normSq z.2 := by
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  obtain ⟨j₀, hj₀_img, _, _⟩ := ghCollSlot_exists hp hm perm hR2 hNotInj
  have hneJ : (∅ : Finset (Fin m)) ≠ J := by
    dsimp only [J]
    rw [hj₀_img]
    exact (Finset.singleton_ne_empty j₀).symm
  have hpt (w : Fin (2 ^ (m * (n + 1)))) :
      normSq (ghCollState hp hm perm R z w) =
        normSq z.1 * normSq (ghBasisVec hp hm perm R ∅ w) +
          normSq z.2 * normSq (ghBasisVec hp hm perm R J w) := by
    unfold ghCollState
    dsimp only
    rcases ghBasisVec_mul_eq_zero_of_ne hp hm perm R
      (Finset.empty_subset J) Finset.Subset.rfl hneJ w with h0 | h1
    · rw [h0, mul_zero, zero_add, Complex.normSq_zero, mul_zero, zero_add, map_mul]
    · rw [h1, mul_zero, add_zero, Complex.normSq_zero, mul_zero, add_zero, map_mul]
  rcases sum_normSq_ghBasisVec_coll hp hm hsub3 perm hR2 hNotInj with ⟨hs0, hs1⟩
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs0, hs1, mul_one, mul_one]
private lemma ghPrep_grover_eq_ghCollState {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))}
    {active : ℕ} {μ : Fin (2 ^ (k * n))}
    (hsub : memSeen n k (memPrefix k active) μ ⊆ S)
    (hR2 : (S \ memSeen n k (memPrefix k active) μ).card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x))
      ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))))
    (kInit : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let R := S \ memSeen n k (memPrefix k active) μ
    let θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let prepOp := (lowBlock W M).embedMatrix (wdPrepUnitary hp hm perm).1
    ((diffOp * phaseOp) ^ kInit) *ᵥ (prepOp *ᵥ single (workMemIdx n m k 0 μ) 1) =
      workMemState (ghCollState hp hm perm R (ghInitColl2 θ₂ kInit)) (single μ 1) := by
  dsimp only
  rw [wdPrepUnitary_mulVec_workMemIdx_gh hp hm perm μ,
    ghDeflatedGrover_iter_zoomProdState hp hm perm hsub (fun j ↦ j) _ kInit]
  set R := S \ memSeen n k (memPrefix k active) μ
  set θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
  obtain ⟨j₀, hj₀_img, hj₀_card, hj₀_empty⟩ := ghCollSlot_exists hp hm perm hR2 hNotInj
  rw [ghCollState_eq_zoomProdState hp hm perm hj₀_img]
  congr 1
  funext w
  unfold zoomProdState
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  dsimp only
  by_cases hj : j = j₀
  · subst hj
    rw [ite_eq_left rfl]
    have h0 : 0 < (subcubeLocalSet hp hm (R.image perm) j).card := by omega
    have hlt : (subcubeLocalSet hp hm (R.image perm) j).card < 2 ^ (n - p) := by omega
    have hθ : Real.arcsin (√(((subcubeLocalSet hp hm (R.image perm) j).card : ℝ) /
        (2 ^ (n - p) : ℝ))) = θ₂ := by
      rw [hj₀_card, Nat.cast_two, Real.sqrt_div zero_le_two]
    have hinit := hadamard_zero_eq_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0 hlt
    have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0 hlt
      kInit (Real.cos θ₂) (Real.sin θ₂)
    rw [hθ] at hinit hiter
    dsimp only at hinit hiter
    have hc_add :
        Real.cos (2 * (kInit : ℝ) * θ₂) * Real.cos θ₂ -
          Real.sin (2 * (kInit : ℝ) * θ₂) * Real.sin θ₂ =
          Real.cos ((2 * (kInit : ℝ) + 1) * θ₂) := by
      rw [← Real.cos_add]
      exact congrArg Real.cos (by ring)
    have hs_add :
        Real.sin (2 * (kInit : ℝ) * θ₂) * Real.cos θ₂ +
          Real.cos (2 * (kInit : ℝ) * θ₂) * Real.sin θ₂ =
          Real.sin ((2 * (kInit : ℝ) + 1) * θ₂) := by
      rw [← Real.sin_add]
      exact congrArg Real.sin (by ring)
    rw [hc_add, hs_add] at hiter
    rw [hinit, hiter, grover2DVec_linear]
    rfl
  · rw [ite_eq_right hj, hj₀_empty j hj, ← groverMultiState_zero_eq_hadamard_mulVec ∅,
      Function.iterate_fixed diffuser_oracle_empty_groverMultiState_zero]
private lemma ghGrover_iter_ghCollState {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))}
    {active : ℕ} {μ : Fin (2 ^ (k * n))}
    (hsub : memSeen n k (memPrefix k active) μ ⊆ S)
    (hR2 : (S \ memSeen n k (memPrefix k active) μ).card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x))
      ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))))
    (z : ℂ × ℂ) (kNext : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let R := S \ memSeen n k (memPrefix k active) μ
    let θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
    let ck := (Real.cos (2 * (kNext : ℝ) * θ₂) : ℂ)
    let sk := (Real.sin (2 * (kNext : ℝ) * θ₂) : ℂ)
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    ((diffOp * phaseOp) ^ kNext) *ᵥ workMemState (ghCollState hp hm perm R z) (single μ 1) =
      workMemState
        (ghCollState hp hm perm R (ck * z.1 - sk * z.2, sk * z.1 + ck * z.2))
        (single μ 1) := by
  dsimp only
  obtain ⟨j₀, hj₀_img, hj₀_card, hj₀_empty⟩ := ghCollSlot_exists hp hm perm hR2 hNotInj
  rw [ghCollState_eq_zoomProdState hp hm perm hj₀_img z,
    ghDeflatedGrover_iter_zoomProdState hp hm perm hsub (fun j ↦ j) _ kNext]
  set R := S \ memSeen n k (memPrefix k active) μ
  set θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
  rw [ghCollState_eq_zoomProdState hp hm perm hj₀_img]
  congr 1
  funext w
  unfold zoomProdState
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  dsimp only
  by_cases hj : j = j₀
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have h0 : 0 < (subcubeLocalSet hp hm (R.image perm) j).card := by omega
    have hlt : (subcubeLocalSet hp hm (R.image perm) j).card < 2 ^ (n - p) := by omega
    have hθ : Real.arcsin (√(((subcubeLocalSet hp hm (R.image perm) j).card : ℝ) /
        (2 ^ (n - p) : ℝ))) = θ₂ := by
      rw [hj₀_card, Nat.cast_two, Real.sqrt_div zero_le_two]
    have hiter := diffuser_oracle_iter_grover2DVecC
      (subcubeLocalSet hp hm (R.image perm) j) h0 hlt kNext z.1 z.2
    dsimp only at hiter
    rw [hθ] at hiter
    rw [hiter]
  · rw [ite_eq_right hj, ite_eq_right hj, hj₀_empty j hj,
      Function.iterate_fixed diffuser_oracle_empty_groverMultiState_zero]
private lemma ghDamp_and_click_marked_ghCollState {n p m : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n)))
    {R : Finset (Fin (2 ^ n))} (hR2 : R.card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (pr : GHZoomProbe) (z : ℂ × ℂ) :
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    ghDampVec n m (ghProbeWSpec2 pr) (P_R *ᵥ ghCollState hp hm perm R z) =
        P_R *ᵥ ghCollState hp hm perm R (z.1, pr.1.val * z.2) ∧
      ghClickVec n m (ghProbeWSpec2 pr) (P_R *ᵥ ghCollState hp hm perm R z) = 0 := by
  intro P_R
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  obtain ⟨j₀, hj₀_img, _, _⟩ := ghCollSlot_exists hp hm perm hR2 hNotInj
  have hJ_card : J.card = 1 := by dsimp only [J]; rw [hj₀_img, Finset.card_singleton]
  have hneJ : (∅ : Finset (Fin m)) ≠ J := by
    dsimp only [J]; rw [hj₀_img]; exact (Finset.singleton_ne_empty j₀).symm
  constructor
  · funext o
    dsimp only [ghDampVec, P_R]
    rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom,
      permUnitary_parallelMarkPerm_mulVec_apply_zoom]
    set w := parallelMarkPerm n m R o
    unfold ghCollState
    dsimp only
    by_cases h0 : ghBasisVec hp hm perm R ∅ w ≠ 0
    · have h1 : ghBasisVec hp hm perm R J w = 0 := by
        rcases ghBasisVec_mul_eq_zero_of_ne hp hm perm R
          (Finset.empty_subset J) Finset.Subset.rfl hneJ w with ha | hb
        · exact absurd ha h0
        · exact hb
      have hcnt : wdHitCount n m o = 0 := by
        simpa using (ghBasisVec_support_props hp hm perm R (Finset.empty_subset J) o h0).2.2.2
      rw [h1, hcnt]
      simp [ghProbeWSpec2, gaussOne, pythOne, GaussPyth.val, PythPair.cVal]
    · rw [not_not] at h0
      rw [h0, mul_zero, zero_add, zero_add]
      by_cases h1 : ghBasisVec hp hm perm R J w ≠ 0
      · have hcnt : wdHitCount n m o = 1 := by
          have hc := (ghBasisVec_support_props hp hm perm R Finset.Subset.rfl o h1).2.2.2
          rwa [hJ_card] at hc
        rw [hcnt]
        simp [ghProbeWSpec2, pythOne, PythPair.cVal, mul_assoc]
      · rw [not_not] at h1
        rw [h1, mul_zero, mul_zero, mul_zero]
  · funext o
    dsimp only [ghClickVec, P_R]
    rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom]
    set w := parallelMarkPerm n m R o
    unfold ghCollState
    dsimp only
    by_cases h0 : ghBasisVec hp hm perm R ∅ w ≠ 0
    · have h1 : ghBasisVec hp hm perm R J w = 0 := by
        rcases ghBasisVec_mul_eq_zero_of_ne hp hm perm R
          (Finset.empty_subset J) Finset.Subset.rfl hneJ w with ha | hb
        · exact absurd ha h0
        · exact hb
      have hcnt : wdHitCount n m o = 0 := by
        simpa using (ghBasisVec_support_props hp hm perm R (Finset.empty_subset J) o h0).2.2.2
      rw [h1, hcnt]
      simp [ghProbeWSpec2, pythOne, PythPair.sVal]
    · rw [not_not] at h0
      rw [h0, mul_zero, zero_add]
      by_cases h1 : ghBasisVec hp hm perm R J w ≠ 0
      · have hcnt : wdHitCount n m o = 1 := by
          have hc := (ghBasisVec_support_props hp hm perm R Finset.Subset.rfl o h1).2.2.2
          rwa [hJ_card] at hc
        rw [hcnt]
        simp [ghProbeWSpec2, pythOne, PythPair.sVal]
      · rw [not_not] at h1
        rw [h1, mul_zero, mul_zero]; rfl
private lemma sum_normSq_zoomSlotWrap_coll_hit {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} {j₀ : Fin m}
    (hj₀_img : R.image (fun x ↦ subcubePref hp hm (perm x)) = {j₀})
    (hj₀_card : (subcubeLocalSet hp hm (R.image perm) j₀).card = 2)
    {x₀ : Fin (2 ^ n)} (hx₀ : x₀ ∈ R) :
    (∑ z : Fin (2 ^ (1 * (n + 1))),
      if firstMarkedAddr n 1 (parallelMarkPerm n 1 R z) = some x₀ then
        normSq (zoomSlotWrap hp hm perm j₀
          (grover2DVec (subcubeLocalSet hp hm (R.image perm) j₀) 0 1) z)
      else 0) = 1 / 2 := by
  let M_loc := subcubeLocalSet hp hm (R.image perm) j₀
  let φ := grover2DVec M_loc 0 1
  have hx₀_pref : subcubePref hp hm (perm x₀) = j₀ := by
    have hm_img : subcubePref hp hm (perm x₀) ∈ R.image (fun x ↦ subcubePref hp hm (perm x)) :=
      Finset.mem_image_of_mem _ hx₀
    rwa [hj₀_img, Finset.mem_singleton] at hm_img
  let w₀ : Fin (2 ^ (n - p)) := (subcubeSplit hp hm (perm x₀)).1
  have hw₀_mem : w₀ ∈ M_loc := by
    rw [mem_subcubeLocalSet_iff]
    have hsp : (subcubeSplit hp hm).symm (w₀, j₀) = perm x₀ := by
      have h1 : (w₀, j₀) = subcubeSplit hp hm (perm x₀) :=
        Prod.ext rfl hx₀_pref.symm
      rw [h1, Equiv.symm_apply_apply]
    rw [hsp]
    exact Finset.mem_image_of_mem perm hx₀
  let z₀ : Fin (2 ^ (1 * (n + 1))) :=
    (addrReg n 1).basisSplitEquiv.symm
      ((wdPerm1n perm).symm ((zoomCast1nEquiv hp).symm
        ((lowHighEquiv (n - p) p).symm (w₀, finCongr hm j₀))), 0)
  have hz₀_val : zoomSlotWrap hp hm perm j₀ φ z₀ = φ w₀ := by
    dsimp only [z₀, zoomSlotWrap, tensorState, workMemState, Function.comp_apply]
    rw [← QRegister.basisSplitEquiv_apply_fst]
    simp only [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  have hφ_w₀ : φ w₀ = (1 / √2 : ℝ) := by
    dsimp only [φ, grover2DVec]
    rw [ite_eq_left hw₀_mem, hj₀_card, Nat.cast_two]
  have hz₀_nz : zoomSlotWrap hp hm perm j₀ φ z₀ ≠ 0 := by
    rw [hz₀_val, hφ_w₀]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hz₀_hit : firstMarkedAddr n 1 (parallelMarkPerm n 1 R z₀) = some x₀ := by
    have hsp := zoomSlotWrap_support_firstMarkedAddr hp hm perm R j₀ φ z₀ hz₀_nz
    have hloc_z₀ :
        (lowHighEquiv (n - p) p (zoomCast1nEquiv hp
          (wdPerm1n perm ((addrReg n 1).extractIndex z₀)))).1 = w₀ := by
      dsimp only [z₀]
      rw [← QRegister.basisSplitEquiv_apply_fst]
      simp only [Equiv.apply_symm_apply]
    rw [hsp.2.2.2, hloc_z₀, ite_eq_left hw₀_mem, Option.some.injEq]
    have hsp_px : (w₀, j₀) = subcubeSplit hp hm (perm x₀) :=
      Prod.ext rfl hx₀_pref.symm
    rw [hsp_px, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single z₀ (fun z _ hne ↦ ?_) (fun hnot ↦ absurd (Finset.mem_univ z₀) hnot),
    ite_eq_left hz₀_hit, hz₀_val, hφ_w₀, Complex.normSq_ofReal, div_mul_div_comm, one_mul,
    Real.mul_self_sqrt zero_le_two]
  by_cases hnz : zoomSlotWrap hp hm perm j₀ φ z = 0
  · rw [hnz, Complex.normSq_zero, ite_self]
  · rcases zoomSlotWrap_support_firstMarkedAddr hp hm perm R j₀ φ z hnz with
      ⟨hE, hφ_z, hy_z, hfa_z⟩
    set u := (addrReg n 1).extractIndex z
    set w_loc := (lowHighEquiv (n - p) p (zoomCast1nEquiv hp (wdPerm1n perm u))).1
    have hw_mem : w_loc ∈ M_loc := by
      by_contra hnot
      apply hφ_z
      dsimp only [φ, grover2DVec]
      rw [ite_eq_right hnot, zero_div, Complex.ofReal_zero]
    have hne_w : w_loc ≠ w₀ := by
      intro heq_w
      apply hne
      have hlh : lowHighEquiv (n - p) p (zoomCast1nEquiv hp (wdPerm1n perm u)) =
          (w₀, finCongr hm j₀) := Prod.ext heq_w hy_z
      have hu_eq : u = (wdPerm1n perm).symm ((zoomCast1nEquiv hp).symm
          ((lowHighEquiv (n - p) p).symm (w₀, finCongr hm j₀))) := by
        rw [← hlh, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have hbs : (addrReg n 1).basisSplitEquiv z = (u, 0) :=
        Prod.ext (QRegister.basisSplitEquiv_apply_fst _ z) hE
      dsimp only [z₀]
      rw [← hu_eq, ← hbs, Equiv.symm_apply_apply]
    have hne_fa : firstMarkedAddr n 1 (parallelMarkPerm n 1 R z) ≠ some x₀ := by
      rw [hfa_z, ite_eq_left hw_mem]
      intro hsome
      have hx_eq := Option.some.inj hsome
      have hp_eq := congrArg (subcubeSplit hp hm ∘ perm) hx_eq
      dsimp only [Function.comp_apply] at hp_eq
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hp_eq
      exact hne_w (congrArg Prod.fst hp_eq)
    exact ite_eq_right hne_fa
private lemma sum_normSq_ghCollState_readout {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (hsub3 : 3 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n)))
    {R : Finset (Fin (2 ^ n))} (hR2 : R.card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n))))
    (z : ℂ × ℂ) (G : Finset (Fin (2 ^ n)) → ℂ) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∑ o : Fin (2 ^ (m * (n + 1))),
      (normSq (ghCollState hp hm perm R z (parallelMarkPerm n m R o)) : ℂ) *
        G (R \ (groupHits hbg1 o).toFinset)) =
      (normSq z.1 : ℂ) * G R +
        (normSq z.2 : ℂ) * ∑ x ∈ R, ((1 / 2 : ℝ) : ℂ) * G (R \ {x}) := by
  intro hbg1
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  obtain ⟨j₀, hj₀_img, hj₀_card, _⟩ := ghCollSlot_exists hp hm perm hR2 hNotInj
  have hneJ : (∅ : Finset (Fin m)) ≠ J := by
    dsimp only [J]; rw [hj₀_img]; exact (Finset.singleton_ne_empty j₀).symm
  rcases sum_normSq_ghBasisVec_coll hp hm hsub3 perm hR2 hNotInj with ⟨hs0, _⟩
  have hsplit (o : Fin (2 ^ (m * (n + 1)))) :
      (normSq (ghCollState hp hm perm R z (parallelMarkPerm n m R o)) : ℂ) *
          G (R \ (groupHits hbg1 o).toFinset) =
        (normSq z.1 : ℂ) *
            ((normSq (ghBasisVec hp hm perm R ∅ (parallelMarkPerm n m R o)) : ℂ) *
              G (R \ (groupHits hbg1 o).toFinset)) +
          (normSq z.2 : ℂ) *
            ((normSq (ghBasisVec hp hm perm R J (parallelMarkPerm n m R o)) : ℂ) *
              G (R \ (groupHits hbg1 o).toFinset)) := by
    set w := parallelMarkPerm n m R o
    unfold ghCollState
    dsimp only
    rcases ghBasisVec_mul_eq_zero_of_ne hp hm perm R
      (Finset.empty_subset J) Finset.Subset.rfl hneJ w with h0 | h1
    · rw [h0, mul_zero, zero_add, Complex.normSq_zero, Complex.ofReal_zero, zero_mul, mul_zero,
        zero_add, map_mul, Complex.ofReal_mul, mul_assoc]
    · rw [h1, mul_zero, add_zero, Complex.normSq_zero, Complex.ofReal_zero, zero_mul, mul_zero,
        add_zero, map_mul, Complex.ofReal_mul, mul_assoc]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  · congr 1
    have hterm0 (o : Fin (2 ^ (m * (n + 1)))) :
        (normSq (ghBasisVec hp hm perm R ∅ (parallelMarkPerm n m R o)) : ℂ) *
            G (R \ (groupHits hbg1 o).toFinset) =
          (normSq (ghBasisVec hp hm perm R ∅ (parallelMarkPerm n m R o)) : ℂ) * G R := by
      by_cases hnz : ghBasisVec hp hm perm R ∅ (parallelMarkPerm n m R o) = 0
      · simp [hnz]
      · have hlen := (ghBasisVec_support_props hp hm perm R (Finset.empty_subset J) o hnz).2.2.2
        unfold wdHitCount at hlen
        simp only [Finset.card_empty] at hlen
        rw [List.eq_nil_of_length_eq_zero hlen, List.toFinset_nil, Finset.sdiff_empty]
    rw [Finset.sum_congr rfl fun o _ ↦ hterm0 o, ← Finset.sum_mul, ← Complex.ofReal_sum,
      Equiv.sum_comp (parallelMarkPerm n m R) (fun w ↦ normSq (ghBasisVec hp hm perm R ∅ w)),
      hs0, Complex.ofReal_one, one_mul]
  · congr 1
    let ξ (j : Fin m) : Fin (2 ^ (1 * (n + 1))) → ℂ :=
      zoomSlotWrap hp hm perm j
        (if j ∈ J then
          if j ∈ J then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1
          else grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0
        else groverMultiState ∅ 0)
    have hbasis_ξ : ghBasisVec hp hm perm R J = zoomProdState ξ := rfl
    rw [hbasis_ξ]
    have hinv_sum :
        (∑ o : Fin (2 ^ (m * (n + 1))),
          (normSq (zoomProdState ξ (parallelMarkPerm n m R o)) : ℂ) *
            G (R \ (groupHits hbg1 o).toFinset)) =
        ∑ w : Fin (2 ^ (m * (n + 1))),
          (normSq (zoomProdState ξ w) : ℂ) *
            G (R \ (groupHits hbg1 (parallelMarkPerm n m R w)).toFinset) := by
      rw [← Equiv.sum_comp (parallelMarkPerm n m R)]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [parallelMarkPerm_involutive]
    rw [hinv_sum, ← (groupSplitEquiv hbg1).symm.sum_comp]
    let hit0 (z : Fin (2 ^ (1 * (n + 1)))) : Option (Fin (2 ^ n)) :=
      firstMarkedAddr n 1 (parallelMarkPerm n 1 R z)
    have hzs (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) :
        (normSq (zoomProdState ξ ((groupSplitEquiv hbg1).symm zs)) : ℂ) *
            G (R \ (groupHits hbg1 (parallelMarkPerm n m R
              ((groupSplitEquiv hbg1).symm zs))).toFinset) =
          ∑ x ∈ R,
            (if hit0 (zs j₀) = some x then (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) else 0) *
              G (R \ {x}) := by
      have hex (j : Fin m) :
          (groupReg hbg1 j).extractIndex ((groupSplitEquiv hbg1).symm zs) = zs j := by
        rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
      have hprod :
          (normSq (zoomProdState ξ ((groupSplitEquiv hbg1).symm zs)) : ℂ) =
            ∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ) := by
        unfold zoomProdState
        simp_rw [hex, map_prod, Complex.ofReal_prod]
      rw [hprod]
      by_cases hzero : (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) = 0
      · rw [hzero, zero_mul]
        refine (Finset.sum_eq_zero fun x _ ↦ ?_).symm
        split_ifs <;> simp
      · have hnz (j : Fin m) : ξ j (zs j) ≠ 0 := by
          intro hj0
          apply hzero
          refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
          rw [hj0, Complex.normSq_zero, Complex.ofReal_zero]
        set o_zs := parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs)
        have hslot_nz (j : Fin m) :
            ξ j ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o_zs)) ≠ 0 := by
          dsimp only [o_zs]
          rw [parallelMarkPerm_involutive, hex]
          exact hnz j
        rcases groupHits_of_zoomSlotWrap hp hm perm R id
            (fun j ↦ if j ∈ J then
              if j ∈ J then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1
              else grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0
            else groverMultiState ∅ 0) o_zs hslot_nz with ⟨hmem_sub, htf_eq⟩
        have hξ_j₀ : ξ j₀ (zs j₀) =
            zoomSlotWrap hp hm perm j₀
              (grover2DVec (subcubeLocalSet hp hm (R.image perm) j₀) 0 1) (zs j₀) := by
          simp [ξ, J, hj₀_img]
        have hnz_j₀ :
            zoomSlotWrap hp hm perm j₀
              (grover2DVec (subcubeLocalSet hp hm (R.image perm) j₀) 0 1) (zs j₀) ≠ 0 :=
          hξ_j₀ ▸ hnz j₀
        rcases zoomSlotWrap_support_firstMarkedAddr hp hm perm R j₀ _ (zs j₀) hnz_j₀ with
          ⟨_, hφ_j₀, _, hfa_j₀⟩
        set w_loc := (lowHighEquiv (n - p) p (zoomCast1nEquiv hp
          (wdPerm1n perm ((addrReg n 1).extractIndex (zs j₀))))).1
        have hw_mem : w_loc ∈ subcubeLocalSet hp hm (R.image perm) j₀ := by
          by_contra hnot
          apply hφ_j₀
          unfold grover2DVec
          rw [ite_eq_right hnot, zero_div, Complex.ofReal_zero]
        let x_hit := perm.symm ((subcubeSplit hp hm).symm (w_loc, j₀))
        have hhit_j₀ : hit0 (zs j₀) = some x_hit := by
          dsimp only [hit0]
          rw [hfa_j₀, ite_eq_left hw_mem]
        have hx_hit_R : x_hit ∈ R := by
          have hex_o : (groupReg hbg1 j₀).extractIndex o_zs = parallelMarkPerm n 1 R (zs j₀) := by
            dsimp only [o_zs]
            rw [extractIndex_groupReg_parallelMarkPerm, hex]
          exact (hmem_sub j₀ x_hit ((congrArg (firstMarkedAddr n 1) hex_o).trans hhit_j₀)).1
        have htf_sing : (groupHits hbg1 o_zs).toFinset = {x_hit} := by
          rw [htf_eq]
          ext y
          simp only [List.mem_toFinset, List.mem_filterMap, mem_finRange, true_and,
            Finset.mem_singleton]
          constructor
          · rintro ⟨j, hj_y⟩
            rcases hmem_sub j y hj_y with ⟨hyR, hpref_y⟩
            have hj_eq : j = j₀ := by
              have hmem_J : subcubePref hp hm (perm y) ∈ J := Finset.mem_image_of_mem _ hyR
              dsimp only [J] at hmem_J
              rw [hj₀_img, Finset.mem_singleton] at hmem_J
              exact hpref_y.symm.trans hmem_J
            subst hj_eq
            have hex_o : (groupReg hbg1 j).extractIndex o_zs = parallelMarkPerm n 1 R (zs j) := by
              dsimp only [o_zs]
              rw [extractIndex_groupReg_parallelMarkPerm, hex]
            rw [hex_o] at hj_y
            exact Option.some.inj (hj_y.symm.trans hhit_j₀)
          · rintro rfl
            refine ⟨j₀, ?_⟩
            dsimp only [o_zs]
            rwa [extractIndex_groupReg_parallelMarkPerm, hex]
        rw [htf_sing, Finset.sum_eq_single x_hit (fun x _ hne ↦ by
            have hne_s : hit0 (zs j₀) ≠ some x := by
              rw [hhit_j₀]; exact fun h ↦ hne (Option.some.inj h).symm
            rw [ite_eq_right hne_s, zero_mul])
            (fun hnot ↦ absurd hx_hit_R hnot), ite_eq_left hhit_j₀]
    simp_rw [hzs]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← Finset.sum_mul]
    congr 1
    let splitJ : (Fin m → Fin (2 ^ (1 * (n + 1)))) ≃
        Fin (2 ^ (1 * (n + 1))) × ({j : Fin m // j ≠ j₀} → Fin (2 ^ (1 * (n + 1)))) :=
      Equiv.piSplitAt j₀ (fun _ ↦ Fin (2 ^ (1 * (n + 1))))
    rw [← splitJ.symm.sum_comp, sum_prod_type]
    have hsplit_term (z₀ : Fin (2 ^ (1 * (n + 1))))
        (zrest : {j : Fin m // j ≠ j₀} → Fin (2 ^ (1 * (n + 1)))) :
        (if hit0 (splitJ.symm (z₀, zrest) j₀) = some x then
            ∏ j : Fin m, (normSq (ξ j (splitJ.symm (z₀, zrest) j)) : ℂ)
          else 0) =
          (if hit0 z₀ = some x then (normSq (ξ j₀ z₀) : ℂ) else 0) *
            ∏ j : {j : Fin m // j ≠ j₀}, (normSq (ξ j.1 (zrest j)) : ℂ) := by
      have hj₀_app : splitJ.symm (z₀, zrest) j₀ = z₀ := by simp [splitJ]
      rw [hj₀_app]
      by_cases hh : hit0 z₀ = some x
      · rw [ite_eq_left hh, ite_eq_left hh,
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀), hj₀_app]
        congr 1
        refine Finset.prod_bij (fun j hj ↦ ⟨j, (Finset.mem_erase.mp hj).1⟩)
          (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ congrArg Subtype.val h)
          (fun j _ ↦ ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩, rfl⟩)
          (fun j hj ↦ ?_)
        have hne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
        simp [splitJ, hne]
      · rw [ite_eq_right hh, ite_eq_right hh, zero_mul]
    simp_rw [hsplit_term, ← Finset.mul_sum,
      ← Fintype.prod_sum (fun (j : {j : Fin m // j ≠ j₀}) z ↦ (normSq (ξ j.1 z) : ℂ))]
    have hrest_one :
        (∏ j : {j : Fin m // j ≠ j₀}, ∑ z, (normSq (ξ j.1 z) : ℂ)) = 1 := by
      refine Finset.prod_eq_one fun j _ ↦ ?_
      have hj_not : j.1 ∉ J := by
        dsimp only [J]
        rw [hj₀_img, Finset.mem_singleton]
        exact j.2
      have hξ_j : ξ j.1 = zoomSlotWrap hp hm perm j.1 (groverMultiState ∅ 0) := by
        dsimp only [ξ]
        rw [ite_eq_right hj_not]
      rw [hξ_j, ← Complex.ofReal_sum,
        sum_normSq_zoomSlotWrap_of_norm hp hm perm j.1 _ 1 (sum_normSq_groverMultiState_eq_one ∅ 0),
        Complex.ofReal_one]
    have hξ_j₀ : ξ j₀ = zoomSlotWrap hp hm perm j₀
        (grover2DVec (subcubeLocalSet hp hm (R.image perm) j₀) 0 1) := by
      simp [ξ, J, hj₀_img]
    simp only [hrest_one, mul_one, hξ_j₀]
    have hreal :
        (∑ z₀ : Fin (2 ^ (1 * (n + 1))),
          if hit0 z₀ = some x then
            (normSq (zoomSlotWrap hp hm perm j₀
              (grover2DVec (subcubeLocalSet hp hm (R.image perm) j₀) 0 1) z₀) : ℂ)
          else 0) =
        ((∑ z₀ : Fin (2 ^ (1 * (n + 1))),
          if hit0 z₀ = some x then
            normSq (zoomSlotWrap hp hm perm j₀
              (grover2DVec (subcubeLocalSet hp hm (R.image perm) j₀) 0 1) z₀)
          else 0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun z₀ _ ↦ ?_
      split_ifs <;> simp
    rw [hreal]
    dsimp only [hit0]
    exact congrArg Complex.ofReal (sum_normSq_zoomSlotWrap_coll_hit hp hm perm hj₀_img hj₀_card hx)
private lemma normSq_rot2D_real (cr sr : ℝ) (hcs : cr ^ 2 + sr ^ 2 = 1) (a b : ℂ) :
    normSq ((cr : ℂ) * a - (sr : ℂ) * b) + normSq ((sr : ℂ) * a + (cr : ℂ) * b) =
      normSq a + normSq b := by
  have key :
      normSq ((cr : ℂ) * a - (sr : ℂ) * b) + normSq ((sr : ℂ) * a + (cr : ℂ) * b) =
        (cr ^ 2 + sr ^ 2) * (normSq a + normSq b) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [key, hcs, one_mul]
private lemma ghCollNorm_probe (θ₂ : ℝ) (pr : GHZoomProbe) {z : ℂ × ℂ}
    (hz : normSq z.1 + normSq z.2 = 1) :
    (normSq z.1 + normSq (pr.1.val * z.2) = 1) ∧
      (normSq (ghProbeNextColl2 θ₂ pr z).1 + normSq (ghProbeNextColl2 θ₂ pr z).2 = 1) := by
  have hd : normSq z.1 + normSq (pr.1.val * z.2) = 1 := by
    rw [map_mul, GaussPyth.normSq_val, one_mul, hz]
  refine ⟨hd, ?_⟩
  unfold ghProbeNextColl2
  dsimp only
  rw [normSq_rot2D_real _ _ (Real.cos_sq_add_sin_sq _)]
  exact hd
/-! ## Section 3: QHL Semantics, `ScaledCostRel`, Subset DP, & Certified Drift Theorems -/
private lemma wdAmpStateC_congr_le {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) {u₁ u₂ : ℕ → ℂ}
    (hu : ∀ b ≤ R.card, u₁ b = u₂ b) :
    wdAmpStateC hp hm perm R u₁ = wdAmpStateC hp hm perm R u₂ := by
  funext w
  unfold wdAmpStateC
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  have hle : A.card ≤ R.card :=
    (Finset.card_le_card (Finset.mem_powerset.mp hA)).trans Finset.card_image_le
  rw [hu A.card hle]
private lemma gh_constAssertion_mono {Var : Type} {d : ℕ} {α₁ α₂ : ℝ}
    (h0 : 0 ≤ α₁) (h : α₁ ≤ α₂) (h1 : α₂ ≤ 1) :
    (constAssertion α₁ : CQAssertion (Store Var) d) ≤ constAssertion α₂ := fun σ ↦ by
  apply Subtype.coe_le_coe.mp
  rw [constAssertion_apply_of_bounds α₁ h0 (h.trans h1),
    constAssertion_apply_of_bounds α₂ (h0.trans h) h1]
  exact smul_le_smul_of_nonneg_right h (by simp)
private lemma gh_wp_constAssertion_le {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (P : QProg Var d) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    wp P (constAssertion α) ≤ constAssertion α := by
  induction P with
  | «skip» => exact le_rfl
  | «abort» => exact bot_le
  | assign _ _ => exact fun _ ↦ le_rfl
  | qMeasure x ℳ =>
    intro σ
    apply Subtype.coe_le_coe.mp
    rw [wp_qMeasure, CQAssertion.qMeasure_coe, constAssertion_apply_of_bounds α hα0 hα1]
    have hsum :
        (∑ o : Fin _,
          HermitianMat.conj (ℳ.1 o)ᴴ
            (((constAssertion α : CQAssertion (Store Var) d) (σ.subst x ↑o.1)).1)) =
        α • ∑ o : Fin _, HermitianMat.conj (ℳ.1 o)ᴴ 1 := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      rw [constAssertion_apply_of_bounds α hα0 hα1]
      apply HermitianMat.ext
      simp [HermitianMat.conj_apply_mat]
    rw [hsum]
    exact smul_le_smul_of_nonneg_left (ℳ.sum_conj_le_one fun _ ↦ le_rfl) hα0
  | qSet =>
    intro σ
    apply Subtype.coe_le_coe.mp
    rw [wp_qSet, constAssertion_apply_of_bounds α hα0 hα1]
    have h00 : ((constAssertion α : CQAssertion (Store Var) d) σ).1.1 0 0 = (α : ℂ) := by
      rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1]
      simp
    refine le_of_eq ?_
    apply HermitianMat.ext
    rw [← HermitianMat.val_eq_coe, qhlQSet_val, h00]
    simp [HermitianMat.mat_smul, HermitianMat.mat_one]
  | qAssign U =>
    intro σ
    apply Subtype.coe_le_coe.mp
    refine le_of_eq ?_
    apply HermitianMat.ext
    have hmat : ∀ τ : Store Var, ((constAssertion α : CQAssertion (Store Var) d) τ).1.1 =
        (α : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := fun τ ↦ by
      rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1,
        HermitianMat.mat_smul, HermitianMat.mat_one]
      ext i j
      simp [Complex.real_smul]
    rw [wp_qAssign, ← HermitianMat.val_eq_coe, qhlQAssign_val, hmat σ,
      ← HermitianMat.val_eq_coe, hmat σ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp U.2]
  | qSeq c₁ c₂ ih₁ ih₂ => exact (wp_mono c₁ ih₂).trans ih₁
  | qIf b c₁ c₂ ih₁ ih₂ =>
    intro σ; dsimp [wp]; split_ifs
    · exact ih₁ σ
    · exact ih₂ σ
  | qWhile b c ih =>
    have hrec : ∀ t, whileRecWP (wp c) b t (constAssertion α) ≤ constAssertion α := by
      intro t
      induction t with
      | zero => exact bot_le
      | succ t iht =>
        intro σ; dsimp [whileRecWP]; split_ifs
        · exact ((wp_mono c iht).trans ih) σ
        · exact le_rfl
    intro σ
    rw [wp_qWhile]
    exact OmegaCompletePartialOrder.ωSup_le
      (whileRecWP.chain (wp c) (wp_mono c) b (constAssertion α)) (constAssertion α) hrec σ
private lemma gh_expect_constAssertion {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    𝔼[Δ, constAssertion α] = α * Δ.trace := by
  rw [expect_eq_mul_of_apply_eq_smul Δ (Ψ := ⊤) α (fun σ ↦ by
    rw [constAssertion_apply_of_bounds α hα0 hα1]
    rfl), expect_top]
private lemma gh_expect_nonneg {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) (θ : CQAssertion
    (Store Var) d) :
    0 ≤ 𝔼[Δ, θ] := by
  simpa using expect_mono (le_rfl : Δ ≤ Δ) (bot_le : ⊥ ≤ θ)
private lemma ghScaledCostRel_of_zero {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {model : CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d}
    (hP : CostBound (Var := Var) model P 0) :
    ScaledCostRel model B P ⊥ 0 := by
  refine ⟨le_rfl, hB.le, bot_le, fun Δ ↦ ?_⟩
  have h0 := hP Δ
  simp only [ENNReal.coe_zero, mul_zero, nonpos_iff_eq_zero] at h0
  simp [h0]
private lemma ghScaledCostRel_of_costBound {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {model : CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d} {k_cost : ℝ≥0}
    (hP : CostBound (Var := Var) model P k_cost) (hkB : (k_cost : ℝ) ≤ B) :
    ScaledCostRel model B P (constAssertion ((k_cost : ℝ) / B)) (k_cost : ℝ) := by
  have hc0 : 0 ≤ (k_cost : ℝ) := NNReal.coe_nonneg k_cost
  have hdiv0 : 0 ≤ (k_cost : ℝ) / B := div_nonneg hc0 hB.le
  have hdiv1 : (k_cost : ℝ) / B ≤ 1 := (div_le_one hB).mpr hkB
  refine ⟨hc0, hkB, le_rfl, fun Δ ↦ (hP Δ).trans ?_⟩
  rw [gh_expect_constAssertion Δ hdiv0 hdiv1, ← mul_assoc, mul_div_cancel₀ _ hB.ne',
    mul_comm (k_cost : ℝ) Δ.trace, ENNReal.ofReal_mul Δ.trace.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
private lemma ghScaledCostRel_qIf {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {model : CostModel d} {B : ℝ} (hB : 0 < B)
    (b : Store Var → Prop) [DecidablePred b]
    {P₁ P₂ : QProg Var d} {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ}
    (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel model B P₂ θ₂ c₂) :
    ScaledCostRel model B (.qIf b P₁ P₂) (fun σ ↦ if b σ then θ₁ σ else θ₂ σ) (max c₁ c₂) := by
  have hmB : max c₁ c₂ ≤ B := max_le h₁.2.1 h₂.2.1
  refine ⟨le_max_of_le_left h₁.1, hmB, fun σ ↦ ?_, fun Δ ↦ ?_⟩
  · dsimp only
    split_ifs
    · exact (h₁.2.2.1 σ).trans
        (gh_constAssertion_mono (div_nonneg h₁.1 hB.le)
          (div_le_div_of_nonneg_right (le_max_left c₁ c₂) hB.le)
          ((div_le_one hB).mpr hmB) σ)
    · exact (h₂.2.2.1 σ).trans
        (gh_constAssertion_mono (div_nonneg h₂.1 hB.le)
          (div_le_div_of_nonneg_right (le_max_right c₁ c₂) hB.le)
          ((div_le_one hB).mpr hmB) σ)
  · simp only [expectedCost]
    have hnn1 : 0 ≤ B * 𝔼[Δ.wdTrueSt b, θ₁] := mul_nonneg hB.le (gh_expect_nonneg _ _)
    have hnn2 : 0 ≤ B * 𝔼[Δ.wdFalseSt b, θ₂] := mul_nonneg hB.le (gh_expect_nonneg _ _)
    calc expectedCost model P₁ (Δ.wdTrueSt b) + expectedCost model P₂ (Δ.wdFalseSt b)
        ≤ ENNReal.ofReal (B * 𝔼[Δ.wdTrueSt b, θ₁]) +
            ENNReal.ofReal (B * 𝔼[Δ.wdFalseSt b, θ₂]) :=
          add_le_add (h₁.2.2.2 _) (h₂.2.2.2 _)
      _ = ENNReal.ofReal (B * 𝔼[Δ, fun σ ↦ if b σ then θ₁ σ else θ₂ σ]) := by
          rw [← ENNReal.ofReal_add hnn1 hnn2, ← mul_add, ← wdExpectItePartition]
private theorem ghScaledCostRel_add_le {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {model : CostModel d} {B : ℝ} (hB : 0 < B)
    {P₁ P₂ : QProg Var d} {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ}
    (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel model B P₂ θ₂ c₂)
    (hc_sum : c₁ + c₂ ≤ B) (σ : Store Var) :
    (θ₁ σ).1 + ((wp P₁ θ₂) σ).1 ≤ 1 := by
  have h_wp_le : wp P₁ θ₂ ≤ constAssertion (c₂ / B) :=
    (wp_mono P₁ h₂.2.2.1).trans
      (gh_wp_constAssertion_le P₁ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1))
  have ha : (θ₁ σ).1 ≤ (c₁ / B) • 1 := by
    have h := Subtype.coe_le_coe.mpr (h₁.2.2.1 σ)
    rwa [constAssertion_apply_of_bounds _ (div_nonneg h₁.1 hB.le)
      ((div_le_one hB).mpr h₁.2.1)] at h
  have hb : ((wp P₁ θ₂) σ).1 ≤ (c₂ / B) • 1 := by
    have h := Subtype.coe_le_coe.mpr (h_wp_le σ)
    rwa [constAssertion_apply_of_bounds _ (div_nonneg h₂.1 hB.le)
      ((div_le_one hB).mpr h₂.2.1)] at h
  calc (θ₁ σ).1 + ((wp P₁ θ₂) σ).1
      ≤ (c₁ / B) • 1 + (c₂ / B) • 1 := add_le_add ha hb
    _ = ((c₁ + c₂) / B) • 1 := by rw [add_div, add_smul]
    _ ≤ (1 : ℝ) • (1 : HermitianMat (Fin d) ℂ) :=
        smul_le_smul_of_nonneg_right ((div_le_one hB).mpr hc_sum) (by simp)
    _ = 1 := one_smul _ _
private lemma ghScaledCostRel_seq {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {model : CostModel d} {B : ℝ} (hB : 0 < B)
    {P₁ P₂ : QProg Var d} {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ}
    (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel model B P₂ θ₂ c₂)
    (hc_sum : c₁ + c₂ ≤ B) :
    ScaledCostRel model B (P₁ ;; P₂)
      (θ₁.add (wp P₁ θ₂) (ghScaledCostRel_add_le hB h₁ h₂ hc_sum)) (c₁ + c₂) := by
  have h_wp_le : wp P₁ θ₂ ≤ constAssertion (c₂ / B) :=
    (wp_mono P₁ h₂.2.2.1).trans
      (gh_wp_constAssertion_le P₁ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1))
  refine ⟨add_nonneg h₁.1 h₂.1, hc_sum, fun σ ↦ ?_, fun Δ ↦ ?_⟩
  · apply Subtype.coe_le_coe.mp
    rw [CQAssertion.add_apply, Observable.add_coe,
      constAssertion_apply_of_bounds _ (div_nonneg (add_nonneg h₁.1 h₂.1) hB.le)
        ((div_le_one hB).mpr hc_sum)]
    have ha : (θ₁ σ).1 ≤ (c₁ / B) • 1 := by
      have h := Subtype.coe_le_coe.mpr (h₁.2.2.1 σ)
      rwa [constAssertion_apply_of_bounds _ (div_nonneg h₁.1 hB.le)
        ((div_le_one hB).mpr h₁.2.1)] at h
    have hb : ((wp P₁ θ₂) σ).1 ≤ (c₂ / B) • 1 := by
      have h := Subtype.coe_le_coe.mpr (h_wp_le σ)
      rwa [constAssertion_apply_of_bounds _ (div_nonneg h₂.1 hB.le)
        ((div_le_one hB).mpr h₂.2.1)] at h
    calc (θ₁ σ).1 + ((wp P₁ θ₂) σ).1
        ≤ (c₁ / B) • 1 + (c₂ / B) • 1 := add_le_add ha hb
      _ = ((c₁ + c₂) / B) • 1 := by rw [add_div, add_smul]
  · rw [expectedCost_qSeq]
    have hnn1 : 0 ≤ B * 𝔼[Δ, θ₁] := mul_nonneg hB.le (gh_expect_nonneg _ _)
    have hnn2 : 0 ≤ B * 𝔼[(interp P₁).toStateFun Δ, θ₂] :=
      mul_nonneg hB.le (gh_expect_nonneg _ _)
    calc expectedCost model P₁ Δ + expectedCost model P₂ ((interp P₁).toStateFun Δ)
        ≤ ENNReal.ofReal (B * 𝔼[Δ, θ₁]) +
            ENNReal.ofReal (B * 𝔼[(interp P₁).toStateFun Δ, θ₂]) :=
          add_le_add (h₁.2.2.2 Δ) (h₂.2.2.2 _)
      _ = ENNReal.ofReal (B * 𝔼[Δ, θ₁.add (wp P₁ θ₂)
          (ghScaledCostRel_add_le hB h₁ h₂ hc_sum)]) := by
          rw [← ENNReal.ofReal_add hnn1 hnn2, ← wp_expectation_eq P₁ Δ θ₂,
            ← mul_add, ← expect_assertion_add]
private lemma ghScaledCostRel_mono_c {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {model : CostModel d} {B : ℝ} (hB : 0 < B)
    {P : QProg Var d} {θ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ}
    (h : ScaledCostRel model B P θ c₁) (hc : c₁ ≤ c₂) (hcB : c₂ ≤ B) :
    ScaledCostRel model B P θ c₂ :=
  ⟨h.1.trans hc, hcB,
    h.2.2.1.trans
      (gh_constAssertion_mono (div_nonneg h.1 hB.le)
        (div_le_div_of_nonneg_right hc hB.le) ((div_le_one hB).mpr hcB)),
    h.2.2.2⟩
private lemma ghScaledCostRel_seq_zero_left {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {model : CostModel d} {B : ℝ} (hB : 0 < B)
    {P₁ P₂ : QProg Var d} {θ₂ : CQAssertion (Store Var) d} {c₂ : ℝ}
    (h₁ : CostBound (Var := Var) model P₁ 0)
    (h₂ : ScaledCostRel model B P₂ θ₂ c₂) :
    ScaledCostRel model B (P₁ ;; P₂) (wp P₁ θ₂) c₂ := by
  refine ⟨h₂.1, h₂.2.1,
    (wp_mono P₁ h₂.2.2.1).trans
      (gh_wp_constAssertion_le P₁ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1)),
    fun Δ ↦ ?_⟩
  have h0 := h₁ Δ
  simp only [ENNReal.coe_zero, mul_zero, nonpos_iff_eq_zero] at h0
  rw [expectedCost_qSeq, h0, zero_add]
  exact (h₂.2.2.2 ((interp P₁).toStateFun Δ)).trans_eq (by rw [wp_expectation_eq])
private lemma gh_cqAssertion_add_mat {Var : Type} {d : ℕ}
    (θ₁ θ₂ : CQAssertion (Store Var) d) (h : ∀ σ, (θ₁ σ).1 + (θ₂ σ).1 ≤ 1) (σ : Store Var) :
    ((θ₁.add θ₂ h) σ).1.1 = (θ₁ σ).1.1 + (θ₂ σ).1.1 := by
  simp only [HermitianMat.val_eq_coe, CQAssertion.add_apply, Observable.add_coe,
    HermitianMat.mat_add]
private noncomputable def ghQuadForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) : ℂ :=
  star v ⬝ᵥ (A *ᵥ v)
private lemma ghQuadForm_zero_mat {d : ℕ} (v : Fin d → ℂ) :
    ghQuadForm (0 : Matrix (Fin d) (Fin d) ℂ) v = 0 := by
  unfold ghQuadForm; simp
private lemma ghQuadForm_bot_apply {Var : Type} {d : ℕ} (σ : Store Var) (v : Fin d → ℂ) :
    ghQuadForm ((⊥ : CQAssertion (Store Var) d) σ).1.1 v = 0 :=
  ghQuadForm_zero_mat v
private lemma ghQuadForm_zero_vec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ghQuadForm A (0 : Fin d → ℂ) = 0 := by
  unfold ghQuadForm; simp
private lemma ghQuadForm_add_mat {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    ghQuadForm (A + B) v = ghQuadForm A v + ghQuadForm B v := by
  unfold ghQuadForm
  rw [Matrix.add_mulVec, dotProduct_add]
private lemma ghQuadForm_single {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (idx : Fin d) :
    ghQuadForm A (single idx 1) = A idx idx :=
  (diag_eq_star_single_dotProduct_mulVec A idx).symm
private lemma ghQuadForm_smul_vec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (c : ℂ) (v : Fin d → ℂ) :
    ghQuadForm A (c • v) = (normSq c : ℂ) * ghQuadForm A v := by
  unfold ghQuadForm
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
private lemma ghQuadForm_unitaryEffect {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {P : QProg Var d} {U : Matrix (Fin d) (Fin d) ℂ} (hU : UnitaryEffect P U)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var) (v : Fin d → ℂ) :
    ghQuadForm ((wp P Θ) σ).1.1 v = ghQuadForm (Θ σ).1.1 (U *ᵥ v) := by
  unfold ghQuadForm
  rw [unitaryEffect_apply hU Θ σ, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
private lemma ghQuadForm_wp_measureRegister {Var : Type} [DecidableEq Var] (x : Var)
    {w Q : ℕ} (r : QRegister w Q) (Θ : CQAssertion (Store Var) (2 ^ Q))
    (σ : Store Var) (v : Fin (2 ^ Q) → ℂ) :
    ghQuadForm ((wp (measureRegister x r) Θ) σ).1.1 v =
      ∑ o : Fin (2 ^ w),
        ghQuadForm ((Θ (Store.subst σ x (Int.ofNat o.val))).1.1)
          (r.basisOutcomeProjector o *ᵥ v) := by
  unfold ghQuadForm
  rw [wp_measureRegister, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.vecMul_conjTranspose, star_star, QRegister.basisOutcomeProjector_conjTranspose]
private lemma ghQuadForm_constAssertion_workMemState {Var : Type} {W M : ℕ}
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (τ : Store Var)
    (ξ : Fin (2 ^ W) → ℂ) (μ : Fin (2 ^ M)) :
    ghQuadForm ((constAssertion α : CQAssertion (Store Var) (2 ^ (W + M))) τ).1.1
        (workMemState ξ (single μ 1)) =
      (α : ℂ) * ∑ w : Fin (2 ^ W), (normSq (ξ w) : ℂ) := by
  have hmat : ((constAssertion α : CQAssertion (Store Var) (2 ^ (W + M))) τ).1.1 =
      (α : ℂ) • (1 : Matrix (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ) := by
    rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1,
      HermitianMat.mat_smul, HermitianMat.mat_one]
    ext i j
    simp [Complex.real_smul]
  rw [hmat]
  unfold ghQuadForm
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [dotProduct]
  let f (z : Fin (2 ^ (W + M))) : ℂ :=
    star (workMemState ξ (single μ 1) z) * workMemState ξ (single μ 1) z
  change ∑ z, f z = _
  rw [← (lowHighEquiv W M).symm.sum_comp f, sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [sum_eq_single μ (fun ν hν ↦ by
    dsimp only [f, workMemState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hν, mul_zero, mul_zero])]
  dsimp only [f, workMemState]
  rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one, RCLike.star_def,
    ← Complex.normSq_eq_conj_mul_self]
private lemma memSeen_writeMemBatch_gh {n k active : ℕ} {S : Finset (Fin (2 ^ n))}
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
    (L : List (Fin (2 ^ n))) (hlen : active + L.length ≤ k) :
    memSeen n k (memPrefix k (active + L.length)) (writeMemBatch active L μ) =
      memSeen n k (memPrefix k active) μ ∪ L.toFinset := by
  have hslot_lt (i : Fin k) (hi : i.val < active) :
      addrEquiv n k (writeMemBatch active L μ) i = addrEquiv n k μ i := by
    unfold writeMemBatch
    rw [Equiv.apply_symm_apply, Pi.add_apply, ite_eq_right (not_le_of_gt hi), add_zero]
  have hslot_ge (i : Fin k) (hge : active ≤ i.val) (hlt : i.val < active + L.length) :
      addrEquiv n k (writeMemBatch active L μ) i = L[i.val - active]'(by omega) := by
    unfold writeMemBatch
    have hzero : addrEquiv n k μ i = 0 := hval.2.2.2 i hge
    have hsub : i.val - active < L.length := by omega
    rw [Equiv.apply_symm_apply, Pi.add_apply, hzero, zero_add, ite_eq_left hge]
    simp [List.getElem?_eq_getElem hsub]
  ext x
  simp only [memSeen, memPrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases lt_or_ge i.val active with hlt | hge
    · exact Or.inl ⟨i, hlt, (hslot_lt i hlt).symm⟩
    · right
      rw [hslot_ge i hge hi]
      exact List.getElem_mem _
  · rintro (⟨i, hi, rfl⟩ | hxL)
    · exact ⟨i, by omega, hslot_lt i hi⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hxL
      let idx : Fin k := ⟨active + a, by omega⟩
      refine ⟨idx, by dsimp [idx]; omega, ?_⟩
      have hge : active ≤ idx.val := by dsimp [idx]; omega
      have hlt : idx.val < active + L.length := by dsimp [idx]; omega
      rw [hslot_ge idx hge hlt]
      simp [idx]
private lemma ghQuadForm_wp_wdReadoutWrite_of_support {Var : Type} [DecidableEq Var] (res : Var)
    {n m k active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ))
    (σ : Store Var) (φ : Fin (2 ^ (m * (n + 1))) → ℂ)
    (hsupp : ∀ o : Fin (2 ^ (m * (n + 1))),
      φ (parallelMarkPerm n m (S \ memSeen n k (memPrefix k active) μ) o) ≠ 0 →
        ∀ x ∈ groupHits (Nat.mul_one m) o, x ∈ S \ memSeen n k (memPrefix k active) μ) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    ghQuadForm
        ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign
            (groverParallelMarkingOracle m S)) Θ) σ).1.1
        (workMemState (P_R *ᵥ φ) (single μ 1)) =
      ∑ o : Fin (2 ^ (m * (n + 1))),
        (normSq (φ (parallelMarkPerm n m R o)) : ℂ) *
          (Ψ (R \ (groupHits (Nat.mul_one m) o).toFinset) : ℂ) := by
  intro R P_R
  let hbg1 : m * 1 = m := Nat.mul_one m
  unfold wdReadoutWrite
  dsimp only [compile]
  rw [wp_qSeq, ghQuadForm_unitaryEffect (unitaryEffect_phaseTag _)]
  unfold ghQuadForm
  rw [wp_setCountAndResetWork, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star,
    krausLowBlock_mulVec_memAddPerm]
  change ghQuadForm _
    ((P_R *ᵥ φ) o • single (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg1 o) μ)) 1) = _
  rw [ghQuadForm_smul_vec, ghQuadForm_single]
  dsimp only [P_R]
  rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom]
  by_cases hnz : φ (parallelMarkPerm n m R o) = 0
  · simp [hnz]
  · obtain ⟨hlen, hval'⟩ :=
      memPrefixValid_writeMemBatch hcard hval (nodup_groupHits hbg1 o) (hsupp o hnz)
    have hcnt : (batchNextCount hm1 hkN hbg1 active o).val =
        active + (groupHits hbg1 o).length := by
      simp [batchNextCount, Nat.min_eq_right hlen]
    have hsdiff :
        S \ memSeen n k (memPrefix k (active + (groupHits hbg1 o).length))
            (writeMemBatch active (groupHits hbg1 o) μ) =
          R \ (groupHits hbg1 o).toFinset := by
      rw [memSeen_writeMemBatch_gh hval (groupHits hbg1 o) hlen]
      ext x
      simp only [R, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [hcnt, hΘ (active + (groupHits hbg1 o).length) _ _ hlen (by simp [Store.subst]) hval',
      hsdiff]
private lemma ghQuadForm_wp_topAncProbe {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (active : ℕ) (wSpec : ℕ → GaussPyth × PythPair)
    (noClickCirc : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    (S : Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)))
    (σ : Store Var) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ)
    {μ : Fin (2 ^ (k * n))} (hμ : μ.val < 2 ^ (k * n - 1)) :
    let W := m * (n + 1)
    let M := k * n
    let oracle := groverParallelMarkingOracle m S
    let probeCirc : OracleCirc Var (W + M) ((n + 1) * m) :=
      .seq (.step (phaseTag (gaussianHammingAllHitUnitary n m M hM wSpec)))
        (.seq (.measure res (topAncReg W M hM))
          (.qIf (fun τ ↦ τ res = 1)
            (wdClickCleanup res hm1 hkN hM active)
            noClickCirc))
    ghQuadForm ((wp (probeCirc.compile qAssign oracle) Θ) σ).1.1 (workMemState ψ (single μ 1)) =
      ghQuadForm ((wp (noClickCirc.compile qAssign oracle) Θ) (Store.subst σ res 0)).1.1
          (workMemState (ghDampVec n m wSpec ψ) (single μ 1)) +
        ghQuadForm ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign oracle) Θ)
            (Store.subst σ res 1)).1.1
          (workMemState (ghClickVec n m wSpec ψ) (single μ 1)) := by
  intro W M oracle probeCirc
  dsimp only [probeCirc, compile]
  rw [wp_qSeq, wp_qSeq, ghQuadForm_unitaryEffect (unitaryEffect_phaseTag _),
    show (gaussianHammingAllHitUnitary n m M hM wSpec).1 =
      gaussianHammingAllHitMat n m M hM wSpec from rfl,
    gaussianHammingAllHitMat_mulVec_workMemState hM wSpec ψ hμ, ghQuadForm_wp_measureRegister]
  refine (Fin.sum_univ_two _).trans ?_
  have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) res ≠ 1 := by
    simp [Store.subst]
  have hs1 : (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) res = 1 := by
    simp [Store.subst]
  let branchProg :=
    QProg.qIf (fun τ ↦ τ res = 1)
      ((wdClickCleanup res hm1 hkN hM active).compile qAssign oracle)
      (noClickCirc.compile qAssign oracle)
  have hwp0 :
      wp branchProg Θ (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) =
        wp (noClickCirc.compile qAssign oracle) Θ (Store.subst σ res 0) := by
    rw [wp_qIf]; dsimp only; rw [ite_eq_right hs0]; rfl
  have hwp1 :
      wp branchProg Θ (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) =
        wp ((wdClickCleanup res hm1 hkN hM active).compile qAssign oracle) Θ
          (Store.subst σ res 1) := by
    rw [wp_qIf]; dsimp only; rw [ite_eq_left hs1]; rfl
  congr 1
  · change ghQuadForm
        ((wp branchProg Θ (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val))).1.1) _ = _
    rw [hwp0, topAncReg_projector_zero_mulVec hM _ _ hμ]
  · change ghQuadForm
        ((wp branchProg Θ (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val))).1.1) _ = _
    rw [hwp1, topAncReg_projector_one_mulVec hM _ _ hμ]
    unfold wdClickCleanup
    dsimp only [compile]
    rw [wp_qSeq, ghQuadForm_unitaryEffect (unitaryEffect_phaseTag _),
      topAncReg_flip_mulVec_one hM _ hμ]
private lemma deflatedRead_mulVec_workMemState_gh {n m k active : ℕ}
    {S : Finset (Fin (2 ^ n))} {μ : Fin (2 ^ (k * n))}
    (hsub : memSeen n k (memPrefix k active) μ ⊆ S) :
    let W := m * (n + 1)
    let M := k * n
    let R := S \ memSeen n k (memPrefix k active) μ
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    (∀ ξ : Fin (2 ^ W) → ℂ,
      (unm * orac) *ᵥ workMemState ξ (single μ 1) = workMemState (P_R *ᵥ ξ) (single μ 1)) ∧
    (∀ ξ : Fin (2 ^ W) → ℂ, P_R *ᵥ (P_R *ᵥ ξ) = ξ) := by
  intro W M R orac unm P_R
  constructor
  · intro ξ
    rw [← mulVec_mulVec, unmark_mul_parallelOracle_workMemState (memPrefix k active) ξ μ hsub,
      show S \ memSeen n k (memPrefix k active) μ = R from rfl,
      fullReg_embedUnitary_eq_permutationUnitary R]
  · intro ξ
    funext w
    rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom,
      permUnitary_parallelMarkPerm_mulVec_apply_zoom, parallelMarkPerm_involutive]
private lemma unitaryEffect_wdPrepAndNoClick_gh {Var : Type} [DecidableEq Var]
    {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n)))
    (S : Finset (Fin (2 ^ n))) (active : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let prepOp := (lowBlock W M).embedMatrix (wdPrepUnitary hp hm perm).1
    (∀ kInit : ℕ,
      UnitaryEffect
        ((wdPrepAndLoop (Var := Var) (k := k) hp hm perm active kInit).compile qAssign
          (groverParallelMarkingOracle m S))
        ((unm * orac) * ((diffOp * phaseOp) ^ kInit) * prepOp)) ∧
    (∀ kNext : ℕ,
      UnitaryEffect
        ((wdNoClickStep (Var := Var) (k := k) hp perm active kNext).compile qAssign
          (groverParallelMarkingOracle m S))
        ((unm * orac) * ((diffOp * phaseOp) ^ kNext) * (unm * orac))) := by
  intro W M fc orac unm phaseOp diffOp prepOp
  have hwwhole : workMemReg n m k (W + M) le_rfl = QRegister.whole (W + M) := by
    ext i; exact Nat.zero_add i.val
  have hwlow : workReg n m (W + M) (by omega) = lowBlock W M := rfl
  have hread : UnitaryEffect
      ((deflatedOracle (Var := Var) (m := m) (k := k) le_rfl (memPrefix k active)).compile qAssign
        (groverParallelMarkingOracle m S))
      (unm * orac) := by
    unfold deflatedOracle; dsimp only [compile]
    rw [hwwhole, QRegister.whole_embedUnitary]
    have h1 := unitaryEffect_qAssign (Var := Var)
      ((workFullReg n m (W + M) (by omega)).embedUnitary (groverParallelMarkingOracle m S))
    rw [workFullReg_embedUnitary_eq] at h1
    exact unitaryEffect_seq h1 (unitaryEffect_phaseTag _)
  have hphase : UnitaryEffect
      ((deflatedPhaseStep (Var := Var) (m := m) (k := k) le_rfl (memPrefix k active)).compile
        qAssign (groverParallelMarkingOracle m S))
      phaseOp := by
    unfold deflatedPhaseStep; dsimp only [compile]; rw [hwlow]
    have hfc := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (flagConj n m))
    rw [embedUnitary_val] at hfc
    simpa only [phaseOp, Matrix.mul_assoc] using unitaryEffect_seq hfc (unitaryEffect_seq hread hfc)
  have hloop (t : ℕ) : UnitaryEffect
      ((wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp perm active t).compile qAssign
        (groverParallelMarkingOracle m S))
      ((diffOp * phaseOp) ^ t) := by
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using unitaryEffect_skip (Var := Var) (d := 2 ^ (W + M))
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold wdDeflatedGroverStep; dsimp only [compile]
      have hdiff := unitaryEffect_phaseTag (Var := Var)
        ((lowBlock W M).embedUnitary (wdDiffuserUnitary (m := m) hp perm))
      rw [embedUnitary_val] at hdiff
      rw [pow_succ]
      exact unitaryEffect_seq (unitaryEffect_seq hphase hdiff) ih
  constructor
  · intro kInit
    unfold wdPrepAndLoop; dsimp only [compile]
    have hprep := unitaryEffect_phaseTag (Var := Var)
      ((lowBlock W M).embedUnitary (wdPrepUnitary hp hm perm))
    rw [embedUnitary_val] at hprep
    simpa only [Matrix.mul_assoc] using
      unitaryEffect_seq hprep (unitaryEffect_seq (hloop kInit) hread)
  · intro kNext
    unfold wdNoClickStep; dsimp only [compile]
    simpa only [Matrix.mul_assoc] using
      unitaryEffect_seq hread (unitaryEffect_seq (hloop kNext) hread)
private lemma costBounds_ghPieces {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n)))
    (S : Finset (Fin (2 ^ n))) (active : ℕ) :
    let model := CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)
    (∀ kInit : ℕ,
      CostBound (Var := Var) model
        ((wdPrepAndLoop (k := k) hp hm perm active kInit).compile qAssign
          (groverParallelMarkingOracle m S)) (kInit + 1)) ∧
    (∀ kNext : ℕ,
      CostBound (Var := Var) model
        ((wdNoClickStep (k := k) hp perm active kNext).compile qAssign
          (groverParallelMarkingOracle m S)) (kNext + 2)) ∧
    CostBound (Var := Var) model
      ((wdReadoutWrite (k := k) res hm1 hkN active).compile qAssign
        (groverParallelMarkingOracle m S)) 0 ∧
    CostBound (Var := Var) model
      ((wdClickCleanup (k := k) res hm1 hkN hM active).compile qAssign
        (groverParallelMarkingOracle m S)) 0 := by
  intro model
  let W := m * (n + 1)
  let M := k * n
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hread := costBound_deflatedOracle (Var := Var) (m := m) (k := k)
    le_rfl (memPrefix k active) S
  have hloop (t : ℕ) :
      CostBound (Var := Var) model
        ((wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp perm active t).compile qAssign
          (groverParallelMarkingOracle m S)) t := by
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using CostBound.skip_zero (Var := Var) model
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold wdDeflatedGroverStep; dsimp only [compile]
      have hstep : CostBound (Var := Var) model
          ((deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k active)).compile qAssign
              (groverParallelMarkingOracle m S) ;;
            .qAssign (phaseTag ((lowBlock W M).embedUnitary
              (wdDiffuserUnitary (m := m) hp perm)))) 1 := by
        simpa using (costBound_deflatedPhaseStep le_rfl (memPrefix k active) S).seq
          (costBound_qAssign_phaseTag (Var := Var) hor _)
      exact (hstep.seq ih).mono (by rw [← NNReal.coe_le_coe]; push_cast; linarith)
  have hrw : CostBound (Var := Var) model
      ((wdReadoutWrite (Var := Var) (k := k) res hm1 hkN active).compile qAssign
        (groverParallelMarkingOracle m S)) 0 := by
    unfold wdReadoutWrite; dsimp only [compile]
    exact ((costBound_qAssign_phaseTag (Var := Var) hor _).seq
      (costBound_setCountAndResetWork (Var := Var) (M := M) res
        (batchNextCount hm1 hkN (Nat.mul_one m) active) hor)).mono (by simp)
  refine ⟨fun kInit ↦ ?_, fun kNext ↦ ?_, hrw, ?_⟩
  · unfold wdPrepAndLoop; dsimp only [compile]
    exact ((costBound_qAssign_phaseTag (Var := Var) hor _).seq
      ((hloop kInit).seq hread)).mono (by simp)
  · unfold wdNoClickStep; dsimp only [compile]
    exact (hread.seq ((hloop kNext).seq hread)).mono (le_of_eq (by ring))
  · unfold wdClickCleanup; dsimp only [compile]
    exact ((costBound_qAssign_phaseTag (Var := Var) hor _).seq hrw).mono (by simp)
/-- Polymorphic Gaussian-Hamming probe chain parameterized by `wSpecOf` and `stepsOf`. -/
noncomputable def ghProbeChain {P : Type*} {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ)
    (wSpecOf : P → ℕ → GaussPyth × PythPair) (stepsOf : P → ℕ) :
    List P → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | [] => wdReadoutWrite res hm1 hkN active
  | pr :: rest =>
      let W := m * (n + 1)
      let M := k * n
      .seq (.step (phaseTag (gaussianHammingAllHitUnitary n m M hM (wSpecOf pr))))
        (.seq (.measure res (topAncReg W M hM))
          (.qIf (fun τ ↦ τ res = 1)
            (wdClickCleanup res hm1 hkN hM active)
            (.seq (wdNoClickStep hp perm active (stepsOf pr))
              (ghProbeChain res hm1 hkN hM hp perm active wSpecOf stepsOf rest))))
/-- One Gaussian-Hamming deflated subcube round (`kInit` initial steps + `ghProbeChain`). -/
noncomputable def ghDeflatedRound {P : Type*} {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n)))
    (active kInit : ℕ) (wSpecOf : P → ℕ → GaussPyth × PythPair) (stepsOf : P → ℕ)
    (probes : List P) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (wdPrepAndLoop hp hm perm active kInit)
    (ghProbeChain res hm1 hkN hM hp perm active wSpecOf stepsOf probes)
private lemma ghDampAmp2_eq_wSpec (pr : GHZoomProbe) (u : ℕ → ℂ) {b : ℕ} (hb : b ≤ 2) :
    ((ghProbeWSpec2 pr b).2.cVal : ℂ) * (ghProbeWSpec2 pr b).1.val * u b =
      ghDampAmp2 pr.1 pr.2.1 pr.2.2.1 u b := by
  match b, hb with
  | 0, _ => simp [ghProbeWSpec2, ghDampAmp2, gaussOne, pythOne, GaussPyth.val, PythPair.cVal]
  | 1, _ => simp [ghProbeWSpec2, ghDampAmp2, pythOne, PythPair.cVal]
  | 2, _ => simp [ghProbeWSpec2, ghDampAmp2]
  | _ + 3, hb => omega
private lemma ghQuadForm_wp_ghProbeChain_inj2 {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) (hμ : μ.val < 2 ^ (k * n - 1))
    (hR2 : (S \ memSeen n k (memPrefix k active) μ).card = 2)
    (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x))
      ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))))
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ))
    (probes : List GHZoomProbe) (u : ℕ → ℂ) (σ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    ghQuadForm
        ((wp ((ghProbeChain res hm1 hkN hM hp perm active
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes).compile qAssign
            (groverParallelMarkingOracle m S)) Θ) σ).1.1
        (workMemState (P_R *ᵥ wdAmpStateC hp hm perm R u) (single μ 1)) =
      ((ghChainClickProb2 θ₁ probes u * Ψ ∅ +
          ∑ B ∈ R.powerset,
            normSq (ghChainFinalAmp2 θ₁ probes u B.card) * Ψ (R \ B) : ℝ) : ℂ) := by
  intro R P_R θ₁
  let hbg1 : m * 1 = m := Nat.mul_one m
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hsub : memSeen n k (memPrefix k active) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
  have hsupp_amp (u' : ℕ → ℂ) (o : Fin (2 ^ (m * (n + 1))))
      (hnz : wdAmpStateC hp hm perm R u' (parallelMarkPerm n m R o) ≠ 0) :
      ∀ x ∈ groupHits hbg1 o, x ∈ R := by
    unfold wdAmpStateC at hnz
    obtain ⟨A, hA, hAnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    have hAb : ghBasisVec hp hm perm R A (parallelMarkPerm n m R o) ≠ 0 :=
      fun h0 ↦ hAnz (by rw [h0, mul_zero])
    exact (ghBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA) o hAb).2.2.1
  induction probes generalizing u σ with
  | nil =>
    dsimp only [ghProbeChain, ghChainClickProb2, ghChainFinalAmp2]
    rw [ghQuadForm_wp_wdReadoutWrite_of_support res hm1 hkN hcard hval Θ Ψ hΘ σ _
        (hsupp_amp u), sum_normSq_wdAmpStateC_readout hp hm hsub2 perm hInj u (fun X ↦ (Ψ X : ℂ))]
    push_cast; ring
  | cons pr rest ih =>
    dsimp only [ghProbeChain]
    rw [ghQuadForm_wp_topAncProbe res hm1 hkN hM active (ghProbeWSpec2 pr) _ S Θ σ _ hμ]
    have hzero_sub : ∀ b < R.card, (ghProbeWSpec2 pr b).2.sVal = 0 := by
      intro b hb
      rw [hR2] at hb
      match b, hb with
      | 0, _ => simp [ghProbeWSpec2, pythOne, PythPair.sVal]
      | 1, _ => simp [ghProbeWSpec2, pythOne, PythPair.sVal]
      | _ + 2, hb => omega
    rcases ghDamp_and_click_marked_wdAmpStateC hp hm perm hInj (ghProbeWSpec2 pr) hzero_sub u with
      ⟨hdamp, hclick⟩
    have hdamp_eq :
        wdAmpStateC hp hm perm R
          (fun b ↦ ((ghProbeWSpec2 pr b).2.cVal : ℂ) * (ghProbeWSpec2 pr b).1.val * u b) =
        wdAmpStateC hp hm perm R (ghDampAmp2 pr.1 pr.2.1 pr.2.2.1 u) :=
      wdAmpStateC_congr_le hp hm perm R fun b hb ↦
        ghDampAmp2_eq_wSpec pr u (hb.trans_eq hR2)
    rw [hdamp, hdamp_eq, hclick]
    let J := R.image pref
    have hsmul_ws (c : ℂ) (v : Fin (2 ^ (m * (n + 1))) → ℂ) :
        workMemState (c • v) (single μ 1) = c • workMemState v (single μ 1) := by
      funext idx; simp [workMemState, mul_assoc]
    have hclick_val :
        ghQuadForm
            ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign
                (groverParallelMarkingOracle m S)) Θ) (Store.subst σ res 1)).1.1
            (workMemState
              ((((ghProbeWSpec2 pr R.card).2.sVal : ℂ) *
                (ghProbeWSpec2 pr R.card).1.val * u R.card) •
                (P_R *ᵥ ghBasisVec hp hm perm R J))
              (single μ 1)) =
          (((pr.2.2.1.sVal : ℝ) ^ 2 * normSq (u 2) * Ψ ∅ : ℝ) : ℂ) := by
      rw [hsmul_ws, ghQuadForm_smul_vec,
        ghQuadForm_wp_wdReadoutWrite_of_support res hm1 hkN hcard hval Θ Ψ hΘ _ _
          (fun o hnz ↦ (ghBasisVec_support_props hp hm perm R Finset.Subset.rfl o hnz).2.2.1)]
      have h_click_o (o : Fin (2 ^ (m * (n + 1)))) :
          (normSq (ghBasisVec hp hm perm R J (parallelMarkPerm n m R o)) : ℂ) *
              (Ψ (R \ (groupHits hbg1 o).toFinset) : ℂ) =
            (normSq (ghBasisVec hp hm perm R J (parallelMarkPerm n m R o)) : ℂ) * (Ψ ∅ : ℂ) := by
        by_cases hnz : ghBasisVec hp hm perm R J (parallelMarkPerm n m R o) = 0
        · simp [hnz]
        · rw [ghBasisVec_groupHits_toFinset_eq hp hm perm hInj Finset.Subset.rfl o hnz,
            Finset.sdiff_self]
      rw [Finset.sum_congr rfl fun o _ ↦ h_click_o o, ← Finset.sum_mul, ← Complex.ofReal_sum,
        Equiv.sum_comp (parallelMarkPerm n m R)
          (fun w ↦ normSq (ghBasisVec hp hm perm R J w)),
        sum_normSq_ghBasisVec hp hm hsub2 perm hInj J, hR2]
      dsimp only [ghProbeWSpec2]
      rw [map_mul, map_mul, Complex.normSq_ofReal, GaussPyth.normSq_val]
      push_cast; ring
    rcases deflatedRead_mulVec_workMemState_gh (m := m) hsub with ⟨hread_mul, hPR_inv⟩
    have hue :=
      (unitaryEffect_wdPrepAndNoClick_gh (Var := Var) (k := k) hp hm perm S active).2 pr.2.2.2
    have hnoclick_vec :
        let W := m * (n + 1)
        let M := k * n
        let fc := (lowBlock W M).embedMatrix (flagConj n m).1
        let orac := (lowBlock W M).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
        let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
        let phaseOp := fc * unm * orac * fc
        let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
        ((unm * orac) * ((diffOp * phaseOp) ^ pr.2.2.2) * (unm * orac)) *ᵥ
            workMemState (P_R *ᵥ wdAmpStateC hp hm perm R (ghDampAmp2 pr.1 pr.2.1 pr.2.2.1 u))
              (single μ 1) =
          workMemState
            (P_R *ᵥ wdAmpStateC hp hm perm R (ghProbeNextAmp2 θ₁ pr u))
            (single μ 1) := by
      intro W M fc orac unm phaseOp diffOp
      dsimp only [W, M, fc, orac, unm, phaseOp, diffOp]
      rw [← mulVec_mulVec, ← mulVec_mulVec, hread_mul, hPR_inv,
        ghGrover_iter_wdAmpStateC hp hm hsub2 perm hsub hInj _ pr.2.2.2, hread_mul]
      have hrc2 : (S \ memSeen n k (memPrefix k active) μ).card = 2 := hR2
      rw [hrc2]
      rfl
    dsimp only [compile]
    rw [wp_qSeq, ghQuadForm_unitaryEffect hue, hnoclick_vec, ih, hclick_val]
    dsimp only [ghChainClickProb2, ghChainFinalAmp2]
    push_cast; ring
private lemma ghQuadForm_wp_ghProbeChain_coll2 {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) (hμ : μ.val < 2 ^ (k * n - 1))
    (hR2 : (S \ memSeen n k (memPrefix k active) μ).card = 2)
    (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref hp hm (perm x))
      ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))))
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ))
    (probes : List GHZoomProbe) (z : ℂ × ℂ) (σ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    let θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
    let zf := ghChainFinalColl2 θ₂ probes z
    ghQuadForm
        ((wp ((ghProbeChain res hm1 hkN hM hp perm active
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes).compile qAssign
            (groverParallelMarkingOracle m S)) Θ) σ).1.1
        (workMemState (P_R *ᵥ ghCollState hp hm perm R z) (single μ 1)) =
      ((normSq zf.1 * Ψ R +
          normSq zf.2 * ∑ x ∈ R, (1 / 2 : ℝ) * Ψ (R \ {x}) : ℝ) : ℂ) := by
  intro R P_R θ₂ zf
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hsub : memSeen n k (memPrefix k active) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
  have hsupp_coll (z' : ℂ × ℂ) (o : Fin (2 ^ (m * (n + 1))))
      (hnz : ghCollState hp hm perm R z' (parallelMarkPerm n m R o) ≠ 0) :
      ∀ x ∈ groupHits hbg1 o, x ∈ R := by
    let J := R.image fun x ↦ subcubePref hp hm (perm x)
    unfold ghCollState at hnz
    dsimp only at hnz
    by_cases h0 : ghBasisVec hp hm perm R ∅ (parallelMarkPerm n m R o) ≠ 0
    · exact (ghBasisVec_support_props hp hm perm R (Finset.empty_subset J) o h0).2.2.1
    · rw [not_not] at h0
      rw [h0, mul_zero, zero_add] at hnz
      have h1 : ghBasisVec hp hm perm R J (parallelMarkPerm n m R o) ≠ 0 :=
        fun h1 ↦ hnz (by rw [h1, mul_zero])
      exact (ghBasisVec_support_props hp hm perm R Finset.Subset.rfl o h1).2.2.1
  induction probes generalizing z σ with
  | nil =>
    dsimp only [ghProbeChain, zf, ghChainFinalColl2]
    rw [ghQuadForm_wp_wdReadoutWrite_of_support res hm1 hkN hcard hval Θ Ψ hΘ σ _
        (hsupp_coll z),
      sum_normSq_ghCollState_readout hp hm hsub3 perm hR2 hNotInj z (fun X ↦ (Ψ X : ℂ))]
    push_cast; ring
  | cons pr rest ih =>
    dsimp only [ghProbeChain]
    rw [ghQuadForm_wp_topAncProbe res hm1 hkN hM active (ghProbeWSpec2 pr) _ S Θ σ _ hμ]
    rcases ghDamp_and_click_marked_ghCollState hp hm perm hR2 hNotInj pr z with ⟨hdamp, hclick⟩
    have hws0 : workMemState (0 : Fin (2 ^ (m * (n + 1))) → ℂ) (single μ 1) = 0 := by
      funext idx; simp [workMemState]
    rw [hdamp, hclick, hws0, ghQuadForm_zero_vec, add_zero]
    rcases deflatedRead_mulVec_workMemState_gh (m := m) hsub with ⟨hread_mul, hPR_inv⟩
    have hue :=
      (unitaryEffect_wdPrepAndNoClick_gh (Var := Var) (k := k) hp hm perm S active).2 pr.2.2.2
    have hnoclick_vec :
        let W := m * (n + 1)
        let M := k * n
        let fc := (lowBlock W M).embedMatrix (flagConj n m).1
        let orac := (lowBlock W M).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
        let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
        let phaseOp := fc * unm * orac * fc
        let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
        ((unm * orac) * ((diffOp * phaseOp) ^ pr.2.2.2) * (unm * orac)) *ᵥ
            workMemState (P_R *ᵥ ghCollState hp hm perm R (z.1, pr.1.val * z.2))
              (single μ 1) =
          workMemState (P_R *ᵥ ghCollState hp hm perm R (ghProbeNextColl2 θ₂ pr z))
            (single μ 1) := by
      intro W M fc orac unm phaseOp diffOp
      dsimp only [W, M, fc, orac, unm, phaseOp, diffOp]
      rw [← mulVec_mulVec, ← mulVec_mulVec, hread_mul, hPR_inv,
        ghGrover_iter_ghCollState hp hm hsub3 perm hsub hR2 hNotInj _ pr.2.2.2, hread_mul]
      rfl
    dsimp only [compile]
    rw [wp_qSeq, ghQuadForm_unitaryEffect hue, hnoclick_vec]
    exact ih (ghProbeNextColl2 θ₂ pr z) (Store.subst σ res 0)
private lemma wp_ghDeflatedRound_of_finset {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k active : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) (kInit : ℕ) (probes : List GHZoomProbe)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (hact : active < k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
    (hR2 : (S \ memSeen n k (memPrefix k active) μ).card = 2)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ))
    (τ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let pref := fun x ↦ subcubePref hp hm (perm x)
    ((wp ((ghDeflatedRound res hm1 hkN hM hp hm perm active kInit
        ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes).compile qAssign
        (groverParallelMarkingOracle m S)) Θ) τ).1.1
        (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      if Set.InjOn pref (R : Set (Fin (2 ^ n))) then
        let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
        let u₀ := ghInitAmp2 θ₁ kInit
        let uf := ghChainFinalAmp2 θ₁ probes u₀
        ((ghChainClickProb2 θ₁ probes u₀ * Ψ ∅ +
            ∑ B ∈ R.powerset, normSq (uf B.card) * Ψ (R \ B) : ℝ) : ℂ)
      else
        let θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
        let z₀ := ghInitColl2 θ₂ kInit
        let zf := ghChainFinalColl2 θ₂ probes z₀
        ((normSq zf.1 * Ψ R +
            normSq zf.2 * ∑ x ∈ R, (1 / 2 : ℝ) * Ψ (R \ {x}) : ℝ) : ℂ) := by
  dsimp only
  set R := S \ memSeen n k (memPrefix k active) μ
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hseen := card_memSeen_of_memPrefixValid hval
  have hμ : μ.val < 2 ^ (k * n - 1) := memPrefixValid_lt_half hn hk1 hval hact
  have hsub2 : 2 ≤ 2 ^ (n - p) := by omega
  refine (ghQuadForm_single _ (workMemIdx n m k 0 μ)).symm.trans ?_
  have hue := (unitaryEffect_wdPrepAndNoClick_gh (Var := Var) (k := k) hp hm perm S active).1 kInit
  unfold ghDeflatedRound
  dsimp only [compile]
  rw [wp_qSeq, ghQuadForm_unitaryEffect hue]
  rcases deflatedRead_mulVec_workMemState_gh (m := m) hseen.2 with ⟨hread_mul, _⟩
  by_cases hInj : Set.InjOn pref (R : Set (Fin (2 ^ n)))
  · rw [ite_eq_left hInj, ← mulVec_mulVec, ← mulVec_mulVec,
      ghPrep_grover_eq_wdAmpStateC hp hm hsub2 perm hseen.2 hInj kInit, hread_mul]
    have hinit_eq :
        dickeStep (S \ memSeen n k (memPrefix k active) μ).card
          (Real.cos ((2 * (kInit : ℝ) + 1) * Real.arcsin (1 / √(2 ^ (n - p) : ℝ))) : ℂ)
          (Real.sin ((2 * (kInit : ℝ) + 1) * Real.arcsin (1 / √(2 ^ (n - p) : ℝ))) : ℂ)
          (fun b ↦ if b = 0 then 1 else 0) =
        ghInitAmp2 (Real.arcsin (1 / √(2 ^ (n - p) : ℝ))) kInit := by
      rw [hR2]; rfl
    rw [hinit_eq]
    exact ghQuadForm_wp_ghProbeChain_inj2 res hm1 hkN hM hp hm hsub2 perm hcard hval hμ hR2 hInj
      Θ Ψ hΘ probes _ τ
  · rw [ite_eq_right hInj, ← mulVec_mulVec, ← mulVec_mulVec,
      ghPrep_grover_eq_ghCollState hp hm hsub3 perm hseen.2 hR2 hInj kInit, hread_mul]
    exact ghQuadForm_wp_ghProbeChain_coll2 res hm1 hkN hM hp hm hsub3 perm hcard hval hμ hR2 hInj
      Θ Ψ hΘ probes _ τ
private def ghProbesMaxQ (probes : List GHZoomProbe) : ℕ :=
  (probes.map fun pr ↦ pr.2.2.2 + 2).sum
private lemma scaledCostRel_ghProbeChain {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n)))
    (probes : List GHZoomProbe) {B : ℝ} (hB : 0 < B)
    (hcB : (ghProbesMaxQ probes : ℝ) ≤ B) :
    let R := fun μ ↦ S \ memSeen n k (memPrefix k active) μ
    let P_R := fun μ ↦ (permutationUnitary (parallelMarkPerm n m (R μ))).1
    let pref := fun x ↦ subcubePref hp hm (perm x)
    let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)),
      ScaledCostRel (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B
        ((ghProbeChain res hm1 hkN hM hp perm active
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes).compile qAssign
          (groverParallelMarkingOracle m S))
        θ (ghProbesMaxQ probes) ∧
      (∀ (μ : Fin (2 ^ (k * n))) (σ : Store Var),
        S.card = k → active < k → MemPrefixValid S active μ → (R μ).card = 2 →
        Set.InjOn pref ((R μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))) →
        ∀ u : ℕ → ℂ,
          ghQuadForm (θ σ).1.1
              (workMemState (P_R μ *ᵥ wdAmpStateC hp hm perm (R μ) u) (single μ 1)) =
            ((ghChainExtraQueries2 θ₁ probes u / B : ℝ) : ℂ)) ∧
      (∀ (μ : Fin (2 ^ (k * n))) (σ : Store Var),
        S.card = k → active < k → MemPrefixValid S active μ → (R μ).card = 2 →
        ¬ Set.InjOn pref ((R μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))) →
        ∀ z : ℂ × ℂ, normSq z.1 + normSq z.2 = 1 →
          ghQuadForm (θ σ).1.1
              (workMemState (P_R μ *ᵥ ghCollState hp hm perm (R μ) z) (single μ 1)) =
            (((ghProbesMaxQ probes : ℝ) / B : ℝ) : ℂ)) := by
  intro R P_R pref θ₁
  let W := m * (n + 1)
  let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hsub2 : 2 ≤ 2 ^ (n - p) := by omega
  rcases costBounds_ghPieces (Var := Var) res hm1 hkN hM hp hm perm S active with
    ⟨_, hcb_noclick, hcb_rw, hcb_click⟩
  induction probes with
  | nil =>
    refine ⟨⊥, ghScaledCostRel_mono_c hB (ghScaledCostRel_of_zero hB hcb_rw)
      (by simp [ghProbesMaxQ]) hcB, ?_, ?_⟩
    · intro μ σ _ _ _ _ _ u
      dsimp only [ghChainExtraQueries2, ghProbesMaxQ]
      change ghQuadForm 0 _ = _
      rw [ghQuadForm_zero_mat]; simp
    · intro μ σ _ _ _ _ _ z _
      dsimp only [ghProbesMaxQ, List.map_nil, List.sum_nil]
      change ghQuadForm 0 _ = _
      rw [ghQuadForm_zero_mat]; simp
  | cons pr rest ih =>
    have hfin2 (f : Fin (2 ^ 1) → ℂ) : (∑ o : Fin (2 ^ 1), f o) = f 0 + f 1 :=
      Fin.sum_univ_two f
    have hc_eq : (ghProbesMaxQ (pr :: rest) : ℝ) =
        (pr.2.2.2 : ℝ) + 2 + (ghProbesMaxQ rest : ℝ) := by
      simp [ghProbesMaxQ]
    have hc_rest_le : (ghProbesMaxQ rest : ℝ) ≤ B := by
      have : (0 : ℝ) ≤ (pr.2.2.2 : ℝ) + 2 := by positivity
      linarith
    rcases ih hc_rest_le with ⟨θ_rest, hrel_rest, hinj_rest, hnot_rest⟩
    have hcb_step : CostBound (Var := Var) model
        (.qAssign (phaseTag (gaussianHammingAllHitUnitary n m M hM (ghProbeWSpec2 pr)))) 0 :=
      costBound_qAssign_phaseTag (Var := Var) hor _
    have hcb_meas : CostBound (Var := Var) model
        (measureRegister res (topAncReg W M hM)) 0 := by
      simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
        CostBound.qMeasure (Var := Var) model res
          ((topAncReg W M hM).computationalBasisMeasurement :
            Measurement (2 ^ (W + M)) (2 ^ 1))
    have hkNext_le : (((pr.2.2.2 + 2 : ℕ) : ℝ≥0) : ℝ) ≤ B := by
      have : (0 : ℝ) ≤ (ghProbesMaxQ rest : ℝ) := Nat.cast_nonneg _
      push_cast; linarith
    have hrel_nc0 := ghScaledCostRel_of_costBound hB (k_cost := (pr.2.2.2 + 2 : ℕ))
      (by simpa [Nat.cast_add] using hcb_noclick pr.2.2.2) hkNext_le
    have hsum_le : (((pr.2.2.2 + 2 : ℕ) : ℝ≥0) : ℝ) + (ghProbesMaxQ rest : ℝ) ≤ B := by
      push_cast; linarith
    have hrel_false := ghScaledCostRel_seq hB hrel_nc0 hrel_rest hsum_le
    have hrel_true := ghScaledCostRel_of_zero hB hcb_click
    have hmax_eq :
        max (0 : ℝ) ((((pr.2.2.2 + 2 : ℕ) : ℝ≥0) : ℝ) + (ghProbesMaxQ rest : ℝ)) =
          (ghProbesMaxQ (pr :: rest) : ℝ) := by
      rw [max_eq_right (by positivity)]
      push_cast; linarith
    have hrel_if := ghScaledCostRel_mono_c hB
      (ghScaledCostRel_qIf hB (fun τ ↦ τ res = 1) hrel_true hrel_false)
      (le_of_eq hmax_eq) hcB
    have hrel_tot := ghScaledCostRel_seq_zero_left hB hcb_step
      (ghScaledCostRel_seq_zero_left hB hcb_meas hrel_if)
    refine ⟨_, hrel_tot, ?_, ?_⟩
    · intro μ σ hcard hact hval hR2 hInj u
      have hn : 1 ≤ n := by
        by_contra hn0; push Not at hn0
        have hn_eq : n = 0 := by omega
        have hp_eq : p = 0 := by omega
        subst hn_eq hp_eq; omega
      have hk1 : 1 ≤ k := by omega
      have hμ : μ.val < 2 ^ (k * n - 1) := memPrefixValid_lt_half hn hk1 hval hact
      have hseen := card_memSeen_of_memPrefixValid hval
      have hstep_vec :
          (gaussianHammingAllHitUnitary n m M hM (ghProbeWSpec2 pr)).1 *ᵥ
              workMemState (P_R μ *ᵥ wdAmpStateC hp hm perm (R μ) u) (single μ 1) =
            workMemState (ghDampVec n m (ghProbeWSpec2 pr)
                (P_R μ *ᵥ wdAmpStateC hp hm perm (R μ) u)) (single μ 1) +
              workMemState (ghClickVec n m (ghProbeWSpec2 pr)
                (P_R μ *ᵥ wdAmpStateC hp hm perm (R μ) u))
                (single (memWithTopOne hM μ hμ) 1) :=
        gaussianHammingAllHitMat_mulVec_workMemState hM (ghProbeWSpec2 pr) _ hμ
      rw [ghQuadForm_unitaryEffect (unitaryEffect_phaseTag _), hstep_vec,
        ghQuadForm_wp_measureRegister, hfin2]
      have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) res ≠ 1 := by
        simp [Store.subst]
      have hs1 : (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) res = 1 := by
        simp [Store.subst]
      rw [topAncReg_projector_zero_mulVec hM _ _ hμ, topAncReg_projector_one_mulVec hM _ _ hμ,
        ite_eq_right hs0, ite_eq_left hs1, ghQuadForm_bot_apply, add_zero]
      have hzero_sub : ∀ b < (R μ).card, (ghProbeWSpec2 pr b).2.sVal = 0 := by
        intro b hb
        rw [hR2] at hb
        match b, hb with
        | 0, _ => simp [ghProbeWSpec2, pythOne, PythPair.sVal]
        | 1, _ => simp [ghProbeWSpec2, pythOne, PythPair.sVal]
        | _ + 2, hb => omega
      rcases ghDamp_and_click_marked_wdAmpStateC hp hm perm hInj (ghProbeWSpec2 pr) hzero_sub u
        with ⟨hdamp, _⟩
      have hdamp_eq :
          wdAmpStateC hp hm perm (R μ)
            (fun b ↦ ((ghProbeWSpec2 pr b).2.cVal : ℂ) * (ghProbeWSpec2 pr b).1.val * u b) =
          wdAmpStateC hp hm perm (R μ) (ghDampAmp2 pr.1 pr.2.1 pr.2.2.1 u) :=
        wdAmpStateC_congr_le hp hm perm (R μ) fun b hb ↦
          ghDampAmp2_eq_wSpec pr u (hb.trans_eq hR2)
      rw [hdamp, hdamp_eq, gh_cqAssertion_add_mat, ghQuadForm_add_mat]
      have hdiv0 : 0 ≤ (((pr.2.2.2 + 2 : ℕ) : ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le
      have hdiv1 : (((pr.2.2.2 + 2 : ℕ) : ℝ≥0) : ℝ) / B ≤ 1 := (div_le_one hB).mpr hkNext_le
      rw [ghQuadForm_constAssertion_workMemState hdiv0 hdiv1]
      set uD := ghDampAmp2 pr.1 pr.2.1 pr.2.2.1 u
      have hnorm_damp :
          (∑ o : Fin (2 ^ W), (normSq ((P_R μ *ᵥ wdAmpStateC hp hm perm (R μ) uD) o) : ℂ)) =
            ((normSq (uD 0) + 2 * normSq (uD 1) + normSq (uD 2) : ℝ) : ℂ) := by
        have h1 := sum_normSq_wdAmpStateC_mul_card hp hm hsub2 perm hInj uD (fun _ ↦ 1)
        simp only [mul_one] at h1
        dsimp only [P_R]
        simp_rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom]
        rw [h1, hR2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
        norm_num
      rcases deflatedRead_mulVec_workMemState_gh (m := m) hseen.2 with ⟨hread_mul, hPR_inv⟩
      have hue :=
        (unitaryEffect_wdPrepAndNoClick_gh (Var := Var) (k := k) hp hm perm S active).2 pr.2.2.2
      have hnext_eq :
          dickeStep (R μ).card (Real.cos (2 * (pr.2.2.2 : ℝ) * θ₁) : ℂ)
            (Real.sin (2 * (pr.2.2.2 : ℝ) * θ₁) : ℂ) uD =
          ghProbeNextAmp2 θ₁ pr u := by
        rw [hR2]; rfl
      rw [hnorm_damp, ghQuadForm_unitaryEffect hue, ← mulVec_mulVec,
        ← mulVec_mulVec, hread_mul, hPR_inv,
        ghGrover_iter_wdAmpStateC hp hm hsub2 perm hseen.2 hInj uD pr.2.2.2,
        show S \ memSeen n k (memPrefix k active) μ = R μ from rfl, hnext_eq, hread_mul,
        hinj_rest μ _ hcard hact hval hR2 hInj]
      dsimp only [ghChainExtraQueries2, uD]
      push_cast; ring
    · intro μ σ hcard hact hval hR2 hNotInj z hz
      have hn : 1 ≤ n := by
        by_contra hn0; push Not at hn0
        have hn_eq : n = 0 := by omega
        have hp_eq : p = 0 := by omega
        subst hn_eq hp_eq; omega
      have hk1 : 1 ≤ k := by omega
      have hμ : μ.val < 2 ^ (k * n - 1) := memPrefixValid_lt_half hn hk1 hval hact
      have hseen := card_memSeen_of_memPrefixValid hval
      let θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
      rcases ghCollNorm_probe θ₂ pr hz with ⟨hd_norm, hnext_norm⟩
      have hstep_vec :
          (gaussianHammingAllHitUnitary n m M hM (ghProbeWSpec2 pr)).1 *ᵥ
              workMemState (P_R μ *ᵥ ghCollState hp hm perm (R μ) z) (single μ 1) =
            workMemState (ghDampVec n m (ghProbeWSpec2 pr)
                (P_R μ *ᵥ ghCollState hp hm perm (R μ) z)) (single μ 1) +
              workMemState (ghClickVec n m (ghProbeWSpec2 pr)
                (P_R μ *ᵥ ghCollState hp hm perm (R μ) z))
                (single (memWithTopOne hM μ hμ) 1) :=
        gaussianHammingAllHitMat_mulVec_workMemState hM (ghProbeWSpec2 pr) _ hμ
      rw [ghQuadForm_unitaryEffect (unitaryEffect_phaseTag _), hstep_vec,
        ghQuadForm_wp_measureRegister, hfin2]
      have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) res ≠ 1 := by
        simp [Store.subst]
      have hs1 : (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) res = 1 := by
        simp [Store.subst]
      rw [topAncReg_projector_zero_mulVec hM _ _ hμ, topAncReg_projector_one_mulVec hM _ _ hμ,
        ite_eq_right hs0, ite_eq_left hs1, ghQuadForm_bot_apply, add_zero]
      rcases ghDamp_and_click_marked_ghCollState hp hm perm hR2 hNotInj pr z with ⟨hdamp, _⟩
      rw [hdamp, gh_cqAssertion_add_mat, ghQuadForm_add_mat]
      have hdiv0 : 0 ≤ (((pr.2.2.2 + 2 : ℕ) : ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le
      have hdiv1 : (((pr.2.2.2 + 2 : ℕ) : ℝ≥0) : ℝ) / B ≤ 1 := (div_le_one hB).mpr hkNext_le
      rw [ghQuadForm_constAssertion_workMemState hdiv0 hdiv1]
      have hnorm1 :
          (∑ o : Fin (2 ^ W),
            (normSq ((P_R μ *ᵥ ghCollState hp hm perm (R μ) (z.1, pr.1.val * z.2)) o) : ℂ)) =
            1 := by
        dsimp only [P_R]
        simp_rw [permUnitary_parallelMarkPerm_mulVec_apply_zoom]
        rw [← Complex.ofReal_sum, Equiv.sum_comp (parallelMarkPerm n m (R μ))
            (fun w ↦ normSq (ghCollState hp hm perm (R μ) (z.1, pr.1.val * z.2) w)),
          sum_normSq_ghCollState hp hm hsub3 perm hR2 hNotInj (z.1, pr.1.val * z.2),
          hd_norm, Complex.ofReal_one]
      rcases deflatedRead_mulVec_workMemState_gh (m := m) hseen.2 with ⟨hread_mul, hPR_inv⟩
      have hue :=
        (unitaryEffect_wdPrepAndNoClick_gh (Var := Var) (k := k) hp hm perm S active).2 pr.2.2.2
      have hnext_coll :
          ((Real.cos (2 * (pr.2.2.2 : ℝ) * θ₂) : ℂ) * (z.1, pr.1.val * z.2).1 -
              (Real.sin (2 * (pr.2.2.2 : ℝ) * θ₂) : ℂ) * (z.1, pr.1.val * z.2).2,
            (Real.sin (2 * (pr.2.2.2 : ℝ) * θ₂) : ℂ) * (z.1, pr.1.val * z.2).1 +
              (Real.cos (2 * (pr.2.2.2 : ℝ) * θ₂) : ℂ) * (z.1, pr.1.val * z.2).2) =
          ghProbeNextColl2 θ₂ pr z := rfl
      rw [hnorm1, mul_one, ghQuadForm_unitaryEffect hue, ← mulVec_mulVec,
        ← mulVec_mulVec, hread_mul, hPR_inv,
        ghGrover_iter_ghCollState hp hm hsub3 perm hseen.2 hR2 hNotInj _ pr.2.2.2,
        show S \ memSeen n k (memPrefix k active) μ = R μ from rfl, hnext_coll, hread_mul,
        hnot_rest μ _ hcard hact hval hR2 hNotInj (ghProbeNextColl2 θ₂ pr z) hnext_norm, hc_eq]
      push_cast; ring
private lemma scaledCostRel_ghDeflatedRound {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n)))
    (kInit : ℕ) (probes : List GHZoomProbe) {B : ℝ} (hB : 0 < B)
    (hcB : (ghMaxQueries kInit probes : ℝ) ≤ B) :
    ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)),
      ScaledCostRel (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B
        ((ghDeflatedRound res hm1 hkN hM hp hm perm active kInit
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes).compile
          qAssign (groverParallelMarkingOracle m S))
        θ (ghMaxQueries kInit probes) ∧
      (∀ (μ : Fin (2 ^ (k * n))) (τ : Store Var),
        S.card = k → active < k → MemPrefixValid S active μ →
        (S \ memSeen n k (memPrefix k active) μ).card = 2 →
          (θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
            let R := S \ memSeen n k (memPrefix k active) μ
            let pref := fun x ↦ subcubePref hp hm (perm x)
            if Set.InjOn pref (R : Set (Fin (2 ^ n))) then
              let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
              let u₀ := ghInitAmp2 θ₁ kInit
              ((((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes u₀) / B : ℂ)
            else
              ((ghMaxQueries kInit probes : ℝ) / B : ℂ)) := by
  have hmax_eq : (ghMaxQueries kInit probes : ℝ) =
      (kInit : ℝ) + 1 + (ghProbesMaxQ probes : ℝ) := by
    unfold ghMaxQueries ghProbesMaxQ; push_cast; ring
  have hc_probes : (ghProbesMaxQ probes : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ (kInit : ℝ) + 1 := by positivity
    linarith
  have hc_init : (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ (ghProbesMaxQ probes : ℝ) := Nat.cast_nonneg _
    push_cast; linarith
  have hsub2 : 2 ≤ 2 ^ (n - p) := by omega
  rcases costBounds_ghPieces (Var := Var) res hm1 hkN hM hp hm perm S active with
    ⟨hcb_prep, _, _, _⟩
  rcases scaledCostRel_ghProbeChain (Var := Var) res hm1 hkN hM hp hm hsub3 perm S probes hB
    hc_probes with ⟨θ_ch, hrel_ch, hinj_ch, hnot_ch⟩
  have hrel_init := ghScaledCostRel_of_costBound hB (k_cost := (kInit + 1 : ℕ))
    (by simpa [Nat.cast_add] using hcb_prep kInit) hc_init
  have hsum_le : (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) + (ghProbesMaxQ probes : ℝ) ≤ B := by
    push_cast; linarith
  have hrel_tot := ghScaledCostRel_mono_c hB
    (ghScaledCostRel_seq hB hrel_init hrel_ch hsum_le)
    (le_of_eq (by push_cast; linarith)) hcB
  refine ⟨_, hrel_tot, fun μ τ hcard hact hval hR2 ↦ ?_⟩
  dsimp only
  set R := S \ memSeen n k (memPrefix k active) μ
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hseen := card_memSeen_of_memPrefixValid hval
  refine (ghQuadForm_single _ (workMemIdx n m k 0 μ)).symm.trans ?_
  rw [gh_cqAssertion_add_mat, ghQuadForm_add_mat, ghQuadForm_single]
  have hdiv0 : 0 ≤ (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le
  have hdiv1 : (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B ≤ 1 := (div_le_one hB).mpr hc_init
  have hconst_diag :
      ((constAssertion ((((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B) :
        CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) τ).1.1
        (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      ((((kInit + 1 : ℕ) : ℝ) / B : ℝ) : ℂ) := by
    rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds _ hdiv0 hdiv1,
      HermitianMat.mat_smul, HermitianMat.mat_one]
    simp [Complex.real_smul]
  have hue := (unitaryEffect_wdPrepAndNoClick_gh (Var := Var) (k := k) hp hm perm S active).1 kInit
  rcases deflatedRead_mulVec_workMemState_gh (m := m) hseen.2 with ⟨hread_mul, _⟩
  rw [hconst_diag, ghQuadForm_unitaryEffect hue]
  by_cases hInj : Set.InjOn pref (R : Set (Fin (2 ^ n)))
  · rw [ite_eq_left hInj, ← mulVec_mulVec, ← mulVec_mulVec,
      ghPrep_grover_eq_wdAmpStateC hp hm hsub2 perm hseen.2 hInj kInit, hread_mul]
    have hinit_eq :
        dickeStep (S \ memSeen n k (memPrefix k active) μ).card
          (Real.cos ((2 * (kInit : ℝ) + 1) * Real.arcsin (1 / √(2 ^ (n - p) : ℝ))) : ℂ)
          (Real.sin ((2 * (kInit : ℝ) + 1) * Real.arcsin (1 / √(2 ^ (n - p) : ℝ))) : ℂ)
          (fun b ↦ if b = 0 then 1 else 0) =
        ghInitAmp2 (Real.arcsin (1 / √(2 ^ (n - p) : ℝ))) kInit := by
      rw [hR2]; rfl
    rw [hinit_eq, hinj_ch μ τ hcard hact hval hR2 hInj]
    push_cast; ring
  · rw [ite_eq_right hInj, ← mulVec_mulVec, ← mulVec_mulVec,
      ghPrep_grover_eq_ghCollState hp hm hsub3 perm hseen.2 hR2 hInj kInit, hread_mul]
    have hinit_norm :
        normSq (ghInitColl2 (Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))) kInit).1 +
          normSq (ghInitColl2 (Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))) kInit).2 = 1 := by
      unfold ghInitColl2
      dsimp only
      rw [Complex.normSq_ofReal, Complex.normSq_ofReal, ← sq, ← sq]
      exact Real.cos_sq_add_sin_sq _
    rw [hnot_ch μ τ hcard hact hval hR2 hInj _ hinit_norm, hmax_eq]
    push_cast; ring
private lemma unitaryEffect_wdZoomPrepAndLoop_slot {Var : Type} [DecidableEq Var]
    {n p m k : ℕ} (slot : Fin k) (act1 : ℕ)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) (kZoom : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k act1))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp2 perm).1
    let hadOp := (lowBlock W M).embedMatrix (zoomHadPermUnitary (m := m) hp2 perm).1
    let ctrlOp := (permutationUnitary (zoomCtrlPrefixPermSlot slot hp hm hp2 hm2_pow perm)).1
    UnitaryEffect (Var := Var)
      ((OracleDynamicCircuit.seq
        (.step (phaseTag (permutationUnitary (zoomCtrlPrefixPermSlot slot hp hm hp2 hm2_pow perm))))
        (.seq
          (.step (phaseTag ((lowBlock W M).embedUnitary (zoomHadPermUnitary (m := m) hp2 perm))))
          (.seq (wdDeflatedGroverLoop (m := m) (k := k) hp2 perm act1 kZoom)
            (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k act1))))).compile qAssign
        (groverParallelMarkingOracle m S))
      ((unm * orac) * ((diffOp * phaseOp) ^ kZoom) * hadOp * ctrlOp) := by
  intro W M fc orac unm phaseOp diffOp hadOp ctrlOp
  have hwwhole : workMemReg n m k (W + M) le_rfl = QRegister.whole (W + M) := by
    ext i; exact Nat.zero_add i.val
  have hwlow : workReg n m (W + M) (by omega) = lowBlock W M := rfl
  have hread : UnitaryEffect (Var := Var)
      ((deflatedOracle (m := m) (k := k) le_rfl (memPrefix k act1)).compile qAssign
        (groverParallelMarkingOracle m S))
      (unm * orac) := by
    unfold deflatedOracle; dsimp only [compile]
    rw [hwwhole, QRegister.whole_embedUnitary]
    have h1 := unitaryEffect_qAssign (Var := Var)
      ((workFullReg n m (W + M) (by omega)).embedUnitary (groverParallelMarkingOracle m S))
    rw [workFullReg_embedUnitary_eq] at h1
    exact unitaryEffect_seq h1 (unitaryEffect_phaseTag _)
  have hphase : UnitaryEffect (Var := Var)
      ((deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k act1)).compile
        qAssign (groverParallelMarkingOracle m S))
      phaseOp := by
    unfold deflatedPhaseStep; dsimp only [compile]; rw [hwlow]
    have hfc := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (flagConj n m))
    rw [embedUnitary_val] at hfc
    simpa only [phaseOp, Matrix.mul_assoc] using
      unitaryEffect_seq hfc (unitaryEffect_seq hread hfc)
  have hloop : ∀ t : ℕ, UnitaryEffect (Var := Var)
      ((wdDeflatedGroverLoop (m := m) (k := k) hp2 perm act1 t).compile qAssign
        (groverParallelMarkingOracle m S))
      ((diffOp * phaseOp) ^ t) := by
    intro t
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using unitaryEffect_skip (Var := Var)
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold wdDeflatedGroverStep; dsimp only [compile]
      have hdiff := unitaryEffect_phaseTag (Var := Var)
        ((lowBlock W M).embedUnitary (wdDiffuserUnitary (m := m) hp2 perm))
      rw [embedUnitary_val] at hdiff
      rw [pow_succ]
      exact unitaryEffect_seq (unitaryEffect_seq hphase hdiff) ih
  have hctrl := unitaryEffect_phaseTag (Var := Var)
    (permutationUnitary (zoomCtrlPrefixPermSlot slot hp hm hp2 hm2_pow perm))
  have hhad := unitaryEffect_phaseTag (Var := Var)
    ((lowBlock W M).embedUnitary (zoomHadPermUnitary (m := m) hp2 perm))
  rw [embedUnitary_val] at hhad
  dsimp only [compile]
  simpa only [Matrix.mul_assoc] using
    unitaryEffect_seq hctrl (unitaryEffect_seq hhad (unitaryEffect_seq (hloop kZoom) hread))
private lemma costBound_wdZoomSubcubeRoundSlot {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (slot : Fin k) (act1 kZoom : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm slot act1 kZoom).compile qAssign
        (groverParallelMarkingOracle m S))
      ((kZoom + 1 : ℕ) : ℝ≥0) := by
  let W := m * (n + 1)
  let M := k * n
  let model := CostModel.ofEmbeddedOracle (n := W + M) (groverParallelMarkingOracle m S)
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hread := costBound_deflatedOracle (Var := Var) (m := m) (k := k)
    le_rfl (memPrefix k act1) S
  have hloop (t : ℕ) :
      CostBound (Var := Var) model
        ((wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp2 perm act1 t).compile qAssign
          (groverParallelMarkingOracle m S)) t := by
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using CostBound.skip_zero (Var := Var) model
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold wdDeflatedGroverStep; dsimp only [compile]
      have hstep : CostBound (Var := Var) model
          ((deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k act1)).compile qAssign
              (groverParallelMarkingOracle m S) ;;
            .qAssign (phaseTag ((lowBlock W M).embedUnitary
              (wdDiffuserUnitary (m := m) hp2 perm)))) 1 := by
        simpa using (costBound_deflatedPhaseStep le_rfl (memPrefix k act1) S).seq
          (costBound_qAssign_phaseTag (Var := Var) hor _)
      exact (hstep.seq ih).mono (by rw [← NNReal.coe_le_coe]; push_cast; linarith)
  have hrw : CostBound (Var := Var) model
      ((wdReadoutWrite (Var := Var) (k := k) res hm1 hkN act1).compile qAssign
        (groverParallelMarkingOracle m S)) 0 := by
    unfold wdReadoutWrite; dsimp only [compile]
    exact ((costBound_qAssign_phaseTag (Var := Var) hor _).seq
      (costBound_setCountAndResetWork (Var := Var) (M := M) res
        (batchNextCount hm1 hkN (Nat.mul_one m) act1) hor)).mono (by simp)
  unfold wdZoomSubcubeRoundSlot; dsimp only [compile]
  exact ((costBound_qAssign_phaseTag (Var := Var) hor _).seq
    ((costBound_qAssign_phaseTag (Var := Var) hor _).seq
      ((hloop kZoom).seq (hread.seq hrw)))).mono (by rw [← NNReal.coe_le_coe]; push_cast; linarith)
private noncomputable def ghZoomPostΨ {α : Type*} [DecidableEq α]
    (subDimZoom kZoom : ℕ) (withCost : Bool) (injS : Prop)
    (Ψ : Finset α → ℝ) (R' : Finset α) : ℝ :=
  open Classical in
  if R'.card = 1 then
    (if withCost then ((kZoom + 1 : ℕ) : ℝ) else 0) +
      if injS then Ψ R'
      else p_succ_frac kZoom 1 subDimZoom * Ψ ∅ + (1 - p_succ_frac kZoom 1 subDimZoom) * Ψ R'
  else Ψ R'
private lemma wp_wdZoomSubcubeRoundSlot_k2_of_finset {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hk1 : 1 ≤ k) (hk_eq : k = 2) (hkN : k ≤ 2 ^ n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (kZoom : ℕ)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ))
    (τ : Store Var) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S 1 μ) :
    let pref := fun x ↦ subcubePref hp hm (perm x)
    ((wp ((wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom).compile
        qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1
        (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom false (Set.InjOn pref (S : Set (Fin (2 ^ n)))) Ψ
        (S \ memSeen n k (memPrefix k 1) μ) : ℂ) := by
  intro pref
  classical
  let W := m * (n + 1)
  let M := k * n
  let hbg1 : m * 1 = m := Nat.mul_one m
  let x₀ := addrEquiv n k μ ⟨0, hk1⟩
  have hseen_sub : memSeen n k (memPrefix k 1) μ ⊆ S :=
    (card_memSeen_of_memPrefixValid hval).2
  have hseen_eq : memSeen n k (memPrefix k 1) μ = {x₀} := by
    ext z
    simp only [memSeen, memPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton, x₀]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi0 : i = ⟨0, hk1⟩ := Fin.ext (Nat.lt_one_iff.mp hi)
      rw [hi0]
    · rintro rfl
      exact ⟨⟨0, hk1⟩, Nat.zero_lt_one, rfl⟩
  have hx₀_S : x₀ ∈ S := by
    have hsub := hseen_sub
    rw [hseen_eq, Finset.singleton_subset_iff] at hsub
    exact hsub
  set R := S \ memSeen n k (memPrefix k 1) μ
  have hR_card : R.card = 1 := by
    have hadd := Finset.card_sdiff_add_card_eq_card hseen_sub
    have hsc : (memSeen n k (memPrefix k 1) μ).card = 1 := by rw [hseen_eq, Finset.card_singleton]
    dsimp only [R]; omega
  obtain ⟨y, hyR⟩ := Finset.card_eq_one.mp hR_card
  have hy_mem : y ∈ R := hyR ▸ Finset.mem_singleton_self y
  have hy_S : y ∈ S := (Finset.mem_sdiff.mp hy_mem).1
  have hy_ne_x₀ : y ≠ x₀ := by
    have hnmem := (Finset.mem_sdiff.mp hy_mem).2
    rwa [hseen_eq, Finset.mem_singleton] at hnmem
  have hS_pair : S = {x₀, y} := by
    have hsub_pair : ({x₀, y} : Finset (Fin (2 ^ n))) ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hx₀_S
      · exact (Finset.mem_singleton.mp hz') ▸ hy_S
    exact (Finset.eq_of_subset_of_card_le hsub_pair
      (by rw [hcard, hk_eq, Finset.card_pair hy_ne_x₀.symm])).symm
  let j_hit := pref x₀
  have hinj_iff : Set.InjOn pref (S : Set (Fin (2 ^ n))) ↔ pref y ≠ j_hit := by
    constructor
    · intro hInj heq
      exact hy_ne_x₀ (hInj hy_S hx₀_S heq)
    · intro hne a ha b hb hab
      rw [hS_pair] at ha hb
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha) with rfl | ha' <;>
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hb) with rfl | hb'
      · rfl
      · rw [Finset.mem_singleton.mp hb'] at hab ⊢; exact False.elim (hne hab.symm)
      · rw [Finset.mem_singleton.mp ha'] at hab ⊢; exact False.elim (hne hab)
      · rw [Finset.mem_singleton.mp ha', Finset.mem_singleton.mp hb']
  let preCirc : OracleCirc Var (W + M) ((n + 1) * m) :=
    .seq (.step (phaseTag (permutationUnitary
        (zoomCtrlPrefixPermSlot ⟨0, hk1⟩ hp hm hp2 hm2_pow perm))))
      (.seq (.step (phaseTag ((lowBlock W M).embedUnitary (zoomHadPermUnitary (m := m) hp2 perm))))
        (.seq (wdDeflatedGroverLoop (m := m) (k := k) hp2 perm 1 kZoom)
          (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k 1))))
  have hassoc :
      wp ((wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom).compile
          qAssign (groverParallelMarkingOracle m S)) Θ =
        wp (preCirc.compile qAssign (groverParallelMarkingOracle m S))
          (wp ((wdReadoutWrite res hm1 hkN 1).compile qAssign
            (groverParallelMarkingOracle m S)) Θ) := by
    unfold wdZoomSubcubeRoundSlot
    dsimp only [preCirc, compile]
    simp only [wp_qSeq]; rfl
  rw [← ghQuadForm_single
      ((wp ((wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom).compile
        qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n m k 0 μ), hassoc,
    ghQuadForm_unitaryEffect
      (unitaryEffect_wdZoomPrepAndLoop_slot ⟨0, hk1⟩ 1 hp2 hm2_pow hp hm perm S kZoom)]
  let jSub (j₂ : Fin m) : Fin (m * m) := zoomCombine j₂ j_hit
  let ξ (j₂ : Fin m) := zoomSlotWrap hp2 hm2_pow perm (jSub j₂)
    (groverMultiState (subcubeLocalSet hp2 hm2_pow (R.image perm) (jSub j₂)) kZoom)
  let φ := zoomProdState ξ
  let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
  have hvec :
      (((permutationUnitary (unmarkPerm n m k (memPrefix k 1))).1 *
          (lowBlock W M).embedMatrix
            ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1) *
        (((lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp2 perm).1 *
            ((lowBlock W M).embedMatrix (flagConj n m).1 *
              (permutationUnitary (unmarkPerm n m k (memPrefix k 1))).1 *
              (lowBlock W M).embedMatrix
                ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 *
              (lowBlock W M).embedMatrix (flagConj n m).1)) ^ kZoom) *
        (lowBlock W M).embedMatrix (zoomHadPermUnitary (m := m) hp2 perm).1 *
        (permutationUnitary (zoomCtrlPrefixPermSlot ⟨0, hk1⟩ hp hm hp2 hm2_pow perm)).1) *ᵥ
          single (workMemIdx n m k 0 μ) 1 =
        workMemState (P_R *ᵥ φ) (single μ 1) := by
    dsimp only [W, M]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      zoomPrep_mulVec_workMemIdx_slot ⟨0, hk1⟩ hp2 hm2_pow hp hm perm μ,
      zoomDeflatedGrover_iter hp2 hm2_pow perm hseen_sub jSub kZoom,
      unmark_mul_parallelOracle_workMemState (memPrefix k 1) φ μ hseen_sub,
      show S \ memSeen n k (memPrefix k 1) μ = R from rfl,
      fullReg_embedUnitary_eq_permutationUnitary R]
  rw [hvec]
  have hsupp : ∀ o : Fin (2 ^ W),
      φ (parallelMarkPerm n m R o) ≠ 0 → ∀ x ∈ groupHits hbg1 o, x ∈ R := by
    intro o hnz x hx
    have hslot_nz (j₂ : Fin m) :
        ξ j₂ ((groupReg hbg1 j₂).extractIndex (parallelMarkPerm n m R o)) ≠ 0 :=
      fun h0 ↦ hnz (Finset.prod_eq_zero (Finset.mem_univ j₂) h0)
    rcases groupHits_of_zoomSlotWrap hp2 hm2_pow perm R jSub _ o hslot_nz with ⟨hmem_sub, htoFin⟩
    have hx_tf : x ∈ (groupHits hbg1 o).toFinset := List.mem_toFinset.mpr hx
    rw [htoFin, List.mem_toFinset, List.mem_filterMap] at hx_tf
    rcases hx_tf with ⟨j₂, _, hj₂⟩
    exact (hmem_sub j₂ x hj₂).1
  rw [ghQuadForm_wp_wdReadoutWrite_of_support res hm1 hkN hcard hval Θ Ψ hΘ τ φ hsupp]
  have hsing := sum_normSq_zoomReadout_singleton hm1 hp2 hm2_pow hp hm perm y j_hit kZoom
    (fun T ↦ (Ψ T : ℂ))
  dsimp only at hsing
  rw [← hyR] at hsing
  rw [hsing]
  unfold ghZoomPostΨ
  rw [ite_eq_left hR_card]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  by_cases hInj : Set.InjOn pref (S : Set (Fin (2 ^ n)))
  · have hne : pref y ≠ j_hit := hinj_iff.mp hInj
    rw [ite_eq_right hne, ite_eq_left hInj]
  · have heq : pref y = j_hit := not_ne_iff.mp (mt hinj_iff.mpr hInj)
    rw [ite_eq_left heq, ite_eq_right hInj]
    push_cast; ring
/-- One `k = 2` Gaussian-Hamming Weak-Dicke + Clicked-Subcube Zoom pass. -/
noncomputable def ghZoomOnePass {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hk1 : 1 ≤ k) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHZoomSpec) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  match spec_fn 2 with
  | none => .skip
  | some (kInit, probes, kZoom) =>
      .qIf (fun σ ↦ σ res = 0)
        (.seq
          (ghDeflatedRound res hm1 hkN hM hp hm perm 0 kInit
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes)
          (.qIf (fun σ ↦ σ res = 1)
            (wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom)
            .skip))
        .skip
/-- Sequential execution of `ghZoomOnePass` across a list of `(perm, spec_fn)` passes. -/
noncomputable def ghZoomSweeps {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hk1 : 1 ≤ k) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)) →
      OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | (perm, spec_fn) :: rest =>
      .seq (ghZoomOnePass res hm1 hk1 hkN hM hp2 hm2_pow hp hm perm spec_fn)
        (ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm rest)
/-- Multi-sweep prefix initializing `res` via computational-basis measurement before
  `ghZoomSweeps`. -/
noncomputable def ghZoomMultiSweepPre {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hk1 : 1 ≤ k) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec))) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (.measure res (QRegister.whole (m * (n + 1) + k * n)))
    (.qIf (fun σ ↦ σ res = 0)
      (ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes)
      .skip)
/-- Instantiate `passes` along rotated bit-slices `0.. W - 1` at subcube exponent `n - p`. -/
noncomputable def ghZoomPermPasses {n p m W : ℕ}
    (hs : (n - W * p) + W * p = n) (hm : m = 2 ^ p)
    (passes : List GHZoomPassFn) (hW_eq : passes.length = W) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)) :=
  (List.finRange W).map fun i ↦
    (rotatedSliceSwapPerm hs hm (Nat.zero_lt_of_lt i.isLt) i,
      (passes[i.val]'(by rw [hW_eq]; exact i.isLt)) (n - p))
/-- Rotated bit-slice Gaussian-Hamming Weak-Dicke + Clicked-Subcube Zoom multi-pass circuit
  (`420 ≤ n`, `passes.length ≤ 16`, `k = 2`), falling back to `Stage1.circuit` outside the
  asymptotic regime. -/
noncomputable def ghZoomRotCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (passes : List GHZoomPassFn) (hW : passes.length ≤ 16)
    (n : ℕ) : OracleCirc Var (Stage1.qubits n m k) ((n + 1) * m) :=
  if hn420 : 420 ≤ n then
    if hkN : k ≤ 2 ^ n then
      if _ : k = 2 then
        let p := Stage2CertInternals.gridExp m
        have hgb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2
        have hp10 : p ≤ 10 := hgb.2.1
        have hm : m = 2 ^ p := hgb.2.2.symm
        have hm2_pow : m * m = 2 ^ (2 * p) := by
          rw [hm, ← pow_add, Nat.two_mul]
        have hs : (n - passes.length * p) + passes.length * p = n :=
          Nat.sub_add_cancel ((Nat.mul_le_mul hW hp10).trans (by omega))
        .seq
          (ghZoomMultiSweepPre res (one_le_of_mem_groverGrid hm_grid)
            (Nat.le_trans (by omega : 1 ≤ 2) hk2) hkN
            (Nat.mul_pos (by omega) (by omega))
            (by omega) hm2_pow (by omega) hm (ghZoomPermPasses hs hm passes rfl))
          (findAllBatchTail res (one_le_of_mem_groverGrid hm_grid) hkN
            (b := fun u ↦ if u < k - 1 then stage2Batch m (k - u) else 1)
            (g := fun u ↦ if u < k - 1 then stage2Group m (k - u) else m)
            (fun u _ ↦ by
              by_cases hlt : u < k - 1
              · rw [ite_eq_left hlt, ite_eq_left hlt]
                have hk_hi := le_1024_of_mem_groverGrid hk_grid
                exact (stage2_bg hm_grid hm2 (by omega) (by omega)).2
              · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul])
            (fun u ↦
              K_varPhi (stage2Angle m (k - u)) n
                (if u < k - 1 then stage2Group m (k - u) else m) (k - u))
            (eigLockStage res n m k hm_grid hk_grid (by omega)
              ⟨k - 1, Nat.sub_lt (by omega) zero_lt_one⟩))
      else Stage1.circuit res n m k
    else Stage1.circuit res n m k
  else Stage1.circuit res n m k
private def IsWpTopGH {Var : Type} [DecidableEq Var] {Q O : ℕ}
    (C : OracleCirc Var Q O) : Prop :=
  ∀ oracle : Unitary (2 ^ O),
    wp (C.compile qAssign oracle) (⊤ : CQAssertion (Store Var) (2 ^ Q)) = ⊤
private lemma isWpTopGH_skip {Var : Type} [DecidableEq Var] {Q O : ℕ} :
    IsWpTopGH (.skip : OracleCirc Var Q O) := fun _ ↦ rfl
private lemma isWpTopGH_step {Var : Type} [DecidableEq Var] {Q O : ℕ} (U : Unitary (2 ^ Q)) :
    IsWpTopGH (.step U : OracleCirc Var Q O) := fun _ ↦ by
  funext σ; simp [compile]
private lemma isWpTopGH_oracle {Var : Type} [DecidableEq Var] {Q O : ℕ} (r : QRegister O Q) :
    IsWpTopGH (.oracle r : OracleCirc Var Q O) := fun _ ↦ by
  funext σ; simp [compile]
private lemma isWpTopGH_measure {Var : Type} [DecidableEq Var] {w Q O : ℕ}
    (x : Var) (r : QRegister w Q) :
    IsWpTopGH (.measure x r : OracleCirc Var Q O) := fun _ ↦ by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  dsimp only [compile]
  rw [← HermitianMat.val_eq_coe, wp_measureRegister]
  have hidem (o : Fin (2 ^ w)) :
      r.basisOutcomeProjector o *
          ((⊤ : CQAssertion (Store Var) (2 ^ Q)) (Store.subst σ x (Int.ofNat o.val))).1.1 *
          r.basisOutcomeProjector o =
        r.basisOutcomeProjector o := by
    change r.basisOutcomeProjector o * (1 : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) *
        r.basisOutcomeProjector o = _
    rw [Matrix.mul_one, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    ext z₁ z₂
    by_cases hz : z₁ = z₂
    · subst hz; by_cases h : r.extractIndex z₁ = o <;> simp [h]
    · simp [hz]
  simp_rw [hidem]
  exact r.sum_basisOutcomeProjector
private lemma isWpTopGH_seq {Var : Type} [DecidableEq Var] {Q O : ℕ}
    {c₁ c₂ : OracleCirc Var Q O} (h₁ : IsWpTopGH c₁) (h₂ : IsWpTopGH c₂) :
    IsWpTopGH (.seq c₁ c₂) := fun oracle ↦ by
  dsimp only [compile]; rw [wp_qSeq, h₂ oracle, h₁ oracle]
private lemma isWpTopGH_qIf {Var : Type} [DecidableEq Var] {Q O : ℕ}
    (b : Store Var → Prop) [DecidablePred b]
    {c₁ c₂ : OracleCirc Var Q O} (h₁ : IsWpTopGH c₁) (h₂ : IsWpTopGH c₂) :
    IsWpTopGH (.qIf b c₁ c₂) := fun oracle ↦ by
  funext σ; dsimp only [compile]; rw [wp_qIf]; dsimp only
  split_ifs <;> simp [h₁ oracle, h₂ oracle]
private lemma isWpTopGH_sequence {Var : Type} [DecidableEq Var] {Q O : ℕ}
    (l : List (OracleCirc Var Q O)) (hl : ∀ c ∈ l, IsWpTopGH c) :
    IsWpTopGH (OracleDynamicCircuit.sequence l) := by
  induction l with
  | nil => exact isWpTopGH_skip
  | cons c rest ih =>
    rw [OracleDynamicCircuit.sequence_cons]
    exact isWpTopGH_seq (hl c List.mem_cons_self)
      (ih fun x hx ↦ hl x (List.mem_cons_of_mem c hx))
private lemma isWpTopGH_setCountAndResetWork {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ W) → Fin (2 ^ W)) :
    IsWpTopGH (setCountAndResetWork (Var := Var) (M := M) (O := O) res g) := fun _ ↦ by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  rw [← HermitianMat.val_eq_coe, wp_setCountAndResetWork]
  have h_proj_o (o : Fin (2 ^ W)) :
      ((lowBlock W M).embedMatrix (Matrix.single 0 o 1))ᴴ *
        ((⊤ : CQAssertion (Store Var) (2 ^ (W + M))) (Store.subst σ res (Int.ofNat (g o).val))).1.1
          *
        (lowBlock W M).embedMatrix (Matrix.single 0 o 1) =
      (lowBlock W M).basisOutcomeProjector o := by
    change ((lowBlock W M).embedMatrix (Matrix.single 0 o 1))ᴴ * 1 *
        (lowBlock W M).embedMatrix (Matrix.single 0 o 1) = _
    rw [Matrix.mul_one, ← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul]
    have hsing : (Matrix.single (0 : Fin (2 ^ W)) o (1 : ℂ))ᴴ * Matrix.single 0 o 1 =
        compProj o := by
      ext i j
      rw [Matrix.mul_apply, compProj,
        Fintype.sum_eq_single (0 : Fin (2 ^ W)) (fun x hx ↦ by simp [hx.symm])]
      simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
      by_cases hi : o = i
      · subst hi; by_cases hj : o = j <;> simp [hj]
      · simp [hi]
    rw [hsing, QRegister.basisOutcomeProjector]
  simp_rw [h_proj_o]
  exact (lowBlock W M).sum_basisOutcomeProjector
private lemma isWpTopGH_ghDeflatedRound {P : Type*} {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n)))
    (active kInit : ℕ) (wSpecOf : P → ℕ → GaussPyth × PythPair) (stepsOf : P → ℕ)
    (probes : List P) :
    IsWpTopGH
      (ghDeflatedRound (Var := Var) res hm1 hkN hM hp hm perm active kInit
        wSpecOf stepsOf probes) := by
  have hread : IsWpTopGH
      (deflatedOracle (Var := Var) (n := n) (m := m) (k := k) le_rfl (memPrefix k active)) :=
    isWpTopGH_seq (isWpTopGH_oracle _) (isWpTopGH_step _)
  have hloop (t : ℕ) : IsWpTopGH
      (wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp perm active t) :=
    isWpTopGH_sequence _ fun c hc ↦ by
      rw [List.mem_replicate] at hc; rcases hc with ⟨_, rfl⟩
      exact isWpTopGH_seq
        (isWpTopGH_seq (isWpTopGH_step _) (isWpTopGH_seq hread (isWpTopGH_step _)))
        (isWpTopGH_step _)
  have hprep : IsWpTopGH (wdPrepAndLoop (Var := Var) (k := k) hp hm perm active kInit) :=
    isWpTopGH_seq (isWpTopGH_step _) (isWpTopGH_seq (hloop kInit) hread)
  have hrw : IsWpTopGH (wdReadoutWrite (Var := Var) (k := k) res hm1 hkN active) :=
    isWpTopGH_seq (isWpTopGH_step _) (isWpTopGH_setCountAndResetWork res _)
  have hclean : IsWpTopGH (wdClickCleanup (Var := Var) (k := k) res hm1 hkN hM active) :=
    isWpTopGH_seq (isWpTopGH_step _) hrw
  have hnoclick (t : ℕ) : IsWpTopGH (wdNoClickStep (Var := Var) (k := k) hp perm active t) :=
    isWpTopGH_seq hread (isWpTopGH_seq (hloop t) hread)
  have hchain : ∀ l : List P, IsWpTopGH
      (ghProbeChain (Var := Var) res hm1 hkN hM hp perm active wSpecOf stepsOf l) := by
    intro l
    induction l with
    | nil => exact hrw
    | cons pr rest ih =>
      exact isWpTopGH_seq (isWpTopGH_step _)
        (isWpTopGH_seq (isWpTopGH_measure _ _)
          (isWpTopGH_qIf _ hclean (isWpTopGH_seq (hnoclick (stepsOf pr)) ih)))
  exact isWpTopGH_seq hprep (hchain probes)
private lemma isWpTopGH_wdZoomSubcubeRoundSlot {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (slot : Fin k) (act1 kZoom : ℕ) :
    IsWpTopGH
      (wdZoomSubcubeRoundSlot (Var := Var) res hm1 hkN hp2 hm2_pow hp hm perm slot act1 kZoom) := by
  have hread : IsWpTopGH
      (deflatedOracle (Var := Var) (n := n) (m := m) (k := k) le_rfl (memPrefix k act1)) :=
    isWpTopGH_seq (isWpTopGH_oracle _) (isWpTopGH_step _)
  have hloop : IsWpTopGH
      (wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp2 perm act1 kZoom) :=
    isWpTopGH_sequence _ fun c hc ↦ by
      rw [List.mem_replicate] at hc; rcases hc with ⟨_, rfl⟩
      exact isWpTopGH_seq
        (isWpTopGH_seq (isWpTopGH_step _) (isWpTopGH_seq hread (isWpTopGH_step _)))
        (isWpTopGH_step _)
  have hrw : IsWpTopGH (wdReadoutWrite (Var := Var) (k := k) res hm1 hkN act1) :=
    isWpTopGH_seq (isWpTopGH_step _) (isWpTopGH_setCountAndResetWork res _)
  exact isWpTopGH_seq (isWpTopGH_step _)
    (isWpTopGH_seq (isWpTopGH_step _) (isWpTopGH_seq hloop (isWpTopGH_seq hread hrw)))
private lemma isWpTopGH_ghZoomSweeps {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hm1 : 1 ≤ m) (hk1 : 1 ≤ k) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec))) :
    IsWpTopGH (ghZoomSweeps (Var := Var) res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes) := by
  induction passes with
  | nil => exact isWpTopGH_skip
  | cons ps rest ih =>
    rcases ps with ⟨perm, spec_fn⟩
    refine isWpTopGH_seq ?_ ih
    unfold ghZoomOnePass
    cases spec_fn 2 with
    | none => exact isWpTopGH_skip
    | some kpz =>
      rcases kpz with ⟨kInit, probes, kZoom⟩
      exact isWpTopGH_qIf _
        (isWpTopGH_seq
          (isWpTopGH_ghDeflatedRound res hm1 hkN hM hp hm perm 0 kInit
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes)
          (isWpTopGH_qIf _
            (isWpTopGH_wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom)
            isWpTopGH_skip))
        isWpTopGH_skip
private noncomputable def ghZoomBaseStep {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool)
    (kInit : ℕ) (probes : List GHZoomProbe) (Ψ : Finset α → ℝ) (R : Finset α) : ℝ :=
  open Classical in
  if Set.InjOn pref (R : Set α) then
    let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
    let u₀ := ghInitAmp2 θ₁ kInit
    let uf := ghChainFinalAmp2 θ₁ probes u₀
    (if withCost then ((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes u₀ else 0) +
      ghChainClickProb2 θ₁ probes u₀ * Ψ ∅ +
      ∑ B ∈ R.powerset, Complex.normSq (uf B.card) * Ψ (R \ B)
  else
    let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
    let z₀ := ghInitColl2 θ₂ kInit
    let zf := ghChainFinalColl2 θ₂ probes z₀
    (if withCost then (ghMaxQueries kInit probes : ℝ) else 0) +
      Complex.normSq zf.1 * Ψ R +
      Complex.normSq zf.2 * ∑ x ∈ R, (1 / 2 : ℝ) * Ψ (R \ {x})
private noncomputable def ghZoomSubsetStep {α : Type*} [DecidableEq α] {m : ℕ}
    (subN subNZoom : ℕ) (pref : α → Fin m) (withCost : Bool)
    (spec_fn : ℕ → GHZoomSpec) (Ψ : Finset α → ℝ) (R : Finset α) : ℝ :=
  open Classical in
  match spec_fn 2 with
  | none => Ψ R
  | some (kInit, probes, kZoom) =>
      if R.card = 2 then
        ghZoomBaseStep subN pref withCost kInit probes
          (ghZoomPostΨ (2 ^ subNZoom) kZoom withCost (Set.InjOn pref (R : Set α)) Ψ) R
      else Ψ R
private noncomputable def ghZoomCircDP {n p m : ℕ}
    (hp2 : 2 * p ≤ n) (hp : p ≤ n) (hm : m = 2 ^ p) (withCost : Bool) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)) →
      (Finset (Fin (2 ^ n)) → ℝ) → Finset (Fin (2 ^ n)) → ℝ
  | [], Ψ, R => Ψ R
  | (perm, spec_fn) :: rest, Ψ, R =>
      ghZoomSubsetStep (n - p) (n - 2 * p) (fun x ↦ subcubePref hp hm (perm x)) withCost spec_fn
        (ghZoomCircDP hp2 hp hm withCost rest Ψ) R
private lemma ghChainClickProb2_nonneg (θ₁ : ℝ) :
    ∀ (probes : List GHZoomProbe) (u : ℕ → ℂ), 0 ≤ ghChainClickProb2 θ₁ probes u
  | [], _ => le_rfl
  | _ :: rest, _ =>
      add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
        (ghChainClickProb2_nonneg θ₁ rest _)
private lemma ghChainExtraQueries2_nonneg (θ₁ : ℝ) :
    ∀ (probes : List GHZoomProbe) (u : ℕ → ℂ), 0 ≤ ghChainExtraQueries2 θ₁ probes u
  | [], _ => le_rfl
  | _ :: rest, _ =>
      add_nonneg
        (mul_nonneg
          (add_nonneg
            (add_nonneg (Complex.normSq_nonneg _)
              (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
            (Complex.normSq_nonneg _))
          (Nat.cast_nonneg _))
        (ghChainExtraQueries2_nonneg θ₁ rest _)
private lemma ghZoomPostΨ_nonneg {α : Type*} [DecidableEq α]
    (subDimZoom kZoom : ℕ) (withCost : Bool) (injS : Prop)
    {Ψ : Finset α → ℝ} {R : Finset α} (hΨ : ∀ R' ⊆ R, 0 ≤ Ψ R')
    {R' : Finset α} (hR' : R' ⊆ R) :
    0 ≤ ghZoomPostΨ subDimZoom kZoom withCost injS Ψ R' := by
  classical
  unfold ghZoomPostΨ
  split_ifs
  · exact add_nonneg (Nat.cast_nonneg _) (hΨ R' hR')
  · refine add_nonneg (Nat.cast_nonneg _) (add_nonneg ?_ ?_)
    · exact mul_nonneg (sq_nonneg _) (hΨ ∅ (Finset.empty_subset R))
    · exact mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one _)) (hΨ R' hR')
  · simpa using hΨ R' hR'
  · refine add_nonneg (by simp) (add_nonneg ?_ ?_)
    · exact mul_nonneg (sq_nonneg _) (hΨ ∅ (Finset.empty_subset R))
    · exact mul_nonneg (sub_nonneg.mpr (Real.sin_sq_le_one _)) (hΨ R' hR')
  · exact hΨ R' hR'
private lemma ghZoomBaseStep_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool)
    (kInit : ℕ) (probes : List GHZoomProbe) {Ψ : Finset α → ℝ} {R : Finset α}
    (hΨ : ∀ R' ⊆ R, 0 ≤ Ψ R') :
    0 ≤ ghZoomBaseStep subN pref withCost kInit probes Ψ R := by
  classical
  unfold ghZoomBaseStep
  by_cases hInj : Set.InjOn pref (R : Set α)
  · rw [ite_eq_left hInj]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · cases withCost
      · simp
      · exact add_nonneg (Nat.cast_nonneg _) (ghChainExtraQueries2_nonneg _ _ _)
    · exact mul_nonneg (ghChainClickProb2_nonneg _ _ _) (hΨ ∅ (Finset.empty_subset R))
    · exact Finset.sum_nonneg fun B _ ↦
        mul_nonneg (Complex.normSq_nonneg _) (hΨ (R \ B) Finset.sdiff_subset)
  · rw [ite_eq_right hInj]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · cases withCost
      · simp
      · exact Nat.cast_nonneg _
    · exact mul_nonneg (Complex.normSq_nonneg _) (hΨ R Finset.Subset.rfl)
    · refine mul_nonneg (Complex.normSq_nonneg _) (Finset.sum_nonneg fun x _ ↦ ?_)
      exact mul_nonneg (by norm_num) (hΨ (R \ {x}) Finset.sdiff_subset)
private lemma ghZoomSubsetStep_nonneg {α : Type*} [DecidableEq α] {m : ℕ}
    (subN subNZoom : ℕ) (pref : α → Fin m) (withCost : Bool)
    (spec_fn : ℕ → GHZoomSpec) {Ψ : Finset α → ℝ} {R : Finset α}
    (hΨ : ∀ R' ⊆ R, 0 ≤ Ψ R') :
    0 ≤ ghZoomSubsetStep subN subNZoom pref withCost spec_fn Ψ R := by
  classical
  unfold ghZoomSubsetStep
  cases spec_fn 2 with
  | none => exact hΨ R Finset.Subset.rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    split_ifs
    · exact ghZoomBaseStep_nonneg _ _ _ _ _ fun R' hR' ↦ ghZoomPostΨ_nonneg _ _ _ _ hΨ hR'
    · exact hΨ R Finset.Subset.rfl
private lemma ghZoomCircDP_nonneg {n p m : ℕ}
    (hp2 : 2 * p ≤ n) (hp : p ≤ n) (hm : m = 2 ^ p) (withCost : Bool)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    {Ψ : Finset (Fin (2 ^ n)) → ℝ} {R : Finset (Fin (2 ^ n))}
    (hΨ : ∀ R' ⊆ R, 0 ≤ Ψ R') :
    0 ≤ ghZoomCircDP hp2 hp hm withCost passes Ψ R := by
  induction passes generalizing R with
  | nil => exact hΨ R Finset.Subset.rfl
  | cons _ rest ih =>
    exact ghZoomSubsetStep_nonneg _ _ _ _ _ fun R' hR' ↦
      ih fun R'' hR'' ↦ hΨ R'' (hR''.trans hR')
private lemma ghZoomBaseStep_true_eq_cost_add_false {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHZoomProbe)
    (Ψ : Finset α → ℝ) (R : Finset α) :
    ghZoomBaseStep subN pref true kInit probes Ψ R =
      ghZoomBaseStep subN pref true kInit probes (fun _ ↦ 0) R +
        ghZoomBaseStep subN pref false kInit probes Ψ R := by
  classical
  unfold ghZoomBaseStep
  by_cases hInj : Set.InjOn pref (R : Set α)
  · simp only [ite_eq_left hInj, ↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero]
    ring
  · simp only [ite_eq_right hInj, ↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero]
    ring
private lemma ghZoomBaseStep_false_add {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHZoomProbe)
    (A B : Finset α → ℝ) (R : Finset α) :
    ghZoomBaseStep subN pref false kInit probes (fun R' ↦ A R' + B R') R =
      ghZoomBaseStep subN pref false kInit probes A R +
        ghZoomBaseStep subN pref false kInit probes B R := by
  classical
  unfold ghZoomBaseStep
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  by_cases hInj : Set.InjOn pref (R : Set α)
  · rw [ite_eq_left hInj, ite_eq_left hInj, ite_eq_left hInj]
    simp_rw [mul_add, Finset.sum_add_distrib]
    ring
  · rw [ite_eq_right hInj, ite_eq_right hInj, ite_eq_right hInj]
    simp_rw [mul_add, Finset.sum_add_distrib]
    ring
private lemma ghZoomBaseStep_false_mul {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHZoomProbe)
    (c : ℝ) (Ψ : Finset α → ℝ) (R : Finset α) :
    ghZoomBaseStep subN pref false kInit probes (fun R' ↦ c * Ψ R') R =
      c * ghZoomBaseStep subN pref false kInit probes Ψ R := by
  classical
  unfold ghZoomBaseStep
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  by_cases hInj : Set.InjOn pref (R : Set α)
  · rw [ite_eq_left hInj, ite_eq_left hInj]
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc]
    rw [← Finset.mul_sum, ← mul_add]
  · rw [ite_eq_right hInj, ite_eq_right hInj]
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc]
    rw [← Finset.mul_sum]
    ring
private lemma ghZoomPostΨ_true_eq_cost_add_false {α : Type*} [DecidableEq α]
    (subDimZoom kZoom : ℕ) (injS : Prop)
    (Ψ : Finset α → ℝ) (R' : Finset α) :
    ghZoomPostΨ subDimZoom kZoom true injS Ψ R' =
      ghZoomPostΨ subDimZoom kZoom true injS (fun _ ↦ 0) R' +
        ghZoomPostΨ subDimZoom kZoom false injS Ψ R' := by
  classical
  unfold ghZoomPostΨ
  by_cases h1 : R'.card = 1
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h1]
    by_cases hinj : injS <;> simp [hinj]
  · simp [h1]
private lemma ghZoomPostΨ_false_mul {α : Type*} [DecidableEq α]
    (subDimZoom kZoom : ℕ) (injS : Prop)
    (c : ℝ) (Ψ : Finset α → ℝ) (R' : Finset α) :
    ghZoomPostΨ subDimZoom kZoom false injS (fun T ↦ c * Ψ T) R' =
      c * ghZoomPostΨ subDimZoom kZoom false injS Ψ R' := by
  classical
  unfold ghZoomPostΨ
  by_cases h1 : R'.card = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases hinj : injS
    · simp [hinj]
    · rw [ite_eq_right hinj, ite_eq_right hinj]
      simp only [Bool.false_eq_true, ↓reduceIte]; ring
  · simp [h1]
private lemma ghZoomPostΨ_false_add {α : Type*} [DecidableEq α]
    (subDimZoom kZoom : ℕ) (injS : Prop)
    (A B : Finset α → ℝ) (R' : Finset α) :
    ghZoomPostΨ subDimZoom kZoom false injS (fun T ↦ A T + B T) R' =
      ghZoomPostΨ subDimZoom kZoom false injS A R' +
        ghZoomPostΨ subDimZoom kZoom false injS B R' := by
  classical
  unfold ghZoomPostΨ
  by_cases h1 : R'.card = 1
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h1]
    by_cases hinj : injS
    · simp [hinj]
    · rw [ite_eq_right hinj, ite_eq_right hinj, ite_eq_right hinj]
      simp only [Bool.false_eq_true, ↓reduceIte]; ring
  · simp [h1]
private lemma ghZoomSubsetStep_true_eq_cost_add_false {α : Type*} [DecidableEq α] {m : ℕ}
    (subN subNZoom : ℕ) (pref : α → Fin m)
    (spec_fn : ℕ → GHZoomSpec) (Ψ : Finset α → ℝ) (R : Finset α) :
    ghZoomSubsetStep subN subNZoom pref true spec_fn Ψ R =
      ghZoomSubsetStep subN subNZoom pref true spec_fn (fun _ ↦ 0) R +
        ghZoomSubsetStep subN subNZoom pref false spec_fn Ψ R := by
  classical
  unfold ghZoomSubsetStep
  cases spec_fn 2 with
  | none => simp
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    by_cases hr2 : R.card = 2
    · rw [ite_eq_left hr2, ite_eq_left hr2, ite_eq_left hr2]
      have hpost :
          ghZoomPostΨ (2 ^ subNZoom) kZoom true (Set.InjOn pref (R : Set α)) Ψ =
            fun R' ↦
              ghZoomPostΨ (2 ^ subNZoom) kZoom true (Set.InjOn pref (R : Set α)) (fun _ ↦ 0) R' +
                ghZoomPostΨ (2 ^ subNZoom) kZoom false (Set.InjOn pref (R : Set α)) Ψ R' :=
        funext (ghZoomPostΨ_true_eq_cost_add_false _ _ _ Ψ)
      rw [hpost, ghZoomBaseStep_true_eq_cost_add_false, ghZoomBaseStep_false_add,
        ← add_assoc, ← ghZoomBaseStep_true_eq_cost_add_false]
    · simp [hr2]
private lemma ghZoomSubsetStep_false_mul {α : Type*} [DecidableEq α] {m : ℕ}
    (subN subNZoom : ℕ) (pref : α → Fin m)
    (spec_fn : ℕ → GHZoomSpec) (c : ℝ) (Ψ : Finset α → ℝ) (R : Finset α) :
    ghZoomSubsetStep subN subNZoom pref false spec_fn (fun R' ↦ c * Ψ R') R =
      c * ghZoomSubsetStep subN subNZoom pref false spec_fn Ψ R := by
  classical
  unfold ghZoomSubsetStep
  cases spec_fn 2 with
  | none => rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    by_cases hr2 : R.card = 2
    · rw [ite_eq_left hr2, ite_eq_left hr2]
      have hpost :
          ghZoomPostΨ (2 ^ subNZoom) kZoom false (Set.InjOn pref (R : Set α))
            (fun R' ↦ c * Ψ R') =
            fun R' ↦ c * ghZoomPostΨ (2 ^ subNZoom) kZoom false
              (Set.InjOn pref (R : Set α)) Ψ R' :=
        funext (ghZoomPostΨ_false_mul _ _ _ c Ψ)
      rw [hpost, ghZoomBaseStep_false_mul]
    · simp [hr2]
private lemma ghZoomSubsetStep_false_add {α : Type*} [DecidableEq α] {m : ℕ}
    (subN subNZoom : ℕ) (pref : α → Fin m)
    (spec_fn : ℕ → GHZoomSpec) (A B : Finset α → ℝ) (R : Finset α) :
    ghZoomSubsetStep subN subNZoom pref false spec_fn (fun R' ↦ A R' + B R') R =
      ghZoomSubsetStep subN subNZoom pref false spec_fn A R +
        ghZoomSubsetStep subN subNZoom pref false spec_fn B R := by
  classical
  unfold ghZoomSubsetStep
  cases spec_fn 2 with
  | none => rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    by_cases hr2 : R.card = 2
    · rw [ite_eq_left hr2, ite_eq_left hr2, ite_eq_left hr2]
      have hpost :
          ghZoomPostΨ (2 ^ subNZoom) kZoom false (Set.InjOn pref (R : Set α))
            (fun R' ↦ A R' + B R') =
            fun R' ↦
              ghZoomPostΨ (2 ^ subNZoom) kZoom false (Set.InjOn pref (R : Set α)) A R' +
                ghZoomPostΨ (2 ^ subNZoom) kZoom false (Set.InjOn pref (R : Set α)) B R' :=
        funext (ghZoomPostΨ_false_add _ _ _ A B)
      rw [hpost, ghZoomBaseStep_false_add]
    · simp [hr2]
private lemma ghZoomCircDP_false_mul {n p m : ℕ}
    (hp2 : 2 * p ≤ n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    (c : ℝ) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghZoomCircDP hp2 hp hm false passes (fun R' ↦ c * Ψ R') R =
      c * ghZoomCircDP hp2 hp hm false passes Ψ R := by
  induction passes generalizing R with
  | nil => rfl
  | cons _ rest ih =>
    dsimp only [ghZoomCircDP]
    rw [funext ih, ghZoomSubsetStep_false_mul]
private lemma ghZoomCircDP_false_sum {ι : Type*} {n p m : ℕ}
    (hp2 : 2 * p ≤ n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    (s : Finset ι) (F : ι → Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghZoomCircDP hp2 hp hm false passes (fun R' ↦ ∑ i ∈ s, F i R') R =
      ∑ i ∈ s, ghZoomCircDP hp2 hp hm false passes (F i) R := by
  classical
  induction s using Finset.induction generalizing R with
  | empty =>
    have hzero :
        ∀ (l : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec))) (T : Finset (Fin (2 ^ n))),
          ghZoomCircDP hp2 hp hm false l (fun _ ↦ (0 : ℝ)) T = 0 := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons ps rest _ =>
        intro T
        have hm0 := ghZoomCircDP_false_mul hp2 hp hm (ps :: rest) 0 (fun _ ↦ 0) T
        simpa using hm0
    simpa using hzero passes R
  | @insert a s ha ihs =>
    have hadd : ∀ (l : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
        (A B : Finset (Fin (2 ^ n)) → ℝ) (T : Finset (Fin (2 ^ n))),
        ghZoomCircDP hp2 hp hm false l (fun R' ↦ A R' + B R') T =
          ghZoomCircDP hp2 hp hm false l A T + ghZoomCircDP hp2 hp hm false l B T := by
      intro l
      induction l with
      | nil => intro _ _ _; rfl
      | cons _ rest ihl =>
        intro A B T
        dsimp only [ghZoomCircDP]
        rw [funext (ihl A B), ghZoomSubsetStep_false_add]
    simp_rw [Finset.sum_insert ha]
    rw [hadd, ihs]
private lemma ghZoomCircDP_true_eq_cost_add_false {n p m : ℕ}
    (hp2 : 2 * p ≤ n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    (Ψ : Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghZoomCircDP hp2 hp hm true passes Ψ R =
      ghZoomCircDP hp2 hp hm true passes (fun _ ↦ 0) R +
        ghZoomCircDP hp2 hp hm false passes Ψ R := by
  induction passes generalizing R with
  | nil => simp [ghZoomCircDP]
  | cons _ rest ih =>
    dsimp only [ghZoomCircDP]
    rw [funext ih, ghZoomSubsetStep_true_eq_cost_add_false, ghZoomSubsetStep_false_add,
      ← add_assoc, ← ghZoomSubsetStep_true_eq_cost_add_false]
private lemma wp_ghZoomOnePass_of_finset {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk_eq : k = 2)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHZoomSpec)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ))
    {active : ℕ} (hact : active ≤ k) {τ : Store Var} (hτ : τ res = (active : ℤ))
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) :
    ((wp ((ghZoomOnePass res hm1 hk1 hkN hM hp2 hm2_pow hp hm perm spec_fn).compile qAssign
        (groverParallelMarkingOracle m S)) Θ) τ).1.1
        (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      (ghZoomSubsetStep (n - p) (n - 2 * p) (fun x ↦ subcubePref hp hm (perm x)) false spec_fn Ψ
        (S \ memSeen n k (memPrefix k active) μ) : ℂ) := by
  classical
  let pref := fun x ↦ subcubePref hp hm (perm x)
  unfold ghZoomOnePass ghZoomSubsetStep
  cases hsp2 : spec_fn 2 with
  | none =>
    dsimp only [compile, wp]
    exact hΘ active τ μ hact hτ hval
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only [compile]
    rw [wp_qIf]
    dsimp only
    by_cases hact0 : active = 0
    · subst hact0
      have hτ0 : τ res = 0 := by simpa using hτ
      have hseen0 : memSeen n k (memPrefix k 0) μ = ∅ := by
        ext x; simp [memSeen, memPrefix]
      have hRS : S \ memSeen n k (memPrefix k 0) μ = S := by
        rw [hseen0, Finset.sdiff_empty]
      have hR2 : (S \ memSeen n k (memPrefix k 0) μ).card = 2 := by
        rw [hRS, hcard, hk_eq]
      rw [ite_eq_left hτ0, ite_eq_left hR2, wp_qSeq]
      let postCirc : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
        .qIf (fun σ ↦ σ res = 1)
          (wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom) .skip
      have hΘ_post : ∀ (s : ℕ) (τ' : Store Var) (ν : Fin (2 ^ (k * n))),
          s ≤ k → τ' res = (s : ℤ) → MemPrefixValid S s ν →
            ((wp (postCirc.compile qAssign (groverParallelMarkingOracle m S)) Θ) τ').1.1
                (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
              (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom false (Set.InjOn pref (S : Set (Fin (2 ^ n)))) Ψ
                (S \ memSeen n k (memPrefix k s) ν) : ℂ) := by
        intro s τ' ν hs hτ' hval'
        dsimp only [postCirc, compile]
        rw [wp_qIf]
        dsimp only
        have hseen_card := (card_memSeen_of_memPrefixValid hval').1
        have hadd := Finset.card_sdiff_add_card_eq_card (card_memSeen_of_memPrefixValid hval').2
        by_cases hs1 : s = 1
        · subst hs1
          have hτ1 : τ' res = 1 := by simpa using hτ'
          rw [ite_eq_left hτ1]
          exact wp_wdZoomSubcubeRoundSlot_k2_of_finset res hm1 hk1 hk_eq hkN hp2 hm2_pow hp hm
            perm kZoom hcard Θ Ψ hΘ τ' hval'
        · have hτ_ne1 : τ' res ≠ 1 := by rw [hτ']; omega
          have hrc_ne1 : (S \ memSeen n k (memPrefix k s) ν).card ≠ 1 := by omega
          rw [ite_eq_right hτ_ne1]
          dsimp only [wp]
          rw [hΘ s τ' ν hs hτ' hval']
          unfold ghZoomPostΨ
          rw [ite_eq_right hrc_ne1]
      have hmain := wp_ghDeflatedRound_of_finset res hn hk1 hm1 hkN hM hp hm hsub3
        perm kInit probes hcard hk1 hval hR2
        (wp (postCirc.compile qAssign (groverParallelMarkingOracle m S)) Θ)
        (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom false (Set.InjOn pref (S : Set (Fin (2 ^ n)))) Ψ)
        hΘ_post τ
      dsimp only [postCirc, compile] at hmain
      rw [hmain, hRS]
      unfold ghZoomBaseStep
      by_cases hInj : Set.InjOn pref (S : Set (Fin (2 ^ n)))
      · rw [ite_eq_left hInj, ite_eq_left hInj]
        dsimp only [pref]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      · rw [ite_eq_right hInj, ite_eq_right hInj]
        dsimp only [pref]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    · have hτ_ne0 : τ res ≠ 0 := by rw [hτ]; omega
      have hseen_card := (card_memSeen_of_memPrefixValid hval).1
      have hadd := Finset.card_sdiff_add_card_eq_card (card_memSeen_of_memPrefixValid hval).2
      have hR_ne2 : (S \ memSeen n k (memPrefix k active) μ).card ≠ 2 := by omega
      rw [ite_eq_right hτ_ne0, ite_eq_right hR_ne2]
      dsimp only [wp]
      exact hΘ active τ μ hact hτ hval
private lemma wp_ghZoomSweeps_of_finset {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk_eq : k = 2)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ))
    {active : ℕ} (hact : active ≤ k) {τ : Store Var} (hτ : τ res = (active : ℤ))
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) :
    ((wp ((ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
        (groverParallelMarkingOracle m S)) Θ) τ).1.1
        (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      (ghZoomCircDP hp2 hp hm false passes Ψ (S \ memSeen n k (memPrefix k active) μ) : ℂ) := by
  induction passes generalizing active τ μ with
  | nil => exact hΘ active τ μ hact hτ hval
  | cons ps rest ih =>
    rcases ps with ⟨perm, spec_fn⟩
    dsimp only [ghZoomSweeps, ghZoomCircDP, compile]
    rw [wp_qSeq]
    exact wp_ghZoomOnePass_of_finset res hn hk1 hk_eq hm1 hkN hM hp2 hm2_pow hp hm hsub3
      perm spec_fn hcard
      (wp ((ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm rest).compile qAssign
        (groverParallelMarkingOracle m S)) Θ)
      (ghZoomCircDP hp2 hp hm false rest Ψ)
      (fun s τ' ν hs hτ' hval' ↦ ih hs hτ' hval')
      hact hτ hval
private lemma wp_qSet_measure_whole_apply_mat_gh {Var : Type} [DecidableEq Var] (res : Var)
    (Q : ℕ) (Φ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    ((wp (.qSet ;; measureRegister res (QRegister.whole Q)) Φ) σ).1.1 =
      ((Φ (Store.subst σ res 0)).1.1 0 0) • (1 : Operator (2 ^ Q)) := by
  rw [wp_qSeq, wp_qSet, qhlQSet_val, wp_measureRegister]
  congr 1
  have hsum :
      (∑ o : Fin (2 ^ Q),
        (QRegister.whole Q).basisOutcomeProjector o *
          (Φ (Store.subst σ res (Int.ofNat o.val))).1.1 *
          (QRegister.whole Q).basisOutcomeProjector o) =
      ∑ o : Fin (2 ^ Q),
        ((Φ (Store.subst σ res (Int.ofNat o.val))).1.1 o o) • compProj o := by
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [QRegister.basisOutcomeProjector, QRegister.whole_embedMatrix, compProj_mul_mul]
  rw [hsum, Matrix.sum_apply,
    sum_eq_single (0 : Fin (2 ^ Q)) (fun o ho ↦ by simp [compProj_apply, ho.symm])]
  simp [compProj_apply]
private lemma wp_qSet_measure_lowBlock_apply_mat_gh {Var : Type} [DecidableEq Var] (res : Var)
    (W M : ℕ) (Φ : CQAssertion (Store Var) (2 ^ (W + M))) (σ : Store Var) :
    ((wp (.qSet ;; measureRegister res (lowBlock W M)) Φ) σ).1.1 =
      ((Φ (Store.subst σ res 0)).1.1 0 0) • (1 : Operator (2 ^ (W + M))) := by
  rw [wp_qSeq, wp_qSet, qhlQSet_val, wp_measureRegister]
  congr 1
  refine (diag_eq_star_single_dotProduct_mulVec _ 0).trans ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  have hproj (o : Fin (2 ^ W)) :
      (lowBlock W M).basisOutcomeProjector o *ᵥ single (0 : Fin (2 ^ (W + M))) 1 =
        if o = 0 then single 0 1 else 0 := by
    rw [QRegister.basisOutcomeProjector, ← workMemState_zero W M,
      embedMatrix_lowBlock_mulVec_workMemState, compProj_mulVec]
    by_cases ho : o = 0
    · subst ho; rw [ite_eq_left rfl, Pi.single_eq_same, workMemState_zero]
    · rw [ite_eq_right ho, Pi.single_eq_of_ne ho, Pi.single_zero]
      funext z; simp [workMemState]
  rw [sum_eq_single 0 (fun o ho ↦ by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj o, ite_eq_right ho,
      Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero])]
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj 0, ite_eq_left rfl,
    Matrix.dotProduct_mulVec, ← QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.vecMul_conjTranspose, star_star, hproj 0, ite_eq_left rfl]
  refine (diag_eq_star_single_dotProduct_mulVec _ 0).symm.trans ?_
  simp [HermitianMat.val_eq_coe]
private lemma wp_qSet_ghZoomMultiSweepPre_of_invariant {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk_eq : k = 2)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (f : ℕ → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (f s : ℂ))
    (σ : Store Var) :
    ((wp (.qSet ;;
        (ghZoomMultiSweepPre res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
      (ghZoomCircDP hp2 hp hm false passes (fun R ↦ f (k - R.card)) S : ℂ) •
        (1 : Operator (2 ^ (m * (n + 1) + k * n))) := by
  dsimp only [ghZoomMultiSweepPre, compile]
  have hassoc :
      wp (.qSet ;;
          (measureRegister res (QRegister.whole (m * (n + 1) + k * n)) ;;
            .qIf (fun σ ↦ σ res = 0)
              ((ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
                (groverParallelMarkingOracle m S))
              .skip)) Θ =
        wp (.qSet ;; measureRegister res (QRegister.whole (m * (n + 1) + k * n)))
          (wp (.qIf (fun σ ↦ σ res = 0)
            ((ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
              (groverParallelMarkingOracle m S))
            .skip) Θ) := by
    simp only [wp_qSeq]
  have hs0 : (Store.subst σ res 0) res = 0 := by simp [Store.subst]
  have hif0 :
      wp (.qIf (fun τ ↦ τ res = 0)
          ((ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
            (groverParallelMarkingOracle m S))
          .skip) Θ (Store.subst σ res 0) =
        wp ((ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
          (groverParallelMarkingOracle m S)) Θ (Store.subst σ res 0) := by
    rw [wp_qIf]; exact ite_eq_left hs0
  have hΘ_fin : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν →
        (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
          (f (k - (S \ memSeen n k (memPrefix k s) ν).card) : ℂ) := by
    intro s τ ν hs hτ hval
    have hseen := (card_memSeen_of_memPrefixValid hval).1
    have hadd := Finset.card_sdiff_add_card_eq_card (card_memSeen_of_memPrefixValid hval).2
    have hsub_eq : k - (S \ memSeen n k (memPrefix k s) ν).card = s := by omega
    rw [hsub_eq]
    exact hΘ s τ ν hs hτ hval
  have hseen0 : memSeen n k (memPrefix k 0) (0 : Fin (2 ^ (k * n))) = ∅ := by
    ext x; simp [memSeen, memPrefix]
  rw [hassoc, wp_qSet_measure_whole_apply_mat_gh, hif0, ← workMemIdx_zero n m k,
    wp_ghZoomSweeps_of_finset res hn hk1 hk_eq hm1 hkN hM hp2 hm2_pow hp hm hsub3
      passes hcard Θ (fun R ↦ f (k - R.card)) hΘ_fin (Nat.zero_le k) hs0 (memPrefixValid_zero S),
    hseen0, Finset.sdiff_empty]
private noncomputable def ghZoomOccLaw {n p m k : ℕ}
    (hp2 : 2 * p ≤ n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    (S : Finset (Fin (2 ^ n))) (s : ℕ) : ℝ :=
  ghZoomCircDP hp2 hp hm false passes (fun R ↦ if k - R.card = s then 1 else 0) S
private lemma ghZoomOccLaw_props {n p m k : ℕ}
    (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk_eq : k = 2)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    (∀ s, 0 ≤ ghZoomOccLaw (k := k) hp2 hp hm passes S s) ∧
    (∑ s ∈ Finset.range (k + 1), ghZoomOccLaw (k := k) hp2 hp hm passes S s = 1) ∧
    (∀ f : ℕ → ℝ,
      (∑ s ∈ Finset.range (k + 1), ghZoomOccLaw (k := k) hp2 hp hm passes S s * f s) =
        ghZoomCircDP hp2 hp hm false passes (fun R ↦ f (k - R.card)) S) := by
  have hnn : ∀ s, 0 ≤ ghZoomOccLaw (k := k) hp2 hp hm passes S s := fun s ↦
    ghZoomCircDP_nonneg hp2 hp hm false passes fun R _ ↦ by split_ifs <;> norm_num
  have hexp : ∀ f : ℕ → ℝ,
      (∑ s ∈ Finset.range (k + 1), ghZoomOccLaw (k := k) hp2 hp hm passes S s * f s) =
        ghZoomCircDP hp2 hp hm false passes (fun R ↦ f (k - R.card)) S := by
    intro f
    have h_occ_s (s : ℕ) :
        ghZoomOccLaw (k := k) hp2 hp hm passes S s * f s =
          ghZoomCircDP hp2 hp hm false passes
            (fun R ↦ f s * (if k - R.card = s then 1 else 0)) S := by
      unfold ghZoomOccLaw
      rw [mul_comm, ← ghZoomCircDP_false_mul]
    simp_rw [h_occ_s, ← ghZoomCircDP_false_sum]
    have hfun :
        (fun R : Finset (Fin (2 ^ n)) ↦
          ∑ x ∈ Finset.range (k + 1), f x * if k - R.card = x then 1 else 0) =
        fun R ↦ f (k - R.card) := by
      funext R
      have hmem : k - R.card ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (k - R.card)
        (fun s _ hne ↦ by rw [ite_eq_right hne.symm, mul_zero])
        (fun hnot ↦ absurd hmem hnot)]
      simp
    rw [hfun]
  refine ⟨hnn, ?_, hexp⟩
  rw [show (∑ s ∈ Finset.range (k + 1), ghZoomOccLaw (k := k) hp2 hp hm passes S s) =
      ∑ s ∈ Finset.range (k + 1), ghZoomOccLaw (k := k) hp2 hp hm passes S s * 1 by simp,
    hexp (fun _ ↦ 1)]
  have htop := wp_qSet_ghZoomMultiSweepPre_of_invariant (Var := Unit) ()
    hn hk1 hk_eq hm1 hkN hM hp2 hm2_pow hp hm hsub3 passes hcard ⊤ (fun _ ↦ 1)
    (fun _ _ _ _ _ _ ↦ by simp [HermitianMat.val_eq_coe]) (fun _ ↦ 0)
  have hwp_top :
      wp (.qSet ;;
        (ghZoomMultiSweepPre () hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
          (groverParallelMarkingOracle m S))
        (⊤ : CQAssertion (Store Unit) (2 ^ (m * (n + 1) + k * n))) = ⊤ := by
    have hpre_top :
        IsWpTopGH (ghZoomMultiSweepPre (Var := Unit) () hm1 hk1 hkN hM
          hp2 hm2_pow hp hm passes) :=
      isWpTopGH_seq (isWpTopGH_measure _ _)
        (isWpTopGH_qIf _
          (isWpTopGH_ghZoomSweeps () hm1 hk1 hkN hM hp2 hm2_pow hp hm passes)
          isWpTopGH_skip)
    rw [wp_qSeq, hpre_top (groverParallelMarkingOracle m S)]
    funext σ
    apply Subtype.ext; apply HermitianMat.ext
    rw [wp_qSet, ← HermitianMat.val_eq_coe, qhlQSet_val]
    simp [HermitianMat.val_eq_coe]
  rw [hwp_top] at htop
  have h00 := congrFun (congrFun htop 0) 0
  simp only [HermitianMat.val_eq_coe, Matrix.one_apply_eq,
    Matrix.smul_apply, smul_eq_mul, mul_one] at h00
  exact Complex.ofReal_injective h00.symm
private def ghZoomRoundMaxQ : GHZoomSpec → ℕ
  | none => 0
  | some (kInit, probes, kZoom) => ghZoomMaxQueries kInit probes kZoom
private lemma scaledCostRel_ghZoomOnePass {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk_eq : k = 2)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (perm : Equiv.Perm (Fin (2 ^ n))) (spec_fn : ℕ → GHZoomSpec)
    (S : Finset (Fin (2 ^ n))) {M_step B : ℝ} (hM_step : 0 ≤ M_step) (hB : 0 < B)
    (hcB : M_step ≤ B)
    (hspec_le : ∀ r ≤ k, (ghZoomRoundMaxQ (spec_fn r) : ℝ) ≤ M_step) :
    ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)),
      ScaledCostRel (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B
        ((ghZoomOnePass res hm1 hk1 hkN hM hp2 hm2_pow hp hm perm spec_fn).compile qAssign
          (groverParallelMarkingOracle m S))
        θ M_step ∧
      (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
        S.card = k → s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
            ((ghZoomSubsetStep (n - p) (n - 2 * p) (fun x ↦ subcubePref hp hm (perm x))
              true spec_fn (fun _ ↦ 0) (S \ memSeen n k (memPrefix k s) μ) / B : ℝ) : ℂ)) := by
  classical
  let W := m * (n + 1)
  let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hrel_skip : ScaledCostRel model B
      ((OracleDynamicCircuit.skip : OracleCirc Var (W + M) ((n + 1) * m)).compile qAssign oracle)
      ⊥ M_step :=
    ghScaledCostRel_mono_c hB (ghScaledCostRel_of_zero hB (CostBound.skip_zero model)) hM_step hcB
  unfold ghZoomOnePass ghZoomSubsetStep
  cases hsp2 : spec_fn 2 with
  | none =>
    refine ⟨⊥, hrel_skip, fun _ _ _ _ _ _ _ ↦ ?_⟩
    simp [HermitianMat.val_eq_coe]
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    have hm2_le : ((ghZoomMaxQueries kInit probes kZoom : ℕ) : ℝ) ≤ M_step := by
      have h2 := hspec_le 2 (by omega)
      simpa [ghZoomRoundMaxQ, hsp2] using h2
    let c₁ : ℝ := (ghMaxQueries kInit probes : ℝ)
    let c₂ : ℝ := ((kZoom + 1 : ℕ) : ℝ)
    have hc₁_nn : 0 ≤ c₁ := Nat.cast_nonneg _
    have hc₂_nn : 0 ≤ c₂ := Nat.cast_nonneg _
    have hc₁₂_eq : c₁ + c₂ = ((ghZoomMaxQueries kInit probes kZoom : ℕ) : ℝ) := by
      dsimp only [c₁, c₂, ghZoomMaxQueries]
      push_cast
      ring
    have hc₁₂_M : c₁ + c₂ ≤ M_step := hc₁₂_eq.trans_le hm2_le
    have hc₁₂_B : c₁ + c₂ ≤ B := hc₁₂_M.trans hcB
    have hc₁_B : c₁ ≤ B := by linarith
    have hc₂_B : c₂ ≤ B := by linarith
    rcases scaledCostRel_ghDeflatedRound (Var := Var) res hm1 hkN hM hp hm hsub3 perm S
      kInit probes hB hc₁_B with ⟨θ₁, hrel₁_0, hdiag₁⟩
    have hrel₁ : ScaledCostRel model B
        ((ghDeflatedRound res hm1 hkN hM hp hm perm 0 kInit
          ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes).compile qAssign oracle)
        θ₁ c₁ :=
      ghScaledCostRel_mono_c hB hrel₁_0 le_rfl hc₁_B
    have hcb_zoom := costBound_wdZoomSubcubeRoundSlot (Var := Var) res hm1 hkN
      hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom S
    have hrel_zoom : ScaledCostRel model B
        ((wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom).compile
          qAssign oracle)
        (constAssertion (c₂ / B)) c₂ := by
      simpa [c₂] using ghScaledCostRel_of_costBound hB hcb_zoom (by simpa [c₂] using hc₂_B)
    let postCirc : OracleCirc Var (W + M) ((n + 1) * m) :=
      .qIf (fun σ ↦ σ res = 1)
        (wdZoomSubcubeRoundSlot res hm1 hkN hp2 hm2_pow hp hm perm ⟨0, hk1⟩ 1 kZoom) .skip
    let θ_post : CQAssertion (Store Var) (2 ^ (W + M)) :=
      fun σ ↦ if σ res = 1 then constAssertion (c₂ / B) σ else ⊥
    have hrel_post : ScaledCostRel model B (postCirc.compile qAssign oracle) θ_post c₂ :=
      ghScaledCostRel_mono_c hB
        (ghScaledCostRel_qIf hB (fun σ ↦ σ res = 1) hrel_zoom
          (ghScaledCostRel_of_zero hB (CostBound.skip_zero model)))
        (le_of_eq (max_eq_left hc₂_nn)) hc₂_B
    have hrel_then : ScaledCostRel model B
        ((OracleDynamicCircuit.seq
          (ghDeflatedRound res hm1 hkN hM hp hm perm 0 kInit
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes)
          postCirc).compile qAssign oracle)
        (θ₁.add
          (wp ((ghDeflatedRound res hm1 hkN hM hp hm perm 0 kInit
            ghProbeWSpec2 (fun pr ↦ pr.2.2.2) probes).compile qAssign oracle) θ_post)
          (ghScaledCostRel_add_le hB hrel₁ hrel_post hc₁₂_B))
        M_step :=
      ghScaledCostRel_mono_c hB
        (ghScaledCostRel_seq hB hrel₁ hrel_post hc₁₂_B) hc₁₂_M hcB
    have hrel_pass := ghScaledCostRel_mono_c hB
      (ghScaledCostRel_qIf hB (fun σ ↦ σ res = 0) hrel_then hrel_skip)
      (le_of_eq (max_self M_step)) hcB
    refine ⟨_, hrel_pass, fun s τ μ hcard hs hτ hval ↦ ?_⟩
    dsimp only
    by_cases hs0 : s = 0
    · subst hs0
      have hτ0 : τ res = 0 := by simpa using hτ
      have hseen0 : memSeen n k (memPrefix k 0) μ = ∅ := by
        ext x; simp [memSeen, memPrefix]
      have hRS : S \ memSeen n k (memPrefix k 0) μ = S := by
        rw [hseen0, Finset.sdiff_empty]
      have hS2 : S.card = 2 := by rw [hcard, hk_eq]
      have hR2 : (S \ memSeen n k (memPrefix k 0) μ).card = 2 := by rw [hRS, hS2]
      rw [ite_eq_left hτ0, ite_eq_left hR2, gh_cqAssertion_add_mat, Matrix.add_apply,
        hdiag₁ μ τ hcard hk1 hval hR2]
      have hΘ_post : ∀ (s' : ℕ) (τ' : Store Var) (ν : Fin (2 ^ (k * n))),
          s' ≤ k → τ' res = (s' : ℤ) → MemPrefixValid S s' ν →
            (θ_post τ').1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) =
              ((ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0)
                (S \ memSeen n k (memPrefix k s') ν) / B : ℝ) : ℂ) := by
        intro s' τ' ν hs' hτ' hval'
        have hseen_card := (card_memSeen_of_memPrefixValid hval').1
        have hadd := Finset.card_sdiff_add_card_eq_card (card_memSeen_of_memPrefixValid hval').2
        dsimp only [θ_post]
        by_cases hs1 : s' = 1
        · subst hs1
          have hτ1 : τ' res = 1 := by simpa using hτ'
          have hrc1 : (S \ memSeen n k (memPrefix k 1) ν).card = 1 := by omega
          rw [ite_eq_left hτ1, HermitianMat.val_eq_coe, constAssertion_apply_of_bounds (c₂ / B)
              (div_nonneg hc₂_nn hB.le) ((div_le_one hB).mpr hc₂_B)]
          unfold ghZoomPostΨ
          rw [ite_eq_left hrc1]
          by_cases hInj : Set.InjOn pref (S : Set (Fin (2 ^ n))) <;>
            simp [hInj, c₂, Complex.real_smul]
        · have hτ_ne1 : τ' res ≠ 1 := by rw [hτ']; omega
          have hrc_ne1 : (S \ memSeen n k (memPrefix k s') ν).card ≠ 1 := by omega
          rw [ite_eq_right hτ_ne1]
          unfold ghZoomPostΨ
          rw [ite_eq_right hrc_ne1]
          simp [HermitianMat.val_eq_coe]
      have hwp_post := wp_ghDeflatedRound_of_finset res hn hk1 hm1 hkN hM hp hm hsub3
        perm kInit probes hcard hk1 hval hR2 θ_post
        (fun R' ↦ ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
          (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0) R' / B)
        hΘ_post τ
      rw [hwp_post, hRS]
      have hdiv_step :
          ghZoomBaseStep (n - p) pref false kInit probes
              (fun R' ↦ ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0) R' / B) S =
            ghZoomBaseStep (n - p) pref false kInit probes
              (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0)) S / B := by
        simpa [div_eq_inv_mul] using
          ghZoomBaseStep_false_mul (n - p) pref kInit probes (1 / B)
            (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
              (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0)) S
      have hrhs_base :
          ((if Set.InjOn pref (S : Set (Fin (2 ^ n))) then
              let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
              let u₀ := ghInitAmp2 θ₁ kInit
              let uf := ghChainFinalAmp2 θ₁ probes u₀
              ((ghChainClickProb2 θ₁ probes u₀ *
                  (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                    (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0)
                    (∅ : Finset (Fin (2 ^ n))) / B) +
                ∑ B_sub ∈ S.powerset, normSq (uf B_sub.card) *
                  (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                    (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0) (S \ B_sub) / B) : ℝ) : ℂ)
            else
              let θ₂ := Real.arcsin (√2 / √(2 ^ (n - p) : ℝ))
              let z₀ := ghInitColl2 θ₂ kInit
              let zf := ghChainFinalColl2 θ₂ probes z₀
              ((normSq zf.1 *
                  (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                    (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0) S / B) +
                normSq zf.2 * ∑ x ∈ S, (1 / 2 : ℝ) *
                  (ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                    (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0) (S \ {x}) / B) :
                ℝ) : ℂ))) =
          ((ghZoomBaseStep (n - p) pref false kInit probes
              (fun R' ↦ ghZoomPostΨ (2 ^ (n - 2 * p)) kZoom true
                (Set.InjOn pref (S : Set (Fin (2 ^ n)))) (fun _ ↦ 0) R' / B) S : ℝ) : ℂ) := by
        unfold ghZoomBaseStep
        by_cases hInj : Set.InjOn pref (S : Set (Fin (2 ^ n))) <;>
          simp [hInj]
      rw [hrhs_base, hdiv_step]
      conv_rhs => rw [ghZoomBaseStep_true_eq_cost_add_false]
      unfold ghZoomBaseStep
      by_cases hInj : Set.InjOn pref (S : Set (Fin (2 ^ n)))
      · rw [ite_eq_left hInj, ite_eq_left hInj, ite_eq_left hInj]
        simp only [↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero]
        push_cast; ring
      · rw [ite_eq_right hInj, ite_eq_right hInj, ite_eq_right hInj]
        simp only [↓reduceIte, Bool.false_eq_true, mul_zero, Finset.sum_const_zero]
        push_cast; ring
    · have hτ_ne0 : τ res ≠ 0 := by rw [hτ]; omega
      have hseen_card := (card_memSeen_of_memPrefixValid hval).1
      have hadd := Finset.card_sdiff_add_card_eq_card (card_memSeen_of_memPrefixValid hval).2
      have hR_ne2 : (S \ memSeen n k (memPrefix k s) μ).card ≠ 2 := by omega
      rw [ite_eq_right hτ_ne0, ite_eq_right hR_ne2]
      simp [HermitianMat.val_eq_coe]
private lemma scaledCostRel_ghZoomSweeps {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk_eq : k = 2)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    (S : Finset (Fin (2 ^ n))) {M_step B : ℝ} (hM_step : 0 ≤ M_step) (hB : 0 < B)
    (hcB : (passes.length : ℝ) * M_step ≤ B)
    (hspec_le : ∀ ps ∈ passes, ∀ r ≤ k, (ghZoomRoundMaxQ (ps.2 r) : ℝ) ≤ M_step) :
    ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)),
      ScaledCostRel (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B
        ((ghZoomSweeps res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
          (groverParallelMarkingOracle m S))
        θ ((passes.length : ℝ) * M_step) ∧
      (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
        S.card = k → s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
            ((ghZoomCircDP hp2 hp hm true passes (fun _ ↦ 0)
                (S \ memSeen n k (memPrefix k s) μ) / B : ℝ) : ℂ)) := by
  let W := m * (n + 1)
  let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  induction passes with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, zero_mul]
    refine ⟨⊥, ghScaledCostRel_of_zero hB (CostBound.skip_zero model), fun _ _ _ _ _ _ _ ↦ ?_⟩
    simp [ghZoomCircDP, HermitianMat.val_eq_coe]
  | cons ps rest ih =>
    rcases ps with ⟨perm, spec_fn⟩
    have hc_eq : (((perm, spec_fn) :: rest).length : ℝ) * M_step =
        M_step + (rest.length : ℝ) * M_step := by
      simp [List.length_cons, add_mul]
      ring
    have hc_rest_B : (rest.length : ℝ) * M_step ≤ B := by linarith
    have hc_head_B : M_step ≤ B := by
      have : 0 ≤ (rest.length : ℝ) * M_step := mul_nonneg (Nat.cast_nonneg _) hM_step
      linarith
    rcases ih hc_rest_B (fun q hq r hr ↦ hspec_le q (List.mem_cons_of_mem _ hq) r hr) with
      ⟨θ_rest, hrel_rest, hdiag_rest⟩
    rcases scaledCostRel_ghZoomOnePass (Var := Var) res hn hk1 hk_eq hm1 hkN hM
      hp2 hm2_pow hp hm hsub3 perm spec_fn S hM_step hB hc_head_B
      (hspec_le (perm, spec_fn) List.mem_cons_self) with ⟨θ_sw, hrel_sw, hdiag_sw⟩
    have hsum_B : M_step + (rest.length : ℝ) * M_step ≤ B := by linarith
    have hrel_tot := ghScaledCostRel_mono_c hB
      (ghScaledCostRel_seq hB hrel_sw hrel_rest hsum_B)
      (le_of_eq hc_eq.symm) hcB
    refine ⟨_, hrel_tot, fun s τ μ hcard hs hτ hval ↦ ?_⟩
    rw [gh_cqAssertion_add_mat, Matrix.add_apply, hdiag_sw s τ μ hcard hs hτ hval,
      wp_ghZoomOnePass_of_finset res hn hk1 hk_eq hm1 hkN hM hp2 hm2_pow hp hm hsub3
        perm spec_fn hcard θ_rest (fun R' ↦ ghZoomCircDP hp2 hp hm true rest (fun _ ↦ 0) R' / B)
        (fun s' τ' ν hs' hτ' hval' ↦ hdiag_rest s' τ' ν hcard hs' hτ' hval') hs hτ hval]
    have hdiv_step :
        ghZoomSubsetStep (n - p) (n - 2 * p) (fun x ↦ subcubePref hp hm (perm x)) false spec_fn
            (fun R' ↦ ghZoomCircDP hp2 hp hm true rest (fun _ ↦ 0) R' / B)
            (S \ memSeen n k (memPrefix k s) μ) =
          ghZoomSubsetStep (n - p) (n - 2 * p) (fun x ↦ subcubePref hp hm (perm x)) false spec_fn
            (ghZoomCircDP hp2 hp hm true rest (fun _ ↦ 0))
            (S \ memSeen n k (memPrefix k s) μ) / B := by
      simpa [div_eq_inv_mul] using
        ghZoomSubsetStep_false_mul (n - p) (n - 2 * p) (fun x ↦ subcubePref hp hm (perm x))
          spec_fn (1 / B) (ghZoomCircDP hp2 hp hm true rest (fun _ ↦ 0))
          (S \ memSeen n k (memPrefix k s) μ)
    rw [hdiv_step]
    dsimp only [ghZoomCircDP]
    conv_rhs => rw [ghZoomSubsetStep_true_eq_cost_add_false]
    push_cast
    ring
private lemma expectedCost_and_bound_ghZoomMultiSweepPre {Var : Type} [DecidableEq Var] (res : Var)
    {n p m k : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hk_eq : k = 2)
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n)
    (hp2 : 2 * p ≤ n) (hm2_pow : m * m = 2 ^ (2 * p))
    (hp : p ≤ n) (hm : m = 2 ^ p) (hsub3 : 3 ≤ 2 ^ (n - p))
    (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → GHZoomSpec)))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    {M_step : ℝ} (hM_pos : 0 < M_step)
    (hspec_le : ∀ ps ∈ passes, ∀ r ≤ k, (ghZoomRoundMaxQ (ps.2 r) : ℝ) ≤ M_step) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((ghZoomMultiSweepPre res hm1 hk1 hkN hM hp2 hm2_pow hp hm passes).compile qAssign
        (groverParallelMarkingOracle m S))
      (Real.toNNReal (ghZoomCircDP hp2 hp hm true passes (fun _ ↦ 0) S)) ∧
    ghZoomCircDP hp2 hp hm true passes (fun _ ↦ 0) S ≤ (passes.length : ℝ) * M_step := by
  let W := m * (n + 1)
  let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  let c₀ := ghZoomCircDP hp2 hp hm true passes (fun _ ↦ 0) S
  have hc0_nn : 0 ≤ c₀ := ghZoomCircDP_nonneg hp2 hp hm true passes fun _ _ ↦ le_rfl
  have hseen0 : memSeen n k (memPrefix k 0) (0 : Fin (2 ^ (k * n))) = ∅ := by
    ext x; simp [memSeen, memPrefix]
  have hbnd_top : c₀ ≤ (passes.length : ℝ) * M_step := by
    by_cases hnil : passes = []
    · subst hnil; simp [c₀, ghZoomCircDP]
    · have hlen_pos : 0 < (passes.length : ℝ) := by exact_mod_cast List.length_pos_iff.mpr hnil
      set B2 : ℝ := (passes.length : ℝ) * M_step
      have hB2 : 0 < B2 := mul_pos hlen_pos hM_pos
      rcases scaledCostRel_ghZoomSweeps (Var := Unit) () hn hk1 hk_eq hm1 hkN hM
        hp2 hm2_pow hp hm hsub3 passes S hM_pos.le hB2 le_rfl hspec_le with ⟨θ_sw2, _, hdiag_sw2⟩
      let O : Observable (Fin (2 ^ (W + M))) :=
        wp (.qSet ;; measureRegister () (lowBlock W M)) θ_sw2 (fun _ ↦ 0)
      have hO_mat : O.1.1 = diagonal (fun _ ↦ ((c₀ / B2 : ℝ) : ℂ)) := by
        dsimp only [O, c₀]
        rw [wp_qSet_measure_lowBlock_apply_mat_gh, ← workMemIdx_zero n m k,
          hdiag_sw2 0 (Store.subst (fun _ ↦ 0) () 0) 0 hcard (Nat.zero_le k)
            (by simp [Store.subst]) (memPrefixValid_zero S), hseen0, Finset.sdiff_empty]
        ext z₁ z₂
        by_cases hz : z₁ = z₂ <;> simp [hz]
      have hbnd := (observable_diag_real_bounds O _ hO_mat 0).2.2
      simp only [Complex.ofReal_re] at hbnd
      exact (div_le_one hB2).mp hbnd
  refine ⟨fun Δ ↦ ?_, hbnd_top⟩
  have hmeas_cb : CostBound (Var := Var) model
      (measureRegister res (QRegister.whole (W + M))) 0 := by
    simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) model res
        ((QRegister.whole (W + M)).computationalBasisMeasurement :
          Measurement (2 ^ (W + M)) (2 ^ (W + M)))
  set B1 : ℝ := (passes.length : ℝ) * M_step + 1
  have hB1 : 0 < B1 := by positivity
  have hc0_B1 : c₀ ≤ B1 := by dsimp [B1]; linarith
  have hdiv0 : 0 ≤ c₀ / B1 := div_nonneg hc0_nn hB1.le
  have hdiv1 : c₀ / B1 ≤ 1 := (div_le_one hB1).mpr hc0_B1
  rcases scaledCostRel_ghZoomSweeps (Var := Var) res hn hk1 hk_eq hm1 hkN hM
    hp2 hm2_pow hp hm hsub3 passes S hM_pos.le hB1 (by dsimp [B1]; linarith) hspec_le with
    ⟨θ_sw1, hrel_sw1, hdiag_sw1⟩
  have hrel_if := ghScaledCostRel_qIf hB1 (fun τ ↦ τ res = 0) hrel_sw1
    (ghScaledCostRel_of_zero hB1 (CostBound.skip_zero model))
  have hrel_pre1 := ghScaledCostRel_seq_zero_left hB1 hmeas_cb hrel_if
  let θ_if : CQAssertion (Store Var) (2 ^ (W + M)) :=
    fun σ ↦ if σ res = 0 then θ_sw1 σ else (⊥ : CQAssertion (Store Var) (2 ^ (W + M))) σ
  have hθ_le : wp (measureRegister res (QRegister.whole (W + M))) θ_if ≤
      constAssertion (c₀ / B1) := by
    intro σ
    apply Subtype.coe_le_coe.mp
    rw [constAssertion_apply_of_bounds _ hdiv0 hdiv1]
    let p0 : HermitianMat (Fin (2 ^ (W + M))) ℂ :=
      ⟨compProj (0 : Fin (2 ^ (W + M))), compProj_isHermitian _⟩
    have hp0_mat : p0.mat = compProj (0 : Fin (2 ^ (W + M))) := rfl
    have hθ_eq : ((wp (measureRegister res (QRegister.whole (W + M))) θ_if) σ).1 =
        (c₀ / B1) • p0 := by
      apply HermitianMat.ext
      rw [← HermitianMat.val_eq_coe, wp_measureRegister, HermitianMat.mat_smul, hp0_mat]
      have hsum :
          (∑ o : Fin (2 ^ (W + M)),
            (QRegister.whole (W + M)).basisOutcomeProjector o *
              (θ_if (Store.subst σ res (Int.ofNat o.val))).1.1 *
              (QRegister.whole (W + M)).basisOutcomeProjector o) =
          ((c₀ / B1 : ℝ) : ℂ) • compProj (0 : Fin (2 ^ (W + M))) := by
        rw [sum_eq_single (0 : Fin (2 ^ (W + M))) (fun o ho ↦ by
          have hv : (o.val : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.val_ne_of_ne ho)
          have ho_ne : (Store.subst σ res (Int.ofNat o.val)) res ≠ 0 := by
            simpa [Store.subst] using hv
          dsimp only [θ_if]
          rw [ite_eq_right ho_ne]
          change _ * 0 * _ = 0
          simp)]
        have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ (W + M))).val)) res = 0 := by
          simp [Store.subst]
        dsimp only [θ_if]
        rw [ite_eq_left hs0, QRegister.basisOutcomeProjector, QRegister.whole_embedMatrix,
          compProj_mul_mul]
        have h0_eq : Store.subst σ res (Int.ofNat (0 : Fin (2 ^ (W + M))).val) =
            Store.subst σ res 0 := rfl
        rw [h0_eq, ← workMemIdx_zero n m k,
          hdiag_sw1 0 (Store.subst σ res 0) 0 hcard (Nat.zero_le k)
            (by simp [Store.subst]) (memPrefixValid_zero S), hseen0, Finset.sdiff_empty]
      rw [hsum]
      ext i j
      simp [Complex.real_smul]
    rw [hθ_eq]
    have hp0_le : p0 ≤ 1 := compProj_le_one 0
    exact smul_le_smul_of_nonneg_left hp0_le hdiv0
  refine (hrel_pre1.2.2.2 Δ).trans ?_
  have hexp_le : 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if] ≤
      (c₀ / B1) * Δ.trace := by
    calc 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if]
        ≤ 𝔼[Δ, constAssertion (c₀ / B1)] := expect_mono le_rfl hθ_le
      _ = (c₀ / B1) * Δ.trace := gh_expect_constAssertion Δ hdiv0 hdiv1
  have hmul_le : B1 * 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if] ≤
      Δ.trace * c₀ := by
    calc B1 * 𝔼[Δ, wp (measureRegister res (QRegister.whole (W + M))) θ_if]
        ≤ B1 * ((c₀ / B1) * Δ.trace) := mul_le_mul_of_nonneg_left hexp_le hB1.le
      _ = Δ.trace * c₀ := by rw [← mul_assoc, mul_div_cancel₀ _ hB1.ne', mul_comm]
  refine (ENNReal.ofReal_le_ofReal hmul_le).trans ?_
  rw [ENNReal.ofReal_mul Δ.trace.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ← Real.coe_toNNReal c₀ hc0_nn, ENNReal.ofReal_coe_nnreal]
private noncomputable def ghZoomSubsetDP {α : Type*} [DecidableEq α] {W m : ℕ}
    (subN p : ℕ) (slices : α → Fin W → Fin m) :
    List (Fin W × (ℕ → GHZoomSpec)) → (Finset α → ℝ) → Finset α → ℝ
  | [], Ψ, R => Ψ R
  | (t, spec_fn) :: rest, Ψ, R =>
      ghZoomSubsetStep subN (subN - p) (fun x ↦ slices x t) true spec_fn
        (ghZoomSubsetDP subN p slices rest Ψ) R
private noncomputable def ghZoomPostCard (subDimZoom kZoom : ℕ) (injS : Bool)
    (g : ℕ → ℝ) (u : ℕ) : ℝ :=
  if u = 1 then
    ((kZoom + 1 : ℕ) : ℝ) +
      if injS then g 1
      else p_succ_frac kZoom 1 subDimZoom * g 0 + (1 - p_succ_frac kZoom 1 subDimZoom) * g 1
  else g u
private noncomputable def ghZoomExactOneDimStep (subN p m : ℕ)
    (spec_fn : ℕ → GHZoomSpec) (g : ℕ → ℝ) (r : ℕ) : ℝ :=
  match spec_fn 2 with
  | none => g r
  | some (kInit, probes, kZoom) =>
      if r = 2 then
        let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
        let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
        let u₀ := ghInitAmp2 θ₁ kInit
        let uf := ghChainFinalAmp2 θ₁ probes u₀
        let z₀ := ghInitColl2 θ₂ kInit
        let zf := ghChainFinalColl2 θ₂ probes z₀
        let gInj := ghZoomPostCard (2 ^ (subN - p)) kZoom true g
        let gColl := ghZoomPostCard (2 ^ (subN - p)) kZoom false g
        rotCfProb m 2 *
          (((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes u₀ +
            (ghChainClickProb2 θ₁ probes u₀ + Complex.normSq (uf 2)) * gInj 0 +
            Complex.normSq (uf 0) * gInj 2 +
            2 * Complex.normSq (uf 1) * gInj 1) +
          (1 - rotCfProb m 2) *
            ((ghMaxQueries kInit probes : ℝ) +
              Complex.normSq zf.1 * gColl 2 +
              Complex.normSq zf.2 * gColl 1)
      else g r
private noncomputable def ghZoomExactOneDimDP (subN p m : ℕ) :
    List (ℕ → GHZoomSpec) → (ℕ → ℝ) → ℕ → ℝ
  | [], V_tail, r => V_tail r
  | spec_fn :: rest, V_tail, r =>
      ghZoomExactOneDimStep subN p m spec_fn (ghZoomExactOneDimDP subN p m rest V_tail) r
private lemma ghZoomBaseStep_congr_on_subset {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool)
    (kInit : ℕ) (probes : List GHZoomProbe) {Ψ₁ Ψ₂ : Finset α → ℝ} {R : Finset α}
    (hΨ : ∀ R' ⊆ R, Ψ₁ R' = Ψ₂ R') :
    ghZoomBaseStep subN pref withCost kInit probes Ψ₁ R =
      ghZoomBaseStep subN pref withCost kInit probes Ψ₂ R := by
  classical
  unfold ghZoomBaseStep
  by_cases hInj : Set.InjOn pref (R : Set α)
  · rw [ite_eq_left hInj, ite_eq_left hInj, hΨ ∅ (Finset.empty_subset R)]
    dsimp only
    congr 1
    exact Finset.sum_congr rfl fun B _ ↦ by rw [hΨ (R \ B) Finset.sdiff_subset]
  · rw [ite_eq_right hInj, ite_eq_right hInj, hΨ R Finset.Subset.rfl]
    dsimp only
    congr 1; congr 1
    exact Finset.sum_congr rfl fun x _ ↦ by rw [hΨ (R \ {x}) Finset.sdiff_subset]
private lemma ghZoomSubsetStep_congr_on_subset {α : Type*} [DecidableEq α] {m : ℕ}
    (subN subNZoom : ℕ) (pref : α → Fin m) (withCost : Bool)
    (spec_fn : ℕ → GHZoomSpec) {Ψ₁ Ψ₂ : Finset α → ℝ} {R : Finset α}
    (hΨ : ∀ R' ⊆ R, Ψ₁ R' = Ψ₂ R') :
    ghZoomSubsetStep subN subNZoom pref withCost spec_fn Ψ₁ R =
      ghZoomSubsetStep subN subNZoom pref withCost spec_fn Ψ₂ R := by
  classical
  unfold ghZoomSubsetStep
  cases spec_fn 2 with
  | none => exact hΨ R Finset.Subset.rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    split_ifs
    · refine ghZoomBaseStep_congr_on_subset _ _ _ _ _ fun R' hR' ↦ ?_
      unfold ghZoomPostΨ
      by_cases h1 : R'.card = 1
      · rw [ite_eq_left h1, ite_eq_left h1, hΨ R' hR', hΨ ∅ (Finset.empty_subset R)]
      · rw [ite_eq_right h1, ite_eq_right h1, hΨ R' hR']
    · exact hΨ R Finset.Subset.rfl
private lemma ghZoomSubsetDP_congr_on_subset {α : Type*} [DecidableEq α] {W m : ℕ}
    (subN p : ℕ) (slices : α → Fin W → Fin m)
    (passes : List (Fin W × (ℕ → GHZoomSpec)))
    {Ψ₁ Ψ₂ : Finset α → ℝ} {R : Finset α} (hΨ : ∀ R' ⊆ R, Ψ₁ R' = Ψ₂ R') :
    ghZoomSubsetDP subN p slices passes Ψ₁ R = ghZoomSubsetDP subN p slices passes Ψ₂ R := by
  induction passes generalizing R with
  | nil => exact hΨ R Finset.Subset.rfl
  | cons _ rest ih =>
    exact ghZoomSubsetStep_congr_on_subset _ _ _ _ _ fun R' hR' ↦
      ih fun R'' hR'' ↦ hΨ R'' (hR''.trans hR')
private lemma ghZoomCircDP_map_swap_eq {n p m W : ℕ}
    (hs : (n - W * p) + W * p = n) (hp2 : 2 * p ≤ n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (passes : List GHZoomPassFn) (hW_eq : passes.length = W)
    (l : List (Fin W)) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) :
    ghZoomCircDP hp2 hp hm true
        (l.map fun i ↦
          (rotatedSliceSwapPerm hs hm (Nat.zero_lt_of_lt i.isLt) i,
            (passes[i.val]'(by rw [hW_eq]; exact i.isLt)) (n - p))) Ψ R =
      ghZoomSubsetDP (n - p) p (slicesOf (rotatedSliceEquiv hs hm))
        (l.map fun i ↦ (i, (passes[i.val]'(by rw [hW_eq]; exact i.isLt)) (n - p))) Ψ R := by
  have hsub2p : n - 2 * p = (n - p) - p := by omega
  induction l generalizing R with
  | nil => rfl
  | cons i rest ih =>
    dsimp only [List.map, ghZoomCircDP, ghZoomSubsetDP]
    have hpref :
        (fun x ↦ subcubePref hp hm
          (rotatedSliceSwapPerm hs hm (Nat.zero_lt_of_lt i.isLt) i x)) =
        (fun x ↦ slicesOf (rotatedSliceEquiv hs hm) x i) :=
      funext fun x ↦ subcubePref_rotatedSliceSwapPerm hs hp hm (Nat.zero_lt_of_lt i.isLt) i x
    rw [hpref, hsub2p, funext ih]
private lemma ghZoomBaseStep_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {m : ℕ}
    (subN : ℕ) {emb : α → β} (hemb : Function.Injective emb)
    (pref : β → Fin m) (kInit : ℕ) (probes : List GHZoomProbe)
    (Ψ : Finset β → ℝ) (I : Finset α) :
    ghZoomBaseStep subN pref true kInit probes Ψ (I.image emb) =
      ghZoomBaseStep subN (fun i ↦ pref (emb i)) true kInit probes
        (fun I' ↦ Ψ (I'.image emb)) I := by
  classical
  have hinj_iff :
      Set.InjOn pref ((I.image emb : Finset β) : Set β) ↔
        Set.InjOn (fun i ↦ pref (emb i)) (I : Set α) := by
    constructor
    · intro h1 i₁ hi₁ i₂ hi₂ heq
      exact hemb (h1 (Finset.mem_coe.mpr (Finset.mem_image_of_mem emb hi₁))
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem emb hi₂)) heq)
    · intro h2 y₁ hy₁ y₂ hy₂ heq
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hy₁) with ⟨i₁, hi₁, rfl⟩
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hy₂) with ⟨i₂, hi₂, rfl⟩
      exact congrArg emb (h2 hi₁ hi₂ heq)
  unfold ghZoomBaseStep
  by_cases hP : Set.InjOn pref (I.image emb : Set β)
  · rw [ite_eq_left hP, ite_eq_left (hinj_iff.mp hP)]
    dsimp only
    rw [Finset.image_empty]
    congr 1
    refine Finset.sum_bij (fun B _ ↦ B.preimage emb hemb.injOn)
      (fun B hB ↦ Finset.mem_powerset.mpr fun a ha ↦ ?_)
      (fun B₁ hB₁ B₂ hB₂ heq ↦ ?_)
      (fun A hA ↦ ⟨A.image emb, Finset.mem_powerset.mpr (Finset.image_subset_image
        (Finset.mem_powerset.mp hA)),
        Finset.coe_injective (by rw [Finset.coe_preimage, Finset.coe_image,
          Set.preimage_image_eq _ hemb])⟩)
      (fun B hB ↦ ?_)
    · have hsub := Finset.mem_powerset.mp hB (Finset.mem_preimage.mp ha)
      rcases Finset.mem_image.mp hsub with ⟨i', hi', hi'_eq⟩
      exact hemb hi'_eq ▸ hi'
    · have hsub₁ : (B₁ : Set β) ⊆ Set.range emb := fun y hy ↦ by
        rcases Finset.mem_image.mp (Finset.mem_powerset.mp hB₁ hy) with ⟨i, _, rfl⟩
        exact ⟨i, rfl⟩
      have hsub₂ : (B₂ : Set β) ⊆ Set.range emb := fun y hy ↦ by
        rcases Finset.mem_image.mp (Finset.mem_powerset.mp hB₂ hy) with ⟨i, _, rfl⟩
        exact ⟨i, rfl⟩
      have him := congrArg (fun S ↦ S.image emb) heq
      rwa [Finset.image_preimage emb B₁ hemb.injOn, Finset.filter_true_of_mem
        (fun y hy ↦ hsub₁ hy), Finset.image_preimage emb B₂ hemb.injOn, Finset.filter_true_of_mem
        (fun y hy ↦ hsub₂ hy)] at him
    · have hsub : (B : Set β) ⊆ Set.range emb := fun y hy ↦ by
        rcases Finset.mem_image.mp (Finset.mem_powerset.mp hB hy) with ⟨i, _, rfl⟩
        exact ⟨i, rfl⟩
      have himB : (B.preimage emb hemb.injOn).image emb = B := by
        rw [Finset.image_preimage emb B hemb.injOn]
        exact Finset.filter_true_of_mem fun y hy ↦ hsub hy
      have hcardB : B.card = (B.preimage emb hemb.injOn).card := by
        simpa only [himB] using
          Finset.card_image_of_injective (B.preimage emb hemb.injOn) hemb
      have hsdiff : I.image emb \ B = (I \ B.preimage emb hemb.injOn).image emb := by
        conv_lhs => rw [← himB]
        exact (Finset.image_sdiff I (B.preimage emb hemb.injOn) hemb).symm
      rw [hcardB, hsdiff]
  · rw [ite_eq_right hP, ite_eq_right (mt hinj_iff.mpr hP)]
    dsimp only
    congr 1; congr 1
    rw [Finset.sum_image (fun _ _ _ _ h ↦ hemb h)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hsdiff : I.image emb \ {emb i} = (I \ {i}).image emb := by
      rw [← Finset.image_singleton]
      exact (Finset.image_sdiff I {i} hemb).symm
    rw [hsdiff]
private lemma ghZoomSubsetStep_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {m : ℕ}
    (subN subNZoom : ℕ) {emb : α → β} (hemb : Function.Injective emb)
    (pref : β → Fin m) (spec_fn : ℕ → GHZoomSpec) (Ψ : Finset β → ℝ) (I : Finset α) :
    ghZoomSubsetStep subN subNZoom pref true spec_fn Ψ (I.image emb) =
      ghZoomSubsetStep subN subNZoom (fun i ↦ pref (emb i)) true spec_fn
        (fun I' ↦ Ψ (I'.image emb)) I := by
  classical
  have hcard : (I.image emb).card = I.card := Finset.card_image_of_injective I hemb
  have hinj_iff :
      Set.InjOn pref ((I.image emb : Finset β) : Set β) ↔
        Set.InjOn (fun i ↦ pref (emb i)) (I : Set α) := by
    constructor
    · intro h1 i₁ hi₁ i₂ hi₂ heq
      exact hemb (h1 (Finset.mem_coe.mpr (Finset.mem_image_of_mem emb hi₁))
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem emb hi₂)) heq)
    · intro h2 y₁ hy₁ y₂ hy₂ heq
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hy₁) with ⟨i₁, hi₁, rfl⟩
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hy₂) with ⟨i₂, hi₂, rfl⟩
      exact congrArg emb (h2 hi₁ hi₂ heq)
  unfold ghZoomSubsetStep
  cases spec_fn 2 with
  | none => rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    rw [hcard]
    by_cases hr2 : I.card = 2
    · rw [ite_eq_left hr2, ite_eq_left hr2,
        ghZoomBaseStep_image_of_inj subN hemb pref kInit probes _ I]
      refine ghZoomBaseStep_congr_on_subset _ _ _ _ _ fun I' _ ↦ ?_
      unfold ghZoomPostΨ
      dsimp only
      rw [Finset.card_image_of_injective I' hemb, Finset.image_empty]
      by_cases h1 : I'.card = 1
      · rw [ite_eq_left h1, ite_eq_left h1]
        congr 1
        by_cases hP : Set.InjOn pref (I.image emb : Set β)
        · rw [ite_eq_left hP, ite_eq_left (hinj_iff.mp hP)]
        · rw [ite_eq_right hP, ite_eq_right (mt hinj_iff.mpr hP)]
      · rw [ite_eq_right h1, ite_eq_right h1]
    · simp [hr2]
private lemma ghZoomSubsetDP_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {W m : ℕ}
    (subN p : ℕ) {emb : α → β} (hemb : Function.Injective emb)
    (slices : β → Fin W → Fin m)
    (passes : List (Fin W × (ℕ → GHZoomSpec)))
    (Ψ : Finset β → ℝ) (I : Finset α) :
    ghZoomSubsetDP subN p slices passes Ψ (I.image emb) =
      ghZoomSubsetDP subN p (fun i t ↦ slices (emb i) t) passes
        (fun I' ↦ Ψ (I'.image emb)) I := by
  induction passes generalizing I with
  | nil => rfl
  | cons ps rest ih =>
    rcases ps with ⟨t, spec_fn⟩
    dsimp only [ghZoomSubsetDP]
    rw [ghZoomSubsetStep_image_of_inj subN (subN - p) hemb (fun y ↦ slices y t) spec_fn _ I]
    exact ghZoomSubsetStep_congr_on_subset _ _ _ _ _ fun I' _ ↦ ih I'
private lemma ghZoomBaseStep_of_card_two {α : Type*} [DecidableEq α] {m : ℕ} (subN : ℕ)
    (pref : α → Fin m) (kInit : ℕ) (probes : List GHZoomProbe)
    {Ψ : Finset α → ℝ} (g : ℕ → ℝ) {R : Finset α} (hR2 : R.card = 2)
    (hΨ : ∀ R', R' ⊆ R → Ψ R' = g R'.card) :
    ghZoomBaseStep subN pref true kInit probes Ψ R =
      if Set.InjOn pref (R : Set α) then
        let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
        let u₀ := ghInitAmp2 θ₁ kInit
        let uf := ghChainFinalAmp2 θ₁ probes u₀
        ((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes u₀ +
          (ghChainClickProb2 θ₁ probes u₀ + Complex.normSq (uf 2)) * g 0 +
          Complex.normSq (uf 0) * g 2 +
          2 * Complex.normSq (uf 1) * g 1
      else
        let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
        let z₀ := ghInitColl2 θ₂ kInit
        let zf := ghChainFinalColl2 θ₂ probes z₀
        (ghMaxQueries kInit probes : ℝ) +
          Complex.normSq zf.1 * g 2 +
          Complex.normSq zf.2 * g 1 := by
  classical
  unfold ghZoomBaseStep
  by_cases hInj : Set.InjOn pref (R : Set α)
  · rw [ite_eq_left hInj, ite_eq_left hInj, hΨ ∅ (Finset.empty_subset R), Finset.card_empty]
    simp only [↓reduceIte]
    have hpow : R.powerset = (Finset.range (R.card + 1)).biUnion R.powersetCard := by
      ext B
      simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_powersetCard]
      exact ⟨fun h ↦ ⟨B.card, Nat.lt_succ_of_le (Finset.card_le_card h), h, rfl⟩,
        fun ⟨_, _, h, _⟩ ↦ h⟩
    have hdisj :
        Set.PairwiseDisjoint (Finset.range (R.card + 1) : Set ℕ) R.powersetCard :=
      fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun B h1 h2 ↦
        hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
    have hsum_eq :
        (∑ B ∈ R.powerset,
          Complex.normSq
            (ghChainFinalAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
              (ghInitAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) B.card) * Ψ (R \ B)) =
        ∑ w ∈ Finset.range 3,
          (Nat.choose 2 w : ℝ) *
            Complex.normSq
              (ghChainFinalAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
                (ghInitAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) w) * g (2 - w) := by
      rw [hpow, Finset.sum_biUnion hdisj, hR2]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      have hcongr : ∀ B ∈ R.powersetCard w,
          Complex.normSq
            (ghChainFinalAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
              (ghInitAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) B.card) * Ψ (R \ B) =
          Complex.normSq
            (ghChainFinalAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
              (ghInitAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) w) * g (2 - w) := by
        intro B hB
        rcases Finset.mem_powersetCard.mp hB with ⟨hBR, hBw⟩
        have hcs : (R \ B).card = 2 - w := by
          have h := Finset.card_sdiff_add_card_eq_card hBR
          omega
        rw [hBw, hΨ (R \ B) Finset.sdiff_subset, hcs]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard, hR2,
        nsmul_eq_mul, ← mul_assoc]
    rw [hsum_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
    ring
  · rw [ite_eq_right hInj, ite_eq_right hInj, hΨ R Finset.Subset.rfl, hR2]
    simp only [↓reduceIte]
    have hsum_x : (∑ x ∈ R, (1 / 2 : ℝ) * Ψ (R \ {x})) = g 1 := by
      have hcongr : ∀ x ∈ R, (1 / 2 : ℝ) * Ψ (R \ {x}) = (1 / 2 : ℝ) * g 1 := by
        intro x hx
        have hcard1 : (R \ {x}).card = 1 := by
          rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hx, hR2]
        rw [hΨ (R \ {x}) Finset.sdiff_subset, hcard1]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, hR2, nsmul_eq_mul]
      norm_num
      ring
    rw [hsum_x]
private lemma gh_card_filter_injective_two (m : ℕ) :
    ((Finset.univ : Finset (Fin 2 → Fin m)).filter Function.Injective).card =
      m.descFactorial 2 := by
  let e : (Fin 2 → Fin m) ≃ Fin m × Fin m :=
    { toFun := fun h ↦ (h 0, h 1)
      invFun := fun q a ↦ if a = 0 then q.1 else q.2
      left_inv := fun h ↦ funext fun a ↦ by fin_cases a <;> rfl
      right_inv := fun ⟨_, _⟩ ↦ rfl }
  have hinj_pair (h : Fin 2 → Fin m) : Function.Injective h ↔ h 0 ≠ h 1 := by
    constructor
    · intro hInj heq
      exact absurd (congrArg Fin.val (hInj heq)) (by simp)
    · intro hne a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact False.elim (hne hab)
      · exact False.elim (hne hab.symm)
      · rfl
  let OffDiag := ((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))).filter
    fun q : Fin m × Fin m ↦ q.1 ≠ q.2
  have hbij :
      ((Finset.univ : Finset (Fin 2 → Fin m)).filter Function.Injective).card = OffDiag.card := by
    refine Finset.card_bij (fun h _ ↦ e h)
      (fun h hh ↦ Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
          (hinj_pair h).mp (Finset.mem_filter.mp hh).2⟩)
      (fun _ _ _ _ heq ↦ e.injective heq)
      (fun q hq ↦ ⟨e.symm q, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hinj_pair (e.symm q)).mpr (Finset.mem_filter.mp hq).2⟩, e.apply_symm_apply q⟩)
  have hdiag : ((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))).filter
      (fun q : Fin m × Fin m ↦ ¬ q.1 ≠ q.2) =
      (Finset.univ : Finset (Fin m)).map ⟨fun x ↦ (x, x), fun _ _ h ↦ congrArg Prod.fst h⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, not_ne_iff,
      Finset.mem_map]
    constructor
    · rintro rfl
      exact ⟨a, rfl⟩
    · rintro ⟨x, hx⟩
      exact (congrArg Prod.fst hx).symm.trans (congrArg Prod.snd hx)
  have hpart := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m)))
    (fun q : Fin m × Fin m ↦ q.1 ≠ q.2) (fun _ ↦ (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hpart
  have hcard_prod :
      (((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))).card) = m * m := by
    simp
  have hcard_diag :
      (((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))).filter
        (fun q : Fin m × Fin m ↦ ¬ q.1 ≠ q.2)).card = m := by
    rw [hdiag, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hoff : OffDiag.card + m = m * m := by
    dsimp only [OffDiag]
    omega
  rw [hbij, Nat.descFactorial_succ, Nat.descFactorial_one]
  cases m with
  | zero =>
    have h0 : OffDiag.card = 0 := by omega
    rw [h0]
  | succ m' =>
    have hsub : m' + 1 - 1 = m' := Nat.add_sub_cancel m' 1
    rw [hsub]
    have hmul : (m' + 1) * (m' + 1) = m' * (m' + 1) + (m' + 1) := by ring
    omega
private lemma sum_ghZoomSubsetStep_of_card_eq {k m : ℕ} (hm1 : 1 ≤ m) (subN p : ℕ)
    (spec_fn : ℕ → GHZoomSpec) (g : ℕ → ℝ) (I : Finset (Fin k)) :
    (∑ f_t : Fin k → Fin m,
      ghZoomSubsetStep subN (subN - p) f_t true spec_fn (fun I' ↦ g I'.card) I) =
      ((m : ℝ) ^ k) * ghZoomExactOneDimStep subN p m spec_fn g I.card := by
  classical
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hm_pos 2
  unfold ghZoomSubsetStep ghZoomExactOneDimStep
  cases hsp2 : spec_fn 2 with
  | none => simp [Finset.sum_const, nsmul_eq_mul]
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    by_cases hr2 : I.card = 2
    · simp_rw [ite_eq_left hr2]
      let gInj := ghZoomPostCard (2 ^ (subN - p)) kZoom true g
      let gColl := ghZoomPostCard (2 ^ (subN - p)) kZoom false g
      let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
      let θ₂ := Real.arcsin (√2 / √(2 ^ subN : ℝ))
      let u₀ := ghInitAmp2 θ₁ kInit
      let uf := ghChainFinalAmp2 θ₁ probes u₀
      let z₀ := ghInitColl2 θ₂ kInit
      let zf := ghChainFinalColl2 θ₂ probes z₀
      let valInj : ℝ :=
        ((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes u₀ +
          (ghChainClickProb2 θ₁ probes u₀ + Complex.normSq (uf 2)) * gInj 0 +
          Complex.normSq (uf 0) * gInj 2 +
          2 * Complex.normSq (uf 1) * gInj 1
      let valColl : ℝ :=
        (ghMaxQueries kInit probes : ℝ) +
          Complex.normSq zf.1 * gColl 2 +
          Complex.normSq zf.2 * gColl 1
      have hstep_ft (f_t : Fin k → Fin m) :
          ghZoomBaseStep subN f_t true kInit probes
              (ghZoomPostΨ (2 ^ (subN - p)) kZoom true (Set.InjOn f_t (I : Set (Fin k)))
                (fun J ↦ g J.card)) I =
            if Set.InjOn f_t (I : Set (Fin k)) then valInj else valColl := by
        by_cases hInj : Set.InjOn f_t (I : Set (Fin k))
        · have hΨ_inj : ∀ I' ⊆ I,
              ghZoomPostΨ (2 ^ (subN - p)) kZoom true (Set.InjOn f_t (I : Set (Fin k)))
                (fun J ↦ g J.card) I' = gInj I'.card := by
            intro I' _
            unfold ghZoomPostΨ gInj ghZoomPostCard
            by_cases h1 : I'.card = 1
            · rw [ite_eq_left h1, ite_eq_left hInj]; simp [h1]
            · rw [ite_eq_right h1, ite_eq_right h1]
          rw [ghZoomBaseStep_of_card_two subN f_t kInit probes gInj hr2 hΨ_inj,
            ite_eq_left hInj, ite_eq_left hInj]
        · have hΨ_coll : ∀ I' ⊆ I,
              ghZoomPostΨ (2 ^ (subN - p)) kZoom true (Set.InjOn f_t (I : Set (Fin k)))
                (fun J ↦ g J.card) I' = gColl I'.card := by
            intro I' _
            unfold ghZoomPostΨ gColl ghZoomPostCard
            by_cases h1 : I'.card = 1
            · rw [ite_eq_left h1, ite_eq_right hInj]; simp [h1]
            · rw [ite_eq_right h1, ite_eq_right h1]
          rw [ghZoomBaseStep_of_card_two subN f_t kInit probes gColl hr2 hΨ_coll,
            ite_eq_right hInj, ite_eq_right hInj]
      simp_rw [hstep_ft]
      let eI : Fin 2 ≃ I := (Finset.equivFinOfCardEq hr2).symm
      let splitI : (Fin k → Fin m) ≃ (Fin 2 → Fin m) × ({i : Fin k // i ∉ I} → Fin m) :=
        { toFun := fun f_t ↦ (fun a ↦ f_t (eI a), fun b ↦ f_t b.1)
          invFun := fun q i ↦ if hi : i ∈ I then q.1 (eI.symm ⟨i, hi⟩) else q.2 ⟨i, hi⟩
          left_inv := fun f_t ↦ funext fun i ↦ by by_cases hi : i ∈ I <;> simp [hi]
          right_inv := fun ⟨h, hc⟩ ↦ Prod.ext
            (funext fun a ↦ by simp [(eI a).2])
            (funext fun b ↦ by simp [b.2]) }
      have hcard_r :
          (m : ℝ) ^ k =
            (m : ℝ) ^ 2 * (Fintype.card ({i : Fin k // i ∉ I} → Fin m) : ℝ) := by
        have hc := Fintype.card_congr splitI
        simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
          Nat.cast_mul, Nat.cast_pow] using congrArg (Nat.cast (R := ℝ)) hc
      rw [← splitI.symm.sum_comp, Fintype.sum_prod_type]
      have hinj_eq (h : Fin 2 → Fin m) (hc : {i : Fin k // i ∉ I} → Fin m) :
          Set.InjOn (splitI.symm (h, hc)) (I : Set (Fin k)) ↔ Function.Injective h := by
        constructor
        · intro hInj a₁ a₂ heq
          have h1 : splitI.symm (h, hc) (eI a₁) = h a₁ := by simp [splitI, (eI a₁).2]
          have h2 : splitI.symm (h, hc) (eI a₂) = h a₂ := by simp [splitI, (eI a₂).2]
          exact eI.injective
            (Subtype.ext (hInj (eI a₁).2 (eI a₂).2 (h1.trans (heq.trans h2.symm))))
        · intro hh i₁ hi₁ i₂ hi₂ heq
          dsimp only [splitI, Equiv.coe_fn_symm_mk] at heq
          rw [dite_eq_left (Finset.mem_coe.mp hi₁), dite_eq_left (Finset.mem_coe.mp hi₂)] at heq
          exact congrArg Subtype.val (eI.symm.injective (hh heq))
      have hsummand (h : Fin 2 → Fin m) (hc : {i : Fin k // i ∉ I} → Fin m) :
          (if Set.InjOn (splitI.symm (h, hc)) (I : Set (Fin k)) then valInj else valColl) =
            if Function.Injective h then valInj else valColl :=
        if_congr (hinj_eq h hc) rfl rfl
      simp_rw [hsummand, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
        hcard_r]
      let U : Finset (Fin 2 → Fin m) := Finset.univ
      let Inj := U.filter Function.Injective
      let Coll := U.filter fun h ↦ ¬ Function.Injective h
      have hsplit_U :
          (∑ h : Fin 2 → Fin m, if Function.Injective h then valInj else valColl) =
            (Inj.card : ℝ) * valInj + (Coll.card : ℝ) * valColl := by
        have h1 := (Finset.sum_filter_add_sum_filter_not U Function.Injective
          (fun h ↦ if Function.Injective h then valInj else valColl)).symm
        have h2 : (∑ h ∈ Inj, if Function.Injective h then valInj else valColl) =
            (Inj.card : ℝ) * valInj := by
          rw [Finset.sum_congr rfl (fun h hh ↦ ite_eq_left (Finset.mem_filter.mp hh).2),
            Finset.sum_const, nsmul_eq_mul]
        have h3 : (∑ h ∈ Coll, if Function.Injective h then valInj else valColl) =
            (Coll.card : ℝ) * valColl := by
          rw [Finset.sum_congr rfl (fun h hh ↦ ite_eq_right (Finset.mem_filter.mp hh).2),
            Finset.sum_const, nsmul_eq_mul]
        dsimp only [Inj, Coll, U] at h1 h2 h3 ⊢
        rw [h1, h2, h3]
      have hinj_card_r : (Inj.card : ℝ) = (m : ℝ) ^ 2 * rotCfProb m 2 := by
        dsimp only [Inj, U]
        rw [gh_card_filter_injective_two m]
        unfold rotCfProb
        field_simp [hm2_pos.ne']
      have hcoll_card_r : (Coll.card : ℝ) = (m : ℝ) ^ 2 * (1 - rotCfProb m 2) := by
        have hadd : Inj.card + Coll.card = U.card := by
          simpa [Inj, Coll] using
            Finset.sum_filter_add_sum_filter_not U Function.Injective (fun _ ↦ (1 : ℕ))
        have hU_card : U.card = m ^ 2 := by simp [U]
        have hadd_r : (Inj.card : ℝ) + (Coll.card : ℝ) = (m : ℝ) ^ 2 := by
          have hc := congrArg (Nat.cast (R := ℝ)) hadd
          simpa only [hU_card, Nat.cast_add, Nat.cast_pow] using hc
        linarith [hinj_card_r]
      rw [hsplit_U, hinj_card_r, hcoll_card_r]
      dsimp only [valInj, valColl, θ₁, θ₂, u₀, uf, z₀, zf, gInj, gColl]
      ring
    · simp [hr2, Finset.sum_const, nsmul_eq_mul]
private lemma ghZoomSubsetDP_congr_slices {α : Type*} [DecidableEq α] {W m : ℕ} (subN p : ℕ)
    {s₁ s₂ : α → Fin W → Fin m}
    (passes : List (Fin W × (ℕ → GHZoomSpec)))
    (hs : ∀ ps ∈ passes, ∀ x : α, s₁ x ps.1 = s₂ x ps.1)
    (Ψ : Finset α → ℝ) (R : Finset α) :
    ghZoomSubsetDP subN p s₁ passes Ψ R = ghZoomSubsetDP subN p s₂ passes Ψ R := by
  induction passes generalizing R with
  | nil => rfl
  | cons ps rest ih =>
    rcases ps with ⟨t, spec_fn⟩
    have ht : (fun x ↦ s₁ x t) = (fun x ↦ s₂ x t) :=
      funext fun x ↦ hs (t, spec_fn) List.mem_cons_self x
    dsimp only [ghZoomSubsetDP]
    rw [ht]
    exact ghZoomSubsetStep_congr_on_subset _ _ _ _ _ fun R' _ ↦
      ih (fun q hq x ↦ hs q (List.mem_cons_of_mem _ hq) x) R'
private lemma sum_fintype_ghZoomBaseStep {α β : Type*} [DecidableEq α] [Fintype β] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (kInit : ℕ) (probes : List GHZoomProbe)
    (F : β → Finset α → ℝ) (G : Finset α → ℝ) (I : Finset α)
    (hFG : ∀ I' ⊆ I, (∑ fr : β, F fr I') = (Fintype.card β : ℝ) * G I') :
    (∑ fr : β, ghZoomBaseStep subN pref true kInit probes (F fr) I) =
      (Fintype.card β : ℝ) * ghZoomBaseStep subN pref true kInit probes G I := by
  classical
  unfold ghZoomBaseStep
  simp only [↓reduceIte]
  by_cases hInj : Set.InjOn pref (I : Set α)
  · simp_rw [ite_eq_left hInj]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, hFG ∅ (Finset.empty_subset I), Finset.sum_comm]
    have hB_sum (B : Finset α) :
        (∑ fr : β,
          Complex.normSq
            (ghChainFinalAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
              (ghInitAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) B.card) *
            F fr (I \ B)) =
        (Fintype.card β : ℝ) *
          (Complex.normSq
            (ghChainFinalAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
              (ghInitAmp2 (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) B.card) *
            G (I \ B)) := by
      rw [← Finset.mul_sum, hFG (I \ B) Finset.sdiff_subset]
      ring
    simp_rw [hB_sum, ← Finset.mul_sum]
    ring
  · simp_rw [ite_eq_right hInj]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, hFG I Finset.Subset.rfl, ← Finset.mul_sum, Finset.sum_comm]
    have hx_sum : ∀ x ∈ I,
        (∑ fr : β, (1 / 2 : ℝ) * F fr (I \ {x})) =
          (Fintype.card β : ℝ) * ((1 / 2 : ℝ) * G (I \ {x})) := by
      intro x _
      rw [← Finset.mul_sum, hFG (I \ {x}) Finset.sdiff_subset]
      ring
    rw [Finset.sum_congr rfl hx_sum, ← Finset.mul_sum]
    ring
private lemma sum_fintype_ghZoomSubsetStep {α β : Type*} [DecidableEq α] [Fintype β] {m : ℕ}
    (subN subNZoom : ℕ) (pref : α → Fin m) (spec_fn : ℕ → GHZoomSpec)
    (F : β → Finset α → ℝ) (G : Finset α → ℝ) (I : Finset α)
    (hFG : ∀ I' ⊆ I, (∑ fr : β, F fr I') = (Fintype.card β : ℝ) * G I') :
    (∑ fr : β, ghZoomSubsetStep subN subNZoom pref true spec_fn (F fr) I) =
      (Fintype.card β : ℝ) * ghZoomSubsetStep subN subNZoom pref true spec_fn G I := by
  classical
  unfold ghZoomSubsetStep
  cases spec_fn 2 with
  | none => exact hFG I Finset.Subset.rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    by_cases hr2 : I.card = 2
    · simp_rw [ite_eq_left hr2]
      refine sum_fintype_ghZoomBaseStep subN pref kInit probes _ _ I fun I' hI' ↦ ?_
      unfold ghZoomPostΨ
      by_cases h1 : I'.card = 1
      · simp_rw [ite_eq_left h1]
        by_cases hinj : Set.InjOn pref (I : Set α)
        · simp_rw [ite_eq_left hinj, ite_true]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hFG I' hI']
          ring
        · simp_rw [ite_eq_right hinj, ite_true]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            hFG ∅ (Finset.empty_subset I), hFG I' hI']
          ring
      · simp_rw [ite_eq_right h1]
        exact hFG I' hI'
    · simp_rw [ite_eq_right hr2]
      exact hFG I Finset.Subset.rfl
private lemma avg_ghZoomSubsetDP_eq_ghZoomExactOneDimDP {W m k : ℕ} (hm1 : 1 ≤ m) (subN p : ℕ)
    (passes : List (Fin W × (ℕ → GHZoomSpec)))
    (hnodup : (passes.map Prod.fst).Nodup)
    (V_tail : ℕ → ℝ) (I : Finset (Fin k)) :
    (∑ f : Fin k → Fin W → Fin m,
      ghZoomSubsetDP subN p f passes (fun I' ↦ V_tail I'.card) I) /
      (((m ^ W) ^ k : ℕ) : ℝ) =
      ghZoomExactOneDimDP subN p m (passes.map Prod.snd) V_tail I.card := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hMW_pos : (0 : ℝ) < (((m ^ W) ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (Nat.pow_pos (by omega : 0 < m))
  rw [div_eq_iff hMW_pos.ne']
  induction passes generalizing I with
  | nil =>
    simp [ghZoomSubsetDP, ghZoomExactOneDimDP, Finset.sum_const, nsmul_eq_mul, mul_comm]
  | cons head rest ih =>
    rcases head with ⟨t, spec_fn⟩
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨ht_notMem, hrest_nodup⟩
    let splitW : (Fin k → Fin W → Fin m) ≃
        (Fin k → Fin m) × (Fin k → {t' : Fin W // t' ≠ t} → Fin m) :=
      { toFun := fun f ↦ (fun i ↦ f i t, fun i t' ↦ f i t'.1)
        invFun := fun q i t' ↦ if h : t' = t then q.1 i else q.2 i ⟨t', h⟩
        left_inv := fun f ↦ funext fun i ↦ funext fun t' ↦ by by_cases h : t' = t <;> simp [h]
        right_inv := fun ⟨ft, fr⟩ ↦ Prod.ext (funext fun i ↦ by simp)
          (funext fun i ↦ funext fun t' ↦ by simp [t'.2]) }
    let RestType := Fin k → {t' : Fin W // t' ≠ t} → Fin m
    have hcard_Wr : (((m ^ W) ^ k : ℕ) : ℝ) = ((m : ℝ) ^ k) * (Fintype.card RestType : ℝ) := by
      have hcard_W : Fintype.card (Fin k → Fin W → Fin m) =
          Fintype.card (Fin k → Fin m) * Fintype.card RestType := by
        rw [Fintype.card_congr splitW, Fintype.card_prod]
      have hlhs : Fintype.card (Fin k → Fin W → Fin m) = (m ^ W) ^ k := by simp [Fintype.card_fin]
      have hm_k : Fintype.card (Fin k → Fin m) = m ^ k := by simp [Fintype.card_fin]
      rw [hlhs, hm_k] at hcard_W
      have hr := congrArg (Nat.cast (R := ℝ)) hcard_W
      rw [Nat.cast_mul, Nat.cast_pow m k] at hr
      exact hr
    let f₀ : Fin k → Fin m := fun _ ↦ ⟨0, by omega⟩
    have hrest_indep (ft : Fin k → Fin m) (fr : RestType) (I' : Finset (Fin k)) :
        ghZoomSubsetDP subN p (splitW.symm (ft, fr)) rest (fun J ↦ V_tail J.card) I' =
          ghZoomSubsetDP subN p (splitW.symm (f₀, fr)) rest (fun J ↦ V_tail J.card) I' := by
      refine ghZoomSubsetDP_congr_slices subN p rest (fun q hq i ↦ ?_) _ I'
      have hne : q.1 ≠ t := fun heq ↦ ht_notMem (heq ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)
      dsimp only [splitW, Equiv.coe_fn_symm_mk]
      simp [hne]
    let g_rest : ℕ → ℝ := ghZoomExactOneDimDP subN p m (rest.map Prod.snd) V_tail
    have hsum_fr (I' : Finset (Fin k)) :
        (∑ fr : RestType,
          ghZoomSubsetDP subN p (splitW.symm (f₀, fr)) rest (fun J ↦ V_tail J.card) I') =
          (Fintype.card RestType : ℝ) * g_rest I'.card := by
      have hih := ih hrest_nodup I'
      rw [← splitW.symm.sum_comp, Fintype.sum_prod_type] at hih
      simp_rw [hrest_indep] at hih
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, hcard_Wr] at hih
      exact mul_left_cancel₀ (pow_pos hm_pos k).ne' (by dsimp only [g_rest]; linarith)
    dsimp only [ghZoomSubsetDP, List.map, ghZoomExactOneDimDP]
    rw [← splitW.symm.sum_comp, Fintype.sum_prod_type]
    have hhead_t (ft : Fin k → Fin m) (fr : RestType) :
        (fun i : Fin k ↦ splitW.symm (ft, fr) i t) = ft := by
      funext i; dsimp only [splitW, Equiv.coe_fn_symm_mk]; simp
    have hinner (ft : Fin k → Fin m) :
        (∑ fr : RestType,
          ghZoomSubsetStep subN (subN - p) (fun i ↦ splitW.symm (ft, fr) i t) true spec_fn
            (ghZoomSubsetDP subN p (splitW.symm (ft, fr)) rest (fun J ↦ V_tail J.card)) I) =
          (Fintype.card RestType : ℝ) *
            ghZoomSubsetStep subN (subN - p) ft true spec_fn (fun I' ↦ g_rest I'.card) I := by
      simp_rw [hhead_t ft]
      refine sum_fintype_ghZoomSubsetStep subN (subN - p) ft spec_fn _ _ I fun I' _ ↦ ?_
      simp_rw [hrest_indep ft _ I']
      exact hsum_fr I'
    rw [Finset.sum_congr rfl fun ft _ ↦ hinner ft, ← Finset.mul_sum,
      sum_ghZoomSubsetStep_of_card_eq hm1 subN p spec_fn g_rest I, hcard_Wr]
    dsimp only [g_rest]
    ring
private lemma avg_ghZoomSubsetDP_mkGoodTargetSet_eq {n s W m k : ℕ}
    (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)) (hm1 : 1 ≤ m) (subN p : ℕ)
    (passes : List (Fin W × (ℕ → GHZoomSpec)))
    (hnodup : (passes.map Prod.fst).Nodup)
    (V_tail : ℕ → ℝ) (U : Finset (Fin (2 ^ s))) (hU : U.card = k) :
    (∑ f : Fin k → Fin W → Fin m,
      ghZoomSubsetDP subN p (slicesOf e) passes
        (fun R' ↦ V_tail R'.card) (mkGoodTargetSet e U hU f)) /
      (((m ^ W) ^ k : ℕ) : ℝ) =
      ghZoomExactOneDimDP subN p m (passes.map Prod.snd) V_tail k := by
  have heq (f : Fin k → Fin W → Fin m) :
      ghZoomSubsetDP subN p (slicesOf e) passes
          (fun R' ↦ V_tail R'.card) (mkGoodTargetSet e U hU f) =
        ghZoomSubsetDP subN p f passes (fun I' ↦ V_tail I'.card) Finset.univ := by
    let emb : Fin k → Fin (2 ^ n) := fun i ↦ e.symm (U.orderEmbOfFin hU i, f i)
    have hemb : Function.Injective emb := fun i₁ i₂ h ↦
      (U.orderEmbOfFin hU).injective (congrArg Prod.fst (e.symm.injective h))
    have hslices : (fun i t ↦ slicesOf e (emb i) t) = f := by
      funext i t; simp [slicesOf, emb]
    have hcard (I' : Finset (Fin k)) : (I'.image emb).card = I'.card :=
      Finset.card_image_of_injective I' hemb
    unfold mkGoodTargetSet
    change ghZoomSubsetDP subN p (slicesOf e) passes _ (Finset.univ.image emb) = _
    rw [ghZoomSubsetDP_image_of_inj subN p hemb (slicesOf e) passes _ Finset.univ, hslices]
    simp_rw [hcard]
  simp_rw [heq]
  simpa using avg_ghZoomSubsetDP_eq_ghZoomExactOneDimDP hm1 subN p passes hnodup V_tail Finset.univ
private lemma rotCfProb_two_bounds {m : ℕ} (hm1 : 1 ≤ m) :
    0 ≤ rotCfProb m 2 ∧ 0 ≤ 1 - rotCfProb m 2 := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm2_pos : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hm_pos 2
  unfold rotCfProb
  refine ⟨div_nonneg (Nat.cast_nonneg _) hm2_pos.le, sub_nonneg.mpr ?_⟩
  refine (div_le_one hm2_pos).mpr ?_
  have hdesc : m.descFactorial 2 ≤ m ^ 2 := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one, sq]
    exact Nat.mul_le_mul_right m (Nat.sub_le m 1)
  exact_mod_cast hdesc
private lemma ghZoomExactOneDimStep_mono_on (subN p m : ℕ) (hm1 : 1 ≤ m)
    (spec_fn : ℕ → GHZoomSpec) {g₁ g₂ : ℕ → ℝ} {r : ℕ} (hg : ∀ u ≤ r, g₁ u ≤ g₂ u) :
    ghZoomExactOneDimStep subN p m spec_fn g₁ r ≤
      ghZoomExactOneDimStep subN p m spec_fn g₂ r := by
  unfold ghZoomExactOneDimStep
  cases spec_fn 2 with
  | none => exact hg r le_rfl
  | some kpz =>
    rcases kpz with ⟨kInit, probes, kZoom⟩
    dsimp only
    by_cases hr2 : r = 2
    · subst hr2
      rw [ite_eq_left rfl, ite_eq_left rfl]
      rcases rotCfProb_two_bounds hm1 with ⟨hcf0, hcf1⟩
      have hgInj : ∀ u ≤ 2,
          ghZoomPostCard (2 ^ (subN - p)) kZoom true g₁ u ≤
            ghZoomPostCard (2 ^ (subN - p)) kZoom true g₂ u := by
        intro u hu
        unfold ghZoomPostCard
        by_cases h1 : u = 1
        · rw [ite_eq_left h1, ite_eq_left h1]
          simp only [↓reduceIte]
          exact add_le_add le_rfl (hg 1 (by omega))
        · rw [ite_eq_right h1, ite_eq_right h1]
          exact hg u hu
      have hgColl : ∀ u ≤ 2,
          ghZoomPostCard (2 ^ (subN - p)) kZoom false g₁ u ≤
            ghZoomPostCard (2 ^ (subN - p)) kZoom false g₂ u := by
        intro u hu
        unfold ghZoomPostCard
        by_cases h1 : u = 1
        · rw [ite_eq_left h1, ite_eq_left h1]
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine add_le_add le_rfl (add_le_add ?_ ?_)
          · exact mul_le_mul_of_nonneg_left (hg 0 (by omega)) (sq_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hg 1 (by omega))
              (sub_nonneg.mpr (Real.sin_sq_le_one _))
        · rw [ite_eq_right h1, ite_eq_right h1]
          exact hg u hu
      refine add_le_add
        (mul_le_mul_of_nonneg_left ?_ hcf0)
        (mul_le_mul_of_nonneg_left ?_ hcf1)
      · refine add_le_add
          (add_le_add
            (add_le_add le_rfl
              (mul_le_mul_of_nonneg_left (hgInj 0 (by omega))
                (add_nonneg (ghChainClickProb2_nonneg _ _ _) (Complex.normSq_nonneg _))))
            (mul_le_mul_of_nonneg_left (hgInj 2 (by omega)) (Complex.normSq_nonneg _)))
          (mul_le_mul_of_nonneg_left (hgInj 1 (by omega))
            (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
      · refine add_le_add
          (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hgColl 2 (by omega)) (Complex.normSq_nonneg _)))
          (mul_le_mul_of_nonneg_left (hgColl 1 (by omega)) (Complex.normSq_nonneg _))
    · rw [ite_eq_right hr2, ite_eq_right hr2]
      exact hg r le_rfl
private lemma ghZoomExactOneDimStep_le_ghZoomOneDimUpper (subN p m : ℕ)
    (spec_fn : ℕ → GHZoomSpec) {f : ℕ → ℝ} {r : ℕ} (hf0 : f 0 = 0) :
    ghZoomExactOneDimStep subN p m spec_fn f r ≤ ghZoomOneDimUpper subN p m (spec_fn r) f r := by
  refine le_of_eq ?_
  unfold ghZoomExactOneDimStep ghZoomOneDimUpper
  by_cases hr0 : r = 0
  · subst hr0
    cases spec_fn 2 <;> simp [hf0]
  · rw [ite_eq_right hr0]
    by_cases hr2 : r = 2
    · subst hr2
      cases hsp2 : spec_fn 2 with
      | none => rfl
      | some kpz =>
        rcases kpz with ⟨kInit, probes, kZoom⟩
        dsimp only
        rw [ite_eq_left rfl, ite_eq_left rfl]
        unfold ghZoomPostCard
        simp only [Nat.reduceEqDiff, ↓reduceIte, Bool.false_eq_true, hf0, mul_zero, zero_add]
        ring
    · cases spec_fn 2 with
      | none =>
        cases spec_fn r with
        | none => rfl
        | some kpz =>
          rcases kpz with ⟨_, _, _⟩
          dsimp only
          rw [ite_eq_right hr2]
      | some kpz2 =>
        rcases kpz2 with ⟨_, _, _⟩
        dsimp only
        rw [ite_eq_right hr2]
        cases spec_fn r with
        | none => rfl
        | some kpz =>
          rcases kpz with ⟨_, _, _⟩
          dsimp only
          rw [ite_eq_right hr2]
private lemma two_pow_sub_eq_div_gh {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) :
    (2 ^ (n - p) : ℝ) = (2 ^ n : ℝ) / (m : ℝ) := by
  have hm_ne : (m : ℝ) ≠ 0 := by rw [hm]; positivity
  rw [eq_div_iff hm_ne, hm]
  push_cast
  rw [← pow_add, Nat.sub_add_cancel hp]
private lemma getD_last_of_getLast?_gh {α : Type*} (fFinal : α) :
    ∀ (l : List α) (n : ℕ), l.length = n + 1 → l.getLast? = some fFinal →
      l.getD n fFinal = fFinal := by
  intro l
  induction l with
  | nil => intro n hn; simp at hn
  | cons x xs ih =>
    intro n hn hlast
    cases xs with
    | nil =>
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      have hx : x = fFinal := by simpa using hlast
      simpa [List.getD] using hx
    | cons _ _ =>
      cases n with
      | zero => simp at hn
      | succ n' => exact ih n' (by simpa using hn) (by simpa using hlast)
private lemma drop_eq_getElem_cons_gh {α : Type*} :
    ∀ (l : List α) {i : ℕ} (hi : i < l.length),
      l.drop i = l[i] :: l.drop (i + 1) := by
  intro l
  induction l with
  | nil => intro _ hi; cases hi
  | cons _ _ ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ _ => exact ih (Nat.lt_of_succ_lt_succ hi)
/-- Total correctness (`wp = ⊤`) of `.qSet;; ghZoomRotCircuit` across all `1 ≤ n` and `k =
  2`. -/
theorem ghZoomRotCircuit_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hn : 1 ≤ n) (hmk : Stage1.cells m k = true)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hk_eq : k = 2) (hkN : k ≤ 2 ^ n)
    (passes : List GHZoomPassFn) (hW : passes.length ≤ 16)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;; (ghZoomRotCircuit res (Stage1.cells_mem_grid hmk).1 (Stage1.cells_mem_grid hmk).2
      hm2 hk2 passes hW n).compile qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp fun σ ↦ decodeTargets n k (σ res) = S ⦄ := by
  have hm_grid := (Stage1.cells_mem_grid hmk).1
  have hk_grid := (Stage1.cells_mem_grid hmk).2
  by_cases hn420 : 420 ≤ n
  · unfold ghZoomRotCircuit
    rw [dite_eq_left hn420, dite_eq_left hkN, dite_eq_left hk_eq]
    dsimp only
    let p := Stage2CertInternals.gridExp m
    have hgb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2
    have hp10 : p ≤ 10 := hgb.2.1
    have hm_pow : m = 2 ^ p := hgb.2.2.symm
    have hm2_pow : m * m = 2 ^ (2 * p) := by rw [hm_pow, ← pow_add, Nat.two_mul]
    have hp_le : p ≤ n := by omega
    have hp2_le : 2 * p ≤ n := by omega
    have hs : (n - passes.length * p) + passes.length * p = n :=
      Nat.sub_add_cancel ((Nat.mul_le_mul hW hp10).trans (by omega))
    have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    have hk1 : 1 ≤ k := by omega
    have hM : 1 ≤ k * n := Nat.mul_pos (by omega) (by omega)
    have hsub3 : 3 ≤ 2 ^ (n - p) := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - p) := Nat.pow_le_pow_right (by omega) (by omega)
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
    have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
    let bFn (u : ℕ) : ℕ := if u < k - 1 then stage2Batch m (k - u) else 1
    let gFn (u : ℕ) : ℕ := if u < k - 1 then stage2Group m (k - u) else m
    have hbg : ∀ u < k, bFn u * gFn u = m := fun u _ ↦ by
      dsimp only [bFn, gFn]
      by_cases hlt : u < k - 1
      · rw [ite_eq_left hlt, ite_eq_left hlt]
        exact (stage2_bg hm_grid hm2 (by omega) (by omega)).2
      · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul]
    have hb : ∀ u < k - 1, 1 ≤ bFn u := fun u hu ↦ by
      dsimp only [bFn]; rw [ite_eq_left hu]
      exact (stage2_bg hm_grid hm2 (by omega) (by omega)).1
    set scale : ℝ := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
    have hscale_nn : 0 ≤ scale := by dsimp only [scale]; positivity [Real.pi_pos]
    have hdrift_sc : ∀ u < k - 1,
        ((K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u) + 1 : ℕ) : ℝ) +
          (∑ cs : Fin (bFn u) → Option (Fin (k - u)),
            iidCouponProb n (gFn u) (k - u)
              (K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u)) cs *
              (stage2NormPot m k (u + ((List.finRange (bFn u)).filterMap cs).dedup.length) *
                scale)) ≤
          stage2NormPot m k u * scale := by
      intro u hu
      have hbg_u := hbg u (by omega)
      have hb1 := hb u hu
      have hg1 : 1 ≤ gFn u := by
        by_contra hg0; push Not at hg0
        have : gFn u = 0 := by omega
        rw [this, mul_zero] at hbg_u; omega
      have hg_hi : gFn u ≤ 1024 :=
        (hbg_u ▸ Nat.le_mul_of_pos_left (gFn u) hb1).trans hm_hi
      have hr1 : 1 ≤ k - u := by omega
      have hr_hi : k - u ≤ 1024 := by omega
      have hK_le :
          ((K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u) + 1 : ℕ) : ℝ) ≤
            varPhiCHi (stage2Angle m (k - u)) * √((bFn u : ℝ) / (k - u : ℕ)) * scale := by
        simpa [scale] using (K_varPhi_add_one_bounds (stage2Angle m (k - u)) (by omega) hg1 hg_hi
          hr1 hr_hi).2.2 (bFn u) m hb1 hbg_u
      have hp_bnds := varPhiGroupSuccProb_bounds (stage2Angle m (k - u)) (n := n) (by omega)
        hg1 hg_hi hr1 hr_hi
      have hsum_W := sum_iidCouponProb_le_couponStepUpper_iter (b := bFn u) hr1
        hp_bnds.2.1 hp_bnds.2.2 (fun d ↦ stage2NormPot m k (u + d))
      have hsum_sc :
          (∑ cs : Fin (bFn u) → Option (Fin (k - u)),
            iidCouponProb n (gFn u) (k - u)
              (K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u)) cs *
              (stage2NormPot m k (u + ((List.finRange (bFn u)).filterMap cs).dedup.length) *
                scale)) ≤
            ((couponStepUpper (varPhiSinLo (stage2Angle m (k - u)) ^ 2)
              (varPhiSinHi (stage2Angle m (k - u)) ^ 2) (k - u))^[bFn u]
              (fun d ↦ stage2NormPot m k (u + d)) 0) * scale := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hsum_W hscale_nn
      have hce : stage2CouponStepUpper = couponStepUpper := rfl
      have hdr_u := stage2NormPot_drift hm_grid hk_grid hm2 hk2 u hu
      dsimp only at hdr_u
      have hb_eq : bFn u = stage2Batch m (k - u) := ite_eq_left hu
      rw [← hb_eq, hce] at hdr_u
      linarith [mul_le_mul_of_nonneg_right hdr_u hscale_nn]
    let pPasses := ghZoomPermPasses hs hm_pow passes rfl
    rcases ghZoomOccLaw_props hn hk1 hk_eq hm1 hkN hM hp2_le hm2_pow hp_le hm_pow hsub3 pPasses
      hcard with ⟨hP_nn, hP_sum, hP_exp⟩
    unfold Stage1.qubits
    refine Triple.of_eq_wp ?_
    exact (wp_init_seq_findAllBatchTail_of_drift res hm1 hkN hbg
      (fun u ↦ K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u))
      (ghZoomMultiSweepPre res hm1 hk1 hkN hM hp2_le hm2_pow hp_le hm_pow pPasses)
      (eigLockStage res n m k hm_grid hk_grid (by omega) ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
      hcard (ghZoomOccLaw (k := k) hp2_le hp_le hm_pow pPasses S)
      (fun s _ ↦ hP_nn s) hP_sum
      (fun Θ f hΘ σ ↦ by
        rw [wp_qSet_ghZoomMultiSweepPre_of_invariant res hn hk1 hk_eq hm1 hkN hM
          hp2_le hm2_pow hp_le hm_pow hsub3 pPasses hcard Θ f hΘ σ, ← hP_exp f])
      (fun τ μ hτ hval ↦ wp_eigLockStage_last_workMemIdx_eq_one res hm_grid hk_grid (by omega)
        hk1 hcard τ μ hτ hval)
      (fun u ↦ stage2NormPot m k u * scale)
      (fun u hu ↦ mul_nonneg (stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 u hu) hscale_nn)
      hdrift_sc).symm
  · unfold ghZoomRotCircuit
    rw [dite_eq_right hn420]
    exact Stage1.correctness res hn hmk hkN hS
/-- Asymptotic average-case parallel oracle query bound for `ghZoomRotCircuit` from any
  certified
  backward potential sequence satisfying `ghZoomOneDimUpper` on `0.. k` and `Stage2`
  boundary
  `potWInt`. -/
theorem ghZoomRotCircuit_relCost_of_drift {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hk_eq : k = 2)
    (passes : List GHZoomPassFn) (hW : passes.length ≤ 16)
    (M_q : ℝ) (hMq : 0 ≤ M_q)
    (hq_bound : ∀ subN, 210 ≤ subN → ∀ pf ∈ passes, ∀ r ≤ k,
      ∀ kInit probes kZoom, pf subN r = some (kInit, probes, kZoom) →
        (ghZoomMaxQueries kInit probes kZoom : ℝ) ≤ M_q * ((π / 4) * √(2 ^ subN : ℝ)))
    (vOut : ℕ → ℕ) (num den : ℕ) (hden : 1 ≤ den)
    (hpot : ∀ subN, 210 ≤ subN →
      let p := Stage2CertInternals.gridExp m
      let scale : ℝ := ((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ)
      ∃ fFinal : ℕ → ℝ,
        (∀ r ≤ k, 0 ≤ fFinal r ∧
          (Stage2CertInternals.potWInt
            ⟨p - 1, by
              have hb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2; omega⟩
            r : ℝ) * scale ≤ fFinal r) ∧
        fFinal 0 = 0 ∧
        (∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ k → fFinal u₁ ≤ fFinal u₂) ∧
        ∃ fSeq : List (ℕ → ℝ),
          fSeq.length = passes.length + 1 ∧
          fSeq.getLast? = some fFinal ∧
          (∀ i (hi : i < passes.length),
            let fNext := fSeq.getD (i + 1) fFinal
            let fCur := fSeq.getD i fFinal
            fCur 0 = 0 ∧
              (∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ k → fCur u₁ ≤ fCur u₂) ∧
              (∀ r ≤ k, ghZoomOneDimUpper subN p m (passes[i] subN r) fNext r ≤ fCur r)) ∧
          fSeq.headD fFinal = fun r ↦ (vOut r : ℝ) * scale)
    (hratio : den * (vOut k + 1) ≤
      num * Stage2CertInternals.treeSum (Stage2CertInternals.gridExp k) 0
        (fun x ↦ Stage2CertInternals.invSqrtLo (x + 1))) :
    let c_rel : ℚ≥0 := (num : ℚ≥0) / (den : ℚ≥0)
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦
          qset ;; (ghZoomRotCircuit res hm_grid hk_grid hm2 hk2 passes hW n).compile
            qAssign (groverParallelMarkingOracle m S))
        ((c_rel : ℝ) * vanillaFindAllCost n m k) := by
  intro c_rel
  let M_pot : ℝ := ∑ u ∈ Finset.range (k + 1), stage2NormPot m k u
  have hMpot_nn : 0 ≤ M_pot :=
    Finset.sum_nonneg fun u hu ↦
      stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu))
  let C_bad : ℝ := 16 * (M_q + 1) + M_pot
  have hCbad_pos : 0 < C_bad := by dsimp only [C_bad]; linarith
  let s₀ : ℕ := Nat.ceil ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) + 1
  refine ⟨max 420 (s₀ + 160), fun n hn_ge hkN ↦ ?_⟩
  have hn420 : 420 ≤ n := le_trans (le_max_left _ _) hn_ge
  have hs0_le : s₀ + 160 ≤ n := le_trans (le_max_right _ _) hn_ge
  unfold ghZoomRotCircuit
  rw [dite_eq_left hn420, dite_eq_left hkN, dite_eq_left hk_eq]
  dsimp only
  let p := Stage2CertInternals.gridExp m
  have hgb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2
  have hgm1 : 1 ≤ p := hgb.1
  have hp10 : p ≤ 10 := hgb.2.1
  have hm_pow : m = 2 ^ p := hgb.2.2.symm
  have hm2_pow : m * m = 2 ^ (2 * p) := by rw [hm_pow, ← pow_add, Nat.two_mul]
  have hp_le : p ≤ n := by omega
  have hp2_le : 2 * p ≤ n := by omega
  have hs : (n - passes.length * p) + passes.length * p = n :=
    Nat.sub_add_cancel ((Nat.mul_le_mul hW hp10).trans (by omega))
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hk1 : 1 ≤ k := by omega
  have hn1 : 1 ≤ n := by omega
  have hM : 1 ≤ k * n := Nat.mul_pos hk1 hn1
  have hsub210 : 210 ≤ n - p := by omega
  have hsub3 : 3 ≤ 2 ^ (n - p) := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - p) := Nat.pow_le_pow_right (by omega) (by omega)
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  let bFn (u : ℕ) : ℕ := if u < k - 1 then stage2Batch m (k - u) else 1
  let gFn (u : ℕ) : ℕ := if u < k - 1 then stage2Group m (k - u) else m
  have hbg : ∀ u < k, bFn u * gFn u = m := fun u _ ↦ by
    dsimp only [bFn, gFn]
    by_cases hlt : u < k - 1
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact (stage2_bg hm_grid hm2 (by omega) (by omega)).2
    · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul]
  have hb : ∀ u < k - 1, 1 ≤ bFn u := fun u hu ↦ by
    dsimp only [bFn]; rw [ite_eq_left hu]
    exact (stage2_bg hm_grid hm2 (by omega) (by omega)).1
  set scale : ℝ := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
  have hscale_pos : 0 < scale := by
    dsimp only [scale]
    exact mul_pos (div_pos Real.pi_pos (by norm_num))
      (Real.sqrt_pos.mpr (div_pos (by positivity) (by positivity)))
  have hscale_nn : 0 ≤ scale := hscale_pos.le
  have hscale_sub : (π / 4) * √(2 ^ (n - p) : ℝ) = scale := by
    dsimp only [scale]
    rw [two_pow_sub_eq_div_gh hp_le hm_pow]
  have hMscale_pos : (0 : ℝ) < (Stage2CertInternals.M_scale : ℝ) := by
    unfold Stage2CertInternals.M_scale; norm_num
  have hlast_le : (Real.toNNReal ((stage1RelCost : ℝ) * scale) : ℝ) ≤
      stage2NormPot m k (k - 1) * scale := by
    rw [Real.coe_toNNReal _ (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ hscale_nn
    have hst : (stage1RelCost : ℝ) ≤ 81831 / 100000 := by unfold stage1RelCost; norm_num
    exact hst.trans (stage2NormPot_last hm_grid hk_grid hm2 hk2)
  have hdrift_sc : ∀ u < k - 1,
      ((K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u) + 1 : ℕ) : ℝ) +
        (∑ cs : Fin (bFn u) → Option (Fin (k - u)),
          iidCouponProb n (gFn u) (k - u)
            (K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u)) cs *
            (stage2NormPot m k (u + ((List.finRange (bFn u)).filterMap cs).dedup.length) *
              scale)) ≤
        stage2NormPot m k u * scale := by
    intro u hu
    have hbg_u := hbg u (by omega)
    have hb1 := hb u hu
    have hg1 : 1 ≤ gFn u := by
      by_contra hg0; push Not at hg0
      have : gFn u = 0 := by omega
      rw [this, mul_zero] at hbg_u; omega
    have hg_hi : gFn u ≤ 1024 :=
      (hbg_u ▸ Nat.le_mul_of_pos_left (gFn u) hb1).trans hm_hi
    have hr1 : 1 ≤ k - u := by omega
    have hr_hi : k - u ≤ 1024 := by omega
    have hK_le :
        ((K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u) + 1 : ℕ) : ℝ) ≤
          varPhiCHi (stage2Angle m (k - u)) * √((bFn u : ℝ) / (k - u : ℕ)) * scale := by
      simpa [scale] using (K_varPhi_add_one_bounds (stage2Angle m (k - u)) (by omega) hg1 hg_hi
        hr1 hr_hi).2.2 (bFn u) m hb1 hbg_u
    have hp_bnds := varPhiGroupSuccProb_bounds (stage2Angle m (k - u)) (n := n) (by omega)
      hg1 hg_hi hr1 hr_hi
    have hsum_W := sum_iidCouponProb_le_couponStepUpper_iter (b := bFn u) hr1
      hp_bnds.2.1 hp_bnds.2.2 (fun d ↦ stage2NormPot m k (u + d))
    have hsum_sc :
        (∑ cs : Fin (bFn u) → Option (Fin (k - u)),
          iidCouponProb n (gFn u) (k - u)
            (K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u)) cs *
            (stage2NormPot m k (u + ((List.finRange (bFn u)).filterMap cs).dedup.length) *
              scale)) ≤
          ((couponStepUpper (varPhiSinLo (stage2Angle m (k - u)) ^ 2)
            (varPhiSinHi (stage2Angle m (k - u)) ^ 2) (k - u))^[bFn u]
            (fun d ↦ stage2NormPot m k (u + d)) 0) * scale := by
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hsum_W hscale_nn
    have hce : stage2CouponStepUpper = couponStepUpper := rfl
    have hdr_u := stage2NormPot_drift hm_grid hk_grid hm2 hk2 u hu
    dsimp only at hdr_u
    have hb_eq : bFn u = stage2Batch m (k - u) := ite_eq_left hu
    rw [← hb_eq, hce] at hdr_u
    linarith [mul_le_mul_of_nonneg_right hdr_u hscale_nn]
  let pPasses := ghZoomPermPasses hs hm_pow passes rfl
  let M_step : ℝ := (M_q + 1) * scale
  have hMstep_pos : 0 < M_step := mul_pos (by linarith) hscale_pos
  have hspec_rmax :
      ∀ ps ∈ pPasses, ∀ r ≤ k, (ghZoomRoundMaxQ (ps.2 r) : ℝ) ≤ M_step := by
    intro ps hps r hr
    unfold pPasses ghZoomPermPasses at hps
    rcases List.mem_map.mp hps with ⟨i, _, rfl⟩
    have hmem : passes[i.val] ∈ passes := List.getElem_mem i.isLt
    dsimp only [ghZoomRoundMaxQ]
    generalize hsome : passes[i.val] (n - p) r = q_opt
    cases q_opt with
    | none => simpa using hMstep_pos.le
    | some kpz =>
      rcases kpz with ⟨kInit, probes, kZoom⟩
      have hqb := hq_bound (n - p) hsub210 passes[i.val] hmem r hr kInit probes kZoom hsome
      rw [hscale_sub] at hqb
      dsimp only [M_step]
      linarith
  let wFn (S : Finset (Fin (2 ^ n))) : ℝ :=
    if S.card = k then
      ghZoomCircDP hp2_le hp_le hm_pow true pPasses (fun R ↦ stage2NormPot m k (k - R.card) * scale)
        S
    else 0
  have hw_nn (S : Finset (Fin (2 ^ n))) : 0 ≤ wFn S := by
    dsimp only [wFn]
    split_ifs with hcard
    · exact ghZoomCircDP_nonneg hp2_le hp_le hm_pow true pPasses fun R _ ↦
        mul_nonneg (stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 _ (Nat.sub_le _ _)) hscale_nn
    · exact le_rfl
  unfold Stage1.qubits
  refine ⟨fun S ↦ ⟨wFn S, hw_nn S⟩, fun S hS ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    rcases ghZoomOccLaw_props hn1 hk1 hk_eq hm1 hkN hM hp2_le hm2_pow hp_le hm_pow hsub3
      pPasses hcard with ⟨hP_nn, hP_sum, hP_exp⟩
    rcases expectedCost_and_bound_ghZoomMultiSweepPre res hn1 hk1 hk_eq hm1 hkN hM
      hp2_le hm2_pow hp_le hm_pow hsub3 pPasses hcard hMstep_pos hspec_rmax with
      ⟨hinit_cost, _⟩
    have hc_init_nn : 0 ≤ ghZoomCircDP hp2_le hp_le hm_pow true pPasses (fun _ ↦ 0) S :=
      ghZoomCircDP_nonneg hp2_le hp_le hm_pow true pPasses fun _ _ ↦ le_rfl
    change CostBound _
      (.qSet ;; ((ghZoomMultiSweepPre res hm1 hk1 hkN hM hp2_le hm2_pow hp_le hm_pow pPasses).seq
        (findAllBatchTail res hm1 hkN hbg
          (fun u ↦ K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u))
          (eigLockStage res n m k hm_grid hk_grid (by omega)
            ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩))).compile qAssign
        (groverParallelMarkingOracle m S)) _
    refine costBound_init_seq_findAllBatchTail_of_drift res hm1 hkN hbg
      (fun u ↦ K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u))
      (ghZoomMultiSweepPre res hm1 hk1 hkN hM hp2_le hm2_pow hp_le hm_pow pPasses)
      (eigLockStage res n m k hm_grid hk_grid (by omega) ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
      hcard (ghZoomOccLaw (k := k) hp2_le hp_le hm_pow pPasses S)
      (fun s _ ↦ hP_nn s) hP_sum
      (fun Θ f hΘ σ ↦ by
        rw [wp_qSet_ghZoomMultiSweepPre_of_invariant res hn1 hk1 hk_eq hm1 hkN hM
          hp2_le hm2_pow hp_le hm_pow hsub3 pPasses hcard Θ f hΘ σ, ← hP_exp f])
      (Real.toNNReal (ghZoomCircDP hp2_le hp_le hm_pow true pPasses (fun _ ↦ 0) S)) hinit_cost
      (validObs n m k S (k - 1))
      (fun τ μ _ hval ↦ validObs_apply_workMemIdx_eq_one τ hval)
      (Real.toNNReal ((stage1RelCost : ℝ) * scale))
      (expectedCost_eigLockStage_last_le res hm_grid hk_grid (by omega) hk1 hcard)
      (fun u ↦ stage2NormPot m k u * scale) ⟨wFn S, hw_nn S⟩
      (fun u hu ↦ mul_nonneg (stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 u hu) hscale_nn)
      hlast_le hdrift_sc ?_
    rw [Real.coe_toNNReal _ hc_init_nn]
    change ghZoomCircDP hp2_le hp_le hm_pow true pPasses (fun _ ↦ 0) S + _ ≤ wFn S
    dsimp only [wFn]
    rw [ite_eq_left hcard, hP_exp (fun u ↦ stage2NormPot m k u * scale),
      ← ghZoomCircDP_true_eq_cost_add_false]
  · change (∑ S ∈ groverTargetSets n k, wFn S) / ((groverTargetSets n k).card : ℝ) ≤ _
    let e := rotatedSliceEquiv hs hm_pow
    let im : Fin 10 := ⟨p - 1, by omega⟩
    let scale_s : ℝ := scale / (Stage2CertInternals.M_scale : ℝ)
    let V_tail (u : ℕ) : ℝ := (Stage2CertInternals.potWInt im u : ℝ) * scale_s
    have hpot_sub := hpot (n - p) hsub210
    dsimp only at hpot_sub
    rw [hscale_sub] at hpot_sub
    rcases hpot_sub with ⟨fFinal, hfFinal_bnd, hfFinal0, hfFinal_mono,
      fSeq, hfSeq_len, hfSeq_last, hfSeq_step, hfSeq_head⟩
    have hgetD_last : fSeq.getD passes.length fFinal = fFinal :=
      getD_last_of_getLast?_gh fFinal fSeq passes.length hfSeq_len hfSeq_last
    have hdp_ind : ∀ d ≤ passes.length, ∀ r ≤ k,
        ghZoomExactOneDimDP (n - p) p m ((passes.drop (passes.length - d)).map fun pf ↦ pf (n - p))
          V_tail r ≤ fSeq.getD (passes.length - d) fFinal r := by
      intro d
      induction d with
      | zero =>
        intro _ r hr
        simp only [Nat.sub_zero, List.drop_length, List.map_nil, ghZoomExactOneDimDP, hgetD_last]
        exact (hfFinal_bnd r hr).2
      | succ d ih =>
        intro hd r hr
        set i := passes.length - (d + 1)
        have hi : i < passes.length := by omega
        have hi1 : passes.length - d = i + 1 := by omega
        rw [drop_eq_getElem_cons_gh passes hi, List.map_cons, ghZoomExactOneDimDP]
        have hfNext0 : fSeq.getD (i + 1) fFinal 0 = 0 := by
          by_cases hi_next : i + 1 < passes.length
          · exact (hfSeq_step (i + 1) hi_next).1
          · have heq_len : i + 1 = passes.length := by omega
            rw [heq_len, hgetD_last]
            exact hfFinal0
        have h1 :
            ghZoomExactOneDimStep (n - p) p m (passes[i] (n - p))
                (ghZoomExactOneDimDP (n - p) p m ((passes.drop (i + 1)).map fun pf ↦ pf (n - p))
                  V_tail)
                r ≤
              ghZoomExactOneDimStep (n - p) p m (passes[i] (n - p))
                (fSeq.getD (i + 1) fFinal) r := by
          refine ghZoomExactOneDimStep_mono_on (n - p) p m hm1 (passes[i] (n - p)) fun u hu ↦ ?_
          simpa only [hi1] using ih (by omega) u (hu.trans hr)
        have h2 := ghZoomExactOneDimStep_le_ghZoomOneDimUpper (n - p) p m (passes[i] (n - p))
          (r := r) hfNext0
        exact (h1.trans h2).trans ((hfSeq_step i hi).2.2 r hr)
    have hdp_top :
        ghZoomExactOneDimDP (n - p) p m (passes.map fun pf ↦ pf (n - p)) V_tail k ≤
          (vOut k : ℝ) * scale_s := by
      have htop := hdp_ind passes.length le_rfl k le_rfl
      have hgetD0 : fSeq.getD 0 fFinal = fSeq.headD fFinal := by cases fSeq <;> rfl
      simpa only [Nat.sub_self, List.drop_zero, hgetD0, hfSeq_head] using htop
    have hw_max (S : Finset (Fin (2 ^ n))) (hS : S ∈ groverTargetSets n k) :
        wFn S ≤ C_bad * scale := by
      have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
      dsimp only [wFn]
      rw [ite_eq_left hcard, ghZoomCircDP_true_eq_cost_add_false]
      have hcost_le :
          ghZoomCircDP hp2_le hp_le hm_pow true pPasses (fun _ ↦ 0) S ≤
            16 * (M_q + 1) * scale := by
        have hbnd := (expectedCost_and_bound_ghZoomMultiSweepPre (Var := Var) res hn1 hk1 hk_eq
          hm1 hkN hM hp2_le hm2_pow hp_le hm_pow hsub3 pPasses hcard hMstep_pos hspec_rmax).2
        have hlen_p : pPasses.length = passes.length := by simp [pPasses, ghZoomPermPasses]
        have hlen16 : (pPasses.length : ℝ) ≤ 16 := by rw [hlen_p]; exact_mod_cast hW
        calc ghZoomCircDP hp2_le hp_le hm_pow true pPasses (fun _ ↦ 0) S
            ≤ (pPasses.length : ℝ) * M_step := hbnd
          _ ≤ 16 * M_step := mul_le_mul_of_nonneg_right hlen16 hMstep_pos.le
          _ = 16 * (M_q + 1) * scale := by dsimp only [M_step]; ring
      rcases ghZoomOccLaw_props hn1 hk1 hk_eq hm1 hkN hM hp2_le hm2_pow hp_le hm_pow hsub3
        pPasses hcard with ⟨hP_nn, hP_sum, hP_exp⟩
      have hrem_le :
          ghZoomCircDP hp2_le hp_le hm_pow false pPasses
              (fun R ↦ stage2NormPot m k (k - R.card) * scale) S ≤
            M_pot * scale := by
        rw [← hP_exp (fun u ↦ stage2NormPot m k u * scale)]
        calc (∑ u ∈ Finset.range (k + 1),
              ghZoomOccLaw (k := k) hp2_le hp_le hm_pow pPasses S u *
                (stage2NormPot m k u * scale))
            ≤ ∑ u ∈ Finset.range (k + 1),
                ghZoomOccLaw (k := k) hp2_le hp_le hm_pow pPasses S u * (M_pot * scale) := by
              refine Finset.sum_le_sum fun u hu ↦
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hscale_nn) (hP_nn u)
              exact Finset.single_le_sum
                (fun v hv ↦ stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 v
                  (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))) hu
          _ = M_pot * scale := by
              rw [← Finset.sum_mul, hP_sum, one_mul]
      dsimp only [C_bad]
      linarith
    have hgood_avg (U : Finset (Fin (2 ^ (n - passes.length * p)))) (hU : U.card = k) :
        (∑ f : Fin k → Fin passes.length → Fin m, wFn (mkGoodTargetSet e U hU f)) /
          (((m ^ passes.length) ^ k : ℕ) : ℝ) ≤ (vOut k : ℝ) * scale_s := by
      let fPasses := (List.finRange passes.length).map fun i ↦ (i, passes[i.val] (n - p))
      have hw_good (f : Fin k → Fin passes.length → Fin m) :
          wFn (mkGoodTargetSet e U hU f) =
            ghZoomSubsetDP (n - p) p (slicesOf e) fPasses (fun R' ↦ V_tail R'.card)
              (mkGoodTargetSet e U hU f) := by
        have hSc : (mkGoodTargetSet e U hU f).card = k := card_mkGoodTargetSet e U hU f
        dsimp only [wFn]
        rw [ite_eq_left hSc]
        unfold pPasses ghZoomPermPasses
        rw [ghZoomCircDP_map_swap_eq hs hp2_le hp_le hm_pow passes rfl
          (List.finRange passes.length)]
        refine ghZoomSubsetDP_congr_on_subset (n - p) p (slicesOf e) fPasses fun R' hR' ↦ ?_
        have hrc : R'.card ≤ k := hSc ▸ Finset.card_le_card hR'
        have hsub_k : k - (k - R'.card) = R'.card := by omega
        unfold stage2NormPot V_tail scale_s
        rw [dite_eq_left ⟨hgm1, hp10⟩, hsub_k]
        ring
      simp_rw [hw_good]
      have hnodup : (fPasses.map Prod.fst).Nodup := by
        have heq_fst : fPasses.map Prod.fst = List.finRange passes.length :=
          List.ext_getElem (by simp [fPasses]) (fun _ _ _ ↦ by simp [fPasses])
        rw [heq_fst]
        exact List.nodup_finRange passes.length
      have hsnd_eq : fPasses.map Prod.snd = passes.map (fun pf ↦ pf (n - p)) :=
        List.ext_getElem (by simp [fPasses]) (fun _ _ _ ↦ by simp [fPasses])
      rw [avg_ghZoomSubsetDP_mkGoodTargetSet_eq e hm1 (n - p) p fPasses hnodup V_tail U hU, hsnd_eq]
      exact hdp_top
    have hs_ge : s₀ ≤ n - passes.length * p := by
      have hmul160 : passes.length * p ≤ 160 := (Nat.mul_le_mul hW hp10).trans (by norm_num)
      omega
    have hk_le_s : k ≤ 2 ^ (n - passes.length * p) := by
      have hk_1024 : k ≤ 2 ^ 10 := hk_hi
      have h10_s : 10 ≤ n - passes.length * p := by
        have hmul160 : passes.length * p ≤ 160 := (Nat.mul_le_mul hW hp10).trans (by norm_num)
        omega
      exact hk_1024.trans (Nat.pow_le_pow_right (by omega) h10_s)
    have havg := avg_groverTargetSets_le_of_goodSuffix e hm1 hk_le_s
      (G_iid := (vOut k : ℝ) * scale_s) (W_max := C_bad * scale)
      (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hscale_nn hMscale_pos.le))
      (mul_nonneg hCbad_pos.le hscale_nn) hw_max hgood_avg
    have hbad_small :
        ((k : ℝ) ^ 2 / (2 ^ (n - passes.length * p) : ℝ)) * (C_bad * scale) ≤ scale_s := by
      set s := n - passes.length * p
      have hs_pow : ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) ≤ (2 ^ s : ℝ) := by
        have hceil := Nat.le_ceil ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ))
        have hs0_lt : (s₀ : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
        have hpow_lt : (s : ℝ) < (2 ^ s : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
        have hceil_s0 :
            (Nat.ceil ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) : ℝ) <
              (s₀ : ℝ) := by
          dsimp only [s₀]; push_cast; linarith
        linarith
      have h2s_pos : (0 : ℝ) < (2 ^ s : ℝ) := by positivity
      have hdiv1 :
          ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) / (2 ^ s : ℝ) ≤ 1 :=
        (div_le_one h2s_pos).mpr hs_pow
      have hrew :
          ((k : ℝ) ^ 2 / (2 ^ s : ℝ)) * (C_bad * scale) =
            (((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) / (2 ^ s : ℝ)) *
              scale_s := by
        dsimp only [scale_s]
        field_simp [h2s_pos.ne', hMscale_pos.ne']
      rw [hrew]
      exact (mul_le_mul_of_nonneg_right hdiv1 (div_nonneg hscale_nn hMscale_pos.le)).trans_eq
        (one_mul _)
    have hv_plus1 :
        (vOut k : ℝ) * scale_s +
            ((k : ℝ) ^ 2 / (2 ^ (n - passes.length * p) : ℝ)) * (C_bad * scale) ≤
          (((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ)) * scale := by
      have heq_rhs :
          (((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ)) * scale =
            (vOut k : ℝ) * scale_s + scale_s := by
        dsimp only [scale_s]
        push_cast
        ring
      rw [heq_rhs]
      linarith [hbad_small]
    set hsum := Stage2CertInternals.treeSum (Stage2CertInternals.gridExp k) 0
      (fun x ↦ Stage2CertInternals.invSqrtLo (x + 1))
    have hsum_le : (hsum : ℝ) / (Stage2CertInternals.M_scale : ℝ) ≤
        groverHarmonicSqrtSum k := by
      have hk_gb := Stage2CertInternals.gridExp_bounds_of_mem hk_grid hk2
      rw [groverHarmonicSqrtSum_eq_sum_range]
      have hts : hsum = ∑ x ∈ Finset.range k, Stage2CertInternals.invSqrtLo (x + 1) := by
        dsimp only [hsum]
        rw [Stage2CertInternals.treeSum_eq_sum_Ico, zero_add, hk_gb.2.2, Nat.Ico_zero_eq_range]
      rw [hts, Nat.cast_sum, Finset.sum_div]
      exact Finset.sum_le_sum fun x hx ↦
        Stage2CertInternals.invSqrtLo_bound (by omega)
          (by have := Finset.mem_range.mp hx; omega)
    have hden_pos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
    have hratio_r : (den : ℝ) * ((vOut k + 1 : ℕ) : ℝ) ≤ (num : ℝ) * (hsum : ℝ) := by
      exact_mod_cast hratio
    have hc_rel_eq : (c_rel : ℝ) = (num : ℝ) / (den : ℝ) := by
      dsimp only [c_rel]; push_cast; rfl
    have hrat_le :
        ((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ) ≤
          (c_rel : ℝ) * ((hsum : ℝ) / (Stage2CertInternals.M_scale : ℝ)) := by
      rw [hc_rel_eq, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hMscale_pos.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hden_pos]
      linarith
    have hfin :
        (((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ)) * scale ≤
          (c_rel : ℝ) * vanillaFindAllCost n m k := by
      rw [vanillaFindAllCost]
      have h1 := hrat_le.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
      exact (mul_le_mul_of_nonneg_right h1 hscale_nn).trans_eq (by dsimp only [scale]; ring)
    exact (havg.trans hv_plus1).trans hfin
end
end QuantumComputation.Specs.DickeSol
end GHZoomQHL
section GHZoom_EvalAndSoundness
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped NNReal NNRat ENNReal QProg.Notation QHLExpectation
@[expose] public section
/-! ## Shared `WDCVal` (`10 ^ 15`-Scaled Complex-Interval) Arithmetic & GMP WHNF Forcing -/
/-- Complex outward interval `(reIV, imIV)` scaled by `wdScale = 10 ^ 15`. -/
abbrev WDCVal := WDIVal × WDIVal
/-- Membership predicate `z ∈ iv / 10 ^ 15` on `ℂ = ℝ + i ℝ`. -/
def wdCMem (z : ℂ) (iv : WDCVal) : Prop :=
  wdMem z.re iv.1 ∧ wdMem z.im iv.2
/-- `O(1)` GMP-literal WHNF forcing for `ℕ` (`Nat.add n 1` preserves `Literal.natVal`). -/
def ghForceNat : ℕ → ℕ
  | .zero => 0
  | .succ n => Nat.add n 1
theorem ghForceNat_eq (n : ℕ) : ghForceNat n = n := by
  cases n <;> rfl
/-- Pure-GMP WHNF-forcing `ℤ` wrapper (`O(1)` `Literal.natVal` fold on `Nat.succ`). -/
def ghForceInt : ℤ → ℤ
  | .ofNat .zero => .ofNat 0
  | .ofNat (.succ k) => .ofNat (Nat.succ k)
  | .negSucc .zero => .negSucc 0
  | .negSucc (.succ k) => .negSucc (Nat.succ k)
theorem ghForceInt_eq (z : ℤ) : ghForceInt z = z := by
  rcases z with (_ | k) | (_ | k) <;> rfl
/-- Strict CPS WHNF barrier forcing both `ℤ` endpoints of `iv` before evaluating `k`. -/
def ghSeqIV {α : Type*} (iv : WDIVal) (k : WDIVal → α) : α :=
  match ghForceInt iv.1, ghForceInt iv.2 with
  | Int.ofNat a, Int.ofNat b => k (Int.ofNat a, Int.ofNat b)
  | Int.ofNat a, Int.negSucc b => k (Int.ofNat a, Int.negSucc b)
  | Int.negSucc a, Int.ofNat b => k (Int.negSucc a, Int.ofNat b)
  | Int.negSucc a, Int.negSucc b => k (Int.negSucc a, Int.negSucc b)
theorem ghSeqIV_eq {α : Type*} (iv : WDIVal) (k : WDIVal → α) : ghSeqIV iv k = k iv := by
  rcases iv with ⟨a, b⟩
  unfold ghSeqIV
  rw [ghForceInt_eq, ghForceInt_eq]
  cases a <;> cases b <;> rfl
/-- Forces both endpoints of a `WDIVal` before constructing the pair. -/
def ghForceIV (iv : WDIVal) : WDIVal :=
  ghSeqIV iv id
theorem ghForceIV_eq (iv : WDIVal) : ghForceIV iv = iv := by
  simp only [ghForceIV, ghSeqIV_eq, id_eq]
/-- Strict CPS WHNF barrier forcing all four `ℤ` endpoints of `z` before evaluating `k`. -/
def ghSeqCIV {α : Type*} (z : WDCVal) (k : WDCVal → α) : α :=
  ghSeqIV z.1 fun re' ↦ ghSeqIV z.2 fun im' ↦ k (re', im')
theorem ghSeqCIV_eq {α : Type*} (z : WDCVal) (k : WDCVal → α) : ghSeqCIV z k = k z := by
  rcases z with ⟨_, _⟩
  simp only [ghSeqCIV, ghSeqIV_eq]
/-- Forces all four `ℤ` endpoints of a `WDCVal` via `ghSeqCIV` before constructing the pair. -/
def ghForceCIV (z : WDCVal) : WDCVal :=
  ghSeqCIV z id
theorem ghForceCIV_eq (z : WDCVal) : ghForceCIV z = z := by
  simp only [ghForceCIV, ghSeqCIV_eq, id_eq]
/-- Strict CPS WHNF barrier forcing an entire `List WDCVal` spine before evaluating `k`. -/
def ghSeqCIVList {α : Type*} : List WDCVal → (List WDCVal → α) → α
  | [], k => k []
  | z :: zs, k => ghSeqCIV z fun z' ↦ ghSeqCIVList zs fun zs' ↦ k (z' :: zs')
theorem ghSeqCIVList_eq {α : Type*} (xs : List WDCVal) (k : List WDCVal → α) :
    ghSeqCIVList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons z zs ih => simp only [ghSeqCIVList, ghSeqCIV_eq, ih]
/-- Strict CPS WHNF barrier forcing a `List (List WDCVal)` matrix before evaluating `k`. -/
def ghSeqCIVRows {α : Type*} : List (List WDCVal) → (List (List WDCVal) → α) → α
  | [], k => k []
  | row :: rest, k =>
      ghSeqCIVList row fun row' ↦ ghSeqCIVRows rest fun rest' ↦ k (row' :: rest')
theorem ghSeqCIVRows_eq {α : Type*} (rows : List (List WDCVal))
    (k : List (List WDCVal) → α) : ghSeqCIVRows rows k = k rows := by
  induction rows generalizing k with
  | nil => rfl
  | cons row rest ih => simp only [ghSeqCIVRows, ghSeqCIVList_eq, ih]
/-- Constructor-matched boolean `a ≤ b` on `ℤ` avoiding `LinearOrder` dictionary synthesis. -/
def ghBleZ (a b : ℤ) : Bool :=
  match Int.sub b a with
  | Int.ofNat _ => true
  | Int.negSucc _ => false
theorem ghBleZ_eq_decide (a b : ℤ) : ghBleZ a b = decide (a ≤ b) := by
  unfold ghBleZ
  have hsub : Int.sub b a = b - a := rfl
  rw [hsub]
  cases h : b - a with
  | ofNat n =>
      have hab : a ≤ b := by rw [Int.ofNat_eq_natCast] at h; omega
      simp [hab]
  | negSucc n =>
      have hab : ¬(a ≤ b) := by rw [Int.negSucc_eq] at h; omega
      simp [hab]
/-- Primitive `min` on `ℤ` via `ghBleZ`. -/
def ghMinZ (a b : ℤ) : ℤ :=
  cond (ghBleZ a b) a b
theorem ghMinZ_eq (a b : ℤ) : ghMinZ a b = min a b := by
  unfold ghMinZ
  rw [ghBleZ_eq_decide]
  by_cases h : a ≤ b
  · simp [h]
  · rw [decide_eq_false h]; dsimp [cond]; omega
/-- Primitive `max` on `ℤ` via `ghBleZ`. -/
def ghMaxZ (a b : ℤ) : ℤ :=
  cond (ghBleZ a b) b a
theorem ghMaxZ_eq (a b : ℤ) : ghMaxZ a b = max a b := by
  unfold ghMaxZ
  rw [ghBleZ_eq_decide]
  by_cases h : a ≤ b
  · simp [h]
  · rw [decide_eq_false h]; dsimp [cond]; omega
/-- Primitive `WDIVal` multiplication avoiding Mathlib `LinearOrder ℤ` `min`/`max`. -/
def ghMulIV (x y : WDIVal) : WDIVal :=
  let p1 := Int.mul x.1 y.1
  let p2 := Int.mul x.1 y.2
  let p3 := Int.mul x.2 y.1
  let p4 := Int.mul x.2 y.2
  (wdDivFloor (ghMinZ (ghMinZ p1 p2) (ghMinZ p3 p4)) (wdScale : ℤ),
    wdDivCeil (ghMaxZ (ghMaxZ p1 p2) (ghMaxZ p3 p4)) (wdScale : ℤ))
theorem ghMulIV_eq (x y : WDIVal) : ghMulIV x y = wdMul x y := by
  unfold ghMulIV wdMul
  simp only [Int.mul_def, ghMinZ_eq, ghMaxZ_eq]
/-- Primitive `WDIVal` squaring avoiding Mathlib `LinearOrder ℤ` `min`/`max`. -/
def ghSqIV (x : WDIVal) : WDIVal :=
  let p1 := Int.mul x.1 x.1
  let p2 := Int.mul x.2 x.2
  (cond (ghBleZ x.1 0 && ghBleZ 0 x.2) 0 (wdDivFloor (ghMinZ p1 p2) (wdScale : ℤ)),
    wdDivCeil (ghMaxZ p1 p2) (wdScale : ℤ))
theorem ghSqIV_eq (x : WDIVal) : ghSqIV x = wdSq x := by
  unfold ghSqIV wdSq
  have hm1 : Int.mul x.1 x.1 = x.1 * x.1 := rfl
  have hm2 : Int.mul x.2 x.2 = x.2 * x.2 := rfl
  rw [hm1, hm2]
  simp only [ghBleZ_eq_decide, ghMinZ_eq, ghMaxZ_eq]
  by_cases h1 : x.1 ≤ 0 <;> by_cases h2 : 0 ≤ x.2 <;> simp [h1, h2]
/-- CPS GMP-forced base trigonometric enclosure binding `(c, s)` once before `k c s`. -/
def ghTrigBaseCPS {α : Type*} (u : WDIVal) (k : WDIVal → WDIVal → α) : α :=
  let B : ℤ := wdScale
  let uh2 := wdDivCeil (Int.mul u.2 u.2) B
  let ul2 := wdDivFloor (Int.mul u.1 u.1) B
  let uh4 := wdDivCeil (Int.mul uh2 uh2) B
  let cLo := B - wdDivCeil (Int.mul u.2 u.2) (2 * B)
  let cHi := B - wdDivFloor (Int.mul u.1 u.1) (2 * B) + wdDivCeil uh4 24
  let uh3 := wdDivCeil (Int.mul uh2 u.2) B
  let ul3 := wdDivFloor (Int.mul ul2 u.1) B
  let uh5 := wdDivCeil (Int.mul uh4 u.2) B
  let sLo := ghMaxZ 0 (u.1 - wdDivCeil uh3 6)
  let sHi := u.2 - wdDivFloor ul3 6 + wdDivCeil uh5 120
  ghSeqIV (cLo, cHi) fun c ↦ ghSeqIV (sLo, sHi) fun s ↦ k c s
theorem ghTrigBaseCPS_eq {α : Type*} (u : WDIVal) (k : WDIVal → WDIVal → α) :
    ghTrigBaseCPS u k = k (wdTrigBase u).1 (wdTrigBase u).2 := by
  unfold ghTrigBaseCPS wdTrigBase
  simp only [Int.mul_def, ghSeqIV_eq, ghMaxZ_eq]
/-- CPS GMP-forced 10-step double-angle recursion avoiding `Prod` projection re-evaluation. -/
def ghDoubleAngleIterCPS {α : Type*} :
    ℕ → WDIVal → WDIVal → (WDIVal → WDIVal → α) → α
  | 0, c, s, k => k c s
  | n + 1, c, s, k =>
      ghSeqIV (wdSub (ghSqIV c) (ghSqIV s)) fun c' ↦
        ghSeqIV (wdScaleNat 2 (ghMulIV s c)) fun s' ↦
          ghDoubleAngleIterCPS n c' s' k
theorem ghDoubleAngleIterCPS_eq {α : Type*} :
    ∀ (n : ℕ) (c s : WDIVal) (k : WDIVal → WDIVal → α),
      ghDoubleAngleIterCPS n c s k =
        k (wdDoubleAngleIter n (c, s)).1 (wdDoubleAngleIter n (c, s)).2
  | 0, _, _, _ => rfl
  | n + 1, c, s, k => by
      simp only [ghDoubleAngleIterCPS, wdDoubleAngleIter, ghSeqIV_eq, ghSqIV_eq, ghMulIV_eq]
      exact ghDoubleAngleIterCPS_eq n _ _ k
/-- CPS GMP-forced trigonometric enclosure binding `(c, s)` strictly once before `k c s`. -/
def ghTrigCPS {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) : α :=
  ghSeqIV (wdDivFloor x.1 1024, wdDivCeil x.2 1024) fun u ↦
    ghTrigBaseCPS u fun c0 s0 ↦
      ghDoubleAngleIterCPS 10 c0 s0 k
theorem ghTrigCPS_eq {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) :
    ghTrigCPS x k = k (wdTrig x).1 (wdTrig x).2 := by
  unfold ghTrigCPS wdTrig
  rw [ghSeqIV_eq, ghTrigBaseCPS_eq]
  rcases wdTrigBase (wdDivFloor x.1 1024, wdDivCeil x.2 1024) with ⟨c0, s0⟩
  exact ghDoubleAngleIterCPS_eq 10 c0 s0 k
/-- Fast GMP-forced trigonometric enclosure equivalent to `wdTrig`. -/
def ghTrig (x : WDIVal) : WDIVal × WDIVal :=
  ghTrigCPS x Prod.mk
theorem ghTrig_eq (x : WDIVal) : ghTrig x = wdTrig x := by
  unfold ghTrig
  rw [ghTrigCPS_eq]
/-- Exact complex zero interval `((0, 0), (0, 0))`. -/
def wdCZero : WDCVal := ((0, 0), (0, 0))
/-- Exact complex unit interval `((wdScale, wdScale), (0, 0))`. -/
def wdCOne : WDCVal := (((wdScale : ℤ), (wdScale : ℤ)), (0, 0))
/-- Embeds a real interval `x: WDIVal` along the real axis `(x, (0, 0))`. -/
def wdCOfReal (x : WDIVal) : WDCVal := (x, (0, 0))
/-- Outward complex interval addition. -/
def wdCAdd (a b : WDCVal) : WDCVal := (wdAdd a.1 b.1, wdAdd a.2 b.2)
/-- Outward complex interval subtraction. -/
def wdCSub (a b : WDCVal) : WDCVal := (wdSub a.1 b.1, wdSub a.2 b.2)
/-- Outward complex interval multiplication. -/
def wdCMul (a b : WDCVal) : WDCVal :=
  (wdSub (ghMulIV a.1 b.1) (ghMulIV a.2 b.2), wdAdd (ghMulIV a.1 b.2) (ghMulIV a.2 b.1))
/-- Outward real-by-complex interval scalar multiplication. -/
def wdCRMul (rIV : WDIVal) (zIV : WDCVal) : WDCVal :=
  (ghMulIV rIV zIV.1, ghMulIV rIV zIV.2)
/-- Certified `10 ^ 15`-scaled upper bound on `Complex.normSq z = z.re ^ 2 + z.im ^ 2`. -/
def wdCAbs2Hi (zIV : WDCVal) : ℤ :=
  (ghSqIV zIV.1).2 + (ghSqIV zIV.2).2
/-- Outward interval enclosure of `(aNum + i * bNum) / den`. -/
def wdCGaussRat (aNum bNum : ℤ) (den : ℕ) : WDCVal :=
  (wdRat aNum den, wdRat bNum den)
theorem wdCMem_zero : wdCMem 0 wdCZero := by
  unfold wdCZero
  exact ⟨by simpa using wdMem_zero, by simpa using wdMem_zero⟩
theorem wdCMem_one : wdCMem 1 wdCOne := by
  unfold wdCOne
  exact ⟨by simpa using wdMem_one, by simpa using wdMem_zero⟩
theorem wdCMem_ofReal {r : ℝ} {ir : WDIVal} (hr : wdMem r ir) :
    wdCMem (r : ℂ) (wdCOfReal ir) := by
  unfold wdCOfReal
  exact ⟨by simpa using hr, by simpa using wdMem_zero⟩
theorem wdCMem_add {z w : ℂ} {iz iw : WDCVal} (hz : wdCMem z iz) (hw : wdCMem w iw) :
    wdCMem (z + w) (wdCAdd iz iw) := by
  unfold wdCAdd
  exact ⟨by simpa [Complex.add_re] using wdMem_add hz.1 hw.1,
    by simpa [Complex.add_im] using wdMem_add hz.2 hw.2⟩
theorem wdCMem_sub {z w : ℂ} {iz iw : WDCVal} (hz : wdCMem z iz) (hw : wdCMem w iw) :
    wdCMem (z - w) (wdCSub iz iw) := by
  unfold wdCSub
  exact ⟨by simpa [Complex.sub_re] using wdMem_sub hz.1 hw.1,
    by simpa [Complex.sub_im] using wdMem_sub hz.2 hw.2⟩
theorem wdCMem_mul {z w : ℂ} {iz iw : WDCVal} (hz : wdCMem z iz) (hw : wdCMem w iw) :
    wdCMem (z * w) (wdCMul iz iw) := by
  unfold wdCMul
  simp only [ghMulIV_eq]
  exact ⟨by
      rw [Complex.mul_re]
      exact wdMem_sub (wdMem_mul hz.1 hw.1) (wdMem_mul hz.2 hw.2),
    by
      rw [Complex.mul_im]
      exact wdMem_add (wdMem_mul hz.1 hw.2) (wdMem_mul hz.2 hw.1)⟩
theorem wdCMem_rmul {r : ℝ} {z : ℂ} {rIV : WDIVal} {zIV : WDCVal}
    (hr : wdMem r rIV) (hz : wdCMem z zIV) :
    wdCMem ((r : ℂ) * z) (wdCRMul rIV zIV) := by
  unfold wdCRMul
  simp only [ghMulIV_eq]
  exact ⟨by
      have hre : ((r : ℂ) * z).re = r * z.re := by simp [Complex.mul_re]
      rw [hre]; exact wdMem_mul hr hz.1,
    by
      have him : ((r : ℂ) * z).im = r * z.im := by simp [Complex.mul_im]
      rw [him]; exact wdMem_mul hr hz.2⟩
theorem wdCAbs2Hi_nonneg (zIV : WDCVal) : 0 ≤ wdCAbs2Hi zIV := by
  unfold wdCAbs2Hi
  simp only [ghSqIV_eq]
  unfold wdSq
  dsimp only
  have h1 : 0 ≤ max (zIV.1.1 * zIV.1.1) (zIV.1.2 * zIV.1.2) :=
    le_trans (mul_self_nonneg _) (le_max_left _ _)
  have h2 : 0 ≤ max (zIV.2.1 * zIV.2.1) (zIV.2.2 * zIV.2.2) :=
    le_trans (mul_self_nonneg _) (le_max_left _ _)
  exact add_nonneg (wdDivCeil_nonneg h1 (by unfold wdScale; norm_num))
    (wdDivCeil_nonneg h2 (by unfold wdScale; norm_num))
theorem normSq_le_wdCAbs2Hi {z : ℂ} {zIV : WDCVal} (hz : wdCMem z zIV) :
    Complex.normSq z ≤ (wdCAbs2Hi zIV : ℝ) / wdScaleR := by
  have hre := (wdMem_sq hz.1).2
  have him := (wdMem_sq hz.2).2
  have hnsq : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  rw [hnsq]
  unfold wdCAbs2Hi
  simp only [ghSqIV_eq]
  push_cast
  rw [add_div]
  exact add_le_add hre him
theorem wdCMem_gaussPyth (g : GaussPyth) :
    wdCMem g.val (wdCGaussRat g.aNum g.bNum g.den) := by
  have hval : g.val = (((g.aNum : ℝ) / (g.den : ℝ) : ℝ) : ℂ) +
      Complex.I * (((g.bNum : ℝ) / (g.den : ℝ) : ℝ) : ℂ) := by
    unfold GaussPyth.val; push_cast; ring
  unfold wdCGaussRat
  exact ⟨by rw [hval]; simpa using wdMem_rat g.hDen,
    by rw [hval]; simpa using wdMem_rat g.hDen⟩
/-- GMP WHNF-forced `w = 0.. 4` reifier for `r ≤ 4` complex-interval chains. -/
def wdCReify5 (u : ℕ → WDCVal) : ℕ → WDCVal :=
  ghSeqCIV (u 0) fun u0 ↦
  ghSeqCIV (u 1) fun u1 ↦
  ghSeqCIV (u 2) fun u2 ↦
  ghSeqCIV (u 3) fun u3 ↦
  ghSeqCIV (u 4) fun u4 ↦
    fun w ↦
      match w with
      | 0 => u0 | 1 => u1 | 2 => u2 | 3 => u3 | 4 => u4 | _ => wdCZero
theorem wdCReify5_mem {r : ℕ} (hr : r ≤ 4) {u : ℕ → ℂ} {uIV : ℕ → WDCVal}
    (hz : ∀ w, r < w → u w = 0) (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w, wdCMem (u w) (wdCReify5 uIV w) := by
  have heq : wdCReify5 uIV = fun w ↦
      match w with
      | 0 => uIV 0 | 1 => uIV 1 | 2 => uIV 2 | 3 => uIV 3 | 4 => uIV 4 | _ => wdCZero := by
    unfold wdCReify5
    simp only [ghSeqCIV_eq]
  rw [heq]
  intro w
  match w with
  | 0 | 1 | 2 | 3 | 4 => exact hu _
  | w + 5 =>
    rw [hz (w + 5) (by omega)]
    exact wdCMem_zero
/-- Single non-recursive Pascal layer for `dickeStep (r + 1)` over `WDCVal`. -/
def dickeStepCIVStep (r : ℕ) (c s : WDIVal) (p0 p1 : ℕ → WDCVal) (w' : ℕ) : WDCVal :=
  if w' ≤ r then wdCSub (wdCRMul c (p0 w')) (wdCRMul s (p1 w'))
  else if w' = r + 1 then wdCAdd (wdCRMul s (p0 r)) (wdCRMul c (p1 r))
  else wdCZero
private lemma dickeStepCIVStep_mem (r : ℕ) {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {p0 p1 : ℕ → WDCVal}
    (hp0 : ∀ w', wdCMem (dickeStep r (c : ℂ) (s : ℂ) u w') (p0 w'))
    (hp1 : ∀ w', wdCMem (dickeStep r (c : ℂ) (s : ℂ) (fun w ↦ u (w + 1)) w') (p1 w')) :
    ∀ w', wdCMem (dickeStep (r + 1) (c : ℂ) (s : ℂ) u w')
      (dickeStepCIVStep r cIV sIV p0 p1 w') := by
  intro w'
  simp only [dickeStep, dickeStepCIVStep]
  split_ifs
  · exact wdCMem_sub (wdCMem_rmul hc (hp0 w')) (wdCMem_rmul hs (hp1 w'))
  · exact wdCMem_add (wdCMem_rmul hs (hp0 r)) (wdCMem_rmul hc (hp1 r))
  · exact wdCMem_zero
/-- `r = 0` complex-interval `dickeStep`. -/
def dickeStepCIV0 (u : ℕ → WDCVal) (w' : ℕ) : WDCVal :=
  if w' = 0 then u 0 else wdCZero
/-- `r = 1` complex-interval `dickeStep`. -/
def dickeStepCIV1 (c s : WDIVal) (u : ℕ → WDCVal) : ℕ → WDCVal :=
  dickeStepCIVStep 0 c s (dickeStepCIV0 u) (dickeStepCIV0 (fun w ↦ u (w + 1)))
/-- `r = 2` GMP-memoized complex-interval `dickeStep`. -/
def dickeStepCIV2 (c s : WDIVal) (u : ℕ → WDCVal) : ℕ → WDCVal :=
  let p0 := wdCReify5 (dickeStepCIV1 c s u)
  let p1 := wdCReify5 (dickeStepCIV1 c s (fun w ↦ u (w + 1)))
  dickeStepCIVStep 1 c s p0 p1
/-- `r = 3` GMP-memoized complex-interval `dickeStep`. -/
def dickeStepCIV3 (c s : WDIVal) (u : ℕ → WDCVal) : ℕ → WDCVal :=
  let p0 := wdCReify5 (dickeStepCIV2 c s u)
  let p1 := wdCReify5 (dickeStepCIV2 c s (fun w ↦ u (w + 1)))
  dickeStepCIVStep 2 c s p0 p1
/-- `r = 4` GMP-memoized complex-interval `dickeStep`. -/
def dickeStepCIV4 (c s : WDIVal) (u : ℕ → WDCVal) : ℕ → WDCVal :=
  let p0 := wdCReify5 (dickeStepCIV3 c s u)
  let p1 := wdCReify5 (dickeStepCIV3 c s (fun w ↦ u (w + 1)))
  dickeStepCIVStep 3 c s p0 p1
/-- Non-recursive GMP-memoized complex-interval `dickeStep` for `r ≤ 4` (`0` binary fanout). -/
def dickeStepCIV (r : ℕ) (c s : WDIVal) (u : ℕ → WDCVal) : ℕ → WDCVal :=
  match r with
  | 0 => dickeStepCIV0 u
  | 1 => dickeStepCIV1 c s u
  | 2 => dickeStepCIV2 c s u
  | 3 => dickeStepCIV3 c s u
  | 4 => dickeStepCIV4 c s u
  | _ => fun _ ↦ wdCZero
private lemma dickeStepCIV0_mem {c s : ℝ} {u : ℕ → ℂ} {uIV : ℕ → WDCVal}
    (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w', wdCMem (dickeStep 0 (c : ℂ) (s : ℂ) u w') (dickeStepCIV0 uIV w') := by
  intro w'
  simp only [dickeStep, dickeStepCIV0]
  split_ifs
  · exact hu 0
  · exact wdCMem_zero
private lemma dickeStepCIV1_mem {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {uIV : ℕ → WDCVal} (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w', wdCMem (dickeStep 1 (c : ℂ) (s : ℂ) u w') (dickeStepCIV1 cIV sIV uIV w') :=
  dickeStepCIVStep_mem 0 hc hs (dickeStepCIV0_mem hu) (dickeStepCIV0_mem fun w ↦ hu (w + 1))
private lemma dickeStepCIV2_mem {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {uIV : ℕ → WDCVal} (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w', wdCMem (dickeStep 2 (c : ℂ) (s : ℂ) u w') (dickeStepCIV2 cIV sIV uIV w') :=
  dickeStepCIVStep_mem 1 hc hs
    (wdCReify5_mem (by omega) (fun _ hw ↦ dickeStep_eq_zero_of_gt 1 _ _ _ hw)
      (dickeStepCIV1_mem hc hs hu))
    (wdCReify5_mem (by omega) (fun _ hw ↦ dickeStep_eq_zero_of_gt 1 _ _ _ hw)
      (dickeStepCIV1_mem hc hs fun w ↦ hu (w + 1)))
private lemma dickeStepCIV3_mem {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {uIV : ℕ → WDCVal} (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w', wdCMem (dickeStep 3 (c : ℂ) (s : ℂ) u w') (dickeStepCIV3 cIV sIV uIV w') :=
  dickeStepCIVStep_mem 2 hc hs
    (wdCReify5_mem (by omega) (fun _ hw ↦ dickeStep_eq_zero_of_gt 2 _ _ _ hw)
      (dickeStepCIV2_mem hc hs hu))
    (wdCReify5_mem (by omega) (fun _ hw ↦ dickeStep_eq_zero_of_gt 2 _ _ _ hw)
      (dickeStepCIV2_mem hc hs fun w ↦ hu (w + 1)))
private lemma dickeStepCIV4_mem {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {uIV : ℕ → WDCVal} (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w', wdCMem (dickeStep 4 (c : ℂ) (s : ℂ) u w') (dickeStepCIV4 cIV sIV uIV w') :=
  dickeStepCIVStep_mem 3 hc hs
    (wdCReify5_mem (by omega) (fun _ hw ↦ dickeStep_eq_zero_of_gt 3 _ _ _ hw)
      (dickeStepCIV3_mem hc hs hu))
    (wdCReify5_mem (by omega) (fun _ hw ↦ dickeStep_eq_zero_of_gt 3 _ _ _ hw)
      (dickeStepCIV3_mem hc hs fun w ↦ hu (w + 1)))
theorem dickeStepCIV_mem {r : ℕ} (hr : r ≤ 4) {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {uIV : ℕ → WDCVal} (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w', wdCMem (dickeStep r (c : ℂ) (s : ℂ) u w') (dickeStepCIV r cIV sIV uIV w') := by
  match r, hr with
  | 0, _ => exact dickeStepCIV0_mem hu
  | 1, _ => exact dickeStepCIV1_mem hc hs hu
  | 2, _ => exact dickeStepCIV2_mem hc hs hu
  | 3, _ => exact dickeStepCIV3_mem hc hs hu
  | 4, _ => exact dickeStepCIV4_mem hc hs hu
  | _ + 5, hr => omega
/-- Fast GMP-backed binomial coefficient avoiding unary `Nat.choose` unfolding in `decide`. -/
def ghBinom (r w : ℕ) : ℕ :=
  ghForceNat (r.descFactorial w / w.factorial)
theorem ghBinom_eq (r w : ℕ) : ghBinom r w = r.choose w := by
  unfold ghBinom
  rw [ghForceNat_eq]
  exact (Nat.choose_eq_descFactorial_div_factorial r w).symm
theorem ghListMapRange_getD {α : Type*} (n : ℕ) (f : ℕ → α) (i : ℕ) (d : α) :
    ((List.range n).map f).getD i d = if i < n then f i else d := by
  by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
/-- Combines two level-`t` complex-interval Dicke vectors (`off` and `off + 1`) into `t +
  1`. -/
def dickeCombinePairCIV (t : ℕ) (c s : WDIVal) (left right : List WDCVal) : List WDCVal :=
  (List.range (Nat.add t 2)).map fun w' ↦
    if w' ≤ t then
      wdCSub (wdCRMul c (left.getD w' wdCZero)) (wdCRMul s (right.getD w' wdCZero))
    else
      wdCAdd (wdCRMul s (left.getD t wdCZero)) (wdCRMul c (right.getD t wdCZero))
private lemma dickeCombinePairCIV_mem (t : ℕ) {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {left right : List WDCVal}
    (hL : ∀ w', wdCMem (dickeStep t (c : ℂ) (s : ℂ) u w') (left.getD w' wdCZero))
    (hR : ∀ w', wdCMem (dickeStep t (c : ℂ) (s : ℂ) (fun w ↦ u (w + 1)) w')
      (right.getD w' wdCZero)) :
    ∀ w', wdCMem (dickeStep (t + 1) (c : ℂ) (s : ℂ) u w')
      ((dickeCombinePairCIV t cIV sIV left right).getD w' wdCZero) := by
  intro w'
  unfold dickeCombinePairCIV
  have ht2 : Nat.add t 2 = t + 2 := rfl
  rw [ht2, ghListMapRange_getD]
  simp only [dickeStep]
  by_cases hw_lt : w' < t + 2
  · rw [ite_eq_left hw_lt]
    by_cases hw_le : w' ≤ t
    · rw [ite_eq_left hw_le, ite_eq_left hw_le]
      exact wdCMem_sub (wdCMem_rmul hc (hL w')) (wdCMem_rmul hs (hR w'))
    · have hw_eq : w' = t + 1 := by omega
      rw [ite_eq_right hw_le, ite_eq_right hw_le, ite_eq_left hw_eq]
      exact wdCMem_add (wdCMem_rmul hs (hL t)) (wdCMem_rmul hc (hR t))
  · rw [ite_eq_right hw_lt, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact wdCMem_zero
/-- Advances `rows` from level `t` (`numOut + 1` vectors) to level `t + 1` (`numOut`
  vectors). -/
def dickeAdvanceLayerCIV (t numOut : ℕ) (c s : WDIVal)
    (rows : List (List WDCVal)) : List (List WDCVal) :=
  (List.range numOut).map fun off ↦
    dickeCombinePairCIV t c s (rows.getD off []) (rows.getD (Nat.add off 1) [])
private lemma dickeAdvanceLayerCIV_mem (t numOut : ℕ) {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {rows : List (List WDCVal)}
    (hrows : ∀ off < numOut + 1, ∀ w',
      wdCMem (dickeStep t (c : ℂ) (s : ℂ) (fun w ↦ u (off + w)) w')
        ((rows.getD off []).getD w' wdCZero)) :
    ∀ off < numOut, ∀ w',
      wdCMem (dickeStep (t + 1) (c : ℂ) (s : ℂ) (fun w ↦ u (off + w)) w')
        (((dickeAdvanceLayerCIV t numOut cIV sIV rows).getD off []).getD w' wdCZero) := by
  intro off hoff w'
  unfold dickeAdvanceLayerCIV
  rw [ghListMapRange_getD, ite_eq_left hoff]
  have hoff1 : Nat.add off 1 = off + 1 := rfl
  rw [hoff1]
  refine dickeCombinePairCIV_mem t hc hs (hrows off (by omega)) ?_ w'
  intro w
  have h1 := hrows (off + 1) (by omega) w
  have hfun : (fun x ↦ u ((off + 1) + x)) = (fun x ↦ u (off + (x + 1))) := by
    funext x; congr 1; omega
  rwa [hfun] at h1
/-- Strictly forced `O(r ^ 2)` bottom-up Pascal layer iteration over `WDCVal`
  (`ghSeqCIVRows`). -/
def dickeIterLayersCIV (c s : WDIVal) : ℕ → ℕ → List (List WDCVal) → List (List WDCVal)
  | 0, _, rows => rows
  | rem + 1, t, rows =>
      ghSeqCIVRows (dickeAdvanceLayerCIV t (Nat.add rem 1) c s rows) fun rows' ↦
        dickeIterLayersCIV c s rem (Nat.add t 1) rows'
theorem dickeIterLayersCIV_mem {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV) (u : ℕ → ℂ) :
    ∀ (rem t : ℕ) (rows : List (List WDCVal)),
      (∀ off < rem + 1, ∀ w',
        wdCMem (dickeStep t (c : ℂ) (s : ℂ) (fun w ↦ u (off + w)) w')
          ((rows.getD off []).getD w' wdCZero)) →
      ∀ w', wdCMem (dickeStep (t + rem) (c : ℂ) (s : ℂ) u w')
        (((dickeIterLayersCIV cIV sIV rem t rows).getD 0 []).getD w' wdCZero)
  | 0, _, rows, hrows, w' => by
    have h0 := hrows 0 (by omega) w'
    have hfun : (fun w ↦ u (0 + w)) = u := by funext w; simp
    simpa [dickeIterLayersCIV, hfun] using h0
  | rem + 1, t, rows, hrows, w' => by
    simp only [dickeIterLayersCIV, ghSeqCIVRows_eq]
    have hr1 : Nat.add rem 1 = rem + 1 := rfl
    have ht1 : Nat.add t 1 = t + 1 := rfl
    rw [hr1, ht1]
    have hnext := dickeAdvanceLayerCIV_mem t (rem + 1) hc hs hrows
    have hih := dickeIterLayersCIV_mem hc hs u rem (t + 1) _ hnext w'
    have hadd : (t + 1) + rem = t + (rem + 1) := by omega
    rwa [hadd] at hih
/-- `O(r ^ 2)` WHNF-forced complex-interval evaluation of `dickeStep r c s u` across `0..
  r`. -/
def dickeStepCIVVec (r : ℕ) (c s : WDIVal) (u : ℕ → WDCVal) : List WDCVal :=
  ghSeqCIVRows ((List.range (Nat.add r 1)).map fun off ↦ [u off]) fun initRows ↦
    (dickeIterLayersCIV c s r 0 initRows).getD 0 []
theorem dickeStepCIVVec_mem (r : ℕ) {c s : ℝ} {cIV sIV : WDIVal}
    (hc : wdMem c cIV) (hs : wdMem s sIV)
    {u : ℕ → ℂ} {uIV : ℕ → WDCVal} (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w', wdCMem (dickeStep r (c : ℂ) (s : ℂ) u w')
      ((dickeStepCIVVec r cIV sIV uIV).getD w' wdCZero) := by
  intro w'
  unfold dickeStepCIVVec
  rw [ghSeqCIVRows_eq]
  have hr1 : Nat.add r 1 = r + 1 := rfl
  rw [hr1]
  have hinit : ∀ off < r + 1, ∀ w,
      wdCMem (dickeStep 0 (c : ℂ) (s : ℂ) (fun x ↦ u (off + x)) w)
        ((((List.range (r + 1)).map fun i ↦ [uIV i]).getD off []).getD w wdCZero) := by
    intro off hoff w
    rw [ghListMapRange_getD, ite_eq_left hoff]
    cases w with
    | zero => simpa [dickeStep] using hu off
    | succ w => simpa [dickeStep] using wdCMem_zero
  simpa using dickeIterLayersCIV_mem hc hs u r 0 _ hinit w'
/-- CPS `O(r ^ 2)` WHNF-forced single-pair (`b = 0, 1`, `w₁ ≤ r - 2`) step avoiding `Prod`
  projection re-evaluation across multi-probe folds. -/
def stepHas2CIVVecCPS {α : Type*} (r : ℕ) (c1 s1 c2 s2 : WDIVal) (z0 z1 : ℕ → WDCVal)
    (k : List WDCVal → List WDCVal → α) : α :=
  ghSeqCIVList (dickeStepCIVVec (r - 2) c1 s1 z0) fun m0 ↦
    ghSeqCIVList (dickeStepCIVVec (r - 2) c1 s1 z1) fun m1 ↦
      ghSeqCIVList ((List.range (r - 1)).map fun w1 ↦
        wdCSub (wdCRMul c2 (m0.getD w1 wdCZero)) (wdCRMul s2 (m1.getD w1 wdCZero))) fun n0 ↦
      ghSeqCIVList ((List.range (r - 1)).map fun w1 ↦
        wdCAdd (wdCRMul s2 (m0.getD w1 wdCZero)) (wdCRMul c2 (m1.getD w1 wdCZero))) fun n1 ↦
        k n0 n1
/-- `O(r ^ 2)` WHNF-forced single-pair (`b = 0, 1`, `w₁ ≤ r - 2`) complex-interval step. -/
def stepHas2CIVVec (r : ℕ) (c1 s1 c2 s2 : WDIVal) (z0 z1 : ℕ → WDCVal) :
    List WDCVal × List WDCVal :=
  stepHas2CIVVecCPS r c1 s1 c2 s2 z0 z1 Prod.mk
theorem stepHas2CIVVecCPS_eq {α : Type*} (r : ℕ) (c1 s1 c2 s2 : WDIVal)
    (z0 z1 : ℕ → WDCVal) (k : List WDCVal → List WDCVal → α) :
    stepHas2CIVVecCPS r c1 s1 c2 s2 z0 z1 k =
      k (stepHas2CIVVec r c1 s1 c2 s2 z0 z1).1 (stepHas2CIVVec r c1 s1 c2 s2 z0 z1).2 := by
  unfold stepHas2CIVVec stepHas2CIVVecCPS
  simp only [ghSeqCIVList_eq]
theorem stepHas2CIVVec_mem (r : ℕ) {c1 s1 c2 s2 : ℝ} {c1IV s1IV c2IV s2IV : WDIVal}
    (hc1 : wdMem c1 c1IV) (hs1 : wdMem s1 s1IV)
    (hc2 : wdMem c2 c2IV) (hs2 : wdMem s2 s2IV)
    {z0 z1 : ℕ → ℂ} {z0IV z1IV : ℕ → WDCVal}
    (hz0 : ∀ w1, wdCMem (z0 w1) (z0IV w1)) (hz1 : ∀ w1, wdCMem (z1 w1) (z1IV w1))
    {w1 : ℕ} (hw1 : w1 < r - 1) :
    wdCMem ((c2 : ℂ) * dickeStep (r - 2) (c1 : ℂ) (s1 : ℂ) z0 w1 -
        (s2 : ℂ) * dickeStep (r - 2) (c1 : ℂ) (s1 : ℂ) z1 w1)
      ((stepHas2CIVVec r c1IV s1IV c2IV s2IV z0IV z1IV).1.getD w1 wdCZero) ∧
    wdCMem ((s2 : ℂ) * dickeStep (r - 2) (c1 : ℂ) (s1 : ℂ) z0 w1 +
        (c2 : ℂ) * dickeStep (r - 2) (c1 : ℂ) (s1 : ℂ) z1 w1)
      ((stepHas2CIVVec r c1IV s1IV c2IV s2IV z0IV z1IV).2.getD w1 wdCZero) := by
  unfold stepHas2CIVVec stepHas2CIVVecCPS
  simp only [ghSeqCIVList_eq]
  rw [ghListMapRange_getD, ite_eq_left hw1, ghListMapRange_getD, ite_eq_left hw1]
  have hm0 := dickeStepCIVVec_mem (r - 2) hc1 hs1 hz0 w1
  have hm1 := dickeStepCIVVec_mem (r - 2) hc1 hs1 hz1 w1
  exact ⟨wdCMem_sub (wdCMem_rmul hc2 hm0) (wdCMem_rmul hs2 hm1),
    wdCMem_add (wdCMem_rmul hs2 hm0) (wdCMem_rmul hc2 hm1)⟩
/-! ## Subcube Angle Bounds, Padded Zoom Scaling & Gaussian-Hamming `r = 2` Evaluator -/
private lemma ghZoomScaleR_pos : 0 < wdScaleR := by
  unfold wdScaleR wdScale; norm_num
private lemma ghZoom_four_div_pi_le : (4 : ℝ) / π ≤ (wdPi4InvHi : ℝ) / wdScaleR := by
  have hpi : (3141592653589793 : ℝ) / 1000000000000000 < π := by linarith [Real.pi_gt_d20]
  rw [div_le_iff₀ Real.pi_pos]
  have h1 : (4 : ℝ) ≤ ((wdPi4InvHi : ℝ) / wdScaleR) *
      ((3141592653589793 : ℝ) / 1000000000000000) := by
    unfold wdPi4InvHi wdScaleR wdScale; norm_num
  exact h1.trans
    (mul_le_mul_of_nonneg_left hpi.le (by unfold wdPi4InvHi wdScaleR wdScale; positivity))
private lemma ghZoom_sqrt2_bounds :
    (wdSqrt2Lo : ℝ) / wdScaleR ≤ √2 ∧ √2 ≤ (wdSqrt2Hi : ℝ) / wdScaleR := by
  constructor
  · refine Real.le_sqrt_of_sq_le ?_
    unfold wdSqrt2Lo wdScaleR wdScale; norm_num
  · rw [Real.sqrt_le_iff]
    refine ⟨by unfold wdSqrt2Hi wdScaleR wdScale; positivity, ?_⟩
    unfold wdSqrt2Hi wdScaleR wdScale; norm_num
/-- Certified `10 ^ 15`-scaled upper bound on `1 / √(2 ^ diff)` for padded subcube zoom. -/
def wdZoomScaleHi15 (diff : ℕ) : ℤ :=
  if diff % 2 == 0 then
    ghForceInt (wdDivCeil (wdScale : ℤ) ((2 ^ (diff / 2) : ℕ) : ℤ))
  else
    ghForceInt (wdDivCeil (wdSqrt2Hi + 1) ((2 ^ (Nat.add diff 1 / 2) : ℕ) : ℤ))
theorem wdZoomScaleHi15_nonneg (diff : ℕ) : 0 ≤ wdZoomScaleHi15 diff := by
  unfold wdZoomScaleHi15
  simp only [ghForceInt_eq]
  split_ifs
  · exact wdDivCeil_nonneg (by unfold wdScale; norm_num)
      (by exact_mod_cast Nat.pos_of_ne_zero (by positivity))
  · exact wdDivCeil_nonneg (by unfold wdSqrt2Hi; norm_num)
      (by exact_mod_cast Nat.pos_of_ne_zero (by positivity))
theorem one_div_sqrt_two_pow_le_wdZoomScaleHi15 (diff : ℕ) :
    1 / √((2 : ℝ) ^ diff) ≤ (wdZoomScaleHi15 diff : ℝ) / wdScaleR := by
  have hB := ghZoomScaleR_pos
  unfold wdZoomScaleHi15
  simp only [ghForceInt_eq]
  have hd1 : Nat.add diff 1 = diff + 1 := rfl
  rw [hd1]
  by_cases hpar : diff % 2 = 0
  · have hbeq : (diff % 2 == 0) = true := beq_iff_eq.mpr hpar
    simp only [hbeq, ↓reduceIte]
    set q := diff / 2
    have hdiff : diff = 2 * q := by omega
    have hpow : (2 : ℝ) ^ diff = ((2 : ℝ) ^ q) ^ 2 := by rw [hdiff, mul_comm 2 q, pow_mul]
    have hsqrt : √((2 : ℝ) ^ diff) = (2 : ℝ) ^ q := by
      rw [hpow, Real.sqrt_sq (by positivity)]
    rw [hsqrt]
    have hq_posZ : (0 : ℤ) < ((2 ^ q : ℕ) : ℤ) := by
      exact_mod_cast (pow_pos (by norm_num : 0 < 2) q)
    have hceil := le_wdDivCeil (a := (wdScale : ℤ)) hq_posZ
    have h1 : 1 / (2 : ℝ) ^ q = ((wdScale : ℝ) / (((2 ^ q : ℕ) : ℤ) : ℝ)) / wdScaleR := by
      push_cast
      unfold wdScaleR
      field_simp [hB.ne']
    rw [h1]
    exact div_le_div_of_nonneg_right (by simpa using hceil) hB.le
  · have hbeq : (diff % 2 == 0) = false := beq_eq_false_iff_ne.mpr hpar
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    set q := (diff + 1) / 2
    have hdiff : diff + 1 = 2 * q := by omega
    have hpow : (2 : ℝ) ^ diff * 2 = ((2 : ℝ) ^ q) ^ 2 := by
      rw [← pow_succ, hdiff, mul_comm 2 q, pow_mul]
    have hsqrt_prod : √((2 : ℝ) ^ diff) * √2 = (2 : ℝ) ^ q := by
      rw [← Real.sqrt_mul (by positivity), hpow, Real.sqrt_sq (by positivity)]
    have hsqrt_pos : 0 < √((2 : ℝ) ^ diff) := Real.sqrt_pos.mpr (by positivity)
    have h2q_pos : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
    have hinv_eq : 1 / √((2 : ℝ) ^ diff) = √2 / (2 : ℝ) ^ q := by
      rw [div_eq_div_iff hsqrt_pos.ne' h2q_pos.ne', one_mul]
      linarith [hsqrt_prod]
    rw [hinv_eq]
    have hs2 : √2 ≤ ((wdSqrt2Hi + 1 : ℤ) : ℝ) / wdScaleR := by
      have h := ghZoom_sqrt2_bounds.2
      have hle : (wdSqrt2Hi : ℝ) ≤ ((wdSqrt2Hi + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact h.trans (div_le_div_of_nonneg_right hle hB.le)
    have hq_posZ : (0 : ℤ) < ((2 ^ q : ℕ) : ℤ) := by
      exact_mod_cast (pow_pos (by norm_num : 0 < 2) q)
    have hceil := le_wdDivCeil (a := wdSqrt2Hi + 1) hq_posZ
    have hdiv1 : √2 / (2 : ℝ) ^ q ≤
        (((wdSqrt2Hi + 1 : ℤ) : ℝ) / (((2 ^ q : ℕ) : ℤ) : ℝ)) / wdScaleR := by
      have hm := div_le_div_of_nonneg_right hs2 h2q_pos.le
      push_cast at hm ⊢
      rwa [div_right_comm] at hm
    exact hdiv1.trans (div_le_div_of_nonneg_right hceil hB.le)
theorem scale15_subNZoom_le {subN diff : ℕ} (hle : diff ≤ subN) :
    (((π / 4) * √(2 ^ (subN - diff) : ℝ)) / wdScaleR) ≤
      ((wdZoomScaleHi15 diff : ℝ) / wdScaleR) * (((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR) := by
  have hB := ghZoomScaleR_pos
  have hsplit : (2 : ℝ) ^ subN = (2 : ℝ) ^ (subN - diff) * (2 : ℝ) ^ diff := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hsqrt_split : √(2 ^ subN : ℝ) = √(2 ^ (subN - diff) : ℝ) * √((2 : ℝ) ^ diff) := by
    rw [hsplit, Real.sqrt_mul (by positivity)]
  have hsqrt_diff_pos : 0 < √((2 : ℝ) ^ diff) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_z : √(2 ^ (subN - diff) : ℝ) = (1 / √((2 : ℝ) ^ diff)) * √(2 ^ subN : ℝ) := by
    rw [hsqrt_split]
    field_simp [hsqrt_diff_pos.ne']
  have hscale := one_div_sqrt_two_pow_le_wdZoomScaleHi15 diff
  have hfac_nn : 0 ≤ ((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR :=
    div_nonneg (by positivity [Real.pi_pos]) hB.le
  calc (((π / 4) * √(2 ^ (subN - diff) : ℝ)) / wdScaleR)
      = (1 / √((2 : ℝ) ^ diff)) * (((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR) := by
          rw [hsqrt_z]; ring
    _ ≤ ((wdZoomScaleHi15 diff : ℝ) / wdScaleR) * (((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR) :=
          mul_le_mul_of_nonneg_right hscale hfac_nn
private lemma ghZoom_arcsin_le_add_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.arcsin x ≤ x + x ^ 2 := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have h3 : x * (1 + x) ^ 3 ≤ 2 := by
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x) (by linarith : 1 + x ≤ 3 / 2) 3]
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
    ⟨by nlinarith [Real.pi_gt_three], by nlinarith [Real.pi_gt_three]⟩]
  nlinarith [Real.sin_gt_sub_cube (by positivity : 0 < x + x ^ 2),
    mul_le_mul_of_nonneg_left h3 (sq_nonneg x)]
theorem ghZoom_subN_angle_bounds {subN : ℕ} (hsub : 200 ≤ subN) :
    let D : ℝ := (2 ^ subN : ℝ)
    let θ₁ : ℝ := Real.arcsin (1 / √D)
    let θ₂ : ℝ := Real.arcsin (√2 / √D)
    (0 < θ₁ ∧ 1 / √D ≤ θ₁ ∧ θ₁ ≤ 1 / wdScaleR) ∧
      (1 : ℝ) ≤ (1 / wdScaleR) * √D ∧
      wdMem (θ₂ / θ₁) (wdSqrt2Lo - 1, wdSqrt2Hi + 1) := by
  intro D θ₁ θ₂
  have hD_ge : (2 ^ 200 : ℝ) ≤ D := pow_le_pow_right₀ (by norm_num) hsub
  have hD_pos : 0 < D := lt_of_lt_of_le (by norm_num) hD_ge
  have hsqrtD_ge : (2 ^ 100 : ℝ) ≤ √D :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 ^ 100 : ℝ) ^ 2) ≤ 2 ^ 200).trans hD_ge)
  have hsqrtD_pos : 0 < √D := lt_of_lt_of_le (by norm_num) hsqrtD_ge
  set x₁ : ℝ := 1 / √D
  have hx₁_pos : 0 < x₁ := div_pos one_pos hsqrtD_pos
  have hx₁_le : x₁ ≤ 1 / 2 ^ 100 :=
    one_div_le_one_div_of_le (by norm_num) hsqrtD_ge
  have hx₁_θ₁ : x₁ ≤ θ₁ := self_le_arcsin hx₁_pos.le (hx₁_le.trans (by norm_num))
  have hθ₁_pos : 0 < θ₁ := hx₁_pos.trans_le hx₁_θ₁
  have hθ₁_hi100 : θ₁ ≤ (1 + 1 / 2 ^ 100) * x₁ := by
    have h := ghZoom_arcsin_le_add_sq hx₁_pos.le (hx₁_le.trans (by norm_num))
    have hsq : x₁ ^ 2 ≤ (1 / 2 ^ 100) * x₁ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hx₁_le hx₁_pos.le
    linarith
  have hθ₁_le_scale : θ₁ ≤ 1 / wdScaleR := by
    have h1 : θ₁ ≤ (1 + 1 / 2 ^ 100) * (1 / 2 ^ 100) :=
      hθ₁_hi100.trans (mul_le_mul_of_nonneg_left hx₁_le (by norm_num))
    refine h1.trans ?_
    unfold wdScaleR wdScale; norm_num
  have hone_le : (1 : ℝ) ≤ (1 / wdScaleR) * √D := by
    have hB : wdScaleR ≤ 2 ^ 100 := by unfold wdScaleR wdScale; norm_num
    have hB_pos := ghZoomScaleR_pos
    rw [one_div, inv_mul_eq_div, one_le_div hB_pos]
    exact hB.trans hsqrtD_ge
  set x₂ : ℝ := √2 / √D
  have hx₂_eq : x₂ = √2 * x₁ := by
    dsimp only [x₂, x₁]; rw [div_eq_mul_one_div]
  obtain ⟨hs2_lo, hs2_hi⟩ := ghZoom_sqrt2_bounds
  have hx₂_nn : 0 ≤ x₂ := div_nonneg (Real.sqrt_nonneg _) hsqrtD_pos.le
  have hx₂_le : x₂ ≤ 2 / 2 ^ 100 := by
    rw [hx₂_eq]
    have hs2_2 : √2 ≤ 2 := hs2_hi.trans (by unfold wdSqrt2Hi wdScaleR wdScale; norm_num)
    exact (mul_le_mul hs2_2 hx₁_le hx₁_pos.le (by norm_num)).trans (by norm_num)
  have hx₂_θ₂ : x₂ ≤ θ₂ := self_le_arcsin hx₂_nn (hx₂_le.trans (by norm_num))
  have hθ₂_hi100 : θ₂ ≤ (1 + 2 / 2 ^ 100) * x₂ := by
    have h := ghZoom_arcsin_le_add_sq hx₂_nn (hx₂_le.trans (by norm_num))
    have hsq : x₂ ^ 2 ≤ (2 / 2 ^ 100) * x₂ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hx₂_le hx₂_nn
    linarith
  refine ⟨⟨hθ₁_pos, hx₁_θ₁, hθ₁_le_scale⟩, hone_le, ?_, ?_⟩
  · rw [le_div_iff₀ hθ₁_pos]
    have hcoef : (((wdSqrt2Lo - 1 : ℤ) : ℝ) / wdScaleR) * (1 + 1 / 2 ^ 100) ≤
        (wdSqrt2Lo : ℝ) / wdScaleR := by
      unfold wdSqrt2Lo wdScaleR wdScale; push_cast; norm_num
    calc (((wdSqrt2Lo - 1 : ℤ) : ℝ) / wdScaleR) * θ₁
        ≤ (((wdSqrt2Lo - 1 : ℤ) : ℝ) / wdScaleR) * ((1 + 1 / 2 ^ 100) * x₁) :=
          mul_le_mul_of_nonneg_left hθ₁_hi100 (by unfold wdSqrt2Lo wdScaleR wdScale; positivity)
      _ = ((((wdSqrt2Lo - 1 : ℤ) : ℝ) / wdScaleR) * (1 + 1 / 2 ^ 100)) * x₁ := by ring
      _ ≤ ((wdSqrt2Lo : ℝ) / wdScaleR) * x₁ := mul_le_mul_of_nonneg_right hcoef hx₁_pos.le
      _ ≤ √2 * x₁ := mul_le_mul_of_nonneg_right hs2_lo hx₁_pos.le
      _ = x₂ := hx₂_eq.symm
      _ ≤ θ₂ := hx₂_θ₂
  · rw [div_le_iff₀ hθ₁_pos]
    have hcoef : (1 + 2 / 2 ^ 100) * ((wdSqrt2Hi : ℝ) / wdScaleR) ≤
        ((wdSqrt2Hi + 1 : ℤ) : ℝ) / wdScaleR := by
      unfold wdSqrt2Hi wdScaleR wdScale; push_cast; norm_num
    calc θ₂
        ≤ (1 + 2 / 2 ^ 100) * (√2 * x₁) := by rw [← hx₂_eq]; exact hθ₂_hi100
      _ ≤ (1 + 2 / 2 ^ 100) * (((wdSqrt2Hi : ℝ) / wdScaleR) * θ₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hs2_hi hx₁_θ₁ hx₁_pos.le
            (by unfold wdSqrt2Hi wdScaleR wdScale; positivity)) (by norm_num)
      _ = ((1 + 2 / 2 ^ 100) * ((wdSqrt2Hi : ℝ) / wdScaleR)) * θ₁ := by ring
      _ ≤ (((wdSqrt2Hi + 1 : ℤ) : ℝ) / wdScaleR) * θ₁ :=
          mul_le_mul_of_nonneg_right hcoef hθ₁_pos.le
theorem ghZoomStepCount_bounds {aNum aDen subN : ℕ} (hden : 0 < aDen) (hsub : 200 ≤ subN)
    (c : ℕ) :
    let D : ℝ := (2 ^ subN : ℝ)
    let θ₁ : ℝ := Real.arcsin (1 / √D)
    let scale15 : ℝ := ((π / 4) * √D) / wdScaleR
    let aIV : WDIVal := wdRat (aNum : ℤ) aDen
    let K : ℕ := wdStepCount aNum aDen subN
    let qHi : ℤ := wdDivCeil ((aIV.2 + 2 * (c : ℤ)) * wdPi4InvHi) (2 * (wdScale : ℤ))
    wdMem ((2 * (K : ℝ) + 1) * θ₁) (max 0 (aIV.1 - 1), aIV.2 + 1) ∧
      wdMem (2 * (K : ℝ) * θ₁) (max 0 (aIV.1 - 2), aIV.2) ∧
      0 ≤ qHi ∧
      ((K + c : ℕ) : ℝ) ≤ (qHi : ℝ) * scale15 := by
  intro D θ₁ scale15 aIV K qHi
  have hB := ghZoomScaleR_pos
  have h2BZ : (0 : ℤ) < 2 * (wdScale : ℤ) := by unfold wdScale; norm_num
  obtain ⟨⟨hθ₁_pos, hx₁_θ₁, hθ₁_scale⟩, hone_le, _⟩ := ghZoom_subN_angle_bounds hsub
  set a : ℝ := (aNum : ℝ) / (aDen : ℝ)
  have ha_nn : 0 ≤ a := by positivity
  have ha_mem : wdMem a aIV := by
    simpa [a, aIV] using wdMem_rat (num := (aNum : ℤ)) hden
  have h2θ_pos : 0 < 2 * θ₁ := by linarith
  have hK_le : (K : ℝ) ≤ a / (2 * θ₁) := Nat.floor_le (div_nonneg ha_nn h2θ_pos.le)
  have hK_gt : a / (2 * θ₁) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2K_hi : 2 * (K : ℝ) * θ₁ ≤ a := by
    have h := (le_div_iff₀ h2θ_pos).mp hK_le; linarith
  have h2K_lo : a - 2 * θ₁ ≤ 2 * (K : ℝ) * θ₁ := by
    have h := (div_lt_iff₀ h2θ_pos).mp hK_gt; linarith
  have hθ₁_sc : θ₁ ≤ 1 / wdScaleR := hθ₁_scale
  have h2θ₁_sc : 2 * θ₁ ≤ 2 / wdScaleR := by
    have h2 : (2 : ℝ) / wdScaleR = 2 * (1 / wdScaleR) := by ring
    linarith
  have hm1 : wdMem ((2 * (K : ℝ) + 1) * θ₁) (max 0 (aIV.1 - 1), aIV.2 + 1) := by
    unfold wdMem
    constructor
    · push_cast
      rw [div_le_iff₀ hB]
      refine max_le (by positivity) ?_
      rw [← div_le_iff₀ hB, sub_div]
      linarith [ha_mem.1, h2K_lo, hθ₁_sc]
    · push_cast; rw [add_div]; linarith [ha_mem.2, h2K_hi, hθ₁_sc]
  have hm2 : wdMem (2 * (K : ℝ) * θ₁) (max 0 (aIV.1 - 2), aIV.2) := by
    unfold wdMem
    constructor
    · push_cast
      rw [div_le_iff₀ hB]
      refine max_le (by positivity) ?_
      rw [← div_le_iff₀ hB, sub_div]
      linarith [ha_mem.1, h2K_lo, h2θ₁_sc]
    · linarith [ha_mem.2, h2K_hi]
  have haIV2_nn : 0 ≤ aIV.2 := by
    dsimp only [aIV, wdRat]
    exact wdDivCeil_nonneg (mul_nonneg (Nat.cast_nonneg _) (by unfold wdScale; norm_num))
      (by exact_mod_cast hden)
  have hqHi_nn : 0 ≤ qHi := by
    dsimp only [qHi]
    refine wdDivCeil_nonneg ?_ h2BZ
    exact mul_nonneg (by linarith) (by unfold wdPi4InvHi; norm_num)
  have hsqrtD_nn : 0 ≤ √D := Real.sqrt_nonneg _
  have hK_sqrt : (K : ℝ) ≤ (a / 2) * √D := by
    have hinv : 1 / (2 * θ₁) ≤ √D / 2 := by
      have hsqrt_pos : 0 < √D := lt_of_lt_of_le (by norm_num)
        (Real.le_sqrt_of_sq_le ((by norm_num : ((2 ^ 100 : ℝ) ^ 2) ≤ 2 ^ 200).trans
          (pow_le_pow_right₀ (by norm_num) hsub)))
      rw [div_le_div_iff₀ h2θ_pos (by norm_num)]
      have h1 := mul_le_mul_of_nonneg_right hx₁_θ₁ hsqrt_pos.le
      rw [one_div_mul_cancel hsqrt_pos.ne'] at h1
      linarith
    calc (K : ℝ) ≤ a * (1 / (2 * θ₁)) := by rw [← div_eq_mul_one_div]; exact hK_le
      _ ≤ a * (√D / 2) := mul_le_mul_of_nonneg_left hinv ha_nn
      _ = (a / 2) * √D := by ring
  have hc_sqrt : (c : ℝ) ≤ ((c : ℝ) / wdScaleR) * √D := by
    have h := mul_le_mul_of_nonneg_left hone_le (Nat.cast_nonneg c)
    linarith [show (c : ℝ) * ((1 / wdScaleR) * √D) = ((c : ℝ) / wdScaleR) * √D by ring]
  have hKc_sqrt : ((K + c : ℕ) : ℝ) ≤ (((aIV.2 + 2 * (c : ℤ) : ℤ) : ℝ) / (2 * wdScaleR)) * √D := by
    push_cast
    have hcoef : a / 2 + (c : ℝ) / wdScaleR ≤ ((aIV.2 : ℝ) + 2 * (c : ℝ)) / (2 * wdScaleR) := by
      have h2B : 0 < 2 * wdScaleR := by linarith
      rw [le_div_iff₀ h2B]
      have ha2 : a * wdScaleR ≤ (aIV.2 : ℝ) := (le_div_iff₀ hB).mp ha_mem.2
      have hcancel : (a / 2 + (c : ℝ) / wdScaleR) * (2 * wdScaleR) =
          a * wdScaleR + 2 * (c : ℝ) := by
        field_simp [hB.ne']
      linarith
    calc (K : ℝ) + (c : ℝ)
        ≤ (a / 2 + (c : ℝ) / wdScaleR) * √D := by linarith
      _ ≤ (((aIV.2 : ℝ) + 2 * (c : ℝ)) / (2 * wdScaleR)) * √D :=
          mul_le_mul_of_nonneg_right hcoef hsqrtD_nn
  have hpi_conv : √D ≤ ((wdPi4InvHi : ℝ) / wdScaleR) * ((π / 4) * √D) := by
    have h4pi := ghZoom_four_div_pi_le
    have h1 : (1 : ℝ) ≤ ((wdPi4InvHi : ℝ) / wdScaleR) * (π / 4) := by
      have hp := Real.pi_pos
      have hm := mul_le_mul_of_nonneg_right h4pi (by positivity : 0 ≤ π / 4)
      have heq : (4 / π) * (π / 4) = 1 := by field_simp [hp.ne']
      linarith
    have hm_d := mul_le_mul_of_nonneg_right h1 hsqrtD_nn
    linarith
  have hqHi_bound : ((K + c : ℕ) : ℝ) ≤ (qHi : ℝ) * scale15 := by
    have hcoef_nn : 0 ≤ ((aIV.2 + 2 * (c : ℤ) : ℤ) : ℝ) / (2 * wdScaleR) := by
      refine div_nonneg ?_ (by linarith)
      exact_mod_cast (show 0 ≤ aIV.2 + 2 * (c : ℤ) by positivity)
    have hceil := le_wdDivCeil (a := (aIV.2 + 2 * (c : ℤ)) * wdPi4InvHi) h2BZ
    calc ((K + c : ℕ) : ℝ)
        ≤ (((aIV.2 + 2 * (c : ℤ) : ℤ) : ℝ) / (2 * wdScaleR)) *
            (((wdPi4InvHi : ℝ) / wdScaleR) * ((π / 4) * √D)) :=
          hKc_sqrt.trans (mul_le_mul_of_nonneg_left hpi_conv hcoef_nn)
      _ = ((((aIV.2 + 2 * (c : ℤ)) * wdPi4InvHi : ℤ) : ℝ) / (2 * wdScaleR)) * scale15 := by
          dsimp only [scale15]; push_cast; ring
      _ ≤ (qHi : ℝ) * scale15 := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (by positivity [Real.pi_pos]) hB.le)
          simpa [qHi, wdScaleR] using hceil
  exact ⟨hm1, hm2, hqHi_nn, hqHi_bound⟩
/-- Single `r = 2` Gaussian-Hamming probe specification `(da, rot2, g1, g2)`. -/
structure GHProbeSpec where
  daNum : ℕ
  daDen : ℕ
  cNum : ℤ
  sNum : ℕ
  cDen : ℕ
  ga1 : ℤ
  gb1 : ℤ
  gd1 : ℕ
  ga2 : ℤ
  gb2 : ℤ
  gd2 : ℕ
  deriving DecidableEq, Repr
/-- Row specification `(a0, bZoom, probes)` for `r = 2` Gaussian-Hamming Zoom. -/
structure GHZoomRowSpec where
  a0Num : ℕ
  a0Den : ℕ
  bNum : ℕ
  bDen : ℕ
  probes : List GHProbeSpec
  deriving DecidableEq, Repr
/-- Per-pass table mapping `r` to `Option GHZoomRowSpec`. -/
abbrev GHZoomPassSpec := List (Option GHZoomRowSpec)
/-- Validity predicate for one `GHProbeSpec`. -/
abbrev ghProbeValid (p : GHProbeSpec) : Prop :=
  0 < p.daDen ∧ 0 < p.cDen ∧ p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 = (p.cDen : ℤ) ^ 2 ∧
    0 < p.gd1 ∧ p.ga1 ^ 2 + p.gb1 ^ 2 = (p.gd1 : ℤ) ^ 2 ∧
    0 < p.gd2 ∧ p.ga2 ^ 2 + p.gb2 ^ 2 = (p.gd2 : ℤ) ^ 2
/-- Compiles one `GHProbeSpec` at subcube dimension `subN`. -/
noncomputable def compileGHProbe (p : GHProbeSpec) (subN : ℕ) : Option GHZoomProbe :=
  if h : ghProbeValid p then
    some ({ aNum := p.ga1, bNum := p.gb1, den := p.gd1, hDen := h.2.2.2.1, hPyth := h.2.2.2.2.1 },
      { aNum := p.ga2, bNum := p.gb2, den := p.gd2, hDen := h.2.2.2.2.2.1, hPyth := h.2.2.2.2.2.2 },
      { cNum := p.cNum, sNum := p.sNum, cDen := p.cDen, hDen := h.2.1, hPyth := h.2.2.1 },
      wdStepCount p.daNum p.daDen subN)
  else
    none
/-- Compiles a `List GHProbeSpec` into `Option (List GHZoomProbe)` at `subN`. -/
noncomputable def compileGHProbes : List GHProbeSpec → ℕ → Option (List GHZoomProbe)
  | [], _ => some []
  | p :: rest, subN =>
      match compileGHProbe p subN, compileGHProbes rest subN with
      | some pk, some tail => some (pk :: tail)
      | _, _ => none
/-- Compiles a `GHZoomRowSpec` at `(p, subN)` into `GHZoomSpec`. -/
noncomputable def compileGHZoomRow (p : ℕ) (spec : GHZoomRowSpec) (subN : ℕ) : GHZoomSpec :=
  if 0 < spec.a0Den ∧ 0 < spec.bDen then
    match compileGHProbes spec.probes subN with
    | none => none
    | some probes =>
        some (wdStepCount spec.a0Num spec.a0Den subN, probes,
          wdStepCount spec.bNum spec.bDen (subN - p))
  else
    none
/-- Compiles a `GHZoomPassSpec` at `p = Stage2CertInternals.gridExp m` into `GHZoomPassFn`. -/
noncomputable def compileGHZoomPassSpec (p : ℕ) (ps : GHZoomPassSpec) : GHZoomPassFn :=
  fun subN r ↦
    match ps.getD r none with
    | none => none
    | some spec => compileGHZoomRow p spec subN
/-- Complex-interval damping step mirroring `ghDampAmp2`. -/
def ghDampIV2 (g1IV g2IV : WDCVal) (cPyth : WDIVal) (uIV : ℕ → WDCVal) : ℕ → WDCVal
  | 0 => uIV 0
  | 1 => wdCMul g1IV (uIV 1)
  | 2 => wdCRMul cPyth (wdCMul g2IV (uIV 2))
  | _ => wdCZero
private lemma ghDampIV2_mem {g1 g2 : GaussPyth} {rot2 : PythPair}
    {g1IV g2IV : WDCVal} {cPyth : WDIVal}
    (hg1 : wdCMem g1.val g1IV) (hg2 : wdCMem g2.val g2IV) (hc : wdMem rot2.cVal cPyth)
    {u : ℕ → ℂ} {uIV : ℕ → WDCVal} (hu : ∀ w, wdCMem (u w) (uIV w)) :
    ∀ w, wdCMem (ghDampAmp2 g1 g2 rot2 u w) (ghDampIV2 g1IV g2IV cPyth uIV w) := by
  intro w
  match w with
  | 0 => exact hu 0
  | 1 => exact wdCMem_mul hg1 (hu 1)
  | 2 =>
    dsimp only [ghDampAmp2, ghDampIV2]
    rw [mul_assoc]
    exact wdCMem_rmul hc (wdCMem_mul hg2 (hu 2))
  | _ + 3 => exact wdCMem_zero
/-- Strict GMP-normalizing packer forcing all probe accumulators before `Option.some`. -/
def ghPackStep (stepQ qdaHi : ℤ) (z0Raw z1Raw : WDCVal) (uNextRaw : ℕ → WDCVal) :
    Option (ℤ × ℤ × WDCVal × WDCVal × (ℕ → WDCVal)) :=
  ghSeqIV (stepQ, qdaHi) fun sqPair ↦
  ghSeqCIV (uNextRaw 0) fun u0 ↦
  ghSeqCIV (uNextRaw 1) fun u1 ↦
  ghSeqCIV (uNextRaw 2) fun u2 ↦
  ghSeqCIV z0Raw fun z0 ↦
  ghSeqCIV z1Raw fun z1 ↦
    some (sqPair.1, sqPair.2, z0, z1,
      fun w ↦
        match w with
        | 0 => u0 | 1 => u1 | 2 => u2 | _ => wdCZero)
private lemma ghPackStep_eq (stepQ qdaHi : ℤ) (z0Raw z1Raw : WDCVal) (uNextRaw : ℕ → WDCVal) :
    ghPackStep stepQ qdaHi z0Raw z1Raw uNextRaw =
      some (stepQ, qdaHi, z0Raw, z1Raw,
        fun w ↦
          match w with
          | 0 => uNextRaw 0 | 1 => uNextRaw 1 | 2 => uNextRaw 2 | _ => wdCZero) := by
  unfold ghPackStep
  simp only [ghSeqIV_eq, ghSeqCIV_eq]
/-- Single-probe complex-interval step over both `InjOn` (`uIV`) and `¬ InjOn` (`z0IV,
  z1IV`). -/
def evalGHProbeStep (p : GHProbeSpec) (uIV : ℕ → WDCVal) (z0IV z1IV : WDCVal) :
    Option (ℤ × ℤ × WDCVal × WDCVal × (ℕ → WDCVal)) :=
  if ghProbeValid p then
    let daIV := wdRat (p.daNum : ℤ) p.daDen
    let dphi1IV : WDIVal := (ghMaxZ 0 (daIV.1 - 2), daIV.2)
    let dphi2IV : WDIVal := ghMulIV dphi1IV (wdSqrt2Lo - 1, wdSqrt2Hi + 1)
    if 0 ≤ dphi1IV.1 ∧ dphi1IV.2 ≤ 1024 * (wdScale : ℤ) ∧
        0 ≤ dphi2IV.1 ∧ dphi2IV.2 ≤ 1024 * (wdScale : ℤ) then
      let g1IV := wdCGaussRat p.ga1 p.gb1 p.gd1
      let g2IV := wdCGaussRat p.ga2 p.gb2 p.gd2
      let cPyth := wdRat p.cNum p.cDen
      let uD := ghDampIV2 g1IV g2IV cPyth uIV
      let z1D := wdCMul g1IV z1IV
      let sHi := wdCAbs2Hi (uD 0) + 2 * wdCAbs2Hi (uD 1) + wdCAbs2Hi (uD 2)
      let qdaHi := wdDivCeil ((daIV.2 + 4) * wdPi4InvHi) (2 * (wdScale : ℤ))
      let stepQ := wdDivCeil (sHi * qdaHi) (wdScale : ℤ)
      ghTrigCPS dphi1IV fun c1 s1 ↦
      ghTrigCPS dphi2IV fun c2 s2 ↦
        let uNextRaw := dickeStepCIV 2 c1 s1 uD
        let z0Raw := wdCSub (wdCRMul c2 z0IV) (wdCRMul s2 z1D)
        let z1Raw := wdCAdd (wdCRMul s2 z0IV) (wdCRMul c2 z1D)
        ghPackStep stepQ qdaHi z0Raw z1Raw uNextRaw
    else
      none
  else
    none
/-- Multi-probe complex-interval chain evaluator for `r = 2` Gaussian-Hamming Zoom. -/
def evalGHProbes :
    List GHProbeSpec → (ℕ → WDCVal) → WDCVal → WDCVal →
      Option (ℤ × ℤ × WDCVal × WDCVal × (ℕ → WDCVal))
  | [], uIV, z0IV, z1IV => some (0, 0, z0IV, z1IV, uIV)
  | p :: rest, uIV, z0IV, z1IV =>
      match evalGHProbeStep p uIV z0IV z1IV with
      | none => none
      | some (stepQ, qdaHi, z0Next, z1Next, uNext) =>
          match evalGHProbes rest uNext z0Next z1Next with
          | none => none
          | some (qExRest, qCollRest, z0Fin, z1Fin, uFin) =>
              ghSeqIV (stepQ + qExRest, qdaHi + qCollRest) fun qPair ↦
                some (qPair.1, qPair.2, z0Fin, z1Fin, uFin)
private lemma ghZoomProbeStep_qColl {subN : ℕ} (hsub : 200 ≤ subN)
    {p : GHProbeSpec} {uIV : ℕ → WDCVal} {z0IV z1IV : WDCVal}
    {stepQ qdaHi : ℤ} {z0N z1N : WDCVal} {uNext : ℕ → WDCVal} {pk : GHZoomProbe}
    (heval : evalGHProbeStep p uIV z0IV z1IV = some (stepQ, qdaHi, z0N, z1N, uNext))
    (hcomp : compileGHProbe p subN = some pk) :
    ((pk.2.2.2 + 2 : ℕ) : ℝ) ≤ (qdaHi : ℝ) * (((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR) := by
  unfold evalGHProbeStep at heval
  simp only [ghMaxZ_eq, ghMulIV_eq, ghTrigCPS_eq] at heval
  unfold compileGHProbe at hcomp
  split_ifs at heval with hvalid _
  rw [ghPackStep_eq] at heval
  rw [dite_eq_left hvalid] at hcomp
  injection hcomp with hpk
  subst hpk
  injection heval with htuple
  rcases Prod.mk.inj htuple with ⟨_, hrest1⟩
  rcases Prod.mk.inj hrest1 with ⟨hqda, _⟩
  subst hqda
  exact (ghZoomStepCount_bounds (aNum := p.daNum) hvalid.1 hsub 2).2.2.2
private lemma ghZoomProbes_qColl {subN : ℕ} (hsub : 200 ≤ subN) :
    ∀ (ps : List GHProbeSpec) (uIV : ℕ → WDCVal) (z0IV z1IV : WDCVal)
      {qEx qCollAdd : ℤ} {z0Fin z1Fin : WDCVal} {uFinal : ℕ → WDCVal}
      {probes : List GHZoomProbe},
      evalGHProbes ps uIV z0IV z1IV = some (qEx, qCollAdd, z0Fin, z1Fin, uFinal) →
      compileGHProbes ps subN = some probes →
      (((probes.map fun pk ↦ pk.2.2.2 + 2).sum : ℕ) : ℝ) ≤
        (qCollAdd : ℝ) * (((π / 4) * √(2 ^ subN : ℝ)) / wdScaleR)
  | [], _, _, _, _, _, _, _, _, _, heval, hcomp => by
    simp only [evalGHProbes, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨_, rfl, _, _, _⟩
    simp only [compileGHProbes, Option.some.injEq] at hcomp
    subst hcomp
    simp
  | p :: rest, uIV, z0IV, z1IV, _, _, _, _, _, _, heval, hcomp => by
    simp only [evalGHProbes] at heval
    simp only [compileGHProbes] at hcomp
    cases hstep : evalGHProbeStep p uIV z0IV z1IV with
    | none => rw [hstep] at heval; cases heval
    | some sRes =>
      rcases sRes with ⟨stepQ, qdaHi, z0N, z1N, uNext⟩
      rw [hstep] at heval
      dsimp only at heval
      cases hrest : evalGHProbes rest uNext z0N z1N with
      | none => rw [hrest] at heval; cases heval
      | some rRes =>
        rcases rRes with ⟨qExR, qCollR, z0F, z1F, uFin⟩
        rw [hrest] at heval
        simp only [ghSeqIV_eq, Option.some.injEq, Prod.mk.injEq] at heval
        rcases heval with ⟨_, rfl, _, _, _⟩
        cases hc1 : compileGHProbe p subN with
        | none => rw [hc1] at hcomp; cases hcomp
        | some pk =>
          rw [hc1] at hcomp
          cases hc2 : compileGHProbes rest subN with
          | none => rw [hc2] at hcomp; cases hcomp
          | some tail =>
            rw [hc2] at hcomp
            simp only [Option.some.injEq] at hcomp
            subst hcomp
            have h1 := ghZoomProbeStep_qColl hsub hstep hc1
            have h2 := ghZoomProbes_qColl hsub rest uNext z0N z1N hrest hc2
            simp only [List.map_cons, List.sum_cons]
            push_cast at h1 h2 ⊢
            linarith
private lemma ghZoomProbeStep_sound {subN : ℕ} (hsub : 200 ≤ subN)
    {p : GHProbeSpec} {u : ℕ → ℂ} {uIV : ℕ → WDCVal} {z : ℂ × ℂ} {z0IV z1IV : WDCVal}
    {stepQ qdaHi : ℤ} {z0N z1N : WDCVal} {uNext : ℕ → WDCVal}
    (heval : evalGHProbeStep p uIV z0IV z1IV = some (stepQ, qdaHi, z0N, z1N, uNext))
    (hu : ∀ w, wdCMem (u w) (uIV w)) (hz0 : wdCMem z.1 z0IV) (hz1 : wdCMem z.2 z1IV) :
    let D : ℝ := (2 ^ subN : ℝ)
    let θ₁ : ℝ := Real.arcsin (1 / √D)
    let θ₂ : ℝ := Real.arcsin (√2 / √D)
    let scale15 : ℝ := ((π / 4) * √D) / wdScaleR
    ∃ pk : GHZoomProbe,
      compileGHProbe p subN = some pk ∧
      ((pk.2.2.2 + 2 : ℕ) : ℝ) ≤ (qdaHi : ℝ) * scale15 ∧
      (Complex.normSq (ghDampAmp2 pk.1 pk.2.1 pk.2.2.1 u 0) +
          2 * Complex.normSq (ghDampAmp2 pk.1 pk.2.1 pk.2.2.1 u 1) +
          Complex.normSq (ghDampAmp2 pk.1 pk.2.1 pk.2.2.1 u 2)) *
        ((pk.2.2.2 + 2 : ℕ) : ℝ) ≤ (stepQ : ℝ) * scale15 ∧
      (∀ w, wdCMem (ghProbeNextAmp2 θ₁ pk u w) (uNext w)) ∧
      wdCMem (ghProbeNextColl2 θ₂ pk z).1 z0N ∧
      wdCMem (ghProbeNextColl2 θ₂ pk z).2 z1N := by
  intro D θ₁ θ₂ scale15
  have hB := ghZoomScaleR_pos
  have hBZ : (0 : ℤ) < (wdScale : ℤ) := by unfold wdScale; norm_num
  have hs15 : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
  unfold evalGHProbeStep at heval
  simp only [ghMaxZ_eq, ghMulIV_eq, ghTrigCPS_eq] at heval
  split_ifs at heval with hvalid hdphi
  rw [ghPackStep_eq] at heval
  injection heval with htuple
  rcases Prod.mk.inj htuple with ⟨hstepQ_eq, hrest1⟩
  rcases Prod.mk.inj hrest1 with ⟨hqda_eq, hrest2⟩
  rcases Prod.mk.inj hrest2 with ⟨hz0_eq, hrest3⟩
  rcases Prod.mk.inj hrest3 with ⟨hz1_eq, huNext_eq⟩
  subst hstepQ_eq hqda_eq hz0_eq hz1_eq huNext_eq
  let g1 : GaussPyth :=
    { aNum := p.ga1, bNum := p.gb1, den := p.gd1, hDen := hvalid.2.2.2.1,
      hPyth := hvalid.2.2.2.2.1 }
  let g2 : GaussPyth :=
    { aNum := p.ga2, bNum := p.gb2, den := p.gd2, hDen := hvalid.2.2.2.2.2.1,
      hPyth := hvalid.2.2.2.2.2.2 }
  let rot2 : PythPair :=
    { cNum := p.cNum, sNum := p.sNum, cDen := p.cDen, hDen := hvalid.2.1, hPyth := hvalid.2.2.1 }
  let kNext : ℕ := wdStepCount p.daNum p.daDen subN
  obtain ⟨⟨hθ₁_pos, _, _⟩, _, hratio_mem⟩ := ghZoom_subN_angle_bounds hsub
  obtain ⟨_, hm2_da, _, hqda_bound⟩ := ghZoomStepCount_bounds (aNum := p.daNum) hvalid.1 hsub 2
  refine ⟨(g1, g2, rot2, kNext), ?_, hqda_bound, ?_, ?_, ?_, ?_⟩
  · unfold compileGHProbe
    rw [dite_eq_left hvalid]
  · have hg1 : wdCMem g1.val (wdCGaussRat p.ga1 p.gb1 p.gd1) := wdCMem_gaussPyth g1
    have hg2 : wdCMem g2.val (wdCGaussRat p.ga2 p.gb2 p.gd2) := wdCMem_gaussPyth g2
    have hpyth : wdMem rot2.cVal (wdRat p.cNum p.cDen) := wdMem_rat hvalid.2.1
    have huD := ghDampIV2_mem hg1 hg2 hpyth hu
    set uD := ghDampAmp2 g1 g2 rot2 u
    set uDIV := ghDampIV2 (wdCGaussRat p.ga1 p.gb1 p.gd1) (wdCGaussRat p.ga2 p.gb2 p.gd2)
      (wdRat p.cNum p.cDen) uIV
    set sHi : ℤ := wdCAbs2Hi (uDIV 0) + 2 * wdCAbs2Hi (uDIV 1) + wdCAbs2Hi (uDIV 2)
    have hs0 := normSq_le_wdCAbs2Hi (huD 0)
    have hs1 := normSq_le_wdCAbs2Hi (huD 1)
    have hs2 := normSq_le_wdCAbs2Hi (huD 2)
    have hsHi_bound :
        Complex.normSq (uD 0) + 2 * Complex.normSq (uD 1) + Complex.normSq (uD 2) ≤
          (sHi : ℝ) / wdScaleR := by
      dsimp only [sHi]; push_cast; rw [add_div, add_div, mul_div_assoc]; linarith
    have hsum_nn : 0 ≤ Complex.normSq (uD 0) + 2 * Complex.normSq (uD 1) +
        Complex.normSq (uD 2) := by
      positivity [Complex.normSq_nonneg (uD 0), Complex.normSq_nonneg (uD 1),
        Complex.normSq_nonneg (uD 2)]
    set qda := wdDivCeil (((wdRat (p.daNum : ℤ) p.daDen).2 + 4) * wdPi4InvHi) (2 * (wdScale : ℤ))
    have h1 := mul_le_mul hsHi_bound hqda_bound (Nat.cast_nonneg _) (hsum_nn.trans hsHi_bound)
    have h2 : ((sHi : ℝ) / wdScaleR) * ((qda : ℝ) * scale15) =
        (((sHi * qda : ℤ) : ℝ) / wdScaleR) * scale15 := by push_cast; ring
    have h3 : ((sHi * qda : ℤ) : ℝ) / wdScaleR ≤
        (wdDivCeil (sHi * qda) (wdScale : ℤ) : ℝ) := by
      simpa [wdScaleR] using le_wdDivCeil (a := sHi * qda) hBZ
    exact (h1.trans_eq h2).trans (mul_le_mul_of_nonneg_right h3 hs15)
  · have hg1 : wdCMem g1.val (wdCGaussRat p.ga1 p.gb1 p.gd1) := wdCMem_gaussPyth g1
    have hg2 : wdCMem g2.val (wdCGaussRat p.ga2 p.gb2 p.gd2) := wdCMem_gaussPyth g2
    have hpyth : wdMem rot2.cVal (wdRat p.cNum p.cDen) := wdMem_rat hvalid.2.1
    have hcs1 := wdTrig_mem
      (iv := (max 0 ((wdRat (p.daNum : ℤ) p.daDen).1 - 2), (wdRat (p.daNum : ℤ) p.daDen).2))
      hdphi.1 hdphi.2.1 hm2_da
    have hstep := dickeStepCIV_mem (by omega : 2 ≤ 4) hcs1.1 hcs1.2
      (ghDampIV2_mem hg1 hg2 hpyth hu)
    intro w
    dsimp only [ghProbeNextAmp2, D, θ₁] at hstep ⊢
    match w with
    | 0 | 1 | 2 => exact hstep _
    | w + 3 =>
      rw [dickeStep_eq_zero_of_gt 2 _ _ _ (by omega)]
      exact wdCMem_zero
  · have hg1 : wdCMem g1.val (wdCGaussRat p.ga1 p.gb1 p.gd1) := wdCMem_gaussPyth g1
    have hθ₁_ne : θ₁ ≠ 0 := by
      dsimp only [θ₁, D]
      exact ne_of_gt hθ₁_pos
    have hm2_2 : wdMem (2 * (kNext : ℝ) * θ₂)
        (wdMul (max 0 ((wdRat (p.daNum : ℤ) p.daDen).1 - 2), (wdRat (p.daNum : ℤ) p.daDen).2)
          (wdSqrt2Lo - 1, wdSqrt2Hi + 1)) := by
      have heq : 2 * (kNext : ℝ) * θ₂ = (2 * (kNext : ℝ) * θ₁) * (θ₂ / θ₁) := by
        field_simp [hθ₁_ne]
      rw [heq]; exact wdMem_mul hm2_da hratio_mem
    have hcs2 := wdTrig_mem
      (iv := wdMul (max 0 ((wdRat (p.daNum : ℤ) p.daDen).1 - 2), (wdRat (p.daNum : ℤ) p.daDen).2)
        (wdSqrt2Lo - 1, wdSqrt2Hi + 1))
      hdphi.2.2.1 hdphi.2.2.2 hm2_2
    dsimp only [ghProbeNextColl2, D, θ₂]
    exact wdCMem_sub (wdCMem_rmul hcs2.1 hz0) (wdCMem_rmul hcs2.2 (wdCMem_mul hg1 hz1))
  · have hg1 : wdCMem g1.val (wdCGaussRat p.ga1 p.gb1 p.gd1) := wdCMem_gaussPyth g1
    have hθ₁_ne : θ₁ ≠ 0 := by
      dsimp only [θ₁, D]
      exact ne_of_gt hθ₁_pos
    have hm2_2 : wdMem (2 * (kNext : ℝ) * θ₂)
        (wdMul (max 0 ((wdRat (p.daNum : ℤ) p.daDen).1 - 2), (wdRat (p.daNum : ℤ) p.daDen).2)
          (wdSqrt2Lo - 1, wdSqrt2Hi + 1)) := by
      have heq : 2 * (kNext : ℝ) * θ₂ = (2 * (kNext : ℝ) * θ₁) * (θ₂ / θ₁) := by
        field_simp [hθ₁_ne]
      rw [heq]; exact wdMem_mul hm2_da hratio_mem
    have hcs2 := wdTrig_mem
      (iv := wdMul (max 0 ((wdRat (p.daNum : ℤ) p.daDen).1 - 2), (wdRat (p.daNum : ℤ) p.daDen).2)
        (wdSqrt2Lo - 1, wdSqrt2Hi + 1))
      hdphi.2.2.1 hdphi.2.2.2 hm2_2
    dsimp only [ghProbeNextColl2, D, θ₂]
    exact wdCMem_add (wdCMem_rmul hcs2.2 hz0) (wdCMem_rmul hcs2.1 (wdCMem_mul hg1 hz1))
private lemma ghZoomProbes_sound {subN : ℕ} (hsub : 200 ≤ subN) :
    let D : ℝ := (2 ^ subN : ℝ)
    let θ₁ : ℝ := Real.arcsin (1 / √D)
    let θ₂ : ℝ := Real.arcsin (√2 / √D)
    let scale15 : ℝ := ((π / 4) * √D) / wdScaleR
    ∀ (ps : List GHProbeSpec) {u : ℕ → ℂ} {uIV : ℕ → WDCVal}
      {z : ℂ × ℂ} {z0IV z1IV : WDCVal}
      {qEx qCollAdd : ℤ} {z0Fin z1Fin : WDCVal} {uFinal : ℕ → WDCVal},
      evalGHProbes ps uIV z0IV z1IV = some (qEx, qCollAdd, z0Fin, z1Fin, uFinal) →
      (∀ w, wdCMem (u w) (uIV w)) →
      wdCMem z.1 z0IV →
      wdCMem z.2 z1IV →
      ∃ probes,
        compileGHProbes ps subN = some probes ∧
        (((probes.map fun pk ↦ pk.2.2.2 + 2).sum : ℕ) : ℝ) ≤ (qCollAdd : ℝ) * scale15 ∧
        ghChainExtraQueries2 θ₁ probes u ≤ (qEx : ℝ) * scale15 ∧
        (∀ w, wdCMem (ghChainFinalAmp2 θ₁ probes u w) (uFinal w)) ∧
        wdCMem (ghChainFinalColl2 θ₂ probes z).1 z0Fin ∧
        wdCMem (ghChainFinalColl2 θ₂ probes z).2 z1Fin := by
  intro D θ₁ θ₂ scale15 ps
  induction ps with
  | nil =>
    intro u uIV z z0IV z1IV qEx qCollAdd z0Fin z1Fin uFinal heval hu hz0 hz1
    simp only [evalGHProbes, Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, by simp, by simp [ghChainExtraQueries2],
      fun w ↦ by simpa [ghChainFinalAmp2] using hu w,
      by simpa [ghChainFinalColl2] using hz0,
      by simpa [ghChainFinalColl2] using hz1⟩
  | cons p rest ih =>
    intro u uIV z z0IV z1IV qEx qCollAdd z0Fin z1Fin uFinal heval hu hz0 hz1
    simp only [evalGHProbes] at heval
    cases hstep : evalGHProbeStep p uIV z0IV z1IV with
    | none => rw [hstep] at heval; cases heval
    | some sRes =>
      rcases sRes with ⟨stepQ, qdaHi, z0N, z1N, uNext⟩
      rw [hstep] at heval
      dsimp only at heval
      cases hrest : evalGHProbes rest uNext z0N z1N with
      | none => rw [hrest] at heval; cases heval
      | some rRes =>
        rcases rRes with ⟨qExR, qCollR, z0F, z1F, uFin⟩
        rw [hrest] at heval
        simp only [ghSeqIV_eq, Option.some.injEq, Prod.mk.injEq] at heval
        rcases heval with ⟨rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨pk, hc1, hqda, hstepQ, huN, hz0N, hz1N⟩ :=
          ghZoomProbeStep_sound hsub hstep hu hz0 hz1
        obtain ⟨tail, hc2, hqCollR, hexR, hufR, hz0F, hz1F⟩ :=
          ih hrest huN hz0N hz1N
        refine ⟨pk :: tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [compileGHProbes, hc1, hc2]
        · simp only [List.map_cons, List.sum_cons]
          push_cast at hqda hqCollR ⊢
          linarith
        · simp only [ghChainExtraQueries2]
          push_cast at hstepQ hexR ⊢
          linarith
        · intro w
          dsimp only [ghChainFinalAmp2, D, θ₁] at hufR ⊢
          exact hufR w
        · dsimp only [ghChainFinalColl2, D, θ₂] at hz0F ⊢
          exact hz0F
        · dsimp only [ghChainFinalColl2, D, θ₂] at hz1F ⊢
          exact hz1F
/-- Certified `10 ^ 15`-scaled upper bound on `1 / √m` for `m ∈ {4, 8,..., 1024}`. -/
def ghInvSqrtMHi (m : ℕ) : Option ℤ :=
  if m = 4 then some 500000000000000
  else if m = 8 then some (wdDivCeil wdSqrt2Hi 4)
  else if m = 16 then some 250000000000000
  else if m = 32 then some (wdDivCeil wdSqrt2Hi 8)
  else if m = 64 then some 125000000000000
  else if m = 128 then some (wdDivCeil wdSqrt2Hi 16)
  else if m = 256 then some 62500000000000
  else if m = 512 then some (wdDivCeil wdSqrt2Hi 32)
  else if m = 1024 then some 31250000000000
  else none
/-- Pass-independent `10 ^ 15`-scaled summary evaluated once per `(m, rowSpec)`. -/
structure GHZoomSummary where
  qDistHi : ℤ
  qCollHi : ℤ
  qZoomHi : ℤ
  zHitLo : ℤ
  u0Hi : ℤ
  u1Hi : ℤ
  z0Hi : ℤ
  z1Hi : ℤ
  deriving DecidableEq, Repr
/-- Evaluates the `16`-probe complex-interval chain once per `(m, spec)`. -/
def evalGHZoomRowSummary (m : ℕ) (spec : GHZoomRowSpec) : Option GHZoomSummary :=
  match ghInvSqrtMHi m with
  | none => none
  | some invSqrtMHi =>
      let p := Stage2CertInternals.gridExp m
      if 4 ≤ m ∧ m = 2 ^ p ∧ p ≤ 10 ∧ 0 < spec.a0Den ∧ 0 < spec.bDen ∧
          0 ≤ invSqrtMHi ∧ (wdScale : ℤ) ^ 2 ≤ invSqrtMHi ^ 2 * (m : ℤ) then
        let a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den
        let phi0IV : WDIVal := (ghMaxZ 0 (a0IV.1 - 1), a0IV.2 + 1)
        let phi02IV : WDIVal := ghMulIV phi0IV (wdSqrt2Lo - 1, wdSqrt2Hi + 1)
        ghTrigCPS phi0IV fun c0 s0 ↦
        ghTrigCPS phi02IV fun c02 s02 ↦
        let u0IV := wdCReify5 (dickeStepCIV 2 c0 s0
          (fun w ↦ if w = 0 then wdCOne else wdCZero))
        let z0IV := wdCOfReal c02
        let z1IV := wdCOfReal s02
        let q0Hi := wdDivCeil ((a0IV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
        match evalGHProbes spec.probes u0IV z0IV z1IV with
        | none => none
        | some (qExtraHi, qCollAddHi, z0Fin, z1Fin, ufIV) =>
            let qDistHi := q0Hi + qExtraHi
            let qCollHi := q0Hi + qCollAddHi
            let bIV := wdRat (spec.bNum : ℤ) spec.bDen
            let phiZoomIV : WDIVal := (ghMaxZ 0 (bIV.1 - 1), bIV.2 + 1)
            let zHitLo := (ghSqIV (ghTrig phiZoomIV).2).1
            let qZoomSub2Hi := wdDivCeil ((bIV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
            let qZoomHi := wdDivCeil (qZoomSub2Hi * invSqrtMHi) (wdScale : ℤ)
            if 0 ≤ phi0IV.1 ∧ phi0IV.2 ≤ 1024 * (wdScale : ℤ) ∧
                0 ≤ phi02IV.1 ∧ phi02IV.2 ≤ 1024 * (wdScale : ℤ) ∧
                0 ≤ phiZoomIV.1 ∧ phiZoomIV.2 ≤ 1024 * (wdScale : ℤ) ∧
                0 ≤ zHitLo ∧ zHitLo ≤ (wdScale : ℤ) ∧
                qCollHi + qZoomHi ≤ 12 * (wdScale : ℤ) then
              some
                { qDistHi := ghForceInt qDistHi
                  qCollHi := ghForceInt qCollHi
                  qZoomHi := ghForceInt qZoomHi
                  zHitLo := ghForceInt zHitLo
                  u0Hi := ghForceInt (wdCAbs2Hi (ufIV 0))
                  u1Hi := ghForceInt (wdCAbs2Hi (ufIV 1))
                  z0Hi := ghForceInt (wdCAbs2Hi z0Fin)
                  z1Hi := ghForceInt (wdCAbs2Hi z1Fin) }
            else
              none
      else
        none
/-- Scalar `O(1)` Bellman step contracting `vNext` via pre-evaluated `GHZoomSummary`. -/
def evalGHZoomStepFromSummary (m : ℕ) (s : GHZoomSummary) (vNext : List ℕ) : Option ℕ :=
  let fr215 : ℤ := (vNext.getD 2 0 : ℤ) * 1000000
  let fr115 : ℤ := (vNext.getD 1 0 : ℤ) * 1000000
  let remDist0Hi := wdDivCeil (s.u0Hi * fr215) (wdScale : ℤ)
  let remDist1Hi := wdDivCeil (2 * s.u1Hi * (s.qZoomHi + fr115)) (wdScale : ℤ)
  let clickZoomRemHi := s.qZoomHi + wdDivCeil (((wdScale : ℤ) - s.zHitLo) * fr115) (wdScale : ℤ)
  let collRemHi := wdDivCeil (s.z0Hi * fr215) (wdScale : ℤ) +
    wdDivCeil (s.z1Hi * clickZoomRemHi) (wdScale : ℤ)
  let mPow : ℤ := ((m ^ 2 : ℕ) : ℤ)
  let descM : ℤ := ((m.descFactorial 2 : ℕ) : ℤ)
  let totalNum15 : ℤ := descM * (s.qDistHi + remDist0Hi + remDist1Hi) +
    (m : ℤ) * (s.qCollHi + collRemHi)
  let outHiZ : ℤ := wdDivCeil totalNum15 (mPow * 1000000)
  if 0 ≤ outHiZ then some outHiZ.toNat else none
/-- Certified `10 ^ 9`-scaled integer upper bound on `ghZoomOneDimUpper subN p m` (`210 ≤
  subN`). -/
def evalGHZoomRowHi (m r : ℕ) (specOpt : Option GHZoomRowSpec) (vNext : List ℕ) : Option ℕ :=
  if r = 0 then
    if specOpt.isNone then some 0 else none
  else
    match specOpt with
    | none => some (vNext.getD r 0)
    | some spec =>
        if r = 2 then
          match evalGHZoomRowSummary m spec with
          | none => none
          | some s => evalGHZoomStepFromSummary m s vNext
        else
          none
private lemma ghOne_div_sqrt_m_le_of_sq {m : ℕ} {inv : ℤ}
    (hm_pos : 0 < m) (hinv_nn : 0 ≤ inv) (hsq : (wdScale : ℤ) ^ 2 ≤ inv ^ 2 * (m : ℤ)) :
    (1 : ℝ) / √(m : ℝ) ≤ (inv : ℝ) / wdScaleR := by
  have hB := ghZoomScaleR_pos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hsqrt_pos : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hmR
  have hinvR_nn : 0 ≤ (inv : ℝ) / wdScaleR := div_nonneg (by exact_mod_cast hinv_nn) hB.le
  rw [div_le_iff₀ hsqrt_pos]
  have hsqR : (1 : ℝ) ≤ (((inv : ℝ) / wdScaleR) * √(m : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hmR.le, div_pow, div_mul_eq_mul_div,
      le_div_iff₀ (pow_pos hB 2), one_mul]
    unfold wdScaleR
    exact_mod_cast hsq
  have hprod_nn : 0 ≤ ((inv : ℝ) / wdScaleR) * √(m : ℝ) := mul_nonneg hinvR_nn hsqrt_pos.le
  by_contra hlt; push Not at hlt
  nlinarith
private lemma ghZoom_kZoom_bound {subN p m bNum bDen : ℕ} {invSqrtMHi : ℤ}
    (hsub : 210 ≤ subN) (hp10 : p ≤ 10) (hm4 : 4 ≤ m) (hm_pow : m = 2 ^ p)
    (hbDen : 0 < bDen) (hinv_nn : 0 ≤ invSqrtMHi)
    (hinv_sq : (wdScale : ℤ) ^ 2 ≤ invSqrtMHi ^ 2 * (m : ℤ)) :
    let D : ℝ := (2 ^ subN : ℝ)
    let scale15 : ℝ := ((π / 4) * √D) / wdScaleR
    let bIV := wdRat (bNum : ℤ) bDen
    let kZoom := wdStepCount bNum bDen (subN - p)
    let qZoomSub2Hi := wdDivCeil ((bIV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
    let qZoomHi := wdDivCeil (qZoomSub2Hi * invSqrtMHi) (wdScale : ℤ)
    wdMem ((2 * (kZoom : ℝ) + 1) * Real.arcsin (1 / √(2 ^ (subN - p) : ℝ)))
        (max 0 (bIV.1 - 1), bIV.2 + 1) ∧
      0 ≤ qZoomHi ∧
      ((kZoom + 1 : ℕ) : ℝ) ≤ (qZoomHi : ℝ) * scale15 := by
  intro D scale15 bIV kZoom qZoomSub2Hi qZoomHi
  have hB := ghZoomScaleR_pos
  have hBZ : (0 : ℤ) < (wdScale : ℤ) := by unfold wdScale; norm_num
  have hs15_nn : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
  have hsub2 : 200 ≤ subN - p := by omega
  have hp_sub : p ≤ subN := by omega
  obtain ⟨hmem_z, _, hqZ2_nn, hqZ2_bound⟩ :=
    ghZoomStepCount_bounds (aNum := bNum) hbDen hsub2 1
  have hqZ_nn : 0 ≤ qZoomHi := wdDivCeil_nonneg (mul_nonneg hqZ2_nn hinv_nn) hBZ
  refine ⟨hmem_z, hqZ_nn, ?_⟩
  have hm_pos : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hsqrt_m_pos : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hmR
  have hinv_le : (1 : ℝ) / √(m : ℝ) ≤ (invSqrtMHi : ℝ) / wdScaleR :=
    ghOne_div_sqrt_m_le_of_sq hm_pos hinv_nn hinv_sq
  have hpow_split : (2 ^ subN : ℝ) = (2 ^ (subN - p) : ℝ) * (m : ℝ) := by
    have hpow_nat : 2 ^ subN = 2 ^ (subN - p) * 2 ^ p := by
      rw [← pow_add, Nat.sub_add_cancel hp_sub]
    rw [hm_pow]
    exact_mod_cast hpow_nat
  have hsqrt_split : √(2 ^ (subN - p) : ℝ) = √D * (1 / √(m : ℝ)) := by
    dsimp only [D]
    rw [hpow_split, Real.sqrt_mul (by positivity), mul_one_div,
      mul_div_cancel_right₀ _ hsqrt_m_pos.ne']
  have hsc_split : ((π / 4) * √(2 ^ (subN - p) : ℝ)) / wdScaleR =
      scale15 * (1 / √(m : ℝ)) := by
    dsimp only [scale15, D]
    rw [hsqrt_split]
    ring
  rw [hsc_split] at hqZ2_bound
  have hqZ2_nnR : (0 : ℝ) ≤ (qZoomSub2Hi : ℝ) := by exact_mod_cast hqZ2_nn
  have hstep1 : scale15 * (1 / √(m : ℝ)) ≤ scale15 * ((invSqrtMHi : ℝ) / wdScaleR) :=
    mul_le_mul_of_nonneg_left hinv_le hs15_nn
  have hstep2 : (qZoomSub2Hi : ℝ) * (scale15 * ((invSqrtMHi : ℝ) / wdScaleR)) =
      (((qZoomSub2Hi * invSqrtMHi : ℤ) : ℝ) / wdScaleR) * scale15 := by
    push_cast; ring
  have hceil : (((qZoomSub2Hi * invSqrtMHi : ℤ) : ℝ) / wdScaleR) ≤ (qZoomHi : ℝ) := by
    simpa [qZoomHi, wdScaleR] using le_wdDivCeil (a := qZoomSub2Hi * invSqrtMHi) hBZ
  exact (hqZ2_bound.trans (mul_le_mul_of_nonneg_left hstep1 hqZ2_nnR)).trans
    ((le_of_eq hstep2).trans (mul_le_mul_of_nonneg_right hceil hs15_nn))
theorem evalGHZoomRowHi_qBound {m r subN : ℕ} {ps : GHZoomPassSpec} {vNext : List ℕ} {outVal : ℕ}
    (heval : evalGHZoomRowHi m r (ps.getD r none) vNext = some outVal) (hsub : 210 ≤ subN)
    {kInit : ℕ} {probes : List GHZoomProbe} {kZoom : ℕ}
    (hcomp : compileGHZoomPassSpec (Stage2CertInternals.gridExp m) ps subN r =
      some (kInit, probes, kZoom)) :
    (ghZoomMaxQueries kInit probes kZoom : ℝ) ≤ 12 * ((π / 4) * √(2 ^ subN : ℝ)) := by
  unfold evalGHZoomRowHi at heval
  unfold compileGHZoomPassSpec at hcomp
  by_cases hr0 : r = 0
  · subst hr0
    simp only [↓reduceIte] at heval
    split_ifs at heval with hnone
    rw [Option.isNone_iff_eq_none.mp hnone] at hcomp
    cases hcomp
  · simp only [hr0, ↓reduceIte] at heval
    cases hopt : ps.getD r none with
    | none => rw [hopt] at hcomp; cases hcomp
    | some spec =>
      rw [hopt] at heval hcomp
      dsimp only at heval hcomp
      split_ifs at heval with hr2
      subst hr2
      cases hsum : evalGHZoomRowSummary m spec with
      | none => rw [hsum] at heval; cases heval
      | some s =>
        unfold evalGHZoomRowSummary at hsum
        simp only [ghMaxZ_eq, ghMulIV_eq, ghSqIV_eq, ghTrigCPS_eq, ghTrig_eq] at hsum
        cases hinv : ghInvSqrtMHi m with
        | none => rw [hinv] at hsum; cases hsum
        | some invSqrtMHi =>
          rw [hinv] at hsum
          dsimp only at hsum
          split_ifs at hsum with hvalid
          rcases hvalid with ⟨hm4, hm_pow, hp10, ha0Den, hbDen, hinv_nn, hinv_sq⟩
          set a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den
          set phi0IV : WDIVal := (max 0 (a0IV.1 - 1), a0IV.2 + 1)
          set phi02IV : WDIVal := wdMul phi0IV (wdSqrt2Lo - 1, wdSqrt2Hi + 1)
          set cs0 := wdTrig phi0IV
          set cs02 := wdTrig phi02IV
          set u0IV := wdCReify5 (dickeStepCIV 2 cs0.1 cs0.2
            (fun w ↦ if w = 0 then wdCOne else wdCZero))
          set z0IV := wdCOfReal cs02.1
          set z1IV := wdCOfReal cs02.2
          cases hpRes : evalGHProbes spec.probes u0IV z0IV z1IV with
          | none => rw [hpRes] at hsum; cases hsum
          | some pTuple =>
            rcases pTuple with ⟨qExtraHi, qCollAddHi, z0Fin, z1Fin, ufIV⟩
            rw [hpRes] at hsum
            dsimp only at hsum
            split_ifs at hsum with hguard
            unfold compileGHZoomRow at hcomp
            rw [ite_eq_left ⟨ha0Den, hbDen⟩] at hcomp
            cases hcPr : compileGHProbes spec.probes subN with
            | none => rw [hcPr] at hcomp; cases hcomp
            | some prList =>
              rw [hcPr] at hcomp
              injection hcomp with htriple
              rcases Prod.mk.inj htriple with ⟨hkInit, hrest⟩
              rcases Prod.mk.inj hrest with ⟨hpr, hkZoom⟩
              subst hkInit hpr hkZoom
              set D : ℝ := (2 ^ subN : ℝ)
              set scale15 : ℝ := ((π / 4) * √D) / wdScaleR
              have hB := ghZoomScaleR_pos
              have hs15_nn : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
              obtain ⟨_, _, _, hq0_bound⟩ :=
                ghZoomStepCount_bounds (subN := subN) (aNum := spec.a0Num) ha0Den (by omega) 1
              have hqAdd := ghZoomProbes_qColl (subN := subN) (by omega)
                spec.probes u0IV z0IV z1IV hpRes hcPr
              obtain ⟨_, _, hqZoom_bound⟩ :=
                ghZoom_kZoom_bound hsub hp10 hm4 hm_pow hbDen hinv_nn hinv_sq
                  (bNum := spec.bNum)
              set q0Hi := wdDivCeil ((a0IV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
              set qCollHi : ℤ := q0Hi + qCollAddHi
              set bIV := wdRat (spec.bNum : ℤ) spec.bDen
              set qZoomSub2Hi := wdDivCeil ((bIV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
              set qZoomHi := wdDivCeil (qZoomSub2Hi * invSqrtMHi) (wdScale : ℤ)
              have hqColl :
                  (ghMaxQueries (wdStepCount spec.a0Num spec.a0Den subN) prList : ℝ) ≤
                    (qCollHi : ℝ) * scale15 := by
                unfold ghMaxQueries
                dsimp only [qCollHi]
                push_cast at hq0_bound hqAdd ⊢
                linarith
              have hsum_q :
                  (ghZoomMaxQueries (wdStepCount spec.a0Num spec.a0Den subN) prList
                    (wdStepCount spec.bNum spec.bDen
                      (subN - Stage2CertInternals.gridExp m)) : ℝ) ≤
                    ((qCollHi + qZoomHi : ℤ) : ℝ) * scale15 := by
                unfold ghZoomMaxQueries
                push_cast at hqColl hqZoom_bound ⊢
                linarith
              have h12_Z : qCollHi + qZoomHi ≤ 12 * (wdScale : ℤ) :=
                hguard.2.2.2.2.2.2.2.2
              have h12_R : ((qCollHi + qZoomHi : ℤ) : ℝ) ≤ 12 * wdScaleR := by
                unfold wdScaleR; exact_mod_cast h12_Z
              calc _ ≤ ((qCollHi + qZoomHi : ℤ) : ℝ) * scale15 := hsum_q
                _ ≤ (12 * wdScaleR) * scale15 := mul_le_mul_of_nonneg_right h12_R hs15_nn
                _ = 12 * ((π / 4) * √D) := by dsimp only [scale15]; field_simp [hB.ne']
theorem evalGHZoomRowHi_sound {m r subN : ℕ} {ps : GHZoomPassSpec} {vNext : List ℕ} {outVal : ℕ}
    (heval : evalGHZoomRowHi m r (ps.getD r none) vNext = some outVal) (hsub : 210 ≤ subN)
    {fNext : ℕ → ℝ}
    (hf : ∀ u ≤ r, 0 ≤ fNext u ∧
      fNext u ≤ (vNext.getD u 0 : ℝ) *
        (((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ))) :
    let p := Stage2CertInternals.gridExp m
    ghZoomOneDimUpper subN p m (compileGHZoomPassSpec p ps subN r) fNext r ≤
      (outVal : ℝ) * (((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ)) := by
  intro p
  set D : ℝ := (2 ^ subN : ℝ)
  set scale : ℝ := ((π / 4) * √D) / (Stage2CertInternals.M_scale : ℝ)
  set scale15 : ℝ := ((π / 4) * √D) / wdScaleR
  have hB := ghZoomScaleR_pos
  have hBZ : (0 : ℤ) < (wdScale : ℤ) := by unfold wdScale; norm_num
  have hscale_eq : scale = 1000000 * scale15 := by
    dsimp only [scale, scale15]
    unfold Stage2CertInternals.M_scale wdScaleR wdScale
    ring
  have hs15_nn : 0 ≤ scale15 := div_nonneg (by positivity [Real.pi_pos]) hB.le
  by_cases hr0 : r = 0
  · subst hr0
    unfold evalGHZoomRowHi at heval
    simp only [↓reduceIte] at heval
    split_ifs at heval
    cases heval
    simp [ghZoomOneDimUpper]
  · unfold evalGHZoomRowHi at heval
    simp only [hr0, ↓reduceIte] at heval
    cases hopt : ps.getD r none with
    | none =>
      rw [hopt] at heval
      cases heval
      unfold ghZoomOneDimUpper compileGHZoomPassSpec
      simp only [hr0, ↓reduceIte, hopt]
      exact (hf r le_rfl).2
    | some spec =>
      rw [hopt] at heval
      dsimp only at heval
      split_ifs at heval with hr2
      subst hr2
      cases hsum : evalGHZoomRowSummary m spec with
      | none => rw [hsum] at heval; cases heval
      | some s =>
        rw [hsum] at heval
        unfold evalGHZoomStepFromSummary at heval
        dsimp only at heval
        split_ifs at heval with hout_nn
        cases heval
        unfold evalGHZoomRowSummary at hsum
        simp only [ghMaxZ_eq, ghMulIV_eq, ghSqIV_eq, ghTrigCPS_eq, ghTrig_eq] at hsum
        cases hinv : ghInvSqrtMHi m with
        | none => rw [hinv] at hsum; cases hsum
        | some invSqrtMHi =>
          rw [hinv] at hsum
          dsimp only [p] at hsum ⊢
          split_ifs at hsum with hvalid
          rcases hvalid with ⟨hm4, hm_pow, hp10, ha0Den, hbDen, hinv_nn, hinv_sq⟩
          set a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den
          set phi0IV : WDIVal := (max 0 (a0IV.1 - 1), a0IV.2 + 1)
          set phi02IV : WDIVal := wdMul phi0IV (wdSqrt2Lo - 1, wdSqrt2Hi + 1)
          set cs0 := wdTrig phi0IV
          set cs02 := wdTrig phi02IV
          set u0IV := wdCReify5 (dickeStepCIV 2 cs0.1 cs0.2
            (fun w ↦ if w = 0 then wdCOne else wdCZero))
          set z0IV := wdCOfReal cs02.1
          set z1IV := wdCOfReal cs02.2
          cases hpRes : evalGHProbes spec.probes u0IV z0IV z1IV with
          | none => rw [hpRes] at hsum; cases hsum
          | some pTuple =>
            rcases pTuple with ⟨qExtraHi, qCollAddHi, z0Fin, z1Fin, ufIV⟩
            rw [hpRes] at hsum
            dsimp only at hsum
            split_ifs at hsum with hguard
            injection hsum with hs_eq
            subst hs_eq
            simp only [ghForceInt_eq] at hout_nn ⊢
            rcases hguard with ⟨hphi0_lo, hphi0_hi, hphi02_lo, hphi02_hi,
              hphiZ_lo, hphiZ_hi, hzHit_lo_nn, hzHit_le, _⟩
            set kInit := wdStepCount spec.a0Num spec.a0Den subN
            set kZoom := wdStepCount spec.bNum spec.bDen (subN - p)
            set θ₁ := Real.arcsin (1 / √D)
            set θ₂ := Real.arcsin (√2 / √D)
            obtain ⟨⟨hθ₁_pos, _, _⟩, _, hratio_mem⟩ :=
              ghZoom_subN_angle_bounds (subN := subN) (by omega)
            obtain ⟨hm1_0, _, _, hq0_bound⟩ :=
              ghZoomStepCount_bounds (subN := subN) (aNum := spec.a0Num) ha0Den (by omega) 1
            obtain ⟨hphiZ_mem, hqZoom_nn, hqZoom_bound⟩ :=
              ghZoom_kZoom_bound hsub hp10 hm4 hm_pow hbDen hinv_nn hinv_sq (bNum := spec.bNum)
            have hm1_02 : wdMem ((2 * (kInit : ℝ) + 1) * θ₂) phi02IV := by
              have heq : (2 * (kInit : ℝ) + 1) * θ₂ = ((2 * (kInit : ℝ) + 1) * θ₁) * (θ₂ / θ₁) := by
                rw [mul_assoc, mul_div_cancel₀ _ hθ₁_pos.ne']
              rw [heq]; exact wdMem_mul hm1_0 hratio_mem
            have hcs0 := wdTrig_mem hphi0_lo hphi0_hi hm1_0
            have hcs02 := wdTrig_mem hphi02_lo hphi02_hi hm1_02
            have hu_base : ∀ w, wdCMem (if w = 0 then (1 : ℂ) else 0)
                (if w = 0 then wdCOne else wdCZero) := by
              intro w; by_cases hw : w = 0 <;> simp [hw, wdCMem_one, wdCMem_zero]
            have hu0 : ∀ w, wdCMem (ghInitAmp2 θ₁ kInit w) (u0IV w) :=
              wdCReify5_mem (by omega) (fun _ hw ↦ dickeStep_eq_zero_of_gt 2 _ _ _ hw)
                (dickeStepCIV_mem (by omega : 2 ≤ 4) hcs0.1 hcs0.2 hu_base)
            have hz0_init : wdCMem (ghInitColl2 θ₂ kInit).1 z0IV := wdCMem_ofReal hcs02.1
            have hz1_init : wdCMem (ghInitColl2 θ₂ kInit).2 z1IV := wdCMem_ofReal hcs02.2
            obtain ⟨probes, hcProbes, hqCollAdd, hextra, huf, hzf0, hzf1⟩ :=
              ghZoomProbes_sound (subN := subN) (by omega) spec.probes hpRes
                hu0 hz0_init hz1_init
            unfold ghZoomOneDimUpper compileGHZoomPassSpec
            rw [ite_eq_right (by omega : (2 : ℕ) ≠ 0), hopt]
            dsimp only [compileGHZoomRow]
            rw [ite_eq_left ⟨ha0Den, hbDen⟩, hcProbes]
            dsimp only
            rw [ite_eq_left rfl]
            set q0Hi := wdDivCeil ((a0IV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
            set qDistHi := q0Hi + qExtraHi
            set qCollHi := q0Hi + qCollAddHi
            set bIV := wdRat (spec.bNum : ℤ) spec.bDen
            set qZoomSub2Hi := wdDivCeil ((bIV.2 + 2) * wdPi4InvHi) (2 * (wdScale : ℤ))
            set qZoomHi := wdDivCeil (qZoomSub2Hi * invSqrtMHi) (wdScale : ℤ)
            have hqDist :
                ((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes (ghInitAmp2 θ₁ kInit) ≤
                  (qDistHi : ℝ) * scale15 := by
              have hq0' : ((kInit + 1 : ℕ) : ℝ) ≤ (q0Hi : ℝ) * scale15 := by
                simpa [q0Hi, a0IV] using hq0_bound
              have hextra' :
                  ghChainExtraQueries2 θ₁ probes (ghInitAmp2 θ₁ kInit) ≤
                    (qExtraHi : ℝ) * scale15 := by
                dsimp only [D, θ₁, scale15] at hextra ⊢; exact hextra
              have hcast : (qDistHi : ℝ) * scale15 =
                  (q0Hi : ℝ) * scale15 + (qExtraHi : ℝ) * scale15 := by
                dsimp only [qDistHi]; push_cast; ring
              rw [hcast]; exact add_le_add hq0' hextra'
            have hqColl : (ghMaxQueries kInit probes : ℝ) ≤ (qCollHi : ℝ) * scale15 := by
              unfold ghMaxQueries
              have hq0' : ((kInit + 1 : ℕ) : ℝ) ≤ (q0Hi : ℝ) * scale15 := by
                simpa [q0Hi, a0IV] using hq0_bound
              have hqAdd' : (((probes.map fun pk ↦ pk.2.2.2 + 2).sum : ℕ) : ℝ) ≤
                  (qCollAddHi : ℝ) * scale15 := by
                simpa [D, scale15] using hqCollAdd
              dsimp only [qCollHi]; push_cast at hq0' hqAdd' ⊢; linarith
            have hqZoom : ((kZoom + 1 : ℕ) : ℝ) ≤ (qZoomHi : ℝ) * scale15 := by
              simpa [kZoom, qZoomHi, qZoomSub2Hi, bIV, D, scale15] using hqZoom_bound
            set fr215 : ℤ := (vNext.getD 2 0 : ℤ) * 1000000
            set fr115 : ℤ := (vNext.getD 1 0 : ℤ) * 1000000
            obtain ⟨hf1_nn, hf1_hi0⟩ := hf 1 (by omega)
            obtain ⟨hf2_nn, hf2_hi0⟩ := hf 2 le_rfl
            have hf2_hi : fNext 2 ≤ (fr215 : ℝ) * scale15 := by
              rw [hscale_eq] at hf2_hi0; dsimp only [fr215]; push_cast; linarith
            have hf1_hi : fNext 1 ≤ (fr115 : ℝ) * scale15 := by
              rw [hscale_eq] at hf1_hi0; dsimp only [fr115]; push_cast; linarith
            set uf := ghChainFinalAmp2 θ₁ probes (ghInitAmp2 θ₁ kInit)
            set zf := ghChainFinalColl2 θ₂ probes (ghInitColl2 θ₂ kInit)
            set u0Hi := wdCAbs2Hi (ufIV 0)
            set u1Hi := wdCAbs2Hi (ufIV 1)
            set z0Hi := wdCAbs2Hi z0Fin
            set z1Hi := wdCAbs2Hi z1Fin
            set remDist0Hi := wdDivCeil (u0Hi * fr215) (wdScale : ℤ)
            set remDist1Hi := wdDivCeil (2 * u1Hi * (qZoomHi + fr115)) (wdScale : ℤ)
            have hrem0 : Complex.normSq (uf 0) * fNext 2 ≤ (remDist0Hi : ℝ) * scale15 := by
              have hsq0 := normSq_le_wdCAbs2Hi (by dsimp only [uf, D, θ₁] at huf ⊢; exact huf 0)
              have hm := mul_le_mul hsq0 hf2_hi hf2_nn
                (le_trans (Complex.normSq_nonneg _) hsq0)
              have heq : ((u0Hi : ℝ) / wdScaleR) * ((fr215 : ℝ) * scale15) =
                  (((u0Hi * fr215 : ℤ) : ℝ) / wdScaleR) * scale15 := by push_cast; ring
              have hceil := le_wdDivCeil (a := u0Hi * fr215) hBZ
              exact (hm.trans_eq heq).trans
                (mul_le_mul_of_nonneg_right (by simpa [wdScaleR] using hceil) hs15_nn)
            have hrem1 :
                2 * Complex.normSq (uf 1) * (((kZoom + 1 : ℕ) : ℝ) + fNext 1) ≤
                  (remDist1Hi : ℝ) * scale15 := by
              have h1 := normSq_le_wdCAbs2Hi (by dsimp only [uf, D, θ₁] at huf ⊢; exact huf 1)
              have hsq1 : 2 * Complex.normSq (uf 1) ≤ ((2 * u1Hi : ℤ) : ℝ) / wdScaleR := by
                push_cast; rw [mul_div_assoc]; linarith
              have hzf1_nn : 0 ≤ ((kZoom + 1 : ℕ) : ℝ) + fNext 1 := by positivity
              have hzf1_hi :
                  ((kZoom + 1 : ℕ) : ℝ) + fNext 1 ≤ ((qZoomHi + fr115 : ℤ) : ℝ) * scale15 := by
                push_cast at hqZoom ⊢; linarith
              have hm := mul_le_mul hsq1 hzf1_hi hzf1_nn
                (le_trans (by positivity [Complex.normSq_nonneg (uf 1)]) hsq1)
              have heq : (((2 * u1Hi : ℤ) : ℝ) / wdScaleR) *
                  (((qZoomHi + fr115 : ℤ) : ℝ) * scale15) =
                  (((2 * u1Hi * (qZoomHi + fr115) : ℤ) : ℝ) / wdScaleR) * scale15 := by
                push_cast; ring
              have hceil := le_wdDivCeil (a := 2 * u1Hi * (qZoomHi + fr115)) hBZ
              exact (hm.trans_eq heq).trans
                (mul_le_mul_of_nonneg_right (by simpa [wdScaleR] using hceil) hs15_nn)
            set phiZoomIV : WDIVal := (max 0 (bIV.1 - 1), bIV.2 + 1)
            set zHitLo := (wdSq (wdTrig phiZoomIV).2).1
            set pZoom := p_succ_frac kZoom 1 (2 ^ (subN - p))
            have hpZoom_eq : pZoom =
                Real.sin ((2 * (kZoom : ℝ) + 1) * Real.arcsin (1 / √(2 ^ (subN - p) : ℝ))) ^ 2 := by
              dsimp only [pZoom]; unfold p_succ_frac; push_cast
              rw [one_div, Real.sqrt_inv, ← one_div]
            have hpZoom_lo : (zHitLo : ℝ) / wdScaleR ≤ pZoom := by
              rw [hpZoom_eq]
              exact (wdMem_sq (wdTrig_mem hphiZ_lo hphiZ_hi hphiZ_mem).2).1
            have hpZoom_le1 : pZoom ≤ 1 := by rw [hpZoom_eq]; exact Real.sin_sq_le_one _
            have h1_sub_pZoom :
                1 - pZoom ≤ (((wdScale : ℤ) - zHitLo : ℤ) : ℝ) / wdScaleR := by
              push_cast; rw [sub_div]
              have hdiv1 : (wdScale : ℝ) / wdScaleR = 1 := by
                unfold wdScaleR; exact div_self hB.ne'
              linarith
            set clickZoomRemHi := qZoomHi +
              wdDivCeil (((wdScale : ℤ) - zHitLo) * fr115) (wdScale : ℤ)
            have hclick_nn : 0 ≤ ((kZoom + 1 : ℕ) : ℝ) + (1 - pZoom) * fNext 1 := by
              have h1m_nn : 0 ≤ 1 - pZoom := by linarith
              positivity
            have hclick_rem :
                ((kZoom + 1 : ℕ) : ℝ) + (1 - pZoom) * fNext 1 ≤
                  (clickZoomRemHi : ℝ) * scale15 := by
              have h1m_nn : 0 ≤ 1 - pZoom := by linarith
              have hm := mul_le_mul h1_sub_pZoom hf1_hi hf1_nn (le_trans h1m_nn h1_sub_pZoom)
              have heq : ((((wdScale : ℤ) - zHitLo : ℤ) : ℝ) / wdScaleR) *
                  ((fr115 : ℝ) * scale15) =
                  (((((wdScale : ℤ) - zHitLo) * fr115 : ℤ) : ℝ) / wdScaleR) * scale15 := by
                push_cast; ring
              have hceil := le_wdDivCeil (a := ((wdScale : ℤ) - zHitLo) * fr115) hBZ
              have hmiss :
                  (1 - pZoom) * fNext 1 ≤
                    (wdDivCeil (((wdScale : ℤ) - zHitLo) * fr115) (wdScale : ℤ) : ℝ) * scale15 :=
                (hm.trans_eq heq).trans
                  (mul_le_mul_of_nonneg_right (by simpa [wdScaleR] using hceil) hs15_nn)
              dsimp only [clickZoomRemHi]; push_cast at hqZoom ⊢; linarith
            set collRemHi := wdDivCeil (z0Hi * fr215) (wdScale : ℤ) +
              wdDivCeil (z1Hi * clickZoomRemHi) (wdScale : ℤ)
            have hcoll0 :
                Complex.normSq zf.1 * fNext 2 ≤
                  (wdDivCeil (z0Hi * fr215) (wdScale : ℤ) : ℝ) * scale15 := by
              have hsq := normSq_le_wdCAbs2Hi (by dsimp only [zf, D, θ₂] at hzf0 ⊢; exact hzf0)
              have hm := mul_le_mul hsq hf2_hi hf2_nn
                (le_trans (Complex.normSq_nonneg _) hsq)
              have heq : ((z0Hi : ℝ) / wdScaleR) * ((fr215 : ℝ) * scale15) =
                  (((z0Hi * fr215 : ℤ) : ℝ) / wdScaleR) * scale15 := by push_cast; ring
              have hceil := le_wdDivCeil (a := z0Hi * fr215) hBZ
              exact (hm.trans_eq heq).trans
                (mul_le_mul_of_nonneg_right (by simpa [wdScaleR] using hceil) hs15_nn)
            have hcoll1 :
                Complex.normSq zf.2 * (((kZoom + 1 : ℕ) : ℝ) + (1 - pZoom) * fNext 1) ≤
                  (wdDivCeil (z1Hi * clickZoomRemHi) (wdScale : ℤ) : ℝ) * scale15 := by
              have hsq := normSq_le_wdCAbs2Hi (by dsimp only [zf, D, θ₂] at hzf1 ⊢; exact hzf1)
              have hm := mul_le_mul hsq hclick_rem hclick_nn
                (le_trans (Complex.normSq_nonneg _) hsq)
              have heq : ((z1Hi : ℝ) / wdScaleR) * ((clickZoomRemHi : ℝ) * scale15) =
                  (((z1Hi * clickZoomRemHi : ℤ) : ℝ) / wdScaleR) * scale15 := by push_cast; ring
              have hceil := le_wdDivCeil (a := z1Hi * clickZoomRemHi) hBZ
              exact (hm.trans_eq heq).trans
                (mul_le_mul_of_nonneg_right (by simpa [wdScaleR] using hceil) hs15_nn)
            set mPow : ℤ := ((m ^ 2 : ℕ) : ℤ)
            set descM : ℤ := ((m.descFactorial 2 : ℕ) : ℤ)
            have hmPow_pos : (0 : ℝ) < (mPow : ℝ) := by
              dsimp only [mPow]; exact_mod_cast pow_pos (by omega : 0 < m) 2
            have hpDist_eq : rotCfProb m 2 = (descM : ℝ) / (mPow : ℝ) := by
              unfold rotCfProb; dsimp only [descM, mPow]; push_cast; rfl
            have hdesc2_eq : m.descFactorial 2 + m = m ^ 2 := by
              rw [Nat.descFactorial_succ, Nat.descFactorial_one]
              zify [show 1 ≤ m by omega]; ring
            have hcoll_eq : 1 - rotCfProb m 2 = (m : ℝ) / (mPow : ℝ) := by
              rw [hpDist_eq]; dsimp only [descM, mPow]
              have hR : ((m.descFactorial 2 : ℕ) : ℝ) + (m : ℝ) = ((m ^ 2 : ℕ) : ℝ) := by
                exact_mod_cast hdesc2_eq
              field_simp [hmPow_pos.ne']
              push_cast at hR ⊢; linarith
            have hdesc_nn : (0 : ℝ) ≤ (descM : ℝ) / (mPow : ℝ) :=
              div_nonneg (by dsimp only [descM]; exact_mod_cast Nat.zero_le _) hmPow_pos.le
            have hm_div_nn : (0 : ℝ) ≤ (m : ℝ) / (mPow : ℝ) :=
              div_nonneg (Nat.cast_nonneg m) hmPow_pos.le
            set totalNum15 : ℤ := descM * (qDistHi + remDist0Hi + remDist1Hi) +
              (m : ℤ) * (qCollHi + collRemHi)
            set outHiZ : ℤ := wdDivCeil totalNum15 (mPow * 1000000)
            have hinj_le :
                ((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes (ghInitAmp2 θ₁ kInit) +
                  Complex.normSq (uf 0) * fNext 2 +
                  2 * Complex.normSq (uf 1) * (((kZoom + 1 : ℕ) : ℝ) + fNext 1) ≤
                ((qDistHi + remDist0Hi + remDist1Hi : ℤ) : ℝ) * scale15 := by
              push_cast at hqDist hrem1 ⊢; linarith [hqDist, hrem0, hrem1]
            have hcoll_le :
                (ghMaxQueries kInit probes : ℝ) +
                  Complex.normSq zf.1 * fNext 2 +
                  Complex.normSq zf.2 * (((kZoom + 1 : ℕ) : ℝ) + (1 - pZoom) * fNext 1) ≤
                ((qCollHi + collRemHi : ℤ) : ℝ) * scale15 := by
              dsimp only [collRemHi]; push_cast at hcoll1 ⊢; linarith [hqColl, hcoll0, hcoll1]
            have hcomb :
                rotCfProb m 2 *
                  (((kInit + 1 : ℕ) : ℝ) + ghChainExtraQueries2 θ₁ probes (ghInitAmp2 θ₁ kInit) +
                    Complex.normSq (uf 0) * fNext 2 +
                    2 * Complex.normSq (uf 1) * (((kZoom + 1 : ℕ) : ℝ) + fNext 1)) +
                  (1 - rotCfProb m 2) *
                    ((ghMaxQueries kInit probes : ℝ) +
                      Complex.normSq zf.1 * fNext 2 +
                      Complex.normSq zf.2 * (((kZoom + 1 : ℕ) : ℝ) + (1 - pZoom) * fNext 1)) ≤
                ((totalNum15 : ℝ) / (mPow : ℝ)) * scale15 := by
              rw [hcoll_eq, hpDist_eq]
              have ht1 := mul_le_mul_of_nonneg_left hinj_le hdesc_nn
              have ht2 := mul_le_mul_of_nonneg_left hcoll_le hm_div_nn
              have hsum_eq :
                  ((descM : ℝ) / (mPow : ℝ)) *
                    (((qDistHi + remDist0Hi + remDist1Hi : ℤ) : ℝ) * scale15) +
                    ((m : ℝ) / (mPow : ℝ)) * (((qCollHi + collRemHi : ℤ) : ℝ) * scale15) =
                  ((totalNum15 : ℝ) / (mPow : ℝ)) * scale15 := by
                dsimp only [totalNum15]; push_cast; field_simp [hmPow_pos.ne']
              linarith
            have hscale_conv : ((totalNum15 : ℝ) / (mPow : ℝ)) * scale15 =
                ((totalNum15 : ℝ) / ((mPow * 1000000 : ℤ) : ℝ)) * scale := by
              rw [hscale_eq]; push_cast; field_simp [hmPow_pos.ne']
            have hmPow6_pos : (0 : ℤ) < mPow * 1000000 := by
              have hmPow_posZ : (0 : ℤ) < mPow := by exact_mod_cast hmPow_pos
              omega
            have hceil := le_wdDivCeil (a := totalNum15) hmPow6_pos
            have hout_cast : (outHiZ.toNat : ℝ) = (outHiZ : ℝ) := by
              exact_mod_cast Int.toNat_of_nonneg hout_nn
            have hscale_nn : 0 ≤ scale := by rw [hscale_eq]; positivity
            rw [hout_cast]
            exact (hcomb.trans_eq hscale_conv).trans
              (mul_le_mul_of_nonneg_right hceil hscale_nn)
private lemma ghZoomMono_of_adj {k : ℕ} (v : List ℕ)
    (hadj : ∀ u < k, v.getD u 0 ≤ v.getD (u + 1) 0) :
    ∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ k → v.getD u₁ 0 ≤ v.getD u₂ 0 := by
  intro u₁ u₂ h12
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h12
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h2k
    rw [← Nat.add_assoc]
    exact Nat.le_trans (ih (Nat.le_add_right _ _) (by omega)) (hadj (u₁ + d) (by omega))
private lemma ghZoomMap_getD_of_lt {α β : Type*} (l : List α) (g : α → β) {idx : ℕ}
    (h : idx < l.length) (dα : α) (dβ : β) :
    (l.map g).getD idx dβ = g (l.getD idx dα) := by
  simp [List.getD_eq_getElem?_getD, h]
private lemma ghZoomMap_getLast?_of_succ {α β : Type*} (l : List α) (g : α → β) {W : ℕ}
    (hlen : l.length = W + 1) (dα : α) :
    (l.map g).getLast? = some (g (l.getD W dα)) := by
  have hlt : W < l.length := by omega
  rw [List.getLast?_eq_getElem?, List.length_map, hlen, Nat.add_sub_cancel]
  simp [List.getD_eq_getElem?_getD, hlt]
private lemma ghZoomMap_headD_of_succ {α β : Type*} (l : List α) (g : α → β) {W : ℕ}
    (hlen : l.length = W + 1) (dα : α) (dβ : β) :
    (l.map g).headD dβ = g (l.getD 0 dα) := by
  cases l with
  | nil => simp at hlen
  | cons _ _ => simp
/-- Stationary single-row pass spec `[none, none, some rowSpec]` for `k = 2`. -/
def ghK2PassSpec (rowSpec : GHZoomRowSpec) : GHZoomPassSpec :=
  [none, none, some rowSpec]
/-- Checks one `k = 2` stationary pass using pre-evaluated `GHZoomSummary`. -/
def checkGHZoomPassSummary (m : ℕ) (s : GHZoomSummary) (vCur vNext : List ℕ) : Bool :=
  (vCur.getD 0 0 == 0) &&
    Nat.ble (vCur.getD 0 0) (vCur.getD 1 0) &&
    Nat.ble (vCur.getD 1 0) (vCur.getD 2 0) &&
    Nat.ble (vNext.getD 1 0) (vCur.getD 1 0) &&
    match evalGHZoomStepFromSummary m s vNext with
    | some hi => Nat.ble hi (vCur.getD 2 0)
    | none => false
/-- Evaluates `evalGHZoomRowSummary` once and checks `W` Bellman passes for `(m, 2)`. -/
def checkGHZoomSchedule (m W : ℕ) (rowSpec : GHZoomRowSpec) (vSeq : List (List ℕ))
    (num den : ℕ) : Bool :=
  if hgm : 1 ≤ Stage2CertInternals.gridExp m ∧ Stage2CertInternals.gridExp m ≤ 10 then
    match evalGHZoomRowSummary m rowSpec with
    | none => false
    | some s =>
        let pIdx : Fin 10 := ⟨Stage2CertInternals.gridExp m - 1, by omega⟩
        let vLast := vSeq.getD W []
        let vTop := vSeq.getD 0 []
        decide (2 ≤ m ∧ 1 ≤ den ∧ W ≤ 16 ∧ vSeq.length = W + 1) &&
          (vLast.getD 0 0 == 0) &&
          (List.range 2).all (fun u ↦ Nat.ble (vLast.getD u 0) (vLast.getD (u + 1) 0)) &&
          (List.range 3).all (fun r ↦
            Nat.ble (Stage2CertInternals.potWInt pIdx r) (vLast.getD r 0)) &&
          (List.range W).all (fun i ↦
            checkGHZoomPassSummary m s (vSeq.getD i []) (vSeq.getD (i + 1) [])) &&
          Nat.ble (den * (vTop.getD 2 0 + 1))
            (num * Stage2CertInternals.treeSum (Stage2CertInternals.gridExp 2) 0
              (fun x ↦ Stage2CertInternals.invSqrtLo (x + 1)))
  else
    false
/-- Circuit wrapper instantiating `ghZoomRotCircuit` on `W` stationary `k = 2` passes. -/
noncomputable def ghZoomCertCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (W : ℕ) (rowSpec : GHZoomRowSpec) (hW : W ≤ 16) (n : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Stage1.qubits n m k)) Var
      (Stage1.qubits n m k) ((n + 1) * m) :=
  let p := Stage2CertInternals.gridExp m
  let passSpecs := List.replicate W (ghK2PassSpec rowSpec)
  ghZoomRotCircuit res hm_grid hk_grid hm2 hk2 (passSpecs.map (compileGHZoomPassSpec p))
    (by simpa [passSpecs] using hW) n
theorem ghZoomCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hn : 1 ≤ n) (hmk : Stage1.cells m k = true)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hk_eq : k = 2) (hkN : k ≤ 2 ^ n)
    (W : ℕ) (rowSpec : GHZoomRowSpec) (hW : W ≤ 16)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;; (ghZoomCertCircuit res (Stage1.cells_mem_grid hmk).1 (Stage1.cells_mem_grid hmk).2
      hm2 hk2 W rowSpec hW n).compile qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp fun σ ↦ decodeTargets n k (σ res) = S ⦄ :=
  ghZoomRotCircuit_correctness res hn hmk hm2 hk2 hk_eq hkN
    ((List.replicate W (ghK2PassSpec rowSpec)).map
      (compileGHZoomPassSpec (Stage2CertInternals.gridExp m)))
    (by simpa using hW) hS
theorem ghZoomCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hk_eq : k = 2)
    (W : ℕ) (rowSpec : GHZoomRowSpec) (hW : W ≤ 16)
    (vSeq : List (List ℕ)) (num den : ℕ)
    (hcert : checkGHZoomSchedule m W rowSpec vSeq num den = true) :
    let c_rel : ℚ≥0 := (num : ℚ≥0) / (den : ℚ≥0)
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦
          qset ;; (ghZoomCertCircuit res hm_grid hk_grid hm2 hk2 W rowSpec hW n).compile
            qAssign (groverParallelMarkingOracle m S))
        ((c_rel : ℝ) * vanillaFindAllCost n m k) := by
  subst hk_eq
  unfold checkGHZoomSchedule at hcert
  have hgm := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2
  rw [dite_eq_left ⟨hgm.1, hgm.2.1⟩] at hcert
  cases hsum : evalGHZoomRowSummary m rowSpec with
  | none => rw [hsum] at hcert; cases hcert
  | some s =>
    rw [hsum] at hcert
    dsimp only at hcert
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hcert
    rcases hcert with ⟨⟨⟨⟨⟨⟨_, hden, _, hvlen⟩, hvLast0⟩, hvLastAdj⟩, hvLastPot⟩,
      hpasses⟩, hratio⟩
    have extractRow {i r : ℕ} (hi : i < W) (hr : r ≤ 2) :
        ∃ outVal, evalGHZoomRowHi m r ((ghK2PassSpec rowSpec).getD r none)
            (vSeq.getD (i + 1) []) = some outVal ∧
          outVal ≤ (vSeq.getD i []).getD r 0 := by
      have hp := hpasses i hi
      unfold checkGHZoomPassSummary at hp
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hp
      rcases hp with ⟨⟨⟨⟨hv0, _⟩, _⟩, hv1⟩, hv2⟩
      match r, hr with
      | 0, _ => exact ⟨0, rfl, by omega⟩
      | 1, _ => exact ⟨(vSeq.getD (i + 1) []).getD 1 0, rfl, hv1⟩
      | 2, _ =>
        cases hev : evalGHZoomStepFromSummary m s (vSeq.getD (i + 1) []) with
        | none => rw [hev] at hv2; cases hv2
        | some outVal =>
          rw [hev] at hv2
          refine ⟨outVal, ?_, Nat.ble_eq.mp hv2⟩
          simpa [evalGHZoomRowHi, ghK2PassSpec, hsum] using hev
      | _ + 3, hr => omega
    set p := Stage2CertInternals.gridExp m
    set passSpecs := List.replicate W (ghK2PassSpec rowSpec)
    refine ghZoomRotCircuit_relCost_of_drift res hm_grid hk_grid hm2 hk2 rfl
      (passSpecs.map (compileGHZoomPassSpec p)) (by simpa [passSpecs] using hW)
      12 (by norm_num) ?_ (fun r ↦ (vSeq.getD 0 []).getD r 0) num den hden ?_ hratio
    · intro subN hsub pf hpf r hr kInit probes kZoom hcomp
      obtain ⟨ps, hps_mem, rfl⟩ := List.mem_map.mp hpf
      obtain ⟨i, hi, hps_eq⟩ := List.getElem_of_mem hps_mem
      have hiW : i < W := by simpa [passSpecs] using hi
      have hps_k2 : ps = ghK2PassSpec rowSpec := by
        simpa [passSpecs] using hps_eq.symm
      subst hps_k2
      obtain ⟨outVal, hev, _⟩ := extractRow hiW hr
      exact evalGHZoomRowHi_qBound hev hsub hcomp
    · intro subN hsub
      set scale : ℝ := ((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ)
      have hscale_nn : 0 ≤ scale :=
        div_nonneg (by positivity [Real.pi_pos]) (Nat.cast_nonneg _)
      let fOf (v : List ℕ) (r : ℕ) : ℝ := (v.getD r 0 : ℝ) * scale
      let fFinal := fOf (vSeq.getD W [])
      refine ⟨fFinal, ?_, ?_, ?_, ?_⟩
      · intro r hr
        refine ⟨by dsimp only [fFinal, fOf]; positivity, ?_⟩
        have hle := hvLastPot r (Nat.lt_succ_of_le hr)
        dsimp only [fFinal, fOf]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hscale_nn
      · dsimp only [fFinal, fOf]; rw [hvLast0]; simp
      · intro u₁ u₂ h12 h2k
        have hmono := ghZoomMono_of_adj (vSeq.getD W []) hvLastAdj u₁ u₂ h12 h2k
        dsimp only [fFinal, fOf]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmono) hscale_nn
      · refine ⟨vSeq.map fOf, by simp [passSpecs, hvlen],
          ghZoomMap_getLast?_of_succ vSeq fOf hvlen [], ?_, ?_⟩
        · intro i hi
          have hiW : i < W := by simpa [passSpecs] using hi
          have hi_lt : i < vSeq.length := by omega
          have hi1_lt : i + 1 < vSeq.length := by omega
          have hfNext_eq : (vSeq.map fOf).getD (i + 1) fFinal = fOf (vSeq.getD (i + 1) []) :=
            ghZoomMap_getD_of_lt vSeq fOf hi1_lt [] fFinal
          have hfCur_eq : (vSeq.map fOf).getD i fFinal = fOf (vSeq.getD i []) :=
            ghZoomMap_getD_of_lt vSeq fOf hi_lt [] fFinal
          dsimp only
          rw [hfNext_eq, hfCur_eq]
          have hp := hpasses i hiW
          unfold checkGHZoomPassSummary at hp
          simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hp
          rcases hp with ⟨⟨⟨⟨hvCur0, hvAdj01⟩, hvAdj12⟩, _⟩, _⟩
          have hvCurAdj : ∀ u < 2, (vSeq.getD i []).getD u 0 ≤ (vSeq.getD i []).getD (u + 1) 0 := by
            intro u hu
            match u, hu with
            | 0, _ => exact hvAdj01
            | 1, _ => exact hvAdj12
            | _ + 2, hu => omega
          refine ⟨?_, ?_, ?_⟩
          · dsimp only [fOf]; rw [hvCur0]; simp
          · intro u₁ u₂ h12 h2k
            have hmono := ghZoomMono_of_adj (vSeq.getD i []) hvCurAdj u₁ u₂ h12 h2k
            dsimp only [fOf]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmono) hscale_nn
          · intro r hr
            obtain ⟨outVal, hev, hout_le⟩ := extractRow hiW hr
            have hps_eq : (passSpecs.map (compileGHZoomPassSpec p))[i] =
                compileGHZoomPassSpec p (ghK2PassSpec rowSpec) := by
              simp [passSpecs]
            rw [hps_eq]
            have hsound := evalGHZoomRowHi_sound hev hsub (fNext := fOf (vSeq.getD (i + 1) []))
              (fun u _ ↦ ⟨by dsimp only [fOf]; positivity, le_rfl⟩)
            exact hsound.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hout_le) hscale_nn)
        · rw [ghZoomMap_headD_of_succ vSeq fOf hvlen [] fFinal]
end
end QuantumComputation.Specs.DickeSol
end GHZoom_EvalAndSoundness
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs
open QuantumComputation.Specs.DickeSol
/-- Bundled `r = 2` Gaussian-Hamming Zoom cell certificate `(W, rowSpec, vSeq, num, den)`. -/
structure GHZoomCellCert where
  W : ℕ
  rowSpec : GHZoomRowSpec
  vSeq : List (List ℕ)
  num : ℕ
  den : ℕ
/-- Exported helper `ghZoomRow4`. -/
def ghZoomRow4 : GHZoomRowSpec :=
  { a0Num := 1098959, a0Den := 1000000, bNum := 1344124, bDen := 1000000, probes :=
    [ ⟨58507, 1000000, 3726723, 1705036, 4098245,
      4133080, 12198, 4133098, 4108720, 12162, 4108738⟩
    , ⟨56590, 1000000, 1769976, 696470, 1902074,
      28268464, 478530, 28272514, 26100032, 439374, 26103730⟩
    , ⟨54086, 1000000, 64563744, 25520830, 69424706,
      66657040, -3381138, 66742738, 21580448, -1105986, 21608770⟩
    , ⟨55476, 1000000, 20375037, 7694516, 21779525,
      1696909, -78180, 1698709, 14946293, -665124, 14961085⟩
    , ⟨43295, 1000000, 4887935, 2025888, 5291137,
      -12418941, 1965460, 12573509, -62033925, 9892052, 62817677⟩
    , ⟨50700, 1000000, 32091975, 13740712, 34909913,
      55077923, 18058236, 57962725, 263511, 86320, 277289⟩
    , ⟨79430, 1000000, 20614675, 10703052, 23227573,
      1078000, -81042, 1081042, 10606681, -782160, 10635481⟩ ] }
/-- Exported helper `ghZoomVSeq4`. -/
def ghZoomVSeq4 : List (List ℕ) :=
  [ [0, 818310000, 1056797878]
  , [0, 818310000, 1056797878]
  , [0, 818310000, 1056797878]
  , [0, 818310000, 1056797878]
  , [0, 818310000, 1056797881]
  , [0, 818310000, 1056798119]
  , [0, 818310000, 1056816956]
  , [0, 818310000, 1058312956]
  , [0, 818310000, 1177121919] ]
/-- Exported helper `ghZoomCert4k2`. -/
def ghZoomCert4k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 1064044129, a0Den := 1000000000, bNum := 1344204010, bDen := 1000000000, probes :=
      [⟨3683992,1000000000,248437388,34791165,250861637,123103740,15691,123103741,99249960,14089,
      99249961⟩,⟨3656494,1000000000,16191207,297776,16193945,399160437,79916,399160445,76387599,
      17480,76387601⟩,⟨8386785,1000000000,120971448,17513185,122232577,284900637,-67516,284900645,
      368947255,-115248,368947273⟩,⟨7064150,1000000000,17051892,2464955,17229133,1,0,1,1,0,1⟩,
      ⟨3926643,1000000000,125066712,18156265,126377737,248503695,-31528,248503697,105662184,-14537,
      105662185⟩,⟨3934760,1000000000,480753329,8770800,480833329,536848899,-46340,536848901,1,0,1⟩,
      ⟨3792087,1000000000,266661291,37552780,269292509,1,0,1,1,0,1⟩,⟨3792277,1000000000,257373100,
      4787379,257417621,74188376,36543,74188385,15163235,7788,15163237⟩,⟨3693786,1000000000,
      116712284,16680213,117898205,37109112,-8615,37109113,220647020,-63021,220647029⟩,⟨3705519,
      1000000000,223512801,4186280,223552001,64331824,-11343,64331825,343694517,-74156,343694525⟩,
      ⟨3689450,1000000000,327099159,44776160,330149609,32829304,-8103,32829305,281199357,-67076,
      281199365⟩,⟨3678403,1000000000,7859928,146705,7861297,202236825,-113768,202236857,108326455,
      -62448,108326473⟩,⟨3748097,1000000000,506854491,72088580,511955309,124646236,110523,
      124646285,72131033,67944,72131065⟩,⟨3742934,1000000000,45114245,832908,45121933,224147960,
      63519,224147969,182729840,57351,182729849⟩,⟨8002635,1000000000,382650895,55188168,386610193,
      231648351,-213080,231648449,280261017,-267856,280261145⟩,⟨7831305,1000000000,221032300,
      32275011,223376261,201185807,198576,201185905,83812380,90629,83812429⟩,⟨7968169,1000000000,
      372988105,53906592,376863433,393308215,-118992,393308233,127622205,-45188,127622213⟩,
      ⟨7781459,1000000000,204238641,29804320,206401841,5641440,-3359,5641441,171007913,-104616,
      171007945⟩,⟨7927122,1000000000,213047380,31190379,215318429,256035796,158403,256035845,
      462077967,300944,462078065⟩,⟨8026262,1000000000,239150044,34622733,241643285,40819317,-25556,
      40819325,8892323,-5964,8892325⟩,⟨7705090,1000000000,167771033,24519456,169553305,498852221,
      89340,498852229,117121512,15305,117121513⟩,⟨8196049,1000000000,301309095,43892888,304489337,
      107122499,20700,107122501,231283263,30416,231283265⟩,⟨3891472,1000000000,290318007,42470824,
      293408105,60403983,15544,60403985,72249999,17000,72250001⟩,⟨3898758,1000000000,325595129,
      5918760,325648921,1,0,1,1,0,1⟩,⟨4138423,1000000000,291828303,42511696,294908465,39010944,
      -8833,39010945,444661565,-84348,444661573⟩,⟨4136556,1000000000,176085864,3171623,176114425,1,
      0,1,484880399,44040,484880401⟩,⟨4022051,1000000000,10274392,1495305,10382633,182385896,57297,
      182385905,152024480,52311,152024489⟩,⟨4019821,1000000000,497204597,9008796,497286205,
      134699235,23212,134699237,345476565,74348,345476573⟩,⟨8253381,1000000000,295780511,43282440,
      298930561,439657023,-41936,439657025,345142083,-37156,345142085⟩,⟨8101660,1000000000,
      48714955,7095972,49229053,36881325,-24292,36881333,322741189,-215580,322741261⟩,⟨8148784,
      1000000000,238890683,35304444,241485325,514200927,-317464,514201025,3979020,-2821,3979021⟩,
      ⟨4067634,1000000000,2768160,398671,2796721,835924,1293,835925,170589621,261220,170589821⟩,
      ⟨4056397,1000000000,199244304,3613303,199277065,52152672,51065,52152697,33062491,34500,
      33062509⟩,⟨8512221,1000000000,336099643,49300524,339696205,181127504,-171297,181127585,
      216632072,-187335,216632153⟩,⟨8108385,1000000000,58322360,8544081,58944881,189034901,-274980,
      189035101,258212617,-385656,258212905⟩,⟨8563120,1000000000,440105781,64703660,444836669,
      260946952,-251295,260947073,44076648,-46945,44076673⟩,⟨7701452,1000000000,54467,7956,55045,
      336612309,366940,336612509,489825255,575432,489825593⟩,⟨8919072,1000000000,6927457,1013376,
      7001185,138428160,16639,138428161,140185599,23680,140185601⟩,⟨4157598,1000000000,155705760,
      22593961,157336489,502521633,717344,502522145,196756629,280540,196756829⟩,⟨4161433,
      1000000000,52578188,953715,52586837,5148840,3209,5148841,254409112,112785,254409137⟩,
      ⟨4160696,1000000000,262192249,38184720,264958201,165238008,-90895,165238033,349390839,
      -186920,349390889⟩,⟨4135514,1000000000,50989785,914048,50997977,161315365,-152412,161315437,
      71126640,-83489,71126689⟩,⟨5591562,1000000000,10229648,1482945,10336577,11717628,-24205,
      11717653,113175928,-195585,113176097⟩,⟨6200498,1000000000,9012069,805340,9047981,28504917,
      21356,28504925,276290835,232708,276290933⟩,⟨4839329,1000000000,223381628,32104365,225676853,
      508585815,-3743632,508599593,202867560,-1470439,202872889⟩,⟨4850082,1000000000,203203936,
      12444273,203584625,266959880,2703519,266973569,167077251,1680380,167085701⟩,⟨85204,
      1000000000,480594015,28380008,481431233,372412613,152503884,402428365,17505045,7151492,
      18909533⟩,⟨24,1000000000,500368141,23359500,500913109,97457360,39854961,105291761,25566765,
      10672948,27705077⟩,⟨30,1000000000,86046017,4305456,86153665,77037975,31901272,83381897,
      3026016,1236937,3269065⟩,⟨1255,1000000000,431036295,21723328,431583353,389155115,158811492,
      420312733,228178797,92467604,246202805⟩,⟨11,1000000000,388174281,20497360,388715081,
      470800335,191195608,508142417,228498700,94602981,247308269⟩,⟨7,1000000000,9479511,511280,
      9493289,225308059,94230300,244219309,7797104,3177303,8419625⟩,⟨123825,1000000000,129207225,
      6913568,129392057,14564012,6030165,15763037,437341875,182679068,473961557⟩,⟨4714817,
      1000000000,63945,4048,64073,196275404,79822053,211885805,154280460,62670589,166523461⟩,
      ⟨2948840,1000000000,313479987,19591684,314091605,26637700,-7299,26637701,185031024,-211607,
      185031145⟩,⟨7742995,1000000000,348438219,57725860,353187581,47920136,1498023,47943545,
      290693975,9446808,290847433⟩,⟨7254701,1000000000,170033481,28472960,172400969,122226612,
      -15635,122226613,313679517,-70844,313679525⟩,⟨7479236,1000000000,53714101,9090780,54477949,
      35235735,-225568,35236457,100339265,-641088,100341313⟩,⟨7546103,1000000000,138163535,
      23379672,140127697,100861845,-40172,100861853,228231588,-149555,228231637⟩,⟨3725445,
      1000000000,512300169,87043880,519642281,28804673,42936,28804705,85033780,143451,85033901⟩,
      ⟨3746956,1000000000,47937551,900120,47946001,16982577,65936,16982705,15912057,63824,
      15912185⟩,⟨3726644,1000000000,24398876,4016157,24727205,142450236,-219427,142450405,7733957,
      -11124,7733965⟩,⟨3709219,1000000000,39409803,740804,39416765,155800315,-74892,155800333,
      219780609,-118600,219780641⟩,⟨7578163,1000000000,63715211,10685340,64604989,138249723,
      -681964,138251405,436723595,-2215188,436729213⟩,⟨8061168,1000000000,143521847,24697296,
      145631305,410345025,-1296448,410347073,386160777,-1257664,386162825⟩,⟨7711948,1000000000,
      316415227,54740364,321115405,489559587,-752284,489560165,123143309,-221940,123143509⟩,
      ⟨8369733,1000000000,499104529,86104320,506477329,239382255,711712,239383313,337382583,
      1065344,337384265⟩,⟨7931605,1000000000,133882995,23251228,135886997,575664,1073,575665,
      414814289,814680,414815089⟩,⟨8525191,1000000000,451976799,78915320,458814401,17269564,5877,
      17269565,248310608,66855,248310617⟩,⟨7843374,1000000000,148529788,26038005,150794813,
      98346873,-79336,98346905,31545620,-23829,31545629⟩,⟨8608023,1000000000,54715889,9563400,
      55545361,63675588,78995,63675637,439698817,503256,439699105⟩,⟨8158582,1000000000,371223271,
      64866360,376847929,73265368,205785,73265657,382984059,1135060,382985741⟩,⟨4287491,1000000000,
      241929341,43034940,245727109,257441961,-256720,257442089,144023965,-144012,144024037⟩,
      ⟨4311903,1000000000,425520297,7756504,425590985,513384523,-951636,513385405,220670829,
      -415940,220671221⟩,⟨4060784,1000000000,163197660,27722299,165535501,5769603,-4804,5769605,
      441041937,-336016,441042065⟩,⟨4024466,1000000000,91385679,1701680,91401521,461691165,85948,
      461691173,536848899,46340,536848901⟩,⟨5111467,1000000000,33881955,5806948,34375973,70745512,
      -11895,70745513,67593564,11627,67593565⟩,⟨4245366,1000000000,50849055,3867712,50995937,
      401561421,-400780,401561621,420618825,-656288,420619337⟩,⟨4607550,1000000000,132900560,
      21640311,134650889,410224467,283556,410224565,64047993,64024,64048025⟩,⟨4672776,1000000000,
      42862204,3623397,43015085,419512323,40964,419512325,22384740,-6691,22384741⟩,⟨5584277,
      1000000000,126982189,20484660,128623861,97175740,13941,97175741,276689955,33268,276689957⟩,
      ⟨1786256,1000000000,85423995,8532188,85849037,86248353,-74296,86248385,11476840,-4791,
      11476841⟩,⟨1543314,1000000000,15376024,726657,15393185,12236003,-6996,12236005,107910535,
      -62328,107910553⟩,⟨4004712,1000000000,434739783,39615056,436540985,53875599,-14680,53875601,
      369139365,-76852,369139373⟩]},
    [[0,818310000,1056718414],[0,818310000,1056718414],[0,818310000,1056718414],
    [0,818310000,1056718414],[0,818310000,1056718414],[0,818310000,1056718414],
    [0,818310000,1056718414],[0,818310000,1056718414],[0,818310000,1056718414],
    [0,818310000,1056718414],[0,818310000,1056718414],[0,818310000,1056718414],
    [0,818310000,1056718417],[0,818310000,1056718651],[0,818310000,1056737309],
    [0,818310000,1058226697],[0,818310000,1177121919]],1056718415,1707106781⟩
/-- Exported helper `ghZoomRow8`. -/
def ghZoomRow8 : GHZoomRowSpec :=
  { a0Num := 10446199, a0Den := 10000000, bNum := 14093544, bDen := 10000000, probes :=
    [ ⟨1116215, 10000000, 7810093, 5634324, 9630325,
      53069704, -568230, 53072746, 10962360, -125818, 10963082⟩
    , ⟨1038019, 10000000, 43377480, 29928058, 52700042,
      38101029, -864220, 38110829, 25167789, -501700, 25172789⟩
    , ⟨879524, 10000000, 13551679, 8962920, 16247521,
      34470183, -1186144, 34490585, 199760, -6258, 199858⟩
    , ⟨875400, 10000000, 20636845, 12427812, 24090037,
      67108863, 16384, 67108865, 7425609, 21800, 7425641⟩
    , ⟨632117, 10000000, 58844880, 33897938, 67910162,
      -5266865, 2211792, 5712433, -39395783, 16545456, 42729145⟩
    , ⟨1135039, 10000000, 1824344, 1172790, 2168794,
      17070872, 6759654, 18360490, 63442175, 24936288, 68166913⟩
    , ⟨1104884, 10000000, 32212040, 23232378, 39715978,
      13499643, 3098924, 13850765, 42499267, 10282356, 43725445⟩ ] }
/-- Exported helper `ghZoomVSeq8`. -/
def ghZoomVSeq8 : List (List ℕ) :=
  [ [0, 818310000, 965107807]
  , [0, 818310000, 965107807]
  , [0, 818310000, 965107807]
  , [0, 818310000, 965107807]
  , [0, 818310000, 965107807]
  , [0, 818310000, 965107848]
  , [0, 818310000, 965114430]
  , [0, 818310000, 966178273]
  , [0, 818310000, 1138140398] ]
/-- Exported helper `ghZoomCert8k2`. -/
def ghZoomCert8k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 989205597, a0Den := 1000000000, bNum := 1409551300, bDen := 1000000000, probes :=
      [⟨11038875,1000000000,94352076,18035293,96060325,96530621,-39300,96530629,170293508,-55365,
      170293517⟩,⟨10302892,1000000000,105821331,20357980,107761781,276789733,199644,276789805,
      208059576,142793,208059625⟩,⟨10565316,1000000000,70200207,13347776,71457905,99588384,14113,
      99588385,26725360,7311,26725361⟩,⟨10496189,1000000000,66992976,12989593,68240665,428034657,
      -331024,428034785,511347573,-633164,511347965⟩,⟨10540290,1000000000,282796825,53510688,
      287814937,99362692,70485,99362717,56679292,53235,56679317⟩,⟨10770359,1000000000,52776965,
      10306188,53773837,481012399,-657960,481012849,1339884,-1637,1339885⟩,⟨10449316,1000000000,
      516564747,100332596,526218365,251920383,31744,251920385,274366095,-33128,274366097⟩,
      ⟨10127837,1000000000,320217421,61043100,325983829,195691925,391692,195692317,436182649,
      1002480,436183801⟩,⟨10234305,1000000000,171396285,32772292,174501317,137475481,-281400,
      137475769,376669935,-892768,376670993⟩,⟨10386230,1000000000,518157219,101039660,527916581,
      313218979,530940,313219429,53421445,87708,53421517⟩,⟨10563250,1000000000,124970008,24574095,
      127363217,167756244,-18317,167756245,185146520,57729,185146529⟩,⟨10058199,1000000000,
      125204840,24468561,127573361,29757021,21820,29757029,134304905,92712,134304937⟩,⟨10423110,
      1000000000,107321585,20647488,109289713,223259268,-528275,223259893,206151875,-488172,
      206152453⟩,⟨10656899,1000000000,493518141,96873140,502935941,345699505,446232,345699793,
      119596047,153104,119596145⟩,⟨10221867,1000000000,446415571,88019580,455010229,52173052,
      -112365,52173173,253732384,-698337,253733345⟩,⟨10346317,1000000000,90983232,18041705,
      92754793,117461955,368492,117462533,89605620,307901,89606149⟩,⟨5679417,1000000000,153659748,
      30350645,156628477,84953073,-73736,84953105,92891019,-96380,92891069⟩,⟨5215194,1000000000,
      231544208,5487855,231609233,153091029,-247460,153091229,517107311,-773160,517107889⟩,
      ⟨5455204,1000000000,52317077,10496436,53359645,223555472,190305,223555553,449948863,381816,
      449949025⟩,⟨6107758,1000000000,6090185,375288,6101737,453051209,170280,453051241,18550136,
      18273,18550145⟩,⟨5566000,1000000000,253817900,50054829,258706421,253382699,-159180,253382749,
      85082151,-92240,85082201⟩,⟨6198030,1000000000,28344529,1917720,28409329,159592685,50532,
      159592693,157653127,75336,157653145⟩,⟨5584067,1000000000,235398372,47076995,240059653,
      471410719,651360,471411169,467553985,518952,467554273⟩,⟨5872415,1000000000,189638520,
      10852031,189948769,264842995,292932,264843157,6953765,10548,6953773⟩,⟨5553798,1000000000,
      250168680,50559769,255226681,124634895,22328,124634897,244640877,-62564,244640885⟩,⟨5317966,
      1000000000,298964905,9960768,299130793,319228789,-1072020,319230589,173896485,-580228,
      173897453⟩,⟨5972871,1000000000,310627895,62239968,316801993,354267635,-263508,354267733,
      18671037,-17284,18671045⟩,⟨5921295,1000000000,232734493,14469324,233183845,155849332,-335445,
      155849693,510895125,-994532,510896093⟩,⟨5500958,1000000000,514608955,105208428,525253453,
      25941424,136857,25941785,5373075,32452,5373173⟩,⟨6087958,1000000000,384416315,21222348,
      385001677,95648280,13831,95648281,11814660,-4861,11814661⟩,⟨5283543,1000000000,222426117,
      44907044,226914125,315595189,-213180,315595261,205893785,-114792,205893817⟩,⟨5751368,
      1000000000,42815891,2422020,42884341,372874251,1660660,372877949,2417788,10995,2417813⟩,
      ⟨4813578,1000000000,109169800,21483609,111263609,24269484,-76637,24269605,182576396,-630597,
      182577485⟩,⟨6413362,1000000000,361398829,15744420,361741621,153667500,-543461,153668461,
      190260764,-760773,190262285⟩,⟨11122347,1000000000,17944803,3670396,18316325,520980609,182600,
      520980641,139695552,183865,139695673⟩,⟨10982276,1000000000,237911520,49318321,242969521,
      37295413,-73284,37295485,89529323,-208164,89529565⟩,⟨11143369,1000000000,19164497,3978504,
      19573105,536848899,-46340,536848901,1,0,1⟩,⟨11226540,1000000000,65259948,13517845,66645277,
      370062153,153896,370062185,476330609,174600,476330641⟩,⟨11218949,1000000000,35801631,7520000,
      36582881,257482680,1883519,257489569,263692168,1906095,263699057⟩,⟨11069102,1000000000,
      116082897,24001496,118538225,6128500,3501,6128501,26173455,10232,26173457⟩,⟨11617683,
      1000000000,3190647,671704,3260585,217472713,1061784,217475305,118330259,543900,118331509⟩,
      ⟨11368690,1000000000,28665325,6007428,29288053,22848111,-162520,22848689,144991680,-1004711,
      144995161⟩,⟨11345569,1000000000,21276996,4479797,21743485,253999648,-1915815,254006873,
      195008980,-1402179,195014021⟩,⟨11337881,1000000000,220153515,46156292,224939933,274763415,
      -629888,274764137,190853969,-442080,190854481⟩,⟨12072930,1000000000,239423304,50584897,
      244708705,364004397,-2365796,364012085,171005993,-1150776,171009865⟩,⟨11288560,1000000000,
      12360801,2601760,12631649,370638543,1193624,370640465,33837389,116340,33837589⟩,⟨11143812,
      1000000000,25220916,5305763,25772965,507532125,6938932,507579557,274718081,3712800,
      274743169⟩,⟨11159353,1000000000,9368073,1944664,9567785,23597355,514948,23602973,85367399,
      1866480,85387801⟩,⟨10659108,1000000000,245932032,50854895,251134993,80387475,735212,80390837,
      484034001,4400200,484054001⟩,⟨12208459,1000000000,34173351,6992440,34881401,535891171,
      -8195100,535953829,223997633,-3472344,224024545⟩,⟨2100723,1000000000,83567008,14311425,
      84783617,-7099671,-171736840,171883529,-18554525,-449058732,449441893⟩,⟨8615255,1000000000,
      98652168,13869785,99622393,-21290085,-524826188,525257837,-464921,-11481720,11491129⟩,
      ⟨9259987,1000000000,219048720,41352241,222917809,51940065,-403592,51941633,119519520,-912199,
      119523001⟩,⟨9995325,1000000000,1654000,316071,1683929,456968005,13083948,457155277,243383128,
      6906345,243481097⟩,⟨9376056,1000000000,308153333,60177444,313974205,299099003,12074004,
      299342605,275678205,11226332,275906693⟩,⟨10929645,1000000000,198530739,39217660,202367189,
      406232825,10804152,406376473,42303480,1113079,42318121⟩,⟨9182053,1000000000,2034564,403373,
      2074165,14628028,-189315,14629253,2486829,-31540,2487029⟩,⟨10590205,1000000000,121433220,
      23942611,123771061,272493615,-4721288,272534513,525881685,-9264932,525963293⟩,⟨10143764,
      1000000000,331061055,65858968,337548257,19123125,17492,19123133,473845655,565968,473845993⟩,
      ⟨10279596,1000000000,258852924,52113893,264046765,524269693,2472876,524275525,724197,3404,
      724205⟩,⟨10719251,1000000000,233713560,46778231,238348969,161334660,-125741,161334709,
      22401285,-18932,22401293⟩,⟨9833778,1000000000,128159229,25712020,130713029,366875667,268156,
      366875765,408080365,242412,408080437⟩,⟨10524690,1000000000,213655724,43444707,218028005,
      64657677,-32164,64657685,70392099,-16780,70392101⟩,⟨11213372,1000000000,3506955,703868,
      3576893,215094060,-642971,215095021,53447316,-175763,53447605⟩,⟨10431950,1000000000,66945180,
      13478011,68288461,512380215,4119752,512396777,157226680,1365441,157232609⟩,⟨11400844,
      1000000000,278728499,57226620,284542549,423083757,-82276,423083765,179721828,-94795,
      179721853⟩,⟨10417267,1000000000,407991549,84225140,416594501,152446293,-1135924,152450525,
      294873359,-2232360,294881809⟩,⟨5652035,1000000000,154259968,31478865,157439057,296184099,
      -34420,296184101,58982399,-15360,58982401⟩,⟨5908922,1000000000,83649423,3494536,83722385,
      10394167,-19344,10394185,52301743,-130176,52301905⟩,⟨11272425,1000000000,387326989,79527660,
      395407189,37645160,26031,37645169,87011535,130592,87011633⟩,⟨4474514,1000000000,98745371,
      20519460,100854829,177453900,-207229,177454021,511980453,-1176604,511981805⟩,⟨7758474,
      1000000000,2009763,87916,2011685,108304625,666048,108306673,347444559,2646880,347454641⟩,
      ⟨11385340,1000000000,255468065,53869992,261086017,515697237,1725884,515700125,333098217,
      1022056,333099785⟩,⟨6078877,1000000000,57836609,12235200,59116609,505169735,-1303608,
      505171417,390259349,-1027260,390260701⟩,⟨6922662,1000000000,132528,6695,132697,172633285,
      -157668,172633357,217966208,-313185,217966433⟩,⟨11592389,1000000000,248438388,52832155,
      253993837,68526840,-152191,68527009,185801252,-289155,185801477⟩,⟨6478833,1000000000,
      494940383,103832256,505714465,3279717,7244,3279725,178569625,320712,178569913⟩,⟨6681190,
      1000000000,312229723,18774036,312793645,451307247,-722296,451307825,14124608,-15945,
      14124617⟩,⟨6679946,1000000000,258645141,54657980,264357341,99531928,70545,99531953,1,0,1⟩,
      ⟨5976669,1000000000,139982380,6745011,140144789,117243872,229695,117244097,58583595,168388,
      58583837⟩,⟨6371288,1000000000,19580,4179,20021,229764435,-697268,229765493,317337755,
      -1033212,317339437⟩,⟨6446585,1000000000,163135,7272,163297,121396299,110180,121396349,
      449524779,212020,449524829⟩,⟨7146456,1000000000,4116312,868385,4206913,491996661,443620,
      491996861,73650715,51492,73650733⟩,⟨6013289,1000000000,439303795,21762708,439842517,
      304293111,-174440,304293161,153759991,-74400,153760009⟩]},
    [[0,818310000,964679690],[0,818310000,964679690],[0,818310000,964679690],
    [0,818310000,964679690],[0,818310000,964679690],[0,818310000,964679690],
    [0,818310000,964679690],[0,818310000,964679690],[0,818310000,964679690],
    [0,818310000,964679690],[0,818310000,964679690],[0,818310000,964679690],
    [0,818310000,964679690],[0,818310000,964679728],[0,818310000,964685974],
    [0,818310000,965723742],[0,818310000,1138140398]],964679691,1707106781⟩
/-- Exported helper `ghZoomRow16`. -/
def ghZoomRow16 : GHZoomRowSpec :=
  { a0Num := 10320829, a0Den := 10000000, bNum := 14535030, bDen := 10000000, probes :=
    [ ⟨1220838, 10000000, 46383072, 37956946, 59934290,
      29889999, -1038920, 29908049, 3403001, -118080, 3405049⟩
    , ⟨1164164, 10000000, 18459864, 14619770, 23547914,
      17207312, -688734, 17221090, 54375249, -1829000, 54406001⟩
    , ⟨879785, 10000000, 22788961, 17681880, 28844161,
      9073079, 3298680, 9654121, 59286640, 21638418, 63112018⟩
    , ⟨815780, 10000000, 25997091, 16554980, 30820709,
      35228056, 13592250, 37759306, 33432685, 12632388, 35739637⟩
    , ⟨138613, 10000000, 7818045, 4391852, 8967173,
      -24222285, 11285092, 26722133, -30884391, 14659280, 34186841⟩
    , ⟨436276, 10000000, 59991843, 18826876, 62876645,
      7280244, 21519133, 22717285, 3253620, 9753029, 10281421⟩
    , ⟨806105, 10000000, 16866285, 9190508, 19207733,
      3506564, 9821523, 10428725, 2005770, 5610136, 5957914⟩
    , ⟨1022002, 10000000, 15253147, 10638804, 18596845,
      -50825225, -49502232, 70948393, -21739440, -21107938, 30300962⟩
    , ⟨1135672, 10000000, 392935, 290832, 488857,
      11863378, -13555680, 18013778, 20136584, -23682513, 31086065⟩
    , ⟨1332299, 10000000, 41109217, 31212456, 51615745,
      29305743, 22968176, 37233905, 51352952, 39930186, 65050330⟩ ] }
/-- Exported helper `ghZoomVSeq16`. -/
def ghZoomVSeq16 : List (List ℕ) :=
  [ [0, 818310000, 919805476]
  , [0, 818310000, 919805476]
  , [0, 818310000, 919805476]
  , [0, 818310000, 919805476]
  , [0, 818310000, 919805476]
  , [0, 818310000, 919805481]
  , [0, 818310000, 919807420]
  , [0, 818310000, 920448444]
  , [0, 818310000, 1132394210] ]
/-- Exported helper `ghZoomCert16k2`. -/
def ghZoomCert16k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 971677348, a0Den := 1000000000, bNum := 1453992481, bDen := 1000000000, probes :=
      [⟨15016870,1000000000,93894885,22284988,96503213,13030512,-5105,13030513,409455221,-80940,
      409455229⟩,⟨14111559,1000000000,12155725,2907108,12498517,33454607,-80976,33454705,89632480,
      -254391,89632841⟩,⟨14093194,1000000000,228498124,51867843,234311045,162357939,637100,
      162359189,276555811,1097580,276557989⟩,⟨14355940,1000000000,481925589,118989460,496397789,
      164121705,-102488,164121737,144279060,-118909,144279109⟩,⟨10362813,1000000000,408811125,
      92700932,419189693,14617800,-37849,14617849,305060531,-873300,305061781⟩,⟨11554617,
      1000000000,218865980,41038389,222680189,48901793,223776,48902305,419509515,2171092,
      419515133⟩,⟨16008924,1000000000,86821163,19900116,89072605,428324391,206960,428324441,
      497022355,401292,497022517⟩,⟨15283961,1000000000,374069833,102112944,387756745,14017415,
      -82368,14017657,266731823,-1600536,266736625⟩,⟨14283531,1000000000,38864905,9189528,39936553,
      289067883,374044,289068125,258167184,431737,258167545⟩,⟨14666308,1000000000,9481904,2329497,
      9763865,315984151,1599840,315988201,212694388,886875,212696237⟩,⟨13310364,1000000000,
      102673095,25254592,105733433,156224677,-449964,156225325,25989579,-50980,25989629⟩,⟨14937062,
      1000000000,146185032,35845225,150515593,6937955,-5268,6937957,141372051,-166460,141372149⟩,
      ⟨14442175,1000000000,83143384,20671863,85674665,129640827,296036,129641165,126067903,202104,
      126068065⟩,⟨15202765,1000000000,232784148,60413635,240495877,243765705,-249808,243765833,
      191316320,-176049,191316401⟩,⟨12288457,1000000000,94242723,22860964,96975845,440746355,
      -1721508,440749717,392157653,-1346604,392159965⟩,⟨12185260,1000000000,450207111,98822720,
      460925561,3674748,-13555,3674773,129549299,-569100,129550549⟩,⟨13658325,1000000000,464154411,
      114824740,478146461,208223939,894660,208225861,377911391,1827360,377915809⟩,⟨10425803,
      1000000000,95881645,23316132,98675893,172814291,1446060,172820341,2249951,21000,2250049⟩,
      ⟨10110624,1000000000,27792743,4879224,28217785,24703156,-161667,24703685,161440236,-1203923,
      161444725⟩,⟨9872341,1000000000,74414255,17949408,76548433,87139521,-970840,87144929,41691405,
      -490732,41694293⟩,⟨11152582,1000000000,131929,26280,134521,263054025,1427272,263057897,
      523992405,3387868,524003357⟩,⟨15644672,1000000000,332010485,83661828,342389053,484581227,
      8233236,484651165,406476315,6976052,406536173⟩,⟨8471180,1000000000,194841816,48593713,
      200810065,515679081,6358520,515718281,532026195,5489708,532054517⟩,⟨7845260,1000000000,
      318061509,48146420,321684941,22571901,-95020,22572101,534348495,-1433192,534350417⟩,
      ⟨15009474,1000000000,233009967,56798944,239832785,459735955,-6561252,459782773,264664985,
      -4034712,264695737⟩,⟨15689239,1000000000,6238440,1663921,6456529,203792336,-6117873,
      203884145,34554897,-1034704,34570385⟩,⟨9512296,1000000000,1982580,565091,2061541,36143975,
      -156312,36144313,93353883,-367156,93354605⟩,⟨9631108,1000000000,8688801,826280,8728001,
      222836980,401109,222837341,221066680,777999,221068049⟩,⟨16648409,1000000000,144378937,
      40469016,149943385,125116395,2259572,125136797,72313527,1139536,72322505⟩,⟨16981578,
      1000000000,44069860,12678771,45857429,125080631,-782880,125083081,425306193,-1814824,
      425310065⟩,⟨10498383,1000000000,202137701,56903220,209994349,525402201,51405760,527911001,
      441313793,43580376,443460385⟩,⟨10210713,1000000000,7431783,978056,7495865,402459453,10192004,
      402588485,8247015,212528,8249753⟩,⟨8387646,1000000000,487866867,138877156,507248405,9907113,
      1540616,10026185,142406743,21757824,144059305⟩,⟨7108192,1000000000,54181799,4789200,54393049,
      16338432,485945,16345657,421067803,11943804,421237165⟩,⟨15239496,1000000000,237072864,
      59487473,244422385,72156903,-92240896,117111065,52015932,-66325675,84289693⟩,⟨9915886,
      1000000000,496830399,126944200,512791649,269020811,16967940,269555389,12575535,801848,
      12601073⟩,⟨14462023,1000000000,1920144,451817,1972585,-151434283,48361956,158969245,
      -353659071,113364160,371384129⟩,⟨11109640,1000000000,25856,6183,26585,3903396,-551797,
      3942205,71586372,-10087795,72293653⟩,⟨10657604,1000000000,21006055,5068368,21608857,
      -10599979,-5286300,11845021,-38899740,-19452011,43492189⟩,⟨12881275,1000000000,170123040,
      38666729,174461929,311023035,-47080132,314566157,257540296,-39308247,260522825⟩,⟨12997984,
      1000000000,251739183,62960744,259493105,-254729541,-389828660,465675341,-277978491,
      -427284380,509748941⟩,⟨12133508,1000000000,4292065,1051848,4419073,298403055,-74958848,
      307673873,76236591,-19307200,78643409⟩,⟨10933909,1000000000,30399545,6745152,31138873,
      -142237689,-113578360,182020889,-15110423,-12115536,19367785⟩,⟨11012811,1000000000,72877320,
      15822329,74575129,123071348,-706005,123073373,303450159,-2752360,303462641⟩,⟨6938824,
      1000000000,483831869,100393020,494137669,255083800,-81893889,267907361,1326795,-422092,
      1392317⟩,⟨11882672,1000000000,62368377,12892936,63687065,-19931340,-40794901,45403549,
      -167843055,-341914088,380889137⟩,⟨13571945,1000000000,7190425,1750248,7400377,181609181,
      -66776820,193496869,106470680,-39287319,113487881⟩,⟨12730085,1000000000,31643975,7487808,
      32517817,-203848023,-182611736,273680585,-101578008,-90961225,136352617⟩,⟨16778163,
      1000000000,26539012,6242085,27263213,167691628,-39924765,172378853,107665948,-25457325,
      110634677⟩,⟨14793918,1000000000,358846683,98610644,372149165,-488836023,-118064936,502891625,
      -519325015,-125455632,534263593⟩,⟨10470067,1000000000,84180,19411,86389,283937011,-78057540,
      294471061,2154468,-592885,2234557⟩,⟨8430656,1000000000,107967084,22440187,110274445,
      200875605,95616028,222471197,130825588,61831275,144701213⟩,⟨89706,1000000000,191824627,
      42554436,196488085,-5571252,5230765,7641973,-311533089,292098400,427053089⟩,⟨15885146,
      1000000000,47594012,1024485,47605037,29581860,2178251,29661949,41211152,3079815,41326073⟩,
      ⟨15065620,1000000000,422971749,99807740,434587949,343047219,45476900,346048469,10737567,
      1425256,10831745⟩,⟨123289,1000000000,487767315,131597492,505207733,-99337700,86611491,
      131793509,-39886605,35233972,53220053⟩,⟨57689,1000000000,490222985,26401608,490933417,
      351921465,59945168,356990393,444126309,78104260,450941741⟩,⟨10492748,1000000000,345822603,
      9336196,345948605,19574195,3903588,19959637,515544777,103689536,525868745⟩,⟨9527798,
      1000000000,125318853,9724204,125695565,369062505,153688,369062537,22264460,-20019,22264469⟩,
      ⟨6183393,1000000000,1671855,440752,1728977,34561120,-163262079,166880129,77267565,-361634788,
      369797237⟩,⟨6361022,1000000000,522652355,20533668,523055557,530779137,-5897984,530811905,
      77966691,-830020,77971109⟩,⟨105358,1000000000,529940861,21090900,530360389,230375279,7256040,
      230489521,387241905,12438392,387441617⟩,⟨4304392,1000000000,319091175,45378872,322301753,
      261080965,12995052,261404173,73073805,3659828,73165397⟩,⟨4191972,1000000000,105488009,
      6082800,105663241,109661943,-607376,109663625,336572691,-2018060,336578741⟩,⟨13468955,
      1000000000,451654427,88960764,460332205,93321607,5160576,93464185,11681097,629096,11698025⟩,
      ⟨17046753,1000000000,159672588,42484925,165228037,351021345,8693968,351128993,260401740,
      6687139,260487589⟩,⟨17151885,1000000000,517198199,130689840,533454601,3157544,22617,3157625,
      118224864,753473,118227265⟩,⟨141844,1000000000,184118088,48280745,190343113,334757907,
      61993876,340449845,377359437,71098084,383998805⟩,⟨70161,1000000000,307867279,8949480,
      307997329,212903495,-17846088,213650137,10217208,-918575,10258417⟩,⟨16645651,1000000000,
      1215313,79416,1217905,110560200,-8467289,110883961,402059581,-29615940,403148869⟩,⟨17387753,
      1000000000,113455265,29032848,117111073,232497535,1921248,232505473,30256000,225591,
      30256841⟩,⟨17766985,1000000000,303827865,75591152,313090073,52373145,463168,52375193,
      223678440,1882439,223686361⟩,⟨17913924,1000000000,362733251,102188220,376852549,67864283,
      -313044,67865005,4592433,-17144,4592465⟩,⟨20174890,1000000000,290698449,79840480,301463249,
      120387132,-853435,120390157,86447620,-407619,86448581⟩,⟨7718923,1000000000,223304536,
      63099423,232048385,515243577,-1452736,515245625,469284893,-1126476,469286245⟩,⟨7410224,
      1000000000,215801305,8463168,215967193,149792221,-734340,149794021,88641969,-301280,
      88642481⟩,⟨7944728,1000000000,42863345,6724608,43387633,25283160,7111,25283161,58525116,
      -248837,58525645⟩,⟨6632974,1000000000,53282367,3754256,53414465,224232520,-360009,224232809,
      429566907,-538876,429567245⟩,⟨19183379,1000000000,5500537,1650216,5742745,154231365,-347732,
      154231757,390812065,-1423368,390814657⟩,⟨10615836,1000000000,343466725,80830788,352849837,
      107941812,367325,107942437,536848899,46340,536848901⟩,⟨10061719,1000000000,217787613,
      15534884,218340965,404572707,-683876,404573285,359779399,2845200,359790649⟩,⟨12241323,
      1000000000,4337532,1246525,4513093,270993963,1942516,271000925,426752603,785004,426753325⟩,
      ⟨9363709,1000000000,10043895,843752,10079273,192210487,-83184,192210505,469327047,1863104,
      469330745⟩,⟨20555217,1000000000,249650435,70484772,259409797,414854799,1018400,414856049,
      518290531,-682980,518290981⟩]},
    [[0,818310000,919068353],[0,818310000,919068353],[0,818310000,919068353],
    [0,818310000,919068353],[0,818310000,919068353],[0,818310000,919068353],
    [0,818310000,919068353],[0,818310000,919068353],[0,818310000,919068353],
    [0,818310000,919068353],[0,818310000,919068353],[0,818310000,919068353],
    [0,818310000,919068354],[0,818310000,919068358],[0,818310000,919070090],
    [0,818310000,919676912],[0,818310000,1132394210]],919068354,1707106781⟩
/-- Exported helper `ghZoomRow32`. -/
def ghZoomRow32 : GHZoomRowSpec :=
  { a0Num := 1024317, a0Den := 1000000, bNum := 1485445, bDen := 1000000, probes :=
    [ ⟨131497, 1000000, 48829287, 42895184, 64994585,
      62603507, -2643276, 62659285, 60610144, -2569710, 60664594⟩
    , ⟨123533, 1000000, 38474695, 31969512, 50023513,
      34257685, -3586932, 34444957, 8007120, -776242, 8044658⟩
    , ⟨128616, 1000000, 506989, 474300, 694261,
      58574673, 47395936, 75348305, 57386175, 46662832, 73963457⟩
    , ⟨35190, 1000000, 2883552, 2014414, 3517490,
      -61638595, 33251172, 70035397, -14787957, 8133076, 16876925⟩
    , ⟨128945, 1000000, 37982280, 27792502, 47064602,
      -22208147, 21512796, 30919285, -54623616, 52535950, 75787634⟩
    , ⟨94422, 1000000, 11614045, 10198188, 15456037,
      -27603160, -35329161, 44833961, -182628, -231485, 294853⟩
    , ⟨133573, 1000000, 49544277, 40336036, 63887645,
      -36860195, -15457812, 39970213, -6771280, -2853618, 7348018⟩
    , ⟨85085, 1000000, 55307577, 42159736, 69544025,
      -33631368, 50684585, 60827593, -15284178, 23003600, 27618322⟩
    , ⟨133817, 1000000, 19359633, 14399344, 24127505,
      43634408, 20905206, 48383770, 8215584, 4037390, 9154034⟩
    , ⟨117421, 1000000, 33323672, 26446746, 42542890,
      60671960, 12955782, 62039818, 65982105, 15638248, 67809977⟩ ] }
/-- Exported helper `ghZoomVSeq32`. -/
def ghZoomVSeq32 : List (List ℕ) :=
  [ [0, 818310000, 896670606]
  , [0, 818310000, 896670606]
  , [0, 818310000, 896670606]
  , [0, 818310000, 896670606]
  , [0, 818310000, 896670606]
  , [0, 818310000, 896670607]
  , [0, 818310000, 896671222]
  , [0, 818310000, 897042926]
  , [0, 818310000, 1121961376] ]
/-- Exported helper `ghZoomCert32k2`. -/
def ghZoomCert32k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 960745646, a0Den := 1000000000, bNum := 1486116472, bDen := 1000000000, probes :=
      [⟨15177937,1000000000,124513207,29595624,127982185,20129512,-6345,20129513,508592655,-315728,
      508592753⟩,⟨15325156,1000000000,96845364,24561277,99911365,125976052,-79365,125976077,
      55487597,-29796,55487605⟩,⟨14257327,1000000000,280854875,67613268,288878893,113356612,75285,
      113356637,113166995,148932,113167093⟩,⟨14253732,1000000000,24276875,5825388,24966013,
      158180925,50308,158180933,377758071,194360,377758121⟩,⟨14356641,1000000000,257400624,
      62411543,264858985,475283585,-174408,475283617,275892019,-298980,275892181⟩,⟨14289735,
      1000000000,154932116,37713837,159456245,452753275,127668,452753293,502252905,179288,
      502252937⟩,⟨13935929,1000000000,416913505,102186792,429254017,520615345,547608,520615633,
      238949539,463740,238949989⟩,⟨14410811,1000000000,13438252,3316605,13841477,238949755,92748,
      238949773,108326455,-62448,108326473⟩,⟨14709222,1000000000,87788799,21730880,90438401,
      147799360,-395439,147799889,236605563,-584516,236606285⟩,⟨14829674,1000000000,386084661,
      102662420,399500861,324936651,-180260,324936701,261632752,-251625,261632873⟩,⟨14102025,
      1000000000,79244291,19787820,81677509,245956425,250928,245956553,148522528,224055,148522697⟩,
      ⟨14902390,1000000000,164279031,41202040,169367081,52417519,-130320,52417681,368332135,
      -1036368,368333593⟩,⟨14607623,1000000000,388456177,103052736,401893105,339554229,368540,
      339554429,4115580,2869,4115581⟩,⟨14576826,1000000000,152096105,38380752,156863977,532775915,
      2446692,532781533,232073387,1127316,232076125⟩,⟨14608842,1000000000,466054629,123235180,
      482072429,536848899,-46340,536848901,337824319,330840,337824481⟩,⟨14119846,1000000000,
      210030128,53610105,216764153,1810700,-5709,1810709,27081535,-93672,27081697⟩,⟨14268189,
      1000000000,110797815,29278928,114601097,51854385,57608,51854417,41886783,12944,41886785⟩,
      ⟨13894747,1000000000,6437739,1662700,6648989,180578883,833156,180580805,319656877,1501836,
      319660405⟩,⟨14191688,1000000000,137590457,36149424,142260025,258308823,-610736,258309545,
      45305620,-104709,45305741⟩,⟨13904564,1000000000,28757,7524,29725,37246816,-198513,37247345,
      74338523,-327636,74339245⟩,⟨13950696,1000000000,98040456,25513033,101305705,51609567,244256,
      51610145,98405871,456320,98406929⟩,⟨13525896,1000000000,36963023,9798936,38239825,36507212,
      435795,36509813,197342232,2284705,197355457⟩,⟨13721741,1000000000,251604080,64514889,
      259743689,65495749,-485580,65497549,393421141,-3094260,393433309⟩,⟨13267079,1000000000,
      470160187,126125484,486783565,239105156,-4526883,239148005,151488212,-2872155,151515437⟩,
      ⟨13201083,1000000000,99166236,24791677,102218245,23949016,-325287,23951225,88921179,-1150460,
      88928621⟩,⟨12782073,1000000000,405655835,110023308,420311533,231493921,-1460640,231498529,
      521568003,-3608404,521580485⟩,⟨12997324,1000000000,129404281,31626840,133213081,449058157,
      -762876,449058805,28313005,-63852,28313077⟩,⟨12869100,1000000000,395318693,108923676,
      410050285,224117635,9613308,224323717,239452296,10353497,239676025⟩,⟨13098045,1000000000,
      9270035,2213652,9530677,134959840,3959871,135017921,200320761,5888480,200407289⟩,⟨12580949,
      1000000000,228623019,63337300,237234269,219440429,15712380,220002229,1355461,97860,1358989⟩,
      ⟨11942690,1000000000,354230129,81993960,363595921,324913303,11141304,325104265,125807043,
      4285276,125880005⟩,⟨19542601,1000000000,340571097,103307296,355894745,99817303,-198465696,
      222153385,22782552,-45308305,50713777⟩,⟨17952209,1000000000,485977571,154189740,509851621,
      -450392243,67719324,455454805,-30674691,4609820,31019141⟩,⟨15628197,1000000000,1169049,
      349760,1220249,38875473,-6557336,39424625,723324,-121907,733525⟩,⟨17457418,1000000000,
      104307369,31305400,108903881,-15128932,-5331765,16040957,-294831845,-103795212,312568813⟩,
      ⟨18893298,1000000000,125363868,38846075,131244493,100813272,-33305905,106172497,4271267,
      -1411356,4498405⟩,⟨17622806,1000000000,165305116,51756387,173218085,-214517296,-151916097,
      262861505,-1814937,-1284584,2223545⟩,⟨18619801,1000000000,35877956,11079717,37549805,
      356345569,-157594080,389638369,74575072,-32999295,81549953⟩,⟨19388288,1000000000,58304988,
      18102725,61050637,-6320605,-5130612,8140837,-217519063,-176299416,279992905⟩,⟨18151616,
      1000000000,510660399,160304680,535230449,282728359,-124562400,308951641,201300253,-88645404,
      219954085⟩,⟨20055671,1000000000,156053520,49369441,163676641,-1853885,-1655652,2485573,
      -33898185,-30285592,45456617⟩,⟨21132171,1000000000,402155655,130093048,422674073,271816383,
      -182849344,327594305,349291093,-235288476,421147165⟩,⟨15469843,1000000000,2308152,706225,
      2413777,-291762481,-172617480,339001681,-93830424,-55533457,109032625⟩,⟨15383676,1000000000,
      135477572,37533285,140580653,81320988,-21780445,84187237,144222820,-38669181,149316869⟩,
      ⟨16470161,1000000000,199090676,56276157,206891525,44042871,-8063440,44774921,238360545,
      -43656448,242325473⟩,⟨17213942,1000000000,52509184,14785863,54551225,-117742920,-15115591,
      118709209,-468661227,-60873364,472598045⟩,⟨17194511,1000000000,503769333,143527444,523816445,
      466593981,-159380780,493064069,305791721,-105724440,323552521⟩,⟨15138114,1000000000,12607744,
      3657633,13127585,356653401,234847880,427030649,19295928,12788945,23149297⟩,⟨17560222,
      1000000000,16299055,4573272,16928497,-442478397,256762796,511580165,-320390665,186484848,
      370711177⟩,⟨18150507,1000000000,14993421,4302100,15598421,1808023,381264,1847785,338112619,
      71778180,345647581⟩,⟨17356023,1000000000,14229384,4034863,14790385,171963056,35175567,
      175523825,37327481,7614840,38096281⟩,⟨19129565,1000000000,291565109,85229820,303766909,
      -366306171,248278060,442518029,-145563796,98853603,175956965⟩,⟨17206670,1000000000,203764308,
      59206685,212191717,93718388,23803275,96694013,214943740,55157739,221908061⟩,⟨18305425,
      1000000000,184918253,53464404,192492085,201481,244320,316681,124281825,151055768,195611393⟩,
      ⟨175342,1000000000,87530625,25020952,91036577,26050980,41619869,49100581,244732297,390344304,
      460719625⟩,⟨19142127,1000000000,1,0,1,391125419,363906180,534234781,764525,711348,1044277⟩,
      ⟨3137189,1000000000,488916345,114688672,502187897,156483613,277141116,318267685,168718875,
      302338732,346229357⟩,⟨3442890,1000000000,118897968,5660975,119032657,493561249,27736800,
      494340001,533016621,27806380,533741429⟩,⟨19794974,1000000000,410550187,86915484,419649565,
      458158365,125545012,475048037,596025,162032,617657⟩,⟨19484810,1000000000,177482668,55612605,
      185991557,56689796,1565403,56711405,8902231,268560,8906281⟩,⟨1494899,1000000000,6566840,
      1277991,6690041,7572060,45724861,46347589,27883077,168669436,170958605⟩,⟨17837134,1000000000,
      111496731,22005140,113647469,16804704,105362353,106694065,6882307,43092924,43639045⟩,
      ⟨16393338,1000000000,482930321,126760920,499289521,51376420,780549,51382349,492779,7020,
      492829⟩,⟨17061504,1000000000,217094156,56666667,224367965,277367163,-11627284,277610765,
      318305641,-13276680,318582409⟩,⟨16993982,1000000000,1485477,388364,1535405,147648109,
      37475820,152329909,49806680,12767409,51417041⟩,⟨17578290,1000000000,235877100,62588299,
      244039549,273546819,-33438260,275582981,103436156,-12926667,104240765⟩,⟨13666568,1000000000,
      323366505,91220768,335986793,2738840,-119391,2741441,395284075,-16346292,395621917⟩,
      ⟨18829804,1000000000,32293016,5833887,32815745,529090323,-1886164,529093685,340992195,
      -1144892,340994117⟩,⟨7959197,1000000000,361141785,108668728,377136953,184030912,940065,
      184033313,47045877,27436,47045885⟩,⟨19582948,1000000000,230672285,50909628,236223397,230399,
      960,230401,40978040,244431,40978769⟩,⟨19985578,1000000000,125041221,29954260,128579021,
      47794804,-107547,47794925,73071948,60445,73071973⟩,⟨900957,1000000000,11010664,3267927,
      11485385,216798400,478929,216798929,79845960,-543391,79847809⟩,⟨903481,1000000000,218034013,
      5138916,218094565,54596537,-413784,54598105,514653635,-1406532,514655557⟩,⟨11918589,
      1000000000,328049111,39009600,330360361,423864063,-1688216,423867425,70721724,-11893,
      70721725⟩,⟨11207651,1000000000,450014721,10522640,450137729,518017591,136560,518017609,
      934344,-1367,934345⟩,⟨11452045,1000000000,10081968,2741255,10447993,334304535,402248,
      334304777,933155,-1932,933157⟩,⟨10750233,1000000000,439645983,42361856,441682145,157360,-561,
      157361,48985901,139980,48986101⟩,⟨5499304,1000000000,206864808,64309375,216630433,78412584,
      -237937,78412945,252936687,-731584,252937745⟩,⟨5845177,1000000000,264935480,7113489,
      265030961,134466591,579800,134467841,531347445,1567468,531349757⟩,⟨14432315,1000000000,
      412030723,54069036,415563205,247743879,1920280,247751321,63265587,365884,63266645⟩,⟨12878127,
      1000000000,345072689,104433480,360529489,233019201,976960,233021249,31505669,112260,
      31505869⟩,⟨13002856,1000000000,278221293,25179076,279358325,426835591,123960,426835609,
      94957968,68905,94957993⟩,⟨12798853,1000000000,202312487,57542184,210336505,316732725,-783068,
      316733693,122168745,-176848,122168873⟩,⟨12427041,1000000000,8295305,738048,8328073,422713239,
      -781280,422713961,24700891,-29820,24700909⟩]},
    [[0,818310000,895547518],[0,818310000,895547518],[0,818310000,895547518],
    [0,818310000,895547518],[0,818310000,895547518],[0,818310000,895547518],
    [0,818310000,895547518],[0,818310000,895547518],[0,818310000,895547518],
    [0,818310000,895547518],[0,818310000,895547518],[0,818310000,895547518],
    [0,818310000,895547518],[0,818310000,895547519],[0,818310000,895547991],
    [0,818310000,895874543],[0,818310000,1121961376]],895547519,1707106781⟩
/-- Exported helper `ghZoomRow64`. -/
def ghZoomRow64 : GHZoomRowSpec :=
  { a0Num := 1023126, a0Den := 1000000, bNum := 1508316, bDen := 1000000, probes :=
    [ ⟨143299, 1000000, 45249435, 41658812, 61505837,
      5820888, -197866, 5824250, 2511549, -82420, 2512901⟩
    , ⟨134626, 1000000, 30169905, 28383352, 41422673,
      25975073, -2612736, 26106145, 14568000, -1367918, 14632082⟩
    , ⟨139521, 1000000, 9742104, 9698410, 13746554,
      32442137, 23505984, 40062745, 47742120, 34737478, 59042378⟩
    , ⟨81743, 1000000, 10966465, 9803088, 14709313,
      -41643595, 23387628, 47761597, -59749305, 33710288, 68602937⟩
    , ⟨140702, 1000000, 75945, 69368, 102857,
      -580659, 546140, 797141, -48537853, 45407004, 66465925⟩
    , ⟨124016, 1000000, 38837326, 39191232, 55175090,
      -17105320, -16458198, 23737402, -42902195, -41330292, 59571733⟩
    , ⟨173629, 1000000, 26109678, 26570480, 37251922,
      -54820337, -9392784, 55619185, -36295035, -6154828, 36813197⟩
    , ⟨91872, 1000000, 3108120, 2772778, 4165178,
      -3057300, 4116979, 5128021, -29290404, 38503997, 48378565⟩
    , ⟨131732, 1000000, 19885943, 14855376, 24822025,
      19687448, 12835014, 23501770, 7821632, 5140974, 9359890⟩
    , ⟨158923, 1000000, 19965816, 17860490, 26788634,
      32096963, 16451484, 36067525, 11191911, 6110360, 12751289⟩ ] }
/-- Exported helper `ghZoomVSeq64`. -/
def ghZoomVSeq64 : List (List ℕ) :=
  [ [0, 818310000, 884351385]
  , [0, 818310000, 884351385]
  , [0, 818310000, 884351385]
  , [0, 818310000, 884351385]
  , [0, 818310000, 884351385]
  , [0, 818310000, 884351385]
  , [0, 818310000, 884351571]
  , [0, 818310000, 884558142]
  , [0, 818310000, 1115040245] ]
/-- Exported helper `ghZoomCert64k2`. -/
def ghZoomCert64k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 956912190, a0Den := 1000000000, bNum := 1509496222, bDen := 1000000000, probes :=
      [⟨18269440,1000000000,116436576,30577943,120384745,426670311,206560,426670361,29822364,7723,
      29822365⟩,⟨18258870,1000000000,18755893,5300076,19490365,1,0,1,174788900,56091,174788909⟩,
      ⟨17479692,1000000000,197172963,52144484,203951525,191551164,-19573,191551165,536848899,46340,
      536848901⟩,⟨17511213,1000000000,209992287,57530816,217730465,12271005,-14012,12271013,
      527345071,-688920,527345521⟩,⟨16955259,1000000000,14851837,4060116,15396805,163642116,126637,
      163642165,18284175,8552,18284177⟩,⟨17623851,1000000000,328204305,91142408,340624433,81162077,
      36036,81162085,248566675,283788,248566837⟩,⟨17159753,1000000000,360682041,98584760,373912409,
      278055609,-133400,278055641,107443116,-102613,107443165⟩,⟨16588220,1000000000,113087799,
      31015480,117263849,152596605,49412,152596613,450797799,212320,450797849⟩,⟨16887638,
      1000000000,111517577,30868464,115710985,115231380,-15181,115231381,222499488,-147665,
      222499537⟩,⟨17097198,1000000000,162346055,45564288,168618937,23020779,-47980,23020829,
      272018905,-395832,272019193⟩,⟨16634194,1000000000,135709708,38310405,141013517,428200213,
      248316,428200285,2911284,2413,2911285⟩,⟨16735853,1000000000,236954592,67515935,246385633,
      339738599,184320,339738649,1,0,1⟩,⟨18400267,1000000000,292658355,83729188,304400213,
      421070231,533520,421070569,27593993,42024,27594025⟩,⟨18476819,1000000000,104206004,32111997,
      109041605,219276575,503472,219277153,145880060,358701,145880501⟩,⟨15630811,1000000000,
      152202808,44009625,158437817,6390308,10725,6390317,196925025,224528,196925153⟩,⟨15267580,
      1000000000,101324535,27400888,104964137,109533788,-666045,109535813,15030985,-93048,
      15031273⟩,⟨17285552,1000000000,237598801,69526800,247562449,200740624,-220407,200740745,
      427579603,-372204,427579765⟩,⟨17212421,1000000000,86283432,26317585,90207793,405779647,
      1329504,405781825,266504024,900393,266505545⟩,⟨18448509,1000000000,338836557,99021076,
      353009045,2693516,6963,2693525,208916976,470143,208917505⟩,⟨18663980,1000000000,476378877,
      156457436,501413765,112591412,2476155,112618637,25874433,569744,25880705⟩,⟨17681018,
      1000000000,133799165,40658772,139840453,345259245,-9737492,345396533,380800815,-10577672,
      380947697⟩,⟨17285941,1000000000,220906796,67667397,231038285,105254831,-2318760,105280369,
      450487851,-9976220,450598301⟩,⟨17672722,1000000000,72227360,22210839,75565289,15934975,
      263472,15937153,20628395,336108,20631133⟩,⟨17455887,1000000000,18212159,5797440,19112641,
      171520940,9838899,171802901,527412381,30418900,528288869⟩,⟨15923709,1000000000,24584192,
      7771215,25783217,19401412,-2590845,19573637,96079912,-12851025,96935537⟩,⟨16221592,
      1000000000,92363967,26064944,95971265,69371660,459381,69373181,389979535,2488248,389987473⟩,
      ⟨22228756,1000000000,464954973,156233836,490501925,-91943763,48935684,104155445,-9109120,
      4834479,10312529⟩,⟨16774678,1000000000,12993945,4325152,13694873,-2145408,93380575,93405217,
      -275964,12515923,12518965⟩,⟨22012353,1000000000,37970075,12754332,40054957,5212389,138612220,
      138710189,5700780,153533549,153639349⟩,⟨20070885,1000000000,130838923,45038964,138373885,
      -133478988,68299595,149938237,-286810797,146641396,322124405⟩,⟨18739999,1000000000,123619671,
      40663040,130135721,29522664,-8230177,30648385,2856147,-794996,2964725⟩,⟨20540287,1000000000,
      219081096,72690097,230825425,-242249796,-76706597,254104045,-461411799,-145614520,483843401⟩,
      ⟨21586412,1000000000,253555720,86993751,268064201,82049671,-35613960,89445529,179072145,
      -77587288,195157937⟩,⟨22585469,1000000000,1393179,491180,1477229,-118535955,-40112092,
      125138933,-1629067,-551244,1719805⟩,⟨21258054,1000000000,282417993,98770976,299191625,
      28726335,-18007928,33904097,216264040,-135796401,255364049⟩,⟨21873415,1000000000,298820253,
      103608596,316272485,-68355308,-38726595,78563333,-290965475,-164690148,334340773⟩,⟨12818386,
      1000000000,77461779,26986460,82028021,134674260,-85169149,159345349,15961681,-10120200,
      18899569⟩,⟨12709434,1000000000,191583543,23825224,193059305,29161704,-145103,29162065,
      61418245,-282132,61418893⟩,⟨12924052,1000000000,462738075,164352788,491058413,-97087639,
      -60261360,114269161,-178642555,-111038052,210339277⟩,⟨13028828,1000000000,526729517,70015044,
      531362485,72845969,273120,72846481,469891033,1560744,469893625⟩,⟨21627519,1000000000,
      120565445,41748972,127589197,84891024,-85582343,120543865,11743360,-11840151,16676201⟩,
      ⟨14724022,1000000000,355370511,127690480,377614961,-8673803,-34857804,35920765,-112653275,
      -451364892,465210733⟩,⟨13730070,1000000000,5809707,642124,5845085,184968705,-3699472,
      185005697,184995635,-3726948,185033173⟩,⟨14799519,1000000000,480083019,155729420,504709181,
      -54874185,-169257832,177930857,-73307380,-225505581,237121781⟩,⟨17648893,1000000000,
      446146827,131619436,465156605,374911065,-213137432,431260793,114490136,-64999527,131654585⟩,
      ⟨20807866,1000000000,164920440,51810401,172867201,224680236,-48330173,229819525,285591535,
      -61491528,292136497⟩,⟨19921514,1000000000,409754541,138311540,432468341,-233003340,-59026741,
      240363709,-27301731,-6898460,28159781⟩,⟨18994571,1000000000,281517587,89923884,295530805,
      86887380,-24178819,90188869,848771,-236220,881029⟩,⟨26855607,1000000000,507796397,169830804,
      535443445,342732315,338353132,481610093,22938060,22630069,32222269⟩,⟨20580665,1000000000,
      464285135,168406272,493883953,-191701995,67768388,203327837,-187517801,66159240,198846601⟩,
      ⟨18534895,1000000000,186135485,55550148,194247877,71922852,20728765,74850373,333743569,
      96556560,347430481⟩,⟨24048254,1000000000,179386329,59721200,189066329,67675257,19409824,
      70403705,3983700,1143251,4144501⟩,⟨328305,1000000000,85942788,4498445,86060437,15716376,
      3514343,16104505,28239080,6283191,28929641⟩,⟨28482244,1000000000,34457828,12106725,36522797,
      -3294753,2310904,4024385,-434473361,304929720,530800561⟩,⟨18060648,1000000000,152673540,
      56462219,162779581,306204165,120256108,328971917,487021265,192240408,523589617⟩,⟨11495656,
      1000000000,116649495,21059048,118535177,122927607,25029424,125449865,55004107,11136276,
      56120125⟩,⟨11794967,1000000000,153742180,47558259,160929941,16137060,34065691,37694509,93815,
      198792,219817⟩,⟨8801628,1000000000,172400585,18513792,173391817,253191580,-967629,253193429,
      34237752,-91025,34237873⟩,⟨27042930,1000000000,395637315,125676428,415118597,12139523,
      486862764,487014085,5094661,202717380,202781389⟩,⟨8424216,1000000000,461325015,155147272,
      486714953,30914843,90750876,95872045,78914560,231006969,244114169⟩,⟨10963082,1000000000,
      88695657,2788024,88739465,41187915,-680308,41193533,268111000,-3635649,268135649⟩,⟨22233510,
      1000000000,65396100,20045611,68399389,44133144,18301583,47777425,254259765,104694412,
      274970813⟩,⟨11363571,1000000000,2769432,757625,2871193,1556716,549837,1650965,490879723,
      175889364,521440285⟩,⟨3920200,1000000000,255324163,35848284,257828485,215095508,31130115,
      217336517,358788903,52455904,362603225⟩,⟨37928185,1000000000,508375565,157199628,532125397,
      -2545233,305311456,305322065,-1063563,174077516,174080765⟩,⟨5693780,1000000000,98070905,
      25806408,101409433,-260961,24871720,24873089,-993669,103692020,103696781⟩,⟨8363703,
      1000000000,489891647,119818704,504331585,29800932,4794155,30184093,839085,136012,850037⟩,
      ⟨24250896,1000000000,46818277,12169836,48374125,110660772,34761995,115992253,323402765,
      102144012,339150037⟩,⟨10371150,1000000000,126461040,38091151,132073201,427119315,80665588,
      434669813,95135335,17809128,96787897⟩,⟨12578572,1000000000,534686295,21601552,535122473,
      66990252,127325,66990373,144184,537,144185⟩,⟨24363537,1000000000,104728980,33389629,
      109922821,58079505,-6533848,58445873,26163808,-2919735,26326217⟩,⟨24873135,1000000000,
      22407345,7208672,23538353,175110793,-13666776,175643305,71596135,-5639688,71817913⟩,
      ⟨11308959,1000000000,79057164,25843373,83174005,11161072,-278775,11164553,18085305,-442312,
      18090713⟩,⟨11677044,1000000000,246766320,8643191,246917641,145470620,-51171,145470629,
      11863320,-4871,11863321⟩,⟨12604329,1000000000,276071527,79656864,287333785,96952752,153175,
      96952873,219975132,398525,219975493⟩,⟨11113327,1000000000,198219084,5953987,198308485,
      149904132,-536765,149905093,451135391,-1996560,451139809⟩,⟨20245620,1000000000,345306623,
      114135336,363680545,330585099,-181820,330585149,161950955,-279972,161951197⟩,⟨18389000,
      1000000000,114234795,25573012,117062237,316199499,-177820,316199549,414651285,895972,
      414652253⟩,⟨9240343,1000000000,1122429,364820,1180229,230196324,-2167157,230206525,10741432,
      -88065,10741793⟩,⟨20332500,1000000000,4357837,325884,4370005,590784,1087,590785,331895443,
      -327924,331895605⟩,⟨14518506,1000000000,15658084,5281563,16524845,217208475,383188,217208813,
      227633364,618773,227634205⟩,⟨13000302,1000000000,14587812,1324715,14647837,16652196,40397,
      16652245,213568971,146140,213569021⟩,⟨17041550,1000000000,410096417,138283344,432783265,
      190964420,-58629,190964429,317409847,106896,317409865⟩,⟨14993030,1000000000,3120199,265200,
      3131449,251888952,246895,251889073,411440031,1014200,411441281⟩]},
    [[0,818310000,882938863],[0,818310000,882938863],[0,818310000,882938863],
    [0,818310000,882938863],[0,818310000,882938863],[0,818310000,882938863],
    [0,818310000,882938863],[0,818310000,882938863],[0,818310000,882938863],
    [0,818310000,882938863],[0,818310000,882938863],[0,818310000,882938863],
    [0,818310000,882938863],[0,818310000,882938864],[0,818310000,882938991],
    [0,818310000,883111177],[0,818310000,1115040245]],882938864,1707106781⟩
/-- Exported helper `ghZoomRow128`. -/
def ghZoomRow128 : GHZoomRowSpec :=
  { a0Num := 1023952, a0Den := 1000000, bNum := 1523910, bDen := 1000000, probes :=
    [ ⟨143970, 1000000, 20123280, 19065118, 27720482,
      6485273, -224136, 6489145, 35475648, -1203314, 35496050⟩
    , ⟨134850, 1000000, 35928392, 33416394, 49066330,
      2295513, -230584, 2307065, 10721259, -1016180, 10769309⟩
    , ⟨143966, 1000000, 28338318, 29469440, 40884082,
      9980743, 7057176, 12223705, 41337615, 29554952, 50816273⟩
    , ⟨93721, 1000000, 32279635, 30848748, 44649973,
      -62026971, 35506820, 71470829, -59826351, 34262480, 68942801⟩
    , ⟨147922, 1000000, 47655456, 45773870, 66077906,
      -38192557, 37077324, 53229685, -170815, 165432, 237793⟩
    , ⟨142557, 1000000, 38709990, 42181576, 57251626,
      -12169135, -11629632, 16832593, -24695649, -23609600, 34165601⟩
    , ⟨225838, 1000000, 28606116, 35836237, 45853525,
      -1961256, -317530, 1986794, -38927077, -6233964, 39423085⟩
    , ⟨121687, 1000000, 34747720, 39014841, 52245209,
      -16970912, 22926255, 28524113, -18293084, 23841837, 30051125⟩
    , ⟨130181, 1000000, 17557808, 14850894, 22996210,
      41812264, 27000330, 49772314, 47415893, 31712076, 57043165⟩
    , ⟨199825, 1000000, 536130, 537136, 758914,
      61322877, 39349564, 72862085, 41340189, 28556740, 50244389⟩ ] }
/-- Exported helper `ghZoomVSeq128`. -/
def ghZoomVSeq128 : List (List ℕ) :=
  [ [0, 818310000, 877773403]
  , [0, 818310000, 877773403]
  , [0, 818310000, 877773403]
  , [0, 818310000, 877773403]
  , [0, 818310000, 877773403]
  , [0, 818310000, 877773404]
  , [0, 818310000, 877773487]
  , [0, 818310000, 877913843]
  , [0, 818310000, 1115040245] ]
/-- Exported helper `ghZoomCert128k2`. -/
def ghZoomCert128k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 955290947, a0Den := 1000000000, bNum := 1526222158, bDen := 1000000000, probes :=
      [⟨18205276,1000000000,249101316,69237763,258544645,362559665,-152328,362559697,88644608,
      -39945,88644617⟩,⟨18411028,1000000000,23105757,6187324,23919845,123889540,-15741,123889541,
      536848899,-46340,536848901⟩,⟨18376399,1000000000,255775996,72468147,265843925,175912484,
      168813,175912565,182763345,108152,182763377⟩,⟨18301817,1000000000,1685804,461397,1747805,
      46922499,13700,46922501,265305588,161245,265305637⟩,⟨18213189,1000000000,21305219,6107220,
      22163269,5513103,-4696,5513105,193356052,-216315,193356173⟩,⟨18254549,1000000000,443055225,
      124275848,460154777,118722815,21792,118722817,162536985,-101992,162537017⟩,⟨18533746,
      1000000000,18169076,5317443,18931205,484968123,836836,484968845,130301969,365280,130302481⟩,
      ⟨18468052,1000000000,10943100,3200179,11401429,384316815,-39208,384316817,3642300,2699,
      3642301⟩,⟨18795219,1000000000,159990405,46880708,166717517,85285209,-73880,85285241,
      494217165,-622468,494217557⟩,⟨18879392,1000000000,294673109,88649340,307718941,129413255,
      -250272,129413497,55711175,-164208,55711417⟩,⟨18900378,1000000000,45603503,13778904,47639665,
      177288969,426080,177289481,265719984,668537,265720825⟩,⟨19290150,1000000000,96108080,
      29317911,100480361,343991193,148376,343991225,233042376,280657,233042545⟩,⟨19244300,
      1000000000,199462825,62423088,209002537,180442892,-284955,180443117,422343345,-657632,
      422343857⟩,⟨19522832,1000000000,508229133,157550756,532089365,196981209,-112280,196981241,
      229401235,-272628,229401397⟩,⟨19473402,1000000000,443932909,143115180,466431541,86805913,
      -447216,86807065,38625969,-198880,38626481⟩,⟨19856172,1000000000,432228,136445,453253,
      11824384,-4863,11824385,65975584,11487,65975585⟩,⟨19796748,1000000000,104413075,34603068,
      109997557,29473941,108580,29474141,254019115,860652,254020573⟩,⟨19756238,1000000000,6821280,
      2172359,7158841,392078305,1425672,392080897,42513308,138315,42513533⟩,⟨20031283,1000000000,
      81591883,27638844,86146045,530748603,-1336204,530750285,74614963,-155484,74615125⟩,⟨19929116,
      1000000000,270359691,88099660,284351741,303312567,-2333744,303321545,112753740,-795901,
      112756549⟩,⟨19738581,1000000000,166887683,56609556,176227525,228726036,-4128077,228763285,
      29342940,-543931,29347981⟩,⟨18491106,1000000000,249290356,83116317,262781285,487248167,
      51148656,489925465,51176536,5399823,51460625⟩,⟨20440748,1000000000,378906945,124794488,
      398928737,470397405,26123188,471122213,32023205,1743588,32070637⟩,⟨19471464,1000000000,
      8633391,2962120,9127409,-501742353,-45922304,503839505,-386963063,-35484984,388586665⟩,
      ⟨18385416,1000000000,120644745,40160648,127153577,-73988904,60718847,95713825,-256739175,
      210366872,331917497⟩,⟨16039018,1000000000,302692143,95470576,317391185,-126252789,410341540,
      429324989,-3824601,12407720,12983801⟩,⟨19333968,1000000000,463830823,149559264,487346905,
      -71631833,321670056,329549305,-467847,2098096,2149625⟩,⟨19069630,1000000000,64592349,
      21334660,68024549,-85693641,182995720,202066409,-126121605,269653868,297690893⟩,⟨15877004,
      1000000000,384787855,124308912,404369137,-622687,3147216,3208225,-77146875,391745788,
      399269837⟩,⟨18298098,1000000000,211920497,64419096,221495185,1055336,99119127,99124745,
      2519152,254204895,254217377⟩,⟨21653268,1000000000,92786211,31908820,98119589,-66741555,
      313885412,320902613,-69110625,324683408,331957217⟩,⟨11894351,1000000000,13931660,4276539,
      14573261,-145766551,123401760,190986601,-94666695,80072048,123989177⟩,⟨11542210,1000000000,
      196323729,52695280,203272721,206104604,-1035453,206107205,1464091,-7260,1464109⟩,⟨10278563,
      1000000000,129983771,32792460,134056429,14524399,-19351200,24195601,1126081,-1499400,
      1875169⟩,⟨25405259,1000000000,189031372,57834765,197680853,-78075623,-54735936,95351065,
      -66288551,-46452120,80944249⟩,⟨19661410,1000000000,3723,1364,3965,-55396623,-108445064,
      121774865,-113287984,-222297537,249500225⟩,⟨20516758,1000000000,49928307,17098076,52774805,
      -100760609,-365805960,379429441,-107907075,-390614948,405245573⟩,⟨24249186,1000000000,634881,
      226520,674081,-7709509,-17055420,18716941,-11950043,-26285724,28874605⟩,⟨25139900,1000000000,
      118877437,44843916,127054405,-267090725,-391719348,474111277,-243240167,-357862944,
      432702745⟩,⟨23620783,1000000000,485469779,180303900,517871029,-33445540,-51262101,61207901,
      -11809356,-18070933,21587485⟩,⟨23457394,1000000000,120699688,44905185,128782337,-70709776,
      -250335207,260129945,-55549431,-195918640,203641481⟩,⟨24939699,1000000000,5602549,2049060,
      5965501,-701085,-1583908,1732133,-1087809,-2464000,2693441⟩,⟨25363057,1000000000,140274623,
      53228064,150033985,-5628237,-20112884,20885525,-71062719,-252999440,262790081⟩,⟨24735973,
      1000000000,323657685,122456908,346049117,-2475625,-7649448,8040073,-88690385,-273721488,
      287731537⟩,⟨24970194,1000000000,171862640,64300761,183497561,-29433656,-97099767,101462825,
      -7382900,-24200061,25301189⟩,⟨22943272,1000000000,299199285,110185172,318843197,-11055656,
      -193720167,194035385,-617785,-10779168,10796857⟩,⟨18424520,1000000000,116141880,37866961,
      122159089,-126768052,-225586515,258765173,-11522135,-20546328,23556553⟩,⟨26431903,1000000000,
      234472425,81020128,248075753,166260780,-8409101,166473301,78997897,-4054296,79101865⟩,
      ⟨13355940,1000000000,241424652,79909085,254305573,-243630031,-237296760,340096081,-41294752,
      -40167855,57608273⟩,⟨17678768,1000000000,161833212,48208435,168861013,7234368,-14647535,
      16336657,69289233,-140695856,156832145⟩,⟨21014078,1000000000,24253355,7768188,25467037,
      225626192,-54883305,232205417,201771032,-48862695,207603257⟩,⟨23846823,1000000000,171907309,
      59863500,182032309,-178171305,417593152,454014377,-8843055,20642408,22456817⟩,⟨15789184,
      1000000000,479207223,186728864,514302665,-58422065,267948072,274243153,-14996652,68292365,
      69919573⟩,⟨16741804,1000000000,366622113,17773984,367052705,56957173,90564,56957245,68597184,
      11713,68597185⟩,⟨16426504,1000000000,65160780,27135179,70585021,-19071679,534900240,
      535240129,-8349525,232665428,232815197⟩,⟨16124709,1000000000,947644,39933,948485,190742697,
      883904,190744745,129105180,787381,129107581⟩,⟨28698955,1000000000,338609699,134962500,
      364515301,-4412433,16079144,16673585,-107775655,393049272,407557753⟩,⟨22661257,1000000000,
      44386451,16596300,47387701,112031967,342977056,360810785,39696100,121886499,128187749⟩,
      ⟨21982126,1000000000,342383853,111933196,360216245,43952160,98547031,107904169,216413825,
      487227312,533127937⟩,⟨25510834,1000000000,100912105,34472808,106637833,143114697,324836104,
      354965225,55176,125993,137545⟩,⟨26593466,1000000000,48571248,17796655,51728977,92411605,
      260112972,276041053,6580635,18522908,19657133⟩,⟨14288098,1000000000,484083765,181579268,
      517018493,2675813,6065484,6629485,52234237,118022316,129064645⟩,⟨14390097,1000000000,
      454216371,11296420,454356821,400900929,5606440,400940129,492369531,7233940,492422669⟩,
      ⟨17009756,1000000000,198695200,68070639,210031889,-29898733,508653156,509531125,-30599193,
      530515424,531397145⟩,⟨16253880,1000000000,349985009,48757800,353365009,283757905,8490888,
      283884913,141215589,4611380,141290861⟩,⟨13225961,1000000000,237858985,106467528,260599753,
      6430840,28750809,29461241,56734516,254901213,261138725⟩,⟨12062017,1000000000,268083844,
      6507117,268162805,250967148,4996315,251016877,500454855,10156888,500557913⟩,⟨12057580,
      1000000000,247236576,50446207,252330625,60548980,216517581,224824469,142384599,509332640,
      528860201⟩,⟨24144468,1000000000,477458595,96940268,487200293,85622144,2080833,85647425,
      187590676,4513443,187644965⟩,⟨31395364,1000000000,245276240,93911679,262640129,11260099,
      47528940,48844549,59997665,254957952,261922273⟩,⟨189068,1000000000,472716717,107742044,
      484839605,157027941,141409820,211316141,116825596,105049197,157110005⟩,⟨8502208,1000000000,
      323785605,58609348,329047373,1774589,1442100,2286661,134413509,108845660,172957709⟩,
      ⟨15385879,1000000000,85947357,23996476,89234405,117353349,77454740,140609549,393926241,
      261103360,472602209⟩,⟨14684562,1000000000,318652611,42327740,321451589,13049536,270777,
      13052345,251636528,5317095,251692697⟩,⟨24370605,1000000000,494237783,185792544,528005545,
      266783985,80187128,278574353,458552779,138083700,478892221⟩,⟨23867590,1000000000,290353399,
      63452280,297205801,366506423,-20722464,367091785,233657292,-12347875,233983333⟩,⟨19874304,
      1000000000,2854485,1164748,3082973,101193112,-7103265,101442113,14241535,-974208,14274817⟩,
      ⟨20388580,1000000000,33264495,842128,33275153,406814259,-4881140,406843541,59766245,-711252,
      59770477⟩,⟨27753444,1000000000,63328608,28399265,69404833,155817508,-16883445,156729533,
      90632832,-9775175,91158457⟩,⟨26141559,1000000000,394317,78244,402005,309051911,2355720,
      309060889,13719447,96304,13719785⟩,⟨25821971,1000000000,14765859,6157540,15998309,3838800,
      -80359,3839641,267999704,-5765097,268061705⟩,⟨27196263,1000000000,514913203,100265604,
      524584405,77662344,510983,77664025,481711895,2326488,481717513⟩,⟨24707492,1000000000,
      314093087,143178216,345187585,494302193,2845824,494310385,6657560,32841,6657641⟩,⟨26444165,
      1000000000,263411176,40214193,266463185,30012,-245,30013,84198884,-895413,84203645⟩]},
    [[0,818310000,876003627],[0,818310000,876003627],[0,818310000,876003627],
    [0,818310000,876003627],[0,818310000,876003627],[0,818310000,876003627],
    [0,818310000,876003627],[0,818310000,876003627],[0,818310000,876003627],
    [0,818310000,876003627],[0,818310000,876003627],[0,818310000,876003627],
    [0,818310000,876003627],[0,818310000,876003627],[0,818310000,876003662],
    [0,818310000,876094560],[0,818310000,1115040245]],876003628,1707106781⟩
/-- Exported helper `ghZoomRow256`. -/
def ghZoomRow256 : GHZoomRowSpec :=
  { a0Num := 1023372, a0Den := 1000000, bNum := 1534440, bDen := 1000000, probes :=
    [ ⟨146010, 1000000, 15754101, 14860700, 21657149,
      54137720, -1928058, 54172042, 5844875, -207948, 5848573⟩
    , ⟨141880, 1000000, 44872917, 44004644, 62848925,
      57914899, -5256420, 58152949, 42642567, -3620944, 42796025⟩
    , ⟨143547, 1000000, 48945180, 52249061, 71593261, 760, 522, 922, 55552112, 38736834, 67724290⟩
    , ⟨103687, 1000000, 26814897, 26222704, 37505585,
      -31651763, 18202884, 36512725, -32561841, 18710360, 37554641⟩
    , ⟨151542, 1000000, 2431905, 2409088, 3423137,
      -50152229, 47678700, 69199021, -39043127, 37119936, 53872585⟩
    , ⟨158842, 1000000, 165550, 193104, 254354,
      -51048640, -46120878, 68797522, -32210339, -29138700, 43434661⟩
    , ⟨257750, 1000000, 24933496, 35373297, 43277585,
      -6853376, -1013250, 6927874, -14219232, -2094674, 14372690⟩
    , ⟨143016, 1000000, 9390148, 12030195, 15261077,
      -27885564, 37389523, 46643125, -44693038, 57042480, 72465938⟩
    , ⟨150167, 1000000, 18745712, 18044034, 26019010,
      2180355, 1548652, 2674373, 58964349, 44135060, 73652549⟩
    , ⟨224492, 1000000, 10205616, 11678513, 15509425,
      929960, 656982, 1138618, 318791, 243600, 401209⟩ ] }
/-- Exported helper `ghZoomVSeq256`. -/
def ghZoomVSeq256 : List (List ℕ) :=
  [ [0, 818310000, 874241515]
  , [0, 818310000, 874241515]
  , [0, 818310000, 874241515]
  , [0, 818310000, 874241515]
  , [0, 818310000, 874241515]
  , [0, 818310000, 874241515]
  , [0, 818310000, 874241571]
  , [0, 818310000, 874356800]
  , [0, 818310000, 1115040245] ]
/-- Exported helper `ghZoomCert256k2`. -/
def ghZoomCert256k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 956096940, a0Den := 1000000000, bNum := 1539283631, bDen := 1000000000, probes :=
      [⟨23122330,1000000000,337203795,103680068,352783157,250812800,67191,250812809,204484852,
      101115,204484877⟩,⟨22673566,1000000000,45893635,14270028,48060997,117267237,43316,117267245,
      58094883,15244,58094885⟩,⟨22329494,1000000000,47226432,14700335,49461457,536848899,-46340,
      536848901,356227867,-113244,356227885⟩,⟨22237725,1000000000,221664012,69567355,232324237,
      225929984,-191313,225930065,508096617,-360656,508096745⟩,⟨22268568,1000000000,214207188,
      67985995,224737213,5065744,-3183,5065745,251933880,-157129,251933929⟩,⟨22094065,1000000000,
      25151860,7975869,26386181,486952453,264804,486952525,7546612,3885,7546613⟩,⟨21875175,
      1000000000,422908983,137506456,444702185,93448108,68355,93448133,129878832,80585,129878857⟩,
      ⟨22042563,1000000000,6046920,1940071,6350521,56972303,-15096,56972305,258440108,-68205,
      258440117⟩,⟨22887645,1000000000,275059547,91323804,289823725,89359205,-37812,89359213,
      336098885,-73332,336098893⟩,⟨22724586,1000000000,129588151,43690440,136755049,170459111,
      -130560,170459161,215094480,-228151,215094601⟩,⟨22620141,1000000000,37717284,12849413,
      39845965,262960320,986119,262962169,87777761,374760,87778561⟩,⟨23019763,1000000000,153577941,
      53049620,162482141,464227907,-2025324,464232325,165237096,-781697,165238945⟩,⟨23368338,
      1000000000,107683128,37599775,114058753,16756148,86835,16756373,457528619,2524020,457535581⟩,
      ⟨23218487,1000000000,28027947,9920404,29731805,431184441,1162840,431186009,154927553,398304,
      154928065⟩,⟨23424160,1000000000,158754565,57279372,168771853,426917715,-950452,426918773,
      388877671,-1064880,388879129⟩,⟨24267020,1000000000,239463120,86670871,254665321,3299736,
      -43673,3300025,236595315,-3168692,236616533⟩,⟨24004193,1000000000,323441547,120943604,
      345314045,523616949,-14921020,523829501,523344957,-14734076,523552325⟩,⟨24133793,1000000000,
      7937271,2949920,8467721,4945667,431844,4964485,187822323,16489036,188544725⟩,⟨23981172,
      1000000000,10514231,4045800,11265769,63526215,2598872,63579353,263540640,10723721,263758729⟩,
      ⟨21132860,1000000000,15809421,5735380,16817621,-276021159,-22780360,276959609,-32049304,
      -2652303,32158865⟩,⟨19960966,1000000000,39429943,13487424,41672905,-58153508,48805485,
      75919733,-327193911,274482280,427078889⟩,⟨18220557,1000000000,251398028,86726685,265936997,
      -38476499,128184420,133834549,-136784181,456284540,476345981⟩,⟨20896509,1000000000,229153960,
      76836159,241692641,-24555740,101497509,104425709,-61366668,253329565,260656357⟩,⟨21496731,
      1000000000,404016675,141684508,428140133,-188810937,404465416,446365145,-14615115,31304812,
      34548413⟩,⟨17422192,1000000000,1014972,348245,1073053,-10267868,45298965,46448093,-36410920,
      160265559,164349641⟩,⟨21261147,1000000000,92145625,31301328,97316953,-1330665,272492888,
      272496137,-581508,100519835,100521517⟩,⟨23617757,1000000000,327865039,118628400,348666289,
      -38116489,187761840,191591689,-23918988,117650195,120057013⟩,⟨13271558,1000000000,47057220,
      15398909,49512709,-121209284,93785787,153256205,-312107959,241730400,394772041⟩,⟨12530662,
      1000000000,488230779,133565020,506170829,300879993,-6800024,300956825,59954880,-1325071,
      59969521⟩,⟨13721385,1000000000,23466135,6383728,24318953,98217185,-150761712,179932513,
      163541523,-251066564,299633525⟩,⟨29467859,1000000000,99934224,35906857,106189225,-231211677,
      -159433964,280852325,-34883148,-24037915,42363373⟩,⟨22409320,1000000000,416757837,163749916,
      447773525,-232990705,-424491792,484229233,-173492697,-315930904,360433145⟩,⟨23852113,
      1000000000,227989893,84285724,243070925,-29530605,-81051068,86263157,-160085943,-438768824,
      467060585⟩,⟨26875555,1000000000,439646373,171032164,471742445,-69638408,-136700055,153415817,
      -243771009,-478022600,536591009⟩,⟨28355696,1000000000,56696380,22984269,61178069,-926163,
      -1272284,1573685,-214676,-294507,364445⟩,⟨27116020,1000000000,32280600,13031881,34811881,
      -50176404,-71381347,87252325,-146039712,-207427375,253680337⟩,⟨27240085,1000000000,330681605,
      132163092,356114317,-38752420,-108255669,114982781,-19175164,-53662323,56985365⟩,⟨28510458,
      1000000000,352562331,144122900,380882669,-216446601,-436316320,487053449,-15794444,-31712667,
      35428205⟩,⟨29232810,1000000000,110479845,45508412,119485613,-32561760,-91093081,96737881,
      -524832,-1472455,1563193⟩,⟨29230133,1000000000,1686981,694300,1824269,-160449625,-408958272,
      439307353,-123962715,-314181532,337752557⟩,⟨31292161,1000000000,213386140,90493611,231781661,
      -121302525,-327787852,349512773,-52374237,-141496916,150878885⟩,⟨29402766,1000000000,
      490406829,207424780,532469621,-8208384,-66857863,67359865,-24217028,-196575165,198061253⟩,
      ⟨25783731,1000000000,209499033,83291056,225448985,-5685155,-9061092,10696933,-950291,
      -1513980,1787509⟩,⟨28291990,1000000000,95289156,38315333,102703885,279076061,-22403460,
      279973861,16751812,-1361355,16807037⟩,⟨21920056,1000000000,200795553,76583104,214904225,
      -7198905,-6539432,9725657,-269443275,-244453972,363809597⟩,⟨18177756,1000000000,251273,77064,
      262825,16784745,-40150192,43517417,289441,-692160,750241⟩,⟨25758237,1000000000,242939928,
      89911265,259044097,43240460,-11280531,44687669,15993460,-4180299,16530749⟩,⟨28494143,
      1000000000,192972360,74648801,206907649,-95416635,201344668,222809357,-30532029,64414780,
      71284421⟩,⟨20046335,1000000000,298653855,132665368,326793857,-57862220,254515821,261010229,
      -93458343,405874624,416495705⟩,⟨19741187,1000000000,45076580,2650221,45154421,281769571,
      -503580,281770021,483823391,-1099800,483824641⟩,⟨19636034,1000000000,383783153,180229896,
      423995665,-21631905,399501752,400086977,-23825,453792,454417⟩,⟨18579257,1000000000,186922420,
      9264339,187151861,426091323,1197236,426093005,10732284,50963,10732405⟩,⟨18819508,1000000000,
      226801520,103627929,249354521,-2533203,8642396,9006005,-136320191,463865400,483481441⟩,
      ⟨18043987,1000000000,75228729,2845400,75282521,392810791,5827080,392854009,344782797,5867804,
      344832725⟩,⟨30292476,1000000000,82475820,36023819,89999869,37314067,131440644,136634485,
      8954989,31512300,32759989⟩,⟨28727431,1000000000,7102627,2784564,7628965,8122744,21139617,
      22646465,41987799,108597800,116432201⟩,⟨16776308,1000000000,155612764,64051323,168279245,
      229536,614473,655945,166276235,450736812,480428413⟩,⟨15987340,1000000000,533937077,13772964,
      534114685,15458220,506051,15466501,181831524,6503893,181947805⟩,⟨18547799,1000000000,
      66855695,28446912,72656113,5718663,18598616,19457945,103194315,333991108,349569917⟩,
      ⟨18410797,1000000000,206147080,5746881,206227169,408811557,11242876,408966125,348530065,
      10306392,348682417⟩,⟨19356962,1000000000,1463905,685032,1616257,19213260,48505709,52172341,
      20924457,52672424,56676425⟩,⟨19846507,1000000000,1666281,51640,1667081,17246253,282404,
      17248565,19862044,384483,19865765⟩,⟨21753419,1000000000,40473111,17329000,44026889,-36075,
      427052,428573,-41604381,493581740,495332069⟩,⟨20369896,1000000000,263767449,8446360,
      263902649,55424181,923180,55431869,45302068,809115,45309293⟩,⟨20148891,1000000000,188387192,
      92371695,209814833,53350803,276329804,281432885,20052896,104581953,106487105⟩,⟨20494101,
      1000000000,452961965,54325908,456208117,71689356,4876267,71855005,11102787,753484,11128325⟩,
      ⟨21027548,1000000000,489430421,194286180,526582621,109324773,476387564,488770925,8299460,
      36230139,37168589⟩,⟨20780372,1000000000,92856580,2603139,92893061,55825743,1061024,55835825,
      213927813,4271084,213970445⟩,⟨30930348,1000000000,217753332,106867355,242563693,8831844,
      40006133,40969405,106143219,483556820,495069269⟩,⟨28790883,1000000000,5053132,1019205,
      5154893,509865653,25026396,510479485,101563203,5827396,101730245⟩,⟨37880,1000000000,
      330146715,90846452,342417773,338469159,328690240,471803609,50686545,49664032,70962257⟩,
      ⟨1079599,1000000000,96123880,21018129,98394929,316190567,289169856,428480665,22176495,
      19726408,29680433⟩,⟨35077390,1000000000,2463916,687987,2558165,78906187,58185516,98039485,
      372003681,278678920,464810369⟩,⟨23600434,1000000000,11888100,4858621,12842629,55845196,
      21812547,59953925,381705647,147022296,409041265⟩,⟨22308121,1000000000,154286396,16412403,
      155156885,126866460,-175219,126866581,50491200,-10049,50491201⟩,⟨25662503,1000000000,
      461906523,206385236,505917485,261854133,-13143844,262183805,80162847,-3886904,80257025⟩,
      ⟨27082972,1000000000,477720831,72905920,483251969,153743997,-5010004,153825605,17568375,
      -561728,17577353⟩,⟨25507142,1000000000,212669280,100460761,235203289,2922269,-376860,2946469,
      514823869,-65203980,518936581⟩,⟨27700111,1000000000,63029688,8156975,63555313,256669812,
      -113285,256669837,6311880,24871,6311929⟩,⟨30184683,1000000000,76646984,36329313,84820865,
      1229781,-22180,1229981,327575031,-6769400,327644969⟩,⟨29245927,1000000000,23089768,3852735,
      23408993,37000704,868903,37010905,211484000,3763761,211517489⟩,⟨16114416,1000000000,96639232,
      46776825,107364857,208760552,5333535,208828673,56393708,1433835,56411933⟩,⟨15333052,
      1000000000,13162476,241157,13164685,463466865,7578208,463528817,193781697,3118304,193806785⟩,
      ⟨18642200,1000000000,207409148,19267605,208302173,230973420,1010171,230975629,31291648,
      197775,31292273⟩]},
    [[0,818310000,872162330],[0,818310000,872162330],[0,818310000,872162330],
    [0,818310000,872162330],[0,818310000,872162330],[0,818310000,872162330],
    [0,818310000,872162330],[0,818310000,872162330],[0,818310000,872162330],
    [0,818310000,872162330],[0,818310000,872162330],[0,818310000,872162330],
    [0,818310000,872162330],[0,818310000,872162330],[0,818310000,872162340],
    [0,818310000,872209777],[0,818310000,1115040245]],872162331,1707106781⟩
/-- Exported helper `ghZoomRow512`. -/
def ghZoomRow512 : GHZoomRowSpec :=
  { a0Num := 1021246, a0Den := 1000000, bNum := 1541057, bDen := 1000000, probes :=
    [ ⟨148056, 1000000, 24310289, 22756080, 33299089,
      61703967, -1775456, 61729505, 55297088, -1621266, 55320850⟩
    , ⟨142721, 1000000, 4047960, 4055719, 5730169,
      4990713, -518984, 5017625, 16032877, -1587564, 16111285⟩
    , ⟨146053, 1000000, 14099898, 15007720, 20592202,
      50679552, 35350286, 61790450, 48642399, 34606720, 59696801⟩
    , ⟨109313, 1000000, 5757972, 5848405, 8207197,
      -62419631, 34945680, 71536081, -26556105, 14906488, 30453737⟩
    , ⟨157084, 1000000, 26534544, 27059017, 37898185,
      -42991400, 40735002, 59225002, -35914333, 33757644, 49289125⟩
    , ⟨164557, 1000000, 4104, 5047, 6505, -15994937, -14655216, 21693625, -10117, -9156, 13645⟩
    , ⟨267578, 1000000, 323550, 466336, 567586,
      -43224544, -5335470, 43552594, -49730331, -6288740, 50126381⟩
    , ⟨177584, 1000000, 4786198, 6944760, 8434298,
      -20891890, 31739664, 37998386, -41875742, 58589280, 72015842⟩
    , ⟨145973, 1000000, 53899998, 56229040, 77890402,
      54153440, 43260642, 69311458, 10800271, 9228960, 14206321⟩
    , ⟨271502, 1000000, 2268966, 2927912, 3704170,
      53414465, 52102512, 74617537, 12432882, 12915440, 17927218⟩ ] }
/-- Exported helper `ghZoomVSeq512`. -/
def ghZoomVSeq512 : List (List ℕ) :=
  [ [0, 818310000, 872361260]
  , [0, 818310000, 872361260]
  , [0, 818310000, 872361260]
  , [0, 818310000, 872361260]
  , [0, 818310000, 872361260]
  , [0, 818310000, 872361260]
  , [0, 818310000, 872361307]
  , [0, 818310000, 872467676]
  , [0, 818310000, 1115040245] ]
/-- Exported helper `ghZoomCert512k2`. -/
def ghZoomCert512k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 960365533, a0Den := 1000000000, bNum := 1548007887, bDen := 1000000000, probes :=
      [⟨32641157,1000000000,138440852,51404685,147676373,378613715,-272412,378613813,18181687,
      -25584,18181705⟩,⟨31458119,1000000000,60662877,22844164,64821605,6900608,11145,6900617,
      26871756,51317,26871805⟩,⟨31589309,1000000000,165680400,62215471,176976721,451901939,
      -1062900,451903189,67221952,-127545,67222073⟩,⟨31724812,1000000000,1262644,483483,1352045,
      10778085,13132,10778093,108383304,161953,108383425⟩,⟨32693395,1000000000,245531572,97275675,
      264099053,130201300,209781,130201469,536848899,-46340,536848901⟩,⟨32052556,1000000000,
      2073212,827925,2232413,397443007,-1315776,397445185,38130621,-24700,38130629⟩,⟨32378697,
      1000000000,203704560,82756201,219873001,108559692,-427315,108560533,220519376,-1197057,
      220522625⟩,⟨32226443,1000000000,439062837,179601884,474376445,283366915,4343172,283400197,
      137070039,1990360,137084489⟩,⟨31880969,1000000000,226116707,95286924,245373925,518027471,
      -18894120,518371921,119406941,-4153020,119479141⟩,⟨32021316,1000000000,246445151,102303720,
      266835649,36769656,2634367,36863905,36749267,2632644,36843445⟩,⟨33203861,1000000000,
      210770200,92323809,230103809,1909152,-119255,1912873,519019585,-32274888,520022113⟩,
      ⟨32484293,1000000000,348143795,151027932,379491157,8357817,-46256,8357945,4990707,-31276,
      4990805⟩,⟨2122,1000000000,223605609,66626920,233320841,-204952224,-30840257,207259585,
      -6259888,-975975,6335513⟩,⟨32337266,1000000000,473723733,149166844,496653725,-38675361,
      14154560,41184161,-152671121,56775720,162886321⟩,⟨18127226,1000000000,41072549,15999300,
      44078701,-15740460,233274299,233804749,-17063903,251105904,251685025⟩,⟨13336300,1000000000,
      336940131,103412620,352452581,-52772841,97072040,110489609,-57895420,106488531,121209269⟩,
      ⟨24513316,1000000000,3674643,1207924,3868085,-39838377,76819136,86534825,-47261795,91134108,
      102660133⟩,⟨18171527,1000000000,2310093,820876,2451605,-46969236,114575923,123829525,
      -84975877,206701836,223487245⟩,⟨20328206,1000000000,15362381,5262900,16238869,-16758000,
      54207079,56738329,-69574780,225522381,236010581⟩,⟨23135170,1000000000,212594639,76557360,
      225959089,-20364491,128368020,129973309,-76991909,481573980,487689709⟩,⟨13622051,1000000000,
      52709564,16743123,55304885,-88211293,33359076,94308325,-211429581,80167220,226117781⟩,
      ⟨12572126,1000000000,222200212,67163565,232129013,172284180,-17713411,173192389,483402689,
      -51079440,486093889⟩,⟨18469372,1000000000,400130275,111834372,415464997,13088520,-146578561,
      147161761,22618424,-241460607,242517665⟩,⟨28320692,1000000000,144860257,54643824,154823905,
      -221369731,-142428900,263230981,-112149840,-71711719,133117081⟩,⟨23546353,1000000000,
      253186521,100508200,272406521,-334677197,-256804596,421850005,-115187488,-89061735,
      145602713⟩,⟨27939620,1000000000,127082809,50442120,136727641,-179824855,-136067688,225502537,
      -41312624,-31169457,51751985⟩,⟨27321868,1000000000,3670744,1494783,3963425,-8951365,-6998652,
      11362573,-393089067,-305488244,497837405⟩,⟨29227874,1000000000,141236859,58927540,153036941,
      -4997577,-3218464,5944265,-125462799,-80844560,149254001⟩,⟨28252257,1000000000,129033793,
      53698776,139761505,-162277680,-104766121,193157929,-31278068,-20133075,37197557⟩,⟨29565700,
      1000000000,20914024,8788593,22685585,-34531772,-29599005,45481253,-41102399,-35203800,
      54117601⟩,⟨30810704,1000000000,104802517,44806356,113978845,-11306893,-9097476,14512405,
      -13631360,-11000151,17516201⟩,⟨31871662,1000000000,161873295,69935512,176334737,-37577833,
      -33769056,50521705,-616420,-556989,830789⟩,⟨30796332,1000000000,33305860,14685891,36399941,
      -12083016,-11121137,16421905,-9124920,-8306969,12339769⟩,⟨31403322,1000000000,411600847,
      181947096,450022225,-3792348,-3525115,5177677,-135009444,-126700333,185150005⟩,⟨35187214,
      1000000000,33377720,14509161,36394889,-133312008,-132346585,187850233,-18107700,-17754949,
      25359949⟩,⟨24119003,1000000000,13235805,5510092,14336933,-300216345,-231148288,378892313,
      -79456035,-61310612,100360613⟩,⟨26907197,1000000000,18567303,7275304,19941785,300516681,
      -15260080,300903881,525729471,-26376400,526390721⟩,⟨32073523,1000000000,440565877,202098564,
      484708285,-137739960,-111504401,177216049,-20002431,-16127720,25694369⟩,⟨8643031,1000000000,
      24416003,7506996,25544005,-2105668,-12393285,12570893,-12609200,-75094791,76146041⟩,
      ⟨38166606,1000000000,353232425,119195568,372801193,354462109,-172015740,393995941,201688656,
      -98097167,224279665⟩,⟨28739457,1000000000,272384437,130778484,302152765,-4424571,2601340,
      5132621,-216586885,127176588,251164813⟩,⟨22661730,1000000000,4961892,1742365,5258917,7475740,
      181749,7477949,107567940,3065821,107611621⟩,⟨21687266,1000000000,177576465,67903472,
      190116497,-8118068,27492645,28666157,-147208111,509054400,529911889⟩,⟨25353847,1000000000,
      29568759,11000720,31548809,3175235,-60588,3175813,163887723,-1510636,163894685⟩,⟨27029426,
      1000000000,200967012,89260765,219898213,-38502792,204296455,207893017,-7628728,41591655,
      42285497⟩,⟨23975561,1000000000,360708711,92082640,372276761,182540760,5140321,182613121,
      8392160,135201,8393249⟩,⟨27286825,1000000000,458482871,209050080,503893321,-27071616,
      49743113,56632585,-3766400,6660009,7651241⟩,⟨28596750,1000000000,224913136,74287473,
      236863985,268018692,3588715,268042717,329802321,5085080,329841521⟩,⟨16149864,1000000000,
      471237569,219958440,520044769,-40189919,521938920,523483969,-19228420,248037021,248781221⟩,
      ⟨18843290,1000000000,261221241,33296920,263334809,86648925,3985108,86740517,31499835,1470868,
      31534157⟩,⟨27805350,1000000000,51090567,23392856,56191385,-20159405,291093612,291790837,
      -31647321,501280520,502278521⟩,⟨24076125,1000000000,455892045,101132548,466974677,23629635,
      943228,23648453,470263379,19043820,470648821⟩,⟨21259204,1000000000,73482245,37329012,
      82420237,-5644659,103070660,103225109,-3389448,55197505,55301473⟩,⟨24680041,1000000000,
      514086329,18141600,514406329,387408297,22526504,388062665,154080699,8816780,154332749⟩,
      ⟨24661387,1000000000,10077961,5099640,11294761,-5104748,40968165,41284973,-11780813,92802516,
      93547285⟩,⟨22876593,1000000000,25606275,5197892,26128517,220206055,15055872,220720153,
      423066675,30584852,424170773⟩,⟨24480103,1000000000,474257927,225929736,525323545,78465,
      123135112,123135137,439,96360,96361⟩,⟨30406362,1000000000,58954435,12086388,60180613,
      412869093,16014524,413179565,334947709,12959940,335198341⟩,⟨31389971,1000000000,361619783,
      197506056,412040665,-4997505,13355312,14259713,-72278344,190815417,204045785⟩,⟨30467793,
      1000000000,150132435,35706172,154320053,326470265,4914768,326507257,345019809,3863600,
      345041441⟩,⟨28642780,1000000000,313062297,175684304,358988825,-8965236,59603323,60273805,
      -26041020,166170851,168198949⟩,⟨27579586,1000000000,235016892,44181475,239133733,408180969,
      25064120,408949769,529634329,35922120,530851129⟩,⟨27793773,1000000000,61791735,26824168,
      67362857,-390796,2682003,2710325,-39018924,260240893,263149765⟩,⟨31043070,1000000000,
      14797292,2044875,14937917,426105381,34293940,427483181,21181024,1556607,21238145⟩,⟨26535707,
      1000000000,38725085,25035972,46113253,-5916815,41606208,42024817,-29271195,214182052,
      216172973⟩,⟨27920098,1000000000,58854252,8429675,59454877,98640285,6399428,98847653,
      242296456,18217983,242980385⟩,⟨18906389,1000000000,216255657,91675976,234885065,14825272,
      40374945,43010753,45548073,126750536,134686025⟩,⟨19262085,1000000000,183524809,18882480,
      184493641,109430035,3201372,109476853,34170132,454685,34173157⟩,⟨16341551,1000000000,
      31914535,5751408,32428633,84043005,-3044108,84098117,65205647,-2051304,65237905⟩,⟨14888057,
      1000000000,353256135,29986328,354526553,173248871,-5397240,173332921,178146584,-4134063,
      178194545⟩,⟨11712,1000000000,139014953,28826496,141972265,404781,743540,846581,100124220,
      183899629,209389429⟩,⟨2140791,1000000000,91478772,20895955,93834997,48972329,73168680,
      88045129,138242384,203240487,245800025⟩,⟨28257699,1000000000,7616357,3519276,8390125,
      104057100,71660059,126344941,271084251,186947540,329296301⟩,⟨29344924,1000000000,211916592,
      13079095,212319817,176861628,-4420115,176916853,222587631,-4088080,222625169⟩,⟨27836709,
      1000000000,235203549,127807420,267685349,247846436,-18112827,248507405,4237039,-333720,
      4250161⟩,⟨35623345,1000000000,115997851,6141180,116160301,78673560,-3550801,78753649,
      155206308,-5198195,155293333⟩,⟨35214728,1000000000,72133788,38257085,81651013,134632840,
      -35766711,139302761,110480920,-29799039,114429089⟩,⟨27516760,1000000000,480135645,24286252,
      480749477,10433585,491112,10445137,156776047,6838104,156925105⟩,⟨26456245,1000000000,
      389144823,192289664,434061065,53110000,-3206721,53206721,97688800,-5355489,97835489⟩,
      ⟨29303628,1000000000,179008992,7021175,179146633,334500939,31822780,336011261,157215143,
      14585424,157890265⟩,⟨14719252,1000000000,151280541,75373180,169017509,258085731,5623100,
      258146981,27135504,302047,27137185⟩,⟨10013765,1000000000,251006245,17691948,251628973,
      138578303,-965304,138581665,469660005,20896628,470124653⟩,⟨17431907,1000000000,1835001,86720,
      1837049,39191661,3032260,39308789,105749312,-218145,105749537⟩,⟨23573438,1000000000,36968293,
      2262876,37037485,4622491,-12900,4622509,251439708,9532325,251620333⟩]},
    [[0,818310000,870037186],[0,818310000,870037186],[0,818310000,870037186],
    [0,818310000,870037186],[0,818310000,870037186],[0,818310000,870037186],
    [0,818310000,870037186],[0,818310000,870037186],[0,818310000,870037186],
    [0,818310000,870037186],[0,818310000,870037186],[0,818310000,870037186],
    [0,818310000,870037186],[0,818310000,870037186],[0,818310000,870037189],
    [0,818310000,870061967],[0,818310000,1115040245]],870037187,1707106781⟩
/-- Exported helper `ghZoomRow1024`. -/
def ghZoomRow1024 : GHZoomRowSpec :=
  { a0Num := 1022615, a0Den := 1000000, bNum := 1544704, bDen := 1000000, probes :=
    [ ⟨147810, 1000000, 47055041, 44574840, 64815841,
      46622697, -1529696, 46647785, 23158885, -750828, 23171053⟩
    , ⟨142706, 1000000, 46376799, 45778840, 65165249,
      31735617, -3294344, 31906145, 37304421, -3644540, 37482029⟩
    , ⟨148932, 1000000, 41817622, 45744120, 61977722,
      39137945, 26789688, 47428537, 38792555, 26927148, 47222173⟩
    , ⟨113773, 1000000, 89244, 92933, 128845,
      -48763160, 29008422, 56739178, -41124295, 24364872, 47800153⟩
    , ⟨156990, 1000000, 28569388, 29597205, 41136413,
      -18246624, 17277470, 25128674, -103179, 97300, 141821⟩
    , ⟨162442, 1000000, 25901946, 30651272, 40129930,
      -51277496, -46173270, 69002554, -9266313, -8272016, 12421385⟩
    , ⟨279820, 1000000, 24851900, 37540269, 45020981,
      -47265445, -6865428, 47761453, -36309000, -5523302, 36726698⟩
    , ⟨200741, 1000000, 28, 45, 53, -22684848, 30892505, 38326873, -27783262, 35153520, 44807138⟩
    , ⟨147681, 1000000, 49589340, 53842579, 73199221,
      47014947, 40918396, 62327525, 19821015, 18831568, 27340457⟩
    , ⟨309988, 1000000, 19740810, 28314904, 34517146,
      36815791, 35816160, 51363409, 48622028, 50890485, 70384253⟩ ] }
/-- Exported helper `ghZoomVSeq1024`. -/
def ghZoomVSeq1024 : List (List ℕ) :=
  [ [0, 818310000, 871368983]
  , [0, 818310000, 871368983]
  , [0, 818310000, 871368983]
  , [0, 818310000, 871368983]
  , [0, 818310000, 871368983]
  , [0, 818310000, 871368983]
  , [0, 818310000, 871369029]
  , [0, 818310000, 871474735]
  , [0, 818310000, 1115040245] ]
/-- Exported helper `ghZoomCert1024k2`. -/
def ghZoomCert1024k2 : GHZoomCellCert :=
  ⟨16,
    { a0Num := 959838491, a0Den := 1000000000, bNum := 1554697565, bDen := 1000000000, probes :=
      [⟨32984885,1000000000,96725036,36101973,103242845,499655585,-1430592,499657633,438315367,
      -1130544,438316825⟩,⟨32108079,1000000000,442127763,165967084,472252085,200533521,566440,
      200534321,473192333,1131156,473193685⟩,⟨31879372,1000000000,111728436,42630827,119585245,
      15335055,-7832,15335057,327972099,-36220,327972101⟩,⟨32310083,1000000000,403188123,155778436,
      432235565,909900,1349,909901,3111695,3528,3111697⟩,⟨32103766,1000000000,241683540,95702381,
      259942069,354567531,1393420,354570269,247683419,1101660,247685869⟩,⟨31567849,1000000000,
      110240603,43883196,118653805,370057269,-2693180,370067069,249958996,-1855797,249965885⟩,
      ⟨32623733,1000000000,209393460,84466189,225787861,101464845,443212,101465813,145587995,
      458508,145588717⟩,⟨33929398,1000000000,210662899,88463460,228483349,149645389,733980,
      149647189,76351915,471852,76353373⟩,⟨32561577,1000000000,187822569,80780840,204457481,
      140035541,-4213260,140098909,39920545,-1213248,39938977⟩,⟨32463497,1000000000,225859549,
      94819740,244955749,78323300,5297229,78502229,336228009,22750280,336996809⟩,⟨32786361,
      1000000000,442966295,192310008,482910217,473130815,-19101768,473516257,98084,-3987,98165⟩,
      ⟨33579856,1000000000,311229415,136737432,339942457,471084949,-14326620,471302749,320585573,
      -9813036,320735725⟩,⟨6545,1000000000,146350008,46853305,153667033,-112541296,-6498897,
      112728785,-482274575,-30892632,483262993⟩,⟨29548449,1000000000,368980143,108746024,384671345,
      -227281047,106485104,250989545,-357239413,170203116,395713405⟩,⟨22147171,1000000000,
      441689583,170750944,473545745,-1671696,11390447,11512465,-901813,6123516,6189565⟩,⟨16378476,
      1000000000,134698041,45365840,142132409,-91670228,168031275,191410397,-213583997,391435404,
      445914565⟩,⟨24607388,1000000000,246195492,87194275,261180133,-57191256,110638567,124546105,
      -2969139,5724460,6448661⟩,⟨21003007,1000000000,221733419,82502100,236584669,-2254791,5249480,
      5713241,-43375052,100778085,109716077⟩,⟨20482020,1000000000,3229007,1141824,3424945,
      -96681297,298220504,313500785,-48233760,148354871,155998921⟩,⟨25626141,1000000000,26593345,
      9681672,28300897,-58654449,352662400,357506801,-37283433,225677744,228736745⟩,⟨13034348,
      1000000000,213455424,72937393,225572785,-3166653,1134796,3363845,-348426463,124287216,
      369930145⟩,⟨14129824,1000000000,124245300,35324261,129169261,48448625,-4794672,48685297,
      66480492,-6592195,66806533⟩,⟨19317603,1000000000,182471580,55857011,190829461,23696473,
      -259539864,260619385,2022056,-22698417,22788305⟩,⟨29950809,1000000000,17656977,6914864,
      18962705,-46101867,-30206044,55116125,-13320164,-8710677,15915485⟩,⟨24903881,1000000000,
      486360819,198316820,525239381,-121852563,-93692716,153708725,-182089320,-140313161,
      229878889⟩,⟨28749318,1000000000,115722568,47565735,125116793,-269873097,-200853296,336412745,
      -30587795,-22779732,38138293⟩,⟨28468761,1000000000,127627629,52793660,138115829,-407376095,
      -312356448,513343777,-117814008,-90499945,148561033⟩,⟨29962593,1000000000,488759957,
      207654876,531043165,-41497140,-26200301,49076149,-166661572,-104685915,196812653⟩,⟨31256978,
      1000000000,340738085,147238068,371189293,-73965845,-47540148,87926173,-394224441,-253406200,
      468644441⟩,⟨32074999,1000000000,480851073,210058664,524730785,-365672127,-307506064,
      477782465,-291059923,-244818564,380331445⟩,⟨31940119,1000000000,179025,79672,195953,
      -48917451,-39387980,62803901,-62311431,-50420560,80155769⟩,⟨37561229,1000000000,189611460,
      87697459,208909909,-66211991,-60028920,89372809,-10916955,-9825188,14687213⟩,⟨22292043,
      1000000000,205144603,88442796,223397485,-176950900,-158591829,237619421,-224202045,
      -201031628,301131653⟩,⟨24531563,1000000000,2592348,912845,2748373,207398508,-8657675,
      207579133,403550565,-16958492,403906733⟩,⟨25425892,1000000000,673013,277884,728125,
      -149526676,-135366243,201698405,-64977876,-58335907,87322405⟩,⟨25379718,1000000000,162865188,
      61360765,174040837,49759220,-2484771,49821221,129679805,-6242268,129829957⟩,⟨46328717,
      1000000000,176479588,85205085,195971813,-356417085,-357698708,504956933,-121194017,
      -122272656,172158625⟩,⟨33114477,1000000000,31039435,14502132,34260157,-174163115,-130657332,
      217724893,-240599451,-177565060,299027501⟩,⟨25654434,1000000000,175901068,85072635,195393293,
      343063893,-7186924,343139165,10804,-147,10805⟩,⟨37162381,1000000000,175832052,71615635,
      189857077,-404006567,-328710144,520837465,-168016277,-135241164,215684125⟩,⟨21627088,
      1000000000,13668697,5989104,14923225,-13449675,-65731868,67093757,-15379225,-78317448,
      79813177⟩,⟨31571047,1000000000,394071829,140520660,418376221,295681737,-148388416,330827465,
      45712293,-23791876,51533165⟩,⟨23113074,1000000000,5895295,2701968,6484993,-255488413,
      149662284,296096485,-416686803,238930196,480328565⟩,⟨21934533,1000000000,221601395,43767108,
      225882133,362850601,11430600,363030601,185590396,6493653,185703965⟩,⟨24056031,1000000000,
      417958605,207533908,466647317,-21907380,74727709,77872741,-83124069,283793060,295716269⟩,
      ⟨25568223,1000000000,22373013,4814084,22885085,175641753,424096,175642265,123229216,-204087,
      123229385⟩,⟨25188862,1000000000,128784761,68134440,145697689,-43722996,213344003,217778245,
      -103131055,495392472,506013553⟩,⟨25195078,1000000000,3978885,729092,4045133,329095097,
      1015896,329096665,445377975,1224032,445379657⟩,⟨28477513,1000000000,116984205,62993572,
      132866453,-224771705,411300648,468711577,-21918036,39838277,45469645⟩,⟨27790771,1000000000,
      87742865,18231312,89616913,536848899,46340,536848901,62105248,256335,62105777⟩,⟨24281358,
      1000000000,94191815,48899088,106128313,-25947275,290719572,291875197,-21838948,262018125,
      262926677⟩,⟨22767794,1000000000,131649792,22457015,133551433,222134895,10047992,222362033,
      504542099,26919060,505259701⟩,⟨26432861,1000000000,145475981,75890100,164080981,-154972,
      2134635,2140253,-618499,8604300,8626501⟩,⟨23814357,1000000000,11892895,1056312,11939713,
      12421152,443665,12429073,499755925,12609348,499914973⟩,⟨29282834,1000000000,424895705,
      238685832,487347193,-25942451,398015940,398860501,-6968483,102255156,102492325⟩,⟨26696089,
      1000000000,86192533,12173556,87047965,437817387,11844116,437977565,164994680,6377319,
      165117881⟩,⟨25828401,1000000000,46562964,26744723,53697205,-65649855,474062048,478586177,
      -21777961,157796760,159292489⟩,⟨28716927,1000000000,25970747,3237204,26171725,324896061,
      16949140,325337861,294310515,16235252,294757973⟩,⟨29846043,1000000000,396277167,227753056,
      457063505,90421,11323860,11324221,2940195,499749788,499758437⟩,⟨31187541,1000000000,
      411602867,55593156,415340245,387633099,9884380,387759101,108189276,2750957,108224245⟩,
      ⟨37618866,1000000000,867855,509168,1006193,-20214945,52697792,56442017,-132909627,345078164,
      369789005⟩,⟨35208624,1000000000,198261817,47301144,203826265,7569100,159531,7570781,
      530172503,15705096,530405065⟩,⟨36140026,1000000000,132427855,84536832,157110193,-13403616,
      83517863,84586585,-362223,2338336,2366225⟩,⟨29736052,1000000000,467257237,58999116,470967325,
      262881928,16632225,263407553,56370119,3680880,56490169⟩,⟨34857256,1000000000,36304797,
      21797996,42346085,-71690025,480166688,485488937,-33504560,225717681,228190769⟩,⟨33285351,
      1000000000,6479079,586040,6505529,126550465,12434352,127159873,221592123,20594564,222547085⟩,
      ⟨41464977,1000000000,401059491,266953060,481780709,-9337464,70200473,70818745,-17353768,
      109398135,110765993⟩,⟨40879011,1000000000,389860785,38589088,391765937,16998564,1581827,
      17072005,530718309,39190100,532163309⟩,⟨15206683,1000000000,15309665,9151608,17836417,673816,
      1799487,1921505,8830783,23725944,25316065⟩,⟨17874692,1000000000,557225,41832,558793,
      309111713,7877184,309212065,234960564,10429523,235191925⟩,⟨15716022,1000000000,725613,161116,
      743285,287437387,-915516,287438845,1093660,-16269,1093781⟩,⟨12802670,1000000000,2862912,
      241895,2873113,371208453,3622196,371226125,154920792,2728465,154944817⟩,⟨48825228,1000000000,
      484660911,218902240,531802961,28729893,59748524,66297005,64856047,133014504,147983665⟩,
      ⟨51521,1000000000,117692364,21739277,119683285,144305037,253239716,291469205,18985372,
      33163755,38213597⟩,⟨22266502,1000000000,403318195,175812108,439972117,367852625,288762192,
      467652817,232187949,188174660,298866101⟩,⟨21544928,1000000000,52788,2275,52837,472457169,
      8694800,472537169,152900,1659,152909⟩,⟨30194714,1000000000,420647953,217180896,473404945,
      474522685,-27982212,475347013,290885869,-17404260,291406069⟩,⟨31303275,1000000000,90000020,
      4710771,90123221,129062232,-2490385,129086257,355054025,-2562648,355063273⟩,⟨33942300,
      1000000000,6782640,3504631,7634569,249681711,-76160680,261039089,305998147,-92214804,
      319591045⟩,⟨29489916,1000000000,177169571,8121540,177355621,245066360,-1129089,245068961,
      532683999,-2261840,532688801⟩,⟨36576964,1000000000,73187251,41564820,84166549,12492100,
      -1467051,12577949,181645356,-23243483,183126445⟩,⟨36828755,1000000000,264457840,8303361,
      264588161,263061084,11677987,263320165,239453240,10309719,239675081⟩,⟨33286634,1000000000,
      411291867,243458956,477946925,105603624,421457,105604465,92113080,176449,92113249⟩,⟨35430953,
      1000000000,164526597,6106604,164639885,229416025,8362248,229568377,153985260,4545709,
      154052341⟩]},
    [[0,818310000,868844442],[0,818310000,868844442],[0,818310000,868844442],
    [0,818310000,868844442],[0,818310000,868844442],[0,818310000,868844442],
    [0,818310000,868844442],[0,818310000,868844442],[0,818310000,868844442],
    [0,818310000,868844442],[0,818310000,868844442],[0,818310000,868844442],
    [0,818310000,868844442],[0,818310000,868844442],[0,818310000,868844443],
    [0,818310000,868857411],[0,818310000,1115040245]],868844443,1707106781⟩
lemma ghZoomCert4_2_ok :
    checkGHZoomSchedule 4 ghZoomCert4k2.W ghZoomCert4k2.rowSpec
      ghZoomCert4k2.vSeq 1056718415 1707106781 = true := by
  decide +kernel
lemma ghZoomCert8_2_ok :
    checkGHZoomSchedule 8 ghZoomCert8k2.W ghZoomCert8k2.rowSpec
      ghZoomCert8k2.vSeq 964679691 1707106781 = true := by
  decide +kernel
lemma ghZoomCert16_2_ok :
    checkGHZoomSchedule 16 ghZoomCert16k2.W ghZoomCert16k2.rowSpec
      ghZoomCert16k2.vSeq 919068354 1707106781 = true := by
  decide +kernel
lemma ghZoomCert32_2_ok :
    checkGHZoomSchedule 32 ghZoomCert32k2.W ghZoomCert32k2.rowSpec
      ghZoomCert32k2.vSeq 895547519 1707106781 = true := by
  decide +kernel
lemma ghZoomCert64_2_ok :
    checkGHZoomSchedule 64 ghZoomCert64k2.W ghZoomCert64k2.rowSpec
      ghZoomCert64k2.vSeq 882938864 1707106781 = true := by
  decide +kernel
lemma ghZoomCert128_2_ok :
    checkGHZoomSchedule 128 ghZoomCert128k2.W ghZoomCert128k2.rowSpec
      ghZoomCert128k2.vSeq 876003628 1707106781 = true := by
  decide +kernel
lemma ghZoomCert256_2_ok :
    checkGHZoomSchedule 256 ghZoomCert256k2.W ghZoomCert256k2.rowSpec
      ghZoomCert256k2.vSeq 872162331 1707106781 = true := by
  decide +kernel
lemma ghZoomCert512_2_ok :
    checkGHZoomSchedule 512 ghZoomCert512k2.W ghZoomCert512k2.rowSpec
      ghZoomCert512k2.vSeq 870037187 1707106781 = true := by
  decide +kernel
lemma ghZoomCert1024_2_ok :
    checkGHZoomSchedule 1024 ghZoomCert1024k2.W ghZoomCert1024k2.rowSpec
      ghZoomCert1024k2.vSeq 868844443 1707106781 = true := by
  decide +kernel
theorem ghZoomCertsK2_bundle_ok :
    checkGHZoomSchedule 4 ghZoomCert4k2.W ghZoomCert4k2.rowSpec
      ghZoomCert4k2.vSeq 1056718415 1707106781 = true ∧
    checkGHZoomSchedule 8 ghZoomCert8k2.W ghZoomCert8k2.rowSpec
      ghZoomCert8k2.vSeq 964679691 1707106781 = true ∧
    checkGHZoomSchedule 16 ghZoomCert16k2.W ghZoomCert16k2.rowSpec
      ghZoomCert16k2.vSeq 919068354 1707106781 = true ∧
    checkGHZoomSchedule 32 ghZoomCert32k2.W ghZoomCert32k2.rowSpec
      ghZoomCert32k2.vSeq 895547519 1707106781 = true ∧
    checkGHZoomSchedule 64 ghZoomCert64k2.W ghZoomCert64k2.rowSpec
      ghZoomCert64k2.vSeq 882938864 1707106781 = true ∧
    checkGHZoomSchedule 128 ghZoomCert128k2.W ghZoomCert128k2.rowSpec
      ghZoomCert128k2.vSeq 876003628 1707106781 = true ∧
    checkGHZoomSchedule 256 ghZoomCert256k2.W ghZoomCert256k2.rowSpec
      ghZoomCert256k2.vSeq 872162331 1707106781 = true ∧
    checkGHZoomSchedule 512 ghZoomCert512k2.W ghZoomCert512k2.rowSpec
      ghZoomCert512k2.vSeq 870037187 1707106781 = true ∧
    checkGHZoomSchedule 1024 ghZoomCert1024k2.W ghZoomCert1024k2.rowSpec
      ghZoomCert1024k2.vSeq 868844443 1707106781 = true :=
  ⟨ghZoomCert4_2_ok, ghZoomCert8_2_ok, ghZoomCert16_2_ok, ghZoomCert32_2_ok, ghZoomCert64_2_ok,
   ghZoomCert128_2_ok, ghZoomCert256_2_ok, ghZoomCert512_2_ok, ghZoomCert1024_2_ok⟩
end QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
end
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2Base
open scoped NNReal NNRat
/-- Computable cell selector for the `9` certified `k = 2` Gaussian-Hamming Zoom cells. -/
def isGaussianHammingZoomK2BaseCell (m k : ℕ) : Bool :=
  (k == 2) &&
    ((m == 4) || (m == 8) || (m == 16) || (m == 32) || (m == 64) ||
      (m == 128) || (m == 256) || (m == 512) || (m == 1024))
/-- Total qubit count `m * (n + 1) + k * n` matching `DickeSol.Stage1.qubits`. -/
abbrev gaussianHammingZoomK2BaseQubits (n m k : ℕ) : ℕ :=
  m * (n + 1) + k * n
/-- Exact coprime asymptotic relative-cost table across the `9` `k = 2` cells. -/
def relCostGaussianHammingZoomK2Base (m k : ℕ) : ℚ≥0 :=
  if m == 4 && k == 2 then NNRat.divNat 1056718415 1707106781
  else if m == 8 && k == 2 then NNRat.divNat 964679691 1707106781
  else if m == 16 && k == 2 then NNRat.divNat 919068354 1707106781
  else if m == 32 && k == 2 then NNRat.divNat 895547519 1707106781
  else if m == 64 && k == 2 then NNRat.divNat 882938864 1707106781
  else if m == 128 && k == 2 then NNRat.divNat 876003628 1707106781
  else if m == 256 && k == 2 then NNRat.divNat 872162331 1707106781
  else if m == 512 && k == 2 then NNRat.divNat 870037187 1707106781
  else if m == 1024 && k == 2 then NNRat.divNat 868844443 1707106781
  else 1
end QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2Base
end
section
namespace QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2Base
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs
open QuantumComputation.Specs.DickeSol
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
/-- Lookup table activating Gaussian-Hamming Zoom across all `9` `(m, 2)` cells. -/
def ghZoomBaseLookup (m k : ℕ) : Option GHZoomCellCert :=
  if k = 2 then
    if m = 4 then some ghZoomCert4k2
    else if m = 8 then some ghZoomCert8k2
    else if m = 16 then some ghZoomCert16k2
    else if m = 32 then some ghZoomCert32k2
    else if m = 64 then some ghZoomCert64k2
    else if m = 128 then some ghZoomCert128k2
    else if m = 256 then some ghZoomCert256k2
    else if m = 512 then some ghZoomCert512k2
    else if m = 1024 then some ghZoomCert1024k2
    else none
  else
    none
private lemma ghZoomBaseLookup_isSome {m k : ℕ} (h : isGaussianHammingZoomK2BaseCell m k = true) :
    (ghZoomBaseLookup m k).isSome = true := by
  unfold isGaussianHammingZoomK2BaseCell at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ <;>
    simp [ghZoomBaseLookup]
private lemma ghZoom_stage1_cell {m p : ℕ} (hp : p < 11) (hm : 2 ^ p = m) :
    Stage1.cells m 2 = true := by
  simp only [Stage1.cells, gridCells, Bool.and_eq_true, decide_eq_true_eq, groverGrid,
    Finset.mem_image, Finset.mem_range]; exact ⟨⟨p, hp, hm⟩, ⟨1, by omega, rfl⟩⟩
private lemma ghZoomBaseLookup_props {m k : ℕ} {c : GHZoomCellCert}
    (h : ghZoomBaseLookup m k = some c) :
    Stage1.cells m k = true ∧ 2 ≤ m ∧ 2 ≤ k ∧ k = 2 ∧ c.W ≤ 16 ∧
      checkGHZoomSchedule m c.W c.rowSpec c.vSeq c.num c.den = true ∧
      relCostGaussianHammingZoomK2Base m k = (c.num : ℚ≥0) / (c.den : ℚ≥0) := by
  unfold ghZoomBaseLookup at h
  by_cases hk2 : k = 2
  · rw [ite_eq_left hk2] at h; subst hk2
    by_cases hm4 : m = 4
    · rw [ite_eq_left hm4] at h; cases h; subst hm4
      exact ⟨ghZoom_stage1_cell (p := 2) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert4k2]; omega, ghZoomCert4_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert4k2]; simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm4] at h
    by_cases hm8 : m = 8
    · rw [ite_eq_left hm8] at h; cases h; subst hm8
      exact ⟨ghZoom_stage1_cell (p := 3) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert8k2]; omega, ghZoomCert8_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert8k2]; simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm8] at h
    by_cases hm16 : m = 16
    · rw [ite_eq_left hm16] at h; cases h; subst hm16
      exact ⟨ghZoom_stage1_cell (p := 4) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert16k2]; omega, ghZoomCert16_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert16k2]; simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm16] at h
    by_cases hm32 : m = 32
    · rw [ite_eq_left hm32] at h; cases h; subst hm32
      exact ⟨ghZoom_stage1_cell (p := 5) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert32k2]; omega, ghZoomCert32_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert32k2]; simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm32] at h
    by_cases hm64 : m = 64
    · rw [ite_eq_left hm64] at h; cases h; subst hm64
      exact ⟨ghZoom_stage1_cell (p := 6) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert64k2]; omega, ghZoomCert64_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert64k2]; simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm64] at h
    by_cases hm128 : m = 128
    · rw [ite_eq_left hm128] at h; cases h; subst hm128
      exact ⟨ghZoom_stage1_cell (p := 7) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert128k2]; omega, ghZoomCert128_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert128k2]
          simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm128] at h
    by_cases hm256 : m = 256
    · rw [ite_eq_left hm256] at h; cases h; subst hm256
      exact ⟨ghZoom_stage1_cell (p := 8) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert256k2]; omega, ghZoomCert256_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert256k2]
          simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm256] at h
    by_cases hm512 : m = 512
    · rw [ite_eq_left hm512] at h; cases h; subst hm512
      exact ⟨ghZoom_stage1_cell (p := 9) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert512k2]; omega, ghZoomCert512_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert512k2]
          simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm512] at h
    by_cases hm1024 : m = 1024
    · rw [ite_eq_left hm1024] at h; cases h; subst hm1024
      exact ⟨ghZoom_stage1_cell (p := 10) (by omega) (by norm_num), by omega, by omega, rfl,
        by dsimp [ghZoomCert1024k2]; omega, ghZoomCert1024_2_ok, by
          dsimp only [relCostGaussianHammingZoomK2Base, ghZoomCert1024k2]
          simp [NNRat.divNat_eq_div]⟩
    rw [ite_eq_right hm1024] at h
    cases h
  · rw [ite_eq_right hk2] at h; cases h
private lemma ghZoomBase_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S =
      GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle
  rfl
private lemma ghZoomBase_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k :=
  rfl
private lemma ghZoomBase_vanilla_eq (n m k : ℕ) :
    DickeSol.vanillaFindAllCost n m k =
      (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) :=
  rfl
end QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2Base
end
public section
namespace QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2Base
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs
/-- Dynamic circuit dispatching the `9` `k = 2` cells to `DickeSol.ghZoomCertCircuit`. -/
noncomputable def findAllGaussianHammingZoomK2BaseCircuit {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ gaussianHammingZoomK2BaseQubits n m k)) Var
      (gaussianHammingZoomK2BaseQubits n m k) ((n + 1) * m) :=
  match hlook : ghZoomBaseLookup m k with
  | some c =>
      let hv := ghZoomBaseLookup_props hlook
      DickeSol.ghZoomCertCircuit res (DickeSol.Stage1.cells_mem_grid hv.1).1
        (DickeSol.Stage1.cells_mem_grid hv.1).2 hv.2.1 hv.2.2.1 c.W c.rowSpec hv.2.2.2.2.1 n
  | none => .skip
/-- Exact probability-`1` recovery of `S` on every certified `GaussianHammingZoomK2` cell. -/
theorem gaussianHammingZoomK2Base_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isGaussianHammingZoomK2BaseCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ gaussianHammingZoomK2BaseQubits n m k)) ⦄
    (QProg.qSet ;; (findAllGaussianHammingZoomK2BaseCircuit res n m k).compile QProg.qAssign
      (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  cases hlook : ghZoomBaseLookup m k with
  | none =>
      have his := ghZoomBaseLookup_isSome hcell
      rw [hlook] at his; cases his
  | some c =>
      have hv := ghZoomBaseLookup_props hlook
      have hcirc : findAllGaussianHammingZoomK2BaseCircuit (Var := Var) res n m k =
          DickeSol.ghZoomCertCircuit res (DickeSol.Stage1.cells_mem_grid hv.1).1
            (DickeSol.Stage1.cells_mem_grid hv.1).2 hv.2.1 hv.2.2.1 c.W c.rowSpec
            hv.2.2.2.2.1 n := by
        unfold findAllGaussianHammingZoomK2BaseCircuit
        split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [ghZoomBase_targetSets_eq]
      rw [hcirc, ← ghZoomBase_oracle_eq]
      have hcorr :=
        DickeSol.ghZoomCert_correctness res hn hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hkN
          c.W c.rowSpec hv.2.2.2.2.1 hS'
      dsimp only [gaussianHammingZoomK2BaseQubits, DickeSol.Stage1.qubits] at hcorr ⊢
      exact hcorr
/-- Asymptotic uniform-average relative cost bound on every certified
  `GaussianHammingZoomK2` cell. -/
theorem gaussianHammingZoomK2Base_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isGaussianHammingZoomK2BaseCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;; (findAllGaussianHammingZoomK2BaseCircuit res n m k).compile QProg.qAssign
              (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostGaussianHammingZoomK2Base m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  cases hlook : ghZoomBaseLookup m k with
  | none =>
      have his := ghZoomBaseLookup_isSome hcell
      rw [hlook] at his; cases his
  | some c =>
      have hv := ghZoomBaseLookup_props hlook
      have hgrid := DickeSol.Stage1.cells_mem_grid hv.1
      obtain ⟨n₀, hn₀⟩ := DickeSol.ghZoomCert_relCost (Var := Var) res hgrid.1 hgrid.2
        hv.2.1 hv.2.2.1 hv.2.2.2.1 c.W c.rowSpec hv.2.2.2.2.1 c.vSeq c.num c.den
        hv.2.2.2.2.2.1
      refine ⟨n₀, fun n hn hkN ↦ ?_⟩
      have hcirc : findAllGaussianHammingZoomK2BaseCircuit (Var := Var) res n m k =
          DickeSol.ghZoomCertCircuit res hgrid.1 hgrid.2 hv.2.1 hv.2.2.1 c.W c.rowSpec
            hv.2.2.2.2.1 n := by
        unfold findAllGaussianHammingZoomK2BaseCircuit
        split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      obtain ⟨q, hq, hsum⟩ := hn₀ n hn hkN
      refine ⟨q, fun S hS ↦ ?_, ?_⟩
      · rw [hcirc, ← ghZoomBase_oracle_eq]
        have hqS := hq S (by rwa [ghZoomBase_targetSets_eq])
        dsimp only [gaussianHammingZoomK2BaseQubits, DickeSol.Stage1.qubits] at hqS ⊢
        exact hqS
      · rw [← ghZoomBase_targetSets_eq, ← ghZoomBase_vanilla_eq, hv.2.2.2.2.2.2]
        exact hsum
end QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2Base
end
