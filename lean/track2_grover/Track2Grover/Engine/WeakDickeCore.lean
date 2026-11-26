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
public import Track2Grover.FindAllEvaluator

public import Mathlib.Data.Fintype.CardEmbedding
public import QuantumComputation.Maths.Trigonometry
public import Track2Grover.Engine.WeakDickeBase
/-
# Weak-Dicke & Multi-Pulse Core (`WeakDickeCore`)
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

section WD_FindAllVarPhiAnalysis
namespace QuantumComputation.Specs.DickeSol
open Real
@[expose] public section
private lemma varPhi_oddFrac_bounds_n100 {n g r : ℕ} (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024)
    (hr1 : 1 ≤ r) (hr : r ≤ 1024) : (((g : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)) * (1 - 1 / 2 ^ 80) ≤ oddFrac
    n g r ∧ oddFrac n g r ≤ ((g : ℝ) * (r : ℝ)) / (2 ^ n : ℝ) ∧ oddFrac n g r ≤ 1 / 2 ^ 80 ∧ 0 <
    oddFrac n g r := by
  have hg_pos : (0 : ℝ) < g := (by exact_mod_cast hg1)
  have hr_pos : (0 : ℝ) < r := (by exact_mod_cast hr1)
  have hg_le : (g : ℝ) ≤ 1024 := (by exact_mod_cast hg)
  have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr)
  have h2n_ge : (2 ^ 100 : ℝ) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h2n_pos : (0 : ℝ) < 2 ^ n := (by positivity)
  have h2r_le : 2 * r ≤ 2 ^ n := by
    have h100 : 2 * 1024 ≤ 2 ^ 100 := (by norm_num)
    have hpow : 2 ^ 100 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn; omega
  have hr_lt : r < 2 ^ n := (by omega)
  rcases oddFrac_sandwich (m := g) h2r_le with ⟨hlo_sand, hhi_sand⟩
  have hp_pos : 0 < oddFrac n g r := (oddFrac_pos_lt_one hg1 hr1 hr_lt).1
  set p₀ : ℝ := ((g : ℝ) * (r : ℝ)) / (2 ^ n : ℝ); have hp0_nn : 0 ≤ p₀ := (by positivity)
  have hp0_80 : p₀ ≤ 1 / 2 ^ 80 := by
    dsimp only [p₀]; rw [div_le_iff₀ h2n_pos]
    have hgr : (g : ℝ) * (r : ℝ) ≤ 2 ^ 20 := (by nlinarith); nlinarith
  have hlo : p₀ * (1 - 1 / 2 ^ 80) ≤ oddFrac n g r :=
    (mul_le_mul_of_nonneg_left (by linarith) hp0_nn).trans hlo_sand
  exact ⟨hlo, hhi_sand, hhi_sand.trans hp0_80, hp_pos⟩
private lemma varPhi_cos_step_ge {x c c' : ℝ} (hc : 0 ≤ c) (h : c ≤ cos (x / 2))
    (hc' : c' ≤ 2 * c ^ 2 - 1) : c' ≤ cos x := hc'.trans (two_mul_sq_sub_one_le_cos hc h)
private lemma varPhi_cos_step_le {x c c' : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2)
    (h : cos (x / 2) ≤ c) (hc' : 2 * c ^ 2 - 1 ≤ c') : cos x ≤ c' := by
  have hcos : 0 ≤ cos (x / 2) := (by have h1 := one_sub_sq_div_two_le_cos (x := x / 2); nlinarith)
  have hdouble := cos_two_mul (x / 2); rw [show 2 * (x / 2) = x by ring] at hdouble
  nlinarith [pow_le_pow_left₀ hcos h 2]
/-- Target phase palette `Φ ∈ [3/64, 3/2]` (`44` rational angles: `0..27` dyadic + `28..43`
  fine-grid `m = 2` multi-hit optimal phases). -/
noncomputable def varPhi (idx : Fin 44) : ℝ :=
  match idx.val with
  | 0 => 3/2
  | 1 => 11/8
  | 2 => 5/4
  | 3 => 19/16
  | 4 => 7/6
  | 5 => 9/8
  | 6 => 17/16
  | 7 => 1
  | 8 => 15/16
  | 9 => 7/8
  | 10 => 13/16
  | 11 => 3/4
  | 12 => 11/16
  | 13 => 5/8
  | 14 => 9/16
  | 15 => 1/2
  | 16 => 7/16
  | 17 => 3/8
  | 18 => 5/16
  | 19 => 1/4
  | 20 => 7/32
  | 21 => 3/16
  | 22 => 5/32
  | 23 => 1/8
  | 24 => 3/32
  | 25 => 5/64
  | 26 => 1/16
  | 27 => 3/64
  | 28 => 11069/10000
  | 29 => 2839/2500
  | 30 => 11383/10000
  | 31 => 11467/10000
  | 32 => 1439/1250
  | 33 => 2883/2500
  | 34 => 11549/10000
  | 35 => 5783/5000
  | 36 => 11579/10000
  | 37 => 2899/2500
  | 38 => 11611/10000
  | 39 => 1453/1250
  | 40 => 2327/2000
  | 41 => 2911/2500
  | 42 => 11651/10000
  | _ => 5827/5000
/-- Numerators (over `10 ^ 8`) of certified lower bounds `sin_lo` on `sin Φ` for `varPhi`. -/
def varPhiSinLoNum (idx : Fin 44) : ℕ :=
  match idx.val with
  | 0 => 99749498
  | 1 => 98089305
  | 2 => 94898461
  | 3 => 92743691
  | 4 => 91944497
  | 5 => 90226759
  | 6 => 87357493
  | 7 => 84147098
  | 8 => 80608110
  | 9 => 76754349
  | 10 => 72600864
  | 11 => 68163874
  | 12 => 63460705
  | 13 => 58509724
  | 14 => 53330263
  | 15 => 47942549
  | 16 => 42367620
  | 17 => 36627246
  | 18 => 30743843
  | 19 => 24740387
  | 20 => 21700948
  | 21 => 18640319
  | 22 => 15561488
  | 23 => 12467461
  | 24 => 9361260
  | 25 => 7804541
  | 26 => 6245918
  | 27 => 4685769
  | 28 => 89431593
  | 29 => 90678728
  | 30 => 90792227
  | 31 => 91141096
  | 32 => 91325346
  | 33 => 91406642
  | 34 => 91475456
  | 35 => 91544005
  | 36 => 91596247
  | 37 => 91664329
  | 38 => 91724182
  | 39 => 91775888
  | 40 => 91819517
  | 41 => 91855132
  | 42 => 91882780
  | _ => 91894616
/-- Numerators (over `10 ^ 8`) of certified upper bounds `sin_hi` on `sin Φ` for `varPhi`. -/
def varPhiSinHiNum (idx : Fin 44) : ℕ :=
  match idx.val with
  | 0 => 99749499
  | 1 => 98089306
  | 2 => 94898462
  | 3 => 92743692
  | 4 => 91944498
  | 5 => 90226760
  | 6 => 87357494
  | 7 => 84147099
  | 8 => 80608111
  | 9 => 76754351
  | 10 => 72600866
  | 11 => 68163877
  | 12 => 63460709
  | 13 => 58509728
  | 14 => 53330268
  | 15 => 47942554
  | 16 => 42367626
  | 17 => 36627253
  | 18 => 30743852
  | 19 => 24740396
  | 20 => 21700959
  | 21 => 18640330
  | 22 => 15561500
  | 23 => 12467474
  | 24 => 9361274
  | 25 => 7804556
  | 26 => 6245932
  | 27 => 4685784
  | 28 => 89431594
  | 29 => 90678730
  | 30 => 90792228
  | 31 => 91141097
  | 32 => 91325347
  | 33 => 91406643
  | 34 => 91475457
  | 35 => 91544006
  | 36 => 91596248
  | 37 => 91664330
  | 38 => 91724183
  | 39 => 91775889
  | 40 => 91819518
  | 41 => 91855133
  | 42 => 91882781
  | _ => 91894617
/-- Numerators (over `10 ^ 8`) of certified query-cost prefactors `c_hi` relative to
  `(π / 4) * √(2 ^ n / (g * r))` for `K_varPhi + 1`. -/
def varPhiCHiNum (idx : Fin 44) : ℕ :=
  match idx.val with
  | 0 => 95492966
  | 1 => 87535219
  | 2 => 79577472
  | 3 => 75598598
  | 4 => 74272307
  | 5 => 71619725
  | 6 => 67640851
  | 7 => 63661978
  | 8 => 59683104
  | 9 => 55704231
  | 10 => 51725357
  | 11 => 47746483
  | 12 => 43767610
  | 13 => 39788736
  | 14 => 35809863
  | 15 => 31830989
  | 16 => 27852116
  | 17 => 23873242
  | 18 => 19894368
  | 19 => 15915495
  | 20 => 13926058
  | 21 => 11936621
  | 22 => 9947184
  | 23 => 7957748
  | 24 => 5968311
  | 25 => 4973592
  | 26 => 3978874
  | 27 => 2984156
  | 28 => 70467443
  | 29 => 72294542
  | 30 => 72466429
  | 31 => 73001190
  | 32 => 73287669
  | 33 => 73414993
  | 34 => 73523218
  | 35 => 73631443
  | 36 => 73714204
  | 37 => 73822429
  | 38 => 73917922
  | 39 => 74000683
  | 40 => 74070711
  | 41 => 74128007
  | 42 => 74172570
  | _ => 74191669
/-- Certified rational lower bound `sin_lo` on `sin Φ` for palette index `idx`. -/
noncomputable def varPhiSinLo (idx : Fin 44) : ℝ := (varPhiSinLoNum idx : ℝ) / 100000000
/-- Certified rational upper bound `sin_hi` on `sin Φ` for palette index `idx`. -/
noncomputable def varPhiSinHi (idx : Fin 44) : ℝ := (varPhiSinHiNum idx : ℝ) / 100000000
/-- Certified rational query-cost prefactor `c_hi` for palette index `idx`. -/
noncomputable def varPhiCHi (idx : Fin 44) : ℝ := (varPhiCHiNum idx : ℝ) / 100000000
/-- Single-group projective Grover iteration count stopping near target phase `varPhi idx`
  for
  slot-group size `g` and `r` remaining unmarked targets on `n`-bit addresses. -/
noncomputable def K_varPhi (idx : Fin 44) (n g r : ℕ) : ℕ :=
  Int.toNat (round (varPhi idx / (2 * arcsin (√(oddFrac n g r)))))
private lemma varPhiGroupSuccProb_of_cert {idx : Fin 44} {n g r : ℕ} (hn : 100 ≤ n) (hg1 : 1 ≤ g)
    (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) {d_lo d_hi l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 u0 u1 u2
    u3 u4 u5 u6 u7 u8 u9 : ℝ} (hcert : 0 ≤ varPhi idx ∧ 0 < d_lo ∧ d_lo ≤ 2 ∧ d_lo ≤
    314159265358979323846 / 100000000000000000000 / 2 - (varPhi idx + 1 / 100000000000) ∧
    314159265358979323847 / 100000000000000000000 / 2 - varPhi idx ≤ d_hi ∧ d_hi ≤ 3 ∧ 0 ≤ d_lo /
    2048 - (d_lo / 2048) ^ 3 / 6 ∧ 0 < varPhiSinLo idx ∧ 0 ≤ l0 ∧ l0 ≤ 1 - (d_hi / 1024) ^ 2 / 2 ∧ 0
    ≤ l1 ∧ l1 ≤ 2 * l0 ^ 2 - 1 ∧ 0 ≤ l2 ∧ l2 ≤ 2 * l1 ^ 2 - 1 ∧ 0 ≤ l3 ∧ l3 ≤ 2 * l2 ^ 2 - 1 ∧ 0 ≤
    l4 ∧ l4 ≤ 2 * l3 ^ 2 - 1 ∧ 0 ≤ l5 ∧ l5 ≤ 2 * l4 ^ 2 - 1 ∧ 0 ≤ l6 ∧ l6 ≤ 2 * l5 ^ 2 - 1 ∧ 0 ≤ l7
    ∧ l7 ≤ 2 * l6 ^ 2 - 1 ∧ 0 ≤ l8 ∧ l8 ≤ 2 * l7 ^ 2 - 1 ∧ 0 ≤ l9 ∧ l9 ≤ 2 * l8 ^ 2 - 1 ∧
    varPhiSinLo idx ≤ 2 * l9 ^ 2 - 1 ∧ 1 - 2 * (d_lo / 2048 - (d_lo / 2048) ^ 3 / 6) ^ 2 ≤ u0 ∧ 2 *
    u0 ^ 2 - 1 ≤ u1 ∧ 2 * u1 ^ 2 - 1 ≤ u2 ∧ 2 * u2 ^ 2 - 1 ≤ u3 ∧ 2 * u3 ^ 2 - 1 ≤ u4 ∧ 2 * u4 ^ 2 -
    1 ≤ u5 ∧ 2 * u5 ^ 2 - 1 ≤ u6 ∧ 2 * u6 ^ 2 - 1 ≤ u7 ∧ 2 * u7 ^ 2 - 1 ≤ u8 ∧ 2 * u8 ^ 2 - 1 ≤ u9 ∧
    2 * u9 ^ 2 - 1 ≤ varPhiSinHi idx) : 0 < sin ((2 * (K_varPhi idx n g r : ℝ) + 1) * arcsin
    (√(oddFrac n g r))) ^ 2 ∧ varPhiSinLo idx ^ 2 ≤ sin ((2 * (K_varPhi idx n g r : ℝ) + 1) * arcsin
    (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi idx n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^
    2 ≤ varPhiSinHi idx ^ 2 := by
  rcases hcert with
    ⟨hφ0, hd_lo_pos, hd_lo_le2, hd_lo_pi, hd_hi_pi, hd_hi_le3, hz_nn, hsin_lo_pos,
      hl0_nn, hl0, hl1_nn, hl1, hl2_nn, hl2, hl3_nn, hl3, hl4_nn, hl4,
      hl5_nn, hl5, hl6_nn, hl6, hl7_nn, hl7, hl8_nn, hl8, hl9_nn, hl9, hl10,
      hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, hu10⟩
  obtain ⟨_, _, hp_80, hp_pos⟩ := varPhi_oddFrac_bounds_n100 hn hg1 hg hr1 hr
  set p := oddFrac n g r; set c := 1 / p
  have hc_ge : (2 ^ 80 : ℝ) ≤ c := by
    dsimp only [c]; rw [le_one_div (by norm_num) hp_pos]; exact hp_80
  have hc_pos : 0 < c := lt_of_lt_of_le (by norm_num) hc_ge
  have hsqrt_eq : √p = 1 / √c := (by simp only [c, one_div, sqrt_inv, inv_inv])
  set θ := arcsin (√p); have hθ_pos : 0 < θ := arcsin_pos.2 (sqrt_pos.2 hp_pos)
  have hθ_le : θ ≤ 1 / 200000000000 := by
    dsimp only [θ]; rw [hsqrt_eq]
    refine arcsin_one_div_sqrt_le hc_pos (by norm_num) (by norm_num) ?_
    have h80 : (1 : ℝ) ≤
        (2 ^ 80 : ℝ) * ((1 / 200000000000 : ℝ) - (1 / 200000000000 : ℝ) ^ 3 / 6) ^ 2 := by
      norm_num
    have hsq_nn : 0 ≤ ((1 / 200000000000 : ℝ) - (1 / 200000000000 : ℝ) ^ 3 / 6) ^ 2 := sq_nonneg _
    exact h80.trans (mul_le_mul_of_nonneg_right hc_ge hsq_nn)
  obtain ⟨hΦ0, hΦ1⟩ := odd_round_div_sub_mem_Icc hθ_pos hφ0
  set Φ := (2 * (K_varPhi idx n g r : ℝ) + 1) * θ
  have hΦ_lo : varPhi idx ≤ Φ := (by dsimp only [Φ, K_varPhi, θ] at hΦ0 ⊢; linarith)
  have hΦ_hi : Φ ≤ varPhi idx + 1 / 100000000000 := by
    dsimp only [Φ, K_varPhi, θ] at hΦ1 ⊢; linarith
  set δ := π / 2 - Φ; have hd_lo : d_lo ≤ δ := (by dsimp only [δ]; linarith [pi_gt_d20])
  have hd_hi : δ ≤ d_hi := (by dsimp only [δ]; linarith [pi_lt_d20])
  have hcos_ge : cos d_hi ≤ sin Φ := by
    rw [← cos_pi_div_two_sub Φ]
    exact cos_le_cos_of_nonneg_of_le_pi (by dsimp only [δ] at hd_lo; linarith)
      (by linarith [pi_gt_three]) hd_hi
  have hcos_le : sin Φ ≤ cos d_lo := by
    rw [← cos_pi_div_two_sub Φ]; exact cos_le_cos_of_nonneg_of_le_pi hd_lo_pos.le
      (by dsimp only [δ] at hd_hi; linarith [pi_gt_three]) hd_lo
  have c0 : l0 ≤ cos (d_hi / 1024) := hl0.trans (one_sub_sq_div_two_le_cos (x := d_hi / 1024))
  have c1 : l1 ≤ cos (d_hi / 512) :=
    varPhi_cos_step_ge hl0_nn (by rwa [show d_hi / 512 / 2 = d_hi / 1024 by ring]) hl1
  have c2 : l2 ≤ cos (d_hi / 256) :=
    varPhi_cos_step_ge hl1_nn (by rwa [show d_hi / 256 / 2 = d_hi / 512 by ring]) hl2
  have c3 : l3 ≤ cos (d_hi / 128) :=
    varPhi_cos_step_ge hl2_nn (by rwa [show d_hi / 128 / 2 = d_hi / 256 by ring]) hl3
  have c4 : l4 ≤ cos (d_hi / 64) :=
    varPhi_cos_step_ge hl3_nn (by rwa [show d_hi / 64 / 2 = d_hi / 128 by ring]) hl4
  have c5 : l5 ≤ cos (d_hi / 32) :=
    varPhi_cos_step_ge hl4_nn (by rwa [show d_hi / 32 / 2 = d_hi / 64 by ring]) hl5
  have c6 : l6 ≤ cos (d_hi / 16) :=
    varPhi_cos_step_ge hl5_nn (by rwa [show d_hi / 16 / 2 = d_hi / 32 by ring]) hl6
  have c7 : l7 ≤ cos (d_hi / 8) :=
    varPhi_cos_step_ge hl6_nn (by rwa [show d_hi / 8 / 2 = d_hi / 16 by ring]) hl7
  have c8 : l8 ≤ cos (d_hi / 4) :=
    varPhi_cos_step_ge hl7_nn (by rwa [show d_hi / 4 / 2 = d_hi / 8 by ring]) hl8
  have c9 : l9 ≤ cos (d_hi / 2) :=
    varPhi_cos_step_ge hl8_nn (by rwa [show d_hi / 2 / 2 = d_hi / 4 by ring]) hl9
  have c10 : varPhiSinLo idx ≤ cos d_hi := varPhi_cos_step_ge hl9_nn c9 hl10
  have d0 : cos (d_lo / 1024) ≤ u0 := by
    set z : ℝ := d_lo / 2048; have hz_pos : 0 < z := (by dsimp only [z]; linarith)
    have hsin_gt := sin_gt_sub_cube hz_pos
    have hsin_sq : (z - z ^ 3 / 6) ^ 2 ≤ sin z ^ 2 := pow_le_pow_left₀ hz_nn hsin_gt.le 2
    have h2z : 2 * z = d_lo / 1024 := (by dsimp only [z]; ring); have hcd := cos_two_mul z
    have hsc := sin_sq_add_cos_sq z; rw [← h2z]
    have hcos_eq : cos (2 * z) = 1 - 2 * sin z ^ 2 := (by linarith)
    have hcos_2z : cos (2 * z) ≤ 1 - 2 * (z - z ^ 3 / 6) ^ 2 := by
      rw [hcos_eq]; exact sub_le_sub_left (mul_le_mul_of_nonneg_left hsin_sq (by norm_num)) 1
    exact hcos_2z.trans hu0
  have d1 : cos (d_lo / 512) ≤ u1 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 512 / 2 = d_lo / 1024 by ring]) hu1
  have d2 : cos (d_lo / 256) ≤ u2 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 256 / 2 = d_lo / 512 by ring]) hu2
  have d3 : cos (d_lo / 128) ≤ u3 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 128 / 2 = d_lo / 256 by ring]) hu3
  have d4 : cos (d_lo / 64) ≤ u4 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 64 / 2 = d_lo / 128 by ring]) hu4
  have d5 : cos (d_lo / 32) ≤ u5 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 32 / 2 = d_lo / 64 by ring]) hu5
  have d6 : cos (d_lo / 16) ≤ u6 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 16 / 2 = d_lo / 32 by ring]) hu6
  have d7 : cos (d_lo / 8) ≤ u7 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 8 / 2 = d_lo / 16 by ring]) hu7
  have d8 : cos (d_lo / 4) ≤ u8 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 4 / 2 = d_lo / 8 by ring]) hu8
  have d9 : cos (d_lo / 2) ≤ u9 :=
    varPhi_cos_step_le (by linarith) (by linarith)
      (by rwa [show d_lo / 2 / 2 = d_lo / 4 by ring]) hu9
  have d10 : cos d_lo ≤ varPhiSinHi idx := varPhi_cos_step_le hd_lo_pos.le hd_lo_le2 d9 hu10
  have hsin_lo : varPhiSinLo idx ≤ sin Φ := c10.trans hcos_ge
  have hsin_hi : sin Φ ≤ varPhiSinHi idx := hcos_le.trans d10
  have hsq_lo : varPhiSinLo idx ^ 2 ≤ sin Φ ^ 2 := pow_le_pow_left₀ hsin_lo_pos.le hsin_lo 2
  have hsq_hi : sin Φ ^ 2 ≤ varPhiSinHi idx ^ 2 :=
    pow_le_pow_left₀ (hsin_lo_pos.le.trans hsin_lo) hsin_hi 2
  have hsq_pos : 0 < sin Φ ^ 2 := lt_of_lt_of_le (pow_pos hsin_lo_pos 2) hsq_lo
  exact ⟨hsq_pos, hsq_lo, hsq_hi⟩
private lemma varPhiGroupSuccProb_bounds_0 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨0, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨0, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨0, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨0, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨0, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 553096303 / 7812500000) (d_hi := 14159265359 / 200000000000)
    (l0 := 9999999976100349 / 10000000000000000) (l1 := 2499999976100349 / 2500000000000000)
    (l2 := 1999999923521117 / 2000000000000000) (l3 := 9999998470422369 / 10000000000000000)
    (l4 := 9999993881689943 / 10000000000000000) (l5 := 4999987763383629 / 5000000000000000)
    (l6 := 9999902107188819 / 10000000000000000) (l7 := 2499902107667969 / 2500000000000000)
    (l8 := 9998433753352811 / 10000000000000000) (l9 := 1998747100807391 / 2000000000000000)
    (u0 := 199999999522007 / 200000000000000) (u1 := 9999999904401401 / 10000000000000000)
    (u2 := 4999999808802803 / 5000000000000000) (u3 := 4999999235211227 / 5000000000000000)
    (u4 := 2499998470422571 / 2500000000000000) (u5 := 9999975526768623 / 10000000000000000)
    (u6 := 249997552679857 / 250000000000000) (u7 := 9999608430693721 / 10000000000000000)
    (u8 := 9998433753440189 / 10000000000000000) (u9 := 4996867752193207 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_1 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨1, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨1, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨1, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨1, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨1, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 1529658803 / 7812500000) (d_hi := 39159265359 / 200000000000)
    (l0 := 1999999963439749 / 2000000000000000) (l1 := 4999999634397493 / 5000000000000000)
    (l2 := 199999941503601 / 200000000000000) (l3 := 999998830072191 / 1000000000000000)
    (l4 := 4999976601457507 / 5000000000000000) (l5 := 9999812812098049 / 10000000000000000)
    (l6 := 4999625627700029 / 5000000000000000) (l7 := 9997005133723927 / 10000000000000000)
    (l8 := 998802232874051 / 1000000000000000) (l9 := 49760590039419 / 50000000000000)
    (u0 := 9999999817198747 / 10000000000000000) (u1 := 1999999853758999 / 2000000000000000)
    (u2 := 9999997075180087 / 10000000000000000) (u3 := 9999988300722059 / 10000000000000000)
    (u4 := 9999953202915611 / 10000000000000000) (u5 := 4999906406050219 / 5000000000000000)
    (u6 := 4999625627704807 / 5000000000000000) (u7 := 9997005133762149 / 10000000000000000)
    (u8 := 9988022328893353 / 10000000000000000) (u9 := 248802950212361 / 250000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_2 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨2, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨2, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨2, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨2, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨2, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 2506221303 / 7812500000) (d_hi := 64159265359 / 200000000000)
    (l0 := 9999999509285529 / 10000000000000000) (l1 := 2499999509285541 / 2500000000000000)
    (l2 := 4999996074284713 / 5000000000000000) (l3 := 624998037143127 / 625000000000000)
    (l4 := 9999874377357391 / 10000000000000000) (l5 := 9999497512585773 / 10000000000000000)
    (l6 := 2499497525210453 / 2500000000000000) (l7 := 9991961211306173 / 10000000000000000)
    (l8 := 622991110603089 / 625000000000000) (l9 := 9871637703192077 / 10000000000000000)
    (u0 := 4999999754642767 / 5000000000000000) (u1 := 1999999607428437 / 2000000000000000)
    (u2 := 9999992148569511 / 10000000000000000) (u3 := 9999968594290373 / 10000000000000000)
    (u4 := 2499968594339689 / 2500000000000000) (u5 := 4999748756295617 / 5000000000000000)
    (u6 := 1249748762607957 / 1250000000000000) (u7 := 2497990302848383 / 2500000000000000)
    (u8 := 498392888499929 / 500000000000000) (u9 := 9871637704584213 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_3 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨3, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨3, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨3, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨3, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨3, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 2994502553 / 7812500000) (d_hi := 76659265359 / 200000000000)
    (l0 := 9999999299449567 / 10000000000000000) (l1 := 4999998598899183 / 5000000000000000)
    (l2 := 4999994395597517 / 5000000000000000) (l3 := 9999955164805263 / 10000000000000000)
    (l4 := 999982065962309 / 1000000000000000) (l5 := 4999641322462477 / 5000000000000000)
    (l6 := 2499282670654869 / 2500000000000000) (l7 := 199770487541487 / 200000000000000)
    (l8 := 4977061923140853 / 5000000000000000) (l9 := 490845815471141 / 500000000000000)
    (u0 := 1249999912431197 / 1250000000000000) (u1 := 9999997197798403 / 10000000000000000)
    (u2 := 9999988791195183 / 10000000000000000) (u3 := 499997758240293 / 500000000000000)
    (u4 := 9999820659625479 / 10000000000000000) (u5 := 999928264493451 / 1000000000000000)
    (u6 := 4998565341328849 / 5000000000000000) (u7 := 1997704875445439 / 2000000000000000)
    (u8 := 1990824769378477 / 2000000000000000) (u9 := 9816916311854331 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_4 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨4, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨4, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨4, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨4, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨4, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 202064830059 / 500000000000) (d_hi := 404129660129 / 1000000000000)
    (l0 := 9999999221225823 / 10000000000000000) (l1 := 9999996884903413 / 10000000000000000)
    (l2 := 1249998442451949 / 1250000000000000) (l3 := 499997507924671 / 500000000000000)
    (l4 := 1999960126894103 / 2000000000000000) (l5 := 4999601272915691 / 5000000000000000)
    (l6 := 4998405155256079 / 5000000000000000) (l7 := 9987243276872437 / 10000000000000000)
    (l8 := 4974502827143369 / 5000000000000000) (l9 := 1224567837725737 / 1250000000000000)
    (u0 := 4999999610612917 / 5000000000000000) (u1 := 4999998442451729 / 5000000000000000)
    (u2 := 9999987539615773 / 10000000000000000) (u3 := 1999990031698829 / 2000000000000000)
    (u4 := 1249975079309177 / 1250000000000000) (u5 := 9999202545842987 / 10000000000000000)
    (u6 := 399872412422343 / 400000000000000) (u7 := 9987243277058047 / 10000000000000000)
    (u8 := 1243625706878529 / 1250000000000000) (u9 := 2449135676189187 / 2500000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_5 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨5, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨5, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨5, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨5, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨5, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3482783803 / 7812500000) (d_hi := 89159265359 / 200000000000)
    (l0 := 9999999052360701 / 10000000000000000) (l1 := 9999996209442983 / 10000000000000000)
    (l2 := 1999996967554961 / 2000000000000000) (l3 := 4999969675572599 / 5000000000000000)
    (l4 := 312492418916139 / 312500000000000) (l5 := 2499757408259057 / 2500000000000000)
    (l6 := 249902968011683 / 250000000000000) (l7 := 4992238947367721 / 5000000000000000)
    (l8 := 1242244970761517 / 1250000000000000) (l9 := 2438152215623303 / 2500000000000000)
    (u0 := 9999999052360717 / 10000000000000000) (u1 := 1249999526180381 / 1250000000000000)
    (u2 := 4999992418887533 / 5000000000000000) (u3 := 9999939351146243 / 10000000000000000)
    (u4 := 9999757405320629 / 10000000000000000) (u5 := 1249878704131619 / 1250000000000000)
    (u6 := 9996118720534211 / 10000000000000000) (u7 := 9984477895002903 / 10000000000000000)
    (u8 := 9937959767160321 / 10000000000000000) (u9 := 1950521773347889 / 2000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_6 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨6, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨6, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨6, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨6, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨6, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3971065053 / 7812500000) (d_hi := 101659265359 / 200000000000)
    (l0 := 9999998768018933 / 10000000000000000) (l1 := 1999999014415207 / 2000000000000000)
    (l2 := 2499995072077249 / 2500000000000000) (l3 := 4999960576656847 / 5000000000000000)
    (l4 := 1999936922899627 / 2000000000000000) (l5 := 4999369238943071 / 5000000000000000)
    (l6 := 624684639364511 / 625000000000000) (l7 := 9979822011288021 / 10000000000000000)
    (l8 := 619960592212361 / 625000000000000) (l9 := 9678778157890629 / 10000000000000000)
    (u0 := 9999998768018959 / 10000000000000000) (u1 := 499999753603807 / 500000000000000)
    (u2 := 9999980288309417 / 10000000000000000) (u3 := 9999921153315379 / 10000000000000000)
    (u4 := 2499921153626219 / 2500000000000000) (u5 := 9998738477913107 / 10000000000000000)
    (u6 := 1249369278742503 / 1250000000000000) (u7 := 2494955502929799 / 2500000000000000)
    (u8 := 9919369477118997 / 10000000000000000) (u9 := 9678778164720001 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_7 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨7, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨7, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨7, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨7, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨7, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 4459346303 / 7812500000) (d_hi := 114159265359 / 200000000000)
    (l0 := 9999998446424261 / 10000000000000000) (l1 := 4999996892848763 / 5000000000000000)
    (l2 := 9999975142797827 / 10000000000000000) (l3 := 2499975142828721 / 2500000000000000)
    (l4 := 2499900571809187 / 2500000000000000) (l5 := 31245028689319 / 31250000000000)
    (l6 := 2498409307117401 / 2500000000000000) (l7 := 398982280434029 / 400000000000000)
    (l8 := 989835751254227 / 1000000000000000) (l9 := 4797748144610199 / 5000000000000000)
    (u0 := 4999999223212151 / 5000000000000000) (u1 := 9999993785697691 / 10000000000000000)
    (u2 := 1249996892849811 / 1250000000000000) (u3 := 9999900571317529 / 10000000000000000)
    (u4 := 9999602287247329 / 10000000000000000) (u5 := 9998409180624403 / 10000000000000000)
    (u6 := 999363722863887 / 1000000000000000) (u7 := 9974557011527359 / 10000000000000000)
    (u8 := 30932367235131 / 31250000000000) (u9 := 239887407497731 / 250000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_8 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨8, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨8, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨8, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨8, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨8, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 4947627553 / 7812500000) (d_hi := 126659265359 / 200000000000)
    (l0 := 9999998087576687 / 10000000000000000) (l1 := 9999992350307479 / 10000000000000000)
    (l2 := 9999969401241619 / 10000000000000000) (l3 := 2499969401288433 / 2500000000000000)
    (l4 := 9999510423611027 / 10000000000000000) (l5 := 2499510435595279 / 2500000000000000)
    (l6 := 2498041934119761 / 2500000000000000) (l7 := 2492170803696637 / 2500000000000000)
    (l8 := 9874929007353413 / 10000000000000000) (l9 := 2375711145013493 / 2500000000000000)
    (u0 := 9999998087576749 / 10000000000000000) (u1 := 624999521894233 / 625000000000000)
    (u2 := 1249996175155327 / 1250000000000000) (u3 := 9999877605157721 / 10000000000000000)
    (u4 := 1249938802953373 / 1250000000000000) (u5 := 4999020871222471 / 5000000000000000)
    (u6 := 9992167736734299 / 10000000000000000) (u7 := 9968683215806769 / 10000000000000000)
    (u8 := 4937464505710759 / 5000000000000000) (u9 := 1187855574515359 / 1250000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_9 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨9, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨9, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨9, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨9, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨9, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 5435908803 / 7812500000) (d_hi := 139159265359 / 200000000000)
    (l0 := 9999997691476209 / 10000000000000000) (l1 := 9999990765905901 / 10000000000000000)
    (l2 := 9999963063640657 / 10000000000000000) (l3 := 4999926127417743 / 5000000000000000)
    (l4 := 999940902370767 / 1000000000000000) (l5 := 399905446587251 / 400000000000000)
    (l6 := 4995272888134291 / 5000000000000000) (l7 := 24905502453859 / 25000000000000)
    (l8 := 9849089679333653 / 10000000000000000) (l9 := 1880182700462267 / 2000000000000000)
    (u0 := 9999997691476299 / 10000000000000000) (u1 := 4999995382953131 / 5000000000000000)
    (u2 := 4999981531821051 / 5000000000000000) (u3 := 9999852254841267 / 10000000000000000)
    (u4 := 1999881804746159 / 2000000000000000) (u5 := 9997636164773771 / 10000000000000000)
    (u6 := 124881822207981 / 125000000000000) (u7 := 4981100491510897 / 5000000000000000)
    (u8 := 123113621065301 / 125000000000000) (u9 := 4700456762758737 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_10 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨10, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨10, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨10, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨10, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨10, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 5924190053 / 7812500000) (d_hi := 151659265359 / 200000000000)
    (l0 := 9999997258122829 / 10000000000000000) (l1 := 9999989032492819 / 10000000000000000)
    (l2 := 9999956129995333 / 10000000000000000) (l3 := 9999824520366247 / 10000000000000000)
    (l4 := 1249912260952951 / 1250000000000000) (l5 := 2499298112257657 / 2500000000000000)
    (l6 := 9988771372591001 / 10000000000000000) (l7 := 4977555353389351 / 5000000000000000)
    (l8 := 9820845836843989 / 10000000000000000) (l9 := 4644901295105591 / 5000000000000000)
    (u0 := 1999999451624591 / 2000000000000000) (u1 := 2499997258123331 / 2500000000000000)
    (u2 := 4999978064998677 / 5000000000000000) (u3 := 2499956130093583 / 2500000000000000)
    (u4 := 2499824521913987 / 2500000000000000) (u5 := 499859622457999 / 500000000000000)
    (u6 := 1248596421638533 / 1250000000000000) (u7 := 9955110708845431 / 10000000000000000)
    (u8 := 2455211461268449 / 2500000000000000) (u9 := 9289802622540649 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_11 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨11, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨11, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨11, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨11, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨11, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 6412471303 / 7812500000) (d_hi := 164159265359 / 200000000000)
    (l0 := 1999999357503309 / 2000000000000000) (l1 := 2499996787517061 / 2500000000000000)
    (l2 := 4999974300153 / 5000000000000) (l3 := 1999958880350477 / 2000000000000000)
    (l4 := 9999177615463667 / 10000000000000000) (l5 := 9996710597117933 / 10000000000000000)
    (l6 := 2496711138126499 / 2500000000000000) (l7 := 9947412823183737 / 10000000000000000)
    (l8 := 611887773435503 / 625000000000000) (l9 := 9169620340728701 / 10000000000000000)
    (u0 := 4999998393758359 / 5000000000000000) (u1 := 9999987150068937 / 10000000000000000)
    (u2 := 9999948600308773 / 10000000000000000) (u3 := 4999897200881739 / 5000000000000000)
    (u4 := 9999177615508039 / 10000000000000000) (u5 := 9996710597295407 / 10000000000000000)
    (u6 := 9986844553215659 / 10000000000000000) (u7 := 310856650813083 / 312500000000000)
    (u8 := 9790204386248093 / 10000000000000000) (u9 := 229240509622557 / 250000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_12 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨12, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨12, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨12, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨12, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨12, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 6900752553 / 7812500000) (d_hi := 176659265359 / 200000000000)
    (l0 := 9999996279657359 / 10000000000000000) (l1 := 2499996279658051 / 2500000000000000)
    (l2 := 9999940474573107 / 10000000000000000) (l3 := 9999761899001083 / 10000000000000000)
    (l4 := 9999047607342749 / 10000000000000000) (l5 := 199923812215627 / 200000000000000)
    (l6 := 9984765345414643 / 10000000000000000) (l7 := 9939107800598639 / 10000000000000000)
    (l8 := 9757172774384143 / 10000000000000000) (l9 := 904048410983663 / 1000000000000000)
    (u0 := 9999996279657591 / 10000000000000000) (u1 := 9999985118633133 / 10000000000000000)
    (u2 := 1249992559322103 / 1250000000000000) (u3 := 624985118688497 / 625000000000000)
    (u4 := 624940475462639 / 625000000000000) (u5 := 9996190611019229 / 10000000000000000)
    (u6 := 4992382673182899 / 5000000000000000) (u7 := 9939107804397463 / 10000000000000000)
    (u8 := 152455824835733 / 156250000000000) (u9 := 4520242084390381 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_13 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨13, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨13, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨13, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨13, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨13, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 7389033803 / 7812500000) (d_hi := 189159265359 / 200000000000)
    (l0 := 999999573454527 / 1000000000000000) (l1 := 4999991469092359 / 5000000000000000)
    (l2 := 9999931752797093 / 10000000000000000) (l3 := 2499931753029977 / 2500000000000000)
    (l4 := 2499727015846027 / 2500000000000000) (l5 := 4997816246000773 / 5000000000000000)
    (l6 := 9982533783031407 / 10000000000000000) (l7 := 4965098072936333 / 5000000000000000)
    (l8 := 972175909910087 / 1000000000000000) (l9 := 8902519996190111 / 10000000000000000)
    (u0 := 4999997867272787 / 5000000000000000) (u1 := 1999996587637187 / 2000000000000000)
    (u2 := 4999965876400981 / 5000000000000000) (u3 := 1999945402427877 / 2000000000000000)
    (u4 := 1999781612692403 / 2000000000000000) (u5 := 9995632492313141 / 10000000000000000)
    (u6 := 9982533784277243 / 10000000000000000) (u7 := 9930196150847307 / 10000000000000000)
    (u8 := 1944351823772107 / 2000000000000000) (u9 := 4451260036514797 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_14 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨14, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨14, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨14, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨14, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨14, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 7877315053 / 7812500000) (d_hi := 201659265359 / 200000000000)
    (l0 := 9999995152180277 / 10000000000000000) (l1 := 624998788045363 / 625000000000000)
    (l2 := 2499980608744609 / 2500000000000000) (l3 := 999968974111701 / 1000000000000000)
    (l4 := 4999379491860077 / 5000000000000000) (l5 := 9995036242904897 / 10000000000000000)
    (l6 := 9980149899396487 / 10000000000000000) (l7 := 9920678402884741 / 10000000000000000)
    (l8 := 9683971994692747 / 10000000000000000) (l9 := 2188965679699671 / 2500000000000000)
    (u0 := 999999515218067 / 1000000000000000) (u1 := 9999980608727381 / 10000000000000000)
    (u2 := 9999922434984729 / 10000000000000000) (u3 := 9999689741142183 / 10000000000000000)
    (u4 := 2499689745955211 / 2500000000000000) (u5 := 1249379530413451 / 1250000000000000)
    (u6 := 9980149901006533 / 10000000000000000) (u7 := 9920678409312143 / 10000000000000000)
    (u8 := 9683972020198423 / 10000000000000000) (u9 := 4377931408798593 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_15 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨15, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨15, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨15, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨15, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨15, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 8365596303 / 7812500000) (d_hi := 214159265359 / 200000000000)
    (l0 := 4999997266281191 / 5000000000000000) (l1 := 4999989065127753 / 5000000000000000)
    (l2 := 9999912521117681 / 10000000000000000) (l3 := 4999825043000617 / 5000000000000000)
    (l4 := 9998600368492897 / 10000000000000000) (l5 := 9994401865765259 / 10000000000000000)
    (l6 := 4988806865441209 / 5000000000000000) (l7 := 619409697033667 / 625000000000000)
    (l8 := 2410955171575541 / 2500000000000000) (l9 := 2150163871477477 / 2500000000000000)
    (u0 := 9999994532562881 / 10000000000000000) (u1 := 9999978130257503 / 10000000000000000)
    (u2 := 999991252112567 / 1000000000000000) (u3 := 9999650086033191 / 10000000000000000)
    (u4 := 9998600368620721 / 10000000000000000) (u5 := 2498600466569121 / 2500000000000000)
    (u6 := 4988806866463087 / 5000000000000000) (u7 := 9910555160695397 / 10000000000000000)
    (u8 := 4821910359318617 / 5000000000000000) (u9 := 2150163902660839 / 2500000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_16 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨16, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨16, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨16, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨16, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨16, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 8853877553 / 7812500000) (d_hi := 226659265359 / 200000000000)
    (l0 := 9999993875691583 / 10000000000000000) (l1 := 9999975502773833 / 10000000000000000)
    (l2 := 4999951005607677 / 5000000000000000) (l3 := 624975502923861 / 625000000000000)
    (l4 := 9998432217852569 / 10000000000000000) (l5 := 624608085187403 / 625000000000000)
    (l6 := 9974925316171473 / 10000000000000000) (l7 := 309369594144991 / 312500000000000)
    (l8 := 1200164372004773 / 1250000000000000) (l9 := 4218524926909511 / 5000000000000000)
    (u0 := 999999387569221 / 1000000000000000) (u1 := 4999987751388171 / 5000000000000000)
    (u2 := 9999902011225391 / 10000000000000000) (u3 := 2499902011705481 / 2500000000000000)
    (u4 := 1999686443602631 / 2000000000000000) (u5 := 2498432340910173 / 2500000000000000)
    (u6 := 9974925318738839 / 10000000000000000) (u7 := 4949913511441713 / 5000000000000000)
    (u8 := 1200164377075323 / 1250000000000000) (u9 := 1054631251200957 / 1250000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_17 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨17, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨17, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨17, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨17, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨17, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 9342158803 / 7812500000) (d_hi := 239159265359 / 200000000000)
    (l0 := 4999996590783941 / 5000000000000000) (l1 := 4999986363140413 / 5000000000000000)
    (l2 := 399995636210883 / 400000000000000) (l3 := 9999563623468631 / 10000000000000000)
    (l4 := 9998254531959419 / 10000000000000000) (l5 := 2498254684292353 / 2500000000000000)
    (l6 := 9972084696283789 / 10000000000000000) (l7 := 9888494637971469 / 10000000000000000)
    (l8 := 4778232620519049 / 5000000000000000) (l9 := 826520558063387 / 1000000000000000)
    (u0 := 4999996590784329 / 5000000000000000) (u1 := 9999972726283931 / 10000000000000000)
    (u2 := 624993181580281 / 625000000000000) (u3 := 2499890905879579 / 2500000000000000)
    (u4 := 9998254532158151 / 10000000000000000) (u5 := 4996509368982101 / 5000000000000000)
    (u6 := 9972084699460731 / 10000000000000000) (u7 := 2472123662660941 / 2500000000000000)
    (u8 := 2389116322790517 / 2500000000000000) (u9 := 4132602886118531 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_18 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨18, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨18, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨18, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨18, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨18, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 9830440053 / 7812500000) (d_hi := 251659265359 / 200000000000)
    (l0 := 4999996225095639 / 5000000000000000) (l1 := 9999969800776511 / 10000000000000000)
    (l2 := 4999939601644221 / 5000000000000000) (l3 := 9999516816072137 / 10000000000000000)
    (l4 := 9998067310981889 / 10000000000000000) (l5 := 2498067497746231 / 2500000000000000)
    (l6 := 996909191454757 / 1000000000000000) (l7 := 4938279360069773 / 5000000000000000)
    (l8 := 9509282430472901 / 10000000000000000) (l9 := 202132261712503 / 250000000000000)
    (u0 := 9999992450192229 / 10000000000000000) (u1 := 2499992450195079 / 2500000000000000)
    (u2 := 9999879203303663 / 10000000000000000) (u3 := 9999516816133021 / 10000000000000000)
    (u4 := 4999033655612707 / 5000000000000000) (u5 := 2498067497989709 / 2500000000000000)
    (u6 := 623068244902513 / 625000000000000) (u7 := 4938279367830987 / 5000000000000000)
    (u8 := 9509282491796171 / 10000000000000000) (u9 := 8085290701756239 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_19 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨19, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨19, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨19, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨19, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨19, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 10318721303 / 7812500000) (d_hi := 264159265359 / 200000000000)
    (l0 := 9999991681561771 / 10000000000000000) (l1 := 9999966726260923 / 10000000000000000)
    (l2 := 62499168157907 / 62500000000000) (l3 := 9999467624603321 / 10000000000000000)
    (l4 := 2499467638774499 / 2500000000000000) (l5 := 4995741563649551 / 5000000000000000)
    (l6 := 622871688538783 / 625000000000000) (l7 := 123300249845219 / 125000000000000)
    (l8 := 9459778063223587 / 10000000000000000) (l9 := 7897480201089239 / 10000000000000000)
    (u0 := 399999667262517 / 400000000000000) (u1 := 499998336313277 / 500000000000000)
    (u2 := 9999866905283589 / 10000000000000000) (u3 := 9999467624677197 / 10000000000000000)
    (u4 := 1999574111078697 / 2000000000000000) (u5 := 9991483128480807 / 10000000000000000)
    (u6 := 9965947021343323 / 10000000000000000) (u7 := 9864020006444371 / 10000000000000000)
    (u8 := 4729889068753481 / 5000000000000000) (u9 := 3948740241085469 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_20 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨20, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨20, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨20, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨20, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨20, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 1320357741 / 976562500) (d_hi := 270409265359 / 200000000000)
    (l0 := 4999995641638589 / 5000000000000000) (l1 := 2499991283280977 / 2500000000000000)
    (l2 := 9999860532738771 / 10000000000000000) (l3 := 9999442134845307 / 10000000000000000)
    (l4 := 4998884300811967 / 5000000000000000) (l5 := 4995537701161739 / 5000000000000000)
    (l6 := 9964317538982649 / 10000000000000000) (l7 := 4928762401767723 / 5000000000000000)
    (l8 := 4717079525231653 / 5000000000000000) (l9 := 7800671397887741 / 10000000000000000)
    (u0 := 4999995641639223 / 5000000000000000) (u1 := 9999965133128981 / 10000000000000000)
    (u2 := 1249982566594883 / 1250000000000000) (u3 := 9999442134926479 / 10000000000000000)
    (u4 := 1999553720389721 / 2000000000000000) (u5 := 9991075403621873 / 10000000000000000)
    (u6 := 1992863508834319 / 2000000000000000) (u7 := 985752482421717 / 1000000000000000)
    (u8 := 188683182640231 / 200000000000000) (u9 := 1560134341124677 / 2000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_21 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨21, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨21, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨21, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨21, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨21, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 10807002553 / 7812500000) (d_hi := 276659265359 / 200000000000)
    (l0 := 15624985743249 / 15625000000000) (l1 := 999996350273409 / 1000000000000000)
    (l2 := 999985401120277 / 1000000000000000) (l3 := 79995328392589 / 80000000000000)
    (l4 := 2499416066123559 / 2500000000000000) (l5 := 4995329074554507 / 5000000000000000)
    (l6 := 9962650050471669 / 10000000000000000) (l7 := 9850879205632629 / 10000000000000000)
    (l8 := 9407964224793067 / 10000000000000000) (l9 := 3850979085498621 / 5000000000000000)
    (u0 := 9999990875680749 / 10000000000000000) (u1 := 9999963502739647 / 10000000000000000)
    (u2 := 9999854011224999 / 10000000000000000) (u3 := 9999416049162541 / 10000000000000000)
    (u4 := 9997664264849881 / 10000000000000000) (u5 := 9990658150531263 / 10000000000000000)
    (u6 := 1245331257019419 / 1250000000000000) (u7 := 615679951767653 / 625000000000000)
    (u8 := 235199107851033 / 250000000000000) (u9 := 7701958506854993 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_22 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨22, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨22, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨22, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨22, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨22, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 5525571589 / 3906250000) (d_hi := 282909265359 / 200000000000)
    (l0 := 2499997614692079 / 2500000000000000) (l1 := 9999961835091471 / 10000000000000000)
    (l2 := 2499961835164299 / 2500000000000000) (l3 := 4999694683644879 / 5000000000000000)
    (l4 := 9997557543733493 / 10000000000000000) (l5 := 4995115684026247 / 5000000000000000)
    (l6 := 9960944557444001 / 10000000000000000) (l7 := 2461020823823663 / 2500000000000000)
    (l8 := 4690597592469921 / 5000000000000000) (l9 := 1520272923917539 / 2000000000000000)
    (u0 := 1999998091753967 / 2000000000000000) (u1 := 2499990458774387 / 2500000000000000)
    (u2 := 312495229396297 / 312500000000000) (u3 := 999938936738699 / 1000000000000000)
    (u4 := 4998778772061199 / 5000000000000000) (u5 := 1998046273921547 / 2000000000000000)
    (u6 := 9960944563658889 / 10000000000000000) (u7 := 1968816664011423 / 2000000000000000)
    (u8 := 9381195282445343 / 10000000000000000) (u9 := 950170623184369 / 1250000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_23 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨23, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨23, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨23, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨23, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨23, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 11295283803 / 7812500000) (d_hi := 289159265359 / 200000000000)
    (l0 := 9999990032544047 / 10000000000000000) (l1 := 4999980065098029 / 5000000000000000)
    (l2 := 1249980065137769 / 1250000000000000) (l3 := 9999362089495311 / 10000000000000000)
    (l4 := 4998724219683603 / 5000000000000000) (l5 := 2497448764890289 / 2500000000000000)
    (l6 := 311225033325203 / 312500000000000) (l7 := 9837137176222457 / 10000000000000000)
    (l8 := 9353853564763587 / 10000000000000000) (l9 := 1874728825552023 / 2500000000000000)
    (u0 := 1249998754068213 / 1250000000000000) (u1 := 9999960130202687 / 10000000000000000)
    (u2 := 9999840521128669 / 10000000000000000) (u3 := 9999362089601379 / 10000000000000000)
    (u4 := 2499362109947863 / 2500000000000000) (u5 := 2497448765314427 / 2500000000000000)
    (u6 := 9959201073185779 / 10000000000000000) (u7 := 1967427440645791 / 2000000000000000)
    (u8 := 4676926835515119 / 5000000000000000) (u9 := 1874728924952293 / 2500000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_24 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨24, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨24, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨24, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨24, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨24, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 2884856107 / 1953125000) (d_hi := 295409265359 / 200000000000)
    (l0 := 1249998699625819 / 1250000000000000) (l1 := 2499989597011963 / 2500000000000000)
    (l2 := 4999916776268859 / 5000000000000000) (l3 := 9999334215691823 / 10000000000000000)
    (l4 := 9997336951421041 / 10000000000000000) (l5 := 998934922404971 / 1000000000000000)
    (l6 := 2489354896001127 / 2500000000000000) (l7 := 9830040954383301 / 10000000000000000)
    (l8 := 9325941032970591 / 10000000000000000) (l9 := 3697317615044457 / 5000000000000000)
    (u0 := 9999989597008357 / 10000000000000000) (u1 := 9999958388055073 / 10000000000000000)
    (u2 := 9999833552566603 / 10000000000000000) (u3 := 4999667107903681 / 5000000000000000)
    (u4 := 9997336951883167 / 10000000000000000) (u5 := 9989349225897723 / 10000000000000000)
    (u6 := 622338724461793 / 625000000000000) (u7 := 4915020491897127 / 5000000000000000)
    (u8 := 4662970574307471 / 5000000000000000) (u9 := 7394635661485877 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_25 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨25, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨25, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨25, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨25, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨25, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 23322989481 / 15625000000) (d_hi := 298534265359 / 200000000000)
    (l0 := 156249833996021 / 156250000000000) (l1 := 199999150060079 / 200000000000000)
    (l2 := 4999915006188499 / 5000000000000000) (l3 := 199986401105743 / 200000000000000)
    (l4 := 4998640156806781 / 5000000000000000) (l5 := 312160085431033 / 312500000000000)
    (l6 := 9956514598156251 / 10000000000000000) (l7 := 4913218294329853 / 5000000000000000)
    (l8 := 232794280154751 / 250000000000000) (l9 := 3670908299642991 / 5000000000000000)
    (u0 := 9999989375747227 / 10000000000000000) (u1 := 9999957503011483 / 10000000000000000)
    (u2 := 9999830012407131 / 10000000000000000) (u3 := 9999320055407681 / 10000000000000000)
    (u4 := 4998640157047827 / 5000000000000000) (u5 := 99891227357209 / 100000000000000)
    (u6 := 248912865146481 / 250000000000000) (u7 := 2456609154834419 / 2500000000000000)
    (u8 := 9311771326772091 / 10000000000000000) (u9 := 3670908524209487 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_26 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨26, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨26, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨26, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨26, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨26, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 11783565053 / 7812500000) (d_hi := 301659265359 / 200000000000)
    (l0 := 9999989152155831 / 10000000000000000) (l1 := 9999956608646859 / 10000000000000000)
    (l2 := 9999826434963997 / 10000000000000000) (l3 := 1249913218235119 / 1250000000000000)
    (l4 := 2499305769980391 / 2500000000000000) (l5 := 124861173274291 / 125000000000000)
    (l6 := 4977800058516813 / 5000000000000000) (l7 := 9822794738055989 / 10000000000000000)
    (l8 := 1859491858639217 / 2000000000000000) (l9 := 227767183178989 / 312500000000000)
    (u0 := 9999989152157793 / 10000000000000000) (u1 := 2499989152163677 / 2500000000000000)
    (u2 := 4999913217497697 / 5000000000000000) (u3 := 9999305746006539 / 10000000000000000)
    (u4 := 4998611540211939 / 5000000000000000) (u5 := 9988893863951979 / 10000000000000000)
    (u6 := 19911200250119 / 20000000000000) (u7 := 9822794770016947 / 10000000000000000)
    (u8 := 4648729709387229 / 5000000000000000) (u9 := 7288550328751577 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_27 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨27, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨27, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨27, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨27, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨27, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 23811270731 / 15625000000) (d_hi := 304784265359 / 200000000000)
    (l0 := 9999988926238011 / 10000000000000000) (l1 := 9999955704976569 / 10000000000000000)
    (l2 := 1999964564059737 / 2000000000000000) (l3 := 9999291287473269 / 10000000000000000)
    (l4 := 1999433050069553 / 2000000000000000) (l5 := 4994331304276089 / 5000000000000000)
    (l6 := 124433451768721 / 125000000000000) (l7 := 9819115416420627 / 10000000000000000)
    (l8 := 2320751378049461 / 2500000000000000) (l9 := 7234838267899111 / 10000000000000000)
    (u0 := 1249998615780007 / 1250000000000000) (u1 := 39999822819939 / 40000000000000)
    (u2 := 999982282033141 / 1000000000000000) (u3 := 9999291287604167 / 10000000000000000)
    (u4 := 9997165250871321 / 10000000000000000) (u5 := 9988662610645809 / 10000000000000000)
    (u6 := 995467614986271 / 1000000000000000) (u7 := 4909557724864547 / 5000000000000000)
    (u8 := 4641502821510859 / 5000000000000000) (u9 := 7234838753674613 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_28 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨28, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨28, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨28, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨28, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨28, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3624190053 / 7812500000) (d_hi := 92779265359 / 200000000000)
    (l0 := 9999998973847379 / 10000000000000000) (l1 := 4999997947694863 / 5000000000000000)
    (l2 := 9999983581562273 / 10000000000000000) (l3 := 1999986865260601 / 2000000000000000)
    (l4 := 4999868653037313 / 5000000000000000) (l5 := 9998949238100123 / 10000000000000000)
    (l6 := 4997898586610303 / 5000000000000000) (l7 := 9983192225633011 / 10000000000000000)
    (l8 := 4966412701393939 / 5000000000000000) (l9 := 4866102048226817 / 5000000000000000)
    (u0 := 4999999486923699 / 5000000000000000) (u1 := 9999995895389803 / 10000000000000000)
    (u2 := 4999991790781291 / 5000000000000000) (u3 := 4999967163152121 / 5000000000000000)
    (u4 := 399989492243183 / 400000000000000) (u5 := 124986865476499 / 125000000000000)
    (u6 := 4997898586649893 / 5000000000000000) (u7 := 9983192225949599 / 10000000000000000)
    (u8 := 4966412702026051 / 5000000000000000) (u9 := 9732204101476561 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_29 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨29, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨29, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨29, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨29, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨29, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3399971303 / 7812500000) (d_hi := 87039265359 / 200000000000)
    (l0 := 1999999819378049 / 2000000000000000) (l1 := 9999996387561143 / 10000000000000000)
    (l2 := 9999985550247181 / 10000000000000000) (l3 := 9999942201030483 / 10000000000000000)
    (l4 := 2499942201197519 / 2500000000000000) (l5 := 9999075229850549 / 10000000000000000)
    (l6 := 9996301090442161 / 10000000000000000) (l7 := 9985207098155027 / 10000000000000000)
    (l8 := 9940872158609107 / 10000000000000000) (l9 := 9764187854761937 / 10000000000000000)
    (u0 := 9999999096890259 / 10000000000000000) (u1 := 24999990968903 / 25000000000000)
    (u2 := 999998555024741 / 1000000000000000) (u3 := 49999711005157 / 50000000000000)
    (u4 := 1999953760958749 / 2000000000000000) (u5 := 399963009194609 / 400000000000000)
    (u6 := 9996301090500861 / 10000000000000000) (u7 := 9985207098389741 / 10000000000000000)
    (u8 := 397634886381863 / 400000000000000) (u9 := 4882093929244819 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_30 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨30, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨30, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨30, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨30, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨30, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3378877553 / 7812500000) (d_hi := 86499265359 / 200000000000)
    (l0 := 9999999108061443 / 10000000000000000) (l1 := 9999996432245931 / 10000000000000000)
    (l2 := 9999985728986269 / 10000000000000000) (l3 := 624996432249113 / 625000000000000)
    (l4 := 2499942916148737 / 2500000000000000) (l5 := 9999086668807203 / 10000000000000000)
    (l6 := 1999269368412717 / 2000000000000000) (l7 := 9985390037366921 / 10000000000000000)
    (l8 := 9941602839669311 / 10000000000000000) (l9 := 9767093404344181 / 10000000000000000)
    (u0 := 4999999554030729 / 5000000000000000) (u1 := 1249999554030749 / 1250000000000000)
    (u2 := 4999992864493257 / 5000000000000000) (u3 := 9999942915986789 / 10000000000000000)
    (u4 := 9999771664598873 / 10000000000000000) (u5 := 1249885833602863 / 1250000000000000)
    (u6 := 624771677632899 / 625000000000000) (u7 := 4992695018809013 / 5000000000000000)
    (u8 := 1988320568134453 / 2000000000000000) (u9 := 976709340833257 / 1000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_31 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨31, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨31, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨31, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨31, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨31, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3313252553 / 7812500000) (d_hi := 84819265359 / 200000000000)
    (l0 := 9999999142371681 / 10000000000000000) (l1 := 9999996569486871 / 10000000000000000)
    (l2 := 9999986277949837 / 10000000000000000) (l3 := 4999972555918503 / 5000000000000000)
    (l4 := 4999890223975283 / 5000000000000000) (l5 := 2499780450360721 / 2500000000000000)
    (l6 := 9996487360018077 / 10000000000000000) (l7 := 2496487976950059 / 2500000000000000)
    (l8 := 4971923550489917 / 5000000000000000) (l9 := 9776019033533009 / 10000000000000000)
    (u0 := 4999999571185847 / 5000000000000000) (u1 := 2499999142371731 / 2500000000000000)
    (u2 := 199999725559001 / 200000000000000) (u3 := 9999945111837859 / 10000000000000000)
    (u4 := 9999780447953979 / 10000000000000000) (u5 := 9999121801456537 / 10000000000000000)
    (u6 := 1999297472014537 / 2000000000000000) (u7 := 312060997125581 / 312500000000000)
    (u8 := 77686305483219 / 78125000000000) (u9 := 2444004759250553 / 2500000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_32 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨32, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨32, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨32, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨32, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨32, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3278096303 / 7812500000) (d_hi := 83919265359 / 200000000000)
    (l0 := 9999999160475361 / 10000000000000000) (l1 := 624999790118849 / 625000000000000)
    (l2 := 9999986567608591 / 10000000000000000) (l3 := 9999946270470449 / 10000000000000000)
    (l4 := 312493283826849 / 312500000000000) (l5 := 9999140339074581 / 10000000000000000)
    (l6 := 1999312300820341 / 2000000000000000) (l7 := 2496562095264407 / 2500000000000000)
    (l8 := 9945031345635219 / 10000000000000000) (l9 := 978072969313341 / 1000000000000000)
    (u0 := 4999999580237687 / 5000000000000000) (u1 := 9999996641901637 / 10000000000000000)
    (u2 := 2499996641902201 / 2500000000000000) (u3 := 4999973135235651 / 5000000000000000)
    (u4 := 9999785082462581 / 10000000000000000) (u5 := 4999570169544117 / 5000000000000000)
    (u6 := 9996561504156313 / 10000000000000000) (u7 := 4993124190637993 / 5000000000000000)
    (u8 := 9945031346507451 / 10000000000000000) (u9 := 9780729696603161 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_33 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨33, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨33, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨33, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨33, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨33, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3262471303 / 7812500000) (d_hi := 83519265359 / 200000000000)
    (l0 := 2499999792114863 / 2500000000000000) (l1 := 4999998336918973 / 5000000000000000)
    (l2 := 2499996673838499 / 2500000000000000) (l3 := 4999973390725693 / 5000000000000000)
    (l4 := 4999893563185993 / 5000000000000000) (l5 := 499957425727549 / 500000000000000)
    (l6 := 9996594203209413 / 10000000000000000) (l7 := 9986379132728007 / 10000000000000000)
    (l8 := 2486388409129269 / 2500000000000000) (l9 := 4891403713683803 / 5000000000000000)
    (u0 := 1999999833691893 / 2000000000000000) (u1 := 9999996673837999 / 10000000000000000)
    (u2 := 9999986695354209 / 10000000000000000) (u3 := 9999946781452239 / 10000000000000000)
    (u4 := 9999787126375399 / 10000000000000000) (u5 := 9999148514564633 / 10000000000000000)
    (u6 := 4998297101632011 / 5000000000000000) (u7 := 998637913294637 / 1000000000000000)
    (u8 := 9945553637389339 / 10000000000000000) (u9 := 9782807430837663 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_34 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨34, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨34, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨34, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨34, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨34, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3249190053 / 7812500000) (d_hi := 83179265359 / 200000000000)
    (l0 := 9999999175215937 / 10000000000000000) (l1 := 2499999175215971 / 2500000000000000)
    (l2 := 624999175216107 / 625000000000000) (l3 := 9999947213865677 / 10000000000000000)
    (l4 := 9999788856019983 / 10000000000000000) (l5 := 156236803640567 / 156250000000000)
    (l6 := 2499155468660959 / 2500000000000000) (l7 := 1248311222615191 / 1250000000000000)
    (l8 := 9945995628890021 / 10000000000000000) (l9 := 244614145249497 / 250000000000000)
    (u0 := 9999999175215949 / 10000000000000000) (u1 := 9999996700863933 / 10000000000000000)
    (u2 := 9999986803457909 / 10000000000000000) (u3 := 4999973606933233 / 5000000000000000)
    (u4 := 499989442801157 / 500000000000000) (u5 := 2499788858252229 / 2500000000000000)
    (u6 := 1999324374938869 / 2000000000000000) (u7 := 9986489781123497 / 10000000000000000)
    (u8 := 9945995629696807 / 10000000000000000) (u9 := 9784565813189597 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_35 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨35, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨35, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨35, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨35, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨35, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3235908803 / 7812500000) (d_hi := 82839265359 / 200000000000)
    (l0 := 499999959097243 / 500000000000000) (l1 := 9999996727779573 / 10000000000000000)
    (l2 := 9999986911120433 / 10000000000000000) (l3 := 1999989528903199 / 2000000000000000)
    (l4 := 9999790578612199 / 10000000000000000) (l5 := 9999162323220259 / 10000000000000000)
    (l6 := 9996649433221513 / 10000000000000000) (l7 := 9986599978145599 / 10000000000000000)
    (l8 := 1989287164939907 / 2000000000000000) (l9 := 9786317122973263 / 10000000000000000)
    (u0 := 1249999897743109 / 1250000000000000) (u1 := 4999998363889811 / 5000000000000000)
    (u2 := 999998691112063 / 1000000000000000) (u3 := 624996727782299 / 625000000000000)
    (u4 := 2499947644653839 / 2500000000000000) (u5 := 1249895290404111 / 1250000000000000)
    (u6 := 4998324716636013 / 5000000000000000) (u7 := 156040624661681 / 156250000000000)
    (u8 := 4973217912753197 / 5000000000000000) (u9 := 9786317126183413 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_36 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨36, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨36, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨36, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨36, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨36, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3225752553 / 7812500000) (d_hi := 82579265359 / 200000000000)
    (l0 := 9999999187071911 / 10000000000000000) (l1 := 312499898383993 / 312500000000000)
    (l2 := 4999993496576609 / 5000000000000000) (l3 := 9999947972646707 / 10000000000000000)
    (l4 := 9999791891128197 / 10000000000000000) (l5 := 1249895946646831 / 1250000000000000)
    (l6 := 399866817251419 / 400000000000000) (l7 := 1248335492793433 / 1250000000000000)
    (l8 := 9946771232868137 / 10000000000000000) (l9 := 9787651591802623 / 10000000000000000)
    (u0 := 9999999187071923 / 10000000000000000) (u1 := 399999869931513 / 400000000000000)
    (u2 := 1999997398630683 / 2000000000000000) (u3 := 1249993496580937 / 1250000000000000)
    (u4 := 4999895945565677 / 5000000000000000) (u5 := 9999167573187277 / 10000000000000000)
    (u6 := 2499167607833997 / 2500000000000000) (u7 := 199733678850989 / 200000000000000)
    (u8 := 4973385616837503 / 5000000000000000) (u9 := 9787651595012921 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_37 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨37, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨37, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨37, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨37, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨37, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3212471303 / 7812500000) (d_hi := 82239265359 / 200000000000)
    (l0 := 9999999193752197 / 10000000000000000) (l1 := 4999998387504459 / 5000000000000000)
    (l2 := 1249998387504719 / 1250000000000000) (l3 := 9999948400184289 / 10000000000000000)
    (l4 := 312493550039677 / 312500000000000) (l5 := 9999174413598743 / 10000000000000000)
    (l6 := 9996697790713553 / 10000000000000000) (l7 := 4993396671885723 / 5000000000000000)
    (l8 := 9947208258239531 / 10000000000000000) (l9 := 611836901659859 / 625000000000000)
    (u0 := 9999999193752209 / 10000000000000000) (u1 := 9999996775008967 / 10000000000000000)
    (u2 := 9999987100037949 / 10000000000000000) (u3 := 4999974200092539 / 5000000000000000)
    (u4 := 9999793601272821 / 10000000000000000) (u5 := 9999174413611371 / 10000000000000000)
    (u6 := 4998348895382031 / 5000000000000000) (u7 := 1248349167996677 / 1250000000000000)
    (u8 := 1989441651809269 / 2000000000000000) (u9 := 2447347607441991 / 2500000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_38 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨38, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨38, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨38, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨38, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨38, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3200752553 / 7812500000) (d_hi := 81939265359 / 200000000000)
    (l0 := 9999999199623679 / 10000000000000000) (l1 := 2499999199623711 / 2500000000000000)
    (l2 := 399999487759257 / 400000000000000) (l3 := 4999974387979249 / 5000000000000000)
    (l4 := 2499948776089693 / 2500000000000000) (l5 := 2499795106457883 / 2500000000000000)
    (l6 := 9996721837666491 / 10000000000000000) (l7 := 499344474996781 / 500000000000000)
    (l8 := 9947592376784867 / 10000000000000000) (l9 := 9790918818933679 / 10000000000000000)
    (u0 := 999999919962369 / 1000000000000000) (u1 := 9999996798494889 / 10000000000000000)
    (u2 := 4999993596990803 / 5000000000000000) (u3 := 9999948775959223 / 10000000000000000)
    (u4 := 9999795104361673 / 10000000000000000) (u5 := 9999180425843137 / 10000000000000000)
    (u6 := 2499180459428227 / 2500000000000000) (u7 := 9986889500121229 / 10000000000000000)
    (u8 := 9947592377526331 / 10000000000000000) (u9 := 9790918821883993 / 10000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_39 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨39, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨39, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨39, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨39, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨39, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3190596303 / 7812500000) (d_hi := 81679265359 / 200000000000)
    (l0 := 9999999204694939 / 10000000000000000) (l1 := 4999998409389941 / 5000000000000000)
    (l2 := 624999204695097 / 625000000000000) (l3 := 156249204695603 / 156250000000000)
    (l4 := 9999796402592519 / 10000000000000000) (l5 := 1249898202332557 / 1250000000000000)
    (l6 := 9996742607285217 / 10000000000000000) (l7 := 9986972551262327 / 10000000000000000)
    (l8 := 994792414793343 / 1000000000000000) (l9 := 9792238970607411 / 10000000000000000)
    (u0 := 9999999204694951 / 10000000000000000) (u1 := 9999996818779931 / 10000000000000000)
    (u2 := 9999987275121749 / 10000000000000000) (u3 := 9999949100519381 / 10000000000000000)
    (u4 := 2499949100648919 / 2500000000000000) (u5 := 1999837123734617 / 2000000000000000)
    (u6 := 999674260733573 / 1000000000000000) (u7 := 4993486275732157 / 5000000000000000)
    (u8 := 4973962074370163 / 5000000000000000) (u9 := 2448059743454547 / 2500000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_40 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨40, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨40, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨40, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨40, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨40, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3182002553 / 7812500000) (d_hi := 81459265359 / 200000000000)
    (l0 := 4999999604486709 / 5000000000000000) (l1 := 9999996835893797 / 10000000000000000)
    (l2 := 999998734357719 / 1000000000000000) (l3 := 9999949374340797 / 10000000000000000)
    (l4 := 9999797497875779 / 10000000000000000) (l5 := 4999594999852269 / 5000000000000000)
    (l6 := 9996760130038247 / 10000000000000000) (l7 := 9987042619504461 / 10000000000000000)
    (l8 := 1989640811351941 / 2000000000000000) (l9 := 195867055819721 / 200000000000000)
    (u0 := 9999999208973429 / 10000000000000000) (u1 := 4999998417946921 / 5000000000000000)
    (u2 := 9999987343577371 / 10000000000000000) (u3 := 4999974687170761 / 5000000000000000)
    (u4 := 249994937446967 / 250000000000000) (u5 := 4999594999858071 / 5000000000000000)
    (u6 := 499838006504233 / 500000000000000) (u7 := 4993521309845027 / 5000000000000000)
    (u8 := 2487051014375279 / 2500000000000000) (u9 := 4896676396968167 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_41 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨41, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨41, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨41, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨41, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨41, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3174971303 / 7812500000) (d_hi := 81279265359 / 200000000000)
    (l0 := 39062496923693 / 39062500000000) (l1 := 2499999212465439 / 2500000000000000)
    (l2 := 624999212465563 / 625000000000000) (l3 := 4999974798913893 / 5000000000000000)
    (l4 := 9999798391819219 / 10000000000000000) (l5 := 9999193575406047 / 10000000000000000)
    (l6 := 9996774431688313 / 10000000000000000) (l7 := 4993549903805719 / 5000000000000000)
    (l8 := 2487108128359621 / 2500000000000000) (l9 := 979426189488799 / 1000000000000000)
    (u0 := 9999999212465419 / 10000000000000000) (u1 := 9999996849861801 / 10000000000000000)
    (u2 := 9999987399449189 / 10000000000000000) (u3 := 9999949597828511 / 10000000000000000)
    (u4 := 249994959795553 / 250000000000000) (u5 := 2499798393854413 / 2500000000000000)
    (u6 := 999677443173473 / 1000000000000000) (u7 := 9987099807797047 / 10000000000000000)
    (u8 := 9948432514179963 / 10000000000000000) (u9 := 2448565474459653 / 2500000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_42 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨42, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨42, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨42, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨42, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨42, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3169502553 / 7812500000) (d_hi := 81139265359 / 200000000000)
    (l0 := 9999999215176059 / 10000000000000000) (l1 := 9999996860704359 / 10000000000000000)
    (l2 := 9999987442819407 / 10000000000000000) (l3 := 2499987442827291 / 2500000000000000)
    (l4 := 249994977143531 / 250000000000000) (l5 := 9999196351038267 / 10000000000000000)
    (l6 := 4998392766661699 / 5000000000000000) (l7 := 4993572099926397 / 5000000000000000)
    (l8 := 497430492686533 / 500000000000000) (l9 := 2448741901087339 / 2500000000000000)
    (u0 := 9999999215176071 / 10000000000000000) (u1 := 1249999607588051 / 1250000000000000)
    (u2 := 2499996860704901 / 2500000000000000) (u3 := 9999949771309953 / 10000000000000000)
    (u4 := 9999799085744397 / 10000000000000000) (u5 := 624949771940681 / 625000000000000)
    (u6 := 9996785533373911 / 10000000000000000) (u7 := 9987144200054783 / 10000000000000000)
    (u8 := 9948609854537579 / 10000000000000000) (u9 := 4897483803780223 / 5000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
private lemma varPhiGroupSuccProb_bounds_43 {n g r : ℕ}
    (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤ 1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    0 < sin ((2 * (K_varPhi ⟨43, by omega⟩ n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^ 2 ∧
      varPhiSinLo ⟨43, by omega⟩ ^ 2 ≤ sin ((2 * (K_varPhi ⟨43, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi ⟨43, by omega⟩ n g r : ℝ) + 1) * arcsin
      (√(oddFrac n g r))) ^ 2 ≤ varPhiSinHi ⟨43, by omega⟩ ^ 2 :=
  varPhiGroupSuccProb_of_cert hn hg1 hg hr1 hr
    (d_lo := 3167158803 / 7812500000) (d_hi := 81079265359 / 200000000000)
    (l0 := 9999999216336337 / 10000000000000000) (l1 := 999999686534547 / 1000000000000000)
    (l2 := 1999997492276769 / 2000000000000000) (l3 := 9999949845566823 / 10000000000000000)
    (l4 := 1999959876554077 / 2000000000000000) (l5 := 4999598769565497 / 5000000000000000)
    (l6 := 1999358057062533 / 2000000000000000) (l7 := 4993581600852167 / 5000000000000000)
    (l8 := 1243585720436929 / 1250000000000000) (l9 := 9795269684155337 / 10000000000000000)
    (u0 := 2499999804084087 / 2500000000000000) (u1 := 1999999373069103 / 2000000000000000)
    (u2 := 4999993730692013 / 5000000000000000) (u3 := 2499987461391887 / 2500000000000000)
    (u4 := 4999899691386643 / 5000000000000000) (u5 := 9999197539142599 / 10000000000000000)
    (u6 := 4998395142679541 / 5000000000000000) (u7 := 1248395400236243 / 1250000000000000)
    (u8 := 248717144105923 / 250000000000000) (u9 := 979526968710607 / 1000000000000000)
    (by dsimp only [varPhi, varPhiSinLo, varPhiSinLoNum, varPhiSinHi, varPhiSinHiNum]; norm_num)
/-- Positivity and `[varPhiSinLo idx ^ 2, varPhiSinHi idx ^ 2]` enclosure on
  `sin ((2 * K_varPhi idx n g r + 1) * arcsin (√(oddFrac n g r))) ^ 2`
  (definitionally equal to `groupSuccProb n g r (K_varPhi idx n g r)`) across all `44`
  palette
  angles for `100 ≤ n` and `1 ≤ g, r ≤ 1024`. -/
theorem varPhiGroupSuccProb_bounds (idx : Fin 44) {n g r : ℕ} (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤
    1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) : 0 < sin ((2 * (K_varPhi idx n g r : ℝ) + 1) * arcsin
    (√(oddFrac n g r))) ^ 2 ∧ varPhiSinLo idx ^ 2 ≤ sin ((2 * (K_varPhi idx n g r : ℝ) + 1) * arcsin
    (√(oddFrac n g r))) ^ 2 ∧ sin ((2 * (K_varPhi idx n g r : ℝ) + 1) * arcsin (√(oddFrac n g r))) ^
    2 ≤ varPhiSinHi idx ^ 2 := by
  rcases idx with ⟨val, hlt⟩; interval_cases val
  · exact varPhiGroupSuccProb_bounds_0 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_1 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_2 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_3 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_4 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_5 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_6 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_7 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_8 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_9 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_10 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_11 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_12 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_13 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_14 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_15 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_16 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_17 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_18 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_19 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_20 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_21 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_22 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_23 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_24 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_25 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_26 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_27 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_28 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_29 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_30 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_31 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_32 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_33 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_34 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_35 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_36 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_37 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_38 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_39 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_40 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_41 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_42 hn hg1 hg hr1 hr
  · exact varPhiGroupSuccProb_bounds_43 hn hg1 hg hr1 hr
private lemma varPhi_k_cert_0 :
    0 ≤ varPhi ⟨0, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨0, by omega⟩ ∧
      (varPhi ⟨0, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨0, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_1 :
    0 ≤ varPhi ⟨1, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨1, by omega⟩ ∧
      (varPhi ⟨1, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨1, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_2 :
    0 ≤ varPhi ⟨2, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨2, by omega⟩ ∧
      (varPhi ⟨2, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨2, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_3 :
    0 ≤ varPhi ⟨3, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨3, by omega⟩ ∧
      (varPhi ⟨3, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨3, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_4 :
    0 ≤ varPhi ⟨4, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨4, by omega⟩ ∧
      (varPhi ⟨4, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨4, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_5 :
    0 ≤ varPhi ⟨5, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨5, by omega⟩ ∧
      (varPhi ⟨5, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨5, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_6 :
    0 ≤ varPhi ⟨6, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨6, by omega⟩ ∧
      (varPhi ⟨6, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨6, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_7 :
    0 ≤ varPhi ⟨7, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨7, by omega⟩ ∧
      (varPhi ⟨7, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨7, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_8 :
    0 ≤ varPhi ⟨8, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨8, by omega⟩ ∧
      (varPhi ⟨8, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨8, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_9 :
    0 ≤ varPhi ⟨9, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨9, by omega⟩ ∧
      (varPhi ⟨9, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨9, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_10 :
    0 ≤ varPhi ⟨10, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨10, by omega⟩ ∧
      (varPhi ⟨10, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨10, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_11 :
    0 ≤ varPhi ⟨11, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨11, by omega⟩ ∧
      (varPhi ⟨11, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨11, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_12 :
    0 ≤ varPhi ⟨12, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨12, by omega⟩ ∧
      (varPhi ⟨12, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨12, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_13 :
    0 ≤ varPhi ⟨13, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨13, by omega⟩ ∧
      (varPhi ⟨13, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨13, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_14 :
    0 ≤ varPhi ⟨14, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨14, by omega⟩ ∧
      (varPhi ⟨14, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨14, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_15 :
    0 ≤ varPhi ⟨15, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨15, by omega⟩ ∧
      (varPhi ⟨15, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨15, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_16 :
    0 ≤ varPhi ⟨16, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨16, by omega⟩ ∧
      (varPhi ⟨16, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨16, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_17 :
    0 ≤ varPhi ⟨17, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨17, by omega⟩ ∧
      (varPhi ⟨17, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨17, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_18 :
    0 ≤ varPhi ⟨18, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨18, by omega⟩ ∧
      (varPhi ⟨18, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨18, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_19 :
    0 ≤ varPhi ⟨19, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨19, by omega⟩ ∧
      (varPhi ⟨19, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨19, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_20 :
    0 ≤ varPhi ⟨20, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨20, by omega⟩ ∧
      (varPhi ⟨20, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨20, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_21 :
    0 ≤ varPhi ⟨21, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨21, by omega⟩ ∧
      (varPhi ⟨21, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨21, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_22 :
    0 ≤ varPhi ⟨22, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨22, by omega⟩ ∧
      (varPhi ⟨22, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨22, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_23 :
    0 ≤ varPhi ⟨23, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨23, by omega⟩ ∧
      (varPhi ⟨23, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨23, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_24 :
    0 ≤ varPhi ⟨24, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨24, by omega⟩ ∧
      (varPhi ⟨24, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨24, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_25 :
    0 ≤ varPhi ⟨25, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨25, by omega⟩ ∧
      (varPhi ⟨25, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨25, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_26 :
    0 ≤ varPhi ⟨26, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨26, by omega⟩ ∧
      (varPhi ⟨26, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨26, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_27 :
    0 ≤ varPhi ⟨27, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨27, by omega⟩ ∧
      (varPhi ⟨27, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨27, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_28 :
    0 ≤ varPhi ⟨28, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨28, by omega⟩ ∧
      (varPhi ⟨28, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨28, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_29 :
    0 ≤ varPhi ⟨29, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨29, by omega⟩ ∧
      (varPhi ⟨29, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨29, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_30 :
    0 ≤ varPhi ⟨30, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨30, by omega⟩ ∧
      (varPhi ⟨30, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨30, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_31 :
    0 ≤ varPhi ⟨31, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨31, by omega⟩ ∧
      (varPhi ⟨31, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨31, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_32 :
    0 ≤ varPhi ⟨32, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨32, by omega⟩ ∧
      (varPhi ⟨32, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨32, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_33 :
    0 ≤ varPhi ⟨33, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨33, by omega⟩ ∧
      (varPhi ⟨33, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨33, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_34 :
    0 ≤ varPhi ⟨34, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨34, by omega⟩ ∧
      (varPhi ⟨34, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨34, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_35 :
    0 ≤ varPhi ⟨35, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨35, by omega⟩ ∧
      (varPhi ⟨35, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨35, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_36 :
    0 ≤ varPhi ⟨36, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨36, by omega⟩ ∧
      (varPhi ⟨36, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨36, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_37 :
    0 ≤ varPhi ⟨37, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨37, by omega⟩ ∧
      (varPhi ⟨37, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨37, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_38 :
    0 ≤ varPhi ⟨38, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨38, by omega⟩ ∧
      (varPhi ⟨38, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨38, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_39 :
    0 ≤ varPhi ⟨39, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨39, by omega⟩ ∧
      (varPhi ⟨39, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨39, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_40 :
    0 ≤ varPhi ⟨40, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨40, by omega⟩ ∧
      (varPhi ⟨40, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨40, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_41 :
    0 ≤ varPhi ⟨41, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨41, by omega⟩ ∧
      (varPhi ⟨41, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨41, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_42 :
    0 ≤ varPhi ⟨42, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨42, by omega⟩ ∧
      (varPhi ⟨42, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨42, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
private lemma varPhi_k_cert_43 :
    0 ≤ varPhi ⟨43, by omega⟩ ∧ 0 ≤ varPhiCHi ⟨43, by omega⟩ ∧
      (varPhi ⟨43, by omega⟩ / 2) *
          (100000000000000000001 / 100000000000000000000 : ℝ) + 3 / 2 / 2 ^ 40 ≤
        varPhiCHi ⟨43, by omega⟩ * (314159265358979323846 / 100000000000000000000 / 4) := by
  dsimp only [varPhi, varPhiCHi, varPhiCHiNum]; norm_num
/-- Per-round query-count upper bounds (`K_varPhi idx n g r + 1`, including the `+1`
  verification
  oracle call) across all 44 target phases `idx: Fin 44` for `100 ≤ n` and `1 ≤ g, r ≤
  1024`. -/
theorem K_varPhi_add_one_bounds (idx : Fin 44) {n g r : ℕ} (hn : 100 ≤ n) (hg1 : 1 ≤ g) (hg : g ≤
    1024) (hr1 : 1 ≤ r) (hr : r ≤ 1024) : ((K_varPhi idx n g r + 1 : ℕ) : ℝ) ≤ varPhiCHi idx * ((π /
    4) * √((2 ^ n : ℝ) / (g * r))) ∧ ((K_varPhi idx n g r + 1 : ℕ) : ℝ) ≤ varPhiCHi idx * √((2 ^ n :
    ℝ) / (g * r)) ∧ (∀ b m : ℕ, 1 ≤ b → b * g = m → ((K_varPhi idx n g r + 1 : ℕ) : ℝ) ≤ varPhiCHi
    idx * √((b : ℝ) / r) * ((π / 4) * √((2 ^ n : ℝ) / m))) := by
  set R_inv : ℝ := 100000000000000000001 / 100000000000000000000
  have hcert : 0 ≤ varPhi idx ∧ 0 ≤ varPhiCHi idx ∧ (varPhi idx / 2) * R_inv + 3 / 2 / 2 ^ 40 ≤
    varPhiCHi idx * (314159265358979323846 / 100000000000000000000 / 4) := by
    rcases idx with ⟨val, hlt⟩; interval_cases val
    · exact varPhi_k_cert_0
    · exact varPhi_k_cert_1
    · exact varPhi_k_cert_2
    · exact varPhi_k_cert_3
    · exact varPhi_k_cert_4
    · exact varPhi_k_cert_5
    · exact varPhi_k_cert_6
    · exact varPhi_k_cert_7
    · exact varPhi_k_cert_8
    · exact varPhi_k_cert_9
    · exact varPhi_k_cert_10
    · exact varPhi_k_cert_11
    · exact varPhi_k_cert_12
    · exact varPhi_k_cert_13
    · exact varPhi_k_cert_14
    · exact varPhi_k_cert_15
    · exact varPhi_k_cert_16
    · exact varPhi_k_cert_17
    · exact varPhi_k_cert_18
    · exact varPhi_k_cert_19
    · exact varPhi_k_cert_20
    · exact varPhi_k_cert_21
    · exact varPhi_k_cert_22
    · exact varPhi_k_cert_23
    · exact varPhi_k_cert_24
    · exact varPhi_k_cert_25
    · exact varPhi_k_cert_26
    · exact varPhi_k_cert_27
    · exact varPhi_k_cert_28
    · exact varPhi_k_cert_29
    · exact varPhi_k_cert_30
    · exact varPhi_k_cert_31
    · exact varPhi_k_cert_32
    · exact varPhi_k_cert_33
    · exact varPhi_k_cert_34
    · exact varPhi_k_cert_35
    · exact varPhi_k_cert_36
    · exact varPhi_k_cert_37
    · exact varPhi_k_cert_38
    · exact varPhi_k_cert_39
    · exact varPhi_k_cert_40
    · exact varPhi_k_cert_41
    · exact varPhi_k_cert_42
    · exact varPhi_k_cert_43
  rcases hcert with ⟨hφ0, hchi0, hcoeff⟩
  obtain ⟨hp_lo, _, hp_80, hp_pos⟩ := varPhi_oddFrac_bounds_n100 hn hg1 hg hr1 hr
  have hg_pos : (0 : ℝ) < g := (by exact_mod_cast hg1)
  have hr_pos : (0 : ℝ) < r := (by exact_mod_cast hr1)
  have hg_le : (g : ℝ) ≤ 1024 := (by exact_mod_cast hg)
  have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr)
  have hgr_pos : (0 : ℝ) < (g : ℝ) * (r : ℝ) := mul_pos hg_pos hr_pos
  have h2n_ge : (2 ^ 100 : ℝ) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h2n_pos : (0 : ℝ) < 2 ^ n := (by positivity); set p := oddFrac n g r; set c := 1 / p
  have hc1 : (1 : ℝ) ≤ c := by
    dsimp only [c]; rw [le_one_div zero_lt_one hp_pos]; exact hp_80.trans (by norm_num)
  have hsqrt_eq : √p = 1 / √c := (by simp only [c, one_div, sqrt_inv, inv_inv])
  have hK_le : (K_varPhi idx n g r : ℝ) ≤ varPhi idx / 2 * √c + 1 / 2 := by
    dsimp only [K_varPhi]; rw [hsqrt_eq]; exact toNat_round_div_two_mul_arcsin_inv_sqrt_le hφ0 hc1
  set S := √((2 ^ n : ℝ) / (g * r)); have hS_nn : 0 ≤ S := sqrt_nonneg _
  have hdiv_ge : (2 ^ 80 : ℝ) ≤ (2 ^ n : ℝ) / (g * r) := by
    rw [le_div_iff₀ hgr_pos]; have hgr_le : (g : ℝ) * (r : ℝ) ≤ 2 ^ 20 := (by nlinarith); nlinarith
  have hS_ge : (2 ^ 40 : ℝ) ≤ S := by
    rw [show (2 ^ 40 : ℝ) = √((2 ^ 40 : ℝ) ^ 2) from (sqrt_sq (by norm_num)).symm]
    refine sqrt_le_sqrt ?_
    exact (by norm_num : ((2 ^ 40 : ℝ) ^ 2) ≤ 2 ^ 80).trans hdiv_ge
  have hc_le : c ≤ (R_inv * S) ^ 2 := by
    have hsq : (R_inv * S) ^ 2 = R_inv ^ 2 * ((2 ^ n : ℝ) / (g * r)) := by
      rw [mul_pow, sq_sqrt (div_nonneg h2n_pos.le hgr_pos.le)]
    rw [hsq]
    have hp_lo_pos : 0 < (((g : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)) * (1 - 1 / 2 ^ 80) :=
      mul_pos (div_pos (mul_pos hg_pos hr_pos) h2n_pos) (by norm_num)
    have hc_ub : c ≤ 1 / ((((g : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)) * (1 - 1 / 2 ^ 80)) :=
      one_div_le_one_div_of_le hp_lo_pos hp_lo
    refine hc_ub.trans ?_
    have hrew : 1 / ((((g : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)) * (1 - 1 / 2 ^ 80)) = (1 / (1 - 1 / 2 ^
      80)) * ((2 ^ n : ℝ) / (g * r)) := by
      field_simp
    rw [hrew]; refine mul_le_mul_of_nonneg_right ?_ (div_nonneg h2n_pos.le hgr_pos.le)
    dsimp only [R_inv]; norm_num
  have hsqrt_c_le : √c ≤ R_inv * S := by
    have hRS_nn : 0 ≤ R_inv * S := mul_nonneg (by dsimp only [R_inv]; norm_num) hS_nn
    exact (sqrt_le_sqrt hc_le).trans (by rw [sqrt_sq hRS_nn])
  have h1 : ((K_varPhi idx n g r + 1 : ℕ) : ℝ) ≤ varPhiCHi idx * ((π / 4) * S) := by
    rw [Nat.cast_add, Nat.cast_one]
    have h32 : (3 / 2 : ℝ) ≤ (3 / 2 / 2 ^ 40 : ℝ) * S := (by linarith)
    have hmul_c : varPhi idx / 2 * √c ≤ (varPhi idx / 2) * (R_inv * S) :=
      mul_le_mul_of_nonneg_left hsqrt_c_le (div_nonneg hφ0 zero_le_two)
    have hstep1 : (K_varPhi idx n g r : ℝ) + 1 ≤
        ((varPhi idx / 2) * R_inv + 3 / 2 / 2 ^ 40) * S := by
      linarith
    have hpi_lo : (314159265358979323846 / 100000000000000000000 : ℝ) / 4 ≤ π / 4 := by
      linarith [pi_gt_d20]
    have hstep2 : ((varPhi idx / 2) * R_inv + 3 / 2 / 2 ^ 40) * S ≤ varPhiCHi idx * ((π / 4) *
      S) := by
      calc ((varPhi idx / 2) * R_inv + 3 / 2 / 2 ^ 40) * S ≤ (varPhiCHi idx * (314159265358979323846
            / 100000000000000000000 / 4)) * S := mul_le_mul_of_nonneg_right hcoeff hS_nn
        _ ≤ (varPhiCHi idx * (π / 4)) * S :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpi_lo hchi0) hS_nn
        _ = varPhiCHi idx * ((π / 4) * S) := by ring
    exact hstep1.trans hstep2
  have h2 : ((K_varPhi idx n g r + 1 : ℕ) : ℝ) ≤ varPhiCHi idx * S := by
    have hpi4 : π / 4 ≤ 1 := (by linarith [pi_lt_d20]); refine h1.trans ?_
    calc varPhiCHi idx * ((π / 4) * S) ≤ varPhiCHi idx * (1 * S) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpi4 hS_nn) hchi0
      _ = varPhiCHi idx * S := by ring
  refine ⟨h1, h2, fun b m hb1 hbg ↦ ?_⟩
  have hb_pos : (0 : ℝ) < b := (by exact_mod_cast hb1)
  have hm_eq : (m : ℝ) = (b : ℝ) * (g : ℝ) := (by exact_mod_cast hbg.symm)
  have hS_split : S = √((b : ℝ) / r) * √((2 ^ n : ℝ) / m) := by
    dsimp only [S]; rw [← sqrt_mul (div_nonneg hb_pos.le hr_pos.le)]; congr 1; rw [hm_eq]
    field_simp
  rw [hS_split] at h1; linarith
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllVarPhiAnalysis
section WD_FindAllCert
namespace QuantumComputation.Specs.DickeSol
open Real
open scoped NNReal NNRat
@[expose] public section
/-- Piecewise-linear 1-step upper backward operator on the number `d` of distinct coupons
  already collected out of `r`, definitionally equal to `FindAllStage2.couponStepUpper`. -/
noncomputable def stage2CouponStepUpper (p_lo p_hi : ℝ) (r : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  f d + ((r - d : ℝ) / r) * (if f (d + 1) ≤ f d then p_lo else p_hi) * (f (d + 1) - f d)
namespace Stage2CertInternals
def gridExp : ℕ → ℕ
  | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5
  | 64 => 6 | 128 => 7 | 256 => 8 | 512 => 9 | 1024 => 10
  | _ => 0
lemma mem_groverGrid_two_le_cases {x : ℕ} (hx : x ∈ groverGrid) (hx2 : 2 ≤ x) : x = 2 ∨ x = 4 ∨ x =
    8 ∨ x = 16 ∨ x = 32 ∨ x = 64 ∨ x = 128 ∨ x = 256 ∨ x = 512 ∨ x = 1024 := by
  simp only [groverGrid, Finset.mem_image, Finset.mem_range] at hx; obtain ⟨i, hi, rfl⟩ := hx
  interval_cases i <;> omega
lemma gridExp_bounds_of_mem {x : ℕ} (hx : x ∈ groverGrid) (hx2 : 2 ≤ x) :
    1 ≤ gridExp x ∧ gridExp x ≤ 10 ∧ 2 ^ gridExp x = x := by
  rcases mem_groverGrid_two_le_cases hx hx2 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, rfl⟩
def M_scale : ℕ := 1000000000
/-- Complete binary tree of `2 ^ d` natural numbers for `O(d)` kernel lookup without lists. -/
inductive BTree : ℕ → Type
  | leaf : ℕ → BTree 0
  | node {d : ℕ} : BTree d → BTree d → BTree (d + 1)
def BTree.get : {d : ℕ} → BTree d → ℕ → ℕ
  | 0, .leaf x, _ => x
  | d + 1, .node l r, i =>
    if i < 2 ^ d then l.get i else r.get (i - 2 ^ d)
def b8 (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) : BTree 3 :=
  .node
    (.node (.node (.leaf x0) (.leaf x1)) (.node (.leaf x2) (.leaf x3)))
    (.node (.node (.leaf x4) (.leaf x5)) (.node (.leaf x6) (.leaf x7)))
def n4 {d : ℕ} (t0 t1 t2 t3 : BTree d) : BTree (d + 2) := .node (.node t0 t1) (.node t2 t3)
def relCostNumTable : List (List ℕ) :=
  [ [299729, 358237, 3449771, 6701589, 1639747, 807189, 638563, 791851, 6298901, 3136767],
  [689543, 310097, 283819, 531001, 31539, 242841, 118043, 462571, 455763, 225471], [166677,
  537271, 479571, 21707, 399197, 374021, 88951, 342737, 33341, 326773], [331671, 247479, 53473,
  185513, 10327, 18747, 138579, 26071, 248889, 240437], [65723, 467971, 92767, 324313, 279947,
  244467, 54997, 201821, 94347, 35839], [81647, 57463, 338109, 282217, 118873, 51161, 35823,
  39947, 145931, 27163], [81647, 228513, 65099, 49649, 216051, 34759, 149163, 65491, 14473,
  52653], [81647, 454359, 161019, 234009, 91189, 160419, 12713, 3397, 95361, 83869], [81647,
  454359, 31941, 230823, 169233, 133681, 116531, 46303, 78921, 34519], [81647, 227179, 318383,
  229293, 166539, 123461, 20133, 21257, 68171, 28807] ]
def relCostDenTable : List (List ℕ) :=
  [ [400000, 500000, 5000000, 10000000, 2500000, 1250000, 1000000, 1250000, 10000000, 5000000],
  [1000000, 500000, 500000, 1000000, 62500, 500000, 250000, 1000000, 1000000, 500000], [250000,
  1000000, 1000000, 50000, 1000000, 1000000, 250000, 1000000, 100000, 1000000], [500000, 500000,
  125000, 500000, 31250, 62500, 500000, 100000, 1000000, 1000000], [100000, 1000000, 250000,
  1000000, 1000000, 1000000, 250000, 1000000, 500000, 200000], [125000, 125000, 1000000, 1000000,
  500000, 250000, 200000, 250000, 1000000, 200000], [125000, 500000, 200000, 200000, 1000000,
  200000, 1000000, 500000, 125000, 500000], [125000, 1000000, 500000, 1000000, 500000, 1000000,
  100000, 31250, 1000000, 1000000], [125000, 1000000, 100000, 1000000, 1000000, 1000000, 1000000,
  500000, 1000000, 500000], [125000, 500000, 1000000, 1000000, 1000000, 1000000, 200000, 250000,
  1000000, 500000] ]
def relCostNum (im ik : ℕ) : ℕ := (relCostNumTable.getD im []).getD ik 1
def relCostDen (im ik : ℕ) : ℕ := (relCostDenTable.getD im []).getD ik 1
def gammaIm (im : Fin 10) : ℕ :=
  match im.val with
  | 0 => 500000000
  | 1 => 500000000
  | 2 => 500000000
  | 3 => 20000
  | 4 => 80000
  | 5 => 80000
  | 6 => 80000
  | 7 => 80000
  | 8 => 70000
  | _ => 20000
def cubicA2 (im : Fin 10) : ℕ :=
  match im.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 252112895
  | 4 => 252133006
  | 5 => 256206035
  | 6 => 256206035
  | 7 => 257104812
  | 8 => 257104812
  | _ => 257303161
def cubicA3 (im : Fin 10) : ℕ :=
  match im.val with
  | 0 => 500000000
  | 1 => 500000000
  | 2 => 500000000
  | 3 => 52453547
  | 4 => 46924450
  | 5 => 48976573
  | 6 => 48976573
  | 7 => 49875350
  | 8 => 49844126
  | _ => 50042475
def tIdxSched (im_val r : ℕ) : ℕ × ℕ :=
  match im_val with
  | 0 =>
    if r ≤ 365 then if r ≤ 42 then if r ≤ 8 then if r ≤ 4 then if r ≤ 2 then (1, 30) else if r ≤ 3
    then (1, 28) else (1, 31) else if r ≤ 6 then if r ≤ 5 then (1, 29) else (1, 32) else if r ≤ 7
    then (1, 31) else (1, 33) else if r ≤ 13 then if r ≤ 9 then (1, 32) else if r ≤ 11 then (1, 34)
    else (1, 35) else if r ≤ 21 then if r ≤ 16 then (1, 36) else (1, 37) else if r ≤ 29 then (1, 38)
    else (1, 39) else if r ≤ 346 then if r ≤ 332 then if r ≤ 69 then (1, 40) else if r ≤ 138 then
    (1, 41) else (1, 42) else if r ≤ 341 then if r ≤ 333 then (1, 43) else (1, 42) else if r ≤ 342
    then (1, 43) else (1, 42) else if r ≤ 358 then if r ≤ 354 then if r ≤ 347 then (1, 43) else (1,
    42) else if r ≤ 355 then (1, 43) else (1, 42) else if r ≤ 361 then if r ≤ 360 then (1, 43) else
    (1, 42) else if r ≤ 364 then (1, 43) else (1, 42) else if r ≤ 391 then if r ≤ 377 then if r ≤
    370 then if r ≤ 366 then (1, 43) else if r ≤ 367 then (1, 42) else (1, 43) else if r ≤ 375 then
    if r ≤ 374 then (1, 42) else (1, 43) else if r ≤ 376 then (1, 42) else (1, 43) else if r ≤ 381
    then if r ≤ 378 then (1, 42) else if r ≤ 379 then (1, 43) else (1, 42) else if r ≤ 388 then if r
    ≤ 385 then (1, 43) else (1, 42) else if r ≤ 390 then (1, 43) else (1, 42) else if r ≤ 411 then
    if r ≤ 406 then if r ≤ 392 then (1, 43) else if r ≤ 393 then (1, 42) else (1, 43) else if r ≤
    408 then if r ≤ 407 then (1, 42) else (1, 43) else if r ≤ 409 then (1, 42) else (1, 43) else if
    r ≤ 432 then if r ≤ 417 then if r ≤ 412 then (1, 42) else (1, 43) else if r ≤ 418 then (1, 42)
    else (1, 43) else if r ≤ 437 then if r ≤ 433 then (1, 42) else (1, 43) else if r ≤ 438 then (1,
    42) else (1, 43)
  | 1 =>
    if r ≤ 3 then if r ≤ 2 then (2, 8) else (2, 5) else if r ≤ 5 then (2, 6) else if r ≤ 15 then (2,
    5) else (2, 4)
  | 2 =>
    if r ≤ 8 then if r ≤ 4 then if r ≤ 2 then (3, 12) else if r ≤ 3 then (3, 8) else (3, 6) else if
    r ≤ 5 then (3, 5) else if r ≤ 7 then (3, 7) else (3, 6) else if r ≤ 32 then if r ≤ 11 then (3,
    5) else if r ≤ 13 then (3, 6) else (3, 5) else if r ≤ 34 then (3, 4) else if r ≤ 38 then (3, 5)
    else (3, 4)
  | 3 =>
    if r ≤ 51 then if r ≤ 16 then if r ≤ 7 then if r ≤ 4 then if r ≤ 2 then (4, 15) else if r ≤ 3
    then (4, 12) else (4, 10) else if r ≤ 5 then (4, 8) else if r ≤ 6 then (4, 6) else (4, 5) else
    if r ≤ 11 then if r ≤ 9 then (4, 4) else if r ≤ 10 then (4, 9) else (4, 8) else if r ≤ 14 then
    if r ≤ 12 then (4, 7) else (4, 6) else if r ≤ 15 then (4, 5) else (4, 4) else if r ≤ 29 then if
    r ≤ 23 then if r ≤ 18 then (4, 3) else if r ≤ 20 then (4, 7) else (4, 6) else if r ≤ 27 then if
    r ≤ 25 then (4, 5) else (4, 4) else if r ≤ 28 then (4, 3) else (4, 5) else if r ≤ 39 then if r ≤
    32 then (4, 6) else if r ≤ 36 then (4, 5) else (4, 4) else if r ≤ 42 then if r ≤ 40 then (4, 3)
    else (4, 6) else if r ≤ 47 then (4, 5) else (4, 4) else if r ≤ 139 then if r ≤ 94 then if r ≤ 70
    then if r ≤ 58 then (4, 5) else if r ≤ 64 then (4, 4) else (4, 5) else if r ≤ 82 then if r ≤ 76
    then (4, 4) else (4, 5) else if r ≤ 89 then (4, 4) else (4, 5) else if r ≤ 114 then if r ≤ 101
    then (4, 4) else if r ≤ 106 then (4, 5) else (4, 4) else if r ≤ 126 then if r ≤ 118 then (4, 5)
    else (4, 4) else if r ≤ 130 then (4, 5) else (4, 4) else if r ≤ 181 then if r ≤ 155 then if r ≤
    143 then (4, 5) else if r ≤ 152 then (4, 4) else (4, 5) else if r ≤ 168 then if r ≤ 165 then (4,
    4) else (4, 5) else if r ≤ 178 then (4, 4) else (4, 5) else if r ≤ 205 then if r ≤ 192 then (4,
    4) else if r ≤ 193 then (4, 5) else (4, 4) else if r ≤ 218 then if r ≤ 206 then (4, 5) else (4,
    4) else if r ≤ 219 then (4, 5) else (4, 4)
  | 4 =>
    if r ≤ 406 then if r ≤ 125 then if r ≤ 30 then if r ≤ 13 then if r ≤ 6 then if r ≤ 3 then if r ≤
    2 then (5, 18) else (5, 15) else if r ≤ 4 then (5, 14) else if r ≤ 5 then (5, 12) else (5, 10)
    else if r ≤ 8 then if r ≤ 7 then (5, 9) else (5, 8) else if r ≤ 9 then (5, 6) else if r ≤ 11
    then (5, 5) else (5, 4) else if r ≤ 19 then if r ≤ 15 then if r ≤ 14 then (5, 12) else (5, 11)
    else if r ≤ 16 then (5, 10) else if r ≤ 18 then (5, 9) else (5, 8) else if r ≤ 26 then if r ≤ 21
    then (5, 7) else if r ≤ 23 then (5, 6) else (5, 5) else if r ≤ 27 then (5, 4) else if r ≤ 29
    then (5, 3) else (5, 2) else if r ≤ 69 then if r ≤ 44 then if r ≤ 33 then if r ≤ 31 then (5, 9)
    else (5, 8) else if r ≤ 37 then (5, 7) else if r ≤ 40 then (5, 6) else (5, 5) else if r ≤ 54
    then if r ≤ 47 then (5, 4) else if r ≤ 51 then (5, 3) else (5, 7) else if r ≤ 60 then (5, 6)
    else if r ≤ 65 then (5, 5) else (5, 4) else if r ≤ 91 then if r ≤ 74 then if r ≤ 73 then (5, 3)
    else (5, 7) else if r ≤ 80 then (5, 6) else if r ≤ 87 then (5, 5) else (5, 4) else if r ≤ 109
    then if r ≤ 96 then (5, 3) else if r ≤ 102 then (5, 6) else (5, 5) else if r ≤ 114 then (5, 4)
    else if r ≤ 120 then (5, 3) else (5, 6) else if r ≤ 262 then if r ≤ 194 then if r ≤ 156 then if
    r ≤ 138 then if r ≤ 133 then (5, 5) else (5, 4) else if r ≤ 144 then (5, 3) else if r ≤ 150 then
    (5, 6) else (5, 5) else if r ≤ 174 then if r ≤ 162 then (5, 4) else if r ≤ 168 then (5, 3) else
    (5, 6) else if r ≤ 180 then (5, 5) else if r ≤ 186 then (5, 4) else (5, 3) else if r ≤ 223 then
    if r ≤ 205 then if r ≤ 198 then (5, 6) else (5, 5) else if r ≤ 211 then (5, 4) else if r ≤ 219
    then (5, 3) else (5, 6) else if r ≤ 244 then if r ≤ 230 then (5, 5) else if r ≤ 237 then (5, 4)
    else (5, 3) else if r ≤ 248 then (5, 6) else if r ≤ 254 then (5, 5) else (5, 4) else if r ≤ 330
    then if r ≤ 296 then if r ≤ 273 then if r ≤ 270 then (5, 3) else (5, 6) else if r ≤ 279 then (5,
    5) else if r ≤ 288 then (5, 4) else (5, 3) else if r ≤ 314 then if r ≤ 298 then (5, 6) else if r
    ≤ 304 then (5, 5) else (5, 4) else if r ≤ 322 then (5, 3) else if r ≤ 324 then (5, 6) else (5,
    5) else if r ≤ 365 then if r ≤ 348 then if r ≤ 339 then (5, 4) else (5, 3) else if r ≤ 349 then
    (5, 6) else if r ≤ 355 then (5, 5) else (5, 4) else if r ≤ 380 then if r ≤ 373 then (5, 3) else
    if r ≤ 374 then (5, 6) else (5, 5) else if r ≤ 391 then (5, 4) else if r ≤ 400 then (5, 3) else
    (5, 5) else if r ≤ 735 then if r ≤ 585 then if r ≤ 504 then if r ≤ 452 then if r ≤ 426 then if r
    ≤ 418 then (5, 4) else (5, 3) else if r ≤ 431 then (5, 5) else if r ≤ 444 then (5, 4) else (5,
    3) else if r ≤ 478 then if r ≤ 457 then (5, 5) else if r ≤ 470 then (5, 4) else (5, 3) else if r
    ≤ 483 then (5, 5) else if r ≤ 497 then (5, 4) else (5, 3) else if r ≤ 550 then if r ≤ 523 then
    if r ≤ 508 then (5, 5) else (5, 4) else if r ≤ 531 then (5, 3) else if r ≤ 535 then (5, 5) else
    (5, 4) else if r ≤ 560 then if r ≤ 557 then (5, 3) else if r ≤ 558 then (5, 4) else (5, 5) else
    if r ≤ 576 then (5, 4) else if r ≤ 584 then (5, 3) else (5, 4) else if r ≤ 664 then if r ≤ 615
    then if r ≤ 603 then if r ≤ 587 then (5, 5) else (5, 4) else if r ≤ 610 then (5, 3) else if r ≤
    614 then (5, 4) else (5, 5) else if r ≤ 639 then if r ≤ 629 then (5, 4) else if r ≤ 637 then (5,
    3) else (5, 4) else if r ≤ 641 then (5, 5) else if r ≤ 656 then (5, 4) else (5, 3) else if r ≤
    692 then if r ≤ 668 then if r ≤ 666 then (5, 4) else (5, 5) else if r ≤ 682 then (5, 4) else if
    r ≤ 691 then (5, 3) else (5, 4) else if r ≤ 717 then if r ≤ 695 then (5, 5) else if r ≤ 709 then
    (5, 4) else (5, 3) else if r ≤ 719 then (5, 4) else if r ≤ 722 then (5, 5) else (5, 4) else if r
    ≤ 880 then if r ≤ 801 then if r ≤ 771 then if r ≤ 748 then if r ≤ 744 then (5, 3) else (5, 4)
    else if r ≤ 749 then (5, 5) else if r ≤ 761 then (5, 4) else (5, 3) else if r ≤ 788 then if r ≤
    773 then (5, 4) else if r ≤ 775 then (5, 5) else (5, 4) else if r ≤ 798 then (5, 3) else if r ≤
    799 then (5, 4) else (5, 5) else if r ≤ 842 then if r ≤ 824 then if r ≤ 815 then (5, 4) else (5,
    3) else if r ≤ 826 then (5, 4) else if r ≤ 829 then (5, 5) else (5, 4) else if r ≤ 856 then if r
    ≤ 851 then (5, 3) else if r ≤ 853 then (5, 4) else (5, 5) else if r ≤ 868 then (5, 4) else if r
    ≤ 878 then (5, 3) else (5, 4) else if r ≤ 959 then if r ≤ 908 then if r ≤ 895 then if r ≤ 883
    then (5, 5) else (5, 4) else if r ≤ 905 then (5, 3) else if r ≤ 906 then (5, 4) else (5, 5) else
    if r ≤ 934 then if r ≤ 921 then (5, 4) else if r ≤ 932 then (5, 3) else (5, 4) else if r ≤ 936
    then (5, 5) else if r ≤ 948 then (5, 4) else (5, 3) else if r ≤ 989 then if r ≤ 962 then if r ≤
    960 then (5, 4) else (5, 5) else if r ≤ 974 then (5, 4) else if r ≤ 986 then (5, 3) else (5, 4)
    else if r ≤ 1012 then if r ≤ 990 then (5, 5) else if r ≤ 1001 then (5, 4) else (5, 3) else if r
    ≤ 1014 then (5, 4) else if r ≤ 1017 then (5, 5) else (5, 4)
  | 5 =>
    if r ≤ 303 then if r ≤ 74 then if r ≤ 21 then if r ≤ 9 then if r ≤ 5 then if r ≤ 3 then if r ≤ 2
    then (6, 19) else (6, 18) else if r ≤ 4 then (6, 16) else (6, 15) else if r ≤ 7 then if r ≤ 6
    then (6, 14) else (6, 13) else if r ≤ 8 then (6, 12) else (6, 11) else if r ≤ 14 then if r ≤ 12
    then if r ≤ 10 then (6, 10) else (6, 9) else if r ≤ 13 then (6, 8) else (6, 7) else if r ≤ 17
    then if r ≤ 16 then (6, 6) else (6, 5) else if r ≤ 19 then (6, 4) else (6, 3) else if r ≤ 41
    then if r ≤ 29 then if r ≤ 24 then if r ≤ 22 then (6, 13) else (6, 12) else if r ≤ 26 then (6,
    11) else (6, 10) else if r ≤ 34 then if r ≤ 31 then (6, 9) else (6, 8) else if r ≤ 38 then (6,
    7) else (6, 6) else if r ≤ 53 then if r ≤ 47 then if r ≤ 45 then (6, 5) else (6, 4) else if r ≤
    51 then (6, 3) else (6, 2) else if r ≤ 58 then if r ≤ 54 then (6, 10) else (6, 9) else if r ≤ 63
    then (6, 8) else if r ≤ 68 then (6, 7) else (6, 6) else if r ≤ 169 then if r ≤ 113 then if r ≤
    92 then if r ≤ 84 then if r ≤ 80 then (6, 5) else (6, 4) else if r ≤ 90 then (6, 3) else (6, 2)
    else if r ≤ 99 then if r ≤ 93 then (6, 9) else (6, 8) else if r ≤ 105 then (6, 7) else (6, 6)
    else if r ≤ 135 then if r ≤ 124 then if r ≤ 120 then (6, 5) else (6, 4) else if r ≤ 131 then (6,
    3) else (6, 2) else if r ≤ 147 then if r ≤ 139 then (6, 8) else (6, 7) else if r ≤ 154 then (6,
    6) else if r ≤ 163 then (6, 5) else (6, 4) else if r ≤ 228 then if r ≤ 198 then if r ≤ 181 then
    if r ≤ 176 then (6, 3) else (6, 2) else if r ≤ 191 then (6, 7) else (6, 6) else if r ≤ 215 then
    if r ≤ 208 then (6, 5) else (6, 4) else if r ≤ 223 then (6, 3) else (6, 2) else if r ≤ 262 then
    if r ≤ 242 then if r ≤ 235 then (6, 7) else (6, 6) else if r ≤ 255 then (6, 5) else (6, 4) else
    if r ≤ 277 then if r ≤ 271 then (6, 3) else (6, 2) else if r ≤ 281 then (6, 7) else if r ≤ 289
    then (6, 6) else (6, 5) else if r ≤ 641 then if r ≤ 473 then if r ≤ 376 then if r ≤ 340 then if
    r ≤ 320 then if r ≤ 311 then (6, 4) else (6, 3) else if r ≤ 326 then (6, 2) else (6, 6) else if
    r ≤ 361 then if r ≤ 351 then (6, 5) else (6, 4) else if r ≤ 371 then (6, 3) else (6, 2) else if
    r ≤ 422 then if r ≤ 400 then if r ≤ 389 then (6, 6) else (6, 5) else if r ≤ 411 then (6, 4) else
    (6, 3) else if r ≤ 440 then if r ≤ 427 then (6, 2) else (6, 6) else if r ≤ 449 then (6, 5) else
    if r ≤ 461 then (6, 4) else (6, 3) else if r ≤ 548 then if r ≤ 512 then if r ≤ 490 then if r ≤
    478 then (6, 2) else (6, 6) else if r ≤ 499 then (6, 5) else (6, 4) else if r ≤ 530 then if r ≤
    525 then (6, 3) else (6, 2) else if r ≤ 540 then (6, 6) else (6, 5) else if r ≤ 590 then if r ≤
    577 then if r ≤ 563 then (6, 4) else (6, 3) else if r ≤ 581 then (6, 2) else (6, 6) else if r ≤
    615 then if r ≤ 598 then (6, 5) else (6, 4) else if r ≤ 629 then (6, 3) else if r ≤ 633 then (6,
    2) else (6, 6) else if r ≤ 823 then if r ≤ 734 then if r ≤ 685 then if r ≤ 666 then if r ≤ 650
    then (6, 5) else (6, 4) else if r ≤ 681 then (6, 3) else (6, 2) else if r ≤ 699 then if r ≤ 691
    then (6, 6) else (6, 5) else if r ≤ 719 then (6, 4) else (6, 3) else if r ≤ 771 then if r ≤ 742
    then if r ≤ 737 then (6, 2) else (6, 6) else if r ≤ 750 then (6, 5) else (6, 4) else if r ≤ 789
    then if r ≤ 786 then (6, 3) else (6, 2) else if r ≤ 792 then (6, 6) else if r ≤ 800 then (6, 5)
    else (6, 4) else if r ≤ 902 then if r ≤ 851 then if r ≤ 841 then if r ≤ 839 then (6, 3) else (6,
    2) else if r ≤ 843 then (6, 6) else (6, 5) else if r ≤ 892 then if r ≤ 875 then (6, 4) else (6,
    3) else if r ≤ 894 then (6, 2) else (6, 5) else if r ≤ 954 then if r ≤ 946 then if r ≤ 927 then
    (6, 4) else (6, 3) else if r ≤ 953 then (6, 5) else (6, 4) else if r ≤ 980 then if r ≤ 955 then
    (6, 5) else (6, 4) else if r ≤ 999 then (6, 3) else if r ≤ 1005 then (6, 5) else (6, 4)
  | 6 =>
    if r ≤ 259 then if r ≤ 63 then if r ≤ 20 then if r ≤ 9 then if r ≤ 5 then if r ≤ 2 then (6, 19)
    else if r ≤ 3 then (6, 18) else (7, 18) else if r ≤ 6 then (7, 17) else if r ≤ 7 then (7, 16)
    else (7, 15) else if r ≤ 14 then if r ≤ 11 then (7, 14) else if r ≤ 12 then (7, 13) else (7, 12)
    else if r ≤ 16 then (7, 11) else if r ≤ 18 then (7, 10) else (7, 9) else if r ≤ 34 then if r ≤
    26 then if r ≤ 22 then (7, 8) else if r ≤ 24 then (7, 7) else (7, 6) else if r ≤ 29 then (7, 5)
    else if r ≤ 30 then (7, 4) else (7, 3) else if r ≤ 44 then if r ≤ 37 then (7, 14) else if r ≤ 40
    then (7, 13) else (7, 12) else if r ≤ 53 then if r ≤ 49 then (7, 11) else (7, 10) else if r ≤ 58
    then (7, 9) else (7, 8) else if r ≤ 142 then if r ≤ 95 then if r ≤ 81 then if r ≤ 69 then (7, 7)
    else if r ≤ 75 then (7, 6) else (7, 5) else if r ≤ 85 then (7, 4) else if r ≤ 91 then (7, 3)
    else (7, 2) else if r ≤ 109 then if r ≤ 96 then (7, 12) else if r ≤ 102 then (7, 11) else (7,
    10) else if r ≤ 124 then if r ≤ 116 then (7, 9) else (7, 8) else if r ≤ 133 then (7, 7) else (7,
    6) else if r ≤ 185 then if r ≤ 163 then if r ≤ 150 then (7, 5) else if r ≤ 155 then (7, 4) else
    (7, 3) else if r ≤ 173 then (7, 2) else if r ≤ 176 then (7, 10) else (7, 9) else if r ≤ 219 then
    if r ≤ 197 then (7, 8) else if r ≤ 206 then (7, 7) else (7, 6) else if r ≤ 236 then if r ≤ 231
    then (7, 5) else (7, 4) else if r ≤ 247 then (7, 3) else (7, 2) else if r ≤ 568 then if r ≤ 410
    then if r ≤ 337 then if r ≤ 302 then if r ≤ 275 then (7, 8) else if r ≤ 289 then (7, 7) else (7,
    6) else if r ≤ 319 then (7, 5) else if r ≤ 326 then (7, 4) else (7, 3) else if r ≤ 376 then if r
    ≤ 351 then (7, 2) else if r ≤ 356 then (7, 8) else (7, 7) else if r ≤ 406 then if r ≤ 388 then
    (7, 6) else (7, 5) else if r ≤ 408 then (7, 4) else (7, 5) else if r ≤ 466 then if r ≤ 421 then
    if r ≤ 418 then (7, 4) else if r ≤ 419 then (7, 3) else (7, 4) else if r ≤ 432 then (7, 3) else
    if r ≤ 447 then (7, 2) else (7, 7) else if r ≤ 515 then if r ≤ 477 then (7, 6) else if r ≤ 499
    then (7, 5) else (7, 4) else if r ≤ 545 then if r ≤ 528 then (7, 3) else (7, 2) else if r ≤ 557
    then (7, 7) else (7, 6) else if r ≤ 769 then if r ≤ 661 then if r ≤ 627 then if r ≤ 595 then (7,
    5) else if r ≤ 614 then (7, 4) else (7, 3) else if r ≤ 644 then (7, 2) else if r ≤ 648 then (7,
    7) else (7, 6) else if r ≤ 691 then if r ≤ 662 then (7, 5) else if r ≤ 667 then (7, 6) else (7,
    5) else if r ≤ 728 then if r ≤ 714 then (7, 4) else (7, 3) else if r ≤ 744 then (7, 2) else (7,
    6) else if r ≤ 888 then if r ≤ 831 then if r ≤ 789 then (7, 5) else if r ≤ 812 then (7, 4) else
    (7, 3) else if r ≤ 846 then (7, 2) else if r ≤ 869 then (7, 6) else (7, 5) else if r ≤ 949 then
    if r ≤ 914 then (7, 4) else if r ≤ 934 then (7, 3) else (7, 2) else if r ≤ 986 then if r ≤ 969
    then (7, 6) else (7, 5) else if r ≤ 1016 then (7, 4) else (7, 3)
  | 7 =>
    if r ≤ 341 then if r ≤ 78 then if r ≤ 28 then if r ≤ 8 then if r ≤ 4 then if r ≤ 2 then (6, 19)
    else if r ≤ 3 then (6, 18) else (8, 20) else if r ≤ 5 then (8, 19) else if r ≤ 6 then (7, 17)
    else (8, 18) else if r ≤ 15 then if r ≤ 10 then (8, 17) else if r ≤ 13 then (8, 16) else (8, 15)
    else if r ≤ 21 then if r ≤ 18 then (8, 14) else (8, 13) else if r ≤ 24 then (8, 12) else (8, 11)
    else if r ≤ 49 then if r ≤ 38 then if r ≤ 31 then (8, 10) else if r ≤ 34 then (8, 9) else (8, 8)
    else if r ≤ 42 then (8, 7) else if r ≤ 45 then (8, 6) else (8, 5) else if r ≤ 57 then if r ≤ 52
    then (8, 4) else if r ≤ 56 then (8, 3) else (8, 2) else if r ≤ 64 then if r ≤ 58 then (8, 16)
    else (8, 15) else if r ≤ 70 then (8, 14) else (8, 13) else if r ≤ 198 then if r ≤ 129 then if r
    ≤ 102 then if r ≤ 85 then (8, 12) else if r ≤ 93 then (8, 11) else (8, 10) else if r ≤ 110 then
    (8, 9) else if r ≤ 119 then (8, 8) else (8, 7) else if r ≤ 156 then if r ≤ 140 then (8, 6) else
    if r ≤ 149 then (8, 5) else (8, 4) else if r ≤ 176 then if r ≤ 164 then (8, 3) else (8, 2) else
    if r ≤ 186 then (8, 12) else (8, 11) else if r ≤ 286 then if r ≤ 239 then if r ≤ 210 then (8,
    10) else if r ≤ 225 then (8, 9) else (8, 8) else if r ≤ 257 then (8, 7) else if r ≤ 275 then (8,
    6) else (8, 5) else if r ≤ 299 then if r ≤ 292 then (8, 4) else if r ≤ 293 then (8, 3) else (8,
    4) else if r ≤ 330 then if r ≤ 308 then (8, 3) else (8, 2) else if r ≤ 337 then (8, 10) else (8,
    9) else if r ≤ 655 then if r ≤ 540 then if r ≤ 450 then if r ≤ 382 then if r ≤ 345 then (8, 10)
    else if r ≤ 361 then (8, 9) else (8, 8) else if r ≤ 403 then (8, 7) else if r ≤ 424 then (8, 6)
    else (8, 5) else if r ≤ 462 then if r ≤ 457 then (8, 4) else if r ≤ 460 then (8, 3) else (8, 4)
    else if r ≤ 505 then if r ≤ 479 then (8, 3) else (8, 2) else if r ≤ 508 then (8, 9) else (8, 8)
    else if r ≤ 612 then if r ≤ 564 then if r ≤ 558 then (8, 7) else if r ≤ 559 then (8, 6) else (8,
    7) else if r ≤ 590 then (8, 6) else if r ≤ 610 then (8, 5) else (8, 4) else if r ≤ 627 then if r
    ≤ 618 then (8, 5) else if r ≤ 621 then (8, 4) else (8, 5) else if r ≤ 635 then if r ≤ 633 then
    (8, 4) else (8, 3) else if r ≤ 639 then (8, 4) else (8, 3) else if r ≤ 817 then if r ≤ 763 then
    if r ≤ 737 then if r ≤ 689 then (8, 2) else if r ≤ 701 then (8, 8) else (8, 7) else if r ≤ 740
    then (8, 6) else if r ≤ 743 then (8, 7) else (8, 6) else if r ≤ 801 then if r ≤ 793 then (8, 5)
    else if r ≤ 798 then (8, 4) else (8, 5) else if r ≤ 809 then if r ≤ 807 then (8, 4) else (8, 5)
    else if r ≤ 816 then (8, 4) else (8, 3) else if r ≤ 942 then if r ≤ 829 then if r ≤ 823 then (8,
    4) else if r ≤ 826 then (8, 3) else (8, 4) else if r ≤ 881 then if r ≤ 842 then (8, 3) else (8,
    2) else if r ≤ 920 then (8, 7) else (8, 6) else if r ≤ 980 then if r ≤ 971 then (8, 5) else if r
    ≤ 972 then (8, 4) else (8, 5) else if r ≤ 1013 then if r ≤ 1011 then (8, 4) else (8, 3) else if
    r ≤ 1017 then (8, 4) else (8, 3)
  | 8 =>
    if r ≤ 268 then if r ≤ 55 then if r ≤ 13 then if r ≤ 5 then if r ≤ 3 then if r ≤ 2 then (6, 19)
    else (9, 23) else if r ≤ 4 then (8, 20) else (8, 19) else if r ≤ 7 then if r ≤ 6 then (9, 21)
    else (9, 20) else if r ≤ 9 then (9, 19) else if r ≤ 10 then (8, 17) else (9, 18) else if r ≤ 27
    then if r ≤ 18 then if r ≤ 14 then (8, 15) else (9, 17) else if r ≤ 22 then (9, 16) else (9, 15)
    else if r ≤ 38 then if r ≤ 32 then (9, 14) else (9, 13) else if r ≤ 43 then (9, 12) else if r ≤
    49 then (9, 11) else (9, 10) else if r ≤ 115 then if r ≤ 80 then if r ≤ 67 then if r ≤ 61 then
    (9, 9) else (9, 8) else if r ≤ 73 then (9, 7) else (9, 6) else if r ≤ 90 then if r ≤ 86 then (9,
    5) else (9, 4) else if r ≤ 96 then (9, 3) else if r ≤ 104 then (9, 17) else (9, 16) else if r ≤
    185 then if r ≤ 141 then if r ≤ 127 then (9, 15) else (9, 14) else if r ≤ 155 then (9, 13) else
    if r ≤ 170 then (9, 12) else (9, 11) else if r ≤ 218 then if r ≤ 201 then (9, 10) else (9, 9)
    else if r ≤ 234 then (9, 8) else if r ≤ 251 then (9, 7) else (9, 6) else if r ≤ 644 then if r ≤
    445 then if r ≤ 332 then if r ≤ 293 then if r ≤ 283 then (9, 5) else (9, 4) else if r ≤ 305 then
    (9, 3) else (9, 2) else if r ≤ 368 then if r ≤ 348 then (9, 13) else (9, 12) else if r ≤ 392
    then (9, 11) else if r ≤ 417 then (9, 10) else (9, 9) else if r ≤ 559 then if r ≤ 508 then if r
    ≤ 473 then (9, 8) else (9, 7) else if r ≤ 534 then (9, 6) else (9, 5) else if r ≤ 574 then if r
    ≤ 569 then (9, 4) else (9, 3) else if r ≤ 582 then (9, 4) else if r ≤ 597 then (9, 3) else (9,
    2) else if r ≤ 860 then if r ≤ 715 then if r ≤ 678 then if r ≤ 670 then (9, 10) else (9, 9) else
    if r ≤ 686 then (9, 10) else (9, 9) else if r ≤ 794 then if r ≤ 754 then (9, 8) else (9, 7) else
    if r ≤ 839 then (9, 6) else if r ≤ 857 then (9, 5) else (9, 4) else if r ≤ 906 then if r ≤ 876
    then if r ≤ 873 then (9, 5) else (9, 4) else if r ≤ 889 then (9, 5) else if r ≤ 900 then (9, 4)
    else (9, 3) else if r ≤ 940 then if r ≤ 910 then (9, 4) else (9, 3) else if r ≤ 993 then (9, 2)
    else if r ≤ 1010 then (9, 9) else (9, 8)
  | _ =>
    if r ≤ 169 then if r ≤ 39 then if r ≤ 8 then if r ≤ 4 then if r ≤ 2 then (6, 19) else if r ≤ 3
    then (9, 23) else (8, 20) else if r ≤ 5 then (10, 23) else if r ≤ 6 then (9, 21) else (10, 22)
    else if r ≤ 16 then if r ≤ 10 then (10, 21) else if r ≤ 13 then (10, 20) else (10, 19) else if r
    ≤ 24 then if r ≤ 18 then (9, 17) else (10, 18) else if r ≤ 31 then (10, 17) else (10, 16) else
    if r ≤ 108 then if r ≤ 67 then if r ≤ 48 then (10, 15) else if r ≤ 57 then (10, 14) else (10,
    13) else if r ≤ 87 then if r ≤ 77 then (10, 12) else (10, 11) else if r ≤ 98 then (10, 10) else
    (10, 9) else if r ≤ 141 then if r ≤ 119 then (10, 8) else if r ≤ 130 then (10, 7) else (10, 6)
    else if r ≤ 158 then if r ≤ 151 then (10, 5) else (10, 4) else if r ≤ 167 then (10, 3) else (10,
    2) else if r ≤ 504 then if r ≤ 289 then if r ≤ 211 then if r ≤ 170 then (10, 18) else if r ≤ 189
    then (10, 17) else (10, 16) else if r ≤ 235 then (10, 15) else if r ≤ 261 then (10, 14) else
    (10, 13) else if r ≤ 378 then if r ≤ 317 then (10, 12) else if r ≤ 347 then (10, 11) else (10,
    10) else if r ≤ 439 then if r ≤ 408 then (10, 9) else (10, 8) else if r ≤ 471 then (10, 7) else
    (10, 6) else if r ≤ 707 then if r ≤ 576 then if r ≤ 533 then (10, 5) else if r ≤ 551 then (10,
    4) else (10, 3) else if r ≤ 630 then if r ≤ 624 then (10, 2) else (10, 14) else if r ≤ 667 then
    (10, 13) else (10, 12) else if r ≤ 855 then if r ≤ 750 then (10, 11) else if r ≤ 805 then (10,
    10) else (10, 9) else if r ≤ 978 then if r ≤ 910 then (10, 8) else (10, 7) else if r ≤ 1018 then
    (10, 6) else (10, 5)
def potTree0 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1279173514 1673817701 1994990881 2287749627 2548349797
  2791397203 3016090944) (b8 3228490495 3428783773 3619884488 3802242599 3977426961 4145904065
  4308603378 4465935056) (b8 4618496523 4766628504 4910742418 5051115977 5188048320 5321765094
  5452493367 5580417416) (b8 5705715470 5828539192 5949032132 6067320322 6183521754 6297742175
  6410080177 6520625408)) (n4 (b8 6629461350 6736664682 6842306887 6946454118 7049168169
  7150506562 7250523163 7349268348) (b8 7446789418 7543130779 7638334239 7732439163 7825482734
  7917500059 8008524368 8098587124) (b8 8187718170 8275945833 8363297038 8449797392 8535471285
  8620341957 8704431587 8787761345) (b8 8870351466 8952221300 9033389368 9113873412 9193690440
  9272856762 9351388038 9429299309)) (n4 (b8 9506605030 9583319105 9659454914 9735025339
  9810042788 9884519223 9958466185 10031894806) (b8 10104815836 10177239658 10249176305
  10320635479 10391626558 10462158629 10532240474 10601880614) (b8 10671087289 10739868499
  10808231993 10876185290 10943735687 11010890266 11077655904 11144039282) (b8 11210046890
  11275685040 11340959866 11405877335 11470443253 11534663269 11598542884 11662087454)) (n4 (b8
  11725302196 11788192192 11850762399 11913017644 11974962636 12036601968 12097940119 12158981464)
  (b8 12219730267 12280190696 12340366820 12400262609 12459881949 12519228628 12578306358
  12637118758) (b8 12695669375 12753961671 12811999035 12869784785 12927322164 12984614348
  13041664444 13098475496) (b8 13155050483 13211392325 13267503880 13323387948 13379047274
  13434484548 13489702408 13544703435))) (n4 (n4 (b8 13599490168 13654065089 13708430638
  13762589204 13816543136 13870294733 13923846258 13977199925) (b8 14030357914 14083322361
  14136095364 14188678985 14241075247 14293286140 14345313617 14397159597) (b8 14448825966
  14500314580 14551627258 14602765795 14653731948 14704527451 14755154007 14805613288) (b8
  14855906946 14906036595 14956003835 15005810231 15055457326 15104946642 15154279668
  15203457883)) (n4 (b8 15252482728 15301355636 15350078004 15398651221 15447076642 15495355613
  15543489453 15591479463) (b8 15639326925 15687033100 15734599236 15782026554 15829316267
  15876469563 15923487616 15970371585) (b8 16017122608 16063741813 16110230305 16156589180
  16202819514 16248922372 16294898802 16340749839) (b8 16386476503 16432079801 16477560724
  16522920256 16568159360 16613278993 16658280095 16703163594)) (n4 (b8 16747930410 16792581446
  16837117598 16881539746 16925848763 16970045507 17014130829 17058105565) (b8 17101970546
  17145726588 17189374499 17232915076 17276349107 17319677372 17362900639 17406019667) (b8
  17449035208 17491948001 17534758782 17577468273 17620077189 17662586238 17704996121 17747307525)
  (b8 17789521136 17831637626 17873657666 17915581912 17957411019 17999145630 18040786383
  18082333909)) (n4 (b8 18123788831 18165151764 18206423319 18247604101 18288694701 18329695716
  18370607722 18411431304) (b8 18452167024 18492815455 18533377149 18573852664 18614242544
  18654547332 18694767562 18734903765) (b8 18774956466 18814926182 18854813430 18894618714
  18934342541 18973985407 19013547806 19053030225) (b8 19092433147 19131757053 19171002412
  19210169697 19249259369 19288271889 19327207713 19366067290))) (n4 (n4 (b8 19404851067
  19443559485 19482192983 19520751992 19559236943 19597648262 19635986368 19674251678) (b8
  19712444607 19750565562 19788614950 19826593172 19864500626 19902337706 19940104802 19977802303)
  (b8 20015430589 20052990043 20090481039 20127903952 20165259148 20202546998 20239767861
  20276922099) (b8 20314010069 20351032122 20387988610 20424879879 20461706274 20498468136
  20535165802 20571799609)) (n4 (b8 20608369887 20644876966 20681321175 20717702833 20754022266
  20790279788 20826475717 20862610366) (b8 20898684043 20934697059 20970649715 21006542318
  21042375162 21078148551 21113862775 21149518129) (b8 21185114904 21220653384 21256133859
  21291556608 21326921915 21362230056 21397481311 21432675949) (b8 21467814247 21502896470
  21537922890 21572893769 21607809374 21642669962 21677475796 21712227130)) (n4 (b8 21746924221
  21781567322 21816156685 21850692557 21885175189 21919604821 21953981703 21988306071) (b8
  22022578170 22056798234 22090966503 22125083207 22159148583 22193162860 22227126267 22261039033)
  (b8 22294901382 22328713539 22362475727 22396188166 22429851076 22463464674 22497029176
  22530544798) (b8 22564011751 22597430248 22630800497 22664122709 22697397088 22730623842
  22763803173 22796935285)) (n4 (b8 22830020377 22863058650 22896050302 22928995530 22961894530
  22994747495 23027554618 23060316090) (b8 23093032102 23125702841 23158328496 23190909253
  23223445297 23255936811 23288383978 23320786977) (b8 23353145990 23385461195 23417732770
  23449960890 23482145731 23514287468 23546386270 23578442314) (b8 23610455765 23642426796
  23674355573 23706242266 23738087037 23769890054 23801651479 23833371476))) (n4 (n4 (b8
  23865050206 23896687831 23928284508 23959840398 23991355656 24022830442 24054264908 24085659211)
  (b8 24117013504 24148327939 24179602667 24210837841 24242033608 24273190120 24304307521
  24335385961) (b8 24366425584 24397426536 24428388962 24459313003 24490198804 24521046504
  24551856246 24582628168) (b8 24613362411 24644059110 24674718404 24705340431 24735925324
  24766473218 24796984248 24827458548)) (n4 (b8 24857896248 24888297482 24918662377 24948991067
  24979283679 25009540342 25039761183 25069946331) (b8 25100095910 25130210046 25160288865
  25190332489 25220341044 25250314649 25280253428 25310157502) (b8 25340026991 25369862015
  25399662693 25429429142 25459161482 25488859829 25518524298 25548155006) (b8 25577752067
  25607315598 25636845711 25666342517 25695806133 25725236667 25754634231 25783998937)) (n4 (b8
  25813330892 25842630209 25871896993 25901131356 25930333402 25959503240 25988640977 26017746716)
  (b8 26046820565 26075862627 26104873006 26133851806 26162799130 26191715079 26220599757
  26249453264) (b8 26278275700 26307067167 26335827764 26364557589 26393256741 26421925318
  26450563419 26479171139) (b8 26507748575 26536295824 26564812980 26593300139 26621757395
  26650184842 26678582574 26706950683)) (n4 (b8 26735289262 26763598404 26791878199 26820128739
  26848350113 26876542414 26904705730 26932840150) (b8 26960945763 26989022659 27017070922
  27045090644 27073081907 27101044804 27128979413 27156885827) (b8 27184764125 27212614398
  27240436725 27268231195 27295997887 27323736886 27351448274 27379132134) (b8 27406788549
  27434417598 27462019364 27489593926 27517141366 27544661762 27572155196 27599621745)))) (n4 (n4
  (n4 (b8 27627061489 27654474506 27681860872 27709220667 27736553967 27763860850 27791141391
  27818395668) (b8 27845623754 27872825727 27900001659 27927151628 27954275706 27981373969
  28008446488 28035493338) (b8 28062514592 28089510321 28116480599 28143425495 28170345085
  28197239436 28224108621 28250952710) (b8 28277771773 28304565880 28331335101 28358079504
  28384799160 28411494135 28438164499 28464810319)) (n4 (b8 28491431664 28518028601 28544601194
  28571149514 28597673626 28624173593 28650649487 28677101367) (b8 28703529303 28729933357
  28756313595 28782670082 28809002879 28835312055 28861597667 28887859785) (b8 28914098465
  28940313776 28966505775 28992674528 29018820094 29044942537 29071041916 29097118294) (b8
  29123171730 29149202286 29175210020 29201194994 29227157268 29253096898 29279013947
  29304908472)) (n4 (b8 29330780532 29356630185 29382457489 29408262502 29434045283 29459805887
  29485544374 29511260798) (b8 29536955217 29562627687 29588278266 29613907006 29639513967
  29665099201 29690662765 29716204714) (b8 29741725102 29767223985 29792701415 29818157448
  29843592137 29869005534 29894397696 29919768672) (b8 29945118519 29970447287 29995755029
  30021041798 30046307645 30071552624 30096776784 30121980177)) (n4 (b8 30147162856 30172324870
  30197466270 30222587108 30247687431 30272767295 30297826744 30322865832) (b8 30347884606
  30372883117 30397861413 30422819543 30447757557 30472675502 30497573427 30522451380) (b8
  30547309410 30572147563 30596965889 30621764433 30646543245 30671302367 30696041852 30720761743)
  (b8 30745462086 30770142931 30794804320 30819446301 30844068918 30868672221 30893256248
  30917821053))) (n4 (n4 (b8 30942366673 30966893159 30991400551 31015888898 31040358239
  31064808624 31089240093 31113652692) (b8 31138046462 31162421449 31186777696 31211115244
  31235434140 31259734423 31284016138 31308279325) (b8 31332524029 31356750291 31380958153
  31405147658 31429318845 31453471759 31477606438 31501722926) (b8 31525821261 31549901489
  31573963645 31598007775 31622033914 31646042107 31670032391 31694004808)) (n4 (b8 31717959396
  31741896198 31765815249 31789716593 31813600264 31837466307 31861314757 31885145655) (b8
  31908959038 31932754944 31956533415 31980294485 32004038196 32027764583 32051473685 32075165540)
  (b8 32098840185 32122497658 32146137996 32169761237 32193367415 32216956571 32240528739
  32264083958) (b8 32287622262 32311143689 32334648274 32358136055 32381607066 32405061344
  32428498925 32451919844)) (n4 (b8 32475324136 32498711838 32522082983 32545437607 32568775747
  32592097434 32615402707 32638691596) (b8 32661964141 32685220370 32708460323 32731684031
  32754891529 32778082850 32801258029 32824417099) (b8 32847560094 32870687045 32893797990
  32916892958 32939971985 32963035101 32986082342 33009113737) (b8 33032129324 33055129129
  33078113191 33101081537 33124034202 33146971217 33169892615 33192798426)) (n4 (b8 33215688684
  33238563419 33261422663 33284266448 33307094804 33329907764 33352705357 33375487616) (b8
  33398254572 33421006253 33443742694 33466463921 33489169968 33511860863 33534536639 33557197323)
  (b8 33579842948 33602473541 33625089135 33647689756 33670275439 33692846207 33715402097
  33737943131) (b8 33760469344 33782980762 33805477415 33827959333 33850426543 33872879076
  33895316959 33917740222))) (n4 (n4 (b8 33940148892 33962542998 33984922569 34007287632
  34029638216 34051974350 34074296060 34096603376) (b8 34118896324 34141174933 34163439231
  34185689243 34207924999 34230146525 34252353850 34274546999) (b8 34296726001 34318890881
  34341041669 34363178388 34385301068 34407409734 34429504413 34451585131) (b8 34473651916
  34495704791 34517743787 34539768926 34561780236 34583777744 34605761474 34627731452)) (n4 (b8
  34649687705 34671630258 34693559136 34715474367 34737375972 34759263982 34781138418 34802999307)
  (b8 34824846674 34846680543 34868500941 34890307890 34912101418 34933881547 34955648304
  34977401712) (b8 34999141797 35020868580 35042582090 35064282348 35085969381 35107643209
  35129303861 35150951357) (b8 35172585725 35194206985 35215815162 35237410281 35258992363
  35280561435 35302117516 35323660635)) (n4 (b8 35345190811 35366708069 35388212432 35409703923
  35431182566 35452648383 35474101398 35495541632) (b8 35516969110 35538383853 35559785885
  35581175227 35602551904 35623915935 35645267346 35666606157) (b8 35687932391 35709246071
  35730547218 35751835854 35773112002 35794375683 35815626920 35836865733) (b8 35858092146
  35879306178 35900507855 35921697193 35942874219 35964038950 35985191409 36006331618)) (n4 (b8
  36027459597 36048575369 36069678953 36090770372 36111849646 36132916796 36153971842 36175014807)
  (b8 36196045709 36217064572 36238071415 36259066258 36280049122 36301020028 36321978996
  36342926046) (b8 36363861199 36384784475 36405695894 36426595476 36447483242 36468359210
  36489223404 36510075839) (b8 36530916538 36551745520 36572562804 36593368411 36614162360
  36634944670 36655715361 36676474453))) (n4 (n4 (b8 36697221964 36717957915 36738682325
  36759395212 36780096597 36800786496 36821464933 36842131923) (b8 36862787486 36883431642
  36904064408 36924685805 36945295850 36965894563 36986481962 37007058065) (b8 37027622893
  37048176460 37068718790 37089249897 37109769802 37130278522 37150776076 37171262482) (b8
  37191737757 37212201921 37232654991 37253096986 37273527922 37293947820 37314356694
  37334754566)) (n4 (b8 37355141450 37375517366 37395882331 37416236363 37436579479 37456911697
  37477233035 37497543508) (b8 37517843137 37538131936 37558409925 37578677119 37598933537
  37619179195 37639414111 37659638301) (b8 37679851784 37700054574 37720246691 37740428151
  37760598970 37780759165 37800908754 37821047751) (b8 37841176175 37861294043 37881401371
  37901498175 37921584471 37941660277 37961725607 37981780481)) (n4 (b8 38001824911 38021858918
  38041882515 38061895718 38081898546 38101891012 38121873135 38141844928) (b8 38161806409
  38181757592 38201698496 38221629135 38241549525 38261459681 38281359621 38301249359) (b8
  38321128910 38340998293 38360857519 38380706608 38400545572 38420374428 38440193190 38460001876)
  (b8 38479800498 38499589075 38519367619 38539136149 38558894677 38578643219 38598381791
  38618110407)) (n4 (b8 38637829082 38657537832 38677236671 38696925614 38716604677 38736273874
  38755933220 38775582730) (b8 38795222417 38814852299 38834472388 38854082699 38873683248
  38893274048 38912855115 38932426462) (b8 38951988104 38971540056 38991082331 39010614946
  39030137912 39049651246 39069154961 39088649071) (b8 39108133591 39127608534 39147073916
  39166529749 39185976047 39205412826 39224840098 39244257879))))
def potTree1 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1177121919 1459147015 1726903190 1938423859 2132124486
  2315599158 2481393433) (b8 2635978593 2784096503 2923896723 3056455109 3184074082 3306782455
  3424628569 3538584574) (b8 3649065745 3756119378 3860084204 3961356848 4060052143 4156302626
  4250346804 4342341310) (b8 4432368165 4520556816 4607040200 4691899873 4775212238 4857071068
  4937552895 5016716049)) (n4 (b8 5094623892 5171339558 5246913878 5321393497 5394826810
  5467257709 5538724317 5609263953) (b8 5678912918 5747703804 5815666834 5882831545 5949225722
  6014874913 6079803501 6144034952) (b8 6207591219 6270492964 6332760037 6394411350 6455464737
  6515937202 6575845065 6635203849) (b8 6694028330 6752332671 6810130448 6867434622 6924257602
  6980611315 7036507196 7091956209)) (n4 (b8 7146968900 7201555403 7255725470 7309488483
  7362853474 7415829150 7468423910 7520645848) (b8 7572502774 7624002237 7675151526 7725957682
  7776427520 7826567626 7876384378 7925883950) (b8 7975072323 8023955289 8072538465 8120827300
  8168827077 8216542924 8263979818 8311142595) (b8 8358035949 8404664445 8451032519 8497144487
  8543004541 8588616768 8633985138 8679113524)) (n4 (b8 8724005689 8768665304 8813095949
  8857301104 8901284172 8945048460 8988597204 9031933556) (b8 9075060594 9117981319 9160698663
  9203215493 9245534604 9287658725 9329590531 9371332628) (b8 9412887571 9454257852 9495445910
  9536454132 9577284856 9617940361 9658422888 9698734622) (b8 9738877710 9778854248 9818666293
  9858315859 9897804916 9937135401 9976309206 10015328190))) (n4 (n4 (b8 10054194173 10092908942
  10131474246 10169891803 10208163301 10246290390 10284274691 10322117800) (b8 10359821277
  10397386657 10434815445 10472109121 10509269140 10546296924 10583193876 10619961375) (b8
  10656600773 10693113398 10729500557 10765763537 10801903598 10837921981 10873819909 10909598582)
  (b8 10945259177 10980802860 11016230770 11051544033 11086743753 11121831019 11156806902
  11191672457)) (n4 (b8 11226428717 11261076708 11295617434 11330051886 11364381036 11398605847
  11432727262 11466746214) (b8 11500663621 11534480386 11568197399 11601815538 11635335668
  11668758641 11702085297 11735316464) (b8 11768452956 11801495580 11834445130 11867302385
  11900068116 11932743087 11965328047 11997823734) (b8 12030230877 12062550200 12094782409
  12126928205 12158988282 12190963321 12222853990 12254660961)) (n4 (b8 12286384888 12318026414
  12349586177 12381064815 12412462945 12443781180 12475020131 12506180396) (b8 12537262565
  12568267221 12599194946 12630046305 12660821864 12691522176 12722147793 12752699256) (b8
  12783177101 12813581858 12843914051 12874174195 12904362803 12934480380 12964527422 12994504425)
  (b8 13024411878 13054250259 13084020045 13113721710 13143355717 13172922527 13202422594
  13231856368)) (n4 (b8 13261224297 13290526817 13319764363 13348937369 13378046258 13407091449
  13436073362 13464992409) (b8 13493848994 13522643521 13551376389 13580047994 13608658724
  13637208966 13665699101 13694129510) (b8 13722500563 13750812633 13779066085 13807261282
  13835398584 13863478344 13891500915 13919466646) (b8 13947375878 13975228954 14003026213
  14030767988 14058454608 14086086405 14113663700 14141186814))) (n4 (n4 (b8 14168656067
  14196071774 14223434246 14250743790 14278000716 14305205325 14332357915 14359458786) (b8
  14386508233 14413506544 14440454012 14467350920 14494197554 14520994193 14547741114 14574438599)
  (b8 14601086914 14627686332 14654237122 14680739551 14707193878 14733600368 14759959278
  14786270865) (b8 14812535380 14838753079 14864924210 14891049017 14917127749 14943160651
  14969147957 14995089909)) (n4 (b8 15020986746 15046838700 15072646004 15098408887 15124127581
  15149802309 15175433299 15201020771) (b8 15226564949 15252066047 15277524289 15302939884
  15328313049 15353643995 15378932933 15404180069) (b8 15429385613 15454549767 15479672735
  15504754718 15529795917 15554796531 15579756755 15604676784) (b8 15629556812 15654397033
  15679197634 15703958807 15728680738 15753363613 15778007616 15802612930)) (n4 (b8 15827179740
  15851708221 15876198555 15900650920 15925065491 15949442441 15973781946 15998084177) (b8
  16022349304 16046577497 16070768925 16094923754 16119042149 16143124276 16167170298 16191180373)
  (b8 16215154667 16239093337 16262996543 16286864437 16310697182 16334494931 16358257833
  16381986045) (b8 16405679718 16429339003 16452964046 16476554998 16500112005 16523635216
  16547124770 16570580818)) (n4 (b8 16594003500 16617392955 16640749327 16664072759 16687363383
  16710621341 16733846773 16757039809) (b8 16780200586 16803329243 16826425907 16849490713
  16872523793 16895525277 16918495294 16941433974) (b8 16964341444 16987217830 17010063263
  17032877861 17055661754 17078415063 17101137914 17123830425) (b8 17146492719 17169124917
  17191727139 17214299502 17236842123 17259355125 17281838617 17304292719))) (n4 (n4 (b8
  17326717546 17349113211 17371479827 17393817509 17416126367 17438406513 17460658057 17482881111)
  (b8 17505075780 17527242177 17549380406 17571490576 17593572795 17615627166 17637653795
  17659652786) (b8 17681624245 17703568272 17725484971 17747374444 17769236792 17791072115
  17812880515 17834662088) (b8 17856416936 17878145155 17899846843 17921522098 17943171016
  17964793691 17986390220 18007960698)) (n4 (b8 18029505217 18051023871 18072516756 18093983961
  18115425578 18136841700 18158232418 18179597818) (b8 18200937995 18222253036 18243543028
  18264808061 18286048222 18307263598 18328454278 18349620342) (b8 18370761882 18391878980
  18412971721 18434040188 18455084467 18476104639 18497100788 18518072995) (b8 18539021344
  18559945913 18580846784 18601724039 18622577756 18643408015 18664214894 18684998474)) (n4 (b8
  18705758832 18726496044 18747210188 18767901343 18788569584 18809214986 18829837624 18850437577)
  (b8 18871014914 18891569714 18912102050 18932611994 18953099620 18973565001 18994008208
  19014429314) (b8 19034828391 19055205508 19075560738 19095894151 19116205817 19136495804
  19156764183 19177011023) (b8 19197236390 19217440355 19237622986 19257784348 19277924510
  19298043538 19318141498 19338218457)) (n4 (b8 19358274482 19378309634 19398323983 19418317588
  19438290520 19458242838 19478174608 19498085893) (b8 19517976756 19537847257 19557697464
  19577527434 19597337231 19617126916 19636896551 19656646196) (b8 19676375910 19696085756
  19715775794 19735446081 19755096677 19774727643 19794339035 19813930914) (b8 19833503336
  19853056360 19872590044 19892104443 19911599618 19931075621 19950532513 19969970346)))) (n4 (n4
  (n4 (b8 19989389178 20008789066 20028170063 20047532224 20066875604 20086200261 20105506244
  20124793610) (b8 20144062413 20163312705 20182544539 20201757971 20220953051 20240129833
  20259288366 20278428706) (b8 20297550904 20316655009 20335741074 20354809151 20373859289
  20392891540 20411905952 20430902577) (b8 20449881466 20468842664 20487786226 20506712197
  20525620629 20544511567 20563385062 20582241162)) (n4 (b8 20601079916 20619901369 20638705570
  20657492566 20676262407 20695015135 20713750800 20732469449) (b8 20751171126 20769855878
  20788523751 20807174791 20825809042 20844426551 20863027363 20881611522) (b8 20900179071
  20918730059 20937264526 20955782518 20974284079 20992769251 21011238078 21029690606) (b8
  21048126874 21066546928 21084950809 21103338560 21121710223 21140065843 21158405457
  21176729110)) (n4 (b8 21195036843 21213328699 21231604714 21249864935 21268109401 21286338152
  21304551227 21322748670) (b8 21340930519 21359096814 21377247595 21395382904 21413502777
  21431607253 21449696374 21467770180) (b8 21485828705 21503871990 21521900077 21539913000
  21557910797 21575893509 21593861173 21611813826) (b8 21629751504 21647674247 21665582092
  21683475075 21701353232 21719216604 21737065222 21754899127)) (n4 (b8 21772718353 21790522938
  21808312915 21826088324 21843849196 21861595571 21879327480 21897044963) (b8 21914748053
  21932436783 21950111191 21967771311 21985417178 22003048824 22020666287 22038269597) (b8
  22055858790 22073433901 22090994965 22108542010 22126075075 22143594191 22161099392 22178590710)
  (b8 22196068179 22213531833 22230981701 22248417818 22265840218 22283248931 22300643990
  22318025426))) (n4 (n4 (b8 22335393272 22352747561 22370088322 22387415588 22404729392
  22422029762 22439316731 22456590332) (b8 22473850594 22491097545 22508331221 22525551651
  22542758863 22559952889 22577133762 22594301507) (b8 22611456157 22628597741 22645726291
  22662841835 22679944402 22697034021 22714110724 22731174538) (b8 22748225494 22765263617
  22782288941 22799301494 22816301300 22833288391 22850262798 22867224545)) (n4 (b8 22884173662
  22901110177 22918034120 22934945516 22951844393 22968730782 22985604708 23002466198) (b8
  23019315280 23036151985 23052976335 23069788359 23086588083 23103375539 23120150747 23136913738)
  (b8 23153664536 23170403173 23187129667 23203844052 23220546348 23237236588 23253914792
  23270580990) (b8 23287235205 23303877465 23320507795 23337126220 23353732766 23370327459
  23386910323 23403481384)) (n4 (b8 23420040669 23436588199 23453124002 23469648103 23486160525
  23502661294 23519150435 23535627970) (b8 23552093928 23568548329 23584991200 23601422563
  23617842444 23634250867 23650647855 23667033431) (b8 23683407622 23699770449 23716121936
  23732462107 23748790986 23765108595 23781414959 23797710098) (b8 23813994040 23830266804
  23846528415 23862778895 23879018267 23895246554 23911463779 23927669964)) (n4 (b8 23943865131
  23960049303 23976222504 23992384755 24008536075 24024676491 24040806024 24056924694) (b8
  24073032525 24089129537 24105215753 24121291195 24137355884 24153409841 24169453088 24185485648)
  (b8 24201507539 24217518784 24233519405 24249509423 24265488856 24281457730 24297416062
  24313363874) (b8 24329301187 24345228022 24361144399 24377050339 24392945863 24408830991
  24424705740 24440570137))) (n4 (n4 (b8 24456424199 24472267943 24488101394 24503924572
  24519737491 24535540176 24551332647 24567114922) (b8 24582887021 24598648963 24614400771
  24630142461 24645874052 24661595567 24677307022 24693008438) (b8 24708699834 24724381228
  24740052641 24755714090 24771365597 24787007177 24802638852 24818260639) (b8 24833872559
  24849474626 24865066864 24880649289 24896221919 24911784773 24927337870 24942881229)) (n4 (b8
  24958414866 24973938801 24989453050 25004957635 25020452569 25035937875 25051413569 25066879666)
  (b8 25082336187 25097783150 25113220572 25128648469 25144066862 25159475765 25174875198
  25190265177) (b8 25205645720 25221016844 25236378566 25251730905 25267073878 25282407498
  25297731787 25313046761) (b8 25328352434 25343648827 25358935955 25374213833 25389482480
  25404741914 25419992148 25435233201)) (n4 (b8 25450465089 25465687830 25480901438 25496105929
  25511301322 25526487632 25541664876 25556833069) (b8 25571992228 25587142369 25602283509
  25617415661 25632538843 25647653073 25662758364 25677854730) (b8 25692942193 25708020764
  25723090461 25738151294 25753203289 25768246454 25783280804 25798306357) (b8 25813323131
  25828331137 25843330391 25858320910 25873302708 25888275801 25903240203 25918195930)) (n4 (b8
  25933142998 25948081421 25963011211 25977932389 25992844966 26007748958 26022644377 26037531244)
  (b8 26052409568 26067279364 26082140651 26096993439 26111837746 26126673583 26141500968
  26156319914) (b8 26171130434 26185932543 26200726258 26215511590 26230288554 26245057166
  26259817437 26274569384) (b8 26289313020 26304048358 26318775413 26333494201 26348204731
  26362907021 26377601084 26392286933))) (n4 (n4 (b8 26406964581 26421634043 26436295333
  26450948465 26465593450 26480230304 26494859040 26509479671) (b8 26524092211 26538696674
  26553293072 26567881417 26582461727 26597034012 26611598285 26626154558) (b8 26640702850
  26655243169 26669775527 26684299942 26698816423 26713324986 26727825640 26742318402) (b8
  26756803282 26771280295 26785749451 26800210766 26814664250 26829109918 26843547782
  26857977853)) (n4 (b8 26872400146 26886814673 26901221445 26915620475 26930011776 26944395363
  26958771243 26973139431) (b8 26987499941 27001852783 27016197969 27030535514 27044865428
  27059187724 27073502412 27087809507) (b8 27102109021 27116400963 27130685349 27144962188
  27159231493 27173493276 27187747549 27201994322) (b8 27216233609 27230465422 27244689773
  27258906670 27273116129 27287318160 27301512776 27315699985)) (n4 (b8 27329879801 27344052238
  27358217302 27372375008 27386525368 27400668393 27414804090 27428932478) (b8 27443053563
  27457167356 27471273872 27485373120 27499465112 27513549857 27527627369 27541697657) (b8
  27555760735 27569816610 27583865296 27597906803 27611941143 27625968325 27639988362 27654001264)
  (b8 27668007040 27682005706 27695997268 27709981738 27723959128 27737929447 27751892707
  27765848918)) (n4 (b8 27779798092 27793740237 27807675366 27821603490 27835524617 27849438758
  27863345926 27877246130) (b8 27891139380 27905025686 27918905060 27932777512 27946643050
  27960501688 27974353435 27988198298) (b8 28002036293 28015867425 28029691708 28043509149
  28057319761 28071123551 28084920534 28098710714) (b8 28112494106 28126270718 28140040559
  28153803641 28167559972 28181309565 28195052424 28208788566))))
def potTree2 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1138140398 1307069440 1496007706 1696122344 1860050862
  1981795915 2096412582) (b8 2213703260 2332469493 2443068792 2539304256 2628681633 2716532744
  2805498741 2893102433) (b8 2975795254 3052898145 3126731193 3199868644 3272979317 3344890822
  3414145937 3480459220) (b8 3544815727 3608411763 3671650279 3734043365 3794885650 3853957998
  3911666313 3968616903)) (n4 (b8 4025086517 4080933312 4135858806 4189592855 4242316120
  4294338598 4345827182 4396838586) (b8 4447237052 4496857376 4545679656 4593842418 4641513190
  4688767305 4735569558 4781827858) (b8 4827484198 4872573326 4917193481 4961428936 5005297756
  5048759601 5091765121 5134304564) (b8 5176419365 5218171115 5259598424 5300698267 5341442172
  5381809001 5421806999 5461469911)) (n4 (b8 5500833595 5539913991 5578703476 5617185720
  5655354832 5693223557 5730815839 5768151646) (b8 5805236769 5842064796 5878628010 5914927615
  5950975556 5986787756 6022375108 6057739434) (b8 6092876804 6127784700 6162466999 6196933296
  6231193883 6265254763 6299116540 6332777463) (b8 6366237785 6399501923 6432577092 6465469920
  6498183903 6530719495 6563076456 6595256315)) (n4 (b8 6627263145 6659102221 6690777903
  6722292437 6753646468 6784840639 6815876939 6846758814) (b8 6877490107 6908073805 6938511553
  6968804200 6998952847 7028959513 7058827011 7088558179) (b8 7118155185 7147619372 7176951728
  7206153526 7235226639 7264173332 7292995761 7321695585) (b8 7350273994 7378732025 7407070977
  7435292501 7463398432 7491390456 7519269923 7547037905))) (n4 (n4 (b8 7574695450 7602243781
  7629684334 7657018611 7684247975 7711373566 7738396376 7765317404) (b8 7792137772 7818858724
  7845481501 7872007245 7898436948 7924771522 7951011898 7977159092) (b8 8003214173 8029178199
  8055052140 8080836876 8106533245 8132142104 8157664361 8183100945) (b8 8208452767 8233720670
  8258905445 8284007857 8309028688 8333968747 8358828850 8383609789)) (n4 (b8 8408312313
  8432937130 8457484942 8481956459 8506352403 8530673493 8554920430 8579093881) (b8 8603194491
  8627222897 8651179743 8675065676 8698881338 8722627350 8746304315 8769912817) (b8 8793453439
  8816926764 8840333373 8863673841 8886948730 8910158580 8933303930 8956385306) (b8 8979403239
  9002358254 9025250869 9048081594 9070850920 9093559336 9116207327 9138795373)) (n4 (b8
  9161323951 9183793531 9206204576 9228557535 9250852857 9273090983 9295272351 9317397397) (b8
  9339466551 9361480232 9383438853 9405342827 9427192555 9448988442 9470730883 9492420274) (b8
  9514056998 9535641435 9557173963 9578654951 9600084773 9621463790 9642792364 9664070848) (b8
  9685299594 9706478948 9727609252 9748690846 9769724069 9790709248 9811646713 9832536785)) (n4
  (b8 9853379788 9874176035 9894925840 9915629515 9936287364 9956899692 9977466797 9997988973) (b8
  10018466518 10038899719 10059288862 10079634230 10099936109 10120194773 10140410494 10160583548)
  (b8 10180714204 10200802723 10220849374 10240854417 10260818108 10280740702 10300622454
  10320463613) (b8 10340264424 10360025136 10379745989 10399427227 10419069082 10438671793
  10458235592 10477760711))) (n4 (n4 (b8 10497247376 10516695818 10536106255 10555478913
  10574814010 10594111763 10613372390 10632596101) (b8 10651783112 10670933629 10690047857
  10709126009 10728168279 10747174877 10766145999 10785081842) (b8 10803982606 10822848479
  10841679657 10860476332 10879238692 10897966923 10916661211 10935321740) (b8 10953948691
  10972542249 10991102587 11009629887 11028124322 11046586066 11065015294 11083412176)) (n4 (b8
  11101776883 11120109581 11138410437 11156679617 11174917283 11193123603 11211298733 11229442834)
  (b8 11247556065 11265638582 11283690542 11301712096 11319703403 11337664609 11355595867
  11373497328) (b8 11391369136 11409211441 11427024389 11444808123 11462562784 11480288516
  11497985464 11515653763) (b8 11533293552 11550904969 11568488152 11586043233 11603570350
  11621069634 11638541220 11655985235)) (n4 (b8 11673401810 11690791077 11708153161 11725488188
  11742796289 11760077584 11777332203 11794560264) (b8 11811761889 11828937202 11846086322
  11863209369 11880306462 11897377718 11914423255 11931443186) (b8 11948437628 11965406693
  11982350498 11999269155 12016162773 12033031465 12049875339 12066694505) (b8 12083489072
  12100259148 12117004839 12133726251 12150423490 12167096660 12183745863 12200371205)) (n4 (b8
  12216972788 12233550711 12250105078 12266635986 12283143537 12299627829 12316088961 12332527028)
  (b8 12348942127 12365334355 12381703807 12398050578 12414374763 12430676454 12446955744
  12463212723) (b8 12479447486 12495660121 12511850720 12528019373 12544166167 12560291193
  12576394534 12592476284) (b8 12608536525 12624575343 12640592826 12656589057 12672564122
  12688518102 12704451082 12720363146))) (n4 (n4 (b8 12736254374 12752124848 12767974651
  12783803861 12799612559 12815400824 12831168738 12846916375) (b8 12862643816 12878351138
  12894038417 12909705730 12925353155 12940980765 12956588636 12972176840) (b8 12987745457
  13003294556 13018824210 13034334494 13049825482 13065297241 13080749845 13096183364) (b8
  13111597872 13126993434 13142370122 13157728005 13173067155 13188387634 13203689514
  13218972865)) (n4 (b8 13234237749 13249484233 13264712388 13279922276 13295113966 13310287520
  13325443001 13340580480) (b8 13355700015 13370801672 13385885515 13400951606 13416000008
  13431030780 13446043988 13461039693) (b8 13476017955 13490978833 13505922391 13520848686
  13535757778 13550649727 13565524595 13580382436) (b8 13595223309 13610047273 13624854389
  13639644708 13654418290 13669175193 13683915473 13698639183)) (n4 (b8 13713346382 13728037125
  13742711465 13757369459 13772011161 13786636625 13801245904 13815839053) (b8 13830416125
  13844977174 13859522249 13874051407 13888564697 13903062170 13917543884 13932009884) (b8
  13946460223 13960894950 13975314119 13989717778 14004105976 14018478765 14032836193 14047178311)
  (b8 14061505164 14075816804 14090113279 14104394636 14118660922 14132912188 14147148477
  14161369841)) (n4 (b8 14175576324 14189767970 14203944830 14218106948 14232254369 14246387142
  14260505311 14274608918) (b8 14288698011 14302772635 14316832833 14330878650 14344910129
  14358927317 14372930255 14386918985) (b8 14400893551 14414853997 14428800367 14442732703
  14456651045 14470555436 14484445919 14498322533) (b8 14512185322 14526034326 14539869588
  14553691149 14567499045 14581293321 14595074014 14608841165)))) (n4 (n4 (n4 (b8 14622594817
  14636335007 14650061775 14663775160 14677475199 14691161934 14704835401 14718495641) (b8
  14732142693 14745776593 14759397377 14773005089 14786599759 14800181431 14813750136 14827305917)
  (b8 14840848808 14854378847 14867896068 14881400510 14894892207 14908371195 14921837513
  14935291194) (b8 14948732275 14962160790 14975576773 14988980261 15002371290 15015749892
  15029116103 15042469959)) (n4 (b8 15055811489 15069140731 15082457718 15095762485 15109055065
  15122335489 15135603795 15148860011) (b8 15162104171 15175336312 15188556463 15201764657
  15214960928 15228145306 15241317823 15254478512) (b8 15267627406 15280764535 15293889932
  15307003627 15320105651 15333196035 15346274811 15359342010) (b8 15372397663 15385441797
  15398474449 15411495643 15424505412 15437503785 15450490793 15463466466)) (n4 (b8 15476430832
  15489383921 15502325764 15515256388 15528175825 15541084100 15553981244 15566867287) (b8
  15579742255 15592606179 15605459087 15618301004 15631131964 15643951987 15656761109 15669559353)
  (b8 15682346749 15695123323 15707889103 15720644116 15733388388 15746121950 15758844825
  15771557043) (b8 15784258627 15796949608 15809630007 15822299856 15834959179 15847608001
  15860246350 15872874251)) (n4 (b8 15885491730 15898098812 15910695525 15923281892 15935857941
  15948423694 15960979179 15973524419) (b8 15986059441 15998584269 16011098928 16023603444
  16036097838 16048582138 16061056368 16073520551) (b8 16085974711 16098418873 16110853062
  16123277302 16135691613 16148096023 16160490555 16172875230) (b8 16185250075 16197615111
  16209970363 16222315850 16234651600 16246977636 16259293977 16271600646))) (n4 (n4 (b8
  16283897672 16296185072 16308462869 16320731087 16332989749 16345238873 16357478485 16369708608)
  (b8 16381929263 16394140471 16406342253 16418534632 16430717630 16442891268 16455055570
  16467210556) (b8 16479356243 16491492658 16503619819 16515737751 16527846471 16539946002
  16552036365 16564117579) (b8 16576189664 16588252645 16600306540 16612351368 16624387152
  16636413913 16648431668 16660440438)) (n4 (b8 16672440245 16684431108 16696413046 16708386080
  16720350232 16732305517 16744251958 16756189573) (b8 16768118382 16780038406 16791949662
  16803852172 16815745952 16827631023 16839507404 16851375114) (b8 16863234171 16875084597
  16886926408 16898759621 16910584260 16922400339 16934207878 16946006897) (b8 16957797412
  16969579443 16981353009 16993118125 17004874812 17016623087 17028362968 17040094476)) (n4 (b8
  17051817623 17063532431 17075238917 17086937098 17098626991 17110308617 17121981991 17133647131)
  (b8 17145304053 17156952775 17168593314 17180225690 17191849917 17203466014 17215073998
  17226673885) (b8 17238265689 17249849430 17261425128 17272992796 17284552452 17296104111
  17307647790 17319183504) (b8 17330711273 17342231112 17353743038 17365247066 17376743212
  17388231494 17399711924 17411184522)) (n4 (b8 17422649306 17434106286 17445555482 17456996909
  17468430582 17479856516 17491274730 17502685237) (b8 17514088053 17525483193 17536870675
  17548250511 17559622717 17570987310 17582344307 17593693719) (b8 17605035563 17616369855
  17627696607 17639015836 17650327560 17661631789 17672928542 17684217830) (b8 17695499669
  17706774075 17718041062 17729300644 17740552837 17751797654 17763035111 17774265220))) (n4 (n4
  (b8 17785487997 17796703458 17807911615 17819112482 17830306076 17841492407 17852671493
  17863843344) (b8 17875007978 17886165407 17897315646 17908458708 17919594607 17930723357
  17941844970 17952959463) (b8 17964066846 17975167137 17986260346 17997346489 18008425577
  18019497623 18030562644 18041620650) (b8 18052671657 18063715677 18074752724 18085782808
  18096805945 18107822150 18118831430 18129833805)) (n4 (b8 18140829284 18151817880 18162799606
  18173774477 18184742504 18195703699 18206658076 18217605650) (b8 18228546429 18239480427
  18250407659 18261328135 18272241869 18283148875 18294049160 18304942741) (b8 18315829629
  18326709836 18337583376 18348450259 18359310500 18370164108 18381011095 18391851478) (b8
  18402685263 18413512466 18424333096 18435147169 18445954694 18456755683 18467550146
  18478338100)) (n4 (b8 18489119552 18499894518 18510663007 18521425028 18532180597 18542929724
  18553672421 18564408701) (b8 18575138571 18585862047 18596579138 18607289855 18617994212
  18628692219 18639383886 18650069224) (b8 18660748247 18671420965 18682087387 18692747528
  18703401396 18714049002 18724690360 18735325477) (b8 18745954369 18756577042 18767193510
  18777803781 18788407867 18799005783 18809597534 18820183132)) (n4 (b8 18830762591 18841335916
  18851903124 18862464221 18873019218 18883568128 18894110961 18904647725) (b8 18915178434
  18925703094 18936221720 18946734318 18957240904 18967741482 18978236070 18988724668) (b8
  18999207295 19009683955 19020154665 19030619427 19041078259 19051531168 19061978161 19072419250)
  (b8 19082854448 19093283760 19103707199 19114124777 19124536499 19134942377 19145342421
  19155736641))) (n4 (n4 (b8 19166125046 19176507647 19186884454 19197255475 19207620719
  19217980197 19228333921 19238681894) (b8 19249024134 19259360644 19269691437 19280016519
  19290335904 19300649597 19310957612 19321259953) (b8 19331556636 19341847664 19352133049
  19362412800 19372686927 19382955439 19393218344 19403475653) (b8 19413727373 19423973515
  19434214086 19444449098 19454678557 19464902475 19475120861 19485333718)) (n4 (b8 19495541063
  19505742899 19515939237 19526130088 19536315460 19546495358 19556669797 19566838778) (b8
  19577002316 19587160419 19597313094 19607460350 19617602198 19627738642 19637869693 19647995361)
  (b8 19658115652 19668230578 19678340145 19688444362 19698543238 19708636779 19718724996
  19728807897) (b8 19738885491 19748957785 19759024789 19769086509 19779142954 19789194133
  19799240054 19809280727)) (n4 (b8 19819316158 19829346356 19839371328 19849391083 19859405629
  19869414975 19879419129 19889418097) (b8 19899411892 19909400515 19919383978 19929362290
  19939335456 19949303486 19959266388 19969224171) (b8 19979176839 19989124403 19999066869
  20009004246 20018936541 20028863764 20038785921 20048703020) (b8 20058615067 20068522073
  20078424041 20088320985 20098212909 20108099820 20117981729 20127858637)) (n4 (b8 20137730557
  20147597496 20157459461 20167316459 20177168497 20187015587 20196857730 20206694934) (b8
  20216527212 20226354566 20236177007 20245994540 20255807174 20265614916 20275417770 20285215747)
  (b8 20295008854 20304797098 20314580486 20324359024 20334132721 20343901583 20353665616
  20363424831) (b8 20373179234 20382928829 20392673626 20402413629 20412148850 20421879291
  20431604963 20441325872))))
def potTree3 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1132394210 1255328321 1378187927 1501087533 1624027139
  1747006745 1870026351) (b8 1992295478 2060777683 2129299888 2197862093 2266464298 2335106503
  2403788708 2472510913) (b8 2541273118 2610075323 2668852323 2718279605 2767746887 2817254169
  2866801451 2916388733) (b8 2966016015 3015683297 3065390579 3115137861 3164925143 3205603117
  3245435064 3285307011)) (n4 (b8 3325218958 3365170905 3405162852 3445194799 3485266746
  3525378693 3565530640 3605722587) (b8 3642337941 3676253325 3710208709 3744204093 3778239477
  3812314861 3846430245 3880585629) (b8 3914781013 3949016397 3983291781 4017607165 4048535807
  4078460804 4108425801 4138430798) (b8 4168475795 4198560792 4228685789 4258850786 4289055783
  4319300780 4349585777 4379910774)) (n4 (b8 4407791575 4434789186 4461826797 4488904408
  4516022019 4543179630 4570377241 4597614852) (b8 4624892463 4652210074 4679567685 4706965296
  4733149459 4757884470 4782659481 4807474492) (b8 4832329503 4857224514 4882159525 4907134536
  4932149547 4957204558 4982299569 5007434580) (b8 5032292847 5055505883 5078470755 5101475627
  5124520499 5147605371 5170730243 5193895115)) (n4 (b8 5217099987 5240344859 5263629731
  5286954603 5310319475 5332848868 5354339900 5375857126) (b8 5397414352 5419011578 5440648804
  5462326030 5484043256 5505800482 5527597708 5549434934) (b8 5571312160 5593135730 5613874708
  5634135361 5654436014 5674776667 5695157320 5715577973) (b8 5736038626 5756539279 5777079932
  5797660585 5818281238 5838941891 5859470328 5878842325))) (n4 (n4 (b8 5898064630 5917326935
  5936629240 5955971545 5975353850 5994776155 6014238460 6033740765) (b8 6053283070 6072865375
  6092487680 6111854364 6130213888 6148538433 6166902978 6185305301) (b8 6203747624 6222229947
  6240752270 6259314593 6277916916 6296559239 6315241562 6333963885) (b8 6352348425 6369879036
  6387418588 6404994094 6422606454 6440258814 6457951174 6475683534)) (n4 (b8 6493455894
  6511268254 6529120614 6547012974 6564945334 6582509015 6599328788 6616175804) (b8 6633046686
  6649957568 6666908450 6683899332 6700930214 6718001096 6735111978 6752262860) (b8 6769453742
  6786684624 6803568442 6819763862 6835990431 6852232256 6868514081 6884835906) (b8 6901197731
  6917599556 6934041381 6950523206 6967045031 6983606856 7000208681 7016523950)) (n4 (b8
  7032165948 7047824190 7063498553 7079212916 7094967279 7110761642 7126596005 7142470368) (b8
  7158384731 7174339094 7190333457 7206367820 7222175458 7237348210 7252485883 7267644818) (b8
  7282843753 7298082688 7313361623 7328680558 7344039493 7359438428 7374877363 7390356298) (b8
  7405875233 7421223383 7435996919 7450658407 7465346188 7480073969 7494841750 7509649531)) (n4
  (b8 7524497312 7539385093 7554312874 7569280655 7584288436 7599336217 7614263190 7628684659) (b8
  7642922856 7657177538 7671472220 7685806902 7700181584 7714596266 7729050948 7743545630) (b8
  7758080312 7772654994 7787269676 7801806391 7815910371 7829776015 7843630860 7857525705) (b8
  7871460550 7885435395 7899450240 7913505085 7927599930 7941734775 7955909620 7970124465))) (n4
  (n4 (b8 7984296467 7998108702 8011646991 8025131507 8038655985 8052220463 8065824941 8079469419)
  (b8 8093153897 8106878375 8120642853 8134447331 8148291809 8162120871 8175660130 8188909692) (b8
  8202060428 8215239849 8228459270 8241718691 8255018112 8268357533 8281736954 8295156375) (b8
  8308615796 8322115217 8335620462 8348900317 8361892770 8374744772 8387601844 8400498916)) (n4
  (b8 8413435988 8426413060 8439430132 8452487204 8465584276 8478721348 8491898420 8505096912) (b8
  8518127296 8530887312 8543473192 8556030446 8568625552 8581260658 8593935764 8606650870) (b8
  8619405976 8632201082 8645036188 8657911294 8670818643 8683607198 8696153016 8708502044) (b8
  8720786912 8733097921 8745448930 8757839939 8770270948 8782741957 8795252966 8807803975)) (n4
  (b8 8820394984 8833025740 8845578738 8857923236 8870060401 8882099616 8894143414 8906227212) (b8
  8918351010 8930514808 8942718606 8954962404 8967246202 8979570000 8991933798 9004256953) (b8
  9016408763 9028354344 9040173172 9051969482 9063800603 9075671724 9087582845 9099533966) (b8
  9111525087 9123556208 9135627329 9147738450 9159836221 9171800853 9183570440 9195191863)) (n4
  (b8 9206762175 9218353832 9229985489 9241657146 9253368803 9265120460 9276912117 9288743774) (b8
  9300615431 9312493201 9324273784 9335878585 9347322615 9358688067 9370054467 9381458759) (b8
  9392903051 9404387343 9415911635 9427475927 9439080219 9450724511 9462388339 9473986874) (b8
  9485434276 9496717376 9507898151 9519056693 9530244513 9541472333 9552740153 9564047973))) (n4
  (n4 (b8 9575395793 9586783613 9598211433 9609667955 9621086119 9632380417 9643515486 9654529978)
  (b8 9665498251 9676480628 9687502126 9698563624 9709665122 9720806620 9731988118 9743209616) (b8
  9754465794 9765705412 9776848874 9787845150 9798709447 9809504839 9820295888 9831120177) (b8
  9841984466 9852888755 9863833044 9874817333 9885841622 9896904501 9907967902 9918961424)) (n4
  (b8 9929824973 9940552440 9951191375 9961805770 9972441867 9983117700 9993833533 10004589366)
  (b8 10015385199 10026221032 10037096865 10047986904 10058830762 10069565117 10080166117
  10090663629) (b8 10101116160 10111575746 10122070973 10132606200 10143181427 10153796654
  10164451881 10175147108) (b8 10185867037 10196561460 10207168143 10217650109 10228019295
  10238324485 10248619827 10258941794)) (n4 (b8 10269303761 10279705728 10290147695 10300629662
  10311151629 10321705004 10332250362 10342729711) (b8 10353097464 10363349010 10373520565
  10383664301 10393822808 10404018109 10414253410 10424528711) (b8 10434844012 10445199313
  10455590337 10465987492 10476339036 10486595225 10496737486 10506787717) (b8 10516792550
  10526798006 10536833002 10546907998 10557022994 10567177990 10577372986 10587606247)) (n4 (b8
  10597856404 10608079535 10618225177 10628263944 10638203419 10648081794 10657945034 10667828073)
  (b8 10677748457 10687708841 10697709225 10707749609 10717829877 10727935025 10738029136
  10748064038) (b8 10758002973 10767840448 10777603683 10787335909 10797075927 10806847396
  10816658845 10826510294) (b8 10836401743 10846333192 10856295879 10866260660 10876183889
  10886024932 10895766906 10905425224)))) (n4 (n4 (n4 (b8 10915037497 10924643922 10934273618
  10943941135 10953648652 10963396169 10973183686 10983006489) (b8 10992842290 11002652817
  11012396243 11022047190 11031609284 11041112011 11050594673 11060090397) (b8 11069618939
  11079187342 11088795745 11098444148 11108130210 11117837722 11127534471 11137179739) (b8
  11146742266 11156215009 11165617992 11174986702 11184356715 11193752518 11203186169
  11212659820)) (n4 (b8 11222173471 11231726284 11241306793 11250888833 11260434797 11269910081
  11279298511 11288610032) (b8 11297874610 11307127441 11316397210 11325700799 11335043950
  11344427101 11353850096 11363305518) (b8 11372772388 11382217661 11391605560 11400912956
  11410140139 11419309335 11428454048 11437605123) (b8 11446783899 11456000584 11465257269
  11474553954 11483886248 11493238130 11502581373 11511880863)) (n4 (b8 11521109102 11530257104
  11539339388 11548384502 11557424661 11566484738 11575578988 11584712941) (b8 11593886894
  11603098464 11612335935 11621575945 11630785687 11639935105 11649008082 11658009945) (b8
  11666964105 11675901221 11684849056 11693825856 11702840521 11711895186 11720988750 11730112825)
  (b8 11739248695 11748367303 11757437341 11766437436 11775364569 11784235315 11793077528
  11801920010)) (n4 (b8 11810784570 11819683919 11828622579 11837600805 11846612978 11855644465
  11864670257 11873659697) (b8 11882587997 11891444565 11900238714 11908993591 11917737958
  11926496175 11935284346 11944110429) (b8 11952976154 11961878084 11970805414 11979736931
  11988644343 11997500573 12006289469 12015012548) (b8 12023687577 12032341131 12040998981
  12049681036 12058397770 12067153778 12075947603 12084771282))) (n4 (n4 (b8 12093607701
  12102431279 12111214650 12119937256 12128593725 12137195323 12145765061 12154329447) (b8
  12162910264 12171521830 12180171047 12188858668 12197579776 12206320483 12215058747 12223767688)
  (b8 12232424415 12241017197 12249551051 12258044098 12266521319 12275006629 12283517206
  12292063002) (b8 12300646808 12309266424 12317911347 12326562758 12335195859 12343785937
  12352317164 12360787468)) (n4 (b8 12369210154 12377606985 12386002819 12394417030 12402862671
  12411345445 12419865216 12428414600) (b8 12436978021 12445533413 12454055794 12462526127
  12470936337 12479293800 12487616929 12495929271) (b8 12504252420 12512601834 12520986243
  12529407968 12537862378 12546337388 12554813227 12563266459) (b8 12571675565 12580027901
  12588324795 12596580122 12604815074 12613052440 12621310028 12629599305)) (n4 (b8 12637925155
  12646285543 12654671715 12663066774 12671448987 12679795895 12688091480 12696331370) (b8
  12704524022 12712688018 12720845187 12729015562 12737213045 12745445438 12753713040 12762010448)
  (b8 12770323855 12778633290 12786916533 12795155404 12803340682 12811475248 12819573790
  12827656685) (b8 12835745018 12843854566 12851996168 12860173108 12868381799 12876612649
  12884847730 12893065899)) (n4 (b8 12901247554 12909379284 12917459431 12925497603 12933512037
  12941523096 12949549474 12957603292) (b8 12965691279 12973812620 12981960244 12990119693
  12998271114 13006394254 13014473058 13022501243) (b8 13030483452 13038434754 13046374346
  13054321631 13062291484 13070292922 13078328267 13086392675) (b8 13094475254 13102558268
  13110621311 13118646767 13126624344 13134554549 13142447582 13150320837))) (n4 (n4 (b8
  13158194097 13166083806 13174001505 13181952258 13189934364 13197939238 13205951983 13213953449)
  (b8 13221924798 13229852742 13237733020 13245572295 13253384395 13261188765 13269002476
  13276839675) (b8 13284707898 13292608396 13300535514 13308476657 13316414537 13324330414
  13332208505 13340040907) (b8 13347829632 13355585893 13363325984 13371068534 13378828810
  13386617085 13394437097 13402286193)) (n4 (b8 13410154902 13418027516 13425886318 13433714226
  13441499720 13449240629 13456944563 13464625786) (b8 13472301602 13479988915 13487700134
  13495441574 13503212995 13511008745 13518814626 13526614452) (b8 13534390677 13542129473
  13549824792 13557480190 13565106853 13572720752 13580339277 13587976791) (b8 13595641500
  13603336792 13611058691 13618797003 13626536024 13634259070 13641950867 13649601506)) (n4 (b8
  13657211083 13664787227 13672344154 13679898112 13687465146 13695056200 13702676614 13710325038)
  (b8 13717994480 13725671491 13733339762 13740983101 13748589822 13756155645 13763684755
  13771188889) (b8 13778682941 13786183384 13793703540 13801250806 13808826600 13816426899
  13824040354 13831652001) (b8 13839245619 13846808240 13854331553 13861816261 13869271477
  13876710359 13884148386 13891600671)) (n4 (b8 13899077008 13906581656 13914112323 13921661211
  13929214730 13936757071 13944274434 13951756089) (b8 13959198568 13966608160 13973995852
  13981375942 13988764073 13996172213 14003606758 14011068708) (b8 14018551928 14026045744
  14033535659 14041006400 14048445758 14055848119 14063214608 14070554998) (b8 14077881193
  14085209191 14092552037 14099918593 14107312230 14114729895 14122162696 14129598268))) (n4 (n4
  (b8 14137020852 14144417974 14151780259 14159106542 14166402195 14173679062 14180950743
  14188231656) (b8 14195532462 14202859400 14210211232 14217582687 14224961823 14232335103
  14239688475 14247010930) (b8 14254298400 14261552764 14268783039 14276002637 14283225619
  14290463368 14297724975 14305012023) (b8 14312320856 14319643069 14326964962 14334273384
  14341555810 14348804911 14356020066 14363207556)) (n4 (b8 14370378638 14377546858 14384725410
  14391923730 14399146572 14406393097 14413656807 14420926216) (b8 14428187991 14435429205
  14442640748 14449818430 14456965432 14464091589 14471209310 14478331127) (b8 14485469139
  14492629628 14499813967 14507018512 14514234186 14521447585 14528646189 14535819780) (b8
  14542961117 14550069854 14557154315 14564224691 14571293882 14578373944 14585474157
  14592597354)) (n4 (b8 14599742522 14606902830 14614066796 14621221644 14628355926 14635461170
  14642533936 14649579195) (b8 14656605790 14663625488 14670651263 14677692541 14684756376
  14691842233 14698946776 14706059496) (b8 14713168831 14720262880 14727331762 14734369692
  14741378406 14748363895 14755338103 14762312306) (b8 14769297978 14776303424 14783330886
  14790378512 14797439335 14804501922 14811554290 14818586004)) (n4 (b8 14825589974 14832563128
  14839511127 14846442300 14853368539 14860301747 14867250704 14874220847) (b8 14881211635
  14888219424 14895233667 14902243558 14909237264 14916205973 14923145732 14930057446) (b8
  14936949233 14943830862 14950714158 14957609437 14964523600 14971458714 14978412199 14985377022)
  (b8 14992342629 14999297276 15006230874 15013136970 15020015078 15026869550 15033709883
  15040546623))))
def potTree4 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1121961376 1223678663 1303042667 1382566671 1462250675
  1542094679 1622098683) (b8 1702262687 1782586691 1863070695 1943714699 2024518703 2084426111
  2122740468 2161214825) (b8 2199849182 2238643539 2277597896 2316712253 2355986610 2395420967
  2435015324 2474769681) (b8 2514684038 2554758395 2594992752 2635387109 2675941466 2716655823
  2757530180 2783095339)) (n4 (b8 2808820498 2834705657 2860750816 2886955975 2913321134
  2939846293 2966531452 2993376611) (b8 3020381770 3047546929 3074872088 3102357247 3130002406
  3157807565 3185772724 3213897883) (b8 3242183042 3270628201 3299233360 3322403992 3342132909
  3362021826 3382070743 3402279660) (b8 3422648577 3443177494 3463866411 3484715328 3505724245
  3526893162 3548222079 3569710996)) (n4 (b8 3591359913 3613168830 3635137747 3657266664
  3679555581 3702004498 3724613415 3747382332) (b8 3770311249 3789152530 3805608823 3822058161
  3838667499 3855436837 3872366175 3889455513) (b8 3906704851 3924050473 3941556095 3959221717
  3977047339 3995032961 4013178583 4031484205) (b8 4049949827 4068575449 4087361071 4106306693
  4125412315 4144677937 4164103559 4183689181)) (n4 (b8 4200069684 4214222051 4228534418
  4243006785 4257639152 4272431519 4287383886 4302256519) (b8 4317289152 4332481785 4347834418
  4363347051 4379019684 4394852317 4410768442 4426844567) (b8 4443080692 4459476817 4476032942
  4492749067 4509625192 4526661317 4543857442 4561213567) (b8 4574290916 4587079316 4600027716
  4613136116 4626404516 4639689490 4652917942 4666212583))) (n4 (n4 (b8 4679667224 4693281865
  4707056506 4720991147 4735085788 4749198011 4763444945 4777834709) (b8 4792384473 4807094237
  4821926800 4836919363 4852071926 4867384489 4882857052 4898489615) (b8 4911372794 4923150193
  4935087592 4947136526 4959183573 4971238424 4983202627 4995258097) (b8 5007473567 5019849037
  5032384507 5045079977 5057925927 5070778852 5083668509 5096701911)) (n4 (b8 5109891022
  5123240133 5136695542 5150277267 5164018992 5177920717 5191982442 5206204167) (b8 5220486471
  5231470600 5242550844 5253639730 5264727414 5275765261 5286781374 5297824426) (b8 5309024062
  5320383698 5331903334 5343582970 5355422606 5367255437 5379129636 5391042451) (b8 5403082716
  5415281369 5427637213 5440062634 5452606972 5465300981 5478154990 5491168999)) (n4 (b8
  5504343008 5517660289 5528161763 5538472218 5548738749 5558989756 5569249791 5579477226) (b8
  5589810933 5600304640 5610958347 5621772054 5632745761 5643770140 5654806869 5665871098) (b8
  5676980257 5688183945 5699536348 5711044056 5722626378 5734289011 5746077964 5758025556) (b8
  5770133148 5782400740 5794828332 5805604487 5815216521 5824837973 5834438328 5844065903)) (n4
  (b8 5853667180 5863400924 5873294668 5883348412 5893562156 5903906037 5914246750 5924612289) (b8
  5935000472 5945427398 5955923003 5966537864 5977306524 5988170090 5999098971 6010111375) (b8
  6021251772 6032552169 6044012566 6055632963 6067073632 6076139123 6085221481 6094296254) (b8
  6103387938 6112457461 6121669292 6131041123 6140572954 6150262304 6160049328 6169825461))) (n4
  (n4 (b8 6179609608 6189421361 6199263113 6209154557 6219130654 6229236814 6239470885 6249763844)
  (b8 6260129981 6270578670 6281149146 6291876759 6302764372 6313811985 6323691363 6332315077) (b8
  6340934458 6349574637 6358177230 6366926899 6375836568 6384906237 6394130463 6403428558) (b8
  6412725326 6422016927 6431322312 6440658074 6450029417 6459457646 6468979284 6478632135)) (n4
  (b8 6488372050 6498171039 6508040993 6517992461 6528055564 6538266744 6548637924 6559169104) (b8
  6567965001 6576185853 6584443111 6592627408 6600961298 6609455188 6618109078 6626919328) (b8
  6635793500 6644664711 6653536658 6662407061 6671293905 6680213573 6689171686 6698190446) (b8
  6707305765 6716551448 6725842873 6735202914 6744630762 6754137575 6763745099 6773487091)) (n4
  (b8 6783385523 6793443955 6801500199 6809401707 6817233262 6825188027 6833302792 6841577557) (b8
  6850010527 6858515359 6867016997 6875512752 6884010673 6892509039 6901024896 6909575333) (b8
  6918165404 6926816810 6935564675 6944433771 6953335393 6962295633 6971325523 6980430241) (b8
  6989626663 6998941415 7008403007 7018023286 7025596848 7033142545 7040751573 7048516816)) (n4
  (b8 7056442059 7064526866 7072696619 7080870112 7089036847 7097199667 7105365491 7113533223) (b8
  7121718203 7129937525 7138196769 7146516751 7154930475 7163454939 7172010724 7180611940) (b8
  7189278077 7198016878 7206838917 7215765772 7224823815 7234005352 7241291462 7248592885) (b8
  7256032836 7263632787 7271392738 7279252940 7287133245 7295005478 7302873196 7310737683))) (n4
  (n4 (b8 7318605342 7326476690 7334363814 7342283240 7350243349 7358261413 7366368838 7374580905)
  (b8 7382823392 7391103553 7399437270 7407839784 7416319683 7424892057 7433579749 7442395941) (b8
  7449491419 7456630811 7463925356 7471379901 7478950129 7486562122 7494169811 7501771943) (b8
  7509369934 7516965569 7524564258 7532166731 7539784004 7547431095 7555117447 7562859261)) (n4
  (b8 7570683882 7578610591 7586569275 7594558657 7602592325 7610684887 7618850357 7627097840) (b8
  7635445901 7643914628 7650968970 7657975283 7665141262 7672436129 7679795969 7687164407) (b8
  7694525743 7701882743 7709236421 7716586941 7723940858 7731299427 7738670324 7746068318) (b8
  7753503698 7760990538 7768553584 7776214080 7783918282 7791644299 7799404840 7807214852)) (n4
  (b8 7815088634 7823038429 7831075415 7839218601 7846342847 7853233650 7860264128 7867382477) (b8
  7874529011 7881672624 7888810122 7895942874 7903073681 7910200789 7917330883 7924465280) (b8
  7931611277 7938780088 7945983537 7953235525 7960555562 7967967156 7975437325 7982925631) (b8
  7990439944 7997991923 8005597989 8013271052 8021022462 8028867096 8036138278 8042913990)) (n4
  (b8 8049797294 8056730976 8063674873 8070612341 8077543815 8084472166 8091397297 8098320300) (b8
  8105243843 8112173388 8119110891 8126069331 8133058057 8140091611 8147187240 8154365954) (b8
  8161614879 8168888082 8176178244 8183498466 8190859360 8198277220 8205764964 8213334426) (b8
  8220801668 8227453950 8234180200 8240934219 8247688329 8254436633 8261179714 8267917603)))) (n4
  (n4 (n4 (b8 8274654503 8281388581 8288122543 8294861788 8301608262 8308370896 8315161566
  8321991634) (b8 8328877636 8335839559 8342876110 8349951989 8357040219 8364148137 8371288750
  8378473270) (b8 8385717507 8393032775 8400401268 8407237801 8413807151 8420388847 8426967951
  8433540790) (b8 8440108755 8446672129 8453234011 8459793006 8466352864 8472914779 8479483672
  8486066011)) (n4 (b8 8492672231 8499313455 8506003463 8512762113 8519595678 8526484355
  8533389802 8540306778) (b8 8547246244 8554219597 8561240642 8568320658 8575471728 8582520115
  8589024914 8595444993) (b8 8601861783 8608272451 8614677979 8621079056 8627478166 8633874211
  8640271595 8646669825) (b8 8653072986 8659488764 8665922891 8672388170 8678896558 8685463682
  8692105446 8698809089)) (n4 (b8 8705545834 8712291789 8719049180 8725830908 8732649803
  8739516377 8746443789 8753425876) (b8 8760109615 8766411424 8772676369 8778936763 8785190362
  8791440442 8797688722 8803933450) (b8 8810178541 8816424616 8822674529 8828933799 8835208600
  8841509368 8847848275 8854237832) (b8 8860694841 8867221387 8873794122 8880381105 8886977370
  8893586393 8900222084 8906893850)) (n4 (b8 8913615775 8920399204 8927209068 8933549169
  8939686928 8945805504 8951918849 8958026851) (b8 8964134344 8970237601 8976340634 8982443237
  8988549842 8994664240 9000789865 9006938387) (b8 9013118425 9019342202 9025626674 9031978812
  9038389636 9044830007 9051275703 9057732402) (b8 9064202110 9070700677 9077234558 9083819783
  9090465836 9097025329 9103129389 9109121213))) (n4 (n4 (b8 9115103625 9121080451 9127054126
  9133026081 9138996381 9144965688 9150935934 9156915213) (b8 9162902973 9168907837 9174939951
  9181008330 9187131358 9193317738 9199568296 9205861836) (b8 9212172848 9218486611 9224810800
  9231150485 9237517554 9243921592 9250378168 9256892159) (b8 9263177696 9269101633 9274961017
  9280814397 9286665346 9292511536 9298358474 9304202277)) (n4 (b8 9310048136 9315896452
  9321756346 9327627406 9333520348 9339445640 9345416889 9351446537) (b8 9357538105 9363686219
  9369864466 9376051087 9382240424 9388441311 9394657908 9400900777) (b8 9407180742 9413515109
  9419905616 9425915570 9431689378 9437425622 9443160256 9448891168) (b8 9454619486 9460346552
  9466073956 9471803606 9477537923 9483285411 9489049289 9494840970)) (n4 (b8 9500671177
  9506551233 9512493003 9518493012 9524538965 9530599826 9536669633 9542741049) (b8 9548825783
  9554924541 9561050643 9567213497 9573432062 9579655450 9585447569 9591091826) (b8 9596716054
  9602338218 9607954071 9613570303 9619187609 9624803993 9630424843 9636053230) (b8 9641699554
  9647363254 9653061810 9658804496 9664598452 9670456411 9676366255 9682308474)) (n4 (b8
  9688255533 9694215525 9700176992 9706150415 9712137111 9718154650 9724205059 9730312264) (b8
  9736340519 9741963554 9747492916 9753010267 9758523770 9764035499 9769546154 9775058289) (b8
  9780570423 9786089892 9791621048 9797169663 9802743058 9808355476 9814016116 9819730690) (b8
  9825506857 9831325496 9837163050 9843003154 9848856320 9854716261 9860584011 9866463940))) (n4
  (n4 (b8 9872375735 9878321582 9884323075 9890146841 9895631829 9901053317 9906468246 9911883572)
  (b8 9917294957 9922707087 9928117946 9933534433 9938957487 9944398013 9949855678 9955345736) (b8
  9960877878 9966461465 9972103860 9977798623 9983520013 9989256408 9994998730 10000751371) (b8
  10006510587 10012278345 10018060252 10023869953 10029716305 10035614368 10041239217
  10046601619)) (n4 (b8 10051925785 10057245447 10062564374 10067882887 10073200079 10078516669
  10083840225 10089176466) (b8 10094528280 10099903991 10105317030 10110775763 10116285509
  10121857181 10127466848 10133095043) (b8 10138734076 10144381065 10150040472 10155704639
  10161376970 10167064781 10172776906 10178527671) (b8 10184321851 10189758975 10195013053
  10200244402 10205475177 10210702851 10215932354 10221157382)) (n4 (b8 10226386896 10231624672
  10236878675 10242147732 10247446858 10252788513 10258178335 10263620053) (b8 10269116278
  10274644767 10280179830 10285727978 10291283598 10296853073 10302425078 10308009011) (b8
  10313605854 10319225276 10324883994 10330551236 10335834745 10340993184 10346139626 10351281890)
  (b8 10356423614 10361568595 10366708870 10371852924 10377012300 10382187406 10387379885
  10392608240)) (n4 (b8 10397881503 10403206938 10408582602 10414006014 10419448816 10424894339
  10430353873 10435826131) (b8 10441308749 10446793826 10452291738 10457801501 10463335245
  10468903210 10474431512 10479591091) (b8 10484657602 10489720378 10494782793 10499844966
  10504903117 10509964580 10515030702 10520116025) (b8 10525213152 10530337738 10535500111
  10540709534 10545970954 10551282102 10556629851 10561988513))) (n4 (n4 (b8 10567351551
  10572726515 10578117284 10583516930 10588918484 10594335828 10599762632 10605212578) (b8
  10610695009 10616082066 10621126687 10626116052 10631099670 10636083079 10641066396 10646045681)
  (b8 10651032581 10656027168 10661036030 10666064408 10671126702 10676224668 10681374479
  10686574765) (b8 10691818922 10697089879 10702369995 10707653242 10712950146 10718260613
  10723581322 10728903364)) (n4 (b8 10734240943 10739587038 10744958224 10750359069 10755601911
  10760552484 10765463732 10770371974) (b8 10775281245 10780187238 10785097004 10790011590
  10794933130 10799873671 10804841154 10809837922) (b8 10814879611 10819971994 10825110742
  10830289078 10835482018 10840687180 10845893614 10851114086) (b8 10856348186 10861595867
  10866840884 10872102410 10877373485 10882663377 10887986967 10893092716)) (n4 (b8 10897953201
  10902793106 10907632505 10912469591 10917304618 10922143944 10926987505 10931844856) (b8
  10936722031 10941625657 10946567567 10951549977 10956588304 10961667023 10966781055 10971900191)
  (b8 10977030263 10982162221 10987310780 10992471442 10997646676 11002815827 11008007488
  11013205513) (b8 11018419851 11023668708 11028639292 11033421937 11038193534 11042961658
  11047730311 11052497171)) (n4 (b8 11057273520 11062048919 11066846220 11071661654 11076506904
  11081395545 11086325527 11091307780) (b8 11096325336 11101373789 11106419367 11111482341
  11116541573 11121621135 11126712056 11131811896) (b8 11136917040 11142034551 11147164132
  11152305313 11157477548 11162326482 11167034482 11171737039) (b8 11176443116 11181146951
  11185851279 11190558732 11195275951 11200012127 11204771812 11209564862))))
def potTree5 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1115040245 1211553225 1280023657 1329660754 1378954008
  1428407262 1478020516) (b8 1527793770 1577727024 1627820278 1678073532 1728486786 1779060040
  1829793294 1880686548) (b8 1931739802 1982953056 2034326310 2085859564 2137552818 2160133320
  2179916339 2199679885) (b8 2219603431 2239686977 2259930523 2280334069 2300897615 2321621161
  2342504707 2363548253)) (n4 (b8 2384751799 2406115345 2427638891 2449322437 2471165983
  2493169529 2515333075 2537656621) (b8 2560140167 2582783713 2605587259 2628550805 2651674351
  2674957897 2698401443 2722004989) (b8 2745768535 2769692081 2793775627 2818019173 2842422719
  2861057461 2873864573 2886172948) (b8 2898641323 2911269698 2924058073 2936616862 2949335651
  2962214440 2975253229 2988219527)) (n4 (b8 3001324467 3014589407 3028014347 3041599287
  3055282687 3069003853 3082885019 3096926185) (b8 3111127351 3125488517 3140009683 3154657779
  3169465875 3184433971 3199562067 3214850163) (b8 3230298259 3245906355 3261674451 3277602547
  3293690643 3309938739 3326346835 3342914931) (b8 3359643027 3376531123 3393579219 3410601275
  3424185277 3433746158 3443020669 3452455180)) (n4 (b8 3462049691 3471668593 3481447495
  3491297211 3500868423 3510599635 3520490847 3530542059) (b8 3540753271 3551075478 3561107938
  3571290852 3581587733 3592044614 3602661495 3613438376) (b8 3624375257 3635186695 3646012351
  3656998007 3668143663 3679449319 3690914975 3702540631) (b8 3714128555 3725834626 3737700697
  3749726768 3761912839 3774196074 3786639309 3799242544))) (n4 (n4 (b8 3812005779 3824929014
  3838012249 3851249951 3864300370 3877510789 3890881208 3902592089) (b8 3910329581 3918227073
  3926284565 3934165909 3942003828 3950001747 3958159666 3966477585) (b8 3974929121 3983116321
  3991462233 3999820615 4007967479 4016264175 4024703450 4033302725) (b8 4042062000 4050981275
  4059969455 4068735059 4077660663 4086606153 4095523090 4104543145)) (n4 (b8 4113723200
  4123063255 4132563310 4142072461 4151605944 4161299427 4171024173 4180832682) (b8 4190792417
  4200788074 4210933373 4221238672 4231662951 4242241995 4252981039 4263880083) (b8 4274640704
  4285474718 4296468732 4307622746 4318936760 4326974690 4333859823 4340904956) (b8 4348094037
  4355136653 4362229539 4369386422 4376421918 4383488341 4390702705 4397743110)) (n4 (b8
  4404772696 4411948848 4419283987 4426779126 4434434265 4442193707 4449728881 4457383704) (b8
  4465107242 4472628672 4480310102 4488021243 4495716692 4503510995 4511461443 4519571891) (b8
  4527780699 4535917355 4544185610 4552474251 4560813647 4569299391 4577827958 4586398718) (b8
  4595038003 4603798224 4612628905 4621612052 4630747780 4640010921 4649429750 4658645763)) (n4
  (b8 4667999147 4677512480 4687182871 4696726015 4705667779 4711872488 4718086589 4724427088) (b8
  4730671392 4736874680 4743187787 4749590929 4755748504 4762024495 4768456892 4775049256) (b8
  4781801172 4788673618 4795413433 4802167273 4809027029 4815671092 4822434524 4829270954) (b8
  4835929843 4842726256 4849566807 4856402661 4863325390 4870395857 4877625453 4884856694))) (n4
  (n4 (b8 4892103252 4899429752 4906712556 4914118145 4921550654 4929041260 4936641798 4944271855)
  (b8 4951948389 4959675832 4967483988 4975405259 4983411625 4991569979 4999877847 5008110526) (b8
  5016358591 5024735084 5033264781 5041624845 5050096279 5056859028 5062412068 5068088148) (b8
  5073921565 5079510397 5085148569 5090942616 5096896626 5103006974 5109229902 5115330269)) (n4
  (b8 5121448924 5127611611 5133681798 5139789157 5145936909 5151942693 5158060399 5164210410) (b8
  5170239717 5176392873 5182586529 5188788888 5195085942 5201530304 5208122031 5214621029) (b8
  5221191937 5227772468 5234393069 5241055652 5247729173 5254497910 5261304504 5268170928) (b8
  5275061902 5282027641 5289032410 5296087761 5303207802 5310422509 5317739667 5325167235)) (n4
  (b8 5332739349 5340105069 5347622120 5355257681 5362834256 5370440603 5377318283 5382423530) (b8
  5387638989 5393012527 5398543091 5404205574 5409858346 5415464645 5421105399 5426723094) (b8
  5432316395 5437949276 5443539153 5449107996 5454737409 5460278796 5465838418 5471462989) (b8
  5477030491 5482624620 5488294068 5493987639 5499739450 5505614991 5511636665 5517631759)) (n4
  (b8 5523673630 5529677860 5535718501 5541784713 5547885017 5554028685 5560193478 5566430912) (b8
  5572723533 5579037768 5585386908 5591767265 5598215765 5604710176 5611254206 5617861365) (b8
  5624558776 5631356763 5638263538 5645086856 5651941964 5658925193 5665872046 5672798987) (b8
  5678982050 5684232073 5689468803 5694672308 5699904602 5705114833 5710309300 5715537114))) (n4
  (n4 (b8 5720726726 5725902413 5731129177 5736277612 5741448173 5746675371 5751805075 5756961520)
  (b8 5762163511 5767324401 5772520209 5777783593 5783078694 5788439330 5793925336 5799539819) (b8
  5805090987 5810684781 5816278477 5821893900 5827494922 5833131643 5838796487 5844499255) (b8
  5850240271 5856017484 5861863577 5867720289 5873609782 5879528297 5885480899 5891480100)) (n4
  (b8 5897539303 5903647015 5909809234 5916044785 5922375275 5928808379 5935125106 5941507552) (b8
  5947989246 5954395047 5960836522 5966569144 5971431077 5976317170 5981179819 5986026447) (b8
  5990911029 5995747915 6000583900 6005470024 6010297056 6015121374 6019987760 6024835161) (b8
  6029652378 6034504109 6039331117 6044181113 6049091421 6054041911 6059051826 6064172676)) (n4
  (b8 6069420916 6074634688 6079897930 6085103922 6090351095 6095600880 6100870764 6106131452) (b8
  6111424197 6116746813 6122107588 6127506601 6132944286 6138431540 6143936877 6149455204) (b8
  6155005869 6160588078 6166203246 6171868033 6177590978 6183364266 6189192010 6195092953) (b8
  6201089650 6207039747 6212987721 6219037673 6225044768 6231057473 6236776650 6241355350)) (n4
  (b8 6245912229 6250494579 6255072046 6259621203 6264191214 6268771167 6273329076 6277890301) (b8
  6282456280 6287022306 6291583858 6296135058 6300686975 6305281203 6309926945 6314623390) (b8
  6319402595 6324303318 6329251321 6334181815 6339113209 6344067791 6349000727 6353942410) (b8
  6358900818 6363874122 6368851030 6373843539 6378867666 6383928692 6389029119 6394165565)))) (n4
  (n4 (n4 (b8 6399343581 6404529857 6409743184 6414970785 6420226639 6425514575 6430835139
  6436200398) (b8 6441624159 6447099341 6452627948 6458225262 6463910447 6469484794 6475124203
  6480810033) (b8 6486464467 6492154429 6496761713 6501095123 6505430405 6509753308 6514079024
  6518407848) (b8 6522738128 6527063406 6531381503 6535709717 6540047749 6544353055 6548671333
  6553034746)) (n4 (b8 6557449514 6561923268 6566490727 6571159675 6575854059 6580523310
  6585212597 6589890417) (b8 6594582964 6599277384 6603963717 6608664694 6613381893 6618109234
  6622843954 6627605165) (b8 6632396747 6637228209 6642097929 6647004543 6651915383 6656848246
  6661802195 6666775174) (b8 6671771842 6676798243 6681857495 6686953024 6692103264 6697309593
  6702566545 6707884441)) (n4 (b8 6713278918 6718569951 6723921405 6729342895 6734670050
  6739837668 6743960535 6748083311) (b8 6752203423 6756319202 6760443068 6764572810 6768677579
  6772797172 6776951145 6781042142) (b8 6785150299 6789304675 6793512211 6797780800 6802142861
  6806600759 6811068343 6815522052) (b8 6819990231 6824446580 6828915181 6833378869 6837852512
  6842328023 6846802217 6851291763)) (n4 (b8 6855794634 6860310549 6864835876 6869388564
  6873973067 6878598444 6883263771 6887936623) (b8 6892629564 6897332225 6902056642 6906803206
  6911567934 6916360323 6921180540 6926039703) (b8 6930937011 6935891814 6940898371 6945961955
  6951086831 6956150353 6961237743 6966401942) (b8 6971485194 6976141802 6980088325 6984013220
  6987952873 6991927650 6995839846 6999769724))) (n4 (n4 (b8 7003744541 7007674137 7011592903
  7015554845 7019569982 7023646073 7027810404 7032072804) (b8 7036354465 7040622678 7044896417
  7049155248 7053432371 7057697476 7061975702 7066246538) (b8 7070531135 7074814594 7079101416
  7083402134 7087714561 7092042036 7096379576 7100747036) (b8 7105141160 7109579782 7114052974
  7118526164 7123012137 7127516017 7132032377 7136574617)) (n4 (b8 7141133921 7145712330
  7150323433 7154959759 7159632270 7164349351 7169123142 7173949731) (b8 7178833417 7183699973
  7188550164 7193462464 7198349042 7202709977 7206474322 7210284017) (b8 7214062733 7217823198
  7221617503 7225426845 7229179696 7232962162 7236798706 7240692588) (b8 7244670766 7248746763
  7252854321 7256961484 7261065616 7265162765 7269264242 7273355373)) (n4 (b8 7277461469
  7281555691 7285663669 7289764174 7293877975 7297990647 7302109883 7306242448) (b8 7310383356
  7314542999 7318710496 7322906722 7327128724 7331396100 7335694310 7340000938) (b8 7344303869
  7348622246 7352957556 7357304661 7361680015 7366069794 7370483932 7374923969) (b8 7379394500
  7383896961 7388448552 7393051777 7397708826 7402422331 7407050459 7411732327)) (n4 (b8
  7416433846 7420650994 7424312796 7427942264 7431575036 7435254767 7438883104 7442503145) (b8
  7446169203 7449898185 7453696719 7457588778 7461534343 7465492908 7469441262 7473395356) (b8
  7477344488 7481290495 7485237836 7489177964 7493127174 7497071758 7501025980 7504973263) (b8
  7508933485 7512897767 7516863130 7520839615 7524824991 7528834387 7532850662 7536885561))) (n4
  (n4 (b8 7540952140 7545056652 7549197197 7553341124 7557493824 7561648292 7565815971 7569995860)
  (b8 7574191260 7578412524 7582648576 7586907280 7591195404 7595513071 7599857741 7604254295) (b8
  7608696579 7613196540 7617718752 7622186660 7626714565 7630932891 7634429529 7637944918) (b8
  7641499157 7644985625 7648493754 7652062537 7655689697 7659404930 7663192168 7667009888)) (n4
  (b8 7670824948 7674637352 7678450828 7682267702 7686080805 7689886410 7693693541 7697500188) (b8
  7701306592 7705115099 7708930356 7712744897 7716558988 7720390956 7724216304 7728052583) (b8
  7731898722 7735762453 7739641327 7743537688 7747457357 7751410236 7755402330 7759401608) (b8
  7763403069 7767419898 7771436856 7775466802 7779509697 7783566003 7787642494 7791742251)) (n4
  (b8 7795856034 7799998504 7804172162 7808376925 7812625898 7816921566 7821265757 7825632065) (b8
  7829949448 7834238433 7837660748 7841079655 7844453874 7847865909 7851341199 7854884268) (b8
  7858506308 7862185988 7865874766 7869566073 7873254164 7876946203 7880633015 7884320975) (b8
  7888006227 7891695810 7895376222 7899053143 7902737667 7906422988 7910107134 7913796808)) (n4
  (b8 7917486504 7921190547 7924894779 7928603597 7932321291 7936050673 7939801444 7943568588) (b8
  7947349683 7951165826 7955018090 7958882521 7962758456 7966632528 7970517972 7974411189) (b8
  7978313473 7982226289 7986160629 7990104254 7994070468 7998054257 8002068127 8006103717) (b8
  8010173717 8014281364 8018438954 8022642612 8026871869 8031048016 8034618349 8037894508))) (n4
  (n4 (b8 8041216777 8044606382 8048062823 8051589940 8055162201 8058744580 8062319085 8065892119)
  (b8 8069464384 8073043292 8076613722 8080191200 8083758949 8087331226 8090904413 8094466299) (b8
  8098036900 8101608558 8105175419 8108748895 8112331086 8115909879 8119502763 8123096255) (b8
  8126693381 8130308573 8133931590 8137578251 8141241999 8144925525 8148642308 8152388809)) (n4
  (b8 8156134524 8159888522 8163654237 8167422000 8171195970 8174977782 8178774141 8182591237) (b8
  8186418962 8190259291 8194123620 8198007777 8201926182 8205864894 8209843861 8213866579) (b8
  8217937105 8222043700 8225823629 8229059979 8232367469 8235740706 8239179716 8242649383) (b8
  8246123603 8249588734 8253065759 8256532595 8259999877 8263467760 8266942217 8270409179)) (n4
  (b8 8273877830 8277341763 8280809395 8284275600 8287735757 8291202236 8294665176 8298133407) (b8
  8301605798 8305080117 8308565213 8312047786 8315544594 8319042611 8322563217 8326088050) (b8
  8329634653 8333201768 8336795246 8340420004 8344060958 8347694091 8351347446 8355002447) (b8
  8358662901 8362333057 8366006377 8369692287 8373391019 8377115417 8380840057 8384590804)) (n4
  (b8 8388359201 8392162482 8395980738 8399836759 8403733631 8407672437 8411658866 8415065874) (b8
  8418356775 8421706277 8425087074 8428466549 8431832813 8435213276 8438585703 8441956394) (b8
  8445328688 8448699672 8452072703 8455448266 8458819973 8462191364 8465555568 8468924594) (b8
  8472296230 8475664495 8479035691 8482399301 8485775882 8489152331 8492536855 8495927620))))
def potTree6 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1115040245 1211553225 1272569199 1326956765 1358771009
  1390745253 1422879497) (b8 1451247184 1479774871 1508462558 1537310245 1566317932 1595485619
  1624813306 1654300993) (b8 1683948680 1713756367 1743724054 1773851741 1804139428 1834587115
  1865194802 1895962489) (b8 1926890176 1957977863 1989225550 2020633237 2052200924 2083928611
  2115816298 2147863985)) (n4 (b8 2180071672 2212439359 2231836106 2243677465 2255678824
  2266344911 2277170998 2288157085) (b8 2299303172 2309436426 2319729680 2330182934 2340796188
  2350774033 2360911878 2371209723) (b8 2381667568 2391464230 2401420892 2411537554 2421814216
  2432141942 2442270494 2452559046) (b8 2463007598 2473616150 2483930396 2494404642 2505038888
  2515833134 2526787380 2537760673)) (n4 (b8 2548751977 2559903281 2571214585 2582685889
  2594317193 2605903223 2617649253 2629555283) (b8 2641621313 2653847343 2666233373 2678779403
  2691485433 2704351463 2717377493 2730563523) (b8 2743909553 2757415583 2771081613 2784907643
  2798893673 2813039703 2827345733 2841811763) (b8 2856437793 2871223823 2886169853 2901233701
  2916457549 2931841397 2947385245 2959768065)) (n4 (b8 2966041577 2972257957 2978524775
  2984763061 2991161347 2997719633 3003957319 3010029410) (b8 3016098640 3022327870 3028717100
  3035266330 3041744993 3047727328 3053821539 3060075750) (b8 3066489961 3072758356 3079148951
  3085699546 3092358589 3098591709 3104717976 3111004243) (b8 3117450510 3124056777 3130823044
  3137730274 3144275551 3150667057 3157218563 3163930069))) (n4 (n4 (b8 3170700595 3177536863
  3184506080 3191635297 3198924514 3205710537 3212501220 3219451793) (b8 3226562106 3233832145
  3241261716 3248738434 3256313326 3264047197 3271547543 3278872669) (b8 3286325778 3293935570
  3301702052 3309625132 3317704951 3325941275 3334043309 3342127947) (b8 3350367940 3358763244
  3367313827 3375919803 3384560706 3393356395 3402306813 3411412033)) (n4 (b8 3420672086
  3430086914 3439656516 3448831548 3458098768 3467519439 3477093655 3486821345) (b8 3496702602
  3506737441 3516925922 3527267996 3537763801 3543993039 3548496503 3553156605) (b8 3557907071
  3562732133 3567463921 3571942680 3576410423 3581032115 3585808451 3590739001) (b8 3595823981
  3600527047 3604997575 3609620124 3614395004 3619322025 3624392527 3629392836)) (n4 (b8
  3634167851 3638909966 3643804261 3648837523 3653936404 3658864970 3663499058 3668283617) (b8
  3673218676 3678216118 3683283948 3688470489 3693802059 3699284688 3704294251 3709294655) (b8
  3714420527 3719694058 3725116487 3730277422 3735303002 3740418432 3745682781 3751096255) (b8
  3756658590 3762352204 3768103695 3773493906 3778910416 3784474493 3790115103 3795837060)) (n4
  (b8 3801684166 3807522851 3813196459 3818808699 3824546943 3830430345 3836460094 3842472794) (b8
  3848344168 3854360590 3860521921 3866828531 3873168674 3879552937 3885892372 3892198759) (b8
  3898588589 3905122392 3911799977 3918595418 3925446136 3932352590 3939403159 3946165023) (b8
  3952960234 3959859078 3966901256 3974086188 3981414722 3988886544 3996501863 4004229317))) (n4
  (n4 (b8 4011623805 4019104548 4026726709 4033785183 4037667951 4041691309 4045719627 4049599122)
  (b8 4053381778 4057233716 4061224959 4065318704 4069388523 4073264314 4077010878 4080901660) (b8
  4084916468 4088996549 4093154639 4097241106 4100985245 4104873037 4108857605 4112908543) (b8
  4117052455 4121320329 4125729790 4130081542 4134135705 4138218962 4142427778 4146778261)) (n4
  (b8 4151221409 4155256462 4159256188 4163372972 4167628642 4172025279 4176253685 4180338814) (b8
  4184455554 4188697017 4193079834 4197605107 4202262586 4207011635 4211316151 4215668088) (b8
  4220160936 4224784449 4229491953 4234050274 4238460548 4242949127 4247551232 4252229732) (b8
  4257000755 4261859512 4266687285 4271385134 4276048958 4280834440 4285757263 4290552433)) (n4
  (b8 4295307173 4300198738 4305228060 4310248310 4315151109 4320163962 4325294292 4330372241) (b8
  4335587182 4340909324 4346268569 4351655378 4357009146 4362349936 4367774675 4373337036) (b8
  4379034270 4384642334 4390041479 4395576134 4401244442 4407022461 4412855212 4418740662) (b8
  4424760619 4430546269 4436335158 4442213671 4448220146 4454362020 4460638861 4466228922)) (n4
  (b8 4469594666 4473032261 4476555282 4480195458 4483633635 4486866610 4490199472 4493601674) (b8
  4497090815 4500693688 4504431029 4508163387 4511684114 4515136228 4518679720 4522352626) (b8
  4526137109 4529737314 4533147829 4536603018 4540182065 4543896214 4547616333 4551189919) (b8
  4554631462 4558095183 4561689108 4565419773 4569051244 4572543419 4576026318 4579605752))) (n4
  (n4 (b8 4583317620 4587164360 4591143480 4595226923 4599026085 4602681066 4606473178 4610396972)
  (b8 4614431044 4618365105 4622044008 4625795996 4629683857 4633684654 4637717392 4641613395) (b8
  4645406005 4649280846 4653261253 4657317965 4661463079 4665693147 4669782267 4673890451) (b8
  4678016513 4682171635 4686348827 4690379393 4694494364 4698737765 4702935972 4707073027)) (n4
  (b8 4711280866 4715621399 4719976335 4724344096 4728677286 4733013799 4737391785 4741880363) (b8
  4746326196 4750896117 4755569043 4760289990 4765038427 4769768326 4774485186 4779263848) (b8
  4784034907 4788741251 4793429430 4798169219 4803023708 4808006026 4813001507 4817854563) (b8
  4822674340 4827624972 4832695014 4837847832 4843055011 4848341321 4853644961 4856970643)) (n4
  (b8 4860060257 4863275134 4866597676 4869790147 4872799766 4875814032 4878932857 4882178257) (b8
  4885464600 4888647779 4891701600 4894735103 4897860595 4901121365 4904366208 4907490237) (b8
  4910557469 4913680756 4916859499 4920112859 4923318843 4926402221 4929448407 4932558621) (b8
  4935790899 4939150332 4942642421 4946244502 4949713130 4952963708 4956249119 4959668486)) (n4
  (b8 4963209088 4966763202 4970076151 4973301260 4976662737 4980145145 4983712066 4987166515) (b8
  4990406881 4993719397 4997164250 5000718476 5004303647 5007753202 5011105872 5014536691) (b8
  5018065376 5021674939 5025368900 5029072753 5032643672 5036296858 5040033264 5043728995) (b8
  5047375395 5051041189 5054733707 5058448308 5062110779 5065734677 5069460316 5073238417)))) (n4
  (n4 (n4 (b8 5076973383 5080694762 5084505407 5088339262 5092200781 5096103171 5100018940
  5103913680) (b8 5107806558 5111726951 5115733007 5119752087 5123830760 5128018144 5132276185
  5136571022) (b8 5140612837 5144754441 5148978327 5153245305 5157527095 5161792788 5166063743
  5170385072) (b8 5174686438 5178936281 5183179235 5187480298 5191895250 5196425817 5200958128
  5205361467)) (n4 (b8 5209739311 5212750742 5215622689 5218404201 5221178203 5224006301
  5226894504 5229814005) (b8 5232663114 5235420538 5238175634 5241016467 5243972986 5246956418
  5249788290 5252529172) (b8 5255266604 5258085723 5261021512 5264083256 5267272137 5270511772
  5273602998 5276538413) (b8 5279525326 5282632782 5285850379 5289011612 5291989477 5294918221
  5297948659 5301101203)) (n4 (b8 5304302734 5307371617 5310298438 5313259179 5316351421
  5319539361 5322712349 5325721754) (b8 5328666388 5331707061 5334868460 5338106616 5341296036
  5344377628 5347432621 5350571621) (b8 5353801668 5357113187 5360483107 5363719951 5366984974
  5370334338 5373697700 5376936250) (b8 5380242504 5383634771 5386997327 5390314255 5393638560
  5396991328 5400369692 5403710228)) (n4 (b8 5407008115 5410384273 5413818847 5417232826
  5420626579 5424084666 5427525461 5431003971) (b8 5434509263 5438042998 5441614624 5445200241
  5448762811 5452328564 5455917822 5459599062) (b8 5463286779 5467036697 5470887694 5474716119
  5478386703 5482098579 5485892549 5489775119) (b8 5493707887 5497522780 5501274688 5505116687
  5509020590 5512949409 5516884079 5520813487))) (n4 (n4 (b8 5524769677 5528740806 5532686678
  5536597725 5539224844 5541748718 5544369526 5547108274) (b8 5549925576 5552473834 5554952052
  5557453943 5560046728 5562748499 5565574499 5568515408) (b8 5571469561 5574273503 5576963596
  5579718675 5582587331 5585540608 5588425267 5591141418) (b8 5593829840 5596620863 5599522561
  5602447073 5605262859 5607947651 5610660958 5613471627)) (n4 (b8 5616377330 5619262183
  5622009999 5624691508 5627438146 5630301393 5633218258 5636079986) (b8 5638808359 5641523338
  5644339478 5647269305 5650228970 5653135076 5655949890 5658768380) (b8 5661677398 5664665414
  5667735214 5670783451 5673725124 5676753043 5679837610 5682846020) (b8 5685839739 5688899739
  5691996846 5695012334 5698029279 5701130081 5704240697 5707316227)) (n4 (b8 5710380847
  5713460239 5716571737 5719665993 5722723887 5725806867 5728961657 5732130982) (b8 5735274039
  5738449945 5741593835 5744783876 5747969938 5751183879 5754426486 5757694341) (b8 5760998576
  5764325358 5767634223 5770940384 5774270878 5777673382 5781108855 5784582979) (b8 5788143338
  5791490117 5794909541 5798344351 5801848636 5805427972 5808946085 5812358303)) (n4 (b8
  5815823588 5819370469 5822997862 5826640896 5830178932 5833684277 5837276739 5840917484) (b8
  5843349919 5845891657 5848558738 5851294458 5853980711 5856531283 5859043315 5861627806) (b8
  5864321235 5867039394 5869668060 5872171992 5874683311 5877303516 5880008806 5882694823) (b8
  5885275625 5887768084 5890299694 5892938785 5895629347 5898284930 5900819834 5903309808))) (n4
  (n4 (b8 5905884626 5908533109 5911221887 5913819394 5916329397 5918827897 5921413457 5924094077)
  (b8 5926773921 5929375041 5931882113 5934435868 5937085153 5939816390 5942553124 5945213168) (b8
  5947822570 5950465975 5953193470 5956009080 5958858429 5961624016 5964381217 5967218579) (b8
  5970055029 5972814135 5975605416 5978464505 5981278739 5984065877 5986895762 5989768592)) (n4
  (b8 5992597221 5995399437 5998267676 6001171656 6004049373 6006902544 6009765630 6012661381) (b8
  6015549633 6018411481 6021281516 6024206428 6027141113 6030090045 6033042174 6035978827) (b8
  6038938402 6041873592 6044858092 6047834480 6050835309 6053870092 6056921933 6060017781) (b8
  6063125050 6066233487 6069331034 6072454465 6075643283 6078868019 6082125422 6085276966)) (n4
  (b8 6088407949 6091604258 6094836109 6098112692 6101401275 6104558570 6107762985 6111002122) (b8
  6114309310 6117659040 6120937730 6124153043 6127424158 6130765158 6133675368 6136053163) (b8
  6138391317 6140796110 6143305540 6145835099 6148280874 6150628019 6152984860 6155412696) (b8
  6157923399 6160412374 6162827623 6165171603 6167543140 6170003874 6172507105 6174967836)) (n4
  (b8 6177347863 6179693630 6182073735 6184547600 6187057860 6189516800 6191873163 6194200663) (b8
  6196595479 6199076588 6201576840 6204026478 6206393813 6208754706 6211212191 6213737382) (b8
  6216298893 6218811833 6221263108 6223722985 6226255846 6228868377 6231530588 6234162365) (b8
  6236712050 6239357222 6242024706 6244612336 6247197181 6249859304 6252513035 6255103820))) (n4
  (n4 (b8 6257713805 6260405868 6263041645 6265661196 6268308098 6271011568 6273667135 6276293928)
  (b8 6278982783 6281719386 6284417475 6287107954 6289790273 6292510714 6295230953 6297917964) (b8
  6300623392 6303372981 6306089995 6308846645 6311609331 6314385776 6317166132 6319925777) (b8
  6322709173 6325482575 6328298755 6331105136 6333946298 6336812285 6339700502 6342622564)) (n4
  (b8 6345559692 6348490241 6351427236 6354388846 6357406035 6360457266 6363400336 6366331543) (b8
  6369304978 6372332839 6375400353 6378430303 6381385341 6384374874 6387407076 6390472480) (b8
  6393583007 6396636129 6399643821 6402682807 6405779448 6408413128 6410754295 6413015025) (b8
  6415219705 6417457468 6419787212 6422142238 6424458878 6426685296 6428899500 6431153816)) (n4
  (b8 6433488566 6435844830 6438162113 6440374184 6442565681 6444824706 6447174709 6449531352) (b8
  6451844830 6454040691 6456245193 6458494960 6460840968 6463188618 6465470781 6467706551) (b8
  6469925441 6472245315 6474635136 6477038601 6479408773 6481710795 6484033520 6486426203) (b8
  6488903022 6491416061 6493857130 6496269834 6498759682 6501262264 6503703687 6506145674)) (n4
  (b8 6508667570 6511139675 6513587119 6516052611 6518558665 6521049046 6523497044 6525993151) (b8
  6528503433 6530992997 6533471995 6536004707 6538547336 6541036956 6543543414 6546093375) (b8
  6548675880 6551227660 6553770954 6556321973 6558899796 6561466281 6564007471 6566579820) (b8
  6569170415 6571757850 6574340131 6576918224 6579539499 6582165312 6584799194 6587424030))))
def potTree7 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1115040245 1211553225 1265142959 1309020347 1353057735
  1380331940 1407766145) (b8 1428803218 1450000291 1471357364 1490338576 1509479788 1525969238
  1542618688 1559428138) (b8 1574082944 1588897750 1603872556 1619007362 1634302168 1649756974
  1665371780 1681146586) (b8 1697081392 1713176198 1729431004 1745845810 1762420616 1779155422
  1796050228 1813105034)) (n4 (b8 1830319840 1847694646 1865229452 1882924258 1900779064
  1918793870 1936968676 1955303482) (b8 1973798288 1992453094 2011267900 2030242706 2049377512
  2068672318 2088127124 2107741930) (b8 2127516736 2147451542 2167546348 2187801154 2208215960
  2228790766 2249525572 2270420378) (b8 2291475184 2303074816 2309428769 2315710821 2322152873
  2328754925 2335516977 2342439029)) (n4 (b8 2348291933 2353956708 2359781483 2365766258
  2371911033 2378215808 2384680583 2389786513) (b8 2395052443 2400478373 2406064303 2411810233
  2417716163 2423782093 2428616254 2433610415) (b8 2438764576 2444078737 2449552898 2455187059
  2460981220 2466625450 2471382392 2476299334) (b8 2481376276 2486613218 2492010160 2497567102
  2503284044 2508796135 2513551495 2518466855)) (n4 (b8 2523542215 2528777575 2534172935
  2539728295 2545443655 2551319015 2556078476 2560997937) (b8 2566077398 2571316859 2576716320
  2582275781 2587995242 2593874703 2599678612 2604659390) (b8 2609800168 2615100946 2620561724
  2626182502 2631963280 2637904058 2644004836 2650265614) (b8 2655495292 2660884970 2666434648
  2672144326 2678014004 2684043682 2690233360 2696583038))) (n4 (n4 (b8 2703092716 2709474546
  2715165703 2721012283 2727013874 2733170177 2739480519 2745944668) (b8 2752562088 2759332465
  2766255340 2773330356 2779794340 2786138769 2792630989 2799270607) (b8 2806057473 2812991119
  2820071456 2827298081 2834670889 2842091180 2849128165 2856308394) (b8 2863631803 2871098182
  2878707237 2886458930 2894071255 2901810840 2909691609 2917713222)) (n4 (b8 2925875905
  2934179042 2942622845 2951207088 2959865872 2967912853 2976097523 2984419703) (b8 2992879305
  3001476280 3010210647 3019082046 3028090647 3037236463 3046519122 3055938806) (b8 3061859021
  3065264523 3068813363 3072506284 3075914308 3078761167 3081751314 3084884611) (b8 3088161421
  3091581894 3094842740 3098159175 3101613968 3105207316 3108445458 3111205341)) (n4 (b8
  3114103534 3117139583 3120314234 3123627717 3127079870 3130671558 3134180130 3137709080) (b8
  3140571832 3143278989 3146119459 3149093466 3152200979 3155443036 3158819228 3162329728) (b8
  3165975424 3169671273 3172855135 3175554645 3178383228 3181341355 3184428650 3187646161) (b8
  3190993448 3194471612 3198080257 3201645447 3204736188 3207701543 3210797322 3214023860)) (n4
  (b8 3217381332 3220826780 3224202302 3227704922 3231182936 3234271524 3237136339 3240127300) (b8
  3243245726 3246490572 3249862995 3253363179 3256991463 3260747987 3264632885 3267976179) (b8
  3270935100 3274017658 3277224137 3280554414 3284008797 3287588266 3291292322 3295121517) (b8
  3298941358 3302027065 3305237581 3308573591 3312034815 3315621133 3319334205 3323172788))) (n4
  (n4 (b8 3327138462 3331048014 3334167042 3337408035 3340771347 3344257588 3347866541 3351598654)
  (b8 3355454323 3359433504 3363536714 3367720866 3371832942 3375370547 3379017022 3382784343) (b8
  3386672859 3390682388 3394813266 3398950934 3402707976 3406216214 3409843218 3413588118) (b8
  3417451239 3421432956 3425533158 3429752275 3434089931 3438545565 3442592994 3446688779)) (n4
  (b8 3450901951 3455232452 3459679564 3464244703 3468726052 3473213886 3477359174 3481530713) (b8
  3485816208 3490216151 3494728135 3499090022 3503556355 3508136140 3512829904 3517638081) (b8
  3522559694 3527594308 3532674887 3537573347 3542354287 3547090492 3551939017 3556898503) (b8
  3561902221 3566728898 3571502987 3576388517 3581385825 3586491087 3591708521 3597036415)) (n4
  (b8 3602372540 3607684638 3613099744 3618623156 3624257052 3630002160 3635858648 3641826276) (b8
  3647906138 3654096133 3660263398 3662475741 3664578673 3666798630 3669137813 3671596193) (b8
  3674142957 3676594514 3679008181 3681540851 3684184522 3686444497 3688538226 3690747120) (b8
  3693070725 3695457246 3697844539 3700328188 3702816874 3705328113 3707906226 3710374556)) (n4
  (b8 3712542535 3714564306 3716697239 3718943224 3721302330 3723777130 3726367285 3729071540) (b8
  3731891324 3734772145 3737110041 3739187917 3741189916 3743305182 3745531468 3747871954) (b8
  3750323376 3752887207 3755562462 3758353594 3761258086 3763853814 3766079484 3768228666) (b8
  3770488283 3772857138 3775337344 3777929108 3780629452 3783445315 3786315225 3788988530))) (n4
  (n4 (b8 3791263164 3793346483 3795536918 3797835250 3800243329 3802755548 3805379787 3808113060)
  (b8 3810955298 3813828109 3816314062 3818572655 3820940908 3823418404 3826008733 3828706619) (b8
  3831520070 3834440207 3837472040 3840432969 3842600688 3844861329 3847231768 3849710786) (b8
  3852298905 3854996880 3857803874 3860721962 3863709079 3866541952 3868781736 3871125734)) (n4
  (b8 3873576260 3876134505 3878799716 3881571660 3884452943 3887442617 3890541952 3893733131) (b8
  3896733666 3899166292 3901705944 3904346244 3907095909 3909951161 3912914839 3915984121) (b8
  3919143885 3922315857 3925283041 3927922622 3930658715 3933500230 3936445608 3939494895) (b8
  3942649312 3945828925 3948770601 3951474159 3954144617 3956919279 3959798467 3962778953)) (n4
  (b8 3965863427 3969053115 3972272161 3975076251 3977985305 3980997430 3984109646 3987329345) (b8
  3990649566 3993820228 3997070627 4000422216 4003750340 4007037178 4010189001 4013406251) (b8
  4016723813 4020146615 4023667464 4027249825 4030775547 4034290594 4037513829 4040754732) (b8
  4044096084 4047534138 4051073559 4054557165 4058045131 4061633518 4065318340 4068772292)) (n4
  (b8 4072169789 4075669960 4079120691 4082568901 4086116065 4089757522 4093499689 4097340441) (b8
  4101283049 4105320192 4109396673 4113331847 4117164557 4120949535 4124791834 4128729917) (b8
  4132738385 4136717428 4140581705 4144431169 4148382520 4152427755 4156569532 4160804598) (b8
  4165139409 4167232009 4168967430 4170806043 4172564179 4174391635 4176323521 4178354788)))) (n4
  (n4 (n4 (b8 4180493314 4182737888 4185092353 4187240565 4189068608 4190744328 4192469733
  4194295960) (b8 4196225066 4198253918 4200391037 4202632369 4204958515 4207254642 4209313377
  4211061494) (b8 4212693534 4214425894 4216261437 4218197507 4220226123 4222364913 4224604538
  4226946475) (b8 4229315345 4231369511 4233194264 4235067659 4236788178 4238564081 4240443662
  4242419868)) (n4 (b8 4244503562 4246682283 4248964552 4251302501 4253448708 4255320263
  4257133953 4259052643) (b8 4261076419 4263200163 4265425545 4267761748 4270189578 4272697706
  4275024184 4276770581) (b8 4278556841 4280450698 4282441766 4284530692 4286692179 4288938515
  4291283817 4293737059) (b8 4296190747 4298211121 4299923963 4301729568 4303636395 4305647258
  4307754761 4309961963)) (n4 (b8 4312270911 4314678767 4317133531 4319424947 4321183815
  4323033282 4324982456 4327027942) (b8 4329177616 4331426905 4333770996 4336215804 4338767815
  4341406568 4343959222 4345813987) (b8 4347768766 4349823263 4351978236 4354229599 4356578970
  4359026211 4361575870 4364214071) (b8 4366706039 4368750229 4370758936 4372852173 4375051804
  4377342284 4379736280 4382227725)) (n4 (b8 4384808287 4387444716 4389922258 4392204980
  4394558550 4396813521 4399163626 4401613787) (b8 4404153458 4406795955 4409304592 4411542933
  4413883125 4416316108 4418578638 4420934150) (b8 4423385613 4425934378 4428580576 4430928117
  4433175519 4435520428 4437957104 4440491234) (b8 4443119994 4445730976 4448271274 4450651076
  4453092995 4455635372 4458271319 4460814255))) (n4 (n4 (b8 4463368051 4466013583 4468759331
  4471493257 4474179658 4476941803 4479761725 4482569261) (b8 4485316866 4487967990 4490685726
  4493490744 4496393461 4499391948 4502442223 4505211445) (b8 4507904120 4510548871 4513271861
  4516081176 4518991817 4521985816 4525013476 4527996901) (b8 4530964012 4533656758 4536374365
  4539186576 4542081307 4545071154 4548026277 4550982804)) (n4 (b8 4554015038 4557126306
  4560142207 4563040079 4565968854 4568923801 4571849865 4574826108) (b8 4577878583 4581027233
  4584264139 4587597850 4591017932 4594518943 4598054161 4601460750) (b8 4604767724 4606307568
  4607890747 4609571136 4611345342 4613218229 4615184544 4617205650) (b8 4619042433 4620617315
  4622133786 4623742633 4625445454 4627086489 4628656460 4630327748)) (n4 (b8 4632091403
  4633942321 4635895724 4637895939 4639719687 4641275817 4642765515 4644358293) (b8 4646046207
  4647836005 4649719919 4651702630 4653780086 4655930908 4657986081 4659588117) (b8 4661047602
  4662598337 4664227078 4665959899 4667778623 4669658935 4671650323 4673719882) (b8 4675855588
  4677803559 4679390707 4680842739 4682372393 4684010704 4685747013 4687575353)) (n4 (b8
  4689487776 4691492470 4693526613 4695648699 4697635708 4699111147 4700675637 4702226436) (b8
  4703827299 4705520326 4707314862 4709194606 4711167904 4713232883 4715357840 4717329636) (b8
  4718845458 4720359218 4721983019 4723691774 4725487436 4727386637 4729380615 4731463012) (b8
  4733657482 4735935519 4738185803 4739957332 4741527253 4743187028 4744949215 4746803094))) (n4
  (n4 (b8 4748753858 4750788177 4752934195 4755151850 4757431318 4759491267 4761039118 4762693530)
  (b8 4764432430 4766279035 4768196495 4770226053 4772334022 4774541431 4776845064 4779003381) (b8
  4780764846 4782454631 4784208569 4786074037 4788009657 4790053643 4792182916 4794420294) (b8
  4796701074 4798708112 4800607944 4802607637 4804703957 4806890828 4808977862 4811144708)) (n4
  (b8 4813409201 4815444097 4817447866 4819402161 4821439816 4823560044 4825770456 4827871988) (b8
  4830019917 4832153544 4834168397 4836271071 4838205944 4840240200 4842340678 4844542478) (b8
  4846828140 4848919494 4850871565 4852877130 4854961811 4857130960 4859397204 4861525719) (b8
  4863683507 4865953420 4868157720 4870331867 4872588728 4874701067 4876860668 4879126177)) (n4
  (b8 4881385252 4883600592 4885860231 4888218665 4890637764 4893034201 4895401565 4897862920) (b8
  4900338513 4902822440 4905089041 4907418010 4909823183 4912198355 4914546525 4916986988) (b8
  4919458452 4921924177 4924333300 4926643513 4929007777 4931457537 4934007942 4936644194) (b8
  4939339621 4941835123 4944203594 4946530942 4948896697 4951332018 4953875831 4956492127)) (n4
  (b8 4959167160 4961828981 4964462428 4966975797 4969355749 4971770929 4974280926 4976874787) (b8
  4979515328 4982142632 4984786752 4987503944 4990261823 4992933459 4995514230 4998118126) (b8
  5000747484 5002986583 5004776550 5006154994 5007384078 5008720671 5010125488 5011637519) (b8
  5013235070 5014892162 5016645221 5018471705 5020379895 5022119558 5023539350 5024780967))) (n4
  (n4 (b8 5026087084 5027493431 5028983454 5030577478 5032246476 5033988590 5035807630 5037674687)
  (b8 5039469184 5040904874 5042232118 5043556989 5044935877 5046373161 5047904939 5049550195) (b8
  5051242682 5053058289 5054930767 5056758588 5058294631 5059612043 5060973547 5062421487) (b8
  5063899567 5065357064 5066917425 5068539034 5070271061 5072083251 5073968403 5075737389)) (n4
  (b8 5077148135 5078446339 5079813311 5081280803 5082811552 5084462888 5086193949 5088022828) (b8
  5089935334 5091947186 5093981847 5095732199 5097192183 5098588539 5100051384 5101617421) (b8
  5103256907 5105006184 5106848166 5108777711 5110803511 5112814690 5114455690 5115834116) (b8
  5117232098 5118742052 5120329655 5122022096 5123799519 5125663589 5127623297 5129630855)) (n4
  (b8 5131540031 5133088982 5134474917 5135944773 5137514361 5139152878 5140905416 5142729451) (b8
  5144654668 5146649951 5148685368 5150337928 5151982306 5153471720 5155018570 5156702378) (b8
  5158425740 5160262089 5162195886 5164199619 5166204568 5167786499 5169485117 5171251699) (b8
  5173108279 5175074141 5177092116 5178964980 5180686649 5182415584 5184225739 5186130676)) (n4
  (b8 5188061435 5189932407 5191921964 5193851475 5195636893 5197410077 5199160274 5200996705) (b8
  5202894552 5204853438 5206731040 5208663532 5210547421 5212339061 5214188101 5215899249) (b8
  5217726496 5219616236 5221600418 5223504578 5225381598 5227238524 5229011874 5230869159) (b8
  5232821668 5234788162 5236634625 5238537789 5240571239 5242492124 5244417281 5246438483))))
def potTree8 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1115040245 1211365880 1265142884 1304774362 1335135512
  1365636662 1396277812) (b8 1420455393 1444772974 1462806460 1480979946 1499293432 1517746918
  1527902407 1538197896) (b8 1548633385 1559208874 1568625560 1578182246 1587878932 1597715618
  1607692304 1615697064) (b8 1623841824 1632126584 1640551344 1649116104 1657233980 1665491856
  1673889732 1682427608)) (n4 (b8 1691105484 1699021311 1707077138 1715272965 1723608792
  1732084619 1739263962 1746583305) (b8 1754042648 1761641991 1769381334 1777260677 1784985353
  1792850029 1800854705 1808999381) (b8 1817284057 1825367901 1833591745 1841955589 1850459433
  1859103277 1867887121 1876674114) (b8 1885601107 1894668100 1903875093 1913222086 1922709079
  1932336072 1942103065 1952010058)) (n4 (b8 1962057051 1972244044 1982571037 1993038030
  2003645023 2014392016 2025279009 2036306002) (b8 2047472995 2058779988 2070226981 2081813974
  2093540967 2105407960 2117414953 2129561946) (b8 2141848939 2154275932 2166842925 2179549918
  2192396911 2205383904 2218510897 2231777890) (b8 2245184883 2258731876 2272418869 2286245862
  2300212855 2314319848 2328566841 2342953834)) (n4 (b8 2357019807 2361173232 2365338222
  2369567892 2373937562 2378447232 2383096902 2387886572) (b8 2391703409 2394901110 2398186096
  2401611082 2405176068 2408881054 2412726040 2416645204) (b8 2420535888 2424566572 2428737256
  2432141162 2434949484 2437894045 2440909093 2443907390) (b8 2447040454 2450308072 2453710263
  2457246956 2460917841 2464561383 2468240782 2471754503))) (n4 (n4 (b8 2474194855 2476758016
  2479443975 2482252581 2485052271 2487899302 2490868151 2493958813) (b8 2497171222 2500505460
  2503961530 2507394667 2510848300 2513259474 2515592634 2518036707) (b8 2520591802 2523258073
  2525872511 2528564789 2531367476 2534280796 2537304901 2540439893) (b8 2543685747 2546947299
  2550181631 2552676944 2554910585 2557245088 2559680627 2562209152)) (n4 (b8 2564661141
  2567213705 2569867132 2572621669 2575477322 2578434367 2581492933 2584597921) (b8 2587637369
  2590778006 2593140300 2595387710 2597727788 2600084628 2602432541 2604872904) (b8 2607405885
  2610031702 2612750704 2615562906 2618468643 2621410916 2624291150 2627264807) (b8 2630331872
  2633285621 2635539956 2637732251 2640009816 2642372995 2644822021 2647356959)) (n4 (b8
  2649978182 2652685861 2655480220 2658234899 2660998644 2663849000 2666786077 2669810373) (b8
  2672921887 2675852389 2678098816 2680425086 2682831407 2685318061 2687885292 2690533318) (b8
  2693174234 2695787574 2698481776 2701256845 2704113265 2707051197 2710070743 2713172466) (b8
  2716356306 2719622681 2722095183 2724579666 2727140200 2729607305 2732129758 2734728284)) (n4
  (b8 2737402808 2740153847 2742981517 2745886169 2748868040 2751927295 2755064195 2758253300) (b8
  2761466938 2764758710 2768031295 2770522227 2773085403 2775720805 2778428737 2781209514) (b8
  2784063267 2786990188 2789990861 2793051134 2796122447 2799267831 2802487551 2805781673) (b8
  2809150648 2812594639 2816113975 2819492663 2822290103 2825157536 2828095144 2831033185))) (n4
  (n4 (b8 2834036893 2837111411 2840256785 2843473475 2846761829 2850121800 2853553784 2857057905)
  (b8 2860634626 2864284007 2868006447 2871802159 2875667226 2878745173 2881891727 2885106952) (b8
  2888391364 2891744918 2895167940 2898660880 2902223606 2905856692 2909560273 2913334687) (b8
  2917179729 2921096295 2925084282 2929063384 2932661615 2936328926 2940065372 2943871419)) (n4
  (b8 2947746954 2951692748 2955708553 2959794900 2963951816 2967962061 2972006160 2976120362) (b8
  2980304622 2984559281 2988884725 2993280821 2997748184 3002286803 3006897139 3011579322) (b8
  3016333371 3021105539 3025293816 3029551104 3033877381 3038272947 3042738194 3047273249) (b8
  3051878350 3056553738 3061299589 3066116333 3071004022 3075962751 3080992893 3086094932)) (n4
  (b8 3091268573 3096514514 3101832893 3107223480 3112687087 3118223794 3123833631 3129517139) (b8
  3135274169 3141105246 3147010274 3152989839 3157612051 3159422051 3161306260 3163268293) (b8
  3165307173 3167371285 3169252574 3170579184 3171971575 3173432064 3174964744 3176566987) (b8
  3178242843 3179951352 3181650590 3183360594 3184987268 3186641248 3188365046 3190047891)) (n4
  (b8 3191742647 3193500189 3195332449 3197237829 3199217374 3201218634 3203047663 3204324490) (b8
  3205665406 3207073547 3208550270 3210094191 3211706913 3213362878 3215015498 3216661646) (b8
  3218276304 3219902674 3221557125 3223200853 3224859815 3226584661 3228377567 3230242680) (b8
  3232178911 3234085555 3235745062 3236990670 3238298350 3239668988 3241103162 3242603462))) (n4
  (n4 (b8 3244171029 3245777713 3247376998 3248973036 3250635875 3252357967 3254145701 3256006107)
  (b8 3257685340 3259407733 3261199647 3263058656 3264966358 3266734248 3267956622 3269196735) (b8
  3270498239 3271861192 3273292195 3274783645 3276338744 3277882563 3279418168 3280993714) (b8
  3282635815 3284338263 3286108092 3287939682 3289833570 3291790198 3293813729 3295905963)) (n4
  (b8 3297871884 3299055295 3300267886 3301540617 3302876522 3304275496 3305733126 3307250913) (b8
  3308754607 3310237945 3311776282 3313372695 3315037853 3316760172 3318545961 3320390425) (b8
  3322298519 3324270906 3326304627 3328240447 3329661014 3331081348 3332561459 3334000201) (b8
  3335445792 3336944924 3338499115 3340115908 3341783237 3343491698 3345105472 3346783674)) (n4
  (b8 3348514857 3350307953 3352160799 3354075921 3356052004 3358036835 3359403458 3360779764) (b8
  3362207394 3363623485 3365020924 3366465601 3367962098 3369510113 3371119008 3372788205) (b8
  3374515109 3376301903 3378147079 3380043501 3381998542 3384004666 3386043710 3388116328) (b8
  3390246696 3391802888 3393190375 3394547274 3395938935 3397383509 3398881562 3400439391)) (n4
  (b8 3402056106 3403727565 3405454113 3407230751 3409069568 3410965779 3412914272 3414905686) (b8
  3416904037 3418959012 3421023846 3422813431 3424254090 3425743467 3427282761 3428876744) (b8
  3430523568 3432228485 3433986908 3435802443 3437668009 3439576620 3441506065 3443476035) (b8
  3445501157 3447582821 3449717017 3451906629 3453538773 3454980463 3456475302 3458022109)))) (n4
  (n4 (n4 (b8 3459623885 3461276936 3462989256 3464746297 3466555796 3468415592 3470304113
  3472215686) (b8 3474184108 3476199249 3478268627 3480398094 3482582096 3484825625 3487118114
  3489295180) (b8 3491116060 3492847070 3494636873 3496466940 3498297160 3500173051 3502070058
  3504007334) (b8 3505998437 3508034447 3510124246 3512273319 3514473877 3516723177 3518854127
  3520582715)) (n4 (b8 3522280543 3524029818 3525821816 3527618787 3529454339 3531343800
  3533285325 3535279754) (b8 3537332305 3539429724 3541578330 3543777189 3546032959 3548341151
  3550709732 3552767478) (b8 3554731249 3556751374 3558813665 3560927654 3563097040 3565316305
  3567595350 3569921365) (b8 3572292713 3574574015 3576818522 3579107900 3581457178 3583862449
  3586188183 3588212486)) (n4 (b8 3590296949 3592425067 3594616727 3596842216 3599120652
  3601454914 3603699555 3605899262) (b8 3608153795 3610457967 3612813173 3615220825 3617675103
  3620180964 3622741230 3625354564) (b8 3628025032 3630738692 3633451741 3635968677 3638403809
  3640701107 3643029682 3645413341) (b8 3647838600 3650317549 3652842693 3655424034 3658065430
  3660752612 3663415186 3665845192)) (n4 (b8 3668246183 3670696813 3673196630 3675749691
  3678348374 3680998559 3683701660 3686457948) (b8 3689264175 3692121538 3694866413 3697627943
  3700426807 3703280006 3706189466 3709146522) (b8 3712146205 3715208236 3718316182 3721482551
  3724706476 3727976596 3731293984 3734670216) (b8 3738080738 3741385779 3744333110 3747325810
  3750368930 3753460330 3756610804 3759815152))) (n4 (n4 (b8 3763074730 3766374836 3769731859
  3773140141 3774553914 3775598286 3776654623 3777752414) (b8 3778901446 3780120981 3781378650
  3782703437 3784073796 3785494869 3786984999 3788518296) (b8 3790015787 3791207019 3792186675
  3793207882 3794232765 3795251067 3796274270 3797351789) (b8 3798481977 3799666092 3800888158
  3802148722 3803337587 3804568458 3805716291 3806897908)) (n4 (b8 3808113868 3809398418
  3810729630 3812115183 3813566047 3815063939 3816271912 3817297598) (b8 3818290477 3819293029
  3820324425 3821411574 3822530219 3823706356 3824915827 3826057084) (b8 3827238622 3828474848
  3829665492 3830848032 3832087155 3833374328 3834715472 3836105900) (b8 3837548525 3839052153
  3840566601 3841535611 3842467842 3843448503 3844430568 3845410477)) (n4 (b8 3846401885
  3847430597 3848508936 3849638951 3850832595 3852063215 3853357445 3854697729) (b8 3856097675
  3857538032 3859022202 3860416569 3861751100 3863151540 3864600440 3866076627) (b8 3867307532
  3868223957 3869167791 3870133101 3871091303 3872047434 3873050697 3874074867) (b8 3875157425
  3876286222 3877463360 3878710380 3879994651 3881323806 3882718537 3884151063)) (n4 (b8
  3885635019 3887155416 3888719201 3890306121 3891941097 3893113188 3894088617 3895024091) (b8
  3895967448 3896951023 3897982783 3899072393 3900210011 3901385849 3902628830 3903903234) (b8
  3905240949 3906607693 3908004793 3909392877 3910828556 3912311219 3913833737 3915371845) (b8
  3916969928 3918345472 3919378234 3920305990 3921227970 3922167985 3923159206 3924196894))) (n4
  (n4 (b8 3925286063 3926422104 3927614460 3928837992 3930113582 3931447581 3932836203 3934256095)
  (b8 3935738725 3937242608 3938749385 3940318933 3941893514 3943237775 3944318213 3945337585) (b8
  3946420165 3947529738 3948700212 3949916928 3951181399 3952492605 3953854464 3955258479) (b8
  3956684792 3958148796 3959607129 3961057992 3962556976 3964038848 3965562057 3967115215)) (n4
  (b8 3968464936 3969553197 3970556972 3971612515 3972702834 3973852753 3975036201 3976268024) (b8
  3977568637 3978879798 3980254641 3981664092 3983089243 3984557977 3986058834 3987612655) (b8
  3989201953 3990847492 3992446514 3993616052 3994615069 3995659289 3996748489 3997891862) (b8
  3999060233 4000298373 4001570406 4002890953 4004240176 4005637666 4007072671 4008522481)) (n4
  (b8 4010018191 4011542318 4013119948 4014754093 4016439652 4018170583 4019936683 4021297351) (b8
  4022389827 4023534994 4024727212 4025949236 4027218398 4028528333 4029892743 4031276634) (b8
  4032677516 4034125396 4035597722 4037138166 4038721751 4040355655 4042032271 4043738151) (b8
  4045513836 4047140876 4048515466 4049899246 4051229944 4052565112 4053912452 4055297177)) (n4
  (b8 4056691127 4058123739 4059574026 4061083331 4062613098 4064199184 4065833730 4067516992) (b8
  4069254178 4070937107 4072305694 4073695543 4075016419 4076306399 4077657770 4078979372) (b8
  4080345773 4081759155 4083211869 4084714287 4086275959 4087872169 4089505138 4091200857) (b8
  4092930203 4094461967 4095795878 4097155437 4098560923 4100013395 4101502360 4103057551))) (n4
  (n4 (b8 4104633224 4106278069 4107946037 4109677103 4111224376 4112817662 4114437398 4116104058)
  (b8 4117811810 4119569537 4121279790 4122908691 4124556098 4126260800 4127827012 4129398287) (b8
  4131002526 4132647809 4134329653 4136076021 4137863801 4139695159 4141571643 4143337055) (b8
  4145088952 4146873330 4148712771 4150589096 4152463512 4154172969 4155750497 4157366636)) (n4
  (b8 4159032403 4160739774 4162497409 4164285372 4166111049 4167874531 4169608636 4171377957) (b8
  4173178049 4175010931 4176900714 4178821561 4180661254 4182277712 4183920783 4185605377) (b8
  4187344340 4189107181 4190933691 4192683180 4194405821 4196134165 4197917895 4199722379) (b8
  4201589934 4203493316 4205462790 4207444475 4209506978 4211582244 4213703951 4215870452)) (n4
  (b8 4218061261 4220138468 4222112530 4223988546 4225809007 4227635442 4229534288 4231470926) (b8
  4233454997 4235457662 4237526504 4239640191 4241785114 4243944058 4245985033 4247903156) (b8
  4249830219 4251817087 4253823718 4255871223 4257989520 4260113341 4262300713 4264533144) (b8
  4266812199 4269106091 4271405866 4273639151 4275908117 4278216042 4280555847 4282959933)) (n4
  (b8 4285404850 4287525560 4288658810 4289818531 4291013592 4292262817 4293568381 4294896333) (b8
  4296256794 4297421827 4298242415 4298970508 4299705689 4300437860 4301170571 4302012674) (b8
  4302890848 4303770889 4304714647 4305494871 4306361162 4307232004 4308196618 4309183929) (b8
  4310210614 4311277037 4312430817 4313608725 4314809278 4316041901 4317355528 4318654214))))
def potTree9 : BTree 10 :=
  .node (n4 (n4 (n4 (b8 818310000 1115040245 1211365880 1265138024 1299837736 1334577448
  1363162989 1391788530) (b8 1411396796 1431045062 1450733328 1466107167 1481521006 1496974845
  1512468684 1528002523) (b8 1543576362 1559190201 1566686964 1574223727 1581800490 1589417253
  1597074016 1604770779) (b8 1610989640 1617248501 1623547362 1629886223 1636265084 1642683945
  1649142806 1655641667)) (n4 (b8 1660703560 1665805453 1670947346 1676129239 1681351132
  1686613025 1691914918 1697256811) (b8 1701465912 1705715013 1710004114 1714333215 1718702316
  1723111417 1727560518 1732049619) (b8 1736578720 1741030225 1745521730 1750053235 1754624740
  1759236245 1763887750 1768579255) (b8 1773310760 1778082265 1782098239 1786154213 1790250187
  1794386161 1798562135 1802778109)) (n4 (b8 1807034083 1811330057 1815666031 1819892717
  1824159403 1828466089 1832812775 1837199461) (b8 1841626147 1846092833 1850599519 1855146205
  1859732891 1864134662 1868576433 1873058204) (b8 1877579975 1882141746 1886743517 1891385288
  1896067059 1900788830 1905550601 1910352372) (b8 1915194143 1920075914 1924997685 1929959456
  1934961227 1940002998 1945084769 1950206540)) (n4 (b8 1955368311 1960570082 1965811853
  1971093624 1976415395 1981777166 1987178937 1992620708) (b8 1998102479 2003624250 2009186021
  2014787792 2020429563 2026111334 2031833105 2037594876) (b8 2043396647 2049238418 2055120189
  2061041960 2067003731 2073005502 2079047273 2085129044) (b8 2091250815 2097412586 2103614357
  2109856128 2116137899 2122459670 2128821441 2135223212))) (n4 (n4 (b8 2141664983 2148146754
  2154668525 2161230296 2167832067 2174473838 2181155609 2187877380) (b8 2194639151 2201440922
  2208282693 2215164464 2222086235 2229048006 2236049777 2243091548) (b8 2250173319 2257295090
  2264456861 2271658632 2278900403 2286182174 2293503945 2300865716) (b8 2308267487 2315709258
  2323191029 2330712800 2338274571 2345876342 2353518113 2361199884)) (n4 (b8 2368921655
  2376683426 2384485197 2392326968 2400208739 2408130510 2416092281 2424094052) (b8 2432135823
  2440217594 2442653143 2444599138 2446552593 2448546048 2450579503 2452652958) (b8 2454766413
  2456919868 2459113323 2461346778 2463620233 2465933688 2468287143 2470680598) (b8 2473114053
  2475587508 2478100963 2480654418 2483247873 2485383143 2487019088 2488695033)) (n4 (b8
  2490410978 2492166923 2493962868 2495798813 2497584651 2499363011 2501181371 2503039731) (b8
  2504938091 2506876451 2508854811 2510873171 2512931531 2515029891 2517168251 2519346611) (b8
  2521564971 2523823331 2526121691 2528034555 2529412842 2530830466 2532287029 2533782986) (b8
  2535317724 2536891811 2538504882 2540156683 2541847478 2543577214 2545217437 2546863723)) (n4
  (b8 2548548208 2550271170 2552032557 2553832115 2555669748 2557545793 2559460119 2561412429) (b8
  2563402890 2565431699 2567498252 2569426060 2570647461 2571903743 2573194959 2574521285) (b8
  2575882288 2577278460 2578709319 2580175028 2581675542 2583211018 2584781424 2586386512) (b8
  2587968309 2589491408 2591048778 2592640779 2594267034 2595927569 2597622807 2599352215))) (n4
  (n4 (b8 2601116043 2602914478 2604747053 2606614087 2608515740 2610253888 2611395320 2612568058)
  (b8 2613772038 2615007471 2616274028 2617571925 2618901390 2620261944 2621653969 2623077300) (b8
  2624531798 2626017877 2627535235 2628985377 2630421858 2631889590 2633388232 2634917837) (b8
  2636478685 2638070481 2639693513 2641347557 2643032728 2644749056 2646496390 2648275134)) (n4
  (b8 2650084951 2651277468 2652403631 2653558282 2654740939 2655951993 2657191277 2658459034) (b8
  2659755030 2661079613 2662432283 2663813681 2665223376 2666658334 2667988893 2669347806) (b8
  2670734681 2672149775 2673593066 2675064488 2676564363 2678092451 2679648672 2681233461) (b8
  2682846470 2684487691 2686157511 2687855778 2689582375 2691147845 2692262830 2693403571)) (n4
  (b8 2694570420 2695762822 2696981124 2698225374 2699495530 2700791427 2702113272 2703461230) (b8
  2704747001 2706017238 2707313079 2708634803 2709982401 2711355625 2712754695 2714179736) (b8
  2715630432 2717107211 2718609968 2720138766 2721693434 2723274139 2724881000 2726513857) (b8
  2728172935 2729858160 2731569490 2732959432 2734121193 2735306705 2736516258 2737749331)) (n4
  (b8 2739006502 2740287431 2741474391 2742679218 2743907520 2745159811 2746435663 2747735418) (b8
  2749058745 2750406171 2751777283 2753172423 2754591333 2756034182 2757501120 2758992211) (b8
  2760507127 2762046202 2763609520 2765196822 2766808278 2768444174 2770104266 2771788567) (b8
  2773497268 2775230197 2776555469 2777675591 2778817488 2779981529 2781167138 2782375226))) (n4
  (n4 (b8 2783605264 2784857389 2786131504 2787427720 2788746148 2790086953 2791449803 2792835137)
  (b8 2794242616 2795672278 2797124612 2798599347 2800096368 2801616015 2803158203 2804722713) (b8
  2806310045 2807919823 2809552419 2811207681 2812885640 2814586414 2816309925 2818056323) (b8
  2819679862 2820869847 2822080292 2823311455 2824563203 2825836046 2827129543 2828443701)) (n4
  (b8 2829778903 2831135193 2832512218 2833910159 2835329361 2836769227 2838230385 2839712647) (b8
  2841216180 2842740505 2844286666 2845853598 2847442091 2849051694 2850682804 2852335212) (b8
  2854008883 2855704322 2857421256 2859159593 2860919680 2862701167 2864504467 2866221214) (b8
  2867518030 2868834626 2870171233 2871527502 2872903369 2874299282 2875715311 2877151016)) (n4
  (b8 2878606973 2880082733 2881578560 2883094551 2884630851 2886186774 2887763390 2889360022) (b8
  2890977092 2892614377 2894271797 2895949646 2897648366 2899366977 2901106261 2902866039) (b8
  2904646244 2906447497 2908268810 2910111225 2911974132 2913857561 2915762073 2917491796) (b8
  2918935573 2920398148 2921880020 2923381301 2924901560 2926441108 2927999915 2929578016)) (n4
  (b8 2931175504 2932792359 2934428630 2936084439 2937759613 2939454407 2941168519 2942902617) (b8
  2944655968 2946429225 2948222114 2950034683 2951867272 2953719541 2955591391 2957483464) (b8
  2959395067 2961327050 2963278745 2965250412 2967242417 2969254081 2971286217 2973338167) (b8
  2975169877 2976804018 2978457048 2980128215 2981818794 2983528072 2985256245 2987003022)))) (n4
  (n4 (n4 (b8 2988769084 2990554018 2992357700 2994180684 2996022868 2997883750 2999764084
  3001663464) (b8 3003582281 3005520252 3007477450 3009454027 3011449832 3013465186 3015500075
  3017553888) (b8 3019627942 3021721062 3023833597 3025966106 3028117999 3030078017 3031986597
  3033914018) (b8 3035860364 3037825622 3039809770 3041813068 3043835069 3045876662 3047936650
  3050016105)) (n4 (b8 3052114836 3054232660 3056369653 3058525686 3060701180 3062896262
  3065110146 3067244700) (b8 3069363312 3071500729 3073657164 3075832907 3078027408 3080241397
  3082474585 3084727336) (b8 3086999123 3089289901 3091600343 3093929905 3096279220 3098647696
  3101036077 3103443554) (b8 3105870710 3108317517 3110784055 3113270056 3115775689 3118301359
  3120846408 3123411317)) (n4 (b8 3125635295 3127862123 3130108142 3132373168 3134656617
  3136959299 3139280617 3141621550) (b8 3143981118 3146359650 3148757174 3151173880 3153609734
  3156064792 3158538533 3161032153) (b8 3163545039 3166076925 3168628122 3171198879 3173789423
  3176398880 3179027749 3181676426) (b8 3184344268 3187031934 3189738825 3192466118 3195212473
  3197978230 3200764476 3203569850)) (n4 (b8 3206395705 3209240689 3212106188 3214990870
  3217895724 3220820932 3223765955 3226730639) (b8 3229715814 3232721139 3235746028 3238791218
  3241856818 3244942769 3248048735 3251174807) (b8 3253700515 3254632990 3255593175 3256559426
  3257554527 3258572970 3259558009 3260382715) (b8 3261223525 3262089477 3262977961 3263879041
  3264807774 3265755640 3266723519 3267712405))) (n4 (n4 (b8 3268716667 3269746651 3270795249
  3271867611 3272958031 3274075133 3275207299 3276358638) (b8 3277493102 3278305915 3278930265
  3279571211 3280233525 3280907923 3281606194 3282325695) (b8 3283063098 3283818647 3284599003
  3285391190 3286202682 3287034754 3287888127 3288759672) (b8 3289647273 3290555612 3291482606
  3292295455 3293053822 3293826893 3294619508 3295434168)) (n4 (b8 3296270068 3297123338
  3297997636 3298889346 3299803308 3300737992 3301686281 3302660535) (b8 3303648158 3304663563
  3305692683 3306745172 3307819434 3308911344 3310019681 3311150958) (b8 3312038482 3312715867
  3313326014 3313953698 3314599191 3315261000 3315947508 3316647372) (b8 3317365643 3318099750
  3318856809 3319631085 3320422684 3321231922 3322061185 3322909260)) (n4 (b8 3323773928
  3324658883 3325561008 3326313107 3327072619 3327849051 3328639809 3329456174) (b8 3330284088
  3331136539 3332005140 3332893844 3333804301 3334729398 3335672557 3336638366) (b8 3337621225
  3338620935 3339645165 3340689993 3341748012 3342828870 3343924563 3344772508) (b8 3345428723
  3346015672 3346618387 3347244802 3347883166 3348535840 3349209254 3349900357)) (n4 (b8
  3350612134 3351335709 3352081238 3352846585 3353622473 3354418288 3355236928 3356067089) (b8
  3356924198 3357793253 3358681698 3359582182 3360504893 3361448544 3362347521 3363172194) (b8
  3364017688 3364882899 3365762092 3366664115 3367586428 3368521126 3369474453 3370446292) (b8
  3371440344 3372449929 3373476553 3374528429 3375590159 3376442675 3377094249 3377658369))) (n4
  (n4 (b8 3378237978 3378833883 3379444870 3380076957 3380723395 3381388516 3382072388 3382766724)
  (b8 3383479735 3384212381 3384963996 3385726619 3386512858 3387313882 3388130467 3388963612) (b8
  3389817286 3390686412 3391572934 3392476741 3393400101 3394333257 3395292860 3396264089) (b8
  3397255162 3398266694 3399293185 3400334378 3401394204 3402475478 3403572226 3404684757)) (n4
  (b8 3405790356 3406780440 3407437931 3408103518 3408792487 3409362926 3409946887 3410539023) (b8
  3411150554 3411778305 3412417913 3413079176 3413755396 3414451800 3415158808 3415881677) (b8
  3416622889 3417383569 3418155983 3418945244 3419754567 3420577660 3421418376 3422278498) (b8
  3423157044 3424043200 3424949383 3425876797 3426816571 3427778821 3428753769 3429743739)) (n4
  (b8 3430752298 3431781194 3432826284 3433887192 3434964064 3436057609 3437070602 3437842288) (b8
  3438484047 3439144609 3439817314 3440502195 3441204111 3441923342 3442659640 3443408942) (b8
  3444178949 3444958496 3445758541 3446568382 3447403433 3448246146 3449109907 3449942148) (b8
  3450737393 3451548289 3452374717 3453216195 3454077038 3454947281 3455846244 3456749604)) (n4
  (b8 3457674768 3458613550 3459569509 3460545207 3461531839 3462542426 3463559408 3464599112) (b8
  3465655435 3466716114 3467680454 3468323401 3468953662 3469593167 3470248894 3470919383) (b8
  3471605694 3472301684 3473017213 3473752505 3474495821 3475263916 3476038728 3476829113) (b8
  3477634417 3478456343 3479297926 3480154945 3481021478 3481905094 3482806369 3483724167))) (n4
  (n4 (b8 3484653533 3485602721 3486565913 3487543495 3488535875 3489551759 3490580705 3491617008)
  (b8 3492676627 3493748731 3494839935 3495948757 3497069231 3498212496 3499326967 3499957817) (b8
  3500592360 3501251850 3501922133 3502606904 3503303480 3504020284 3504752160 3505496397) (b8
  3506255759 3507031092 3507817960 3508618308 3509437339 3510273774 3511123213 3511985570)) (n4
  (b8 3512863259 3513760070 3514669744 3515592881 3516533974 3517483341 3518453160 3519440712) (b8
  3520445988 3521460616 3522491064 3523536137 3524601533 3525682178 3526779972 3527883431) (b8
  3529009550 3530098261 3531052432 3531776210 3532508367 3533262931 3534020418 3534796421) (b8
  3535593587 3536405203 3537221969 3538055100 3538902353 3539771076 3540644395 3541544581)) (n4
  (b8 3542450944 3543376095 3544309666 3545261873 3546227600 3547214773 3548209154 3549216951) (b8
  3550243721 3551286928 3552344749 3553412331 3554499849 3555598116 3556717590 3557852085) (b8
  3558999125 3560157035 3561142059 3561851938 3562567894 3563308427 3564051043 3564810012) (b8
  3565588062 3566374635 3567183396 3567999060 3568828496 3569673553 3570535484 3571415726)) (n4
  (b8 3572300252 3573200559 3574115409 3575048640 3576001868 3576961671 3577935360 3578923060) (b8
  3579920174 3580940614 3581977688 3583021956 3584088455 3585157859 3586253390 3587357018) (b8
  3588481917 3589620057 3590768059 3591932950 3593108953 3594303434 3595516157 3596738197) (b8
  3597875412 3598868705 3599708232 3600552292 3601406539 3602277427 3603152711 3604047397))))
def tSched (m r : ℕ) : ℕ := min (gridExp m) (tIdxSched (gridExp m - 1) r).1
def idxSched (m r : ℕ) : Fin 44 :=
  if 2 ≤ m then ⟨(tIdxSched (gridExp m - 1) r).2 % 44, Nat.mod_lt _ (by decide)⟩
  else ⟨0, by decide⟩
def potTree (im : Fin 10) : BTree 10 :=
  match im.val with
  | 0 => potTree0 | 1 => potTree1 | 2 => potTree2 | 3 => potTree3 | 4 => potTree4
  | 5 => potTree5 | 6 => potTree6 | 7 => potTree7 | 8 => potTree8 | _ => potTree9
def potWInt (im : Fin 10) : ℕ → ℕ
  | 0 => 0
  | u + 1 => (potTree im).get u
def slopeWInt (im : Fin 10) (u : ℕ) : ℕ := potWInt im u - potWInt im (u - 1)
/-- Depth-`d` divide-and-conquer universal quantifier over `[base, base + 2 ^ d)`. -/
def checkRange : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, base, P => P base
  | d + 1, base, P => checkRange d base P && checkRange d (base + 2 ^ d) P
lemma checkRange_sound (P : ℕ → Bool) : ∀ (d base : ℕ), checkRange d base P = true → ∀ i, base ≤ i →
    i < base + 2 ^ d → P i = true := by
  intro d
  induction d with
  | zero =>
    intro base h i hlo hhi; have hi_eq : i = base := (by omega); subst hi_eq
    simpa [checkRange] using h
  | succ d ih =>
    intro base h i hlo hhi; simp only [checkRange, Bool.and_eq_true] at h
    by_cases hmid : i < base + 2 ^ d
    · exact ih base h.1 i hlo hmid
    · refine ih (base + 2 ^ d) h.2 i (by omega) ?_
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := (by ring); omega
/-- Depth-`d` divide-and-conquer sum over `[base, base + 2 ^ d)`. -/
def treeSum : ℕ → ℕ → (ℕ → ℕ) → ℕ
  | 0, base, f => f base
  | d + 1, base, f => treeSum d base f + treeSum d (base + 2 ^ d) f
lemma treeSum_eq_sum_Ico (f : ℕ → ℕ) :
    ∀ (d base : ℕ), treeSum d base f = ∑ x ∈ Finset.Ico base (base + 2 ^ d), f x := by
  intro d
  induction d with
  | zero => intro base; simp [treeSum]
  | succ d ih =>
    intro base; rw [treeSum, ih base, ih (base + 2 ^ d)]
    have hpow : base + 2 ^ (d + 1) = (base + 2 ^ d) + 2 ^ d := by
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := (by ring); omega
    rw [hpow, Finset.sum_Ico_consecutive f (Nat.le_add_right _ _) (Nat.le_add_right _ _)]
def newtonSqrt : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | s + 1, n, g => newtonSqrt s n ((g + n / max 1 g) / 2)
/-- Force a `ℕ` value to WHNF before invoking `k` in `decide +kernel`. -/
def withForcedNat {α : Type*} (x : ℕ) (k : ℕ → α) : α :=
  match x with
  | 0 => k 0
  | n + 1 => k (n + 1)
lemma withForcedNat_eq {α : Type*} (x : ℕ) (k : ℕ → α) : withForcedNat x k = k x := by
  cases x <;> rfl
def sqCeil (b r : ℕ) : ℕ :=
  let n := (b * M_scale * M_scale - 1) / r
  let g0 := if 64 * r ≤ b then 16 * M_scale else if 4 * r ≤ b then 4 * M_scale else if r ≤ 4 * b
    then M_scale else if r ≤ 64 * b then M_scale / 4 else M_scale / 16
  withForcedNat (newtonSqrt 6 n g0) fun g ↦
    (if n < g * g then g - 1 else g) + 1
def invSqrtLo (x : ℕ) : ℕ :=
  let n := (M_scale * M_scale) / max 1 x
  let g0 := if x ≤ 4 then M_scale else if x ≤ 64 then M_scale / 4 else M_scale / 16
  withForcedNat (newtonSqrt 6 n g0) fun g ↦
    if g * g ≤ n then g else g - 1
def pow2Ceil : ℕ → ℕ → ℕ
  | 0, q => q
  | t + 1, q => pow2Ceil t (((M_scale - 1) + q * q) / M_scale)
def pow2Floor : ℕ → ℕ → ℕ
  | 0, q => q
  | t + 1, q => pow2Floor t ((q * q) / M_scale)
def sinSqLo (idx : Fin 44) : ℕ := varPhiSinLoNum idx * varPhiSinLoNum idx
def qjCeil (j : ℕ) (idx : Fin 44) (r : ℕ) : ℕ :=
  let den := 10000000000000000 * r
  ((den - 1) + M_scale * (den - j * sinSqLo idx)) / den
def qjFloor (j : ℕ) (idx : Fin 44) (r : ℕ) : ℕ :=
  let den := 10000000000000000 * r
  (M_scale * (den - j * sinSqLo idx)) / den
def stepIntUpper (idx : Fin 44) (r : ℕ) (F : ℕ → ℕ) (d : ℕ) : ℕ :=
  let v0 := F d
  let v1 := F (d + 1)
  v1 + ((M_scale - 1) + qjCeil (r - d) idx r * (v0 - v1)) / M_scale
def forceCons (x : ℕ) (xs : List ℕ) : List ℕ :=
  match x with
  | 0 =>
    match xs with
    | [] => [0]
    | y :: ys => 0 :: y :: ys
  | n + 1 =>
    match xs with
    | [] => [n + 1]
    | y :: ys => (n + 1) :: y :: ys
def ofFnFrom (F : ℕ → ℕ) (d₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => F d₀ :: ofFnFrom F (d₀ + 1) k
def qListFrom (idx : Fin 44) (r d₀ : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => qjCeil (r - d₀) idx r :: qListFrom idx r (d₀ + 1) k
def stepWithQs : List ℕ → List ℕ → List ℕ
  | v0 :: v1 :: vs, q :: qs =>
    forceCons (v1 + ((M_scale - 1) + q * (v0 - v1)) / M_scale) (stepWithQs (v1 :: vs) qs)
  | _, _ => []
def iterStepWithQs (qs : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, vs => vs
  | b + 1, vs =>
    match stepWithQs vs qs with
    | [] => []
    | x :: xs => iterStepWithQs qs b (x :: xs)
def checkMode3 (im : Fin 10) (idx : Fin 44) (r b sc Wr : ℕ) : Bool :=
  let qs := qListFrom idx r 0 b
  let init := ofFnFrom (fun d ↦ potWInt im (r - d)) 0 (b + 1)
  let v_end := (iterStepWithQs qs b init).headD 0
  decide (sc + v_end ≤ Wr)
def checkSlopeStep (im : Fin 10) (i : ℕ) : Bool :=
  let u := i + 1
  let w0 := potWInt im i
  let w1 := potWInt im u
  let w_first := potWInt im 1
  let A2 := cubicA2 im
  let A3 := cubicA3 im
  decide (w0 ≤ w1) &&
    decide (w1 + A2 * (u * (u - 1)) ≤ w_first * u + A3 * (u * (u - 1) * (u - 2))) &&
    if i + 1 < 1024 then
      let w2 := potWInt im (i + 2)
      decide (w2 - w1 ≤ w1 - w0 + 2 * gammaIm im)
    else true
def checkDriftAt (im : Fin 10) (r : ℕ) : Bool :=
  if 2 ≤ r ∧ r ≤ 1024 then
    let p := tIdxSched im.val r
    let t := min (im.val + 1) p.1
    let idx : Fin 44 := ⟨p.2 % 44, Nat.mod_lt _ (by decide)⟩
    let b := 2 ^ t
    withForcedNat (pow2Ceil t (qjCeil 1 idx r)) fun qt1_hi ↦
      let qt1_lo := pow2Floor t (qjFloor 1 idx r)
      let qt2_hi := pow2Ceil t (qjCeil 2 idx r)
      let qt2_lo := pow2Floor t (qjFloor 2 idx r)
      let qt3_hi := pow2Ceil t (qjCeil 3 idx r)
      let sq := sqCeil b r
      let sc := (99999999 + varPhiCHiNum idx * sq) / 100000000
      let u₀ := max 1 (min r (((M_scale - 1) + r * qt1_hi) / M_scale))
      let Wu₀ := potWInt im u₀
      let wu₀ := Wu₀ - potWInt im (u₀ - 1)
      let Wr := potWInt im r
      let w1 := potWInt im 1
      let γ := gammaIm im
      let A2 := cubicA2 im
      let A3 := cubicA3 im
      let m3 := decide (t ≤ 6) && checkMode3 im idx r b sc Wr
      let m0 := decide (1 ≤ u₀ ∧ u₀ ≤ r) && decide (M_scale * sc + M_scale * Wu₀ + wu₀ * (r *
        qt1_hi) + γ * (r * (r - 1) * qt2_hi + u₀ * (u₀ - 1) * M_scale) ≤ M_scale * Wr + wu₀ *
        (M_scale * u₀) + 2 * γ * (u₀ - 1) * r * qt1_lo)
      let m1 := decide (3 * sinSqLo idx ≤ 10000000000000000 * r) && decide (M_scale * sc + w1 * r *
        qt1_hi + A3 * (r * (r - 1) * (r - 2)) * qt3_hi ≤ M_scale * Wr + A2 * (r * (r - 1)) * qt2_lo)
      decide (M_scale ^ 2 * b ≤ r * sq ^ 2) && (m0 || m1 || m3)
  else true
def checkSlopeIm (im : Fin 10) : Bool :=
  decide (818310000 ≤ potWInt im 1) && checkRange 10 0 (checkSlopeStep im)
def checkPotIm (im : Fin 10) : Bool := checkSlopeIm im && checkRange 10 1 (checkDriftAt im)
lemma checkRange_join {d base mid : ℕ} {P : ℕ → Bool}
    (h1 : checkRange d base P = true) (h2 : checkRange d mid P = true)
    (hmid : base + 2 ^ d = mid := by decide) :
    checkRange (d + 1) base P = true := by subst hmid; simp only [checkRange, h1, h2, Bool.and_self]
lemma checkPotIm_join {im : Fin 10} (hs : checkSlopeIm im = true) (hd : checkRange 10 1
    (checkDriftAt im) = true) : checkPotIm im = true := by
  simp only [checkPotIm, hs, hd, Bool.and_self]
lemma checkInvSqrtLo_all :
    checkRange 10 1 (fun x ↦ decide (x * (invSqrtLo x) ^ 2 ≤ M_scale ^ 2)) = true := rfl
private abbrev wdIm0 : Fin 10 := ⟨0, by omega⟩
private abbrev wdIm1 : Fin 10 := ⟨1, by omega⟩
private abbrev wdIm2 : Fin 10 := ⟨2, by omega⟩
private abbrev wdIm3 : Fin 10 := ⟨3, by omega⟩
private abbrev wdIm4 : Fin 10 := ⟨4, by omega⟩
private abbrev wdIm5 : Fin 10 := ⟨5, by omega⟩
private abbrev wdIm6 : Fin 10 := ⟨6, by omega⟩
private abbrev wdIm7 : Fin 10 := ⟨7, by omega⟩
private abbrev wdIm8 : Fin 10 := ⟨8, by omega⟩
private abbrev wdIm9 : Fin 10 := ⟨9, by omega⟩
private lemma wdSl_0 : checkSlopeIm wdIm0 = true := rfl
private lemma wdDr_0_0 : checkRange 7 1 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDr_0_1 : checkRange 7 129 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDr_0_2 : checkRange 7 257 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDr_0_3 : checkRange 7 385 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDr_0_4 : checkRange 7 513 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDr_0_5 : checkRange 7 641 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDr_0_6 : checkRange 7 769 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDr_0_7 : checkRange 7 897 (checkDriftAt wdIm0) = true := by conv => lhs; whnf
private lemma wdDrAll_0 : checkRange 10 1 (checkDriftAt wdIm0) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join wdDr_0_0 wdDr_0_1 (hmid := rfl))
      (
      checkRange_join wdDr_0_2 wdDr_0_3 (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join wdDr_0_4 wdDr_0_5 (hmid := rfl))
      (
      checkRange_join wdDr_0_6 wdDr_0_7 (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_0 : checkPotIm ⟨0, by decide⟩ = true :=
  checkPotIm_join wdSl_0 wdDrAll_0
private lemma wdSl_1 : checkSlopeIm wdIm1 = true := rfl
private lemma wdDr_1_0 : checkRange 7 1 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDr_1_1 : checkRange 7 129 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDr_1_2 : checkRange 7 257 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDr_1_3 : checkRange 7 385 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDr_1_4 : checkRange 7 513 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDr_1_5 : checkRange 7 641 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDr_1_6 : checkRange 7 769 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDr_1_7 : checkRange 7 897 (checkDriftAt wdIm1) = true := by conv => lhs; whnf
private lemma wdDrAll_1 : checkRange 10 1 (checkDriftAt wdIm1) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join wdDr_1_0 wdDr_1_1 (hmid := rfl))
      (
      checkRange_join wdDr_1_2 wdDr_1_3 (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join wdDr_1_4 wdDr_1_5 (hmid := rfl))
      (
      checkRange_join wdDr_1_6 wdDr_1_7 (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_1 : checkPotIm ⟨1, by decide⟩ = true :=
  checkPotIm_join wdSl_1 wdDrAll_1
lemma checkSlopeIm_2 : checkSlopeIm ⟨2, by decide⟩ = true := rfl
private lemma wdDr_2_0_0 : checkRange 6 1 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_0_1 : checkRange 6 65 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_0_2 : checkRange 6 129 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_0_3 : checkRange 6 193 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
lemma checkDrift_2_0 : checkRange 8 1 (checkDriftAt ⟨2, by decide⟩) = true :=
  checkRange_join
    (
    checkRange_join wdDr_2_0_0 wdDr_2_0_1 (hmid := rfl))
    (
    checkRange_join wdDr_2_0_2 wdDr_2_0_3 (hmid := rfl))
    (hmid := rfl)
private lemma wdDr_2_1_0 : checkRange 6 257 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_1_1 : checkRange 6 321 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_1_2 : checkRange 6 385 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_1_3 : checkRange 6 449 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
lemma checkDrift_2_1 : checkRange 8 257 (checkDriftAt ⟨2, by decide⟩) = true :=
  checkRange_join
    (
    checkRange_join wdDr_2_1_0 wdDr_2_1_1 (hmid := rfl))
    (
    checkRange_join wdDr_2_1_2 wdDr_2_1_3 (hmid := rfl))
    (hmid := rfl)
private lemma wdDr_2_2_0 : checkRange 6 513 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_2_1 : checkRange 6 577 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_2_2 : checkRange 6 641 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_2_3 : checkRange 6 705 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
lemma checkDrift_2_2 : checkRange 8 513 (checkDriftAt ⟨2, by decide⟩) = true :=
  checkRange_join
    (
    checkRange_join wdDr_2_2_0 wdDr_2_2_1 (hmid := rfl))
    (
    checkRange_join wdDr_2_2_2 wdDr_2_2_3 (hmid := rfl))
    (hmid := rfl)
private lemma wdDr_2_3_0 : checkRange 6 769 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_3_1 : checkRange 6 833 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_3_2 : checkRange 6 897 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
private lemma wdDr_2_3_3 : checkRange 6 961 (checkDriftAt wdIm2) = true := by conv => lhs; whnf
lemma checkDrift_2_3 : checkRange 8 769 (checkDriftAt ⟨2, by decide⟩) = true :=
  checkRange_join
    (
    checkRange_join wdDr_2_3_0 wdDr_2_3_1 (hmid := rfl))
    (
    checkRange_join wdDr_2_3_2 wdDr_2_3_3 (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_2 : checkPotIm ⟨2, by decide⟩ = true :=
  checkPotIm_join checkSlopeIm_2 (checkRange_join (checkRange_join checkDrift_2_0 checkDrift_2_1)
    (checkRange_join checkDrift_2_2 checkDrift_2_3))
private lemma wdSl_3 : checkSlopeIm wdIm3 = true := rfl
private lemma wdDr_3_0 : checkRange 6 1 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_1 : checkRange 6 65 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_2 : checkRange 6 129 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_3 : checkRange 6 193 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_4 : checkRange 6 257 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_5 : checkRange 6 321 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_6 : checkRange 6 385 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_7 : checkRange 6 449 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_8 : checkRange 6 513 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_9 : checkRange 6 577 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_10 : checkRange 6 641 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_11 : checkRange 6 705 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_12 : checkRange 6 769 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_13 : checkRange 6 833 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_14 : checkRange 6 897 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDr_3_15 : checkRange 6 961 (checkDriftAt wdIm3) = true := by conv => lhs; whnf
private lemma wdDrAll_3 : checkRange 10 1 (checkDriftAt wdIm3) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join wdDr_3_0 wdDr_3_1 (hmid := rfl))
        (
        checkRange_join wdDr_3_2 wdDr_3_3 (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join wdDr_3_4 wdDr_3_5 (hmid := rfl))
        (
        checkRange_join wdDr_3_6 wdDr_3_7 (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join wdDr_3_8 wdDr_3_9 (hmid := rfl))
        (
        checkRange_join wdDr_3_10 wdDr_3_11 (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join wdDr_3_12 wdDr_3_13 (hmid := rfl))
        (
        checkRange_join wdDr_3_14 wdDr_3_15 (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_3 : checkPotIm ⟨3, by decide⟩ = true :=
  checkPotIm_join wdSl_3 wdDrAll_3
private lemma wdSl_4 : checkSlopeIm wdIm4 = true := rfl
private lemma wdDr_4_0 : checkRange 6 1 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_1 : checkRange 6 65 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_2 : checkRange 6 129 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_3 : checkRange 6 193 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_4 : checkRange 6 257 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_5 : checkRange 6 321 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_6 : checkRange 6 385 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_7 : checkRange 6 449 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_8 : checkRange 6 513 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_9 : checkRange 6 577 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_10 : checkRange 6 641 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_11 : checkRange 6 705 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_12 : checkRange 6 769 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_13 : checkRange 6 833 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_14 : checkRange 6 897 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDr_4_15 : checkRange 6 961 (checkDriftAt wdIm4) = true := by conv => lhs; whnf
private lemma wdDrAll_4 : checkRange 10 1 (checkDriftAt wdIm4) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join wdDr_4_0 wdDr_4_1 (hmid := rfl))
        (
        checkRange_join wdDr_4_2 wdDr_4_3 (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join wdDr_4_4 wdDr_4_5 (hmid := rfl))
        (
        checkRange_join wdDr_4_6 wdDr_4_7 (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join wdDr_4_8 wdDr_4_9 (hmid := rfl))
        (
        checkRange_join wdDr_4_10 wdDr_4_11 (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join wdDr_4_12 wdDr_4_13 (hmid := rfl))
        (
        checkRange_join wdDr_4_14 wdDr_4_15 (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_4 : checkPotIm ⟨4, by decide⟩ = true :=
  checkPotIm_join wdSl_4 wdDrAll_4
private lemma wdSl_5 : checkSlopeIm wdIm5 = true := rfl
private lemma wdDr_5_0 : checkRange 5 1 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_1 : checkRange 5 33 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_2 : checkRange 5 65 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_3 : checkRange 5 97 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_4 : checkRange 5 129 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_5 : checkRange 5 161 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_6 : checkRange 5 193 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_7 : checkRange 5 225 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_8 : checkRange 5 257 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_9 : checkRange 5 289 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_10 : checkRange 5 321 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_11 : checkRange 5 353 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_12 : checkRange 5 385 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_13 : checkRange 5 417 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_14 : checkRange 5 449 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_15 : checkRange 5 481 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_16 : checkRange 5 513 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_17 : checkRange 5 545 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_18 : checkRange 5 577 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_19 : checkRange 5 609 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_20 : checkRange 5 641 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_21 : checkRange 5 673 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_22 : checkRange 5 705 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_23 : checkRange 5 737 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_24 : checkRange 5 769 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_25 : checkRange 5 801 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_26 : checkRange 5 833 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_27 : checkRange 5 865 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_28 : checkRange 5 897 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_29 : checkRange 5 929 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_30 : checkRange 5 961 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDr_5_31 : checkRange 5 993 (checkDriftAt wdIm5) = true := by conv => lhs; whnf
private lemma wdDrAll_5 : checkRange 10 1 (checkDriftAt wdIm5) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_5_0 wdDr_5_1 (hmid := rfl))
          (
          checkRange_join wdDr_5_2 wdDr_5_3 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_5_4 wdDr_5_5 (hmid := rfl))
          (
          checkRange_join wdDr_5_6 wdDr_5_7 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_5_8 wdDr_5_9 (hmid := rfl))
          (
          checkRange_join wdDr_5_10 wdDr_5_11 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_5_12 wdDr_5_13 (hmid := rfl))
          (
          checkRange_join wdDr_5_14 wdDr_5_15 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_5_16 wdDr_5_17 (hmid := rfl))
          (
          checkRange_join wdDr_5_18 wdDr_5_19 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_5_20 wdDr_5_21 (hmid := rfl))
          (
          checkRange_join wdDr_5_22 wdDr_5_23 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_5_24 wdDr_5_25 (hmid := rfl))
          (
          checkRange_join wdDr_5_26 wdDr_5_27 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_5_28 wdDr_5_29 (hmid := rfl))
          (
          checkRange_join wdDr_5_30 wdDr_5_31 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_5 : checkPotIm ⟨5, by decide⟩ = true :=
  checkPotIm_join wdSl_5 wdDrAll_5
private lemma wdSl_6 : checkSlopeIm wdIm6 = true := rfl
private lemma wdDr_6_0 : checkRange 5 1 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_1 : checkRange 5 33 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_2 : checkRange 5 65 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_3 : checkRange 5 97 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_4 : checkRange 5 129 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_5 : checkRange 5 161 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_6 : checkRange 5 193 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_7 : checkRange 5 225 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_8 : checkRange 5 257 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_9 : checkRange 5 289 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_10 : checkRange 5 321 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_11 : checkRange 5 353 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_12 : checkRange 5 385 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_13 : checkRange 5 417 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_14 : checkRange 5 449 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_15 : checkRange 5 481 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_16 : checkRange 5 513 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_17 : checkRange 5 545 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_18 : checkRange 5 577 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_19 : checkRange 5 609 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_20 : checkRange 5 641 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_21 : checkRange 5 673 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_22 : checkRange 5 705 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_23 : checkRange 5 737 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_24 : checkRange 5 769 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_25 : checkRange 5 801 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_26 : checkRange 5 833 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_27 : checkRange 5 865 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_28 : checkRange 5 897 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_29 : checkRange 5 929 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_30 : checkRange 5 961 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDr_6_31 : checkRange 5 993 (checkDriftAt wdIm6) = true := by conv => lhs; whnf
private lemma wdDrAll_6 : checkRange 10 1 (checkDriftAt wdIm6) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_6_0 wdDr_6_1 (hmid := rfl))
          (
          checkRange_join wdDr_6_2 wdDr_6_3 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_6_4 wdDr_6_5 (hmid := rfl))
          (
          checkRange_join wdDr_6_6 wdDr_6_7 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_6_8 wdDr_6_9 (hmid := rfl))
          (
          checkRange_join wdDr_6_10 wdDr_6_11 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_6_12 wdDr_6_13 (hmid := rfl))
          (
          checkRange_join wdDr_6_14 wdDr_6_15 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_6_16 wdDr_6_17 (hmid := rfl))
          (
          checkRange_join wdDr_6_18 wdDr_6_19 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_6_20 wdDr_6_21 (hmid := rfl))
          (
          checkRange_join wdDr_6_22 wdDr_6_23 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_6_24 wdDr_6_25 (hmid := rfl))
          (
          checkRange_join wdDr_6_26 wdDr_6_27 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_6_28 wdDr_6_29 (hmid := rfl))
          (
          checkRange_join wdDr_6_30 wdDr_6_31 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_6 : checkPotIm ⟨6, by decide⟩ = true :=
  checkPotIm_join wdSl_6 wdDrAll_6
private lemma wdSl_7 : checkSlopeIm wdIm7 = true := rfl
private lemma wdDr_7_0 : checkRange 5 1 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_1 : checkRange 5 33 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_2 : checkRange 5 65 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_3 : checkRange 5 97 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_4 : checkRange 5 129 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_5 : checkRange 5 161 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_6 : checkRange 5 193 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_7 : checkRange 5 225 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_8 : checkRange 5 257 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_9 : checkRange 5 289 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_10 : checkRange 5 321 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_11 : checkRange 5 353 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_12 : checkRange 5 385 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_13 : checkRange 5 417 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_14 : checkRange 5 449 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_15 : checkRange 5 481 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_16 : checkRange 5 513 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_17 : checkRange 5 545 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_18 : checkRange 5 577 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_19 : checkRange 5 609 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_20 : checkRange 5 641 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_21 : checkRange 5 673 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_22 : checkRange 5 705 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_23 : checkRange 5 737 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_24 : checkRange 5 769 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_25 : checkRange 5 801 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_26 : checkRange 5 833 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_27 : checkRange 5 865 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_28 : checkRange 5 897 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_29 : checkRange 5 929 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_30 : checkRange 5 961 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDr_7_31 : checkRange 5 993 (checkDriftAt wdIm7) = true := by conv => lhs; whnf
private lemma wdDrAll_7 : checkRange 10 1 (checkDriftAt wdIm7) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_7_0 wdDr_7_1 (hmid := rfl))
          (
          checkRange_join wdDr_7_2 wdDr_7_3 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_7_4 wdDr_7_5 (hmid := rfl))
          (
          checkRange_join wdDr_7_6 wdDr_7_7 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_7_8 wdDr_7_9 (hmid := rfl))
          (
          checkRange_join wdDr_7_10 wdDr_7_11 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_7_12 wdDr_7_13 (hmid := rfl))
          (
          checkRange_join wdDr_7_14 wdDr_7_15 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_7_16 wdDr_7_17 (hmid := rfl))
          (
          checkRange_join wdDr_7_18 wdDr_7_19 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_7_20 wdDr_7_21 (hmid := rfl))
          (
          checkRange_join wdDr_7_22 wdDr_7_23 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_7_24 wdDr_7_25 (hmid := rfl))
          (
          checkRange_join wdDr_7_26 wdDr_7_27 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_7_28 wdDr_7_29 (hmid := rfl))
          (
          checkRange_join wdDr_7_30 wdDr_7_31 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_7 : checkPotIm ⟨7, by decide⟩ = true :=
  checkPotIm_join wdSl_7 wdDrAll_7
private lemma wdSl_8 : checkSlopeIm wdIm8 = true := rfl
private lemma wdDr_8_0 : checkRange 5 1 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_1 : checkRange 5 33 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_2 : checkRange 5 65 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_3 : checkRange 5 97 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_4 : checkRange 5 129 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_5 : checkRange 5 161 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_6 : checkRange 5 193 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_7 : checkRange 5 225 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_8 : checkRange 5 257 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_9 : checkRange 5 289 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_10 : checkRange 5 321 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_11 : checkRange 5 353 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_12 : checkRange 5 385 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_13 : checkRange 5 417 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_14 : checkRange 5 449 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_15 : checkRange 5 481 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_16 : checkRange 5 513 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_17 : checkRange 5 545 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_18 : checkRange 5 577 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_19 : checkRange 5 609 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_20 : checkRange 5 641 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_21 : checkRange 5 673 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_22 : checkRange 5 705 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_23 : checkRange 5 737 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_24 : checkRange 5 769 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_25 : checkRange 5 801 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_26 : checkRange 5 833 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_27 : checkRange 5 865 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_28 : checkRange 5 897 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_29 : checkRange 5 929 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_30 : checkRange 5 961 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDr_8_31 : checkRange 5 993 (checkDriftAt wdIm8) = true := by conv => lhs; whnf
private lemma wdDrAll_8 : checkRange 10 1 (checkDriftAt wdIm8) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_8_0 wdDr_8_1 (hmid := rfl))
          (
          checkRange_join wdDr_8_2 wdDr_8_3 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_8_4 wdDr_8_5 (hmid := rfl))
          (
          checkRange_join wdDr_8_6 wdDr_8_7 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_8_8 wdDr_8_9 (hmid := rfl))
          (
          checkRange_join wdDr_8_10 wdDr_8_11 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_8_12 wdDr_8_13 (hmid := rfl))
          (
          checkRange_join wdDr_8_14 wdDr_8_15 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_8_16 wdDr_8_17 (hmid := rfl))
          (
          checkRange_join wdDr_8_18 wdDr_8_19 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_8_20 wdDr_8_21 (hmid := rfl))
          (
          checkRange_join wdDr_8_22 wdDr_8_23 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_8_24 wdDr_8_25 (hmid := rfl))
          (
          checkRange_join wdDr_8_26 wdDr_8_27 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_8_28 wdDr_8_29 (hmid := rfl))
          (
          checkRange_join wdDr_8_30 wdDr_8_31 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_8 : checkPotIm ⟨8, by decide⟩ = true :=
  checkPotIm_join wdSl_8 wdDrAll_8
private lemma wdSl_9 : checkSlopeIm wdIm9 = true := rfl
private lemma wdDr_9_0 : checkRange 5 1 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_1 : checkRange 5 33 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_2 : checkRange 5 65 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_3 : checkRange 5 97 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_4 : checkRange 5 129 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_5 : checkRange 5 161 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_6 : checkRange 5 193 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_7 : checkRange 5 225 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_8 : checkRange 5 257 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_9 : checkRange 5 289 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_10 : checkRange 5 321 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_11 : checkRange 5 353 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_12 : checkRange 5 385 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_13 : checkRange 5 417 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_14 : checkRange 5 449 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_15 : checkRange 5 481 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_16 : checkRange 5 513 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_17 : checkRange 5 545 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_18 : checkRange 5 577 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_19 : checkRange 5 609 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_20 : checkRange 5 641 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_21 : checkRange 5 673 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_22 : checkRange 5 705 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_23 : checkRange 5 737 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_24 : checkRange 5 769 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_25 : checkRange 5 801 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_26 : checkRange 5 833 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_27 : checkRange 5 865 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_28 : checkRange 5 897 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_29 : checkRange 5 929 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_30 : checkRange 5 961 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDr_9_31 : checkRange 5 993 (checkDriftAt wdIm9) = true := by conv => lhs; whnf
private lemma wdDrAll_9 : checkRange 10 1 (checkDriftAt wdIm9) = true :=
  checkRange_join
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_9_0 wdDr_9_1 (hmid := rfl))
          (
          checkRange_join wdDr_9_2 wdDr_9_3 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_9_4 wdDr_9_5 (hmid := rfl))
          (
          checkRange_join wdDr_9_6 wdDr_9_7 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_9_8 wdDr_9_9 (hmid := rfl))
          (
          checkRange_join wdDr_9_10 wdDr_9_11 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_9_12 wdDr_9_13 (hmid := rfl))
          (
          checkRange_join wdDr_9_14 wdDr_9_15 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (
    checkRange_join
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_9_16 wdDr_9_17 (hmid := rfl))
          (
          checkRange_join wdDr_9_18 wdDr_9_19 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_9_20 wdDr_9_21 (hmid := rfl))
          (
          checkRange_join wdDr_9_22 wdDr_9_23 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (
      checkRange_join
        (
        checkRange_join
          (
          checkRange_join wdDr_9_24 wdDr_9_25 (hmid := rfl))
          (
          checkRange_join wdDr_9_26 wdDr_9_27 (hmid := rfl))
          (hmid := rfl))
        (
        checkRange_join
          (
          checkRange_join wdDr_9_28 wdDr_9_29 (hmid := rfl))
          (
          checkRange_join wdDr_9_30 wdDr_9_31 (hmid := rfl))
          (hmid := rfl))
        (hmid := rfl))
      (hmid := rfl))
    (hmid := rfl)
lemma checkPotIm_9 : checkPotIm ⟨9, by decide⟩ = true :=
  checkPotIm_join wdSl_9 wdDrAll_9
lemma checkPotIm_all (im : Fin 10) : checkPotIm im = true := by
  fin_cases im
  · exact checkPotIm_0
  · exact checkPotIm_1
  · exact checkPotIm_2
  · exact checkPotIm_3
  · exact checkPotIm_4
  · exact checkPotIm_5
  · exact checkPotIm_6
  · exact checkPotIm_7
  · exact checkPotIm_8
  · exact checkPotIm_9
lemma potWInt_one_ge (im : Fin 10) : 818310000 ≤ potWInt im 1 := by
  have h12 := (Bool.and_eq_true _ _).mp (checkPotIm_all im)
  have h1 := (Bool.and_eq_true _ _).mp h12.1; exact of_decide_eq_true h1.1
lemma checkSlopeRange_true (im : Fin 10) : checkRange 10 0 (checkSlopeStep im) = true := by
  have h12 := (Bool.and_eq_true _ _).mp (checkPotIm_all im)
  exact ((Bool.and_eq_true _ _).mp h12.1).2
lemma checkDriftAt_true (im : Fin 10) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    checkDriftAt im r = true := by
  have h12 := (Bool.and_eq_true _ _).mp (checkPotIm_all im)
  exact checkRange_sound (checkDriftAt im) 10 1 h12.2 r hr1 (by omega)
/- ### Monotonicity, Semi-Concavity, and Falling-Factorial Eigenfunction Soundness -/
lemma checkSlopeStep_true (im : Fin 10) {i : ℕ} (hi : i < 1024) : checkSlopeStep im i = true :=
  checkRange_sound (checkSlopeStep im) 10 0 (checkSlopeRange_true im) i (Nat.zero_le i) (by omega)
lemma potWInt_mono_step (im : Fin 10) {u : ℕ} (hu1 : 1 ≤ u) (hu : u ≤ 1024) :
    potWInt im (u - 1) ≤ potWInt im u := by
  have hstep := checkSlopeStep_true im (i := u - 1) (by omega); unfold checkSlopeStep at hstep
  dsimp only at hstep; have hu_eq : u - 1 + 1 = u := (by omega); rw [hu_eq] at hstep
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hstep).1).1
lemma potWInt_step (im : Fin 10) {u : ℕ} (hu1 : 1 ≤ u) (hu : u ≤ 1024) :
    potWInt im u = potWInt im (u - 1) + slopeWInt im u := by
  have hle := potWInt_mono_step im hu1 hu; unfold slopeWInt; omega
lemma potWInt_le_cubic (im : Fin 10) {u : ℕ} (hu : u ≤ 1024) : potWInt im u + cubicA2 im * (u * (u -
    1)) ≤ potWInt im 1 * u + cubicA3 im * (u * (u - 1) * (u - 2)) := by
  rcases eq_or_ne u 0 with rfl | hne
  · simp [potWInt]
  · have hstep := checkSlopeStep_true im (i := u - 1) (by omega); unfold checkSlopeStep at hstep
    dsimp only at hstep; have hu_eq : u - 1 + 1 = u := (by omega); rw [hu_eq] at hstep
    exact of_decide_eq_true ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hstep).1).2
def adjSlopeZ (im : Fin 10) (u : ℕ) : ℤ :=
  (slopeWInt im u : ℤ) - 2 * (gammaIm im : ℤ) * ((u : ℤ) - 1)
def adjPotZ (im : Fin 10) (u : ℕ) : ℤ :=
  (potWInt im u : ℤ) - (gammaIm im : ℤ) * (u : ℤ) * ((u : ℤ) - 1)
lemma adjPotZ_step (im : Fin 10) {u : ℕ} (hu1 : 1 ≤ u) (hu : u ≤ 1024) :
    adjPotZ im u = adjPotZ im (u - 1) + adjSlopeZ im u := by
  have hstep := potWInt_step im hu1 hu
  have hstepZ : (potWInt im u : ℤ) = (potWInt im (u - 1) : ℤ) + (slopeWInt im u : ℤ) := by
    exact_mod_cast hstep
  have hcast : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := (by omega); unfold adjPotZ adjSlopeZ
  rw [hstepZ, hcast]; ring
lemma adjSlopeZ_antitone (im : Fin 10) {a b : ℕ} (ha1 : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1024) :
    adjSlopeZ im b ≤ adjSlopeZ im a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab; clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep := checkSlopeStep_true im (i := a + d - 1) (by omega); unfold checkSlopeStep at hstep
    dsimp only at hstep; have hu1 : a + d - 1 + 1 = a + d := (by omega)
    have hu2 : a + d - 1 + 2 = a + d + 1 := (by omega); have hlt : a + d < 1024 := (by omega)
    rw [hu1, hu2, ite_eq_left hlt] at hstep
    have hdec : potWInt im (a + d + 1) - potWInt im (a + d) ≤ potWInt im (a + d) - potWInt im (a +
      d - 1) + 2 * gammaIm im := of_decide_eq_true ((Bool.and_eq_true _ _).mp hstep).2
    have hsl1 : slopeWInt im (a + (d + 1)) = potWInt im (a + d + 1) - potWInt im (a + d) := by
      unfold slopeWInt; have h1 : a + (d + 1) = a + d + 1 := (by omega)
      have h2 : a + d + 1 - 1 = a + d := (by omega); rw [h1, h2]
    have hsl0 : slopeWInt im (a + d) = potWInt im (a + d) - potWInt im (a + d - 1) := rfl
    have hdec_sl : slopeWInt im (a + (d + 1)) ≤ slopeWInt im (a + d) + 2 * gammaIm im := by
      rw [hsl1, hsl0]; exact hdec
    have hdecZ : (slopeWInt im (a + (d + 1)) : ℤ) ≤
        (slopeWInt im (a + d) : ℤ) + 2 * (gammaIm im : ℤ) := by
      exact_mod_cast hdec_sl
    have hstep_adj : adjSlopeZ im (a + (d + 1)) ≤ adjSlopeZ im (a + d) := by
      unfold adjSlopeZ; push_cast; linarith
    exact hstep_adj.trans (ih (by omega))
lemma adjPotZ_concave_tangent (im : Fin 10) {u u₀ : ℕ} (hu : u ≤ 1024) (hu0_lo : 1 ≤ u₀) (hu0_hi :
    u₀ ≤ 1024) : adjPotZ im u ≤ adjPotZ im u₀ + adjSlopeZ im u₀ * ((u : ℤ) - (u₀ : ℤ)) := by
  rcases le_total u u₀ with hle | hge
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle; have hu_eq : u = u₀ - d := (by omega); rw [hu_eq]
    have hd_le : d ≤ u₀ := (by omega); clear hle hd hu_eq hu u
    induction d with
    | zero => simp
    | succ d ih =>
      have hstep := adjPotZ_step im (u := u₀ - d) (by omega) (by omega)
      have hsub_eq : u₀ - d - 1 = u₀ - (d + 1) := (by omega); rw [hsub_eq] at hstep
      have hanti := adjSlopeZ_antitone im (a := u₀ - d) (b := u₀) (by omega) (by omega) hu0_hi
      have ih' := ih (by omega)
      have hcast_sub : ((u₀ - (d + 1) : ℕ) : ℤ) = ((u₀ - d : ℕ) : ℤ) - 1 := (by omega)
      rw [hcast_sub]; linarith
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge; clear hge
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← Nat.add_assoc]; have hstep := adjPotZ_step im (u := u₀ + d + 1) (by omega) hu
      have hsub_eq : u₀ + d + 1 - 1 = u₀ + d := (by omega); rw [hsub_eq] at hstep
      have hanti := adjSlopeZ_antitone im (a := u₀) (b := u₀ + d + 1) hu0_lo (by omega) hu
      have ih' := ih (by omega); push_cast at ih' ⊢; linarith
lemma potWInt_semiconcave_tangent (im : Fin 10) {u u₀ : ℕ} (hu : u ≤ 1024) (hu0_lo : 1 ≤ u₀) (hu0_hi
    : u₀ ≤ 1024) : (potWInt im u : ℤ) ≤ ((potWInt im u₀ : ℤ) - (slopeWInt im u₀ : ℤ) * (u₀ : ℤ) +
    (gammaIm im : ℤ) * (u₀ : ℤ) * ((u₀ : ℤ) - 1)) + ((slopeWInt im u₀ : ℤ) - 2 * (gammaIm im : ℤ) *
    ((u₀ : ℤ) - 1)) * (u : ℤ) + (gammaIm im : ℤ) * ((u : ℤ) * ((u : ℤ) - 1)) := by
  have h := adjPotZ_concave_tangent im hu hu0_lo hu0_hi; unfold adjPotZ adjSlopeZ at h; linarith
noncomputable def stepExact (p : ℝ) (r : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  f d + ((r - d : ℝ) / r) * p * (f (d + 1) - f d)
lemma stepExact_mono_on {p : ℝ} {r : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g₁ g₂ : ℕ → ℝ} (hg : ∀ d ≤ r,
    g₁ d ≤ g₂ d) : ∀ d ≤ r, stepExact p r g₁ d ≤ stepExact p r g₂ d := by
  intro d hd; unfold stepExact; rcases eq_or_lt_of_le hd with rfl | hlt
  · simp [hg d le_rfl]
  · have hr_pos : (0 : ℝ) < r := (by exact_mod_cast (Nat.zero_lt_of_lt hlt))
    have hd_le : (d : ℝ) ≤ r := (by exact_mod_cast hd)
    have hq0 : 0 ≤ ((r - d : ℝ) / r) * p := mul_nonneg (div_nonneg (by linarith) hr_pos.le) hp0
    have hdiv1 : (r - d : ℝ) / r ≤ 1 := (div_le_one hr_pos).2 (by linarith)
    have hq1 : ((r - d : ℝ) / r) * p ≤ 1 :=
      (mul_le_mul_of_nonneg_left hp1 (div_nonneg (by linarith) hr_pos.le)).trans (by linarith)
    have hd0 := hg d hd; have hd1 := hg (d + 1) hlt; nlinarith
lemma stepExact_iter_mono_on {p : ℝ} {r : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g₁ g₂ : ℕ → ℝ} (hg : ∀ d ≤
    r, g₁ d ≤ g₂ d) (b : ℕ) : ∀ d ≤ r, (stepExact p r)^[b] g₁ d ≤ (stepExact p r)^[b] g₂ d := by
  induction b with
  | zero => exact hg
  | succ b ih =>
    intro d hd
    have h1 : (stepExact p r)^[b + 1] g₁ d = stepExact p r ((stepExact p r)^[b] g₁) d :=
      congr_fun (Function.iterate_succ_apply' (stepExact p r) b g₁) d
    have h2 : (stepExact p r)^[b + 1] g₂ d = stepExact p r ((stepExact p r)^[b] g₂) d :=
      congr_fun (Function.iterate_succ_apply' (stepExact p r) b g₂) d
    rw [h1, h2]; exact stepExact_mono_on hp0 hp1 ih d hd
lemma stepExact_antitone_on {p : ℝ} {r : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g : ℕ → ℝ} (hg : ∀ d < r, g
    (d + 1) ≤ g d) : ∀ d < r, stepExact p r g (d + 1) ≤ stepExact p r g d := by
  intro d hd; have hr_pos : (0 : ℝ) < r := (by exact_mod_cast (Nat.zero_lt_of_lt hd))
  have hd1 := hg d hd; rcases eq_or_lt_of_le (show d + 1 ≤ r by omega) with heq | hlt2
  · unfold stepExact; have hsub0 : (r : ℝ) - ((d + 1 : ℕ) : ℝ) = 0 := (by rw [heq]; ring)
    have hd_le : (d : ℝ) ≤ r := (by exact_mod_cast hd.le)
    have hdiv1 : (r - d : ℝ) / r ≤ 1 := (div_le_one hr_pos).2 (by linarith)
    have hq1 : ((r - d : ℝ) / r) * p ≤ 1 :=
      (mul_le_mul_of_nonneg_left hp1 (div_nonneg (by linarith) hr_pos.le)).trans (by linarith)
    rw [hsub0, zero_div, zero_mul, zero_mul, add_zero]; nlinarith
  · have hd2 := hg (d + 1) hlt2; have hd1_le : ((d + 1 : ℕ) : ℝ) ≤ r := (by exact_mod_cast hlt2.le)
    have hdiv1 : (r - d : ℝ) / r ≤ 1 := (div_le_one hr_pos).2 (by push_cast at hd1_le; linarith)
    have hq1 : ((r - d : ℝ) / r) * p ≤ 1 :=
      (mul_le_mul_of_nonneg_left hp1
        (div_nonneg (by push_cast at hd1_le; linarith) hr_pos.le)).trans (by linarith)
    have hq2 : 0 ≤ ((r - (d + 1 : ℕ) : ℝ) / r) * p :=
      mul_nonneg (div_nonneg (by linarith) hr_pos.le) hp0
    unfold stepExact; nlinarith
lemma stage2CouponStepUpper_iter_eq_stepExact_iter_on (p_lo p_hi : ℝ) (r : ℕ) (hp0 : 0 ≤ p_lo) (hp1
    : p_lo ≤ 1) {g : ℕ → ℝ} (hg : ∀ d < r, g (d + 1) ≤ g d) (b : ℕ) : (∀ d ≤ r,
    (stage2CouponStepUpper p_lo p_hi r)^[b] g d = (stepExact p_lo r)^[b] g d) ∧ (∀ d < r, (stepExact
    p_lo r)^[b] g (d + 1) ≤ (stepExact p_lo r)^[b] g d) := by
  induction b with
  | zero => exact ⟨fun _ _ ↦ rfl, hg⟩
  | succ b ih =>
    rcases ih with ⟨heq, hanti⟩; refine ⟨fun d hd ↦ ?_, fun d hd ↦ ?_⟩
    · set F := (stage2CouponStepUpper p_lo p_hi r)^[b] g; set G := (stepExact p_lo r)^[b] g
      have h1 : (stage2CouponStepUpper p_lo p_hi r)^[b + 1] g d = stage2CouponStepUpper p_lo p_hi r
        F d := congr_fun (Function.iterate_succ_apply' (stage2CouponStepUpper p_lo p_hi r) b g) d
      have h2 : (stepExact p_lo r)^[b + 1] g d = stepExact p_lo r G d := congr_fun
        (Function.iterate_succ_apply' (stepExact p_lo r) b g) d
      rw [h1, h2]; unfold stage2CouponStepUpper stepExact; rcases eq_or_lt_of_le hd with rfl | hlt
      · have hFG : F d = G d := heq d le_rfl; rw [hFG]; ring
      · have hFGd : F d = G d := heq d hd
        have hFGd1 : F (d + 1) = G (d + 1) := heq (d + 1) (by omega)
        have hle_step : G (d + 1) ≤ G d := hanti d hlt; rw [hFGd, hFGd1, ite_eq_left hle_step]
    · have h2d : (stepExact p_lo r)^[b + 1] g d = stepExact p_lo r ((stepExact p_lo r)^[b] g) d :=
        congr_fun (Function.iterate_succ_apply' (stepExact p_lo r) b g) d
      have h2d1 : (stepExact p_lo r)^[b + 1] g (d + 1) = stepExact p_lo r ((stepExact p_lo r)^[b] g)
        (d + 1) := congr_fun (Function.iterate_succ_apply' (stepExact p_lo r) b g) (d + 1)
      rw [h2d, h2d1]; exact stepExact_antitone_on hp0 hp1 hanti d hd
def gPoly3 (c₀ c₁ c₂ c₃ : ℝ) (r d : ℕ) : ℝ :=
  let u : ℝ := (r : ℝ) - (d : ℝ)
  c₀ + c₁ * u + c₂ * (u * (u - 1)) + c₃ * (u * (u - 1) * (u - 2))
lemma stepExact_gPoly3 {p c₀ c₁ c₂ c₃ : ℝ} {r : ℕ} (hr : 1 ≤ r) : stepExact p r (gPoly3 c₀ c₁ c₂ c₃
    r) = gPoly3 c₀ (c₁ * (1 - p / (r : ℝ))) (c₂ * (1 - 2 * p / (r : ℝ))) (c₃ * (1 - 3 * p / (r :
    ℝ))) r := by
  have hr_pos : (0 : ℝ) < r := (by exact_mod_cast hr); have hr_ne : (r : ℝ) ≠ 0 := hr_pos.ne'
  funext d; unfold stepExact gPoly3; dsimp only; push_cast; field_simp [hr_ne]; ring
lemma stepExact_iter_gPoly3 {p c₀ c₁ c₂ c₃ : ℝ} {r : ℕ} (hr : 1 ≤ r) (b : ℕ) : (stepExact p r)^[b]
    (gPoly3 c₀ c₁ c₂ c₃ r) = gPoly3 c₀ (c₁ * (1 - p / (r : ℝ)) ^ b) (c₂ * (1 - 2 * p / (r : ℝ)) ^ b)
    (c₃ * (1 - 3 * p / (r : ℝ)) ^ b) r := by
  induction b generalizing c₁ c₂ c₃ with
  | zero => funext d; simp [gPoly3]
  | succ b ih =>
    rw [Function.iterate_succ_apply, stepExact_gPoly3 hr, ih]; funext d; unfold gPoly3; dsimp only
    ring
lemma iter_upper_le_gPoly3 (p_lo p_hi : ℝ) {c₀ c₁ c₂ c₃ : ℝ} {r : ℕ} (hr : 1 ≤ r) (hp0 : 0 ≤ p_lo)
    (hp1 : p_lo ≤ 1) {f : ℕ → ℝ} (hanti : ∀ d < r, f (d + 1) ≤ f d) (hf_le : ∀ d ≤ r, f d ≤ gPoly3
    c₀ c₁ c₂ c₃ r d) (b : ℕ) : (stage2CouponStepUpper p_lo p_hi r)^[b] f 0 ≤ c₀ + c₁ * (r : ℝ) *
    (1 - p_lo / (r : ℝ)) ^ b + c₂ * ((r : ℝ) * ((r : ℝ) - 1)) * (1 - 2 * p_lo / (r : ℝ)) ^ b + c₃ *
    ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2)) * (1 - 3 * p_lo / (r : ℝ)) ^ b := by
  have heq := (stage2CouponStepUpper_iter_eq_stepExact_iter_on p_lo p_hi r hp0 hp1 hanti b).1 0
    (Nat.zero_le r)
  rw [heq]; have hm := stepExact_iter_mono_on hp0 hp1 hf_le b 0 (Nat.zero_le r)
  rw [stepExact_iter_gPoly3 hr b] at hm; refine hm.trans (le_of_eq ?_)
  unfold gPoly3; dsimp only; rw [Nat.cast_zero, sub_zero]; ring
lemma nat_cast_fall2 (u : ℕ) : ((u * (u - 1) : ℕ) : ℝ) = (u : ℝ) * ((u : ℝ) - 1) := by
  rcases u with _ | u
  · simp
  · push_cast; ring
lemma nat_cast_fall3 (u : ℕ) :
    ((u * (u - 1) * (u - 2) : ℕ) : ℝ) = (u : ℝ) * ((u : ℝ) - 1) * ((u : ℝ) - 2) := by
  rcases u with _ | _ | u
  · simp
  · simp
  · push_cast; ring
lemma nat_le_ceilDiv_mul (a d : ℕ) (hd : 0 < d) : a ≤ d * (((d - 1) + a) / d) := by
  have hmod := Nat.div_add_mod ((d - 1) + a) d; have hlt := Nat.mod_lt ((d - 1) + a) hd; omega
lemma pow2Ceil_bound (t : ℕ) : ∀ {x : ℝ} (_hx0 : 0 ≤ x) (q : ℕ), x ≤ (q : ℝ) / (M_scale : ℝ) → x ^
    (2 ^ t) ≤ (pow2Ceil t q : ℝ) / (M_scale : ℝ) := by
  induction t with
  | zero => intro x _ q hq; change x ^ 1 ≤ (q : ℝ) / (M_scale : ℝ); rwa [pow_one]
  | succ t ih =>
    intro x hx0 q hq; have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
    set q' := ((M_scale - 1) + q * q) / M_scale
    have hsq : x ^ 2 ≤ (q' : ℝ) / (M_scale : ℝ) := by
      have h1 : x ^ 2 ≤ ((q : ℝ) / (M_scale : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 hq 2
      refine h1.trans ?_
      have hceil : (q : ℝ) * (q : ℝ) ≤ (M_scale : ℝ) * (q' : ℝ) := by
        have hc := Nat.cast_le (α := ℝ).mpr
          (nat_le_ceilDiv_mul (q * q) M_scale (by unfold M_scale; norm_num))
        rwa [Nat.cast_mul, Nat.cast_mul] at hc
      rw [sq, div_mul_div_comm, ← mul_div_mul_left (q' : ℝ) (M_scale : ℝ) hM_pos.ne']
      exact div_le_div_of_nonneg_right hceil (mul_nonneg hM_pos.le hM_pos.le)
    have hrec := ih (sq_nonneg x) q' hsq
    have hpow : (x ^ 2) ^ (2 ^ t) = x ^ (2 ^ (t + 1)) := by
      rw [← pow_mul, mul_comm 2 (2 ^ t), ← Nat.pow_succ]
    have hdef : pow2Ceil (t + 1) q = pow2Ceil t q' := rfl; rw [← hpow, hdef]; exact hrec
lemma pow2Floor_bound (t : ℕ) : ∀ {x : ℝ} (q : ℕ), (q : ℝ) / (M_scale : ℝ) ≤ x → (pow2Floor t q : ℝ)
    / (M_scale : ℝ) ≤ x ^ (2 ^ t) := by
  induction t with
  | zero => intro x q hq; change (q : ℝ) / (M_scale : ℝ) ≤ x ^ 1; rwa [pow_one]
  | succ t ih =>
    intro x q hq; have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
    have hq0 : 0 ≤ (q : ℝ) / (M_scale : ℝ) := div_nonneg (Nat.cast_nonneg q) hM_pos.le
    set q' := (q * q) / M_scale
    have hsq : (q' : ℝ) / (M_scale : ℝ) ≤ x ^ 2 := by
      have h1 : ((q : ℝ) / (M_scale : ℝ)) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hq0 hq 2
      refine (?_ : (q' : ℝ) / (M_scale : ℝ) ≤ ((q : ℝ) / (M_scale : ℝ)) ^ 2).trans h1
      have hfl : (M_scale : ℝ) * (q' : ℝ) ≤ (q : ℝ) * (q : ℝ) := by
        have hc := Nat.cast_le (α := ℝ).mpr (Nat.mul_div_le (q * q) M_scale)
        rwa [Nat.cast_mul, Nat.cast_mul] at hc
      rw [sq, div_mul_div_comm, ← mul_div_mul_left (q' : ℝ) (M_scale : ℝ) hM_pos.ne']
      exact div_le_div_of_nonneg_right hfl (mul_nonneg hM_pos.le hM_pos.le)
    have hrec := ih q' hsq
    have hpow : (x ^ 2) ^ (2 ^ t) = x ^ (2 ^ (t + 1)) := by
      rw [← pow_mul, mul_comm 2 (2 ^ t), ← Nat.pow_succ]
    have hdef : pow2Floor (t + 1) q = pow2Floor t q' := rfl; rw [← hpow, hdef]; exact hrec
lemma sinSqLo_le (idx : Fin 44) : sinSqLo idx ≤ 10000000000000000 := by
  fin_cases idx <;> exact Nat.le_of_ble_eq_true rfl
lemma varPhi_p_lo_le_one (idx : Fin 44) : varPhiSinLo idx ^ 2 ≤ 1 := by
  have h := sinSqLo_le idx; have hc : (sinSqLo idx : ℝ) ≤ 10000000000000000 := (by exact_mod_cast h)
  have hsin_eq : varPhiSinLo idx ^ 2 = (sinSqLo idx : ℝ) / 10000000000000000 := by
    unfold varPhiSinLo sinSqLo; push_cast; ring
  rw [hsin_eq]; linarith
lemma qj_bounds {j : ℕ} (idx : Fin 44) {r : ℕ} (hr : 1 ≤ r) (hj : j * sinSqLo idx ≤
    10000000000000000 * r) : 0 ≤ 1 - (j : ℝ) * (varPhiSinLo idx ^ 2) / (r : ℝ) ∧ (qjFloor j idx r :
    ℝ) / (M_scale : ℝ) ≤ 1 - (j : ℝ) * (varPhiSinLo idx ^ 2) / (r : ℝ) ∧ 1 - (j : ℝ) * (varPhiSinLo
    idx ^ 2) / (r : ℝ) ≤ (qjCeil j idx r : ℝ) / (M_scale : ℝ) := by
  have hr_pos : (0 : ℝ) < r := (by exact_mod_cast hr)
  have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
  set den : ℕ := 10000000000000000 * r; have hden_pos : 0 < den := (by dsimp only [den]; omega)
  have hdenR : (0 : ℝ) < den := (by exact_mod_cast hden_pos)
  have hden_eq : (den : ℝ) = 10000000000000000 * (r : ℝ) := by
    dsimp only [den]; rw [Nat.cast_mul]; norm_num
  have hsin_eq : varPhiSinLo idx ^ 2 = (sinSqLo idx : ℝ) / 10000000000000000 := by
    unfold varPhiSinLo sinSqLo; push_cast; ring
  have hp_div : ((j * sinSqLo idx : ℕ) : ℝ) / (den : ℝ) =
      (j : ℝ) * (varPhiSinLo idx ^ 2) / (r : ℝ) := by
    rw [Nat.cast_mul, hsin_eq, hden_eq]; field_simp [hr_pos.ne']
  have hjR : ((j * sinSqLo idx : ℕ) : ℝ) ≤ (den : ℝ) := (by exact_mod_cast hj)
  have hnn : 0 ≤ 1 - (j : ℝ) * (varPhiSinLo idx ^ 2) / (r : ℝ) := by
    rw [← hp_div, sub_nonneg, div_le_one hdenR]; exact hjR
  have hfl : (den : ℝ) * (qjFloor j idx r : ℝ) ≤
      (M_scale : ℝ) * ((den : ℝ) - ((j * sinSqLo idx : ℕ) : ℝ)) := by
    have hc := Nat.cast_le (α := ℝ).mpr (Nat.mul_div_le (M_scale * (den - j * sinSqLo idx)) den)
    push_cast at hc; rw [Nat.cast_sub hj] at hc; exact hc
  have hceil : (M_scale : ℝ) * ((den : ℝ) - ((j * sinSqLo idx : ℕ) : ℝ)) ≤
      (den : ℝ) * (qjCeil j idx r : ℝ) := by
    have hc := Nat.cast_le (α := ℝ).mpr
      (nat_le_ceilDiv_mul (M_scale * (den - j * sinSqLo idx)) den hden_pos)
    push_cast at hc; rw [Nat.cast_sub hj] at hc; exact hc
  refine ⟨hnn, ?_, ?_⟩
  · rw [← hp_div, one_sub_div hdenR.ne', div_le_div_iff₀ hM_pos hdenR]; linarith
  · rw [← hp_div, one_sub_div hdenR.ne', div_le_div_iff₀ hdenR hM_pos]; linarith
lemma forceCons_eq (x : ℕ) (xs : List ℕ) : forceCons x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
lemma stepWithQs_nil_iter (qs : List ℕ) :
    ∀ (b : ℕ), (fun l ↦ stepWithQs l qs)^[b] [] = []
  | 0 => rfl
  | b + 1 => by rw [Function.iterate_succ_apply]; exact stepWithQs_nil_iter qs b
lemma iterStepWithQs_eq (qs : List ℕ) :
    ∀ (b : ℕ) (vs : List ℕ), iterStepWithQs qs b vs = (fun l ↦ stepWithQs l qs)^[b] vs
  | 0, _ => rfl
  | b + 1, vs => by
    simp only [iterStepWithQs, Function.iterate_succ_apply]
    cases stepWithQs vs qs with
    | nil => exact (stepWithQs_nil_iter qs b).symm
    | cons x xs => exact iterStepWithQs_eq qs b (x :: xs)
lemma stepWithQs_ofFnFrom (idx : Fin 44) (r : ℕ) (F : ℕ → ℕ) :
    ∀ (k m d₀ : ℕ),
      stepWithQs (ofFnFrom F d₀ (k + 2)) (qListFrom idx r d₀ (m + k + 1)) =
        ofFnFrom (stepIntUpper idx r F) d₀ (k + 1)
  | 0, _, d₀ => forceCons_eq (stepIntUpper idx r F d₀) []
  | k + 1, m, d₀ =>
    (forceCons_eq _ _).trans
      (congrArg (stepIntUpper idx r F d₀ :: ·) (stepWithQs_ofFnFrom idx r F k m (d₀ + 1)))
lemma stepWithQs_iter_ofFnFrom (idx : Fin 44) (r : ℕ) (qs : List ℕ) :
    ∀ (b k m : ℕ) (F : ℕ → ℕ),
      qs = qListFrom idx r 0 (m + k + b) →
      (fun l ↦ stepWithQs l qs)^[b] (ofFnFrom F 0 (k + b + 1)) =
        ofFnFrom ((stepIntUpper idx r)^[b] F) 0 (k + 1)
  | 0, _, _, _, _ => rfl
  | b + 1, k, m, F, hqs => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hstep : stepWithQs (ofFnFrom F 0 (k + (b + 1) + 1)) qs =
        ofFnFrom (stepIntUpper idx r F) 0 (k + b + 1) := by
      rw [hqs, show m + k + (b + 1) = m + (k + b) + 1 by omega,
        show k + (b + 1) + 1 = (k + b) + 2 by omega]
      exact stepWithQs_ofFnFrom idx r F (k + b) m 0
    rw [hstep]; exact stepWithQs_iter_ofFnFrom idx r qs b k (m + 1) (stepIntUpper idx r F)
      (by rw [hqs]; congr 1; omega)
lemma stepExact_le_stepIntUpper (idx : Fin 44) {r : ℕ} (hr : 1 ≤ r) {g : ℕ → ℝ} (hg_anti : ∀ d < r,
    g (d + 1) ≤ g d) {F : ℕ → ℕ} (hF : ∀ d ≤ r, g d ≤ (F d : ℝ) / (M_scale : ℝ)) : ∀ d ≤ r,
    stepExact (varPhiSinLo idx ^ 2) r g d ≤ (stepIntUpper idx r F d : ℝ) / (M_scale : ℝ) := by
  intro d hd; have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
  have hr_pos : (0 : ℝ) < r := (by exact_mod_cast hr); set p_lo : ℝ := varPhiSinLo idx ^ 2
  have hp0 : 0 ≤ p_lo := sq_nonneg _; have hp1 : p_lo ≤ 1 := varPhi_p_lo_le_one idx; set v0 := F d
  set v1 := F (d + 1); set q := qjCeil (r - d) idx r; change stepExact p_lo r g d ≤
    ((v1 + ((M_scale - 1) + q * (v0 - v1)) / M_scale : ℕ) : ℝ) / (M_scale : ℝ)
  rcases le_total v1 v0 with hv | hv
  · have hmono := stepExact_mono_on hp0 hp1 hF d hd; refine hmono.trans ?_
    have hj : (r - d) * sinSqLo idx ≤ 10000000000000000 * r := by
      calc (r - d) * sinSqLo idx ≤ r * 10000000000000000 :=
            Nat.mul_le_mul (Nat.sub_le r d) (sinSqLo_le idx)
        _ = 10000000000000000 * r := Nat.mul_comm _ _
    obtain ⟨_, _, hq_cl⟩ := qj_bounds (j := r - d) idx hr hj
    have hstep_eq : stepExact p_lo r (fun i ↦ (F i : ℝ) / (M_scale : ℝ)) d = ((v1 : ℝ) + (1 - ((r -
      d : ℕ) : ℝ) * p_lo / (r : ℝ)) * ((v0 - v1 : ℕ) : ℝ)) / (M_scale : ℝ) := by
      unfold stepExact
      change (v0 : ℝ) / (M_scale : ℝ) + ((r : ℝ) - (d : ℝ)) / (r : ℝ) * p_lo * ((v1 : ℝ) / (M_scale
        : ℝ) - (v0 : ℝ) / (M_scale : ℝ)) = _
      rw [Nat.cast_sub hd, Nat.cast_sub hv]; field_simp [hr_pos.ne', hM_pos.ne']; ring
    rw [hstep_eq]; refine div_le_div_of_nonneg_right ?_ hM_pos.le
    have hmul : (1 - ((r - d : ℕ) : ℝ) * p_lo / (r : ℝ)) * ((v0 - v1 : ℕ) : ℝ) ≤ ((q : ℝ) / (M_scale
      : ℝ)) * ((v0 - v1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hq_cl (Nat.cast_nonneg _)
    have hceil : (q : ℝ) * ((v0 - v1 : ℕ) : ℝ) ≤
        (M_scale : ℝ) * (((M_scale - 1) + q * (v0 - v1)) / M_scale : ℕ) := by
      have hc := Nat.cast_le (α := ℝ).mpr
        (nat_le_ceilDiv_mul (q * (v0 - v1)) M_scale (by unfold M_scale; norm_num))
      rwa [Nat.cast_mul, Nat.cast_mul] at hc
    have hceil_div : ((q : ℝ) / (M_scale : ℝ)) * ((v0 - v1 : ℕ) : ℝ) ≤
        (((M_scale - 1) + q * (v0 - v1)) / M_scale : ℕ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hM_pos]; linarith
    rw [Nat.cast_add]; linarith
  · have hg_le_v0 : stepExact p_lo r g d ≤ (v0 : ℝ) / (M_scale : ℝ) := by
      rcases eq_or_lt_of_le hd with rfl | hlt
      · unfold stepExact; simpa using hF d le_rfl
      · unfold stepExact; have hd_le : (d : ℝ) ≤ r := (by exact_mod_cast hd)
        have hcoeff : 0 ≤ ((r - d : ℝ) / r) * p_lo :=
          mul_nonneg (div_nonneg (by linarith) hr_pos.le) hp0
        have hdiff : g (d + 1) - g d ≤ 0 := sub_nonpos.mpr (hg_anti d hlt)
        have hterm : ((r - d : ℝ) / r) * p_lo * (g (d + 1) - g d) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hcoeff hdiff
        linarith [hF d hd]
    refine hg_le_v0.trans ?_
    refine div_le_div_of_nonneg_right ?_ hM_pos.le
    exact_mod_cast hv.trans (Nat.le_add_right v1 _)
lemma stepExact_iter_le_stepIntUpper_iter (idx : Fin 44) {r : ℕ} (hr : 1 ≤ r) {f : ℕ → ℝ} (hf_anti :
    ∀ d < r, f (d + 1) ≤ f d) {F : ℕ → ℕ} (hF : ∀ d ≤ r, f d ≤ (F d : ℝ) / (M_scale : ℝ)) (b : ℕ) :
    ∀ d ≤ r, (stepExact (varPhiSinLo idx ^ 2) r)^[b] f d ≤ ((stepIntUpper idx r)^[b] F d : ℝ) /
    (M_scale : ℝ) := by
  induction b with
  | zero => exact hF
  | succ b ih =>
    intro d hd; set p_lo : ℝ := varPhiSinLo idx ^ 2
    have h1 : (stepExact p_lo r)^[b + 1] f d = stepExact p_lo r ((stepExact p_lo r)^[b] f) d :=
      congr_fun (Function.iterate_succ_apply' (stepExact p_lo r) b f) d
    have h2 : (stepIntUpper idx r)^[b + 1] F d = stepIntUpper idx r ((stepIntUpper idx r)^[b] F) d
      := congr_fun (Function.iterate_succ_apply' (stepIntUpper idx r) b F) d
    rw [h1, h2]
    have hanti_b := (stage2CouponStepUpper_iter_eq_stepExact_iter_on p_lo p_lo r (sq_nonneg _)
      (varPhi_p_lo_le_one idx) hf_anti b).2
    exact stepExact_le_stepIntUpper idx hr hanti_b ih d hd
lemma invSqrtLo_bound {x : ℕ} (hx1 : 1 ≤ x) (hx : x ≤ 1024) :
    (invSqrtLo x : ℝ) / (M_scale : ℝ) ≤ 1 / √(x : ℝ) := by
  have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
  have hnat : x * (invSqrtLo x) ^ 2 ≤ M_scale ^ 2 := by
    have hb := checkRange_sound _ 10 1 checkInvSqrtLo_all x hx1 (by omega)
    exact of_decide_eq_true hb
  have hsqR : (x : ℝ) * (invSqrtLo x : ℝ) ^ 2 ≤ (M_scale : ℝ) ^ 2 := by
    have hc := Nat.cast_le (α := ℝ).mpr hnat; rwa [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at hc
  have hx_pos : (0 : ℝ) < x := (by exact_mod_cast hx1)
  have hdiv : ((invSqrtLo x : ℝ) / (M_scale : ℝ)) ^ 2 ≤ 1 / (x : ℝ) := by
    rw [div_pow, div_le_div_iff₀ (pow_pos hM_pos 2) hx_pos]; linarith
  have hrt := Real.sqrt_le_sqrt hdiv
  rwa [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) hM_pos.le),
    one_div, Real.sqrt_inv, ← one_div] at hrt
lemma drift_mode0 (im : Fin 10) (idx : Fin 44) {r b sc qt1_hi qt1_lo qt2_hi u₀ : ℕ} {p_lo p_hi : ℝ}
    {f : ℕ → ℝ} (hr1 : 1 ≤ r) (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024) (hu1 : 1 ≤ u₀) (hur : u₀ ≤ r)
    (hp_lo_nn : 0 ≤ p_lo) (hp_lo_le1 : p_lo ≤ 1) (hf_eq : ∀ d, f d = (potWInt im (r - d) : ℝ) /
    (M_scale : ℝ)) (hf_anti : ∀ d < r, f (d + 1) ≤ f d) (hsc_le : varPhiCHi idx * √((b : ℝ) / r) ≤
    (sc : ℝ) / (M_scale : ℝ)) (hpow1_hi : (1 - p_lo / (r : ℝ)) ^ b ≤ (qt1_hi : ℝ) / (M_scale : ℝ))
    (hpow1_lo : (qt1_lo : ℝ) / (M_scale : ℝ) ≤ (1 - p_lo / (r : ℝ)) ^ b) (hpow2_hi : (1 - 2 * p_lo /
    (r : ℝ)) ^ b ≤ (qt2_hi : ℝ) / (M_scale : ℝ)) (hdr_nat : M_scale * sc + M_scale * potWInt im u₀ +
    slopeWInt im u₀ * (r * qt1_hi) + gammaIm im * (r * (r - 1) * qt2_hi + u₀ * (u₀ - 1) * M_scale) ≤
    M_scale * potWInt im r + slopeWInt im u₀ * (M_scale * u₀) + 2 * gammaIm im * (u₀ - 1) * r *
    qt1_lo) : varPhiCHi idx * √((b : ℝ) / r) + (stage2CouponStepUpper p_lo p_hi r)^[b] f 0 ≤ f
    0 := by
  have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
  have hr2_nn : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) := by
    have : (2 : ℝ) ≤ r := (by exact_mod_cast hr2); nlinarith
  have hu0_ge0 : 0 ≤ (u₀ : ℝ) - 1 := (by have : (1 : ℝ) ≤ u₀ := (by exact_mod_cast hu1); linarith)
  set Wu₀ := potWInt im u₀; set wu₀ := slopeWInt im u₀; set Wr := potWInt im r; set γ := gammaIm im
  change M_scale * sc + M_scale * Wu₀ + wu₀ * (r * qt1_hi) + γ * (r * (r - 1) * qt2_hi + u₀ * (u₀ -
    1) * M_scale) ≤ M_scale * Wr + wu₀ * (M_scale * u₀) + 2 * γ * (u₀ - 1) * r * qt1_lo at hdr_nat
  set c₀ : ℝ := ((Wu₀ : ℝ) - (wu₀ : ℝ) * (u₀ : ℝ) +
    (γ : ℝ) * (u₀ : ℝ) * ((u₀ : ℝ) - 1)) / (M_scale : ℝ)
  set c₁ : ℝ := ((wu₀ : ℝ) - 2 * (γ : ℝ) * ((u₀ : ℝ) - 1)) / (M_scale : ℝ)
  set c₂ : ℝ := (γ : ℝ) / (M_scale : ℝ)
  have hf_le : ∀ d ≤ r, f d ≤ gPoly3 c₀ c₁ c₂ 0 r d := by
    intro d hd; rw [hf_eq d]; have hscZ := potWInt_semiconcave_tangent im (u := r - d) (u₀ := u₀)
      (by omega) hu1 (hur.trans hr_hi)
    have hscR := Int.cast_le (R := ℝ).mpr hscZ; push_cast at hscR; rw [Nat.cast_sub hd] at hscR
    unfold gPoly3; dsimp only [c₀, c₁, c₂]; unfold M_scale; push_cast; linarith
  have hiter := iter_upper_le_gPoly3 p_lo p_hi hr1 hp_lo_nn hp_lo_le1 hf_anti hf_le b
  have hp1_hi := (le_div_iff₀ hM_pos).mp hpow1_hi; have hp1_lo := (div_le_iff₀ hM_pos).mp hpow1_lo
  have hp2_hi := (le_div_iff₀ hM_pos).mp hpow2_hi
  have h1 : (wu₀ : ℝ) * (r : ℝ) * ((1 - p_lo / (r : ℝ)) ^ b * (M_scale : ℝ)) ≤ (wu₀ : ℝ) * (r : ℝ) *
    (qt1_hi : ℝ) := mul_le_mul_of_nonneg_left hp1_hi (by positivity)
  have h2 : (2 * (γ : ℝ) * ((u₀ : ℝ) - 1) * (r : ℝ)) * (qt1_lo : ℝ) ≤ (2 * (γ : ℝ) * ((u₀ : ℝ) -
    1) * (r : ℝ)) * ((1 - p_lo / (r : ℝ)) ^ b * (M_scale : ℝ)) := mul_le_mul_of_nonneg_left hp1_lo
    (by positivity)
  have h3 : (γ : ℝ) * ((r : ℝ) * ((r : ℝ) - 1)) * ((1 - 2 * p_lo / (r : ℝ)) ^ b * (M_scale : ℝ)) ≤
    (γ : ℝ) * ((r : ℝ) * ((r : ℝ) - 1)) * (qt2_hi : ℝ) := mul_le_mul_of_nonneg_left hp2_hi
    (mul_nonneg (by positivity) hr2_nn)
  have hdrR := Nat.cast_le (α := ℝ).mpr hdr_nat; push_cast at hdrR
  rw [Nat.cast_sub hr1, Nat.cast_sub hu1] at hdrR
  have hf0 : f 0 = (Wr : ℝ) / (M_scale : ℝ) := (by simpa using hf_eq 0); rw [hf0]
  have hcomb : (sc : ℝ) / (M_scale : ℝ) + (c₀ + c₁ * (r : ℝ) * (1 - p_lo / (r : ℝ)) ^ b + c₂ * ((r :
    ℝ) * ((r : ℝ) - 1)) * (1 - 2 * p_lo / (r : ℝ)) ^ b + 0 * ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) -
    2)) * (1 - 3 * p_lo / (r : ℝ)) ^ b) ≤ (Wr : ℝ) / (M_scale : ℝ) := by
    dsimp only [c₀, c₁, c₂]; unfold M_scale at h1 h2 h3 hdrR ⊢; push_cast at h1 h2 h3 hdrR ⊢
    linarith
  exact (add_le_add hsc_le hiter).trans hcomb
lemma drift_mode1 (im : Fin 10) (idx : Fin 44) {r b sc qt1_hi qt2_lo qt3_hi : ℕ} {p_lo p_hi : ℝ} {f
    : ℕ → ℝ} (hr1 : 1 ≤ r) (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024) (hp_lo_nn : 0 ≤ p_lo) (hp_lo_le1 : p_lo
    ≤ 1) (hf_eq : ∀ d, f d = (potWInt im (r - d) : ℝ) / (M_scale : ℝ)) (hf_anti : ∀ d < r, f (d + 1)
    ≤ f d) (hsc_le : varPhiCHi idx * √((b : ℝ) / r) ≤ (sc : ℝ) / (M_scale : ℝ)) (hpow1_hi : (1 -
    p_lo / (r : ℝ)) ^ b ≤ (qt1_hi : ℝ) / (M_scale : ℝ)) (hpow2_lo : (qt2_lo : ℝ) / (M_scale : ℝ) ≤
    (1 - 2 * p_lo / (r : ℝ)) ^ b) (hpow3_hi : (1 - 3 * p_lo / (r : ℝ)) ^ b ≤ (qt3_hi : ℝ) / (M_scale
    : ℝ)) (hdr_nat : M_scale * sc + potWInt im 1 * r * qt1_hi + cubicA3 im * (r * (r - 1) * (r -
    2)) * qt3_hi ≤ M_scale * potWInt im r + cubicA2 im * (r * (r - 1)) * qt2_lo) : varPhiCHi idx *
    √((b : ℝ) / r) + (stage2CouponStepUpper p_lo p_hi r)^[b] f 0 ≤ f 0 := by
  have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
  have hr2_nn : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) := by
    have : (2 : ℝ) ≤ r := (by exact_mod_cast hr2); nlinarith
  have hr3_nn : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) := by
    have : (2 : ℝ) ≤ r := (by exact_mod_cast hr2); exact mul_nonneg hr2_nn (by linarith)
  set Wr := potWInt im r; set w1 := potWInt im 1; set A2 := cubicA2 im; set A3 := cubicA3 im
  change M_scale * sc + w1 * r * qt1_hi + A3 * (r * (r - 1) * (r - 2)) * qt3_hi ≤
    M_scale * Wr + A2 * (r * (r - 1)) * qt2_lo at hdr_nat
  set c₁ : ℝ := (w1 : ℝ) / (M_scale : ℝ); set c₂ : ℝ := - ((A2 : ℝ) / (M_scale : ℝ))
  set c₃ : ℝ := (A3 : ℝ) / (M_scale : ℝ)
  have hf_le : ∀ d ≤ r, f d ≤ gPoly3 0 c₁ c₂ c₃ r d := by
    intro d hd; rw [hf_eq d]; have hcub := potWInt_le_cubic im (u := r - d) (by omega)
    have hcubR := Nat.cast_le (α := ℝ).mpr hcub
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, nat_cast_fall2,
      Nat.cast_mul, Nat.cast_mul, nat_cast_fall3, Nat.cast_sub hd] at hcubR
    unfold gPoly3; dsimp only [c₁, c₂, c₃, w1, A2, A3]; unfold M_scale; push_cast; linarith
  have hiter := iter_upper_le_gPoly3 p_lo p_hi hr1 hp_lo_nn hp_lo_le1 hf_anti hf_le b
  have hp1_hi := (le_div_iff₀ hM_pos).mp hpow1_hi; have hp2_lo := (div_le_iff₀ hM_pos).mp hpow2_lo
  have hp3_hi := (le_div_iff₀ hM_pos).mp hpow3_hi
  have h1 : (w1 : ℝ) * (r : ℝ) * ((1 - p_lo / (r : ℝ)) ^ b * (M_scale : ℝ)) ≤ (w1 : ℝ) * (r : ℝ) *
    (qt1_hi : ℝ) := mul_le_mul_of_nonneg_left hp1_hi (by positivity)
  have h2 : (A2 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1)) * (qt2_lo : ℝ) ≤ (A2 : ℝ) * ((r : ℝ) * ((r : ℝ) -
    1)) * ((1 - 2 * p_lo / (r : ℝ)) ^ b * (M_scale : ℝ)) := mul_le_mul_of_nonneg_left hp2_lo
    (mul_nonneg (by positivity) hr2_nn)
  have h3 : (A3 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2)) * ((1 - 3 * p_lo / (r : ℝ)) ^ b *
    (M_scale : ℝ)) ≤ (A3 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2)) * (qt3_hi : ℝ) :=
    mul_le_mul_of_nonneg_left hp3_hi (mul_nonneg (by positivity) hr3_nn)
  have hdrR := Nat.cast_le (α := ℝ).mpr hdr_nat; push_cast at hdrR
  rw [Nat.cast_sub hr1, Nat.cast_sub hr2] at hdrR
  have hf0 : f 0 = (Wr : ℝ) / (M_scale : ℝ) := (by simpa using hf_eq 0); rw [hf0]
  have hcomb : (sc : ℝ) / (M_scale : ℝ) + (0 + c₁ * (r : ℝ) * (1 - p_lo / (r : ℝ)) ^ b + c₂ * ((r :
    ℝ) * ((r : ℝ) - 1)) * (1 - 2 * p_lo / (r : ℝ)) ^ b + c₃ * ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) -
    2)) * (1 - 3 * p_lo / (r : ℝ)) ^ b) ≤ (Wr : ℝ) / (M_scale : ℝ) := by
    dsimp only [c₁, c₂, c₃]; unfold M_scale at h1 h2 h3 hdrR ⊢; push_cast at h1 h2 h3 hdrR ⊢
    linarith
  exact (add_le_add hsc_le hiter).trans hcomb
lemma drift_mode3 (im : Fin 10) (idx : Fin 44) {r b sc : ℕ} {p_hi : ℝ} {f : ℕ → ℝ} (hr1 : 1 ≤ r)
    (hf_eq : ∀ d, f d = (potWInt im (r - d) : ℝ) / (M_scale : ℝ)) (hf_anti : ∀ d < r, f (d + 1) ≤ f
    d) (hsc_le : varPhiCHi idx * √((b : ℝ) / r) ≤ (sc : ℝ) / (M_scale : ℝ)) (hm3 : checkMode3 im idx
    r b sc (potWInt im r) = true) : varPhiCHi idx * √((b : ℝ) / r) + (stage2CouponStepUpper
    (varPhiSinLo idx ^ 2) p_hi r)^[b] f 0 ≤ f 0 := by
  have hM_pos : (0 : ℝ) < M_scale := (by unfold M_scale; norm_num)
  set p_lo : ℝ := varPhiSinLo idx ^ 2; set F0 : ℕ → ℕ := fun d ↦ potWInt im (r - d)
  set qs := qListFrom idx r 0 b; set v_end := (iterStepWithQs qs b (ofFnFrom F0 0 (b + 1))).headD 0
  unfold checkMode3 at hm3; have hdr_nat : sc + v_end ≤ potWInt im r := of_decide_eq_true hm3
  have hlist := stepWithQs_iter_ofFnFrom idx r qs b 0 0 F0 (by simp [qs])
  have hv_eq : v_end = (stepIntUpper idx r)^[b] F0 0 := by
    dsimp only [v_end]; rw [iterStepWithQs_eq, show b + 1 = 0 + b + 1 by omega, hlist]; rfl
  have heq := (stage2CouponStepUpper_iter_eq_stepExact_iter_on p_lo p_hi r (sq_nonneg _)
    (varPhi_p_lo_le_one idx) hf_anti b).1 0 (Nat.zero_le r)
  have hF0 : ∀ d ≤ r, f d ≤ (F0 d : ℝ) / (M_scale : ℝ) := fun d _ ↦ (hf_eq d).le
  have hiter := stepExact_iter_le_stepIntUpper_iter idx hr1 hf_anti hF0 b 0 (Nat.zero_le r)
  change (stepExact p_lo r)^[b] f 0 ≤ ((stepIntUpper idx r)^[b] F0 0 : ℝ) / (M_scale : ℝ) at hiter
  rw [← heq, ← hv_eq] at hiter
  have hf0 : f 0 = (potWInt im r : ℝ) / (M_scale : ℝ) := (by simpa using hf_eq 0); rw [hf0]
  have hdrR : (sc : ℝ) + (v_end : ℝ) ≤ (potWInt im r : ℝ) := (by exact_mod_cast hdr_nat)
  have hcomb : (sc : ℝ) / (M_scale : ℝ) + (v_end : ℝ) / (M_scale : ℝ) ≤
      (potWInt im r : ℝ) / (M_scale : ℝ) := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hdrR hM_pos.le
  exact (add_le_add hsc_le hiter).trans hcomb
end Stage2CertInternals
/- ## Exported Schedule, Angle, Cost Table, Potential, and Six Target Theorems -/
/-- Number of simultaneous projective Grover groups `b = 2 ^ tSched m r` at `(m, r)`. -/
def stage2Batch (m r : ℕ) : ℕ := if 2 ≤ m then 2 ^ Stage2CertInternals.tSched m r else 1
/-- Slot-group size `g = m / stage2Batch m r` at `(m, r)`. -/
def stage2Group (m r : ℕ) : ℕ :=
  if 2 ≤ m then 2 ^ (Stage2CertInternals.gridExp m - Stage2CertInternals.tSched m r) else m
/-- Target rotation angle index `idx: Fin 44` in `varPhi` at `(m, r)`. -/
def stage2Angle (m r : ℕ) : Fin 44 := Stage2CertInternals.idxSched m r
/-- Certified coprime relative-cost bound across all `121 / 121` cells of `groverGrid`. -/
def stage2RelCost (m k : ℕ) : ℚ≥0 :=
  if 2 ≤ m ∧ 2 ≤ k then
    let gm := Stage2CertInternals.gridExp m
    let gk := Stage2CertInternals.gridExp k
    if 1 ≤ gm ∧ gm ≤ 10 ∧ 1 ≤ gk ∧ gk ≤ 10 then
      ((Stage2CertInternals.relCostNum (gm - 1) (gk - 1) : ℚ≥0) /
        (Stage2CertInternals.relCostDen (gm - 1) (gk - 1) : ℚ≥0))
    else stage1RelCost
  else stage1RelCost
/-- Certified normalized potential `W_{m, k}(s)` on `0 ≤ s ≤ k` at integer scale `10 ^ 9`. -/
noncomputable def stage2NormPot (m k s : ℕ) : ℝ :=
  if h : 1 ≤ Stage2CertInternals.gridExp m ∧ Stage2CertInternals.gridExp m ≤ 10 then
    (Stage2CertInternals.potWInt ⟨Stage2CertInternals.gridExp m - 1, by omega⟩ (k - s) : ℝ) /
      (Stage2CertInternals.M_scale : ℝ)
  else 0
/-- Positivity and exact slot partition `stage2Batch m r * stage2Group m r = m` on
  `groverGrid`. -/
theorem stage2_bg : ∀ {m r : ℕ}, m ∈ groverGrid → 2 ≤ m → 2 ≤ r → r ≤ 1024 →
    1 ≤ stage2Batch m r ∧ stage2Batch m r * stage2Group m r = m := by
  intro m r hm hm2 _ _; obtain ⟨_, _, hpow⟩ := Stage2CertInternals.gridExp_bounds_of_mem hm hm2
  unfold stage2Batch stage2Group Stage2CertInternals.tSched; rw [ite_eq_left hm2, ite_eq_left hm2]
  refine ⟨Nat.one_le_two_pow, ?_⟩
  rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.min_le_left _ _)]; exact hpow
/-- Nonnegativity of `stage2NormPot` across all states `s ≤ k`. -/
theorem stage2NormPot_nonneg : ∀ {m k : ℕ}, m ∈ groverGrid → k ∈ groverGrid →
    2 ≤ m → 2 ≤ k → ∀ s ≤ k, 0 ≤ stage2NormPot m k s := by
  intro m k _ _ _ _ s _; unfold stage2NormPot Stage2CertInternals.M_scale; split_ifs <;> positivity
/-- Terminal `r = 1` (`s = k - 1`) condition `(81831 / 100000: ℝ) ≤ stage2NormPot m k (k -
  1)`. -/
theorem stage2NormPot_last : ∀ {m k : ℕ}, m ∈ groverGrid → k ∈ groverGrid →
    2 ≤ m → 2 ≤ k → (81831 / 100000 : ℝ) ≤ stage2NormPot m k (k - 1) := by
  intro m k hm _ hm2 hk2; obtain ⟨hg1, hg10, _⟩ := Stage2CertInternals.gridExp_bounds_of_mem hm hm2
  have hk_sub : k - (k - 1) = 1 := (by omega); unfold stage2NormPot
  rw [dite_eq_left ⟨hg1, hg10⟩, hk_sub]; have hw1 : (818310000 : ℝ) ≤
      (Stage2CertInternals.potWInt ⟨Stage2CertInternals.gridExp m - 1, by omega⟩ 1 : ℝ) := by
    have hc := Nat.cast_le (α := ℝ).mpr
      (Stage2CertInternals.potWInt_one_ge ⟨Stage2CertInternals.gridExp m - 1, by omega⟩)
    have hc8 : ((818310000 : ℕ) : ℝ) = 818310000 := (by norm_num); rwa [hc8] at hc
  unfold Stage2CertInternals.M_scale; linarith
/-- Per-round variable-angle drift inequality across all `s < k - 1` (`2 ≤ r ≤ 1024`). -/
theorem stage2NormPot_drift : ∀ {m k : ℕ}, m ∈ groverGrid → k ∈ groverGrid →
    2 ≤ m → 2 ≤ k → ∀ s < k - 1,
      let r := k - s; let b := stage2Batch m r; let idx := stage2Angle m r
      varPhiCHi idx * √((b : ℝ) / r) + (stage2CouponStepUpper (varPhiSinLo idx ^ 2) (varPhiSinHi idx
        ^ 2) r)^[b] (fun d ↦ stage2NormPot m k (s + d)) 0 ≤ stage2NormPot m k s := by
  intro m k hm hk hm2 _ s hs; dsimp only; set r := k - s
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk; have hr2 : 2 ≤ r := (by omega)
  have hr1 : 1 ≤ r := (by omega); have hr_hi : r ≤ 1024 := (by omega)
  obtain ⟨hg1, hg10, _⟩ := Stage2CertInternals.gridExp_bounds_of_mem hm hm2
  let im : Fin 10 := ⟨Stage2CertInternals.gridExp m - 1, by omega⟩
  have him_exp : im.val + 1 = Stage2CertInternals.gridExp m := (by dsimp only [im]; omega)
  have him_val : im.val = Stage2CertInternals.gridExp m - 1 := rfl
  have hdr_bool := Stage2CertInternals.checkDriftAt_true im hr1 hr_hi
  unfold Stage2CertInternals.checkDriftAt at hdr_bool; rw [ite_eq_left ⟨hr2, hr_hi⟩] at hdr_bool
  dsimp only at hdr_bool; rw [Stage2CertInternals.withForcedNat_eq] at hdr_bool
  have hb12 := (Bool.and_eq_true _ _).mp hdr_bool; have hsq_nat := of_decide_eq_true hb12.1
  have hm_or := hb12.2; set p := Stage2CertInternals.tIdxSched im.val r
  set t := min (im.val + 1) p.1; set idx : Fin 44 := ⟨p.2 % 44, Nat.mod_lt _ (by norm_num)⟩
  have hb_eq : stage2Batch m r = 2 ^ t := by
    unfold stage2Batch Stage2CertInternals.tSched; rw [ite_eq_left hm2, ← him_val, ← him_exp]
  have hidx_eq : stage2Angle m r = idx := by
    unfold stage2Angle Stage2CertInternals.idxSched; rw [ite_eq_left hm2]
  rw [hb_eq, hidx_eq]; set b := 2 ^ t; set sq := Stage2CertInternals.sqCeil b r
  set sc := (99999999 + varPhiCHiNum idx * sq) / 100000000
  set qt1_hi := Stage2CertInternals.pow2Ceil t (Stage2CertInternals.qjCeil 1 idx r)
  set qt1_lo := Stage2CertInternals.pow2Floor t (Stage2CertInternals.qjFloor 1 idx r)
  set qt2_hi := Stage2CertInternals.pow2Ceil t (Stage2CertInternals.qjCeil 2 idx r)
  set qt2_lo := Stage2CertInternals.pow2Floor t (Stage2CertInternals.qjFloor 2 idx r)
  set qt3_hi := Stage2CertInternals.pow2Ceil t (Stage2CertInternals.qjCeil 3 idx r)
  set u₀ := max 1 (min r (((Stage2CertInternals.M_scale - 1) + r * qt1_hi) /
    Stage2CertInternals.M_scale))
  set Wu₀ := Stage2CertInternals.potWInt im u₀; set wu₀ := Stage2CertInternals.slopeWInt im u₀
  have hwu0_eq : Wu₀ - Stage2CertInternals.potWInt im (u₀ - 1) = wu₀ := rfl
  have hM_pos : (0 : ℝ) < Stage2CertInternals.M_scale := by
    unfold Stage2CertInternals.M_scale; norm_num
  have hr_pos : (0 : ℝ) < r := (by exact_mod_cast hr1)
  have hsqrt_le : √((b : ℝ) / r) ≤ (sq : ℝ) / (Stage2CertInternals.M_scale : ℝ) := by
    have hsqR : (Stage2CertInternals.M_scale : ℝ) ^ 2 * (b : ℝ) ≤ (r : ℝ) * (sq : ℝ) ^ 2 := by
      have hc := Nat.cast_le (α := ℝ).mpr hsq_nat
      rwa [Nat.cast_mul, Nat.cast_mul,
        Nat.cast_pow Stage2CertInternals.M_scale 2, Nat.cast_pow sq 2] at hc
    have hdiv : (b : ℝ) / (r : ℝ) ≤ ((sq : ℝ) / (Stage2CertInternals.M_scale : ℝ)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ hr_pos (pow_pos hM_pos 2)]; linarith
    exact (Real.sqrt_le_sqrt hdiv).trans_eq
      (Real.sqrt_sq (div_nonneg (Nat.cast_nonneg sq) hM_pos.le))
  have hchi_nn : 0 ≤ varPhiCHi idx := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hsc_le : varPhiCHi idx * √((b : ℝ) / r) ≤ (sc : ℝ) / (Stage2CertInternals.M_scale : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt_le hchi_nn; refine hmul.trans ?_
    have hceil : (varPhiCHiNum idx : ℝ) * (sq : ℝ) ≤ 100000000 * (sc : ℝ) := by
      have hc := Nat.cast_le (α := ℝ).mpr
        (Stage2CertInternals.nat_le_ceilDiv_mul (varPhiCHiNum idx * sq) 100000000 (by norm_num))
      rw [Nat.cast_mul, Nat.cast_mul] at hc
      have hc2 : ((100000000 : ℕ) : ℝ) = 100000000 := (by norm_num); rwa [hc2] at hc
    unfold varPhiCHi; rw [mul_div_assoc', div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hM_pos.le
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 100000000)]; linarith
  set p_lo : ℝ := varPhiSinLo idx ^ 2; set p_hi : ℝ := varPhiSinHi idx ^ 2
  have hp_lo_nn : 0 ≤ p_lo := sq_nonneg _
  have hp_lo_le1 : p_lo ≤ 1 := Stage2CertInternals.varPhi_p_lo_le_one idx
  have hf_eq : ∀ d, stage2NormPot m k (s + d) =
      (Stage2CertInternals.potWInt im (r - d) : ℝ) / (Stage2CertInternals.M_scale : ℝ) := by
    intro d; have hsub : k - (s + d) = r - d := (by omega); unfold stage2NormPot
    rw [dite_eq_left ⟨hg1, hg10⟩, hsub]
  have hf_anti : ∀ d < r, stage2NormPot m k (s + (d + 1)) ≤ stage2NormPot m k (s + d) := by
    intro d hd; rw [hf_eq (d + 1), hf_eq d]; refine div_le_div_of_nonneg_right ?_ hM_pos.le
    have hsub_eq : r - (d + 1) = (r - d) - 1 := (by omega); rw [hsub_eq]
    exact_mod_cast Stage2CertInternals.potWInt_mono_step im (u := r - d) (by omega) (by omega)
  have hsin_le := Stage2CertInternals.sinSqLo_le idx
  obtain ⟨hq1_nn, hq1_fl, hq1_cl⟩ := Stage2CertInternals.qj_bounds (j := 1) idx hr1 (by omega)
  obtain ⟨hq2_nn, hq2_fl, hq2_cl⟩ := Stage2CertInternals.qj_bounds (j := 2) idx hr1 (by omega)
  have hpow1_hi : (1 - p_lo / (r : ℝ)) ^ b ≤ (qt1_hi : ℝ) / (Stage2CertInternals.M_scale : ℝ) := by
    simpa [p_lo, one_mul] using Stage2CertInternals.pow2Ceil_bound t hq1_nn
      (Stage2CertInternals.qjCeil 1 idx r) hq1_cl
  have hpow1_lo : (qt1_lo : ℝ) / (Stage2CertInternals.M_scale : ℝ) ≤ (1 - p_lo / (r : ℝ)) ^ b := by
    simpa [p_lo, one_mul] using Stage2CertInternals.pow2Floor_bound t
      (Stage2CertInternals.qjFloor 1 idx r) hq1_fl
  have hpow2_hi : (1 - 2 * p_lo / (r : ℝ)) ^ b ≤
      (qt2_hi : ℝ) / (Stage2CertInternals.M_scale : ℝ) := by
    simpa [p_lo] using Stage2CertInternals.pow2Ceil_bound t hq2_nn
      (Stage2CertInternals.qjCeil 2 idx r) hq2_cl
  have hpow2_lo : (qt2_lo : ℝ) / (Stage2CertInternals.M_scale : ℝ) ≤
      (1 - 2 * p_lo / (r : ℝ)) ^ b := by
    simpa [p_lo] using Stage2CertInternals.pow2Floor_bound t
      (Stage2CertInternals.qjFloor 2 idx r) hq2_fl
  have hpot_s : stage2NormPot m k s = (fun d ↦ stage2NormPot m k (s + d)) 0 := (by simp)
  rw [hpot_s]; rcases (Bool.or_eq_true _ _).mp hm_or with hm01 | hm3
  · rcases (Bool.or_eq_true _ _).mp hm01 with hm0 | hm1
    · have hm0_pair := (Bool.and_eq_true _ _).mp hm0
      rcases of_decide_eq_true hm0_pair.1 with ⟨hu1, hur⟩; have hdr_nat := hm0_pair.2
      rw [hwu0_eq] at hdr_nat
      exact Stage2CertInternals.drift_mode0 im idx hr1 hr2 hr_hi hu1 hur hp_lo_nn hp_lo_le1
        hf_eq hf_anti hsc_le hpow1_hi hpow1_lo hpow2_hi (of_decide_eq_true hdr_nat)
    · have hm1_pair := (Bool.and_eq_true _ _).mp hm1; have hj3 := of_decide_eq_true hm1_pair.1
      have hdr_nat := of_decide_eq_true hm1_pair.2
      obtain ⟨hq3_nn, _, hq3_cl⟩ := Stage2CertInternals.qj_bounds (j := 3) idx hr1 hj3
      have hpow3_hi : (1 - 3 * p_lo / (r : ℝ)) ^ b ≤
          (qt3_hi : ℝ) / (Stage2CertInternals.M_scale : ℝ) := by
        simpa [p_lo] using Stage2CertInternals.pow2Ceil_bound t hq3_nn
          (Stage2CertInternals.qjCeil 3 idx r) hq3_cl
      exact Stage2CertInternals.drift_mode1 im idx hr1 hr2 hr_hi hp_lo_nn hp_lo_le1
        hf_eq hf_anti hsc_le hpow1_hi hpow2_lo hpow3_hi hdr_nat
  · exact Stage2CertInternals.drift_mode3 im idx hr1 hf_eq hf_anti hsc_le
      ((Bool.and_eq_true _ _).mp hm3).2
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllCert
section WD_FindAllSubcube
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val tensorState)
open Matrix (mulVec_mulVec mulVec_diagonal)
open Complex (normSq)
open List (mem_finRange prod_cons finRange map_cons)
open Fintype (sum_eq_single sum_prod_type)
open Equiv (swap)
open Pi (single)
open scoped Matrix NNReal ENNReal ComplexOrder MatrixOrder QProg.Notation QHLExpectation
@[expose] public section
/- ## Prefix-Subcube Partition of `Fin (2 ^ n)` (`m = 2 ^ p`) -/
/-- Split `x: Fin (2 ^ n)` (`p ≤ n`, `m = 2 ^ p`) into its low `(n - p)`-bit local
  coordinate and
  its high `p`-bit subcube index in `Fin m`. -/
noncomputable abbrev subcubeSplit {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) :
    Fin (2 ^ n) ≃ Fin (2 ^ (n - p)) × Fin m :=
  (finCongr (by congr 1; omega)).trans
    ((lowHighEquiv (n - p) p).trans (Equiv.prodCongr (.refl _) (finCongr hm.symm)))
/-- Prefix subcube index `j: Fin m` of `x: Fin (2 ^ n)`. -/
noncomputable def subcubePref {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (x : Fin (2 ^ n)) : Fin m :=
  (subcubeSplit hp hm x).2
/-- Local `(n - p)`-bit target set inside subcube `j: Fin m`. -/
noncomputable def subcubeLocalSet {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (j : Fin m) : Finset (Fin (2 ^ (n - p))) :=
  (S.filter fun x ↦ subcubePref hp hm x = j).image fun x ↦ (subcubeSplit hp hm x).1
theorem mem_subcubeLocalSet_iff {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (j : Fin m) (u : Fin (2 ^ (n - p))) :
    u ∈ subcubeLocalSet hp hm S j ↔ (subcubeSplit hp hm).symm (u, j) ∈ S := by
  simp only [subcubeLocalSet, Finset.mem_image, Finset.mem_filter]; constructor
  · rintro ⟨x, ⟨hxS, hxj⟩, rfl⟩
    have hpair : subcubeSplit hp hm x = ((subcubeSplit hp hm x).1, j) := Prod.ext rfl hxj
    rwa [← hpair, Equiv.symm_apply_apply]
  · intro hmem; refine ⟨(subcubeSplit hp hm).symm (u, j), ⟨hmem, ?_⟩, ?_⟩
    · simp [subcubePref]
    · simp
theorem card_subcubeLocalSet_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (j : Fin m) :
    (subcubeLocalSet hp hm S j).card = (S.filter fun x ↦ subcubePref hp hm x = j).card := by
  refine Finset.card_image_of_injOn fun x₁ hx₁ x₂ hx₂ heq ↦ ?_
  have h1 : (subcubeSplit hp hm x₁).2 = j := (Finset.mem_filter.mp hx₁).2
  have h2 : (subcubeSplit hp hm x₂).2 = j := (Finset.mem_filter.mp hx₂).2
  exact (subcubeSplit hp hm).injective (Prod.ext heq (h1.trans h2.symm))
theorem sum_card_subcubeLocalSet_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (S : Finset (Fin (2 ^
    n))) : (∑ j : Fin m, (subcubeLocalSet hp hm S j).card) = S.card := by
  simp_rw [card_subcubeLocalSet_eq]
  exact (Finset.card_eq_sum_card_fiberwise (f := subcubePref hp hm) (t := Finset.univ)
    fun _ _ ↦ Finset.mem_univ _).symm
/-- Total parallel-oracle queries `(allKs.map (· + 1)).sum` used across `allKs.length`
  prefix-subcube sweeps with iteration counts `allKs`. -/
def subcubeSweepsQueries (allKs : List ℕ) : ℕ := (allKs.map (· + 1)).sum
@[simp]
theorem subcubeSweepsQueries_nil : subcubeSweepsQueries [] = 0 := rfl
@[simp] theorem subcubeSweepsQueries_cons (K_sub : ℕ) (ks : List ℕ) :
    subcubeSweepsQueries (K_sub :: ks) = (K_sub + 1) + subcubeSweepsQueries ks := rfl
/-- Single-step backward Markov expectation on the per-subcube remaining-target vector
  `r: Fin m → ℕ` under a coherent deflated prefix-subcube sweep with `K_sub` local Grover
  iterations on subcubes of size `subDim = 2 ^ (n - p)`. -/
noncomputable def subcubeStepExp {m : ℕ} (subDim K_sub : ℕ)
    (F : (Fin m → ℕ) → ℝ) (r : Fin m → ℕ) : ℝ :=
  ∑ b : Fin m → Bool,
    (∏ j : Fin m,
      match b j with
      | true => p_succ_frac K_sub (r j) subDim
      | false => 1 - p_succ_frac K_sub (r j) subDim) *
      F (fun j ↦ if b j then r j - 1 else r j)
/-- Multi-sweep backward Markov expectation on `r: Fin m → ℕ` across `allKs: List ℕ`. -/
noncomputable def subcubeSweepsExp {m : ℕ} (subDim : ℕ) :
    List ℕ → ((Fin m → ℕ) → ℝ) → (Fin m → ℕ) → ℝ
  | [], F => F
  | K_sub :: ks, F => subcubeStepExp subDim K_sub (subcubeSweepsExp subDim ks F)
/-- Exact 1D single-subcube backward expectation across `allKs: List ℕ` starting from `c`
  targets
  in a subcube of size `subDim = 2 ^ (n - p)`. -/
noncomputable def subcubeOneDimExp (subDim : ℕ) : List ℕ → (ℕ → ℝ) → ℕ → ℝ
  | [], pot₀, c => pot₀ c
  | K_sub :: ks, pot₀, c =>
      p_succ_frac K_sub c subDim * subcubeOneDimExp subDim ks pot₀ (c - 1) +
        (1 - p_succ_frac K_sub c subDim) * subcubeOneDimExp subDim ks pot₀ c
end
public section
/- ## Single-Slot `(n - p) + p` Register Cast and Coherent `T = ∅` Subcube Circuit -/
private abbrev cast1nReg {n p : ℕ} (hp : p ≤ n) : QRegister ((n - p) + p) (1 * n) :=
  QRegister.block 0 ((n - p) + p) (by omega)
private abbrev cast1nEquiv {n p : ℕ} (hp : p ≤ n) : Fin (2 ^ (1 * n)) ≃ Fin (2 ^ ((n - p) + p)) :=
  finCongr (by congr 1; omega)
private lemma extractIndex_cast1nReg {n p : ℕ} (hp : p ≤ n) (u : Fin (2 ^ (1 * n))) :
    (cast1nReg hp).extractIndex u = cast1nEquiv hp u := by
  apply (basisBits ((n - p) + p)).injective; funext q
  rw [basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit]
  simp [cast1nReg, cast1nEquiv]
private lemma agreeOutside_cast1nReg {n p : ℕ} (hp : p ≤ n) (i j : Fin (2 ^ (1 * n))) :
    (cast1nReg hp).AgreeOutside i j := by
  intro q hq; exact False.elim (hq ⟨⟨q.val, by omega⟩, Fin.ext (by simp [cast1nReg])⟩)
private lemma embedMatrix_cast1nReg_mulVec_comp {n p : ℕ} (hp : p ≤ n)
    (B : Operator (2 ^ ((n - p) + p))) (ψ : Fin (2 ^ ((n - p) + p)) → ℂ) :
    (cast1nReg hp).embedMatrix B *ᵥ (ψ ∘ cast1nEquiv hp) = (B *ᵥ ψ) ∘ cast1nEquiv hp := by
  funext i; rw [Matrix.mulVec, dotProduct]
  simp_rw [QRegister.embedMatrix_apply_of_agreeOutside, extractIndex_cast1nReg,
    agreeOutside_cast1nReg, ite_true, mul_one]
  exact (cast1nEquiv hp).sum_comp (fun y ↦ B (cast1nEquiv hp i) y * ψ y)
private lemma finCongr_symm_finCongr {a b : ℕ} (h : a = b) (j : Fin a) :
    finCongr h.symm (finCongr h j) = j := by ext; simp
private lemma subcubeSplit_addrEquiv_one {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (u : Fin (2 ^
    (1 * n))) : subcubeSplit hp hm (addrEquiv n 1 u 0) = ((lowHighEquiv (n - p) p (cast1nEquiv hp
    u)).1, finCongr hm.symm (lowHighEquiv (n - p) p (cast1nEquiv hp u)).2) := by
  have hcast : finCongr (by congr 1; omega) (addrEquiv n 1 u 0) = cast1nEquiv hp u := by
    ext; rw [finCongr_apply, Fin.val_cast, addrEquiv_eq_div_pow_mod]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, finCongr_apply, Fin.val_cast]
    exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using u.isLt)
  unfold subcubeSplit; rw [Equiv.trans_apply, Equiv.trans_apply, hcast]; rfl
private lemma mem_oddSet_one_iff {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) :
    u ∈ oddSet n 1 S ↔ addrEquiv n 1 u 0 ∈ S := by
  rw [oddSet, Finset.mem_filter]; simp only [Finset.mem_univ, true_and, Fin.prod_univ_one]
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h1 ↦ absurd h1 (by norm_num), fun hm ↦ absurd hm h⟩
private lemma firstTupleHit_one_eq {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) :
    firstTupleHit n 1 S u = if addrEquiv n 1 u 0 ∈ S then some (addrEquiv n 1 u 0) else none := by
  unfold firstTupleHit; by_cases hu : u ∈ oddSet n 1 S
  · have hmem : addrEquiv n 1 u 0 ∈ S := (mem_oddSet_one_iff S u).mp hu
    rw [dite_eq_left hu, ite_eq_left hmem]
    exact congrArg (fun j : Fin 1 ↦ some (addrEquiv n 1 u j)) (Subsingleton.elim _ _)
  · have hnmem : addrEquiv n 1 u 0 ∉ S := mt (mem_oddSet_one_iff S u).mpr hu
    rw [dite_eq_right hu, ite_eq_right hnmem]
private noncomputable def subcubeSlotPrep {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (j : Fin m) : Unitary (2 ^ (1 * (n + 1))) :=
  (addrReg n 1).embedUnitary ((cast1nReg hp).embedUnitary
    (((lowBlock (n - p) p).embedUnitary hadamardUnitary) *
      ((highBlock (n - p) p).embedUnitary (permutationUnitary (swap 0 (finCongr hm j))))))
private noncomputable def subcubePrepUnitary {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) :
    Unitary (2 ^ (m * (n + 1))) :=
  ((finRange m).map fun j ↦
    (groupReg (Nat.mul_one m) j).embedUnitary (subcubeSlotPrep hp hm j)).prod
private noncomputable def subcubeSlotDiffuser {n p : ℕ} (hp : p ≤ n) :
    Unitary (2 ^ (1 * (n + 1))) :=
  (addrReg n 1).embedUnitary ((cast1nReg hp).embedUnitary
    ((lowBlock (n - p) p).embedUnitary Grover.diffuserUnitary))
private noncomputable def subcubeDiffuserUnitary {n p m : ℕ} (hp : p ≤ n) :
    Unitary (2 ^ (m * (n + 1))) :=
  ((finRange m).map fun j ↦
    (groupReg (Nat.mul_one m) j).embedUnitary (subcubeSlotDiffuser hp)).prod
private noncomputable def subcubePhaseStep {Var : Type} (n m k : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let fc := (lowBlock (m * (n + 1)) (k * n)).embedUnitary (flagConj n m)
  .seq (.step (phaseTag fc))
    (.seq (.oracle (workFullReg n m (m * (n + 1) + k * n) (by omega)))
      (.step (phaseTag fc)))
private noncomputable def subcubeGroverStep {Var : Type} {n p m k : ℕ} (hp : p ≤ n) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (subcubePhaseStep n m k)
    (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
      (subcubeDiffuserUnitary (m := m) hp))))
private noncomputable def subcubeGroverLoop {Var : Type} {n p m k : ℕ} (hp : p ≤ n)
    (K_sub : ℕ) : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  OracleDynamicCircuit.sequence (List.replicate K_sub (subcubeGroverStep hp))
/-- Single `T = ∅` coherent prefix-subcube pre-sweep on `m * (n + 1) + k * n` qubits (`K_sub
  + 1`
  parallel oracle calls, `0` extra ancillas, `0` `.qIf` trees). -/
noncomputable def subcubeInitRound {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_sub : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  let hbg1 : m * 1 = m := Nat.mul_one m
  .seq (.step (phaseTag ((lowBlock W M).embedUnitary (subcubePrepUnitary hp hm))))
    (.seq (subcubeGroverLoop hp K_sub)
      (.seq (.oracle (workFullReg n m (W + M) (by omega)))
        (.seq (.step (phaseTag (permutationUnitary (memWriteBatchPerm 0 (groupHits hbg1)))))
          (setCountAndResetWork res (batchNextCount hm1 hkN hbg1 0)))))
private noncomputable def subcubeProdState {n m : ℕ}
    (ξ : Fin m → Fin (2 ^ (1 * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  ∏ j : Fin m, ξ j ((groupReg (Nat.mul_one m) j).extractIndex w)
private lemma prod_groupReg_embedMatrix_mulVec_het {n m b g : ℕ} (hbg : b * g = m) (A : Fin b →
    Matrix (Fin (2 ^ (g * (n + 1)))) (Fin (2 ^ (g * (n + 1)))) ℂ) (f : Fin b → Fin (2 ^ (g * (n +
    1))) → ℂ) : ((finRange b).map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod *ᵥ (fun w ↦ ∏ c :
    Fin b, f c ((groupReg hbg c).extractIndex w)) = fun w ↦ ∏ c : Fin b, (A c *ᵥ f c) ((groupReg hbg
    c).extractIndex w) := by
  suffices ∀ l : List (Fin b), l.Nodup → ((l.map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod)
    *ᵥ (fun w ↦ ∏ c : Fin b, f c ((groupReg hbg c).extractIndex w)) = fun w ↦ ∏ c : Fin b, (if c ∈ l
    then A c *ᵥ f c else f c) ((groupReg hbg c).extractIndex w) by
    rw [this (finRange b) (List.nodup_finRange b)]; funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_left (mem_finRange c)]
  intro l hl
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]; funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_right List.not_mem_nil]
  | cons c₀ l ih =>
    rcases List.nodup_cons.mp hl with ⟨hc₀, hl'⟩
    rw [map_cons, prod_cons, ← mulVec_mulVec, ih hl', embedMatrix_groupReg_mulVec_prod]; funext w
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    by_cases h : c = c₀
    · subst h; rw [ite_eq_left rfl, ite_eq_right hc₀, ite_eq_left List.mem_cons_self]
    · have hmem : c ∈ c₀ :: l ↔ c ∈ l := (by simp [List.mem_cons, h]); by_cases hl_mem : c ∈ l
      · rw [ite_eq_left (hmem.mpr hl_mem), ite_eq_right h, ite_eq_left hl_mem]
      · rw [ite_eq_right (mt hmem.mp hl_mem), ite_eq_right h, ite_eq_right hl_mem]
private noncomputable def subcubeSlotState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (t : ℕ) (j : Fin m) : Fin (2 ^ (1 * (n + 1))) → ℂ :=
  (addrReg n 1).tensorState (workMemState (groverMultiState (subcubeLocalSet hp hm S j) t) (single
  (finCongr hm j) 1) ∘ cast1nEquiv hp) (single 0 1)
private lemma oracleMat_oddSet_one_mulVec_subcube {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (S :
    Finset (Fin (2 ^ n))) (j : Fin m) (ψ : Fin (2 ^ (n - p)) → ℂ) : oracleMat (oddSet n 1 S) *ᵥ
    (workMemState ψ (single (finCongr hm j) 1) ∘ cast1nEquiv hp) = workMemState (oracleMat
    (subcubeLocalSet hp hm S j) *ᵥ ψ) (single (finCongr hm j) 1) ∘ cast1nEquiv hp := by
  funext u; rw [oracleMat, mulVec_diagonal]; dsimp only [Function.comp_apply, workMemState]
  rw [oracleMat, mulVec_diagonal]
  by_cases hj : (lowHighEquiv (n - p) p (cast1nEquiv hp u)).2 = finCongr hm j
  · have hsp := subcubeSplit_addrEquiv_one hp hm u; rw [hj, finCongr_symm_finCongr] at hsp
    have hiff : u ∈ oddSet n 1 S ↔
        (lowHighEquiv (n - p) p (cast1nEquiv hp u)).1 ∈ subcubeLocalSet hp hm S j := by
      rw [mem_oddSet_one_iff, mem_subcubeLocalSet_iff, ← hsp, Equiv.symm_apply_apply]
    rw [hj, Pi.single_eq_same, mul_one, mul_one, if_congr hiff rfl rfl]
  · rw [Pi.single_eq_of_ne hj]; ring
private noncomputable def subcubeUnitaryPre {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (K_sub : ℕ) : Operator (2 ^ (m * (n + 1) + k * n)) :=
  let W := m * (n + 1)
  let M := k * n
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1
  let orac := (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let phaseOp := fc * orac * fc
  let diffOp := (lowBlock W M).embedMatrix (subcubeDiffuserUnitary (m := m) hp).1
  let prepOp := (lowBlock W M).embedMatrix (subcubePrepUnitary hp hm).1
  let writeOp := (permutationUnitary
    (memWriteBatchPerm (W := W) (n := n) (k := k) 0 (groupHits (n := n) (Nat.mul_one m)))).1
  writeOp * orac * ((diffOp * phaseOp) ^ K_sub) * prepOp
private lemma unitaryEffect_subcubePrefix {Var : Type} [DecidableEq Var] {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (S : Finset (Fin (2 ^ n))) (K_sub : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let pref : OracleCirc Var (W + M) ((n + 1) * m) :=
      .seq (.step (phaseTag ((lowBlock W M).embedUnitary (subcubePrepUnitary hp hm)))) (.seq
        (subcubeGroverLoop hp K_sub) (.seq (.oracle (workFullReg n m (W + M) (by omega))) (.step
        (phaseTag (permutationUnitary (memWriteBatchPerm (W := W) (n := n) (k := k) 0 (groupHits (n
        := n) (Nat.mul_one m))))))))
    UnitaryEffect (pref.compile qAssign (groverParallelMarkingOracle m S))
      (subcubeUnitaryPre hp hm S K_sub) := by
  intro W M pref
  have horac : UnitaryEffect (.qAssign ((workFullReg n m (W + M) (by omega)).embedUnitary
    (groverParallelMarkingOracle m S)) : QProg Var (2 ^ (W + M))) ((lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1) := by
    have h1 := unitaryEffect_qAssign (Var := Var)
      ((workFullReg n m (W + M) (by omega)).embedUnitary (groverParallelMarkingOracle m S))
    rwa [workFullReg_embedUnitary_eq] at h1
  have hphase : UnitaryEffect ((subcubePhaseStep (Var := Var) n m k).compile qAssign
    (groverParallelMarkingOracle m S)) ((lowBlock W M).embedMatrix (flagConj n m).1 * (lowBlock W
    M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 * (lowBlock W
    M).embedMatrix (flagConj n m).1) := by
    unfold subcubePhaseStep
    dsimp only [compile]
    have hfc := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (flagConj n m))
    rw [embedUnitary_val] at hfc
    simpa only [Matrix.mul_assoc] using unitaryEffect_seq hfc (unitaryEffect_seq horac hfc)
  have hloop (t : ℕ) : UnitaryEffect ((subcubeGroverLoop (Var := Var) (m := m) (k := k) hp
    t).compile qAssign (groverParallelMarkingOracle m S)) (((lowBlock W M).embedMatrix
    (subcubeDiffuserUnitary (m := m) hp).1 * ((lowBlock W M).embedMatrix (flagConj n m).1 *
    (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 *
    (lowBlock W M).embedMatrix (flagConj n m).1)) ^ t) := by
    unfold subcubeGroverLoop
    induction t with
    | zero => simpa using unitaryEffect_skip (Var := Var) (d := 2 ^ (W + M))
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold subcubeGroverStep; dsimp only [compile]
      have hdiff := unitaryEffect_phaseTag (Var := Var)
        ((lowBlock W M).embedUnitary (subcubeDiffuserUnitary (m := m) hp))
      rw [embedUnitary_val] at hdiff; rw [pow_succ]
      exact unitaryEffect_seq (unitaryEffect_seq hphase hdiff) ih
  dsimp only [pref, compile]; have hprep := unitaryEffect_phaseTag (Var := Var)
    ((lowBlock W M).embedUnitary (subcubePrepUnitary hp hm))
  rw [embedUnitary_val] at hprep
  have hwrite := unitaryEffect_phaseTag (Var := Var) (permutationUnitary (memWriteBatchPerm (W := W)
    (n := n) (k := k) 0 (groupHits (n := n) (Nat.mul_one m))))
  unfold subcubeUnitaryPre; dsimp only; simpa only [Matrix.mul_assoc] using
    unitaryEffect_seq hprep (unitaryEffect_seq (hloop K_sub) (unitaryEffect_seq horac hwrite))
private lemma subcubePrepUnitary_mulVec_workMemIdx {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (R :
    Finset (Fin (2 ^ n))) (μ : Fin (2 ^ (k * n))) : (lowBlock (m * (n + 1)) (k * n)).embedMatrix
    (subcubePrepUnitary hp hm).1 *ᵥ single (workMemIdx n m k 0 μ) 1 = workMemState (subcubeProdState
    (subcubeSlotState hp hm R 0)) (single μ 1) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hex0 : (addrReg n 1).extractIndex 0 = 0 := by
    apply (basisBits (1 * n)).injective; funext r; simp [basisBits_extractIndex]
  have henv0 : ((addrReg n 1).basisSplitEquiv 0).2 = 0 := by
    funext e; simp [QRegister.basisSplitEquiv]
  have hzero_comp : (single (0 : Fin (2 ^ (1 * n))) (1 : ℂ)) = workMemState (single (0 : Fin (2 ^
    (n - p))) 1) (single (0 : Fin (2 ^ p)) 1) ∘ cast1nEquiv hp := by
    rw [workMemState_zero]; funext u; dsimp only [Function.comp_apply]; by_cases hu : u = 0
    · subst hu; have hc0 : cast1nEquiv hp 0 = 0 := Fin.ext (by simp [cast1nEquiv])
      rw [hc0, Pi.single_eq_same, Pi.single_eq_same]
    · have hcne : cast1nEquiv hp u ≠ 0 :=
        fun h ↦ hu ((cast1nEquiv hp).injective (h.trans (Fin.ext (by simp [cast1nEquiv])).symm))
      rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hcne]
  have hprep_slot (j : Fin m) : (subcubeSlotPrep hp hm j).1 *ᵥ single (0 : Fin (2 ^ (1 * (n + 1))))
    1 = subcubeSlotState hp hm R 0 j := by
    unfold subcubeSlotPrep subcubeSlotState
    rw [embedUnitary_val, QRegister.embedMatrix_mulVec_single_factors, hex0, henv0,
      embedUnitary_val, Submonoid.coe_mul, embedUnitary_val, embedUnitary_val,
      hzero_comp, embedMatrix_cast1nReg_mulVec_comp, ← mulVec_mulVec,
      embedMatrix_highBlock_mulVec_workMemState, permutationUnitary_mulVec_single,
      Equiv.swap_apply_left, embedMatrix_lowBlock_mulVec_workMemState]
    change (addrReg n 1).tensorState (workMemState (hadamardMatrix (n - p) *ᵥ single 0 1) (single
      (finCongr hm j) 1) ∘ cast1nEquiv hp) (single 0 1) = _
    rw [← groverMultiState_zero_eq_hadamard_mulVec (subcubeLocalSet hp hm R j)]
  have hsub0 : subcubeProdState (n := n) (fun _ : Fin m ↦ single 0 1) = single 0 1 := by
    have hex_g0 (c : Fin m) : (groupReg (n := n) hbg1 c).extractIndex 0 = 0 := by
      apply (basisBits (1 * (n + 1))).injective; funext r; simp [basisBits_extractIndex]
    funext w; unfold subcubeProdState; by_cases hw : w = 0
    · subst hw; simp [hex_g0]
    · rw [Pi.single_eq_of_ne hw]
      have hne : ∃ c : Fin m, (groupReg hbg1 c).extractIndex w ≠ 0 := by
        by_contra! hall
        apply hw; apply (groupSplitEquiv hbg1).injective; funext c
        rw [groupSplitEquiv_apply, groupSplitEquiv_apply, hall c, hex_g0 c]
      obtain ⟨c, hc⟩ := hne; exact Finset.prod_eq_zero (Finset.mem_univ c) (Pi.single_eq_of_ne hc 1)
  rw [workMemIdx, ← workMemState_single, embedMatrix_lowBlock_mulVec_workMemState, ← hsub0]
  have hcoe : (subcubePrepUnitary hp hm).1 = ((finRange m).map fun j ↦ (groupReg hbg1 j).embedMatrix
    (subcubeSlotPrep hp hm j).1).prod := by
    unfold subcubePrepUnitary; rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  unfold subcubeProdState
  rw [hcoe, prod_groupReg_embedMatrix_mulVec_het hbg1 _ (fun _ ↦ single 0 1)]; simp_rw [hprep_slot]
private lemma subcubeDiffuser_mulVec_sDiagM_subcubeProdState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^
    p) (R : Finset (Fin (2 ^ n))) (t : ℕ) : (subcubeDiffuserUnitary (m := m) hp).1 *ᵥ (sDiagM n m R
    *ᵥ subcubeProdState (subcubeSlotState hp hm R t)) = subcubeProdState (subcubeSlotState hp hm R
    (t + 1)) := by
  let hbg1 : m * 1 = m := Nat.mul_one m; have hdiff_coe : (subcubeDiffuserUnitary (m := m) hp).1 =
      ((finRange m).map fun j ↦ (groupReg hbg1 j).embedMatrix (subcubeSlotDiffuser hp).1).prod := by
    unfold subcubeDiffuserUnitary; rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  rw [sDiagM_eq_prod_groupReg hbg1 R]; unfold subcubeProdState
  rw [prod_groupReg_embedMatrix_mulVec_het hbg1]
  have hslot_p (j : Fin m) : sDiagM n 1 R *ᵥ subcubeSlotState hp hm R t j = (addrReg n
    1).tensorState (workMemState (oracleMat (subcubeLocalSet hp hm R j) *ᵥ groverMultiState
    (subcubeLocalSet hp hm R j) t) (single (finCongr hm j) 1) ∘ cast1nEquiv hp) (single 0 1) := by
    unfold subcubeSlotState
    rw [sDiagM_mulVec_tensorState_zero, oracleMat_oddSet_one_mulVec_subcube]
  simp_rw [hslot_p]; rw [hdiff_coe, prod_groupReg_embedMatrix_mulVec_het hbg1]
  have hslot_d (j : Fin m) : (subcubeSlotDiffuser hp).1 *ᵥ (addrReg n 1).tensorState (workMemState
    (oracleMat (subcubeLocalSet hp hm R j) *ᵥ groverMultiState (subcubeLocalSet hp hm R j) t)
    (single (finCongr hm j) 1) ∘ cast1nEquiv hp) (single 0 1) = subcubeSlotState hp hm R (t + 1)
    j := by
    unfold subcubeSlotDiffuser subcubeSlotState
    rw [embedUnitary_val, QRegister.embedMatrix_mulVec_tensorState, embedUnitary_val,
      embedMatrix_cast1nReg_mulVec_comp, embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      groverMultiState_succ]; rfl
  simp_rw [hslot_d]
private lemma permUnitary_parallelMarkPerm_mulVec_apply {n m : ℕ} (R : Finset (Fin (2 ^ n))) (ψ :
    Fin (2 ^ (m * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ((permutationUnitary
    (parallelMarkPerm n m R)).1 *ᵥ ψ) w = ψ (parallelMarkPerm n m R w) := by
  rw [Matrix.mulVec, dotProduct,
    sum_eq_single (parallelMarkPerm n m R w) (fun y hy ↦ by
      rw [permutationUnitary_apply,
        ite_eq_right (fun h ↦ hy (by
          have h2 := congrArg (parallelMarkPerm n m R) h; rw [parallelMarkPerm_involutive] at h2
          exact h2.symm)),
        zero_mul])]
  rw [permutationUnitary_apply, ite_eq_left (parallelMarkPerm_involutive R w).symm, one_mul]
private lemma krausLowBlock_mul_subcubeUnitaryPre_mulVec {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (K_sub : ℕ) (o : Fin (2 ^ (m * (n + 1)))) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (lowBlock (m * (n + 1)) (k * n)).embedMatrix (Matrix.single 0 o 1) *ᵥ
        (subcubeUnitaryPre hp hm S K_sub *ᵥ single (workMemIdx n m k 0 0) 1) =
      subcubeProdState (subcubeSlotState hp hm S K_sub) (parallelMarkPerm n m S o) •
        single (workMemIdx n m k 0 (writeMemBatch 0 (groupHits hbg1 o) 0)) 1 := by
  intro hbg1; let W := m * (n + 1); let M := k * n
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1; let orac := (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let phaseOp := fc * orac * fc
  let diffOp := (lowBlock W M).embedMatrix (subcubeDiffuserUnitary (m := m) hp).1
  have hphase_eq : phaseOp = (lowBlock W M).embedMatrix (sDiagM n m S) := by
    dsimp only [phaseOp, fc, orac]
    rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul, flagConj_mul_embed_mul_flagConj]
  have hiter (t : ℕ) : ((diffOp * phaseOp) ^ t) *ᵥ workMemState (subcubeProdState (subcubeSlotState
    hp hm S 0)) (single 0 1) = workMemState (subcubeProdState (subcubeSlotState hp hm S t)) (single
    0 1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, ← mulVec_mulVec, hphase_eq,
        embedMatrix_lowBlock_mulVec_workMemState, embedMatrix_lowBlock_mulVec_workMemState,
        subcubeDiffuser_mulVec_sDiagM_subcubeProdState]
  unfold subcubeUnitaryPre; dsimp only
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, subcubePrepUnitary_mulVec_workMemIdx hp hm
    S 0, hiter K_sub, embedMatrix_lowBlock_mulVec_workMemState,
    fullReg_embedUnitary_eq_permutationUnitary S, krausLowBlock_mulVec_memAddPerm,
    permUnitary_parallelMarkPerm_mulVec_apply]; rfl
private lemma map_filterMap_eq_filter {α β : Type*} (p : α → Option β) (g : β → α) (hg : ∀ a b, p a
    = some b → g b = a) (l : List α) : (l.filterMap p).map g = l.filter fun a ↦ (p a).isSome := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hpa : p a with
    | none => simp [List.filterMap_cons_none hpa, hpa, ih]
    | some b => simp [List.filterMap_cons_some hpa, hpa, hg a b hpa, ih]
private lemma filter_finRange_length_eq_card {m : ℕ} (P : Fin m → Bool) :
    ((finRange m).filter P).length = (Finset.univ.filter fun j ↦ P j = true).card := by
  have hnd : ((finRange m).filter P).Nodup := (List.nodup_finRange m).filter P
  rw [← List.toFinset_card_of_nodup hnd]; congr 1; ext j; simp
private lemma subcubeSlotState_support_hit {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (S : Finset
    (Fin (2 ^ n))) (K_sub : ℕ) (j : Fin m) (z : Fin (2 ^ (1 * (n + 1)))) (hz : subcubeSlotState hp
    hm S K_sub j z ≠ 0) : ((addrReg n 1).basisSplitEquiv z).2 = 0 ∧ ∀ x, firstMarkedAddr n 1
    (parallelMarkPerm n 1 S z) = some x → x ∈ S ∧ subcubePref hp hm x = j := by
  have hE : ((addrReg n 1).basisSplitEquiv z).2 = 0 := by
    by_contra hne
    apply hz; dsimp only [subcubeSlotState, tensorState]; rw [Pi.single_eq_of_ne hne, mul_zero]
  have hpref : (lowHighEquiv (n - p) p (cast1nEquiv hp ((addrReg n 1).extractIndex z))).2 =
      finCongr hm j := by
    by_contra hne
    apply hz; dsimp only [subcubeSlotState, tensorState, Function.comp_apply, workMemState]
    rw [Pi.single_eq_of_ne hne, mul_zero, zero_mul]
  refine ⟨hE, fun x hx ↦ ?_⟩
  rw [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit S z hE, firstTupleHit_one_eq] at hx
  split_ifs at hx with hmem
  cases hx
  have hsp := subcubeSplit_addrEquiv_one hp hm ((addrReg n 1).extractIndex z)
  rw [hpref, finCongr_symm_finCongr] at hsp; exact ⟨hmem, congrArg Prod.snd hsp⟩
private lemma subcubeSlot_normSq_sum_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (K_sub : ℕ) (j : Fin m) (bit : Bool) :
    let q := p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))
    (∑ z : Fin (2 ^ (1 * (n + 1))),
      if (firstMarkedAddr n 1 (parallelMarkPerm n 1 S z)).isSome = bit then
        (normSq (subcubeSlotState hp hm S K_sub j z) : ℂ)
      else 0) =
      ((match bit with | true => q | false => 1 - q : ℝ) : ℂ) := by
  intro q; let ξ := subcubeSlotState hp hm S K_sub j; let M_loc := subcubeLocalSet hp hm S j
  let term (z : Fin (2 ^ (1 * (n + 1)))) : ℂ :=
    if (firstMarkedAddr n 1 (parallelMarkPerm n 1 S z)).isSome = bit then (normSq (ξ z) : ℂ) else 0
  change ∑ z, term z = _; rw [← (addrReg n 1).basisSplitEquiv.symm.sum_comp term, sum_prod_type]
  have hinner (u : Fin (2 ^ (1 * n))) : (∑ e : (addrReg n 1).Environment → ZMod 2, term ((addrReg n
    1).basisSplitEquiv.symm (u, e))) = if (firstTupleHit n 1 S u).isSome = bit then (normSq
    ((workMemState (groverMultiState M_loc K_sub) (single (finCongr hm j) 1) ∘ cast1nEquiv hp) u) :
    ℂ) else 0 := by
    rw [sum_eq_single 0 (fun e he ↦ by
      dsimp only [term, ξ, subcubeSlotState, tensorState]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero,
        Complex.ofReal_zero, ite_self])]
    dsimp only [term, ξ, subcubeSlotState, tensorState]
    have hE : ((addrReg n 1).basisSplitEquiv
        ((addrReg n 1).basisSplitEquiv.symm (u, 0))).2 = 0 := by
      rw [Equiv.apply_symm_apply]
    have hex : (addrReg n 1).extractIndex ((addrReg n 1).basisSplitEquiv.symm (u, 0)) = u := by
      rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    rw [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit S _ hE, hex, hE,
      Pi.single_eq_same, mul_one]
  simp_rw [hinner]; rw [← (cast1nEquiv hp).symm.sum_comp]
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [← (lowHighEquiv (n - p) p).symm.sum_comp, sum_prod_type]
  have hprod_sum (w_loc : Fin (2 ^ (n - p))) : (∑ y : Fin (2 ^ p), if (firstTupleHit n 1 S
    ((cast1nEquiv hp).symm ((lowHighEquiv (n - p) p).symm (w_loc, y)))).isSome = bit then (normSq
    (workMemState (groverMultiState M_loc K_sub) (single (finCongr hm j) 1) ((lowHighEquiv (n - p)
    p).symm (w_loc, y))) : ℂ) else 0) = if (if w_loc ∈ M_loc then true else false) = bit then
    (normSq (groverMultiState M_loc K_sub w_loc) : ℂ) else 0 := by
    rw [sum_eq_single (finCongr hm j) (fun y hy ↦ by
      dsimp only [workMemState]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hy, mul_zero, Complex.normSq_zero,
        Complex.ofReal_zero, ite_self])]
    set u₀ := (cast1nEquiv hp).symm ((lowHighEquiv (n - p) p).symm (w_loc, finCongr hm j))
    have hsp := subcubeSplit_addrEquiv_one hp hm u₀
    simp only [u₀, Equiv.apply_symm_apply, finCongr_symm_finCongr] at hsp
    have hmem_iff : addrEquiv n 1 u₀ 0 ∈ S ↔ w_loc ∈ M_loc := by
      rw [mem_subcubeLocalSet_iff, ← hsp, Equiv.symm_apply_apply]
    have hisSome : (firstTupleHit n 1 S u₀).isSome = (if w_loc ∈ M_loc then true else false) := by
      rw [firstTupleHit_one_eq]; by_cases hw : w_loc ∈ M_loc
      · rw [ite_eq_left (hmem_iff.mpr hw), ite_eq_left hw]; rfl
      · rw [ite_eq_right (mt hmem_iff.mp hw), ite_eq_right hw]; rfl
    dsimp only [workMemState]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one, hisSome]
  simp_rw [hprod_sum, ← Finset.sum_filter, ← Complex.ofReal_sum]; congr 1; cases bit
  · have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M_loc)
      (fun w_loc ↦ normSq (groverMultiState M_loc K_sub w_loc))
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter,
      sum_mem_normSq_groverMultiState_eq_p_succ_frac, sum_normSq_groverMultiState_eq_one] at hpart
    have hfilt : (Finset.univ.filter fun w_loc ↦ (if w_loc ∈ M_loc then true else false) = false) =
        Finset.univ.filter (· ∉ M_loc) :=
      Finset.filter_congr fun w_loc _ ↦ by by_cases hw : w_loc ∈ M_loc <;> simp [hw]
    rw [hfilt]; dsimp only [q, M_loc] at hpart ⊢; linarith
  · have hfilt : (Finset.univ.filter fun w_loc ↦
        (if w_loc ∈ M_loc then true else false) = true) = M_loc := by
      ext w_loc; by_cases hw : w_loc ∈ M_loc <;> simp [hw]
    rw [hfilt, sum_mem_normSq_groverMultiState_eq_p_succ_frac]
private lemma sum_normSq_subcubeReadout_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (R : Finset
    (Fin (2 ^ n))) (K_sub : ℕ) (G : List (Fin (2 ^ n)) → ℂ) (H : (Fin m → Bool) → ℂ) (hGH : ∀ (hit :
    Fin m → Option (Fin (2 ^ n))), (∀ j x, hit j = some x → x ∈ R ∧ subcubePref hp hm x = j) →
    ((finRange m).filterMap hit).length = (Finset.univ.filter fun j ↦ (hit j).isSome = true).card →
    G ((finRange m).filterMap hit) = H (fun j ↦ (hit j).isSome)) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    let q : Fin m → ℝ := fun j ↦
      p_succ_frac K_sub (subcubeLocalSet hp hm R j).card (2 ^ (n - p))
    (∑ o : Fin (2 ^ (m * (n + 1))),
      (normSq (subcubeProdState (subcubeSlotState hp hm R K_sub)
        (parallelMarkPerm n m R o)) : ℂ) * G (groupHits hbg1 o)) =
      ∑ b : Fin m → Bool,
        ((∏ j : Fin m, match b j with | true => q j | false => 1 - q j : ℝ) : ℂ) * H b := by
  intro hbg1 q; let ξ := subcubeSlotState hp hm R K_sub
  let hitZ (z : Fin (2 ^ (1 * (n + 1)))) : Option (Fin (2 ^ n)) :=
    firstMarkedAddr n 1 (parallelMarkPerm n 1 R z)
  have h1 : (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (subcubeProdState ξ (parallelMarkPerm n m R o))
    : ℂ) * G (groupHits hbg1 o)) = ∑ w : Fin (2 ^ (m * (n + 1))), (normSq (subcubeProdState ξ w) :
    ℂ) * G (groupHits hbg1 (parallelMarkPerm n m R w)) := by
    rw [← Equiv.sum_comp (parallelMarkPerm n m R)]; refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [parallelMarkPerm_involutive]
  rw [h1, ← (groupSplitEquiv hbg1).symm.sum_comp]
  have h2 (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) : (normSq (subcubeProdState ξ ((groupSplitEquiv
    hbg1).symm zs)) : ℂ) * G (groupHits hbg1 (parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm
    zs))) = (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) * H (fun j ↦ (hitZ (zs j)).isSome) := by
    have hex (j : Fin m) :
        (groupReg hbg1 j).extractIndex ((groupSplitEquiv hbg1).symm zs) = zs j := by
      rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
    have hprod : (normSq (subcubeProdState ξ ((groupSplitEquiv hbg1).symm zs)) : ℂ) = ∏ j : Fin m,
      (normSq (ξ j (zs j)) : ℂ) := by
      unfold subcubeProdState; simp_rw [hex, map_prod, Complex.ofReal_prod]
    rw [hprod]; by_cases hzero : (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) = 0
    · rw [hzero, zero_mul, zero_mul]
    · have hnz (j : Fin m) : ξ j (zs j) ≠ 0 := by
        intro hj0; apply hzero; refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        rw [hj0, Complex.normSq_zero, Complex.ofReal_zero]
      have hhits : groupHits hbg1 (parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs)) =
        ((finRange m).filterMap (hitZ ∘ zs)).dedup := by
        unfold groupHits; congr 1; refine List.filterMap_congr fun j _ ↦ ?_
        rw [extractIndex_groupReg_parallelMarkPerm, hex]; rfl
      have hsupp (j : Fin m) (x : Fin (2 ^ n)) (hx : (hitZ ∘ zs) j = some x) : x ∈ R ∧ subcubePref
        hp hm x = j := (subcubeSlotState_support_hit hp hm R K_sub j (zs j) (hnz j)).2 x hx
      have hmap : (((finRange m).filterMap (hitZ ∘ zs)).map (subcubePref hp hm)) = (finRange
        m).filter fun j ↦ (hitZ (zs j)).isSome := map_filterMap_eq_filter (hitZ ∘ zs) (subcubePref
        hp hm) (fun j x hx ↦ (hsupp j x hx).2) (finRange m)
      have hnd_map : (((finRange m).filterMap (hitZ ∘ zs)).map (subcubePref hp hm)).Nodup := by
        rw [hmap]; exact (List.nodup_finRange m).filter _
      have hnd : ((finRange m).filterMap (hitZ ∘ zs)).Nodup := List.Nodup.of_map _ hnd_map
      have hlen : ((finRange m).filterMap (hitZ ∘ zs)).length = (Finset.univ.filter fun j : Fin m ↦
        (hitZ (zs j)).isSome = true).card := by
        rw [← List.length_map (f := subcubePref hp hm), hmap, filter_finRange_length_eq_card]
      rw [hhits, List.Nodup.dedup hnd, hGH (hitZ ∘ zs) hsupp hlen]; rfl
  simp_rw [h2]; symm; have hrhs (b : Fin m → Bool) :
      ((∏ j : Fin m, match b j with | true => q j | false => 1 - q j : ℝ) : ℂ) * H b =
        ∑ zs : Fin m → Fin (2 ^ (1 * (n + 1))),
          (∏ j : Fin m, if (hitZ (zs j)).isSome = b j then (normSq (ξ j (zs j)) : ℂ) else 0) *
            H b := by
    have hslot_b (j : Fin m) :
        ((match b j with | true => q j | false => 1 - q j : ℝ) : ℂ) =
          ∑ z : Fin (2 ^ (1 * (n + 1))),
            if (hitZ z).isSome = b j then (normSq (ξ j z) : ℂ) else 0 :=
      (subcubeSlot_normSq_sum_eq hp hm R K_sub j (b j)).symm
    rw [Complex.ofReal_prod]; simp_rw [hslot_b]; rw [Fintype.prod_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun b _ ↦ hrhs b).trans ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun zs _ ↦ ?_
  rw [sum_eq_single (fun j ↦ (hitZ (zs j)).isSome) (fun b hb ↦ ?_)]
  · simp only [ite_true]
  · obtain ⟨j, hj⟩ : ∃ j : Fin m, (hitZ (zs j)).isSome ≠ b j := by
      by_contra! hall
      exact hb (funext fun j ↦ (hall j).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj), zero_mul]
private lemma subcubeBernProd_eq_zero_of_gt {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (K_sub : ℕ)
    (b : Fin m → Bool) (hgt : k < (Finset.univ.filter fun j ↦ b j = true).card) :
    (∏ j : Fin m,
      match b j with
      | true => p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))
      | false => 1 - p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))) = 0 := by
  have hex : ∃ j₀ ∈ Finset.univ.filter (fun j ↦ b j = true),
      (subcubeLocalSet hp hm S j₀).card = 0 := by
    by_contra! hall
    have h1 : (Finset.univ.filter fun j ↦ b j = true).card ≤
        ∑ j ∈ Finset.univ.filter (fun j ↦ b j = true), (subcubeLocalSet hp hm S j).card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun j hj ↦ Nat.pos_iff_ne_zero.mpr (hall j hj)
    have h2 : (∑ j ∈ Finset.univ.filter (fun j ↦ b j = true), (subcubeLocalSet hp hm S j).card) ≤
        ∑ j : Fin m, (subcubeLocalSet hp hm S j).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [sum_card_subcubeLocalSet_eq hp hm S, hcard] at h2; omega
  obtain ⟨j₀, hj₀, hcard0⟩ := hex; have hbj : b j₀ = true := (Finset.mem_filter.mp hj₀).2
  refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
  rw [hbj, hcard0, p_succ_frac_zero_mid]
private lemma subcubeInitReadout_support_valid {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) {K_sub : ℕ}
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {o : Fin (2 ^ (m * (n + 1)))}
    (hamp : subcubeProdState (subcubeSlotState hp hm S K_sub) (parallelMarkPerm n m S o) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (groupHits hbg1 o).length ≤ k ∧ (batchNextCount hm1 hkN hbg1 0 o).val = (groupHits hbg1
      o).length ∧ MemPrefixValid S (groupHits hbg1 o).length (writeMemBatch 0 (groupHits hbg1 o) (0
      : Fin (2 ^ (k * n)))) := by
  intro hbg1; set w := parallelMarkPerm n m S o; have hflags (j : Fin m) :
      ((addrReg n 1).basisSplitEquiv ((groupReg hbg1 j).extractIndex w)).2 = 0 := by
    by_contra hj
    apply hamp; unfold subcubeProdState; refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    dsimp only [subcubeSlotState, tensorState]; rw [Pi.single_eq_of_ne hj, mul_zero]
  have hnew : ∀ x ∈ groupHits hbg1 o, x ∈ S \ memSeen n k (memPrefix k 0) 0 := by
    intro x hx; have ho : o = parallelMarkPerm n m S w := (parallelMarkPerm_involutive S o).symm
    rw [ho] at hx; have hxS : x ∈ S := mem_of_mem_groupHits_parallelMarkPerm hbg1 hflags hx
    have hemp : memSeen n k (memPrefix k 0) 0 = ∅ := (by ext y; simp [memSeen, memPrefix])
    rw [hemp]; exact Finset.mem_sdiff.mpr ⟨hxS, Finset.notMem_empty x⟩
  obtain ⟨hlen, hval'⟩ :=
    memPrefixValid_writeMemBatch hcard (memPrefixValid_zero S) (nodup_groupHits hbg1 o) hnew
  rw [zero_add] at hlen hval'; exact ⟨hlen, by simp [batchNextCount, Nat.min_eq_right hlen], hval'⟩
private lemma wp_qSet_subcubeInitRound_sum_eq {Var : Type} [DecidableEq Var] (res : Var) {n p m k :
    ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_sub : ℕ) (S : Finset (Fin (2
    ^ n))) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    ((wp (.qSet ;; (subcubeInitRound res hm1 hkN hp hm K_sub).compile qAssign
      (groverParallelMarkingOracle m S)) Θ) σ).1.1 = (∑ o : Fin (2 ^ (m * (n + 1))), (normSq
      (subcubeProdState (subcubeSlotState hp hm S K_sub) (parallelMarkPerm n m S o)) : ℂ) * (Θ
      (Store.subst σ res (Int.ofNat (batchNextCount hm1 hkN hbg1 0 o).val))).1.1 (workMemIdx n m k 0
      (writeMemBatch 0 (groupHits hbg1 o) 0)) (workMemIdx n m k 0 (writeMemBatch 0 (groupHits hbg1
      o) 0))) • (1 : Operator (2 ^ (m * (n + 1) + k * n))) := by
  intro hbg1; let W := m * (n + 1); let M := k * n
  let initProg := (subcubeInitRound (Var := Var) res hm1 hkN hp hm K_sub).compile qAssign
    (groverParallelMarkingOracle m S)
  rw [wp_qSeq, wp_qSet, qhlQSet_val]; congr 1; rw [← workMemIdx_zero n m k]
  let pref : OracleCirc Var (W + M) ((n + 1) * m) := .seq (.step (phaseTag ((lowBlock W
    M).embedUnitary (subcubePrepUnitary hp hm)))) (.seq (subcubeGroverLoop hp K_sub) (.seq (.oracle
    (workFullReg n m (W + M) (by omega))) (.step (phaseTag (permutationUnitary (memWriteBatchPerm (W
    := W) (n := n) (k := k) 0 (groupHits (n := n) hbg1)))))))
  let postReset := (setCountAndResetWork (Var := Var) (W := W) (M := M) (O := (n + 1) * m)
    res (batchNextCount hm1 hkN hbg1 0)).compile qAssign (groverParallelMarkingOracle m S)
  have hwp_eq : wp initProg Θ =
      wp (pref.compile qAssign (groverParallelMarkingOracle m S)) (wp postReset Θ) := by
    dsimp only [initProg, subcubeInitRound, pref, postReset, compile]; simp only [wp_qSeq]; rfl
  have hmat : ((wp initProg Θ) σ).1.1 = ∑ o : Fin (2 ^ W), ((lowBlock W M).embedMatrix
    (Matrix.single 0 o 1) * subcubeUnitaryPre hp hm S K_sub)ᴴ * (Θ (Store.subst σ res (Int.ofNat
    (batchNextCount hm1 hkN hbg1 0 o).val))).1.1 * ((lowBlock W M).embedMatrix (Matrix.single 0 o
    1) * subcubeUnitaryPre hp hm S K_sub) := by
    rw [hwp_eq, unitaryEffect_apply (unitaryEffect_subcubePrefix (Var := Var) hp hm S K_sub) (wp
      postReset Θ) σ, wp_setCountAndResetWork]
    exact (Matrix.sum_conjTranspose_mul_mul_mul Finset.univ _ _ _).symm
  rw [hmat]; refine (diag_eq_star_single_dotProduct_mulVec _ (workMemIdx n m k 0 0)).trans ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]; refine Finset.sum_congr rfl fun o _ ↦ ?_
  set K_op := (lowBlock W M).embedMatrix (Matrix.single 0 o 1) * subcubeUnitaryPre hp hm S K_sub
  set idx := workMemIdx n m k 0 0
  set idx' := workMemIdx n m k 0 (writeMemBatch 0 (groupHits hbg1 o) 0)
  set α := subcubeProdState (subcubeSlotState hp hm S K_sub) (parallelMarkPerm n m S o)
  have hKv : K_op *ᵥ single idx 1 = α • single idx' 1 := by
    dsimp only [K_op, idx, idx', α]; rw [← mulVec_mulVec]
    exact krausLowBlock_mul_subcubeUnitaryPre_mulVec hp hm S K_sub o
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star, hKv, Matrix.mulVec_smul, star_smul, smul_dotProduct,
    dotProduct_smul, ← diag_eq_star_single_dotProduct_mulVec _ idx', smul_eq_mul, smul_eq_mul, ←
    mul_assoc, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
/-- Exact invariant-preserving `wp` expectation of `.qSet;; subcubeInitRound`: transitions
  cleanly
  from `T = ∅` to occupancy `d = (Finset.univ.filter fun j ↦ b j = true).card` under the
  exact
  product-Bernoulli law across the `m` prefix subcubes. -/
theorem wp_qSet_subcubeInitRound_of_invariant {Var : Type} [DecidableEq Var] (res : Var) {n p m k :
    ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_sub : ℕ) {S : Finset (Fin (2
    ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (f : ℕ →
      ℝ) (hΘ :
    ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s
    μ → (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (f s : ℂ)) (σ : Store Var) :
    let q : Fin m → ℝ := fun j ↦
      p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))
    ((wp (.qSet ;;
        (subcubeInitRound res hm1 hkN hp hm K_sub).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
      ((∑ b : Fin m → Bool,
          (∏ j : Fin m, match b j with | true => q j | false => 1 - q j) *
            f (Finset.univ.filter fun j ↦ b j = true).card : ℝ) : ℂ) •
        (1 : Operator (2 ^ (m * (n + 1) + k * n))) := by
  intro q; let hbg1 : m * 1 = m := Nat.mul_one m
  rw [wp_qSet_subcubeInitRound_sum_eq res hm1 hkN hp hm K_sub S Θ σ]; congr 1
  have hterm (o : Fin (2 ^ (m * (n + 1)))) : (normSq (subcubeProdState (subcubeSlotState hp hm S
    K_sub) (parallelMarkPerm n m S o)) : ℂ) * (Θ (Store.subst σ res (Int.ofNat (batchNextCount hm1
    hkN hbg1 0 o).val))).1.1 (workMemIdx n m k 0 (writeMemBatch 0 (groupHits hbg1 o) 0)) (workMemIdx
    n m k 0 (writeMemBatch 0 (groupHits hbg1 o) 0)) = (normSq (subcubeProdState (subcubeSlotState hp
    hm S K_sub) (parallelMarkPerm n m S o)) : ℂ) * (f (groupHits hbg1 o).length : ℂ) := by
    set α := subcubeProdState (subcubeSlotState hp hm S K_sub) (parallelMarkPerm n m S o)
    by_cases hα : α = 0
    · rw [hα, Complex.normSq_zero, Complex.ofReal_zero, zero_mul, zero_mul]
    · obtain ⟨hlen, hcnt, hval'⟩ := subcubeInitReadout_support_valid hm1 hkN hp hm hcard hα
      rw [hcnt, hΘ (groupHits hbg1 o).length _ _ hlen (by simp) hval']
  simp_rw [hterm]
  rw [sum_normSq_subcubeReadout_eq hp hm S K_sub (fun L ↦ (f L.length : ℂ)) (fun b ↦ (f
    (Finset.univ.filter fun j ↦ b j = true).card : ℂ)) (fun _ _ hlen ↦ by rw [hlen]),
    Complex.ofReal_sum]; exact Finset.sum_congr rfl fun b _ ↦ (Complex.ofReal_mul _ _).symm
/- ## Hybrid Composition (`subcubeBatchWithLast`) -/
/-- Hybrid `S`-free circuit (`m > k`): runs 1 coherent variable-`Φ` prefix-subcube pre-sweep
  at `T = ∅` (`subcubeInitRound`) and pipes the resulting `(memReg, res)` state directly
  into
  `findAllBatchTail` (`s < k - 1` multi-harvest loop + `s = k - 1` `lastStage`). -/
noncomputable def subcubeBatchWithLast {Var : Type} (res : Var) {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k
    ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) {b g : ℕ → ℕ} (hbg : ∀ s < k, b s * g s = m) (K_sub : ℕ)
    (K : ℕ → ℕ) (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) : OracleCirc Var
    (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (subcubeInitRound res hm1 hkN hp hm K_sub)
    (findAllBatchTail res hm1 hkN hbg K lastStage)
private noncomputable def subcubeOccLaw {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (K_sub : ℕ) (s : ℕ) : ℝ :=
  ∑ b : Fin m → Bool with (Finset.univ.filter fun j ↦ b j = true).card = s,
    ∏ j : Fin m,
      match b j with
      | true => p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))
      | false => 1 - p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))
private lemma subcubeOccLaw_props {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (K_sub : ℕ) :
    (∀ s ≤ k, 0 ≤ subcubeOccLaw hp hm S K_sub s) ∧
      (∑ s ∈ Finset.range (k + 1), subcubeOccLaw hp hm S K_sub s) = 1 ∧
      ∀ f : ℕ → ℝ,
        (∑ s ∈ Finset.range (k + 1), subcubeOccLaw hp hm S K_sub s * f s) =
          ∑ b : Fin m → Bool,
            (∏ j : Fin m,
              match b j with
              | true => p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))
              | false => 1 - p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))) *
              f (Finset.univ.filter fun j ↦ b j = true).card := by
  let q (j : Fin m) : ℝ := p_succ_frac K_sub (subcubeLocalSet hp hm S j).card (2 ^ (n - p))
  let wt (b : Fin m → Bool) : ℝ :=
    ∏ j : Fin m, match b j with | true => q j | false => 1 - q j
  have hwt_nonneg (b : Fin m → Bool) : 0 ≤ wt b := by
    refine Finset.prod_nonneg fun j _ ↦ ?_
    cases b j
    · exact sub_nonneg.mpr (Real.sin_sq_le_one _)
    · exact sq_nonneg _
  have hsum_f (f : ℕ → ℝ) : (∑ s ∈ Finset.range (k + 1), subcubeOccLaw hp hm S K_sub s * f s) = ∑ b
    : Fin m → Bool, wt b * f (Finset.univ.filter fun j ↦ b j = true).card := by
    unfold subcubeOccLaw
    change (∑ s ∈ Finset.range (k + 1),
        (∑ b : Fin m → Bool with (Finset.univ.filter fun j ↦ b j = true).card = s, wt b) * f s) = _
    simp_rw [Finset.sum_mul]; have hcongr (s : ℕ) :
        (∑ b : Fin m → Bool with (Finset.univ.filter fun j ↦ b j = true).card = s, wt b * f s) =
        ∑ b : Fin m → Bool with (Finset.univ.filter fun j ↦ b j = true).card = s,
          wt b * f (Finset.univ.filter fun j ↦ b j = true).card :=
      Finset.sum_congr rfl fun b hb ↦ by rw [(Finset.mem_filter.mp hb).2]
    simp_rw [hcongr]
    rw [← Finset.sum_biUnion (fun s₁ _ s₂ _ hne ↦ Finset.disjoint_left.mpr fun b hb₁ hb₂ ↦
      hne ((Finset.mem_filter.mp hb₁).2.symm.trans (Finset.mem_filter.mp hb₂).2))]
    refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb_not ↦ ?_
    have hgt : k < (Finset.univ.filter fun j ↦ b j = true).card := by
      by_contra! hle
      exact hb_not (Finset.mem_biUnion.mpr ⟨(Finset.univ.filter fun j ↦ b j = true).card,
        Finset.mem_range.mpr (Nat.lt_succ_of_le hle), Finset.mem_filter.mpr ⟨Finset.mem_univ b,
        rfl⟩⟩)
    have hz : wt b = 0 := subcubeBernProd_eq_zero_of_gt hp hm hcard K_sub b hgt; rw [hz, zero_mul]
  refine ⟨fun s _ ↦ Finset.sum_nonneg fun b _ ↦ hwt_nonneg b, ?_, hsum_f⟩
  have h1 := hsum_f fun _ ↦ 1; simp_rw [mul_one] at h1; rw [h1]
  have hprod_one : (∑ b : Fin m → Bool, wt b) =
      ∏ j : Fin m, ∑ bit : Bool, match bit with | true => q j | false => 1 - q j :=
    (Fintype.prod_sum fun j bit ↦ match bit with | true => q j | false => 1 - q j).symm
  rw [hprod_one]; refine Finset.prod_eq_one fun j _ ↦ ?_
  rw [Fintype.sum_bool]; ring
/-- Total correctness (`wp = ⊤`) of `.qSet;; subcubeBatchWithLast` (`1 ≤ k`) for any `K_sub:
  ℕ`
  whenever every remaining batch occupancy `s < k - 1` has `1 ≤ b s` and
  `0 < groupSuccProb n (g s) (k - s) (K s)` and `lastStage` satisfies `hlast_wp`. -/
theorem wp_subcubeBatchWithLast_eq_top {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hm1
    : 1 ≤ m) (hk : 1 ≤ k) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) {b g : ℕ → ℕ} (hbg : ∀ s <
    k, b s * g s = m) (hb : ∀ s < k - 1, 1 ≤ b s) (K_sub : ℕ) (K : ℕ → ℕ) (lastStage : OracleCirc
    Var (m * (n + 1) + k * n) ((n + 1) * m)) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (hpos :
    ∀ s < k - 1, 0 < groupSuccProb n (g s) (k - s) (K s)) (hlast_wp : ∀ (τ : Store Var) (μ : Fin (2
    ^ (k * n))), τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ → ((wp (lastStage.compile
    qAssign (groverParallelMarkingOracle m S)) (wp (measureRegister res (highBlock (m * (n + 1))
    (k * n))) (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S))) τ).1.1 (workMemIdx n m k 0 μ)
    (workMemIdx n m k 0 μ) = 1) : wp (.qSet ;; (subcubeBatchWithLast res hm1 hkN hp hm hbg K_sub K
    lastStage).compile qAssign (groverParallelMarkingOracle m S)) (liftPureProp fun σ ↦
    decodeTargets n k (σ res) = S) = ⊤ := by
  rcases subcubeOccLaw_props hp hm hcard K_sub with ⟨hP_nn, hP_sum, hP_f⟩
  refine wp_init_seq_findAllBatchTail_eq_top res hm1 hk hkN hbg hb K
    (subcubeInitRound res hm1 hkN hp hm K_sub) lastStage hcard
    (subcubeOccLaw hp hm S K_sub) hP_nn hP_sum (fun Θ f hΘ σ ↦ ?_) hpos hlast_wp
  rw [wp_qSet_subcubeInitRound_of_invariant res hm1 hkN hp hm K_sub hcard Θ f hΘ σ, hP_f f]
private noncomputable def subcubeDeflatedGroverStep {Var : Type} {n p m k : ℕ} (hp : p ≤ n) (active
    : ℕ) : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k active))
    (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
      (subcubeDiffuserUnitary (m := m) hp))))
private noncomputable def subcubeDeflatedGroverLoop {Var : Type} {n p m k : ℕ} (hp : p ≤ n) (active
    K_sub : ℕ) : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  OracleDynamicCircuit.sequence (List.replicate K_sub (subcubeDeflatedGroverStep hp active))
/-- Coherent deflated prefix-subcube round at known occupancy `active` (`K_sub + 1` parallel
  oracle
  calls, `0` extra ancillas): deflates the `active` prefix slots of `memReg`, runs `K_sub`
  local
  subcube Grover iterations on `S \ memSeen`, appends distinct new subcube hits starting at
  slot
  `active`, and updates `res` while resetting `workReg` to `|0⟩`. -/
noncomputable def subcubeDeflatedRound {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (active K_sub : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  let hbg1 : m * 1 = m := Nat.mul_one m
  .seq (.step (phaseTag ((lowBlock W M).embedUnitary (subcubePrepUnitary hp hm))))
    (.seq (subcubeDeflatedGroverLoop hp active K_sub)
      (.seq (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active))
        (.seq (.step (phaseTag (permutationUnitary (memWriteBatchPerm active (groupHits hbg1)))))
          (setCountAndResetWork res (batchNextCount hm1 hkN hbg1 active)))))
/-- Classical `res`-dispatched Sweep 2 over `0 ≤ active < k` (`.skip` when Sweep 1 already
  found
  all `k` targets), costing at most `K_sub2 + 1` parallel oracle calls (`CostBound.qIf`). -/
noncomputable def subcubeSecondSweep {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_sub2 : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  dispFin res (fun s : Fin k ↦ subcubeDeflatedRound res hm1 hkN hp hm s.val K_sub2) (finRange k)
private noncomputable def subcubeDeflatedUnitaryPre {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (S :
    Finset (Fin (2 ^ n))) (active K_sub : ℕ) : Operator (2 ^ (m * (n + 1) + k * n)) :=
  let W := m * (n + 1)
  let M := k * n
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1
  let orac := (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (lowBlock W M).embedMatrix (subcubeDiffuserUnitary (m := m) hp).1
  let readOp := unm * orac
  let prepOp := (lowBlock W M).embedMatrix (subcubePrepUnitary hp hm).1
  let writeOp := (permutationUnitary
    (memWriteBatchPerm (W := W) (n := n) (k := k) active (groupHits (n := n) (Nat.mul_one m)))).1
  writeOp * readOp * ((diffOp * phaseOp) ^ K_sub) * prepOp
private lemma unitaryEffect_subcubeDeflatedPrefix {Var : Type} [DecidableEq Var] {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (S : Finset (Fin (2 ^ n))) (active K_sub : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let pref : OracleCirc Var (W + M) ((n + 1) * m) :=
      .seq (.step (phaseTag ((lowBlock W M).embedUnitary (subcubePrepUnitary hp hm)))) (.seq
        (subcubeDeflatedGroverLoop hp active K_sub) (.seq (deflatedOracle (m := m) (k := k) le_rfl
        (memPrefix k active)) (.step (phaseTag (permutationUnitary (memWriteBatchPerm (W := W) (n :=
        n) (k := k) active (groupHits (n := n) (Nat.mul_one m))))))))
    UnitaryEffect (pref.compile qAssign (groverParallelMarkingOracle m S))
      (subcubeDeflatedUnitaryPre hp hm S active K_sub) := by
  intro W M pref
  have hwwhole : workMemReg n m k (W + M) le_rfl = QRegister.whole (W + M) := by
    ext i
    simp [workMemReg]
    rfl
  have hwlow : workReg n m (W + M) (by omega) = lowBlock W M := rfl
  have hread : UnitaryEffect ((deflatedOracle (Var := Var) (m := m) (k := k) le_rfl (memPrefix k
    active)).compile qAssign (groverParallelMarkingOracle m S)) ((permutationUnitary (unmarkPerm n m
    k (memPrefix k active))).1 * (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary
    (groverParallelMarkingOracle m S)).1) := by
    unfold deflatedOracle
    dsimp only [compile]
    rw [hwwhole, QRegister.whole_embedUnitary]
    have h1 := unitaryEffect_qAssign (Var := Var)
      ((workFullReg n m (W + M) (by omega)).embedUnitary (groverParallelMarkingOracle m S))
    rw [workFullReg_embedUnitary_eq] at h1
    exact unitaryEffect_seq h1 (unitaryEffect_phaseTag _)
  have hphase : UnitaryEffect ((deflatedPhaseStep (Var := Var) (m := m) (k := k) le_rfl (memPrefix k
    active)).compile qAssign (groverParallelMarkingOracle m S)) ((lowBlock W M).embedMatrix
    (flagConj n m).1 * (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1 * (lowBlock W
    M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 * (lowBlock W
    M).embedMatrix (flagConj n m).1) := by
    unfold deflatedPhaseStep
    dsimp only [compile]
    rw [hwlow]
    have hfc := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (flagConj n m))
    rw [embedUnitary_val] at hfc
    simpa only [Matrix.mul_assoc] using unitaryEffect_seq hfc (unitaryEffect_seq hread hfc)
  have hloop (t : ℕ) : UnitaryEffect ((subcubeDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp
    active t).compile qAssign (groverParallelMarkingOracle m S)) (((lowBlock W M).embedMatrix
    (subcubeDiffuserUnitary (m := m) hp).1 * ((lowBlock W M).embedMatrix (flagConj n m).1 *
    (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1 * (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 * (lowBlock W M).embedMatrix
    (flagConj n m).1)) ^ t) := by
    unfold subcubeDeflatedGroverLoop
    induction t with
    | zero => simpa using unitaryEffect_skip (Var := Var) (d := 2 ^ (W + M))
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold subcubeDeflatedGroverStep; dsimp only [compile]
      have hdiff := unitaryEffect_phaseTag (Var := Var)
        ((lowBlock W M).embedUnitary (subcubeDiffuserUnitary (m := m) hp))
      rw [embedUnitary_val] at hdiff; rw [pow_succ]
      exact unitaryEffect_seq (unitaryEffect_seq hphase hdiff) ih
  dsimp only [pref, compile]; have hprep := unitaryEffect_phaseTag (Var := Var)
    ((lowBlock W M).embedUnitary (subcubePrepUnitary hp hm))
  rw [embedUnitary_val] at hprep
  have hwrite := unitaryEffect_phaseTag (Var := Var) (permutationUnitary (memWriteBatchPerm (W := W)
    (n := n) (k := k) active (groupHits (n := n) (Nat.mul_one m))))
  unfold subcubeDeflatedUnitaryPre; dsimp only; simpa only [Matrix.mul_assoc] using
    unitaryEffect_seq hprep (unitaryEffect_seq (hloop K_sub) (unitaryEffect_seq hread hwrite))
private lemma krausLowBlock_mul_subcubeDeflatedUnitaryPre_mulVec {n p m k : ℕ} (hp : p ≤ n) (hm : m
    = 2 ^ p) {S : Finset (Fin (2 ^ n))} {active : ℕ} (K_sub : ℕ) {μ : Fin (2 ^ (k * n))} (hsub :
    memSeen n k (memPrefix k active) μ ⊆ S) (o : Fin (2 ^ (m * (n + 1)))) :
    let hbg1 : m * 1 = m := Nat.mul_one m; let R := S \ memSeen n k (memPrefix k active) μ
    (lowBlock (m * (n + 1)) (k * n)).embedMatrix (Matrix.single 0 o 1) *ᵥ
        (subcubeDeflatedUnitaryPre hp hm S active K_sub *ᵥ single (workMemIdx n m k 0 μ) 1) =
      subcubeProdState (subcubeSlotState hp hm R K_sub) (parallelMarkPerm n m R o) •
        single (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg1 o) μ)) 1 := by
  intro hbg1 R; let W := m * (n + 1); let M := k * n
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1; let orac := (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (lowBlock W M).embedMatrix (subcubeDiffuserUnitary (m := m) hp).1
  have hiter (t : ℕ) : ((diffOp * phaseOp) ^ t) *ᵥ workMemState (subcubeProdState (subcubeSlotState
    hp hm R 0)) (single μ 1) = workMemState (subcubeProdState (subcubeSlotState hp hm R t)) (single
    μ 1) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, ← mulVec_mulVec, deflatedPhaseMat_mulVec_workMemState
        (memPrefix k active) _ μ hsub, show S \ memSeen n k (memPrefix k active) μ = R from rfl,
        embedMatrix_lowBlock_mulVec_workMemState, subcubeDiffuser_mulVec_sDiagM_subcubeProdState]
  unfold subcubeDeflatedUnitaryPre; dsimp only
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, subcubePrepUnitary_mulVec_workMemIdx hp hm
    R μ, hiter K_sub, ← mulVec_mulVec _ unm orac, unmark_mul_parallelOracle_workMemState (memPrefix
    k active) _ μ hsub, show S \ memSeen n k (memPrefix k active) μ = R from rfl,
    fullReg_embedUnitary_eq_permutationUnitary R, krausLowBlock_mulVec_memAddPerm,
    permUnitary_parallelMarkPerm_mulVec_apply]; rfl
private lemma wp_dispFin_subcube_of_lt {Var : Type} [DecidableEq Var] (res : Var) {k Q O : ℕ} (br :
    Fin k → OracleCirc Var Q O) (oracle : Unitary (2 ^ O)) (Θ : CQAssertion (Store Var) (2 ^ Q)) {s
      : ℕ} (hs
    : s < k) {τ : Store Var} (hτ : τ res = (s : ℤ)) : wp ((dispFin res br (finRange k)).compile
    qAssign oracle) Θ τ = wp ((br ⟨s, hs⟩).compile qAssign oracle) Θ τ := by
  set s₀ : Fin k := ⟨s, hs⟩; have hmem : s₀ ∈ finRange k := mem_finRange s₀
  generalize finRange k = l at hmem
  induction l with
  | nil => cases hmem
  | cons x _ ih =>
    simp only [dispFin, compile, wp]; by_cases h : s₀ = x
    · subst h; simp [hτ, s₀]
    · have hne : τ res ≠ (x.val : ℤ) := fun heq ↦ h (Fin.ext (Int.ofNat.inj (hτ.symm.trans heq)))
      simp only [hne, ↓reduceIte]; exact ih (List.mem_of_ne_of_mem h hmem)
private lemma wp_dispFin_subcube_of_ge {Var : Type} [DecidableEq Var] (res : Var) {k Q O : ℕ} (br :
    Fin k → OracleCirc Var Q O) (oracle : Unitary (2 ^ O)) (Θ : CQAssertion (Store Var) (2 ^ Q)) {s
      : ℕ} (hs
    : k ≤ s) {τ : Store Var} (hτ : τ res = (s : ℤ)) : wp ((dispFin res br (finRange k)).compile
    qAssign oracle) Θ τ = Θ τ := by
  suffices ∀ l : List (Fin k),
      wp ((dispFin res br l).compile qAssign oracle) Θ τ = Θ τ from this (finRange k)
  intro l
  induction l with
  | nil => simp [dispFin]
  | cons x rest ih =>
    simp only [dispFin, compile, wp]
    have hne : τ res ≠ (x.val : ℤ) := (by rw [hτ]; have hx := x.isLt; omega)
    simp only [hne, ↓reduceIte]; exact ih
private lemma memSeen_writeMemBatch_zero {n k : ℕ} (L : List (Fin (2 ^ n))) (hlen : L.length ≤ k) :
    memSeen n k (memPrefix k L.length) (writeMemBatch 0 L 0) = L.toFinset := by
  have h0 : addrEquiv n k (0 : Fin (2 ^ (k * n))) = 0 := by
    funext i; exact (memPrefixValid_zero (∅ : Finset (Fin (2 ^ n)))).2.2.2 i (Nat.zero_le _)
  have hslot (i : Fin k) (hi : i.val < L.length) :
      addrEquiv n k (writeMemBatch 0 L 0) i = L[i.val]'hi := by
    unfold writeMemBatch; rw [Equiv.apply_symm_apply, h0, zero_add, ite_eq_left (Nat.zero_le _)]
    simp [List.getElem?_eq_getElem hi]
  ext x
  simp only [memSeen, memPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hslot i hi]; exact List.getElem_mem hi
  · intro hx; obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hx
    refine ⟨⟨a, lt_of_lt_of_le ha hlen⟩, ha, ?_⟩
    exact hslot ⟨a, lt_of_lt_of_le ha hlen⟩ ha
private lemma card_subcubeLocalSet_sdiff_filterMap {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (S :
    Finset (Fin (2 ^ n))) (hit : Fin m → Option (Fin (2 ^ n))) (hhit : ∀ j x, hit j = some x → x ∈ S
    ∧ subcubePref hp hm x = j) (j : Fin m) : (subcubeLocalSet hp hm (S \ ((finRange m).filterMap
    hit).toFinset) j).card = if (hit j).isSome then (subcubeLocalSet hp hm S j).card - 1 else
    (subcubeLocalSet hp hm S j).card := by
  set T : Finset (Fin (2 ^ n)) := ((finRange m).filterMap hit).toFinset
  have hmemT (x : Fin (2 ^ n)) (hxj : subcubePref hp hm x = j) : x ∈ T ↔ hit j = some x := by
    simp only [T, List.mem_toFinset, List.mem_filterMap, mem_finRange, true_and]; constructor
    · rintro ⟨j', hj'⟩
      have heq : j' = j := (hhit j' x hj').2.symm.trans hxj; rwa [heq] at hj'
    · exact fun h ↦ ⟨j, h⟩
  rw [card_subcubeLocalSet_eq hp hm (S \ T) j, card_subcubeLocalSet_eq hp hm S j]
  set F := S.filter fun x ↦ subcubePref hp hm x = j
  cases hhj : hit j with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; congr 1; ext x
    simp only [F, Finset.mem_filter, Finset.mem_sdiff]; constructor
    · exact fun ⟨⟨hxS, _⟩, hxj⟩ ↦ ⟨hxS, hxj⟩
    · intro ⟨hxS, hxj⟩; refine ⟨⟨hxS, ?_⟩, hxj⟩
      rw [hmemT x hxj, hhj]
      rintro ⟨⟩
  | some x₀ =>
    simp only [Option.isSome_some, ↓reduceIte]
    have hx₀ : x₀ ∈ F := Finset.mem_filter.mpr (hhit j x₀ hhj)
    have hfeq : ((S \ T).filter fun x ↦ subcubePref hp hm x = j) = F.erase x₀ := by
      ext x; simp only [F, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]; constructor
      · rintro ⟨⟨hxS, hxT⟩, hxj⟩
        refine ⟨?_, hxS, hxj⟩
        rintro rfl
        exact hxT ((hmemT x hxj).mpr hhj)
      · rintro ⟨hne, hxS, hxj⟩
        refine ⟨⟨hxS, ?_⟩, hxj⟩
        rw [hmemT x hxj, hhj]; exact fun h ↦ hne (Option.some.inj h).symm
    rw [hfeq, Finset.card_erase_of_mem hx₀]
end
/-
 ## Multi-Sweep Coherent Prefix-Subcube Pre-Pass (`ks: List ℕ`) & 1D Per-Subcube Potentials
Implements an arbitrary list `K_init:: ks` of coherent prefix-subcube sweeps
(`subcubeExtraSweeps`, `subcubeMultiSweepBatchWithLast`) on the same `(m * (n + 1) + k *
n)`-qubit
workspace (`0` extra ancilla qubits), together with exact `1D` per-subcube sum and product
factorizations (`subcubeOneDimExp`, `subcubeSweepsExp_sum_eq`, `subcubeSweepsExp_prod_eq`).
-/
public section
/-- Sequence of deflated prefix-subcube sweeps (`subcubeSecondSweep`) for `ks: List ℕ`. -/
noncomputable def subcubeExtraSweeps {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) :
    List ℕ → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | K_sub :: ks =>
      .seq (subcubeSecondSweep res hm1 hkN hp hm K_sub)
        (subcubeExtraSweeps res hm1 hkN hp hm ks)
/-- Multi-sweep coherent prefix-subcube pre-pass: runs `subcubeInitRound... K_init` (`T =
  ∅`)
  followed by `subcubeExtraSweeps... ks` (`memReg`-deflated sweeps). -/
noncomputable def subcubeMultiSweepPre {Var : Type} (res : Var) {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN : k
    ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_init : ℕ) (ks : List ℕ) : OracleCirc Var (m * (n +
    1) + k * n) ((n + 1) * m) :=
  .seq (subcubeInitRound res hm1 hkN hp hm K_init)
    (subcubeExtraSweeps res hm1 hkN hp hm ks)
/-- Multi-sweep `S`-free hybrid circuit (`m ≥ k` or `m = 2 ^ p`): runs `K_init:: ks`
  coherent
  prefix-subcube sweeps (`subcubeMultiSweepPre`) and pipes `(memReg, res)` into
  `findAllBatchTail`. -/
noncomputable def subcubeMultiSweepBatchWithLast {Var : Type} (res : Var) {n p m k : ℕ} (hm1 : 1 ≤
    m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) {b g : ℕ → ℕ} (hbg : ∀ s < k, b s * g s = m)
    (K_init : ℕ) (ks : List ℕ) (K : ℕ → ℕ) (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n +
    1) * m)) : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (subcubeMultiSweepPre res hm1 hkN hp hm K_init ks)
    (findAllBatchTail res hm1 hkN hbg K lastStage)
private lemma memSeen_writeMemBatch {n k active : ℕ} {S : Finset (Fin (2 ^ n))} {μ : Fin (2 ^ (k *
    n))} (hval : MemPrefixValid S active μ) (L : List (Fin (2 ^ n))) (hlen : active + L.length ≤ k)
    : memSeen n k (memPrefix k (active + L.length)) (writeMemBatch active L μ) = memSeen n k
    (memPrefix k active) μ ∪ L.toFinset := by
  have hslot_lt (i : Fin k) (hi : i.val < active) :
      addrEquiv n k (writeMemBatch active L μ) i = addrEquiv n k μ i := by
    unfold writeMemBatch
    rw [Equiv.apply_symm_apply, Pi.add_apply, ite_eq_right (not_le_of_gt hi), add_zero]
  have hslot_ge (i : Fin k) (hge : active ≤ i.val) (hlt : i.val < active + L.length) :
      addrEquiv n k (writeMemBatch active L μ) i = L[i.val - active]'(by omega) := by
    unfold writeMemBatch; have hzero : addrEquiv n k μ i = 0 := hval.2.2.2 i hge
    have hsub : i.val - active < L.length := (by omega)
    rw [Equiv.apply_symm_apply, Pi.add_apply, hzero, zero_add, ite_eq_left hge]
    simp [List.getElem?_eq_getElem hsub]
  ext x
  simp only [memSeen, memPrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases lt_or_ge i.val active with hlt | hge
    · left; exact ⟨i, hlt, (hslot_lt i hlt).symm⟩
    · right; rw [hslot_ge i hge hi]; exact List.getElem_mem _
  · rintro (⟨i, hi, rfl⟩ | hxL)
    · refine ⟨i, by omega, hslot_lt i hi⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hxL; let idx : Fin k := ⟨active + a, by omega⟩
      refine ⟨idx, by dsimp [idx]; omega, ?_⟩
      have hge : active ≤ idx.val := (by dsimp [idx]; omega)
      have hlt : idx.val < active + L.length := (by dsimp [idx]; omega); rw [hslot_ge idx hge hlt]
      simp [idx]
/-- Per-subcube count of remaining undiscovered targets in `S \ memSeen` at prefix `s`. -/
noncomputable def subcubeRemVec {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (s : ℕ) (μ : Fin (2 ^ (k * n))) : Fin m → ℕ :=
  fun j ↦ (subcubeLocalSet hp hm (S \ memSeen n k (memPrefix k s) μ) j).card
private lemma sum_subcubeRemVec_eq {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) {S : Finset (Fin (2 ^
    n))} (hcard : S.card = k) {s : ℕ} {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s μ) : (∑ j :
    Fin m, subcubeRemVec hp hm S s μ j) = k - s := by
  unfold subcubeRemVec; rw [sum_card_subcubeLocalSet_eq hp hm]
  have hseen := card_memSeen_of_memPrefixValid hval
  have hadd := Finset.card_sdiff_add_card_eq_card hseen.2; omega
private lemma wp_subcubeDeflatedRound_of_remVec {Var : Type} [DecidableEq Var] (res : Var) {n p m k
    : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (active K_sub : ℕ) {S :
    Finset (Fin (2 ^ n))} (hcard : S.card = k) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S
    active μ) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (F : (Fin m → ℕ) → ℝ) (hΘ :
      ∀ (s :
    ℕ) (τ : Store Var) (μ' : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ' →
    (Θ τ).1.1 (workMemIdx n m k 0 μ') (workMemIdx n m k 0 μ') = (F (subcubeRemVec hp hm S s μ') :
    ℂ)) (σ : Store Var) : ((wp ((subcubeDeflatedRound res hm1 hkN hp hm active K_sub).compile
    qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0
    μ) = (subcubeStepExp (2 ^ (n - p)) K_sub F (subcubeRemVec hp hm S active μ) : ℂ) := by
  let R := S \ memSeen n k (memPrefix k active) μ; let W := m * (n + 1); let M := k * n
  let hbg1 : m * 1 = m := Nat.mul_one m
  let pref : OracleCirc Var (W + M) ((n + 1) * m) := .seq (.step (phaseTag ((lowBlock W
    M).embedUnitary (subcubePrepUnitary hp hm)))) (.seq (subcubeDeflatedGroverLoop hp active K_sub)
    (.seq (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active)) (.step (phaseTag
    (permutationUnitary (memWriteBatchPerm (W := W) (n := n) (k := k) active (groupHits (n := n)
    hbg1)))))))
  let postReset := (setCountAndResetWork (Var := Var) (W := W) (M := M) (O := (n + 1) * m)
    res (batchNextCount hm1 hkN hbg1 active)).compile qAssign (groverParallelMarkingOracle m S)
  have hwp_eq : wp ((subcubeDeflatedRound (Var := Var) res hm1 hkN hp hm active K_sub).compile
    qAssign (groverParallelMarkingOracle m S)) Θ = wp (pref.compile qAssign
    (groverParallelMarkingOracle m S)) (wp postReset Θ) := by
    unfold subcubeDeflatedRound; dsimp only [pref, postReset, compile]; simp only [wp_qSeq]; rfl
  have hmat : ((wp ((subcubeDeflatedRound res hm1 hkN hp hm active K_sub).compile qAssign
    (groverParallelMarkingOracle m S)) Θ) σ).1.1 = ∑ o : Fin (2 ^ W), ((lowBlock W M).embedMatrix
    (Matrix.single 0 o 1) * subcubeDeflatedUnitaryPre hp hm S active K_sub)ᴴ * (Θ (Store.subst σ res
    (Int.ofNat (batchNextCount hm1 hkN hbg1 active o).val))).1.1 * ((lowBlock W M).embedMatrix
    (Matrix.single 0 o 1) * subcubeDeflatedUnitaryPre hp hm S active K_sub) := by
    rw [hwp_eq, unitaryEffect_apply (unitaryEffect_subcubeDeflatedPrefix (Var := Var) hp hm S active
      K_sub) (wp postReset Θ) σ, wp_setCountAndResetWork]
    exact (Matrix.sum_conjTranspose_mul_mul_mul Finset.univ _ _ _).symm
  rw [hmat]; refine (diag_eq_star_single_dotProduct_mulVec _ (workMemIdx n m k 0 μ)).trans ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]; have hsub := (card_memSeen_of_memPrefixValid hval).2
  let gList : List (Fin (2 ^ n)) → ℂ := fun L ↦
    (F (fun j ↦ (subcubeLocalSet hp hm (R \ L.toFinset) j).card) : ℂ)
  let hBool : (Fin m → Bool) → ℂ := fun b ↦ (F (fun j ↦ if b j then subcubeRemVec hp hm S active μ
    j - 1 else subcubeRemVec hp hm S active μ j) : ℂ)
  have hterm (o : Fin (2 ^ W)) : star (single (workMemIdx n m k 0 μ) 1) ⬝ᵥ ((((lowBlock W
    M).embedMatrix (Matrix.single 0 o 1) * subcubeDeflatedUnitaryPre hp hm S active K_sub)ᴴ * (Θ
    (Store.subst σ res (Int.ofNat (batchNextCount hm1 hkN hbg1 active o).val))).1.1 * ((lowBlock W
    M).embedMatrix (Matrix.single 0 o 1) * subcubeDeflatedUnitaryPre hp hm S active K_sub)) *ᵥ
    single (workMemIdx n m k 0 μ) 1) = (normSq (subcubeProdState (subcubeSlotState hp hm R K_sub)
    (parallelMarkPerm n m R o)) : ℂ) * gList (groupHits hbg1 o) := by
    set K_op := (lowBlock W M).embedMatrix (Matrix.single 0 o 1) *
      subcubeDeflatedUnitaryPre hp hm S active K_sub
    set idx := workMemIdx n m k 0 μ
    set idx' := workMemIdx n m k 0 (writeMemBatch active (groupHits hbg1 o) μ)
    set α := subcubeProdState (subcubeSlotState hp hm R K_sub) (parallelMarkPerm n m R o)
    have hKv : K_op *ᵥ single idx 1 = α • single idx' 1 := by
      dsimp only [K_op, idx, idx', α]; rw [← mulVec_mulVec]
      exact krausLowBlock_mul_subcubeDeflatedUnitaryPre_mulVec hp hm K_sub hsub o
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_conjTranspose, star_star, hKv, Matrix.mulVec_smul, star_smul, smul_dotProduct,
      dotProduct_smul, ← diag_eq_star_single_dotProduct_mulVec _ idx', smul_eq_mul, smul_eq_mul, ←
      mul_assoc, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
    by_cases hα : α = 0
    · rw [hα, Complex.normSq_zero, Complex.ofReal_zero, zero_mul, zero_mul]
    · set w := parallelMarkPerm n m R o; have hflags (j : Fin m) :
          ((addrReg n 1).basisSplitEquiv ((groupReg hbg1 j).extractIndex w)).2 = 0 := by
        by_contra hj
        apply hα; unfold α subcubeProdState; refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        dsimp only [subcubeSlotState, tensorState]; rw [Pi.single_eq_of_ne hj, mul_zero]
      have hnew : ∀ x ∈ groupHits hbg1 o, x ∈ R := by
        intro x hx; have ho : o = parallelMarkPerm n m R w := (parallelMarkPerm_involutive R o).symm
        rw [ho] at hx; exact mem_of_mem_groupHits_parallelMarkPerm hbg1 hflags hx
      obtain ⟨hlen, hval'⟩ := memPrefixValid_writeMemBatch hcard hval (nodup_groupHits hbg1 o) hnew
      have hcnt : (batchNextCount hm1 hkN hbg1 active o).val =
          active + (groupHits hbg1 o).length := by
        simp [batchNextCount, Nat.min_eq_right hlen]
      have hsdiff : S \ memSeen n k (memPrefix k (active + (groupHits hbg1 o).length))
        (writeMemBatch active (groupHits hbg1 o) μ) = R \ (groupHits hbg1 o).toFinset := by
        rw [memSeen_writeMemBatch hval (groupHits hbg1 o) hlen]; ext x; simp [R, and_assoc]
      rw [hcnt, hΘ (active + (groupHits hbg1 o).length) _ _ hlen (by simp) hval']; congr 2
      unfold subcubeRemVec; simp_rw [hsdiff]
  simp_rw [hterm]
  have hGH (hit : Fin m → Option (Fin (2 ^ n))) (hhit : ∀ j x, hit j = some x → x ∈ R ∧ subcubePref
    hp hm x = j) (_hlen : ((finRange m).filterMap hit).length = (Finset.univ.filter fun j ↦ (hit
    j).isSome = true).card) : gList ((finRange m).filterMap hit) = hBool (fun j ↦ (hit
    j).isSome) := by
    dsimp only [gList, hBool]; congr 2; funext j
    exact card_subcubeLocalSet_sdiff_filterMap hp hm R hit hhit j
  rw [sum_normSq_subcubeReadout_eq hp hm R K_sub gList hBool hGH]; unfold subcubeStepExp
  rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun b _ ↦ (Complex.ofReal_mul _ _).symm
private lemma wp_subcubeSecondSweep_of_remVec {Var : Type} [DecidableEq Var] (res : Var) {n p m k :
    ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_sub : ℕ) {S : Finset (Fin (2
    ^ n))} (hcard : S.card = k) {active : ℕ} (hact : active ≤ k) {τ : Store Var} (hτ : τ res =
    (active : ℤ)) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) (Θ : CQAssertion (Store
      Var) (2
    ^ (m * (n + 1) + k * n))) (F : (Fin m → ℕ) → ℝ) (hΘ : ∀ (s : ℕ) (τ' : Store Var) (μ' : Fin (2 ^
    (k * n))), s ≤ k → τ' res = (s : ℤ) → MemPrefixValid S s μ' → (Θ τ').1.1 (workMemIdx n m k 0 μ')
    (workMemIdx n m k 0 μ') = (F (subcubeRemVec hp hm S s μ') : ℂ)) : ((wp ((subcubeSecondSweep res
    hm1 hkN hp hm K_sub).compile qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n
    m k 0 μ) (workMemIdx n m k 0 μ) = (subcubeStepExp (2 ^ (n - p)) K_sub F (subcubeRemVec hp hm S
    active μ) : ℂ) := by
  unfold subcubeSecondSweep; by_cases hlt : active < k
  · rw [wp_dispFin_subcube_of_lt res _ _ Θ hlt hτ]
    exact wp_subcubeDeflatedRound_of_remVec res hm1 hkN hp hm active K_sub hcard hval Θ F hΘ τ
  · have h_eq : active = k := (by omega); subst active
    rw [wp_dispFin_subcube_of_ge res _ _ Θ le_rfl hτ, hΘ k τ μ le_rfl hτ hval]
    have hseen := card_memSeen_of_memPrefixValid hval
    have hmem_eq : memSeen n k (memPrefix k k) μ = S :=
      Finset.eq_of_subset_of_card_le hseen.2 (by rw [hcard, hseen.1])
    have hr0 (j : Fin m) : subcubeRemVec hp hm S k μ j = 0 := by
      simp [subcubeRemVec, hmem_eq, subcubeLocalSet]
    symm; congr 1; unfold subcubeStepExp; rw [sum_eq_single (fun _ : Fin m ↦ false) (fun b hb ↦ ?_)]
    · have hprod1 :
          (∏ j : Fin m,
            match (false : Bool) with
            | true => p_succ_frac K_sub (subcubeRemVec hp hm S k μ j) (2 ^ (n - p))
            | false => 1 - p_succ_frac K_sub (subcubeRemVec hp hm S k μ j) (2 ^ (n - p))) = 1 :=
        Finset.prod_eq_one fun j _ ↦ by simp [hr0 j]
      simp [hprod1]
    · obtain ⟨j, hj⟩ : ∃ j : Fin m, b j = true := by
        by_contra! hall
        exact hb (funext fun j ↦ Bool.eq_false_iff.mpr (hall j))
      have hp0 :
          (∏ j' : Fin m,
            match b j' with
            | true => p_succ_frac K_sub (subcubeRemVec hp hm S k μ j') (2 ^ (n - p))
            | false => 1 - p_succ_frac K_sub (subcubeRemVec hp hm S k μ j') (2 ^ (n - p))) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        simp [hj, hr0 j]
      rw [hp0, zero_mul]
private lemma wp_subcubeExtraSweeps_of_remVec {Var : Type} [DecidableEq Var] (res : Var) {n p m k :
    ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (ks : List ℕ) {S : Finset (Fin
    (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (F :
      (Fin m →
    ℕ) → ℝ) (hΘ : ∀ (s : ℕ) (τ' : Store Var) (μ' : Fin (2 ^ (k * n))), s ≤ k → τ' res = (s : ℤ) →
    MemPrefixValid S s μ' → (Θ τ').1.1 (workMemIdx n m k 0 μ') (workMemIdx n m k 0 μ') = (F
    (subcubeRemVec hp hm S s μ') : ℂ)) : ∀ (active : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
    active ≤ k → τ res = (active : ℤ) → MemPrefixValid S active μ → ((wp ((subcubeExtraSweeps res
    hm1 hkN hp hm ks).compile qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n m k
    0 μ) (workMemIdx n m k 0 μ) = (subcubeSweepsExp (2 ^ (n - p)) ks F (subcubeRemVec hp hm S active
    μ) : ℂ) := by
  induction ks with
  | nil =>
    intro active τ μ hact hτ hval
    simpa [subcubeExtraSweeps, subcubeSweepsExp] using hΘ active τ μ hact hτ hval
  | cons K_sub rest ih =>
    intro active τ μ hact hτ hval; dsimp only [subcubeExtraSweeps, subcubeSweepsExp, compile]
    rw [wp_qSeq]
    exact wp_subcubeSecondSweep_of_remVec res hm1 hkN hp hm K_sub hcard hact hτ hval (wp
      ((subcubeExtraSweeps res hm1 hkN hp hm rest).compile qAssign (groverParallelMarkingOracle m
      S)) Θ) (subcubeSweepsExp (2 ^ (n - p)) rest F) ih
/-- Exact invariant-preserving `wp` expectation of `.qSet;; subcubeMultiSweepPre` for any
  function
  `F: (Fin m → ℕ) → ℝ` of the per-subcube remaining-target vector `subcubeRemVec`. -/
theorem wp_qSet_subcubeMultiSweepPre_of_remVec {Var : Type} [DecidableEq Var] (res : Var) {n p m k :
    ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_init : ℕ) (ks : List ℕ) {S :
    Finset (Fin (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k *
      n))) (F
    : (Fin m → ℕ) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))), s ≤ k → τ res = (s :
    ℤ) → MemPrefixValid S s μ → (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (F
    (subcubeRemVec hp hm S s μ) : ℂ)) (σ : Store Var) : ((wp (.qSet ;; (subcubeMultiSweepPre res hm1
    hkN hp hm K_init ks).compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
    (subcubeSweepsExp (2 ^ (n - p)) (K_init :: ks) F (fun j ↦ (subcubeLocalSet hp hm S j).card) : ℂ)
    • (1 : Operator (2 ^ (m * (n + 1) + k * n))) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  let sweep0 := (subcubeInitRound (Var := Var) res hm1 hkN hp hm K_init).compile qAssign
    (groverParallelMarkingOracle m S)
  let restSweeps := (subcubeExtraSweeps (Var := Var) res hm1 hkN hp hm ks).compile qAssign
    (groverParallelMarkingOracle m S)
  change ((wp (.qSet ;; (sweep0 ;; restSweeps)) Θ) σ).1.1 = _
  have hassoc : wp (.qSet ;; (sweep0 ;; restSweeps)) Θ = wp (.qSet ;; sweep0) (wp restSweeps Θ) :=
    by simp only [wp_qSeq]
  rw [hassoc, wp_qSet_subcubeInitRound_sum_eq res hm1 hkN hp hm K_init S (wp restSweeps Θ) σ]
  congr 1; let F' : (Fin m → ℕ) → ℝ := subcubeSweepsExp (2 ^ (n - p)) ks F
  let c0 (j : Fin m) : ℕ := (subcubeLocalSet hp hm S j).card
  let gList : List (Fin (2 ^ n)) → ℂ := fun L ↦
    (F' (fun j ↦ (subcubeLocalSet hp hm (S \ L.toFinset) j).card) : ℂ)
  let hBool : (Fin m → Bool) → ℂ := fun b ↦ (F' (fun j ↦ if b j then c0 j - 1 else c0 j) : ℂ)
  have hterm (o : Fin (2 ^ (m * (n + 1)))) : (normSq (subcubeProdState (subcubeSlotState hp hm S
    K_init) (parallelMarkPerm n m S o)) : ℂ) * ((wp restSweeps Θ) (Store.subst σ res (Int.ofNat
    (batchNextCount hm1 hkN hbg1 0 o).val))).1.1 (workMemIdx n m k 0 (writeMemBatch 0 (groupHits
    hbg1 o) 0)) (workMemIdx n m k 0 (writeMemBatch 0 (groupHits hbg1 o) 0)) = (normSq
    (subcubeProdState (subcubeSlotState hp hm S K_init) (parallelMarkPerm n m S o)) : ℂ) * gList
    (groupHits hbg1 o) := by
    set α := subcubeProdState (subcubeSlotState hp hm S K_init) (parallelMarkPerm n m S o)
    by_cases hα : α = 0
    · rw [hα, Complex.normSq_zero, Complex.ofReal_zero, zero_mul, zero_mul]
    · obtain ⟨hlen, hcnt, hval'⟩ := subcubeInitReadout_support_valid hm1 hkN hp hm hcard hα
      rw [hcnt,
        wp_subcubeExtraSweeps_of_remVec res hm1 hkN hp hm ks hcard Θ F hΘ _ _ _ hlen (by simp)
          hval']
      dsimp only [gList, F']; congr 3; unfold subcubeRemVec; funext j
      rw [memSeen_writeMemBatch_zero (groupHits hbg1 o) hlen]
  simp_rw [hterm]
  have hGH (hit : Fin m → Option (Fin (2 ^ n))) (hhit : ∀ j x, hit j = some x → x ∈ S ∧ subcubePref
    hp hm x = j) (_hlen : ((finRange m).filterMap hit).length = (Finset.univ.filter fun j ↦ (hit
    j).isSome = true).card) : gList ((finRange m).filterMap hit) = hBool (fun j ↦ (hit
    j).isSome) := by
    dsimp only [gList, hBool, c0]; congr 2; funext j
    exact card_subcubeLocalSet_sdiff_filterMap hp hm S hit hhit j
  rw [sum_normSq_subcubeReadout_eq hp hm S K_init gList hBool hGH]
  dsimp only [subcubeSweepsExp, subcubeStepExp, F', hBool, c0]; rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun b _ ↦ (Complex.ofReal_mul _ _).symm
/-- Exact `wp` expectation of `.qSet;; subcubeMultiSweepPre` for any occupancy function
  `f: ℕ → ℝ` (`s = k - ∑ j, r j`). -/
theorem wp_qSet_subcubeMultiSweepPre_of_invariant {Var : Type} [DecidableEq Var] (res : Var) {n p m
    k : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (K_init : ℕ) (ks : List ℕ)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) +
      k *
    n))) (f : ℕ → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))), s ≤ k → τ res = (s :
    ℤ) → MemPrefixValid S s μ → (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (f s : ℂ))
    (σ : Store Var) : ((wp (.qSet ;; (subcubeMultiSweepPre res hm1 hkN hp hm K_init ks).compile
    qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1 = (subcubeSweepsExp (2 ^ (n - p)) (K_init
    :: ks) (fun r ↦ f (k - ∑ j : Fin m, r j)) (fun j ↦ (subcubeLocalSet hp hm S j).card) : ℂ) • (1 :
    Operator (2 ^ (m * (n + 1) + k * n))) := by
  refine wp_qSet_subcubeMultiSweepPre_of_remVec res hm1 hkN hp hm K_init ks hcard Θ
    (fun r ↦ f (k - ∑ j : Fin m, r j)) (fun s τ μ hs hτ hval ↦ ?_) σ
  rw [hΘ s τ μ hs hτ hval, sum_subcubeRemVec_eq hp hm hcard hval, Nat.sub_sub_self hs]
/- ### Algebraic & Monotonicity Properties of `subcubeSweepsExp` and `subcubeOneDimExp` -/
private lemma subcubeStepWt_nonneg {m : ℕ} (subDim K_sub : ℕ) (r : Fin m → ℕ)
    (b : Fin m → Bool) :
    0 ≤ (∏ j : Fin m,
      match b j with
      | true => p_succ_frac K_sub (r j) subDim
      | false => 1 - p_succ_frac K_sub (r j) subDim) := by
  refine Finset.prod_nonneg fun j _ ↦ ?_
  cases b j
  · exact sub_nonneg.mpr (Real.sin_sq_le_one _)
  · exact sq_nonneg _
private lemma sum_subcubeStepWt_eq_one {m : ℕ} (subDim K_sub : ℕ) (r : Fin m → ℕ) :
    (∑ b : Fin m → Bool,
      ∏ j : Fin m,
        match b j with
        | true => p_succ_frac K_sub (r j) subDim
        | false => 1 - p_succ_frac K_sub (r j) subDim) = 1 := by
  let sp (j : Fin m) (bj : Bool) : ℝ :=
    match bj with
    | true => p_succ_frac K_sub (r j) subDim
    | false => 1 - p_succ_frac K_sub (r j) subDim
  change (∑ b : Fin m → Bool, ∏ j : Fin m, sp j (b j)) = 1; rw [(Fintype.prod_sum sp).symm]
  refine Finset.prod_eq_one fun j _ ↦ ?_
  rw [Fintype.sum_bool]; dsimp only [sp]; ring
private lemma subcubeSweepsExp_mono_on {m : ℕ} (subDim : ℕ) (allKs : List ℕ) (F G : (Fin m → ℕ) → ℝ)
    : ∀ r₀ : Fin m → ℕ, (∀ r : Fin m → ℕ, (∀ j, r j ≤ r₀ j) → F r ≤ G r) → subcubeSweepsExp subDim
    allKs F r₀ ≤ subcubeSweepsExp subDim allKs G r₀ := by
  induction allKs with
  | nil => intro r₀ hle; exact hle r₀ fun _ ↦ le_rfl
  | cons K_sub ks ih =>
    intro r₀ hle; dsimp only [subcubeSweepsExp, subcubeStepExp]
    refine Finset.sum_le_sum fun b _ ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (subcubeStepWt_nonneg subDim K_sub r₀ b)
    refine ih _ fun r hr ↦ hle r fun j ↦ (hr j).trans ?_
    split_ifs <;> omega
private lemma subcubeSweepsExp_eq_on {m : ℕ} (subDim : ℕ) (allKs : List ℕ) (F G : (Fin m → ℕ) → ℝ)
    (r₀ : Fin m → ℕ) (heq : ∀ r : Fin m → ℕ, (∀ j, r j ≤ r₀ j) → F r = G r) : subcubeSweepsExp
    subDim allKs F r₀ = subcubeSweepsExp subDim allKs G r₀ :=
  le_antisymm (subcubeSweepsExp_mono_on subDim allKs F G r₀ fun r hr ↦ (heq r hr).le)
    (subcubeSweepsExp_mono_on subDim allKs G F r₀ fun r hr ↦ (heq r hr).ge)
theorem subcubeSweepsExp_const {m : ℕ} (subDim : ℕ) (allKs : List ℕ) (c : ℝ) (r₀ : Fin m → ℕ) :
    subcubeSweepsExp subDim allKs (fun _ ↦ c) r₀ = c := by
  induction allKs generalizing r₀ with
  | nil => rfl
  | cons K_sub ks ih =>
    dsimp only [subcubeSweepsExp, subcubeStepExp]; simp_rw [ih]
    rw [← Finset.sum_mul, sum_subcubeStepWt_eq_one, one_mul]
theorem subcubeSweepsExp_add {m : ℕ} (subDim : ℕ) (allKs : List ℕ) (F G : (Fin m → ℕ) → ℝ) (r₀ : Fin
    m → ℕ) : subcubeSweepsExp subDim allKs (fun r ↦ F r + G r) r₀ = subcubeSweepsExp subDim allKs F
    r₀ + subcubeSweepsExp subDim allKs G r₀ := by
  induction allKs generalizing r₀ with
  | nil => rfl
  | cons K_sub ks ih =>
    dsimp only [subcubeSweepsExp, subcubeStepExp]; simp_rw [ih, mul_add]
    exact Finset.sum_add_distrib
theorem subcubeSweepsExp_mul_const {m : ℕ} (subDim : ℕ) (allKs : List ℕ) (c : ℝ) (F : (Fin m → ℕ) →
    ℝ) (r₀ : Fin m → ℕ) : subcubeSweepsExp subDim allKs (fun r ↦ c * F r) r₀ = c * subcubeSweepsExp
    subDim allKs F r₀ := by
  induction allKs generalizing r₀ with
  | nil => rfl
  | cons K_sub ks ih =>
    dsimp only [subcubeSweepsExp, subcubeStepExp]
    simp_rw [ih, ← mul_assoc, mul_comm _ c, mul_assoc]; exact (Finset.mul_sum _ _ _).symm
theorem subcubeSweepsExp_finset_sum {m : ℕ} {ι : Type*} (subDim : ℕ) (allKs : List ℕ) (s : Finset ι)
    (F : ι → (Fin m → ℕ) → ℝ) (r₀ : Fin m → ℕ) : subcubeSweepsExp subDim allKs (fun r ↦ ∑ i ∈ s, F i
    r) r₀ = ∑ i ∈ s, subcubeSweepsExp subDim allKs (F i) r₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using subcubeSweepsExp_const subDim allKs 0 r₀
  | @insert a s ha ih => simp_rw [Finset.sum_insert ha]; rw [subcubeSweepsExp_add, ih]
/-- Exact sum factorization: the multi-sweep expectation of any additive per-subcube
  function
  `∑ j: Fin m, pot₀ (r j)` equals the sum of independent 1D per-subcube expectations
  `∑ j: Fin m, subcubeOneDimExp subDim allKs pot₀ (r₀ j)`. -/
theorem subcubeSweepsExp_sum_eq {m : ℕ} (subDim : ℕ) (allKs : List ℕ) (pot₀ : ℕ → ℝ) (r₀ : Fin m →
    ℕ) : subcubeSweepsExp subDim allKs (fun r ↦ ∑ j : Fin m, pot₀ (r j)) r₀ = ∑ j : Fin m,
    subcubeOneDimExp subDim allKs pot₀ (r₀ j) := by
  induction allKs generalizing r₀ with
  | nil => rfl
  | cons K_sub ks ih =>
    dsimp only [subcubeSweepsExp, subcubeStepExp]; simp_rw [ih]; simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j₀ _ ↦ ?_
    let E' := subcubeOneDimExp subDim ks pot₀
    let sp (j : Fin m) (bj : Bool) : ℝ :=
      (match bj with
        | true => p_succ_frac K_sub (r₀ j) subDim
        | false => 1 - p_succ_frac K_sub (r₀ j) subDim) *
      (if j = j₀ then E' (if bj then r₀ j₀ - 1 else r₀ j₀) else 1)
    have hterm (b : Fin m → Bool) :
        (∏ j : Fin m,
          match b j with
          | true => p_succ_frac K_sub (r₀ j) subDim
          | false => 1 - p_succ_frac K_sub (r₀ j) subDim) *
          E' (if b j₀ then r₀ j₀ - 1 else r₀ j₀) =
        ∏ j : Fin m, sp j (b j) := by
      dsimp only [sp]; rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j₀]; simp
    rw [Finset.sum_congr rfl fun b _ ↦ hterm b, (Fintype.prod_sum sp).symm]
    rw [Finset.prod_eq_single j₀ (fun j _ hj ↦ ?_) (fun hj₀ ↦ absurd (Finset.mem_univ j₀) hj₀)]
    · rw [Fintype.sum_bool]; dsimp only [sp, subcubeOneDimExp, E']
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [Fintype.sum_bool]; dsimp only [sp]; simp [hj]
/-- Exact product factorization: the multi-sweep expectation of any multiplicative
  per-subcube
  function `∏ j: Fin m, h₀ (r j)` equals the product of independent 1D per-subcube
  expectations
  `∏ j: Fin m, subcubeOneDimExp subDim allKs h₀ (r₀ j)`. -/
theorem subcubeSweepsExp_prod_eq {m : ℕ} (subDim : ℕ) (allKs : List ℕ) (h₀ : ℕ → ℝ) (r₀ : Fin m → ℕ)
    : subcubeSweepsExp subDim allKs (fun r ↦ ∏ j : Fin m, h₀ (r j)) r₀ = ∏ j : Fin m,
    subcubeOneDimExp subDim allKs h₀ (r₀ j) := by
  induction allKs generalizing r₀ with
  | nil => rfl
  | cons K_sub ks ih =>
    dsimp only [subcubeSweepsExp, subcubeStepExp]; simp_rw [ih]
    let E' := subcubeOneDimExp subDim ks h₀
    let sp (j : Fin m) (bj : Bool) : ℝ :=
      (match bj with
        | true => p_succ_frac K_sub (r₀ j) subDim
        | false => 1 - p_succ_frac K_sub (r₀ j) subDim) *
      E' (if bj then r₀ j - 1 else r₀ j)
    have hterm (b : Fin m → Bool) :
        (∏ j : Fin m,
          match b j with
          | true => p_succ_frac K_sub (r₀ j) subDim
          | false => 1 - p_succ_frac K_sub (r₀ j) subDim) *
          (∏ j : Fin m, E' (if b j then r₀ j - 1 else r₀ j)) =
        ∏ j : Fin m, sp j (b j) :=
      (Finset.prod_mul_distrib).symm
    rw [Finset.sum_congr rfl fun b _ ↦ hterm b, (Fintype.prod_sum sp).symm]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Fintype.sum_bool]; dsimp only [sp, subcubeOneDimExp, E']
    simp only [Bool.false_eq_true, ↓reduceIte]
@[simp] theorem subcubeOneDimExp_id_zero (subDim : ℕ) (allKs : List ℕ) :
    subcubeOneDimExp subDim allKs (fun c ↦ (c : ℝ)) 0 = 0 := by
  induction allKs with
  | nil => simp [subcubeOneDimExp]
  | cons K_sub ks ih => simp [subcubeOneDimExp, ih]
private noncomputable def subcubeMultiSweepOccLaw {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (S : Finset (Fin (2 ^ n))) (allKs : List ℕ) (s : ℕ) : ℝ :=
  subcubeSweepsExp (2 ^ (n - p)) allKs
    (fun r ↦ if S.card - (∑ j : Fin m, r j) = s then (1 : ℝ) else 0)
    (fun j ↦ (subcubeLocalSet hp hm S j).card)
private lemma subcubeMultiSweepOccLaw_props {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) {S : Finset
    (Fin (2 ^ n))} (hcard : S.card = k) (allKs : List ℕ) : (∀ s ≤ k, 0 ≤ subcubeMultiSweepOccLaw hp
    hm S allKs s) ∧ (∑ s ∈ Finset.range (k + 1), subcubeMultiSweepOccLaw hp hm S allKs s) = 1 ∧ ∀ f
    : ℕ → ℝ, (∑ s ∈ Finset.range (k + 1), subcubeMultiSweepOccLaw hp hm S allKs s * f s) =
    subcubeSweepsExp (2 ^ (n - p)) allKs (fun r ↦ f (k - ∑ j : Fin m, r j)) (fun j ↦
    (subcubeLocalSet hp hm S j).card) := by
  let c0 : Fin m → ℕ := fun j ↦ (subcubeLocalSet hp hm S j).card
  have hc0_sum : (∑ j : Fin m, c0 j) = k := by
    dsimp only [c0]; rw [sum_card_subcubeLocalSet_eq hp hm S, hcard]
  have hnn (s : ℕ) (_hs : s ≤ k) : 0 ≤ subcubeMultiSweepOccLaw hp hm S allKs s := by
    unfold subcubeMultiSweepOccLaw
    calc (0 : ℝ) = subcubeSweepsExp (2 ^ (n - p)) allKs (fun _ ↦ 0) c0 := (subcubeSweepsExp_const (2
      ^ (n - p)) allKs 0 c0).symm
      _ ≤ subcubeSweepsExp (2 ^ (n - p)) allKs
            (fun r ↦ if S.card - (∑ j : Fin m, r j) = s then (1 : ℝ) else 0) c0 :=
          subcubeSweepsExp_mono_on (2 ^ (n - p)) allKs _ _ c0 fun r _ ↦ by split_ifs <;> norm_num
  have hsum_f (f : ℕ → ℝ) : (∑ s ∈ Finset.range (k + 1), subcubeMultiSweepOccLaw hp hm S allKs s * f
    s) = subcubeSweepsExp (2 ^ (n - p)) allKs (fun r ↦ f (k - ∑ j : Fin m, r j)) c0 := by
    have hmul (s : ℕ) : subcubeMultiSweepOccLaw hp hm S allKs s * f s = subcubeSweepsExp (2 ^ (n -
      p)) allKs (fun r ↦ (if k - (∑ j : Fin m, r j) = s then (1 : ℝ) else 0) * f s) c0 := by
      unfold subcubeMultiSweepOccLaw; rw [hcard, mul_comm, ← subcubeSweepsExp_mul_const]; congr 1
      funext r; ring
    simp_rw [hmul, ← subcubeSweepsExp_finset_sum]
    refine subcubeSweepsExp_eq_on (2 ^ (n - p)) allKs _ _ c0 fun r hr ↦ ?_
    have hr_le : (∑ j : Fin m, r j) ≤ k := by rw [← hc0_sum]; exact Finset.sum_le_sum fun j _ ↦ hr j
    have hmem : k - (∑ j : Fin m, r j) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single (k - ∑ j : Fin m, r j) (fun s _ hne ↦ by simp [hne.symm]) (fun hnot ↦
      absurd hmem hnot)]; simp
  refine ⟨hnn, ?_, hsum_f⟩
  have h1 := hsum_f fun _ ↦ 1; simp_rw [mul_one] at h1; rw [h1, subcubeSweepsExp_const]
/-- Total correctness (`wp = ⊤`) of `.qSet;; subcubeMultiSweepBatchWithLast` (`1 ≤ k`) for
  any
  multi-sweep schedule `K_init:: ks` whenever every remaining batch occupancy `s < k - 1`
  has
  `1 ≤ b s` and `0 < groupSuccProb n (g s) (k - s) (K s)` and `lastStage` satisfies
  `hlast_wp`. -/
theorem wp_subcubeMultiSweepBatchWithLast_eq_top {Var : Type} [DecidableEq Var] (res : Var) {n p m k
    : ℕ} (hm1 : 1 ≤ m) (hk : 1 ≤ k) (hkN : k ≤ 2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (hb : ∀ s < k - 1, 1 ≤ b s) (K_init : ℕ) (ks : List ℕ) (K : ℕ →
    ℕ) (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) {S : Finset (Fin (2 ^ n))}
    (hcard : S.card = k) (hpos : ∀ s < k - 1, 0 < groupSuccProb n (g s) (k - s) (K s)) (hlast_wp : ∀
    (τ : Store Var) (μ : Fin (2 ^ (k * n))), τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ
    → ((wp (lastStage.compile qAssign (groverParallelMarkingOracle m S)) (wp (measureRegister res
    (highBlock (m * (n + 1)) (k * n))) (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S))) τ).1.1
    (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1) : wp (.qSet ;;
    (subcubeMultiSweepBatchWithLast res hm1 hkN hp hm hbg K_init ks K lastStage).compile qAssign
    (groverParallelMarkingOracle m S)) (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S) =
    ⊤ := by
  rcases subcubeMultiSweepOccLaw_props hp hm hcard (K_init :: ks) with ⟨hP_nn, hP_sum, hP_f⟩
  refine wp_init_seq_findAllBatchTail_eq_top res hm1 hk hkN hbg hb K (subcubeMultiSweepPre res hm1
    hkN hp hm K_init ks) lastStage hcard (subcubeMultiSweepOccLaw hp hm S (K_init :: ks)) hP_nn
    hP_sum (fun Θ f hΘ σ ↦ ?_) hpos hlast_wp
  rw [wp_qSet_subcubeMultiSweepPre_of_invariant res hm1 hkN hp hm K_init ks hcard Θ f hΘ σ, hP_f f]
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllSubcube
section WD_FindAllSubcubeAnalysis
namespace QuantumComputation.Specs.DickeSol
open Real
@[expose] public section
/- ## Section 1: 31-Angle Subcube Palette, Query-Count Bound, and `c ∈ {1, 2, 3}` Hit Bounds -/
noncomputable def subcubePhi (idx : Fin 31) : ℝ :=
  match idx.1 with
  | 0 => 41 / 40
  | 1 => 103 / 100
  | 2 => 27 / 25
  | 3 => 217 / 200
  | 4 => 11 / 10
  | 5 => 23 / 20
  | 6 => 231 / 200
  | 7 => 239 / 200
  | 8 => 49 / 40
  | 9 => 31 / 25
  | 10 => 251 / 200
  | 11 => 259 / 200
  | 12 => 263 / 200
  | 13 => 269 / 200
  | 14 => 271 / 200
  | 15 => 34 / 25
  | 16 => 273 / 200
  | 17 => 281 / 200
  | 18 => 287 / 200
  | 19 => 36 / 25
  | 20 => 291 / 200
  | 21 => 293 / 200
  | 22 => 147 / 100
  | 23 => 297 / 200
  | 24 => 301 / 200
  | 25 => 303 / 200
  | 26 => 38 / 25
  | 27 => 153 / 100
  | 28 => 307 / 200
  | 29 => 77 / 50
  | _ => 31 / 20
/-- Suffix-subcube Grover iteration count stopping near target phase `subcubePhi idx` on a
  subcube
  of dimension `2 ^ subN`. -/
noncomputable def K_subcube (idx : Fin 31) (subN : ℕ) : ℕ :=
  Int.toNat (round (subcubePhi idx / (2 * Real.arcsin (√(1 / (2 ^ subN : ℝ))))))
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllSubcubeAnalysis
section WD_FindAllMultiSweepAnalysis
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open List (finRange)
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped NNReal ENNReal QHLExpectation QProg.Notation
@[expose] public section
/- ## Section 1: 36-Angle Multi-Quadrant Subcube Palette & Universal `c: ℕ` Trig Certificates -/
abbrev multiPaletteLen : ℕ := 36
def multiPhiNumList : List ℕ :=
  [320001, 360001, 2, 11, 12, 520001, 560001, 3, 16, 17, 720001, 760001, 79, 820001, 17, 860001,
   9, 47, 970001, 1, 103, 53, 1075001, 1080001, 1120001, 29, 1220001, 5, 1280001, 34, 139,
   1480001, 151, 77, 31, 311]
def multiPhiDenList : List ℕ :=
  [1000000, 1000000, 5, 25, 25, 1000000, 1000000, 5, 25, 25, 1000000, 1000000, 100, 1000000, 20,
   1000000, 10, 50, 1000000, 1, 100, 50, 1000000, 1000000, 1000000, 25, 1000000, 4, 1000000, 25,
   100, 1000000, 100, 50, 20, 200]
def multiPhiNum (idx : Fin multiPaletteLen) : ℕ := multiPhiNumList.getD idx.val 1
def multiPhiDen (idx : Fin multiPaletteLen) : ℕ := multiPhiDenList.getD idx.val 1
/-- Rational target phase palette `Φ ∈ [0.32, 1.555]` for multi-sweep subcube Grover search. -/
noncomputable def multiPhi (idx : Fin multiPaletteLen) : ℝ :=
  (multiPhiNum idx : ℝ) / (multiPhiDen idx : ℝ)
/-- Suffix-subcube Grover iteration count stopping near target phase `multiPhi idx`. -/
noncomputable def K_multi (idx : Fin multiPaletteLen) (subN : ℕ) : ℕ :=
  Int.toNat (round (multiPhi idx / (2 * Real.arcsin (√(1 / (2 ^ subN : ℝ))))))
/-- Concrete sweep iteration list `[K_multi i₁ subN,..., K_multi i_L subN]`. -/
noncomputable def multiAllKs (subN : ℕ) (idxs : List (Fin multiPaletteLen)) : List ℕ :=
  idxs.map (fun idx ↦ K_multi idx subN)
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllMultiSweepAnalysis
section WD_FindAllStage2
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace
@[expose] public section
/-- Exact 1-step backward Markov expectation operator on the number `d` of distinct coupons
  already collected out of `r`, for single-group hit probability `p`. -/
noncomputable def couponStepExact (p : ℝ) (r : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  f d + ((r - d : ℝ) / r) * p * (f (d + 1) - f d)
/-- Piecewise-linear 1-step upper backward operator on the number `d` of distinct coupons
  already
  collected out of `r`, valid for any (possibly non-monotone) `f: ℕ → ℝ` whenever `p ∈
  [p_lo, p_hi]`
  and `d ≤ r`. -/
noncomputable abbrev couponStepUpper := stage2CouponStepUpper
private lemma filterMap_finRange_succ_toFinset {b r : ℕ}
    (c₀ : Option (Fin r)) (cs' : Fin b → Option (Fin r)) :
    ((List.finRange (b + 1)).filterMap (Fin.cons c₀ cs')).toFinset =
      match c₀ with
      | none => ((List.finRange b).filterMap cs').toFinset
      | some y => insert y ((List.finRange b).filterMap cs').toFinset := by
  rw [List.finRange_succ, List.filterMap_cons, List.filterMap_map]
  have hcomp : (Fin.cons c₀ cs' ∘ Fin.succ) = cs' := (by funext i; simp); rw [hcomp]
  cases c₀ <;> simp
/-- General Finset-accumulator reduction of the `(r + 1)^b`-tuple coupon sum to the `b`-step
  iterated 1D operator `couponStepExact`. -/
theorem sum_iidWeight_eq_couponStepExact_iter_finset (p : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (f : ℕ → ℝ) :
    ∀ (b : ℕ) (A : Finset (Fin r)),
      (∑ cs : Fin b → Option (Fin r),
        (∏ j : Fin b, match cs j with
          | some _ => p / (r : ℝ)
          | none => 1 - p) *
          f (A ∪ ((List.finRange b).filterMap cs).toFinset).card) =
        (couponStepExact p r)^[b] f A.card := by
  have hr_pos : (0 : ℝ) < r := (by exact_mod_cast hr); have hr_ne : (r : ℝ) ≠ 0 := hr_pos.ne'
  intro b
  induction b with
  | zero => intro A; rw [Fintype.sum_unique]; simp
  | succ b ih =>
    intro A; set e := (Fin.consEquiv (fun _ : Fin (b + 1) ↦ Option (Fin r))).symm
    rw [← Equiv.sum_comp e.symm]; have he : ∀ q : Option (Fin r) × (Fin b → Option (Fin r)),
        e.symm q = (Fin.cons q.1 q.2 : Fin (b + 1) → Option (Fin r)) := by
      intro q; rfl
    simp_rw [he, Fintype.sum_prod_type]; rw [Fintype.sum_option]; have hnone :
        (∑ x : Fin b → Option (Fin r),
          (∏ j : Fin (b + 1),
            match (Fin.cons (none : Option (Fin r)) x : Fin (b + 1) → Option (Fin r)) j with
            | some _ => p / (r : ℝ)
            | none => 1 - p) *
            f (A ∪ ((List.finRange (b + 1)).filterMap
              (Fin.cons (none : Option (Fin r)) x : Fin (b + 1) → Option (Fin r))).toFinset).card) =
          (1 - p) * (couponStepExact p r)^[b] f A.card := by
      simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        filterMap_finRange_succ_toFinset, mul_assoc]
      rw [← Finset.mul_sum, ih A]
    have hsome : ∀ y : Fin r,
        (∑ x : Fin b → Option (Fin r),
          (∏ j : Fin (b + 1),
            match (Fin.cons (some y) x : Fin (b + 1) → Option (Fin r)) j with
            | some _ => p / (r : ℝ)
            | none => 1 - p) *
            f (A ∪ ((List.finRange (b + 1)).filterMap
              (Fin.cons (some y) x : Fin (b + 1) → Option (Fin r))).toFinset).card) =
          (p / (r : ℝ)) * (couponStepExact p r)^[b] f (insert y A).card := by
      intro y
      have hunion : ∀ x : Fin b → Option (Fin r), A ∪ insert y ((List.finRange b).filterMap
        x).toFinset = insert y A ∪ ((List.finRange b).filterMap x).toFinset := by
        intro x; ext z; simp
      simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        filterMap_finRange_succ_toFinset, hunion, mul_assoc]
      rw [← Finset.mul_sum, ih (insert y A)]
    rw [hnone, Finset.sum_congr rfl (fun y _ ↦ hsome y)]; set g_b := (couponStepExact p r)^[b] f
    rw [← Finset.sum_add_sum_compl A]
    have hsum_in : (∑ y ∈ A, (p / (r : ℝ)) * g_b (insert y A).card) = (A.card : ℝ) * (p / (r : ℝ)) *
      g_b A.card := by
      have hcongr : ∀ y ∈ A, (p / (r : ℝ)) * g_b (insert y A).card = (p / (r : ℝ)) * g_b
        A.card := by
        intro y hy; rw [Finset.insert_eq_of_mem hy]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul, mul_assoc]
    have hsum_out : (∑ y ∈ Aᶜ, (p / (r : ℝ)) * g_b (insert y A).card) = ((r - A.card : ℕ) : ℝ) * (p
      / (r : ℝ)) * g_b (A.card + 1) := by
      have hcongr : ∀ y ∈ Aᶜ, (p / (r : ℝ)) * g_b (insert y A).card = (p / (r : ℝ)) * g_b (A.card +
        1) := by
        intro y hy; rw [Finset.card_insert_of_notMem (Finset.mem_compl.1 hy)]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_compl, Fintype.card_fin,
        nsmul_eq_mul, mul_assoc]
    rw [hsum_in, hsum_out, Function.iterate_succ_apply']
    have hcard_le : A.card ≤ r := (by simpa using A.card_le_univ); rw [Nat.cast_sub hcard_le]
    change (1 - p) * g_b A.card + ((A.card : ℝ) * (p / (r : ℝ)) * g_b A.card + ((r : ℝ) - (A.card :
      ℝ)) * (p / (r : ℝ)) * g_b (A.card + 1)) = couponStepExact p r g_b A.card
    unfold couponStepExact; generalize g_b A.card = x, g_b (A.card + 1) = y; field_simp [hr_ne]
    ring
/-- Exact reduction of the `(r + 1)^b`-tuple coupon sum to `(couponStepExact p r)^[b] f 0`. -/
theorem sum_iidWeight_eq_couponStepExact_iter (p : ℝ) (r b : ℕ) (hr : 1 ≤ r) (f : ℕ → ℝ) :
    (∑ cs : Fin b → Option (Fin r),
      (∏ j : Fin b, match cs j with
        | some _ => p / (r : ℝ)
        | none => 1 - p) * f ((List.finRange b).filterMap cs).dedup.length) =
      (couponStepExact p r)^[b] f 0 := by
  have h0 := sum_iidWeight_eq_couponStepExact_iter_finset p r hr f b ∅
  simp only [Finset.empty_union, List.card_toFinset, Finset.card_empty] at h0; exact h0
/-- Monotonicity of `couponStepExact p r` on `0 ≤ d ≤ r` when `0 ≤ p ≤ 1`. -/
theorem couponStepExact_mono_on {p : ℝ} {r : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g₁ g₂ : ℕ → ℝ} (hg : ∀
    d ≤ r, g₁ d ≤ g₂ d) : ∀ d ≤ r, couponStepExact p r g₁ d ≤ couponStepExact p r g₂ d := by
  intro d hd; rcases eq_or_lt_of_le hd with rfl | hlt
  · simp [couponStepExact, hg d le_rfl]
  · have hr_pos : (0 : ℝ) < r := (by exact_mod_cast (Nat.zero_lt_of_lt hlt))
    have hd_le : (d : ℝ) ≤ r := (by exact_mod_cast hd)
    have hq0 : 0 ≤ ((r - d : ℝ) / r) * p := mul_nonneg (div_nonneg (by linarith) hr_pos.le) hp0
    have hdiv1 : (r - d : ℝ) / r ≤ 1 := (by rw [div_le_one hr_pos]; linarith)
    have hq1 : ((r - d : ℝ) / r) * p ≤ 1 :=
      (mul_le_mul_of_nonneg_left hp1 (div_nonneg (by linarith) hr_pos.le)).trans (by linarith)
    have hd0 := hg d hd; have hd1 := hg (d + 1) hlt; unfold couponStepExact; nlinarith
/-- Pointwise 1-step domination `couponStepExact p r g d ≤ couponStepUpper p_lo p_hi r g d`
  for `d ≤ r` and `p ∈ [p_lo, p_hi]`. -/
theorem couponStepExact_le_couponStepUpper_on {p p_lo p_hi : ℝ} {r : ℕ} (hlo : p_lo ≤ p) (hhi : p ≤
    p_hi) (g : ℕ → ℝ) : ∀ d ≤ r, couponStepExact p r g d ≤ couponStepUpper p_lo p_hi r g d := by
  intro d hd; rcases eq_or_lt_of_le hd with rfl | hlt
  · simp [couponStepExact, couponStepUpper, stage2CouponStepUpper]
  · have hr_pos : (0 : ℝ) < r := (by exact_mod_cast (Nat.zero_lt_of_lt hlt))
    have hd_le : (d : ℝ) ≤ r := (by exact_mod_cast hd)
    have hcoeff : 0 ≤ (r - d : ℝ) / r := div_nonneg (by linarith) hr_pos.le
    unfold couponStepExact couponStepUpper stage2CouponStepUpper; split_ifs with hle
    · have hsub : g (d + 1) - g d ≤ 0 := sub_nonpos.2 hle
      have hmul : p * (g (d + 1) - g d) ≤ p_lo * (g (d + 1) - g d) :=
        mul_le_mul_of_nonpos_right hlo hsub
      nlinarith
    · have hsub : 0 ≤ g (d + 1) - g d := (by linarith)
      have hmul : p * (g (d + 1) - g d) ≤ p_hi * (g (d + 1) - g d) :=
        mul_le_mul_of_nonneg_right hhi hsub
      nlinarith
/-- Iterated domination of `couponStepExact` by `couponStepUpper` on `d ≤ r`. -/
theorem couponStepExact_iter_le_couponStepUpper_iter_on {p p_lo p_hi : ℝ} {r : ℕ} (hp0 : 0 ≤ p) (hp1
    : p ≤ 1) (hlo : p_lo ≤ p) (hhi : p ≤ p_hi) (f : ℕ → ℝ) (b : ℕ) : ∀ d ≤ r, (couponStepExact p
    r)^[b] f d ≤ (couponStepUpper p_lo p_hi r)^[b] f d := by
  induction b with
  | zero => intro d _; simp
  | succ b ih =>
    intro d hd; rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (couponStepExact_mono_on hp0 hp1 ih d hd).trans (couponStepExact_le_couponStepUpper_on hlo
      hhi ((couponStepUpper p_lo p_hi r)^[b] f) d hd)
/-- Main combinatorial and real-algebraic bridge for Stage 2: for any `f: ℕ → ℝ` (without
  requiring `f` to be monotone) and any `p ∈ [0, 1] ∩ [p_lo, p_hi]`, the `(r + 1)^b` coupon
  expectation is bounded above by `(couponStepUpper p_lo p_hi r)^[b] f 0`. -/
theorem sum_iidWeight_le_couponStepUpper_iter {p p_lo p_hi : ℝ} {r b : ℕ}
    (hr : 1 ≤ r) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hlo : p_lo ≤ p) (hhi : p ≤ p_hi)
    (f : ℕ → ℝ) :
    (∑ cs : Fin b → Option (Fin r),
      (∏ j : Fin b, match cs j with
        | some _ => p / (r : ℝ)
        | none => 1 - p) * f ((List.finRange b).filterMap cs).dedup.length) ≤
      (couponStepUpper p_lo p_hi r)^[b] f 0 := by
  rw [sum_iidWeight_eq_couponStepExact_iter p r b hr f]
  exact couponStepExact_iter_le_couponStepUpper_iter_on hp0 hp1 hlo hhi f b 0 (Nat.zero_le r)
/- ## Direct `iidCouponProb` Bridges and `r = 1` `eigLockStage` Wrappers -/
private lemma iidCouponProb_eq_prod_match {b : ℕ} (n g r K : ℕ) (cs : Fin b → Option (Fin r)) :
    iidCouponProb n g r K cs =
      ∏ j : Fin b, match cs j with
        | some _ => groupSuccProb n g r K / (r : ℝ)
        | none => 1 - groupSuccProb n g r K := by
  unfold iidCouponProb; refine Finset.prod_congr rfl fun j _ ↦ ?_
  cases cs j <;> rfl
/-- Two-sided interval upper bound on `∑ cs, iidCouponProb n g r K cs * f...` via
  `(couponStepUpper p_lo p_hi r)^[b] f 0`. -/
theorem sum_iidCouponProb_le_couponStepUpper_iter {p_lo p_hi : ℝ} {n g r K b : ℕ} (hr : 1 ≤ r) (hlo
    : p_lo ≤ groupSuccProb n g r K) (hhi : groupSuccProb n g r K ≤ p_hi) (f : ℕ → ℝ) : (∑ cs : Fin b
    → Option (Fin r), iidCouponProb n g r K cs * f ((List.finRange b).filterMap cs).dedup.length) ≤
    (couponStepUpper p_lo p_hi r)^[b] f 0 := by
  simp_rw [iidCouponProb_eq_prod_match]; exact sum_iidWeight_le_couponStepUpper_iter hr
    (groupSuccProb_nonneg n g r K) (groupSuccProb_le_one n g r K) hlo hhi f
private lemma inner_compProjHermitian_eq_re {d : ℕ} (H : HermitianMat (Fin d) ℂ) (z : Fin d) :
    ⟪H, compProjHermitian z⟫_ℝ = (H.1 z z).re := by
  rw [HermitianMat.inner_eq_re_trace]; have hdiag (i : Fin d) :
      (H.mat * (compProjHermitian z).mat) i i = if i = z then H.1 z z else 0 := by
    change (H.1 * compProj z) i i = _
    rw [compProj, Matrix.mul_apply, sum_eq_single z (fun k hk ↦ by
      rw [Matrix.single_apply, ite_eq_right (fun h ↦ hk h.1.symm), mul_zero])]
    rw [Matrix.single_apply]; by_cases hiz : i = z
    · subst hiz; simp
    · simp [hiz, Ne.symm hiz]
  dsimp only [Matrix.trace, Matrix.diag]
  rw [Finset.sum_congr rfl (fun i _ ↦ hdiag i), Finset.sum_ite_eq' Finset.univ z]; simp
/-- If `A ≤ B` in `Observable d` (`0 ≤ A ≤ B ≤ 1`) and `A` has diagonal entry `1` at `z`,
  then
  `B` also has diagonal entry `1` at `z`. -/
lemma observable_diag_eq_one_of_le {d : ℕ} {A B : Observable (Fin d)} (hAB : A ≤ B)
    (z : Fin d) (hA : A.1.1 z z = 1) : B.1.1 z z = 1 := by
  have hself : star (B.1.1 z z) = B.1.1 z z := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun B.1.2 z) z
  have hre_eq : B.1.1 z z = ((B.1.1 z z).re : ℂ) := (Complex.conj_eq_iff_re.mp hself).symm
  have hge : (A.1.1 z z).re ≤ (B.1.1 z z).re := by
    rw [← inner_compProjHermitian_eq_re A.1 z, ← inner_compProjHermitian_eq_re B.1 z]
    exact HermitianMat.inner_mono' (compProjHermitian_nonneg z) hAB
  have hle : (B.1.1 z z).re ≤ ((1 : HermitianMat (Fin d) ℂ).1 z z).re := by
    rw [← inner_compProjHermitian_eq_re B.1 z, ← inner_compProjHermitian_eq_re 1 z]
    exact HermitianMat.inner_mono' (compProjHermitian_nonneg z) B.2.2
  rw [hA, Complex.one_re] at hge; change (B.1.1 z z).re ≤ ((1 : Operator d) z z).re at hle
  rw [Matrix.one_apply_eq, Complex.one_re] at hle
  have h1 : (B.1.1 z z).re = 1 := le_antisymm hle hge; rw [hre_eq, h1, Complex.ofReal_one]
/-- Diagonal entry of `validObs n m k S s` at `workMemIdx n m k 0 μ` equals `1` whenever
  `MemPrefixValid S s μ`. -/
lemma validObs_apply_workMemIdx_eq_one {Var : Type} {n m k s : ℕ} {S : Finset (Fin (2 ^ n))} (τ :
    Store Var) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s μ) : (validObs n m k S s τ).1.1
    (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1 := by
  dsimp only [validObs]; rw [realDiagObs_mat, Matrix.diagonal_apply_eq]; unfold validInd
  rw [lowHighEquiv_workMemIdx, ite_eq_left hval, Complex.ofReal_one]
/-- `lastStage` `wp` diagonal-1 wrapper for `eigLockStage` at `s = ⟨k - 1, hk_pos⟩`. -/
theorem wp_eigLockStage_last_workMemIdx_eq_one {Var : Type} [DecidableEq Var] (res : Var) {n m k :
    ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) {S :
    Finset (Fin (2 ^ n))} (hcard : S.card = k) (τ : Store Var) (μ : Fin (2 ^ (k * n))) (_hτ : τ res
    = ((k - 1 : ℕ) : ℤ)) (hval : MemPrefixValid S (k - 1) μ) :
    let s_last : Fin k := ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩
    ((wp ((eigLockStage res n m k hm_grid hk_grid hn200 s_last).compile qAssign
      (groverParallelMarkingOracle m S)) (wp (measureRegister res (highBlock (m * (n + 1)) (k * n)))
      (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S))) τ).1.1 (workMemIdx n m k 0 μ)
      (workMemIdx n m k 0 μ) = 1 := by
  intro s_last
  let lastP := (eigLockStage (Var := Var) res n m k hm_grid hk_grid hn200 s_last).compile
    qAssign (groverParallelMarkingOracle m S)
  let measP := measureRegister (Var := Var) res (highBlock (m * (n + 1)) (k * n))
  let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
    liftPureProp fun σ ↦ decodeTargets n k (σ res) = S
  have hmeas_ge : validObs (Var := Var) n m k S k ≤ wp measP post :=
    validObs_le_wp_measure_decodeTargets res hcard
  have hst_ge : validObs (Var := Var) n m k S (k - 1) ≤ wp lastP (validObs n m k S (s_last.val + 1))
    := (eigLockStage_wp_and_active res hm_grid hk_grid hn200 hcard s_last).1
  have hsk : s_last.val + 1 = k := Nat.sub_add_cancel hk1; rw [hsk] at hst_ge
  have htot_ge : validObs (Var := Var) n m k S (k - 1) ≤ wp lastP (wp measP post) :=
    hst_ge.trans (wp_mono lastP hmeas_ge)
  exact observable_diag_eq_one_of_le (htot_ge τ) (workMemIdx n m k 0 μ)
    (validObs_apply_workMemIdx_eq_one τ hval)
/-- `lastStage` invariant-guarded expected cost bound for `eigLockStage` at
  `s = ⟨k - 1, hk_pos⟩`. -/
theorem expectedCost_eigLockStage_last_le {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) {S :
    Finset (Fin (2 ^ n))} (hcard : S.card = k) (Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)))
      (hV :
    𝔼[Δ, validObs n m k S (k - 1)] = Δ.trace) :
    let s_last : Fin k := ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩
    let c_last : ℝ≥0 :=
      Real.toNNReal ((stage1RelCost : ℝ) * ((π / 4) * √((2 ^ n : ℝ) / m)))
    expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((eigLockStage res n m k hm_grid hk_grid hn200 s_last).compile qAssign
        (groverParallelMarkingOracle m S)) Δ ≤
      stateMass Δ * (c_last : ℝ≥0∞) := by
  intro s_last c_last
  have hcost := expectedCost_eigLockStage_le res hm_grid hk_grid hn200 hcard s_last hV
  have hsub : k - s_last.val = 1 := by
    dsimp only [s_last]; omega
  rw [hsub] at hcost
  have hsc := (stageCost_le_stage1RelCost (r := 1) hn200 hm_grid hk_grid le_rfl hk1).2
  have hv1 : vanillaFindAnyCost n m 1 = (π / 4) * √((2 ^ n : ℝ) / m) := by
    unfold vanillaFindAnyCost; simp
  rw [hv1] at hsc
  have hle_nn : stageCostReal n m 1 ≤ (c_last : ℝ) := by
    dsimp only [c_last]; rw [Real.coe_toNNReal _ (by positivity)]; exact hsc
  exact hcost.trans (mul_le_mul_of_nonneg_left
    ((ENNReal.ofReal_le_ofReal hle_nn).trans_eq ENNReal.ofReal_coe_nnreal) zero_le)
theorem groverHarmonicSqrtSum_eq_sum_range (k : ℕ) :
    groverHarmonicSqrtSum k = ∑ x ∈ Finset.range k, 1 / √((x + 1 : ℕ) : ℝ) := by
  unfold groverHarmonicSqrtSum; refine Finset.sum_bij (fun r _ ↦ r - 1)
    (fun r hr ↦ Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hr; omega))
    (fun r₁ hr₁ r₂ hr₂ h ↦ by
      have := Finset.mem_Icc.mp hr₁; have := Finset.mem_Icc.mp hr₂
      omega)
    (fun x hx ↦ ⟨x + 1, Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hx; omega⟩,
      by omega⟩)
    (fun r hr ↦ by
      have hr1 : r - 1 + 1 = r := (by have := Finset.mem_Icc.mp hr; omega)
      rw [hr1])
/- ## Hybrid Circuit (`s < k - 1` Batch Loop + `s = k - 1` `eigLockStage`) -/
/-- Hybrid batch circuit for `200 ≤ n` and `1 ≤ k`: runs simultaneous `b s`-group projective
  Grover batch rounds (`K_varPhi (idx s) n (g s) (k - s)` iterations) while `σ res < k - 1`,
  followed
  by the stationary 1-call `.qWhile` `eigLockStage` at `s = k - 1` (`r = 1`), and measures
  `memReg`. -/
noncomputable def stage2HybridCircuit {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) (hkN : k ≤
    2 ^ n) {b g : ℕ → ℕ} (idx : ℕ → Fin 44) (hbg : ∀ s < k, b s * g s = m) : OracleCirc Var
    (Stage1.qubits n m k) ((n + 1) * m) :=
  findAllBatchWithLast res (one_le_of_mem_groverGrid hm_grid) hkN hbg
    (fun s ↦ K_varPhi (idx s) n (g s) (k - s))
    (eigLockStage res n m k hm_grid hk_grid hn200 ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
/-- Total correctness (`wp = ⊤`) of `qset;; stage2HybridCircuit` for any schedule `(b, g,
  idx)`
  with `b s * g s = m` and `1 ≤ b s` for `s < k - 1`. -/
theorem wp_stage2HybridCircuit_eq_top {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) (hkN : k ≤
    2 ^ n) {b g : ℕ → ℕ} (idx : ℕ → Fin 44) (hbg : ∀ s < k, b s * g s = m) (hb : ∀ s < k - 1, 1 ≤ b
    s) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) : wp (.qSet ;; (stage2HybridCircuit res
    hm_grid hk_grid hn200 hk1 hkN idx hbg).compile qAssign (groverParallelMarkingOracle m S))
    (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S) = ⊤ := by
  unfold stage2HybridCircuit Stage1.qubits; have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid; have hn100 : 100 ≤ n := (by omega)
  refine wp_findAllBatchWithLast_eq_top res hm1 hk1 hkN hbg hb (fun s ↦ K_varPhi (idx s) n (g s)
    (k - s)) (eigLockStage res n m k hm_grid hk_grid hn200 ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
    hcard (fun s hs ↦ ?_) (wp_eigLockStage_last_workMemIdx_eq_one res hm_grid hk_grid hn200 hk1
    hcard)
  have hsk : s < k := (by omega); have hbg_s := hbg s hsk
  have hg1 : 1 ≤ g s := by
    by_contra! hg0
    have : g s = 0 := (by omega); rw [this, mul_zero] at hbg_s; omega
  have hg_hi : g s ≤ 1024 := by
    have hle : g s ≤ m := (by rw [← hbg_s]; exact Nat.le_mul_of_pos_left (g s) (hb s hs))
    exact hle.trans hm_hi
  exact (varPhiGroupSuccProb_bounds (idx s) hn100 hg1 hg_hi (by omega) (by omega)).1
/-- Full 121-cell hybrid circuit parameterized by a slot-group and phase-angle schedule
  `(b_fn, g_fn, idx_fn)` on `2 ≤ m`, `2 ≤ r ≤ 1024`: dispatches `2 ≤ m ∧ 2 ≤ k ∧ 200 ≤ n ∧ k
  ≤ 2 ^ n`
  to `stage2HybridCircuit` and falls back to `Stage1.circuit` on the `21` boundary cells
  (`m = 1 ∨ k = 1`) and finite-`n` prefix (`n < 200` or `2 ^ n < k`). -/
noncomputable def circuitWithSchedule {Var : Type} [DecidableEq Var] (res : Var) (b_fn g_fn : ℕ → ℕ
    → ℕ) (idx_fn : ℕ → ℕ → Fin 44) (hbg_fn : ∀ {m r : ℕ}, m ∈ groverGrid → 2 ≤ m → 2 ≤ r → r ≤ 1024
    → 1 ≤ b_fn m r ∧ b_fn m r * g_fn m r = m) (n m k : ℕ) : OracleCirc Var (Stage1.qubits n m k)
    ((n + 1) * m) :=
  if hcell : m ∈ groverGrid ∧ k ∈ groverGrid then
    if h2 : 2 ≤ m ∧ 2 ≤ k then
      if hn200 : 200 ≤ n then
        if hkN : k ≤ 2 ^ n then
          stage2HybridCircuit res hcell.1 hcell.2 hn200 (by omega) hkN
            (b := fun s ↦ if s < k - 1 then b_fn m (k - s) else 1)
            (g := fun s ↦ if s < k - 1 then g_fn m (k - s) else m)
            (fun s ↦ idx_fn m (k - s))
            (fun s _ ↦ by
              by_cases hlt : s < k - 1
              · rw [ite_eq_left hlt, ite_eq_left hlt]
                have hk_hi := le_1024_of_mem_groverGrid hcell.2
                exact (hbg_fn hcell.1 h2.1 (by omega) (by omega)).2
              · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul])
        else Stage1.circuit res n m k
      else Stage1.circuit res n m k
    else Stage1.circuit res n m k
  else Stage1.circuit res n m k
/-- Total correctness across all `121 / 121` cells of `groverGrid` for
  `circuitWithSchedule`. -/
theorem correctnessWithSchedule {Var : Type} [DecidableEq Var] (res : Var) (b_fn g_fn : ℕ → ℕ → ℕ)
    (idx_fn : ℕ → ℕ → Fin 44) (hbg_fn : ∀ {m r : ℕ}, m ∈ groverGrid → 2 ≤ m → 2 ≤ r → r ≤ 1024 → 1 ≤
    b_fn m r ∧ b_fn m r * g_fn m r = m) {n m k : ℕ} (hn : 1 ≤ n) (hmk : Stage1.cells m k = true)
    (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) : ⦃ (⊤ :
    CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄ (qset ;; (circuitWithSchedule res b_fn g_fn
      idx_fn
    hbg_fn n m k).compile qAssign (groverParallelMarkingOracle m S)) ⦃ liftPureProp (fun σ ↦
    decodeTargets n k (σ res) = S) ⦄ := by
  have hcell := Stage1.cells_mem_grid hmk
  have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2; unfold circuitWithSchedule
  rw [dite_eq_left hcell]; by_cases h2 : 2 ≤ m ∧ 2 ≤ k
  · rw [dite_eq_left h2]; by_cases hn200 : 200 ≤ n
    · rw [dite_eq_left hn200, dite_eq_left hkN]; refine Triple.of_eq_wp ?_
      symm
      refine wp_stage2HybridCircuit_eq_top res hcell.1 hcell.2 hn200 (by omega) hkN (fun s ↦ idx_fn
        m (k - s)) _ (fun s hs ↦ ?_) hcard
      rw [ite_eq_left hs]; have hk_hi := le_1024_of_mem_groverGrid hcell.2
      exact (hbg_fn hcell.1 h2.1 (by omega) (by omega)).1
    · rw [dite_eq_right hn200]; exact Stage1.correctness res hn hmk hkN hS
  · rw [dite_eq_right h2]; exact Stage1.correctness res hn hmk hkN hS
/-- Certified 1-sweep parameter table `(phi_idx, A1_int, A2_int, B_int, num, den)` at `(im, ik)`
  (`m = 2 ^ (im + 1)`, `k = 2 ^ (ik + 1)`) for the `37` `m ≥ k` cells certified by the
  1-sweep
  variable-`Φ` prefix-subcube pre-pass + 2-indicator analysis. -/
def stage5Param : ℕ → ℕ → Option (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
  | 0, 0 => some (3, 818310000, 460863514, 0, 372003, 500000)
  | 1, 0 => some (10, 818310000, 358811919, 0, 164373, 250000)
  | 1, 1 => some (0, 536284904, 76786823, 282025096, 123453, 200000)
  | 2, 0 => some (12, 818310000, 319830398, 0, 60487, 100000)
  | 2, 1 => some (11, 639376346, 140896744, 178933654, 10561, 20000)
  | 3, 0 => some (13, 818310000, 314088737, 0, 288557, 500000)
  | 3, 1 => some (17, 695377669, 191156406, 122932331, 450899, 1000000)
  | 4, 0 => some (14, 818310000, 303651376, 0, 281449, 500000)
  | 4, 1 => some (19, 716592713, 201934089, 101717287, 402577, 1000000)
  | 4, 2 => some (18, 716592713, 201934089, 101717287, 179221, 500000)
  | 4, 3 => some (4, 738104605, 244957873, 80205395, 31717, 100000)
  | 5, 0 => some (15, 818310000, 296730245, 0, 555731, 1000000)
  | 5, 1 => some (20, 721797020, 200217265, 96512980, 94007, 250000)
  | 5, 2 => some (23, 721797020, 200217265, 96512980, 302291, 1000000)
  | 5, 4 => some (6, 1078838587, 0, 50768986, 234151, 1000000)
  | 6, 0 => some (16, 818310000, 296730245, 0, 276073, 500000)
  | 6, 1 => some (21, 721797020, 200217265, 96512980, 362169, 1000000)
  | 6, 2 => some (24, 721797020, 200217265, 96512980, 133377, 500000)
  | 6, 3 => some (24, 721797020, 200217265, 96512980, 242447, 1000000)
  | 6, 5 => some (7, 1179323352, 0, 30445886, 86709, 500000)
  | 7, 0 => some (16, 818310000, 296730245, 0, 68793, 125000)
  | 7, 1 => some (21, 721797020, 200217265, 96512980, 88771, 250000)
  | 7, 2 => some (25, 721797020, 200217265, 96512980, 123387, 500000)
  | 7, 3 => some (27, 721797020, 200217265, 96512980, 203451, 1000000)
  | 7, 5 => some (5, 1276644278, 0, 17914493, 4903, 31250)
  | 8, 0 => some (16, 818310000, 296730245, 0, 549443, 1000000)
  | 8, 1 => some (22, 721984365, 200404610, 96325635, 351493, 1000000)
  | 8, 2 => some (26, 721984365, 200404610, 96325635, 59049, 250000)
  | 8, 3 => some (29, 721984365, 200404610, 96325635, 44611, 250000)
  | 8, 4 => some (28, 721984365, 200404610, 96325635, 82571, 500000)
  | 8, 6 => some (7, 1378958234, 0, 10083109, 5723, 50000)
  | 9, 0 => some (16, 818310000, 296730245, 0, 8578, 15625)
  | 9, 1 => some (22, 721984365, 200404610, 96325635, 349689, 1000000)
  | 9, 2 => some (26, 721984365, 200404610, 96325635, 28843, 125000)
  | 9, 3 => some (29, 721984365, 200404610, 96325635, 2567, 15625)
  | 9, 4 => some (30, 721984365, 200404610, 96325635, 34527, 250000)
  | 9, 7 => some (8, 1474351518, 0, 5681845, 83711, 1000000)
  | _, _ => none
/-- Certified multi-sweep parameter table
  `(isModeB, first_nat, rest_nats, A1_int, A2_int, B_int, num, den)` at `(im, ik)`
  (`m = 2 ^ (im + 1)`, `k = 2 ^ (ik + 1)`) for the `25` cells upgraded by the `L`-sweep
  coherent
  prefix-subcube deflation pre-pass (`subcubeMultiSweepBatchWithLast`, `11 ModeA + 14
  ModeB`). -/
def stage6MultiParam : ℕ → ℕ → Option (Bool × ℕ × List ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
  | 0, 1 => some (false, 12, [], 423665813, 66219327, 394644187, 3580589, 5000000)
  | 1, 1 => some (false, 19, [], 536284904, 76786823, 282025096, 6158887, 10000000)
  | 1, 2 => some (false, 11, [], 624609373, 345311351, 193700627, 5674687, 10000000)
  | 2, 2 => some (false, 18, [], 632316018, 133836416, 185993982, 599241, 1250000)
  | 3, 2 => some (true, 18, [30], 504225790, 0, 314084210, 31686, 78125)
  | 3, 3 => some (true, 13, [18, 30], 504225790, 0, 314084210, 902219, 2500000)
  | 3, 4 => some (false, 10, [15], 749667795, 624847838, 68642205, 1645497, 5000000)
  | 4, 3 => some (true, 20, [31], 514658624, 0, 303651376, 3076077, 10000000)
  | 4, 4 => some (false, 13, [24], 738225996, 245200655, 80084004, 683931, 2500000)
  | 5, 0 => some (false, 29, [], 521579755, 0, 296730245, 694663, 1250000)
  | 5, 3 => some (true, 19, [31], 521579755, 0, 296730245, 329223, 1250000)
  | 5, 4 => some (true, 12, [19, 31], 521579755, 0, 296730245, 143051, 625000)
  | 5, 5 => some (false, 15, [25], 767867108, 310384981, 50442892, 1009107, 5000000)
  | 6, 4 => some (true, 21, [32], 521579755, 0, 296730245, 967461, 5000000)
  | 6, 5 => some (true, 14, [20, 32], 521579755, 0, 296730245, 835233, 5000000)
  | 7, 4 => some (true, 19, [33], 521579755, 0, 296730245, 8693, 50000)
  | 7, 5 => some (true, 9, [20, 33], 521579755, 0, 296730245, 1511027, 10000000)
  | 8, 3 => some (false, 33, [], 721984365, 200404610, 96325635, 892217, 5000000)
  | 8, 5 => some (true, 21, [34], 521579755, 0, 296730245, 624633, 5000000)
  | 8, 6 => some (true, 13, [21, 34], 521579755, 0, 296730245, 539651, 5000000)
  | 9, 3 => some (false, 33, [], 721984365, 200404610, 96325635, 1642871, 10000000)
  | 9, 4 => some (false, 34, [], 721984365, 200404610, 96325635, 55243, 400000)
  | 9, 5 => some (true, 20, [34], 521579755, 0, 296730245, 14611, 125000)
  | 9, 6 => some (true, 23, [35], 521579755, 0, 296730245, 936209, 10000000)
  | 9, 7 => some (true, 15, [22, 35], 521579755, 0, 296730245, 156081, 2000000)
  | _, _ => none
/-- Certified coprime multi-stage relative-cost bound across all `121 / 121` cells of
  `groverGrid` (`stage1RelCost` on all `21` `m = 1 ∨ k = 1` boundary cells). -/
def stage5RelCost (m k : ℕ) : ℚ≥0 :=
  if 2 ≤ m ∧ 2 ≤ k then
    let gm := Stage2CertInternals.gridExp m
    let gk := Stage2CertInternals.gridExp k
    if 1 ≤ gm ∧ gm ≤ 10 ∧ 1 ≤ gk ∧ gk ≤ 10 then
      match stage6MultiParam (gm - 1) (gk - 1) with
      | some (_, _, _, _, _, _, num, den) => (num : ℚ≥0) / (den : ℚ≥0)
      | none =>
        match stage5Param (gm - 1) (gk - 1) with
        | some (_, _, _, _, num, den) => (num : ℚ≥0) / (den : ℚ≥0)
        | none => stage2RelCost m k
    else stage2RelCost m k
  else stage1RelCost
end
public section
/-- Hybrid 1-sweep `m ≥ k` circuit (`200 ≤ n`, `1 ≤ k`, `m = 2 ^ p`): runs 1 coherent variable-`Φ`
  prefix-subcube pre-sweep (`K_subcube sub_idx (n - p)` iterations) at `T = ∅` followed by
  `findAllBatchTail` (`K_varPhi (idx s)` batch rounds + `s = k - 1` `eigLockStage`). -/
noncomputable def stage5SubcubeCircuit {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) (hkN : k ≤
    2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (sub_idx : Fin 31) {b g : ℕ → ℕ} (idx : ℕ → Fin 44) (hbg :
    ∀ s < k, b s * g s = m) : OracleCirc Var (Stage1.qubits n m k) ((n + 1) * m) :=
  subcubeBatchWithLast res (one_le_of_mem_groverGrid hm_grid) hkN hp hm hbg
    (K_subcube sub_idx (n - p))
    (fun s ↦ K_varPhi (idx s) n (g s) (k - s))
    (eigLockStage res n m k hm_grid hk_grid hn200 ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
/-- Total correctness (`wp = ⊤`) of `.qSet;; stage5SubcubeCircuit`. -/
theorem wp_stage5SubcubeCircuit_eq_top {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) (hkN : k ≤
    2 ^ n) (hp : p ≤ n) (hm : m = 2 ^ p) (sub_idx : Fin 31) {b g : ℕ → ℕ} (idx : ℕ → Fin 44) (hbg :
    ∀ s < k, b s * g s = m) (hb : ∀ s < k - 1, 1 ≤ b s) {S : Finset (Fin (2 ^ n))} (hcard : S.card =
    k) : wp (.qSet ;; (stage5SubcubeCircuit res hm_grid hk_grid hn200 hk1 hkN hp hm sub_idx idx
    hbg).compile qAssign (groverParallelMarkingOracle m S)) (liftPureProp fun σ ↦ decodeTargets n k
    (σ res) = S) = ⊤ := by
  unfold stage5SubcubeCircuit Stage1.qubits; have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid; have hn100 : 100 ≤ n := (by omega)
  refine wp_subcubeBatchWithLast_eq_top res hm1 hk1 hkN hp hm hbg hb (K_subcube sub_idx (n - p))
    (fun s ↦ K_varPhi (idx s) n (g s) (k - s)) (eigLockStage res n m k hm_grid hk_grid hn200 ⟨k - 1,
    Nat.sub_lt hk1 zero_lt_one⟩) hcard (fun s hs ↦ ?_) (wp_eigLockStage_last_workMemIdx_eq_one res
    hm_grid hk_grid hn200 hk1 hcard)
  have hsk : s < k := (by omega); have hbg_s := hbg s hsk
  have hg1 : 1 ≤ g s := by
    by_contra! hg0
    have : g s = 0 := (by omega); rw [this, mul_zero] at hbg_s; omega
  have hg_hi : g s ≤ 1024 := by
    have hle : g s ≤ m := (by rw [← hbg_s]; exact Nat.le_mul_of_pos_left (g s) (hb s hs))
    exact hle.trans hm_hi
  exact (varPhiGroupSuccProb_bounds (idx s) hn100 hg1 hg_hi (by omega) (by omega)).1
/-- Hybrid multi-sweep circuit (`200 ≤ n`, `1 ≤ k`, `m = 2 ^ p`): executes `L ≥ 1` coherent
  variable-`Φ` prefix-subcube deflation sweeps (`K_multi firstIdx (n - p)` followed by
  `multiAllKs (n - p) restIdxs`) before `findAllBatchTail`. -/
noncomputable def stage6MultiSweepCircuit {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) (hkN : k ≤
    2 ^ n) (hp10 : p ≤ 10) (hm : m = 2 ^ p) (firstIdx : Fin multiPaletteLen) (restIdxs : List (Fin
    multiPaletteLen)) {b g : ℕ → ℕ} (idx : ℕ → Fin 44) (hbg : ∀ s < k, b s * g s = m) : OracleCirc
    Var (Stage1.qubits n m k) ((n + 1) * m) :=
  subcubeMultiSweepBatchWithLast res (one_le_of_mem_groverGrid hm_grid) hkN
    (hp10.trans (by omega)) hm hbg
    (K_multi firstIdx (n - p))
    (multiAllKs (n - p) restIdxs)
    (fun s ↦ K_varPhi (idx s) n (g s) (k - s))
    (eigLockStage res n m k hm_grid hk_grid hn200 ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
/-- Total correctness (`wp = ⊤`) of `.qSet;; stage6MultiSweepCircuit`. -/
theorem wp_stage6MultiSweepCircuit_eq_top {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hk1 : 1 ≤ k) (hkN : k ≤
    2 ^ n) (hp10 : p ≤ 10) (hm : m = 2 ^ p) (firstIdx : Fin multiPaletteLen) (restIdxs : List (Fin
    multiPaletteLen)) {b g : ℕ → ℕ} (idx : ℕ → Fin 44) (hbg : ∀ s < k, b s * g s = m) (hb : ∀ s <
    k - 1, 1 ≤ b s) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) : wp (.qSet ;;
    (stage6MultiSweepCircuit res hm_grid hk_grid hn200 hk1 hkN hp10 hm firstIdx restIdxs idx
    hbg).compile qAssign (groverParallelMarkingOracle m S)) (liftPureProp fun σ ↦ decodeTargets n k
    (σ res) = S) = ⊤ := by
  unfold stage6MultiSweepCircuit Stage1.qubits; have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid; have hn100 : 100 ≤ n := (by omega)
  refine wp_subcubeMultiSweepBatchWithLast_eq_top res hm1 hk1 hkN (hp10.trans (by omega)) hm hbg hb
    (K_multi firstIdx (n - p)) (multiAllKs (n - p) restIdxs) (fun s ↦ K_varPhi (idx s) n (g s) (k -
    s)) (eigLockStage res n m k hm_grid hk_grid hn200 ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩) hcard
    (fun s hs ↦ ?_) (wp_eigLockStage_last_workMemIdx_eq_one res hm_grid hk_grid hn200 hk1 hcard)
  have hsk : s < k := (by omega); have hbg_s := hbg s hsk
  have hg1 : 1 ≤ g s := by
    by_contra! hg0
    have : g s = 0 := (by omega); rw [this, mul_zero] at hbg_s; omega
  have hg_hi : g s ≤ 1024 := by
    have hle : g s ≤ m := (by rw [← hbg_s]; exact Nat.le_mul_of_pos_left (g s) (hb s hs))
    exact hle.trans hm_hi
  exact (varPhiGroupSuccProb_bounds (idx s) hn100 hg1 hg_hi (by omega) (by omega)).1
/-- Full 121-cell circuit: dispatches the `25` certified multi-sweep (`ModeA + ModeB`)
  cells to `stage6MultiSweepCircuit`, the `37` certified 1-sweep `m ≥ k` cells to
  `stage5SubcubeCircuit`, and all remaining cells to `circuitWithSchedule`. -/
noncomputable def stage5Circuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleCirc Var (Stage1.qubits n m k) ((n + 1) * m) :=
  if hcell : m ∈ groverGrid ∧ k ∈ groverGrid then
    if h2 : 2 ≤ m ∧ 2 ≤ k then
      match stage6MultiParam (Stage2CertInternals.gridExp m - 1)
          (Stage2CertInternals.gridExp k - 1) with
      | some (_, first_nat, rest_nats, _, _, _, _, _) =>
        if hn200 : 200 ≤ n then
          if hkN : k ≤ 2 ^ n then
            stage6MultiSweepCircuit res hcell.1 hcell.2 hn200 (by omega) hkN
              (p := Stage2CertInternals.gridExp m)
              (Stage2CertInternals.gridExp_bounds_of_mem hcell.1 h2.1).2.1
              (Stage2CertInternals.gridExp_bounds_of_mem hcell.1 h2.1).2.2.symm
              ⟨first_nat % multiPaletteLen, Nat.mod_lt _ (by decide)⟩
              (rest_nats.map fun x ↦ ⟨x % multiPaletteLen, Nat.mod_lt _ (by decide)⟩)
              (b := fun s ↦ if s < k - 1 then stage2Batch m (k - s) else 1)
              (g := fun s ↦ if s < k - 1 then stage2Group m (k - s) else m)
              (fun s ↦ stage2Angle m (k - s))
              (fun s _ ↦ by
                by_cases hlt : s < k - 1
                · rw [ite_eq_left hlt, ite_eq_left hlt]
                  have hk_hi := le_1024_of_mem_groverGrid hcell.2
                  exact (stage2_bg hcell.1 h2.1 (by omega) (by omega)).2
                · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul])
          else Stage1.circuit res n m k
        else Stage1.circuit res n m k
      | none =>
        match stage5Param (Stage2CertInternals.gridExp m - 1)
            (Stage2CertInternals.gridExp k - 1) with
        | some (idx_nat, _, _, _, _, _) =>
          if hn200 : 200 ≤ n then
            if hkN : k ≤ 2 ^ n then
              stage5SubcubeCircuit res hcell.1 hcell.2 hn200 (by omega) hkN
                (p := Stage2CertInternals.gridExp m)
                (by
                  have hb := Stage2CertInternals.gridExp_bounds_of_mem hcell.1 h2.1
                  omega)
                (Stage2CertInternals.gridExp_bounds_of_mem hcell.1 h2.1).2.2.symm
                ⟨idx_nat % 31, Nat.mod_lt _ (Nat.zero_lt_succ 30)⟩
                (b := fun s ↦ if s < k - 1 then stage2Batch m (k - s) else 1)
                (g := fun s ↦ if s < k - 1 then stage2Group m (k - s) else m)
                (fun s ↦ stage2Angle m (k - s))
                (fun s _ ↦ by
                  by_cases hlt : s < k - 1
                  · rw [ite_eq_left hlt, ite_eq_left hlt]
                    have hk_hi := le_1024_of_mem_groverGrid hcell.2
                    exact (stage2_bg hcell.1 h2.1 (by omega) (by omega)).2
                  · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul])
            else Stage1.circuit res n m k
          else Stage1.circuit res n m k
        | none =>
          circuitWithSchedule res stage2Batch stage2Group stage2Angle stage2_bg n m k
    else circuitWithSchedule res stage2Batch stage2Group stage2Angle stage2_bg n m k
  else circuitWithSchedule res stage2Batch stage2Group stage2Angle stage2_bg n m k
end
/- ## Top-Level `DickeSol.FindAll` Exports for `GroverFindAllRelCost` -/
namespace FindAll
@[expose] public section
/-- Claimed dyadic grid cells `(m, k)` for `groverFindAll` (`121 / 121` cells of
  `groverGrid`). -/
abbrev cells (m k : ℕ) : Bool := Stage1.cells m k
theorem cells_mem_grid {m k : ℕ} (hmk : cells m k = true) : m ∈ groverGrid ∧ k ∈ groverGrid :=
  Stage1.cells_mem_grid hmk
/-- Total qubits used by `FindAll.circuit`: `m * (n + 1)` work qubits + `k * n` archive
  qubits. -/
abbrev qubits (n m k : ℕ) : ℕ := Stage1.qubits n m k
/-- Claimed asymptotic expected parallel-round cost ratio relative to `vanillaFindAllCost`. -/
abbrev relCost (m k : ℕ) : ℚ≥0 := stage5RelCost m k
end
public section
/-- Parallel multi-target search circuit across all `121 / 121` cells of `groverGrid`. -/
noncomputable def circuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleCirc Var (qubits n m k) ((n + 1) * m) := stage5Circuit res n m k
/-- Compiled `groverFindAll` program with initial reset `qset`. -/
noncomputable abbrev program {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : QProg Var (2 ^ qubits n m k) :=
  qset ;; (circuit res n m k).compile qAssign oracle
/-- Exact probability-`1` recovery of `S` for `FindAll.program` across all `121 / 121`
  cells. -/
theorem correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hn : 1 ≤ n) (hmk : cells
    m k = true) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) : ⦃ (⊤
    : CQAssertion (Store Var) (2 ^ qubits n m k)) ⦄ program res n m k (groverParallelMarkingOracle m
      S) ⦃
    liftPureProp fun σ ↦ decodeTargets n k (σ res) = S ⦄ := by
  have hcell := Stage1.cells_mem_grid hmk
  have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2; unfold program circuit stage5Circuit
  rw [dite_eq_left hcell]; by_cases h2 : 2 ≤ m ∧ 2 ≤ k
  · rw [dite_eq_left h2]
    cases hparam_c : stage6MultiParam (Stage2CertInternals.gridExp m - 1)
        (Stage2CertInternals.gridExp k - 1) with
    | some val_c =>
      rcases val_c with ⟨_, first_nat, rest_nats, _, _, _, _, _⟩; dsimp only
      by_cases hn200 : 200 ≤ n
      · rw [dite_eq_left hn200, dite_eq_left hkN]; refine Triple.of_eq_wp ?_
        symm
        refine wp_stage6MultiSweepCircuit_eq_top res hcell.1 hcell.2 hn200 (by omega) hkN _ _ _ _
          (fun s ↦ stage2Angle m (k - s)) _ (fun s hs ↦ ?_) hcard
        rw [ite_eq_left hs]; have hk_hi := le_1024_of_mem_groverGrid hcell.2
        exact (stage2_bg hcell.1 h2.1 (by omega) (by omega)).1
      · rw [dite_eq_right hn200]; exact Stage1.correctness res hn hmk hkN hS
    | none =>
      dsimp only; cases hparam : stage5Param (Stage2CertInternals.gridExp m - 1)
          (Stage2CertInternals.gridExp k - 1) with
      | none =>
        exact correctnessWithSchedule res stage2Batch stage2Group stage2Angle stage2_bg hn hmk hkN
          hS
      | some val =>
        rcases val with ⟨idx_nat, _, _, _, _, _⟩; dsimp only; by_cases hn200 : 200 ≤ n
        · rw [dite_eq_left hn200, dite_eq_left hkN]; refine Triple.of_eq_wp ?_
          symm; refine wp_stage5SubcubeCircuit_eq_top res hcell.1 hcell.2 hn200 (by omega) hkN _ _ _
            (fun s ↦ stage2Angle m (k - s)) _ (fun s hs ↦ ?_) hcard
          rw [ite_eq_left hs]; have hk_hi := le_1024_of_mem_groverGrid hcell.2
          exact (stage2_bg hcell.1 h2.1 (by omega) (by omega)).1
        · rw [dite_eq_right hn200]; exact Stage1.correctness res hn hmk hkN hS
  · rw [dite_eq_right h2]
    exact correctnessWithSchedule res stage2Batch stage2Group stage2Angle stage2_bg hn hmk hkN hS
end
end FindAll
end QuantumComputation.Specs.DickeSol
end WD_FindAllStage2
section WD_FindAllRotatedSubcube
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val tensorState)
open Matrix (mulVec_mulVec mulVec_diagonal mulVec_single_one col_apply)
open Complex (normSq)
open List (mem_finRange prod_cons finRange map_cons)
open Fintype (sum_eq_single sum_prod_type)
open Equiv (swap)
open Pi (single)
open scoped Matrix NNReal ENNReal ComplexOrder MatrixOrder QProg.Notation QHLExpectation
@[expose] public section
/- ## Section 1: Subset-Markov Bellman Operators (`rfl`-Aligned with Analysis) -/
end
public section
/- ## Section 2: Permuted Single-Slot & `m`-Slot Unitaries and Uniform Bucket Readout -/
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllRotatedSubcube
section WD_FindAllRotatedSubcubeAnalysis
namespace QuantumComputation.Specs.DickeSol
open Real
@[expose] public section
/- ## Section 1: Disjoint `p`-Bit Coordinate Windows & Involutive Slice-Swap Permutations -/
/-- Canonical decomposition of `Fin (2 ^ n)` (`s + W * p = n`, `m = 2 ^ p`) into a low
  `s`-bit
  suffix in `Fin (2 ^ s)` and `W` disjoint `p`-bit slice coordinates in `Fin W → Fin m`. -/
noncomputable def rotatedSliceEquiv {n s W p m : ℕ} (h : s + W * p = n) (hm : m = 2 ^ p) :
    Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m) :=
  (finCongr (by rw [h])).symm.trans
    ((lowHighEquiv s (W * p)).trans
      (Equiv.prodCongr (.refl _)
        ((addrEquiv p W).trans (Equiv.piCongrRight fun _ ↦ finCongr hm.symm))))
/-- Involutive permutation on `Fin (2 ^ n)` swapping the `t`-th `p`-bit slice coordinate
  with the
  top `p`-bit slice coordinate `⟨W - 1, _⟩` (`bits [n - p.. n)`), fixing the `s`-bit suffix
  and all
  other `p`-bit slices. -/
noncomputable def rotatedSliceSwapPerm {n s W p m : ℕ} (h : s + W * p = n) (hm : m = 2 ^ p)
    (hW : 0 < W) (t : Fin W) : Equiv.Perm (Fin (2 ^ n)) :=
  let top : Fin W := ⟨W - 1, by omega⟩
  let swapSlices : Equiv.Perm (Fin W → Fin m) :=
    { toFun := fun g i ↦ g (Equiv.swap t top i)
      invFun := fun g i ↦ g (Equiv.swap t top i)
      left_inv := fun g ↦ funext fun i ↦ by simp
      right_inv := fun g ↦ funext fun i ↦ by simp }
  (rotatedSliceEquiv h hm).trans
    ((Equiv.prodCongr (.refl (Fin (2 ^ s))) swapSlices).trans (rotatedSliceEquiv h hm).symm)
theorem rotatedSliceSwapPerm_apply_equiv {n s W p m : ℕ} (h : s + W * p = n) (hm : m = 2 ^ p) (hW :
    0 < W) (t : Fin W) (x : Fin (2 ^ n)) : rotatedSliceEquiv h hm (rotatedSliceSwapPerm h hm hW t x)
    = ((rotatedSliceEquiv h hm x).1, fun i : Fin W ↦ (rotatedSliceEquiv h hm x).2 (Equiv.swap t ⟨W -
    1, by omega⟩ i)) := by
  unfold rotatedSliceSwapPerm; simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl]; rfl
/-- Top slice coordinate `⟨W - 1, _⟩` of `rotatedSliceEquiv` coincides identically with
  `FindAllSubcube.subcubePref` (`bits [n - p.. n)`). -/
theorem subcubePref_eq_rotatedSliceEquiv_top {n s W p m : ℕ} (h : s + W * p = n)
    (hp : p ≤ n) (hm : m = 2 ^ p) (hW : 0 < W) (x : Fin (2 ^ n)) :
    subcubePref hp hm x = (rotatedSliceEquiv h hm x).2 ⟨W - 1, by omega⟩ := by
  ext
  have hsub : n - p = s + (W - 1) * p := by
    have hWp : W * p = (W - 1) * p + p := by
      conv_lhs => rw [← Nat.sub_add_cancel hW, Nat.add_mul, Nat.one_mul]
    omega
  have hlhs : (subcubePref hp hm x).val = x.val / 2 ^ (n - p) := by
    let y0 : Fin (2 ^ (n - p + p)) := finCongr (by congr 1; omega) x
    have hy0 : y0.val = x.val := (by simp [y0]); change (finCongr hm.symm (lowHighEquiv (n - p) p
      y0).2).val = _; rw [finCongr_apply, Fin.val_cast, lowHighEquiv_snd_val, hy0]
  have hrhs : ((rotatedSliceEquiv h hm x).2 ⟨W - 1, by omega⟩).val = ((x.val / 2 ^ s) / (2 ^ p) ^ (W
    - 1)) % 2 ^ p := by
    let x0 : Fin (2 ^ (s + W * p)) := (finCongr (by rw [h])).symm x
    have hx0 : x0.val = x.val := (by simp [x0]); have hhi : (lowHighEquiv s (W * p) x0).2.val =
      x.val / 2 ^ s := (by rw [lowHighEquiv_snd_val, hx0])
    change (finCongr hm.symm (addrEquiv p W (lowHighEquiv s (W * p) x0).2 ⟨W - 1, by omega⟩)).val =
      _; rw [finCongr_apply, Fin.val_cast, addrEquiv_eq_div_pow_mod, hhi]
  rw [hlhs, hrhs, Nat.div_div_eq_div_mul, ← pow_mul, Nat.mul_comm p (W - 1), ← pow_add, ← hsub]
  have hlt : x.val / 2 ^ (n - p) < 2 ^ p :=
    (by rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_of_le hp]; exact x.isLt)
  exact (Nat.mod_eq_of_lt hlt).symm
/-- Conjugating by `rotatedSliceSwapPerm h hm hW t` routes the `t`-th `p`-bit coordinate
  slice
  directly into `subcubePref hp hm` (`bits [n - p.. n)`). -/
theorem subcubePref_rotatedSliceSwapPerm {n s W p m : ℕ} (h : s + W * p = n) (hp : p ≤ n) (hm : m =
  2 ^ p) (hW : 0 < W) (t : Fin W) (x : Fin (2 ^ n)) : subcubePref hp hm (rotatedSliceSwapPerm h hm
  hW t x) = (rotatedSliceEquiv h hm x).2 t := by
  rw [subcubePref_eq_rotatedSliceEquiv_top h hp hm hW, rotatedSliceSwapPerm_apply_equiv]
  simp [Equiv.swap_apply_right]
/- ## Section 2: `k!`-Free `GoodSuffix` Suffix-Fiber Bijection & `BadSuffix` Tail Bound -/
/-- Shared `s`-bit suffix projection under any address decomposition
  `e: Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)`. -/
def suffixOf {n s W m : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m))
    (x : Fin (2 ^ n)) : Fin (2 ^ s) :=
  (e x).1
/-- Tuple of `W` slice coordinates in `Fin m` under `e`. -/
def slicesOf {n s W m : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m))
    (x : Fin (2 ^ n)) : Fin W → Fin m :=
  (e x).2
/-- Target set `S` has pairwise-distinct `s`-bit suffixes iff its suffix image has size
  `S.card`. -/
def GoodSuffix {n s W m : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m))
    (S : Finset (Fin (2 ^ n))) : Prop :=
  (S.image (suffixOf e)).card = S.card
instance instDecidableGoodSuffix {n s W m : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m))
    (S : Finset (Fin (2 ^ n))) : Decidable (GoodSuffix e S) :=
  inferInstanceAs (Decidable (_ = _))
/-- Canonical `k!`-free parameterization of a `GoodSuffix` `k`-element target set from its
  ordered
  `k`-element suffix set `U ⊆ Fin (2 ^ s)` and slice-coordinate matrix `f: Fin k → Fin W →
  Fin m`. -/
def mkGoodTargetSet {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m))
    (U : Finset (Fin (2 ^ s))) (hU : U.card = k) (f : Fin k → Fin W → Fin m) :
    Finset (Fin (2 ^ n)) :=
  Finset.univ.image fun i : Fin k ↦ e.symm (U.orderEmbOfFin hU i, f i)
theorem card_mkGoodTargetSet {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)) (U :
  Finset (Fin (2 ^ s))) (hU : U.card = k) (f : Fin k → Fin W → Fin m) : (mkGoodTargetSet e U hU
  f).card = k := by
  unfold mkGoodTargetSet; rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij; have hpair := e.symm.injective hij
    exact (U.orderEmbOfFin hU).injective (congrArg Prod.fst hpair)
theorem image_suffixOf_mkGoodTargetSet {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin
  m)) (U : Finset (Fin (2 ^ s))) (hU : U.card = k) (f : Fin k → Fin W → Fin m) : (mkGoodTargetSet e
  U hU f).image (suffixOf e) = U := by
  apply Finset.eq_of_subset_of_card_le
  · intro u hu; rw [mkGoodTargetSet, Finset.image_image] at hu; rcases Finset.mem_image.mp hu with
      ⟨i, _, rfl⟩; simp [suffixOf, Finset.orderEmbOfFin_mem]
  · rw [hU]; unfold mkGoodTargetSet suffixOf; rw [Finset.image_image,
      Finset.card_image_of_injective]
    · simp
    · intro i j hij; simp only [Function.comp_apply, Equiv.apply_symm_apply] at hij
      exact (U.orderEmbOfFin hU).injective hij
theorem mkGoodTargetSet_mem_filter_goodSuffix {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin
  W → Fin m)) (U : Finset (Fin (2 ^ s))) (hU : U.card = k) (f : Fin k → Fin W → Fin m) :
  mkGoodTargetSet e U hU f ∈ (groverTargetSets n k).filter (GoodSuffix e) := by
  rw [Finset.mem_filter, groverTargetSets, Finset.mem_powersetCard]; refine ⟨⟨Finset.subset_univ _,
    card_mkGoodTargetSet e U hU f⟩, ?_⟩; unfold GoodSuffix; rw [image_suffixOf_mkGoodTargetSet,
    card_mkGoodTargetSet, hU]
/-- Exact `k!`-free sum decomposition over `(groverTargetSets n k).filter (GoodSuffix e)`
  into
  `U ∈ powersetCard k univ` and i.i.d. slice matrices `f: Fin k → Fin W → Fin m`. -/
theorem sum_goodSuffix_groverTargetSets_eq {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W →
  Fin m)) (w : Finset (Fin (2 ^ n)) → ℝ) : (∑ S ∈ (groverTargetSets n k).filter (GoodSuffix e), w S)
  = ∑ U ∈ ((Finset.univ : Finset (Fin (2 ^ s))).powersetCard k).attach, ∑ f : Fin k → Fin W → Fin m,
  w (mkGoodTargetSet e U.1 (Finset.mem_powersetCard.mp U.2).2 f) := by
  classical
  let USet := ((Finset.univ : Finset (Fin (2 ^ s))).powersetCard k).attach
  let FSet := (Finset.univ : Finset (Fin k → Fin W → Fin m))
  rw [← Finset.sum_product']; symm; refine Finset.sum_bij (fun p _ ↦ mkGoodTargetSet e p.1.1
    (Finset.mem_powersetCard.mp p.1.2).2 p.2) (fun p _ ↦ mkGoodTargetSet_mem_filter_goodSuffix e
    p.1.1 _ p.2) (fun p₁ _ p₂ _ heq ↦ ?_) (fun S hS ↦ ?_) (fun _ _ ↦ rfl)
  · have hU_eq : p₁.1.1 = p₂.1.1 := by
      have himg := congrArg (fun T : Finset (Fin (2 ^ n)) ↦ T.image (suffixOf e)) heq
      simpa only [image_suffixOf_mkGoodTargetSet] using himg
    have hp1 : p₁.1 = p₂.1 := Subtype.ext hU_eq; rcases p₁ with ⟨⟨U, hU_mem⟩, f₁⟩; rcases p₂ with
      ⟨⟨_, hU_mem₂⟩, f₂⟩; cases hp1; refine Prod.ext rfl (funext fun i ↦ ?_)
    have hU : U.card = k := (Finset.mem_powersetCard.mp hU_mem).2
    have hmem : e.symm (U.orderEmbOfFin hU i, f₁ i) ∈ mkGoodTargetSet e U hU f₂ :=
      (by rw [← heq]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    simp only [mkGoodTargetSet, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨j, hj⟩ := hmem; have hpair := e.symm.injective hj; have hij : j = i := (U.orderEmbOfFin
      hU).injective (congrArg Prod.fst hpair); subst hij; exact (congrArg Prod.snd hpair).symm
  · rw [Finset.mem_filter, groverTargetSets, Finset.mem_powersetCard] at hS; rcases hS with ⟨⟨_,
      hS_card⟩, hgood⟩
    let U : Finset (Fin (2 ^ s)) := S.image (suffixOf e)
    have hU : U.card = k := hgood.trans hS_card; have hU_mem : U ∈ (Finset.univ : Finset (Fin (2 ^
      s))).powersetCard k := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hU⟩
    have hex (i : Fin k) : ∃ x ∈ S, suffixOf e x = U.orderEmbOfFin hU i := by
      have hmemU : U.orderEmbOfFin hU i ∈ U := Finset.orderEmbOfFin_mem U hU i; simpa only [U,
        Finset.mem_image] using hmemU
    let f : Fin k → Fin W → Fin m := fun i ↦ slicesOf e (Classical.choose (hex i))
    refine ⟨(⟨U, hU_mem⟩, f), Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩, ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro y hy; simp only [mkGoodTargetSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
      obtain ⟨i, rfl⟩ := hy; have hspec := Classical.choose_spec (hex i)
      have hpair : (U.orderEmbOfFin hU i, f i) = e (Classical.choose (hex i)) := Prod.ext
        hspec.2.symm rfl; rw [hpair, Equiv.symm_apply_apply]; exact hspec.1
    · rw [hS_card, card_mkGoodTargetSet]
/-- Exact cardinality `(2 ^ s).choose k * (m ^ W) ^ k` of `GoodSuffix` `k`-element target
  sets. -/
theorem card_goodSuffix_groverTargetSets {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W →
  Fin m)) : ((groverTargetSets n k).filter (GoodSuffix e)).card = (2 ^ s).choose k * (m ^ W) ^ k :=
  by
  have hsum := sum_goodSuffix_groverTargetSets_eq (k := k) e (fun _ ↦ (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_attach, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fun] at hsum; exact_mod_cast hsum
private lemma pow_sub_le_descFactorial_rot (a d : ℕ) : (a - d) ^ d ≤ a.descFactorial d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.descFactorial_succ, pow_succ']; exact Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_left
      (by omega) d).trans ih)
private lemma one_sub_mul_le_pow_of_mem_Icc {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : ∀ d : ℕ, 1 - (d :
  ℝ) * y ≤ (1 - y) ^ d
  | 0 => by simp
  | d + 1 => by
    have ih := one_sub_mul_le_pow_of_mem_Icc hy0 hy1 d; rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hmul : (1 - (d : ℝ) * y) * (1 - y) ≤ (1 - y) ^ d * (1 - y) := mul_le_mul_of_nonneg_right ih
      (by linarith); nlinarith [sq_nonneg y]
/-- Fraction of `S ∈ groverTargetSets n k` failing `GoodSuffix e` is at most `k ^ 2 / 2 ^
  s`. -/
theorem badSuffix_ratio_le {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin W → Fin m)) (hm1 :
  1 ≤ m) (hk_le : k ≤ 2 ^ s) : (((groverTargetSets n k).filter fun S ↦ ¬ GoodSuffix e S).card : ℝ) /
  ((groverTargetSets n k).card : ℝ) ≤ (k : ℝ) ^ 2 / (2 ^ s : ℝ) := by
  let A : ℕ := 2 ^ s; let B : ℕ := m ^ W; have hB1 : 1 ≤ B := Nat.one_le_pow W m hm1
  have hAB : 2 ^ n = A * B := by
    have hc := Fintype.card_congr e; simpa only [Fintype.card_fin, Fintype.card_prod,
      Fintype.card_fun, A, B] using hc
  have hkN : k ≤ 2 ^ n := (by rw [hAB]; exact hk_le.trans (Nat.le_mul_of_pos_right A (by omega)))
  have hcard_all : (groverTargetSets n k).card = (2 ^ n).choose k := (by simp [groverTargetSets])
  have hchoose_pos : 0 < (2 ^ n).choose k := Nat.choose_pos hkN; have hD_pos : (0 : ℝ) <
    ((groverTargetSets n k).card : ℝ) := (by rw [hcard_all]; exact Nat.cast_pos.mpr hchoose_pos)
  have hpart : ((groverTargetSets n k).filter (GoodSuffix e)).card + ((groverTargetSets n k).filter
    fun S ↦ ¬ GoodSuffix e S).card = (groverTargetSets n k).card := by
    have hs := Finset.sum_filter_add_sum_filter_not (groverTargetSets n k) (GoodSuffix e) (fun _ ↦
      (1 : ℕ)); simpa only [Finset.sum_const, smul_eq_mul, mul_one] using hs
  have hkf_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hA_pos : (0 : ℝ) < (A : ℝ) := (by exact_mod_cast (by positivity : 0 < 2 ^ s))
  have hB_pos : (0 : ℝ) < (B : ℝ) := (by exact_mod_cast (by omega : 0 < B))
  have hgood_ratio : 1 - (k : ℝ) ^ 2 / (A : ℝ) ≤ (((groverTargetSets n k).filter (GoodSuffix
    e)).card : ℝ) / ((groverTargetSets n k).card : ℝ) := by
    rw [card_goodSuffix_groverTargetSets e, hcard_all]; change 1 - (k : ℝ) ^ 2 / (A : ℝ) ≤
      ((A.choose k * B ^ k : ℕ) : ℝ) / (((2 ^ n).choose k : ℕ) : ℝ)
    have hnum_nat : k.factorial * (A.choose k * B ^ k) = A.descFactorial k * B ^ k :=
      (by rw [← Nat.mul_assoc, ← Nat.descFactorial_eq_factorial_mul_choose])
    have hden_nat : k.factorial * (2 ^ n).choose k ≤ A ^ k * B ^ k := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, hAB, ← Nat.mul_pow]
      exact Nat.descFactorial_le_pow (A * B) k
    have hstep1 : ((A.descFactorial k * B ^ k : ℕ) : ℝ) / ((A : ℝ) ^ k * (B : ℝ) ^ k) ≤ ((A.choose k
      * B ^ k : ℕ) : ℝ) / (((2 ^ n).choose k : ℕ) : ℝ) := by
      have hnr : (k.factorial : ℝ) * ((A.choose k * B ^ k : ℕ) : ℝ) = ((A.descFactorial k * B ^ k :
        ℕ) : ℝ) := (by exact_mod_cast hnum_nat); have hdr : (k.factorial : ℝ) * (((2 ^ n).choose k :
        ℕ) : ℝ) ≤ (A : ℝ) ^ k * (B : ℝ) ^ k := (by exact_mod_cast hden_nat); rw [← hnr]
      exact (div_le_div_of_nonneg_left (by positivity) (mul_pos hkf_pos (Nat.cast_pos.mpr
        hchoose_pos)) hdr).trans_eq (mul_div_mul_left _ _ hkf_pos.ne')
    have hstep2 : ((A.descFactorial k : ℕ) : ℝ) / (A : ℝ) ^ k = ((A.descFactorial k * B ^ k : ℕ) :
      ℝ) / ((A : ℝ) ^ k * (B : ℝ) ^ k) :=
      (by push_cast; exact (mul_div_mul_right _ _ (pow_pos hB_pos k).ne').symm)
    have hpow_le : (((A - k : ℕ) ^ k : ℕ) : ℝ) ≤ (A.descFactorial k : ℝ) :=
      (by exact_mod_cast pow_sub_le_descFactorial_rot A k)
    set y : ℝ := (k : ℝ) / (A : ℝ); have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg k) hA_pos.le
    have hy1 : y ≤ 1 := (div_le_one hA_pos).mpr (by exact_mod_cast hk_le)
    have hAy : (A : ℝ) * (1 - y) = ((A - k : ℕ) : ℝ) :=
      (by dsimp only [y]; rw [mul_sub, mul_one, mul_div_cancel₀ _ hA_pos.ne', Nat.cast_sub hk_le])
    have hbern : 1 - (k : ℝ) ^ 2 / (A : ℝ) ≤ (1 - y) ^ k := by
      have hb := one_sub_mul_le_pow_of_mem_Icc hy0 hy1 k; have hky : (k : ℝ) * y = (k : ℝ) ^ 2 / (A
        : ℝ) := (by dsimp only [y]; ring); linarith
    refine le_trans ?_ hstep1; rw [← hstep2]
    calc 1 - (k : ℝ) ^ 2 / (A : ℝ) ≤ (1 - y) ^ k := hbern
      _ = ((A : ℝ) * (1 - y)) ^ k / (A : ℝ) ^ k := by
          rw [mul_pow, mul_div_cancel_left₀ _ (pow_pos hA_pos k).ne']
      _ = (((A - k : ℕ) ^ k : ℕ) : ℝ) / (A : ℝ) ^ k := by rw [hAy]; push_cast; rfl
      _ ≤ ((A.descFactorial k : ℕ) : ℝ) / (A : ℝ) ^ k :=
          div_le_div_of_nonneg_right hpow_le (pow_nonneg hA_pos.le k)
  have hsum1 : (((groverTargetSets n k).filter (GoodSuffix e)).card : ℝ) / ((groverTargetSets n
    k).card : ℝ) + (((groverTargetSets n k).filter fun S ↦ ¬ GoodSuffix e S).card : ℝ) /
    ((groverTargetSets n k).card : ℝ) = 1 :=
    (by rw [← add_div, ← Nat.cast_add, hpart, div_self hD_pos.ne']); dsimp only [A] at hgood_ratio;
    push_cast at hgood_ratio; linarith
/-- Turnkey uniform-average reduction over `groverTargetSets n k`: if `0 ≤ w S ≤ W_max` on
  all
  `S ∈ groverTargetSets n k` and the uniform i.i.d. `(Fin k → Fin W → Fin m)` average on
  every
  `GoodSuffix` fiber `U` is at most `G_iid`, then the uniform average over `groverTargetSets
  n k`
  is at most `G_iid + (k ^ 2 / 2 ^ s) * W_max`. -/
theorem avg_groverTargetSets_le_of_goodSuffix {n s W m k : ℕ} (e : Fin (2 ^ n) ≃ Fin (2 ^ s) × (Fin
  W → Fin m)) (hm1 : 1 ≤ m) (hk_le : k ≤ 2 ^ s) {w : Finset (Fin (2 ^ n)) → ℝ} {G_iid W_max : ℝ}
  (hG_nn : 0 ≤ G_iid) (hW_nn : 0 ≤ W_max) (hw_max : ∀ S ∈ groverTargetSets n k, w S ≤ W_max) (hiid :
  ∀ (U : Finset (Fin (2 ^ s))) (hU : U.card = k), (∑ f : Fin k → Fin W → Fin m, w (mkGoodTargetSet e
  U hU f)) / (((m ^ W) ^ k : ℕ) : ℝ) ≤ G_iid) : (∑ S ∈ groverTargetSets n k, w S) /
  ((groverTargetSets n k).card : ℝ) ≤ G_iid + ((k : ℝ) ^ 2 / (2 ^ s : ℝ)) * W_max := by
  have hAB : 2 ^ n = 2 ^ s * m ^ W := by
    have hc := Fintype.card_congr e; simpa only [Fintype.card_fin, Fintype.card_prod,
      Fintype.card_fun] using hc
  have hkN : k ≤ 2 ^ n :=
    (by rw [hAB]; exact hk_le.trans (Nat.le_mul_of_pos_right (2 ^ s) (Nat.one_le_pow W m hm1)))
  have hD_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
    simp only [groverTargetSets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact Nat.cast_pos.mpr (Nat.choose_pos hkN)
  have hM_pos : (0 : ℝ) < (((m ^ W) ^ k : ℕ) : ℝ) :=
    (by exact_mod_cast Nat.pow_pos (Nat.pow_pos (by omega : 0 < m)))
  rw [← Finset.sum_filter_add_sum_filter_not (groverTargetSets n k) (GoodSuffix e), add_div]
  have hgood_sum : (∑ S ∈ (groverTargetSets n k).filter (GoodSuffix e), w S) ≤ (((groverTargetSets n
    k).filter (GoodSuffix e)).card : ℝ) * G_iid := by
    rw [sum_goodSuffix_groverTargetSets_eq e w, card_goodSuffix_groverTargetSets e]
    have hU_each : ∀ U ∈ ((Finset.univ : Finset (Fin (2 ^ s))).powersetCard k).attach, (∑ f : Fin k
      → Fin W → Fin m, w (mkGoodTargetSet e U.1 (Finset.mem_powersetCard.mp U.2).2 f)) ≤ (((m ^ W) ^
      k : ℕ) : ℝ) * G_iid := by
      intro U _; have hle := (div_le_iff₀ hM_pos).mp (hiid U.1 (Finset.mem_powersetCard.mp U.2).2)
      linarith
    refine (Finset.sum_le_sum hU_each).trans_eq ?_; simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hgood_le : (∑ S ∈ (groverTargetSets n k).filter (GoodSuffix e), w S) / ((groverTargetSets n
    k).card : ℝ) ≤ G_iid := by
    have hcard_le : (((groverTargetSets n k).filter (GoodSuffix e)).card : ℝ) ≤ ((groverTargetSets n
      k).card : ℝ) := (by exact_mod_cast Finset.card_filter_le _ _)
    calc (∑ S ∈ (groverTargetSets n k).filter (GoodSuffix e), w S) / ((groverTargetSets n k).card :
          ℝ) ≤ ((((groverTargetSets n k).filter (GoodSuffix e)).card : ℝ) * G_iid) /
          ((groverTargetSets n k).card : ℝ) := div_le_div_of_nonneg_right hgood_sum hD_pos.le
      _ ≤ (((groverTargetSets n k).card : ℝ) * G_iid) /
            ((groverTargetSets n k).card : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard_le hG_nn) hD_pos.le
      _ = G_iid := mul_div_cancel_left₀ G_iid hD_pos.ne'
  have hbad_sum : (∑ S ∈ (groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S), w S) ≤
    (((groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S)).card : ℝ) * W_max := by
    calc (∑ S ∈ (groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S), w S)
        ≤ ∑ _S ∈ (groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S), W_max :=
          Finset.sum_le_sum fun S hS ↦ hw_max S (Finset.mem_filter.mp hS).1
      _ = (((groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S)).card : ℝ) * W_max := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hbad_le : (∑ S ∈ (groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S), w S) /
    ((groverTargetSets n k).card : ℝ) ≤ ((k : ℝ) ^ 2 / (2 ^ s : ℝ)) * W_max := by
    calc (∑ S ∈ (groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S), w S) / ((groverTargetSets
          n k).card : ℝ) ≤ ((((groverTargetSets n k).filter (fun S ↦ ¬ GoodSuffix e S)).card : ℝ) /
          ((groverTargetSets n k).card : ℝ)) * W_max := by
          rw [← mul_div_right_comm]; exact div_le_div_of_nonneg_right hbad_sum hD_pos.le
      _ ≤ ((k : ℝ) ^ 2 / (2 ^ s : ℝ)) * W_max :=
          mul_le_mul_of_nonneg_right (badSuffix_ratio_le e hm1 hk_le) hW_nn
  exact add_le_add hgood_le hbad_le
/- ## Section 3: Pass-by-Pass `GoodSuffix` Fubini Reduction to 1D i.i.d. Multinomial DP -/
/-- Per-slot hit/miss transition probability on a bucket `B: Finset α` under a
  `K_sub`-iteration
  subcube sweep of local dimension `subDim`: misses (`none`) with probability
  `1 - p_succ_frac K_sub B.card subDim`, and hits each `x ∈ B` (`some x`) uniformly with
  probability
  `p_succ_frac K_sub B.card subDim / B.card`. -/
noncomputable def rotSlotHitProb {α : Type*} [DecidableEq α] (subDim K_sub : ℕ)
    (B : Finset α) : Option α → ℝ
  | none => 1 - p_succ_frac K_sub B.card subDim
  | some x => if x ∈ B then p_succ_frac K_sub B.card subDim / (B.card : ℝ) else 0
/-- Finset of distinct elements harvested across `m` subcube slots by `hit: Fin m → Option
  α`. -/
def rotHitFinset {α : Type*} [DecidableEq α] {m : ℕ} (hit : Fin m → Option α) : Finset α :=
  Finset.univ.biUnion fun j ↦ match hit j with | none => ∅ | some x => {x}
/-- Support finset of valid per-slot readout outcomes on surviving target set `R` under
  slice
  projection `pref: α → Fin m`. -/
def rotHitSupport {α : Type*} [DecidableEq α] {m : ℕ} (pref : α → Fin m) (R : Finset α) :
    Finset (Fin m → Option α) :=
  Fintype.piFinset fun j : Fin m ↦ insert none ((R.filter fun x ↦ pref x = j).image some)
/-- Exact single-pass subset-level Bellman step on surviving target set `R` under slice
  projection
  `pref: α → Fin m` and state-dependent schedule `K_opt: ℕ → Option ℕ` (`none` = `.skip` at
  `0`
  queries, `some K_sub` = `stepCost K_sub` plus uniform-within-bucket subcube readout). -/
noncomputable def rotSubsetStep {α : Type*} [DecidableEq α] {m : ℕ} (subDim : ℕ)
    (pref : α → Fin m) (stepCost : ℕ → ℝ) (K_opt : ℕ → Option ℕ)
    (Ψ : Finset α → ℝ) (R : Finset α) : ℝ :=
  match K_opt R.card with
  | none => Ψ R
  | some K_sub =>
      stepCost K_sub +
        ∑ hit ∈ rotHitSupport pref R,
          (∏ j : Fin m, rotSlotHitProb subDim K_sub (R.filter fun x ↦ pref x = j) (hit j)) *
            Ψ (R \ rotHitFinset hit)
theorem rotSlotHitProb_nonneg {α : Type*} [DecidableEq α] (subDim K_sub : ℕ) (B : Finset α) (o :
  Option α) : 0 ≤ rotSlotHitProb subDim K_sub B o := by
  cases o with
  | none => exact sub_nonneg.mpr (sin_sq_le_one _)
  | some x =>
    dsimp only [rotSlotHitProb]; split_ifs
    · exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · exact le_rfl
/-- Naturality of `rotSubsetStep` under any injective target-item embedding `emb: α → β`. -/
theorem rotSubsetStep_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {m : ℕ} (subDim :
  ℕ) {emb : α → β} (hemb : Function.Injective emb) (pref : β → Fin m) (stepCost : ℕ → ℝ) (K_opt : ℕ
  → Option ℕ) (Ψ : Finset β → ℝ) (I : Finset α) : rotSubsetStep subDim pref stepCost K_opt Ψ
  (I.image emb) = rotSubsetStep subDim (fun i ↦ pref (emb i)) stepCost K_opt (fun I' ↦ Ψ (I'.image
  emb)) I := by
  have hcard : (I.image emb).card = I.card := Finset.card_image_of_injective I hemb
  unfold rotSubsetStep; rw [hcard]
  cases K_opt I.card with
  | none => rfl
  | some K_sub =>
    dsimp only; congr 1
    have hB_eq (j : Fin m) : ((I.image emb).filter fun y ↦ pref y = j) = (I.filter fun i ↦ pref (emb
      i) = j).image emb := by
      ext y; simp only [Finset.mem_filter, Finset.mem_image]; constructor
      · rintro ⟨⟨i, hi, rfl⟩, hj⟩; exact ⟨i, ⟨hi, hj⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hj⟩, rfl⟩; exact ⟨⟨i, hi, rfl⟩, hj⟩
    symm; refine Finset.sum_bij (fun hit _ j ↦ (hit j).map emb) (fun hit hhit ↦ ?_) (fun h₁ _ h₂ _
      heq ↦ ?_) (fun hit' hhit' ↦ ?_) (fun hit hhit ↦ ?_)
    · rw [rotHitSupport, Fintype.mem_piFinset] at hhit ⊢; intro j; rw [hB_eq j]
      rcases Finset.mem_insert.mp (hhit j) with hnone | hsome
      · rw [hnone]; exact Finset.mem_insert_self _ _
      · rcases Finset.mem_image.mp hsome with ⟨i, hi, eq_o⟩; rw [← eq_o]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨emb i, Finset.mem_image.mpr ⟨i, hi,
          rfl⟩, rfl⟩)
    · funext j; exact Option.map_injective hemb (congrFun heq j)
    · rw [rotHitSupport, Fintype.mem_piFinset] at hhit'
      have hex (j : Fin m) : ∃ o ∈ insert none ((I.filter fun i ↦ pref (emb i) = j).image some),
        o.map emb = hit' j := by
        have hj := hhit' j; rw [hB_eq j] at hj; rcases Finset.mem_insert.mp hj with hnone | hsome
        · exact ⟨none, Finset.mem_insert_self _ _, hnone.symm⟩
        · rcases Finset.mem_image.mp hsome with ⟨y, hy, hy_eq⟩; rcases Finset.mem_image.mp hy with
            ⟨i, hi, rfl⟩; exact ⟨some i, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi),
            hy_eq⟩
      refine ⟨fun j ↦ Classical.choose (hex j), ?_, funext fun j ↦ (Classical.choose_spec (hex
        j)).2⟩; rw [rotHitSupport, Fintype.mem_piFinset]; exact fun j ↦ (Classical.choose_spec (hex
        j)).1
    · have hprob (j : Fin m) : rotSlotHitProb subDim K_sub (I.filter fun i ↦ pref (emb i) = j) (hit
        j) = rotSlotHitProb subDim K_sub ((I.image emb).filter fun y ↦ pref y = j) ((hit j).map emb)
        := by
        rw [hB_eq j]; have hcj : ((I.filter fun i ↦ pref (emb i) = j).image emb).card = (I.filter
          fun i ↦ pref (emb i) = j).card := Finset.card_image_of_injective _ hemb
        cases ho : hit j with
        | none => simp [rotSlotHitProb, hcj]
        | some i =>
          have hmem_iff :
              emb i ∈ (I.filter fun i' ↦ pref (emb i') = j).image emb ↔
                i ∈ I.filter fun i' ↦ pref (emb i') = j :=
            ⟨fun h ↦ by
              rcases Finset.mem_image.mp h with ⟨i', hi', heq⟩; rwa [← hemb heq],
             fun h ↦ Finset.mem_image_of_mem _ h⟩
          simp [rotSlotHitProb, hcj, hmem_iff]
      have hsdiff : (I \ rotHitFinset hit).image emb = I.image emb \ rotHitFinset (fun j ↦ (hit
        j).map emb) := by
        ext y; simp only [Finset.mem_image, Finset.mem_sdiff, rotHitFinset, Finset.mem_biUnion,
          Finset.mem_univ, true_and]; constructor
        · rintro ⟨i, ⟨hi, hnhit⟩, rfl⟩; refine ⟨⟨i, hi, rfl⟩, ?_⟩; rintro ⟨j, hj⟩; apply hnhit
          refine ⟨j, ?_⟩
          cases ho : hit j with
          | none => simp [ho] at hj
          | some i' => simp only [ho, Option.map_some, Finset.mem_singleton] at hj ⊢; exact hemb hj
        · rintro ⟨⟨i, hi, rfl⟩, hnhit⟩; refine ⟨i, ⟨hi, ?_⟩, rfl⟩; rintro ⟨j, hj⟩; apply hnhit
          refine ⟨j, ?_⟩
          cases ho : hit j with
          | none => simp [ho] at hj
          | some i' => simp only [ho, Finset.mem_singleton] at hj; subst hj; simp
      rw [Finset.prod_congr rfl fun j _ ↦ hprob j, hsdiff]
/-- Whenever `Ψ R'` depends only on `R'.card`, `rotSubsetStep` collapses identically to
  `subcubeStepExp`. -/
theorem rotSubsetStep_of_card_eq {α : Type*} [DecidableEq α] {m : ℕ} (subDim : ℕ)
    (pref : α → Fin m) (stepCost : ℕ → ℝ) (K_opt : ℕ → Option ℕ)
    {Ψ : Finset α → ℝ} (g : ℕ → ℝ) (R : Finset α)
    (hΨ : ∀ R', R' ⊆ R → Ψ R' = g R'.card) :
    rotSubsetStep subDim pref stepCost K_opt Ψ R =
      match K_opt R.card with
      | none => g R.card
      | some K_sub =>
          stepCost K_sub +
            subcubeStepExp subDim K_sub (fun c' ↦ g (∑ j : Fin m, c' j))
              (fun j ↦ (R.filter fun x ↦ pref x = j).card) := by
  unfold rotSubsetStep
  cases K_opt R.card with
  | none => exact hΨ R Finset.Subset.rfl
  | some K_sub =>
    dsimp only; congr 1; let B (j : Fin m) : Finset α := R.filter fun x ↦ pref x = j
    let c₀ (j : Fin m) : ℕ := (B j).card
    have hhit_card (hit : Fin m → Option α) (hhit : hit ∈ rotHitSupport pref R) : Ψ (R \
      rotHitFinset hit) = g (∑ j : Fin m, if (hit j).isSome then c₀ j - 1 else c₀ j) := by
      rw [hΨ (R \ rotHitFinset hit) Finset.sdiff_subset]; congr 1
      have hpart : (R \ rotHitFinset hit).card = ∑ j : Fin m, ((R \ rotHitFinset hit).filter fun x ↦
        pref x = j).card := by
        have hcf (j : Fin m) : ((R \ rotHitFinset hit).filter fun x ↦ pref x = j).card = ∑ x ∈ R \
          rotHitFinset hit, if pref x = j then (1 : ℕ) else 0 := Finset.card_filter _ _
        simp_rw [hcf]; rw [Finset.sum_comm]; simp
      rw [hpart]; refine Finset.sum_congr rfl fun j _ ↦ ?_; have hj_mem := (Fintype.mem_piFinset.mp
        hhit) j
      cases ho : hit j with
      | none =>
        have hfilt : ((R \ rotHitFinset hit).filter fun x ↦ pref x = j) = B j := by
          ext x; simp only [Finset.mem_filter, Finset.mem_sdiff, B]; refine ⟨fun ⟨⟨hxR, _⟩, hxj⟩ ↦
            ⟨hxR, hxj⟩, fun ⟨hxR, hxj⟩ ↦ ⟨⟨hxR, ?_⟩, hxj⟩⟩; intro hxh; simp only [rotHitFinset,
            Finset.mem_biUnion, Finset.mem_univ, true_and] at hxh; rcases hxh with ⟨j', hj'⟩
          cases ho' : hit j' with
          | none => simp [ho'] at hj'
          | some x' =>
            simp only [ho', Finset.mem_singleton] at hj'; subst hj'; have hj'_mem :=
              (Fintype.mem_piFinset.mp hhit) j'; simp only [ho', Finset.mem_insert,
              Option.some.injEq, reduceCtorEq, false_or, Finset.mem_image] at hj'_mem
            rcases hj'_mem with ⟨z, hz, hzx⟩; cases hzx; have hxj' : pref x = j' :=
              (Finset.mem_filter.mp hz).2; have hjj : j' = j := hxj'.symm.trans hxj; subst hjj
            simp [ho] at ho'
        rw [hfilt]; simp [c₀]
      | some y =>
        simp only [ho, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_image,
          Option.some.injEq] at hj_mem; rcases hj_mem with ⟨z, hz, rfl⟩
        have hfilt : ((R \ rotHitFinset hit).filter fun x ↦ pref x = j) = (B j).erase z := by
          ext x; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase, B]; constructor
          · rintro ⟨⟨hxR, hnh⟩, hxj⟩; refine ⟨?_, hxR, hxj⟩; rintro rfl
            apply hnh; simp only [rotHitFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
            exact ⟨j, by simp [ho]⟩
          · rintro ⟨hne, hxR, hxj⟩; refine ⟨⟨hxR, ?_⟩, hxj⟩; intro hxh; simp only [rotHitFinset,
              Finset.mem_biUnion, Finset.mem_univ, true_and] at hxh; rcases hxh with ⟨j', hj'⟩
            cases ho' : hit j' with
            | none => simp [ho'] at hj'
            | some x' =>
              simp only [ho', Finset.mem_singleton] at hj'; have hj'_mem := (Fintype.mem_piFinset.mp
                hhit) j'; simp only [ho', Finset.mem_insert, reduceCtorEq, false_or,
                Finset.mem_image, Option.some.injEq] at hj'_mem; rcases hj'_mem with ⟨w, hw, rfl⟩
              have hxj' : pref x = j' := (by rw [hj']; exact (Finset.mem_filter.mp hw).2)
              have hjj : j' = j := hxj'.symm.trans hxj; subst hjj
              rw [ho] at ho'; exact hne (hj'.trans (Option.some.inj ho').symm)
        rw [hfilt, Finset.card_erase_of_mem hz]; dsimp only [c₀, B]; simp
    rw [Finset.sum_congr rfl fun hit hhit ↦ by rw [hhit_card hit hhit]]; unfold subcubeStepExp; symm
    have hslot (j : Fin m) (bj : Bool) :
        (match bj with
          | true => p_succ_frac K_sub (c₀ j) subDim
          | false => 1 - p_succ_frac K_sub (c₀ j) subDim) =
          ∑ o ∈ insert none ((B j).image some),
            if o.isSome = bj then rotSlotHitProb subDim K_sub (B j) o else 0 := by
      have hnot : (none : Option α) ∉ (B j).image some := (by simp); rw [Finset.sum_insert hnot,
        Finset.sum_image (fun _ _ _ _ h ↦ Option.some.inj h)]
      cases bj with
      | false => simp [rotSlotHitProb, c₀]
      | true =>
        have hmem (x : α) (hx : x ∈ B j) : (if (some x).isSome = true then rotSlotHitProb subDim
          K_sub (B j) (some x) else 0) = p_succ_frac K_sub (c₀ j) subDim / (c₀ j : ℝ) :=
          (by simp [rotSlotHitProb, hx, c₀]); rw [Finset.sum_congr rfl hmem, Finset.sum_const,
          nsmul_eq_mul]; rcases (B j).eq_empty_or_nonempty with hemp | hne
        · have hc0 : c₀ j = 0 := (by simp [c₀, hemp]); simp [hemp, hc0, p_succ_frac]
        · have hc_pos : (0 : ℝ) < (c₀ j : ℝ) := Nat.cast_pos.mpr hne.card_pos
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, zero_add]
          exact (mul_div_cancel₀ _ hc_pos.ne').symm
    have hrhs (b : Fin m → Bool) :
        (∏ j : Fin m,
          match b j with
          | true => p_succ_frac K_sub (c₀ j) subDim
          | false => 1 - p_succ_frac K_sub (c₀ j) subDim) *
          g (∑ j : Fin m, if b j then c₀ j - 1 else c₀ j) =
        ∑ hit ∈ rotHitSupport pref R, (∏ j : Fin m,
            if (hit j).isSome = b j then rotSlotHitProb subDim K_sub (B j) (hit j) else 0) *
            g (∑ j : Fin m, if b j then c₀ j - 1 else c₀ j) := by
      simp_rw [hslot]; rw [Finset.prod_univ_sum, Finset.sum_mul]; rfl
    change (∑ b : Fin m → Bool, (∏ j : Fin m,
          match b j with
          | true => p_succ_frac K_sub (c₀ j) subDim
          | false => 1 - p_succ_frac K_sub (c₀ j) subDim) *
          g (∑ j : Fin m, if b j then c₀ j - 1 else c₀ j)) = _
    simp_rw [hrhs]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun hit _ ↦ ?_
    rw [Fintype.sum_eq_single (fun j ↦ (hit j).isSome) (fun b hb ↦ ?_)]
    · simp only [ite_true]; rfl
    · obtain ⟨j, hj⟩ : ∃ j : Fin m, (hit j).isSome ≠ b j := by
        by_contra! hall; exact hb (funext fun j ↦ (hall j).symm)
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj), zero_mul]
/-- Collision-free placement probability `(m)_r / m ^ r` for `r` i.i.d. uniform targets
  across
  `m` subcubes. -/
noncomputable def rotCfProb (m r : ℕ) : ℝ :=
  (m.descFactorial r : ℝ) / (m : ℝ) ^ r
/-- Exact single-pair-collision placement probability `C(r, 2) * (m)_{r - 1} / m ^ r` (`2 ≤
  r`,
  `0` for `r < 2`). -/
noncomputable def rotPairProb (m r : ℕ) : ℝ :=
  if 2 ≤ r then (r.choose 2 : ℝ) * (m.descFactorial (r - 1) : ℝ) / (m : ℝ) ^ r else 0
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllRotatedSubcubeAnalysis
section WD_FindAllWeakDicke
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
/- ## Section 1: Rational Pythagorean Parameters & Top-Wire Clean Ancilla Split -/
/-- Exact integer Pythagorean triple `(cNum, sNum, cDen)` parametrizing a 1-qubit real
  orthogonal
  rotation `c = cNum / cDen`, `s = sNum / cDen` with `c ^ 2 + s ^ 2 = 1`. -/
structure PythPair where
  cNum : ℤ
  sNum : ℕ
  cDen : ℕ
  hDen : 0 < cDen
  hPyth : cNum ^ 2 + (sNum : ℤ) ^ 2 = (cDen : ℤ) ^ 2
  deriving DecidableEq, Repr
/-- Rational cosine `cNum / cDen` as a real scalar. -/
noncomputable def PythPair.cVal (p : PythPair) : ℝ :=
  (p.cNum : ℝ) / (p.cDen : ℝ)
/-- Nonnegative rational sine `sNum / cDen` as a real scalar. -/
noncomputable def PythPair.sVal (p : PythPair) : ℝ :=
  (p.sNum : ℝ) / (p.cDen : ℝ)
theorem PythPair.cVal_sq_add_sVal_sq (p : PythPair) : p.cVal ^ 2 + p.sVal ^ 2 = 1 := by
  unfold PythPair.cVal PythPair.sVal; have hd : (p.cDen : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.hDen.ne'
  have hp : (p.cNum : ℝ) ^ 2 + (p.sNum : ℝ) ^ 2 = (p.cDen : ℝ) ^ 2 := (by exact_mod_cast p.hPyth)
  rw [div_pow, div_pow, ← add_div, hp, div_self (pow_ne_zero 2 hd)]
/-- Number of distinct marked addresses extracted by `groupHits (Nat.mul_one m)` across the
  `m`
  singleton work slots of `w: Fin (2 ^ (m * (n + 1)))`. -/
def wdHitCount (n m : ℕ) (w : Fin (2 ^ (m * (n + 1)))) : ℕ :=
  (groupHits (Nat.mul_one m) w).length
/-- Top wire `W + M - 1` of the `(W + M)`-qubit workspace (`1 ≤ M`), residing in the highest
  bit
  of the last `memReg` slot `k - 1`. -/
abbrev topAncReg (W M : ℕ) (hM : 1 ≤ M) : QRegister 1 (W + M) :=
  QRegister.block (W + M - 1) 1 (by omega)
/-- Basis index split separating the low `W + M - 1` qubits from the single top ancilla
  qubit. -/
abbrev topAncEquiv (W M : ℕ) (hM : 1 ≤ M) :
    Fin (2 ^ (W + M)) ≃ Fin (2 ^ (W + M - 1)) × Fin (2 ^ 1) :=
  (finCongr (by congr 1; omega)).trans (lowHighEquiv (W + M - 1) 1)
theorem topAncEquiv_fst_val (W M : ℕ) (hM : 1 ≤ M) (z : Fin (2 ^ (W + M))) : ((topAncEquiv W M hM
  z).1).val = z.val % 2 ^ (W + M - 1) := by simp [topAncEquiv]
theorem topAncEquiv_snd_val (W M : ℕ) (hM : 1 ≤ M) (z : Fin (2 ^ (W + M))) : ((topAncEquiv W M hM
  z).2).val = z.val / 2 ^ (W + M - 1) := by simp [topAncEquiv]
theorem topAncEquiv_symm_val (W M : ℕ) (hM : 1 ≤ M) (b : Fin (2 ^ (W + M - 1))) (q : Fin (2 ^ 1)) :
  ((topAncEquiv W M hM).symm (b, q)).val = b.val + 2 ^ (W + M - 1) * q.val := by
  have h1 := topAncEquiv_fst_val W M hM ((topAncEquiv W M hM).symm (b, q)); have h2 :=
    topAncEquiv_snd_val W M hM ((topAncEquiv W M hM).symm (b, q))
  simp only [Equiv.apply_symm_apply] at h1 h2; rw [h1, h2]; exact (Nat.mod_add_div _ _).symm
theorem lowHighEquiv_symm_val (W M : ℕ) (w : Fin (2 ^ W)) (μ : Fin (2 ^ M)) : ((lowHighEquiv W
  M).symm (w, μ)).val = w.val + 2 ^ W * μ.val := by
  have h1 := lowHighEquiv_fst_val W M ((lowHighEquiv W M).symm (w, μ)); have h2 :=
    lowHighEquiv_snd_val W M ((lowHighEquiv W M).symm (w, μ))
  simp only [Equiv.apply_symm_apply] at h1 h2; rw [h1, h2]; exact (Nat.mod_add_div _ _).symm
theorem extractIndex_topAncReg (W M : ℕ) (hM : 1 ≤ M) (z : Fin (2 ^ (W + M))) : (topAncReg W M
  hM).extractIndex z = (topAncEquiv W M hM z).2 := by
  apply (basisBits 1).injective; funext q; rw [basisBits_extractIndex, basisBits_eq_testBit,
    basisBits_eq_testBit, topAncEquiv_snd_val]; have hq : (topAncReg W M hM q).val = q.val + (W + M
    - 1) := (by simp only [topAncReg, QRegister.block_apply_val]; omega); rw [hq,
    Nat.testBit_div_two_pow]
theorem lowHigh_fst_topAncEquiv_symm (W M : ℕ) (hM : 1 ≤ M) (b : Fin (2 ^ (W + M - 1))) (q : Fin (2
  ^ 1)) : (lowHighEquiv W M ((topAncEquiv W M hM).symm (b, q))).1 = ⟨b.val % 2 ^ W, Nat.mod_lt _
  (Nat.two_pow_pos W)⟩ := by
  ext; rw [lowHighEquiv_fst_val, topAncEquiv_symm_val]
  have hpow : 2 ^ (W + M - 1) = 2 ^ W * 2 ^ (M - 1) := (by rw [← pow_add]; congr 1; omega)
  have hval (x : ℕ) : x + 2 ^ (W + M - 1) * q.val = x + 2 ^ W * (2 ^ (M - 1) * q.val) :=
    (by rw [hpow, mul_assoc]); rw [hval b.val, Nat.add_mul_mod_self_left]
/-- Under `MemPrefixValid S s μ` with `s < k` (`1 ≤ n`, `1 ≤ k`), archive slot `k - 1` is
  `0`,
  so `μ.val < 2 ^ (k * n - 1)` and the top bit of `memReg` is guaranteed to be `0`. -/
theorem memPrefixValid_lt_half {n k s : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) {S : Finset (Fin (2 ^ n))} {μ :
  Fin (2 ^ (k * n))} (hval : MemPrefixValid S s μ) (hs : s < k) : μ.val < 2 ^ (k * n - 1) := by
  have hk_zero := hval.2.2.2 ⟨k - 1, by omega⟩ (by simp; omega)
  rw [addrEquiv_eq_div_pow_mod] at hk_zero; have hmod : (μ.val / (2 ^ n) ^ (k - 1)) % 2 ^ n = 0 :=
    congrArg Fin.val hk_zero
  have hpow_eq : (2 ^ n) ^ (k - 1) * 2 ^ n = 2 ^ (k * n) := by
    rw [← pow_mul, ← pow_add]; congr 1
    cases k with
    | zero => omega
    | succ k' => simp only [Nat.add_sub_cancel]; ring
  have hdiv_lt : μ.val / (2 ^ n) ^ (k - 1) < 2 ^ n :=
    (by rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm (2 ^ n), hpow_eq]; exact μ.isLt)
  have hdiv_zero : μ.val / (2 ^ n) ^ (k - 1) = 0 := (by rwa [Nat.mod_eq_of_lt hdiv_lt] at hmod)
  have hlt1 : μ.val < (2 ^ n) ^ (k - 1) := (Nat.div_eq_zero_iff_lt (by positivity)).mp hdiv_zero
  rw [← pow_mul] at hlt1
  have hexp : n * (k - 1) ≤ k * n - 1 := by
    cases k with
    | zero => omega
    | succ k' =>
      simp only [Nat.add_sub_cancel, Nat.add_mul, one_mul]
      have : n * k' = k' * n := Nat.mul_comm n k'; omega
  exact lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by omega) hexp)
/-- Low `(W + M - 1)`-qubit index corresponding to `(w, μ)` when `μ.val < 2 ^ (M - 1)`. -/
def topAncBase {W M : ℕ} (hM : 1 ≤ M) (w : Fin (2 ^ W))
    {μ : Fin (2 ^ M)} (hμ : μ.val < 2 ^ (M - 1)) : Fin (2 ^ (W + M - 1)) :=
  ⟨w.val + 2 ^ W * μ.val, by
    have hpow : 2 ^ (W + M - 1) = 2 ^ W * 2 ^ (M - 1) := by
      rw [← pow_add]; congr 1; omega
    have hw := w.isLt
    nlinarith⟩
/-- Flipped `memReg` index setting the clean top bit `2 ^ (M - 1)` from `0` to `1`. -/
def memWithTopOne {M : ℕ} (hM : 1 ≤ M) (μ : Fin (2 ^ M)) (hμ : μ.val < 2 ^ (M - 1)) :
    Fin (2 ^ M) :=
  ⟨μ.val + 2 ^ (M - 1), by
    have hpow : 2 ^ M = 2 ^ (M - 1) + 2 ^ (M - 1) := by
      cases M with
      | zero => omega
      | succ M' => simp [pow_succ, Nat.mul_two]
    omega⟩
theorem topAncEquiv_lowHigh_zero {W M : ℕ} (hM : 1 ≤ M) (w : Fin (2 ^ W)) {μ : Fin (2 ^ M)} (hμ :
  μ.val < 2 ^ (M - 1)) : topAncEquiv W M hM ((lowHighEquiv W M).symm (w, μ)) = (topAncBase hM w hμ,
  0) := by
  have hlt : w.val + 2 ^ W * μ.val < 2 ^ (W + M - 1) := (topAncBase hM w hμ).isLt; apply Prod.ext
  · ext; rw [topAncEquiv_fst_val, lowHighEquiv_symm_val]; exact Nat.mod_eq_of_lt hlt
  · ext
    rw [topAncEquiv_snd_val, lowHighEquiv_symm_val]; exact (Nat.div_eq_zero_iff_lt
      (by positivity)).mpr hlt
theorem topAncEquiv_lowHigh_one {W M : ℕ} (hM : 1 ≤ M) (w : Fin (2 ^ W)) {μ : Fin (2 ^ M)} (hμ :
  μ.val < 2 ^ (M - 1)) : topAncEquiv W M hM ((lowHighEquiv W M).symm (w, memWithTopOne hM μ hμ)) =
  (topAncBase hM w hμ, 1) := by
  have hpow : 2 ^ (W + M - 1) = 2 ^ W * 2 ^ (M - 1) := (by rw [← pow_add]; congr 1; omega)
  have hlt : w.val + 2 ^ W * μ.val < 2 ^ (W + M - 1) := (topAncBase hM w hμ).isLt
  have hval_eq : ((lowHighEquiv W M).symm (w, memWithTopOne hM μ hμ)).val = (w.val + 2 ^ W * μ.val)
    + 2 ^ (W + M - 1) := (by rw [lowHighEquiv_symm_val]; dsimp only [memWithTopOne]; linarith)
  apply Prod.ext
  · ext; rw [topAncEquiv_fst_val, hval_eq, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hlt
  · ext
    rw [topAncEquiv_snd_val, hval_eq, Nat.add_div_right _ (Nat.two_pow_pos (W + M - 1)),
      (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mpr hlt, zero_add]; rfl
/- ## Section 2: Controlled Weak All-Hit Gate & Top-Wire Projectors -/
/-- Extract the low `W`-qubit `workReg` index from a `(W + M - 1)`-qubit base index. -/
def topAncBaseWork {W M : ℕ} (b : Fin (2 ^ (W + M - 1))) : Fin (2 ^ W) :=
  ⟨b.val % 2 ^ W, Nat.mod_lt _ (Nat.two_pow_pos W)⟩
/-- Generic `(W + M)`-qubit weak rotation matrix controlled by `cond: Fin (2 ^ W) → Bool` on
  the
  low `W` qubits and acting by `(p.cVal, p.sVal)` on the top ancilla bit `W + M - 1`. -/
noncomputable def weakAllHitGenMat (W M : ℕ) (hM : 1 ≤ M) (cond : Fin (2 ^ W) → Bool)
    (p : PythPair) : Matrix (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ :=
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
private lemma fin2_cases (q : Fin (2 ^ 1)) : q = 0 ∨ q = 1 := by
  rcases q with ⟨v, hv⟩; interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl
/-- Unitary wrapper around `weakAllHitGenMat`. -/
noncomputable def weakAllHitGenUnitary (W M : ℕ) (hM : 1 ≤ M) (cond : Fin (2 ^ W) → Bool)
    (p : PythPair) : Unitary (2 ^ (W + M)) :=
  ⟨weakAllHitGenMat W M hM cond p, by
    let U := weakAllHitGenMat W M hM cond p
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
        dsimp only [g, U, weakAllHitGenMat]
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
      dsimp only [g, U, weakAllHitGenMat, Matrix.conjTranspose_apply]
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
        rcases fin2_cases bq₁.2 with h1 | h1 <;> rcases fin2_cases bq₂.2 with h2 | h2 <;>
          rw [h1, h2] <;> simp
      · simp only [↓reduceIte]
        rcases fin2_cases bq₁.2 with h1 | h1 <;> rcases fin2_cases bq₂.2 with h2 | h2 <;>
          rw [h1, h2] <;> simp only [Fin.val_zero, Fin.val_one, star_neg, RCLike.star_def,
            Complex.conj_ofReal]
        · simp; linear_combination hpyth_c
        · simp; ring
        · simp; ring
        · simp; linear_combination hpyth_c
    · have hne_z : z₁ ≠ z₂ := fun h ↦ hb (by subst h; rfl)
      rw [ite_eq_right hne_z]
      refine Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun q _ ↦ ?_
      dsimp only [g, U, weakAllHitGenMat, Matrix.conjTranspose_apply]
      simp only [Matrix.of_apply]
      have hsymm : topAncEquiv W M hM ((topAncEquiv W M hM).symm (b, q)) = (b, q) :=
        Equiv.apply_symm_apply _ _
      rw [hsymm]
      change (if bq₁.1 = b then _ else 0) * star (if bq₂.1 = b then _ else 0) = 0
      by_cases hb1 : bq₁.1 = b
      · have hb2 : bq₂.1 ≠ b := fun h2 ↦ hb (hb1.trans h2.symm)
        rw [ite_eq_right hb2, star_zero, mul_zero]
      · rw [ite_eq_right hb1, zero_mul]⟩
/-- Matrix of the `0`-query weak all-hit gate on `(m * (n + 1) + M)` qubits (`1 ≤ M`),
  applying
  the `2 × 2` real orthogonal rotation `(p.cVal, p.sVal)` to the top ancilla bit iff
  `wdHitCount n m w = r`. -/
noncomputable abbrev weakAllHitMat (n m M : ℕ) (hM : 1 ≤ M) (r : ℕ) (p : PythPair) :
    Matrix (Fin (2 ^ (m * (n + 1) + M))) (Fin (2 ^ (m * (n + 1) + M))) ℂ :=
  weakAllHitGenMat (m * (n + 1)) M hM (fun w ↦ decide (wdHitCount n m w = r)) p
/-- Unitary wrapper around `weakAllHitMat`. -/
noncomputable abbrev weakAllHitUnitary (n m M : ℕ) (hM : 1 ≤ M) (r : ℕ) (p : PythPair) :
    Unitary (2 ^ (m * (n + 1) + M)) :=
  weakAllHitGenUnitary (m * (n + 1)) M hM (fun w ↦ decide (wdHitCount n m w = r)) p
/-- Damped no-click `workReg` vector: multiplies `wdHitCount = r` amplitudes by `c` and
  leaves
  all `wdHitCount ≠ r` amplitudes untouched. -/
noncomputable def wdDampVec (n m r : ℕ) (c : ℝ) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ)
    (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  if wdHitCount n m w = r then (c : ℂ) * ψ w else ψ w
/-- Click `workReg` vector: extracts `wdHitCount = r` amplitudes scaled by `s` and zeroes
  all `wdHitCount ≠ r` amplitudes. -/
noncomputable def wdClickVec (n m r : ℕ) (s : ℝ) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ)
    (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  if wdHitCount n m w = r then (s : ℂ) * ψ w else 0
theorem weakAllHitGenMat_mulVec_workMemState {W M : ℕ} (hM : 1 ≤ M) (cond : Fin (2 ^ W) → Bool) (p :
  PythPair) (ψ : Fin (2 ^ W) → ℂ) {μ : Fin (2 ^ M)} (hμ : μ.val < 2 ^ (M - 1)) : weakAllHitGenMat W
  M hM cond p *ᵥ workMemState ψ (single μ 1) = workMemState (fun w ↦ if cond w then (p.cVal : ℂ) * ψ
  w else ψ w) (single μ 1) + workMemState (fun w ↦ if cond w then (p.sVal : ℂ) * ψ w else 0) (single
  (memWithTopOne hM μ hμ) 1) := by
  funext z; rw [Matrix.mulVec, dotProduct]; dsimp only [Pi.add_apply, workMemState]
  let eμ : Fin (2 ^ M) → ℂ := Pi.single μ 1
  let f (y : Fin (2 ^ (W + M))) : ℂ :=
    weakAllHitGenMat W M hM cond p z y * (ψ (lowHighEquiv W M y).1 * eμ (lowHighEquiv W M y).2)
  change ∑ y, f y = _; rw [← (lowHighEquiv W M).symm.sum_comp f, sum_prod_type]
  have hsum_μ (w : Fin (2 ^ W)) : (∑ ν : Fin (2 ^ M), f ((lowHighEquiv W M).symm (w, ν))) =
    weakAllHitGenMat W M hM cond p z ((lowHighEquiv W M).symm (w, μ)) * ψ w := by
    rw [sum_eq_single μ (fun ν hν ↦ by
      dsimp only [f, eμ]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hν, mul_zero, mul_zero])]
    dsimp only [f, eμ]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  simp_rw [hsum_μ]; set w_z := (lowHighEquiv W M z).1; set ν_z := (lowHighEquiv W M z).2
  have hz_symm : (lowHighEquiv W M).symm (w_z, ν_z) = z := Equiv.symm_apply_apply _ z
  rw [sum_eq_single w_z (fun w hw ↦ by
    dsimp only [weakAllHitGenMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w hμ]
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
    dsimp only [weakAllHitGenMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w_z hμ]
    simp only [ite_true, Fin.val_zero]; rw [hmod_wz]; cases cond w_z <;> simp
  · by_cases hν1 : ν_z = memWithTopOne hM μ hμ
    · rw [Pi.single_eq_of_ne hν0, mul_zero, zero_add, hν1, Pi.single_eq_same, mul_one, ← hz_symm,
        hν1]; dsimp only [weakAllHitGenMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_one hM w_z hμ,
        topAncEquiv_lowHigh_zero hM w_z hμ]
      simp only [ite_true, Fin.val_one, Fin.val_zero]; rw [hmod_wz]; cases cond w_z
      · have h10 : (1 : Fin (2 ^ 1)) ≠ 0 := fun h ↦ by have v := congrArg Fin.val h; simp at v
        simp [h10]
      · simp
    · rw [Pi.single_eq_of_ne hν0, Pi.single_eq_of_ne hν1, mul_zero, mul_zero, add_zero]
      dsimp only [weakAllHitGenMat]; rw [Matrix.of_apply, topAncEquiv_lowHigh_zero hM w_z hμ]
      by_cases hb : (topAncEquiv W M hM z).1 = topAncBase hM w_z hμ
      · exfalso; rcases fin2_cases (topAncEquiv W M hM z).2 with hq0 | hq1
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
theorem weakAllHitMat_mulVec_workMemState {n m M : ℕ} (hM : 1 ≤ M) (r : ℕ) (p : PythPair) (ψ : Fin
  (2 ^ (m * (n + 1))) → ℂ) {μ : Fin (2 ^ M)} (hμ : μ.val < 2 ^ (M - 1)) : weakAllHitMat n m M hM r p
  *ᵥ workMemState ψ (single μ 1) = workMemState (wdDampVec n m r p.cVal ψ) (single μ 1) +
  workMemState (wdClickVec n m r p.sVal ψ) (single (memWithTopOne hM μ hμ) 1) := by
  rw [weakAllHitMat, weakAllHitGenMat_mulVec_workMemState hM _ p ψ hμ]
  refine congrArg₂ (· + ·) (congrArg (fun v ↦ workMemState v (single μ 1)) ?_)
    (congrArg (fun v ↦ workMemState v (single (memWithTopOne hM μ hμ) 1)) ?_)
  · funext w; simp [wdDampVec]
  · funext w; simp [wdClickVec]
theorem topAncReg_projector_zero_mulVec {W M : ℕ} (hM : 1 ≤ M) (α β : Fin (2 ^ W) → ℂ) {μ : Fin (2 ^
  M)} (hμ : μ.val < 2 ^ (M - 1)) : (topAncReg W M hM).basisOutcomeProjector 0 *ᵥ (workMemState α
  (single μ 1) + workMemState β (single (memWithTopOne hM μ hμ) 1)) = workMemState α (single μ 1) :=
  by
  funext z; rw [QRegister.basisOutcomeProjector_eq_diagonal, mulVec_diagonal,
    extractIndex_topAncReg]; dsimp only [Pi.add_apply, workMemState]; set w_z := (lowHighEquiv W M
    z).1; set ν_z := (lowHighEquiv W M z).2; have hz : z = (lowHighEquiv W M).symm (w_z, ν_z) :=
    (Equiv.symm_apply_apply _ z).symm; by_cases h0 : ν_z = μ
  · have h1 : ν_z ≠ memWithTopOne hM μ hμ := by
      rw [h0]; intro h; have hv := congrArg Fin.val h; dsimp only [memWithTopOne] at hv; have :=
        Nat.two_pow_pos (M - 1); omega
    rw [Pi.single_eq_of_ne h1, mul_zero, add_zero, hz, h0, topAncEquiv_lowHigh_zero hM w_z hμ]; simp
  · rw [Pi.single_eq_of_ne h0, mul_zero, zero_add]; by_cases h1 : ν_z = memWithTopOne hM μ hμ
    · rw [hz, h1, topAncEquiv_lowHigh_one hM w_z hμ]; simp
    · rw [Pi.single_eq_of_ne h1, mul_zero, mul_zero]
theorem topAncReg_projector_one_mulVec {W M : ℕ} (hM : 1 ≤ M) (α β : Fin (2 ^ W) → ℂ) {μ : Fin (2 ^
  M)} (hμ : μ.val < 2 ^ (M - 1)) : (topAncReg W M hM).basisOutcomeProjector 1 *ᵥ (workMemState α
  (single μ 1) + workMemState β (single (memWithTopOne hM μ hμ) 1)) = workMemState β (single
  (memWithTopOne hM μ hμ) 1) := by
  have h0 := topAncReg_projector_zero_mulVec hM α β hμ; have hsum : (topAncReg W M
    hM).basisOutcomeProjector 0 + (topAncReg W M hM).basisOutcomeProjector 1 = 1 :=
    (by simpa [Fin.sum_univ_two] using (topAncReg W M hM).sum_basisOutcomeProjector)
  refine add_left_cancel (a := workMemState α (single μ 1)) ?_; nth_rw 1 [← h0]
  rw [← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
theorem topAncReg_flip_mulVec_one {W M : ℕ} (hM : 1 ≤ M) (β : Fin (2 ^ W) → ℂ) {μ : Fin (2 ^ M)} (hμ
  : μ.val < 2 ^ (M - 1)) : ((topAncReg W M hM).embedUnitary (permutationUnitary (swap 0 1))).1 *ᵥ
  workMemState β (single (memWithTopOne hM μ hμ) 1) = workMemState β (single μ 1) := by
  have hag_iff (i j : Fin (2 ^ (W + M))) : (topAncReg W M hM).AgreeOutside i j ↔ (topAncEquiv W M hM
    i).1 = (topAncEquiv W M hM j).1 := by
    constructor
    · intro h; apply (basisBits (W + M - 1)).injective; funext q; rw [basisBits_eq_testBit,
        basisBits_eq_testBit, topAncEquiv_fst_val, topAncEquiv_fst_val, Nat.testBit_mod_two_pow,
        Nat.testBit_mod_two_pow]; simp only [q.isLt, decide_true, Bool.true_and]
      have hbi := h ⟨q.val, by omega⟩ (by
        rintro ⟨p, hp⟩; have hp' := congrArg Fin.val hp; simp only [topAncReg,
          QRegister.block_apply_val] at hp'
        omega)
      rwa [basisBits_eq_testBit, basisBits_eq_testBit] at hbi
    · intro h p hp
      have hplt : p.val < W + M - 1 := by
        by_contra hge
        exact hp ⟨⟨0, by omega⟩, Fin.ext (by
          simp only [topAncReg, QRegister.block_apply_val]; omega)⟩
      rw [basisBits_eq_testBit, basisBits_eq_testBit]; have ht1 : i.val.testBit p.val = (i.val % 2 ^
        (W + M - 1)).testBit p.val := (by rw [Nat.testBit_mod_two_pow]; simp [hplt])
      have ht2 : j.val.testBit p.val = (j.val % 2 ^ (W + M - 1)).testBit p.val :=
        (by rw [Nat.testBit_mod_two_pow]; simp [hplt]); rw [ht1, ht2, ← topAncEquiv_fst_val W M hM
        i, ← topAncEquiv_fst_val W M hM j, h]
  let E : Matrix (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ := (topAncReg W M hM).embedMatrix
    (permutationUnitary (swap 0 1)).1; funext z
  rw [embedUnitary_val]; change (E *ᵥ workMemState β (single (memWithTopOne hM μ hμ) 1)) z = _
  rw [Matrix.mulVec, dotProduct]; dsimp only [workMemState]
  let eμ₁ : Fin (2 ^ M) → ℂ := Pi.single (memWithTopOne hM μ hμ) 1
  let g (y : Fin (2 ^ (W + M))) : ℂ := E z y * (β (lowHighEquiv W M y).1 * eμ₁ (lowHighEquiv W M
    y).2); change ∑ y, g y = _; rw [← (lowHighEquiv W M).symm.sum_comp g, sum_prod_type]
  have hsum_ν (w : Fin (2 ^ W)) : (∑ ν : Fin (2 ^ M), g ((lowHighEquiv W M).symm (w, ν))) = E z
    ((lowHighEquiv W M).symm (w, memWithTopOne hM μ hμ)) * β w := by
    rw [sum_eq_single (memWithTopOne hM μ hμ) (fun ν hν ↦ by
      dsimp only [g, eμ₁]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hν, mul_zero, mul_zero])]
    dsimp only [g, eμ₁]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  simp_rw [hsum_ν]; set w_z := (lowHighEquiv W M z).1; set ν_z := (lowHighEquiv W M z).2
  have hz_symm : (lowHighEquiv W M).symm (w_z, ν_z) = z := Equiv.symm_apply_apply _ z
  rw [sum_eq_single w_z (fun w hw ↦ by
    dsimp only [E]; rw [QRegister.embedMatrix_apply_of_agreeOutside, hag_iff,
      topAncEquiv_lowHigh_one hM w hμ]
    have hne_b : (topAncEquiv W M hM z).1 ≠ topAncBase hM w hμ := by
      intro heq; apply hw
      have h1 := lowHigh_fst_topAncEquiv_symm W M hM (topAncEquiv W M hM z).1 (topAncEquiv W M hM
        z).2; rw [Equiv.symm_apply_apply] at h1; have hval := congrArg Fin.val h1; rw [heq] at hval;
        dsimp only [topAncBase] at hval
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt w.isLt] at hval; exact Fin.ext hval.symm
    dsimp only
    rw [ite_eq_right hne_b, mul_zero, zero_mul])]
  dsimp only [E]; by_cases hν0 : ν_z = μ
  · rw [hν0, Pi.single_eq_same, mul_one, ← hz_symm, hν0,
      QRegister.embedMatrix_apply_of_agreeOutside, hag_iff, extractIndex_topAncReg,
      extractIndex_topAncReg, topAncEquiv_lowHigh_zero hM w_z hμ, topAncEquiv_lowHigh_one hM w_z hμ]
    simp [permutationUnitary_apply]
  · rw [Pi.single_eq_of_ne hν0, mul_zero, QRegister.embedMatrix_apply_of_agreeOutside, hag_iff,
      extractIndex_topAncReg, extractIndex_topAncReg, topAncEquiv_lowHigh_one hM w_z hμ]
    by_cases hb : (topAncEquiv W M hM z).1 = topAncBase hM w_z hμ
    · rcases fin2_cases (topAncEquiv W M hM z).2 with hq0 | hq1
      · exfalso; have heq : topAncEquiv W M hM z = topAncEquiv W M hM ((lowHighEquiv W M).symm (w_z,
          μ)) := (by rw [topAncEquiv_lowHigh_zero hM w_z hμ]; exact Prod.ext hb hq0); have hp_eq :=
          congrArg (lowHighEquiv W M) ((topAncEquiv W M hM).injective heq)
        rw [Equiv.apply_symm_apply] at hp_eq; exact hν0 (congrArg Prod.snd hp_eq)
      · dsimp only; have hs0 : (permutationUnitary (swap (0 : Fin (2 ^ 1)) 1)).1 1 1 = 0 :=
          (by simp [permutationUnitary_apply]); rw [hq1, hs0, zero_mul, zero_mul]
    · dsimp only; rw [ite_eq_right hb, mul_zero, zero_mul]
/- ## Section 3: Zero-Sqrt Unnormalized Polynomial Dicke Step -/
/-- Exact recursive polynomial transform on per-bitstring symmetric amplitudes `u: ℕ → R`
  across
  `r` independent `2 × 2` rotations `[[c, -s], [s, c]]` (`0` square roots, `0` divisions). -/
noncomputable def dickeStep {R : Type*} [CommRing R] : ℕ → R → R → (ℕ → R) → ℕ → R
  | 0, _, _, u, w' => if w' = 0 then u 0 else 0
  | r + 1, c, s, u, w' =>
      if w' ≤ r then
        c * dickeStep r c s u w' - s * dickeStep r c s (fun w ↦ u (w + 1)) w'
      else if w' = r + 1 then
        s * dickeStep r c s u r + c * dickeStep r c s (fun w ↦ u (w + 1)) r
      else 0
/-- Symmetry identity matching the `b₀ = true` tensor branch (`1 ≤ w' ≤ r + 1`) to
  `dickeStep`. -/
theorem dickeStep_alt {R : Type*} [CommRing R] : ∀ (r : ℕ) (c s : R) (u : ℕ → R) {w' : ℕ}, 1 ≤ w' →
  w' ≤ r + 1 → dickeStep (r + 1) c s u w' = s * dickeStep r c s u (w' - 1) + c * dickeStep r c s
  (fun w ↦ u (w + 1)) (w' - 1)
  | 0, c, s, u, w', hw1, hwr => by have hw : w' = 1 := (by omega); subst hw; rfl
  | r + 1, c, s, u, w', hw1, hwr => by
    by_cases htop : w' = r + 2
    · subst htop; simp [dickeStep]
    · have hle : w' ≤ r + 1 := (by omega); obtain ⟨k, rfl⟩ : ∃ k, w' = k + 1 := ⟨w' - 1, by omega⟩
      have hk : k ≤ r := by omega
      have h1 := dickeStep_alt r c s u (w' := k + 1) (by omega) (by omega)
      have h2 := dickeStep_alt r c s (fun w ↦ u (w + 1)) (w' := k + 1) (by omega) (by omega)
      have hlhs : dickeStep (r + 2) c s u (k + 1) = c * dickeStep (r + 1) c s u (k + 1) - s *
        dickeStep (r + 1) c s (fun w ↦ u (w + 1)) (k + 1) := (by simp [dickeStep, hle])
      have hr1 : dickeStep (r + 1) c s u k = c * dickeStep r c s u k - s * dickeStep r c s (fun w ↦
        u (w + 1)) k := (by simp [dickeStep, hk])
      have hr2 : dickeStep (r + 1) c s (fun w ↦ u (w + 1)) k = c * dickeStep r c s (fun w ↦ u (w +
        1)) k - s * dickeStep r c s (fun w ↦ u (w + 2)) k :=
        (by simp [dickeStep, hk, Nat.add_assoc])
      simp only [Nat.add_sub_cancel] at h1 h2 ⊢; rw [hlhs, h1, h2, hr1, hr2]; have hshift : (fun w ↦
        u (w + 1 + 1)) = (fun w ↦ u (w + 2)) := rfl; rw [hshift]; ring
theorem dickeStep_eq_zero_of_gt {R : Type*} [CommRing R] (r : ℕ) (c s : R) (u : ℕ → R) {w' : ℕ} (hgt
  : r < w') : dickeStep r c s u w' = 0 := by
  cases r with
  | zero => simp [dickeStep, Nat.ne_of_gt hgt]
  | succ r' =>
    have h1 : ¬ w' ≤ r' := (by omega); have h2 : w' ≠ r' + 1 := (by omega); simp [dickeStep, h1, h2]
/-- Exact commutative-ring powerset identity expanding `r = J.card` independent `2 × 2`
  rotations
  `[[c, -s], [s, c]]` on active coordinates `j ∈ J` via `dickeStep`. -/
theorem prod_dickeStep_powerset {R : Type*} [CommRing R] {m : ℕ} (J : Finset (Fin m)) (c s : R) (x₀
  x₁ z : Fin m → R) (u : ℕ → R) : (∑ A ∈ J.powerset, u A.card * ∏ j : Fin m, if j ∈ J then if j ∈ A
  then -s * x₀ j + c * x₁ j else c * x₀ j + s * x₁ j else z j) = ∑ B ∈ J.powerset, dickeStep J.card
  c s u B.card * ∏ j : Fin m, if j ∈ J then (if j ∈ B then x₁ j else x₀ j) else z j := by
  induction J using Finset.induction generalizing z u with
  | empty => simp [dickeStep]
  | @insert j₀ J hj₀ ih =>
    have hcard_ins : (insert j₀ J).card = J.card + 1 := Finset.card_insert_of_notMem hj₀
    rw [Finset.sum_powerset_insert hj₀, Finset.sum_powerset_insert hj₀, hcard_ins]
    let z₀ : Fin m → R := fun j ↦ if j = j₀ then c * x₀ j₀ + s * x₁ j₀ else z j
    let z₁ : Fin m → R := fun j ↦ if j = j₀ then -s * x₀ j₀ + c * x₁ j₀ else z j
    let P_out (C : Finset (Fin m)) : R :=
      ∏ j : Fin m, if j ∈ insert j₀ J then (if j ∈ C then x₁ j else x₀ j) else z j
    have hL0 : (∑ A ∈ J.powerset, u A.card * ∏ j : Fin m, if j ∈ insert j₀ J then if j ∈ A then -s *
      x₀ j + c * x₁ j else c * x₀ j + s * x₁ j else z j) = ∑ A ∈ J.powerset, u A.card * ∏ j : Fin m,
      if j ∈ J then if j ∈ A then -s * x₀ j + c * x₁ j else c * x₀ j + s * x₁ j else z₀ j := by
      refine Finset.sum_congr rfl fun A hA ↦ congrArg (u A.card * ·) ?_
      have hj₀A : j₀ ∉ A := fun h ↦ hj₀ (Finset.mem_powerset.mp hA h)
      refine Finset.prod_congr rfl fun j _ ↦ ?_; by_cases hj : j = j₀
      · subst hj; simp [z₀, hj₀, hj₀A]
      · simp [z₀, hj]
    have hL1 : (∑ A ∈ J.powerset, u (insert j₀ A).card * ∏ j : Fin m, if j ∈ insert j₀ J then if j ∈
      insert j₀ A then -s * x₀ j + c * x₁ j else c * x₀ j + s * x₁ j else z j) = ∑ A ∈ J.powerset, u
      (A.card + 1) * ∏ j : Fin m, if j ∈ J then if j ∈ A then -s * x₀ j + c * x₁ j else c * x₀ j + s
      * x₁ j else z₁ j := by
      refine Finset.sum_congr rfl fun A hA ↦ ?_
      have hj₀A : j₀ ∉ A := fun h ↦ hj₀ (Finset.mem_powerset.mp hA h)
      rw [Finset.card_insert_of_notMem hj₀A]
      refine congrArg (u (A.card + 1) * ·) (Finset.prod_congr rfl fun j _ ↦ ?_); by_cases hj : j =
        j₀
      · subst hj; simp [z₁, hj₀]
      · simp [z₁, hj]
    rw [hL0, hL1, ih z₀ u, ih z₁ (fun w ↦ u (w + 1))]
    have hsplit_prod (B : Finset (Fin m)) (hB : B ∈ J.powerset) (a b : R) : (∏ j : Fin m, if j ∈ J
      then (if j ∈ B then x₁ j else x₀ j) else (if j = j₀ then a * x₀ j₀ + b * x₁ j₀ else z j)) = a
      * P_out B + b * P_out (insert j₀ B) := by
      have hj₀B : j₀ ∉ B := fun h ↦ hj₀ (Finset.mem_powerset.mp hB h)
      let restProd : R :=
        ∏ j ∈ Finset.univ.erase j₀, if j ∈ J then (if j ∈ B then x₁ j else x₀ j) else z j
      have hLHS : (∏ j : Fin m, if j ∈ J then (if j ∈ B then x₁ j else x₀ j) else (if j = j₀ then a
        * x₀ j₀ + b * x₁ j₀ else z j)) = (a * x₀ j₀ + b * x₁ j₀) * restProd := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]; simp only [hj₀, ↓reduceIte]
        refine congrArg ((a * x₀ j₀ + b * x₁ j₀) * ·) (Finset.prod_congr rfl fun j hj_er ↦ ?_)
        have hj_ne : j ≠ j₀ := Finset.ne_of_mem_erase hj_er; simp [hj_ne]
      have hP0 : P_out B = x₀ j₀ * restProd := by
        dsimp only [P_out]; rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
        simp only [Finset.mem_insert_self, hj₀B, ↓reduceIte]
        refine congrArg (x₀ j₀ * ·) (Finset.prod_congr rfl fun j hj_er ↦ ?_); have hj_ne : j ≠ j₀ :=
          Finset.ne_of_mem_erase hj_er; simp [hj_ne]
      have hP1 : P_out (insert j₀ B) = x₁ j₀ * restProd := by
        dsimp only [P_out]; rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
        simp only [Finset.mem_insert_self, ↓reduceIte]
        refine congrArg (x₁ j₀ * ·) (Finset.prod_congr rfl fun j hj_er ↦ ?_); have hj_ne : j ≠ j₀ :=
          Finset.ne_of_mem_erase hj_er; simp [hj_ne]
      rw [hLHS, hP0, hP1]; ring
    have hsum0 : (∑ B ∈ J.powerset, dickeStep J.card c s u B.card * ∏ j : Fin m, if j ∈ J then (if j
      ∈ B then x₁ j else x₀ j) else z₀ j) = ∑ B ∈ J.powerset, (c * dickeStep J.card c s u B.card *
      P_out B + s * dickeStep J.card c s u B.card * P_out (insert j₀ B)) :=
      (by refine Finset.sum_congr rfl fun B hB ↦ ?_; rw [hsplit_prod B hB c s]; ring)
    have hsum1 : (∑ B ∈ J.powerset, dickeStep J.card c s (fun w ↦ u (w + 1)) B.card * ∏ j : Fin m,
      if j ∈ J then (if j ∈ B then x₁ j else x₀ j) else z₁ j) = ∑ B ∈ J.powerset, (-s * dickeStep
      J.card c s (fun w ↦ u (w + 1)) B.card * P_out B + c * dickeStep J.card c s (fun w ↦ u (w + 1))
      B.card * P_out (insert j₀ B)) :=
      (by refine Finset.sum_congr rfl fun B hB ↦ ?_; rw [hsplit_prod B hB (-s) c]; ring); rw [hsum0,
      hsum1, ← Finset.sum_add_distrib]
    have hcomb : (∑ B ∈ J.powerset, ((c * dickeStep J.card c s u B.card * P_out B + s * dickeStep
      J.card c s u B.card * P_out (insert j₀ B)) + (-s * dickeStep J.card c s (fun w ↦ u (w + 1))
      B.card * P_out B + c * dickeStep J.card c s (fun w ↦ u (w + 1)) B.card * P_out (insert j₀
      B)))) = (∑ B ∈ J.powerset, dickeStep (J.card + 1) c s u B.card * P_out B) + ∑ B ∈ J.powerset,
      dickeStep (J.card + 1) c s u (insert j₀ B).card * P_out (insert j₀ B) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun B hB ↦ ?_; have hBle : B.card ≤
        J.card := Finset.card_le_card (Finset.mem_powerset.mp hB)
      have hj₀B : j₀ ∉ B := fun h ↦ hj₀ (Finset.mem_powerset.mp hB h); have hd0 : dickeStep (J.card
        + 1) c s u B.card = c * dickeStep J.card c s u B.card - s * dickeStep J.card c s (fun w ↦ u
        (w + 1)) B.card := (by simp [dickeStep, hBle])
      have hd1 : dickeStep (J.card + 1) c s u (insert j₀ B).card = s * dickeStep J.card c s u B.card
        + c * dickeStep J.card c s (fun w ↦ u (w + 1)) B.card := by
        rw [Finset.card_insert_of_notMem hj₀B, dickeStep_alt J.card c s u (by omega) (by omega),
          Nat.add_sub_cancel]
      rw [hd0, hd1]; ring
    exact hcomb
/- ## Section 4: 2D Grover Subspace Evolution & Disjoint-Support Dicke Slot Basis -/
/-- Normalized 2D Grover plane vector on `2 ^ q` basis states (`x` on `Mᶜ`, `y` on `M`). -/
noncomputable def grover2DVec {q : ℕ} (M : Finset (Fin (2 ^ q))) (x y : ℝ)
    (u : Fin (2 ^ q)) : ℂ :=
  if u ∈ M then ((y / √(M.card : ℝ) : ℝ) : ℂ)
  else ((x / √((2 ^ q : ℝ) - M.card) : ℝ) : ℂ)
theorem grover2DVec_linear {q : ℕ} (M : Finset (Fin (2 ^ q))) (x y : ℝ) : grover2DVec M x y = (x :
  ℂ) • grover2DVec M 1 0 + (y : ℂ) • grover2DVec M 0 1 := by
  funext u; unfold grover2DVec; by_cases hu : u ∈ M <;> simp [hu, div_eq_mul_inv]
theorem hadamard_zero_eq_grover2DVec {q : ℕ} (M : Finset (Fin (2 ^ q))) (h0 : 0 < M.card) (hlt :
  M.card < 2 ^ q) :
    let θ := Real.arcsin √((M.card : ℝ) / (2 ^ q : ℝ))
    hadamardMatrix q *ᵥ single 0 1 = grover2DVec M (cos θ) (sin θ) := by
  intro θ; set D : ℝ := (2 ^ q : ℝ); set r : ℝ := (M.card : ℝ); have hD_pos : 0 < D :=
    (by positivity); have hr_pos : 0 < r := (by dsimp only [r]; exact_mod_cast h0)
  have hrc_pos : 0 < D - r := sub_pos.mpr (by dsimp only [D, r]; exact_mod_cast hlt)
  set p : ℝ := r / D; have hp0 : 0 < p := div_pos hr_pos hD_pos; have hp1 : p < 1 := (div_lt_one
    hD_pos).mpr (by dsimp only [D, r]; exact_mod_cast hlt)
  have hsinθ : sin θ = √r / √D := by
    rw [show θ = arcsin √p from rfl, Real.sin_arcsin (by linarith [Real.sqrt_nonneg p])
      (Real.sqrt_le_one.mpr hp1.le), Real.sqrt_div hr_pos.le]
  have hcosθ : cos θ = √(D - r) / √D := by
    rw [show θ = arcsin √p from rfl, Real.cos_arcsin, Real.sq_sqrt hp0.le]; have hsub : 1 - p = (D -
      r) / D := (by dsimp only [p]; field_simp [hD_pos.ne']); rw [hsub, Real.sqrt_div hrc_pos.le]
  funext u; rw [mulVec_single_one, col_apply, hadamardMatrix_apply_zero]; unfold grover2DVec
  by_cases hu : u ∈ M
  · rw [ite_eq_left hu, hsinθ, div_div, mul_comm (√D) (√r), ← div_div, div_self (Real.sqrt_pos.mpr
      hr_pos).ne']; push_cast [D]; rfl
  · rw [ite_eq_right hu, hcosθ, div_div, mul_comm (√D) (√(D - r)), ← div_div, div_self
      (Real.sqrt_pos.mpr hrc_pos).ne']; push_cast [D]; rfl
theorem diffuser_oracle_mulVec_grover2DVec {q : ℕ} (M : Finset (Fin (2 ^ q))) (h0 : 0 < M.card) (hlt
  : M.card < 2 ^ q) (x y : ℝ) :
    let θ := Real.arcsin √((M.card : ℝ) / (2 ^ q : ℝ))
    Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ grover2DVec M x y) = grover2DVec M (cos (2 * θ) * x -
      sin (2 * θ) * y) (sin (2 * θ) * x + cos (2 * θ) * y) := by
  intro θ; set D : ℝ := (2 ^ q : ℝ); set r : ℝ := (M.card : ℝ); have hD_pos : 0 < D :=
    (by positivity); have hr_pos : 0 < r := (by dsimp only [r]; exact_mod_cast h0)
  have hrc_pos : 0 < D - r := sub_pos.mpr (by dsimp only [D, r]; exact_mod_cast hlt)
  set p : ℝ := r / D; have hp0 : 0 < p := div_pos hr_pos hD_pos; have hp1 : p < 1 := (div_lt_one
    hD_pos).mpr (by dsimp only [D, r]; exact_mod_cast hlt)
  have hsinθ : sin θ = √r / √D := by
    rw [show θ = arcsin √p from rfl, Real.sin_arcsin (by linarith [Real.sqrt_nonneg p])
      (Real.sqrt_le_one.mpr hp1.le), Real.sqrt_div hr_pos.le]
  have hcosθ : cos θ = √(D - r) / √D := by
    rw [show θ = arcsin √p from rfl, Real.cos_arcsin, Real.sq_sqrt hp0.le]; have hsub : 1 - p = (D -
      r) / D := (by dsimp only [p]; field_simp [hD_pos.ne']); rw [hsub, Real.sqrt_div hrc_pos.le]
  set a : ℝ := y / √r; set b : ℝ := x / √(D - r)
  have horac (v : Fin (2 ^ q)) : (oracleMat M *ᵥ grover2DVec M x y) v = if v ∈ M then ((-a : ℝ) : ℂ)
    else ((b : ℝ) : ℂ) := by
    rw [oracleMat, mulVec_diagonal]; unfold grover2DVec; change (if v ∈ M then (-1 : ℂ) else 1) *
      (if v ∈ M then ((a : ℝ) : ℂ) else ((b : ℝ) : ℂ)) = _; by_cases hv : v ∈ M <;> simp [hv]
  have hite (v : Fin (2 ^ q)) : (if v ∈ M then ((-a : ℝ) : ℂ) else ((b : ℝ) : ℂ)) = ((b : ℝ) : ℂ) +
    if v ∈ M then ((-a - b : ℝ) : ℂ) else 0 := (by by_cases hv : v ∈ M <;> simp [hv])
  have hsum : (∑ v : Fin (2 ^ q), (oracleMat M *ᵥ grover2DVec M x y) v) = ((√D * (cos θ * x - sin θ
    * y) : ℝ) : ℂ) := by
    simp_rw [horac, hite, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have hreal : D * b + r * (-a - b) = √D * (cos θ * x - sin θ * y) := by
      have h1 : r * a = √D * (sin θ * y) := by
        dsimp only [a]; rw [hsinθ, mul_div_assoc', div_eq_iff (Real.sqrt_pos.mpr hr_pos).ne']
        calc r * y = (√r * √r) * y := by rw [Real.mul_self_sqrt hr_pos.le]
          _ = √D * (√r / √D * y) * √r := by
              rw [← mul_assoc (√D), mul_div_cancel₀ _ (Real.sqrt_pos.mpr hD_pos).ne']; ring
      have h2 : (D - r) * b = √D * (cos θ * x) := by
        dsimp only [b]; rw [hcosθ, mul_div_assoc', div_eq_iff (Real.sqrt_pos.mpr hrc_pos).ne']
        calc (D - r) * x = (√(D - r) * √(D - r)) * x := by rw [Real.mul_self_sqrt hrc_pos.le]
          _ = √D * (√(D - r) / √D * x) * √(D - r) := by
              rw [← mul_assoc (√D), mul_div_cancel₀ _ (Real.sqrt_pos.mpr hD_pos).ne']; ring
      have hexp : D * b + r * (-a - b) = (D - r) * b - r * a := (by ring); rw [hexp, h2, h1]; ring
    rw [← hreal]; dsimp only [D, r]; push_cast; ring
  funext u; rw [Grover.diffuserMatrix_mulVec, hsum, horac u, show (2 : ℂ) / (2 ^ q : ℂ) = ((2 / D :
    ℝ) : ℂ) by push_cast [D]; rfl]
  have h2D : (2 / D) * (√D * (cos θ * x - sin θ * y)) = (2 / √D) * (cos θ * x - sin θ * y) := by
    have h2_eq : 2 / D * √D = 2 / √D := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hD_pos.ne' (Real.sqrt_pos.mpr hD_pos).ne', mul_assoc,
        Real.mul_self_sqrt hD_pos.le]
    rw [← mul_assoc, h2_eq]
  unfold grover2DVec; have hs2 : sin (2 * θ) = 2 * sin θ * cos θ := Real.sin_two_mul θ
  have hc2_s : cos (2 * θ) = 1 - 2 * sin θ ^ 2 := (by rw [Real.cos_two_mul, Real.cos_sq']; ring)
  have hc2_c : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := Real.cos_two_mul θ; by_cases hu : u ∈ M
  · rw [ite_eq_left hu, ite_eq_left hu, ← Complex.ofReal_mul, ← Complex.ofReal_sub]; congr 1
    rw [h2D]; have h2M : 2 / √D = 2 * sin θ / √r :=
      (by rw [hsinθ]; field_simp [(Real.sqrt_pos.mpr hr_pos).ne', (Real.sqrt_pos.mpr hD_pos).ne'])
    dsimp only [a, r]; rw [h2M, hs2, hc2_s]; ring
  · rw [ite_eq_right hu, ite_eq_right hu, ← Complex.ofReal_mul, ← Complex.ofReal_sub]; congr 1
    rw [h2D]; have h2Mc : 2 / √D = 2 * cos θ / √(D - r) :=
      (by rw [hcosθ]; field_simp [(Real.sqrt_pos.mpr hrc_pos).ne', (Real.sqrt_pos.mpr hD_pos).ne'])
    dsimp only [b, D, r]; rw [h2Mc, hs2, hc2_c]; ring
theorem diffuser_oracle_iter_grover2DVec {q : ℕ} (M : Finset (Fin (2 ^ q))) (h0 : 0 < M.card) (hlt :
  M.card < 2 ^ q) (t : ℕ) (x y : ℝ) :
    let θ := Real.arcsin √((M.card : ℝ) / (2 ^ q : ℝ))
    (fun v ↦ Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ v))^[t] (grover2DVec M x y) = grover2DVec M
      (cos (2 * (t : ℝ) * θ) * x - sin (2 * (t : ℝ) * θ) * y) (sin (2 * (t : ℝ) * θ) * x + cos (2 *
      (t : ℝ) * θ) * y) := by
  intro θ
  induction t generalizing x y with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply, diffuser_oracle_mulVec_grover2DVec M h0 hlt, ih]; congr 1
    · push_cast; rw [show 2 * ((t : ℝ) + 1) * θ = 2 * (t : ℝ) * θ + 2 * θ
        by ring, Real.cos_add, Real.sin_add]; ring
    · push_cast; rw [show 2 * ((t : ℝ) + 1) * θ = 2 * (t : ℝ) * θ + 2 * θ
        by ring, Real.sin_add, Real.cos_add]; ring
theorem diffuser_oracle_empty_groverMultiState_zero {q : ℕ} : Grover.diffuserMatrix *ᵥ (oracleMat (∅
  : Finset (Fin (2 ^ q))) *ᵥ groverMultiState (∅ : Finset (Fin (2 ^ q))) 0) = groverMultiState (∅ :
  Finset (Fin (2 ^ q))) 0 := by
  have horac : oracleMat (∅ : Finset (Fin (2 ^ q))) *ᵥ groverMultiState (∅ : Finset (Fin (2 ^ q))) 0
    = groverMultiState (∅ : Finset (Fin (2 ^ q))) 0 :=
    (by funext u; rw [oracleMat, mulVec_diagonal]; simp); rw [horac,
    groverMultiState_zero_eq_hadamard_mulVec]; funext u
  have hval (v : Fin (2 ^ q)) : (hadamardMatrix q *ᵥ single 0 1) v = (1 : ℂ) / (√(2 ^ q : ℝ) : ℂ) :=
    (by rw [mulVec_single_one, col_apply, hadamardMatrix_apply_zero])
  rw [Grover.diffuserMatrix_mulVec]; simp_rw [hval]; rw [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]; have hD : (2 ^ q : ℂ) ≠ 0 := (by positivity); field_simp [hD];
    push_cast; ring
theorem sum_normSq_grover2DVec_zero_one {q : ℕ} (M : Finset (Fin (2 ^ q))) (h0 : 0 < M.card) : (∑ u
  : Fin (2 ^ q), normSq (grover2DVec M 0 1 u)) = 1 := by
  have hr_pos : (0 : ℝ) < M.card := Nat.cast_pos.mpr h0
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M)
    (fun u ↦ normSq (grover2DVec M 0 1 u))
  rw [← hpart, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h1 : (∑ u ∈ M, normSq (grover2DVec M 0 1 u)) = 1 := by
    have hterm (u : Fin (2 ^ q)) (hu : u ∈ M) : normSq (grover2DVec M 0 1 u) = 1 / (M.card : ℝ)
      := by
      unfold grover2DVec; rw [ite_eq_left hu, Complex.normSq_ofReal, div_mul_div_comm, one_mul,
        Real.mul_self_sqrt hr_pos.le]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel hr_pos.ne']
  have h2 : (∑ u ∈ Finset.univ.filter (· ∉ M), normSq (grover2DVec M 0 1 u)) = 0 := by
    refine Finset.sum_eq_zero fun u hu ↦ ?_; have hnot : u ∉ M := (Finset.mem_filter.mp hu).2;
      unfold grover2DVec; simp [hnot]
  linarith
theorem sum_normSq_grover2DVec_one_zero {q : ℕ} (M : Finset (Fin (2 ^ q))) (hlt : M.card < 2 ^ q) :
  (∑ u : Fin (2 ^ q), normSq (grover2DVec M 1 0 u)) = 1 := by
  have hrc_pos : (0 : ℝ) < (2 ^ q : ℝ) - M.card := sub_pos.mpr (by exact_mod_cast hlt)
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M)
    (fun u ↦ normSq (grover2DVec M 1 0 u))
  rw [← hpart, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h1 : (∑ u ∈ M, normSq (grover2DVec M 1 0 u)) = 0 :=
    (by refine Finset.sum_eq_zero fun u hu ↦ ?_; unfold grover2DVec; simp [hu])
  have h2 : (∑ u ∈ Finset.univ.filter (· ∉ M), normSq (grover2DVec M 1 0 u)) = 1 := by
    have hcard_c : ((Finset.univ.filter (· ∉ M)).card : ℝ) = (2 ^ q : ℝ) - M.card := by
      have hc := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M) (fun _ ↦ (1 : ℝ))
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
        mul_one, Finset.card_univ, Fintype.card_fin] at hc; push_cast at hc; linarith
    have hterm (u : Fin (2 ^ q)) (hu : u ∈ Finset.univ.filter (· ∉ M)) :
        normSq (grover2DVec M 1 0 u) = 1 / ((2 ^ q : ℝ) - M.card) := by
      have hnot : u ∉ M := (Finset.mem_filter.mp hu).2; unfold grover2DVec; rw [ite_eq_right hnot,
        Complex.normSq_ofReal, div_mul_div_comm, one_mul, Real.mul_self_sqrt hrc_pos.le]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcard_c, mul_one_div_cancel
      hrc_pos.ne']
  linarith
/- ## Section 4b: Public `WeakDicke` 1D Operators & Rotated Product Dicke Basis -/
/-- Unnormalized damping of the all-hit subset amplitude `w = r` by `pyth.cVal`. -/
noncomputable def wdDampAmp (r : ℕ) (pyth : PythPair) (u : ℕ → ℝ) : ℕ → ℝ :=
  fun w ↦ if w = r then pyth.cVal * u w else u w
/-- Initial per-subset Dicke amplitude after `kInit` Grover steps + initial marking oracle. -/
noncomputable def wdInitAmp (r : ℕ) (θ₁ : ℝ) (kInit : ℕ) : ℕ → ℝ :=
  dickeStep r (Real.cos ((2 * (kInit : ℝ) + 1) * θ₁))
    (Real.sin ((2 * (kInit : ℝ) + 1) * θ₁))
    (fun w ↦ if w = 0 then 1 else 0)
/-- Expected extra parallel oracle queries along `probes` on collision-free `R` (`R.card =
  r`). -/
noncomputable def wdChainExtraQueries (r : ℕ) (θ₁ : ℝ) :
    List (PythPair × ℕ) → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | (pyth, kNext) :: rest, u =>
      let u' := wdDampAmp r pyth u
      (∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) * (u' w) ^ 2) * ((kNext + 2 : ℕ) : ℝ) +
        wdChainExtraQueries r θ₁ rest
          (dickeStep r (Real.cos (2 * (kNext : ℝ) * θ₁))
            (Real.sin (2 * (kNext : ℝ) * θ₁)) u')
/-- Final unnormalized per-subset Dicke amplitude at readout (`probes` exhausted without
  click). -/
noncomputable def wdChainFinalAmp (r : ℕ) (θ₁ : ℝ) :
    List (PythPair × ℕ) → (ℕ → ℝ) → (ℕ → ℝ)
  | [], u => u
  | (pyth, kNext) :: rest, u =>
      wdChainFinalAmp r θ₁ rest
        (dickeStep r (Real.cos (2 * (kNext : ℝ) * θ₁))
          (Real.sin (2 * (kNext : ℝ) * θ₁)) (wdDampAmp r pyth u))
/-- Maximum parallel oracle queries executed by `(kInit, probes)` (when no probe clicks). -/
def wdMaxQueries (kInit : ℕ) (probes : List (PythPair × ℕ)) : ℕ :=
  (kInit + 1) + (probes.map fun pk ↦ pk.2 + 2).sum
/-- Total subcube Grover steps executed when no probe clicks. -/
def wdTotalSteps (kInit : ℕ) (probes : List (PythPair × ℕ)) : ℕ :=
  kInit + (probes.map Prod.snd).sum
/-- One-slot Bernoulli backward step on a remaining-target potential `g`. -/
def wdBernStep (p : ℝ) (g : ℕ → ℝ) (u : ℕ) : ℝ :=
  if u = 0 then g 0 else g u - p * (g u - g (u - 1))
/-- Expected remaining-target potential on a `SinglePair` collision (`1` pair slot at `p₂`
  and
  `r - 2` singleton slots at `p₁`). -/
def wdSinglePairRem (p₁ p₂ : ℝ) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  ((wdBernStep p₁)^[r - 2] (wdBernStep p₂ f)) r
/-- 1-pass `GoodSuffix` Bellman upper bound for `WeakDicke` at `R.card = r` (`subN = n - p`,
  `m = 2 ^ p`, assuming `f 0 = 0` and `f` monotone on `0.. r`). -/
noncomputable def wdOneDimUpper (subN m : ℕ)
    (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 0
  else
    match sched r with
    | none => f r
    | some (kInit, probes) =>
        let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
        let θ₂ := Real.arcsin (√(2 / (2 ^ subN : ℝ)))
        let u₀ := wdInitAmp r θ₁ kInit
        let uf := wdChainFinalAmp r θ₁ probes u₀
        let qDist := ((kInit + 1 : ℕ) : ℝ) + wdChainExtraQueries r θ₁ probes u₀
        let remDist := ∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) * (uf w) ^ 2 * f (r - w)
        let qColl := (wdMaxQueries kInit probes : ℝ)
        let kTot := wdTotalSteps kInit probes
        let p₁ := Real.sin ((2 * (kTot : ℝ) + 1) * θ₁) ^ 2
        let p₂ := Real.sin ((2 * (kTot : ℝ) + 1) * θ₂) ^ 2
        let pDist := rotCfProb m r
        let pPair := rotPairProb m r
        let pRem := (1 - pDist) - pPair
        pDist * (qDist + remDist) + (1 - pDist) * qColl +
          pPair * wdSinglePairRem p₁ p₂ f r + pRem * f r
abbrev wdCast1nReg {n p : ℕ} (hp : p ≤ n) : QRegister ((n - p) + p) (1 * n) :=
  QRegister.block 0 ((n - p) + p) (by omega)
private abbrev wdCast1nEquiv {n p : ℕ} (hp : p ≤ n) :
    Fin (2 ^ (1 * n)) ≃ Fin (2 ^ ((n - p) + p)) :=
  finCongr (by congr 1; omega)
private lemma extractIndex_wdCast1nReg {n p : ℕ} (hp : p ≤ n) (u : Fin (2 ^ (1 * n))) : (wdCast1nReg
  hp).extractIndex u = wdCast1nEquiv hp u := by
  apply (basisBits ((n - p) + p)).injective; funext q; rw [basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]; simp [wdCast1nReg, wdCast1nEquiv]
private lemma agreeOutside_wdCast1nReg {n p : ℕ} (hp : p ≤ n) (i j : Fin (2 ^ (1 * n))) :
  (wdCast1nReg hp).AgreeOutside i j := by
  intro q hq; exact False.elim (hq ⟨⟨q.val, by omega⟩, Fin.ext (by simp [wdCast1nReg])⟩)
private lemma embedMatrix_wdCast1nReg_mulVec_comp {n p : ℕ} (hp : p ≤ n) (B : Operator (2 ^ ((n - p)
  + p))) (ψ : Fin (2 ^ ((n - p) + p)) → ℂ) : (wdCast1nReg hp).embedMatrix B *ᵥ (ψ ∘ wdCast1nEquiv
  hp) = (B *ᵥ ψ) ∘ wdCast1nEquiv hp := by
  funext i; rw [Matrix.mulVec, dotProduct]; simp_rw [QRegister.embedMatrix_apply_of_agreeOutside,
    extractIndex_wdCast1nReg, agreeOutside_wdCast1nReg, ite_true, mul_one]; exact (wdCast1nEquiv
    hp).sum_comp (fun y ↦ B (wdCast1nEquiv hp i) y * ψ y)
private lemma wd_finCongr_symm_finCongr {a b : ℕ} (h : a = b) (j : Fin a) : finCongr h.symm
  (finCongr h j) = j := by ext; simp
private lemma subcubeSplit_addrEquiv_one_wd {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (u : Fin (2 ^
  (1 * n))) : subcubeSplit hp hm (addrEquiv n 1 u 0) = ((lowHighEquiv (n - p) p (wdCast1nEquiv hp
  u)).1, finCongr hm.symm (lowHighEquiv (n - p) p (wdCast1nEquiv hp u)).2) := by
  have hcast : finCongr (by congr 1; omega) (addrEquiv n 1 u 0) = wdCast1nEquiv hp u := by
    ext
    rw [finCongr_apply, Fin.val_cast, addrEquiv_eq_div_pow_mod]; simp only [Fin.val_zero, pow_zero,
      Nat.div_one, finCongr_apply, Fin.val_cast]
    exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using u.isLt)
  unfold subcubeSplit; rw [Equiv.trans_apply, Equiv.trans_apply, hcast]; rfl
private lemma mem_oddSet_one_iff_wd {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) : u ∈
  oddSet n 1 S ↔ addrEquiv n 1 u 0 ∈ S := by
  rw [oddSet, Finset.mem_filter]; simp only [Finset.mem_univ, true_and, Fin.prod_univ_one]
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h1 ↦ absurd h1 (by norm_num), fun hm ↦ absurd hm h⟩
private lemma firstTupleHit_one_eq_wd {n : ℕ} (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (1 * n))) :
  firstTupleHit n 1 S u = if addrEquiv n 1 u 0 ∈ S then some (addrEquiv n 1 u 0) else none := by
  unfold firstTupleHit; by_cases hu : u ∈ oddSet n 1 S
  · have hmem : addrEquiv n 1 u 0 ∈ S := (mem_oddSet_one_iff_wd S u).mp hu; rw [dite_eq_left hu,
      ite_eq_left hmem]
    exact congrArg (fun j : Fin 1 ↦ some (addrEquiv n 1 u j)) (Subsingleton.elim _ _)
  · have hnmem : addrEquiv n 1 u 0 ∉ S := mt (mem_oddSet_one_iff_wd S u).mpr hu; rw [dite_eq_right
      hu, ite_eq_right hnmem]
abbrev wdPerm1n {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) :
    Equiv.Perm (Fin (2 ^ (1 * n))) :=
  (finCongr (by rw [Nat.one_mul])).trans (perm.trans (finCongr (by rw [Nat.one_mul])).symm)
private lemma wdPerm1n_symm {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) : (wdPerm1n perm).symm =
  wdPerm1n perm.symm := by ext u; simp [wdPerm1n]
private lemma addrEquiv_wdPerm1n_zero {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) (u : Fin (2 ^ (1 *
  n))) : addrEquiv n 1 (wdPerm1n perm u) 0 = perm (addrEquiv n 1 u 0) := by
  have he1n (v : Fin (2 ^ (1 * n))) : addrEquiv n 1 v 0 = finCongr (by rw [Nat.one_mul]) v := by
    ext
    rw [addrEquiv_eq_div_pow_mod, finCongr_apply, Fin.val_cast]; simp only [Fin.val_zero, pow_zero,
      Nat.div_one]; exact Nat.mod_eq_of_lt (by simpa [Nat.one_mul] using v.isLt)
  rw [he1n, he1n]; simp [wdPerm1n]
private lemma permUnitary_mulVec_comp_wd {d : ℕ} (σ : Equiv.Perm (Fin d)) (ψ : Fin d → ℂ) :
  (permutationUnitary σ).1 *ᵥ ψ = ψ ∘ σ.symm := by
  funext i
  rw [Matrix.mulVec, dotProduct,
    sum_eq_single (σ.symm i) (fun j hj ↦ by
      have hne : i ≠ σ j := fun h ↦ hj ((σ.symm_apply_eq).mpr h).symm
      rw [permutationUnitary_apply, ite_eq_right hne, zero_mul])]
  rw [permutationUnitary_apply, ite_eq_left (σ.apply_symm_apply i).symm, one_mul]; rfl
private lemma permUnitary_parallelMarkPerm_mulVec_apply_wd {n m : ℕ} (R : Finset (Fin (2 ^ n))) (ψ :
  Fin (2 ^ (m * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ((permutationUnitary
  (parallelMarkPerm n m R)).1 *ᵥ ψ) w = ψ (parallelMarkPerm n m R w) := by
  rw [permUnitary_mulVec_comp_wd]; dsimp only [Function.comp_apply]
  congr 1; exact Equiv.symm_apply_eq _ |>.mpr (parallelMarkPerm_involutive R w).symm
noncomputable def wdSlotPrep {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (j : Fin m) : Unitary (2 ^ (1 * (n + 1))) :=
  (addrReg n 1).embedUnitary (permutationUnitary (wdPerm1n perm.symm)) * (addrReg n
  1).embedUnitary ((wdCast1nReg hp).embedUnitary (((lowBlock (n - p) p).embedUnitary
  hadamardUnitary) * ((highBlock (n - p) p).embedUnitary (permutationUnitary (swap 0 (finCongr hm
  j))))))
noncomputable def wdPrepUnitary {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) : Unitary (2 ^ (m * (n + 1))) :=
  ((finRange m).map fun j ↦
    (groupReg (Nat.mul_one m) j).embedUnitary (wdSlotPrep hp hm perm j)).prod
noncomputable def wdSlotDiffuser {n p : ℕ} (hp : p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) : Unitary (2 ^ (1 * (n + 1))) :=
  (addrReg n 1).embedUnitary (permutationUnitary (wdPerm1n perm.symm)) * (addrReg n
  1).embedUnitary ((wdCast1nReg hp).embedUnitary ((lowBlock (n - p) p).embedUnitary
  Grover.diffuserUnitary)) * (addrReg n 1).embedUnitary (permutationUnitary (wdPerm1n perm))
noncomputable def wdDiffuserUnitary {n p m : ℕ} (hp : p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) : Unitary (2 ^ (m * (n + 1))) :=
  ((finRange m).map fun j ↦
    (groupReg (Nat.mul_one m) j).embedUnitary (wdSlotDiffuser hp perm)).prod
/-- Unified per-slot state embedding a local `(n - p)`-qubit state `φ` into subcube `j`
  under `perm`
  with `0` flag wire. -/
private noncomputable def wdSlotWrap {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (j : Fin m) (φ : Fin (2 ^ (n - p)) → ℂ) :
    Fin (2 ^ (1 * (n + 1))) → ℂ :=
  (addrReg n 1).tensorState
    ((workMemState φ (single (finCongr hm j) 1) ∘ wdCast1nEquiv hp) ∘ wdPerm1n perm)
    (single 0 1)
private noncomputable def wdProdState {n m : ℕ}
    (ξ : Fin m → Fin (2 ^ (1 * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) : ℂ :=
  ∏ j : Fin m, ξ j ((groupReg (Nat.mul_one m) j).extractIndex w)
private lemma prod_groupReg_embedMatrix_mulVec_wd {n m b g : ℕ} (hbg : b * g = m) (A : Fin b →
  Matrix (Fin (2 ^ (g * (n + 1)))) (Fin (2 ^ (g * (n + 1)))) ℂ) (f : Fin b → Fin (2 ^ (g * (n + 1)))
  → ℂ) : ((finRange b).map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod *ᵥ (fun w ↦ ∏ c : Fin b,
  f c ((groupReg hbg c).extractIndex w)) = fun w ↦ ∏ c : Fin b, (A c *ᵥ f c) ((groupReg hbg
  c).extractIndex w) := by
  suffices ∀ l : List (Fin b), l.Nodup → ((l.map fun c ↦ (groupReg hbg c).embedMatrix (A c)).prod)
    *ᵥ (fun w ↦ ∏ c : Fin b, f c ((groupReg hbg c).extractIndex w)) = fun w ↦ ∏ c : Fin b, (if c ∈ l
    then A c *ᵥ f c else f c) ((groupReg hbg c).extractIndex w) by
    rw [this (finRange b) (List.nodup_finRange b)]; funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_left (mem_finRange c)]
  intro l hl
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]; funext w
    exact Finset.prod_congr rfl fun c _ ↦ by rw [ite_eq_right List.not_mem_nil]
  | cons c₀ l ih =>
    rcases List.nodup_cons.mp hl with ⟨hc₀, hl'⟩; rw [map_cons, prod_cons, ← mulVec_mulVec, ih hl',
      embedMatrix_groupReg_mulVec_prod]; funext w; refine Finset.prod_congr rfl fun c _ ↦ ?_
    by_cases h : c = c₀
    · subst h; rw [ite_eq_left rfl, ite_eq_right hc₀, ite_eq_left List.mem_cons_self]
    · have hmem : c ∈ c₀ :: l ↔ c ∈ l := (by simp [List.mem_cons, h]); by_cases hl_mem : c ∈ l
      · rw [ite_eq_left (hmem.mpr hl_mem), ite_eq_right h, ite_eq_left hl_mem]
      · rw [ite_eq_right (mt hmem.mp hl_mem), ite_eq_right h, ite_eq_right hl_mem]
private lemma oracleMat_oddSet_one_mulVec_wdPerm1n {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) (R :
  Finset (Fin (2 ^ n))) (ψ : Fin (2 ^ (1 * n)) → ℂ) : oracleMat (oddSet n 1 R) *ᵥ (ψ ∘ wdPerm1n
  perm) = (oracleMat (oddSet n 1 (R.image perm)) *ᵥ ψ) ∘ wdPerm1n perm := by
  funext u; rw [oracleMat, mulVec_diagonal]; dsimp only [Function.comp_apply]; rw [oracleMat,
    mulVec_diagonal]
  have hiff : u ∈ oddSet n 1 R ↔ wdPerm1n perm u ∈ oddSet n 1 (R.image perm) := by
    rw [mem_oddSet_one_iff_wd, mem_oddSet_one_iff_wd, addrEquiv_wdPerm1n_zero]
    refine ⟨Finset.mem_image_of_mem perm, fun h ↦ ?_⟩; rcases Finset.mem_image.mp h with ⟨y, hy,
      heq⟩
    rwa [← perm.injective heq]
  rw [if_congr hiff rfl rfl]
private lemma oracleMat_oddSet_one_mulVec_subcube_wd {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (T :
  Finset (Fin (2 ^ n))) (j : Fin m) (ψ : Fin (2 ^ (n - p)) → ℂ) : oracleMat (oddSet n 1 T) *ᵥ
  (workMemState ψ (single (finCongr hm j) 1) ∘ wdCast1nEquiv hp) = workMemState (oracleMat
  (subcubeLocalSet hp hm T j) *ᵥ ψ) (single (finCongr hm j) 1) ∘ wdCast1nEquiv hp := by
  funext u; rw [oracleMat, mulVec_diagonal]; dsimp only [Function.comp_apply, workMemState]
  rw [oracleMat, mulVec_diagonal]; by_cases hj : (lowHighEquiv (n - p) p (wdCast1nEquiv hp u)).2 =
    finCongr hm j
  · have hsp := subcubeSplit_addrEquiv_one_wd hp hm u; rw [hj, wd_finCongr_symm_finCongr] at hsp
    have hiff : u ∈ oddSet n 1 T ↔ (lowHighEquiv (n - p) p (wdCast1nEquiv hp u)).1 ∈ subcubeLocalSet
      hp hm T j := (by rw [mem_oddSet_one_iff_wd, mem_subcubeLocalSet_iff, ← hsp,
      Equiv.symm_apply_apply]); rw [hj, Pi.single_eq_same, mul_one, mul_one, if_congr hiff rfl rfl]
  · rw [Pi.single_eq_of_ne hj]; ring
private lemma wdPrepUnitary_mulVec_workMemIdx {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (μ : Fin (2 ^ (k * n))) : (lowBlock (m * (n + 1)) (k * n)).embedMatrix
  (wdPrepUnitary hp hm perm).1 *ᵥ single (workMemIdx n m k 0 μ) 1 = workMemState (wdProdState fun j
  ↦ wdSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0 1)) (single μ 1) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hex0 : (addrReg n 1).extractIndex 0 = 0 :=
    (by apply (basisBits (1 * n)).injective; funext r; simp [basisBits_extractIndex])
  have henv0 : ((addrReg n 1).basisSplitEquiv 0).2 = 0 :=
    (by funext e; simp [QRegister.basisSplitEquiv])
  have hzero_comp : (single (0 : Fin (2 ^ (1 * n))) (1 : ℂ)) = workMemState (single (0 : Fin (2 ^ (n
    - p))) 1) (single (0 : Fin (2 ^ p)) 1) ∘ wdCast1nEquiv hp := by
    rw [workMemState_zero]; funext u; dsimp only [Function.comp_apply]; by_cases hu : u = 0
    · subst hu; have hc0 : wdCast1nEquiv hp 0 = 0 := Fin.ext (by simp [wdCast1nEquiv]); rw [hc0,
        Pi.single_eq_same, Pi.single_eq_same]
    · have hcne : wdCast1nEquiv hp u ≠ 0 := fun h ↦ hu ((wdCast1nEquiv hp).injective (h.trans
        (Fin.ext (by simp [wdCast1nEquiv])).symm)); rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne
        hcne]
  have hprep_slot (j : Fin m) : (wdSlotPrep hp hm perm j).1 *ᵥ single (0 : Fin (2 ^ (1 * (n + 1))))
    1 = wdSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0 1) := by
    unfold wdSlotPrep wdSlotWrap
    rw [Submonoid.coe_mul, embedUnitary_val, embedUnitary_val, ← mulVec_mulVec,
      QRegister.embedMatrix_mulVec_single_factors, hex0, henv0, embedUnitary_val, Submonoid.coe_mul,
      embedUnitary_val, embedUnitary_val, hzero_comp, embedMatrix_wdCast1nReg_mulVec_comp, ←
      mulVec_mulVec, embedMatrix_highBlock_mulVec_workMemState, permutationUnitary_mulVec_single,
      Equiv.swap_apply_left, embedMatrix_lowBlock_mulVec_workMemState,
      QRegister.embedMatrix_mulVec_tensorState, permUnitary_mulVec_comp_wd, wdPerm1n_symm,
      Equiv.symm_symm]; rfl
  have hsub0 : wdProdState (n := n) (fun _ : Fin m ↦ single 0 1) = single 0 1 := by
    have hex_g0 (c : Fin m) : (groupReg (n := n) hbg1 c).extractIndex 0 = 0 :=
      (by apply (basisBits (1 * (n + 1))).injective; funext r; simp [basisBits_extractIndex])
    funext w; unfold wdProdState; by_cases hw : w = 0
    · subst hw; simp [hex_g0]
    · rw [Pi.single_eq_of_ne hw]
      have hne : ∃ c : Fin m, (groupReg hbg1 c).extractIndex w ≠ 0 := by
        by_contra! hall
        apply hw; apply (groupSplitEquiv hbg1).injective; funext c; rw [groupSplitEquiv_apply,
          groupSplitEquiv_apply, hall c, hex_g0 c]
      obtain ⟨c, hc⟩ := hne; exact Finset.prod_eq_zero (Finset.mem_univ c) (Pi.single_eq_of_ne hc 1)
  rw [workMemIdx, ← workMemState_single, embedMatrix_lowBlock_mulVec_workMemState, ← hsub0]
  have hcoe : (wdPrepUnitary hp hm perm).1 = ((finRange m).map fun j ↦ (groupReg hbg1 j).embedMatrix
    (wdSlotPrep hp hm perm j).1).prod := by
    unfold wdPrepUnitary; rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  unfold wdProdState; rw [hcoe, prod_groupReg_embedMatrix_mulVec_wd hbg1 _ (fun _ ↦ single 0 1)]
  simp_rw [hprep_slot]
/-- One rotated subcube Grover step applies `diffuserMatrix *ᵥ (oracleMat M_loc *ᵥ φ j)`
  independently in every slot `j: Fin m`. -/
private lemma wdDiffuser_mulVec_sDiagM_wdProdState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (φ : Fin m → Fin (2 ^ (n - p)) → ℂ) :
  (wdDiffuserUnitary (m := m) hp perm).1 *ᵥ (sDiagM n m R *ᵥ wdProdState (fun j ↦ wdSlotWrap hp hm
  perm j (φ j))) = wdProdState (fun j ↦ wdSlotWrap hp hm perm j (Grover.diffuserMatrix *ᵥ (oracleMat
  (subcubeLocalSet hp hm (R.image perm) j) *ᵥ φ j))) := by
  let hbg1 : m * 1 = m := Nat.mul_one m
  have hdiff_coe : (wdDiffuserUnitary (m := m) hp perm).1 = ((finRange m).map fun j ↦ (groupReg hbg1
    j).embedMatrix (wdSlotDiffuser hp perm).1).prod := by
    unfold wdDiffuserUnitary; rw [Submonoid.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun _ _ ↦ by simp [embedUnitary_val])
  rw [sDiagM_eq_prod_groupReg hbg1 R]; unfold wdProdState; rw [prod_groupReg_embedMatrix_mulVec_wd
    hbg1]
  have hslot_p (j : Fin m) : sDiagM n 1 R *ᵥ wdSlotWrap hp hm perm j (φ j) = (addrReg n
    1).tensorState ((workMemState (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ φ j)
    (single (finCongr hm j) 1) ∘ wdCast1nEquiv hp) ∘ wdPerm1n perm) (single 0 1) := by
    unfold wdSlotWrap; rw [sDiagM_mulVec_tensorState_zero, oracleMat_oddSet_one_mulVec_wdPerm1n,
      oracleMat_oddSet_one_mulVec_subcube_wd]
  simp_rw [hslot_p]; rw [hdiff_coe, prod_groupReg_embedMatrix_mulVec_wd hbg1]
  have hslot_d (j : Fin m) : (wdSlotDiffuser hp perm).1 *ᵥ (addrReg n 1).tensorState ((workMemState
    (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ φ j) (single (finCongr hm j) 1) ∘
    wdCast1nEquiv hp) ∘ wdPerm1n perm) (single 0 1) = wdSlotWrap hp hm perm j (Grover.diffuserMatrix
    *ᵥ (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ φ j)) := by
    unfold wdSlotDiffuser wdSlotWrap; rw [Submonoid.coe_mul, Submonoid.coe_mul, (addrReg n
      1).embedUnitary_val, (addrReg n 1).embedUnitary_val, (addrReg n 1).embedUnitary_val,
      Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, QRegister.embedMatrix_mulVec_tensorState,
      permUnitary_mulVec_comp_wd]; have hcancel : (((workMemState (oracleMat (subcubeLocalSet hp hm
      (R.image perm) j) *ᵥ φ j) (single (finCongr hm j) 1) ∘ wdCast1nEquiv hp) ∘ wdPerm1n perm) ∘
      (wdPerm1n perm).symm) = workMemState (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ φ
      j) (single (finCongr hm j) 1) ∘ wdCast1nEquiv hp := (by funext v; simp)
    rw [hcancel, QRegister.embedMatrix_mulVec_tensorState, embedUnitary_val,
      embedMatrix_wdCast1nReg_mulVec_comp, embedUnitary_val,
      embedMatrix_lowBlock_mulVec_workMemState, QRegister.embedMatrix_mulVec_tensorState,
      permUnitary_mulVec_comp_wd, wdPerm1n_symm, Equiv.symm_symm]; rfl
  simp_rw [hslot_d]
/-- Iterated `t`-step deflated Grover action on any `wdProdState (wdSlotWrap... φ)`. -/
private lemma wdDeflatedGrover_iter_wdProdState {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^ (k * n))} (hsub :
  memSeen n k (memPrefix k active) μ ⊆ S) (φ : Fin m → Fin (2 ^ (n - p)) → ℂ) (t : ℕ) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1; let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    ((diffOp * phaseOp) ^ t) *ᵥ workMemState (wdProdState (fun j ↦ wdSlotWrap hp hm perm j (φ j)))
      (single μ 1) = workMemState (wdProdState (fun j ↦ wdSlotWrap hp hm perm j ((fun ψ ↦
      Grover.diffuserMatrix *ᵥ (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ ψ))^[t] (φ
      j)))) (single μ 1) := by
  intro W M R fc orac unm phaseOp diffOp
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, ← mulVec_mulVec, deflatedPhaseMat_mulVec_workMemState
      (memPrefix k active) _ μ hsub, show S \ memSeen n k (memPrefix k active) μ = R from rfl,
      embedMatrix_lowBlock_mulVec_workMemState, wdDiffuser_mulVec_sDiagM_wdProdState]
    simp only [Function.iterate_succ_apply']
private lemma card_subcubeLocalSet_image_perm {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (j : Fin m) : (subcubeLocalSet hp hm (R.image
  perm) j).card = (R.filter fun x ↦ subcubePref hp hm (perm x) = j).card := by
  rw [card_subcubeLocalSet_eq]
  have himg : ((R.image perm).filter fun y ↦ subcubePref hp hm y = j) = (R.filter fun x ↦
    subcubePref hp hm (perm x) = j).image perm := by
    ext y; simp only [Finset.mem_filter, Finset.mem_image]; constructor
    · rintro ⟨⟨x, hxR, rfl⟩, hj⟩; exact ⟨x, ⟨hxR, hj⟩, rfl⟩
    · rintro ⟨x, ⟨hxR, hj⟩, rfl⟩; exact ⟨⟨x, hxR, rfl⟩, hj⟩
  rw [himg, Finset.card_image_of_injective _ perm.injective]
private lemma wdSlotWrap_eq_linear {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin
  (2 ^ n))) (j : Fin m) (c s : ℂ) (φ₀ φ₁ : Fin (2 ^ (n - p)) → ℂ) (z : Fin (2 ^ (1 * (n + 1)))) :
  wdSlotWrap hp hm perm j (c • φ₀ + s • φ₁) z = c * wdSlotWrap hp hm perm j φ₀ z + s * wdSlotWrap hp
  hm perm j φ₁ z := by
  dsimp only [wdSlotWrap, tensorState, workMemState, Function.comp_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]; ring
/-- Per-subset Dicke product basis vector for `A ⊆ R.image (subcubePref ∘ perm)`: puts
  `|1⟩_G`
  (`grover2DVec M_loc 0 1`) in slots `j ∈ A`, `|0⟩_G` (`grover2DVec M_loc 1 0`) in slots
  `j ∈ R.image pref \ A`, and `groverMultiState ∅ 0` in empty slots `j ∉ R.image pref`. -/
private noncomputable def wdBasisVec {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (A : Finset (Fin m)) :
    Fin (2 ^ (m * (n + 1))) → ℂ :=
  let pref := fun x ↦ subcubePref hp hm (perm x)
  wdProdState fun j ↦
    wdSlotWrap hp hm perm j
      (if j ∈ R.image pref then
        if j ∈ A then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1
        else grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0
      else groverMultiState ∅ 0)
/-- Symmetric superposition over `A ∈ (R.image pref).powerset` weighted by `u A.card`. -/
private noncomputable def wdAmpState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (u : ℕ → ℝ) :
    Fin (2 ^ (m * (n + 1))) → ℂ :=
  let pref := fun x ↦ subcubePref hp hm (perm x)
  fun w ↦ ∑ A ∈ (R.image pref).powerset, ((u A.card : ℝ) : ℂ) * wdBasisVec hp hm perm R A w
private lemma dickeStep_ofReal (r : ℕ) (cr sr : ℝ) (ur : ℕ → ℝ) (a : ℕ) : ((dickeStep r cr sr ur a :
  ℝ) : ℂ) = dickeStep r (cr : ℂ) (sr : ℂ) (fun b ↦ (ur b : ℂ)) a := by
  induction r generalizing ur a with
  | zero => unfold dickeStep; split_ifs <;> simp
  | succ r ih =>
    unfold dickeStep; split_ifs
    · push_cast; rw [ih, ih]
    · push_cast; rw [ih, ih]
    · simp
private lemma wdSlotLocalCard_of_injOn {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm
  (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x))
  (R : Set (Fin (2 ^ n)))) (j : Fin m) : (subcubeLocalSet hp hm (R.image perm) j).card = if j ∈
  R.image (fun x ↦ subcubePref hp hm (perm x)) then 1 else 0 := by
  rw [card_subcubeLocalSet_image_perm]; by_cases hj : j ∈ R.image (fun x ↦ subcubePref hp hm (perm
    x))
  · rw [ite_eq_left hj]; rcases Finset.mem_image.mp hj with ⟨x₀, hx₀, rfl⟩
    have hsing : (R.filter fun x ↦ subcubePref hp hm (perm x) = subcubePref hp hm (perm x₀)) = {x₀}
      := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; exact ⟨fun ⟨hxR, heq⟩ ↦ hInj hxR
        hx₀ heq, fun h ↦ ⟨h ▸ hx₀, by rw [h]⟩⟩
    rw [hsing, Finset.card_singleton]
  · rw [ite_eq_right hj, Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro x hxR heq
    exact hj (heq ▸ Finset.mem_image_of_mem _ hxR)
/-- Initial preparation + `kInit` deflated Grover steps on collision-free `R` yields
  `wdAmpState hp hm perm R (wdInitAmp R.card θ₁ kInit)`. -/
private lemma wdPrep_grover_eq_wdAmpState {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2
  ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^
  (k * n))} (hsub : memSeen n k (memPrefix k active) μ ⊆ S) (hInj : Set.InjOn (fun x ↦ subcubePref
  hp hm (perm x)) ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^
  n)))) (kInit : ℕ) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1; let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let prepOp := (lowBlock W M).embedMatrix (wdPrepUnitary hp hm perm).1
    ((diffOp * phaseOp) ^ kInit) *ᵥ (prepOp *ᵥ single (workMemIdx n m k 0 μ) 1) = workMemState
      (wdAmpState hp hm perm R (wdInitAmp R.card θ₁ kInit)) (single μ 1) := by
  intro W M R θ₁ fc orac unm phaseOp diffOp prepOp; rw [wdPrepUnitary_mulVec_workMemIdx hp hm perm
    μ, wdDeflatedGrover_iter_wdProdState hp hm perm hsub]; congr 1; funext w
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj; set c₀ := Real.cos ((2 * (kInit
    : ℝ) + 1) * θ₁); set s₀ := Real.sin ((2 * (kInit : ℝ) + 1) * θ₁)
  let x₀ (j : Fin m) : ℂ := wdSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image
    perm) j) 1 0) ((groupReg (Nat.mul_one m) j).extractIndex w)
  let x₁ (j : Fin m) : ℂ := wdSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image
    perm) j) 0 1) ((groupReg (Nat.mul_one m) j).extractIndex w)
  let z (j : Fin m) : ℂ :=
    wdSlotWrap hp hm perm j (groverMultiState ∅ 0) ((groupReg (Nat.mul_one m) j).extractIndex w)
  have hprod_lhs : wdProdState (fun j ↦ wdSlotWrap hp hm perm j ((fun ψ ↦ Grover.diffuserMatrix *ᵥ
    (oracleMat (subcubeLocalSet hp hm (R.image perm) j) *ᵥ ψ))^[kInit] (hadamardMatrix (n - p) *ᵥ
    single 0 1))) w = ∏ j : Fin m, if j ∈ J then (c₀ : ℂ) * x₀ j + (s₀ : ℂ) * x₁ j else z j := by
    unfold wdProdState; refine Finset.prod_congr rfl fun j _ ↦ ?_; dsimp only; have hcard :=
      wdSlotLocalCard_of_injOn hp hm perm hInj j; by_cases hj : j ∈ J
    · rw [ite_eq_left hj]
      have hc1 : (subcubeLocalSet hp hm (R.image perm) j).card = 1 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_left hj] at hcard
      have h0 : 0 < (subcubeLocalSet hp hm (R.image perm) j).card := (by omega)
      have hlt : (subcubeLocalSet hp hm (R.image perm) j).card < 2 ^ (n - p) := (by omega)
      have hθ : Real.arcsin (√(((subcubeLocalSet hp hm (R.image perm) j).card : ℝ) / (2 ^ (n - p) :
        ℝ))) = θ₁ := (by rw [hc1, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one])
      have hinit := hadamard_zero_eq_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0 hlt
      have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0 hlt
        kInit (Real.cos θ₁) (Real.sin θ₁)
      have hc_add : Real.cos (2 * (kInit : ℝ) * θ₁) * Real.cos θ₁ - Real.sin (2 * (kInit : ℝ) * θ₁)
        * Real.sin θ₁ = c₀ := (by rw [← Real.cos_add]; exact congrArg Real.cos (by ring))
      have hs_add : Real.sin (2 * (kInit : ℝ) * θ₁) * Real.cos θ₁ + Real.cos (2 * (kInit : ℝ) * θ₁)
        * Real.sin θ₁ = s₀ := (by rw [← Real.sin_add]; exact congrArg Real.sin (by ring))
      rw [hθ] at hinit hiter; dsimp only at hinit hiter; rw [hc_add, hs_add] at hiter; rw [hinit,
        hiter, grover2DVec_linear, wdSlotWrap_eq_linear]
    · rw [ite_eq_right hj]
      have hc0_card : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_right hj] at hcard
      have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0_card
      rw [hemp, ← groverMultiState_zero_eq_hadamard_mulVec ∅, Function.iterate_fixed
        diffuser_oracle_empty_groverMultiState_zero]
  let uInit : ℕ → ℂ := fun a ↦ if a = 0 then 1 else 0
  have hlhs_pow : (∏ j : Fin m, if j ∈ J then (c₀ : ℂ) * x₀ j + (s₀ : ℂ) * x₁ j else z j) = ∑ A ∈
    J.powerset, uInit A.card * ∏ j : Fin m, if j ∈ J then if j ∈ A then -(s₀ : ℂ) * x₀ j + (c₀ : ℂ)
    * x₁ j else (c₀ : ℂ) * x₀ j + (s₀ : ℂ) * x₁ j else z j := by
    rw [Finset.sum_eq_single ∅ (fun A _ hne ↦ by
      have hc_ne : A.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      simp [uInit, hc_ne]) (fun hnot ↦ absurd (Finset.empty_mem_powerset J) hnot)]
    simp only [Finset.card_empty, uInit, ↓reduceIte, one_mul, Finset.notMem_empty]
  have huInit_eq : (fun b ↦ (((if b = 0 then (1 : ℝ) else 0) : ℝ) : ℂ)) = uInit :=
    (by funext b; dsimp only [uInit]; split_ifs <;> simp); rw [hprod_lhs, hlhs_pow,
    prod_dickeStep_powerset J (c₀ : ℂ) (s₀ : ℂ) x₀ x₁ z uInit]
  unfold wdAmpState wdBasisVec wdInitAmp wdProdState; dsimp only
  refine Finset.sum_congr rfl fun B hB ↦ ?_; rw [hJ_card, dickeStep_ofReal, huInit_eq]; congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_; by_cases hj : j ∈ J
  · rw [ite_eq_left hj]; by_cases hjB : j ∈ B
    · simp [J, hj, hjB, x₁]
    · simp [J, hj, hjB, x₀]
  · simp [J, hj, z]
/-- `kNext` deflated Grover steps transform `wdAmpState hp hm perm R u` into
  `wdAmpState hp hm perm R (dickeStep R.card (cos(2*kNext*θ₁)) (sin(2*kNext*θ₁)) u)`. -/
private lemma wdGrover_iter_wdAmpState {n p m k : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2 ^
  (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} {active : ℕ} {μ : Fin (2 ^
  (k * n))} (hsub : memSeen n k (memPrefix k active) μ ⊆ S) (hInj : Set.InjOn (fun x ↦ subcubePref
  hp hm (perm x)) ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^
  n)))) (u : ℕ → ℝ) (kNext : ℕ) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1; let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    ((diffOp * phaseOp) ^ kNext) *ᵥ workMemState (wdAmpState hp hm perm R u) (single μ 1) =
      workMemState (wdAmpState hp hm perm R (dickeStep R.card (Real.cos (2 * (kNext : ℝ) * θ₁))
      (Real.sin (2 * (kNext : ℝ) * θ₁)) u)) (single μ 1) := by
  intro W M R θ₁ fc orac unm phaseOp diffOp; let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj
  have hlin_ws (f : Finset (Fin m) → Fin (2 ^ W) → ℂ) : workMemState (fun w ↦ ∑ A ∈ J.powerset, f A
    w) (single μ 1) = ∑ A ∈ J.powerset, workMemState (f A) (single μ 1) :=
    (by funext idx; simp [workMemState, Finset.sum_mul]); have hlin_smul (c : ℂ) (ψ : Fin (2 ^ W) →
    ℂ) : workMemState (fun w ↦ c * ψ w) (single μ 1) = c • workMemState ψ (single μ 1) :=
    (by funext idx; simp [workMemState, mul_assoc]); unfold wdAmpState; change ((diffOp * phaseOp) ^
    kNext) *ᵥ workMemState (fun w ↦ ∑ A ∈ J.powerset, ((u A.card : ℝ) : ℂ) * wdBasisVec hp hm perm R
    A w) (single μ 1) = _; rw [hlin_ws, Matrix.mulVec_sum]; set ck := Real.cos (2 * (kNext : ℝ) *
    θ₁); set sk := Real.sin (2 * (kNext : ℝ) * θ₁)
  have hterm (A : Finset (Fin m)) : ((diffOp * phaseOp) ^ kNext) *ᵥ workMemState (fun w ↦ ((u A.card
    : ℝ) : ℂ) * wdBasisVec hp hm perm R A w) (single μ 1) = workMemState (fun w ↦ ((u A.card : ℝ) :
    ℂ) * ∏ j : Fin m, if j ∈ J then if j ∈ A then -(sk : ℂ) * wdSlotWrap hp hm perm j (grover2DVec
    (subcubeLocalSet hp hm (R.image perm) j) 1 0) ((groupReg (Nat.mul_one m) j).extractIndex w) +
    (ck : ℂ) * wdSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1)
    ((groupReg (Nat.mul_one m) j).extractIndex w) else (ck : ℂ) * wdSlotWrap hp hm perm j
    (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0) ((groupReg (Nat.mul_one m)
    j).extractIndex w) + (sk : ℂ) * wdSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm
    (R.image perm) j) 0 1) ((groupReg (Nat.mul_one m) j).extractIndex w) else wdSlotWrap hp hm perm
    j (groverMultiState ∅ 0) ((groupReg (Nat.mul_one m) j).extractIndex w)) (single μ 1) := by
    rw [hlin_smul, Matrix.mulVec_smul, wdBasisVec, wdDeflatedGrover_iter_wdProdState hp hm perm
      hsub, ← hlin_smul]; congr 1; funext w; congr 1; unfold wdProdState
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    dsimp only; have hcard := wdSlotLocalCard_of_injOn hp hm perm hInj j; by_cases hj : j ∈ J
    · have hc1 : (subcubeLocalSet hp hm (R.image perm) j).card = 1 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_left hj] at hcard
      simp only [J] at hj; rw [ite_eq_left hj, ite_eq_left hj]; have h0 : 0 < (subcubeLocalSet hp hm
        (R.image perm) j).card := (by omega); have hlt : (subcubeLocalSet hp hm (R.image perm)
        j).card < 2 ^ (n - p) := (by omega); have hθ : Real.arcsin (√(((subcubeLocalSet hp hm
        (R.image perm) j).card : ℝ) / (2 ^ (n - p) : ℝ))) = θ₁ :=
        (by rw [hc1, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]); by_cases hjA : j ∈ A
      · rw [ite_eq_left hjA, ite_eq_left hjA]
        have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0
          hlt kNext 0 1; rw [hθ] at hiter; dsimp only at hiter; have hc_tr : Real.cos (2 * (kNext :
          ℝ) * θ₁) * 0 - Real.sin (2 * (kNext : ℝ) * θ₁) * 1 = -sk := (by ring)
        have hs_tr : Real.sin (2 * (kNext : ℝ) * θ₁) * 0 + Real.cos (2 * (kNext : ℝ) * θ₁) * 1 = ck
          := (by ring); rw [hc_tr, hs_tr] at hiter; rw [hiter, grover2DVec_linear,
          wdSlotWrap_eq_linear, Complex.ofReal_neg]
      · rw [ite_eq_right hjA, ite_eq_right hjA]
        have hiter := diffuser_oracle_iter_grover2DVec (subcubeLocalSet hp hm (R.image perm) j) h0
          hlt kNext 1 0; rw [hθ] at hiter; dsimp only at hiter; have hc_tr : Real.cos (2 * (kNext :
          ℝ) * θ₁) * 1 - Real.sin (2 * (kNext : ℝ) * θ₁) * 0 = ck := (by ring)
        have hs_tr : Real.sin (2 * (kNext : ℝ) * θ₁) * 1 + Real.cos (2 * (kNext : ℝ) * θ₁) * 0 = sk
          := (by ring); rw [hc_tr, hs_tr] at hiter; rw [hiter, grover2DVec_linear,
          wdSlotWrap_eq_linear]
    · have hc0_card : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
        rwa [show R.image (fun x ↦ subcubePref hp hm (perm x)) = J from rfl,
          ite_eq_right hj] at hcard
      simp only [J] at hj; rw [ite_eq_right hj, ite_eq_right hj]
      have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0_card
      rw [hemp, Function.iterate_fixed diffuser_oracle_empty_groverMultiState_zero]
  simp_rw [hterm]; rw [← hlin_ws]; congr 1; funext w; rw [prod_dickeStep_powerset J (ck : ℂ) (sk :
    ℂ) (fun j ↦ wdSlotWrap hp hm perm j (grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0)
    ((groupReg (Nat.mul_one m) j).extractIndex w)) (fun j ↦ wdSlotWrap hp hm perm j (grover2DVec
    (subcubeLocalSet hp hm (R.image perm) j) 0 1) ((groupReg (Nat.mul_one m) j).extractIndex w))
    (fun j ↦ wdSlotWrap hp hm perm j (groverMultiState ∅ 0) ((groupReg (Nat.mul_one m)
    j).extractIndex w)) (fun b ↦ ((u b : ℝ) : ℂ))]; refine Finset.sum_congr rfl fun B hB ↦ ?_
  rw [hJ_card, ← dickeStep_ofReal]; congr 1; unfold wdBasisVec wdProdState
  refine Finset.prod_congr rfl fun j _ ↦ ?_; dsimp only [J]
  split_ifs <;> rfl
/-- Support characterization of `wdSlotWrap`: any nonzero amplitude has `0` flag wire, and
  its
  marked outcome under `parallelMarkPerm n 1 R` is `some x` (`x ∈ R`, `pref x = j`) iff the
  local
  coordinate belongs to `subcubeLocalSet hp hm (R.image perm) j`. -/
private lemma wdSlotWrap_support_firstMarkedAddr {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (j : Fin m) (φ : Fin (2 ^ (n - p)) → ℂ) (z :
  Fin (2 ^ (1 * (n + 1)))) (hz : wdSlotWrap hp hm perm j φ z ≠ 0) :
    let u := (addrReg n 1).extractIndex z
    let w_loc := (lowHighEquiv (n - p) p (wdCast1nEquiv hp (wdPerm1n perm u))).1
    ((addrReg n 1).basisSplitEquiv z).2 = 0 ∧ φ w_loc ≠ 0 ∧ (lowHighEquiv (n - p) p (wdCast1nEquiv
      hp (wdPerm1n perm u))).2 = finCongr hm j ∧ firstMarkedAddr n 1 (parallelMarkPerm n 1 R z) = if
      w_loc ∈ subcubeLocalSet hp hm (R.image perm) j then some (perm.symm ((subcubeSplit hp hm).symm
      (w_loc, j))) else none := by
  intro u w_loc
  have hE : ((addrReg n 1).basisSplitEquiv z).2 = 0 := by
    by_contra hne
    apply hz; dsimp only [wdSlotWrap, tensorState]; rw [Pi.single_eq_of_ne hne, mul_zero]
  have hy : (lowHighEquiv (n - p) p (wdCast1nEquiv hp (wdPerm1n perm u))).2 = finCongr hm j := by
    by_contra hne; apply hz; dsimp only [wdSlotWrap, tensorState, workMemState, Function.comp_apply]
    rw [Pi.single_eq_of_ne hne, mul_zero, zero_mul]
  have hφ : φ w_loc ≠ 0 := by
    intro h0; apply hz; dsimp only [wdSlotWrap, tensorState, workMemState, Function.comp_apply]
    rw [h0, zero_mul, zero_mul]
  refine ⟨hE, hφ, hy, ?_⟩; rw [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R z hE,
    firstTupleHit_one_eq_wd]; set v := wdPerm1n perm u; have hu_eq : u = (wdPerm1n perm).symm v :=
    (Equiv.symm_apply_apply _ u).symm; have hsp := subcubeSplit_addrEquiv_one_wd hp hm v; rw [hy,
    wd_finCongr_symm_finCongr] at hsp
  have hv_addr : addrEquiv n 1 v 0 = (subcubeSplit hp hm).symm (w_loc, j) :=
    (by rw [← hsp, Equiv.symm_apply_apply])
  have hu_addr : addrEquiv n 1 u 0 = perm.symm ((subcubeSplit hp hm).symm (w_loc, j)) :=
    (by rw [hu_eq, wdPerm1n_symm, addrEquiv_wdPerm1n_zero, hv_addr])
  have hmem_iff : addrEquiv n 1 u 0 ∈ R ↔ w_loc ∈ subcubeLocalSet hp hm (R.image perm) j := by
    rw [hu_addr, mem_subcubeLocalSet_iff]; constructor
    · intro hxR; simpa using Finset.mem_image_of_mem perm hxR
    · intro himg; rcases Finset.mem_image.mp himg with ⟨x, hxR, hx_perm⟩
      have hxeq : x = perm.symm ((subcubeSplit hp hm).symm (w_loc, j)) := (by rw [← hx_perm,
        Equiv.symm_apply_apply]); rwa [← hxeq]
  rw [if_congr hmem_iff rfl rfl, hu_addr]
/-- Whenever every slot `j` of `parallelMarkPerm n m R o` has nonzero `wdSlotWrap hp hm perm
  j`,
  each slot's marked address (if any) belongs to `R` with rotated prefix `j`, so the
  per-slot
  `filterMap` is already `Nodup` and equals `groupHits (Nat.mul_one m) o` without `.dedup`. -/
private lemma groupHits_eq_filterMap_of_wdSlotWrap {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (φ : Fin m → Fin (2 ^ (n - p)) → ℂ) (o : Fin
  (2 ^ (m * (n + 1)))) (hslot_nz : ∀ j : Fin m, wdSlotWrap hp hm perm j (φ j) ((groupReg
  (Nat.mul_one m) j).extractIndex (parallelMarkPerm n m R o)) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∀ (j : Fin m) (x : Fin (2 ^ n)), firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) = some
      x → x ∈ R ∧ subcubePref hp hm (perm x) = j) ∧ groupHits hbg1 o = (finRange m).filterMap fun j
      ↦ firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) := by
  intro hbg1; set w := parallelMarkPerm n m R o; have ho_eq : o = parallelMarkPerm n m R w :=
    (parallelMarkPerm_involutive R o).symm
  have hhit_sub (j : Fin m) (x : Fin (2 ^ n)) (hx : firstMarkedAddr n 1 ((groupReg hbg1
    j).extractIndex o) = some x) : x ∈ R ∧ subcubePref hp hm (perm x) = j := by
    have hsp := wdSlotWrap_support_firstMarkedAddr hp hm perm R j (φ j) _ (hslot_nz j)
    have hex_o : (groupReg hbg1 j).extractIndex o = parallelMarkPerm n 1 R ((groupReg hbg1
      j).extractIndex w) := (by rw [ho_eq, extractIndex_groupReg_parallelMarkPerm]); rw [hex_o,
      hsp.2.2.2] at hx; set w_loc := (lowHighEquiv (n - p) p (wdCast1nEquiv hp (wdPerm1n perm
      ((addrReg n 1).extractIndex ((groupReg hbg1 j).extractIndex w))))).1
    by_cases hmem : w_loc ∈ subcubeLocalSet hp hm (R.image perm) j
    · rw [ite_eq_left hmem, Option.some.injEq] at hx; subst hx; have h_perm :=
        (mem_subcubeLocalSet_iff hp hm (R.image perm) j w_loc).mp hmem
      rcases Finset.mem_image.mp h_perm with ⟨y, hyR, hy_perm⟩
      have hyeq : y = perm.symm ((subcubeSplit hp hm).symm (w_loc, j)) :=
        (by rw [← hy_perm, Equiv.symm_apply_apply]); refine ⟨hyeq ▸ hyR, ?_⟩
      dsimp only [subcubePref]; rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · rw [ite_eq_right hmem] at hx; cases hx
  have hfm_nodup : ∀ (l : List (Fin m)), l.Nodup → (l.filterMap fun j ↦ firstMarkedAddr n 1
    ((groupReg hbg1 j).extractIndex o)).Nodup := by
    intro l hl
    induction l with
    | nil => exact List.nodup_nil
    | cons j js ih =>
      rcases List.nodup_cons.mp hl with ⟨hj_not, hjs_nd⟩
      cases hfa : firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o) with
      | none => simp only [List.filterMap_cons, hfa]; exact ih hjs_nd
      | some x =>
        simp only [List.filterMap_cons, hfa, List.nodup_cons]; refine ⟨fun hmem ↦ ?_, ih hjs_nd⟩
        rcases List.mem_filterMap.mp hmem with ⟨j', hj'mem, hj'eq⟩; have hjeq : j = j' := (hhit_sub
          j x hfa).2.symm.trans (hhit_sub j' x hj'eq).2; exact hj_not (hjeq ▸ hj'mem)
  refine ⟨hhit_sub, ?_⟩; unfold groupHits; exact List.dedup_eq_self.mpr (hfm_nodup (finRange m)
    (List.nodup_finRange m))
private lemma length_filterMap_fin_eq_length_filter {m d : ℕ} (p : Fin m → Option (Fin d)) (l : List
  (Fin m)) : (l.filterMap p).length = (l.filter fun a ↦ (p a).isSome).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hpa : p a <;> simp [List.filterMap_cons_none, List.filterMap_cons_some, hpa, ih]
/-- On any nonzero configuration `w = parallelMarkPerm n m R o` of `wdBasisVec hp hm perm R
  A`
  (`A ⊆ R.image pref`), slot `j` outputs a marked hit iff `j ∈ A`, all hits belong to `R`,
  and
  `wdHitCount n m o = A.card`. -/
private lemma wdBasisVec_support_props {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm
  (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) {A : Finset (Fin m)} (hA : A ⊆ R.image fun x ↦
  subcubePref hp hm (perm x)) (o : Fin (2 ^ (m * (n + 1)))) (hamp : wdBasisVec hp hm perm R A
  (parallelMarkPerm n m R o) ≠ 0) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    (∀ j : Fin m, ((addrReg n 1).basisSplitEquiv ((groupReg hbg1 j).extractIndex (parallelMarkPerm n
      m R o))).2 = 0) ∧ (∀ j : Fin m, (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex
      o)).isSome = true ↔ j ∈ A) ∧ (∀ x ∈ groupHits hbg1 o, x ∈ R) ∧ wdHitCount n m o = A.card :=
      by
  intro hbg1; set w := parallelMarkPerm n m R o; have ho_eq : o = parallelMarkPerm n m R w :=
    (parallelMarkPerm_involutive R o).symm; have hslot_nz (j : Fin m) : wdSlotWrap hp hm perm j (if
    j ∈ R.image (fun x ↦ subcubePref hp hm (perm x)) then if j ∈ A then grover2DVec (subcubeLocalSet
    hp hm (R.image perm) j) 0 1 else grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 1 0 else
    groverMultiState ∅ 0) ((groupReg hbg1 j).extractIndex w) ≠ 0 :=
    (by intro h0; exact hamp (Finset.prod_eq_zero (Finset.mem_univ j) h0))
  have hflags (j : Fin m) : ((addrReg n 1).basisSplitEquiv ((groupReg hbg1 j).extractIndex w)).2 = 0
    := (wdSlotWrap_support_firstMarkedAddr hp hm perm R j _ _ (hslot_nz j)).1
  have hisSome (j : Fin m) : (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome =
    true ↔ j ∈ A := by
    have hsp := wdSlotWrap_support_firstMarkedAddr hp hm perm R j _ _ (hslot_nz j)
    have hex_o : (groupReg hbg1 j).extractIndex o = parallelMarkPerm n 1 R ((groupReg hbg1
      j).extractIndex w) := (by rw [ho_eq, extractIndex_groupReg_parallelMarkPerm]); rw [hex_o,
      hsp.2.2.2]; have hφ := hsp.2.1; set w_loc := (lowHighEquiv (n - p) p (wdCast1nEquiv hp
      (wdPerm1n perm ((addrReg n 1).extractIndex ((groupReg hbg1 j).extractIndex w))))).1
    change _ ≠ 0 at hφ; by_cases hjA : j ∈ A
    · have hjR : j ∈ R.image (fun x ↦ subcubePref hp hm (perm x)) := hA hjA; rw [ite_eq_left hjR,
        ite_eq_left hjA] at hφ
      have hw_mem : w_loc ∈ subcubeLocalSet hp hm (R.image perm) j := by
        by_contra hnot
        apply hφ; unfold grover2DVec; rw [ite_eq_right hnot, zero_div, Complex.ofReal_zero]
      rw [ite_eq_left hw_mem]; simp [hjA]
    · by_cases hjR : j ∈ R.image (fun x ↦ subcubePref hp hm (perm x))
      · rw [ite_eq_left hjR, ite_eq_right hjA] at hφ
        have hw_not : w_loc ∉ subcubeLocalSet hp hm (R.image perm) j := by
          intro hmem; apply hφ; unfold grover2DVec; rw [ite_eq_left hmem, zero_div,
            Complex.ofReal_zero]
        rw [ite_eq_right hw_not]; simp [hjA]
      · have hc0 : (subcubeLocalSet hp hm (R.image perm) j).card = 0 := by
          rw [card_subcubeLocalSet_image_perm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x hxR heq; exact hjR (heq ▸ Finset.mem_image_of_mem _ hxR)
        have hemp : subcubeLocalSet hp hm (R.image perm) j = ∅ := Finset.card_eq_zero.mp hc0
        rw [hemp, ite_eq_right (Finset.notMem_empty w_loc)]; simp [hjA]
  have hnew : ∀ x ∈ groupHits hbg1 o, x ∈ R :=
    (by intro x hx; rw [ho_eq] at hx; exact mem_of_mem_groupHits_parallelMarkPerm hbg1 hflags hx)
  have hgh_eq := (groupHits_eq_filterMap_of_wdSlotWrap hp hm perm R _ o hslot_nz).2
  have hhit_card : wdHitCount n m o = A.card := by
    unfold wdHitCount; change (groupHits hbg1 o).length = A.card
    rw [hgh_eq, length_filterMap_fin_eq_length_filter,
      ← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
    congr 1; ext j; simp [hisSome j]
  exact ⟨hflags, hisSome, hnew, hhit_card⟩
/-- Pointwise disjointness of `wdBasisVec` across distinct subsets `A₁ ≠ A₂` of `R.image
  pref`. -/
private lemma wdBasisVec_mul_eq_zero_of_ne {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) {A₁ A₂ : Finset (Fin m)} (hA₁ : A₁ ⊆ R.image
  fun x ↦ subcubePref hp hm (perm x)) (hA₂ : A₂ ⊆ R.image fun x ↦ subcubePref hp hm (perm x)) (hne :
  A₁ ≠ A₂) (w : Fin (2 ^ (m * (n + 1)))) : wdBasisVec hp hm perm R A₁ w = 0 ∨ wdBasisVec hp hm perm
  R A₂ w = 0 := by
  by_contra! hboth
  set o := parallelMarkPerm n m R w; have hw : w = parallelMarkPerm n m R o :=
    (parallelMarkPerm_involutive R w).symm; rw [hw] at hboth; have h1 := (wdBasisVec_support_props
    hp hm perm R hA₁ o hboth.1).2.1; have h2 := (wdBasisVec_support_props hp hm perm R hA₂ o
    hboth.2).2.1; apply hne; ext j; exact (h1 j).symm.trans (h2 j)
/-- Unit squared norm of `wdSlotWrap hp hm perm j φ` whenever `∑ u, normSq (φ u) = 1`. -/
private lemma sum_normSq_wdSlotWrap {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm
  (Fin (2 ^ n))) (j : Fin m) (φ : Fin (2 ^ (n - p)) → ℂ) (hφ : (∑ u : Fin (2 ^ (n - p)), normSq (φ
  u)) = 1) : (∑ z : Fin (2 ^ (1 * (n + 1))), normSq (wdSlotWrap hp hm perm j φ z)) = 1 := by
  rw [← (addrReg n 1).basisSplitEquiv.symm.sum_comp, sum_prod_type]
  have hflag (u : Fin (2 ^ (1 * n))) : (∑ e, normSq (wdSlotWrap hp hm perm j φ ((addrReg n
    1).basisSplitEquiv.symm (u, e)))) = normSq (((workMemState φ (single (finCongr hm j) 1) ∘
    wdCast1nEquiv hp) ∘ wdPerm1n perm) u) := by
    rw [sum_eq_single 0 (fun e he ↦ by
      dsimp only [wdSlotWrap, tensorState]; rw [← QRegister.basisSplitEquiv_apply_fst,
        Equiv.apply_symm_apply]; dsimp only
      rw [Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero])]
    dsimp only [wdSlotWrap, tensorState]; rw [← QRegister.basisSplitEquiv_apply_fst,
      Equiv.apply_symm_apply]; dsimp only; rw [Pi.single_eq_same, mul_one]
  simp_rw [hflag]; rw [← (wdPerm1n perm).symm.sum_comp]; simp only [Function.comp_apply,
    Equiv.apply_symm_apply]; rw [← (wdCast1nEquiv hp).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]; rw [← (lowHighEquiv (n - p) p).symm.sum_comp, sum_prod_type]
  have hhigh (w_loc : Fin (2 ^ (n - p))) : (∑ y : Fin (2 ^ p), normSq (workMemState φ (single
    (finCongr hm j) 1) ((lowHighEquiv (n - p) p).symm (w_loc, y)))) = normSq (φ w_loc) := by
    rw [sum_eq_single (finCongr hm j) (fun y hy ↦ by
      dsimp only [workMemState]; rw [Equiv.apply_symm_apply]; dsimp only
      rw [Pi.single_eq_of_ne hy, mul_zero, Complex.normSq_zero])]
    dsimp only [workMemState]; rw [Equiv.apply_symm_apply]; dsimp only; rw [Pi.single_eq_same,
      mul_one]
  simp_rw [hhigh]; exact hφ
/-- Factorization of `∑ w, normSq (wdProdState ξ w)` across the `m` slots. -/
private lemma sum_normSq_wdProdState {n m : ℕ} (ξ : Fin m → Fin (2 ^ (1 * (n + 1))) → ℂ) : (∑ w :
  Fin (2 ^ (m * (n + 1))), normSq (wdProdState ξ w)) = ∏ j : Fin m, ∑ z : Fin (2 ^ (1 * (n + 1))),
  normSq (ξ j z) := by
  let hbg1 : m * 1 = m := Nat.mul_one m; rw [← (groupSplitEquiv hbg1).symm.sum_comp]
  have hex (g : Fin m → Fin (2 ^ (1 * (n + 1)))) : normSq (wdProdState ξ ((groupSplitEquiv
    hbg1).symm g)) = ∏ j : Fin m, normSq (ξ j (g j)) := by
    unfold wdProdState; rw [map_prod]; refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply]
  simp_rw [hex]; exact (Fintype.prod_sum fun j z ↦ normSq (ξ j z)).symm
/-- Unit squared norm of `wdBasisVec hp hm perm R A` on collision-free `R` (`2 ≤ 2 ^ (n -
  p)`). -/
private lemma sum_normSq_wdBasisVec {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2 ^ (n -
  p)) (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hInj : Set.InjOn (fun x ↦
  subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n)))) (A : Finset (Fin m)) : (∑ w : Fin (2 ^ (m *
  (n + 1))), normSq (wdBasisVec hp hm perm R A w)) = 1 := by
  unfold wdBasisVec; rw [sum_normSq_wdProdState]
  refine Finset.prod_eq_one fun j _ ↦ sum_normSq_wdSlotWrap hp hm perm j _ ?_; have hcard :=
    wdSlotLocalCard_of_injOn hp hm perm hInj j; by_cases hj : j ∈ R.image (fun x ↦ subcubePref hp hm
    (perm x))
  · rw [ite_eq_left hj]; have hc1 : (subcubeLocalSet hp hm (R.image perm) j).card = 1 :=
      (by simpa [hj] using hcard); have h0 : 0 < (subcubeLocalSet hp hm (R.image perm) j).card :=
      (by omega); have hlt : (subcubeLocalSet hp hm (R.image perm) j).card < 2 ^ (n - p) :=
      (by omega); by_cases hjA : j ∈ A
    · rw [ite_eq_left hjA]; exact sum_normSq_grover2DVec_zero_one _ h0
    · rw [ite_eq_right hjA]; exact sum_normSq_grover2DVec_one_zero _ hlt
  · rw [ite_eq_right hj]; exact sum_normSq_groverMultiState_eq_one ∅ 0
/-- Exact weighted sum over `wdAmpState` squared norms via pointwise disjointness of
  `wdBasisVec`
  and `Finset.card_powersetCard`. -/
private lemma sum_normSq_wdAmpState_mul_card {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤
  2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hInj : Set.InjOn (fun x
  ↦ subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n)))) (u : ℕ → ℝ) (g : ℕ → ℂ) : (∑ o : Fin (2 ^
  (m * (n + 1))), (normSq (wdAmpState hp hm perm R u (parallelMarkPerm n m R o)) : ℂ) * g
  (wdHitCount n m o)) = ∑ w ∈ Finset.range (R.card + 1), (((R.card.choose w : ℝ) * (u w) ^ 2 : ℝ) :
  ℂ) * g w := by
  let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj
  have hpt (o : Fin (2 ^ (m * (n + 1)))) : (normSq (wdAmpState hp hm perm R u (parallelMarkPerm n m
    R o)) : ℂ) * g (wdHitCount n m o) = ∑ A ∈ J.powerset, (((u A.card) ^ 2 * normSq (wdBasisVec hp
    hm perm R A (parallelMarkPerm n m R o)) : ℝ) : ℂ) * g A.card := by
    unfold wdAmpState; set w := parallelMarkPerm n m R o; by_cases hex : ∃ A₀ ∈ J.powerset,
      wdBasisVec hp hm perm R A₀ w ≠ 0
    · rcases hex with ⟨A₀, hA₀, hnz⟩
      have hzero (A : Finset (Fin m)) (hA : A ∈ J.powerset) (hne : A ≠ A₀) : wdBasisVec hp hm perm R
        A w = 0 := by
        rcases wdBasisVec_mul_eq_zero_of_ne hp hm perm R (Finset.mem_powerset.mp hA)
          (Finset.mem_powerset.mp hA₀) hne w with h1 | h2
        · exact h1
        · exact absurd h2 hnz
      rw [Finset.sum_eq_single A₀ (fun A hA hne ↦ by rw [hzero A hA hne, mul_zero])
          (fun hnot ↦ absurd hA₀ hnot),
        Finset.sum_eq_single A₀ (fun A hA hne ↦ by
          rw [hzero A hA hne, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])
          (fun hnot ↦ absurd hA₀ hnot)]
      have hhit := (wdBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA₀) o hnz).2.2.2
      rw [hhit, map_mul, Complex.normSq_ofReal]; push_cast; ring
    · simp only [not_exists, not_and, not_not] at hex
      rw [Finset.sum_eq_zero (fun A hA ↦ by rw [hex A hA, mul_zero]),
        Complex.normSq_zero, Complex.ofReal_zero, zero_mul,
        Finset.sum_eq_zero (fun A hA ↦ by
          rw [hex A hA, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])]
  simp_rw [hpt]; rw [Finset.sum_comm]
  have hsum_A (A : Finset (Fin m)) (_hA : A ∈ J.powerset) : (∑ o : Fin (2 ^ (m * (n + 1))), (((u
    A.card) ^ 2 * normSq (wdBasisVec hp hm perm R A (parallelMarkPerm n m R o)) : ℝ) : ℂ) * g
    A.card) = (((u A.card) ^ 2 : ℝ) : ℂ) * g A.card := by
    simp_rw [Complex.ofReal_mul, mul_assoc]; rw [← Finset.mul_sum]
    have hnorm1 : (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (wdBasisVec hp hm perm R A
      (parallelMarkPerm n m R o)) : ℂ)) = 1 := by
      rw [← Complex.ofReal_sum, Equiv.sum_comp (parallelMarkPerm n m R) (fun w ↦ normSq (wdBasisVec
        hp hm perm R A w)), sum_normSq_wdBasisVec hp hm hsub2 perm hInj A, Complex.ofReal_one]
    rw [← Finset.sum_mul, hnorm1, one_mul]
  rw [Finset.sum_congr rfl hsum_A]
  have hpow_union : J.powerset = (Finset.range (J.card + 1)).biUnion fun w ↦ J.powersetCard w := by
    ext A; simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]; exact ⟨fun h ↦ ⟨A.card, Nat.lt_succ_of_le (Finset.card_le_card h),
      h, rfl⟩, fun ⟨_, _, h, _⟩ ↦ h⟩
  have hdisj : Set.PairwiseDisjoint (Finset.range (J.card + 1) : Set ℕ) (fun w ↦ J.powersetCard w)
    := fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun A h1 h2 ↦ hne ((Finset.mem_powersetCard.mp
    h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2); rw [hpow_union, Finset.sum_biUnion hdisj,
    hJ_card]; refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hcongr :
      ∀ A ∈ J.powersetCard w, (((u A.card) ^ 2 : ℝ) : ℂ) * g A.card = (((u w) ^ 2 : ℝ) : ℂ) * g w :=
    fun A hA ↦ by rw [(Finset.mem_powersetCard.mp hA).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard, hJ_card,
    nsmul_eq_mul, ← mul_assoc]; push_cast; rfl
/-- Action of `wdDampVec` and `wdClickVec` on marked `P_R *ᵥ wdAmpState hp hm perm R u`. -/
private lemma wdDamp_and_click_marked_wdAmpState {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hInj : Set.InjOn (fun x ↦ subcubePref hp hm
  (perm x)) (R : Set (Fin (2 ^ n)))) (pyth : PythPair) (u : ℕ → ℝ) :
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    wdDampVec n m R.card pyth.cVal (P_R *ᵥ wdAmpState hp hm perm R u) = P_R *ᵥ wdAmpState hp hm perm
      R (wdDampAmp R.card pyth u) ∧ wdClickVec n m R.card pyth.sVal (P_R *ᵥ wdAmpState hp hm perm R
      u) = ((pyth.sVal * u R.card : ℝ) : ℂ) • (P_R *ᵥ wdBasisVec hp hm perm R (R.image fun x ↦
      subcubePref hp hm (perm x))) := by
  intro P_R; let J := R.image fun x ↦ subcubePref hp hm (perm x)
  have hJ_card : J.card = R.card := Finset.card_image_of_injOn hInj; constructor
  · funext o; dsimp only [wdDampVec, P_R]; rw [permUnitary_parallelMarkPerm_mulVec_apply_wd,
      permUnitary_parallelMarkPerm_mulVec_apply_wd]; unfold wdAmpState wdDampAmp
    by_cases hhit : wdHitCount n m o = R.card
    · rw [ite_eq_left hhit, Finset.mul_sum]; refine Finset.sum_congr rfl fun A hA ↦ ?_
      by_cases hnz : wdBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
      · simp [hnz]
      · have hcardA := (wdBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA) o
          hnz).2.2.2; have hAr : A.card = R.card := hcardA.symm.trans hhit; rw [ite_eq_left hAr];
          push_cast; ring
    · rw [ite_eq_right hhit]; refine Finset.sum_congr rfl fun A hA ↦ ?_
      by_cases hnz : wdBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
      · simp [hnz]
      · have hcardA := (wdBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA) o
          hnz).2.2.2; have hAne : A.card ≠ R.card := fun h ↦ hhit (hcardA.trans h); rw [ite_eq_right
          hAne]
  · funext o; dsimp only [wdClickVec, P_R, Pi.smul_apply, smul_eq_mul]
    rw [permUnitary_parallelMarkPerm_mulVec_apply_wd, permUnitary_parallelMarkPerm_mulVec_apply_wd]
    unfold wdAmpState; by_cases hhit : wdHitCount n m o = R.card
    · rw [ite_eq_left hhit, Finset.mul_sum, Finset.sum_eq_single J (fun A hA hne ↦ ?_) (fun hnot ↦
        absurd (Finset.mem_powerset_self J) hnot)]
      · rw [hJ_card]; push_cast; ring
      · by_cases hnz : wdBasisVec hp hm perm R A (parallelMarkPerm n m R o) = 0
        · simp [hnz]
        · have hcardA := (wdBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp hA) o
            hnz).2.2.2; have hAJ : A = J := Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp
            hA) (by rw [hJ_card, ← hhit, hcardA]); exact absurd hAJ hne
    · rw [ite_eq_right hhit]; symm; by_cases hnz : wdBasisVec hp hm perm R J (parallelMarkPerm n m R
        o) = 0
      · dsimp only [J] at hnz; rw [hnz, mul_zero]
      · have hcardJ := (wdBasisVec_support_props hp hm perm R Finset.Subset.rfl o hnz).2.2.2
        exact absurd (hcardJ.trans hJ_card) hhit
/-- On any collision (`¬ Set.InjOn pref R`), every nonzero configuration of the 1-Tap
  product
  state has `< R.card` marked hits, so `wdClickVec = 0` and `wdDampVec` acts as the
  identity. -/
private lemma wdHitCount_lt_of_not_injOn {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hNotInj : ¬ Set.InjOn (fun x ↦ subcubePref
  hp hm (perm x)) (R : Set (Fin (2 ^ n)))) (t : ℕ) (o : Fin (2 ^ (m * (n + 1)))) (hamp : wdProdState
  (fun j ↦ wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) t))
  (parallelMarkPerm n m R o) ≠ 0) : wdHitCount n m o < R.card := by
  let hbg1 : m * 1 = m := Nat.mul_one m; let pref := fun x ↦ subcubePref hp hm (perm x)
  have hslot_nz (j : Fin m) : wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm
    (R.image perm) j) t) ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o)) ≠ 0 := fun h0 ↦
    hamp (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  rcases groupHits_eq_filterMap_of_wdSlotWrap hp hm perm R _ o hslot_nz with ⟨hhit_sub, hgh_eq⟩
  have hnodup := nodup_groupHits hbg1 o; have hlen_eq : wdHitCount n m o = (groupHits hbg1
    o).toFinset.card := (by unfold wdHitCount; exact (List.toFinset_card_of_nodup hnodup).symm)
  have hinj_hits : Set.InjOn pref ((groupHits hbg1 o).toFinset : Set (Fin (2 ^ n))) := by
    intro x₁ hx₁ x₂ hx₂ hpref_eq; have hx₁_l : x₁ ∈ groupHits hbg1 o := List.mem_toFinset.mp hx₁
    have hx₂_l : x₂ ∈ groupHits hbg1 o := List.mem_toFinset.mp hx₂; rw [hgh_eq] at hx₁_l hx₂_l
    rcases List.mem_filterMap.mp hx₁_l with ⟨j₁, _, hj₁⟩; rcases List.mem_filterMap.mp hx₂_l with
      ⟨j₂, _, hj₂⟩; have hp₁ := (hhit_sub j₁ x₁ hj₁).2; have hp₂ := (hhit_sub j₂ x₂ hj₂).2
    have hjeq : j₁ = j₂ := hp₁.symm.trans (hpref_eq.trans hp₂); subst hjeq
    exact Option.some.inj (hj₁.symm.trans hj₂)
  have himg_sub : (groupHits hbg1 o).toFinset.image pref ⊆ R.image pref := by
    intro j hj; rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩; have hx_l : x ∈ groupHits hbg1 o :=
      List.mem_toFinset.mp hx; rw [hgh_eq] at hx_l; rcases List.mem_filterMap.mp hx_l with ⟨j', _,
      hj'⟩; exact Finset.mem_image_of_mem pref (hhit_sub j' x hj').1
  have hcard_le : (groupHits hbg1 o).toFinset.card ≤ (R.image pref).card :=
    (by rw [← Finset.card_image_of_injOn hinj_hits]; exact Finset.card_le_card himg_sub)
  have himg_lt : (R.image pref).card < R.card := lt_of_le_of_ne Finset.card_image_le fun heq ↦
    hNotInj (Finset.injOn_of_card_image_eq heq); omega
/- ## Section 5a: `ScaledCostRel`, `quadForm`, and Multi-Pulse Circuit Semantics -/
private lemma wd_constAssertion_mono {Var : Type} {d : ℕ} {α₁ α₂ : ℝ}
    (h0 : 0 ≤ α₁) (h1 : α₂ ≤ 1) (h : α₁ ≤ α₂) :
    (constAssertion α₁ : CQAssertion (Store Var) d) ≤ constAssertion α₂ := fun σ ↦ by
  apply Subtype.coe_le_coe.mp
  rw [constAssertion_apply_of_bounds α₁ h0 (h.trans h1),
    constAssertion_apply_of_bounds α₂ (h0.trans h) h1]
  exact smul_le_smul_of_nonneg_right h (by simp)
private lemma wd_wp_constAssertion_le {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] (P : QProg
  Var d) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : wp P (constAssertion α) ≤ constAssertion α := by
  induction P with
  | «skip» => exact le_rfl | «abort» => exact bot_le | assign _ _ => exact fun _ ↦ le_rfl
  | qMeasure x ℳ =>
    intro σ; apply Subtype.coe_le_coe.mp; rw [wp_qMeasure, CQAssertion.qMeasure_coe,
      constAssertion_apply_of_bounds α hα0 hα1]
    have hsum : (∑ o : Fin _, HermitianMat.conj (ℳ.1 o)ᴴ (((constAssertion α : CQAssertion (Store
      Var) d)
      (σ.subst x ↑o.1)).1)) = α • ∑ o : Fin _, HermitianMat.conj (ℳ.1 o)ᴴ 1 := by
      rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun o _ ↦ ?_
      rw [constAssertion_apply_of_bounds α hα0 hα1]; apply HermitianMat.ext
      simp [HermitianMat.conj_apply_mat]
    rw [hsum]; exact smul_le_smul_of_nonneg_left (ℳ.sum_conj_le_one fun _ ↦ le_rfl) hα0
  | qSet =>
    intro σ; apply Subtype.coe_le_coe.mp; rw [wp_qSet, constAssertion_apply_of_bounds α hα0 hα1]
    have h00 : ((constAssertion α : CQAssertion (Store Var) d) σ).1.1 0 0 = (α : ℂ) :=
      (by rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1]; simp)
    refine le_of_eq ?_; apply HermitianMat.ext; rw [← HermitianMat.val_eq_coe,
      qhlQSet_val, h00]; simp [HermitianMat.mat_smul, HermitianMat.mat_one]
  | qAssign U =>
    intro σ; apply Subtype.coe_le_coe.mp; refine le_of_eq ?_; apply HermitianMat.ext
    have hmat : ∀ τ : Store Var, ((constAssertion α : CQAssertion (Store Var) d) τ).1.1 = (α : ℂ) •
      (1 :
      Matrix (Fin d) (Fin d) ℂ) := fun τ ↦ by
      rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1, HermitianMat.mat_smul,
        HermitianMat.mat_one]; ext i j; simp [Complex.real_smul]
    rw [wp_qAssign, ← HermitianMat.val_eq_coe, qhlQAssign_val, hmat σ, ←
      HermitianMat.val_eq_coe, hmat σ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ←
      Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp U.2]
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
    intro σ; rw [wp_qWhile]; exact OmegaCompletePartialOrder.ωSup_le (whileRecWP.chain (wp c)
      (wp_mono c) b (constAssertion α)) (constAssertion α) hrec σ
private lemma wd_expect_constAssertion {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) {α : ℝ} (hα0
    : 0 ≤
  α) (hα1 : α ≤ 1) : 𝔼[Δ, constAssertion α] = α * Δ.trace := by
  rw [expect_eq_mul_of_apply_eq_smul Δ (Ψ := ⊤) α (fun σ ↦ by
    rw [constAssertion_apply_of_bounds α hα0 hα1]
    rfl), expect_top]
private lemma wd_expect_nonneg {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) (θ : CQAssertion
    (Store Var) d) : 0
  ≤ 𝔼[Δ, θ] := by simpa using expect_mono (le_rfl : Δ ≤ Δ) (bot_le : ⊥ ≤ θ)
/-- Exact state-dependent cost-observable certificate normalized by `B > 0`: bounds
  `expectedCost model P Δ` by `ENNReal.ofReal (B * 𝔼[Δ, θ])` with `θ ≤ constAssertion (c /
  B)`. -/
abbrev ScaledCostRel {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (model : CostModel d) (B : ℝ) (P : QProg Var d) (θ : CQAssertion (Store Var) d) (c : ℝ) : Prop
      :=
  0 ≤ c ∧ c ≤ B ∧ θ ≤ constAssertion (c / B) ∧
    ∀ Δ : CQState (Store Var) d, expectedCost model P Δ ≤ ENNReal.ofReal (B * 𝔼[Δ, θ])
private lemma ScaledCostRel.of_zero {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d} (hP : CostBound (Var := Var) model P 0) :
  ScaledCostRel model B P ⊥ 0 := by
  refine ⟨le_rfl, hB.le, bot_le, fun Δ ↦ ?_⟩; have h0 := hP Δ; simp only [ENNReal.coe_zero,
    mul_zero, nonpos_iff_eq_zero] at h0; simp [h0]
private lemma ScaledCostRel.of_costBound {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d} {k_cost : ℝ≥0} (hP : CostBound (Var := Var)
  model P k_cost) (hkB : (k_cost : ℝ) ≤ B) : ScaledCostRel model B P (constAssertion ((k_cost : ℝ) /
  B)) (k_cost : ℝ) := by
  have hc0 : 0 ≤ (k_cost : ℝ) := NNReal.coe_nonneg k_cost; have hdiv0 : 0 ≤ (k_cost : ℝ) / B :=
    div_nonneg hc0 hB.le; have hdiv1 : (k_cost : ℝ) / B ≤ 1 := (div_le_one hB).mpr hkB; refine ⟨hc0,
    hkB, le_rfl, fun Δ ↦ (hP Δ).trans ?_⟩; rw [wd_expect_constAssertion Δ hdiv0 hdiv1, ← mul_assoc,
    mul_div_cancel₀ _ hB.ne', mul_comm (k_cost : ℝ) Δ.trace, ENNReal.ofReal_mul Δ.trace_nonneg, ←
    stateMass_eq_ofReal_trace, ENNReal.ofReal_coe_nnreal]
private lemma ScaledCostRel.qIf {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model : CostModel
  d} {B : ℝ} (hB : 0 < B) (b : Store Var → Prop) [DecidablePred b] {P₁ P₂ : QProg Var d} {θ₁ θ₂ :
  CQAssertion (Store Var) d} {c₁ c₂ : ℝ} (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel
    model B
  P₂ θ₂ c₂) : ScaledCostRel model B (.qIf b P₁ P₂) (fun σ ↦ if b σ then θ₁ σ else θ₂ σ) (max c₁ c₂)
  := by
  refine ⟨le_max_of_le_left h₁.1, max_le h₁.2.1 h₂.2.1, fun σ ↦ ?_, fun Δ ↦ ?_⟩
  · dsimp only; split_ifs
    · exact (h₁.2.2.1 σ).trans (wd_constAssertion_mono (div_nonneg h₁.1 hB.le) ((div_le_one hB).mpr
        (max_le h₁.2.1 h₂.2.1)) (div_le_div_of_nonneg_right (le_max_left c₁ c₂) hB.le) σ)
    · exact (h₂.2.2.1 σ).trans (wd_constAssertion_mono (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr
        (max_le h₁.2.1 h₂.2.1)) (div_le_div_of_nonneg_right (le_max_right c₁ c₂) hB.le) σ)
  · simp only [expectedCost]
    have hnn1 : 0 ≤ B * 𝔼[Δ.wdTrueSt b, θ₁] := mul_nonneg hB.le (wd_expect_nonneg _ _)
    have hnn2 : 0 ≤ B * 𝔼[Δ.wdFalseSt b, θ₂] := mul_nonneg hB.le (wd_expect_nonneg _ _)
    calc expectedCost model P₁ (Δ.wdTrueSt b) + expectedCost model P₂ (Δ.wdFalseSt b)
        ≤ ENNReal.ofReal (B * 𝔼[Δ.wdTrueSt b, θ₁]) + ENNReal.ofReal (B * 𝔼[Δ.wdFalseSt b, θ₂]) :=
          add_le_add (h₁.2.2.2 _) (h₂.2.2.2 _)
      _ = ENNReal.ofReal (B * 𝔼[Δ, fun σ ↦ if b σ then θ₁ σ else θ₂ σ]) := by
          rw [← ENNReal.ofReal_add hnn1 hnn2, ← mul_add, ← wdExpectItePartition]
private theorem scaledCostRel_add_le {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) {P₁ P₂ : QProg Var d} {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁ c₂
    : ℝ}
  (h₁ : ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel model B P₂ θ₂ c₂) (hc_sum : c₁ + c₂ ≤ B)
  (σ : Store Var) : (θ₁ σ).1 + ((wp P₁ θ₂) σ).1 ≤ 1 := by
  have h_wp_le : wp P₁ θ₂ ≤ constAssertion (c₂ / B) := (wp_mono P₁ h₂.2.2.1).trans
    (wd_wp_constAssertion_le P₁ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1))
  have ha : (θ₁ σ).1 ≤ (c₁ / B) • 1 := by
    have h := Subtype.coe_le_coe.mpr (h₁.2.2.1 σ)
    rwa [constAssertion_apply_of_bounds _ (div_nonneg h₁.1 hB.le) ((div_le_one hB).mpr h₁.2.1)] at h
  have hb : ((wp P₁ θ₂) σ).1 ≤ (c₂ / B) • 1 := by
    have h := Subtype.coe_le_coe.mpr (h_wp_le σ)
    rwa [constAssertion_apply_of_bounds _ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1)] at h
  calc (θ₁ σ).1 + ((wp P₁ θ₂) σ).1 ≤ (c₁ / B) • 1 + (c₂ / B) • 1 := add_le_add ha hb
    _ = ((c₁ + c₂) / B) • 1 := by rw [add_div, add_smul]
    _ ≤ (1 : ℝ) • (1 : HermitianMat (Fin d) ℂ) :=
        smul_le_smul_of_nonneg_right ((div_le_one hB).mpr hc_sum) (by simp)
    _ = 1 := one_smul _ _
private lemma ScaledCostRel.seq {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model : CostModel
  d} {B : ℝ} (hB : 0 < B) {P₁ P₂ : QProg Var d} {θ₁ θ₂ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ} (h₁
    :
  ScaledCostRel model B P₁ θ₁ c₁) (h₂ : ScaledCostRel model B P₂ θ₂ c₂) (hc_sum : c₁ + c₂ ≤ B) :
  ScaledCostRel model B (P₁ ;; P₂) (θ₁.add (wp P₁ θ₂) (scaledCostRel_add_le hB h₁ h₂ hc_sum)) (c₁ +
  c₂) := by
  have h_wp_le : wp P₁ θ₂ ≤ constAssertion (c₂ / B) := (wp_mono P₁ h₂.2.2.1).trans
    (wd_wp_constAssertion_le P₁ (div_nonneg h₂.1 hB.le) ((div_le_one hB).mpr h₂.2.1))
  refine ⟨add_nonneg h₁.1 h₂.1, hc_sum, fun σ ↦ ?_, fun Δ ↦ ?_⟩
  · apply Subtype.coe_le_coe.mp; rw [CQAssertion.add_apply, Observable.add_coe,
      constAssertion_apply_of_bounds _ (div_nonneg (add_nonneg h₁.1 h₂.1) hB.le) ((div_le_one
      hB).mpr hc_sum)]
    have ha : (θ₁ σ).1 ≤ (c₁ / B) • 1 := by
      have h := Subtype.coe_le_coe.mpr (h₁.2.2.1 σ)
      rwa [constAssertion_apply_of_bounds _ (div_nonneg h₁.1 hB.le)
        ((div_le_one hB).mpr h₁.2.1)] at h
    have hb : ((wp P₁ θ₂) σ).1 ≤ (c₂ / B) • 1 := by
      have h := Subtype.coe_le_coe.mpr (h_wp_le σ)
      rwa [constAssertion_apply_of_bounds _ (div_nonneg h₂.1 hB.le)
        ((div_le_one hB).mpr h₂.2.1)] at h
    calc (θ₁ σ).1 + ((wp P₁ θ₂) σ).1 ≤ (c₁ / B) • 1 + (c₂ / B) • 1 := add_le_add ha hb
      _ = ((c₁ + c₂) / B) • 1 := by rw [add_div, add_smul]
  · rw [expectedCost_qSeq]; have hnn1 : 0 ≤ B * 𝔼[Δ, θ₁] := mul_nonneg hB.le (wd_expect_nonneg _ _)
    have hnn2 : 0 ≤ B * 𝔼[(interp P₁).toStateFun Δ, θ₂] := mul_nonneg hB.le (wd_expect_nonneg _ _)
    calc expectedCost model P₁ Δ + expectedCost model P₂ ((interp P₁).toStateFun Δ)
        ≤ ENNReal.ofReal (B * 𝔼[Δ, θ₁]) + ENNReal.ofReal (B * 𝔼[(interp P₁).toStateFun Δ, θ₂]) :=
          add_le_add (h₁.2.2.2 Δ) (h₂.2.2.2 _)
      _ = ENNReal.ofReal (B * 𝔼[Δ, θ₁.add (wp P₁ θ₂)
          (scaledCostRel_add_le hB h₁ h₂ hc_sum)]) := by
          rw [← ENNReal.ofReal_add hnn1 hnn2, ← wp_expectation_eq P₁ Δ θ₂, ← mul_add, ←
            expect_assertion_add]
private noncomputable def quadForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) : ℂ :=
  star v ⬝ᵥ (A *ᵥ v)
private lemma quadForm_single {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (idx : Fin d) : quadForm A
  (single idx 1) = A idx idx := (diag_eq_star_single_dotProduct_mulVec A idx).symm
private lemma quadForm_zero_vec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : quadForm A 0 = 0 := by
  simp [quadForm]
private lemma quadForm_zero_mat {d : ℕ} (v : Fin d → ℂ) : quadForm (0 : Matrix (Fin d) (Fin d) ℂ) v
  = 0 := by simp [quadForm]
private lemma quadForm_add_mat {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) : quadForm
  (A + B) v = quadForm A v + quadForm B v := by
  unfold quadForm; rw [Matrix.add_mulVec, dotProduct_add]
private lemma quadForm_smul_vec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (v : Fin d → ℂ) :
  quadForm A (c • v) = (normSq c : ℂ) * quadForm A v := by
  unfold quadForm; rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
private lemma quadForm_unitaryEffect {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {P : QProg
  Var d} {U : Matrix (Fin d) (Fin d) ℂ} (hU : UnitaryEffect P U) (Θ : CQAssertion (Store Var) d) (σ
    : Store
  Var) (v : Fin d → ℂ) : quadForm ((wp P Θ) σ).1.1 v = quadForm (Θ σ).1.1 (U *ᵥ v) := by
  unfold quadForm; rw [unitaryEffect_apply hU Θ σ, Matrix.mul_assoc, ← mulVec_mulVec, ←
    mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
private lemma quadForm_wp_measureRegister {Var : Type} [DecidableEq Var] {w q : ℕ} (res : Var) (reg
  : QRegister w q) (Θ : CQAssertion (Store Var) (2 ^ q)) (σ : Store Var) (v : Fin (2 ^ q) → ℂ) :
    quadForm
  ((wp (measureRegister res reg) Θ) σ).1.1 v = ∑ o : Fin (2 ^ w), quadForm (Θ (Store.subst σ res
  (Int.ofNat o.val))).1.1 (reg.basisOutcomeProjector o *ᵥ v) := by
  unfold quadForm; rw [wp_measureRegister, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  let A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ := (Θ (Store.subst σ res (Int.ofNat o.val))).1.1
  change star v ⬝ᵥ ((reg.basisOutcomeProjector o * A * reg.basisOutcomeProjector o) *ᵥ v) = star
    (reg.basisOutcomeProjector o *ᵥ v) ⬝ᵥ (A *ᵥ (reg.basisOutcomeProjector o *ᵥ v))
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_mulVec, ←
    QRegister.basisOutcomeProjector_conjTranspose, Matrix.vecMul_conjTranspose, star_star,
    QRegister.basisOutcomeProjector_conjTranspose]
/- ## Section 5b: Multi-Pulse `WeakDicke` Circuits, Subset DP, and Total Correctness -/
noncomputable def wdDeflatedGroverStep {Var : Type} {n p m k : ℕ}
    (hp : p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k active))
    (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
      (wdDiffuserUnitary (m := m) hp perm))))
noncomputable def wdDeflatedGroverLoop {Var : Type} {n p m k : ℕ}
    (hp : p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active steps : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  OracleDynamicCircuit.sequence (List.replicate steps (wdDeflatedGroverStep hp perm active))
noncomputable def wdPrepAndLoop {Var : Type} {n p m k : ℕ}
    (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n)))
    (active kInit : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  .seq (.step (phaseTag ((lowBlock W M).embedUnitary (wdPrepUnitary hp hm perm))))
    (.seq (wdDeflatedGroverLoop hp perm active kInit)
      (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active)))
noncomputable def wdNoClickStep {Var : Type} {n p m k : ℕ}
    (hp : p ≤ n) (perm : Equiv.Perm (Fin (2 ^ n))) (active kNext : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active))
    (.seq (wdDeflatedGroverLoop hp perm active kNext)
      (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active)))
noncomputable def wdReadoutWrite {Var : Type} (res : Var) {n m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (active : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let hbg1 : m * 1 = m := Nat.mul_one m
  .seq (.step (phaseTag (permutationUnitary (memWriteBatchPerm active (groupHits hbg1)))))
    (setCountAndResetWork res (batchNextCount hm1 hkN hbg1 active))
noncomputable def wdClickCleanup {Var : Type} (res : Var) {n m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (active : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  .seq (.step (phaseTag ((topAncReg W M hM).embedUnitary (permutationUnitary (swap 0 1)))))
    (wdReadoutWrite res hm1 hkN active)
noncomputable def wdProbeChain {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n)
    (perm : Equiv.Perm (Fin (2 ^ n))) (active r : ℕ) :
    List (PythPair × ℕ) → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | [] => wdReadoutWrite res hm1 hkN active
  | (pyth, kNext) :: rest =>
      let W := m * (n + 1)
      let M := k * n
      .seq (.step (phaseTag (weakAllHitUnitary n m M hM r pyth)))
        (.seq (.measure res (topAncReg W M hM))
          (.qIf (fun σ ↦ σ res = 1)
            (wdClickCleanup res hm1 hkN hM active)
            (.seq (wdNoClickStep hp perm active kNext)
              (wdProbeChain res hm1 hkN hM hp perm active r rest))))
noncomputable def wdDeflatedRound {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n))) (active r kInit : ℕ)
    (probes : List (PythPair × ℕ)) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (wdPrepAndLoop hp hm perm active kInit)
    (wdProbeChain res hm1 hkN hM hp perm active r probes)
noncomputable def wdOptSweep {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (perm : Equiv.Perm (Fin (2 ^ n)))
    (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  dispFin res (fun s : Fin k ↦
    match sched (k - s.val) with
    | none => .skip
    | some (kInit, probes) =>
        wdDeflatedRound res hm1 hkN hM hp hm perm s.val (k - s.val) kInit probes) (finRange k)
noncomputable def wdSweeps {Var : Type} (res : Var) {n p m k : ℕ}
    (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → Option (ℕ × List (PythPair × ℕ)))) →
      OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | [] => .skip
  | (perm, sched) :: rest =>
      .seq (wdOptSweep res hm1 hkN hM hp hm perm sched)
        (wdSweeps res hm1 hkN hM hp hm rest)
private def IsWpTopWD {Var : Type} [DecidableEq Var] {Q O : ℕ}
    (C : OracleCirc Var Q O) : Prop :=
  ∀ oracle : Unitary (2 ^ O),
    wp (C.compile qAssign oracle) (⊤ : CQAssertion (Store Var) (2 ^ Q)) = ⊤
private lemma isWpTopWD_skip {Var : Type} [DecidableEq Var] {Q O : ℕ} :
    IsWpTopWD (.skip : OracleCirc Var Q O) := fun _ ↦ rfl
private lemma isWpTopWD_step {Var : Type} [DecidableEq Var] {Q O : ℕ} (U : Unitary (2 ^ Q)) :
    IsWpTopWD (.step U : OracleCirc Var Q O) := fun _ ↦ by
  funext σ
  simp [compile]
private lemma isWpTopWD_oracle {Var : Type} [DecidableEq Var] {Q O : ℕ} (r : QRegister O Q) :
    IsWpTopWD (.oracle r : OracleCirc Var Q O) := fun _ ↦ by
  funext σ
  simp [compile]
private lemma isWpTopWD_measure {Var : Type} [DecidableEq Var] {w Q O : ℕ}
    (x : Var) (r : QRegister w Q) :
    IsWpTopWD (.measure x r : OracleCirc Var Q O) := fun oracle ↦ by
  funext σ
  apply Subtype.ext; apply HermitianMat.ext
  dsimp only [compile]; rw [← HermitianMat.val_eq_coe, wp_measureRegister]
  have hidem (o : Fin (2 ^ w)) :
      r.basisOutcomeProjector o *
          ((⊤ : CQAssertion (Store Var) (2 ^ Q)) (Store.subst σ x (Int.ofNat o.val))).1.1 *
          r.basisOutcomeProjector o =
        r.basisOutcomeProjector o := by
    change r.basisOutcomeProjector o * (1 : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) *
      r.basisOutcomeProjector o = _; rw [Matrix.mul_one,
      QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]; ext z₁ z₂
    by_cases hz : z₁ = z₂
    · subst hz; by_cases h : r.extractIndex z₁ = o <;> simp [h]
    · simp [hz]
  simp_rw [hidem]; exact r.sum_basisOutcomeProjector
private lemma isWpTopWD_seq {Var : Type} [DecidableEq Var] {Q O : ℕ}
    {c₁ c₂ : OracleCirc Var Q O} (h₁ : IsWpTopWD c₁) (h₂ : IsWpTopWD c₂) :
    IsWpTopWD (.seq c₁ c₂) := fun oracle ↦ by
  dsimp only [compile]; rw [wp_qSeq, h₂ oracle, h₁ oracle]
private lemma isWpTopWD_qIf {Var : Type} [DecidableEq Var] {Q O : ℕ}
    (b : Store Var → Prop) [DecidablePred b]
    {c₁ c₂ : OracleCirc Var Q O} (h₁ : IsWpTopWD c₁) (h₂ : IsWpTopWD c₂) :
    IsWpTopWD (.qIf b c₁ c₂) := fun oracle ↦ by
  funext σ
  dsimp only [compile]; rw [wp_qIf]; dsimp only
  split_ifs <;> simp [h₁ oracle, h₂ oracle]
private lemma isWpTopWD_dispFin {Var : Type} [DecidableEq Var] {n_fin Q O : ℕ} (res : Var) (br : Fin
  n_fin → OracleCirc Var Q O) (l : List (Fin n_fin)) (hbr : ∀ a ∈ l, IsWpTopWD (br a)) : IsWpTopWD
  (dispFin res br l) := by
  induction l with
  | nil => exact isWpTopWD_skip
  | cons a rest ih =>
    exact isWpTopWD_qIf _ (hbr a List.mem_cons_self) (ih fun x hx ↦ hbr x (List.mem_cons_of_mem a
      hx))
private lemma isWpTopWD_sequence {Var : Type} [DecidableEq Var] {Q O : ℕ} (l : List (OracleCirc Var
  Q O)) (hl : ∀ c ∈ l, IsWpTopWD c) : IsWpTopWD (OracleDynamicCircuit.sequence l) := by
  induction l with
  | nil => exact isWpTopWD_skip
  | cons c rest ih =>
    rw [OracleDynamicCircuit.sequence_cons]; exact isWpTopWD_seq (hl c List.mem_cons_self) (ih fun x
      hx ↦ hl x (List.mem_cons_of_mem c hx))
private lemma isWpTopWD_setCountAndResetWork {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ W) → Fin (2 ^ W)) :
    IsWpTopWD (setCountAndResetWork (Var := Var) (M := M) (O := O) res g) := fun oracle ↦ by
  funext σ
  apply Subtype.ext; apply HermitianMat.ext; rw [← HermitianMat.val_eq_coe, wp_setCountAndResetWork]
  have hterm (o : Fin (2 ^ W)) :
      ((lowBlock W M).embedMatrix (Matrix.single 0 o 1))ᴴ *
        ((⊤ : CQAssertion (Store Var) (2 ^ (W + M))) (Store.subst σ res (Int.ofNat (g o).val))).1.1
          *
        (lowBlock W M).embedMatrix (Matrix.single 0 o 1) =
      (lowBlock W M).basisOutcomeProjector o := by
    change ((lowBlock W M).embedMatrix (Matrix.single 0 o 1))ᴴ * 1 * (lowBlock W M).embedMatrix
      (Matrix.single 0 o 1) = _; rw [Matrix.mul_one, ← QRegister.embedMatrix_conjTranspose, ←
      QRegister.embedMatrix_mul]
    have hsing : (Matrix.single (0 : Fin (2 ^ W)) o (1 : ℂ))ᴴ * Matrix.single 0 o 1 = compProj o
      := by
      ext i j; rw [Matrix.mul_apply, compProj, Fintype.sum_eq_single (0 : Fin (2 ^ W)) (fun x hx ↦
        by simp [hx.symm])]; simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
      by_cases hi : o = i
      · subst hi; by_cases hj : o = j
        · subst hj; simp
        · simp [hj]
      · simp [hi]
    rw [hsing, QRegister.basisOutcomeProjector]
  simp_rw [hterm]; exact (lowBlock W M).sum_basisOutcomeProjector
lemma wp_top_wdSweeps {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hm1 : 1 ≤ m) (hkN :
  k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (passes : List (Equiv.Perm (Fin (2 ^ n))
  × (ℕ → Option (ℕ × List (PythPair × ℕ))))) (oracle : Unitary (2 ^ ((n + 1) * m))) : wp ((wdSweeps
  res hm1 hkN hM hp hm passes).compile qAssign oracle) (⊤ : CQAssertion (Store Var) (2 ^ (m * (n +
    1) + k *
  n))) = ⊤ := by
  have hrw (active : ℕ) : IsWpTopWD (wdReadoutWrite (Var := Var) res hm1 hkN active) :=
    isWpTopWD_seq (isWpTopWD_step _) (isWpTopWD_setCountAndResetWork res _)
  have hread (active : ℕ) : IsWpTopWD (deflatedOracle (Var := Var) (n := n) (m := m) (k := k) le_rfl
    (memPrefix k active)) := isWpTopWD_seq (isWpTopWD_oracle _) (isWpTopWD_step _)
  have hloop (perm : Equiv.Perm (Fin (2 ^ n))) (active steps : ℕ) : IsWpTopWD (wdDeflatedGroverLoop
    (Var := Var) (m := m) (k := k) hp perm active steps) := isWpTopWD_sequence _ fun c hc ↦ by
      rw [List.mem_replicate] at hc; rcases hc with ⟨_, rfl⟩; exact isWpTopWD_seq (isWpTopWD_seq
        (isWpTopWD_step _) (isWpTopWD_seq (hread active) (isWpTopWD_step _))) (isWpTopWD_step _)
  have hchain (perm : Equiv.Perm (Fin (2 ^ n))) (active r : ℕ) : ∀ probes, IsWpTopWD (wdProbeChain
    (Var := Var) res hm1 hkN hM hp perm active r probes) := by
    intro probes
    induction probes with
    | nil => exact hrw active
    | cons pk rest ih =>
      exact isWpTopWD_seq (isWpTopWD_step _) (isWpTopWD_seq (isWpTopWD_measure _ _) (isWpTopWD_qIf _
        (isWpTopWD_seq (isWpTopWD_step _) (hrw active)) (isWpTopWD_seq (isWpTopWD_seq (hread active)
        (isWpTopWD_seq (hloop perm active pk.2) (hread active))) ih)))
  have hsweeps : IsWpTopWD (wdSweeps (Var := Var) res hm1 hkN hM hp hm passes) := by
    induction passes with
    | nil => exact isWpTopWD_skip
    | cons ps rest ih =>
      refine isWpTopWD_seq (isWpTopWD_dispFin res _ _ fun s _ ↦ ?_) ih
      cases ps.2 (k - s.val) with
      | none => exact isWpTopWD_skip
      | some kp =>
        exact isWpTopWD_seq (isWpTopWD_seq (isWpTopWD_step _) (isWpTopWD_seq (hloop ps.1 s.val kp.1)
          (hread s.val))) (hchain ps.1 s.val _ kp.2)
  exact hsweeps oracle
noncomputable def wdChainClickProb (r : ℕ) (θ₁ : ℝ) :
    List (PythPair × ℕ) → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | (pyth, kNext) :: rest, u =>
      (pyth.sVal * u r) ^ 2 +
        wdChainClickProb r θ₁ rest
          (dickeStep r (Real.cos (2 * (kNext : ℝ) * θ₁))
            (Real.sin (2 * (kNext : ℝ) * θ₁)) (wdDampAmp r pyth u))
noncomputable def wdSubsetStep {α : Type*} [DecidableEq α] {m : ℕ}
    (subN : ℕ) (pref : α → Fin m) (withCost : Bool)
    (sched : ℕ → Option (ℕ × List (PythPair × ℕ)))
    (Ψ : Finset α → ℝ) (R : Finset α) : ℝ :=
  open Classical in
  if R.card = 0 then Ψ R
  else
    match sched R.card with
    | none => Ψ R
    | some (kInit, probes) =>
        if Set.InjOn pref (R : Set α) then
          let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
          let u₀ := wdInitAmp R.card θ₁ kInit
          let uf := wdChainFinalAmp R.card θ₁ probes u₀
          (if withCost then
              ((kInit + 1 : ℕ) : ℝ) + wdChainExtraQueries R.card θ₁ probes u₀
            else 0) +
            wdChainClickProb R.card θ₁ probes u₀ * Ψ ∅ +
            ∑ B ∈ R.powerset, (uf B.card) ^ 2 * Ψ (R \ B)
        else
          let kTot := wdTotalSteps kInit probes
          (if withCost then (wdMaxQueries kInit probes : ℝ) else 0) +
            ∑ hit ∈ rotHitSupport pref R,
              (∏ j : Fin m,
                rotSlotHitProb (2 ^ subN) kTot (R.filter fun x ↦ pref x = j) (hit j)) *
                Ψ (R \ rotHitFinset hit)
noncomputable def wdCircDP {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p)
    (withCost : Bool) :
    List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → Option (ℕ × List (PythPair × ℕ)))) →
      (Finset (Fin (2 ^ n)) → ℝ) → Finset (Fin (2 ^ n)) → ℝ
  | [], Ψ, R => Ψ R
  | (perm, sched) :: rest, Ψ, R =>
      wdSubsetStep (n - p) (fun x ↦ subcubePref hp hm (perm x)) withCost sched
        (wdCircDP hp hm withCost rest Ψ) R
private lemma wdChainClickProb_nonneg (r : ℕ) (θ₁ : ℝ) : ∀ (probes : List (PythPair × ℕ)) (u : ℕ →
  ℝ), 0 ≤ wdChainClickProb r θ₁ probes u
  | [], _ => le_rfl | _ :: rest, _ => add_nonneg (sq_nonneg _) (wdChainClickProb_nonneg r θ₁ rest _)
private lemma wdChainExtraQueries_nonneg (r : ℕ) (θ₁ : ℝ) : ∀ (probes : List (PythPair × ℕ)) (u : ℕ
  → ℝ), 0 ≤ wdChainExtraQueries r θ₁ probes u
  | [], _ => le_rfl
  | _ :: rest, _ =>
    add_nonneg
      (mul_nonneg
        (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (Nat.cast_nonneg _))
      (wdChainExtraQueries_nonneg r θ₁ rest _)
lemma wdSubsetStep_nonneg {α : Type*} [DecidableEq α] {m : ℕ} (subN : ℕ) (pref : α → Fin m)
  (withCost : Bool) (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) {Ψ : Finset α → ℝ} {R : Finset α}
  (hΨ : ∀ R' ⊆ R, 0 ≤ Ψ R') : 0 ≤ wdSubsetStep subN pref withCost sched Ψ R := by
  classical
  unfold wdSubsetStep; by_cases hr0 : R.card = 0
  · rw [ite_eq_left hr0]; exact hΨ R Finset.Subset.rfl
  · rw [ite_eq_right hr0]
    cases sched R.card with
    | none => exact hΨ R Finset.Subset.rfl
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; dsimp only; by_cases hInj : Set.InjOn pref (R : Set α)
      · rw [ite_eq_left hInj]; refine add_nonneg (add_nonneg ?_ ?_) ?_
        · cases withCost
          · simp
          · simp only [↓reduceIte]; exact add_nonneg (Nat.cast_nonneg _) (wdChainExtraQueries_nonneg
              _ _ _ _)
        · exact mul_nonneg (wdChainClickProb_nonneg _ _ _ _) (hΨ ∅ (Finset.empty_subset R))
        · exact Finset.sum_nonneg fun B _ ↦ mul_nonneg (sq_nonneg _) (hΨ (R \ B)
            Finset.sdiff_subset)
      · rw [ite_eq_right hInj]; refine add_nonneg ?_ ?_
        · cases withCost <;> simp
        · exact Finset.sum_nonneg fun hit _ ↦ mul_nonneg (Finset.prod_nonneg fun j _ ↦
            rotSlotHitProb_nonneg _ _ _ (hit j)) (hΨ (R \ rotHitFinset hit) Finset.sdiff_subset)
lemma wdCircDP_false_mul {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (passes : List (Equiv.Perm (Fin
  (2 ^ n)) × (ℕ → Option (ℕ × List (PythPair × ℕ))))) (c : ℝ) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (R :
  Finset (Fin (2 ^ n))) : wdCircDP hp hm false passes (fun R' ↦ c * Ψ R') R = c * wdCircDP hp hm
  false passes Ψ R := by
  have hstep_mul {pref : Fin (2 ^ n) → Fin m} {sched : ℕ → Option (ℕ × List (PythPair × ℕ))} (Ψ₀ :
    Finset (Fin (2 ^ n)) → ℝ) (R₀ : Finset (Fin (2 ^ n))) : wdSubsetStep (n - p) pref false sched
    (fun R' ↦ c * Ψ₀ R') R₀ = c * wdSubsetStep (n - p) pref false sched Ψ₀ R₀ := by
    classical
    unfold wdSubsetStep; by_cases hr0 : R₀.card = 0
    · rw [ite_eq_left hr0, ite_eq_left hr0]
    · rw [ite_eq_right hr0, ite_eq_right hr0]
      cases sched R₀.card with
      | none => rfl
      | some kp =>
        rcases kp with ⟨kInit, probes⟩; simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        by_cases hInj : Set.InjOn pref (R₀ : Set (Fin (2 ^ n)))
        · rw [ite_eq_left hInj, ite_eq_left hInj]; simp_rw [← mul_assoc, mul_comm _ c, mul_assoc]
          rw [← Finset.mul_sum, ← mul_add]
        · rw [ite_eq_right hInj, ite_eq_right hInj]; simp_rw [← mul_assoc, mul_comm _ c, mul_assoc]
          rw [← Finset.mul_sum]
  induction passes generalizing R with
  | nil => rfl
  | cons ps rest ih =>
    dsimp only [wdCircDP]; have heq : (wdCircDP hp hm false rest fun R' ↦ c * Ψ R') = fun R' ↦ c *
      wdCircDP hp hm false rest Ψ R' := funext ih; rw [heq, hstep_mul]
lemma wdCircDP_false_sum {ι : Type*} {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (passes : List
  (Equiv.Perm (Fin (2 ^ n)) × (ℕ → Option (ℕ × List (PythPair × ℕ))))) (s : Finset ι) (F : ι →
  Finset (Fin (2 ^ n)) → ℝ) (R : Finset (Fin (2 ^ n))) : wdCircDP hp hm false passes (fun R' ↦ ∑ i ∈
  s, F i R') R = ∑ i ∈ s, wdCircDP hp hm false passes (F i) R := by
  have hstep_sum {pref : Fin (2 ^ n) → Fin m} {sched : ℕ → Option (ℕ × List (PythPair × ℕ))} (F₀ : ι
    → Finset (Fin (2 ^ n)) → ℝ) (R₀ : Finset (Fin (2 ^ n))) : wdSubsetStep (n - p) pref false sched
    (fun R' ↦ ∑ i ∈ s, F₀ i R') R₀ = ∑ i ∈ s, wdSubsetStep (n - p) pref false sched (F₀ i) R₀ := by
    classical
    conv_lhs => unfold wdSubsetStep
    by_cases hr0 : R₀.card = 0
    · rw [ite_eq_left hr0]; refine Finset.sum_congr rfl fun i _ ↦ ?_
      unfold wdSubsetStep; exact (ite_eq_left hr0).symm
    · rw [ite_eq_right hr0]; have hrhs_r0 : ∀ i, wdSubsetStep (n - p) pref false sched (F₀ i) R₀ =
            match sched R₀.card with
            | none => F₀ i R₀
            | some (kInit, probes) =>
                if Set.InjOn pref (R₀ : Set (Fin (2 ^ n))) then
                  let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
                  let u₀ := wdInitAmp R₀.card θ₁ kInit
                  let uf := wdChainFinalAmp R₀.card θ₁ probes u₀
                  wdChainClickProb R₀.card θ₁ probes u₀ * F₀ i ∅ +
                    ∑ B ∈ R₀.powerset, (uf B.card) ^ 2 * F₀ i (R₀ \ B)
                else
                  let kTot := wdTotalSteps kInit probes
                  ∑ hit ∈ rotHitSupport pref R₀, (∏ j : Fin m,
                      rotSlotHitProb (2 ^ (n - p)) kTot (R₀.filter fun x ↦ pref x = j) (hit j)) *
                      F₀ i (R₀ \ rotHitFinset hit) := by
        intro i; unfold wdSubsetStep; rw [ite_eq_right hr0]
        cases sched R₀.card with
        | none => rfl
        | some kp =>
          rcases kp with ⟨kInit, probes⟩; simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      simp_rw [hrhs_r0]
      cases sched R₀.card with
      | none => rfl
      | some kp =>
        rcases kp with ⟨kInit, probes⟩; simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        by_cases hInj : Set.InjOn pref (R₀ : Set (Fin (2 ^ n)))
        · simp_rw [ite_eq_left hInj, Finset.mul_sum]; rw [Finset.sum_comm (s := R₀.powerset), ←
            Finset.sum_add_distrib]
        · simp_rw [ite_eq_right hInj, Finset.mul_sum]; rw [Finset.sum_comm]
  induction passes generalizing R with
  | nil => rfl
  | cons ps rest ih =>
    dsimp only [wdCircDP]
    have heq : (wdCircDP hp hm false rest fun R' ↦ ∑ i ∈ s, F i R') = fun R' ↦ ∑ i ∈ s, wdCircDP hp
      hm false rest (F i) R' := funext ih; rw [heq, hstep_sum]
private lemma memSeen_writeMemBatch_wd {n k active : ℕ} {S : Finset (Fin (2 ^ n))} {μ : Fin (2 ^ (k
  * n))} (hval : MemPrefixValid S active μ) (L : List (Fin (2 ^ n))) (hlen : active + L.length ≤ k)
  : memSeen n k (memPrefix k (active + L.length)) (writeMemBatch active L μ) = memSeen n k
  (memPrefix k active) μ ∪ L.toFinset := by
  have hslot_lt (i : Fin k) (hi : i.val < active) : addrEquiv n k (writeMemBatch active L μ) i =
    addrEquiv n k μ i := by
    unfold writeMemBatch; rw [Equiv.apply_symm_apply, Pi.add_apply, ite_eq_right (not_le_of_gt hi),
      add_zero]
  have hslot_ge (i : Fin k) (hge : active ≤ i.val) (hlt : i.val < active + L.length) : addrEquiv n k
    (writeMemBatch active L μ) i = L[i.val - active]'(by omega) := by
    unfold writeMemBatch; have hzero : addrEquiv n k μ i = 0 := hval.2.2.2 i hge
    have hsub : i.val - active < L.length := (by omega); rw [Equiv.apply_symm_apply, Pi.add_apply,
      hzero, zero_add, ite_eq_left hge]; simp [List.getElem?_eq_getElem hsub]
  ext x; simp only [memSeen, memPrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, List.mem_toFinset]; constructor
  · rintro ⟨i, hi, rfl⟩; rcases lt_or_ge i.val active with hlt | hge
    · exact Or.inl ⟨i, hlt, (hslot_lt i hlt).symm⟩
    · right; rw [hslot_ge i hge hi]; exact List.getElem_mem _
  · rintro (⟨i, hi, rfl⟩ | hxL)
    · exact ⟨i, by omega, hslot_lt i hi⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hxL; let idx : Fin k := ⟨active + a, by omega⟩
      refine ⟨idx, by dsimp [idx]; omega, ?_⟩; have hge : active ≤ idx.val :=
        (by dsimp [idx]; omega); have hlt : idx.val < active + L.length := (by dsimp [idx]; omega)
      rw [hslot_ge idx hge hlt]; simp [idx]
private lemma wp_dispFin_wd_of_lt {Var : Type} [DecidableEq Var] (res : Var) {k Q O : ℕ} (br : Fin k
  → OracleCirc Var Q O) (oracle : Unitary (2 ^ O)) (Θ : CQAssertion (Store Var) (2 ^ Q)) {s : ℕ} (hs
    : s <
  k) {τ : Store Var} (hτ : τ res = (s : ℤ)) : wp ((dispFin res br (finRange k)).compile qAssign
  oracle) Θ τ = wp ((br ⟨s, hs⟩).compile qAssign oracle) Θ τ := by
  set s₀ : Fin k := ⟨s, hs⟩; have hmem : s₀ ∈ finRange k := mem_finRange s₀; generalize finRange k =
    l at hmem
  induction l with
  | nil => cases hmem
  | cons x _ ih =>
    simp only [dispFin, compile, wp]; by_cases h : s₀ = x
    · subst h; simp [hτ, s₀]
    · have hne : τ res ≠ (x.val : ℤ) := fun heq ↦ h (Fin.ext (Int.ofNat.inj (hτ.symm.trans heq)))
      simp only [hne, ↓reduceIte]; exact ih (List.mem_of_ne_of_mem h hmem)
private lemma wp_dispFin_wd_of_ge {Var : Type} [DecidableEq Var] (res : Var) {k Q O : ℕ} (br : Fin k
  → OracleCirc Var Q O) (oracle : Unitary (2 ^ O)) (Θ : CQAssertion (Store Var) (2 ^ Q)) {s : ℕ} (hs
    : k ≤
  s) {τ : Store Var} (hτ : τ res = (s : ℤ)) : wp ((dispFin res br (finRange k)).compile qAssign
  oracle) Θ τ = Θ τ := by
  suffices ∀ l : List (Fin k), wp ((dispFin res br l).compile qAssign oracle) Θ τ = Θ τ from this
    (finRange k); intro l
  induction l with
  | nil => simp [dispFin]
  | cons x _ ih =>
    simp only [dispFin, compile, wp]; have hne : τ res ≠ (x.val : ℤ) :=
      (by rw [hτ]; have hx := x.isLt; omega); simp only [hne, ↓reduceIte]; exact ih
private lemma unitaryEffect_wdPrepAndNoClick {Var : Type} [DecidableEq Var] {n p m k : ℕ} (hp : p ≤
  n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) (active : ℕ) :
    let W := m * (n + 1); let M := k * n; let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1; let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let phaseOp := fc * unm * orac * fc
    let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
    let prepOp := (lowBlock W M).embedMatrix (wdPrepUnitary hp hm perm).1
    (∀ kInit : ℕ, UnitaryEffect ((wdPrepAndLoop (Var := Var) (k := k) hp hm perm active
      kInit).compile qAssign (groverParallelMarkingOracle m S)) ((unm * orac) * ((diffOp * phaseOp)
      ^ kInit) * prepOp)) ∧ (∀ kNext : ℕ, UnitaryEffect ((wdNoClickStep (Var := Var) (k := k) hp
      perm active kNext).compile qAssign (groverParallelMarkingOracle m S)) ((unm * orac) * ((diffOp
      * phaseOp) ^ kNext) * (unm * orac))) := by
  intro W M fc orac unm phaseOp diffOp prepOp; have hwwhole : workMemReg n m k (W + M) le_rfl =
    QRegister.whole (W + M) := (by ext i; simp [workMemReg]; rfl)
  have hwlow : workReg n m (W + M) (by omega) = lowBlock W M := rfl
  have hread : UnitaryEffect ((deflatedOracle (Var := Var) (m := m) (k := k) le_rfl (memPrefix k
    active)).compile qAssign (groverParallelMarkingOracle m S)) (unm * orac) := by
    unfold deflatedOracle; dsimp only [compile]; rw [hwwhole, QRegister.whole_embedUnitary]
    have h1 := unitaryEffect_qAssign (Var := Var) ((workFullReg n m (W + M) (by omega)).embedUnitary
      (groverParallelMarkingOracle m S))
    rw [workFullReg_embedUnitary_eq] at h1; exact unitaryEffect_seq h1 (unitaryEffect_phaseTag _)
  have hphase : UnitaryEffect ((deflatedPhaseStep (Var := Var) (m := m) (k := k) le_rfl (memPrefix k
    active)).compile qAssign (groverParallelMarkingOracle m S)) phaseOp := by
    unfold deflatedPhaseStep; dsimp only [compile]; rw [hwlow]
    have hfc := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (flagConj n m))
    rw [embedUnitary_val] at hfc
    simpa only [phaseOp, Matrix.mul_assoc] using unitaryEffect_seq hfc (unitaryEffect_seq hread hfc)
  have hloop (t : ℕ) : UnitaryEffect ((wdDeflatedGroverLoop (Var := Var) (m := m) (k := k) hp perm
    active t).compile qAssign (groverParallelMarkingOracle m S)) ((diffOp * phaseOp) ^ t) := by
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using unitaryEffect_skip (Var := Var) (d := 2 ^ (W + M))
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]; unfold wdDeflatedGroverStep; dsimp only [compile]
      have hdiff := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary
        (wdDiffuserUnitary (m := m) hp perm)); rw [embedUnitary_val] at hdiff; rw [pow_succ]
      exact unitaryEffect_seq (unitaryEffect_seq hphase hdiff) ih
  constructor
  · intro kInit; unfold wdPrepAndLoop; dsimp only [compile]
    have hprep := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (wdPrepUnitary hp
      hm perm)); rw [embedUnitary_val] at hprep
    simpa only [Matrix.mul_assoc] using unitaryEffect_seq hprep (unitaryEffect_seq (hloop kInit)
      hread)
  · intro kNext; unfold wdNoClickStep; dsimp only [compile]
    simpa only [Matrix.mul_assoc] using unitaryEffect_seq hread (unitaryEffect_seq (hloop kNext)
      hread)
private lemma costBounds_wdPieces {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hm1 : 1
  ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (perm : Equiv.Perm (Fin (2 ^
  n))) (S : Finset (Fin (2 ^ n))) (active : ℕ) :
    let model := CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)
    (∀ kInit : ℕ, CostBound (Var := Var) model ((wdPrepAndLoop (k := k) hp hm perm active
      kInit).compile qAssign (groverParallelMarkingOracle m S)) (kInit + 1)) ∧ (∀ kNext : ℕ,
      CostBound (Var := Var) model ((wdNoClickStep (k := k) hp perm active kNext).compile qAssign
      (groverParallelMarkingOracle m S)) (kNext + 2)) ∧ CostBound (Var := Var) model
      ((wdReadoutWrite (k := k) res hm1 hkN active).compile qAssign (groverParallelMarkingOracle m
      S)) 0 ∧ CostBound (Var := Var) model ((wdClickCleanup (k := k) res hm1 hkN hM active).compile
      qAssign (groverParallelMarkingOracle m S)) 0 := by
  intro model; let W := m * (n + 1); let M := k * n
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hread := costBound_deflatedOracle (Var := Var) (m := m) (k := k) le_rfl (memPrefix k active)
    S
  have hloop (t : ℕ) : CostBound (Var := Var) model ((wdDeflatedGroverLoop (Var := Var) (m := m) (k
    := k) hp perm active t).compile qAssign (groverParallelMarkingOracle m S)) t := by
    unfold wdDeflatedGroverLoop
    induction t with
    | zero => simpa using CostBound.skip_zero (Var := Var) model
    | succ t ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]; unfold wdDeflatedGroverStep; dsimp only [compile]
      have hstep : CostBound (Var := Var) model ((deflatedPhaseStep (m := m) (k := k) le_rfl
        (memPrefix k active)).compile qAssign (groverParallelMarkingOracle m S) ;; .qAssign
        (phaseTag ((lowBlock W M).embedUnitary (wdDiffuserUnitary (m := m) hp perm)))) 1 := by
        simpa using (costBound_deflatedPhaseStep le_rfl (memPrefix k active) S).seq
          (costBound_qAssign_phaseTag (Var := Var) hor _)
      exact (hstep.seq ih).mono (by rw [← NNReal.coe_le_coe]; push_cast; linarith)
  have hrw : CostBound (Var := Var) model ((wdReadoutWrite (Var := Var) (k := k) res hm1 hkN
    active).compile qAssign (groverParallelMarkingOracle m S)) 0 := by
    unfold wdReadoutWrite; dsimp only [compile]; exact ((costBound_qAssign_phaseTag (Var := Var) hor
      _).seq (costBound_setCountAndResetWork (Var := Var) (M := M) res (batchNextCount hm1 hkN
      (Nat.mul_one m) active) hor)).mono (by simp)
  refine ⟨fun kInit ↦ ?_, fun kNext ↦ ?_, hrw, ?_⟩
  · unfold wdPrepAndLoop; dsimp only [compile]; exact ((costBound_qAssign_phaseTag (Var := Var) hor
      _).seq ((hloop kInit).seq hread)).mono (by simp)
  · unfold wdNoClickStep; dsimp only [compile]
    exact (hread.seq ((hloop kNext).seq hread)).mono (le_of_eq (by ring))
  · unfold wdClickCleanup; dsimp only [compile]; exact ((costBound_qAssign_phaseTag (Var := Var) hor
      _).seq hrw).mono (by simp)
private lemma quadForm_wp_wdReadoutWrite {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hm1
  : 1 ≤ m) (hkN : k ≤ 2 ^ n) (active : ℕ) (S : Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2
    ^ (m *
  (n + 1) + k * n))) (σ : Store Var) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n))) :
    let hbg1 : m * 1 = m := Nat.mul_one m
    quadForm ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign (groverParallelMarkingOracle
      m S)) Θ) σ).1.1 (workMemState ψ (single μ 1)) = ∑ o : Fin (2 ^ (m * (n + 1))), (normSq (ψ o) :
      ℂ) * (Θ (Store.subst σ res (Int.ofNat (batchNextCount hm1 hkN hbg1 active o).val))).1.1
      (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg1 o) μ)) (workMemIdx n m k 0
      (writeMemBatch active (groupHits hbg1 o) μ)) := by
  intro hbg1; let W := m * (n + 1); let M := k * n
  unfold wdReadoutWrite; dsimp only [compile]; rw [wp_qSeq, quadForm_unitaryEffect
    (unitaryEffect_phaseTag _)]; unfold quadForm; rw [wp_setCountAndResetWork, Matrix.sum_mulVec,
    dotProduct_sum]; refine Finset.sum_congr rfl fun o _ ↦ ?_; rw [Matrix.mul_assoc, ←
    mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
    star_star, krausLowBlock_mulVec_memAddPerm]; change quadForm _ (ψ o • single (workMemIdx n m k 0
    (writeMemBatch active (groupHits hbg1 o) μ)) 1) = _; rw [quadForm_smul_vec, quadForm_single]
private lemma quadForm_wp_topAncProbe {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hm1 :
  1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (active r : ℕ) (pyth : PythPair) (noClickCirc :
  OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) (S : Finset (Fin (2 ^ n))) (Θ : CQAssertion
  (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) {μ :
    Fin (2 ^
  (k * n))} (hμ : μ.val < 2 ^ (k * n - 1)) :
    let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
    let probeCirc : OracleCirc Var (W + M) ((n + 1) * m) :=
      .seq (.step (phaseTag (weakAllHitUnitary n m M hM r pyth)))
        (.seq (.measure res (topAncReg W M hM))
          (.qIf (fun τ ↦ τ res = 1)
            (wdClickCleanup res hm1 hkN hM active) noClickCirc))
    quadForm ((wp (probeCirc.compile qAssign oracle) Θ) σ).1.1 (workMemState ψ (single μ 1)) =
      quadForm ((wp (noClickCirc.compile qAssign oracle) Θ) (Store.subst σ res 0)).1.1 (workMemState
      (wdDampVec n m r pyth.cVal ψ) (single μ 1)) + quadForm ((wp ((wdReadoutWrite res hm1 hkN
      active).compile qAssign oracle) Θ) (Store.subst σ res 1)).1.1 (workMemState (wdClickVec n m r
      pyth.sVal ψ) (single μ 1)) := by
  intro W M oracle probeCirc; dsimp only [probeCirc, compile]
  rw [wp_qSeq, wp_qSeq, quadForm_unitaryEffect (unitaryEffect_phaseTag _), show (weakAllHitUnitary n
    m M hM r pyth).1 = weakAllHitMat n m M hM r pyth from rfl, weakAllHitMat_mulVec_workMemState hM
    r pyth ψ hμ, quadForm_wp_measureRegister]; refine (Fin.sum_univ_two _).trans ?_
  have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) res ≠ 1 := by simp [Store.subst]
  have hs1 : (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) res = 1 := by simp [Store.subst]
  let branchProg := QProg.qIf (fun τ ↦ τ res = 1) ((wdClickCleanup res hm1 hkN hM active).compile
    qAssign oracle) (noClickCirc.compile qAssign oracle)
  have hwp0 : wp branchProg Θ (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) = wp
    (noClickCirc.compile qAssign oracle) Θ (Store.subst σ res 0) := by
    rw [wp_qIf]; dsimp only; rw [ite_eq_right hs0]; rfl
  have hwp1 : wp branchProg Θ (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) = wp
    ((wdClickCleanup res hm1 hkN hM active).compile qAssign oracle) Θ (Store.subst σ res 1) := by
    rw [wp_qIf]; dsimp only; rw [ite_eq_left hs1]; rfl
  congr 1
  · change quadForm ((wp branchProg Θ (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val))).1.1) _
      = _; rw [hwp0, topAncReg_projector_zero_mulVec hM _ _ hμ]
  · change quadForm
        ((wp branchProg Θ (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val))).1.1) _ = _
    rw [hwp1, topAncReg_projector_one_mulVec hM _ _ hμ]; unfold wdClickCleanup; dsimp only [compile]
    rw [wp_qSeq, quadForm_unitaryEffect (unitaryEffect_phaseTag _),
      topAncReg_flip_mulVec_one hM _ hμ]
private lemma wdBasisVec_groupHits_toFinset_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {R B : Finset (Fin (2 ^ n))} (hInj : Set.InjOn (fun x ↦ subcubePref hp
  hm (perm x)) (R : Set (Fin (2 ^ n)))) (hB : B ⊆ R) (o : Fin (2 ^ (m * (n + 1)))) (hamp :
  wdBasisVec hp hm perm R (B.image fun x ↦ subcubePref hp hm (perm x)) (parallelMarkPerm n m R o) ≠
  0) : (groupHits (Nat.mul_one m) o).toFinset = B := by
  let hbg1 : m * 1 = m := Nat.mul_one m; let pref := fun x ↦ subcubePref hp hm (perm x)
  have hA : B.image pref ⊆ R.image pref := Finset.image_subset_image hB; have hprops :=
    wdBasisVec_support_props hp hm perm R hA o hamp
  have hslot_nz (j : Fin m) : wdSlotWrap hp hm perm j (if j ∈ R.image pref then if j ∈ B.image pref
    then grover2DVec (subcubeLocalSet hp hm (R.image perm) j) 0 1 else grover2DVec (subcubeLocalSet
    hp hm (R.image perm) j) 1 0 else groverMultiState ∅ 0) ((groupReg hbg1 j).extractIndex
    (parallelMarkPerm n m R o)) ≠ 0 := fun h0 ↦ hamp (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  rcases groupHits_eq_filterMap_of_wdSlotWrap hp hm perm R _ o hslot_nz with ⟨hhit_sub, hgh_eq⟩
  have hsub_B : (groupHits hbg1 o).toFinset ⊆ B := by
    intro x hx; have hx_l : x ∈ groupHits hbg1 o := List.mem_toFinset.mp hx; rw [hgh_eq] at hx_l
    rcases List.mem_filterMap.mp hx_l with ⟨j, _, hj⟩; rcases hhit_sub j x hj with ⟨hxR, hpref_x⟩
    have his : (firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o)).isSome = true :=
      (by simp [hj]); rw [hprops.2.1 j] at his
    rcases Finset.mem_image.mp his with ⟨y, hyB, hpref_y⟩
    have hxy : x = y := hInj hxR (hB hyB) (hpref_x.trans hpref_y.symm); exact hxy ▸ hyB
  have hcard_eq : (groupHits hbg1 o).toFinset.card = B.card := by
    rw [List.toFinset_card_of_nodup (nodup_groupHits hbg1 o)]
    exact hprops.2.2.2.trans (Finset.card_image_of_injOn (hInj.mono hB))
  exact Finset.eq_of_subset_of_card_le hsub_B hcard_eq.ge
private lemma sum_normSq_wdAmpState_readout {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2
  ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) {R : Finset (Fin (2 ^ n))} (hInj : Set.InjOn (fun x ↦
  subcubePref hp hm (perm x)) (R : Set (Fin (2 ^ n)))) (u : ℕ → ℝ) (G : Finset (Fin (2 ^ n)) → ℂ) :
  (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (wdAmpState hp hm perm R u (parallelMarkPerm n m R o)) :
  ℂ) * G (R \ (groupHits (Nat.mul_one m) o).toFinset)) = ∑ B ∈ R.powerset, (((u B.card) ^ 2 : ℝ) :
  ℂ) * G (R \ B) := by
  let hbg1 : m * 1 = m := Nat.mul_one m; let pref := fun x ↦ subcubePref hp hm (perm x)
  have hpow_img : (R.image pref).powerset = R.powerset.image (fun B ↦ B.image pref) :=
    Finset.powerset_image
  have hinj_pow : Set.InjOn (fun B : Finset (Fin (2 ^ n)) ↦ B.image pref) (R.powerset : Set (Finset
    (Fin (2 ^ n)))) := by
    intro B₁ hB₁ B₂ hB₂ heq; have heq' : B₁.image pref = B₂.image pref := heq; have hB₁R :=
      Finset.mem_powerset.mp hB₁; have hB₂R := Finset.mem_powerset.mp hB₂; ext x; constructor
    · intro hx1; have himg : pref x ∈ B₂.image pref :=
        (by rw [← heq']; exact Finset.mem_image_of_mem pref hx1)
      rcases Finset.mem_image.mp himg with ⟨y, hy2, hyx⟩
      exact hInj (hB₁R hx1) (hB₂R hy2) hyx.symm ▸ hy2
    · intro hx2; have himg : pref x ∈ B₁.image pref :=
        (by rw [heq']; exact Finset.mem_image_of_mem pref hx2); rcases Finset.mem_image.mp himg with
        ⟨y, hy1, hyx⟩; exact hInj (hB₂R hx2) (hB₁R hy1) hyx.symm ▸ hy1
  have hamp_rew (w : Fin (2 ^ (m * (n + 1)))) : wdAmpState hp hm perm R u w = ∑ B ∈ R.powerset, ((u
    B.card : ℝ) : ℂ) * wdBasisVec hp hm perm R (B.image pref) w := by
    unfold wdAmpState; rw [hpow_img, Finset.sum_image hinj_pow]
    refine Finset.sum_congr rfl fun B hB ↦ ?_; rw [Finset.card_image_of_injOn (hInj.mono
      (Finset.mem_powerset.mp hB))]
  have hpt (o : Fin (2 ^ (m * (n + 1)))) : (normSq (wdAmpState hp hm perm R u (parallelMarkPerm n m
    R o)) : ℂ) * G (R \ (groupHits hbg1 o).toFinset) = ∑ B ∈ R.powerset, (((u B.card) ^ 2 * normSq
    (wdBasisVec hp hm perm R (B.image pref) (parallelMarkPerm n m R o)) : ℝ) : ℂ) * G (R \ B) := by
    rw [hamp_rew]; set w := parallelMarkPerm n m R o
    by_cases hex : ∃ B₀ ∈ R.powerset, wdBasisVec hp hm perm R (B₀.image pref) w ≠ 0
    · rcases hex with ⟨B₀, hB₀, hnz⟩
      have hzero (B : Finset (Fin (2 ^ n))) (hB : B ∈ R.powerset) (hne : B ≠ B₀) : wdBasisVec hp hm
        perm R (B.image pref) w = 0 := by
        have hne_img : B.image pref ≠ B₀.image pref := fun heq ↦ hne (hinj_pow hB hB₀ heq)
        rcases wdBasisVec_mul_eq_zero_of_ne hp hm perm R (Finset.image_subset_image
          (Finset.mem_powerset.mp hB)) (Finset.image_subset_image (Finset.mem_powerset.mp hB₀))
          hne_img w with h1 | h2
        · exact h1
        · exact absurd h2 hnz
      rw [Finset.sum_eq_single B₀ (fun B hB hne ↦ by rw [hzero B hB hne, mul_zero])
          (fun hnot ↦ absurd hB₀ hnot),
        Finset.sum_eq_single B₀ (fun B hB hne ↦ by
          rw [hzero B hB hne, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])
          (fun hnot ↦ absurd hB₀ hnot),
        wdBasisVec_groupHits_toFinset_eq hp hm perm hInj (Finset.mem_powerset.mp hB₀) o hnz,
        map_mul, Complex.normSq_ofReal]
      push_cast; ring
    · simp only [not_exists, not_and, not_not] at hex
      rw [Finset.sum_eq_zero (fun B hB ↦ by rw [hex B hB, mul_zero]),
        Complex.normSq_zero, Complex.ofReal_zero, zero_mul,
        Finset.sum_eq_zero (fun B hB ↦ by
          rw [hex B hB, Complex.normSq_zero, mul_zero, Complex.ofReal_zero, zero_mul])]
  simp_rw [hpt]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun B _ ↦ ?_
  simp_rw [Complex.ofReal_mul, mul_assoc]; rw [← Finset.mul_sum, ← Finset.sum_mul, ←
    Complex.ofReal_sum, Equiv.sum_comp (parallelMarkPerm n m R) (fun w ↦ normSq (wdBasisVec hp hm
    perm R (B.image pref) w)), sum_normSq_wdBasisVec hp hm hsub2 perm hInj (B.image pref),
    Complex.ofReal_one, one_mul]
private lemma wd_groverMultiState_eq_of_mem {q : ℕ} {M : Finset (Fin (2 ^ q))} (t : ℕ) {u₁ u₂ : Fin
  (2 ^ q)} (h₁ : u₁ ∈ M) (h₂ : u₂ ∈ M) : groverMultiState M t u₁ = groverMultiState M t u₂ := by
  induction t with
  | zero =>
    rw [groverMultiState_zero_eq_hadamard_mulVec, mulVec_single_one, col_apply, col_apply,
      hadamardMatrix_apply_zero, hadamardMatrix_apply_zero]
  | succ t ih =>
    rw [groverMultiState_succ]; set w := oracleMat M *ᵥ groverMultiState M t
    have hw : w u₁ = w u₂ := by
      dsimp only [w]; rw [oracleMat, mulVec_diagonal, mulVec_diagonal, ite_eq_left h₁, ite_eq_left
        h₂, ih]
    rw [Grover.diffuserMatrix, Matrix.sub_mulVec, Matrix.one_mulVec]; simp only [Pi.sub_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply, hw]
private lemma wd_normSq_groverMultiState_of_mem_eq {q : ℕ} {M : Finset (Fin (2 ^ q))} (t : ℕ) {u :
  Fin (2 ^ q)} (hu : u ∈ M) : normSq (groverMultiState M t u) = p_succ_frac t M.card (2 ^ q) /
  (M.card : ℝ) := by
  have hsum := sum_mem_normSq_groverMultiState_eq_p_succ_frac M t
  have hcongr : (∑ v ∈ M, normSq (groverMultiState M t v)) = (M.card : ℝ) * normSq (groverMultiState
    M t u) := by
    rw [Finset.sum_congr rfl (fun v hv ↦ by rw [wd_groverMultiState_eq_of_mem t hv hu]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hcongr] at hsum; have hpos : (0 : ℝ) < (M.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr
    ⟨u, hu⟩); exact eq_div_of_mul_eq hpos.ne' (by linarith)
private lemma sum_normSq_wdSlotWrap_grover {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (K_sub : ℕ) (j : Fin m) (o_slot : Option (Fin
  (2 ^ n))) : (∑ z : Fin (2 ^ (1 * (n + 1))), if firstMarkedAddr n 1 (parallelMarkPerm n 1 R z) =
  o_slot then (normSq (wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm (R.image
  perm) j) K_sub) z) : ℂ) else 0) = (rotSlotHitProb (2 ^ (n - p)) K_sub (R.filter fun x ↦
  subcubePref hp hm (perm x) = j) o_slot : ℂ) := by
  let ξ := wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) K_sub)
  let M_loc := subcubeLocalSet hp hm (R.image perm) j
  let B := R.filter fun x ↦ subcubePref hp hm (perm x) = j
  have hcard_eq : M_loc.card = B.card := card_subcubeLocalSet_image_perm hp hm perm R j
  let term (z : Fin (2 ^ (1 * (n + 1)))) : ℂ :=
    if firstMarkedAddr n 1 (parallelMarkPerm n 1 R z) = o_slot then (normSq (ξ z) : ℂ) else 0
  change ∑ z, term z = _; rw [← (addrReg n 1).basisSplitEquiv.symm.sum_comp term, sum_prod_type]
  have hinner (u : Fin (2 ^ (1 * n))) : (∑ e : (addrReg n 1).Environment → ZMod 2, term ((addrReg n
    1).basisSplitEquiv.symm (u, e))) = if firstTupleHit n 1 R u = o_slot then (normSq
    (((workMemState (groverMultiState M_loc K_sub) (single (finCongr hm j) 1) ∘ wdCast1nEquiv hp) ∘
    wdPerm1n perm) u) : ℂ) else 0 := by
    rw [sum_eq_single 0 (fun e he ↦ by
      dsimp only [term, ξ, wdSlotWrap, tensorState]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero,
        Complex.ofReal_zero, ite_self])]
    dsimp only [term, ξ, wdSlotWrap, tensorState]; have hE : ((addrReg n 1).basisSplitEquiv
      ((addrReg n 1).basisSplitEquiv.symm (u, 0))).2 = 0 := (by rw [Equiv.apply_symm_apply])
    have hex : (addrReg n 1).extractIndex ((addrReg n 1).basisSplitEquiv.symm (u, 0)) = u :=
      (by rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply])
    rw [firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R _ hE, hex, hE, Pi.single_eq_same,
      mul_one]
  simp_rw [hinner]; rw [← (wdPerm1n perm).symm.sum_comp]; simp only [Function.comp_apply,
    Equiv.apply_symm_apply]; rw [← (wdCast1nEquiv hp).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]; rw [← (lowHighEquiv (n - p) p).symm.sum_comp, sum_prod_type]
  let xOf (w_loc : Fin (2 ^ (n - p))) : Fin (2 ^ n) :=
    perm.symm ((subcubeSplit hp hm).symm (w_loc, j))
  have hprod_sum (w_loc : Fin (2 ^ (n - p))) : (∑ y : Fin (2 ^ p), if firstTupleHit n 1 R ((wdPerm1n
    perm).symm ((wdCast1nEquiv hp).symm ((lowHighEquiv (n - p) p).symm (w_loc, y)))) = o_slot then
    (normSq (workMemState (groverMultiState M_loc K_sub) (single (finCongr hm j) 1) ((lowHighEquiv
    (n - p) p).symm (w_loc, y))) : ℂ) else 0) = if (if w_loc ∈ M_loc then some (xOf w_loc) else
    none) = o_slot then (normSq (groverMultiState M_loc K_sub w_loc) : ℂ) else 0 := by
    rw [sum_eq_single (finCongr hm j) (fun y hy ↦ by
      dsimp only [workMemState]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hy, mul_zero, Complex.normSq_zero,
        Complex.ofReal_zero, ite_self])]
    set v₀ := (wdCast1nEquiv hp).symm ((lowHighEquiv (n - p) p).symm (w_loc, finCongr hm j))
    set u₀ := (wdPerm1n perm).symm v₀; have hsp := subcubeSplit_addrEquiv_one_wd hp hm v₀
    simp only [v₀, Equiv.apply_symm_apply, wd_finCongr_symm_finCongr] at hsp
    have hv₀_eq : addrEquiv n 1 v₀ 0 = (subcubeSplit hp hm).symm (w_loc, j) :=
      (by rw [← hsp, Equiv.symm_apply_apply]); have hu₀_eq : addrEquiv n 1 u₀ 0 = xOf w_loc :=
      (by dsimp only [u₀, xOf]; rw [wdPerm1n_symm, addrEquiv_wdPerm1n_zero, hv₀_eq])
    have hmem_iff : xOf w_loc ∈ R ↔ w_loc ∈ M_loc := by
      dsimp only [xOf, M_loc]; rw [mem_subcubeLocalSet_iff]; constructor
      · intro hxR; simpa using Finset.mem_image_of_mem perm hxR
      · intro himg; rcases Finset.mem_image.mp himg with ⟨x, hxR, hxp⟩
        have hxeq : x = perm.symm ((subcubeSplit hp hm).symm (w_loc, j)) := (by rw [← hxp,
          Equiv.symm_apply_apply]); rwa [← hxeq]
    have hhit_eq : firstTupleHit n 1 R u₀ = if w_loc ∈ M_loc then some (xOf w_loc) else none :=
      (by rw [firstTupleHit_one_eq_wd, hu₀_eq, if_congr hmem_iff rfl rfl])
    dsimp only [workMemState]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one, hhit_eq]
  simp_rw [hprod_sum, ← Finset.sum_filter, ← Complex.ofReal_sum]; congr 1
  cases o_slot with
  | none =>
    have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M_loc)
      (fun w_loc ↦ normSq (groverMultiState M_loc K_sub w_loc))
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter,
      sum_mem_normSq_groverMultiState_eq_p_succ_frac, sum_normSq_groverMultiState_eq_one] at hpart
    have hfilt :
        (Finset.univ.filter fun w_loc ↦ (if w_loc ∈ M_loc then some (xOf w_loc) else none) = none) =
        Finset.univ.filter (· ∉ M_loc) := by
      ext w_loc; by_cases hw : w_loc ∈ M_loc <;> simp [hw]
    rw [hfilt]; dsimp only [rotSlotHitProb]; rw [← hcard_eq]; linarith
  | some x₀ =>
    dsimp only [rotSlotHitProb]; by_cases hxB : x₀ ∈ B
    · rw [ite_eq_left hxB]; rcases Finset.mem_filter.mp hxB with ⟨hxR, hxpref⟩
      let w₀ : Fin (2 ^ (n - p)) := (subcubeSplit hp hm (perm x₀)).1
      have hpair : (subcubeSplit hp hm).symm (w₀, j) = perm x₀ := by
        have hsplit : subcubeSplit hp hm (perm x₀) = (w₀, j) := Prod.ext rfl hxpref; rw [← hsplit,
          Equiv.symm_apply_apply]
      have hw₀_mem : w₀ ∈ M_loc := by
        dsimp only [M_loc]; rw [mem_subcubeLocalSet_iff, hpair]
        exact Finset.mem_image_of_mem perm hxR
      have hx_w₀ : xOf w₀ = x₀ := (by dsimp only [xOf]; rw [hpair, Equiv.symm_apply_apply])
      have hfilt : (Finset.univ.filter fun w_loc ↦ (if w_loc ∈ M_loc then some (xOf w_loc) else
        none) = some x₀) = {w₀} := by
        ext w_loc; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro heq; by_cases hw : w_loc ∈ M_loc
          · rw [ite_eq_left hw, Option.some.injEq] at heq
            have h1 : (subcubeSplit hp hm).symm (w_loc, j) = (subcubeSplit hp hm).symm (w₀, j) :=
              (by rw [hpair]; exact perm.symm.injective (by simpa [xOf] using heq))
            exact congrArg Prod.fst ((subcubeSplit hp hm).symm.injective h1)
          · rw [ite_eq_right hw] at heq; cases heq
        · rintro rfl; rw [ite_eq_left hw₀_mem, hx_w₀]
      rw [hfilt, Finset.sum_singleton, wd_normSq_groverMultiState_of_mem_eq K_sub hw₀_mem, hcard_eq]
    · rw [ite_eq_right hxB]; refine Finset.sum_eq_zero fun w_loc hw_filt ↦ ?_; have heq :=
        (Finset.mem_filter.mp hw_filt).2; by_cases hw : w_loc ∈ M_loc
      · rw [ite_eq_left hw, Option.some.injEq] at heq; subst heq; have himg : (subcubeSplit hp
          hm).symm (w_loc, j) ∈ R.image perm := (mem_subcubeLocalSet_iff hp hm (R.image perm) j
          w_loc).mp hw; rcases Finset.mem_image.mp himg with ⟨x, hxR, hxp⟩; have hxeq : xOf w_loc =
          x := (by dsimp only [xOf]; rw [← hxp, Equiv.symm_apply_apply])
        have hpref : subcubePref hp hm (perm (xOf w_loc)) = j :=
          (by dsimp only [xOf, subcubePref]; simp); exact False.elim (hxB (Finset.mem_filter.mpr
          ⟨hxeq ▸ hxR, hpref⟩))
      · rw [ite_eq_right hw] at heq; cases heq
private lemma sum_normSq_wdMultiReadout_eq {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) (R : Finset (Fin (2 ^ n))) (K_sub : ℕ) (G : Finset (Fin (2 ^ n)) → ℂ) :
    let hbg1 : m * 1 = m := Nat.mul_one m; let pref := fun x ↦ subcubePref hp hm (perm x)
    (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (wdProdState (fun j ↦ wdSlotWrap hp hm perm j
      (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) K_sub)) (parallelMarkPerm n m R o))
      : ℂ) * G (R \ (groupHits hbg1 o).toFinset)) = ∑ hit ∈ rotHitSupport pref R, ((∏ j : Fin m,
      rotSlotHitProb (2 ^ (n - p)) K_sub (R.filter fun x ↦ pref x = j) (hit j) : ℝ) : ℂ) * G (R \
      rotHitFinset hit) := by
  intro hbg1 pref; let ξ (j : Fin m) := wdSlotWrap hp hm perm j
    (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) K_sub)
  let hitZ (z : Fin (2 ^ (1 * (n + 1)))) : Option (Fin (2 ^ n)) :=
    firstMarkedAddr n 1 (parallelMarkPerm n 1 R z)
  have hfm_toFinset (hit : Fin m → Option (Fin (2 ^ n))) : ((finRange m).filterMap hit).toFinset =
    rotHitFinset hit := by
    ext x; simp only [List.mem_toFinset, List.mem_filterMap, mem_finRange, true_and, rotHitFinset,
      Finset.mem_biUnion, Finset.mem_univ]; constructor
    · rintro ⟨j, hj⟩; exact ⟨j, by simp [hj]⟩
    · rintro ⟨j, hj⟩
      cases h : hit j with
      | none => simp [h] at hj
      | some y => simp only [h, Finset.mem_singleton] at hj; exact ⟨j, hj ▸ h⟩
  have h1 : (∑ o : Fin (2 ^ (m * (n + 1))), (normSq (wdProdState ξ (parallelMarkPerm n m R o)) : ℂ)
    * G (R \ (groupHits hbg1 o).toFinset)) = ∑ w : Fin (2 ^ (m * (n + 1))), (normSq (wdProdState ξ
    w) : ℂ) * G (R \ (groupHits hbg1 (parallelMarkPerm n m R w)).toFinset) := by
    rw [← Equiv.sum_comp (parallelMarkPerm n m R)]; refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [parallelMarkPerm_involutive]
  rw [h1, ← (groupSplitEquiv hbg1).symm.sum_comp]
  have h2 (zs : Fin m → Fin (2 ^ (1 * (n + 1)))) : (normSq (wdProdState ξ ((groupSplitEquiv
    hbg1).symm zs)) : ℂ) * G (R \ (groupHits hbg1 (parallelMarkPerm n m R ((groupSplitEquiv
    hbg1).symm zs))).toFinset) = (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) * G (R \ rotHitFinset
    (hitZ ∘ zs)) := by
    have hex (j : Fin m) : (groupReg hbg1 j).extractIndex ((groupSplitEquiv hbg1).symm zs) = zs j :=
      (by rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply])
    have hprod : (normSq (wdProdState ξ ((groupSplitEquiv hbg1).symm zs)) : ℂ) = ∏ j : Fin m,
      (normSq (ξ j (zs j)) : ℂ) :=
      (by unfold wdProdState; simp_rw [hex, map_prod, Complex.ofReal_prod]); rw [hprod]
    by_cases hzero : (∏ j : Fin m, (normSq (ξ j (zs j)) : ℂ)) = 0
    · rw [hzero, zero_mul, zero_mul]
    · have hnz (j : Fin m) : ξ j (zs j) ≠ 0 := by
        intro hj0; apply hzero; refine Finset.prod_eq_zero (Finset.mem_univ j) ?_; rw [hj0,
          Complex.normSq_zero, Complex.ofReal_zero]
      set o_zs := parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs)
      have hslot_nz (j : Fin m) : ξ j ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o_zs))
        ≠ 0 := (by dsimp only [o_zs]; rw [parallelMarkPerm_involutive, hex]; exact hnz j)
      have hgh := (groupHits_eq_filterMap_of_wdSlotWrap hp hm perm R _ o_zs hslot_nz).2
      have hfm_eq : ((finRange m).filterMap fun j ↦ firstMarkedAddr n 1 ((groupReg hbg1
        j).extractIndex o_zs)) = (finRange m).filterMap (hitZ ∘ zs) := by
        refine List.filterMap_congr fun j _ ↦ ?_; dsimp only [o_zs, hitZ, Function.comp_apply]
        rw [extractIndex_groupReg_parallelMarkPerm, hex]
      rw [hgh, hfm_eq, hfm_toFinset]
  simp_rw [h2]; symm
  have hrhs (hit : Fin m → Option (Fin (2 ^ n))) : ((∏ j : Fin m, rotSlotHitProb (2 ^ (n - p)) K_sub
    (R.filter fun x ↦ pref x = j) (hit j) : ℝ) : ℂ) * G (R \ rotHitFinset hit) = ∑ zs : Fin m → Fin
    (2 ^ (1 * (n + 1))), (∏ j : Fin m, if hitZ (zs j) = hit j then (normSq (ξ j (zs j)) : ℂ) else 0)
    * G (R \ rotHitFinset hit) := by
    have hslot_h (j : Fin m) : (rotSlotHitProb (2 ^ (n - p)) K_sub (R.filter fun x ↦ pref x = j)
      (hit j) : ℂ) = ∑ z : Fin (2 ^ (1 * (n + 1))), if hitZ z = hit j then (normSq (ξ j z) : ℂ) else
      0 := (sum_normSq_wdSlotWrap_grover hp hm perm R K_sub j (hit j)).symm
    rw [Complex.ofReal_prod]; simp_rw [hslot_h]; rw [Fintype.prod_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun hit _ ↦ hrhs hit).trans ?_; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun zs _ ↦ ?_; by_cases hzero : (∏ j : Fin m, (normSq (ξ j (zs j)) :
    ℂ)) = 0
  · rw [hzero, zero_mul]; refine Finset.sum_eq_zero fun hit _ ↦ ?_; obtain ⟨j, _, hj0⟩ :=
      Finset.prod_eq_zero_iff.mp hzero; have hterm0 : (if hitZ (zs j) = hit j then (normSq (ξ j (zs
      j)) : ℂ) else 0) = 0 := (by split_ifs <;> simp [hj0]); rw [Finset.prod_eq_zero
      (Finset.mem_univ j) hterm0, zero_mul]
  · have hnz (j : Fin m) : ξ j (zs j) ≠ 0 := by
      intro hj0; apply hzero; refine Finset.prod_eq_zero (Finset.mem_univ j) ?_; rw [hj0,
        Complex.normSq_zero, Complex.ofReal_zero]
    set o_zs := parallelMarkPerm n m R ((groupSplitEquiv hbg1).symm zs)
    have hex (j : Fin m) : (groupReg hbg1 j).extractIndex ((groupSplitEquiv hbg1).symm zs) = zs j :=
      (by rw [← groupSplitEquiv_apply hbg1, Equiv.apply_symm_apply])
    have hslot_nz (j : Fin m) : ξ j ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o_zs)) ≠
      0 := (by dsimp only [o_zs]; rw [parallelMarkPerm_involutive, hex]; exact hnz j)
    have hhit_sub := (groupHits_eq_filterMap_of_wdSlotWrap hp hm perm R _ o_zs hslot_nz).1
    have hmem_supp : (hitZ ∘ zs) ∈ rotHitSupport pref R := by
      unfold rotHitSupport; rw [Fintype.mem_piFinset]; intro j; dsimp only [Function.comp_apply]
      cases h : hitZ (zs j) with
      | none => exact Finset.mem_insert_self _ _
      | some x =>
        have h_ozs : firstMarkedAddr n 1 ((groupReg hbg1 j).extractIndex o_zs) = some x := by
          dsimp only [o_zs]; rwa [extractIndex_groupReg_parallelMarkPerm, hex]
        rcases hhit_sub j x h_ozs with ⟨hxR, hpref⟩
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxR, hpref⟩,
          rfl⟩)
    rw [Finset.sum_eq_single (hitZ ∘ zs) (fun hit _ hne ↦ ?_) (fun hnot ↦ False.elim (hnot
      hmem_supp))]
    · simp only [Function.comp_apply, ite_true]
    · obtain ⟨j, hj⟩ : ∃ j : Fin m, hitZ (zs j) ≠ hit j := by
        by_contra! hall; exact hne (funext fun j ↦ (hall j).symm)
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj), zero_mul]
/- ## Section 5c: Multi-Pass `wp` Invariant, `ScaledCostRel` Cost, & Certified Drift Theorems -/
private lemma deflatedRead_mulVec_workMemState_wd {n m k active : ℕ} {S : Finset (Fin (2 ^ n))} {μ :
  Fin (2 ^ (k * n))} (hsub : memSeen n k (memPrefix k active) μ ⊆ S) :
    let W := m * (n + 1); let M := k * n; let R := S \ memSeen n k (memPrefix k active) μ
    let orac := (lowBlock W M).embedMatrix ((fullReg n m).embedUnitary (groverParallelMarkingOracle
      m S)).1; let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    (∀ ξ : Fin (2 ^ W) → ℂ, (unm * orac) *ᵥ workMemState ξ (single μ 1) = workMemState (P_R *ᵥ ξ)
      (single μ 1)) ∧ (∀ ξ : Fin (2 ^ W) → ℂ, P_R *ᵥ (P_R *ᵥ ξ) = ξ) := by
  intro W M R orac unm P_R; constructor
  · intro ξ; rw [← mulVec_mulVec, unmark_mul_parallelOracle_workMemState (memPrefix k active) ξ μ
      hsub, show S \ memSeen n k (memPrefix k active) μ = R from rfl,
      fullReg_embedUnitary_eq_permutationUnitary R]
  · intro ξ; funext w; rw [permUnitary_parallelMarkPerm_mulVec_apply_wd,
      permUnitary_parallelMarkPerm_mulVec_apply_wd, parallelMarkPerm_involutive]
private lemma quadForm_wp_wdReadoutWrite_of_support_wd {Var : Type} [DecidableEq Var] (res : Var) {n
  m k active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {μ
  : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) (Θ : CQAssertion (Store Var) (2 ^ (m * (n
    + 1) + k
  * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤
  k → τ res = (s : ℤ) → MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0
  ν) = (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ)) (σ : Store Var) (φ : Fin (2 ^ (m * (n + 1))) →
  ℂ) (hsupp : ∀ o : Fin (2 ^ (m * (n + 1))), φ (parallelMarkPerm n m (S \ memSeen n k (memPrefix k
  active) μ) o) ≠ 0 → ∀ x ∈ groupHits (Nat.mul_one m) o, x ∈ S \ memSeen n k (memPrefix k active) μ)
  :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    quadForm ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign (groverParallelMarkingOracle
      m S)) Θ) σ).1.1 (workMemState (P_R *ᵥ φ) (single μ 1)) = ∑ o : Fin (2 ^ (m * (n + 1))),
      (normSq (φ (parallelMarkPerm n m R o)) : ℂ) * (Ψ (R \ (groupHits (Nat.mul_one m) o).toFinset)
      : ℂ) := by
  intro R P_R; let hbg1 : m * 1 = m := Nat.mul_one m
  rw [quadForm_wp_wdReadoutWrite]; refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [permUnitary_parallelMarkPerm_mulVec_apply_wd]; by_cases hnz : φ (parallelMarkPerm n m R o) = 0
  · simp [hnz]
  · obtain ⟨hlen, hval'⟩ := memPrefixValid_writeMemBatch hcard hval (nodup_groupHits hbg1 o) (hsupp
      o hnz); have hcnt : (batchNextCount hm1 hkN hbg1 active o).val = active + (groupHits hbg1
      o).length := (by simp [batchNextCount, Nat.min_eq_right hlen])
    have hsdiff : S \ memSeen n k (memPrefix k (active + (groupHits hbg1 o).length)) (writeMemBatch
      active (groupHits hbg1 o) μ) = R \ (groupHits hbg1 o).toFinset := by
      rw [memSeen_writeMemBatch_wd hval (groupHits hbg1 o) hlen]; ext x; simp only [R,
        Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [hcnt, hΘ (active + (groupHits hbg1 o).length) _ _ hlen (by simp [Store.subst]) hval',
      hsdiff]
private lemma groverMultiState_iterate_wd {q : ℕ} (M : Finset (Fin (2 ^ q))) (s t : ℕ) : ((fun ψ ↦
  Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ ψ))^[t]) (groverMultiState M s) = groverMultiState M (s +
  t) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', ih, Nat.add_succ, groverMultiState_succ]
private lemma quadForm_wp_wdProbeChain_inj {Var : Type} [DecidableEq Var] (res : Var) {n p m k
  active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2
  : 2 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} (hcard : S.card =
  k) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) (hμ : μ.val < 2 ^ (k * n - 1)) (hInj
  : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) ((S \ memSeen n k (memPrefix k active) μ : Finset
  (Fin (2 ^ n))) : Set (Fin (2 ^ n)))) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ
    : Finset
  (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res = (s :
  ℤ) → MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (Ψ (S \
  memSeen n k (memPrefix k s) ν) : ℂ)) (probes : List (PythPair × ℕ)) (u : ℕ → ℝ) (σ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    quadForm ((wp ((wdProbeChain res hm1 hkN hM hp perm active R.card probes).compile qAssign
      (groverParallelMarkingOracle m S)) Θ) σ).1.1 (workMemState (P_R *ᵥ wdAmpState hp hm perm R u)
      (single μ 1)) = ((wdChainClickProb R.card θ₁ probes u * Ψ ∅ + ∑ B ∈ R.powerset,
      (wdChainFinalAmp R.card θ₁ probes u B.card) ^ 2 * Ψ (R \ B) : ℝ) : ℂ) := by
  intro R P_R θ₁; let hbg1 : m * 1 = m := Nat.mul_one m
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hsub : memSeen n k (memPrefix k active) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
  have hsupp_amp (u' : ℕ → ℝ) (o : Fin (2 ^ (m * (n + 1)))) (hnz : wdAmpState hp hm perm R u'
    (parallelMarkPerm n m R o) ≠ 0) : ∀ x ∈ groupHits hbg1 o, x ∈ R := by
    unfold wdAmpState at hnz; obtain ⟨A, hA, hAnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    have hAb : wdBasisVec hp hm perm R A (parallelMarkPerm n m R o) ≠ 0 := fun h0 ↦ hAnz
      (by rw [h0, mul_zero]); exact (wdBasisVec_support_props hp hm perm R (Finset.mem_powerset.mp
      hA) o hAb).2.2.1
  induction probes generalizing u σ with
  | nil =>
    dsimp only [wdProbeChain, wdChainClickProb, wdChainFinalAmp]
    rw [quadForm_wp_wdReadoutWrite_of_support_wd res hm1 hkN hcard hval Θ Ψ hΘ σ _ (hsupp_amp u),
      sum_normSq_wdAmpState_readout hp hm hsub2 perm hInj u (fun X ↦ (Ψ X : ℂ))]; push_cast; ring
  | cons pk rest ih =>
    rcases pk with ⟨pyth, kNext⟩; dsimp only [wdProbeChain]; rw [quadForm_wp_topAncProbe res hm1 hkN
      hM active R.card pyth _ S Θ σ _ hμ]
    rcases wdDamp_and_click_marked_wdAmpState hp hm perm hInj pyth u with ⟨hdamp, hclick⟩
    rw [hdamp, hclick]
    -- Click branch:
    let J := R.image pref
    have hsmul_ws (c : ℂ) (v : Fin (2 ^ (m * (n + 1))) → ℂ) : workMemState (c • v) (single μ 1) = c
      • workMemState v (single μ 1) := (by funext idx; simp [workMemState, mul_assoc])
    have hclick_val : quadForm ((wp ((wdReadoutWrite res hm1 hkN active).compile qAssign
      (groverParallelMarkingOracle m S)) Θ) (Store.subst σ res 1)).1.1 (workMemState (((pyth.sVal *
      u R.card : ℝ) : ℂ) • (P_R *ᵥ wdBasisVec hp hm perm R J)) (single μ 1)) = (((pyth.sVal * u
      R.card) ^ 2 * Ψ ∅ : ℝ) : ℂ) := by
      rw [hsmul_ws, quadForm_smul_vec, Complex.normSq_ofReal,
        quadForm_wp_wdReadoutWrite_of_support_wd res hm1 hkN hcard hval Θ Ψ hΘ _ _ (fun o hnz ↦
        (wdBasisVec_support_props hp hm perm R Finset.Subset.rfl o hnz).2.2.1)]
      have hterm (o : Fin (2 ^ (m * (n + 1)))) : (normSq (wdBasisVec hp hm perm R J
        (parallelMarkPerm n m R o)) : ℂ) * (Ψ (R \ (groupHits hbg1 o).toFinset) : ℂ) = (normSq
        (wdBasisVec hp hm perm R J (parallelMarkPerm n m R o)) : ℂ) * (Ψ ∅ : ℂ) := by
        by_cases hnz : wdBasisVec hp hm perm R J (parallelMarkPerm n m R o) = 0
        · simp [hnz]
        · rw [wdBasisVec_groupHits_toFinset_eq hp hm perm hInj Finset.Subset.rfl o hnz,
            Finset.sdiff_self]
      rw [Finset.sum_congr rfl fun o _ ↦ hterm o, ← Finset.sum_mul, ← Complex.ofReal_sum,
        Equiv.sum_comp (parallelMarkPerm n m R) (fun w ↦ normSq (wdBasisVec hp hm perm R J w)),
        sum_normSq_wdBasisVec hp hm hsub2 perm hInj J]; push_cast; ring
    -- No-click branch:
    rcases deflatedRead_mulVec_workMemState_wd (m := m) hsub with ⟨hread_mul, hPR_inv⟩; have hue :=
      (unitaryEffect_wdPrepAndNoClick (Var := Var) (k := k) hp hm perm S active).2 kNext
    have hnoclick_vec :
        let W := m * (n + 1); let M := k * n; let fc := (lowBlock W M).embedMatrix (flagConj n m).1
        let orac := (lowBlock W M).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
        let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
        let phaseOp := fc * unm * orac * fc
        let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
        ((unm * orac) * ((diffOp * phaseOp) ^ kNext) * (unm * orac)) *ᵥ
            workMemState (P_R *ᵥ wdAmpState hp hm perm R (wdDampAmp R.card pyth u)) (single μ 1) =
          workMemState
            (P_R *ᵥ wdAmpState hp hm perm R (dickeStep R.card (Real.cos (2 * (kNext : ℝ) * θ₁))
                (Real.sin (2 * (kNext : ℝ) * θ₁)) (wdDampAmp R.card pyth u)))
            (single μ 1) := by
      intro W M fc orac unm phaseOp diffOp; dsimp only [W, M, fc, orac, unm, phaseOp, diffOp]
      rw [← mulVec_mulVec, ← mulVec_mulVec, hread_mul, hPR_inv, wdGrover_iter_wdAmpState hp hm hsub2
        perm hsub hInj _ kNext, hread_mul]
    dsimp only [compile]; rw [wp_qSeq, quadForm_unitaryEffect hue, hnoclick_vec, ih, hclick_val]
    dsimp only [wdChainClickProb, wdChainFinalAmp]; push_cast; ring
private lemma quadForm_wp_wdProbeChain_notInj {Var : Type} [DecidableEq Var] (res : Var) {n p m k
  active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (perm :
  Equiv.Perm (Fin (2 ^ n))) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) {μ : Fin (2 ^ (k * n))}
  (hval : MemPrefixValid S active μ) (hμ : μ.val < 2 ^ (k * n - 1)) (hNotInj : ¬ Set.InjOn (fun x ↦
  subcubePref hp hm (perm x)) ((S \ memSeen n k (memPrefix k active) μ : Finset (Fin (2 ^ n))) : Set
  (Fin (2 ^ n)))) (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^
    n)) → ℝ)
  (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ res = (s : ℤ) → MemPrefixValid
  S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (Ψ (S \ memSeen n k (memPrefix k
  s) ν) : ℂ)) (probes : List (PythPair × ℕ)) (t : ℕ) (σ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ
    let P_R := (permutationUnitary (parallelMarkPerm n m R)).1
    let pref := fun x ↦ subcubePref hp hm (perm x)
    let ξ (steps : ℕ) := wdProdState (fun j ↦ wdSlotWrap hp hm perm j (groverMultiState
      (subcubeLocalSet hp hm (R.image perm) j) steps))
    quadForm ((wp ((wdProbeChain res hm1 hkN hM hp perm active R.card probes).compile qAssign
      (groverParallelMarkingOracle m S)) Θ) σ).1.1 (workMemState (P_R *ᵥ ξ t) (single μ 1)) = ((∑
      hit ∈ rotHitSupport pref R, (∏ j : Fin m, rotSlotHitProb (2 ^ (n - p)) (wdTotalSteps t probes)
      (R.filter fun x ↦ pref x = j) (hit j)) * Ψ (R \ rotHitFinset hit) : ℝ) : ℂ) := by
  intro R P_R pref ξ; let hbg1 : m * 1 = m := Nat.mul_one m
  have hsub : memSeen n k (memPrefix k active) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
  induction probes generalizing t σ with
  | nil =>
    dsimp only [wdProbeChain, wdTotalSteps, List.map_nil, List.sum_nil, add_zero]
    have hsupp_prod (o : Fin (2 ^ (m * (n + 1)))) (hnz : ξ t (parallelMarkPerm n m R o) ≠ 0) : ∀ x ∈
      groupHits hbg1 o, x ∈ R := by
      have hslot_nz (j : Fin m) : wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm
        (R.image perm) j) t) ((groupReg hbg1 j).extractIndex (parallelMarkPerm n m R o)) ≠ 0 := fun
        h0 ↦ hnz (Finset.prod_eq_zero (Finset.mem_univ j) h0); have hhit :=
        (groupHits_eq_filterMap_of_wdSlotWrap hp hm perm R _ o hslot_nz).1; intro x hx
      unfold groupHits at hx; rcases List.mem_filterMap.mp (List.mem_dedup.mp hx) with ⟨j, _, hj⟩
      exact (hhit j x hj).1
    rw [quadForm_wp_wdReadoutWrite_of_support_wd res hm1 hkN hcard hval Θ Ψ hΘ σ _ hsupp_prod,
      sum_normSq_wdMultiReadout_eq hp hm perm R t (fun X ↦ (Ψ X : ℂ))]; push_cast; rfl
  | cons pk rest ih =>
    rcases pk with ⟨pyth, kNext⟩; dsimp only [wdProbeChain]; rw [quadForm_wp_topAncProbe res hm1 hkN
      hM active R.card pyth _ S Θ σ _ hμ]
    have hdamp_eq : wdDampVec n m R.card pyth.cVal (P_R *ᵥ ξ t) = P_R *ᵥ ξ t := by
      funext o; dsimp only [wdDampVec]; by_cases hnz : (P_R *ᵥ ξ t) o = 0
      · simp [hnz]
      · have hnz' : ξ t (parallelMarkPerm n m R o) ≠ 0 :=
          (by rwa [permUnitary_parallelMarkPerm_mulVec_apply_wd] at hnz)
        exact ite_eq_right (ne_of_lt (wdHitCount_lt_of_not_injOn hp hm perm hNotInj t o hnz'))
    have hclick_eq : wdClickVec n m R.card pyth.sVal (P_R *ᵥ ξ t) = 0 := by
      funext o; dsimp only [wdClickVec]; by_cases hnz : (P_R *ᵥ ξ t) o = 0
      · simp [hnz]
      · have hnz' : ξ t (parallelMarkPerm n m R o) ≠ 0 :=
          (by rwa [permUnitary_parallelMarkPerm_mulVec_apply_wd] at hnz)
        exact ite_eq_right (ne_of_lt (wdHitCount_lt_of_not_injOn hp hm perm hNotInj t o hnz'))
    have hws0 : workMemState (0 : Fin (2 ^ (m * (n + 1))) → ℂ) (single μ 1) = 0 :=
      (by funext z; simp [workMemState]); rw [hdamp_eq, hclick_eq, hws0, quadForm_zero_vec,
      add_zero]; rcases deflatedRead_mulVec_workMemState_wd (m := m) hsub with ⟨hread_mul, hPR_inv⟩
    have hue := (unitaryEffect_wdPrepAndNoClick (Var := Var) (k := k) hp hm perm S active).2 kNext
    have hnoclick_vec :
        let W := m * (n + 1); let M := k * n; let fc := (lowBlock W M).embedMatrix (flagConj n m).1
        let orac := (lowBlock W M).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
        let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
        let phaseOp := fc * unm * orac * fc
        let diffOp := (lowBlock W M).embedMatrix (wdDiffuserUnitary (m := m) hp perm).1
        ((unm * orac) * ((diffOp * phaseOp) ^ kNext) * (unm * orac)) *ᵥ
            workMemState (P_R *ᵥ ξ t) (single μ 1) =
          workMemState (P_R *ᵥ ξ (t + kNext)) (single μ 1) := by
      intro W M fc orac unm phaseOp diffOp; dsimp only [W, M, fc, orac, unm, phaseOp, diffOp]
      have hiter_eq : (wdProdState fun j ↦ wdSlotWrap hp hm perm j ((fun ψ ↦ Grover.diffuserMatrix
        *ᵥ (oracleMat (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm)
        j) *ᵥ ψ))^[kNext] (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) t))) = ξ (t +
        kNext) := by
        dsimp only [ξ, R]; congr 1; funext j; congr 1; exact groverMultiState_iterate_wd _ t kNext
      rw [← mulVec_mulVec, ← mulVec_mulVec, hread_mul, hPR_inv, wdDeflatedGrover_iter_wdProdState hp
        hm perm hsub _ kNext, hiter_eq, hread_mul]
    have htot : wdTotalSteps (t + kNext) rest = wdTotalSteps t ((pyth, kNext) :: rest) :=
      (by simp [wdTotalSteps, Nat.add_assoc]); dsimp only [compile]; rw [wp_qSeq,
      quadForm_unitaryEffect hue, hnoclick_vec, ih (t + kNext), htot]
private lemma wp_wdDeflatedRound_of_finset {Var : Type} [DecidableEq Var] (res : Var) {n p m k
  active : ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤
  n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (kInit : ℕ)
  (probes : List (PythPair × ℕ)) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (hact : active < k)
  {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ) (Θ : CQAssertion (Store Var) (2 ^ (m *
    (n + 1)
  + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k * n))),
  s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν) (workMemIdx n m
  k 0 ν) = (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ)) (τ : Store Var) :
    let R := S \ memSeen n k (memPrefix k active) μ; let pref := fun x ↦ subcubePref hp hm (perm x)
    ((wp ((wdDeflatedRound res hm1 hkN hM hp hm perm active (k - active) kInit probes).compile
        qAssign (groverParallelMarkingOracle m S)) Θ) τ).1.1
        (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      if Set.InjOn pref (R : Set (Fin (2 ^ n))) then
        let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
        let u₀ := wdInitAmp R.card θ₁ kInit
        let uf := wdChainFinalAmp R.card θ₁ probes u₀
        ((wdChainClickProb R.card θ₁ probes u₀ * Ψ ∅ +
            ∑ B ∈ R.powerset, (uf B.card) ^ 2 * Ψ (R \ B) : ℝ) : ℂ)
      else
        ((∑ hit ∈ rotHitSupport pref R, (∏ j : Fin m,
              rotSlotHitProb (2 ^ (n - p)) (wdTotalSteps kInit probes)
                (R.filter fun x ↦ pref x = j) (hit j)) *
              Ψ (R \ rotHitFinset hit) : ℝ) : ℂ) := by
  dsimp only; set R := S \ memSeen n k (memPrefix k active) μ
  let pref := fun x ↦ subcubePref hp hm (perm x)
  have hseen := card_memSeen_of_memPrefixValid hval; have hadd : R.card + (memSeen n k (memPrefix k
    active) μ).card = S.card := Finset.card_sdiff_add_card_eq_card hseen.2; have hR_card : k -
    active = R.card := (by omega)
  have hμ : μ.val < 2 ^ (k * n - 1) := memPrefixValid_lt_half hn hk1 hval hact
  refine (quadForm_single _ (workMemIdx n m k 0 μ)).symm.trans ?_
  have hcomp :
      (wdDeflatedRound res hm1 hkN hM hp hm perm active (k - active) kInit probes).compile
          qAssign (groverParallelMarkingOracle m S) =
        (wdPrepAndLoop hp hm perm active kInit).compile qAssign (groverParallelMarkingOracle m S) ;;
          (wdProbeChain res hm1 hkN hM hp perm active R.card probes).compile
            qAssign (groverParallelMarkingOracle m S) := by
    rw [wdDeflatedRound, hR_card]; rfl
  have hue := (unitaryEffect_wdPrepAndNoClick (Var := Var) (k := k) hp hm perm S active).1 kInit
  rw [hcomp, wp_qSeq, quadForm_unitaryEffect hue]; rcases deflatedRead_mulVec_workMemState_wd (m :=
    m) hseen.2 with ⟨hread_mul, _⟩; by_cases hInj : Set.InjOn pref (R : Set (Fin (2 ^ n)))
  · rw [ite_eq_left hInj, ← mulVec_mulVec, ← mulVec_mulVec, wdPrep_grover_eq_wdAmpState hp hm hsub2
      perm hseen.2 hInj kInit, hread_mul]
    exact quadForm_wp_wdProbeChain_inj res hm1 hkN hM hp hm hsub2 perm hcard hval hμ hInj Θ Ψ hΘ
      probes _ τ
  · have hhad_eq : (wdProdState fun j ↦ wdSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0
      1)) = wdProdState fun j ↦ wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm
      (R.image perm) j) 0) :=
      (by congr 1; funext j; congr 1; exact (groverMultiState_zero_eq_hadamard_mulVec _).symm)
    have hiter_eq : (wdProdState fun j ↦ wdSlotWrap hp hm perm j ((fun ψ ↦ Grover.diffuserMatrix *ᵥ
      (oracleMat (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm) j) *ᵥ
      ψ))^[kInit] (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) 0))) = wdProdState fun
      j ↦ wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) kInit)
      := by
      dsimp only [R]; congr 1; funext j; congr 1
      simpa using groverMultiState_iterate_wd (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k
        active) μ).image perm) j) 0 kInit
    rw [ite_eq_right hInj, ← mulVec_mulVec, ← mulVec_mulVec, wdPrepUnitary_mulVec_workMemIdx hp hm
      perm μ, hhad_eq, wdDeflatedGrover_iter_wdProdState hp hm perm hseen.2 _ kInit, hiter_eq,
      hread_mul]
    exact quadForm_wp_wdProbeChain_notInj res hm1 hkN hM hp hm perm hcard hval hμ hInj Θ Ψ hΘ probes
      kInit τ
private lemma wp_wdOptSweep_of_finset {Var : Type} [DecidableEq Var] (res : Var) {n p m k active :
  ℕ} (hn : 1 ≤ n) (hk1 : 1 ≤ k) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm :
  m = 2 ^ p) (hsub2 : 2 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (sched : ℕ → Option (ℕ ×
  List (PythPair × ℕ))) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (hact : active ≤ k) {τ :
  Store Var} (hτ : τ res = (active : ℤ)) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
  (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀
    (s : ℕ)
  (τ' : Store Var) (ν : Fin (2 ^ (k * n))), s ≤ k → τ' res = (s : ℤ) → MemPrefixValid S s ν → (Θ
  τ').1.1 (workMemIdx n m k 0 ν) (workMemIdx n m k 0 ν) = (Ψ (S \ memSeen n k (memPrefix k s) ν) :
  ℂ)) : ((wp ((wdOptSweep res hm1 hkN hM hp hm perm sched).compile qAssign
  (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
  (wdSubsetStep (n - p) (fun x ↦ subcubePref hp hm (perm x)) false sched Ψ (S \ memSeen n k
  (memPrefix k active) μ) : ℂ) := by
  classical
  set R := S \ memSeen n k (memPrefix k active) μ; have hseen := card_memSeen_of_memPrefixValid hval
  have hadd : R.card + (memSeen n k (memPrefix k active) μ).card = S.card :=
    Finset.card_sdiff_add_card_eq_card hseen.2; rcases eq_or_lt_of_le hact with hact_eq | hlt
  · have hr0 : R.card = 0 := (by omega); unfold wdOptSweep wdSubsetStep; rw [wp_dispFin_wd_of_ge res
      _ _ Θ (by omega) hτ, ite_eq_left hr0]; exact hΘ active τ μ hact hτ hval
  · have hr_eq : R.card = k - active := (by omega); have hr_ne : R.card ≠ 0 := (by omega)
    unfold wdOptSweep wdSubsetStep; rw [wp_dispFin_wd_of_lt res _ _ Θ hlt hτ, ite_eq_right hr_ne]
    dsimp only
    cases hsc : sched (k - active) with
    | none =>
      have hscR : sched R.card = none := hr_eq.symm ▸ hsc; rw [hscR]
      dsimp only [compile, R]; exact hΘ active τ μ hact hτ hval
    | some kp =>
      rcases kp with ⟨kInit, probes⟩
      have hscR : sched R.card = some (kInit, probes) := hr_eq.symm ▸ hsc; rw [hscR]
      dsimp only [R]; simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [wp_wdDeflatedRound_of_finset res hn hk1 hm1 hkN hM hp hm hsub2 perm kInit probes hcard hlt
        hval Θ Ψ hΘ τ]; dsimp only
      by_cases hInj : Set.InjOn (fun x ↦ subcubePref hp hm (perm x)) ((S \ memSeen n k (memPrefix k
        active) μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n)))
      · rw [ite_eq_left hInj, ite_eq_left hInj]
      · rw [ite_eq_right hInj, ite_eq_right hInj]
lemma wp_wdSweeps_of_finset {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hn : 1 ≤ n)
  (hk1 : 1 ≤ k) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
  (hsub2 : 2 ≤ 2 ^ (n - p)) (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → Option (ℕ × List
  (PythPair × ℕ))))) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (Θ : CQAssertion (Store Var) (2
    ^ (m *
  (n + 1) + k * n))) (Ψ : Finset (Fin (2 ^ n)) → ℝ) (hΘ : ∀ (s : ℕ) (τ : Store Var) (ν : Fin (2 ^ (k
  * n))), s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s ν → (Θ τ).1.1 (workMemIdx n m k 0 ν)
  (workMemIdx n m k 0 ν) = (Ψ (S \ memSeen n k (memPrefix k s) ν) : ℂ)) {active : ℕ} (hact : active
  ≤ k) {τ : Store Var} (hτ : τ res = (active : ℤ)) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S
  active μ) : ((wp ((wdSweeps res hm1 hkN hM hp hm passes).compile qAssign
  (groverParallelMarkingOracle m S)) Θ) τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
  (wdCircDP hp hm false passes Ψ (S \ memSeen n k (memPrefix k active) μ) : ℂ) := by
  induction passes generalizing active τ μ with
  | nil => exact hΘ active τ μ hact hτ hval
  | cons ps rest ih =>
    rcases ps with ⟨perm, sched⟩; dsimp only [wdSweeps, wdCircDP, compile]; rw [wp_qSeq]
    exact wp_wdOptSweep_of_finset res hn hk1 hm1 hkN hM hp hm hsub2 perm sched hcard hact hτ hval
      (wp ((wdSweeps res hm1 hkN hM hp hm rest).compile qAssign (groverParallelMarkingOracle m S))
      Θ) (wdCircDP hp hm false rest Ψ) (fun s τ' ν hs hτ' hval' ↦ ih hs hτ' hval')
private lemma wdSubsetStep_true_eq_cost_add_false {α : Type*} [DecidableEq α] {m : ℕ} (subN : ℕ)
  (pref : α → Fin m) (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) (Ψ : Finset α → ℝ) (R : Finset
  α) : wdSubsetStep subN pref true sched Ψ R = wdSubsetStep subN pref true sched (fun _ ↦ 0) R +
  wdSubsetStep subN pref false sched Ψ R := by
  classical
  unfold wdSubsetStep; by_cases hr0 : R.card = 0
  · simp [hr0]
  · rw [ite_eq_right hr0, ite_eq_right hr0, ite_eq_right hr0]
    cases sched R.card with
    | none => simp
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; dsimp only; by_cases hInj : Set.InjOn pref (R : Set α)
      · simp only [ite_eq_left hInj, ↓reduceIte, Bool.false_eq_true, mul_zero,
          Finset.sum_const_zero]; ring
      · simp only [ite_eq_right hInj, ↓reduceIte, Bool.false_eq_true, mul_zero,
          Finset.sum_const_zero]; ring
lemma wdCircDP_true_eq_cost_add_false {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) (passes : List
  (Equiv.Perm (Fin (2 ^ n)) × (ℕ → Option (ℕ × List (PythPair × ℕ))))) (Ψ : Finset (Fin (2 ^ n)) →
  ℝ) (R : Finset (Fin (2 ^ n))) : wdCircDP hp hm true passes Ψ R = wdCircDP hp hm true passes (fun _
  ↦ 0) R + wdCircDP hp hm false passes Ψ R := by
  induction passes generalizing R with
  | nil => simp [wdCircDP]
  | cons ps rest ih =>
    rcases ps with ⟨perm, sched⟩; dsimp only [wdCircDP]; have hfun : wdCircDP hp hm true rest Ψ =
      fun R' ↦ wdCircDP hp hm true rest (fun _ ↦ 0) R' + wdCircDP hp hm false rest Ψ R' := funext ih
    have hadd_step (A B : Finset (Fin (2 ^ n)) → ℝ) : wdSubsetStep (n - p) (fun x ↦ subcubePref hp
      hm (perm x)) false sched (fun R' ↦ A R' + B R') R = wdSubsetStep (n - p) (fun x ↦ subcubePref
      hp hm (perm x)) false sched A R + wdSubsetStep (n - p) (fun x ↦ subcubePref hp hm (perm x))
      false sched B R := by
      have hs := wdCircDP_false_sum hp hm [(perm, sched)] ({false, true} : Finset Bool) (fun b R' ↦
        if b then B R' else A R') R; simpa [wdCircDP, add_comm] using hs
    rw [hfun, wdSubsetStep_true_eq_cost_add_false, hadd_step, ← add_assoc, ←
      wdSubsetStep_true_eq_cost_add_false]
private lemma cqAssertion_add_mat {Var : Type} {d : ℕ} (θ₁ θ₂ : CQAssertion (Store Var) d) (h : ∀ σ,
    (θ₁
  σ).1 + (θ₂ σ).1 ≤ 1) (σ : Store Var) : ((θ₁.add θ₂ h) σ).1.1 = (θ₁ σ).1.1 + (θ₂ σ).1.1 := by
  simp only [HermitianMat.val_eq_coe, CQAssertion.add_apply, Observable.add_coe,
    HermitianMat.mat_add]
private lemma ScaledCostRel.mono_c {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) {P : QProg Var d} {θ : CQAssertion (Store Var) d} {c₁ c₂ : ℝ} (h
    :
  ScaledCostRel model B P θ c₁) (hc : c₁ ≤ c₂) (hcB : c₂ ≤ B) : ScaledCostRel model B P θ c₂ :=
  ⟨h.1.trans hc, hcB, h.2.2.1.trans
      (wd_constAssertion_mono (div_nonneg h.1 hB.le) ((div_le_one hB).mpr hcB)
        (div_le_div_of_nonneg_right hc hB.le)),
    h.2.2.2⟩
private lemma ScaledCostRel.seq_zero_left {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model :
  CostModel d} {B : ℝ} (hB : 0 < B) {P₁ P₂ : QProg Var d} {θ₂ : CQAssertion (Store Var) d} {c₂ : ℝ}
    (h₁ :
  CostBound (Var := Var) model P₁ 0) (h₂ : ScaledCostRel model B P₂ θ₂ c₂) : ScaledCostRel model B
  (P₁ ;; P₂) (wp P₁ θ₂) c₂ := by
  refine ⟨h₂.1, h₂.2.1, (wp_mono P₁ h₂.2.2.1).trans (wd_wp_constAssertion_le P₁ (div_nonneg h₂.1
    hB.le) ((div_le_one hB).mpr h₂.2.1)), fun Δ ↦ ?_⟩; have h0 := h₁ Δ; simp only [ENNReal.coe_zero,
    mul_zero, nonpos_iff_eq_zero] at h0; rw [expectedCost_qSeq, h0, zero_add]; exact (h₂.2.2.2
    ((interp P₁).toStateFun Δ)).trans_eq (by rw [wp_expectation_eq])
private lemma quadForm_constAssertion_workMemState {Var : Type} {W M : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1
  : α ≤ 1) (τ : Store Var) (ξ : Fin (2 ^ W) → ℂ) (μ : Fin (2 ^ M)) : quadForm ((constAssertion α :
  CQAssertion (Store Var) (2 ^ (W + M))) τ).1.1 (workMemState ξ (single μ 1)) = (α : ℂ) * ∑ w : Fin
    (2 ^ W),
  (normSq (ξ w) : ℂ) := by
  have hmat : ((constAssertion α : CQAssertion (Store Var) (2 ^ (W + M))) τ).1.1 = (α : ℂ) • (1 :
    Matrix
    (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ) := by
    rw [HermitianMat.val_eq_coe, constAssertion_apply_of_bounds α hα0 hα1, HermitianMat.mat_smul,
      HermitianMat.mat_one]; ext i j; simp [Complex.real_smul]
  rw [hmat]; unfold quadForm; rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]; congr 1; rw [dotProduct]
  let f (z : Fin (2 ^ (W + M))) : ℂ := star (workMemState ξ (single μ 1) z) * workMemState ξ (single
    μ 1) z; change ∑ z, f z = _; rw [← (lowHighEquiv W M).symm.sum_comp f, sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [sum_eq_single μ (fun ν hν ↦ by
    dsimp only [f, workMemState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hν, mul_zero, mul_zero])]
  dsimp only [f, workMemState]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one,
    RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
private def wdProbesMaxQ (probes : List (PythPair × ℕ)) : ℕ :=
  (probes.map fun pk ↦ pk.2 + 2).sum
def wdRoundMaxQ : Option (ℕ × List (PythPair × ℕ)) → ℕ
  | none => 0
  | some (kInit, probes) => wdMaxQueries kInit probes
private lemma scaledCostRel_wdProbeChain {Var : Type} [DecidableEq Var] (res : Var) {n p m k active
  : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2
  ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) (probes : List (PythPair ×
  ℕ)) {B : ℝ} (hB : 0 < B) (hcB : (wdProbesMaxQ probes : ℝ) ≤ B) :
    let R := fun μ ↦ S \ memSeen n k (memPrefix k active) μ
    let P_R := fun μ ↦ (permutationUnitary (parallelMarkPerm n m (R μ))).1
    let pref := fun x ↦ subcubePref hp hm (perm x); let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
    ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)), ScaledCostRel
      (CostModel.ofEmbeddedOracle
      (groverParallelMarkingOracle m S)) B ((wdProbeChain res hm1 hkN hM hp perm active (k - active)
      probes).compile qAssign (groverParallelMarkingOracle m S)) θ (wdProbesMaxQ probes) ∧ (∀ (μ :
      Fin (2 ^ (k * n))) (σ : Store Var), S.card = k → active < k → MemPrefixValid S active μ →
      Set.InjOn pref ((R μ : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))) → ∀ u : ℕ → ℝ, quadForm (θ
      σ).1.1 (workMemState (P_R μ *ᵥ wdAmpState hp hm perm (R μ) u) (single μ 1)) =
      ((wdChainExtraQueries (R μ).card θ₁ probes u / B : ℝ) : ℂ)) ∧ (∀ (μ : Fin (2 ^ (k * n))) (σ :
      Store Var), S.card = k → active < k → MemPrefixValid S active μ → ¬ Set.InjOn pref ((R μ :
      Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))) → ∀ t : ℕ, quadForm (θ σ).1.1 (workMemState (P_R μ
      *ᵥ wdProdState (fun j ↦ wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm ((R
      μ).image perm) j) t))) (single μ 1)) = (((wdProbesMaxQ probes : ℝ) / B : ℝ) : ℂ)) := by
  intro R P_R pref θ₁; let W := m * (n + 1); let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  rcases costBounds_wdPieces (Var := Var) res hm1 hkN hM hp hm perm S active with ⟨_, hcb_noclick,
    hcb_rw, hcb_click⟩
  induction probes with
  | nil =>
    refine ⟨⊥, (ScaledCostRel.of_zero hB hcb_rw).mono_c hB (by simp [wdProbesMaxQ]) hcB, ?_, ?_⟩
    · intro μ σ _ _ _ _ u; dsimp only [wdChainExtraQueries, wdProbesMaxQ]; change quadForm 0 _ = _;
        rw [quadForm_zero_mat]; simp
    · intro μ σ _ _ _ _ t; dsimp only [wdProbesMaxQ, List.map_nil, List.sum_nil]
      change quadForm 0 _ = _; rw [quadForm_zero_mat]; simp
  | cons pk rest ih =>
    rcases pk with ⟨pyth, kNext⟩
    have hfin2 (f : Fin (2 ^ 1) → ℂ) : (∑ o : Fin (2 ^ 1), f o) = f 0 + f 1 := Fin.sum_univ_two f
    have hc_eq : (wdProbesMaxQ ((pyth, kNext) :: rest) : ℝ) = (kNext : ℝ) + 2 + (wdProbesMaxQ rest :
      ℝ) := (by simp [wdProbesMaxQ]); have hc_rest_le : (wdProbesMaxQ rest : ℝ) ≤ B :=
      (by have : (0 : ℝ) ≤ (kNext : ℝ) + 2 := (by positivity); linarith); rcases ih hc_rest_le with
      ⟨θ_rest, hrel_rest, hinj_rest, hnot_rest⟩
    have hcb_step : CostBound (Var := Var) model (.qAssign (phaseTag (weakAllHitUnitary n m M hM (k
      - active) pyth))) 0 := costBound_qAssign_phaseTag (Var := Var) hor _
    have hcb_meas : CostBound (Var := Var) model (measureRegister res (topAncReg W M hM)) 0 := by
      simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using CostBound.qMeasure (Var :=
        Var) model res ((topAncReg W M hM).computationalBasisMeasurement : Measurement (2 ^ (W + M))
        (2 ^ 1))
    have hkNext_le : (((kNext + 2 : ℕ) : ℝ≥0) : ℝ) ≤ B :=
      (by have : (0 : ℝ) ≤ (wdProbesMaxQ rest : ℝ) := Nat.cast_nonneg _; push_cast; linarith)
    have hrel_nc0 := ScaledCostRel.of_costBound hB (k_cost := (kNext + 2 : ℕ))
      (by simpa [Nat.cast_add] using hcb_noclick kNext) hkNext_le; have hsum_le : (((kNext + 2 : ℕ)
      : ℝ≥0) : ℝ) + (wdProbesMaxQ rest : ℝ) ≤ B := (by push_cast; linarith); have hrel_false :=
      ScaledCostRel.seq hB hrel_nc0 hrel_rest hsum_le
    have hrel_true := ScaledCostRel.of_zero hB hcb_click; have hmax_eq : max (0 : ℝ) ((((kNext + 2 :
      ℕ) : ℝ≥0) : ℝ) + (wdProbesMaxQ rest : ℝ)) = (wdProbesMaxQ ((pyth, kNext) :: rest) : ℝ) :=
      (by rw [max_eq_right (by positivity)]; push_cast; linarith)
    have hrel_if := (ScaledCostRel.qIf hB (fun τ ↦ τ res = 1) hrel_true hrel_false).mono_c hB
      (le_of_eq hmax_eq) hcB
    have hrel_tot := ScaledCostRel.seq_zero_left hB hcb_step (ScaledCostRel.seq_zero_left hB
      hcb_meas hrel_if); refine ⟨_, hrel_tot, ?_, ?_⟩
    · intro μ σ hcard hact hval hInj u
      have hn : 1 ≤ n := by
        by_contra! hn0
        have hn_eq : n = 0 := (by omega); have hp_eq : p = 0 := (by omega); subst hn_eq hp_eq; omega
      have hk1 : 1 ≤ k := (by omega)
      have hμ : μ.val < 2 ^ (k * n - 1) := memPrefixValid_lt_half hn hk1 hval hact; have hseen :=
        card_memSeen_of_memPrefixValid hval; have hadd := Finset.card_sdiff_add_card_eq_card hseen.2
      have hR_card : k - active = (R μ).card := (by dsimp only [R]; omega)
      have hstep_vec : (weakAllHitUnitary n m M hM (k - active) pyth).1 *ᵥ workMemState (P_R μ *ᵥ
        wdAmpState hp hm perm (R μ) u) (single μ 1) = workMemState (wdDampVec n m (R μ).card
        pyth.cVal (P_R μ *ᵥ wdAmpState hp hm perm (R μ) u)) (single μ 1) + workMemState (wdClickVec
        n m (R μ).card pyth.sVal (P_R μ *ᵥ wdAmpState hp hm perm (R μ) u)) (single (memWithTopOne hM
        μ hμ) 1) := by
        change weakAllHitMat n m M hM (k - active) pyth *ᵥ _ = _; rw [hR_card]
        exact weakAllHitMat_mulVec_workMemState hM (R μ).card pyth _ hμ
      rw [quadForm_unitaryEffect (unitaryEffect_phaseTag _), hstep_vec, quadForm_wp_measureRegister,
        hfin2]; have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) res ≠ 1 :=
        (by simp [Store.subst])
      have hs1 : (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) res = 1 :=
        (by simp [Store.subst]); rw [topAncReg_projector_zero_mulVec hM _ _ hμ,
        topAncReg_projector_one_mulVec hM _ _ hμ, ite_eq_right hs0, ite_eq_left hs1]
      have hzero1 : quadForm ((⊥ : CQAssertion (Store Var) (2 ^ (W + M))) (Store.subst σ res
        (Int.ofNat (1 :
        Fin (2 ^ 1)).val))).1.1 (workMemState (wdClickVec n m (R μ).card pyth.sVal (P_R μ *ᵥ
        wdAmpState hp hm perm (R μ) u)) (single (memWithTopOne hM μ hμ) 1)) = 0 := quadForm_zero_mat
        _; rw [hzero1, add_zero]
      rcases wdDamp_and_click_marked_wdAmpState hp hm perm hInj pyth u with ⟨hdamp, _⟩; rw [hdamp,
        cqAssertion_add_mat, quadForm_add_mat]
      have hdiv0 : 0 ≤ (((kNext + 2 : ℕ) : ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le
      have hdiv1 : (((kNext + 2 : ℕ) : ℝ≥0) : ℝ) / B ≤ 1 := (div_le_one hB).mpr hkNext_le
      rw [quadForm_constAssertion_workMemState hdiv0 hdiv1]
      have hnorm_damp : (∑ o : Fin (2 ^ W), (normSq ((P_R μ *ᵥ wdAmpState hp hm perm (R μ)
        (wdDampAmp (R μ).card pyth u)) o) : ℂ)) = ((∑ w ∈ Finset.range ((R μ).card + 1), ((R
        μ).card.choose w : ℝ) * (wdDampAmp (R μ).card pyth u w) ^ 2 : ℝ) : ℂ) := by
        have h1 := sum_normSq_wdAmpState_mul_card hp hm hsub2 perm hInj (wdDampAmp (R μ).card pyth
          u) (fun _ ↦ 1); simp only [mul_one] at h1; dsimp only [P_R]
        simp_rw [permUnitary_parallelMarkPerm_mulVec_apply_wd]; rw [h1]; push_cast; rfl
      rcases deflatedRead_mulVec_workMemState_wd (m := m) hseen.2 with ⟨hread_mul, hPR_inv⟩
      have hue := (unitaryEffect_wdPrepAndNoClick (Var := Var) (k := k) hp hm perm S active).2 kNext
      rw [hnorm_damp, quadForm_unitaryEffect hue, ← mulVec_mulVec, ← mulVec_mulVec, hread_mul,
        hPR_inv, wdGrover_iter_wdAmpState hp hm hsub2 perm hseen.2 hInj _ kNext, hread_mul,
        hinj_rest μ _ hcard hact hval hInj]; dsimp only [wdChainExtraQueries]; push_cast; ring
    · intro μ σ hcard hact hval hNotInj t
      have hn : 1 ≤ n := by
        by_contra! hn0
        have hn_eq : n = 0 := (by omega); have hp_eq : p = 0 := (by omega); subst hn_eq hp_eq; omega
      have hk1 : 1 ≤ k := (by omega)
      have hμ : μ.val < 2 ^ (k * n - 1) := memPrefixValid_lt_half hn hk1 hval hact; have hseen :=
        card_memSeen_of_memPrefixValid hval; have hadd := Finset.card_sdiff_add_card_eq_card hseen.2
      have hR_card : k - active = (R μ).card := (by dsimp only [R]; omega)
      let ξ (steps : ℕ) := wdProdState (fun j ↦ wdSlotWrap hp hm perm j
        (groverMultiState (subcubeLocalSet hp hm ((R μ).image perm) j) steps))
      have hstep_vec : (weakAllHitUnitary n m M hM (k - active) pyth).1 *ᵥ workMemState (P_R μ *ᵥ ξ
        t) (single μ 1) = workMemState (wdDampVec n m (R μ).card pyth.cVal (P_R μ *ᵥ ξ t)) (single μ
        1) + workMemState (wdClickVec n m (R μ).card pyth.sVal (P_R μ *ᵥ ξ t)) (single
        (memWithTopOne hM μ hμ) 1) := by
        change weakAllHitMat n m M hM (k - active) pyth *ᵥ _ = _; rw [hR_card]
        exact weakAllHitMat_mulVec_workMemState hM (R μ).card pyth _ hμ
      rw [quadForm_unitaryEffect (unitaryEffect_phaseTag _), hstep_vec, quadForm_wp_measureRegister,
        hfin2]; have hs0 : (Store.subst σ res (Int.ofNat (0 : Fin (2 ^ 1)).val)) res ≠ 1 :=
        (by simp [Store.subst])
      have hs1 : (Store.subst σ res (Int.ofNat (1 : Fin (2 ^ 1)).val)) res = 1 :=
        (by simp [Store.subst]); rw [topAncReg_projector_zero_mulVec hM _ _ hμ,
        topAncReg_projector_one_mulVec hM _ _ hμ, ite_eq_right hs0, ite_eq_left hs1]
      have hzero1 : quadForm ((⊥ : CQAssertion (Store Var) (2 ^ (W + M))) (Store.subst σ res
        (Int.ofNat (1 :
        Fin (2 ^ 1)).val))).1.1 (workMemState (wdClickVec n m (R μ).card pyth.sVal (P_R μ *ᵥ ξ t))
        (single (memWithTopOne hM μ hμ) 1)) = 0 := quadForm_zero_mat _; rw [hzero1, add_zero]
      have hdamp_eq : wdDampVec n m (R μ).card pyth.cVal (P_R μ *ᵥ ξ t) = P_R μ *ᵥ ξ t := by
        funext o; dsimp only [wdDampVec]; by_cases hnz : (P_R μ *ᵥ ξ t) o = 0
        · simp [hnz]
        · have hnz' : ξ t (parallelMarkPerm n m (R μ) o) ≠ 0 :=
            (by rwa [permUnitary_parallelMarkPerm_mulVec_apply_wd] at hnz)
          exact ite_eq_right (ne_of_lt (wdHitCount_lt_of_not_injOn hp hm perm hNotInj t o hnz'))
      rw [hdamp_eq, cqAssertion_add_mat, quadForm_add_mat]; have hdiv0 : 0 ≤ (((kNext + 2 : ℕ) :
        ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le; have hdiv1 : (((kNext + 2 : ℕ) : ℝ≥0) :
        ℝ) / B ≤ 1 := (div_le_one hB).mpr hkNext_le; rw [quadForm_constAssertion_workMemState hdiv0
        hdiv1]
      have hnorm1 : (∑ o : Fin (2 ^ W), (normSq ((P_R μ *ᵥ ξ t) o) : ℂ)) = 1 := by
        dsimp only [P_R]; simp_rw [permUnitary_parallelMarkPerm_mulVec_apply_wd]; rw [←
          Complex.ofReal_sum, Equiv.sum_comp (parallelMarkPerm n m (R μ)) (fun w ↦ normSq (ξ t w)),
          sum_normSq_wdProdState]
        have h1 : (∏ j : Fin m, ∑ z : Fin (2 ^ (1 * (n + 1))), normSq (wdSlotWrap hp hm perm j
          (groverMultiState (subcubeLocalSet hp hm ((R μ).image perm) j) t) z)) = 1 :=
          Finset.prod_eq_one fun j _ ↦ sum_normSq_wdSlotWrap hp hm perm j _
          (sum_normSq_groverMultiState_eq_one _ _); rw [h1, Complex.ofReal_one]
      rcases deflatedRead_mulVec_workMemState_wd (m := m) hseen.2 with ⟨hread_mul, hPR_inv⟩
      have hue := (unitaryEffect_wdPrepAndNoClick (Var := Var) (k := k) hp hm perm S active).2 kNext
      have hiter_eq : (wdProdState fun j ↦ wdSlotWrap hp hm perm j ((fun ψ ↦ Grover.diffuserMatrix
        *ᵥ (oracleMat (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm)
        j) *ᵥ ψ))^[kNext] (groverMultiState (subcubeLocalSet hp hm ((R μ).image perm) j) t))) = ξ (t
        + kNext) := by
        dsimp only [ξ, R]; congr 1; funext j; congr 1; exact groverMultiState_iterate_wd _ t kNext
      rw [hnorm1, mul_one, quadForm_unitaryEffect hue, ← mulVec_mulVec, ← mulVec_mulVec, hread_mul,
        hPR_inv, wdDeflatedGrover_iter_wdProdState hp hm perm hseen.2 _ kNext, hiter_eq, hread_mul,
        hnot_rest μ _ hcard hact hval hNotInj (t + kNext), hc_eq]; push_cast; ring
private lemma scaledCostRel_wdDeflatedRound {Var : Type} [DecidableEq Var] (res : Var) {n p m k
    active : ℕ} (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
    (hsub2 : 2 ≤ 2 ^ (n - p)) (perm : Equiv.Perm (Fin (2 ^ n))) (S : Finset (Fin (2 ^ n))) (kInit :
    ℕ) (probes : List (PythPair × ℕ)) {B : ℝ} (hB : 0 < B) (hcB : (wdMaxQueries kInit probes : ℝ) ≤
    B) : ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)), ScaledCostRel
    (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B ((wdDeflatedRound res hm1 hkN
    hM hp hm perm active (k - active) kInit probes).compile qAssign (groverParallelMarkingOracle m
    S)) θ (wdMaxQueries kInit probes) ∧ (∀ (μ : Fin (2 ^ (k * n))) (τ : Store Var), S.card = k →
    active < k → MemPrefixValid S active μ → (θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ)
    =
            let R := S \ memSeen n k (memPrefix k active) μ
            let pref := fun x ↦ subcubePref hp hm (perm x)
            if Set.InjOn pref (R : Set (Fin (2 ^ n))) then
              let θ₁ := Real.arcsin (1 / √(2 ^ (n - p) : ℝ))
              let u₀ := wdInitAmp R.card θ₁ kInit
              ((((kInit + 1 : ℕ) : ℝ) + wdChainExtraQueries R.card θ₁ probes u₀) / B : ℂ)
            else
              ((wdMaxQueries kInit probes : ℝ) / B : ℂ)) := by
  have hmax_eq : (wdMaxQueries kInit probes : ℝ) = (kInit : ℝ) + 1 + (wdProbesMaxQ probes : ℝ) :=
    (by unfold wdMaxQueries wdProbesMaxQ; push_cast; ring); have hc_probes : (wdProbesMaxQ probes :
    ℝ) ≤ B := (by have : (0 : ℝ) ≤ (kInit : ℝ) + 1 := (by positivity); linarith)
  have hc_init : (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) ≤ B :=
    (by have : (0 : ℝ) ≤ (wdProbesMaxQ probes : ℝ) := Nat.cast_nonneg _; push_cast; linarith)
  rcases scaledCostRel_wdProbeChain (Var := Var) res hm1 hkN hM hp hm hsub2 perm S probes hB
    hc_probes with ⟨θ_ch, hrel_ch, hinj_ch, hnot_ch⟩
  rcases costBounds_wdPieces (Var := Var) res hm1 hkN hM hp hm perm S active with ⟨hcb_prep, _, _,
    _⟩
  have hrel_prep := ScaledCostRel.of_costBound hB (k_cost := (kInit + 1 : ℕ))
    (by simpa [Nat.cast_add] using hcb_prep kInit) hc_init; have hsum_le : (((kInit + 1 : ℕ) : ℝ≥0)
    : ℝ) + (wdProbesMaxQ probes : ℝ) ≤ B := (by push_cast; linarith)
  have hrel_tot := (ScaledCostRel.seq hB hrel_prep hrel_ch hsum_le).mono_c hB (le_of_eq
    (by push_cast; linarith)) hcB; refine ⟨_, hrel_tot, fun μ τ hcard hact hval ↦ ?_⟩
  refine (quadForm_single _ (workMemIdx n m k 0 μ)).symm.trans ?_; rw [cqAssertion_add_mat,
    quadForm_add_mat]
  have hdiv0 : 0 ≤ (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B := div_nonneg (by positivity) hB.le
  have hdiv1 : (((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B ≤ 1 := (div_le_one hB).mpr hc_init
  have hq_const : quadForm ((constAssertion ((((kInit + 1 : ℕ) : ℝ≥0) : ℝ) / B) : CQAssertion (Store
    Var) (2
    ^ (m * (n + 1) + k * n))) τ).1.1 (single (workMemIdx n m k 0 μ) 1) = (((kInit + 1 : ℕ) : ℝ) / B
    : ℂ) := by
    rw [workMemIdx, ← workMemState_single, quadForm_constAssertion_workMemState hdiv0 hdiv1,
      sum_eq_single 0 (fun w hw ↦ by rw [Pi.single_eq_of_ne hw, Complex.normSq_zero,
      Complex.ofReal_zero]), Pi.single_eq_same, Complex.normSq_one]; push_cast; ring
  rw [hq_const]; have hseen := card_memSeen_of_memPrefixValid hval
  rcases deflatedRead_mulVec_workMemState_wd (m := m) hseen.2 with ⟨hread_mul, _⟩; have hue :=
    (unitaryEffect_wdPrepAndNoClick (Var := Var) (k := k) hp hm perm S active).1 kInit
  rw [quadForm_unitaryEffect hue]; set R := S \ memSeen n k (memPrefix k active) μ
  let pref := fun x ↦ subcubePref hp hm (perm x)
  by_cases hInj : Set.InjOn pref (R : Set (Fin (2 ^ n)))
  · rw [ite_eq_left hInj, ← mulVec_mulVec, ← mulVec_mulVec, wdPrep_grover_eq_wdAmpState hp hm hsub2
      perm hseen.2 hInj kInit, hread_mul, hinj_ch μ τ hcard hact hval hInj]; push_cast; ring
  · have hhad_eq : (wdProdState fun j ↦ wdSlotWrap hp hm perm j (hadamardMatrix (n - p) *ᵥ single 0
      1)) = wdProdState fun j ↦ wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm
      (R.image perm) j) 0) :=
      (by congr 1; funext j; congr 1; exact (groverMultiState_zero_eq_hadamard_mulVec _).symm)
    have hiter_eq : (wdProdState fun j ↦ wdSlotWrap hp hm perm j ((fun ψ ↦ Grover.diffuserMatrix *ᵥ
      (oracleMat (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k active) μ).image perm) j) *ᵥ
      ψ))^[kInit] (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) 0))) = wdProdState fun
      j ↦ wdSlotWrap hp hm perm j (groverMultiState (subcubeLocalSet hp hm (R.image perm) j) kInit)
      := by
      dsimp only [R]; congr 1; funext j; congr 1
      simpa using groverMultiState_iterate_wd (subcubeLocalSet hp hm ((S \ memSeen n k (memPrefix k
        active) μ).image perm) j) 0 kInit
    rw [ite_eq_right hInj, ← mulVec_mulVec, ← mulVec_mulVec, wdPrepUnitary_mulVec_workMemIdx hp hm
      perm μ, hhad_eq, wdDeflatedGrover_iter_wdProdState hp hm perm hseen.2 _ kInit, hiter_eq,
      hread_mul, hnot_ch μ τ hcard hact hval hInj kInit, hmax_eq]; push_cast; ring
private lemma scaledCostRel_wdOptSweep {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hm1
  : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p) (hsub2 : 2 ≤ 2 ^ (n -
  p)) (perm : Equiv.Perm (Fin (2 ^ n))) (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) (S : Finset
  (Fin (2 ^ n))) {c_sweep B : ℝ} (hc0 : 0 ≤ c_sweep) (hB : 0 < B) (hcB : c_sweep ≤ B) (hsched_le : ∀
  s : Fin k, (wdRoundMaxQ (sched (k - s.val)) : ℝ) ≤ c_sweep) : ∃ θ : CQAssertion (Store Var) (2 ^
    (m * (n +
  1) + k * n)), ScaledCostRel (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B
  ((wdOptSweep res hm1 hkN hM hp hm perm sched).compile qAssign (groverParallelMarkingOracle m S)) θ
  c_sweep ∧ (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))), S.card = k → s ≤ k → τ res = (s : ℤ)
  → MemPrefixValid S s μ → (θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = ((wdSubsetStep
  (n - p) (fun x ↦ subcubePref hp hm (perm x)) true sched (fun _ ↦ 0) (S \ memSeen n k (memPrefix k
  s) μ) / B : ℝ) : ℂ)) := by
  classical
  let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  let br (x : Fin k) : OracleCirc Var (W + M) ((n + 1) * m) :=
    match sched (k - x.val) with
    | none => .skip
    | some (kInit, probes) =>
        wdDeflatedRound res hm1 hkN hM hp hm perm x.val (k - x.val) kInit probes
  have hbr_ex (x : Fin k) : ∃ θ_x : CQAssertion (Store Var) (2 ^ (W + M)), ScaledCostRel model B
    ((br
    x).compile qAssign oracle) θ_x c_sweep ∧ (∀ (τ : Store Var) (μ : Fin (2 ^ M)), S.card = k →
    MemPrefixValid S x.val μ → (θ_x τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
    ((wdSubsetStep (n - p) (fun z ↦ subcubePref hp hm (perm z)) true sched (fun _ ↦ 0) (S \ memSeen
    n k (memPrefix k x.val) μ) / B : ℝ) : ℂ)) := by
    dsimp only [br]; have hx_le := hsched_le x
    cases hsc : sched (k - x.val) with
    | none =>
      refine ⟨⊥, (ScaledCostRel.of_zero hB (CostBound.skip_zero model)).mono_c hB hc0 hcB, fun τ μ
        hcard hval ↦ ?_⟩; have hseen := card_memSeen_of_memPrefixValid hval; have hadd :=
        Finset.card_sdiff_add_card_eq_card hseen.2; have hr_eq : (S \ memSeen n k (memPrefix k
        x.val) μ).card = k - x.val := (by omega); have hr_ne : (S \ memSeen n k (memPrefix k x.val)
        μ).card ≠ 0 := (by omega); unfold wdSubsetStep; rw [ite_eq_right hr_ne, hr_eq, hsc]; simp
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; rw [hsc] at hx_le; dsimp only [wdRoundMaxQ] at hx_le
      rcases scaledCostRel_wdDeflatedRound (Var := Var) (active := x.val) res hm1 hkN hM hp hm hsub2
        perm S kInit probes hB (hx_le.trans hcB) with ⟨θ_r, hrel_r, hdiag_r⟩; refine ⟨θ_r,
        hrel_r.mono_c hB hx_le hcB, fun τ μ hcard hval ↦ ?_⟩; have hseen :=
        card_memSeen_of_memPrefixValid hval; have hadd := Finset.card_sdiff_add_card_eq_card hseen.2
      have hr_eq : (S \ memSeen n k (memPrefix k x.val) μ).card = k - x.val := (by omega)
      have hr_ne : (S \ memSeen n k (memPrefix k x.val) μ).card ≠ 0 := (by omega); rw [hdiag_r μ τ
        hcard x.isLt hval]; unfold wdSubsetStep
      rw [ite_eq_right hr_ne, hr_eq, hsc, ← hr_eq]; dsimp only; by_cases hInj : Set.InjOn (fun z ↦
        subcubePref hp hm (perm z)) ((S \ memSeen n k (memPrefix k x.val) μ : Finset (Fin (2 ^ n)))
        : Set (Fin (2 ^ n)))
      · rw [ite_eq_left hInj, ite_eq_left hInj]; simp only [↓reduceIte, mul_zero,
          Finset.sum_const_zero, add_zero]; push_cast; ring
      · rw [ite_eq_right hInj, ite_eq_right hInj]; simp only [↓reduceIte, mul_zero,
          Finset.sum_const_zero, add_zero]; push_cast; ring
  choose θ_br hrel_br hdiag_br using hbr_ex
  have hdisp : ∀ l : List (Fin k), ∃ θ_l : CQAssertion (Store Var) (2 ^ (W + M)), ScaledCostRel
    model B
    ((dispFin res br l).compile qAssign oracle) θ_l c_sweep ∧ (∀ x ∈ l, ∀ τ : Store Var, τ res =
    (x.val : ℤ) → l.Nodup → θ_l τ = θ_br x τ) ∧ (∀ τ : Store Var, (∀ x ∈ l, τ res ≠ (x.val : ℤ)) →
    θ_l τ = (⊥ : CQAssertion (Store Var) (2 ^ (W + M))) τ) := by
    intro l
    induction l with
    | nil =>
      refine ⟨⊥, (ScaledCostRel.of_zero hB (CostBound.skip_zero model)).mono_c hB hc0 hcB,
        by simp, fun _ _ ↦ rfl⟩
    | cons a rest ih =>
      rcases ih with ⟨θ_rest, hrel_rest, hin_rest, hout_rest⟩; have hif := (ScaledCostRel.qIf hB
        (fun τ ↦ τ res = (a.val : ℤ)) (hrel_br a) hrel_rest).mono_c hB (by rw [max_self]) hcB
      refine ⟨_, hif, ?_, ?_⟩
      · intro x hx τ hτ hnd; rcases List.nodup_cons.mp hnd with ⟨ha_not, hnd_rest⟩
        by_cases hxa : x = a
        · subst hxa; exact ite_eq_left hτ
        · have hx_rest : x ∈ rest := List.mem_of_ne_of_mem hxa hx; have hne : τ res ≠ (a.val : ℤ) :=
            fun heq ↦ hxa (Fin.ext (Int.ofNat.inj (hτ.symm.trans heq))); rw [ite_eq_right hne];
            exact hin_rest x hx_rest τ hτ hnd_rest
      · intro τ hnone; rw [ite_eq_right (hnone a List.mem_cons_self)]
        exact hout_rest τ fun x hx ↦ hnone x (List.mem_cons_of_mem a hx)
  rcases hdisp (finRange k) with ⟨θ_all, hrel_all, hin_all, hout_all⟩; refine ⟨θ_all, hrel_all, fun
    s τ μ hcard hs hτ hval ↦ ?_⟩; rcases eq_or_lt_of_le hs with hs_eq | hlt
  · have hnone : ∀ x ∈ finRange k, τ res ≠ (x.val : ℤ) :=
      (by intro x _; rw [hτ]; have := x.isLt; omega)
    have hseen := card_memSeen_of_memPrefixValid hval; have hadd :=
      Finset.card_sdiff_add_card_eq_card hseen.2; have hr0 : (S \ memSeen n k (memPrefix k s)
      μ).card = 0 := (by omega); rw [hout_all τ hnone]; unfold wdSubsetStep; rw [ite_eq_left hr0];
      simp
  · rw [hin_all ⟨s, hlt⟩ (mem_finRange _) τ hτ (List.nodup_finRange k)]
    exact hdiag_br ⟨s, hlt⟩ τ μ hcard hval
lemma scaledCostRel_wdSweeps {Var : Type} [DecidableEq Var] (res : Var) {n p m k : ℕ} (hn : 1 ≤ n)
  (hk1 : 1 ≤ k) (hm1 : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hM : 1 ≤ k * n) (hp : p ≤ n) (hm : m = 2 ^ p)
  (hsub2 : 2 ≤ 2 ^ (n - p)) (passes : List (Equiv.Perm (Fin (2 ^ n)) × (ℕ → Option (ℕ × List
  (PythPair × ℕ))))) (S : Finset (Fin (2 ^ n))) {M_step B : ℝ} (hM_step : 0 ≤ M_step) (hB : 0 < B)
  (hcB : (passes.length : ℝ) * M_step ≤ B) (hsched_le : ∀ ps ∈ passes, ∀ s : Fin k, (wdRoundMaxQ
  (ps.2 (k - s.val)) : ℝ) ≤ M_step) : ∃ θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)),
  ScaledCostRel (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) B ((wdSweeps res hm1
  hkN hM hp hm passes).compile qAssign (groverParallelMarkingOracle m S)) θ ((passes.length : ℝ) *
  M_step) ∧ (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))), S.card = k → s ≤ k → τ res = (s : ℤ)
  → MemPrefixValid S s μ → (θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = ((wdCircDP hp
  hm true passes (fun _ ↦ 0) (S \ memSeen n k (memPrefix k s) μ) / B : ℝ) : ℂ)) := by
  let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := W + M) oracle
  induction passes with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, zero_mul]; refine ⟨⊥, ScaledCostRel.of_zero hB
      (CostBound.skip_zero model), fun s τ μ _ _ _ _ ↦ ?_⟩; simp [wdCircDP]
  | cons ps rest ih =>
    rcases ps with ⟨perm, sched⟩; have hc_eq : (((perm, sched) :: rest).length : ℝ) * M_step =
      M_step + (rest.length : ℝ) * M_step := (by simp [List.length_cons, add_mul]; ring)
    have hc_rest_B : (rest.length : ℝ) * M_step ≤ B := (by linarith); have hc_head_B : M_step ≤ B :=
      (by have : 0 ≤ (rest.length : ℝ) * M_step := mul_nonneg (Nat.cast_nonneg _) hM_step; linarith)
    rcases ih hc_rest_B (fun q hq s ↦ hsched_le q (List.mem_cons_of_mem _ hq) s) with ⟨θ_rest,
      hrel_rest, hdiag_rest⟩
    rcases scaledCostRel_wdOptSweep (Var := Var) res hm1 hkN hM hp hm hsub2 perm sched S hM_step hB
      hc_head_B (hsched_le (perm, sched) List.mem_cons_self) with ⟨θ_sw, hrel_sw, hdiag_sw⟩
    have hsum_B : M_step + (rest.length : ℝ) * M_step ≤ B := (by linarith); have hrel_tot :=
      (ScaledCostRel.seq hB hrel_sw hrel_rest hsum_B).mono_c hB (le_of_eq hc_eq.symm) hcB
    refine ⟨_, hrel_tot, fun s τ μ hcard hs hτ hval ↦ ?_⟩; rw [cqAssertion_add_mat,
      Matrix.add_apply, hdiag_sw s τ μ hcard hs hτ hval, wp_wdOptSweep_of_finset res hn hk1 hm1 hkN
      hM hp hm hsub2 perm sched hcard hs hτ hval θ_rest (fun R' ↦ wdCircDP hp hm true rest (fun _ ↦
      0) R' / B) (fun s' τ' ν hs' hτ' hval' ↦ hdiag_rest s' τ' ν hcard hs' hτ' hval')]
    have hdiv_step : wdSubsetStep (n - p) (fun x ↦ subcubePref hp hm (perm x)) false sched (fun R' ↦
      wdCircDP hp hm true rest (fun _ ↦ 0) R' / B) (S \ memSeen n k (memPrefix k s) μ) =
      wdSubsetStep (n - p) (fun x ↦ subcubePref hp hm (perm x)) false sched (wdCircDP hp hm true
      rest (fun _ ↦ 0)) (S \ memSeen n k (memPrefix k s) μ) / B := by
      have hm_div := wdCircDP_false_mul hp hm [(perm, sched)] (1 / B) (wdCircDP hp hm true rest (fun
        _ ↦ 0)) (S \ memSeen n k (memPrefix k s) μ); simpa [wdCircDP, div_eq_inv_mul] using hm_div
    rw [hdiv_step]; dsimp only [wdCircDP]
    conv_rhs => rw [wdSubsetStep_true_eq_cost_add_false]
    push_cast; ring
noncomputable def wdSubsetDP {α : Type*} [DecidableEq α] {W m : ℕ}
    (subN : ℕ) (slices : α → Fin W → Fin m) :
    List (Fin W × (ℕ → Option (ℕ × List (PythPair × ℕ)))) →
      (Finset α → ℝ) → Finset α → ℝ
  | [], Ψ, R => Ψ R
  | (t, sched) :: rest, Ψ, R =>
      wdSubsetStep subN (fun x ↦ slices x t) true sched
        (wdSubsetDP subN slices rest Ψ) R
noncomputable def wdExactOneDimStep (subN m : ℕ)
    (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) (g : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r = 0 then g 0
  else
    match sched r with
    | none => g r
    | some (kInit, probes) =>
        let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ))
        let u₀ := wdInitAmp r θ₁ kInit
        let uf := wdChainFinalAmp r θ₁ probes u₀
        let kTot := wdTotalSteps kInit probes
        (∑ h : Fin r → Fin m,
          if Function.Injective h then
            ((kInit + 1 : ℕ) : ℝ) + wdChainExtraQueries r θ₁ probes u₀ +
              wdChainClickProb r θ₁ probes u₀ * g 0 +
              ∑ w ∈ Finset.range (r + 1), (r.choose w : ℝ) * (uf w) ^ 2 * g (r - w)
          else
            (wdMaxQueries kInit probes : ℝ) +
              subcubeStepExp (2 ^ subN) kTot (fun c' ↦ g (∑ j : Fin m, c' j))
                (fun j ↦ (Finset.univ.filter fun a : Fin r ↦ h a = j).card)) /
          ((m : ℝ) ^ r)
noncomputable def wdExactOneDimDP (subN m : ℕ) :
    List (ℕ → Option (ℕ × List (PythPair × ℕ))) → (ℕ → ℝ) → ℕ → ℝ
  | [], V_tail, r => V_tail r
  | sched :: rest, V_tail, r =>
      wdExactOneDimStep subN m sched (wdExactOneDimDP subN m rest V_tail) r
lemma wdSubsetStep_congr_on_subset {α : Type*} [DecidableEq α] {m : ℕ} (subN : ℕ) (pref : α → Fin m)
  (withCost : Bool) (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) {Ψ₁ Ψ₂ : Finset α → ℝ} {R :
  Finset α} (hΨ : ∀ R' ⊆ R, Ψ₁ R' = Ψ₂ R') : wdSubsetStep subN pref withCost sched Ψ₁ R =
  wdSubsetStep subN pref withCost sched Ψ₂ R := by
  classical
  unfold wdSubsetStep; by_cases hr0 : R.card = 0
  · rw [ite_eq_left hr0, ite_eq_left hr0]; exact hΨ R Finset.Subset.rfl
  · rw [ite_eq_right hr0, ite_eq_right hr0]
    cases sched R.card with
    | none => exact hΨ R Finset.Subset.rfl
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; dsimp only; by_cases hInj : Set.InjOn pref (R : Set α)
      · rw [ite_eq_left hInj, ite_eq_left hInj, hΨ ∅ (Finset.empty_subset R)]; congr 1
        refine Finset.sum_congr rfl fun B _ ↦ ?_; rw [hΨ (R \ B) Finset.sdiff_subset]
      · rw [ite_eq_right hInj, ite_eq_right hInj]; congr 1
        refine Finset.sum_congr rfl fun hit _ ↦ ?_; rw [hΨ (R \ rotHitFinset hit)
          Finset.sdiff_subset]
lemma wdSubsetStep_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {m : ℕ} (subN : ℕ)
  {emb : α → β} (hemb : Function.Injective emb) (pref : β → Fin m) (sched : ℕ → Option (ℕ × List
  (PythPair × ℕ))) (Ψ : Finset β → ℝ) (I : Finset α) : wdSubsetStep subN pref true sched Ψ (I.image
  emb) = wdSubsetStep subN (fun i ↦ pref (emb i)) true sched (fun I' ↦ Ψ (I'.image emb)) I := by
  classical
  have hcard : (I.image emb).card = I.card := Finset.card_image_of_injective I hemb
  have hinj_iff : Set.InjOn pref ((I.image emb : Finset β) : Set β) ↔ Set.InjOn (fun i ↦ pref (emb
    i)) (I : Set α) := by
    constructor
    · intro h1 i₁ hi₁ i₂ hi₂ heq; exact hemb (h1 (Finset.mem_coe.mpr (Finset.mem_image_of_mem emb
        hi₁)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem emb hi₂)) heq)
    · intro h2 y₁ hy₁ y₂ hy₂ heq; rcases Finset.mem_image.mp (Finset.mem_coe.mp hy₁) with ⟨i₁, hi₁,
        rfl⟩; rcases Finset.mem_image.mp (Finset.mem_coe.mp hy₂) with ⟨i₂, hi₂, rfl⟩
      exact congrArg emb (h2 hi₁ hi₂ heq)
  by_cases hr0 : I.card = 0
  · unfold wdSubsetStep; have hr0' : (I.image emb).card = 0 := hcard.trans hr0; rw [ite_eq_left
      hr0', ite_eq_left hr0]
  · have hr0' : (I.image emb).card ≠ 0 := (by omega)
    cases hsc : sched I.card with
    | none => unfold wdSubsetStep; rw [ite_eq_right hr0', ite_eq_right hr0, hcard, hsc]
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; by_cases hInj : Set.InjOn (fun i ↦ pref (emb i)) (I : Set α)
      · have hInj' : Set.InjOn pref ((I.image emb : Finset β) : Set β) := hinj_iff.mpr hInj
        unfold wdSubsetStep; rw [ite_eq_right hr0', ite_eq_right hr0, hcard, hsc]
        dsimp only; rw [ite_eq_left hInj', ite_eq_left hInj, Finset.image_empty]; congr 1
        rw [Finset.powerset_image, Finset.sum_image (fun A₁ _ A₂ _ h ↦ Finset.image_injective hemb
          h)]; refine Finset.sum_congr rfl fun A _ ↦ ?_
        have hsdiff : (I.image emb) \ (A.image emb) = (I \ A).image emb := by
          ext y; simp only [Finset.mem_sdiff, Finset.mem_image]; constructor
          · rintro ⟨⟨i, hi, rfl⟩, hnot⟩; exact ⟨i, ⟨hi, fun ha ↦ hnot ⟨i, ha, rfl⟩⟩, rfl⟩
          · rintro ⟨i, ⟨hi, hna⟩, rfl⟩; exact ⟨⟨i, hi, rfl⟩, fun ⟨i', ha', heq⟩ ↦ hna (hemb heq ▸
              ha')⟩
        rw [Finset.card_image_of_injective A hemb, hsdiff]
      · have hInj' : ¬ Set.InjOn pref ((I.image emb : Finset β) : Set β) := mt hinj_iff.mp hInj
        have hlhs : wdSubsetStep subN pref true sched Ψ (I.image emb) = rotSubsetStep (2 ^ subN)
          pref (fun _ ↦ (wdMaxQueries kInit probes : ℝ)) (fun _ ↦ some (wdTotalSteps kInit probes))
          Ψ (I.image emb) := by
          unfold wdSubsetStep rotSubsetStep; rw [ite_eq_right hr0', hcard, hsc]
          dsimp only; rw [ite_eq_right hInj']; rfl
        have hrhs : wdSubsetStep subN (fun i ↦ pref (emb i)) true sched (fun I' ↦ Ψ (I'.image emb))
          I = rotSubsetStep (2 ^ subN) (fun i ↦ pref (emb i)) (fun _ ↦ (wdMaxQueries kInit probes :
          ℝ)) (fun _ ↦ some (wdTotalSteps kInit probes)) (fun I' ↦ Ψ (I'.image emb)) I := by
          unfold wdSubsetStep rotSubsetStep; rw [ite_eq_right hr0, hsc]
          dsimp only; rw [ite_eq_right hInj]; rfl
        rw [hlhs, hrhs]; exact rotSubsetStep_image_of_inj (2 ^ subN) hemb pref _ _ Ψ I
private lemma wdSubsetStep_of_card_eq {α : Type*} [DecidableEq α] {m : ℕ} (subN : ℕ)
    (pref : α → Fin m) (sched : ℕ → Option (ℕ × List (PythPair × ℕ)))
    {Ψ : Finset α → ℝ} (g : ℕ → ℝ) (R : Finset α)
    (hΨ : ∀ R', R' ⊆ R → Ψ R' = g R'.card) :
    wdSubsetStep subN pref true sched Ψ R =
      if R.card = 0 then g 0
      else
        match sched R.card with
        | none => g R.card
        | some (kInit, probes) =>
            if Set.InjOn pref (R : Set α) then
              let θ₁ := Real.arcsin (1 / √(2 ^ subN : ℝ)); let u₀ := wdInitAmp R.card θ₁ kInit
              let uf := wdChainFinalAmp R.card θ₁ probes u₀
              ((kInit + 1 : ℕ) : ℝ) + wdChainExtraQueries R.card θ₁ probes u₀ +
                wdChainClickProb R.card θ₁ probes u₀ * g 0 +
                ∑ w ∈ Finset.range (R.card + 1), (R.card.choose w : ℝ) * (uf w) ^ 2 * g (R.card - w)
            else
              let kTot := wdTotalSteps kInit probes
              (wdMaxQueries kInit probes : ℝ) + subcubeStepExp (2 ^ subN) kTot (fun c' ↦ g (∑ j :
                Fin m, c' j)) (fun j ↦ (R.filter fun x ↦ pref x = j).card) := by
  classical
  by_cases hr0 : R.card = 0
  · unfold wdSubsetStep; rw [ite_eq_left hr0, ite_eq_left hr0, hΨ R Finset.Subset.rfl, hr0]
  · cases hsc : sched R.card with
    | none =>
      unfold wdSubsetStep; rw [ite_eq_right hr0, ite_eq_right hr0, hsc]
      exact hΨ R Finset.Subset.rfl
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; by_cases hInj : Set.InjOn pref (R : Set α)
      · unfold wdSubsetStep; rw [ite_eq_right hr0, ite_eq_right hr0, hsc]; dsimp only
        rw [ite_eq_left hInj, ite_eq_left hInj, hΨ ∅ (Finset.empty_subset R), Finset.card_empty]
        congr 1
        have hpow : R.powerset = (Finset.range (R.card + 1)).biUnion R.powersetCard := by
          ext B; simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
            Finset.mem_powersetCard]; exact ⟨fun h ↦ ⟨B.card, Nat.lt_succ_of_le (Finset.card_le_card
            h), h, rfl⟩, fun ⟨_, _, h, _⟩ ↦ h⟩
        have hdisj : Set.PairwiseDisjoint (Finset.range (R.card + 1) : Set ℕ) R.powersetCard := fun
          _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun B h1 h2 ↦ hne ((Finset.mem_powersetCard.mp
          h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2); rw [hpow, Finset.sum_biUnion hdisj]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        have hcongr : ∀ B ∈ R.powersetCard w, (wdChainFinalAmp R.card (Real.arcsin (1 / √(2 ^ subN :
          ℝ))) probes (wdInitAmp R.card (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) B.card) ^ 2 * Ψ
          (R \ B) = (wdChainFinalAmp R.card (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes (wdInitAmp
          R.card (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) w) ^ 2 * g (R.card - w) := by
          intro B hB; rcases Finset.mem_powersetCard.mp hB with ⟨hBR, hBw⟩
          have hcs : (R \ B).card = R.card - w :=
            (by have h := Finset.card_sdiff_add_card_eq_card hBR; omega); rw [hBw, hΨ (R \ B)
            Finset.sdiff_subset, hcs]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, ←
          mul_assoc]
      · have hlhs : wdSubsetStep subN pref true sched Ψ R = rotSubsetStep (2 ^ subN) pref (fun _ ↦
          (wdMaxQueries kInit probes : ℝ)) (fun _ ↦ some (wdTotalSteps kInit probes)) Ψ R := by
          unfold wdSubsetStep rotSubsetStep; rw [ite_eq_right hr0, hsc]
          dsimp only; rw [ite_eq_right hInj]; rfl
        rw [hlhs, ite_eq_right hr0]; dsimp only
        rw [ite_eq_right hInj]; exact rotSubsetStep_of_card_eq (2 ^ subN) pref _ _ g R hΨ
private lemma sum_wdSubsetStep_of_card_eq {k m : ℕ} (hm1 : 1 ≤ m) (subN : ℕ) (sched : ℕ → Option (ℕ
  × List (PythPair × ℕ))) (g : ℕ → ℝ) (I : Finset (Fin k)) : (∑ f_t : Fin k → Fin m, wdSubsetStep
  subN f_t true sched (fun I' ↦ g I'.card) I) = ((m : ℝ) ^ k) * wdExactOneDimStep subN m sched g
  I.card := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := (by exact_mod_cast (by omega : 0 < m))
  simp_rw [wdSubsetStep_of_card_eq subN _ sched g I (fun _ _ ↦ rfl)]; unfold wdExactOneDimStep
  by_cases hr0 : I.card = 0
  · simp [hr0, Finset.sum_const, nsmul_eq_mul]
  · simp only [ite_eq_right hr0]
    cases sched I.card with
    | none => simp [Finset.sum_const, nsmul_eq_mul]
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; dsimp only; set r : ℕ := I.card
      let eI : Fin r ≃ I := I.equivFin.symm
      let splitI : (Fin k → Fin m) ≃ (Fin r → Fin m) × ({i : Fin k // i ∉ I} → Fin m) :=
        { toFun := fun f_t ↦ (fun a ↦ f_t (eI a), fun b ↦ f_t b.1)
          invFun := fun p i ↦ if hi : i ∈ I then p.1 (eI.symm ⟨i, hi⟩) else p.2 ⟨i, hi⟩
          left_inv := fun f_t ↦ funext fun i ↦ by by_cases hi : i ∈ I <;> simp [hi]
          right_inv := fun ⟨h, hc⟩ ↦ Prod.ext
            (funext fun a ↦ by simp [(eI a).2])
            (funext fun b ↦ by simp [b.2]) }
      have hcard_r : (m : ℝ) ^ k = (m : ℝ) ^ r * (Fintype.card ({i : Fin k // i ∉ I} → Fin m) : ℝ)
        := by
        have hc := Fintype.card_congr splitI; simpa only [Fintype.card_fun, Fintype.card_fin,
          Fintype.card_prod, Nat.cast_mul, Nat.cast_pow] using congrArg (Nat.cast (R := ℝ)) hc
      rw [← splitI.symm.sum_comp, Fintype.sum_prod_type]
      have hinj_eq (h : Fin r → Fin m) (hc : {i : Fin k // i ∉ I} → Fin m) : Set.InjOn (splitI.symm
        (h, hc)) (I : Set (Fin k)) ↔ Function.Injective h := by
        constructor
        · intro hInj a₁ a₂ heq; have h1 : splitI.symm (h, hc) (eI a₁) = h a₁ :=
            (by simp [splitI, (eI a₁).2]); have h2 : splitI.symm (h, hc) (eI a₂) = h a₂ :=
            (by simp [splitI, (eI a₂).2]); exact eI.injective (Subtype.ext (hInj (eI a₁).2 (eI a₂).2
            (h1.trans (heq.trans h2.symm))))
        · intro hh i₁ hi₁ i₂ hi₂ heq; dsimp only [splitI, Equiv.coe_fn_symm_mk] at heq
          rw [dite_eq_left (Finset.mem_coe.mp hi₁), dite_eq_left (Finset.mem_coe.mp hi₂)] at heq
          exact congrArg Subtype.val (eI.symm.injective (hh heq))
      have hterm (h : Fin r → Fin m) (hc : {i : Fin k // i ∉ I} → Fin m) : (fun j : Fin m ↦
        (I.filter fun i ↦ splitI.symm (h, hc) i = j).card) = (fun j : Fin m ↦ (Finset.univ.filter
        fun a : Fin r ↦ h a = j).card) := by
        funext j; refine Finset.card_bij (fun i hi ↦ eI.symm ⟨i, (Finset.mem_filter.mp hi).1⟩) (fun
          i hi ↦ ?_) (fun i₁ _ i₂ _ heq ↦ congrArg Subtype.val (eI.symm.injective heq)) (fun a ha ↦
          ?_)
        · rcases Finset.mem_filter.mp hi with ⟨hiI, hfj⟩; simp only [splitI, Equiv.coe_fn_symm_mk,
            hiI, ↓reduceDIte] at hfj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfj⟩
        · have haj : h a = j := (Finset.mem_filter.mp ha).2; refine ⟨(eI a).1, Finset.mem_filter.mpr
            ⟨(eI a).2, ?_⟩, by simp⟩; simp [splitI, (eI a).2, haj]
      have hsummand (h : Fin r → Fin m) (hc : {i : Fin k // i ∉ I} → Fin m) : (if Set.InjOn
        (splitI.symm (h, hc)) (I : Set (Fin k)) then ((kInit + 1 : ℕ) : ℝ) + wdChainExtraQueries r
        (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes (wdInitAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ)))
        kInit) + wdChainClickProb r (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes (wdInitAmp r
        (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) * g 0 + ∑ w ∈ Finset.range (r + 1), (r.choose w :
        ℝ) * (wdChainFinalAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes (wdInitAmp r (Real.arcsin
        (1 / √(2 ^ subN : ℝ))) kInit) w) ^ 2 * g (r - w) else (wdMaxQueries kInit probes : ℝ) +
        subcubeStepExp (2 ^ subN) (wdTotalSteps kInit probes) (fun c' ↦ g (∑ j : Fin m, c' j)) (fun
        j ↦ (I.filter fun i ↦ splitI.symm (h, hc) i = j).card)) = if Function.Injective h then
        ((kInit + 1 : ℕ) : ℝ) + wdChainExtraQueries r (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes
        (wdInitAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) + wdChainClickProb r (Real.arcsin (1
        / √(2 ^ subN : ℝ))) probes (wdInitAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) * g 0 + ∑
        w ∈ Finset.range (r + 1), (r.choose w : ℝ) * (wdChainFinalAmp r (Real.arcsin (1 / √(2 ^ subN
        : ℝ))) probes (wdInitAmp r (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) w) ^ 2 * g (r - w)
        else (wdMaxQueries kInit probes : ℝ) + subcubeStepExp (2 ^ subN) (wdTotalSteps kInit probes)
        (fun c' ↦ g (∑ j : Fin m, c' j)) (fun j ↦ (Finset.univ.filter fun a : Fin r ↦ h a = j).card)
        := (by rw [if_congr (hinj_eq h hc) rfl (by rw [hterm h hc])]); simp_rw [hsummand,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hcard_r]
      have hmr_ne : (m : ℝ) ^ r ≠ 0 := (pow_pos hm_pos r).ne'; field_simp [hmr_ne]
lemma wdSubsetDP_congr_slices {α : Type*} [DecidableEq α] {W m : ℕ} (subN : ℕ) {s₁ s₂ : α → Fin W →
  Fin m} (passes : List (Fin W × (ℕ → Option (ℕ × List (PythPair × ℕ))))) (hs : ∀ p ∈ passes, ∀ x :
  α, s₁ x p.1 = s₂ x p.1) (Ψ : Finset α → ℝ) (R : Finset α) : wdSubsetDP subN s₁ passes Ψ R =
  wdSubsetDP subN s₂ passes Ψ R := by
  induction passes generalizing R with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨t, sched⟩; have ht : (fun x ↦ s₁ x t) = (fun x ↦ s₂ x t) := funext fun x ↦ hs (t,
      sched) (List.mem_cons_self ..) x; dsimp only [wdSubsetDP]; rw [ht]
    exact wdSubsetStep_congr_on_subset _ _ _ _ fun R' _ ↦ ih (fun q hq x ↦ hs q
      (List.mem_cons_of_mem _ hq) x) R'
private lemma sum_fintype_wdSubsetStep {α β : Type*} [DecidableEq α] [Fintype β] {m : ℕ} (subN : ℕ)
  (pref : α → Fin m) (sched : ℕ → Option (ℕ × List (PythPair × ℕ))) (F : β → Finset α → ℝ) (G :
  Finset α → ℝ) (I : Finset α) (hFG : ∀ I' ⊆ I, (∑ fr : β, F fr I') = (Fintype.card β : ℝ) * G I') :
  (∑ fr : β, wdSubsetStep subN pref true sched (F fr) I) = (Fintype.card β : ℝ) * wdSubsetStep subN
  pref true sched G I := by
  classical
  unfold wdSubsetStep; by_cases hr0 : I.card = 0
  · simp_rw [ite_eq_left hr0]; exact hFG I Finset.Subset.rfl
  · simp_rw [ite_eq_right hr0]
    cases sched I.card with
    | none => exact hFG I Finset.Subset.rfl
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; dsimp only [↓reduceIte]; by_cases hInj : Set.InjOn pref (I :
        Set α)
      · simp_rw [ite_eq_left hInj]; rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hFG ∅
          (Finset.empty_subset I), Finset.sum_comm]; have hB_sum (B : Finset α) : (∑ fr : β,
          (wdChainFinalAmp I.card (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes (wdInitAmp I.card
          (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) B.card) ^ 2 * F fr (I \ B)) = (Fintype.card β :
          ℝ) * ((wdChainFinalAmp I.card (Real.arcsin (1 / √(2 ^ subN : ℝ))) probes (wdInitAmp I.card
          (Real.arcsin (1 / √(2 ^ subN : ℝ))) kInit) B.card) ^ 2 * G (I \ B)) :=
          (by rw [← Finset.mul_sum, hFG (I \ B) Finset.sdiff_subset]; ring); simp_rw [hB_sum, ←
          Finset.mul_sum]; ring
      · simp_rw [ite_eq_right hInj]; rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Finset.sum_comm]; have hhit_sum (hit : Fin m → Option α) : (∑ fr : β, (∏ j :
          Fin m, rotSlotHitProb (2 ^ subN) (wdTotalSteps kInit probes) (I.filter fun x ↦ pref x = j)
          (hit j)) * F fr (I \ rotHitFinset hit)) = (Fintype.card β : ℝ) * ((∏ j : Fin m,
          rotSlotHitProb (2 ^ subN) (wdTotalSteps kInit probes) (I.filter fun x ↦ pref x = j) (hit
          j)) * G (I \ rotHitFinset hit)) :=
          (by rw [← Finset.mul_sum, hFG (I \ rotHitFinset hit) Finset.sdiff_subset]; ring)
        simp_rw [hhit_sum, ← Finset.mul_sum]; ring
lemma avg_wdSubsetDP_eq_wdExactOneDimDP {W m k : ℕ} (hm1 : 1 ≤ m) (subN : ℕ) (passes : List (Fin W ×
  (ℕ → Option (ℕ × List (PythPair × ℕ))))) (hnodup : (passes.map Prod.fst).Nodup) (V_tail : ℕ → ℝ)
  (I : Finset (Fin k)) : (∑ f : Fin k → Fin W → Fin m, wdSubsetDP subN f passes (fun I' ↦ V_tail
  I'.card) I) / (((m ^ W) ^ k : ℕ) : ℝ) = wdExactOneDimDP subN m (passes.map Prod.snd) V_tail I.card
  := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := (by exact_mod_cast (by omega : 0 < m))
  have hMW_pos : (0 : ℝ) < (((m ^ W) ^ k : ℕ) : ℝ) :=
    (by exact_mod_cast Nat.pow_pos (Nat.pow_pos (by omega : 0 < m))); rw [div_eq_iff hMW_pos.ne']
  induction passes generalizing I with
  | nil => simp [wdSubsetDP, wdExactOneDimDP, Finset.sum_const, nsmul_eq_mul, mul_comm]
  | cons head rest ih =>
    rcases head with ⟨t, sched⟩; rw [List.map_cons, List.nodup_cons] at hnodup; rcases hnodup with
      ⟨ht_notMem, hrest_nodup⟩
    let splitW : (Fin k → Fin W → Fin m) ≃
        (Fin k → Fin m) × (Fin k → {t' : Fin W // t' ≠ t} → Fin m) :=
      { toFun := fun f ↦ (fun i ↦ f i t, fun i t' ↦ f i t'.1)
        invFun := fun p i t' ↦ if h : t' = t then p.1 i else p.2 i ⟨t', h⟩
        left_inv := fun f ↦ funext fun i ↦ funext fun t' ↦ by by_cases h : t' = t <;> simp [h]
        right_inv := fun ⟨ft, fr⟩ ↦ Prod.ext (funext fun i ↦ by simp)
          (funext fun i ↦ funext fun t' ↦ by simp [t'.2]) }
    let RestType := Fin k → {t' : Fin W // t' ≠ t} → Fin m
    have hcard_Wr : (((m ^ W) ^ k : ℕ) : ℝ) = ((m : ℝ) ^ k) * (Fintype.card RestType : ℝ) := by
      have hcard_W : Fintype.card (Fin k → Fin W → Fin m) = Fintype.card (Fin k → Fin m) *
        Fintype.card RestType := (by rw [Fintype.card_congr splitW, Fintype.card_prod])
      have hlhs : Fintype.card (Fin k → Fin W → Fin m) = (m ^ W) ^ k := (by simp [Fintype.card_fin])
      have hm_k : Fintype.card (Fin k → Fin m) = m ^ k := (by simp [Fintype.card_fin]); rw [hlhs,
        hm_k] at hcard_W; have hr := congrArg (Nat.cast (R := ℝ)) hcard_W; rw [Nat.cast_mul,
        Nat.cast_pow m k] at hr; exact hr
    let f₀ : Fin k → Fin m := fun _ ↦ ⟨0, by omega⟩
    have hrest_indep (ft : Fin k → Fin m) (fr : RestType) (I' : Finset (Fin k)) : wdSubsetDP subN
      (splitW.symm (ft, fr)) rest (fun J ↦ V_tail J.card) I' = wdSubsetDP subN (splitW.symm (f₀,
      fr)) rest (fun J ↦ V_tail J.card) I' := by
      refine wdSubsetDP_congr_slices subN rest (fun q hq i ↦ ?_) _ I'
      have hne : q.1 ≠ t := fun heq ↦ ht_notMem (heq ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)
      dsimp only [splitW, Equiv.coe_fn_symm_mk]; simp [hne]
    let g_rest : ℕ → ℝ := wdExactOneDimDP subN m (rest.map Prod.snd) V_tail
    have hsum_fr (I' : Finset (Fin k)) : (∑ fr : RestType, wdSubsetDP subN (splitW.symm (f₀, fr))
      rest (fun J ↦ V_tail J.card) I') = (Fintype.card RestType : ℝ) * g_rest I'.card := by
      have hih := ih hrest_nodup I'; rw [← splitW.symm.sum_comp, Fintype.sum_prod_type] at hih
      simp_rw [hrest_indep] at hih; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, hcard_Wr] at hih
      exact mul_left_cancel₀ (pow_pos hm_pos k).ne' (by dsimp only [g_rest]; linarith)
    dsimp only [wdSubsetDP, List.map, wdExactOneDimDP]; rw [← splitW.symm.sum_comp,
      Fintype.sum_prod_type]; have hhead_t (ft : Fin k → Fin m) (fr : RestType) : (fun i : Fin k ↦
      splitW.symm (ft, fr) i t) = ft :=
      (by funext i; dsimp only [splitW, Equiv.coe_fn_symm_mk]; simp)
    have hinner (ft : Fin k → Fin m) : (∑ fr : RestType, wdSubsetStep subN (fun i ↦ splitW.symm (ft,
      fr) i t) true sched (wdSubsetDP subN (splitW.symm (ft, fr)) rest (fun J ↦ V_tail J.card)) I) =
      (Fintype.card RestType : ℝ) * wdSubsetStep subN ft true sched (fun I' ↦ g_rest I'.card) I
      := by
      simp_rw [hhead_t ft]; refine sum_fintype_wdSubsetStep subN ft sched _ _ I fun I' _ ↦ ?_
      simp_rw [hrest_indep ft _ I']; exact hsum_fr I'
    rw [Finset.sum_congr rfl fun ft _ ↦ hinner ft, ← Finset.mul_sum, sum_wdSubsetStep_of_card_eq hm1
      subN sched g_rest I, hcard_Wr]; dsimp only [g_rest]; ring
private lemma card_filter_injective_fin (r m : ℕ) : ((Finset.univ : Finset (Fin r → Fin m)).filter
  Function.Injective).card = m.descFactorial r := by
  induction r with
  | zero => have hinj (h : Fin 0 → Fin m) : Function.Injective h := fun a ↦ Fin.elim0 a; simp [hinj]
  | succ r ih =>
    let split0 : (Fin (r + 1) → Fin m) ≃ Fin m × (Fin r → Fin m) :=
      { toFun := fun h ↦ (h 0, fun i ↦ h i.succ)
        invFun := fun p ↦ Fin.cases p.1 p.2
        left_inv := fun h ↦ funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
        right_inv := fun ⟨j, h'⟩ ↦ Prod.ext rfl (funext fun _ ↦ rfl) }
    let InjR := (Finset.univ : Finset (Fin r → Fin m)).filter Function.Injective
    let Pairs := InjR.biUnion fun h' ↦ (Finset.univ \ Finset.univ.image h').map ⟨fun j ↦ (j, h'),
      fun _ _ heq ↦ congrArg Prod.fst heq⟩
    have hcard_eq : ((Finset.univ : Finset (Fin (r + 1) → Fin m)).filter Function.Injective).card =
      Pairs.card := by
      refine Finset.card_bij (fun h _ ↦ split0 h) (fun h hh ↦ ?_) (fun _ _ _ _ heq ↦
        split0.injective heq) (fun p hp ↦ ?_)
      · have hInj : Function.Injective h := (Finset.mem_filter.mp hh).2
        have hInj' : Function.Injective (fun i : Fin r ↦ h i.succ) := fun i₁ i₂ heq ↦
          Fin.succ_injective _ (hInj heq)
        have hnot : h 0 ∉ Finset.univ.image (fun i : Fin r ↦ h i.succ) := by
          intro hm; rcases Finset.mem_image.mp hm with ⟨i, _, hi⟩; exact Fin.succ_ne_zero i (hInj
            hi)
        exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hInj'⟩,
          Finset.mem_map.mpr ⟨h 0, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩, rfl⟩⟩
      · rcases Finset.mem_biUnion.mp hp with ⟨h', hh', hm⟩; rcases Finset.mem_map.mp hm with ⟨j, hj,
          rfl⟩; have hInj' : Function.Injective h' := (Finset.mem_filter.mp hh').2
        have hnot : j ∉ Finset.univ.image h' := (Finset.mem_sdiff.mp hj).2; refine ⟨split0.symm (j,
          h'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, split0.apply_symm_apply _⟩
        intro a₁ a₂; refine Fin.cases ?_ (fun i₁ ↦ ?_) a₁ <;> refine Fin.cases ?_ (fun i₂ ↦ ?_) a₂
        · intro _; rfl
        · intro heq; exact False.elim (hnot (Finset.mem_image.mpr ⟨i₂, Finset.mem_univ _,
            heq.symm⟩))
        · intro heq; exact False.elim (hnot (Finset.mem_image.mpr ⟨i₁, Finset.mem_univ _, heq⟩))
        · intro heq; exact congrArg Fin.succ (hInj' heq)
    have hdisj : Set.PairwiseDisjoint (InjR : Set (Fin r → Fin m)) fun h' ↦ (Finset.univ \
      Finset.univ.image h').map ⟨fun j ↦ (j, h'), fun _ _ heq ↦ congrArg Prod.fst heq⟩ := by
      intro h₁ _ h₂ _ hne; refine Finset.disjoint_left.mpr fun p hp₁ hp₂ ↦ hne ?_
      rcases Finset.mem_map.mp hp₁ with ⟨j₁, _, heq₁⟩; rcases Finset.mem_map.mp hp₂ with ⟨j₂, _,
        heq₂⟩; exact (congrArg Prod.snd heq₁).trans (congrArg Prod.snd heq₂).symm
    rw [hcard_eq, Finset.card_biUnion hdisj]
    have hterm : ∀ h' ∈ InjR, ((Finset.univ \ Finset.univ.image h').map ⟨fun j ↦ (j, h'), fun _ _
      heq ↦ congrArg Prod.fst heq⟩).card = m - r := by
      intro h' hh'; have hInj' : Function.Injective h' := (Finset.mem_filter.mp hh').2
      have himg_card : (Finset.univ.image h').card = r :=
        (by simpa using Finset.card_image_of_injective Finset.univ hInj')
      have hsdiff_card : (Finset.univ \ Finset.univ.image h').card = m - r := by
        have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Finset.univ.image h'))
        simp only [Finset.card_univ, Fintype.card_fin, himg_card] at h; have hle : r ≤ m :=
          (by omega); omega
      rw [Finset.card_map, hsdiff_card]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, ih, Nat.descFactorial_succ,
      Nat.mul_comm]
private abbrev wdOcc {r m : ℕ} (h : Fin r → Fin m) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun a : Fin r ↦ h a = j).card
private abbrev wdIsSinglePair {r m : ℕ} (h : Fin r → Fin m) : Prop :=
  ∃ j₂ : Fin m, wdOcc h j₂ = 2 ∧ ∀ j : Fin m, j ≠ j₂ → wdOcc h j ≤ 1
private lemma wdIsSinglePair_not_injective {r m : ℕ} {h : Fin r → Fin m} (hsp : wdIsSinglePair h) :
  ¬ Function.Injective h := by
  rcases hsp with ⟨j₂, hj₂, _⟩; intro hinj
  have hle1 : wdOcc h j₂ ≤ 1 := by
    refine Finset.card_le_one.mpr fun a₁ ha₁ a₂ ha₂ ↦ hinj ?_; exact (Finset.mem_filter.mp
      ha₁).2.trans (Finset.mem_filter.mp ha₂).2.symm
  omega
private def wdInsertIdx {n : ℕ} (a₂ : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  ⟨if i.1 < a₂.1 then i.1 else i.1 + 1, by split_ifs <;> omega⟩
private def wdRemoveIdx {n : ℕ} (a₂ : Fin (n + 1)) (x : Fin (n + 1)) (hx : x ≠ a₂) : Fin n :=
  ⟨if x.1 < a₂.1 then x.1 else x.1 - 1, by
    have hne : x.1 ≠ a₂.1 := fun hv ↦ hx (Fin.ext hv)
    split_ifs <;> omega⟩
private lemma wdInsertIdx_ne {n : ℕ} (a₂ : Fin (n + 1)) (i : Fin n) : wdInsertIdx a₂ i ≠ a₂ := by
  intro heq; have hv := congrArg Fin.val heq; dsimp [wdInsertIdx] at hv; split_ifs at hv <;> omega
private lemma wdRemoveIdx_insertIdx {n : ℕ} (a₂ : Fin (n + 1)) (i : Fin n) : wdRemoveIdx a₂
  (wdInsertIdx a₂ i) (wdInsertIdx_ne a₂ i) = i := by
  apply Fin.ext; dsimp [wdRemoveIdx, wdInsertIdx]; split_ifs <;> omega
private lemma wdInsertIdx_removeIdx {n : ℕ} (a₂ : Fin (n + 1)) (x : Fin (n + 1)) (hx : x ≠ a₂) :
  wdInsertIdx a₂ (wdRemoveIdx a₂ x hx) = x := by
  have hne : x.1 ≠ a₂.1 := fun hv ↦ hx (Fin.ext hv); apply Fin.ext; dsimp [wdInsertIdx, wdRemoveIdx]
  split_ifs <;> omega
private lemma wd_finset_pair_min_max {α : Type*} [LinearOrder α] {P : Finset α} (hP2 : P.card = 2) :
    let hne : P.Nonempty := Finset.card_pos.mp (by omega)
    P.min' hne ≠ P.max' hne ∧ P = {P.min' hne, P.max' hne} := by
  intro hne; set a₁ := P.min' hne; set a₂ := P.max' hne
  have ha₁₂ : a₁ ≠ a₂ := by
    intro heq
    have hsub : P ⊆ {a₁} := by
      intro x hx; have h1 : a₁ ≤ x := Finset.min'_le P x hx
      have h2 : x ≤ a₂ := Finset.le_max' P x hx; rw [← heq] at h2
      exact Finset.mem_singleton.mpr (le_antisymm h2 h1)
    have hle1 : P.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp); omega
  refine ⟨ha₁₂, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.min'_mem P hne
    · exact Finset.mem_singleton.mp hx' ▸ Finset.max'_mem P hne
  · rw [Finset.card_pair ha₁₂, hP2]
private lemma wd_card_singlePair_eq {r m : ℕ} (hr2 : 2 ≤ r) : ((Finset.univ : Finset (Fin r → Fin
  m)).filter wdIsSinglePair).card = r.choose 2 * m.descFactorial (r - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩; have hsub1 : n + 1 - 1 = n :=
    Nat.add_sub_cancel n 1; rw [hsub1]
  let SP := (Finset.univ : Finset (Fin (n + 1) → Fin m)).filter wdIsSinglePair
  let Pairs := (Finset.univ : Finset (Fin (n + 1))).powersetCard 2
  let InjN := (Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective
  let mkFn (P : Finset (Fin (n + 1))) (hP2 : P.card = 2) (g : Fin n → Fin m) :
      Fin (n + 1) → Fin m :=
    let hne : P.Nonempty := Finset.card_pos.mp (by omega); let a₁ := P.min' hne
    let a₂ := P.max' hne; let ha₁₂ : a₁ ≠ a₂ := (wd_finset_pair_min_max hP2).1
    fun x ↦ if hx : x = a₂ then g (wdRemoveIdx a₂ a₁ ha₁₂) else g (wdRemoveIdx a₂ x hx)
  have hmk_props (P : Finset (Fin (n + 1))) (hP2 : P.card = 2)
      (g : Fin n → Fin m) (hg : Function.Injective g) :
      let hne : P.Nonempty := Finset.card_pos.mp (by omega); let a₁ := P.min' hne
      let a₂ := P.max' hne; let ha₁₂ : a₁ ≠ a₂ := (wd_finset_pair_min_max hP2).1
      let j₂ := g (wdRemoveIdx a₂ a₁ ha₁₂); let h := mkFn P hP2 g
      (Finset.univ.filter fun x ↦ h x = j₂) = P ∧
        (∀ j : Fin m, j ≠ j₂ → wdOcc h j ≤ 1) ∧
        (∀ i : Fin n, h (wdInsertIdx a₂ i) = g i) := by
    intro hne a₁ a₂ ha₁₂ j₂ h; have hP_eq : P = {a₁, a₂} := (wd_finset_pair_min_max hP2).2
    refine ⟨?_, ?_, ?_⟩
    · ext x; rw [hP_eq]; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]; by_cases hx : x = a₂
      · subst hx; have hval : h a₂ = j₂ := dite_eq_left rfl; simp [hval]
      · have hval : h x = g (wdRemoveIdx a₂ x hx) := dite_eq_right hx; rw [hval]; constructor
        · intro heq; have hrem := hg heq; have hins := congrArg (wdInsertIdx a₂) hrem
          rw [wdInsertIdx_removeIdx, wdInsertIdx_removeIdx] at hins; exact Or.inl hins
        · rintro (rfl | rfl)
          · rfl
          · exact False.elim (hx rfl)
    · intro j hj; refine Finset.card_le_one.mpr fun x₁ hx₁ x₂ hx₂ ↦ ?_; have hx₁_eq : h x₁ = j :=
        (Finset.mem_filter.mp hx₁).2; have hx₂_eq : h x₂ = j := (Finset.mem_filter.mp hx₂).2
      have hx₁_ne : x₁ ≠ a₂ :=
        (by rintro rfl; have : h a₂ = j₂ := dite_eq_left rfl; exact hj (hx₁_eq.symm.trans this))
      have hx₂_ne : x₂ ≠ a₂ :=
        (by rintro rfl; have : h a₂ = j₂ := dite_eq_left rfl; exact hj (hx₂_eq.symm.trans this))
      have hv₁ : g (wdRemoveIdx a₂ x₁ hx₁_ne) = j := (dite_eq_right hx₁_ne).symm.trans hx₁_eq
      have hv₂ : g (wdRemoveIdx a₂ x₂ hx₂_ne) = j := (dite_eq_right hx₂_ne).symm.trans hx₂_eq
      have hins := congrArg (wdInsertIdx a₂) (hg (hv₁.trans hv₂.symm))
      rwa [wdInsertIdx_removeIdx, wdInsertIdx_removeIdx] at hins
    · intro i; have hne_i := wdInsertIdx_ne a₂ i; change (if hx : wdInsertIdx a₂ i = a₂ then _ else
        g (wdRemoveIdx a₂ _ hx)) = g i; rw [dite_eq_right hne_i, wdRemoveIdx_insertIdx]
  have hbij : SP.card = (Pairs ×ˢ InjN).card := by
    symm; refine Finset.card_bij (fun p hp ↦ mkFn p.1 (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp hp).1).2 p.2) (fun p hp ↦ ?_) (fun p₁ hp₁ p₂ hp₂ heq ↦ ?_) (fun h hh ↦
      ?_)
    · have hP2 : p.1.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
      have hg : Function.Injective p.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
      have hpr := hmk_props p.1 hP2 p.2 hg; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨_, ?_,
        hpr.2.1⟩⟩; change (Finset.univ.filter fun x ↦ mkFn p.1 hP2 p.2 x = _).card = 2; rw [hpr.1,
        hP2]
    · have hP₁ : p₁.1.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp₁).1).2
      have hg₁ : Function.Injective p₁.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hp₁).2).2
      have hP₂ : p₂.1.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp₂).1).2
      have hg₂ : Function.Injective p₂.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hp₂).2).2
      have hpr₁ := hmk_props p₁.1 hP₁ p₁.2 hg₁; have hpr₂ := hmk_props p₂.1 hP₂ p₂.2 hg₂; set h :=
        mkFn p₁.1 hP₁ p₁.2; set j₁ := p₁.2 (wdRemoveIdx (p₁.1.max' (Finset.card_pos.mp (by omega)))
        (p₁.1.min' (Finset.card_pos.mp (by omega))) (wd_finset_pair_min_max hP₁).1)
      set j₂ := p₂.2 (wdRemoveIdx (p₂.1.max' (Finset.card_pos.mp (by omega))) (p₂.1.min'
        (Finset.card_pos.mp (by omega))) (wd_finset_pair_min_max hP₂).1)
      have hpr₂_h : (Finset.univ.filter fun x ↦ h x = j₂) = p₂.1 ∧ (∀ j : Fin m, j ≠ j₂ → wdOcc h j
        ≤ 1) ∧ (∀ i : Fin n, h (wdInsertIdx (p₂.1.max' (Finset.card_pos.mp (by omega))) i) = p₂.2 i)
        := (by simpa only [← heq] using hpr₂)
      have hj_eq : j₁ = j₂ := by
        by_contra hj_ne
        have hle1 : wdOcc h j₂ ≤ 1 := hpr₁.2.1 j₂ (Ne.symm hj_ne); have heq2 : wdOcc h j₂ = 2 :=
          (by change (Finset.univ.filter fun x ↦ h x = j₂).card = 2; rw [hpr₂_h.1, hP₂]); omega
      have hP_same : p₁.1 = p₂.1 := by
        rw [← hpr₁.1, ← hpr₂_h.1]; change Finset.filter (fun x ↦ h x = j₁) Finset.univ =
          Finset.filter (fun x ↦ h x = j₂) Finset.univ; rw [hj_eq]
      rcases p₁ with ⟨P₁, g₁⟩; rcases p₂ with ⟨P₂, g₂⟩; dsimp only at hP_same hpr₁ hpr₂_h ⊢
      subst hP_same; refine Prod.ext rfl (funext fun i ↦ ?_)
      exact (hpr₁.2.2 i).symm.trans (hpr₂_h.2.2 i)
    · rcases (Finset.mem_filter.mp hh).2 with ⟨j₂, hj₂, hle1⟩
      let P := Finset.univ.filter fun x : Fin (n + 1) ↦ h x = j₂
      have hP2 : P.card = 2 := hj₂; have hne : P.Nonempty := Finset.card_pos.mp (by omega)
      set a₁ := P.min' hne; set a₂ := P.max' hne; have ha₁₂ : a₁ ≠ a₂ := (wd_finset_pair_min_max
        hP2).1
      let g : Fin n → Fin m := fun i ↦ h (wdInsertIdx a₂ i)
      have hg_inj : Function.Injective g := by
        intro i₁ i₂ heq_g; set x₁ := wdInsertIdx a₂ i₁
        set x₂ := wdInsertIdx a₂ i₂; have hx₁_ne : x₁ ≠ a₂ := wdInsertIdx_ne a₂ i₁
        have hx₂_ne : x₂ ≠ a₂ := wdInsertIdx_ne a₂ i₂
        have hxeq : x₁ = x₂ := by
          have hx₂_eq_x₁ : h x₂ = h x₁ := heq_g.symm; by_cases hj : h x₁ = j₂
          · have hx₁P : x₁ ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
            have hx₂P : x₂ ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₂_eq_x₁.trans hj⟩
            rw [(wd_finset_pair_min_max hP2).2] at hx₁P hx₂P; rcases Finset.mem_insert.mp hx₁P with
              h1 | h1
            · rcases Finset.mem_insert.mp hx₂P with h2 | h2
              · exact h1.trans h2.symm
              · exact False.elim (hx₂_ne (Finset.mem_singleton.mp h2))
            · exact False.elim (hx₁_ne (Finset.mem_singleton.mp h1))
          · exact Finset.card_le_one.mp (hle1 (h x₁) hj) x₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ
              x₁, rfl⟩) x₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ x₂, hx₂_eq_x₁⟩)
        have hsub_eq : (⟨x₁, hx₁_ne⟩ : {z : Fin (n + 1) // z ≠ a₂}) = ⟨x₂, hx₂_ne⟩ := Subtype.ext
          hxeq
        have hrem := congrArg (fun z : {z : Fin (n + 1) // z ≠ a₂} ↦ wdRemoveIdx a₂ z.1 z.2) hsub_eq
        dsimp only at hrem; rwa [wdRemoveIdx_insertIdx, wdRemoveIdx_insertIdx] at hrem
      have hmem : (P, g) ∈ Pairs ×ˢ InjN := Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ P, hP2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg_inj⟩⟩; refine ⟨(P,
        g), hmem, ?_⟩; funext x; dsimp only [mkFn]; have ha₁_j₂ : h a₁ = j₂ := (Finset.mem_filter.mp
        (Finset.min'_mem P hne)).2; have ha₂_j₂ : h a₂ = j₂ := (Finset.mem_filter.mp
        (Finset.max'_mem P hne)).2; have hg_a₁ : g (wdRemoveIdx a₂ a₁ ha₁₂) = j₂ :=
        (by dsimp only [g]; rw [wdInsertIdx_removeIdx, ha₁_j₂]); by_cases hx : x = a₂
      · subst hx; rw [dite_eq_left rfl, hg_a₁, ha₂_j₂]
      · rw [dite_eq_right hx]; dsimp only [g]; rw [wdInsertIdx_removeIdx]
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    card_filter_injective_fin n m]
private def wdSubSum {m : ℕ} (q : Fin m → ℝ) (c₀ : Fin m → ℕ)
    (s : Finset (Fin m)) (offset : ℕ) (G : ℕ → ℝ) : ℝ :=
  ∑ T ∈ s.powerset,
    (∏ j ∈ s, if j ∈ T then q j else 1 - q j) *
      G (offset + ∑ j ∈ s, if j ∈ T then c₀ j - 1 else c₀ j)
private lemma wdSubSum_empty {m : ℕ} (q : Fin m → ℝ) (c₀ : Fin m → ℕ) (offset : ℕ) (G : ℕ → ℝ) :
  wdSubSum q c₀ ∅ offset G = G offset := by simp [wdSubSum]
private lemma wdSubSum_insert_pos {m : ℕ} (q : Fin m → ℝ) (c₀ : Fin m → ℕ) {s : Finset (Fin m)} {j₀
  : Fin m} (hj₀ : j₀ ∉ s) (hc : 1 ≤ c₀ j₀) (offset : ℕ) (G : ℕ → ℝ) : wdSubSum q c₀ (insert j₀ s)
  offset G = wdSubSum q c₀ s (offset + c₀ j₀) (wdBernStep (q j₀) G) := by
  unfold wdSubSum; rw [Finset.sum_powerset_insert hj₀, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T hT ↦ ?_
  have hj₀T : j₀ ∉ T := fun hm ↦ hj₀ (Finset.mem_powerset.mp hT hm); have hprod_no : (∏ j ∈ insert
    j₀ s, if j ∈ T then q j else 1 - q j) = (1 - q j₀) * ∏ j ∈ s, if j ∈ T then q j else 1 - q j :=
    (by rw [Finset.prod_insert hj₀, ite_eq_right hj₀T])
  have hprod_yes : (∏ j ∈ insert j₀ s, if j ∈ insert j₀ T then q j else 1 - q j) = q j₀ * ∏ j ∈ s,
    if j ∈ T then q j else 1 - q j := by
    rw [Finset.prod_insert hj₀, ite_eq_left (Finset.mem_insert_self j₀ T)]; congr 1
    refine Finset.prod_congr rfl fun j hj ↦ ?_; have hjne : j ≠ j₀ := fun heq ↦ hj₀ (heq ▸ hj)
    simp [hjne]
  have hsum_no : (∑ j ∈ insert j₀ s, if j ∈ T then c₀ j - 1 else c₀ j) = c₀ j₀ + ∑ j ∈ s, if j ∈ T
    then c₀ j - 1 else c₀ j := (by rw [Finset.sum_insert hj₀, ite_eq_right hj₀T])
  have hsum_yes : (∑ j ∈ insert j₀ s, if j ∈ insert j₀ T then c₀ j - 1 else c₀ j) = (c₀ j₀ - 1) + ∑
    j ∈ s, if j ∈ T then c₀ j - 1 else c₀ j := by
    rw [Finset.sum_insert hj₀, ite_eq_left (Finset.mem_insert_self j₀ T)]; congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_; have hjne : j ≠ j₀ := fun heq ↦ hj₀ (heq ▸ hj)
    simp [hjne]
  set σ := ∑ j ∈ s, if j ∈ T then c₀ j - 1 else c₀ j
  set w := ∏ j ∈ s, if j ∈ T then q j else 1 - q j; rw [hprod_no, hprod_yes, hsum_no, hsum_yes]
  have hu_ne : offset + c₀ j₀ + σ ≠ 0 := (by omega); have hu_sub : offset + ((c₀ j₀ - 1) + σ) =
    offset + c₀ j₀ + σ - 1 := (by omega); have hu_add : offset + (c₀ j₀ + σ) = offset + c₀ j₀ + σ :=
    (by omega); rw [hu_sub, hu_add]; unfold wdBernStep; rw [ite_eq_right hu_ne]; ring
private lemma wdSubSum_insert_zero {m : ℕ} (q : Fin m → ℝ) (c₀ : Fin m → ℕ) {s : Finset (Fin m)} {j₀
  : Fin m} (hj₀ : j₀ ∉ s) (hc0 : c₀ j₀ = 0) (offset : ℕ) (G : ℕ → ℝ) : wdSubSum q c₀ (insert j₀ s)
  offset G = wdSubSum q c₀ s offset G := by
  unfold wdSubSum; rw [Finset.sum_powerset_insert hj₀, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T hT ↦ ?_
  have hj₀T : j₀ ∉ T := fun hm ↦ hj₀ (Finset.mem_powerset.mp hT hm); have hprod_no : (∏ j ∈ insert
    j₀ s, if j ∈ T then q j else 1 - q j) = (1 - q j₀) * ∏ j ∈ s, if j ∈ T then q j else 1 - q j :=
    (by rw [Finset.prod_insert hj₀, ite_eq_right hj₀T])
  have hprod_yes : (∏ j ∈ insert j₀ s, if j ∈ insert j₀ T then q j else 1 - q j) = q j₀ * ∏ j ∈ s,
    if j ∈ T then q j else 1 - q j := by
    rw [Finset.prod_insert hj₀, ite_eq_left (Finset.mem_insert_self j₀ T)]; congr 1
    refine Finset.prod_congr rfl fun j hj ↦ ?_; have hjne : j ≠ j₀ := fun heq ↦ hj₀ (heq ▸ hj)
    simp [hjne]
  have hsum_no : (∑ j ∈ insert j₀ s, if j ∈ T then c₀ j - 1 else c₀ j) = ∑ j ∈ s, if j ∈ T then c₀ j
    - 1 else c₀ j := (by rw [Finset.sum_insert hj₀, ite_eq_right hj₀T, hc0, zero_add])
  have hsum_yes : (∑ j ∈ insert j₀ s, if j ∈ insert j₀ T then c₀ j - 1 else c₀ j) = ∑ j ∈ s, if j ∈
    T then c₀ j - 1 else c₀ j := by
    rw [Finset.sum_insert hj₀, ite_eq_left (Finset.mem_insert_self j₀ T), hc0]
    simp only [Nat.zero_sub, zero_add]; refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjne : j ≠ j₀ := fun heq ↦ hj₀ (heq ▸ hj); simp [hjne]
  rw [hprod_no, hprod_yes, hsum_no, hsum_yes]; ring
private lemma wdSubSum_zero_set {m : ℕ} (q : Fin m → ℝ) (c₀ : Fin m → ℕ) (Z : Finset (Fin m)) (hZ :
  ∀ j ∈ Z, c₀ j = 0) (offset : ℕ) (G : ℕ → ℝ) : wdSubSum q c₀ Z offset G = G offset := by
  induction Z using Finset.induction with
  | empty => exact wdSubSum_empty q c₀ offset G
  | @insert j₀ Z hj₀ ih =>
    rw [wdSubSum_insert_zero q c₀ hj₀ (hZ j₀ (Finset.mem_insert_self j₀ Z))]
    exact ih fun j hj ↦ hZ j (Finset.mem_insert_of_mem hj)
private lemma wdSubSum_ones_union {m : ℕ} (q : Fin m → ℝ) (c₀ : Fin m → ℕ) (p₁ : ℝ) (S₁ Z : Finset
  (Fin m)) (hdisj : Disjoint S₁ Z) (hc1 : ∀ j ∈ S₁, c₀ j = 1) (hq1 : ∀ j ∈ S₁, q j = p₁) : ∀ (offset
  : ℕ) (G : ℕ → ℝ), wdSubSum q c₀ (S₁ ∪ Z) offset G = wdSubSum q c₀ Z (offset + S₁.card)
  ((wdBernStep p₁)^[S₁.card] G) := by
  induction S₁ using Finset.induction with
  | empty => intro offset G; simp
  | @insert j₀ S₁ hj₀ ih =>
    intro offset G; have hj₀Z : j₀ ∉ Z := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self j₀
      S₁); have hj₀_u : j₀ ∉ S₁ ∪ Z := (by simp [hj₀, hj₀Z]); have hdisj' : Disjoint S₁ Z :=
      Disjoint.mono_left (Finset.subset_insert j₀ S₁) hdisj
    have hc_j₀ : c₀ j₀ = 1 := hc1 j₀ (Finset.mem_insert_self j₀ S₁)
    have hq_j₀ : q j₀ = p₁ := hq1 j₀ (Finset.mem_insert_self j₀ S₁); rw [Finset.insert_union,
      Finset.card_insert_of_notMem hj₀, wdSubSum_insert_pos q c₀ hj₀_u (by omega) offset G, hc_j₀,
      hq_j₀, ih hdisj' (fun j hj ↦ hc1 j (Finset.mem_insert_of_mem hj)) (fun j hj ↦ hq1 j
      (Finset.mem_insert_of_mem hj)) (offset + 1) (wdBernStep p₁ G), Function.iterate_succ_apply]
    have hadd : offset + 1 + S₁.card = offset + (S₁.card + 1) := (by omega); rw [hadd]
private lemma subcubeStepExp_eq_wdSubSum {m : ℕ} (subDim K_sub : ℕ) (c₀ : Fin m → ℕ) (f : ℕ → ℝ) :
  subcubeStepExp subDim K_sub (fun c' ↦ f (∑ j : Fin m, c' j)) c₀ = wdSubSum (fun j ↦ p_succ_frac
  K_sub (c₀ j) subDim) c₀ Finset.univ 0 f := by
  classical
  let q (j : Fin m) : ℝ := p_succ_frac K_sub (c₀ j) subDim
  let e : (Fin m → Bool) ≃ Finset (Fin m) :=
    { toFun := fun b ↦ Finset.univ.filter fun j ↦ b j = true
      invFun := fun T j ↦ if j ∈ T then true else false
      left_inv := fun b ↦ by funext j; cases hbj : b j <;> simp [hbj]
      right_inv := fun T ↦ by ext j; by_cases hj : j ∈ T <;> simp [hj] }
  change (∑ b : Fin m → Bool,
    (∏ j : Fin m, match b j with | true => q j | false => 1 - q j) *
      f (∑ j : Fin m, if b j then c₀ j - 1 else c₀ j)) = _
  rw [Fintype.sum_equiv e _
    (fun T : Finset (Fin m) ↦
      (∏ j : Fin m, if j ∈ T then q j else 1 - q j) *
        f (0 + ∑ j : Fin m, if j ∈ T then c₀ j - 1 else c₀ j))
    (fun b ↦ by
      rw [zero_add]; congr 1
      · refine Finset.prod_congr rfl fun j _ ↦ ?_; cases hbj : b j <;> simp [e, hbj]
      · congr 1; refine Finset.sum_congr rfl fun j _ ↦ ?_
        cases hbj : b j <;> simp [e, hbj])]
  unfold wdSubSum; have hpow : (Finset.univ : Finset (Fin m)).powerset = Finset.univ :=
    (by ext T; simp); rw [hpow]
private lemma subcubeStepExp_mono_and_bounds {m : ℕ} (subDim K_sub : ℕ) (c₀ : Fin m → ℕ) {r : ℕ}
  (hsum_c : (∑ j : Fin m, c₀ j) = r) : (∀ {g₁ g₂ : ℕ → ℝ}, (∀ u ≤ r, g₁ u ≤ g₂ u) → subcubeStepExp
  subDim K_sub (fun c' ↦ g₁ (∑ j : Fin m, c' j)) c₀ ≤ subcubeStepExp subDim K_sub (fun c' ↦ g₂ (∑ j
  : Fin m, c' j)) c₀) ∧ (∀ {f : ℕ → ℝ}, (∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ r → f u₁ ≤ f u₂) → subcubeStepExp
  subDim K_sub (fun c' ↦ f (∑ j : Fin m, c' j)) c₀ ≤ f r) := by
  let wb (b : Fin m → Bool) : ℝ :=
    ∏ j : Fin m,
      match b j with
      | true => p_succ_frac K_sub (c₀ j) subDim | false => 1 - p_succ_frac K_sub (c₀ j) subDim
  have hwb_nn (b : Fin m → Bool) : 0 ≤ wb b := by
    refine Finset.prod_nonneg fun j _ ↦ ?_; cases b j
    · exact sub_nonneg.mpr (Real.sin_sq_le_one _)
    · exact sq_nonneg _
  have hwb_sum : (∑ b : Fin m → Bool, wb b) = 1 := by
    dsimp only [wb]
    refine (Fintype.prod_sum (fun (j : Fin m) (bj : Bool) ↦
      match bj with
      | true => p_succ_frac K_sub (c₀ j) subDim
      | false => 1 - p_succ_frac K_sub (c₀ j) subDim)).symm.trans ?_
    refine Finset.prod_eq_one fun j _ ↦ ?_; rw [Fintype.sum_bool]; ring
  have hsum_le (b : Fin m → Bool) : (∑ j : Fin m, if b j then c₀ j - 1 else c₀ j) ≤ r := by
    rw [← hsum_c]; exact Finset.sum_le_sum fun j _ ↦ by split_ifs <;> omega
  have hexp_eq (g : ℕ → ℝ) : subcubeStepExp subDim K_sub (fun c' ↦ g (∑ j : Fin m, c' j)) c₀ = ∑ b :
    Fin m → Bool, wb b * g (∑ j : Fin m, if b j then c₀ j - 1 else c₀ j) := rfl; refine ⟨fun {g₁ g₂}
    hg ↦ ?_, fun {f} hf_mono ↦ ?_⟩
  · rw [hexp_eq g₁, hexp_eq g₂]; exact Finset.sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left (hg _
      (hsum_le b)) (hwb_nn b)
  · rw [hexp_eq f]
    calc (∑ b : Fin m → Bool, wb b * f (∑ j : Fin m, if b j then c₀ j - 1 else c₀ j)) ≤ ∑ b : Fin m
          → Bool, wb b * f r := Finset.sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left (hf_mono _ r
          (hsum_le b) le_rfl) (hwb_nn b)
      _ = f r := by rw [← Finset.sum_mul, hwb_sum, one_mul]
private lemma sum_occ_eq_r {r m : ℕ} (h : Fin r → Fin m) : (∑ j : Fin m, (Finset.univ.filter fun a :
  Fin r ↦ h a = j).card) = r := by
  have hunion : (Finset.univ : Finset (Fin m)).biUnion (fun j ↦ Finset.univ.filter fun a : Fin r ↦ h
    a = j) = Finset.univ := (by ext a; simp)
  have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin m)) : Set (Fin m)) (fun j ↦
    Finset.univ.filter fun a : Fin r ↦ h a = j) := fun _ _ _ _ hne ↦ Finset.disjoint_left.mpr fun a
    h1 h2 ↦ hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  simpa using (Finset.card_biUnion hdisj).symm.trans (congrArg Finset.card hunion)
private lemma subcubeStepExp_eq_wdSinglePairRem {r m : ℕ} (subDim K_sub : ℕ) (p₁ p₂ : ℝ) (hp₁ :
  p_succ_frac K_sub 1 subDim = p₁) (hp₂ : p_succ_frac K_sub 2 subDim = p₂) (f : ℕ → ℝ) (h : Fin r →
  Fin m) (hsp : wdIsSinglePair h) : subcubeStepExp subDim K_sub (fun c' ↦ f (∑ j : Fin m, c' j))
  (wdOcc h) = wdSinglePairRem p₁ p₂ f r := by
  classical
  rcases hsp with ⟨j₂, hj₂, hle1⟩; let q (j : Fin m) : ℝ := p_succ_frac K_sub (wdOcc h j) subDim
  let S₁ : Finset (Fin m) := Finset.univ.filter fun j ↦ wdOcc h j = 1
  let Z : Finset (Fin m) := Finset.univ.filter fun j ↦ wdOcc h j = 0
  have hj₂_not_S₁ : j₂ ∉ S₁ := fun hm ↦ by
    have hc1 : wdOcc h j₂ = 1 := (Finset.mem_filter.mp hm).2; omega
  have hj₂_not_Z : j₂ ∉ Z := fun hm ↦ by
    have hc0 : wdOcc h j₂ = 0 := (Finset.mem_filter.mp hm).2; omega
  have hj₂_not_u : j₂ ∉ S₁ ∪ Z := (by simp [hj₂_not_S₁, hj₂_not_Z])
  have hdisj : Disjoint S₁ Z := Finset.disjoint_left.mpr fun j h1 h0 ↦ by
      have c1 : wdOcc h j = 1 := (Finset.mem_filter.mp h1).2; have c0 : wdOcc h j = 0 :=
        (Finset.mem_filter.mp h0).2; omega
  have huniv_eq : (Finset.univ : Finset (Fin m)) = insert j₂ (S₁ ∪ Z) := by
    ext j; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, S₁, Z,
      Finset.mem_filter, true_and, true_iff]; by_cases hj : j = j₂
    · exact Or.inl hj
    · have hle := hle1 j hj; omega
  have hcard_S₁ : 2 + S₁.card = r := by
    have hsum : (∑ j : Fin m, wdOcc h j) = r := sum_occ_eq_r h; rw [huniv_eq, Finset.sum_insert
      hj₂_not_u, Finset.sum_union hdisj, hj₂] at hsum
    have hsum1 : (∑ j ∈ S₁, wdOcc h j) = S₁.card := by
      have hc : ∀ j ∈ S₁, wdOcc h j = 1 := fun j hj ↦ (Finset.mem_filter.mp hj).2
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, mul_one]
    have hsum0 : (∑ j ∈ Z, wdOcc h j) = 0 := Finset.sum_eq_zero fun j hj ↦ (Finset.mem_filter.mp
      hj).2; omega
  have hs₁_sub : S₁.card = r - 2 := (by omega); rw [subcubeStepExp_eq_wdSubSum, huniv_eq,
    wdSubSum_insert_pos q (wdOcc h) hj₂_not_u (by omega) 0 f]; have hq_j₂ : q j₂ = p₂ :=
    (by dsimp only [q]; rw [hj₂, hp₂]); rw [zero_add, hj₂, hq_j₂, wdSubSum_ones_union q (wdOcc h) p₁
    S₁ Z hdisj (fun j hj ↦ (Finset.mem_filter.mp hj).2) (fun j hj ↦
    by dsimp only [q]; rw [(Finset.mem_filter.mp hj).2, hp₁]), wdSubSum_zero_set q (wdOcc h) Z (fun
    j hj ↦ (Finset.mem_filter.mp hj).2), hcard_S₁, hs₁_sub]; rfl
lemma wdExactOneDimStep_le_wdOneDimUpper (subN m : ℕ) (hm1 : 1 ≤ m) (sched : ℕ → Option (ℕ × List
  (PythPair × ℕ))) {f : ℕ → ℝ} {r : ℕ} (hf0 : f 0 = 0) (hf_mono : ∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ r → f u₁ ≤
  f u₂) : wdExactOneDimStep subN m sched f r ≤ wdOneDimUpper subN m sched f r := by
  classical
  unfold wdExactOneDimStep wdOneDimUpper; by_cases hr0 : r = 0
  · rw [ite_eq_left hr0, ite_eq_left hr0, hf0]
  · rw [ite_eq_right hr0, ite_eq_right hr0]
    cases sched r with
    | none => exact le_rfl
    | some kp =>
      rcases kp with ⟨kInit, probes⟩; dsimp only; have hm_pos : (0 : ℝ) < (m : ℝ) :=
        (by exact_mod_cast (by omega : 0 < m))
      have hmr_pos : (0 : ℝ) < (m : ℝ) ^ r := pow_pos hm_pos r; set θ₁ := Real.arcsin (1 / √(2 ^
        subN : ℝ)); set θ₂ := Real.arcsin (√(2 / (2 ^ subN : ℝ))); set u₀ := wdInitAmp r θ₁ kInit;
        set uf := wdChainFinalAmp r θ₁ probes u₀; set qDist := ((kInit + 1 : ℕ) : ℝ) +
        wdChainExtraQueries r θ₁ probes u₀; set remDist := ∑ w ∈ Finset.range (r + 1), (r.choose w :
        ℝ) * (uf w) ^ 2 * f (r - w); set qColl := (wdMaxQueries kInit probes : ℝ); set kTot :=
        wdTotalSteps kInit probes; set p₁ := Real.sin ((2 * (kTot : ℝ) + 1) * θ₁) ^ 2; set p₂ :=
        Real.sin ((2 * (kTot : ℝ) + 1) * θ₂) ^ 2; set pDist := rotCfProb m r; set pPair :=
        rotPairProb m r; set pRem := (1 - pDist) - pPair
      have hp₁_eq : p_succ_frac kTot 1 (2 ^ subN) = p₁ := by
        dsimp only [p₁, θ₁]; unfold p_succ_frac; rw [Nat.cast_one, Real.sqrt_div zero_le_one,
          Real.sqrt_one]; push_cast; rfl
      have hp₂_eq : p_succ_frac kTot 2 (2 ^ subN) = p₂ :=
        (by dsimp only [p₂, θ₂]; unfold p_succ_frac; push_cast; rfl)
      let U : Finset (Fin r → Fin m) := Finset.univ; let Inj := U.filter Function.Injective
      let Coll := U.filter fun h ↦ ¬ Function.Injective h
      let term (h : Fin r → Fin m) : ℝ :=
        if Function.Injective h then qDist + wdChainClickProb r θ₁ probes u₀ * f 0 + remDist
        else qColl + subcubeStepExp (2 ^ subN) kTot (fun c' ↦ f (∑ j : Fin m, c' j)) (wdOcc h)
      have hsplit_U : (∑ h ∈ U, term h) = (∑ h ∈ Inj, term h) + ∑ h ∈ Coll, term h :=
        (Finset.sum_filter_add_sum_filter_not U Function.Injective term).symm
      have hinj_sum : (∑ h ∈ Inj, term h) / (m : ℝ) ^ r = pDist * (qDist + remDist) := by
        have hconst : ∀ h ∈ Inj, term h = qDist + remDist := by
          intro h hh; dsimp only [term]; rw [ite_eq_left (Finset.mem_filter.mp hh).2, hf0, mul_zero,
            add_zero]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, card_filter_injective_fin r
          m, ← div_mul_eq_mul_div]; rfl
      have hcard_coll : (Coll.card : ℝ) / (m : ℝ) ^ r = 1 - pDist := by
        have hadd : Inj.card + Coll.card = U.card := by
          simpa [Inj, Coll] using Finset.sum_filter_add_sum_filter_not U Function.Injective (fun _ ↦
            (1 : ℕ))
        have hU_card : U.card = m ^ r := (by simp [U])
        have hinj_card : Inj.card = m.descFactorial r := card_filter_injective_fin r m
        have hadd_r : (m.descFactorial r : ℝ) + (Coll.card : ℝ) = (m : ℝ) ^ r := by
          have hc := congrArg (Nat.cast (R := ℝ)) hadd; simpa only [hinj_card, hU_card,
            Nat.cast_add, Nat.cast_pow] using hc
        dsimp only [pDist, rotCfProb]; field_simp [hmr_pos.ne']; linarith
      change (∑ h ∈ U, term h) / (m : ℝ) ^ r ≤ _; rw [hsplit_U, add_div, hinj_sum]
      by_cases hr2 : 2 ≤ r
      · let SP := Coll.filter wdIsSinglePair; let Rem := Coll.filter fun h ↦ ¬ wdIsSinglePair h
        have hSP_eq : SP = U.filter wdIsSinglePair := by
          ext h; simp only [SP, Coll, U, Finset.mem_filter, Finset.mem_univ, true_and,
            and_iff_right_iff_imp]; exact wdIsSinglePair_not_injective
        have hSP_prob : (SP.card : ℝ) / (m : ℝ) ^ r = pPair := by
          rw [hSP_eq, wd_card_singlePair_eq hr2]; dsimp only [pPair, rotPairProb]; rw [ite_eq_left
            hr2]; push_cast; rfl
        have hsplit_coll_card : SP.card + Rem.card = Coll.card := by
          simpa [SP, Rem] using Finset.sum_filter_add_sum_filter_not Coll wdIsSinglePair (fun _ ↦ (1
            : ℕ))
        have hRem_prob : (Rem.card : ℝ) / (m : ℝ) ^ r = pRem := by
          have hsum_p : (SP.card : ℝ) / (m : ℝ) ^ r + (Rem.card : ℝ) / (m : ℝ) ^ r = 1 - pDist :=
            (by rw [← add_div, ← Nat.cast_add, hsplit_coll_card, hcard_coll]); dsimp only [pRem];
            linarith
        have hcoll_rew : ∀ h ∈ Coll, term h = qColl + subcubeStepExp (2 ^ subN) kTot (fun c' ↦ f (∑
          j : Fin m, c' j)) (wdOcc h) :=
          (by intro h hh; dsimp only [term]; exact ite_eq_right (Finset.mem_filter.mp hh).2)
        have hcoll_le : (∑ h ∈ Coll, term h) / (m : ℝ) ^ r ≤ (1 - pDist) * qColl + pPair *
          wdSinglePairRem p₁ p₂ f r + pRem * f r := by
          rw [Finset.sum_congr rfl hcoll_rew, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul, add_div, ← div_mul_eq_mul_div, hcard_coll, ←
            Finset.sum_filter_add_sum_filter_not Coll wdIsSinglePair]
          have hsp_sum : (∑ h ∈ SP, subcubeStepExp (2 ^ subN) kTot (fun c' ↦ f (∑ j : Fin m, c' j))
            (wdOcc h)) = (SP.card : ℝ) * wdSinglePairRem p₁ p₂ f r := by
            have hc : ∀ h ∈ SP, subcubeStepExp (2 ^ subN) kTot (fun c' ↦ f (∑ j : Fin m, c' j))
              (wdOcc h) = wdSinglePairRem p₁ p₂ f r := fun h hh ↦ subcubeStepExp_eq_wdSinglePairRem
              (2 ^ subN) kTot p₁ p₂ hp₁_eq hp₂_eq f h (Finset.mem_filter.mp hh).2
            rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
          have hrem_le : (∑ h ∈ Rem, subcubeStepExp (2 ^ subN) kTot (fun c' ↦ f (∑ j : Fin m, c' j))
            (wdOcc h)) ≤ (Rem.card : ℝ) * f r := by
            calc _ ≤ ∑ _h ∈ Rem, f r := Finset.sum_le_sum fun h _ ↦ (subcubeStepExp_mono_and_bounds
                  (2 ^ subN) kTot (wdOcc h) (sum_occ_eq_r h)).2 hf_mono
              _ = (Rem.card : ℝ) * f r := by simp [Finset.sum_const, nsmul_eq_mul]
          have hdiv_le : ((∑ h ∈ SP, subcubeStepExp (2 ^ subN) kTot (fun c' ↦ f (∑ j : Fin m, c' j))
            (wdOcc h)) + ∑ h ∈ Rem, subcubeStepExp (2 ^ subN) kTot (fun c' ↦ f (∑ j : Fin m, c' j))
            (wdOcc h)) / (m : ℝ) ^ r ≤ pPair * wdSinglePairRem p₁ p₂ f r + pRem * f r := by
            rw [add_div, hsp_sum, ← div_mul_eq_mul_div, hSP_prob]
            exact add_le_add le_rfl (((div_le_div_of_nonneg_right hrem_le hmr_pos.le).trans_eq
              (div_mul_eq_mul_div _ _ _).symm).trans_eq (by rw [hRem_prob]))
          linarith
        linarith
      · have hr1 : r = 1 := (by omega); subst hr1
        have hcoll_empty : Coll = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro h hh; exact (Finset.mem_filter.mp hh).2 (fun
            a₁ a₂ _ ↦ Subsingleton.elim a₁ a₂)
        have hpDist1 : pDist = 1 := by
          dsimp only [pDist, rotCfProb]; rw [Nat.descFactorial_one, pow_one, div_self hm_pos.ne']
        have hpPair0 : pPair = 0 := (by dsimp only [pPair, rotPairProb]; rw [ite_eq_right hr2])
        have hpRem0 : pRem = 0 := (by dsimp only [pRem]; rw [hpDist1, hpPair0]; ring)
        simp [hcoll_empty, hpDist1, hpPair0, hpRem0]
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllWeakDicke
section WD_FindAllWeakDickeEval
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped NNReal NNRat ENNReal QProg.Notation QHLExpectation
@[expose] public section
/- ## Section 1: `10 ^ 15`-Scaled Signed Fixed-Point Interval Arithmetic -/

/-- Real cast of `wdScale = 10 ^ 15`. -/
abbrev wdScaleR : ℝ := (wdScale : ℝ)
private lemma wdScaleR_pos : 0 < wdScaleR := by unfold wdScaleR wdScale; norm_num
/-- Signed integer interval `(lo, hi)` representing `[lo / 10 ^ 15, hi / 10 ^ 15]`. -/
abbrev WDIVal := ℤ × ℤ
/-- Membership of `x: ℝ` in `[iv.1 / 10 ^ 15, iv.2 / 10 ^ 15]`. -/
def wdMem (x : ℝ) (iv : WDIVal) : Prop :=
  (iv.1 : ℝ) / wdScaleR ≤ x ∧ x ≤ (iv.2 : ℝ) / wdScaleR
/-- Floor integer division `⌊a / d⌋` for `0 < d`. -/
def wdDivFloor (a d : ℤ) : ℤ := a / d
/-- Ceiling integer division `⌈a / d⌉` for `0 < d`. -/
def wdDivCeil (a d : ℤ) : ℤ := -((-a) / d)
theorem wdDivFloor_le {a d : ℤ} (hd : 0 < d) : (wdDivFloor a d : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
  unfold wdDivFloor; have hdR : (0 : ℝ) < (d : ℝ) := (by exact_mod_cast hd); rw [le_div_iff₀ hdR];
    have hmul : (a / d) * d ≤ a := Int.ediv_mul_le a (ne_of_gt hd); exact_mod_cast hmul
theorem le_wdDivCeil {a d : ℤ} (hd : 0 < d) : (a : ℝ) / (d : ℝ) ≤ (wdDivCeil a d : ℝ) := by
  unfold wdDivCeil; have h := wdDivFloor_le (a := -a) hd; unfold wdDivFloor at h; push_cast at h ⊢
  rw [neg_div] at h; linarith
theorem wdDivFloor_le_wdDivCeil {a d : ℤ} (hd : 0 < d) : wdDivFloor a d ≤ wdDivCeil a d := by
  have h := (wdDivFloor_le (a := a) hd).trans (le_wdDivCeil (a := a) hd); exact_mod_cast h
theorem wdDivFloor_nonneg {a d : ℤ} (ha : 0 ≤ a) (hd : 0 < d) : 0 ≤ wdDivFloor a d :=
  Int.ediv_nonneg ha hd.le
theorem wdDivCeil_nonneg {a d : ℤ} (ha : 0 ≤ a) (hd : 0 < d) : 0 ≤ wdDivCeil a d :=
  (wdDivFloor_nonneg ha hd).trans (wdDivFloor_le_wdDivCeil hd)
def wdAdd (x y : WDIVal) : WDIVal := (x.1 + y.1, x.2 + y.2)
def wdSub (x y : WDIVal) : WDIVal := (x.1 - y.2, x.2 - y.1)
def wdScaleNat (c : ℕ) (x : WDIVal) : WDIVal := ((c : ℤ) * x.1, (c : ℤ) * x.2)
def wdRat (num : ℤ) (den : ℕ) : WDIVal :=
  (wdDivFloor (num * (wdScale : ℤ)) (den : ℤ), wdDivCeil (num * (wdScale : ℤ)) (den : ℤ))
def wdMul (x y : WDIVal) : WDIVal :=
  let p1 := x.1 * y.1
  let p2 := x.1 * y.2
  let p3 := x.2 * y.1
  let p4 := x.2 * y.2
  (wdDivFloor (min (min p1 p2) (min p3 p4)) (wdScale : ℤ),
    wdDivCeil (max (max p1 p2) (max p3 p4)) (wdScale : ℤ))
def wdSq (x : WDIVal) : WDIVal :=
  let p1 := x.1 * x.1
  let p2 := x.2 * x.2
  (if x.1 ≤ 0 ∧ 0 ≤ x.2 then 0 else wdDivFloor (min p1 p2) (wdScale : ℤ),
    wdDivCeil (max p1 p2) (wdScale : ℤ))
theorem wdMem_zero : wdMem 0 (0, 0) := by simp [wdMem]
theorem wdMem_one : wdMem 1 ((wdScale : ℤ), (wdScale : ℤ)) := by
  have hne : wdScaleR ≠ 0 := wdScaleR_pos.ne'; unfold wdMem
  constructor <;> push_cast <;> rw [div_self hne]
theorem wdMem_add {x y : ℝ} {ix iy : WDIVal} (hx : wdMem x ix) (hy : wdMem y iy) : wdMem (x + y)
  (wdAdd ix iy) := by
  unfold wdMem wdAdd at *
  constructor <;> push_cast <;> rw [add_div] <;> linarith
theorem wdMem_sub {x y : ℝ} {ix iy : WDIVal} (hx : wdMem x ix) (hy : wdMem y iy) : wdMem (x - y)
  (wdSub ix iy) := by
  unfold wdMem wdSub at *
  constructor <;> push_cast <;> rw [sub_div] <;> linarith
theorem wdMem_scaleNat (c : ℕ) {x : ℝ} {ix : WDIVal} (hx : wdMem x ix) : wdMem ((c : ℝ) * x)
  (wdScaleNat c ix) := by
  unfold wdMem wdScaleNat at *
  have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c; constructor
  · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hx.1 hc
  · push_cast; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hx.2 hc
theorem wdMem_rat {num : ℤ} {den : ℕ} (hden : 0 < den) : wdMem ((num : ℝ) / (den : ℝ)) (wdRat num
  den) := by
  have hdZ : (0 : ℤ) < (den : ℤ) := (by exact_mod_cast hden)
  have hB := wdScaleR_pos; unfold wdMem wdRat; constructor
  · rw [div_le_iff₀ hB]; have h := wdDivFloor_le (a := num * (wdScale : ℤ)) hdZ; push_cast at h ⊢;
      unfold wdScaleR
    rwa [div_mul_eq_mul_div]
  · rw [le_div_iff₀ hB]; have h := le_wdDivCeil (a := num * (wdScale : ℤ)) hdZ; push_cast at h ⊢;
      unfold wdScaleR
    rwa [div_mul_eq_mul_div]
private lemma real_mul_mem_corners {X Y x1 x2 y1 y2 : ℝ} (hx1 : x1 ≤ X) (hx2 : X ≤ x2) (hy1 : y1 ≤
  Y) (hy2 : Y ≤ y2) : min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 * y2)) ≤ X * Y ∧ X * Y ≤ max
  (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2)) := by
  have hmin1 : min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 * y2)) ≤ x1 * y1 := (min_le_left _
    _).trans (min_le_left _ _)
  have hmin2 : min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 * y2)) ≤ x1 * y2 := (min_le_left _
    _).trans (min_le_right _ _); have hmin3 : min (min (x1 * y1) (x1 * y2)) (min (x2 * y1) (x2 *
    y2)) ≤ x2 * y1 := (min_le_right _ _).trans (min_le_left _ _); have hmin4 : min (min (x1 * y1)
    (x1 * y2)) (min (x2 * y1) (x2 * y2)) ≤ x2 * y2 := (min_le_right _ _).trans (min_le_right _ _)
  have hmax1 : x1 * y1 ≤ max (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2)) := (le_max_left _
    _).trans (le_max_left _ _); have hmax2 : x1 * y2 ≤ max (max (x1 * y1) (x1 * y2)) (max (x2 * y1)
    (x2 * y2)) := (le_max_right _ _).trans (le_max_left _ _); have hmax3 : x2 * y1 ≤ max (max (x1 *
    y1) (x1 * y2)) (max (x2 * y1) (x2 * y2)) := (le_max_left _ _).trans (le_max_right _ _)
  have hmax4 : x2 * y2 ≤ max (max (x1 * y1) (x1 * y2)) (max (x2 * y1) (x2 * y2)) := (le_max_right _
    _).trans (le_max_right _ _); by_cases hY : 0 ≤ Y
  · constructor
    · by_cases hx : 0 ≤ x1 <;> nlinarith
    · by_cases hx : 0 ≤ x2 <;> nlinarith
  · constructor
    · by_cases hx : 0 ≤ x2 <;> nlinarith
    · by_cases hx : 0 ≤ x1 <;> nlinarith
theorem wdMem_mul {x y : ℝ} {ix iy : WDIVal} (hx : wdMem x ix) (hy : wdMem y iy) : wdMem (x * y)
  (wdMul ix iy) := by
  have hB := wdScaleR_pos; have hBZ : (0 : ℤ) < (wdScale : ℤ) := (by unfold wdScale; norm_num)
  have hx1 : (ix.1 : ℝ) ≤ x * wdScaleR := (div_le_iff₀ hB).mp hx.1; have hx2 : x * wdScaleR ≤ (ix.2
    : ℝ) := (le_div_iff₀ hB).mp hx.2
  have hy1 : (iy.1 : ℝ) ≤ y * wdScaleR := (div_le_iff₀ hB).mp hy.1; have hy2 : y * wdScaleR ≤ (iy.2
    : ℝ) := (le_div_iff₀ hB).mp hy.2; obtain ⟨hlo, hhi⟩ := real_mul_mem_corners hx1 hx2 hy1 hy2;
    unfold wdMem wdMul; dsimp only; constructor
  · rw [div_le_iff₀ hB]; refine (wdDivFloor_le hBZ).trans ?_
    push_cast; rw [div_le_iff₀ hB]; unfold wdScaleR at hlo ⊢; linarith [show (x * (wdScale : ℝ)) *
      (y * (wdScale : ℝ)) = x * y * (wdScale : ℝ) * (wdScale : ℝ) by ring]
  · rw [le_div_iff₀ hB]; refine le_trans ?_ (le_wdDivCeil hBZ); push_cast; rw [le_div_iff₀ hB];
      unfold wdScaleR at hhi ⊢; linarith [show (x * (wdScale : ℝ)) * (y * (wdScale : ℝ)) = x * y *
      (wdScale : ℝ) * (wdScale : ℝ) by ring]
theorem wdMem_sq {x : ℝ} {ix : WDIVal} (hx : wdMem x ix) : wdMem (x ^ 2) (wdSq ix) := by
  have hB := wdScaleR_pos; have hBZ : (0 : ℤ) < (wdScale : ℤ) := (by unfold wdScale; norm_num)
  have hx1 : (ix.1 : ℝ) ≤ x * wdScaleR := (div_le_iff₀ hB).mp hx.1; have hx2 : x * wdScaleR ≤ (ix.2
    : ℝ) := (le_div_iff₀ hB).mp hx.2; unfold wdMem wdSq; dsimp only; constructor
  · split_ifs with hz
    · simp only [Int.cast_zero, zero_div]; exact sq_nonneg x
    · rw [div_le_iff₀ hB]; refine (wdDivFloor_le hBZ).trans ?_; push_cast; rw [div_le_iff₀ hB];
        unfold wdScaleR at hx1 hx2 ⊢; have hmin1 : min ((ix.1 : ℝ) * ix.1) ((ix.2 : ℝ) * ix.2) ≤
        (ix.1 : ℝ) * ix.1 := min_le_left _ _; have hmin2 : min ((ix.1 : ℝ) * ix.1) ((ix.2 : ℝ) *
        ix.2) ≤ (ix.2 : ℝ) * ix.2 := min_le_right _ _; by_cases h1 : 0 < ix.1
      · have h1R : (0 : ℝ) < ix.1 := (by exact_mod_cast h1); nlinarith [show (x * (wdScale : ℝ)) ^ 2
          = x ^ 2 * (wdScale : ℝ) * (wdScale : ℝ) by ring]
      · have h2 : ix.2 < 0 := (by omega); have h2R : (ix.2 : ℝ) < 0 := (by exact_mod_cast h2)
        nlinarith [show (x * (wdScale : ℝ)) ^ 2 = x ^ 2 * (wdScale : ℝ) * (wdScale : ℝ) by ring]
  · rw [le_div_iff₀ hB]; refine le_trans ?_ (le_wdDivCeil hBZ); push_cast; rw [le_div_iff₀ hB];
      unfold wdScaleR at hx1 hx2 ⊢; have hmax1 : (ix.1 : ℝ) * ix.1 ≤ max ((ix.1 : ℝ) * ix.1) ((ix.2
      : ℝ) * ix.2) := le_max_left _ _
    have hmax2 : (ix.2 : ℝ) * ix.2 ≤ max ((ix.1 : ℝ) * ix.1) ((ix.2 : ℝ) * ix.2) := le_max_right _ _
    by_cases h0 : 0 ≤ x * (wdScale : ℝ) <;> nlinarith [show (x * (wdScale : ℝ)) ^ 2 = x ^ 2 *
      (wdScale : ℝ) * (wdScale : ℝ) by ring]
/- ## Section 2: Zero-`π` Dyadic Angle-Halving Trigonometric Enclosure -/
private lemma wd_sin_ge_deg3 {u : ℝ} (hu : 0 ≤ u) : u - u ^ 3 / 6 ≤ Real.sin u := by
  rcases hu.eq_or_lt with rfl | hpos
  · simp
  · linarith [Real.sin_gt_sub_cube hpos]
private lemma wd_cos_le_deg4 {u : ℝ} (hu : 0 ≤ u) : Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 := by
  let g : ℝ → ℝ := fun t ↦ 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (Real.sin t - (t - t ^ 3 / 6)) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ ↦ 1 - x ^ 2 / 2 + x ^ 4 / 24) (-t + t ^ 3 / 6) t := by
      convert ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24) using 1
      push_cast; ring
    convert h1.sub (Real.hasDerivAt_cos t) using 1
    ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun t _ ↦ (hg_deriv
      t).continuousAt.continuousWithinAt) (fun t _ ↦ (hg_deriv
      t).differentiableAt.differentiableWithinAt) (fun t ht ↦ ?_)
    rw [(hg_deriv t).deriv]; have ht0 : 0 ≤ t := interior_subset ht; linarith [wd_sin_ge_deg3 ht0]
  have h0 : g 0 ≤ g u := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  dsimp only [g] at h0; rw [Real.cos_zero] at h0; linarith
private lemma wd_sin_le_deg5 {u : ℝ} (hu : 0 ≤ u) : Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 := by
  let g : ℝ → ℝ := fun t ↦ t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ ↦ x - x ^ 3 / 6 + x ^ 5 / 120) (1 - t ^ 2 / 2 + t ^ 4 / 24) t
      := by
      convert ((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120) using 1
      push_cast; ring
    exact h1.sub (Real.hasDerivAt_sin t)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun t _ ↦ (hg_deriv
      t).continuousAt.continuousWithinAt) (fun t _ ↦ (hg_deriv
      t).differentiableAt.differentiableWithinAt) (fun t ht ↦ ?_)
    rw [(hg_deriv t).deriv]; have ht0 : 0 ≤ t := interior_subset ht; linarith [wd_cos_le_deg4 ht0]
  have h0 : g 0 ≤ g u := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  dsimp only [g] at h0; rw [Real.sin_zero] at h0; linarith
def wdTrigBase (u : WDIVal) : WDIVal × WDIVal :=
  let B : ℤ := wdScale
  let uh2 := wdDivCeil (u.2 * u.2) B
  let ul2 := wdDivFloor (u.1 * u.1) B
  let uh4 := wdDivCeil (uh2 * uh2) B
  let cLo := B - wdDivCeil (u.2 * u.2) (2 * B)
  let cHi := B - wdDivFloor (u.1 * u.1) (2 * B) + wdDivCeil uh4 24
  let uh3 := wdDivCeil (uh2 * u.2) B
  let ul3 := wdDivFloor (ul2 * u.1) B
  let uh5 := wdDivCeil (uh4 * u.2) B
  let sLo := max 0 (u.1 - wdDivCeil uh3 6)
  let sHi := u.2 - wdDivFloor ul3 6 + wdDivCeil uh5 120
  ((cLo, cHi), (sLo, sHi))
def wdDoubleAngleIter : ℕ → WDIVal × WDIVal → WDIVal × WDIVal
  | 0, cs => cs
  | k + 1, (c, s) =>
      wdDoubleAngleIter k (wdSub (wdSq c) (wdSq s), wdScaleNat 2 (wdMul s c))
def wdTrig (x : WDIVal) : WDIVal × WDIVal :=
  wdDoubleAngleIter 10 (wdTrigBase (wdDivFloor x.1 1024, wdDivCeil x.2 1024))
private lemma wdDoubleAngleIter_mem : ∀ (k : ℕ) {y : ℝ} {cIV sIV : WDIVal}, wdMem (Real.cos y) cIV →
  wdMem (Real.sin y) sIV → wdMem (Real.cos (2 ^ k * y)) (wdDoubleAngleIter k (cIV, sIV)).1 ∧ wdMem
  (Real.sin (2 ^ k * y)) (wdDoubleAngleIter k (cIV, sIV)).2
  | 0, y, cIV, sIV, hc, hs => by simpa [wdDoubleAngleIter] using ⟨hc, hs⟩
  | k + 1, y, cIV, sIV, hc, hs => by
    have hc2 : wdMem (Real.cos (2 * y)) (wdSub (wdSq cIV) (wdSq sIV)) :=
      (by rw [Real.cos_two_mul']; exact wdMem_sub (wdMem_sq hc) (wdMem_sq hs))
    have hs2 : wdMem (Real.sin (2 * y)) (wdScaleNat 2 (wdMul sIV cIV)) := by
      rw [Real.sin_two_mul, mul_assoc]; simpa [Nat.cast_ofNat] using wdMem_scaleNat 2 (wdMem_mul hs
        hc)
    have hih := wdDoubleAngleIter_mem k hc2 hs2; have hexp : (2 : ℝ) ^ (k + 1) * y = (2 : ℝ) ^ k *
      (2 * y) := (by rw [pow_succ]; ring)
    rwa [wdDoubleAngleIter, hexp]
private lemma wdTrigBase_mem {y : ℝ} {u : WDIVal} (hu0 : 0 ≤ u.1) (hu1 : u.2 ≤ (wdScale : ℤ)) (hy :
  wdMem y u) : wdMem (Real.cos y) (wdTrigBase u).1 ∧ wdMem (Real.sin y) (wdTrigBase u).2 := by
  have hB := wdScaleR_pos; have hBZ : (0 : ℤ) < (wdScale : ℤ) := (by unfold wdScale; norm_num)
  have h2BZ : (0 : ℤ) < 2 * (wdScale : ℤ) := (by unfold wdScale; norm_num)
  set ul : ℝ := (u.1 : ℝ) / wdScaleR; set uh : ℝ := (u.2 : ℝ) / wdScaleR; have hul0 : 0 ≤ ul :=
    div_nonneg (by exact_mod_cast hu0) hB.le; have hy0 : 0 ≤ y := hul0.trans hy.1; have huh1 : uh ≤
    1 := (by dsimp only [uh]; rw [div_le_one hB]; unfold wdScaleR; exact_mod_cast hu1)
  have hy_le_uh : y ≤ uh := hy.2; set uh2 : ℤ := wdDivCeil (u.2 * u.2) (wdScale : ℤ); set ul2 : ℤ :=
    wdDivFloor (u.1 * u.1) (wdScale : ℤ); set uh4 : ℤ := wdDivCeil (uh2 * uh2) (wdScale : ℤ)
  set uh3 : ℤ := wdDivCeil (uh2 * u.2) (wdScale : ℤ); set ul3 : ℤ := wdDivFloor (ul2 * u.1) (wdScale
    : ℤ); set uh5 : ℤ := wdDivCeil (uh4 * u.2) (wdScale : ℤ); have huh2_nn : 0 ≤ uh2 :=
    wdDivCeil_nonneg (mul_self_nonneg _) hBZ
  have hul2_nn : 0 ≤ ul2 := wdDivFloor_nonneg (mul_self_nonneg _) hBZ; have huh4_nn : 0 ≤ uh4 :=
    wdDivCeil_nonneg (mul_self_nonneg _) hBZ
  have hy2_le_uh2 : y ^ 2 ≤ (uh2 : ℝ) / wdScaleR := by
    have h1 : y ^ 2 ≤ uh ^ 2 := pow_le_pow_left₀ hy0 hy_le_uh 2
    have h2 : uh ^ 2 ≤ (uh2 : ℝ) / wdScaleR := by
      dsimp only [uh, uh2]; rw [div_pow, sq (u.2 : ℝ), sq wdScaleR, ← div_div]
      refine div_le_div_of_nonneg_right ?_ hB.le; simpa [wdScaleR] using le_wdDivCeil (a := u.2 *
        u.2) hBZ
    exact h1.trans h2
  have hul2_le_y2 : (ul2 : ℝ) / wdScaleR ≤ y ^ 2 := by
    have h1 : ul ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hul0 hy.1 2
    have h2 : (ul2 : ℝ) / wdScaleR ≤ ul ^ 2 := by
      dsimp only [ul, ul2]; rw [div_pow, sq (u.1 : ℝ), sq wdScaleR, ← div_div]
      refine div_le_div_of_nonneg_right ?_ hB.le; simpa [wdScaleR] using wdDivFloor_le (a := u.1 *
        u.1) hBZ
    exact h2.trans h1
  have hy4_le_uh4 : y ^ 4 ≤ (uh4 : ℝ) / wdScaleR := by
    have h1 : y ^ 4 = (y ^ 2) ^ 2 := (by ring); rw [h1]; have h2 : (y ^ 2) ^ 2 ≤ ((uh2 : ℝ) /
      wdScaleR) ^ 2 := pow_le_pow_left₀ (sq_nonneg y) hy2_le_uh2 2
    have h3 : ((uh2 : ℝ) / wdScaleR) ^ 2 ≤ (uh4 : ℝ) / wdScaleR := by
      dsimp only [uh4]; rw [div_pow, sq (uh2 : ℝ), sq wdScaleR, ← div_div]
      refine div_le_div_of_nonneg_right ?_ hB.le; simpa [wdScaleR] using le_wdDivCeil (a := uh2 *
        uh2) hBZ
    exact h2.trans h3
  have hy3_le_uh3 : y ^ 3 ≤ (uh3 : ℝ) / wdScaleR := by
    have h1 : y ^ 3 = y ^ 2 * y := (by ring); rw [h1]
    have h2 : y ^ 2 * y ≤ ((uh2 : ℝ) / wdScaleR) * uh := mul_le_mul hy2_le_uh2 hy_le_uh hy0
      (div_nonneg (by exact_mod_cast huh2_nn) hB.le)
    have h3 : ((uh2 : ℝ) / wdScaleR) * uh ≤ (uh3 : ℝ) / wdScaleR := by
      dsimp only [uh, uh3]; rw [div_mul_div_comm, ← sq, sq wdScaleR, ← div_div]
      refine div_le_div_of_nonneg_right ?_ hB.le; simpa using le_wdDivCeil (a := uh2 * u.2) hBZ
    exact h2.trans h3
  have hul3_le_y3 : (ul3 : ℝ) / wdScaleR ≤ y ^ 3 := by
    have h1 : y ^ 3 = y ^ 2 * y := (by ring); rw [h1]
    have h2 : ((ul2 : ℝ) / wdScaleR) * ul ≤ y ^ 2 * y := mul_le_mul hul2_le_y2 hy.1 hul0 (sq_nonneg
      y)
    have h3 : (ul3 : ℝ) / wdScaleR ≤ ((ul2 : ℝ) / wdScaleR) * ul := by
      dsimp only [ul, ul3]; rw [div_mul_div_comm, ← sq, sq wdScaleR, ← div_div]
      refine div_le_div_of_nonneg_right ?_ hB.le; simpa using wdDivFloor_le (a := ul2 * u.1) hBZ
    exact h3.trans h2
  have hy5_le_uh5 : y ^ 5 ≤ (uh5 : ℝ) / wdScaleR := by
    have h1 : y ^ 5 = y ^ 4 * y := (by ring); rw [h1]
    have h2 : y ^ 4 * y ≤ ((uh4 : ℝ) / wdScaleR) * uh := mul_le_mul hy4_le_uh4 hy_le_uh hy0
      (div_nonneg (by exact_mod_cast huh4_nn) hB.le)
    have h3 : ((uh4 : ℝ) / wdScaleR) * uh ≤ (uh5 : ℝ) / wdScaleR := by
      dsimp only [uh, uh5]; rw [div_mul_div_comm, ← sq, sq wdScaleR, ← div_div]
      refine div_le_div_of_nonneg_right ?_ hB.le; simpa using le_wdDivCeil (a := uh4 * u.2) hBZ
    exact h2.trans h3
  unfold wdTrigBase wdMem; dsimp only; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hc1 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos; have hc2 : 1 - uh ^ 2 /
      2 ≤ 1 - y ^ 2 / 2 := (by linarith [pow_le_pow_left₀ hy0 hy_le_uh 2])
    have hc3 : (((wdScale : ℤ) - wdDivCeil (u.2 * u.2) (2 * (wdScale : ℤ)) : ℤ) : ℝ) / wdScaleR ≤ 1
      - uh ^ 2 / 2 := by
      have hceil := le_wdDivCeil (a := u.2 * u.2) h2BZ; push_cast at hceil ⊢; rw [sub_div, div_self
        hB.ne']; dsimp only [uh, wdScaleR] at hceil ⊢; have hdiv : ((u.2 : ℝ) * u.2 / (2 * (wdScale
        : ℝ))) / (wdScale : ℝ) ≤ (wdDivCeil (u.2 * u.2) (2 * (wdScale : ℤ)) : ℝ) / (wdScale : ℝ) :=
        div_le_div_of_nonneg_right hceil hB.le; have heq : ((u.2 : ℝ) / (wdScale : ℝ)) ^ 2 / 2 =
        ((u.2 : ℝ) * u.2 / (2 * (wdScale : ℝ))) / (wdScale : ℝ) := (by ring); linarith
    exact (hc3.trans hc2).trans hc1
  · have hc1 := wd_cos_le_deg4 hy0; have hfl := wdDivFloor_le (a := u.1 * u.1) h2BZ; have hc4 :=
      le_wdDivCeil (a := uh4) (by omega : (0 : ℤ) < 24); push_cast at hfl hc4 ⊢
    have hfl_div : (wdDivFloor (u.1 * u.1) (2 * (wdScale : ℤ)) : ℝ) / wdScaleR ≤ y ^ 2 / 2 := by
      have hdiv : (wdDivFloor (u.1 * u.1) (2 * (wdScale : ℤ)) : ℝ) / wdScaleR ≤ ((u.1 : ℝ) * u.1 /
        (2 * (wdScale : ℝ))) / wdScaleR := div_le_div_of_nonneg_right hfl hB.le
      have heq : ((u.1 : ℝ) * u.1 / (2 * (wdScale : ℝ))) / wdScaleR = ul ^ 2 / 2 :=
        (by dsimp only [ul, wdScaleR]; ring); have hul_y : ul ^ 2 / 2 ≤ y ^ 2 / 2 :=
        (by linarith [pow_le_pow_left₀ hul0 hy.1 2]); exact (hdiv.trans_eq heq).trans hul_y
    have hc4_div : y ^ 4 / 24 ≤ (wdDivCeil uh4 24 : ℝ) / wdScaleR := by
      have h1 : y ^ 4 / 24 ≤ ((uh4 : ℝ) / 24) / wdScaleR :=
        (by rw [div_right_comm]; exact div_le_div_of_nonneg_right hy4_le_uh4 (by norm_num))
      exact h1.trans (div_le_div_of_nonneg_right hc4 hB.le)
    rw [add_div, sub_div, div_self hB.ne']; linarith
  · have hsin_nn : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0
      (by linarith [hy_le_uh, huh1, Real.pi_gt_three]); have hs1 := wd_sin_ge_deg3 hy0; have hc3 :=
      le_wdDivCeil (a := uh3) (by omega : (0 : ℤ) < 6); push_cast at hc3 ⊢; rw [div_le_iff₀ hB]
    refine max_le (mul_nonneg hsin_nn hB.le) ?_; rw [← div_le_iff₀ hB, sub_div]
    have hc3_div : y ^ 3 / 6 ≤ (wdDivCeil uh3 6 : ℝ) / wdScaleR := by
      have h1 : y ^ 3 / 6 ≤ ((uh3 : ℝ) / 6) / wdScaleR :=
        (by rw [div_right_comm]; exact div_le_div_of_nonneg_right hy3_le_uh3 (by norm_num))
      exact h1.trans (div_le_div_of_nonneg_right hc3 hB.le)
    linarith [hy.1]
  · have hs1 := wd_sin_le_deg5 hy0; have hf3 := wdDivFloor_le (a := ul3) (by omega : (0 : ℤ) < 6)
    have hc5 := le_wdDivCeil (a := uh5) (by omega : (0 : ℤ) < 120); push_cast at hf3 hc5 ⊢
    have hf3_div : (wdDivFloor ul3 6 : ℝ) / wdScaleR ≤ y ^ 3 / 6 := by
      have h1 := div_le_div_of_nonneg_right hf3 hB.le; rw [div_right_comm] at h1
      exact h1.trans (div_le_div_of_nonneg_right hul3_le_y3 (by norm_num))
    have hc5_div : y ^ 5 / 120 ≤ (wdDivCeil uh5 120 : ℝ) / wdScaleR := by
      have h1 : y ^ 5 / 120 ≤ ((uh5 : ℝ) / 120) / wdScaleR :=
        (by rw [div_right_comm]; exact div_le_div_of_nonneg_right hy5_le_uh5 (by norm_num))
      exact h1.trans (div_le_div_of_nonneg_right hc5 hB.le)
    rw [add_div, sub_div]; linarith [hy_le_uh]
theorem wdTrig_mem {x : ℝ} {iv : WDIVal} (h0 : 0 ≤ iv.1) (hhi : iv.2 ≤ 1024 * (wdScale : ℤ)) (hx :
  wdMem x iv) : wdMem (Real.cos x) (wdTrig iv).1 ∧ wdMem (Real.sin x) (wdTrig iv).2 := by
  have hB := wdScaleR_pos; have h1024 : (0 : ℤ) < 1024 := (by omega); set uIV : WDIVal :=
    (wdDivFloor iv.1 1024, wdDivCeil iv.2 1024); have hu0 : 0 ≤ uIV.1 := wdDivFloor_nonneg h0 h1024
  have hu1 : uIV.2 ≤ (wdScale : ℤ) := (by dsimp only [uIV, wdDivCeil]; omega)
  have hmem_u : wdMem (x / 1024) uIV := by
    unfold wdMem; dsimp only [uIV]; constructor
    · have hfl := wdDivFloor_le (a := iv.1) h1024; push_cast at hfl; have h1 :=
        div_le_div_of_nonneg_right hfl hB.le; rw [div_right_comm] at h1
      exact h1.trans (div_le_div_of_nonneg_right hx.1 (by norm_num))
    · have hcl := le_wdDivCeil (a := iv.2) h1024; push_cast at hcl; have h1 :=
        div_le_div_of_nonneg_right hcl hB.le; rw [div_right_comm] at h1
      exact (div_le_div_of_nonneg_right hx.2 (by norm_num)).trans h1
  obtain ⟨hc0, hs0⟩ := wdTrigBase_mem hu0 hu1 hmem_u; have hiter := wdDoubleAngleIter_mem 10 hc0 hs0
  have hx_eq : (2 : ℝ) ^ 10 * (x / 1024) = x := (by ring); simpa [wdTrig, uIV, hx_eq] using hiter
/- ## Section 3: Memoized Polynomial `dickeStepIV` & Multi-Pulse Chain Soundness -/
noncomputable def dickeStepIV : ℕ → WDIVal → WDIVal → (ℕ → WDIVal) → ℕ → WDIVal
  | 0, _, _, u, w' => if w' = 0 then u 0 else (0, 0)
  | r + 1, c, s, u, w' =>
      if w' ≤ r then
        wdSub (wdMul c (dickeStepIV r c s u w'))
          (wdMul s (dickeStepIV r c s (fun w ↦ u (w + 1)) w'))
      else if w' = r + 1 then
        wdAdd (wdMul s (dickeStepIV r c s u r))
          (wdMul c (dickeStepIV r c s (fun w ↦ u (w + 1)) r))
      else (0, 0)
theorem dickeStepIV_mem (r : ℕ) {c s : ℝ} {cIV sIV : WDIVal} (hc : wdMem c cIV) (hs : wdMem s sIV)
  {u : ℕ → ℝ} {uIV : ℕ → WDIVal} (hu : ∀ w, wdMem (u w) (uIV w)) : ∀ w', wdMem (dickeStep r c s u
  w') (dickeStepIV r cIV sIV uIV w') := by
  induction r generalizing u uIV with
  | zero =>
    intro w'; simp only [dickeStep, dickeStepIV]; split_ifs
    · exact hu 0
    · exact wdMem_zero
  | succ r ih =>
    intro w'; simp only [dickeStep, dickeStepIV]; split_ifs
    · exact wdMem_sub (wdMem_mul hc (ih hu w')) (wdMem_mul hs (ih (fun w ↦ hu (w + 1)) w'))
    · exact wdMem_add (wdMem_mul hs (ih hu r)) (wdMem_mul hc (ih (fun w ↦ hu (w + 1)) r))
    · exact wdMem_zero
def wdDampIV (r : ℕ) (cPyth : WDIVal) (uIV : ℕ → WDIVal) : ℕ → WDIVal :=
  fun w ↦ if w = r then wdMul cPyth (uIV w) else uIV w
theorem wdDampIV_mem (r : ℕ) {pyth : PythPair} {cPyth : WDIVal} (hc : wdMem pyth.cVal cPyth) {u : ℕ
  → ℝ} {uIV : ℕ → WDIVal} (hu : ∀ w, wdMem (u w) (uIV w)) : ∀ w, wdMem (wdDampAmp r pyth u w)
  (wdDampIV r cPyth uIV w) := by
  intro w; simp only [wdDampAmp, wdDampIV]; split_ifs
  · exact wdMem_mul hc (hu w)
  · exact hu w
def wdSumRangeZ : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, g => wdSumRangeZ n g + g n
theorem wdSumRangeZ_cast (n : ℕ) (g : ℕ → ℤ) : (wdSumRangeZ n g : ℝ) = ∑ w ∈ Finset.range n, (g w :
  ℝ) := by
  induction n with
  | zero => simp [wdSumRangeZ] | succ n ih => simp [wdSumRangeZ, Finset.sum_range_succ, ih]
def wdPi4InvHi : ℤ := 1273239544735163
def wdSqrt2Lo : ℤ := 1414213562373095
def wdSqrt2Hi : ℤ := 1414213562373096
/-- Single weak-Dicke probe specification `(daNum, daDen, cNum, sNum, cDen)`. -/
structure WDProbeSpec where
  daNum : ℕ
  daDen : ℕ
  cNum : ℤ
  sNum : ℕ
  cDen : ℕ
  deriving DecidableEq, Repr
/-- Heterogeneous multi-pulse Weak-Dicke row specification for `(m, pass, r)`. -/
structure WDRowSpec where
  a0Num : ℕ
  a0Den : ℕ
  probes : List WDProbeSpec
  deriving DecidableEq, Repr
/-- Subcube Grover iteration count `⌊(aNum / aDen) / (2 * θ₁)⌋₊`. -/
noncomputable def wdStepCount (aNum aDen subN : ℕ) : ℕ :=
  Nat.floor (((aNum : ℝ) / (aDen : ℝ)) / (2 * Real.arcsin (1 / √(2 ^ subN : ℝ))))
/-- Compiles one `WDProbeSpec` into `Option (PythPair × ℕ)` at subcube dimension `subN`. -/
noncomputable def compileWDProbe (p : WDProbeSpec) (subN : ℕ) : Option (PythPair × ℕ) :=
  if h : 0 < p.daDen ∧ 0 < p.cDen ∧ p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 = (p.cDen : ℤ) ^ 2 then
    some ({ cNum := p.cNum, sNum := p.sNum, cDen := p.cDen, hDen := h.2.1, hPyth := h.2.2 },
      wdStepCount p.daNum p.daDen subN)
  else
    none
/-- Compiles a `List WDProbeSpec` into `Option (List (PythPair × ℕ))` at `subN`. -/
noncomputable def compileWDProbes : List WDProbeSpec → ℕ → Option (List (PythPair × ℕ))
  | [], _ => some []
  | p :: rest, subN =>
      match compileWDProbe p subN, compileWDProbes rest subN with
      | some pk, some tail => some (pk :: tail)
      | _, _ => none
/-- Certified integer upper bound on `wdBernStep p` at `10 ^ 15` scale (`pLo ≤ p *
  wdScale`). -/
def wdBernStepHi (pLo : ℤ) (g15 : ℕ → ℤ) (u : ℕ) : ℤ :=
  if u = 0 then g15 0
  else g15 u - wdDivFloor (pLo * (g15 u - g15 (u - 1))) (wdScale : ℤ)
end
end QuantumComputation.Specs.DickeSol
end WD_FindAllWeakDickeEval
