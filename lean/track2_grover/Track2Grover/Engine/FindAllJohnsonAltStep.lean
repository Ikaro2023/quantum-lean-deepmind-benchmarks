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

public import Track2Grover.Engine.FindAllJohnsonP01

/-
# Alternating-Kernel Algebra, Orbit Intertwining, & Degree-`8` Polynomial Contraction

Self-contained development over `FindAllJohnsonP01` combining:
1. Binomial absorption, hockey-stick, Mobius inversion, closed-form alternating kernel
   `dAltEntry` / `dAltSymMat`, Johnson step-down intertwining, and orthogonal involution.
2. Isometric Johnson orbit embedding `orbEmbedGen`, fiber-sum intertwining `dAltOrbMat`,
   and `K`-step orbit walk hit-probability reduction `symHitProb_evalSymStage_dAlt`.
3. Euclidean `l_2` norm bounds, tridiagonal skew generator `dAltGenMat`, and degree-`8`
   truncated-exponential contraction, stability, and `q`-substep grouping bounds.
-/

namespace QuantumComputation.Specs.DickeSol

open Real
open scoped Matrix
@[expose] public section

/- ## Section 1: Binomial Absorption, Hockey-Stick, & Möbius Inversion -/
theorem choose_mul_choose {n m u : ℕ} (hum : u ≤ m) (hmn : m ≤ n) :
    n.choose m * m.choose u = n.choose u * (n - u).choose (m - u) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hu_lt_m : u < m := Nat.lt_of_succ_le hum
    have hu_lt_n : u < n := lt_of_lt_of_le hu_lt_m hmn; have ih' := ih hu_lt_m.le
    have h1 := Nat.choose_succ_right_eq n u; have h2 := Nat.choose_succ_right_eq m u
    have h3 := p01_choose_mul_succ (n - u - 1) (m - u - 1)
    have hn_sub : n - u - 1 + 1 = n - u := (by omega)
    have hm_sub : m - u - 1 + 1 = m - u := (by omega); rw [hn_sub, hm_sub] at h3
    have hn_u1 : n - (u + 1) = n - u - 1 := (by omega)
    have hm_u1 : m - (u + 1) = m - u - 1 := (by omega); rw [hn_u1, hm_u1]
    refine Nat.eq_of_mul_eq_mul_right (Nat.succ_pos u) ?_
    calc n.choose m * m.choose (u + 1) * (u + 1)
        = n.choose m * (m.choose (u + 1) * (u + 1)) := by ring
      _ = n.choose m * (m.choose u * (m - u)) := by rw [← h2]
      _ = (n.choose m * m.choose u) * (m - u) := by ring
      _ = (n.choose u * (n - u).choose (m - u)) * (m - u) := by rw [ih']
      _ = n.choose u * ((m - u) * (n - u).choose (m - u)) := by ring
      _ = n.choose u * ((n - u) * (n - u - 1).choose (m - u - 1)) := by rw [← h3]
      _ = (n.choose u * (n - u)) * (n - u - 1).choose (m - u - 1) := by ring
      _ = (n.choose (u + 1) * (u + 1)) * (n - u - 1).choose (m - u - 1) := by rw [← h1]
      _ = n.choose (u + 1) * (n - u - 1).choose (m - u - 1) * (u + 1) := by ring
theorem sum_choose_diag :
    ∀ (m K : ℕ),
      (∑ u ∈ Finset.range (m + 1), (K + m - u).choose (m - u)) = (K + m + 1).choose m
  | 0, K => by simp
  | m + 1, K => by
    rw [Finset.sum_range_succ']
    have hcongr :
        (∑ u ∈ Finset.range (m + 1), (K + (m + 1) - (u + 1)).choose (m + 1 - (u + 1))) =
          ∑ u ∈ Finset.range (m + 1), (K + m - u).choose (m - u) :=
      Finset.sum_congr rfl fun u _ ↦ by congr 1 <;> omega
    rw [hcongr, sum_choose_diag m K]
    have h0 : (K + (m + 1) - 0).choose (m + 1 - 0) = (K + m + 1).choose (m + 1) := rfl
    have hrhs : (K + (m + 1) + 1).choose (m + 1) = (K + m + 1 + 1).choose (m + 1) := rfl
    rw [h0, hrhs, Nat.choose_succ_succ (K + m + 1) m]
theorem mobius_binomial_eval (f : ℕ → ℝ) {m s : ℕ} (hsm : s ≤ m) : (∑ r ∈ Finset.range (m + 1), (∑
    t ∈ Finset.range (r + 1), (-1 : ℝ) ^ (r - t) * (r.choose t : ℝ) * f t) * (s.choose r : ℝ)) = f
    s := by
  have htrunc : (∑ r ∈ Finset.range (m + 1), (∑ t ∈ Finset.range (r + 1), (-1 : ℝ) ^ (r - t) *
    (r.choose t : ℝ) * f t) * (s.choose r : ℝ)) = ∑ r ∈ Finset.range (s + 1), (∑ t ∈ Finset.range
    (r + 1), (-1 : ℝ) ^ (r - t) * (r.choose t : ℝ) * f t) * (s.choose r : ℝ) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun r _ hr_not ↦ ?_
    have hsr : s < r := (by simp only [Finset.mem_range, not_lt] at hr_not; omega)
    rw [Nat.choose_eq_zero_of_lt hsr, Nat.cast_zero, mul_zero]
  rw [htrunc]
  have hexp : (∑ r ∈ Finset.range (s + 1), (∑ t ∈ Finset.range (r + 1), (-1 : ℝ) ^ (r - t) *
    (r.choose t : ℝ) * f t) * (s.choose r : ℝ)) = ∑ r ∈ Finset.range (s + 1), ∑ t ∈ Finset.range
    (s + 1), if t ≤ r then f t * ((-1 : ℝ) ^ (r - t) * ((s.choose r * r.choose t : ℕ) : ℝ)) else
    0 := by
    refine Finset.sum_congr rfl fun r hr ↦ ?_
    have hrs : r ≤ s := (by simp only [Finset.mem_range] at hr; omega); rw [Finset.sum_mul]
    rw [← Finset.sum_filter]
    have hflt : (Finset.range (s + 1)).filter (· ≤ r) = Finset.range (r + 1) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hflt]; refine Finset.sum_congr rfl fun t _ ↦ ?_
    push_cast; ring
  rw [hexp, Finset.sum_comm]
  have hinner (t : ℕ) (ht : t ∈ Finset.range (s + 1)) : (∑ r ∈ Finset.range (s + 1), if t ≤ r then
    f t * ((-1 : ℝ) ^ (r - t) * ((s.choose r * r.choose t : ℕ) : ℝ)) else 0) = if t = s then f s
    else 0 := by
    have hts : t ≤ s := (by simp only [Finset.mem_range] at ht; omega); rw [← Finset.sum_filter]
    have hbij :
        (∑ r ∈ (Finset.range (s + 1)).filter (t ≤ ·),
          f t * ((-1 : ℝ) ^ (r - t) * ((s.choose r * r.choose t : ℕ) : ℝ))) =
        ∑ u ∈ Finset.range (s - t + 1),
          f t * ((s.choose t : ℝ) * ((-1 : ℝ) ^ u * ((s - t).choose u : ℝ))) := by
      refine Finset.sum_bij (fun r _ ↦ r - t) (fun r hr ↦ ?_) (fun r₁ hr₁ r₂ hr₂ heq ↦ ?_) (fun u
        hu ↦ ?_) (fun r hr ↦ ?_)
      · simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢; omega
      · simp only [Finset.mem_filter] at hr₁ hr₂; omega
      · simp only [Finset.mem_range] at hu
        refine ⟨t + u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
      · simp only [Finset.mem_filter, Finset.mem_range] at hr
        rw [choose_mul_choose hr.2 (by omega)]; push_cast; ring
    rw [hbij, ← Finset.mul_sum, ← Finset.mul_sum]
    have halt : (∑ u ∈ Finset.range (s - t + 1), (-1 : ℝ) ^ u * ((s - t).choose u : ℝ)) = if s - t
      = 0 then 1 else 0 := by
      have hpow := add_pow (-1 : ℝ) 1 (s - t); rw [neg_add_cancel] at hpow
      have hcongr : (∑ u ∈ Finset.range (s - t + 1), (-1 : ℝ) ^ u * ((s - t).choose u : ℝ)) = ∑ u
        ∈ Finset.range (s - t + 1), (-1 : ℝ) ^ u * (1 : ℝ) ^ (s - t - u) * ((s - t).choose u :
        ℝ) := by
        refine Finset.sum_congr rfl fun u _ ↦ by simp
      rw [hcongr, ← hpow]; by_cases h0 : s - t = 0
      · rw [h0]; simp
      · simp [h0, zero_pow h0]
    rw [halt]; by_cases hteq : t = s
    · subst hteq; simp
    · have hne : s - t ≠ 0 := (by omega); simp [hteq, hne]
  rw [Finset.sum_congr rfl hinner]; simp
/- ## Section 2: Closed-Form Kernel `dAltEntry`, `dAltSymMat`, & Step-Down Intertwining -/
/-- Closed-form intersection weight for `D_{\text{alt}}` on `N = 2 * M`. -/
noncomputable def dAltEntry (M m s : ℕ) : ℝ :=
  if m = 0 then 1
  else (-1 : ℝ) ^ s * ((M - m : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose (m - s) : ℝ))
/-- Closed-form alternating odd/even Johnson reflection `D_{\text{alt}}` on `P01Subset N m`. -/
noncomputable def dAltSymMat (N m : ℕ) : Matrix (P01Subset N m) (P01Subset N m) ℝ :=
  Matrix.of fun E F ↦ dAltEntry (N / 2) m (E.1 ∩ F.1).card
/-- Subset-inclusion operator `B_{r, m}(U, E) = [U ⊆ E]` from `m`-subsets to `r`-subsets. -/
noncomputable def jDownGenMat (N r m : ℕ) : Matrix (P01Subset N r) (P01Subset N m) ℝ :=
  Matrix.of fun U E ↦ if U.1 ⊆ E.1 then 1 else 0
theorem dAltSymMat_transpose (N m : ℕ) : (dAltSymMat N m)ᵀ = dAltSymMat N m := by
  ext E F; simp [dAltSymMat, Finset.inter_comm]
private lemma dAltEntry_pascal {M k s : ℕ} (hkM : k + 1 < M) (hsk : s ≤ k) : ((k + 1 - s : ℕ) :
    ℝ) * dAltEntry M (k + 1) (s + 1) + ((2 * M - 2 * k - 1 + s : ℕ) : ℝ) * dAltEntry M (k + 1) s =
    (s : ℝ) * dAltEntry M k (s - 1) + ((k + 1 - s : ℕ) : ℝ) * dAltEntry M k s := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_succ (n t : ℕ) : dAltEntry M (n + 1) t =
      (-1 : ℝ) ^ t * ((M - (n + 1) : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose (n + 1 - t) : ℝ)) := rfl
  by_cases hk0 : k = 0
  · subst hk0; have hs0 : s = 0 := (by omega); subst hs0
    have hs2M : 2 * M - 2 * 0 - 1 + 0 = 2 * M - 1 := (by omega)
    have hs01 : 0 + 1 - 0 = 1 := (by omega); have hs00 : (0 : ℕ) - 1 = 0 := (by omega)
    have he11 : dAltEntry M 1 1 =
        (-1 : ℝ) ^ 1 * ((M - 1 : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose 0 : ℝ)) := rfl
    have he10 : dAltEntry M 1 0 =
        (-1 : ℝ) ^ 0 * ((M - 1 : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose 1 : ℝ)) := rfl
    have he00 : dAltEntry M 0 0 = 1 := rfl
    rw [hs01, hs2M, hs00, show (0 : ℕ) + 1 = 1 from rfl, he11, he10, he00]
    have hM1_pos : (0 : ℝ) < ((M - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
    have h2M : ((2 * M - 1 : ℕ) : ℝ) = 2 * (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * M), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [Nat.choose_zero_right, Nat.choose_one_right, h2M]; push_cast; field_simp; rw [hM1]; ring
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; set k := k' + 1; set u := k - s
    have hu_lt : u < M - 1 := (by omega)
    have hc0_pos : (0 : ℝ) < ((M - 1).choose u : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hc1_pos : (0 : ℝ) < ((M - 1).choose (u + 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hrel_nat := Nat.choose_succ_right_eq (M - 1) u
    have hrel : ((M - 1).choose (u + 1) : ℝ) * ((u + 1 : ℕ) : ℝ) = ((M - 1).choose u : ℝ) * ((M -
      1 - u : ℕ) : ℝ) := by
      exact_mod_cast hrel_nat
    have hk1_s1 : k + 1 - (s + 1) = u := (by omega); have hk1_s : k + 1 - s = u + 1 := (by omega)
    have hk_s : k - s = u := rfl
    rw [hd_succ k (s + 1), hd_succ k s, hd_succ k' (s - 1), hd_succ k' s]
    change ((k + 1 - s : ℕ) : ℝ) * ((-1 : ℝ) ^ (s + 1) * ((M - (k + 1) : ℕ) : ℝ) / ((M : ℝ) *
      ((M - 1).choose (k + 1 - (s + 1)) : ℝ))) + ((2 * M - 2 * k - 1 + s : ℕ) : ℝ) * ((-1 : ℝ) ^
      s * ((M - (k + 1) : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose (k + 1 - s) : ℝ))) = (s : ℝ) * ((-1
      : ℝ) ^ (s - 1) * ((M - k : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose (k - (s - 1)) : ℝ))) + ((k +
      1 - s : ℕ) : ℝ) * ((-1 : ℝ) ^ s * ((M - k : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose (k - s) :
      ℝ)))
    rw [hk1_s1, hk1_s, hk_s]
    have hcast1 : ((M - (k + 1) : ℕ) : ℝ) = (M : ℝ) - (k : ℝ) - 1 := by
      have hle : k + 1 ≤ M := (by omega); rw [Nat.cast_sub hle]; push_cast; ring
    have hcast2 : ((M - k : ℕ) : ℝ) = (M : ℝ) - (k : ℝ) := Nat.cast_sub (by omega)
    have hcast3 : ((2 * M - 2 * k - 1 + s : ℕ) : ℝ) =
        2 * (M : ℝ) - 2 * (k : ℝ) - 1 + (s : ℝ) := by
      have hle1 : 2 * k + 1 ≤ 2 * M := (by omega)
      have hsub : 2 * M - 2 * k - 1 = 2 * M - (2 * k + 1) := (by omega)
      rw [Nat.cast_add, hsub, Nat.cast_sub hle1]; push_cast; ring
    have hcast4 : ((M - 1 - u : ℕ) : ℝ) = (M : ℝ) - 1 - (u : ℝ) := by
      have hle1 : u + 1 ≤ M := (by omega); have hsub : M - 1 - u = M - (u + 1) := (by omega)
      rw [hsub, Nat.cast_sub hle1]; push_cast; ring
    have hus : (u : ℝ) = (k : ℝ) - (s : ℝ) := by
      have h : u + s = k := (by omega)
      have h' : (u : ℝ) + (s : ℝ) = (k : ℝ) := (by exact_mod_cast h); linarith
    rw [hcast4] at hrel; push_cast at hrel
    have hswap (X : ℝ) : ((u + 1 : ℕ) : ℝ) * (X / ((M : ℝ) * ((M - 1).choose u : ℝ))) = ((M : ℝ) -
      1 - (u : ℝ)) * X / ((M : ℝ) * ((M - 1).choose (u + 1) : ℝ)) := by
      push_cast
      rw [mul_div_assoc', div_eq_div_iff (mul_ne_zero hM_pos.ne' hc0_pos.ne')
        (mul_ne_zero hM_pos.ne' hc1_pos.ne')]
      calc (((u : ℝ) + 1) * X) * ((M : ℝ) * ((M - 1).choose (u + 1) : ℝ))
          = (M : ℝ) * X * (((M - 1).choose (u + 1) : ℝ) * ((u : ℝ) + 1)) := by ring
        _ = (M : ℝ) * X * (((M - 1).choose u : ℝ) * ((M : ℝ) - 1 - (u : ℝ))) := by rw [hrel]
        _ = (((M : ℝ) - 1 - (u : ℝ)) * X) * ((M : ℝ) * ((M - 1).choose u : ℝ)) := by ring
    rw [hswap, hswap]; by_cases hs0 : s = 0
    · subst hs0
      simp only [Nat.cast_zero, zero_mul, zero_add, sub_zero, pow_zero, pow_one] at hcast3 hus ⊢
      rw [hcast1, hcast2, hcast3, hus]; ring
    · have hs1 : k - (s - 1) = u + 1 := (by omega)
      have hpow_s1 : (-1 : ℝ) ^ (s - 1) = - ((-1 : ℝ) ^ s) := by
        conv_rhs => rw [show s = (s - 1) + 1 by omega, pow_succ]
        ring
      have hpow_sp1 : (-1 : ℝ) ^ (s + 1) = - ((-1 : ℝ) ^ s) := (by rw [pow_succ]; ring)
      rw [hs1, hpow_s1, hpow_sp1, hcast1, hcast2, hcast3, hus]; ring
theorem jDownMat_mul_dAltSymMat {M k : ℕ} (hkM : k + 1 < M) : jDownGenMat (2 * M) k (k + 1) *
    dAltSymMat (2 * M) (k + 1) = dAltSymMat (2 * M) k * jDownGenMat (2 * M) k (k + 1) := by
  have hdiv : (2 * M) / 2 = M := (by omega); ext T F
  simp only [Matrix.mul_apply, jDownGenMat, dAltSymMat, Matrix.of_apply, hdiv]
  set s := (T.1 ∩ F.1).card
  have hsk : s ≤ k := (Finset.card_le_card Finset.inter_subset_left).trans T.2.le
  have hlhs : (∑ E : P01Subset (2 * M) (k + 1), (if T.1 ⊆ E.1 then (1 : ℝ) else 0) * dAltEntry M
    (k + 1) (E.1 ∩ F.1).card) = ((k + 1 - s : ℕ) : ℝ) * dAltEntry M (k + 1) (s + 1) + ((2 * M -
    2 * k - 1 + s : ℕ) : ℝ) * dAltEntry M (k + 1) s := by
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    have hbij : (∑ E ∈ Finset.univ.filter (fun E : P01Subset (2 * M) (k + 1) ↦ T.1 ⊆ E.1),
      dAltEntry M (k + 1) (E.1 ∩ F.1).card) = ∑ x ∈ T.1ᶜ, dAltEntry M (k + 1) ((insert x T.1) ∩
      F.1).card := by
      symm
      refine Finset.sum_bij (fun x hx ↦ ⟨insert x T.1, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hx), T.2]⟩)
        (fun x _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_insert x T.1⟩)
        (fun x₁ hx₁ x₂ hx₂ heq ↦ ?_)
        (fun E hE ↦ ?_)
        (fun _ _ ↦ rfl)
      · have hset : insert x₁ T.1 = insert x₂ T.1 := Subtype.mk.inj heq
        have hx1_in : x₁ ∈ insert x₂ T.1 := hset ▸ Finset.mem_insert_self x₁ T.1
        rcases Finset.mem_insert.mp hx1_in with rfl | hxT
        · rfl
        · exact absurd hxT (Finset.mem_compl.mp hx₁)
      · have hsub : T.1 ⊆ E.1 := (Finset.mem_filter.mp hE).2
        have hcd : (E.1 \ T.1).card = 1 := by rw [Finset.card_sdiff_of_subset hsub, E.2, T.2]; omega
        obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hcd
        have hx_mem : x ∈ E.1 \ T.1 := hx_eq ▸ Finset.mem_singleton_self x
        rcases Finset.mem_sdiff.mp hx_mem with ⟨hxE, hxT⟩
        refine ⟨x, Finset.mem_compl.mpr hxT, Subtype.ext ?_⟩
        ext z; simp only [Finset.mem_insert]; constructor
        · rintro (rfl | hzT)
          · exact hxE
          · exact hsub hzT
        · intro hzE; by_cases hzT : z ∈ T.1
          · exact Or.inr hzT
          · have hz_sdiff : z ∈ E.1 \ T.1 := Finset.mem_sdiff.mpr ⟨hzE, hzT⟩
            rw [hx_eq, Finset.mem_singleton] at hz_sdiff; exact Or.inl hz_sdiff
    rw [hbij, ← Finset.sum_filter_add_sum_filter_not (s := T.1ᶜ) (p := (· ∈ F.1))]
    have hf1 : T.1ᶜ.filter (· ∈ F.1) = F.1 \ T.1 := (by ext x; simp [Finset.mem_sdiff, and_comm])
    have hf2 : T.1ᶜ.filter (fun x ↦ x ∉ F.1) = (T.1 ∪ F.1)ᶜ := (by ext x; simp); rw [hf1, hf2]
    have hs1 : (∑ x ∈ F.1 \ T.1, dAltEntry M (k + 1) ((insert x T.1) ∩ F.1).card) = ((k + 1 - s :
      ℕ) : ℝ) * dAltEntry M (k + 1) (s + 1) := by
      have hc : (∑ x ∈ F.1 \ T.1, dAltEntry M (k + 1) ((insert x T.1) ∩ F.1).card) = ∑ _ ∈ F.1 \
        T.1, dAltEntry M (k + 1) (s + 1) := by
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        rcases Finset.mem_sdiff.mp hx with ⟨hxF, hxT⟩
        have hint : (insert x T.1) ∩ F.1 = insert x (T.1 ∩ F.1) := by
          ext z; simp only [Finset.mem_inter, Finset.mem_insert]
          exact ⟨fun ⟨h, hzF⟩ ↦ h.elim Or.inl (fun hzT ↦ Or.inr ⟨hzT, hzF⟩),
            fun h ↦ h.elim (fun hzx ↦ ⟨Or.inl hzx, hzx ▸ hxF⟩) (fun ⟨hzT, hzF⟩ ↦ ⟨Or.inr hzT, hzF⟩)⟩
        have hx_nin : x ∉ T.1 ∩ F.1 := fun h ↦ hxT (Finset.mem_inter.mp h).1
        rw [hint, Finset.card_insert_of_notMem hx_nin]
      have hcard_sdiff : (F.1 \ T.1).card = k + 1 - s := by
        have h := Finset.card_sdiff_add_card_inter F.1 T.1; rw [Finset.inter_comm, F.2] at h; omega
      rw [hc, Finset.sum_const, hcard_sdiff, nsmul_eq_mul]
    have hs2 : (∑ x ∈ (T.1 ∪ F.1)ᶜ, dAltEntry M (k + 1) ((insert x T.1) ∩ F.1).card) = ((2 * M -
      2 * k - 1 + s : ℕ) : ℝ) * dAltEntry M (k + 1) s := by
      have hc : (∑ x ∈ (T.1 ∪ F.1)ᶜ, dAltEntry M (k + 1) ((insert x T.1) ∩ F.1).card) = ∑ _ ∈ (T.1
        ∪ F.1)ᶜ, dAltEntry M (k + 1) s := by
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hxF : x ∉ F.1 := fun h ↦ Finset.mem_compl.mp hx (Finset.mem_union_right T.1 h)
        have hint : (insert x T.1) ∩ F.1 = T.1 ∩ F.1 := by
          ext z; simp only [Finset.mem_inter, Finset.mem_insert]
          exact ⟨fun ⟨h, hzF⟩ ↦ ⟨h.resolve_left (fun hzx ↦ hxF (hzx ▸ hzF)), hzF⟩,
            fun ⟨hzT, hzF⟩ ↦ ⟨Or.inr hzT, hzF⟩⟩
        rw [hint]
      have hu_card : (T.1 ∪ F.1).card = 2 * k + 1 - s := by
        have h := Finset.card_union_add_card_inter T.1 F.1; rw [T.2, F.2] at h; omega
      have hc_card : (T.1 ∪ F.1)ᶜ.card = 2 * M - 2 * k - 1 + s := by
        have hle : (T.1 ∪ F.1).card ≤ 2 * M :=
          (T.1 ∪ F.1).card_le_univ.trans_eq (Fintype.card_fin (2 * M))
        rw [Finset.card_compl, Fintype.card_fin]; omega
      rw [hc, Finset.sum_const, hc_card, nsmul_eq_mul]
    rw [hs1, hs2]
  have hrhs : (∑ T' : P01Subset (2 * M) k, dAltEntry M k (T.1 ∩ T'.1).card * (if T'.1 ⊆ F.1 then
    (1 : ℝ) else 0)) = (s : ℝ) * dAltEntry M k (s - 1) + ((k + 1 - s : ℕ) : ℝ) * dAltEntry M k
    s := by
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    have hbij : (∑ T' ∈ Finset.univ.filter (fun T' : P01Subset (2 * M) k ↦ T'.1 ⊆ F.1), dAltEntry
      M k (T.1 ∩ T'.1).card) = ∑ y ∈ F.1, dAltEntry M k (T.1 ∩ F.1.erase y).card := by
      symm
      refine Finset.sum_bij (fun y hy ↦ ⟨F.1.erase y, by
          rw [Finset.card_erase_of_mem hy, F.2]; omega⟩)
        (fun y _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.erase_subset y F.1⟩)
        (fun y₁ hy₁ y₂ hy₂ heq ↦ ?_)
        (fun T' hT' ↦ ?_)
        (fun _ _ ↦ rfl)
      · have hset : F.1.erase y₁ = F.1.erase y₂ := Subtype.mk.inj heq
        by_contra hne
        have hy1_in : y₁ ∈ F.1.erase y₂ := Finset.mem_erase.mpr ⟨hne, hy₁⟩; rw [← hset] at hy1_in
        exact (Finset.mem_erase.mp hy1_in).1 rfl
      · have hsub : T'.1 ⊆ F.1 := (Finset.mem_filter.mp hT').2
        have hcd : (F.1 \ T'.1).card = 1 := by
          rw [Finset.card_sdiff_of_subset hsub, F.2, T'.2]; omega
        obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hcd
        have hy_mem : y ∈ F.1 \ T'.1 := hy_eq ▸ Finset.mem_singleton_self y
        rcases Finset.mem_sdiff.mp hy_mem with ⟨hyF, hyT'⟩; refine ⟨y, hyF, Subtype.ext ?_⟩
        ext z; simp only [Finset.mem_erase]; constructor
        · rintro ⟨hne, hzF⟩
          by_contra hzT'
          have hz_sdiff : z ∈ F.1 \ T'.1 := Finset.mem_sdiff.mpr ⟨hzF, hzT'⟩
          rw [hy_eq, Finset.mem_singleton] at hz_sdiff; exact hne hz_sdiff
        · intro hzT'; exact ⟨fun hzy ↦ hyT' (hzy ▸ hzT'), hsub hzT'⟩
    rw [hbij, ← Finset.sum_filter_add_sum_filter_not (s := F.1) (p := (· ∈ T.1))]
    have hf1 : F.1.filter (· ∈ T.1) = T.1 ∩ F.1 := (by ext y; simp [and_comm])
    have hf2 : F.1.filter (fun y ↦ y ∉ T.1) = F.1 \ T.1 := (by ext y; simp [Finset.mem_sdiff])
    rw [hf1, hf2]
    have hs1 : (∑ y ∈ T.1 ∩ F.1, dAltEntry M k (T.1 ∩ F.1.erase y).card) = (s : ℝ) * dAltEntry M k
      (s - 1) := by
      have hc : (∑ y ∈ T.1 ∩ F.1, dAltEntry M k (T.1 ∩ F.1.erase y).card) = ∑ _ ∈ T.1 ∩ F.1,
        dAltEntry M k (s - 1) := by
        refine Finset.sum_congr rfl fun y hy ↦ ?_
        have hint : T.1 ∩ F.1.erase y = (T.1 ∩ F.1).erase y := by
          ext z; simp only [Finset.mem_erase, Finset.mem_inter]; tauto
        rw [hint, Finset.card_erase_of_mem hy]
      rw [hc, Finset.sum_const, nsmul_eq_mul]
    have hs2 : (∑ y ∈ F.1 \ T.1, dAltEntry M k (T.1 ∩ F.1.erase y).card) = ((k + 1 - s : ℕ) : ℝ) *
      dAltEntry M k s := by
      have hc : (∑ y ∈ F.1 \ T.1, dAltEntry M k (T.1 ∩ F.1.erase y).card) = ∑ _ ∈ F.1 \ T.1,
        dAltEntry M k s := by
        refine Finset.sum_congr rfl fun y hy ↦ ?_
        have hyT : y ∉ T.1 := (Finset.mem_sdiff.mp hy).2
        have hint : T.1 ∩ F.1.erase y = T.1 ∩ F.1 := by
          ext z; simp only [Finset.mem_inter, Finset.mem_erase]
          exact ⟨fun ⟨hzT, _, hzF⟩ ↦ ⟨hzT, hzF⟩,
            fun ⟨hzT, hzF⟩ ↦ ⟨hzT, fun hzy ↦ hyT (hzy ▸ hzT), hzF⟩⟩
        rw [hint]
      have hcard_sdiff : (F.1 \ T.1).card = k + 1 - s := by
        have h := Finset.card_sdiff_add_card_inter F.1 T.1; rw [Finset.inter_comm, F.2] at h; omega
      rw [hc, Finset.sum_const, hcard_sdiff, nsmul_eq_mul]
    rw [hs1, hs2]
  rw [hlhs, hrhs, dAltEntry_pascal hkM hsk]
/- ## Section 3: Kernel Action & Inductive Involution Proof -/
private lemma jDownGenMat_mul_step (N r k : ℕ) : jDownGenMat N r k * jDownGenMat N k (k + 1) =
    ((k + 1 - r : ℕ) : ℝ) • jDownGenMat N r (k + 1) := by
  ext U F
  simp only [Matrix.mul_apply, Matrix.smul_apply, jDownGenMat, Matrix.of_apply, smul_eq_mul]
  by_cases hUF : U.1 ⊆ F.1
  · simp only [hUF, ↓reduceIte, mul_one]; have hflt :
        (∑ T : P01Subset N k, (if U.1 ⊆ T.1 then (1 : ℝ) else 0) * (if T.1 ⊆ F.1 then 1 else 0)) =
        ((Finset.univ.filter (fun T : P01Subset N k ↦ U.1 ⊆ T.1 ∧ T.1 ⊆ F.1)).card : ℝ) := by
      have hboole : ∀ T ∈ (Finset.univ : Finset (P01Subset N k)), (if U.1 ⊆ T.1 then (1 : ℝ) else
        0) * (if T.1 ⊆ F.1 then 1 else 0) = if U.1 ⊆ T.1 ∧ T.1 ⊆ F.1 then (1 : ℝ) else 0 := by
        intro T _; by_cases h1 : U.1 ⊆ T.1 <;> by_cases h2 : T.1 ⊆ F.1 <;> simp [h1, h2]
      rw [Finset.sum_congr rfl hboole, Finset.sum_boole]
    rw [hflt]
    have hbij : (Finset.univ.filter (fun T : P01Subset N k ↦ U.1 ⊆ T.1 ∧ T.1 ⊆ F.1)).card = (F.1 \
      U.1).card := by
      symm
      refine Finset.card_bij (fun y hy ↦ ⟨F.1.erase y, by
          rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp hy).1, F.2]; omega⟩)
        (fun y hy ↦ ?_)
        (fun y₁ hy₁ y₂ hy₂ heq ↦ ?_)
        (fun T hT ↦ ?_)
      · rcases Finset.mem_sdiff.mp hy with ⟨_, hyU⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, Finset.erase_subset y F.1⟩
        intro z hzU; exact Finset.mem_erase.mpr ⟨fun hzy ↦ hyU (hzy ▸ hzU), hUF hzU⟩
      · have hset : F.1.erase y₁ = F.1.erase y₂ := Subtype.mk.inj heq
        by_contra hne
        have hy1_in : y₁ ∈ F.1.erase y₂ := Finset.mem_erase.mpr ⟨hne, (Finset.mem_sdiff.mp hy₁).1⟩
        rw [← hset] at hy1_in; exact (Finset.mem_erase.mp hy1_in).1 rfl
      · rcases (Finset.mem_filter.mp hT).2 with ⟨hUT, hTF⟩
        have hcd : (F.1 \ T.1).card = 1 := by rw [Finset.card_sdiff_of_subset hTF, F.2, T.2]; omega
        obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hcd
        have hy_mem : y ∈ F.1 \ T.1 := hy_eq ▸ Finset.mem_singleton_self y
        rcases Finset.mem_sdiff.mp hy_mem with ⟨hyF, hyT⟩
        refine ⟨y, Finset.mem_sdiff.mpr ⟨hyF, fun hyU ↦ hyT (hUT hyU)⟩, Subtype.ext ?_⟩
        ext z; simp only [Finset.mem_erase]; constructor
        · rintro ⟨hne, hzF⟩
          by_contra hzT
          have hz_sdiff : z ∈ F.1 \ T.1 := Finset.mem_sdiff.mpr ⟨hzF, hzT⟩
          rw [hy_eq, Finset.mem_singleton] at hz_sdiff; exact hne hz_sdiff
        · intro hzT; exact ⟨fun hzy ↦ hyT (hzy ▸ hzT), hTF hzT⟩
    rw [hbij, Finset.card_sdiff_of_subset hUF, F.2, U.2]
  · simp only [hUF, ↓reduceIte, mul_zero]; refine Finset.sum_eq_zero fun T _ ↦ ?_
    by_cases hUT : U.1 ⊆ T.1
    · have hnTF : ¬ T.1 ⊆ F.1 := fun hTF ↦ hUF (hUT.trans hTF); simp [hUT, hnTF]
    · simp [hUT]
private lemma jDownGenMat_mulVec_zero_of_step {N k : ℕ} {w : P01Subset N (k + 1) → ℝ} (hw :
    jDownGenMat N k (k + 1) *ᵥ w = 0) : ∀ r : ℕ, r ≤ k → jDownGenMat N r (k + 1) *ᵥ w = 0 := by
  intro r hrk; have hmul := congrArg (· *ᵥ w) (jDownGenMat_mul_step N r k)
  rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero, Matrix.smul_mulVec] at hmul
  have hc_ne : ((k + 1 - r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (smul_eq_zero.mp hmul.symm).resolve_left hc_ne
private lemma transpose_jDownGenMat_mul_self (N r m : ℕ) (E F : P01Subset N m) :
    ((jDownGenMat N r m)ᵀ * jDownGenMat N r m) E F = (((E.1 ∩ F.1).card).choose r : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, jDownGenMat, Matrix.of_apply]
  have hflt : (∑ U : P01Subset N r, (if U.1 ⊆ E.1 then (1 : ℝ) else 0) * (if U.1 ⊆ F.1 then 1 else
    0)) = ((Finset.univ.filter (fun U : P01Subset N r ↦ U.1 ⊆ E.1 ∩ F.1)).card : ℝ) := by
    have hboole : ∀ U ∈ (Finset.univ : Finset (P01Subset N r)), (if U.1 ⊆ E.1 then (1 : ℝ) else
      0) * (if U.1 ⊆ F.1 then 1 else 0) = if U.1 ⊆ E.1 ∩ F.1 then (1 : ℝ) else 0 := by
      intro U _; simp only [Finset.subset_inter_iff]
      by_cases h1 : U.1 ⊆ E.1 <;> by_cases h2 : U.1 ⊆ F.1 <;> simp [h1, h2]
    rw [Finset.sum_congr rfl hboole, Finset.sum_boole]
  rw [hflt, card_p01Subset_filter N r (fun S ↦ S ⊆ E.1 ∩ F.1)]; have hpow :
      (((Finset.univ : Finset (Fin N)).powersetCard r).filter (· ⊆ E.1 ∩ F.1)) =
        (E.1 ∩ F.1).powersetCard r := by
    ext S; simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  rw [hpow, Finset.card_powersetCard]
private lemma dAltEntry_top_mobius {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m < M) : (∑ t ∈ Finset.range
    (m + 1), (-1 : ℝ) ^ (m - t) * (m.choose t : ℝ) * dAltEntry M m t) = (-1 : ℝ) ^ m := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hMm_pos : (0 : ℝ) < ((M - m : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcM_pos : (0 : ℝ) < ((M - 1).choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hbij : (∑ t ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m - t) * (m.choose t : ℝ) * dAltEntry M m
    t) = (-1 : ℝ) ^ m * (((M - m : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose m : ℝ))) * ∑ u ∈
    Finset.range (m + 1), (((M - 1 - u).choose (m - u) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]; refine Finset.sum_bij (fun t _ ↦ m - t)
      (fun t ht ↦ by simp only [Finset.mem_range] at ht ⊢; omega)
      (fun t₁ ht₁ t₂ ht₂ heq ↦ by simp only [Finset.mem_range] at ht₁ ht₂; omega)
      (fun u hu ↦ ⟨m - u, by simp only [Finset.mem_range] at hu ⊢; omega,
        by simp only [Finset.mem_range] at hu; omega⟩)
      (fun t ht ↦ ?_)
    have htm : t ≤ m := (by simp only [Finset.mem_range] at ht; omega); set u := m - t
    have hum : u ≤ m := (by omega); have htu : m - u = t := (by omega); unfold dAltEntry
    simp only [Nat.one_le_iff_ne_zero.mp hm1, ↓reduceIte]
    have hpow : (-1 : ℝ) ^ u * (-1 : ℝ) ^ t = (-1 : ℝ) ^ m := by
      rw [← pow_add, show u + t = m by omega]
    have hch_symm : m.choose t = m.choose u := (by rw [← htu, Nat.choose_symm hum])
    have hcm := choose_mul_choose hum (by omega : m ≤ M - 1)
    have hcu_pos : (0 : ℝ) < ((M - 1).choose u : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hcmR : (((M - 1).choose m : ℝ) * (m.choose u : ℝ)) = ((M - 1).choose u : ℝ) * (((M - 1 -
      u).choose (m - u) : ℕ) : ℝ) := by
      exact_mod_cast hcm
    change (-1 : ℝ) ^ u * (m.choose t : ℝ) *
        ((-1 : ℝ) ^ t * ((M - m : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose u : ℝ))) = _
    rw [hch_symm]
    calc (-1 : ℝ) ^ u * (m.choose u : ℝ) *
            ((-1 : ℝ) ^ t * ((M - m : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose u : ℝ)))
        = ((-1 : ℝ) ^ u * (-1 : ℝ) ^ t) * ((M - m : ℕ) : ℝ) * (m.choose u : ℝ) /
            ((M : ℝ) * ((M - 1).choose u : ℝ)) := by ring
      _ = (-1 : ℝ) ^ m * ((M - m : ℕ) : ℝ) * (((M - 1).choose m : ℝ) * (m.choose u : ℝ)) /
            ((M : ℝ) * ((M - 1).choose m : ℝ) * ((M - 1).choose u : ℝ)) := by
            rw [hpow]; field_simp [hM_pos.ne', hcM_pos.ne', hcu_pos.ne']
      _ = (-1 : ℝ) ^ m * (((M - m : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose m : ℝ))) *
            (((M - 1 - u).choose (m - u) : ℕ) : ℝ) := by
            rw [hcmR]; field_simp [hM_pos.ne', hcM_pos.ne', hcu_pos.ne']
  rw [hbij]
  have hdiag : (∑ u ∈ Finset.range (m + 1), (M - 1 - u).choose (m - u)) = M.choose m := by
    have hK : M - 1 = (M - 1 - m) + m := (by omega)
    have htop : (M - 1 - m) + m + 1 = M := (by omega); have hcongr :
        (∑ u ∈ Finset.range (m + 1), (M - 1 - u).choose (m - u)) =
          ∑ u ∈ Finset.range (m + 1), ((M - 1 - m) + m - u).choose (m - u) :=
      Finset.sum_congr rfl fun u _ ↦ by rw [← hK]
    rw [hcongr, sum_choose_diag m (M - 1 - m), htop]
  have hdiagR : (∑ u ∈ Finset.range (m + 1), (((M - 1 - u).choose (m - u) : ℕ) : ℝ)) = (M.choose m
    : ℝ) := by
    exact_mod_cast hdiag
  rw [hdiagR]
  have habs_nat : M * (M - 1).choose (M - m - 1) = (M - m) * M.choose (M - m) := by
    have h := p01_choose_mul_succ (M - 1) (M - m - 1); have h1 : M - 1 + 1 = M := (by omega)
    have h2 : M - m - 1 + 1 = M - m := (by omega); rw [h1, h2] at h; exact h
  have hc1 : (M - 1).choose (M - m - 1) = (M - 1).choose m := by
    rw [← Nat.choose_symm (by omega : m ≤ M - 1)]; congr 1; omega
  have hc2 : M.choose (M - m) = M.choose m := (by rw [← Nat.choose_symm (by omega : m ≤ M)])
  rw [hc1, hc2] at habs_nat
  have habsR : (M : ℝ) * ((M - 1).choose m : ℝ) = ((M - m : ℕ) : ℝ) * (M.choose m : ℝ) := by
    exact_mod_cast habs_nat
  rw [habsR]
  have hMc_pos : (0 : ℝ) < (M.choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  field_simp [hMm_pos.ne', hMc_pos.ne']
private lemma dAltSymMat_mulVec_of_jDown_zero {M k : ℕ} (hkM : k + 1 < M)
    {w : P01Subset (2 * M) (k + 1) → ℝ} (hw : jDownGenMat (2 * M) k (k + 1) *ᵥ w = 0) :
    dAltSymMat (2 * M) (k + 1) *ᵥ w = (-1 : ℝ) ^ (k + 1) • w := by
  have hdiv : (2 * M) / 2 = M := (by omega)
  let c (r : ℕ) : ℝ :=
    ∑ t ∈ Finset.range (r + 1), (-1 : ℝ) ^ (r - t) * (r.choose t : ℝ) * dAltEntry M (k + 1) t
  have hdecomp : dAltSymMat (2 * M) (k + 1) = ∑ r ∈ Finset.range (k + 2), c r • ((jDownGenMat (2 *
    M) r (k + 1))ᵀ * jDownGenMat (2 * M) r (k + 1)) := by
    ext E F
    simp only [dAltSymMat, Matrix.of_apply, hdiv, Matrix.sum_apply, Matrix.smul_apply,
      transpose_jDownGenMat_mul_self, smul_eq_mul]
    have hle : (E.1 ∩ F.1).card ≤ k + 1 :=
      (Finset.card_le_card Finset.inter_subset_left).trans E.2.le
    exact (mobius_binomial_eval (dAltEntry M (k + 1)) hle).symm
  rw [hdecomp, Matrix.sum_mulVec]; rw [Finset.sum_range_succ]
  have hlow : (∑ r ∈ Finset.range (k + 1), (c r • ((jDownGenMat (2 * M) r (k + 1))ᵀ * jDownGenMat
    (2 * M) r (k + 1))) *ᵥ w) = 0 := by
    refine Finset.sum_eq_zero fun r hr ↦ ?_
    have hrk : r ≤ k := (by simp only [Finset.mem_range] at hr; omega)
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, jDownGenMat_mulVec_zero_of_step hw r hrk,
      Matrix.mulVec_zero, smul_zero]
  rw [hlow, zero_add]
  have htop_id : jDownGenMat (2 * M) (k + 1) (k + 1) = 1 := by
    ext E F; simp only [jDownGenMat, Matrix.of_apply, Matrix.one_apply]; by_cases h : E = F
    · subst h; simp
    · have hnsub : ¬ E.1 ⊆ F.1 := fun hsub ↦
        h (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [E.2, F.2])))
      simp [h, hnsub]
  have hc_top : c (k + 1) = (-1 : ℝ) ^ (k + 1) := dAltEntry_top_mobius (by omega) hkM
  rw [htop_id, Matrix.transpose_one, Matrix.one_mul, hc_top, Matrix.smul_mulVec, Matrix.one_mulVec]
theorem dAltSymMat_mul_self_even {M m : ℕ} (hmM : m < M) :
    dAltSymMat (2 * M) m * dAltSymMat (2 * M) m = 1 := by
  induction m with
  | zero =>
    ext E F
    have hEF : E = F := Subtype.ext (Finset.card_eq_zero.mp E.2 ▸ (Finset.card_eq_zero.mp F.2).symm)
    subst hEF
    have huniv : (Finset.univ : Finset (P01Subset (2 * M) 0)) = {E} := by
      ext G; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subtype.ext (Finset.card_eq_zero.mp G.2 ▸ (Finset.card_eq_zero.mp E.2).symm)
    simp [Matrix.mul_apply, dAltSymMat, dAltEntry, huniv]
  | succ k ih_k =>
    have ih := ih_k (by omega); let D := dAltSymMat (2 * M) (k + 1); let D₀ := dAltSymMat (2 * M) k
    let B := jDownGenMat (2 * M) k (k + 1); let A := D * D - 1
    have hBD : B * D = D₀ * B := jDownMat_mul_dAltSymMat hmM
    have hBA : B * A = 0 := by
      dsimp only [A]
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc B D D, hBD,
        Matrix.mul_assoc D₀ B D, hBD, ← Matrix.mul_assoc D₀ D₀ B, ih, Matrix.one_mul, sub_self]
    have hAt : Aᵀ = A := by
      dsimp only [A, D]
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, dAltSymMat_transpose]
    have hA_vec : ∀ u : P01Subset (2 * M) (k + 1) → ℝ, A *ᵥ u = 0 := by
      intro u; let w := A *ᵥ u
      have hBw : B *ᵥ w = 0 := by dsimp only [w]; rw [Matrix.mulVec_mulVec, hBA, Matrix.zero_mulVec]
      have hDw : D *ᵥ w = (-1 : ℝ) ^ (k + 1) • w := dAltSymMat_mulVec_of_jDown_zero hmM hBw
      have hAw : A *ᵥ w = 0 := by
        dsimp only [A]
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hDw, Matrix.mulVec_smul,
          hDw, smul_smul, ← pow_add, show k + 1 + (k + 1) = 2 * (k + 1) by ring,
          pow_mul, neg_one_sq, one_pow, one_smul, sub_self]
      have hsq : (∑ E : P01Subset (2 * M) (k + 1), (w E) ^ 2) = 0 := by
        have hdot : w ⬝ᵥ w = 0 := by
          calc w ⬝ᵥ w = (A *ᵥ u) ⬝ᵥ w := rfl
            _ = u ⬝ᵥ (Aᵀ *ᵥ w) := by
                simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply,
                  Finset.sum_mul, Finset.mul_sum]
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun _ _ ↦
                  Finset.sum_congr rfl fun _ _ ↦ by ring
            _ = u ⬝ᵥ (A *ᵥ w) := by rw [hAt]
            _ = 0 := by rw [hAw, dotProduct_zero]
        simpa only [dotProduct, sq] using hdot
      have hw0 := (Finset.sum_eq_zero_iff_of_nonneg (fun E _ ↦ sq_nonneg (w E))).mp hsq; funext E
      exact sq_eq_zero_iff.mp (hw0 E (Finset.mem_univ E))
    suffices hA0 : A = 0 by dsimp only [A] at hA0; exact sub_eq_zero.mp hA0
    ext E F; have hv := congrFun (hA_vec (Pi.single F 1)) E; rwa [Matrix.mulVec_single_one] at hv
theorem dAltSymMat_mul_self_two_pow {n m : ℕ} (hn1 : 1 ≤ n) (h2m : 2 * m < 2 ^ n) :
    dAltSymMat (2 ^ n) m * dAltSymMat (2 ^ n) m = 1 := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
  rw [hpow] at h2m ⊢; exact dAltSymMat_mul_self_even (by omega)
/-- Packaged `SymOrthogonal (2 ^ n) m` involution for `D_{\text{alt}}` (`1 ≤ n`,
  `2 * m < 2 ^ n`). -/
noncomputable def dAltSymOrthogonal (n m : ℕ) (hn1 : 1 ≤ n) (h2m : 2 * m < 2 ^ n) :
    SymOrthogonal (2 ^ n) m :=
  SymOrthogonal.ofSymmInvolution (dAltSymMat (2 ^ n) m)
    (dAltSymMat_transpose (2 ^ n) m)
    (dAltSymMat_mul_self_two_pow hn1 h2m)

/- ## Section 1: Orbit Dimension, Cardinality Positivity, & Isometric Embedding -/
/-- Dimension `min m r + 1` of the `(S_r × S_{N-r})`-invariant intersection-size subspace. -/
abbrev orbDim (m r : ℕ) : ℕ := min m r + 1
theorem orbCard_pos_gen {N m r w : ℕ} (hmrN : m + r ≤ N) (hw : w ≤ min m r) :
    0 < orbCard N m r w := by
  have hwm : w ≤ m := hw.trans (Nat.min_le_left m r)
  have hwr : w ≤ r := hw.trans (Nat.min_le_right m r); unfold orbCard
  exact Nat.mul_pos (Nat.choose_pos hwr) (Nat.choose_pos (by omega))
theorem inter_card_lt_orbDim {N m : ℕ} (R : Finset (Fin N)) (E : P01Subset N m) :
    (E.1 ∩ R).card < orbDim m R.card := by
  have h1 : (E.1 ∩ R).card ≤ m := (Finset.card_le_card Finset.inter_subset_left).trans E.2.le
  have h2 : (E.1 ∩ R).card ≤ R.card := Finset.card_le_card Finset.inter_subset_right
  have hle : (E.1 ∩ R).card ≤ min m R.card := le_min h1 h2; unfold orbDim; omega
/-- General isometric embedding of `Fin (orbDim m R.card) → ℝ` into `P01Subset N m → ℝ`. -/
noncomputable def orbEmbedGen (N m : ℕ) (R : Finset (Fin N))
    (x : Fin (orbDim m R.card) → ℝ) (E : P01Subset N m) : ℝ :=
  x ⟨(E.1 ∩ R).card, inter_card_lt_orbDim R E⟩ / √(orbCard N m R.card (E.1 ∩ R).card : ℝ)
theorem sum_mul_orbEmbedGen_filter {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    (x y : Fin (orbDim m R.card) → ℝ) (w : Fin (orbDim m R.card)) :
    (∑ E ∈ Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w.1),
      orbEmbedGen N m R x E * orbEmbedGen N m R y E) = x w * y w := by
  have hw_le : w.1 ≤ min m R.card := Nat.lt_succ_iff.mp w.2
  have hw_m : w.1 ≤ m := hw_le.trans (Nat.min_le_left m R.card)
  have hpos : (0 : ℝ) < (orbCard N m R.card w.1 : ℝ) :=
    Nat.cast_pos.mpr (orbCard_pos_gen hmrN hw_le)
  have hcongr :
      (∑ E ∈ Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w.1),
        orbEmbedGen N m R x E * orbEmbedGen N m R y E) =
      ∑ _ ∈ Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w.1),
        (x w * y w) / (orbCard N m R.card w.1 : ℝ) := by
    refine Finset.sum_congr rfl fun E hE ↦ ?_
    have hwE : (E.1 ∩ R).card = w.1 := (Finset.mem_filter.mp hE).2; unfold orbEmbedGen
    have hfin : (⟨(E.1 ∩ R).card, inter_card_lt_orbDim R E⟩ : Fin (orbDim m R.card)) = w :=
      Fin.ext hwE
    rw [hfin, hwE, div_mul_div_comm, Real.mul_self_sqrt hpos.le]
  rw [hcongr, Finset.sum_const, card_p01Subset_inter_eq R hw_m, nsmul_eq_mul,
    mul_div_cancel₀ _ hpos.ne']
theorem symHitProb_orbEmbedGen {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    (x : Fin (orbDim m R.card) → ℝ) (w : Fin (orbDim m R.card)) :
    symHitProb R (orbEmbedGen N m R x) w.1 = (x w) ^ 2 := by
  simpa only [symHitProb, sq] using sum_mul_orbEmbedGen_filter hmrN x x w
theorem dot_orbEmbedGen {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    (x y : Fin (orbDim m R.card) → ℝ) :
    (∑ E : P01Subset N m, orbEmbedGen N m R x E * orbEmbedGen N m R y E) =
      ∑ w : Fin (orbDim m R.card), x w * y w := by
  let f : P01Subset N m → Fin (orbDim m R.card) :=
    fun E ↦ ⟨(E.1 ∩ R).card, inter_card_lt_orbDim R E⟩
  have hpart := (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := f) (fun _ _ ↦ Finset.mem_univ _)
    (f := fun E ↦ orbEmbedGen N m R x E * orbEmbedGen N m R y E)).symm
  rw [hpart]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hfib : Finset.univ.filter (fun E : P01Subset N m ↦ f E = w) =
      Finset.univ.filter (fun E : P01Subset N m ↦ (E.1 ∩ R).card = w.1) := by
    ext E; simp [f, Fin.ext_iff]
  rw [hfib, sum_mul_orbEmbedGen_filter hmrN x y w]
theorem orbEmbedGen_injective {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    {x y : Fin (orbDim m R.card) → ℝ}
    (heq : orbEmbedGen N m R x = orbEmbedGen N m R y) : x = y := by
  ext w
  have h1 := sum_mul_orbEmbedGen_filter hmrN x (Pi.single w 1) w
  have h2 := sum_mul_orbEmbedGen_filter hmrN y (Pi.single w 1) w; rw [heq] at h1
  simp only [Pi.single_eq_same, mul_one] at h1 h2; exact h1.symm.trans h2
/-- Orbit coordinates of the uniform subset state `u0Vec N m`. -/
noncomputable def u0OrbVecGen (N m r : ℕ) : Fin (orbDim m r) → ℝ :=
  fun w ↦ √((orbCard N m r w.1 : ℝ) / (N.choose m : ℝ))
theorem orbEmbedGen_u0OrbVecGen {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N) :
    orbEmbedGen N m R (u0OrbVecGen N m R.card) = u0Vec N m := by
  ext E
  have hw_le : (E.1 ∩ R).card ≤ min m R.card := Nat.lt_succ_iff.mp (inter_card_lt_orbDim R E)
  have hc_pos : (0 : ℝ) < (orbCard N m R.card (E.1 ∩ R).card : ℝ) :=
    Nat.cast_pos.mpr (orbCard_pos_gen hmrN hw_le)
  unfold orbEmbedGen u0OrbVecGen u0Vec; dsimp only
  rw [Real.sqrt_div hc_pos.le, div_right_comm, div_self (Real.sqrt_pos.mpr hc_pos).ne']
/-- Diagonal odd-intersection parity reflection `diag((-1)^w)` on `Fin (orbDim m r)`. -/
def zOrbMat (m r : ℕ) : Matrix (Fin (orbDim m r)) (Fin (orbDim m r)) ℝ :=
  Matrix.diagonal fun w ↦ (-1 : ℝ) ^ w.1
theorem zOrbMat_transpose (m r : ℕ) : (zOrbMat m r)ᵀ = zOrbMat m r := by
  simp [zOrbMat]
theorem zOrbMat_mul_self (m r : ℕ) : zOrbMat m r * zOrbMat m r = 1 := by
  ext a b
  unfold zOrbMat; rw [Matrix.diagonal_mul_diagonal]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · simp [hab]
theorem symZVec_orbEmbedGen {N m : ℕ} (R : Finset (Fin N))
    (x : Fin (orbDim m R.card) → ℝ) :
    symZVec R (orbEmbedGen N m R x) = orbEmbedGen N m R (zOrbMat m R.card *ᵥ x) := by
  ext E
  unfold symZVec orbEmbedGen zOrbMat; rw [Matrix.mulVec_diagonal]; dsimp only; ring
/- ## Section 2: Subset-Intersection Fiber Counting & `dAltOrbMat` Intertwining -/
theorem card_powersetCard_inter_subset {α : Type*} [DecidableEq α]
    (U A : Finset α) (hAU : A ⊆ U) (k i : ℕ) (hi : i ≤ k) :
    ((U.powersetCard k).filter (fun S ↦ (S ∩ A).card = i)).card =
      A.card.choose i * (U.card - A.card).choose (k - i) := by
  have hbij : ((U.powersetCard k).filter (fun S ↦ (S ∩ A).card = i)).card =
      (A.powersetCard i ×ˢ (U \ A).powersetCard (k - i)).card := by
    refine Finset.card_bij (fun S _ ↦ (S ∩ A, S \ A)) ?_ ?_ ?_
    · intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hSk, hSA⟩
      rcases Finset.mem_powersetCard.mp hSk with ⟨hSU, hScard⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hSA⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff hSU (Finset.Subset.refl A),
          Nat.eq_sub_of_add_eq
            (by rw [← hScard, ← hSA]; exact Finset.card_sdiff_add_card_inter S A)⟩⟩
    · intro S₁ _ S₂ _ heq; have h1 : S₁ ∩ A = S₂ ∩ A := congrArg Prod.fst heq
      have h2 : S₁ \ A = S₂ \ A := congrArg Prod.snd heq
      rw [← Finset.sdiff_union_inter S₁ A, ← Finset.sdiff_union_inter S₂ A, h1, h2]
    · intro p hp
      rcases p with ⟨P, Q⟩
      rcases Finset.mem_product.mp hp with ⟨hP, hQ⟩
      rcases Finset.mem_powersetCard.mp hP with ⟨hPA, hPcard⟩
      rcases Finset.mem_powersetCard.mp hQ with ⟨hQU, hQcard⟩
      have hdisj : Disjoint P Q := by
        refine Finset.disjoint_left.mpr fun x hxP hxQ ↦ ?_
        exact (Finset.mem_sdiff.mp (hQU hxQ)).2 (hPA hxP)
      have hPQ_inter : (P ∪ Q) ∩ A = P := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxP | hxQ, hxA⟩
          · exact hxP
          · exact absurd hxA (Finset.mem_sdiff.mp (hQU hxQ)).2
        · intro hxP; exact ⟨Or.inl hxP, hPA hxP⟩
      have hPQ_sdiff : (P ∪ Q) \ A = Q := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxP | hxQ, hxnA⟩
          · exact absurd (hPA hxP) hxnA
          · exact hxQ
        · intro hxQ; exact ⟨Or.inr hxQ, (Finset.mem_sdiff.mp (hQU hxQ)).2⟩
      refine ⟨P ∪ Q, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact Finset.union_subset (hPA.trans hAU) (hQU.trans Finset.sdiff_subset)
      · rw [Finset.card_union_of_disjoint hdisj, hPcard, hQcard]; omega
      · rw [hPQ_inter, hPcard]
      · exact Prod.ext hPQ_inter hPQ_sdiff
  have hUA_card : (U \ A).card = U.card - A.card := by
    have h := Finset.card_sdiff_add_card_inter U A; rw [Finset.inter_eq_right.mpr hAU] at h; omega
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hUA_card]
theorem sum_powersetCard_inter_subset {α : Type*} [DecidableEq α]
    (U A : Finset α) (hAU : A ⊆ U) (k : ℕ) (f : ℕ → ℝ) :
    (∑ S ∈ U.powersetCard k, f (S ∩ A).card) =
      ∑ i ∈ Finset.range (k + 1),
        (A.card.choose i * (U.card - A.card).choose (k - i) : ℝ) * f i := by
  have hmaps : ∀ S ∈ U.powersetCard k, (S ∩ A).card ∈ Finset.range (k + 1) := by
    intro S hS; have hScard := (Finset.mem_powersetCard.mp hS).2
    have hle : (S ∩ A).card ≤ k := (Finset.card_le_card Finset.inter_subset_left).trans hScard.le
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcongr :
      (∑ S ∈ (U.powersetCard k).filter (fun S ↦ (S ∩ A).card = i), f (S ∩ A).card) =
      ∑ _ ∈ (U.powersetCard k).filter (fun S ↦ (S ∩ A).card = i), f i := by
    refine Finset.sum_congr rfl fun S hS ↦ ?_
    rw [(Finset.mem_filter.mp hS).2]
  rw [hcongr, Finset.sum_const, card_powersetCard_inter_subset U A hAU k i hik, nsmul_eq_mul]
  push_cast; ring
/-- Raw fiber sum `∑_{|F ∩ R| = b} dAltEntry (N / 2) m |E ∩ F|` for `|E ∩ R| = a`. -/
noncomputable def dAltOrbRawSum (N m r a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (b + 1),
    (a.choose i * (r - a).choose (b - i) : ℝ) *
      ∑ j ∈ Finset.range (m - b + 1),
        ((m - a).choose j * (N - r - (m - a)).choose (m - b - j) : ℝ) *
          dAltEntry (N / 2) m (i + j)
theorem sum_p01Subset_filter_dAltEntry {N m : ℕ} (R : Finset (Fin N))
    (E : P01Subset N m) {b : ℕ} (hbm : b ≤ m) :
    (∑ F ∈ Finset.univ.filter (fun F : P01Subset N m ↦ (F.1 ∩ R).card = b),
      dAltEntry (N / 2) m (E.1 ∩ F.1).card) =
      dAltOrbRawSum N m R.card (E.1 ∩ R).card b := by
  have h1 :
      (∑ F ∈ Finset.univ.filter (fun F : P01Subset N m ↦ (F.1 ∩ R).card = b),
        dAltEntry (N / 2) m (E.1 ∩ F.1).card) =
      ∑ S ∈ ((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun S ↦ (S ∩ R).card = b),
        dAltEntry (N / 2) m (E.1 ∩ S).card := by
    refine Finset.sum_bij (fun F _ ↦ F.1) ?_ ?_ ?_ ?_
    · intro F hF; have hFb := (Finset.mem_filter.mp hF).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, F.2⟩, hFb⟩
    · intro F₁ _ F₂ _ heq; exact Subtype.ext heq
    · intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hSm, hSb⟩
      have hScard := (Finset.mem_powersetCard.mp hSm).2
      exact ⟨⟨S, hScard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSb⟩, rfl⟩
    · intro _ _; rfl
  have h2 :
      (∑ S ∈ ((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun S ↦ (S ∩ R).card = b),
        dAltEntry (N / 2) m (E.1 ∩ S).card) =
      ∑ p ∈ R.powersetCard b ×ˢ Rᶜ.powersetCard (m - b),
        dAltEntry (N / 2) m ((p.1 ∩ (E.1 ∩ R)).card + (p.2 ∩ (E.1 \ R)).card) := by
    refine Finset.sum_bij (fun S _ ↦ (S ∩ R, S \ R)) ?_ ?_ ?_ ?_
    · intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hSm, hSb⟩
      have hScard := (Finset.mem_powersetCard.mp hSm).2
      have hsdiff_sub : S \ R ⊆ Rᶜ := by
        intro x hx; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
      have hsdiff_card : (S \ R).card = m - b := by
        have h := Finset.card_sdiff_add_card_inter S R; omega
      exact Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hSb⟩,
         Finset.mem_powersetCard.mpr ⟨hsdiff_sub, hsdiff_card⟩⟩
    · intro S₁ _ S₂ _ heq; have hp1 : S₁ ∩ R = S₂ ∩ R := congrArg Prod.fst heq
      have hp2 : S₁ \ R = S₂ \ R := congrArg Prod.snd heq
      rw [← Finset.sdiff_union_inter S₁ R, ← Finset.sdiff_union_inter S₂ R, hp1, hp2]
    · intro p hp
      rcases p with ⟨P, Q⟩
      rcases Finset.mem_product.mp hp with ⟨hP, hQ⟩
      rcases Finset.mem_powersetCard.mp hP with ⟨hPR, hPcard⟩
      rcases Finset.mem_powersetCard.mp hQ with ⟨hQRc, hQcard⟩
      have hdisj : Disjoint P Q := by
        refine Finset.disjoint_left.mpr fun x hxP hxQ ↦ ?_
        exact Finset.mem_compl.mp (hQRc hxQ) (hPR hxP)
      have hPQ_inter : (P ∪ Q) ∩ R = P := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxP | hxQ, hxR⟩
          · exact hxP
          · exact absurd hxR (Finset.mem_compl.mp (hQRc hxQ))
        · intro hxP; exact ⟨Or.inl hxP, hPR hxP⟩
      have hPQ_sdiff : (P ∪ Q) \ R = Q := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxP | hxQ, hxnR⟩
          · exact absurd (hPR hxP) hxnR
          · exact hxQ
        · intro hxQ; exact ⟨Or.inr hxQ, Finset.mem_compl.mp (hQRc hxQ)⟩
      refine ⟨P ∪ Q, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        ?_⟩, Prod.ext hPQ_inter hPQ_sdiff⟩
      · rw [Finset.card_union_of_disjoint hdisj, hPcard, hQcard]; omega
      · rw [hPQ_inter, hPcard]
    · intro S _
      have hsplit : E.1 ∩ S = ((S ∩ R) ∩ (E.1 ∩ R)) ∪ ((S \ R) ∩ (E.1 \ R)) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
        by_cases hxR : x ∈ R <;> tauto
      have hdisj : Disjoint ((S ∩ R) ∩ (E.1 ∩ R)) ((S \ R) ∩ (E.1 \ R)) := by
        refine Finset.disjoint_left.mpr fun x hx1 hx2 ↦ ?_
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx2).1).2
          (Finset.mem_inter.mp (Finset.mem_inter.mp hx1).1).2
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [h1, h2, Finset.sum_product]
  have hsub_Rc : E.1 \ R ⊆ Rᶜ := by
    intro x hx; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
  have hEsdiff_card : (E.1 \ R).card = m - (E.1 ∩ R).card := by
    have h := Finset.card_sdiff_add_card_inter E.1 R; have hEm := E.2; omega
  have hRc_card : Rᶜ.card = N - R.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hinner : ∀ P ∈ R.powersetCard b, (∑ Q ∈ Rᶜ.powersetCard (m - b),
        dAltEntry (N / 2) m ((P ∩ (E.1 ∩ R)).card + (Q ∩ (E.1 \ R)).card)) =
      ∑ j ∈ Finset.range (m - b + 1), ((m - (E.1 ∩ R).card).choose j *
          (N - R.card - (m - (E.1 ∩ R).card)).choose (m - b - j) : ℝ) *
          dAltEntry (N / 2) m ((P ∩ (E.1 ∩ R)).card + j) := by
    intro P _
    rw [sum_powersetCard_inter_subset Rᶜ (E.1 \ R) hsub_Rc (m - b)
      (fun j ↦ dAltEntry (N / 2) m ((P ∩ (E.1 ∩ R)).card + j))]
    rw [hEsdiff_card, hRc_card]
  rw [Finset.sum_congr rfl hinner]
  rw [sum_powersetCard_inter_subset R (E.1 ∩ R) Finset.inter_subset_right b
    (fun i ↦ ∑ j ∈ Finset.range (m - b + 1),
      ((m - (E.1 ∩ R).card).choose j * (N - R.card - (m - (E.1 ∩ R).card)).choose (m - b - j) : ℝ) *
        dAltEntry (N / 2) m (i + j))]
  rfl
/-- Orbit-space reflection matrix `D_{\text{orb}}` on `Fin (orbDim m r)` intertwining
  `dAltSymMat`. -/
noncomputable def dAltOrbMat (N m r : ℕ) :
    Matrix (Fin (orbDim m r)) (Fin (orbDim m r)) ℝ :=
  Matrix.of fun a b ↦
    √((orbCard N m r a.1 : ℝ) / (orbCard N m r b.1 : ℝ)) *
      dAltOrbRawSum N m r a.1 b.1
theorem dAltSymMat_mulVec_orbEmbedGen {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    (x : Fin (orbDim m R.card) → ℝ) :
    dAltSymMat N m *ᵥ orbEmbedGen N m R x =
      orbEmbedGen N m R (dAltOrbMat N m R.card *ᵥ x) := by
  ext E
  let a : Fin (orbDim m R.card) := ⟨(E.1 ∩ R).card, inter_card_lt_orbDim R E⟩
  have ha_le : a.1 ≤ min m R.card := Nat.lt_succ_iff.mp a.2
  have ha_pos : (0 : ℝ) < (orbCard N m R.card a.1 : ℝ) :=
    Nat.cast_pos.mpr (orbCard_pos_gen hmrN ha_le)
  have hsa_ne : √(orbCard N m R.card a.1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
  let f : P01Subset N m → Fin (orbDim m R.card) :=
    fun F ↦ ⟨(F.1 ∩ R).card, inter_card_lt_orbDim R F⟩
  change (∑ F : P01Subset N m, dAltEntry (N / 2) m (E.1 ∩ F.1).card * orbEmbedGen N m R x F) =
    (∑ b : Fin (orbDim m R.card), dAltOrbMat N m R.card a b * x b) / √(orbCard N m R.card a.1 : ℝ)
  have hpart := (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := f) (fun _ _ ↦ Finset.mem_univ _)
    (f := fun F ↦ dAltEntry (N / 2) m (E.1 ∩ F.1).card * orbEmbedGen N m R x F)).symm
  rw [hpart, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hb_le : b.1 ≤ min m R.card := Nat.lt_succ_iff.mp b.2
  have hb_m : b.1 ≤ m := hb_le.trans (Nat.min_le_left m R.card)
  have hfib : Finset.univ.filter (fun F : P01Subset N m ↦ f F = b) =
      Finset.univ.filter (fun F : P01Subset N m ↦ (F.1 ∩ R).card = b.1) := by
    ext F; simp [f, Fin.ext_iff]
  rw [hfib]
  have hcongr :
      (∑ F ∈ Finset.univ.filter (fun F : P01Subset N m ↦ (F.1 ∩ R).card = b.1),
        dAltEntry (N / 2) m (E.1 ∩ F.1).card * orbEmbedGen N m R x F) =
      (x b / √(orbCard N m R.card b.1 : ℝ)) *
        ∑ F ∈ Finset.univ.filter (fun F : P01Subset N m ↦ (F.1 ∩ R).card = b.1),
          dAltEntry (N / 2) m (E.1 ∩ F.1).card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F hF ↦ ?_
    have hwF : (F.1 ∩ R).card = b.1 := (Finset.mem_filter.mp hF).2; unfold orbEmbedGen
    have hfin : (⟨(F.1 ∩ R).card, inter_card_lt_orbDim R F⟩ : Fin (orbDim m R.card)) = b :=
      Fin.ext hwF
    rw [hfin, hwF]; ring
  rw [hcongr, sum_p01Subset_filter_dAltEntry R E hb_m]; unfold dAltOrbMat
  simp only [Matrix.of_apply]; rw [Real.sqrt_div ha_pos.le]
  have hcancel :
      (√(orbCard N m R.card a.1 : ℝ) / √(orbCard N m R.card b.1 : ℝ) *
        dAltOrbRawSum N m R.card a.1 b.1 * x b) / √(orbCard N m R.card a.1 : ℝ) =
      (x b / √(orbCard N m R.card b.1 : ℝ)) * dAltOrbRawSum N m R.card a.1 b.1 := by
    calc (√(orbCard N m R.card a.1 : ℝ) / √(orbCard N m R.card b.1 : ℝ) *
            dAltOrbRawSum N m R.card a.1 b.1 * x b) / √(orbCard N m R.card a.1 : ℝ)
        = √(orbCard N m R.card a.1 : ℝ) *
            ((x b / √(orbCard N m R.card b.1 : ℝ)) * dAltOrbRawSum N m R.card a.1 b.1) /
            √(orbCard N m R.card a.1 : ℝ) := by ring
      _ = (x b / √(orbCard N m R.card b.1 : ℝ)) * dAltOrbRawSum N m R.card a.1 b.1 :=
            mul_div_cancel_left₀ _ hsa_ne
  exact hcancel.symm
/- ## Section 3: Inherited Symmetry, Involutivity, & `K`-Step Orbit Walk -/
theorem dAltOrbMat_transpose {N m r : ℕ} (hmrN : m + r ≤ N) :
    (dAltOrbMat N m r)ᵀ = dAltOrbMat N m r := by
  have hrN : r ≤ N := by omega
  obtain ⟨R, hRcard⟩ : ∃ R : Finset (Fin N), R.card = r := ⟨(Finset.range r).attach.map
      ⟨fun i ↦ ⟨i.1, (Finset.mem_range.mp i.2).trans_le hrN⟩,
       fun i j h ↦ Subtype.ext (Fin.ext_iff.mp h)⟩, by simp⟩
  subst hRcard
  ext a b
  have hsym_mat := dAltSymMat_transpose N m
  have h1 := dot_orbEmbedGen hmrN (Pi.single a 1) (dAltOrbMat N m R.card *ᵥ Pi.single b 1)
  have h2 := dot_orbEmbedGen hmrN (dAltOrbMat N m R.card *ᵥ Pi.single a 1) (Pi.single b 1)
  rw [← dAltSymMat_mulVec_orbEmbedGen hmrN] at h1 h2
  have hmat_sym :
      (∑ E : P01Subset N m, orbEmbedGen N m R (Pi.single a 1) E *
          (dAltSymMat N m *ᵥ orbEmbedGen N m R (Pi.single b 1)) E) =
      ∑ E : P01Subset N m, (dAltSymMat N m *ᵥ orbEmbedGen N m R (Pi.single a 1)) E *
          orbEmbedGen N m R (Pi.single b 1) E := by
    change orbEmbedGen N m R (Pi.single a 1) ⬝ᵥ
        (dAltSymMat N m *ᵥ orbEmbedGen N m R (Pi.single b 1)) =
      (dAltSymMat N m *ᵥ orbEmbedGen N m R (Pi.single a 1)) ⬝ᵥ
        orbEmbedGen N m R (Pi.single b 1)
    rw [Matrix.dotProduct_mulVec]; congr 1
    funext E
    calc (orbEmbedGen N m R (Pi.single a 1) ᵥ* dAltSymMat N m) E
        = ((dAltSymMat N m)ᵀ *ᵥ orbEmbedGen N m R (Pi.single a 1)) E := by
            simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
      _ = (dAltSymMat N m *ᵥ orbEmbedGen N m R (Pi.single a 1)) E := by rw [hsym_mat]
  have heq := h2.symm.trans (hmat_sym.symm.trans h1)
  have hlhs :
      (∑ w : Fin (orbDim m R.card), (dAltOrbMat N m R.card *ᵥ Pi.single a 1) w *
          (Pi.single b 1 : Fin (orbDim m R.card) → ℝ) w) =
      (dAltOrbMat N m R.card)ᵀ a b := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro w _ hwb; simp [Pi.single_eq_of_ne hwb]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have hrhs :
      (∑ w : Fin (orbDim m R.card), (Pi.single a 1 : Fin (orbDim m R.card) → ℝ) w *
          (dAltOrbMat N m R.card *ᵥ Pi.single b 1) w) =
      dAltOrbMat N m R.card a b := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro w _ hwa; simp [Pi.single_eq_of_ne hwa]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  exact hlhs.symm.trans (heq.trans hrhs)
theorem dAltOrbMat_mul_self_two_pow {n m r : ℕ} (hn1 : 1 ≤ n) (h2m : 2 * m < 2 ^ n)
    (hmrN : m + r ≤ 2 ^ n) :
    dAltOrbMat (2 ^ n) m r * dAltOrbMat (2 ^ n) m r = 1 := by
  have hrN : r ≤ 2 ^ n := by omega
  obtain ⟨R, hRcard⟩ : ∃ R : Finset (Fin (2 ^ n)), R.card = r := ⟨(Finset.range r).attach.map
      ⟨fun i ↦ ⟨i.1, (Finset.mem_range.mp i.2).trans_le hrN⟩,
       fun i j h ↦ Subtype.ext (Fin.ext_iff.mp h)⟩, by simp⟩
  subst hRcard
  ext a b
  let sb : Fin (orbDim m R.card) → ℝ := Pi.single b 1
  have hvec :
      (dAltOrbMat (2 ^ n) m R.card * dAltOrbMat (2 ^ n) m R.card) *ᵥ sb =
        (1 : Matrix (Fin (orbDim m R.card)) (Fin (orbDim m R.card)) ℝ) *ᵥ sb := by
    rw [Matrix.one_mulVec]; apply orbEmbedGen_injective hmrN
    rw [← Matrix.mulVec_mulVec, ← dAltSymMat_mulVec_orbEmbedGen hmrN,
      ← dAltSymMat_mulVec_orbEmbedGen hmrN, Matrix.mulVec_mulVec,
      dAltSymMat_mul_self_two_pow hn1 h2m, Matrix.one_mulVec]
  have hv := congrFun hvec a; simpa only [sb, Matrix.mulVec_single_one, Matrix.col_apply] using hv
/-- Single-step `(d + 1) × (d + 1)` orbit walk matrix
  `U_{\text{orb}} = D_{\text{orb}} * Z_{\text{orb}}`. -/
noncomputable def dAltStepOrbMat (N m r : ℕ) :
    Matrix (Fin (orbDim m r)) (Fin (orbDim m r)) ℝ :=
  dAltOrbMat N m r * zOrbMat m r
theorem dAltStepOrbMat_orthogonal_two_pow {n m r : ℕ} (hn1 : 1 ≤ n) (h2m : 2 * m < 2 ^ n)
    (hmrN : m + r ≤ 2 ^ n) :
    (dAltStepOrbMat (2 ^ n) m r)ᵀ * dAltStepOrbMat (2 ^ n) m r = 1 := by
  unfold dAltStepOrbMat
  rw [Matrix.transpose_mul, dAltOrbMat_transpose hmrN, zOrbMat_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (zOrbMat m r),
    dAltOrbMat_mul_self_two_pow hn1 h2m hmrN, Matrix.one_mul, zOrbMat_mul_self]
theorem evalSymStage_dAltSymMat_orbEmbedGen {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    (K : ℕ) (x : Fin (orbDim m R.card) → ℝ) :
    evalSymStage R (dAltSymMat N m) K (orbEmbedGen N m R x) =
      orbEmbedGen N m R ((dAltStepOrbMat N m R.card ^ K) *ᵥ x) := by
  induction K generalizing x with
  | zero =>
    simp [evalSymStage]
  | succ K ih =>
    rw [evalSymStage, symZVec_orbEmbedGen, dAltSymMat_mulVec_orbEmbedGen hmrN, ih]; congr 1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    change ((dAltStepOrbMat N m R.card ^ K * dAltStepOrbMat N m R.card) *ᵥ x) =
      ((dAltStepOrbMat N m R.card ^ (K + 1)) *ᵥ x)
    rw [← pow_succ]
theorem symHitProb_evalSymStage_dAlt {N m : ℕ} {R : Finset (Fin N)} (hmrN : m + R.card ≤ N)
    (K : ℕ) (w : Fin (orbDim m R.card)) :
    symHitProb R (evalSymStage R (dAltSymMat N m) K (u0Vec N m)) w.1 =
      (((dAltStepOrbMat N m R.card ^ K) *ᵥ u0OrbVecGen N m R.card) w) ^ 2 := by
  rw [← orbEmbedGen_u0OrbVecGen hmrN, evalSymStage_dAltSymMat_orbEmbedGen hmrN,
    symHitProb_orbEmbedGen hmrN]

/- ## Section 1: Euclidean `ℓ_2` Norm & Telescoping Perturbation on `Fin d → ℝ` -/
/-- Squared Euclidean `ℓ_2` norm `∑ i, (v i) ^ 2` on `Fin d → ℝ`. -/
noncomputable def vecSqNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ i : Fin d, (v i) ^ 2
/-- Euclidean `ℓ_2` norm `√(∑ i, (v i) ^ 2)` on `Fin d → ℝ`. -/
noncomputable def vecNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := √(vecSqNorm v)
theorem vecSqNorm_eq_dot {d : ℕ} (v : Fin d → ℝ) : vecSqNorm v = v ⬝ᵥ v := by
  simp [vecSqNorm, dotProduct, sq]
theorem vecSqNorm_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ vecSqNorm v :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
theorem vecNorm_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ vecNorm v := Real.sqrt_nonneg _
theorem sq_vecNorm {d : ℕ} (v : Fin d → ℝ) : (vecNorm v) ^ 2 = vecSqNorm v :=
  Real.sq_sqrt (vecSqNorm_nonneg v)
theorem abs_apply_le_vecNorm {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    |v i| ≤ vecNorm v := by
  unfold vecNorm vecSqNorm
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i))
theorem dot_le_vecNorm_mul {d : ℕ} (u v : Fin d → ℝ) : u ⬝ᵥ v ≤ vecNorm u * vecNorm v := by
  set a := vecNorm u; set b := vecNorm v
  have ha0 : 0 ≤ a := vecNorm_nonneg u; have hb0 : 0 ≤ b := vecNorm_nonneg v
  have ha2 : a ^ 2 = vecSqNorm u := sq_vecNorm u; have hb2 : b ^ 2 = vecSqNorm v := sq_vecNorm v
  by_cases hab : a * b = 0
  · rcases mul_eq_zero.mp hab with ha_eq | hb_eq
    · have hu_sq : vecSqNorm u = 0 := by rw [← ha2, ha_eq]; ring
      have hu_zero : ∀ i : Fin d, u i = 0 := fun i ↦ by
        have hle : (u i) ^ 2 ≤ vecSqNorm u :=
          Finset.single_le_sum (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)
        nlinarith [sq_nonneg (u i)]
      simp [dotProduct, hu_zero, hab]
    · have hv_sq : vecSqNorm v = 0 := by rw [← hb2, hb_eq]; ring
      have hv_zero : ∀ i : Fin d, v i = 0 := fun i ↦ by
        have hle : (v i) ^ 2 ≤ vecSqNorm v :=
          Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
        nlinarith [sq_nonneg (v i)]
      simp [dotProduct, hv_zero, hab]
  · have hab_pos : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha0 hb0) (Ne.symm hab)
    have hsum : 0 ≤ ∑ i : Fin d, (b * u i - a * v i) ^ 2 :=
      Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    have hexp : (∑ i : Fin d, (b * u i - a * v i) ^ 2) =
          b ^ 2 * vecSqNorm u + a ^ 2 * vecSqNorm v - 2 * (a * b) * (u ⬝ᵥ v) := by
      have hterm : ∀ i : Fin d, (b * u i - a * v i) ^ 2 =
            b ^ 2 * (u i) ^ 2 + a ^ 2 * (v i) ^ 2 - 2 * (a * b) * (u i * v i) := fun i ↦ by ring
      simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    rw [hexp, ha2, hb2] at hsum
    have hprod : 0 ≤ 2 * (a * b) * (a * b - u ⬝ᵥ v) := by nlinarith
    nlinarith
theorem vecNorm_zero {d : ℕ} : vecNorm (0 : Fin d → ℝ) = 0 := by simp [vecNorm, vecSqNorm]
theorem vecNorm_neg {d : ℕ} (v : Fin d → ℝ) : vecNorm (-v) = vecNorm v := by
  simp [vecNorm, vecSqNorm]
theorem vecNorm_smul {d : ℕ} (c : ℝ) (v : Fin d → ℝ) : vecNorm (c • v) = |c| * vecNorm v := by
  have hsq : vecSqNorm (c • v) = c ^ 2 * vecSqNorm v := by
    unfold vecSqNorm; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow]
  unfold vecNorm; rw [hsq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
theorem vecNorm_add_le {d : ℕ} (u v : Fin d → ℝ) : vecNorm (u + v) ≤ vecNorm u + vecNorm v := by
  have hrhs : 0 ≤ vecNorm u + vecNorm v := add_nonneg (vecNorm_nonneg u) (vecNorm_nonneg v)
  rw [vecNorm, Real.sqrt_le_iff]
  refine ⟨hrhs, ?_⟩
  have hexp : vecSqNorm (u + v) = vecSqNorm u + 2 * (u ⬝ᵥ v) + vecSqNorm v := by
    unfold vecSqNorm dotProduct
    have hterm : ∀ i : Fin d, (u i + v i) ^ 2 = (u i) ^ 2 + 2 * (u i * v i) + (v i) ^ 2 :=
      fun i ↦ by ring
    simp only [Pi.add_apply, hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp]; have hcs := dot_le_vecNorm_mul u v; have hu2 := sq_vecNorm u; have hv2 := sq_vecNorm v
  nlinarith
theorem vecNorm_sub_le {d : ℕ} (u v : Fin d → ℝ) : vecNorm (u - v) ≤ vecNorm u + vecNorm v := by
  rw [sub_eq_add_neg, ← vecNorm_neg v]; exact vecNorm_add_le u (-v)
theorem vecNorm_sum_range_le {d : ℕ} : ∀ (n : ℕ) (f : ℕ → Fin d → ℝ),
      vecNorm (∑ k ∈ Finset.range n, f k) ≤ ∑ k ∈ Finset.range n, vecNorm (f k)
  | 0, _ => by simp [vecNorm_zero]
  | n + 1, f => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (vecNorm_add_le _ _).trans (add_le_add (vecNorm_sum_range_le n f) le_rfl)
theorem vecNorm_entrywise_le {d : ℕ} {v : Fin d → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hv : ∀ i, |v i| ≤ ε) : vecNorm v ≤ √(d : ℝ) * ε := by
  rw [vecNorm, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  calc vecSqNorm v
      ≤ ∑ _i : Fin d, ε ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ by
          rw [← sq_abs (v i)]; exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
    _ = (d : ℝ) * ε ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
theorem vecNorm_mulVec_of_orthogonal {d : ℕ} {U : Matrix (Fin d) (Fin d) ℝ}
    (hU : Uᵀ * U = 1) (v : Fin d → ℝ) : vecNorm (U *ᵥ v) = vecNorm v := by
  have hsq : vecSqNorm (U *ᵥ v) = vecSqNorm v := by
    rw [vecSqNorm_eq_dot, vecSqNorm_eq_dot, Matrix.dotProduct_mulVec]
    have hvm : (U *ᵥ v) ᵥ* U = Uᵀ *ᵥ (U *ᵥ v) := by
      funext j
      simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
    rw [hvm, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  unfold vecNorm; rw [hsq]
theorem vecNorm_pow_mulVec_le {d : ℕ} {T : Matrix (Fin d) (Fin d) ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hT : ∀ x, vecNorm (T *ᵥ x) ≤ c * vecNorm x) :
    ∀ (k : ℕ) (v : Fin d → ℝ), vecNorm ((T ^ k) *ᵥ v) ≤ c ^ k * vecNorm v
  | 0, v => by simp
  | k + 1, v => by
    have hstep : (T ^ (k + 1)) *ᵥ v = T *ᵥ ((T ^ k) *ᵥ v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hstep, pow_succ']
    calc vecNorm (T *ᵥ ((T ^ k) *ᵥ v))
        ≤ c * vecNorm ((T ^ k) *ᵥ v) := hT _
      _ ≤ c * (c ^ k * vecNorm v) := mul_le_mul_of_nonneg_left (vecNorm_pow_mulVec_le hc hT k v) hc
      _ = c * c ^ k * vecNorm v := by ring
theorem vecNorm_entrywise_mulVec_le {d : ℕ} {E : Matrix (Fin d) (Fin d) ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε) (v : Fin d → ℝ) :
    vecNorm (E *ᵥ v) ≤ (d : ℝ) ^ 2 * ε * vecNorm v := by
  have hrhs : 0 ≤ (d : ℝ) ^ 2 * ε * vecNorm v :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hε) (vecNorm_nonneg v)
  rw [vecNorm, Real.sqrt_le_iff]
  refine ⟨hrhs, ?_⟩
  have hrow (i : Fin d) : |(E *ᵥ v) i| ≤ (d : ℝ) * ε * vecNorm v := by
    calc |(E *ᵥ v) i|
        = |∑ j : Fin d, E i j * v j| := rfl
      _ ≤ ∑ j : Fin d, |E i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin d, |E i j| * |v j| :=
          Finset.sum_congr rfl fun j _ ↦ abs_mul _ _
      _ ≤ ∑ _j : Fin d, ε * vecNorm v :=
          Finset.sum_le_sum fun j _ ↦
            mul_le_mul (hE i j) (abs_apply_le_vecNorm v j) (abs_nonneg _) hε
      _ = (d : ℝ) * ε * vecNorm v := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hsq_row (i : Fin d) : ((E *ᵥ v) i) ^ 2 ≤ ((d : ℝ) * ε * vecNorm v) ^ 2 := by
    rw [← sq_abs ((E *ᵥ v) i)]; exact pow_le_pow_left₀ (abs_nonneg _) (hrow i) 2
  have hsum : vecSqNorm (E *ᵥ v) ≤ (d : ℝ) * ((d : ℝ) * ε * vecNorm v) ^ 2 := by
    calc vecSqNorm (E *ᵥ v)
        ≤ ∑ _i : Fin d, ((d : ℝ) * ε * vecNorm v) ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ hsq_row i
      _ = (d : ℝ) * ((d : ℝ) * ε * vecNorm v) ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  have hd_le : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · norm_num
    · have hd1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd_pos
      nlinarith
  calc vecSqNorm (E *ᵥ v)
      ≤ (d : ℝ) * ((d : ℝ) * ε * vecNorm v) ^ 2 := hsum
    _ ≤ (d : ℝ) ^ 2 * ((d : ℝ) * ε * vecNorm v) ^ 2 :=
        mul_le_mul_of_nonneg_right hd_le (sq_nonneg _)
    _ = ((d : ℝ) ^ 2 * ε * vecNorm v) ^ 2 := by ring
theorem vecNorm_pow_mulVec_sub_le {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ} {δ : ℝ}
    (hA : ∀ x, vecNorm (A *ᵥ x) ≤ vecNorm x)
    (hB : ∀ x, vecNorm (B *ᵥ x) ≤ vecNorm x)
    (hδ : 0 ≤ δ)
    (hdiff : ∀ x, vecNorm ((A - B) *ᵥ x) ≤ δ * vecNorm x) : ∀ (K : ℕ) (u₀ e₀ : Fin d → ℝ),
      vecNorm ((A ^ K) *ᵥ u₀ - (B ^ K) *ᵥ e₀) ≤ vecNorm (u₀ - e₀) + (K : ℝ) * δ * vecNorm e₀
  | 0, u₀, e₀ => by simp
  | K + 1, u₀, e₀ => by
    have hsplit : (A ^ (K + 1)) *ᵥ u₀ - (B ^ (K + 1)) *ᵥ e₀ =
          A *ᵥ ((A ^ K) *ᵥ u₀ - (B ^ K) *ᵥ e₀) + (A - B) *ᵥ ((B ^ K) *ᵥ e₀) := by
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_sub, Matrix.sub_mulVec]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hBK : vecNorm ((B ^ K) *ᵥ e₀) ≤ vecNorm e₀ := by
      simpa using vecNorm_pow_mulVec_le zero_le_one (fun x ↦ by simpa using hB x) K e₀
    rw [hsplit]
    calc vecNorm (A *ᵥ ((A ^ K) *ᵥ u₀ - (B ^ K) *ᵥ e₀) + (A - B) *ᵥ ((B ^ K) *ᵥ e₀))
        ≤ vecNorm (A *ᵥ ((A ^ K) *ᵥ u₀ - (B ^ K) *ᵥ e₀)) +
            vecNorm ((A - B) *ᵥ ((B ^ K) *ᵥ e₀)) := vecNorm_add_le _ _
      _ ≤ vecNorm ((A ^ K) *ᵥ u₀ - (B ^ K) *ᵥ e₀) + δ * vecNorm ((B ^ K) *ᵥ e₀) :=
          add_le_add (hA _) (hdiff _)
      _ ≤ (vecNorm (u₀ - e₀) + (K : ℝ) * δ * vecNorm e₀) + δ * vecNorm e₀ :=
          add_le_add (vecNorm_pow_mulVec_sub_le hA hB hδ hdiff K u₀ e₀)
            (mul_le_mul_of_nonneg_left hBK hδ)
      _ = vecNorm (u₀ - e₀) + ((K + 1 : ℕ) : ℝ) * δ * vecNorm e₀ := by push_cast; ring
/- ## Section 2: Tridiagonal Skew Matrices & `dAltGenMat` -/
/-- Generic `(d + 1) × (d + 1)` skew-symmetric tridiagonal matrix with band `γ 0,..., γ (d -
  1)`:
  subdiagonal `(b + 1, b)` has `+γ b` and superdiagonal `(a, a + 1)` has `-γ a`. -/
def tridiagSkewMat (d : ℕ) (γ : ℕ → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun a b ↦ if a.1 = b.1 + 1 then γ b.1
    else if b.1 = a.1 + 1 then -γ a.1
    else 0
theorem tridiagSkewMat_transpose (d : ℕ) (γ : ℕ → ℝ) :
    (tridiagSkewMat d γ)ᵀ = -tridiagSkewMat d γ := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply, tridiagSkewMat, Matrix.of_apply]
  by_cases h1 : b.1 = a.1 + 1
  · have h2 : ¬(a.1 = b.1 + 1) := by omega
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1]; ring
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : a.1 = b.1 + 1
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]; ring
theorem tridiagSkewMat_smul_sub (d : ℕ) (c : ℝ) (β γ : ℕ → ℝ) :
    c • tridiagSkewMat d β - tridiagSkewMat d γ =
      tridiagSkewMat d (fun w ↦ c * β w - γ w) := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, tridiagSkewMat, Matrix.of_apply]
  split_ifs <;> ring
theorem tridiagSkewMat_mulVec_apply (d : ℕ) (γ : ℕ → ℝ) (v : Fin (d + 1) → ℝ)
    (a : Fin (d + 1)) : (tridiagSkewMat d γ *ᵥ v) a =
      (if ha : 0 < a.1 then γ (a.1 - 1) * v ⟨a.1 - 1, by omega⟩ else 0) +
      (if ha : a.1 < d then -γ a.1 * v ⟨a.1 + 1, by omega⟩ else 0) := by
  unfold Matrix.mulVec dotProduct tridiagSkewMat; simp only [Matrix.of_apply]
  have hsplit (b : Fin (d + 1)) :
      (if a.1 = b.1 + 1 then γ b.1 else if b.1 = a.1 + 1 then -γ a.1 else 0) * v b =
      (if a.1 = b.1 + 1 then γ b.1 * v b else 0) +
      (if b.1 = a.1 + 1 then -γ a.1 * v b else 0) := by
    by_cases h1 : a.1 = b.1 + 1
    · have h2 : ¬(b.1 = a.1 + 1) := by omega
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2]; ring
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : b.1 = a.1 + 1
      · rw [ite_eq_left h2, ite_eq_left h2]; ring
      · rw [ite_eq_right h2, ite_eq_right h2]; ring
  simp_rw [hsplit]; rw [Finset.sum_add_distrib]
  congr 1
  · by_cases ha0 : 0 < a.1
    · rw [dite_eq_left ha0]
      let b0 : Fin (d + 1) := ⟨a.1 - 1, by omega⟩; rw [Finset.sum_eq_single b0]
      · have hb0 : a.1 = b0.1 + 1 := by dsimp [b0]; omega
        rw [ite_eq_left hb0]
      · intro b _ hne
        have hne_val : a.1 ≠ b.1 + 1 := by intro heq; apply hne; ext; dsimp [b0]; omega
        rw [ite_eq_right hne_val]
      · intro hmem; exact absurd (Finset.mem_univ b0) hmem
    · rw [dite_eq_right ha0]
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      have hne_val : a.1 ≠ b.1 + 1 := by omega
      rw [ite_eq_right hne_val]
  · by_cases ha_lt : a.1 < d
    · rw [dite_eq_left ha_lt]
      let b1 : Fin (d + 1) := ⟨a.1 + 1, by omega⟩; rw [Finset.sum_eq_single b1]
      · rw [ite_eq_left rfl]
      · intro b _ hne
        have hne_val : b.1 ≠ a.1 + 1 := by intro heq; apply hne; ext; dsimp [b1]; omega
        rw [ite_eq_right hne_val]
      · intro hmem; exact absurd (Finset.mem_univ b1) hmem
    · rw [dite_eq_right ha_lt]
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      have hb_lt : b.1 < d + 1 := b.2
      have hne_val : b.1 ≠ a.1 + 1 := by omega
      rw [ite_eq_right hne_val]
theorem vecNorm_tridiagSkewMat_mulVec_le {d : ℕ} {γ : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hγ : ∀ w < d, |γ w| ≤ M) (v : Fin (d + 1) → ℝ) :
    vecNorm (tridiagSkewMat d γ *ᵥ v) ≤ (2 * M) * vecNorm v := by
  let rotEquiv : Fin (d + 1) ≃ Fin (d + 1) :=
    { toFun := fun a ↦ if ha : 0 < a.1 then ⟨a.1 - 1, by omega⟩ else ⟨d, by omega⟩
      invFun := fun b ↦ if hb : b.1 < d then ⟨b.1 + 1, by omega⟩ else ⟨0, by omega⟩
      left_inv := fun a ↦ by
        ext
        have ha_lt : a.1 < d + 1 := a.2
        by_cases ha : 0 < a.1
        · simp only [dite_eq_left ha]
          have hlt : a.1 - 1 < d := by omega
          simp only [dite_eq_left hlt]; omega
        · simp only [dite_eq_right ha]
          have hlt : ¬(d < d) := lt_irrefl d; simp only [dite_eq_right hlt]; omega
      right_inv := fun b ↦ by
        ext
        have hb_lt : b.1 < d + 1 := b.2
        by_cases hb : b.1 < d
        · simp only [dite_eq_left hb]
          have hpos : 0 < b.1 + 1 := by omega
          simp only [dite_eq_left hpos]; omega
        · simp only [dite_eq_right hb]
          have hpos : ¬(0 < 0) := lt_irrefl 0; simp only [dite_eq_right hpos]; omega }
  let gLo : Fin (d + 1) → ℝ := fun a ↦
    if ha : 0 < a.1 then γ (a.1 - 1) * v ⟨a.1 - 1, by omega⟩ else 0
  let gHi : Fin (d + 1) → ℝ := fun a ↦ if ha : a.1 < d then -γ a.1 * v ⟨a.1 + 1, by omega⟩ else 0
  have hdecomp : tridiagSkewMat d γ *ᵥ v = gLo + gHi := funext (tridiagSkewMat_mulVec_apply d γ v)
  have hLo : vecNorm gLo ≤ M * vecNorm v := by
    rw [vecNorm, Real.sqrt_le_iff]
    refine ⟨mul_nonneg hM (vecNorm_nonneg v), ?_⟩
    have hterm (a : Fin (d + 1)) : (gLo a) ^ 2 ≤ M ^ 2 * (v (rotEquiv a)) ^ 2 := by
      by_cases ha : 0 < a.1
      · simp only [gLo, rotEquiv, Equiv.coe_fn_mk, dite_eq_left ha]
        rw [mul_pow, ← sq_abs (γ (a.1 - 1))]
        have hw : a.1 - 1 < d := by have := a.2; omega
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hγ (a.1 - 1) hw) 2) (sq_nonneg _)
      · simp only [gLo, dite_eq_right ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc vecSqNorm gLo
        ≤ ∑ a : Fin (d + 1), M ^ 2 * (v (rotEquiv a)) ^ 2 :=
          Finset.sum_le_sum fun a _ ↦ hterm a
      _ = M ^ 2 * ∑ a : Fin (d + 1), (v (rotEquiv a)) ^ 2 := by rw [← Finset.mul_sum]
      _ = M ^ 2 * vecSqNorm v := by rw [Equiv.sum_comp rotEquiv (fun x ↦ (v x) ^ 2)]; rfl
      _ = (M * vecNorm v) ^ 2 := by rw [mul_pow, sq_vecNorm]
  have hHi : vecNorm gHi ≤ M * vecNorm v := by
    rw [vecNorm, Real.sqrt_le_iff]
    refine ⟨mul_nonneg hM (vecNorm_nonneg v), ?_⟩
    have hterm (a : Fin (d + 1)) : (gHi a) ^ 2 ≤ M ^ 2 * (v (rotEquiv.symm a)) ^ 2 := by
      by_cases ha : a.1 < d
      · simp only [gHi, rotEquiv, Equiv.coe_fn_symm_mk, dite_eq_left ha]
        have hsq : (-γ a.1 * v ⟨a.1 + 1, by omega⟩) ^ 2 =
            |γ a.1| ^ 2 * (v ⟨a.1 + 1, by omega⟩) ^ 2 := by
          rw [sq_abs]; ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hγ a.1 ha) 2) (sq_nonneg _)
      · simp only [gHi, dite_eq_right ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc vecSqNorm gHi
        ≤ ∑ a : Fin (d + 1), M ^ 2 * (v (rotEquiv.symm a)) ^ 2 :=
          Finset.sum_le_sum fun a _ ↦ hterm a
      _ = M ^ 2 * ∑ a : Fin (d + 1), (v (rotEquiv.symm a)) ^ 2 := by rw [← Finset.mul_sum]
      _ = M ^ 2 * vecSqNorm v := by rw [Equiv.sum_comp rotEquiv.symm (fun x ↦ (v x) ^ 2)]; rfl
      _ = (M * vecNorm v) ^ 2 := by rw [mul_pow, sq_vecNorm]
  rw [hdecomp]
  calc vecNorm (gLo + gHi)
      ≤ vecNorm gLo + vecNorm gHi := vecNorm_add_le gLo gHi
    _ ≤ M * vecNorm v + M * vecNorm v := add_le_add hLo hHi
    _ = (2 * M) * vecNorm v := by ring
/-- Exact continuum coupling `b_w = √(4 (w + 1) (m - w) (r - w))` between `|w⟩` and `|w +
  1⟩`. -/
noncomputable def dAltCoupling (m r w : ℕ) : ℝ := √((4 * (w + 1) * (m - w) * (r - w) : ℕ) : ℝ)
/-- Closed-form two-band operator norm upper bound `√(4 (min m r + 1) ^ 2 max m r)`. -/
noncomputable def dAltGenNormBound (m r : ℕ) : ℝ := √((4 * (min m r + 1) ^ 2 * max m r : ℕ) : ℝ)
/-- Skew-symmetric tridiagonal generator `G` on `Fin (orbDim m r)` for `(D_{\text{alt}}
  Z_R)`. -/
noncomputable abbrev dAltGenMat (m r : ℕ) : Matrix (Fin (orbDim m r)) (Fin (orbDim m r)) ℝ :=
  tridiagSkewMat (min m r) (dAltCoupling m r)
theorem dAltGenMat_transpose (m r : ℕ) : (dAltGenMat m r)ᵀ = -dAltGenMat m r :=
  tridiagSkewMat_transpose (min m r) (dAltCoupling m r)
private lemma four_mul_le_add_sq (a b : ℕ) : 4 * a * b ≤ (a + b) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]
theorem dAltCoupling_le_half_normBound {m r w : ℕ} (hw : w < min m r) :
    dAltCoupling m r w ≤ (1 / 2) * dAltGenNormBound m r := by
  have hprod_nat : 4 * (w + 1) * (m - w) * (r - w) ≤ (min m r + 1) ^ 2 * max m r := by
    by_cases hmr : m ≤ r
    · have hmin : min m r = m := Nat.min_eq_left hmr
      have hmax : max m r = r := Nat.max_eq_right hmr; rw [hmin] at hw ⊢; rw [hmax]
      have h1 : 4 * (w + 1) * (m - w) ≤ (m + 1) ^ 2 := by
        simpa [show w + 1 + (m - w) = m + 1 by omega] using four_mul_le_add_sq (w + 1) (m - w)
      exact Nat.mul_le_mul h1 (Nat.sub_le r w)
    · have hrm : r ≤ m := by omega
      have hmin : min m r = r := Nat.min_eq_right hrm
      have hmax : max m r = m := Nat.max_eq_left hrm; rw [hmin] at hw ⊢; rw [hmax]
      have h1 : 4 * (w + 1) * (r - w) ≤ (r + 1) ^ 2 := by
        simpa [show w + 1 + (r - w) = r + 1 by omega] using four_mul_le_add_sq (w + 1) (r - w)
      calc 4 * (w + 1) * (m - w) * (r - w)
          = 4 * (w + 1) * (r - w) * (m - w) := by ring
        _ ≤ (r + 1) ^ 2 * m := Nat.mul_le_mul h1 (Nat.sub_le m w)
  have h4 : (4 : ℝ) * ((4 * (w + 1) * (m - w) * (r - w) : ℕ) : ℝ) ≤
      ((4 * (min m r + 1) ^ 2 * max m r : ℕ) : ℝ) := by
    have hnat : 4 * (4 * (w + 1) * (m - w) * (r - w)) ≤ 4 * (min m r + 1) ^ 2 * max m r := by
      calc 4 * (4 * (w + 1) * (m - w) * (r - w))
          = 4 * ((4 * (w + 1) * (m - w) * (r - w))) := rfl
        _ ≤ 4 * ((min m r + 1) ^ 2 * max m r) := Nat.mul_le_mul_left 4 hprod_nat
        _ = 4 * (min m r + 1) ^ 2 * max m r := by ring
    exact_mod_cast hnat
  have hsq := Real.sqrt_le_sqrt h4
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hsq
  unfold dAltCoupling dAltGenNormBound; linarith
theorem vecNorm_dAltGenMat_mulVec_le (m r : ℕ) (v : Fin (orbDim m r) → ℝ) :
    vecNorm (dAltGenMat m r *ᵥ v) ≤ dAltGenNormBound m r * vecNorm v := by
  have hM : 0 ≤ (1 / 2) * dAltGenNormBound m r := by unfold dAltGenNormBound; positivity
  have hbound : ∀ w < min m r, |dAltCoupling m r w| ≤ (1 / 2) * dAltGenNormBound m r := by
    intro w hw
    have hnn : 0 ≤ dAltCoupling m r w := by unfold dAltCoupling; exact Real.sqrt_nonneg _
    rw [abs_of_nonneg hnn]; exact dAltCoupling_le_half_normBound hw
  simpa [mul_comm, ← mul_assoc] using vecNorm_tridiagSkewMat_mulVec_le hM hbound v
/- ## Section 3: Degree-`8` Polynomial Contraction, Stability, & Grouping -/
/-- Degree-`8` truncated exponential `1 + X + X^2 / fact 2 +... + X^8 / fact 8` of a matrix
  `X`. -/
noncomputable def taylor8OfMat {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  1 + X + (1 / 2 : ℝ) • X ^ 2 + (1 / 6 : ℝ) • X ^ 3 + (1 / 24 : ℝ) • X ^ 4 +
    (1 / 120 : ℝ) • X ^ 5 + (1 / 720 : ℝ) • X ^ 6 + (1 / 5040 : ℝ) • X ^ 7 +
    (1 / 40320 : ℝ) • X ^ 8
/-- Scaled degree-`8` truncated exponential `taylor8OfMat (t • G)`. -/
noncomputable abbrev taylor8Mat {d : ℕ} (t : ℝ) (G : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  taylor8OfMat (t • G)
theorem taylor8OfMat_zero {d : ℕ} : taylor8OfMat (0 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  simp [taylor8OfMat]
theorem dot_skew_mulVec {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ} (hX : Xᵀ = -X)
    (u w : Fin d → ℝ) : u ⬝ᵥ (X *ᵥ w) = -((X *ᵥ u) ⬝ᵥ w) := by
  rw [Matrix.dotProduct_mulVec]
  have hvm : u ᵥ* X = Xᵀ *ᵥ u := by
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [hvm, hX, Matrix.neg_mulVec]; simp [dotProduct]
theorem dot_pow_skew_shift {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ} (hX : Xᵀ = -X)
    (v : Fin d → ℝ) :
    ∀ (a b : ℕ), ((X ^ a) *ᵥ v) ⬝ᵥ ((X ^ b) *ᵥ v) = (-1 : ℝ) ^ b * (((X ^ (a + b)) *ᵥ v) ⬝ᵥ v)
  | a, 0 => by simp
  | a, b + 1 => by
    have hb : (X ^ (b + 1)) *ᵥ v = X *ᵥ ((X ^ b) *ᵥ v) := by rw [pow_succ', Matrix.mulVec_mulVec]
    have ha : X *ᵥ ((X ^ a) *ᵥ v) = (X ^ (a + 1)) *ᵥ v := by rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hb, dot_skew_mulVec hX, ha, dot_pow_skew_shift hX v (a + 1) b,
      show a + 1 + b = a + (b + 1) by omega, pow_succ]
    ring
theorem dot_pow_skew_odd {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ} (hX : Xᵀ = -X)
    (v : Fin d → ℝ) (k : ℕ) : ((X ^ (2 * k + 1)) *ᵥ v) ⬝ᵥ v = 0 := by
  have h := dot_pow_skew_shift hX v 0 (2 * k + 1)
  simp only [pow_zero, Matrix.one_mulVec, zero_add] at h
  have hp : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [dotProduct_comm, hp] at h; linarith
theorem dot_pow_skew_even {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ} (hX : Xᵀ = -X)
    (v : Fin d → ℝ) (k : ℕ) :
    ((X ^ (2 * k)) *ᵥ v) ⬝ᵥ v = (-1 : ℝ) ^ k * vecSqNorm ((X ^ k) *ᵥ v) := by
  have h := dot_pow_skew_shift hX v k k; rw [← vecSqNorm_eq_dot, show k + k = 2 * k by omega] at h
  have hp : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc ((X ^ (2 * k)) *ᵥ v) ⬝ᵥ v
      = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (((X ^ (2 * k)) *ᵥ v) ⬝ᵥ v) := by rw [hp, one_mul]
    _ = (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * (((X ^ (2 * k)) *ᵥ v) ⬝ᵥ v)) := by ring
    _ = (-1 : ℝ) ^ k * vecSqNorm ((X ^ k) *ᵥ v) := by rw [← h]
theorem vecNorm_taylor8OfMat_mulVec_le {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ}
    (hX : Xᵀ = -X) (hB : ∀ u, vecNorm (X *ᵥ u) ≤ vecNorm u) (v : Fin d → ℝ) :
    vecNorm (taylor8OfMat X *ᵥ v) ≤ vecNorm v := by
  rw [vecNorm, Real.sqrt_le_iff]
  refine ⟨vecNorm_nonneg v, ?_⟩
  rw [sq_vecNorm]
  let x : ℕ → Fin d → ℝ := fun k ↦ (X ^ k) *ᵥ v
  let s : ℕ → ℝ := fun k ↦ vecSqNorm (x k)
  have hs_step (k : ℕ) : s (k + 1) ≤ s k := by
    have hx : x (k + 1) = X *ᵥ x k := by simp [x, pow_succ', Matrix.mulVec_mulVec]
    have hn := hB (x k); rw [← hx] at hn
    have hsq := pow_le_pow_left₀ (vecNorm_nonneg _) hn 2; rwa [sq_vecNorm, sq_vecNorm] at hsq
  have hneg_even (m : ℕ) : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
  have heo (a b : ℕ) : x (2 * a) ⬝ᵥ x (2 * b + 1) = 0 := by
    dsimp only [x]
    rw [dot_pow_skew_shift hX v (2 * a) (2 * b + 1),
      show 2 * a + (2 * b + 1) = 2 * (a + b) + 1 by omega,
      dot_pow_skew_odd hX v (a + b), mul_zero]
  have hee (a b : ℕ) : x (2 * a) ⬝ᵥ x (2 * b) = (-1 : ℝ) ^ (a + b) * s (a + b) := by
    dsimp only [x, s]
    rw [dot_pow_skew_shift hX v (2 * a) (2 * b),
      show 2 * a + 2 * b = 2 * (a + b) by omega,
      dot_pow_skew_even hX v (a + b), hneg_even b, one_mul]
  have hoo (a b : ℕ) : x (2 * a + 1) ⬝ᵥ x (2 * b + 1) = (-1 : ℝ) ^ (a + b) * s (a + b + 1) := by
    dsimp only [x, s]
    rw [dot_pow_skew_shift hX v (2 * a + 1) (2 * b + 1),
      show (2 * a + 1) + (2 * b + 1) = 2 * (a + b + 1) by omega,
      dot_pow_skew_even hX v (a + b + 1), pow_add (-1 : ℝ) (2 * b) 1, hneg_even b, pow_one,
      pow_add (-1 : ℝ) (a + b) 1, pow_one]
    ring
  let uE : Fin d → ℝ :=
    x 0 + (1 / 2 : ℝ) • x 2 + (1 / 24 : ℝ) • x 4 + (1 / 720 : ℝ) • x 6 + (1 / 40320 : ℝ) • x 8
  let uO : Fin d → ℝ := x 1 + (1 / 6 : ℝ) • x 3 + (1 / 120 : ℝ) • x 5 + (1 / 5040 : ℝ) • x 7
  have hsplit : taylor8OfMat X *ᵥ v = uE + uO := by
    ext i
    simp only [taylor8OfMat, uE, uO, x, pow_zero, pow_one, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcross : uE ⬝ᵥ uO = 0 := by
    dsimp only [uE, uO]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [heo 0 0, heo 0 1, heo 0 2, heo 0 3, heo 1 0, heo 1 1, heo 1 2, heo 1 3,
      heo 2 0, heo 2 1, heo 2 2, heo 2 3, heo 3 0, heo 3 1, heo 3 2, heo 3 3,
      heo 4 0, heo 4 1, heo 4 2, heo 4 3]
    ring
  have hcross' : uO ⬝ᵥ uE = 0 := by rw [dotProduct_comm]; exact hcross
  have hnorm_sum : vecSqNorm (uE + uO) = uE ⬝ᵥ uE + uO ⬝ᵥ uO := by
    simp only [vecSqNorm_eq_dot, add_dotProduct, dotProduct_add, hcross, hcross',
      add_zero, zero_add]
  have hpoly : uE ⬝ᵥ uE + uO ⬝ᵥ uO =
      s 0 - (s 5 / 201600 - s 6 / 1451520) - (s 7 / 33868800 - s 8 / 1625702400) := by
    dsimp only [uE, uO]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hee 0 0, hee 0 1, hee 0 2, hee 0 3, hee 0 4, hee 1 0, hee 1 1, hee 1 2, hee 1 3, hee 1 4,
      hee 2 0, hee 2 1, hee 2 2, hee 2 3, hee 2 4, hee 3 0, hee 3 1, hee 3 2, hee 3 3, hee 3 4,
      hee 4 0, hee 4 1, hee 4 2, hee 4 3, hee 4 4, hoo 0 0, hoo 0 1, hoo 0 2, hoo 0 3,
      hoo 1 0, hoo 1 1, hoo 1 2, hoo 1 3, hoo 2 0, hoo 2 1, hoo 2 2, hoo 2 3,
      hoo 3 0, hoo 3 1, hoo 3 2, hoo 3 3]
    norm_num
    ring
  have hs0 : s 0 = vecSqNorm v := by simp [s, x]
  have hs56 := hs_step 5; have hs78 := hs_step 7
  have hs6_nn : 0 ≤ s 6 := vecSqNorm_nonneg _; have hs8_nn : 0 ≤ s 8 := vecSqNorm_nonneg _
  rw [hsplit, hnorm_sum, hpoly, hs0]; linarith
theorem vecNorm_taylor8Mat_mulVec_le {d : ℕ} {t B : ℝ} {G : Matrix (Fin d) (Fin d) ℝ}
    (hG : Gᵀ = -G) (ht : 0 ≤ t) (_hB0 : 0 ≤ B)
    (hGB : ∀ u, vecNorm (G *ᵥ u) ≤ B * vecNorm u) (htB : t * B ≤ 1)
    (v : Fin d → ℝ) : vecNorm (taylor8Mat t G *ᵥ v) ≤ vecNorm v := by
  apply vecNorm_taylor8OfMat_mulVec_le
  · rw [Matrix.transpose_smul, hG, smul_neg]
  · intro u
    rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg ht]
    calc t * vecNorm (G *ᵥ u)
        ≤ t * (B * vecNorm u) := mul_le_mul_of_nonneg_left (hGB u) ht
      _ = (t * B) * vecNorm u := by ring
      _ ≤ 1 * vecNorm u := mul_le_mul_of_nonneg_right htB (vecNorm_nonneg u)
      _ = vecNorm u := one_mul _
theorem vecNorm_pow_sub_pow_mulVec_le {d : ℕ} {X Y : Matrix (Fin d) (Fin d) ℝ} {δ : ℝ}
    (hX : ∀ u, vecNorm (X *ᵥ u) ≤ (1 / 2) * vecNorm u)
    (hY : ∀ u, vecNorm (Y *ᵥ u) ≤ (1 / 2) * vecNorm u)
    (hδ : 0 ≤ δ)
    (hXY : ∀ u, vecNorm ((X - Y) *ᵥ u) ≤ δ * vecNorm u) : ∀ (k : ℕ) (v : Fin d → ℝ),
      vecNorm ((X ^ k - Y ^ k) *ᵥ v) ≤ (k : ℝ) * (1 / 2 : ℝ) ^ (k - 1) * δ * vecNorm v
  | 0, v => by simp [vecNorm_zero]
  | k + 1, v => by
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simpa using hXY v
    · have hsplit : (X ^ (k + 1) - Y ^ (k + 1)) *ᵥ v =
            X *ᵥ ((X ^ k - Y ^ k) *ᵥ v) + (X - Y) *ᵥ ((Y ^ k) *ᵥ v) := by
        rw [pow_succ', pow_succ', Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply]; ring
      have hYk : vecNorm ((Y ^ k) *ᵥ v) ≤ (1 / 2 : ℝ) ^ k * vecNorm v :=
        vecNorm_pow_mulVec_le (by norm_num) hY k v
      have hpow_eq : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (k - 1) = (1 / 2 : ℝ) ^ k := by
        conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
      rw [hsplit, Nat.add_sub_cancel]
      calc vecNorm (X *ᵥ ((X ^ k - Y ^ k) *ᵥ v) + (X - Y) *ᵥ ((Y ^ k) *ᵥ v))
          ≤ vecNorm (X *ᵥ ((X ^ k - Y ^ k) *ᵥ v)) +
              vecNorm ((X - Y) *ᵥ ((Y ^ k) *ᵥ v)) := vecNorm_add_le _ _
        _ ≤ (1 / 2) * vecNorm ((X ^ k - Y ^ k) *ᵥ v) + δ * vecNorm ((Y ^ k) *ᵥ v) :=
            add_le_add (hX _) (hXY _)
        _ ≤ (1 / 2) * ((k : ℝ) * (1 / 2 : ℝ) ^ (k - 1) * δ * vecNorm v) +
              δ * ((1 / 2 : ℝ) ^ k * vecNorm v) :=
            add_le_add
              (mul_le_mul_of_nonneg_left (vecNorm_pow_sub_pow_mulVec_le hX hY hδ hXY k v)
                (by norm_num))
              (mul_le_mul_of_nonneg_left hYk hδ)
        _ = (k : ℝ) * ((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (k - 1)) * δ * vecNorm v +
              (1 / 2 : ℝ) ^ k * δ * vecNorm v := by ring
        _ = ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k * δ * vecNorm v := by rw [hpow_eq]; push_cast; ring
private lemma vecNorm_add8_le {d : ℕ} (u1 u2 u3 u4 u5 u6 u7 u8 : Fin d → ℝ) :
    vecNorm (u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8) ≤
      vecNorm u1 + vecNorm u2 + vecNorm u3 + vecNorm u4 +
        vecNorm u5 + vecNorm u6 + vecNorm u7 + vecNorm u8 := by
  have h7 := vecNorm_add_le (u1 + u2 + u3 + u4 + u5 + u6 + u7) u8
  have h6 := vecNorm_add_le (u1 + u2 + u3 + u4 + u5 + u6) u7
  have h5 := vecNorm_add_le (u1 + u2 + u3 + u4 + u5) u6
  have h4 := vecNorm_add_le (u1 + u2 + u3 + u4) u5; have h3 := vecNorm_add_le (u1 + u2 + u3) u4
  have h2 := vecNorm_add_le (u1 + u2) u3; have h1 := vecNorm_add_le u1 u2; linarith
theorem vecNorm_taylor8OfMat_sub_mulVec_le {d : ℕ} {X Y : Matrix (Fin d) (Fin d) ℝ} {δ : ℝ}
    (hX : ∀ u, vecNorm (X *ᵥ u) ≤ (1 / 2) * vecNorm u)
    (hY : ∀ u, vecNorm (Y *ᵥ u) ≤ (1 / 2) * vecNorm u)
    (hδ : 0 ≤ δ)
    (hXY : ∀ u, vecNorm ((X - Y) *ᵥ u) ≤ δ * vecNorm u) (v : Fin d → ℝ) :
    vecNorm ((taylor8OfMat X - taylor8OfMat Y) *ᵥ v) ≤ 2 * δ * vecNorm v := by
  let dVec : ℕ → Fin d → ℝ := fun k ↦ (X ^ k - Y ^ k) *ᵥ v
  have hdecomp : (taylor8OfMat X - taylor8OfMat Y) *ᵥ v =
        dVec 1 + (1 / 2 : ℝ) • dVec 2 + (1 / 6 : ℝ) • dVec 3 + (1 / 24 : ℝ) • dVec 4 +
          (1 / 120 : ℝ) • dVec 5 + (1 / 720 : ℝ) • dVec 6 + (1 / 5040 : ℝ) • dVec 7 +
          (1 / 40320 : ℝ) • dVec 8 := by
    ext i
    simp only [taylor8OfMat, dVec, pow_one, Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hd (k : ℕ) : vecNorm (dVec k) ≤ ((k : ℝ) * (1 / 2 : ℝ) ^ (k - 1)) * (δ * vecNorm v) := by
    calc vecNorm (dVec k)
        ≤ (k : ℝ) * (1 / 2 : ℝ) ^ (k - 1) * δ * vecNorm v :=
          vecNorm_pow_sub_pow_mulVec_le hX hY hδ hXY k v
      _ = ((k : ℝ) * (1 / 2 : ℝ) ^ (k - 1)) * (δ * vecNorm v) := by ring
  have hvn : 0 ≤ δ * vecNorm v := mul_nonneg hδ (vecNorm_nonneg v); rw [hdecomp]
  have htri :
      vecNorm (dVec 1 + (1 / 2 : ℝ) • dVec 2 + (1 / 6 : ℝ) • dVec 3 + (1 / 24 : ℝ) • dVec 4 +
          (1 / 120 : ℝ) • dVec 5 + (1 / 720 : ℝ) • dVec 6 + (1 / 5040 : ℝ) • dVec 7 +
          (1 / 40320 : ℝ) • dVec 8) ≤
        vecNorm (dVec 1) + (1 / 2) * vecNorm (dVec 2) + (1 / 6) * vecNorm (dVec 3) +
          (1 / 24) * vecNorm (dVec 4) + (1 / 120) * vecNorm (dVec 5) +
          (1 / 720) * vecNorm (dVec 6) + (1 / 5040) * vecNorm (dVec 7) +
          (1 / 40320) * vecNorm (dVec 8) := by
    have hsm (c : ℝ) (hc : 0 ≤ c) (u : Fin d → ℝ) : vecNorm (c • u) = c * vecNorm u := by
      rw [vecNorm_smul, abs_of_nonneg hc]
    have h8 := vecNorm_add8_le (dVec 1) ((1 / 2 : ℝ) • dVec 2) ((1 / 6 : ℝ) • dVec 3)
      ((1 / 24 : ℝ) • dVec 4) ((1 / 120 : ℝ) • dVec 5) ((1 / 720 : ℝ) • dVec 6)
      ((1 / 5040 : ℝ) • dVec 7) ((1 / 40320 : ℝ) • dVec 8)
    rw [hsm _ (by norm_num), hsm _ (by norm_num), hsm _ (by norm_num), hsm _ (by norm_num),
      hsm _ (by norm_num), hsm _ (by norm_num), hsm _ (by norm_num)] at h8
    exact h8
  calc vecNorm (dVec 1 + (1 / 2 : ℝ) • dVec 2 + (1 / 6 : ℝ) • dVec 3 + (1 / 24 : ℝ) • dVec 4 +
          (1 / 120 : ℝ) • dVec 5 + (1 / 720 : ℝ) • dVec 6 + (1 / 5040 : ℝ) • dVec 7 +
          (1 / 40320 : ℝ) • dVec 8)
      ≤ vecNorm (dVec 1) + (1 / 2) * vecNorm (dVec 2) + (1 / 6) * vecNorm (dVec 3) +
          (1 / 24) * vecNorm (dVec 4) + (1 / 120) * vecNorm (dVec 5) +
          (1 / 720) * vecNorm (dVec 6) + (1 / 5040) * vecNorm (dVec 7) +
          (1 / 40320) * vecNorm (dVec 8) := htri
    _ ≤ (((1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 0) * (δ * vecNorm v) +
          (1 / 2) * ((((2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 1) * (δ * vecNorm v)) +
          (1 / 6) * ((((3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 2) * (δ * vecNorm v)) +
          (1 / 24) * ((((4 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 3) * (δ * vecNorm v)) +
          (1 / 120) * ((((5 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 4) * (δ * vecNorm v)) +
          (1 / 720) * ((((6 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 5) * (δ * vecNorm v)) +
          (1 / 5040) * ((((7 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 6) * (δ * vecNorm v)) +
          (1 / 40320) * ((((8 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 7) * (δ * vecNorm v)) := by
        gcongr
        · exact hd 1
        · exact hd 2
        · exact hd 3
        · exact hd 4
        · exact hd 5
        · exact hd 6
        · exact hd 7
        · exact hd 8
    _ = (354541 / 215040 : ℝ) * (δ * vecNorm v) := by push_cast; ring
    _ ≤ 2 * (δ * vecNorm v) := mul_le_mul_of_nonneg_right (by norm_num) hvn
    _ = 2 * δ * vecNorm v := by ring
theorem vecNorm_taylor8_mul_sub_succ_le {d : ℕ} {Y : Matrix (Fin d) (Fin d) ℝ} {x : ℝ}
    (hx0 : 0 ≤ x) (hY : ∀ u, vecNorm (Y *ᵥ u) ≤ x * vecNorm u)
    (s : ℝ) (hs0 : 0 ≤ s) (hsx : (s + 1) * x ≤ 1 / 2) (v : Fin d → ℝ) :
    vecNorm ((taylor8OfMat Y * taylor8OfMat (s • Y) - taylor8OfMat ((s + 1) • Y)) *ᵥ v) ≤
      (((s + 1) * x) ^ 9 - (s * x) ^ 9) / 180000 * vecNorm v := by
  have hx_half : x ≤ 1 / 2 := by nlinarith
  let y : ℕ → Fin d → ℝ := fun k ↦ (Y ^ k) *ᵥ v
  have hy_smul (r : ℝ) (j : ℕ) : ((r • Y) ^ j) *ᵥ v = (r ^ j) • y j := by
    rw [smul_pow, Matrix.smul_mulVec]
  have hy_mul (i j : ℕ) (c : ℝ) : (Y ^ i) *ᵥ (c • y j) = c • y (i + j) := by
    dsimp only [y]; rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_add]
  have hy_mul1 (i j : ℕ) : (Y ^ i) *ᵥ y j = y (i + j) := by
    dsimp only [y]; rw [Matrix.mulVec_mulVec, ← pow_add]
  let c9 : ℝ := (1 / 40320 : ℝ) * s + (1 / 10080 : ℝ) * s ^ 2 + (1 / 4320 : ℝ) * s ^ 3 +
      (1 / 2880 : ℝ) * s ^ 4 + (1 / 2880 : ℝ) * s ^ 5 + (1 / 4320 : ℝ) * s ^ 6 +
      (1 / 10080 : ℝ) * s ^ 7 + (1 / 40320 : ℝ) * s ^ 8
  let c10 : ℝ := (1 / 80640 : ℝ) * s ^ 2 + (1 / 30240 : ℝ) * s ^ 3 + (1 / 17280 : ℝ) * s ^ 4 +
      (1 / 14400 : ℝ) * s ^ 5 + (1 / 17280 : ℝ) * s ^ 6 + (1 / 30240 : ℝ) * s ^ 7 +
      (1 / 80640 : ℝ) * s ^ 8
  let c11 : ℝ := (1 / 241920 : ℝ) * s ^ 3 + (1 / 120960 : ℝ) * s ^ 4 + (1 / 86400 : ℝ) * s ^ 5 +
      (1 / 86400 : ℝ) * s ^ 6 + (1 / 120960 : ℝ) * s ^ 7 + (1 / 241920 : ℝ) * s ^ 8
  let c12 : ℝ := (1 / 967680 : ℝ) * s ^ 4 + (1 / 604800 : ℝ) * s ^ 5 + (1 / 518400 : ℝ) * s ^ 6 +
      (1 / 604800 : ℝ) * s ^ 7 + (1 / 967680 : ℝ) * s ^ 8
  let c13 : ℝ :=
    (1 / 4838400 : ℝ) * s ^ 5 + (1 / 3628800 : ℝ) * s ^ 6 + (1 / 3628800 : ℝ) * s ^ 7 +
      (1 / 4838400 : ℝ) * s ^ 8
  let c14 : ℝ :=
    (1 / 29030400 : ℝ) * s ^ 6 + (1 / 25401600 : ℝ) * s ^ 7 + (1 / 29030400 : ℝ) * s ^ 8
  let c15 : ℝ := (1 / 203212800 : ℝ) * s ^ 7 + (1 / 203212800 : ℝ) * s ^ 8
  let c16 : ℝ := (1 / 1625702400 : ℝ) * s ^ 8
  have hexp : (taylor8OfMat Y * taylor8OfMat (s • Y) - taylor8OfMat ((s + 1) • Y)) *ᵥ v =
        c9 • y 9 + c10 • y 10 + c11 • y 11 + c12 • y 12 +
          c13 • y 13 + c14 • y 14 + c15 • y 15 + c16 • y 16 := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    have hinner : taylor8OfMat (s • Y) *ᵥ v =
          y 0 + s • y 1 + ((1 / 2 : ℝ) * s ^ 2) • y 2 + ((1 / 6 : ℝ) * s ^ 3) • y 3 +
            ((1 / 24 : ℝ) * s ^ 4) • y 4 + ((1 / 120 : ℝ) * s ^ 5) • y 5 +
            ((1 / 720 : ℝ) * s ^ 6) • y 6 + ((1 / 5040 : ℝ) * s ^ 7) • y 7 +
            ((1 / 40320 : ℝ) * s ^ 8) • y 8 := by
      unfold taylor8OfMat
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hy_smul, smul_smul]
      ext idx
      simp only [y, pow_zero, pow_one, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hsucc : taylor8OfMat ((s + 1) • Y) *ᵥ v =
          y 0 + (s + 1) • y 1 + ((1 / 2 : ℝ) * (s + 1) ^ 2) • y 2 +
            ((1 / 6 : ℝ) * (s + 1) ^ 3) • y 3 + ((1 / 24 : ℝ) * (s + 1) ^ 4) • y 4 +
            ((1 / 120 : ℝ) * (s + 1) ^ 5) • y 5 + ((1 / 720 : ℝ) * (s + 1) ^ 6) • y 6 +
            ((1 / 5040 : ℝ) * (s + 1) ^ 7) • y 7 + ((1 / 40320 : ℝ) * (s + 1) ^ 8) • y 8 := by
      unfold taylor8OfMat
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hy_smul, smul_smul]
      ext idx
      simp only [y, pow_zero, pow_one, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hinner, hsucc]
    have hY1 (u : Fin d → ℝ) : Y *ᵥ u = (Y ^ 1) *ᵥ u := by rw [pow_one]
    unfold taylor8OfMat
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hY1,
      Matrix.mulVec_add, hy_mul, hy_mul1]
    ext idx
    simp only [c9, c10, c11, c12, c13, c14, c15, c16,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    ring
  have hc9 : 0 ≤ c9 := by dsimp [c9]; positivity
  have hc10 : 0 ≤ c10 := by dsimp [c10]; positivity
  have hc11 : 0 ≤ c11 := by dsimp [c11]; positivity
  have hc12 : 0 ≤ c12 := by dsimp [c12]; positivity
  have hc13 : 0 ≤ c13 := by dsimp [c13]; positivity
  have hc14 : 0 ≤ c14 := by dsimp [c14]; positivity
  have hc15 : 0 ≤ c15 := by dsimp [c15]; positivity
  have hc16 : 0 ≤ c16 := by dsimp [c16]; positivity
  have hy_le (m : ℕ) : vecNorm (y m) ≤ x ^ m * vecNorm v := vecNorm_pow_mulVec_le hx0 hY m v
  have hpow_le (k : ℕ) : x ^ (9 + k) ≤ (1 / 2 : ℝ) ^ k * x ^ 9 := by
    rw [pow_add, mul_comm (x ^ 9)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx_half k) (pow_nonneg hx0 9)
  have h10 := mul_le_mul_of_nonneg_left (hpow_le 1) hc10
  have h11 := mul_le_mul_of_nonneg_left (hpow_le 2) hc11
  have h12 := mul_le_mul_of_nonneg_left (hpow_le 3) hc12
  have h13 := mul_le_mul_of_nonneg_left (hpow_le 4) hc13
  have h14 := mul_le_mul_of_nonneg_left (hpow_le 5) hc14
  have h15 := mul_le_mul_of_nonneg_left (hpow_le 6) hc15
  have h16 := mul_le_mul_of_nonneg_left (hpow_le 7) hc16
  have hsum_coeff : c9 * x ^ 9 + c10 * x ^ 10 + c11 * x ^ 11 + c12 * x ^ 12 +
        c13 * x ^ 13 + c14 * x ^ 14 + c15 * x ^ 15 + c16 * x ^ 16 ≤
        (((s + 1) * x) ^ 9 - (s * x) ^ 9) / 180000 := by
    have hgap : 0 ≤ (((s + 1) * x) ^ 9 - (s * x) ^ 9) / 180000 -
          (c9 * x ^ 9 + c10 * ((1 / 2 : ℝ) ^ 1 * x ^ 9) +
            c11 * ((1 / 2 : ℝ) ^ 2 * x ^ 9) + c12 * ((1 / 2 : ℝ) ^ 3 * x ^ 9) +
            c13 * ((1 / 2 : ℝ) ^ 4 * x ^ 9) + c14 * ((1 / 2 : ℝ) ^ 5 * x ^ 9) +
            c15 * ((1 / 2 : ℝ) ^ 6 * x ^ 9) + c16 * ((1 / 2 : ℝ) ^ 7 * x ^ 9)) := by
      have hid : (((s + 1) * x) ^ 9 - (s * x) ^ 9) / 180000 -
            (c9 * x ^ 9 + c10 * ((1 / 2 : ℝ) ^ 1 * x ^ 9) +
              c11 * ((1 / 2 : ℝ) ^ 2 * x ^ 9) + c12 * ((1 / 2 : ℝ) ^ 3 * x ^ 9) +
              c13 * ((1 / 2 : ℝ) ^ 4 * x ^ 9) + c14 * ((1 / 2 : ℝ) ^ 5 * x ^ 9) +
              c15 * ((1 / 2 : ℝ) ^ 6 * x ^ 9) + c16 * ((1 / 2 : ℝ) ^ 7 * x ^ 9)) =
          x ^ 9 * ((1 / 180000 : ℝ) + ((9 / 180000 - 1 / 40320 : ℝ) * s +
             (36 / 180000 - (1 / 10080 + 1 / 161280) : ℝ) * s ^ 2 +
             (84 / 180000 - (1 / 4320 + 1 / 60480 + 1 / 967680) : ℝ) * s ^ 3 +
             (126 / 180000 - (1 / 2880 + 1 / 34560 + 1 / 483840 + 1 / 7741440) : ℝ) * s ^ 4 +
             (126 / 180000 - (1 / 2880 + 1 / 28800 + 1 / 345600 + 1 / 4838400 +
               1 / 77414400) : ℝ) * s ^ 5 +
             (84 / 180000 - (1 / 4320 + 1 / 34560 + 1 / 345600 + 1 / 4147200 +
               1 / 58060800 + 1 / 928972800) : ℝ) * s ^ 6 +
             (36 / 180000 - (1 / 10080 + 1 / 60480 + 1 / 483840 + 1 / 4838400 +
               1 / 58060800 + 1 / 812851200 + 1 / 13005619200) : ℝ) * s ^ 7 +
             (9 / 180000 - (1 / 40320 + 1 / 161280 + 1 / 967680 + 1 / 7741440 +
               1 / 77414400 + 1 / 928972800 + 1 / 13005619200 +
               1 / 208089907200) : ℝ) * s ^ 8)) := by
        dsimp only [c9, c10, c11, c12, c13, c14, c15, c16]; ring
      rw [hid]; positivity
    linarith
  rw [hexp]
  have htri : vecNorm (c9 • y 9 + c10 • y 10 + c11 • y 11 + c12 • y 12 +
          c13 • y 13 + c14 • y 14 + c15 • y 15 + c16 • y 16) ≤
        c9 * vecNorm (y 9) + c10 * vecNorm (y 10) + c11 * vecNorm (y 11) +
          c12 * vecNorm (y 12) + c13 * vecNorm (y 13) + c14 * vecNorm (y 14) +
          c15 * vecNorm (y 15) + c16 * vecNorm (y 16) := by
    have hsm (c : ℝ) (hc : 0 ≤ c) (u : Fin d → ℝ) : vecNorm (c • u) = c * vecNorm u := by
      rw [vecNorm_smul, abs_of_nonneg hc]
    have h8 := vecNorm_add8_le (c9 • y 9) (c10 • y 10) (c11 • y 11) (c12 • y 12)
      (c13 • y 13) (c14 • y 14) (c15 • y 15) (c16 • y 16)
    rw [hsm c9 hc9, hsm c10 hc10, hsm c11 hc11, hsm c12 hc12,
      hsm c13 hc13, hsm c14 hc14, hsm c15 hc15, hsm c16 hc16] at h8
    exact h8
  calc vecNorm (c9 • y 9 + c10 • y 10 + c11 • y 11 + c12 • y 12 +
          c13 • y 13 + c14 • y 14 + c15 • y 15 + c16 • y 16)
      ≤ c9 * vecNorm (y 9) + c10 * vecNorm (y 10) + c11 * vecNorm (y 11) +
          c12 * vecNorm (y 12) + c13 * vecNorm (y 13) + c14 * vecNorm (y 14) +
          c15 * vecNorm (y 15) + c16 * vecNorm (y 16) := htri
    _ ≤ c9 * (x ^ 9 * vecNorm v) + c10 * (x ^ 10 * vecNorm v) +
          c11 * (x ^ 11 * vecNorm v) + c12 * (x ^ 12 * vecNorm v) +
          c13 * (x ^ 13 * vecNorm v) + c14 * (x ^ 14 * vecNorm v) +
          c15 * (x ^ 15 * vecNorm v) + c16 * (x ^ 16 * vecNorm v) := by
        gcongr
        · exact hy_le 9
        · exact hy_le 10
        · exact hy_le 11
        · exact hy_le 12
        · exact hy_le 13
        · exact hy_le 14
        · exact hy_le 15
        · exact hy_le 16
    _ = (c9 * x ^ 9 + c10 * x ^ 10 + c11 * x ^ 11 + c12 * x ^ 12 +
          c13 * x ^ 13 + c14 * x ^ 14 + c15 * x ^ 15 + c16 * x ^ 16) * vecNorm v := by ring
    _ ≤ (((s + 1) * x) ^ 9 - (s * x) ^ 9) / 180000 * vecNorm v :=
        mul_le_mul_of_nonneg_right hsum_coeff (vecNorm_nonneg v)
theorem vecNorm_taylor8Mat_substep_le {d : ℕ} {η B : ℝ} {G : Matrix (Fin d) (Fin d) ℝ}
    (hG : Gᵀ = -G) (hη : 0 ≤ η) (hB0 : 0 ≤ B)
    (hGB : ∀ u, vecNorm (G *ᵥ u) ≤ B * vecNorm u) :
    ∀ (q : ℕ), (q : ℝ) * η * B ≤ 1 / 2 → ∀ (v : Fin d → ℝ),
      vecNorm (((taylor8Mat η G) ^ q - taylor8Mat ((q : ℝ) * η) G) *ᵥ v) ≤
        ((q : ℝ) * η * B) ^ 9 / 180000 * vecNorm v
  | 0, _, v => by
    simp [taylor8Mat, taylor8OfMat_zero, vecNorm_zero]
  | q + 1, hq, v => by
    have hq_prev : (q : ℝ) * η * B ≤ 1 / 2 := by
      have h1 : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ q
      have h2 : (q : ℝ) * (η * B) ≤ ((q + 1 : ℕ) : ℝ) * (η * B) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hη hB0)
      linarith
    have hηB_le1 : η * B ≤ 1 := by
      have h1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos q
      have h2 : 1 * (η * B) ≤ ((q + 1 : ℕ) : ℝ) * (η * B) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hη hB0)
      linarith
    have hT_contr (w : Fin d → ℝ) : vecNorm (taylor8Mat η G *ᵥ w) ≤ vecNorm w :=
      vecNorm_taylor8Mat_mulVec_le hG hη hB0 hGB hηB_le1 w
    have hY_norm (u : Fin d → ℝ) : vecNorm ((η • G) *ᵥ u) ≤ (η * B) * vecNorm u := by
      rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg hη]
      calc η * vecNorm (G *ᵥ u)
          ≤ η * (B * vecNorm u) := mul_le_mul_of_nonneg_left (hGB u) hη
        _ = (η * B) * vecNorm u := by ring
    have hstep_split : ((taylor8Mat η G) ^ (q + 1) - taylor8Mat (((q + 1 : ℕ) : ℝ) * η) G) *ᵥ v =
          taylor8Mat η G *ᵥ (((taylor8Mat η G) ^ q - taylor8Mat ((q : ℝ) * η) G) *ᵥ v) +
          (taylor8OfMat (η • G) * taylor8OfMat ((q : ℝ) • (η • G)) -
            taylor8OfMat (((q : ℝ) + 1) • (η • G))) *ᵥ v := by
      have hsm1 : ((q : ℝ) * η) • G = (q : ℝ) • (η • G) := (smul_smul (q : ℝ) η G).symm
      have hsm2 : (((q + 1 : ℕ) : ℝ) * η) • G = ((q : ℝ) + 1) • (η • G) := by
        push_cast; exact (smul_smul ((q : ℝ) + 1) η G).symm
      dsimp only [taylor8Mat]
      rw [pow_succ', hsm1, hsm2, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
        Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      ext idx
      simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hsecond :=
      vecNorm_taylor8_mul_sub_succ_le (mul_nonneg hη hB0) hY_norm (q : ℝ) (Nat.cast_nonneg q)
        (by push_cast at hq; linarith) v
    have hih := vecNorm_taylor8Mat_substep_le hG hη hB0 hGB q hq_prev v; rw [hstep_split]
    calc vecNorm (taylor8Mat η G *ᵥ (((taylor8Mat η G) ^ q - taylor8Mat ((q : ℝ) * η) G) *ᵥ v) +
            (taylor8OfMat (η • G) * taylor8OfMat ((q : ℝ) • (η • G)) -
              taylor8OfMat (((q : ℝ) + 1) • (η • G))) *ᵥ v)
        ≤ vecNorm (taylor8Mat η G *ᵥ (((taylor8Mat η G) ^ q - taylor8Mat ((q : ℝ) * η) G) *ᵥ v)) +
            vecNorm ((taylor8OfMat (η • G) * taylor8OfMat ((q : ℝ) • (η • G)) -
              taylor8OfMat (((q : ℝ) + 1) • (η • G))) *ᵥ v) := vecNorm_add_le _ _
      _ ≤ ((q : ℝ) * η * B) ^ 9 / 180000 * vecNorm v +
            ((((q : ℝ) + 1) * (η * B)) ^ 9 - ((q : ℝ) * (η * B)) ^ 9) / 180000 * vecNorm v :=
          add_le_add ((hT_contr _).trans hih) hsecond
      _ = (((q + 1 : ℕ) : ℝ) * η * B) ^ 9 / 180000 * vecNorm v := by push_cast; ring

end

/-
# Binomial & Fiber-Sum Bounds for `D_{\text{alt}}` (`FindAllJohnsonAltBinom`)

Establishes the pure-`ℕ` binomial ratio sandwiches, initial-state overlap bound
`vecNorm_u0OrbVecGen_sub_e0_le`, leading diagonal/subdiagonal binomial limits, and far
off-diagonal (`a ≥ b + 2`) entrywise decay bounds used by `FindAllJohnsonAltLim`:

1. **Pure-`ℕ` Binomial Ratio Sandwich (`choose_div_choose_add_le`)**:
   Bounds `A.choose q / B.choose (p + q) ≤ 2 ^ (2 m) * (m / M) ^ p` without real logs or
   Stirling approximations.
2. **Initial State Overlap (`vecNorm_u0OrbVecGen_sub_e0_le`)**:
   Proves `vecNorm (u0OrbVecGen (2 ^ n) m r - e0) ≤ 1 / (2 * wdScale)` for `n ≥ altN0`.
3. **Fiber-Sum & Far Off-Diagonal Decay (`stepOrbMat_sub_linear_entry_le_far`)**:
   Proves `O(1 / M)` decay for `i < b` summands and `a ≥ b + 2` entries of `dAltStepOrbMat`.
-/
@[expose] public section
open Real
open scoped Matrix
/-- Explicit asymptotic threshold `n₀ = 80000` (`600 ≤ altN0`) for general `m ≤ 8192`,
  `r ≤ 1024` `D_{\text{alt}}` orbit convergence within `10 ^ (-15)`. -/
def altN0 : ℕ := 80000
end
public section
open Real
open scoped Matrix
/- ## Section 1: Elementary Combinatorial & Real Sandwich Helpers -/
lemma two_pow_add_self (k : ℕ) : (2 : ℝ) ^ k + (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
  rw [pow_succ, mul_two]
lemma two_pow_le {a b : ℕ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  pow_le_pow_right₀ (by norm_num) h
lemma choose_le_two_pow : ∀ (n k : ℕ), (n.choose k : ℝ) ≤ (2 : ℝ) ^ n
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, 0 => by
    simp only [Nat.choose_zero_right, Nat.cast_one]
    exact one_le_pow₀ (by norm_num)
  | n + 1, k + 1 => by
    have h1 := choose_le_two_pow n k
    have h2 := choose_le_two_pow n (k + 1)
    rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
    linarith
private lemma factorial_mul_choose_le_pow : ∀ (q L : ℕ), q.factorial * L.choose q ≤ L ^ q
  | 0, _ => by simp
  | _ + 1, 0 => by simp
  | q + 1, L + 1 => by
    have h1 := p01_choose_mul_succ L q; have ih := factorial_mul_choose_le_pow q L
    have hpow : L ^ q ≤ (L + 1) ^ q := Nat.pow_le_pow_left (Nat.le_succ L) q
    calc (q + 1).factorial * (L + 1).choose (q + 1)
        = q.factorial * ((q + 1) * (L + 1).choose (q + 1)) := by rw [Nat.factorial_succ]; ring
      _ = (L + 1) * (q.factorial * L.choose q) := by rw [← h1]; ring
      _ ≤ (L + 1) * L ^ q := Nat.mul_le_mul_left _ ih
      _ ≤ (L + 1) * (L + 1) ^ q := Nat.mul_le_mul_left _ hpow
      _ = (L + 1) ^ (q + 1) := by rw [pow_succ']
private lemma sub_pow_le_factorial_mul_choose :
    ∀ (q L : ℕ), q ≤ L → (L - q) ^ q ≤ q.factorial * L.choose q
  | 0, _, _ => by simp
  | q + 1, L, hq => by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have h1 := p01_choose_mul_succ L' q
    have ih := sub_pow_le_factorial_mul_choose q L' (by omega)
    have hsub : L' + 1 - (q + 1) = L' - q := by omega
    rw [hsub, pow_succ']
    calc (L' - q) * (L' - q) ^ q
        ≤ (L' + 1) * (q.factorial * L'.choose q) := Nat.mul_le_mul (by omega) ih
      _ = q.factorial * ((L' + 1) * L'.choose q) := by ring
      _ = q.factorial * ((q + 1) * (L' + 1).choose (q + 1)) := by rw [h1]
      _ = (q + 1).factorial * (L' + 1).choose (q + 1) := by rw [Nat.factorial_succ]; ring
private lemma factorial_add_le_mul_pow :
    ∀ (p q m : ℕ), p + q ≤ m → (p + q).factorial ≤ q.factorial * m ^ p
  | 0, _, _, _ => by simp
  | p + 1, q, m, hpq => by
    have ih := factorial_add_le_mul_pow p q m (by omega)
    rw [show p + 1 + q = (p + q) + 1 by omega, Nat.factorial_succ, pow_succ']
    calc (p + q + 1) * (p + q).factorial
        ≤ m * (q.factorial * m ^ p) := Nat.mul_le_mul (by omega) ih
      _ = q.factorial * (m * m ^ p) := by ring
private lemma one_sub_mul_le_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ q : ℕ, 1 - (q : ℝ) * x ≤ (1 - x) ^ q
  | 0 => by simp
  | q + 1 => by
    have ih := one_sub_mul_le_pow hx0 hx1 q
    have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 - x)
    rw [← pow_succ] at hmul
    have hqx : 0 ≤ (q : ℝ) * x ^ 2 := by positivity
    push_cast; nlinarith
lemma pow_anti_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ (a k : ℕ), x ^ (a + k) ≤ x ^ a
  | _, 0 => by simp
  | a, k + 1 => by
    rw [← add_assoc, pow_succ]
    calc x ^ (a + k) * x
        ≤ x ^ (a + k) * 1 := mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0 _)
      _ = x ^ (a + k) := mul_one _
      _ ≤ x ^ a := pow_anti_of_le_one hx0 hx1 a k
private lemma choose_mul_pow_le_choose_add {A B M p q m : ℕ} (hpq : p + q ≤ m) (hA : A ≤ 2 * M) (hB
    : p + q ≤ B) (hBM : M ≤ 2 * (B - (p + q))) (hM : 0 < M) : A.choose q * M ^ p ≤ B.choose (p +
    q) * (2 ^ (2 * m) * m ^ p) := by
  have hnum2 : q.factorial * A.choose q ≤ (2 * M) ^ q :=
    (factorial_mul_choose_le_pow q A).trans (Nat.pow_le_pow_left hA q)
  have hnum : (p + q).factorial * A.choose q ≤ 2 ^ q * m ^ p * M ^ q := by
    calc (p + q).factorial * A.choose q ≤ (q.factorial * m ^ p) * A.choose q := Nat.mul_le_mul_right
          _ (factorial_add_le_mul_pow p q m hpq)
      _ = m ^ p * (q.factorial * A.choose q) := by ring
      _ ≤ m ^ p * (2 * M) ^ q := Nat.mul_le_mul_left _ hnum2
      _ = 2 ^ q * m ^ p * M ^ q := by rw [mul_pow]; ring
  have hden : M ^ (p + q) ≤ 2 ^ (p + q) * ((p + q).factorial * B.choose (p + q)) := by
    calc M ^ (p + q) ≤ (2 * (B - (p + q))) ^ (p + q) := Nat.pow_le_pow_left hBM (p + q)
      _ = 2 ^ (p + q) * (B - (p + q)) ^ (p + q) := by rw [mul_pow]
      _ ≤ 2 ^ (p + q) * ((p + q).factorial * B.choose (p + q)) :=
          Nat.mul_le_mul_left _ (sub_pow_le_factorial_mul_choose (p + q) B hB)
  have h2pow : 2 ^ (p + 2 * q) ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by omega) (by omega)
  have hprod := Nat.mul_le_mul hnum hden
  have hlhs : ((p + q).factorial * A.choose q) * M ^ (p + q) =
      (A.choose q * M ^ p) * ((p + q).factorial * M ^ q) := by
    rw [pow_add M p q]; ring
  have hrhs : (2 ^ q * m ^ p * M ^ q) * (2 ^ (p + q) * ((p + q).factorial * B.choose (p + q))) =
    (B.choose (p + q) * (2 ^ (p + 2 * q) * m ^ p)) * ((p + q).factorial * M ^ q) := by
    have h2 : 2 ^ q * 2 ^ (p + q) = 2 ^ (p + 2 * q) := by
      rw [← pow_add, show q + (p + q) = p + 2 * q by omega]
    calc (2 ^ q * m ^ p * M ^ q) * (2 ^ (p + q) * ((p + q).factorial * B.choose (p + q)))
        = (B.choose (p + q) * ((2 ^ q * 2 ^ (p + q)) * m ^ p)) * ((p + q).factorial * M ^ q) := by
            ring
      _ = (B.choose (p + q) * (2 ^ (p + 2 * q) * m ^ p)) * ((p + q).factorial * M ^ q) := by rw [h2]
  rw [hlhs, hrhs] at hprod
  have hcancel := Nat.le_of_mul_le_mul_right hprod (Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos
    hM)); exact hcancel.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2pow))
private lemma choose_div_choose_add_le {A B M p q m : ℕ} (hpq : p + q ≤ m) (hA : A ≤ 2 * M) (hB :
    p + q ≤ B) (hBM : M ≤ 2 * (B - (p + q))) (hM : 0 < M) : (A.choose q : ℝ) / (B.choose (p + q) :
    ℝ) ≤ (2 : ℝ) ^ (2 * m) * ((m : ℝ) / (M : ℝ)) ^ p := by
  have hBpos : (0 : ℝ) < (B.choose (p + q) : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hB)
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hnat : ((A.choose q * M ^ p : ℕ) : ℝ) ≤
      ((B.choose (p + q) * (2 ^ (2 * m) * m ^ p) : ℕ) : ℝ) := by
    exact_mod_cast choose_mul_pow_le_choose_add hpq hA hB hBM hM
  push_cast at hnat; rw [div_le_iff₀ hBpos, div_pow]
  have hMp_pos : (0 : ℝ) < (M : ℝ) ^ p := pow_pos hMpos p; rw [← le_div_iff₀ hMp_pos] at hnat
  refine hnat.trans (le_of_eq ?_)
  field_simp [hMp_pos.ne']
/- ## Section 2: Initial State Overlap Bound (`vecNorm (u0 - e0)`) -/
/-- Initial orbit overlap `‖u_0 - e_0‖_2 ≤ 1 / (2 * 10 ^ 15)` for `n ≥ altN0`. -/
theorem vecNorm_u0OrbVecGen_sub_e0_le {n m r : ℕ}
    (hn : altN0 ≤ n) (hm1 : 1 ≤ m) (hm : m ≤ 8192) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    let e0 : Fin (orbDim m r) → ℝ := Pi.single ⟨0, by unfold orbDim; omega⟩ 1
    vecNorm (u0OrbVecGen (2 ^ n) m r - e0) ≤ 1 / (2 * (wdScale : ℝ)) := by
  intro e0; set N : ℕ := 2 ^ n; set M : ℕ := 2 ^ (n - 1); have hn_alt : 80000 ≤ n := hn
  have hN_eq : N = 2 * M := by
    dsimp only [N, M]
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
  have hM_ge30 : 2 ^ 30 ≤ M := Nat.pow_le_pow_right (by omega) (by omega : 30 ≤ n - 1)
  have hM_ge200 : (2 : ℝ) ^ 200 ≤ (M : ℝ) := by
    have h : 2 ^ 200 ≤ M := Nat.pow_le_pow_right (by omega) (by omega : 200 ≤ n - 1)
    exact_mod_cast h
  have hM_pos : (0 : ℝ) < (M : ℝ) := (by positivity)
  have hN_pos : (0 : ℝ) < (N : ℝ) := (by rw [hN_eq]; push_cast; positivity)
  have hmrN : m + r ≤ N := (by have : 9216 < 2 ^ 30 := (by norm_num); omega)
  set u0 := u0OrbVecGen N m r; let z0 : Fin (orbDim m r) := ⟨0, by unfold orbDim; omega⟩
  obtain ⟨R, hRcard⟩ : ∃ R : Finset (Fin N), R.card = r := ⟨(Finset.range r).attach.map ⟨fun i ↦
    ⟨i.1, (Finset.mem_range.mp i.2).trans_le (by omega : r ≤ N)⟩, fun _ _ h ↦ Subtype.ext
    (Fin.ext_iff.mp h)⟩, by simp⟩; have hmrR : m + R.card ≤ N := (by rw [hRcard]; exact hmrN)
  have hu0_sq : vecSqNorm u0 = 1 := by
    have hdot := dot_orbEmbedGen hmrR (u0OrbVecGen N m R.card) (u0OrbVecGen N m R.card)
    rw [orbEmbedGen_u0OrbVecGen hmrR] at hdot; rw [hRcard] at hdot; unfold vecSqNorm
    have hlhs : (∑ i : Fin (orbDim m r), (u0 i) ^ 2) = ∑ i : Fin (orbDim m r), u0 i * u0 i :=
      Finset.sum_congr rfl fun _ _ ↦ sq _; rw [hlhs, ← hdot]
    have hch_pos : (0 : ℝ) < (N.choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hterm : ∀ E : P01Subset N m, u0Vec N m E * u0Vec N m E = 1 / (N.choose m : ℝ) := by
      intro E; unfold u0Vec; rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hch_pos.le]
    simp only [hterm, Finset.sum_const, Finset.card_univ, card_symSubset, nsmul_eq_mul]
    exact mul_one_div_cancel hch_pos.ne'
  have he0_def : e0 = Pi.single z0 1 := rfl
  have he0_sq : vecSqNorm e0 = 1 := by
    unfold vecSqNorm; rw [Finset.sum_eq_single z0]
    · rw [he0_def, Pi.single_eq_same, one_pow]
    · intro b _ hb; rw [he0_def, Pi.single_eq_of_ne hb, zero_pow two_ne_zero]
    · intro hz; exact absurd (Finset.mem_univ z0) hz
  have hdiff_sq : vecSqNorm (u0 - e0) = 2 * (1 - u0 z0) := by
    have hexp : vecSqNorm (u0 - e0) =
        vecSqNorm u0 - 2 * (∑ i : Fin (orbDim m r), u0 i * e0 i) + vecSqNorm e0 := by
      unfold vecSqNorm; have ht : ∀ i : Fin (orbDim m r), (u0 i - e0 i) ^ 2 =
          (u0 i) ^ 2 - 2 * (u0 i * e0 i) + (e0 i) ^ 2 := fun _ ↦ by ring
      simp only [Pi.sub_apply, ht, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hcross : (∑ i : Fin (orbDim m r), u0 i * e0 i) = u0 z0 := by
      rw [Finset.sum_eq_single z0]
      · rw [he0_def, Pi.single_eq_same, mul_one]
      · intro b _ hb; rw [he0_def, Pi.single_eq_of_ne hb, mul_zero]
      · intro hz; exact absurd (Finset.mem_univ z0) hz
    rw [hexp, hcross, hu0_sq, he0_sq]; ring
  have hu0_z0_le1 : u0 z0 ≤ 1 := by
    have h1 : (u0 z0) ^ 2 ≤ vecSqNorm u0 := Finset.single_le_sum (fun i _ ↦ sq_nonneg (u0 i))
      (Finset.mem_univ z0); rw [hu0_sq] at h1; nlinarith [show 0 ≤ u0 z0 from Real.sqrt_nonneg _]
  have hu0_z0_nn : 0 ≤ u0 z0 := Real.sqrt_nonneg _
  have hu0_sq_le : (u0 z0) ^ 2 ≤ u0 z0 := (by nlinarith)
  have hu0_z0_sq_eq : (u0 z0) ^ 2 = ((N - r).choose m : ℝ) / (N.choose m : ℝ) := by
    dsimp only [u0, u0OrbVecGen, z0]
    have hpos : 0 ≤ ((orbCard N m r 0 : ℝ) / (N.choose m : ℝ)) := (by positivity)
    rw [Real.sq_sqrt hpos]; unfold orbCard; simp
  have hratio_lb :
      1 - (m : ℝ) * ((r + m : ℕ) : ℝ) / (N : ℝ) ≤ ((N - r).choose m : ℝ) / (N.choose m : ℝ) := by
    rw [mul_div_assoc]
    have hch_pos : (0 : ℝ) < ((m.factorial * N.choose m : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.choose_pos (by omega)))
    have hden_le : ((m.factorial * N.choose m : ℕ) : ℝ) ≤ (N : ℝ) ^ m := by
      exact_mod_cast factorial_mul_choose_le_pow m N
    have hnum_ge : ((N - r - m : ℕ) : ℝ) ^ m ≤ ((m.factorial * (N - r).choose m : ℕ) : ℝ) := by
      exact_mod_cast sub_pow_le_factorial_mul_choose m (N - r) (by omega)
    set x : ℝ := ((r + m : ℕ) : ℝ) / (N : ℝ); have hx0 : 0 ≤ x := (by positivity)
    have hx1 : x ≤ 1 := by
      dsimp only [x]; rw [div_le_one hN_pos]; exact_mod_cast (by omega : r + m ≤ N)
    have h1x : 1 - x = ((N - r - m : ℕ) : ℝ) / (N : ℝ) := by
      dsimp only [x]; have hsub : N - r - m = N - (r + m) := (by omega)
      rw [hsub, Nat.cast_sub (by omega : r + m ≤ N)]; field_simp [hN_pos.ne']
    have hbern := one_sub_mul_le_pow hx0 hx1 m; rw [h1x, div_pow] at hbern
    have hNpow_pos : (0 : ℝ) < (N : ℝ) ^ m := pow_pos hN_pos m
    by_cases hpos_lhs : 0 ≤ 1 - (m : ℝ) * x
    · have hstep1 : (1 - (m : ℝ) * x) * ((m.factorial * N.choose m : ℕ) : ℝ) ≤ (1 - (m : ℝ) * x) *
        (N : ℝ) ^ m := mul_le_mul_of_nonneg_left hden_le hpos_lhs
      have hstep2 : (1 - (m : ℝ) * x) * (N : ℝ) ^ m ≤ ((N - r - m : ℕ) : ℝ) ^ m := by
        rwa [le_div_iff₀ hNpow_pos] at hbern
      have hcomb := (hstep1.trans hstep2).trans hnum_ge
      have hdiv := (le_div_iff₀ hch_pos).mpr hcomb; refine hdiv.trans (le_of_eq ?_)
      have hm_ne : (m.factorial : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.factorial_pos m)).ne'; push_cast
      field_simp [hm_ne]
    · refine le_trans ?_ (by positivity)
      linarith
  have hsq_bound : vecSqNorm (u0 - e0) ≤ (1 / (2 * (wdScale : ℝ))) ^ 2 := by
    have h1 : vecSqNorm (u0 - e0) ≤ 2 * ((m : ℝ) * ((r + m : ℕ) : ℝ) / (N : ℝ)) := by
      rw [hdiff_sq]; linarith [hu0_sq_le, hu0_z0_sq_eq, hratio_lb]
    have hmr_le : (m : ℝ) * ((r + m : ℕ) : ℝ) ≤ (2 : ℝ) ^ 27 := by
      have hnat : m * (r + m) ≤ 2 ^ 27 :=
        (Nat.mul_le_mul hm (by omega : r + m ≤ 9216)).trans (by norm_num)
      exact_mod_cast hnat
    have h2 : 2 * ((m : ℝ) * ((r + m : ℕ) : ℝ) / (N : ℝ)) ≤ (2 : ℝ) ^ 27 / (M : ℝ) := by
      have hNR : (N : ℝ) = 2 * (M : ℝ) := (by rw [hN_eq]; push_cast; rfl); rw [hNR]
      have hdiv : 2 * ((m : ℝ) * ((r + m : ℕ) : ℝ) / (2 * (M : ℝ))) =
          (m : ℝ) * ((r + m : ℕ) : ℝ) / (M : ℝ) := by field_simp [hM_pos.ne']
      rw [hdiv]; exact div_le_div_of_nonneg_right hmr_le hM_pos.le
    have hwd : (wdScale : ℝ) ≤ (2 : ℝ) ^ 50 := (by unfold wdScale; norm_num)
    have hwd_pos : (0 : ℝ) < 2 * (wdScale : ℝ) := (by unfold wdScale; positivity)
    have h3 : (2 : ℝ) ^ 27 / (M : ℝ) ≤ (1 / (2 * (wdScale : ℝ))) ^ 2 := by
      rw [one_div_pow, div_le_div_iff₀ hM_pos (pow_pos hwd_pos 2)]
      have h2w : (2 * (wdScale : ℝ)) ^ 2 ≤ (2 : ℝ) ^ 102 := by
        calc (2 * (wdScale : ℝ)) ^ 2
            ≤ (2 * (2 : ℝ) ^ 50) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
          _ = (2 : ℝ) ^ 102 := by norm_num
      calc (2 : ℝ) ^ 27 * (2 * (wdScale : ℝ)) ^ 2
          ≤ (2 : ℝ) ^ 27 * (2 : ℝ) ^ 102 := mul_le_mul_of_nonneg_left h2w (by positivity)
        _ = (2 : ℝ) ^ 129 := by rw [← pow_add]
        _ ≤ (2 : ℝ) ^ 200 := two_pow_le (by omega)
        _ ≤ 1 * (M : ℝ) := by linarith [hM_ge200]
    exact (h1.trans h2).trans h3
  rw [vecNorm, Real.sqrt_le_iff]; exact ⟨by unfold wdScale; positivity, hsq_bound⟩
/- ## Section 3: Leading Binomial Limit & Entrywise Perturbation Bound -/
lemma leading_choose_ratio_approx {M m C q : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 8192) (hq : q ≤ m) (hC : C ≤ 9216) (hM : 2 ^ 30 ≤ M) :
    |(((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ)) /
        ((M : ℝ) * ((M - 1).choose q : ℝ)) - (2 : ℝ) ^ q| ≤
      (2 : ℝ) ^ (2 * m + 28) / (M : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hch_pos : (0 : ℝ) < ((M - 1).choose q : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  set Y : ℝ := (M : ℝ) * ((M - 1).choose q : ℝ); have hY_pos : 0 < Y := mul_pos hM_pos hch_pos
  set qf : ℝ := (q.factorial : ℝ); have hqf_pos : 0 < qf := Nat.cast_pos.mpr (Nat.factorial_pos q)
  have hqfY_pos : 0 < qf * Y := mul_pos hqf_pos hY_pos
  set val : ℝ := (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ)) / Y; rw [abs_sub_le_iff]
  constructor
  · -- Upper bound: val - 2^q ≤ 2^(2*m + 28) / M
    have hnum_le : qf * (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ)) ≤
        (2 : ℝ) ^ q * (M : ℝ) ^ (q + 1) := by
      have hnat : q.factorial * ((M - m) * (2 * M - C).choose q) ≤ 2 ^ q * M ^ (q + 1) := by
        have h1 : q.factorial * (2 * M - C).choose q ≤ (2 * M) ^ q :=
          (factorial_mul_choose_le_pow q (2 * M - C)).trans (Nat.pow_le_pow_left (by omega) q)
        calc q.factorial * ((M - m) * (2 * M - C).choose q)
            = (M - m) * (q.factorial * (2 * M - C).choose q) := by ring
          _ ≤ M * (2 * M) ^ q := Nat.mul_le_mul (by omega) h1
          _ = 2 ^ q * M ^ (q + 1) := by rw [mul_pow, pow_succ']; ring
      have hcast : ((q.factorial * ((M - m) * (2 * M - C).choose q) : ℕ) : ℝ) ≤
          ((2 ^ q * M ^ (q + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      dsimp only [qf]; push_cast at hcast; linarith
    have hMq_le : (M : ℝ) ^ q ≤ (2 : ℝ) ^ q * (qf * Y / (M : ℝ)) := by
      have hnat : M ^ q ≤ 2 ^ q * (q.factorial * (M - 1).choose q) := by
        calc M ^ q ≤ (2 * (M - 1 - q)) ^ q := Nat.pow_le_pow_left (by omega) q
          _ = 2 ^ q * (M - 1 - q) ^ q := by rw [mul_pow]
          _ ≤ 2 ^ q * (q.factorial * (M - 1).choose q) :=
              Nat.mul_le_mul_left _ (sub_pow_le_factorial_mul_choose q (M - 1) (by omega))
      have hcast : ((M ^ q : ℕ) : ℝ) ≤
          ((2 ^ q * (q.factorial * (M - 1).choose q) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast; refine hcast.trans (le_of_eq ?_)
      dsimp only [qf, Y]; field_simp [hM_pos.ne']
    have hMq1_le : (M : ℝ) ^ (q + 1) ≤ qf * Y + (q : ℝ) * ((q + 1 : ℕ) : ℝ) * (M : ℝ) ^ q := by
      set u : ℝ := ((q + 1 : ℕ) : ℝ) / (M : ℝ); have hu0 : 0 ≤ u := (by positivity)
      have hu1 : u ≤ 1 := by
        dsimp only [u]; rw [div_le_one hM_pos]; exact_mod_cast (by omega : q + 1 ≤ M)
      have h1u : 1 - u = ((M - 1 - q : ℕ) : ℝ) / (M : ℝ) := by
        dsimp only [u]; have hsub : M - 1 - q = M - (q + 1) := (by omega)
        rw [hsub, Nat.cast_sub (by omega : q + 1 ≤ M)]; field_simp [hM_pos.ne']
      have hbern := one_sub_mul_le_pow hu0 hu1 q; rw [h1u, div_pow] at hbern
      have hMp_pos : (0 : ℝ) < (M : ℝ) ^ q := pow_pos hM_pos q
      have hmul := (le_div_iff₀ hMp_pos).mp hbern
      have hsub_le : ((M - 1 - q : ℕ) : ℝ) ^ q ≤ ((q.factorial * (M - 1).choose q : ℕ) : ℝ) := by
        exact_mod_cast sub_pow_le_factorial_mul_choose q (M - 1) (by omega)
      have hcomb := hmul.trans hsub_le; have hmulM := mul_le_mul_of_nonneg_left hcomb hM_pos.le
      dsimp only [u, qf, Y] at hmulM ⊢; push_cast at hmulM
      have hlhs : (M : ℝ) * ((1 - (q : ℝ) * (((q : ℝ) + 1) / (M : ℝ))) * (M : ℝ) ^ q) =
          (M : ℝ) ^ (q + 1) - (q : ℝ) * ((q : ℝ) + 1) * (M : ℝ) ^ q := by
        rw [pow_succ']; field_simp [hM_pos.ne']
      rw [hlhs] at hmulM; push_cast; linarith
    have hcoeff : (2 : ℝ) ^ (2 * q) * ((q : ℝ) * ((q + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (2 * m + 28) := by
      have h2q : (2 : ℝ) ^ (2 * q) ≤ (2 : ℝ) ^ (2 * m) := two_pow_le (by omega)
      have hqq : (q : ℝ) * ((q + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 28 := by
        have hnat : q * (q + 1) ≤ 2 ^ 28 :=
          (Nat.mul_le_mul (by omega : q ≤ 8192) (by omega : q + 1 ≤ 8193)).trans (by norm_num)
        exact_mod_cast hnat
      calc (2 : ℝ) ^ (2 * q) * ((q : ℝ) * ((q + 1 : ℕ) : ℝ))
          ≤ (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ 28 := mul_le_mul h2q hqq (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (2 * m + 28) := by rw [← pow_add]
    have htot : qf * (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ)) ≤
        ((2 : ℝ) ^ q + (2 : ℝ) ^ (2 * m + 28) / (M : ℝ)) * (qf * Y) := by
      calc qf * (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ))
          ≤ (2 : ℝ) ^ q * (M : ℝ) ^ (q + 1) := hnum_le
        _ ≤ (2 : ℝ) ^ q * (qf * Y + (q : ℝ) * ((q + 1 : ℕ) : ℝ) * (M : ℝ) ^ q) :=
            mul_le_mul_of_nonneg_left hMq1_le (by positivity)
        _ ≤ (2 : ℝ) ^ q * (qf * Y +
              (q : ℝ) * ((q + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ q * (qf * Y / (M : ℝ)))) := by
            gcongr
        _ = (2 : ℝ) ^ q * (qf * Y) +
              ((2 : ℝ) ^ (2 * q) * ((q : ℝ) * ((q + 1 : ℕ) : ℝ))) * (qf * Y / (M : ℝ)) := by
            rw [show 2 * q = q + q by omega, pow_add]; ring
        _ ≤ (2 : ℝ) ^ q * (qf * Y) + (2 : ℝ) ^ (2 * m + 28) * (qf * Y / (M : ℝ)) := by gcongr
        _ = ((2 : ℝ) ^ q + (2 : ℝ) ^ (2 * m + 28) / (M : ℝ)) * (qf * Y) := by ring
    have hdiv : val ≤ (2 : ℝ) ^ q + (2 : ℝ) ^ (2 * m + 28) / (M : ℝ) := by
      dsimp only [val]
      rw [show (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ)) / Y =
          (qf * (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ))) / (qf * Y) by
        field_simp [hqf_pos.ne']]
      exact (div_le_iff₀ hqfY_pos).mpr htot
    linarith
  · -- Lower bound: 2^q - val ≤ 2^(2*m + 28) / M
    have hqfY_le : qf * Y ≤ (M : ℝ) ^ (q + 1) := by
      have hnat : q.factorial * (M * (M - 1).choose q) ≤ M ^ (q + 1) := by
        calc q.factorial * (M * (M - 1).choose q)
            = M * (q.factorial * (M - 1).choose q) := by ring
          _ ≤ M * (M - 1) ^ q := Nat.mul_le_mul_left M (factorial_mul_choose_le_pow q (M - 1))
          _ ≤ M * M ^ q := Nat.mul_le_mul_left M (Nat.pow_le_pow_left (by omega) q)
          _ = M ^ (q + 1) := by rw [pow_succ']
      have hcast : ((q.factorial * (M * (M - 1).choose q) : ℕ) : ℝ) ≤
          ((M ^ (q + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      dsimp only [qf, Y]; push_cast at hcast; linarith
    set v : ℝ := ((C + q : ℕ) : ℝ) / (M : ℝ); have hv0 : 0 ≤ v := (by positivity)
    have hv1 : v ≤ 1 := by
      dsimp only [v]; rw [div_le_one hM_pos]; exact_mod_cast (by omega : C + q ≤ M)
    have h2sub : 2 * (M : ℝ) * (1 - v) ≤ ((2 * M - C - q : ℕ) : ℝ) := by
      have hnat : 2 * (M - (C + q)) ≤ 2 * M - C - q := (by omega)
      have hcast : ((2 * (M - (C + q)) : ℕ) : ℝ) ≤ ((2 * M - C - q : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hlhs : 2 * (M : ℝ) * (1 - v) = ((2 * (M - (C + q)) : ℕ) : ℝ) := by
        dsimp only [v]; rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : C + q ≤ M)]
        field_simp [hM_pos.ne']
      linarith
    have hpow_lb : (2 : ℝ) ^ q * (M : ℝ) ^ q * (1 - (q : ℝ) * v) ≤ ((q.factorial * (2 * M -
      C).choose q : ℕ) : ℝ) := by
      have hbern := one_sub_mul_le_pow hv0 hv1 q
      have h1 : (2 : ℝ) ^ q * (M : ℝ) ^ q * (1 - (q : ℝ) * v) ≤ (2 * (M : ℝ) * (1 - v)) ^ q := by
        rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_left hbern (by positivity)
      have h2 : (2 * (M : ℝ) * (1 - v)) ^ q ≤ ((2 * M - C - q : ℕ) : ℝ) ^ q :=
        pow_le_pow_left₀ (mul_nonneg (by positivity) (sub_nonneg.mpr hv1)) h2sub q
      have h3 : ((2 * M - C - q : ℕ) : ℝ) ^ q ≤ ((q.factorial * (2 * M - C).choose q : ℕ) : ℝ) := by
        exact_mod_cast sub_pow_le_factorial_mul_choose q (2 * M - C) (by omega)
      exact (h1.trans h2).trans h3
    have hMm_eq : ((M - m : ℕ) : ℝ) = (M : ℝ) * (1 - (m : ℝ) / (M : ℝ)) := by
      rw [Nat.cast_sub (by omega : m ≤ M)]; field_simp [hM_pos.ne']
    have hprod_lb : 1 - (2 : ℝ) ^ 28 / (M : ℝ) ≤ (1 - (m : ℝ) / (M : ℝ)) * (1 - (q : ℝ) * v) := by
      have hsum : (m : ℝ) + (q : ℝ) * ((C + q : ℕ) : ℝ) ≤ (2 : ℝ) ^ 28 := by
        have hnat : m + q * (C + q) ≤ 2 ^ 28 := by
          have hmul : q * (C + q) ≤ 8192 * 17408 := Nat.mul_le_mul (by omega) (by omega); omega
        exact_mod_cast hnat
      have hexp : (1 - (m : ℝ) / (M : ℝ)) * (1 - (q : ℝ) * v) = 1 - ((m : ℝ) + (q : ℝ) * ((C + q :
        ℕ) : ℝ)) / (M : ℝ) + ((m : ℝ) / (M : ℝ)) * ((q : ℝ) * v) := by
        dsimp only [v]; field_simp [hM_pos.ne']; ring
      have hnn : 0 ≤ ((m : ℝ) / (M : ℝ)) * ((q : ℝ) * v) := (by positivity)
      have hdiv : ((m : ℝ) + (q : ℝ) * ((C + q : ℕ) : ℝ)) / (M : ℝ) ≤ (2 : ℝ) ^ 28 / (M : ℝ) :=
        div_le_div_of_nonneg_right hsum hM_pos.le; linarith
    have h1_28_nn : 0 ≤ 1 - (2 : ℝ) ^ 28 / (M : ℝ) := by
      rw [sub_nonneg, div_le_one hM_pos]; have hnat : 2 ^ 28 ≤ M := (by omega); exact_mod_cast hnat
    have hnum_ge : ((2 : ℝ) ^ q - (2 : ℝ) ^ (2 * m + 28) / (M : ℝ)) * (qf * Y) ≤ qf * (((M - m : ℕ)
      : ℝ) * ((2 * M - C).choose q : ℝ)) := by
      have hstep1 : (2 : ℝ) ^ q * (qf * Y) * (1 - (2 : ℝ) ^ 28 / (M : ℝ)) ≤ (2 : ℝ) ^ q * (M : ℝ) ^
        (q + 1) * (1 - (2 : ℝ) ^ 28 / (M : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hqfY_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ q)
        exact mul_le_mul_of_nonneg_right h h1_28_nn
      have hstep2 : (2 : ℝ) ^ q * (M : ℝ) ^ (q + 1) * (1 - (2 : ℝ) ^ 28 / (M : ℝ)) ≤ ((M - m : ℕ) :
        ℝ) * ((2 : ℝ) ^ q * (M : ℝ) ^ q * (1 - (q : ℝ) * v)) := by
        rw [hMm_eq]
        calc (2 : ℝ) ^ q * (M : ℝ) ^ (q + 1) * (1 - (2 : ℝ) ^ 28 / (M : ℝ)) ≤ (2 : ℝ) ^ q * (M : ℝ)
              ^ (q + 1) * ((1 - (m : ℝ) / (M : ℝ)) * (1 - (q : ℝ) * v)) := mul_le_mul_of_nonneg_left
              hprod_lb (by positivity)
          _ = (M : ℝ) * (1 - (m : ℝ) / (M : ℝ)) *
                ((2 : ℝ) ^ q * (M : ℝ) ^ q * (1 - (q : ℝ) * v)) := by
              rw [pow_succ']; ring
      have hstep3 : ((M - m : ℕ) : ℝ) * ((2 : ℝ) ^ q * (M : ℝ) ^ q * (1 - (q : ℝ) * v)) ≤ qf *
        (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hpow_lb (Nat.cast_nonneg (M - m)); dsimp only [qf]
        push_cast at h; linarith
      have h2q_le : (2 : ℝ) ^ q * (2 : ℝ) ^ 28 ≤ (2 : ℝ) ^ (2 * m + 28) := by
        rw [← pow_add]; exact two_pow_le (by omega)
      have hstep0 : ((2 : ℝ) ^ q - (2 : ℝ) ^ (2 * m + 28) / (M : ℝ)) * (qf * Y) ≤ (2 : ℝ) ^ q *
        (qf * Y) * (1 - (2 : ℝ) ^ 28 / (M : ℝ)) := by
        have hexp : (2 : ℝ) ^ q * (qf * Y) * (1 - (2 : ℝ) ^ 28 / (M : ℝ)) - ((2 : ℝ) ^ q - (2 : ℝ) ^
          (2 * m + 28) / (M : ℝ)) * (qf * Y) = ((2 : ℝ) ^ (2 * m + 28) - (2 : ℝ) ^ q * (2 : ℝ) ^
          28) * (qf * Y / (M : ℝ)) := by
          ring
        have hnn : 0 ≤ ((2 : ℝ) ^ (2 * m + 28) - (2 : ℝ) ^ q * (2 : ℝ) ^ 28) * (qf * Y / (M : ℝ)) :=
          mul_nonneg (by linarith) (by positivity); linarith
      exact ((hstep0.trans hstep1).trans hstep2).trans hstep3
    have hdiv : (2 : ℝ) ^ q - (2 : ℝ) ^ (2 * m + 28) / (M : ℝ) ≤ val := by
      dsimp only [val]
      rw [show (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ)) / Y =
          (qf * (((M - m : ℕ) : ℝ) * ((2 * M - C).choose q : ℝ))) / (qf * Y) by
        field_simp [hqf_pos.ne']]
      exact (le_div_iff₀ hqfY_pos).mpr hnum_ge
    linarith
lemma orbCard_succ_rel {N m r b : ℕ} (hb : b < min m r) (hmrN : m + r ≤ N) : orbCard N m r (b + 1) *
    ((b + 1) * (N - r - m + b + 1)) = orbCard N m r b * ((r - b) * (m - b)) := by
  have hbm : b < m := lt_of_lt_of_le hb (Nat.min_le_left m r)
  have hbr : b < r := lt_of_lt_of_le hb (Nat.min_le_right m r); unfold orbCard
  have h1 := Nat.choose_succ_right_eq r b; have h2 := Nat.choose_succ_right_eq (N - r) (m - b - 1)
  have hm_sub : m - b - 1 + 1 = m - b := (by omega)
  have hN_sub : N - r - (m - b - 1) = N - r - m + b + 1 := (by omega)
  have hm_b1 : m - (b + 1) = m - b - 1 := (by omega); rw [hm_sub, hN_sub] at h2; rw [hm_b1]
  calc (r.choose (b + 1) * (N - r).choose (m - b - 1)) * ((b + 1) * (N - r - m + b + 1))
      = (r.choose (b + 1) * (b + 1)) *
          ((N - r).choose (m - b - 1) * (N - r - m + b + 1)) := by ring
    _ = (r.choose b * (r - b)) * ((N - r).choose (m - b) * (m - b)) := by rw [h1, ← h2]
    _ = (r.choose b * (N - r).choose (m - b)) * ((r - b) * (m - b)) := by ring
lemma two_mul_succ_sqrt_orbCard_ratio {N m r b : ℕ} (hb : b < min m r) (hmrN : m + r ≤ N) : (2 *
    (b + 1 : ℝ)) * √((orbCard N m r (b + 1) : ℝ) / (orbCard N m r b : ℝ)) = dAltCoupling m r b /
    √((N - r - m + b + 1 : ℕ) : ℝ) := by
  have hb_pos : (0 : ℝ) < (orbCard N m r b : ℝ) := Nat.cast_pos.mpr (orbCard_pos_gen hmrN hb.le)
  have hden_pos : (0 : ℝ) < ((N - r - m + b + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hrel : (orbCard N m r (b + 1) : ℝ) * (((b + 1) * (N - r - m + b + 1) : ℕ) : ℝ) =
      (orbCard N m r b : ℝ) * (((r - b) * (m - b) : ℕ) : ℝ) := by
    exact_mod_cast orbCard_succ_rel hb hmrN
  have hsq_eq : ((2 * (b + 1 : ℝ)) * √((orbCard N m r (b + 1) : ℝ) / (orbCard N m r b : ℝ))) ^ 2 =
    (dAltCoupling m r b / √((N - r - m + b + 1 : ℕ) : ℝ)) ^ 2 := by
    unfold dAltCoupling
    rw [mul_pow, Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt hden_pos.le]
    push_cast at hrel ⊢; field_simp [hb_pos.ne', hden_pos.ne', (by positivity : (b : ℝ) + 1 ≠ 0)]
    linarith
  have hlhs_nn : 0 ≤ (2 * (b + 1 : ℝ)) *
      √((orbCard N m r (b + 1) : ℝ) / (orbCard N m r b : ℝ)) := by positivity
  have hrhs_nn : 0 ≤ dAltCoupling m r b / √((N - r - m + b + 1 : ℕ) : ℝ) := by
    unfold dAltCoupling; positivity
  nlinarith [sq_nonneg ((2 * (b + 1 : ℝ)) * √((orbCard N m r (b + 1) : ℝ) / (orbCard N m r b : ℝ)) -
    dAltCoupling m r b / √((N - r - m + b + 1 : ℕ) : ℝ))]
lemma inv_sqrt_sub_inv_sqrt_le {A B M : ℝ}
    (hM1 : 1 ≤ M) (hMA : M ≤ A) (hAB : A ≤ B) :
    |1 / √A - 1 / √B| ≤ (B - A) / M := by
  have hA_pos : 0 < A := (by linarith); have hB_pos : 0 < B := (by linarith)
  have hsA_ge : √M ≤ √A := Real.sqrt_le_sqrt hMA
  have hsB_ge : √M ≤ √B := Real.sqrt_le_sqrt (hMA.trans hAB)
  have hsM_ge1 : 1 ≤ √M := (by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hM1)
  have hprod_ge : M ≤ √A * √B := by
    calc M = √M * √M := (Real.mul_self_sqrt (by linarith)).symm
      _ ≤ √A * √B := mul_le_mul hsA_ge hsB_ge (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum_ge1 : 1 ≤ √A + √B := (by linarith [hsA_ge, hsB_ge, hsM_ge1])
  have hden_ge : M ≤ √A * √B * (√A + √B) := (by nlinarith)
  have hdiff_nn : 0 ≤ 1 / √A - 1 / √B := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hA_pos) (Real.sqrt_le_sqrt hAB)
  rw [abs_of_nonneg hdiff_nn]; have hsA_ne : √A ≠ 0 := (Real.sqrt_pos.mpr hA_pos).ne'
  have hsB_ne : √B ≠ 0 := (Real.sqrt_pos.mpr hB_pos).ne'
  have hid : (1 / √A - 1 / √B) * (√A * √B * (√A + √B)) = B - A := by
    have h1 : (1 / √A - 1 / √B) * (√A * √B) = √B - √A := (by field_simp [hsA_ne, hsB_ne])
    calc (1 / √A - 1 / √B) * (√A * √B * (√A + √B))
        = ((1 / √A - 1 / √B) * (√A * √B)) * (√A + √B) := by ring
      _ = (√B - √A) * (√A + √B) := by rw [h1]
      _ = (√B) ^ 2 - (√A) ^ 2 := by ring
      _ = B - A := by rw [Real.sq_sqrt hB_pos.le, Real.sq_sqrt hA_pos.le]
  have hden_pos : 0 < √A * √B * (√A + √B) := (by linarith)
  rw [show 1 / √A - 1 / √B = (B - A) / (√A * √B * (√A + √B)) by
    rw [eq_div_iff hden_pos.ne']; exact hid]
  exact div_le_div_of_nonneg_left (by linarith) (by linarith) hden_ge
lemma dAltOrbRawSum_restrict_j {N m r a b : ℕ} (hba : b ≤ a) (ham : a ≤ m) : dAltOrbRawSum N m r a b
    = ∑ i ∈ Finset.range (b + 1), (a.choose i * (r - a).choose (b - i) : ℝ) * ∑ j ∈ Finset.range
    (m - a + 1), ((m - a).choose j * (N - r - (m - a)).choose (m - b - j) : ℝ) * dAltEntry (N / 2) m
    (i + j) := by
  unfold dAltOrbRawSum; refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1; symm; refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj_not ↦ ?_
  have hgt : m - a < j := (by simp only [Finset.mem_range, not_lt] at hj_not; omega)
  rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero, zero_mul, zero_mul]
lemma inner_j_sum_bound_of_pos_p {M m r a b i : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 8192) (hr : r ≤ 1024) (ham : a ≤ m) (har : a ≤ r)
    (hba : b ≤ a) (hib : i < b) (hM : 2 ^ 30 ≤ M) :
    |∑ j ∈ Finset.range (m - a + 1),
        ((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) *
          dAltEntry M m (i + j)| ≤
      (2 : ℝ) ^ (3 * m + 27) / (M : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm : ∀ j ∈ Finset.range (m - a + 1),
      |((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) * dAltEntry M m (i + j)| ≤
        (2 : ℝ) ^ (3 * m + 13) / (M : ℝ) := by
    intro j hj; have hja : j ≤ m - a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    set p : ℕ := b - i; set q : ℕ := m - b - j; have hp1 : 1 ≤ p := (by omega)
    have hpq_eq : m - (i + j) = p + q := (by omega); have hpq_m : p + q ≤ m := (by omega)
    have hd_abs : |dAltEntry M m (i + j)| ≤ 1 / ((M - 1).choose (p + q) : ℝ) := by
      unfold dAltEntry; simp only [show m ≠ 0 by omega, ↓reduceIte, hpq_eq]
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (Nat.cast_nonneg _), abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg _)]
      have hch_pos : (0 : ℝ) < ((M - 1).choose (p + q) : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos (by omega))
      have hle : ((M - m : ℕ) : ℝ) ≤ (M : ℝ) := (by exact_mod_cast Nat.sub_le M m)
      calc ((M - m : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose (p + q) : ℝ)) ≤ (M : ℝ) / ((M : ℝ) * ((M -
            1).choose (p + q) : ℝ)) := div_le_div_of_nonneg_right hle (by positivity)
        _ = 1 / ((M - 1).choose (p + q) : ℝ) := by field_simp [hM_pos.ne']
    have hch_ratio : ((2 * M - r - (m - a)).choose q : ℝ) / ((M - 1).choose (p + q) : ℝ) ≤ (2 : ℝ) ^
      (2 * m) * ((m : ℝ) / (M : ℝ)) := by
      have hbase := choose_div_choose_add_le hpq_m
        (by omega : 2 * M - r - (m - a) ≤ 2 * M)
        (by omega : p + q ≤ M - 1)
        (by omega : M ≤ 2 * (M - 1 - (p + q)))
        (by omega : 0 < M)
      have hx0 : 0 ≤ (m : ℝ) / (M : ℝ) := (by positivity)
      have hx1 : (m : ℝ) / (M : ℝ) ≤ 1 :=
        (div_le_one hM_pos).mpr (by exact_mod_cast (by omega : m ≤ M))
      have hp_anti : ((m : ℝ) / (M : ℝ)) ^ p ≤ ((m : ℝ) / (M : ℝ)) ^ 1 := by
        rw [show p = 1 + (p - 1) by omega]; exact pow_anti_of_le_one hx0 hx1 1 (p - 1)
      rw [pow_one] at hp_anti; exact hbase.trans (mul_le_mul_of_nonneg_left hp_anti (by positivity))
    have hmaj : ((m - a).choose j : ℝ) ≤ (2 : ℝ) ^ m :=
      (choose_le_two_pow (m - a) j).trans (two_pow_le (by omega))
    have hm13 : (m : ℝ) ≤ (2 : ℝ) ^ 13 := by
      have hnat : m ≤ 2 ^ 13 := (by omega); exact_mod_cast hnat
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    calc ((m - a).choose j : ℝ) * ((2 * M - r - (m - a)).choose q : ℝ) * |dAltEntry M m (i + j)|
        ≤ ((m - a).choose j : ℝ) * ((2 * M - r - (m - a)).choose q : ℝ) *
            (1 / ((M - 1).choose (p + q) : ℝ)) :=
          mul_le_mul_of_nonneg_left hd_abs (by positivity)
      _ = ((m - a).choose j : ℝ) *
            (((2 * M - r - (m - a)).choose q : ℝ) / ((M - 1).choose (p + q) : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ (2 * m) * ((m : ℝ) / (M : ℝ))) :=
          mul_le_mul hmaj hch_ratio (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (3 * m) * (m : ℝ) / (M : ℝ) := by
          rw [show 3 * m = m + 2 * m by omega, pow_add]; ring
      _ ≤ (2 : ℝ) ^ (3 * m) * (2 : ℝ) ^ 13 / (M : ℝ) := by gcongr
      _ = (2 : ℝ) ^ (3 * m + 13) / (M : ℝ) := by rw [← pow_add]
  calc |∑ j ∈ Finset.range (m - a + 1),
          ((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) * dAltEntry M m (i + j)|
      ≤ ∑ j ∈ Finset.range (m - a + 1),
          |((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) *
            dAltEntry M m (i + j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (m - a + 1), (2 : ℝ) ^ (3 * m + 13) / (M : ℝ) := Finset.sum_le_sum hterm
    _ = ((m - a + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (3 * m + 13) / (M : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ 14 * ((2 : ℝ) ^ (3 * m + 13) / (M : ℝ)) := by
        have hlen : ((m - a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 14 := by
          have hnat : m - a + 1 ≤ 2 ^ 14 := (by omega); exact_mod_cast hnat
        exact mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = (2 : ℝ) ^ (3 * m + 27) / (M : ℝ) := by
        rw [show 3 * m + 27 = 14 + (3 * m + 13) by omega, pow_add]; ring
lemma inner_j_sum_bound_any_p {M m r a b i : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 8192) (hr : r ≤ 1024) (ham : a ≤ m) (har : a ≤ r)
    (hba : b ≤ a) (hib : i ≤ b) (hM : 2 ^ 30 ≤ M) :
    |∑ j ∈ Finset.range (m - a + 1),
        ((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) *
          dAltEntry M m (i + j)| ≤
      (2 : ℝ) ^ (3 * m + 14) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm : ∀ j ∈ Finset.range (m - a + 1),
      |((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) *
          dAltEntry M m (i + j)| ≤ (2 : ℝ) ^ (3 * m) := by
    intro j hj; have hja : j ≤ m - a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    set p : ℕ := b - i; set q : ℕ := m - b - j; have hpq_eq : m - (i + j) = p + q := (by omega)
    have hpq_m : p + q ≤ m := (by omega)
    have hd_abs : |dAltEntry M m (i + j)| ≤ 1 / ((M - 1).choose (p + q) : ℝ) := by
      unfold dAltEntry; simp only [show m ≠ 0 by omega, ↓reduceIte, hpq_eq]
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (Nat.cast_nonneg _), abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg _)]
      have hle : ((M - m : ℕ) : ℝ) ≤ (M : ℝ) := (by exact_mod_cast Nat.sub_le M m)
      calc ((M - m : ℕ) : ℝ) / ((M : ℝ) * ((M - 1).choose (p + q) : ℝ)) ≤ (M : ℝ) / ((M : ℝ) * ((M -
            1).choose (p + q) : ℝ)) := div_le_div_of_nonneg_right hle (by positivity)
        _ = 1 / ((M - 1).choose (p + q) : ℝ) := by field_simp [hM_pos.ne']
    have hch_ratio : ((2 * M - r - (m - a)).choose q : ℝ) / ((M - 1).choose (p + q) : ℝ) ≤ (2 : ℝ) ^
      (2 * m) := by
      have hbase := choose_div_choose_add_le hpq_m
        (by omega : 2 * M - r - (m - a) ≤ 2 * M)
        (by omega : p + q ≤ M - 1)
        (by omega : M ≤ 2 * (M - 1 - (p + q)))
        (by omega : 0 < M)
      have hx0 : 0 ≤ (m : ℝ) / (M : ℝ) := (by positivity)
      have hx1 : (m : ℝ) / (M : ℝ) ≤ 1 :=
        (div_le_one hM_pos).mpr (by exact_mod_cast (by omega : m ≤ M))
      have hp_le1 : ((m : ℝ) / (M : ℝ)) ^ p ≤ 1 := (by simpa using pow_anti_of_le_one hx0 hx1 0 p)
      exact hbase.trans (by nlinarith [ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * m)) ])
    have hmaj : ((m - a).choose j : ℝ) ≤ (2 : ℝ) ^ m :=
      (choose_le_two_pow (m - a) j).trans (two_pow_le (by omega))
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    calc ((m - a).choose j : ℝ) * ((2 * M - r - (m - a)).choose q : ℝ) * |dAltEntry M m (i + j)|
        ≤ ((m - a).choose j : ℝ) * ((2 * M - r - (m - a)).choose q : ℝ) *
            (1 / ((M - 1).choose (p + q) : ℝ)) :=
          mul_le_mul_of_nonneg_left hd_abs (by positivity)
      _ = ((m - a).choose j : ℝ) *
            (((2 * M - r - (m - a)).choose q : ℝ) / ((M - 1).choose (p + q) : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ m * (2 : ℝ) ^ (2 * m) :=
          mul_le_mul hmaj hch_ratio (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (3 * m) := by rw [← pow_add, show m + 2 * m = 3 * m by omega]
  calc |∑ j ∈ Finset.range (m - a + 1),
          ((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) * dAltEntry M m (i + j)|
      ≤ ∑ j ∈ Finset.range (m - a + 1),
          |((m - a).choose j * (2 * M - r - (m - a)).choose (m - b - j) : ℝ) *
            dAltEntry M m (i + j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (m - a + 1), (2 : ℝ) ^ (3 * m) := Finset.sum_le_sum hterm
    _ = ((m - a + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (3 * m) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ 14 * (2 : ℝ) ^ (3 * m) := by
        have hlen : ((m - a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 14 := by
          have hnat : m - a + 1 ≤ 2 ^ 14 := (by omega); exact_mod_cast hnat
        exact mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = (2 : ℝ) ^ (3 * m + 14) := by rw [← pow_add, show 14 + 3 * m = 3 * m + 14 by omega]
lemma binom_two_sub_one (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * (-1 : ℝ) ^ j * (2 : ℝ) ^ (k - j)) = 1 := by
  have h := add_pow (-1 : ℝ) 2 k; have h1 : (-1 : ℝ) + 2 = 1 := (by norm_num); rw [h1, one_pow] at h
  refine (Finset.sum_congr rfl fun _ _ ↦ ?_).trans h.symm
  ring
lemma stepOrbMat_sub_linear_entry_le_far {M m r : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 8192) (hr : r ≤ 1024) (hM : 2 ^ 30 ≤ M)
    (a b : Fin (orbDim m r)) (hd2 : b.1 + 2 ≤ a.1) :
    |(dAltStepOrbMat (2 * M) m r -
        (1 + (1 / √((2 * M : ℕ) : ℝ)) • dAltGenMat m r)) a b| ≤
      (2 : ℝ) ^ 36000 / (M : ℝ) := by
  have hba : b.1 ≤ a.1 := (by omega); have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have ha_le : a.1 ≤ min m r := Nat.lt_succ_iff.mp a.2
  have hb_le : b.1 ≤ min m r := Nat.lt_succ_iff.mp b.2
  have ham : a.1 ≤ m := ha_le.trans (Nat.min_le_left m r)
  have har : a.1 ≤ r := ha_le.trans (Nat.min_le_right m r)
  have hbm : b.1 ≤ m := hb_le.trans (Nat.min_le_left m r)
  have hmrN : m + r ≤ 2 * M := (by have : 9216 < 2 ^ 30 := (by norm_num); omega)
  have hstep_apply : dAltStepOrbMat (2 * M) m r a b = √((orbCard (2 * M) m r a.1 : ℝ) / (orbCard
    (2 * M) m r b.1 : ℝ)) * dAltOrbRawSum (2 * M) m r a.1 b.1 * (-1 : ℝ) ^ b.1 := by
    unfold dAltStepOrbMat zOrbMat dAltOrbMat; rw [Matrix.mul_diagonal]; simp only [Matrix.of_apply]
  have hdiv2 : (2 * M) / 2 = M := (by omega)
  -- Far off-diagonal a ≥ b + 2: both 1 and dAltGenMat vanish
  have hneq : a ≠ b := fun h ↦ by have := congrArg Fin.val h; omega
  have hne1 : a.1 ≠ b.1 + 1 := (by omega); have hne2 : b.1 ≠ a.1 + 1 := (by omega)
  have hlin0 : ((1 + (1 / √((2 * M : ℕ) : ℝ)) • dAltGenMat m r) :
      Matrix (Fin (orbDim m r)) (Fin (orbDim m r)) ℝ) a b = 0 := by
    simp only [Matrix.add_apply, Matrix.one_apply_ne hneq, zero_add, Matrix.smul_apply,
      smul_eq_mul, dAltGenMat, tridiagSkewMat, Matrix.of_apply, eq_false hne1, eq_false hne2,
      ↓reduceIte, mul_zero]
  rw [Matrix.sub_apply, hlin0, sub_zero, hstep_apply, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, mul_one, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  -- Bound √(orbCard a / orbCard b)
  set d : ℕ := a.1 - b.1; have hd_ge2 : 2 ≤ d := (by omega)
  have horb_ratio : (orbCard (2 * M) m r a.1 : ℝ) / (orbCard (2 * M) m r b.1 : ℝ) ≤ (2 : ℝ) ^ (2 *
    r + 2 * m) * ((m : ℝ) / (M : ℝ)) ^ 2 := by
    unfold orbCard
    have hra : (r.choose a.1 : ℝ) / (r.choose b.1 : ℝ) ≤ (2 : ℝ) ^ (2 * r) := by
      have h1 : (r.choose a.1 : ℝ) ≤ (2 : ℝ) ^ r := choose_le_two_pow r a.1
      have h2 : (1 : ℝ) ≤ (r.choose b.1 : ℝ) := Nat.one_le_cast.mpr (Nat.choose_pos (by omega))
      have h3 : (r.choose a.1 : ℝ) / (r.choose b.1 : ℝ) ≤ (r.choose a.1 : ℝ) / 1 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) zero_lt_one h2
      rw [div_one] at h3; exact (h3.trans h1).trans (two_pow_le (by omega))
    have hmb_eq : m - b.1 = d + (m - a.1) := (by omega); have hch := choose_div_choose_add_le
      (by omega : d + (m - a.1) ≤ m)
      (by omega : 2 * M - r ≤ 2 * M)
      (by omega : d + (m - a.1) ≤ 2 * M - r)
      (by omega : M ≤ 2 * (2 * M - r - (d + (m - a.1))))
      (by omega : 0 < M)
    rw [← hmb_eq] at hch; have hx0 : 0 ≤ (m : ℝ) / (M : ℝ) := (by positivity)
    have hx1 : (m : ℝ) / (M : ℝ) ≤ 1 :=
      (div_le_one hM_pos).mpr (by exact_mod_cast (by omega : m ≤ M))
    have hd_anti : ((m : ℝ) / (M : ℝ)) ^ d ≤ ((m : ℝ) / (M : ℝ)) ^ 2 := by
      rw [show d = 2 + (d - 2) by omega]; exact pow_anti_of_le_one hx0 hx1 2 (d - 2)
    have hch2 := hch.trans (mul_le_mul_of_nonneg_left hd_anti (by positivity)); push_cast
    rw [← div_mul_div_comm]
    calc ((r.choose a.1 : ℝ) / (r.choose b.1 : ℝ)) * (((2 * M - r).choose (m - a.1) : ℝ) / ((2 * M -
          r).choose (m - b.1) : ℝ)) ≤ (2 : ℝ) ^ (2 * r) * ((2 : ℝ) ^ (2 * m) * ((m : ℝ) / (M : ℝ)) ^
          2) := mul_le_mul hra hch2 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (2 * r + 2 * m) * ((m : ℝ) / (M : ℝ)) ^ 2 := by rw [← mul_assoc, ← pow_add]
  have hsqrt_orb : √((orbCard (2 * M) m r a.1 : ℝ) / (orbCard (2 * M) m r b.1 : ℝ)) ≤ (2 : ℝ) ^ (r +
    m + 13) / (M : ℝ) := by
    have hm13 : (m : ℝ) ≤ (2 : ℝ) ^ 13 := by
      have hnat : m ≤ 2 ^ 13 := (by omega); exact_mod_cast hnat
    have hsq_rhs : (2 : ℝ) ^ (2 * r + 2 * m) * ((m : ℝ) / (M : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ (r + m + 13) /
      (M : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, ← pow_mul]
      have hm2 : (m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 13) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hm13 2
      rw [← pow_mul] at hm2
      calc (2 : ℝ) ^ (2 * r + 2 * m) * ((m : ℝ) ^ 2 / (M : ℝ) ^ 2)
          ≤ (2 : ℝ) ^ (2 * r + 2 * m) * ((2 : ℝ) ^ (13 * 2) / (M : ℝ) ^ 2) := by gcongr
        _ = (2 : ℝ) ^ ((r + m + 13) * 2) / (M : ℝ) ^ 2 := by
            rw [show (r + m + 13) * 2 = (2 * r + 2 * m) + 13 * 2 by omega, pow_add]; ring
    rw [Real.sqrt_le_iff]; exact ⟨by positivity, horb_ratio.trans hsq_rhs⟩
  -- Bound |dAltOrbRawSum|
  have hraw_le : |dAltOrbRawSum (2 * M) m r a.1 b.1| ≤ (2 : ℝ) ^ (2 * r + 3 * m + 25) := by
    rw [dAltOrbRawSum_restrict_j hba ham, hdiv2]; have hi_term : ∀ i ∈ Finset.range (b.1 + 1),
        |(a.1.choose i * (r - a.1).choose (b.1 - i) : ℝ) * ∑ j ∈ Finset.range (m - a.1 + 1),
              ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - b.1 - j) : ℝ) *
                dAltEntry M m (i + j)| ≤
          (2 : ℝ) ^ (2 * r + 3 * m + 14) := by
      intro i hi; have hib : i ≤ b.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hc1 : (a.1.choose i : ℝ) ≤ (2 : ℝ) ^ r :=
        (choose_le_two_pow a.1 i).trans (two_pow_le har)
      have hc2 : ((r - a.1).choose (b.1 - i) : ℝ) ≤ (2 : ℝ) ^ r :=
        (choose_le_two_pow (r - a.1) (b.1 - i)).trans (two_pow_le (Nat.sub_le r a.1))
      have hj_bd := inner_j_sum_bound_any_p hm1 hm hr ham har hba hib hM
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
      calc (a.1.choose i : ℝ) * ((r - a.1).choose (b.1 - i) : ℝ) *
            |∑ j ∈ Finset.range (m - a.1 + 1),
              ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - b.1 - j) : ℝ) *
                dAltEntry M m (i + j)|
          ≤ ((2 : ℝ) ^ r * (2 : ℝ) ^ r) * (2 : ℝ) ^ (3 * m + 14) :=
            mul_le_mul (mul_le_mul hc1 hc2 (by positivity) (by positivity))
              hj_bd (abs_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (2 * r + 3 * m + 14) := by
            rw [← pow_add, ← pow_add, show r + r + (3 * m + 14) = 2 * r + 3 * m + 14 by omega]
    calc |∑ i ∈ Finset.range (b.1 + 1),
            (a.1.choose i * (r - a.1).choose (b.1 - i) : ℝ) * ∑ j ∈ Finset.range (m - a.1 + 1),
                ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - b.1 - j) : ℝ) *
                  dAltEntry M m (i + j)|
        ≤ ∑ i ∈ Finset.range (b.1 + 1), |(a.1.choose i * (r - a.1).choose (b.1 - i) : ℝ) *
              ∑ j ∈ Finset.range (m - a.1 + 1),
                ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - b.1 - j) : ℝ) *
                  dAltEntry M m (i + j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (b.1 + 1), (2 : ℝ) ^ (2 * r + 3 * m + 14) := Finset.sum_le_sum hi_term
      _ = ((b.1 + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * r + 3 * m + 14) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ 11 * (2 : ℝ) ^ (2 * r + 3 * m + 14) := by
          have hlen : ((b.1 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 11 := by
            have hnat : b.1 + 1 ≤ 2 ^ 11 := (by omega); exact_mod_cast hnat
          exact mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = (2 : ℝ) ^ (2 * r + 3 * m + 25) := by
          rw [← pow_add, show 11 + (2 * r + 3 * m + 14) = 2 * r + 3 * m + 25 by omega]
  calc √((orbCard (2 * M) m r a.1 : ℝ) / (orbCard (2 * M) m r b.1 : ℝ)) *
        |dAltOrbRawSum (2 * M) m r a.1 b.1|
      ≤ ((2 : ℝ) ^ (r + m + 13) / (M : ℝ)) * (2 : ℝ) ^ (2 * r + 3 * m + 25) :=
        mul_le_mul hsqrt_orb hraw_le (abs_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (3 * r + 4 * m + 38) / (M : ℝ) := by
        rw [show 3 * r + 4 * m + 38 = (r + m + 13) + (2 * r + 3 * m + 25) by omega, pow_add]; ring
    _ ≤ (2 : ℝ) ^ 36000 / (M : ℝ) := div_le_div_of_nonneg_right (two_pow_le (by omega)) hM_pos.le
end
end QuantumComputation.Specs.DickeSol
/-
# Continuum Generator Trajectory Limit for `D_{\text{alt}}` (`FindAllJohnsonAltLim`)

Proves the non-asymptotic `K`-step trajectory convergence bounds
`vecNorm_dAltStepOrbMat_pow_sub_taylor8_vec_le` (for arbitrary unit-bounded vectors `u, e`)
and
`vecNorm_dAltStepOrbMat_pow_sub_taylor8_le` (for `u0OrbVecGen` vs `e0`) across all
`n ≥ altN0`, `1 ≤ m ≤ 8192`, `1 ≤ r ≤ 1024`, and `K ≤ 4 * √(2 ^ n)` without spectral calculus,
Hahn eigenvalues, or `Real.exp`.
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
open Real
open scoped Matrix
/- ## Section 1: Diagonal, Subdiagonal & Symmetric Entrywise Generator Convergence -/
private lemma stepOrbMat_sub_linear_entry_le_lower {M m r : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 8192) (hr : r ≤ 1024) (hM : 2 ^ 30 ≤ M)
    (a b : Fin (orbDim m r)) (hba : b.1 ≤ a.1) :
    |(dAltStepOrbMat (2 * M) m r - (1 + (1 / √((2 * M : ℕ) : ℝ)) • dAltGenMat m r)) a b| ≤
      (2 : ℝ) ^ 36000 / (M : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have ha_le : a.1 ≤ min m r := Nat.lt_succ_iff.mp a.2
  have hb_le : b.1 ≤ min m r := Nat.lt_succ_iff.mp b.2
  have ham : a.1 ≤ m := ha_le.trans (Nat.min_le_left m r)
  have har : a.1 ≤ r := ha_le.trans (Nat.min_le_right m r)
  have hbm : b.1 ≤ m := hb_le.trans (Nat.min_le_left m r)
  have hmrN : m + r ≤ 2 * M := (by have : 9216 < 2 ^ 30 := (by norm_num); omega)
  have hstep_apply : dAltStepOrbMat (2 * M) m r a b = √((orbCard (2 * M) m r a.1 : ℝ) / (orbCard
    (2 * M) m r b.1 : ℝ)) * dAltOrbRawSum (2 * M) m r a.1 b.1 * (-1 : ℝ) ^ b.1 := by
    unfold dAltStepOrbMat zOrbMat dAltOrbMat; rw [Matrix.mul_diagonal]; simp only [Matrix.of_apply]
  have hdiv2 : (2 * M) / 2 = M := (by omega); by_cases hd2 : b.1 + 2 ≤ a.1
  · exact stepOrbMat_sub_linear_entry_le_far hm1 hm hr hM a b hd2
  · by_cases hab_eq : a.1 = b.1
    · -- Case 2: Diagonal a = b
      have ha_eq_b : a = b := Fin.ext hab_eq; subst ha_eq_b
      have hlin1 : ((1 + (1 / √((2 * M : ℕ) : ℝ)) • dAltGenMat m r) :
          Matrix (Fin (orbDim m r)) (Fin (orbDim m r)) ℝ) a a = 1 := by
        simp [Matrix.add_apply, dAltGenMat, tridiagSkewMat]
      have horb1 : √((orbCard (2 * M) m r a.1 : ℝ) / (orbCard (2 * M) m r a.1 : ℝ)) = 1 := by
        have hpos : (0 : ℝ) < (orbCard (2 * M) m r a.1 : ℝ) := Nat.cast_pos.mpr (orbCard_pos_gen
          hmrN ha_le); rw [div_self hpos.ne', Real.sqrt_one]
      rw [Matrix.sub_apply, hlin1, hstep_apply, horb1, one_mul]
      rw [dAltOrbRawSum_restrict_j le_rfl ham, hdiv2, Finset.sum_range_succ, add_mul]
      -- Bound i < a tail
      let tailSum : ℝ := (∑ i ∈ Finset.range a.1, (a.1.choose i * (r - a.1).choose (a.1 - i) : ℝ) *
        ∑ j ∈ Finset.range (m - a.1 + 1), ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m -
        a.1 - j) : ℝ) * dAltEntry M m (i + j)) * (-1 : ℝ) ^ a.1
      let mainSum : ℝ := ((a.1.choose a.1 * (r - a.1).choose (a.1 - a.1) : ℝ) * ∑ j ∈ Finset.range
        (m - a.1 + 1), ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - a.1 - j) : ℝ) *
        dAltEntry M m (a.1 + j)) * (-1 : ℝ) ^ a.1
      change |tailSum + mainSum - 1| ≤ (2 : ℝ) ^ 36000 / (M : ℝ)
      have htail_le : |tailSum| ≤ (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) := by
        dsimp only [tailSum]; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
        have hi_bd : ∀ i ∈ Finset.range a.1, |(a.1.choose i * (r - a.1).choose (a.1 - i) : ℝ) *
                ∑ j ∈ Finset.range (m - a.1 + 1),
                  ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - a.1 - j) : ℝ) *
                    dAltEntry M m (i + j)| ≤
              (2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ) := by
          intro i hi; have hia : i < a.1 := Finset.mem_range.mp hi
          have hc1 : (a.1.choose i : ℝ) ≤ (2 : ℝ) ^ r :=
            (choose_le_two_pow a.1 i).trans (two_pow_le har)
          have hc2 : ((r - a.1).choose (a.1 - i) : ℝ) ≤ (2 : ℝ) ^ r :=
            (choose_le_two_pow (r - a.1) (a.1 - i)).trans (two_pow_le (Nat.sub_le r a.1))
          have hj_bd := inner_j_sum_bound_of_pos_p hm1 hm hr ham har le_rfl hia hM
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
            abs_of_nonneg (Nat.cast_nonneg _)]
          calc (a.1.choose i : ℝ) * ((r - a.1).choose (a.1 - i) : ℝ) *
                |∑ j ∈ Finset.range (m - a.1 + 1),
                  ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - a.1 - j) : ℝ) *
                    dAltEntry M m (i + j)|
              ≤ ((2 : ℝ) ^ r * (2 : ℝ) ^ r) * ((2 : ℝ) ^ (3 * m + 27) / (M : ℝ)) :=
                mul_le_mul (mul_le_mul hc1 hc2 (by positivity) (by positivity))
                  hj_bd (abs_nonneg _) (by positivity)
            _ = (2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ) := by
                rw [show 2 * r + 3 * m + 27 = r + r + (3 * m + 27) by omega,
                  pow_add, pow_add]; ring
        calc |∑ i ∈ Finset.range a.1,
                (a.1.choose i * (r - a.1).choose (a.1 - i) : ℝ) * ∑ j ∈ Finset.range (m - a.1 + 1),
                    ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - a.1 - j) : ℝ) *
                      dAltEntry M m (i + j)|
            ≤ ∑ i ∈ Finset.range a.1, |(a.1.choose i * (r - a.1).choose (a.1 - i) : ℝ) *
                  ∑ j ∈ Finset.range (m - a.1 + 1),
                    ((m - a.1).choose j * (2 * M - r - (m - a.1)).choose (m - a.1 - j) : ℝ) *
                      dAltEntry M m (i + j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ Finset.range a.1, (2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ) :=
              Finset.sum_le_sum hi_bd
          _ = (a.1 : ℝ) * ((2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 : ℝ) ^ 11 * ((2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ)) := by
              have hlen : (a.1 : ℝ) ≤ (2 : ℝ) ^ 11 := by
                have hnat : a.1 ≤ 2 ^ 11 := (by omega); exact_mod_cast hnat
              exact mul_le_mul_of_nonneg_right hlen (by positivity)
          _ = (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) := by
              rw [show 2 * r + 3 * m + 38 = 11 + (2 * r + 3 * m + 27) by omega, pow_add]; ring
      -- Bound |mainSum - 1|
      have hmain_le : |mainSum - 1| ≤ (2 : ℝ) ^ (3 * m + 42) / (M : ℝ) := by
        have hmain_eq : mainSum - 1 = ∑ j ∈ Finset.range (m - a.1 + 1), ((m - a.1).choose j : ℝ) *
          (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) * ((2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ))
          / ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ)) - (2 : ℝ) ^ (m - a.1 - j)) := by
          dsimp only [mainSum]
          rw [Nat.choose_self, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
          conv_lhs => rhs; rw [← binom_two_sub_one (m - a.1)]
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j hj ↦ ?_
          have hja : j ≤ m - a.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hm_sub : m - (a.1 + j) = m - a.1 - j := (by omega)
          have h2M_sub : 2 * M - r - (m - a.1) = 2 * M - (r + (m - a.1)) := (by omega)
          unfold dAltEntry; simp only [show m ≠ 0 by omega, ↓reduceIte, hm_sub, h2M_sub]
          have hsign : (-1 : ℝ) ^ (a.1 + j) * (-1 : ℝ) ^ a.1 = (-1 : ℝ) ^ j := by
            rw [pow_add, mul_right_comm, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
              one_mul]
          calc (((m - a.1).choose j * (2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ) *
                  ((-1 : ℝ) ^ (a.1 + j) * ((M - m : ℕ) : ℝ) /
                    ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ)))) *
                (-1 : ℝ) ^ a.1 -
                ((m - a.1).choose j : ℝ) * (-1 : ℝ) ^ j * (2 : ℝ) ^ (m - a.1 - j)
              = ((m - a.1).choose j : ℝ) * ((-1 : ℝ) ^ (a.1 + j) * (-1 : ℝ) ^ a.1) *
                  ((((M - m : ℕ) : ℝ) * ((2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ)) /
                    ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ))) -
                ((m - a.1).choose j : ℝ) * (-1 : ℝ) ^ j * (2 : ℝ) ^ (m - a.1 - j) := by ring
            _ = ((m - a.1).choose j : ℝ) * (-1 : ℝ) ^ j *
                  ((((M - m : ℕ) : ℝ) * ((2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ)) /
                      ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ)) -
                    (2 : ℝ) ^ (m - a.1 - j)) := by rw [hsign]; ring
        rw [hmain_eq]; have hj_bd : ∀ j ∈ Finset.range (m - a.1 + 1),
            |((m - a.1).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
                  ((2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ)) /
                    ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ)) -
                  (2 : ℝ) ^ (m - a.1 - j))| ≤
              (2 : ℝ) ^ (3 * m + 28) / (M : ℝ) := by
          intro j hj; have hja : j ≤ m - a.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hmaj : ((m - a.1).choose j : ℝ) ≤ (2 : ℝ) ^ m :=
            (choose_le_two_pow (m - a.1) j).trans (two_pow_le (by omega))
          have hlead := leading_choose_ratio_approx hm1 hm
            (by omega : m - a.1 - j ≤ m) (by omega : r + (m - a.1) ≤ 9216) hM
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_neg, abs_one,
            one_pow, mul_one]
          calc ((m - a.1).choose j : ℝ) *
                |(((M - m : ℕ) : ℝ) * ((2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ)) /
                      ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ)) -
                    (2 : ℝ) ^ (m - a.1 - j)|
              ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ (2 * m + 28) / (M : ℝ)) :=
                mul_le_mul hmaj hlead (abs_nonneg _) (by positivity)
            _ = (2 : ℝ) ^ (3 * m + 28) / (M : ℝ) := by
                rw [show 3 * m + 28 = m + (2 * m + 28) by omega, pow_add]; ring
        calc |∑ j ∈ Finset.range (m - a.1 + 1),
                ((m - a.1).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
                    ((2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ)) /
                      ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ)) -
                    (2 : ℝ) ^ (m - a.1 - j))|
            ≤ ∑ j ∈ Finset.range (m - a.1 + 1), |((m - a.1).choose j : ℝ) * (-1 : ℝ) ^ j *
                  ((((M - m : ℕ) : ℝ) * ((2 * M - (r + (m - a.1))).choose (m - a.1 - j) : ℝ)) /
                      ((M : ℝ) * ((M - 1).choose (m - a.1 - j) : ℝ)) -
                    (2 : ℝ) ^ (m - a.1 - j))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ Finset.range (m - a.1 + 1), (2 : ℝ) ^ (3 * m + 28) / (M : ℝ) :=
              Finset.sum_le_sum hj_bd
          _ = ((m - a.1 + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (3 * m + 28) / (M : ℝ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 : ℝ) ^ 14 * ((2 : ℝ) ^ (3 * m + 28) / (M : ℝ)) := by
              have hlen : ((m - a.1 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 14 := by
                have hnat : m - a.1 + 1 ≤ 2 ^ 14 := (by omega); exact_mod_cast hnat
              exact mul_le_mul_of_nonneg_right hlen (by positivity)
          _ = (2 : ℝ) ^ (3 * m + 42) / (M : ℝ) := by
              rw [show 3 * m + 42 = 14 + (3 * m + 28) by omega, pow_add]; ring
      have htri : |tailSum + mainSum - 1| ≤ |tailSum| + |mainSum - 1| := by
        rw [show tailSum + mainSum - 1 = tailSum + (mainSum - 1) by ring]; exact abs_add_le _ _
      have ht1 : (2 : ℝ) ^ (2 * r + 3 * m + 38) ≤ (2 : ℝ) ^ 35999 := two_pow_le (by omega)
      have ht2 : (2 : ℝ) ^ (3 * m + 42) ≤ (2 : ℝ) ^ 35999 := two_pow_le (by omega)
      have hsum36 : (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) + (2 : ℝ) ^ (3 * m + 42) / (M : ℝ) ≤ (2
        : ℝ) ^ 36000 / (M : ℝ) := by
        rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hM_pos.le
        calc (2 : ℝ) ^ (2 * r + 3 * m + 38) + (2 : ℝ) ^ (3 * m + 42)
            ≤ (2 : ℝ) ^ 35999 + (2 : ℝ) ^ 35999 := add_le_add ht1 ht2
          _ = (2 : ℝ) ^ 36000 := two_pow_add_self 35999
      exact (htri.trans (add_le_add htail_le hmain_le)).trans hsum36
    · -- Case 3: Subdiagonal a = b + 1
      have hab1 : a.1 = b.1 + 1 := (by omega); have hb_lt : b.1 < min m r := (by omega)
      have hneq : a ≠ b := fun h ↦ by have := congrArg Fin.val h; omega
      have hlin_sub : ((1 + (1 / √((2 * M : ℕ) : ℝ)) • dAltGenMat m r) : Matrix (Fin (orbDim m r))
        (Fin (orbDim m r)) ℝ) a b = dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ) := by
        simp only [Matrix.add_apply, Matrix.one_apply_ne hneq, zero_add, Matrix.smul_apply,
          smul_eq_mul, dAltGenMat, tridiagSkewMat, Matrix.of_apply, eq_true hab1, ↓reduceIte,
          one_div, inv_mul_eq_div]
      rw [Matrix.sub_apply, hlin_sub, hstep_apply, hab1]
      -- Bound √(orbCard (b + 1) / orbCard b) ≤ 1
      have hsqrt_le1 :
          √((orbCard (2 * M) m r (b.1 + 1) : ℝ) / (orbCard (2 * M) m r b.1 : ℝ)) ≤ 1 := by
        have hb_pos : (0 : ℝ) < (orbCard (2 * M) m r b.1 : ℝ) := Nat.cast_pos.mpr (orbCard_pos_gen
          hmrN hb_le); have hrel := orbCard_succ_rel hb_lt hmrN
        have hle_nat : orbCard (2 * M) m r (b.1 + 1) ≤ orbCard (2 * M) m r b.1 := by
          have hden_ge : (r - b.1) * (m - b.1) ≤ (b.1 + 1) * (2 * M - r - m + b.1 + 1) := by
            have h1 : (r - b.1) * (m - b.1) ≤ 1024 * 8192 := Nat.mul_le_mul (by omega) (by omega)
            have h2 : 1024 * 8192 ≤ 1 * (2 * M - r - m + b.1 + 1) := (by omega)
            exact h1.trans (h2.trans (Nat.mul_le_mul_right _ (by omega : 1 ≤ b.1 + 1)))
          have hmul : orbCard (2 * M) m r (b.1 + 1) * ((b.1 + 1) * (2 * M - r - m + b.1 + 1)) ≤
            orbCard (2 * M) m r b.1 * ((b.1 + 1) * (2 * M - r - m + b.1 + 1)) := by
            rw [hrel]; exact Nat.mul_le_mul_left _ hden_ge
          exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos (by omega) (by omega))
        rw [Real.sqrt_le_one, div_le_one hb_pos]; exact_mod_cast hle_nat
      set sc : ℝ := √((orbCard (2 * M) m r (b.1 + 1) : ℝ) / (orbCard (2 * M) m r b.1 : ℝ))
      have hsc_nn : 0 ≤ sc := Real.sqrt_nonneg _
      rw [dAltOrbRawSum_restrict_j (by omega : b.1 ≤ b.1 + 1) (by omega : b.1 + 1 ≤ m),
        hdiv2, Finset.sum_range_succ]
      let tailSum : ℝ := sc * (∑ i ∈ Finset.range b.1, ((b.1 + 1).choose i * (r - (b.1 + 1)).choose
        (b.1 - i) : ℝ) * ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j * (2 *
        M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) * dAltEntry M m (i + j)) * (-1 : ℝ) ^ b.1
      let mainSum : ℝ := sc * (((b.1 + 1).choose b.1 * (r - (b.1 + 1)).choose (b.1 - b.1) : ℝ) * ∑ j
        ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j * (2 * M - r - (m - (b.1 +
        1))).choose (m - b.1 - j) : ℝ) * dAltEntry M m (b.1 + j)) * (-1 : ℝ) ^ b.1
      have hsplit :
          sc * ((∑ i ∈ Finset.range b.1,
              ((b.1 + 1).choose i * (r - (b.1 + 1)).choose (b.1 - i) : ℝ) *
                ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                    (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                    dAltEntry M m (i + j)) +
            ((b.1 + 1).choose b.1 * (r - (b.1 + 1)).choose (b.1 - b.1) : ℝ) *
              ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                  (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                  dAltEntry M m (b.1 + j)) * (-1 : ℝ) ^ b.1 =
            tailSum + mainSum := by ring
      rw [hsplit]
      -- Bound |tailSum|
      have htail_le : |tailSum| ≤ (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) := by
        dsimp only [tailSum]
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_mul, abs_of_nonneg hsc_nn]
        have hi_bd : ∀ i ∈ Finset.range b.1,
            |((b.1 + 1).choose i * (r - (b.1 + 1)).choose (b.1 - i) : ℝ) *
                ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                    (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                    dAltEntry M m (i + j)| ≤
              (2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ) := by
          intro i hi; have hib : i < b.1 := Finset.mem_range.mp hi
          have hc1 : ((b.1 + 1).choose i : ℝ) ≤ (2 : ℝ) ^ r :=
            (choose_le_two_pow (b.1 + 1) i).trans (two_pow_le (by omega))
          have hc2 : ((r - (b.1 + 1)).choose (b.1 - i) : ℝ) ≤ (2 : ℝ) ^ r :=
            (choose_le_two_pow (r - (b.1 + 1)) (b.1 - i)).trans (two_pow_le (by omega))
          have hj_bd := inner_j_sum_bound_of_pos_p hm1 hm hr
            (by omega : b.1 + 1 ≤ m) (by omega : b.1 + 1 ≤ r)
            (by omega : b.1 ≤ b.1 + 1) hib hM
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
            abs_of_nonneg (Nat.cast_nonneg _)]
          calc ((b.1 + 1).choose i : ℝ) * ((r - (b.1 + 1)).choose (b.1 - i) : ℝ) *
                |∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                    (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                    dAltEntry M m (i + j)|
              ≤ ((2 : ℝ) ^ r * (2 : ℝ) ^ r) * ((2 : ℝ) ^ (3 * m + 27) / (M : ℝ)) :=
                mul_le_mul (mul_le_mul hc1 hc2 (by positivity) (by positivity))
                  hj_bd (abs_nonneg _) (by positivity)
            _ = (2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ) := by
                rw [show 2 * r + 3 * m + 27 = r + r + (3 * m + 27) by omega,
                  pow_add, pow_add]; ring
        have hsum_bd :
            |∑ i ∈ Finset.range b.1, ((b.1 + 1).choose i * (r - (b.1 + 1)).choose (b.1 - i) : ℝ) *
                  ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                      (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                      dAltEntry M m (i + j)| ≤
              (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) := by
          calc |∑ i ∈ Finset.range b.1,
                  ((b.1 + 1).choose i * (r - (b.1 + 1)).choose (b.1 - i) : ℝ) *
                    ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                        (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                        dAltEntry M m (i + j)|
              ≤ ∑ i ∈ Finset.range b.1,
                  |((b.1 + 1).choose i * (r - (b.1 + 1)).choose (b.1 - i) : ℝ) *
                    ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                        (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                        dAltEntry M m (i + j)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i ∈ Finset.range b.1, (2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ) :=
                Finset.sum_le_sum hi_bd
            _ = (b.1 : ℝ) * ((2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ)) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (2 : ℝ) ^ 11 * ((2 : ℝ) ^ (2 * r + 3 * m + 27) / (M : ℝ)) := by
                have hlen : (b.1 : ℝ) ≤ (2 : ℝ) ^ 11 := by
                  have hnat : b.1 ≤ 2 ^ 11 := (by omega); exact_mod_cast hnat
                exact mul_le_mul_of_nonneg_right hlen (by positivity)
            _ = (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) := by
                rw [show 2 * r + 3 * m + 38 = 11 + (2 * r + 3 * m + 27) by omega, pow_add]; ring
        calc sc * |∑ i ∈ Finset.range b.1,
                ((b.1 + 1).choose i * (r - (b.1 + 1)).choose (b.1 - i) : ℝ) *
                  ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
                      (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
                      dAltEntry M m (i + j)|
            ≤ 1 * ((2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ)) :=
              mul_le_mul hsqrt_le1 hsum_bd (abs_nonneg _) zero_le_one
          _ = (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) := one_mul _
      -- Bound |mainSum - (2 * (b + 1)) * sc|
      have hmain_approx :
          |mainSum - (2 * (b.1 + 1 : ℝ)) * sc| ≤ (2 : ℝ) ^ (3 * m + 53) / (M : ℝ) := by
        have hch_b : ((b.1 + 1).choose b.1 : ℝ) = (b.1 + 1 : ℝ) := by
          rw [Nat.choose_succ_self_right]; push_cast; rfl
        have hmain_eq : mainSum - (2 * (b.1 + 1 : ℝ)) * sc = sc * (b.1 + 1 : ℝ) * ∑ j ∈ Finset.range
          (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
          ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) / ((M : ℝ) * ((M - 1).choose
          (m - b.1 - j) : ℝ)) - (2 : ℝ) ^ (m - b.1 - j)) := by
          have h2sc : (2 * (b.1 + 1 : ℝ)) * sc = ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), sc * (b.1 +
            1 : ℝ) * (((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * (2 : ℝ) ^ (m - b.1 - j)) := by
            have h1 := binom_two_sub_one (m - (b.1 + 1))
            calc (2 * (b.1 + 1 : ℝ)) * sc
                = (sc * (b.1 + 1 : ℝ) * 2) * 1 := by ring
              _ = (sc * (b.1 + 1 : ℝ) * 2) *
                    ∑ j ∈ Finset.range (m - (b.1 + 1) + 1),
                      ((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j *
                        (2 : ℝ) ^ (m - (b.1 + 1) - j) :=
                  congrArg ((sc * (b.1 + 1 : ℝ) * 2) * ·) h1.symm
              _ = ∑ j ∈ Finset.range (m - (b.1 + 1) + 1),
                    (sc * (b.1 + 1 : ℝ) * 2) * (((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j *
                        (2 : ℝ) ^ (m - (b.1 + 1) - j)) := by rw [Finset.mul_sum]
              _ = ∑ j ∈ Finset.range (m - (b.1 + 1) + 1),
                    sc * (b.1 + 1 : ℝ) * (((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j *
                        (2 : ℝ) ^ (m - b.1 - j)) := by
                  refine Finset.sum_congr rfl fun j hj ↦ ?_
                  have hjb : j ≤ m - (b.1 + 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                  rw [show m - b.1 - j = (m - (b.1 + 1) - j) + 1 by omega, pow_succ]; ring
          have hmain_lhs : mainSum = ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), sc * (b.1 + 1 : ℝ) *
            (((m - (b.1 + 1)).choose j * (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) *
            dAltEntry M m (b.1 + j) * (-1 : ℝ) ^ b.1) := by
            dsimp only [mainSum]
            rw [hch_b, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
            let innerJ : ℝ := ∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j *
              (2 * M - r - (m - (b.1 + 1))).choose (m - b.1 - j) : ℝ) * dAltEntry M m (b.1 + j)
            change sc * ((b.1 + 1 : ℝ) * innerJ) * (-1 : ℝ) ^ b.1 = _; have hassoc :
                sc * ((b.1 + 1 : ℝ) * innerJ) * (-1 : ℝ) ^ b.1 =
                  (sc * (b.1 + 1 : ℝ)) * (innerJ * (-1 : ℝ) ^ b.1) := by ring
            rw [hassoc]; dsimp only [innerJ]; rw [Finset.sum_mul, Finset.mul_sum]
          rw [hmain_lhs, h2sc, ← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          have hjb : j ≤ m - (b.1 + 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hm_sub : m - (b.1 + j) = m - b.1 - j := (by omega)
          have h2M_sub : 2 * M - r - (m - (b.1 + 1)) = 2 * M - (r + (m - (b.1 + 1))) := (by omega)
          unfold dAltEntry; simp only [show m ≠ 0 by omega, ↓reduceIte, hm_sub, h2M_sub]
          have hsign : (-1 : ℝ) ^ (b.1 + j) * (-1 : ℝ) ^ b.1 = (-1 : ℝ) ^ j := by
            rw [pow_add, mul_right_comm, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
              one_mul]
          calc sc * (b.1 + 1 : ℝ) * (((m - (b.1 + 1)).choose j * (2 * M - (r + (m - (b.1 +
                1)))).choose (m - b.1 - j) : ℝ) * ((-1 : ℝ) ^ (b.1 + j) * ((M - m : ℕ) : ℝ) / ((M :
                ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ))) * (-1 : ℝ) ^ b.1) - sc * (b.1 + 1 : ℝ) *
                (((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * (2 : ℝ) ^ (m - b.1 - j)) = sc *
                (b.1 + 1 : ℝ) * (((m - (b.1 + 1)).choose j : ℝ) * ((-1 : ℝ) ^ (b.1 + j) * (-1 : ℝ) ^
                b.1) * ((((M - m : ℕ) : ℝ) * ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) :
                ℝ)) / ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ))) - ((m - (b.1 + 1)).choose j :
                ℝ) * (-1 : ℝ) ^ j * (2 : ℝ) ^ (m - b.1 - j)) := by
                ring
            _ = sc * (b.1 + 1 : ℝ) *
                  (((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
                      ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) /
                        ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ)) -
                      (2 : ℝ) ^ (m - b.1 - j))) := by rw [hsign]; ring
        rw [hmain_eq, abs_mul, abs_mul, abs_of_nonneg hsc_nn,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.1 + 1 : ℝ))]
        have hj_bd : ∀ j ∈ Finset.range (m - (b.1 + 1) + 1),
            |((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
                  ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) /
                    ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ)) -
                  (2 : ℝ) ^ (m - b.1 - j))| ≤
              (2 : ℝ) ^ (3 * m + 28) / (M : ℝ) := by
          intro j hj; have hjb : j ≤ m - (b.1 + 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hmaj : ((m - (b.1 + 1)).choose j : ℝ) ≤ (2 : ℝ) ^ m :=
            (choose_le_two_pow (m - (b.1 + 1)) j).trans (two_pow_le (by omega))
          have hlead := leading_choose_ratio_approx hm1 hm
            (by omega : m - b.1 - j ≤ m) (by omega : r + (m - (b.1 + 1)) ≤ 9216) hM
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_neg, abs_one,
            one_pow, mul_one]
          calc ((m - (b.1 + 1)).choose j : ℝ) *
                |(((M - m : ℕ) : ℝ) * ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) /
                      ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ)) -
                    (2 : ℝ) ^ (m - b.1 - j)|
              ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ (2 * m + 28) / (M : ℝ)) :=
                mul_le_mul hmaj hlead (abs_nonneg _) (by positivity)
            _ = (2 : ℝ) ^ (3 * m + 28) / (M : ℝ) := by
                rw [show 3 * m + 28 = m + (2 * m + 28) by omega, pow_add]; ring
        have hsum_bd :
            |∑ j ∈ Finset.range (m - (b.1 + 1) + 1), ((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j *
                  ((((M - m : ℕ) : ℝ) *
                    ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) /
                      ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ)) -
                    (2 : ℝ) ^ (m - b.1 - j))| ≤
              (2 : ℝ) ^ (3 * m + 42) / (M : ℝ) := by
          calc |∑ j ∈ Finset.range (m - (b.1 + 1) + 1),
                  ((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
                      ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) /
                        ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ)) -
                      (2 : ℝ) ^ (m - b.1 - j))|
              ≤ ∑ j ∈ Finset.range (m - (b.1 + 1) + 1),
                  |((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
                      ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) /
                        ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ)) -
                      (2 : ℝ) ^ (m - b.1 - j))| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j ∈ Finset.range (m - (b.1 + 1) + 1), (2 : ℝ) ^ (3 * m + 28) / (M : ℝ) :=
                Finset.sum_le_sum hj_bd
            _ = ((m - (b.1 + 1) + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (3 * m + 28) / (M : ℝ)) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (2 : ℝ) ^ 14 * ((2 : ℝ) ^ (3 * m + 28) / (M : ℝ)) := by
                have hlen : ((m - (b.1 + 1) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 14 := by
                  have hnat : m - (b.1 + 1) + 1 ≤ 2 ^ 14 := (by omega); exact_mod_cast hnat
                exact mul_le_mul_of_nonneg_right hlen (by positivity)
            _ = (2 : ℝ) ^ (3 * m + 42) / (M : ℝ) := by
                rw [show 3 * m + 42 = 14 + (3 * m + 28) by omega, pow_add]; ring
        have hb11 : (b.1 + 1 : ℝ) ≤ (2 : ℝ) ^ 11 := by
          have hnat : (b.1 + 1 : ℕ) ≤ 2 ^ 11 := (by omega); exact_mod_cast hnat
        calc sc * (b.1 + 1 : ℝ) *
              |∑ j ∈ Finset.range (m - (b.1 + 1) + 1),
                ((m - (b.1 + 1)).choose j : ℝ) * (-1 : ℝ) ^ j * ((((M - m : ℕ) : ℝ) *
                    ((2 * M - (r + (m - (b.1 + 1)))).choose (m - b.1 - j) : ℝ)) /
                      ((M : ℝ) * ((M - 1).choose (m - b.1 - j) : ℝ)) -
                    (2 : ℝ) ^ (m - b.1 - j))|
            ≤ (1 * (2 : ℝ) ^ 11) * ((2 : ℝ) ^ (3 * m + 42) / (M : ℝ)) :=
              mul_le_mul (mul_le_mul hsqrt_le1 hb11 (by positivity) zero_le_one)
                hsum_bd (abs_nonneg _) (by positivity)
          _ = (2 : ℝ) ^ (3 * m + 53) / (M : ℝ) := by
              rw [one_mul, show 3 * m + 53 = 11 + (3 * m + 42) by omega, pow_add]; ring
      -- Bound |(2 * (b + 1)) * sc - dAltCoupling / √(2 * M)|
      have hcoupl_diff :
          |(2 * (b.1 + 1 : ℝ)) * sc - dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ)| ≤
            (2 : ℝ) ^ 32 / (M : ℝ) := by
        dsimp only [sc]; rw [two_mul_succ_sqrt_orbCard_ratio hb_lt hmrN]
        have hcoupl_le : dAltCoupling m r b.1 ≤ (2 : ℝ) ^ 18 := by
          unfold dAltCoupling; rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
          rw [← pow_mul]
          have hnat : 4 * (b.1 + 1) * (m - b.1) * (r - b.1) ≤ 2 ^ (18 * 2) := by
            calc 4 * (b.1 + 1) * (m - b.1) * (r - b.1) ≤ (4 * 1024) * 8192 * 1024 := Nat.mul_le_mul
                  (Nat.mul_le_mul (by omega) (by omega)) (by omega)
              _ ≤ 2 ^ (18 * 2) := by norm_num
          exact_mod_cast hnat
        have hinv := inv_sqrt_sub_inv_sqrt_le
          (A := ((2 * M - r - m + b.1 + 1 : ℕ) : ℝ))
          (B := ((2 * M : ℕ) : ℝ))
          (M := (M : ℝ))
          (Nat.one_le_cast.mpr (by omega : 1 ≤ M))
          (Nat.cast_le.mpr (by omega : M ≤ 2 * M - r - m + b.1 + 1))
          (Nat.cast_le.mpr (by omega : 2 * M - r - m + b.1 + 1 ≤ 2 * M))
        have hsub_num : ((2 * M : ℕ) : ℝ) - ((2 * M - r - m + b.1 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 14 := by
          have hnat : 2 * M - (2 * M - r - m + b.1 + 1) ≤ 2 ^ 14 := (by omega)
          have hcast : ((2 * M - (2 * M - r - m + b.1 + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ 14 := by
            exact_mod_cast hnat
          rwa [Nat.cast_sub (by omega : 2 * M - r - m + b.1 + 1 ≤ 2 * M)] at hcast
        rw [show dAltCoupling m r b.1 / √((2 * M - r - m + b.1 + 1 : ℕ) : ℝ) -
              dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ) =
            dAltCoupling m r b.1 *
              (1 / √((2 * M - r - m + b.1 + 1 : ℕ) : ℝ) - 1 / √((2 * M : ℕ) : ℝ)) by ring,
          abs_mul, abs_of_nonneg (by unfold dAltCoupling; exact Real.sqrt_nonneg _)]
        calc dAltCoupling m r b.1 *
              |1 / √((2 * M - r - m + b.1 + 1 : ℕ) : ℝ) - 1 / √((2 * M : ℕ) : ℝ)|
            ≤ (2 : ℝ) ^ 18 *
                ((((2 * M : ℕ) : ℝ) - ((2 * M - r - m + b.1 + 1 : ℕ) : ℝ)) / (M : ℝ)) :=
              mul_le_mul hcoupl_le hinv (abs_nonneg _) (by positivity)
          _ ≤ (2 : ℝ) ^ 18 * ((2 : ℝ) ^ 14 / (M : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right hsub_num hM_pos.le) (by positivity)
          _ = (2 : ℝ) ^ 32 / (M : ℝ) := by rw [show (32 : ℕ) = 18 + 14 by omega, pow_add]; ring
      have htri :
          |tailSum + mainSum - dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ)| ≤
            |tailSum| + |mainSum - (2 * (b.1 + 1 : ℝ)) * sc| +
              |(2 * (b.1 + 1 : ℝ)) * sc - dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ)| := by
        calc |tailSum + mainSum - dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ)|
            = |tailSum + (mainSum - (2 * (b.1 + 1 : ℝ)) * sc) + ((2 * (b.1 + 1 : ℝ)) * sc -
                  dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ))| := by ring_nf
          _ ≤ |tailSum + (mainSum - (2 * (b.1 + 1 : ℝ)) * sc)| +
                |(2 * (b.1 + 1 : ℝ)) * sc - dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ)| :=
              abs_add_le _ _
          _ ≤ |tailSum| + |mainSum - (2 * (b.1 + 1 : ℝ)) * sc| +
                |(2 * (b.1 + 1 : ℝ)) * sc - dAltCoupling m r b.1 / √((2 * M : ℕ) : ℝ)| :=
              add_le_add (abs_add_le _ _) le_rfl
      have ht1 : (2 : ℝ) ^ (2 * r + 3 * m + 38) ≤ (2 : ℝ) ^ 35998 := two_pow_le (by omega)
      have ht2 : (2 : ℝ) ^ (3 * m + 53) ≤ (2 : ℝ) ^ 35998 := two_pow_le (by omega)
      have ht3 : (2 : ℝ) ^ 32 ≤ (2 : ℝ) ^ 35998 := two_pow_le (by omega)
      have hsum36 : (2 : ℝ) ^ (2 * r + 3 * m + 38) / (M : ℝ) + (2 : ℝ) ^ (3 * m + 53) / (M : ℝ) + (2
        : ℝ) ^ 32 / (M : ℝ) ≤ (2 : ℝ) ^ 36000 / (M : ℝ) := by
        rw [← add_div, ← add_div]; refine div_le_div_of_nonneg_right ?_ hM_pos.le
        calc (2 : ℝ) ^ (2 * r + 3 * m + 38) + (2 : ℝ) ^ (3 * m + 53) + (2 : ℝ) ^ 32 ≤ ((2 : ℝ) ^
              35998 + (2 : ℝ) ^ 35998) + (2 : ℝ) ^ 35998 := add_le_add (add_le_add ht1 ht2) ht3
          _ = (2 : ℝ) ^ 35999 + (2 : ℝ) ^ 35998 := by rw [two_pow_add_self 35998]
          _ ≤ (2 : ℝ) ^ 35999 + (2 : ℝ) ^ 35999 := add_le_add le_rfl (two_pow_le (by omega))
          _ = (2 : ℝ) ^ 36000 := two_pow_add_self 35999
      exact (htri.trans (add_le_add (add_le_add htail_le hmain_approx) hcoupl_diff)).trans hsum36
private lemma stepOrbMat_sub_linear_entry_symm {N m r : ℕ} (hmrN : m + r ≤ N)
    (a b : Fin (orbDim m r)) :
    |(dAltStepOrbMat N m r - (1 + (1 / √(N : ℝ)) • dAltGenMat m r)) a b| =
      |(dAltStepOrbMat N m r - (1 + (1 / √(N : ℝ)) • dAltGenMat m r)) b a| := by
  have hsym : dAltOrbMat N m r a b = dAltOrbMat N m r b a := by
    have ht := congrFun (congrFun (dAltOrbMat_transpose hmrN) b) a
    simpa [Matrix.transpose_apply] using ht
  have hstep (x y : Fin (orbDim m r)) :
      dAltStepOrbMat N m r x y = dAltOrbMat N m r x y * (-1 : ℝ) ^ y.1 := by
    unfold dAltStepOrbMat zOrbMat; rw [Matrix.mul_diagonal]
  by_cases hab : a = b
  · subst hab; rfl
  · have hba : b ≠ a := Ne.symm hab; by_cases h1 : a.1 = b.1 + 1
    · have h2 : b.1 ≠ a.1 + 1 := (by omega)
      have hneg : (dAltStepOrbMat N m r - (1 + (1 / √(N : ℝ)) • dAltGenMat m r)) a b =
        -((dAltStepOrbMat N m r - (1 + (1 / √(N : ℝ)) • dAltGenMat m r)) b a) := by
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.one_apply_ne
          hba, zero_add, Matrix.smul_apply, smul_eq_mul, hstep, hsym, dAltGenMat, tridiagSkewMat,
          Matrix.of_apply, eq_true h1, eq_false h2, ↓reduceIte]; rw [h1, pow_succ]; ring
      rw [hneg, abs_neg]
    · by_cases h2 : b.1 = a.1 + 1
      · have hneg : (dAltStepOrbMat N m r - (1 + (1 / √(N : ℝ)) • dAltGenMat m r)) a b =
          -((dAltStepOrbMat N m r - (1 + (1 / √(N : ℝ)) • dAltGenMat m r)) b a) := by
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hab,
            Matrix.one_apply_ne hba, zero_add, Matrix.smul_apply, smul_eq_mul, hstep, hsym,
            dAltGenMat, tridiagSkewMat, Matrix.of_apply, eq_false h1, eq_true h2, ↓reduceIte]
          rw [h2, pow_succ]; ring
        rw [hneg, abs_neg]
      · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hab,
          Matrix.one_apply_ne hba, zero_add, Matrix.smul_apply, smul_eq_mul, hstep, hsym,
          dAltGenMat, tridiagSkewMat, Matrix.of_apply, eq_false h1, eq_false h2, ↓reduceIte,
          mul_zero, sub_zero, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
/-
 ## Section 4: `K`-Step Trajectory Limit Bound (`vecNorm_dAltStepOrbMat_pow_sub_taylor8_le`)
-/
private lemma vecNorm_dAltGenMat_mulVec_le_pow {m r : ℕ} (hm : m ≤ 8192) (hr : r ≤ 1024) (v : Fin
    (orbDim m r) → ℝ) : vecNorm (dAltGenMat m r *ᵥ v) ≤ (2 : ℝ) ^ 19 * vecNorm v := by
  have hcoupl : ∀ w < min m r, |dAltCoupling m r w| ≤ (2 : ℝ) ^ 18 := by
    intro w hw; have hw_r : w < r := lt_of_lt_of_le hw (Nat.min_le_right m r); unfold dAltCoupling
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
    rw [← pow_mul]
    have hnat : 4 * (w + 1) * (m - w) * (r - w) ≤ 2 ^ (18 * 2) := by
      calc 4 * (w + 1) * (m - w) * (r - w) ≤ (4 * 1024) * 8192 * 1024 := Nat.mul_le_mul
            (Nat.mul_le_mul (by omega) (by omega)) (by omega)
        _ ≤ 2 ^ (18 * 2) := by norm_num
    exact_mod_cast hnat
  have h := vecNorm_tridiagSkewMat_mulVec_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 18) hcoupl v
  rwa [show 2 * (2 : ℝ) ^ 18 = (2 : ℝ) ^ 19 by norm_num] at h
private lemma vecNorm_smul_nonneg {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (v : Fin d → ℝ) :
    vecNorm (c • v) = c * vecNorm v := by
  rw [vecNorm_smul, abs_of_nonneg hc]
/-- Arbitrary-vector `K`-step trajectory convergence between `(dAltStepOrbMat (2 ^ n) m r) ^
  K`
  and `(taylor8Mat (1 / √(2 ^ n)) (dAltGenMat m r)) ^ K` for any `u, e` with `vecNorm e ≤ 1`
  (supporting both `1`-stage and multi-stage `D_{\text{alt}}` walks). -/
theorem vecNorm_dAltStepOrbMat_pow_sub_taylor8_vec_le {n m r K : ℕ} (hn : altN0 ≤ n) (hm1 : 1 ≤ m)
    (hm : m ≤ 8192) (_hr1 : 1 ≤ r) (hr : r ≤ 1024) (hK : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ)) {u e : Fin
    (orbDim m r) → ℝ} (he : vecNorm e ≤ 1) : vecNorm (((dAltStepOrbMat (2 ^ n) m r) ^ K) *ᵥ u -
    ((taylor8Mat (1 / √(2 ^ n : ℝ)) (dAltGenMat m r)) ^ K) *ᵥ e) ≤ vecNorm (u - e) + 1 / (2 *
    (wdScale : ℝ)) := by
  have hn_alt : 80000 ≤ n := hn; set M : ℕ := 2 ^ (n - 1)
  have h2n_nat : 2 ^ n = 2 * M := by
    dsimp only [M]
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
  have h2n_real : ((2 ^ n : ℕ) : ℝ) = ((2 * M : ℕ) : ℝ) := congrArg Nat.cast h2n_nat
  have h2n_pow : (2 ^ n : ℝ) = ((2 * M : ℕ) : ℝ) := (by rw [← h2n_real]; push_cast; rfl)
  have hM_ge30 : 2 ^ 30 ≤ M := Nat.pow_le_pow_right (by omega) (by omega : 30 ≤ n - 1)
  have hM_real : (M : ℝ) = (2 : ℝ) ^ (n - 1) := (by dsimp only [M]; push_cast; rfl)
  have hM_ge79999 : (2 : ℝ) ^ 79999 ≤ (M : ℝ) := (by rw [hM_real]; exact two_pow_le (by omega))
  have hM_pos : (0 : ℝ) < (M : ℝ) := (by positivity)
  have hN_pos : (0 : ℝ) < (2 ^ n : ℝ) := (by positivity)
  have hsN_pos : 0 < √(2 ^ n : ℝ) := Real.sqrt_pos.mpr hN_pos
  have hmrN : m + r ≤ 2 ^ n := (by have : 9216 < 2 ^ 30 := (by norm_num); omega)
  have h2mN : 2 * m < 2 ^ n := (by have : 16384 < 2 ^ 30 := (by norm_num); omega)
  set A := dAltStepOrbMat (2 ^ n) m r; set η : ℝ := 1 / √(2 ^ n : ℝ); set G := dAltGenMat m r
  set B := taylor8Mat η G; set T1 : Matrix (Fin (orbDim m r)) (Fin (orbDim m r)) ℝ := 1 + η • G
  -- 1. Contraction of A and B
  have hA_orth := dAltStepOrbMat_orthogonal_two_pow (by omega : 1 ≤ n) h2mN hmrN
  have hA_contr : ∀ x, vecNorm (A *ᵥ x) ≤ vecNorm x := fun x ↦
    le_of_eq (vecNorm_mulVec_of_orthogonal hA_orth x)
  have hG_bound : ∀ u, vecNorm (G *ᵥ u) ≤ (2 : ℝ) ^ 19 * vecNorm u :=
    vecNorm_dAltGenMat_mulVec_le_pow hm hr
  have hηB_le1 : η * (2 : ℝ) ^ 19 ≤ 1 := by
    dsimp only [η]; rw [one_div_mul_eq_div, div_le_one hsN_pos]; refine Real.le_sqrt_of_sq_le ?_
    rw [← pow_mul]; exact two_pow_le (by omega)
  have hB_contr : ∀ x, vecNorm (B *ᵥ x) ≤ vecNorm x := fun x ↦ vecNorm_taylor8Mat_mulVec_le
    (dAltGenMat_transpose m r) (by positivity) (by positivity) hG_bound hηB_le1 x
  -- 2. Single-step perturbation: A - T1
  have hAT1_entry : ∀ i j : Fin (orbDim m r), |(A - T1) i j| ≤ (2 : ℝ) ^ 36000 / (M : ℝ) := by
    intro i j; dsimp only [A, T1, η, G]; by_cases hji : j.1 ≤ i.1
    · rw [h2n_nat, h2n_pow]; exact stepOrbMat_sub_linear_entry_le_lower hm1 hm hr hM_ge30 i j hji
    · have hij : i.1 ≤ j.1 := (by omega); have hsym := stepOrbMat_sub_linear_entry_symm hmrN i j
      rw [Nat.cast_pow, Nat.cast_ofNat] at hsym; rw [hsym, h2n_nat, h2n_pow]
      exact stepOrbMat_sub_linear_entry_le_lower hm1 hm hr hM_ge30 j i hij
  have hAT1_op : ∀ x, vecNorm ((A - T1) *ᵥ x) ≤ ((2 : ℝ) ^ 36022 / (M : ℝ)) * vecNorm x := by
    intro x; have h1 := vecNorm_entrywise_mulVec_le (by positivity) hAT1_entry x
    have hd_le : (orbDim m r : ℝ) ^ 2 ≤ (2 : ℝ) ^ 22 := by
      have hnat : orbDim m r ≤ 2 ^ 11 := (by unfold orbDim; omega)
      have hcast : (orbDim m r : ℝ) ≤ (2 : ℝ) ^ 11 := (by exact_mod_cast hnat)
      calc (orbDim m r : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 11) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcast 2
        _ = (2 : ℝ) ^ 22 := by rw [← pow_mul]
    calc vecNorm ((A - T1) *ᵥ x)
        ≤ (orbDim m r : ℝ) ^ 2 * ((2 : ℝ) ^ 36000 / (M : ℝ)) * vecNorm x := h1
      _ ≤ ((2 : ℝ) ^ 22 * ((2 : ℝ) ^ 36000 / (M : ℝ))) * vecNorm x :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hd_le (by positivity)) (vecNorm_nonneg x)
      _ = ((2 : ℝ) ^ 36022 / (M : ℝ)) * vecNorm x := by
          rw [← mul_div_assoc, ← pow_add, show 22 + 36000 = 36022 by omega]
  -- 3. Single-step perturbation: B - T1 (degree 2..8 Taylor tail)
  have hBT1_op : ∀ x, vecNorm ((T1 - B) *ᵥ x) ≤ ((2 : ℝ) ^ 37 / (M : ℝ)) * vecNorm x := by
    intro x; set X := η • G
    have hX_op : ∀ u, vecNorm (X *ᵥ u) ≤ (η * (2 : ℝ) ^ 19) * vecNorm u := by
      intro u; dsimp only [X]
      rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg (by positivity : 0 ≤ η)]
      calc η * vecNorm (G *ᵥ u)
          ≤ η * ((2 : ℝ) ^ 19 * vecNorm u) := mul_le_mul_of_nonneg_left (hG_bound u) (by positivity)
        _ = (η * (2 : ℝ) ^ 19) * vecNorm u := by ring
    have hc_sq : (η * (2 : ℝ) ^ 19) ^ 2 = (2 : ℝ) ^ 37 / (M : ℝ) := by
      dsimp only [η]; rw [one_div_mul_eq_div, div_pow, Real.sq_sqrt hN_pos.le, h2n_pow]; push_cast
      rw [← pow_mul, show 19 * 2 = 37 + 1 by omega, pow_succ]; field_simp [hM_pos.ne']
    have hpow_le : ∀ k : ℕ, 2 ≤ k →
        vecNorm ((X ^ k) *ᵥ x) ≤ ((2 : ℝ) ^ 37 / (M : ℝ)) * vecNorm x := by
      intro k hk2; have h1 := vecNorm_pow_mulVec_le (by positivity) hX_op k x
      have h2 : (η * (2 : ℝ) ^ 19) ^ k ≤ (η * (2 : ℝ) ^ 19) ^ 2 := by
        rw [show k = 2 + (k - 2) by omega]
        exact pow_anti_of_le_one (by positivity) hηB_le1 2 (k - 2)
      rw [hc_sq] at h2; exact h1.trans (mul_le_mul_of_nonneg_right h2 (vecNorm_nonneg x))
    have hexp : (B - T1) *ᵥ x = (1 / 2 : ℝ) • ((X ^ 2) *ᵥ x) + (1 / 6 : ℝ) • ((X ^ 3) *ᵥ x) + (1 /
      24 : ℝ) • ((X ^ 4) *ᵥ x) + (1 / 120 : ℝ) • ((X ^ 5) *ᵥ x) + (1 / 720 : ℝ) • ((X ^ 6) *ᵥ x) +
      (1 / 5040 : ℝ) • ((X ^ 7) *ᵥ x) + (1 / 40320 : ℝ) • ((X ^ 8) *ᵥ x) := by
      ext idx; dsimp only [B, T1, X, taylor8Mat, taylor8OfMat]
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [show (T1 - B) *ᵥ x = -((B - T1) *ᵥ x) by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, neg_sub], vecNorm_neg, hexp]
    let v2 := (1 / 2 : ℝ) • ((X ^ 2) *ᵥ x); let v3 := (1 / 6 : ℝ) • ((X ^ 3) *ᵥ x)
    let v4 := (1 / 24 : ℝ) • ((X ^ 4) *ᵥ x); let v5 := (1 / 120 : ℝ) • ((X ^ 5) *ᵥ x)
    let v6 := (1 / 720 : ℝ) • ((X ^ 6) *ᵥ x); let v7 := (1 / 5040 : ℝ) • ((X ^ 7) *ᵥ x)
    let v8 := (1 / 40320 : ℝ) • ((X ^ 8) *ᵥ x)
    have htri : vecNorm (v2 + v3 + v4 + v5 + v6 + v7 + v8) ≤ (1 / 2) * vecNorm ((X ^ 2) *ᵥ x) + (1 /
      6) * vecNorm ((X ^ 3) *ᵥ x) + (1 / 24) * vecNorm ((X ^ 4) *ᵥ x) + (1 / 120) * vecNorm ((X ^ 5)
      *ᵥ x) + (1 / 720) * vecNorm ((X ^ 6) *ᵥ x) + (1 / 5040) * vecNorm ((X ^ 7) *ᵥ x) + (1 /
      40320) * vecNorm ((X ^ 8) *ᵥ x) := by
      have hs2 : vecNorm (v2 + v3) ≤ vecNorm v2 + vecNorm v3 := vecNorm_add_le _ _
      have hs3 : vecNorm (v2 + v3 + v4) ≤ vecNorm v2 + vecNorm v3 + vecNorm v4 :=
        (vecNorm_add_le _ _).trans (add_le_add hs2 le_rfl)
      have hs4 : vecNorm (v2 + v3 + v4 + v5) ≤ vecNorm v2 + vecNorm v3 + vecNorm v4 + vecNorm v5 :=
        (vecNorm_add_le _ _).trans (add_le_add hs3 le_rfl)
      have hs5 : vecNorm (v2 + v3 + v4 + v5 + v6) ≤ vecNorm v2 + vecNorm v3 + vecNorm v4 + vecNorm
        v5 + vecNorm v6 := (vecNorm_add_le _ _).trans (add_le_add hs4 le_rfl)
      have hs6 : vecNorm (v2 + v3 + v4 + v5 + v6 + v7) ≤ vecNorm v2 + vecNorm v3 + vecNorm v4 +
        vecNorm v5 + vecNorm v6 + vecNorm v7 := (vecNorm_add_le _ _).trans (add_le_add hs5 le_rfl)
      have hs7 : vecNorm (v2 + v3 + v4 + v5 + v6 + v7 + v8) ≤ vecNorm v2 + vecNorm v3 + vecNorm v4 +
        vecNorm v5 + vecNorm v6 + vecNorm v7 + vecNorm v8 := (vecNorm_add_le _ _).trans (add_le_add
        hs6 le_rfl); refine hs7.trans (le_of_eq ?_)
      dsimp only [v2, v3, v4, v5, v6, v7, v8]
      rw [vecNorm_smul_nonneg (by norm_num), vecNorm_smul_nonneg (by norm_num), vecNorm_smul_nonneg
        (by norm_num), vecNorm_smul_nonneg (by norm_num), vecNorm_smul_nonneg (by norm_num),
        vecNorm_smul_nonneg (by norm_num), vecNorm_smul_nonneg (by norm_num)]
    have hp2 := hpow_le 2 (by omega); have hp3 := hpow_le 3 (by omega)
    have hp4 := hpow_le 4 (by omega); have hp5 := hpow_le 5 (by omega)
    have hp6 := hpow_le 6 (by omega); have hp7 := hpow_le 7 (by omega)
    have hp8 := hpow_le 8 (by omega)
    have hvn : 0 ≤ ((2 : ℝ) ^ 37 / (M : ℝ)) * vecNorm x := mul_nonneg (by positivity)
      (vecNorm_nonneg x); linarith
  have hAB_op : ∀ x, vecNorm ((A - B) *ᵥ x) ≤ ((2 : ℝ) ^ 36023 / (M : ℝ)) * vecNorm x := by
    intro x
    have hsplit : (A - B) *ᵥ x = (A - T1) *ᵥ x + (T1 - B) *ᵥ x := by
      simp only [Matrix.sub_mulVec]; abel
    rw [hsplit]; have h37 : (2 : ℝ) ^ 37 ≤ (2 : ℝ) ^ 36022 := two_pow_le (by omega)
    have hsum : (2 : ℝ) ^ 36022 / (M : ℝ) + (2 : ℝ) ^ 37 / (M : ℝ) ≤ (2 : ℝ) ^ 36023 / (M : ℝ) := by
      rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hM_pos.le
      calc (2 : ℝ) ^ 36022 + (2 : ℝ) ^ 37
          ≤ (2 : ℝ) ^ 36022 + (2 : ℝ) ^ 36022 := add_le_add le_rfl h37
        _ = (2 : ℝ) ^ 36023 := two_pow_add_self 36022
    calc vecNorm ((A - T1) *ᵥ x + (T1 - B) *ᵥ x)
        ≤ vecNorm ((A - T1) *ᵥ x) + vecNorm ((T1 - B) *ᵥ x) := vecNorm_add_le _ _
      _ ≤ ((2 : ℝ) ^ 36022 / (M : ℝ)) * vecNorm x + ((2 : ℝ) ^ 37 / (M : ℝ)) * vecNorm x :=
          add_le_add (hAT1_op x) (hBT1_op x)
      _ = ((2 : ℝ) ^ 36022 / (M : ℝ) + (2 : ℝ) ^ 37 / (M : ℝ)) * vecNorm x := (add_mul _ _ _).symm
      _ ≤ ((2 : ℝ) ^ 36023 / (M : ℝ)) * vecNorm x :=
          mul_le_mul_of_nonneg_right hsum (vecNorm_nonneg x)
  -- 4. Telescope K steps from arbitrary u and e
  have htel := vecNorm_pow_mulVec_sub_le hA_contr hB_contr
    (by positivity : 0 ≤ (2 : ℝ) ^ 36023 / (M : ℝ)) hAB_op K u e
  have hK_bd : (K : ℝ) * ((2 : ℝ) ^ 36023 / (M : ℝ)) ≤ 1 / (2 * (wdScale : ℝ)) := by
    have h1 : (K : ℝ) * ((2 : ℝ) ^ 36023 / (M : ℝ)) ≤ (4 * √(2 ^ n : ℝ)) * ((2 : ℝ) ^ 36023 / (M :
      ℝ)) := mul_le_mul_of_nonneg_right hK (by positivity)
    have hwd : (wdScale : ℝ) ≤ (2 : ℝ) ^ 50 := (by unfold wdScale; norm_num)
    have hwd_pos : (0 : ℝ) < 2 * (wdScale : ℝ) := (by unfold wdScale; positivity); have hsq_key :
        (4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 36023 * (2 * (wdScale : ℝ))) ^ 2 ≤ (M : ℝ) ^ 2 := by
      have hsq_lhs : (4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 36023 * (2 * (wdScale : ℝ))) ^ 2 = 128 * (wdScale
        : ℝ) ^ 2 * (2 : ℝ) ^ 72046 * (M : ℝ) := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hN_pos.le, h2n_pow, ← pow_mul, show 36023 * 2 =
          72046 by omega]; push_cast; generalize (2 : ℝ) ^ 72046 = p72; ring
      have hcoeff_le : 128 * (wdScale : ℝ) ^ 2 * (2 : ℝ) ^ 72046 ≤ (M : ℝ) := by
        have hw2 : 128 * (wdScale : ℝ) ^ 2 ≤ (2 : ℝ) ^ 107 := by
          calc 128 * (wdScale : ℝ) ^ 2 ≤ 128 * ((2 : ℝ) ^ 50) ^ 2 := mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (by positivity) hwd 2) (by norm_num)
            _ = (2 : ℝ) ^ 107 := by norm_num
        calc 128 * (wdScale : ℝ) ^ 2 * (2 : ℝ) ^ 72046
            ≤ (2 : ℝ) ^ 107 * (2 : ℝ) ^ 72046 := mul_le_mul_of_nonneg_right hw2 (by positivity)
          _ = (2 : ℝ) ^ 72153 := by rw [← pow_add, show 107 + 72046 = 72153 by omega]
          _ ≤ (2 : ℝ) ^ 79999 := two_pow_le (by omega)
          _ ≤ (M : ℝ) := hM_ge79999
      rw [hsq_lhs, sq (M : ℝ)]; exact mul_le_mul_of_nonneg_right hcoeff_le hM_pos.le
    have hL_nn : 0 ≤ 4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 36023 * (2 * (wdScale : ℝ)) := (by positivity)
    have hkey : 4 * √(2 ^ n : ℝ) * (2 : ℝ) ^ 36023 * (2 * (wdScale : ℝ)) ≤ (M : ℝ) := by
      have hs := Real.sqrt_le_sqrt hsq_key; rwa [Real.sqrt_sq hL_nn, Real.sqrt_sq hM_pos.le] at hs
    have h2 : (4 * √(2 ^ n : ℝ)) * ((2 : ℝ) ^ 36023 / (M : ℝ)) ≤ 1 / (2 * (wdScale : ℝ)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hM_pos hwd_pos, one_mul]; exact hkey
    exact h1.trans h2
  have hterm2 : (K : ℝ) * ((2 : ℝ) ^ 36023 / (M : ℝ)) * vecNorm e ≤ 1 / (2 * (wdScale : ℝ)) := by
    calc (K : ℝ) * ((2 : ℝ) ^ 36023 / (M : ℝ)) * vecNorm e
        ≤ (K : ℝ) * ((2 : ℝ) ^ 36023 / (M : ℝ)) * 1 := mul_le_mul_of_nonneg_left he (by positivity)
      _ = (K : ℝ) * ((2 : ℝ) ^ 36023 / (M : ℝ)) := mul_one _
      _ ≤ 1 / (2 * (wdScale : ℝ)) := hK_bd
  exact htel.trans (add_le_add le_rfl hterm2)
/-- Non-asymptotic `K`-step trajectory convergence between `(dAltStepOrbMat (2 ^ n) m r) ^
  K`
  from `u0OrbVecGen (2 ^ n) m r` and `(taylor8Mat (1 / √(2 ^ n)) (dAltGenMat m r)) ^ K` from
  `e0`
  within `1 / wdScale = 10 ^ (-15)`. -/
theorem vecNorm_dAltStepOrbMat_pow_sub_taylor8_le {n m r K : ℕ} (hn : altN0 ≤ n) (hm1 : 1 ≤ m) (hm :
    m ≤ 8192) (hr1 : 1 ≤ r) (hr : r ≤ 1024) (hK : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ)) :
    let e0 : Fin (orbDim m r) → ℝ := Pi.single ⟨0, by unfold orbDim; omega⟩ 1
    vecNorm (((dAltStepOrbMat (2 ^ n) m r) ^ K) *ᵥ u0OrbVecGen (2 ^ n) m r - ((taylor8Mat (1 / √(2 ^
      n : ℝ)) (dAltGenMat m r)) ^ K) *ᵥ e0) ≤ 1 / (wdScale : ℝ) := by
  intro e0
  have he0_norm : vecNorm e0 = 1 := by
    unfold vecNorm vecSqNorm; let z0 : Fin (orbDim m r) := ⟨0, by unfold orbDim; omega⟩
    have he0_def : e0 = Pi.single z0 1 := rfl; rw [Finset.sum_eq_single z0]
    · rw [he0_def, Pi.single_eq_same, one_pow, Real.sqrt_one]
    · intro b _ hb; rw [he0_def, Pi.single_eq_of_ne hb, zero_pow two_ne_zero]
    · intro hz; exact absurd (Finset.mem_univ z0) hz
  have hv := vecNorm_dAltStepOrbMat_pow_sub_taylor8_vec_le hn hm1 hm hr1 hr hK
    (u := u0OrbVecGen (2 ^ n) m r) he0_norm.le
  have hu0 := vecNorm_u0OrbVecGen_sub_e0_le hn hm1 hm hr1 hr
  have hhalf : 1 / (2 * (wdScale : ℝ)) + 1 / (2 * (wdScale : ℝ)) = 1 / (wdScale : ℝ) := by
    have hne : (wdScale : ℝ) ≠ 0 := (by unfold wdScale; norm_num); field_simp [hne]; ring
  exact (hv.trans (add_le_add hu0 le_rfl)).trans (le_of_eq hhalf)
end
end QuantumComputation.Specs.DickeSol
/-
# Certified Integer `T_8` Horner Walk Evaluator & `JohnsonWalkSpec` Bridge
(`FindAllJohnsonAltStep`)

Connects the continuum tridiagonal skew generator `dAltGenMat` and the `K`-step trajectory
limit
`vecNorm_dAltStepOrbMat_pow_sub_taylor8_le` to fast, WHNF-safe integer certificate checkers
and
`JohnsonWalkSpec`:

1. **Primitive Kernel Evaluators (`strictConsInt`, `altIsqrt15`, `hornerZipLoop`,
   `altEvalRowLo12`, `checkAltDirectTable12`, `checkAltBound12`)**:
   All `decide +kernel` callcone functions use primitive `Nat.*` / `Int.*` / `Bool.*`
   operations
   with `strictConsInt` spine forcing and a single-pass `O(d)` zipper `hornerZipLoop`.
2. **Four-Term `ℓ_2` Trajectory & Horner Rounding Enclosure (`altEvalRowLo12_sound`)**:
   Combines continuum convergence (`1 / 10 ^ 15`), `q`-substep degree-`8` polynomial grouping
   (`truncPad15 / 10 ^ 15`), tridiagonal coupling quantization
   (`nSub * (2 * gCeil + 20) / 10 ^ 15`), and `8`-stage Euclidean-division Horner rounding
   (`66 * nSub / 10 ^ 15` for all `d ≤ 1024`) inside `totalPad15`.
3. **Turnkey `JohnsonWalkSpec` & Parallel Circuit Constructors (`altWalkSpecOf`,
   `altCellCircuit`, `altCell_correctness`, `altCell_rel_cost`)**:
   Instantiates `FindAllJohnsonP01.johnsonCircuit` with zero new Quantum Hoare Logic
   boilerplate,
   supporting both full-table `decide +kernel` checks and `checkAltDirectLoop_append` sub-band
   chaining across `1 ≤ m ≤ 8192` and `2 ≤ k ≤ 1024`.
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
open Real
open scoped Matrix NNRat NNReal ENNReal
/- ## Section 1: WHNF-Safe Kernel Primitives & Certificate Evaluators -/


namespace AltForce

/-- Forces the head constructor of a list before passing to `k` (`WHNF01`). -/
def withForcedList {α β : Type} (xs : List α) (k : List α → β) : β :=
  match xs with
  | [] => k []
  | h :: t => k (h :: t)
theorem withForcedNat_eq {α : Type} (x : ℕ) (k : ℕ → α) : withForcedNat x k = k x := by
  unfold withForcedNat; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]
theorem withForcedList_eq {α β : Type} (xs : List α) (k : List α → β) :
    withForcedList xs k = k xs := by
  cases xs <;> rfl
end AltForce









/-- WHNF-forced `(m: ℤ) - (n: ℤ)` avoiding double thunk evaluation (`0` closures). -/
def primSubNatNat (m n : ℕ) : ℤ :=
  match Nat.sub n m with
  | 0 => primOfNatForced (Nat.sub m n)
  | k + 1 => primNegSuccForced k
/-- WHNF-forced integer addition using primitive `Nat` kernel operations. -/
def primIntAdd : ℤ → ℤ → ℤ
  | Int.ofNat m, Int.ofNat n => primOfNatForced (Nat.add m n)
  | Int.ofNat m, Int.negSucc n => primSubNatNat m (Nat.add n 1)
  | Int.negSucc m, Int.ofNat n => primSubNatNat n (Nat.add m 1)
  | Int.negSucc m, Int.negSucc n => primNegSuccForced (Nat.add (Nat.add m n) 1)
/-- WHNF-forced integer negation using primitive `Nat` kernel operations. -/
def primIntNeg : ℤ → ℤ
  | Int.ofNat n => primNegOfNat n
  | Int.negSucc n => primOfNatForced (Nat.add n 1)
/-- WHNF-forced integer subtraction using primitive `Nat` kernel operations. -/
def primIntSub (a b : ℤ) : ℤ :=
  primIntAdd a (primIntNeg b)

/-- WHNF-forced Euclidean integer division by a positive `Nat` denominator. -/
def primIntEdivPos (x : ℤ) (dNat : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => primOfNatForced (Nat.div m dNat)
  | Int.negSucc m => primNegSuccForced (Nat.div m dNat)
/-- Structural `O(d)` zipper loop (`hb` first after `:` so `0` `WellFounded.fix` in kernel). -/
def hornerZipLoopAux (dNat : ℕ) : List ℤ → ℤ → List ℤ → List ℤ → List ℤ
  | [], prev, vec, cur =>
    match vec with
    | [v] =>
      match cur with
      | [_] => strictConsInt (primIntAdd v (primIntEdivPos prev dNat)) []
      | _ => []
    | _ => []
  | b :: hbRest, prev, vec, cur =>
    match vec with
    | v :: vRest =>
      match cur with
      | c :: curTail =>
        match curTail with
        | cNext :: _ =>
          strictConsInt (primIntAdd v (primIntEdivPos (primIntSub prev (primIntMul b cNext)) dNat))
            (hornerZipLoopAux dNat hbRest (primIntMul b c) vRest curTail)
        | [] => []
      | [] => []
    | [] => []
/-- Single-pass `O(d)` zipper loop computing one Horner stage `vec + (G_pt *ᵥ cur) // dNat`
  with primitive `Nat` kernel operations and `strictConsInt` spine forcing. -/
def hornerZipLoop (dNat : ℕ) (prev : ℤ) (hb vec cur : List ℤ) : List ℤ :=
  hornerZipLoopAux dNat hb prev vec cur
/-- Single degree-`deg` Horner stage on `10 ^ 15`-scaled `List ℤ` vectors. -/
def hornerStagePt (deg : ℕ) (hb vec cur : List ℤ) : List ℤ :=
  AltForce.withForcedNat (Nat.mul deg wdScale) fun dNat =>
    hornerZipLoop dNat (Int.ofNat 0) hb vec cur
/-- Eight-stage degree-`8` Horner step approximating `taylor8OfMat G_pt *ᵥ vec` on `List ℤ`. -/
def hornerT8StepPt (hb vec : List ℤ) : List ℤ :=
  let s7 := hornerStagePt 8 hb vec vec
  AltForce.withForcedList s7 fun c7 =>
  let s6 := hornerStagePt 7 hb vec c7
  AltForce.withForcedList s6 fun c6 =>
  let s5 := hornerStagePt 6 hb vec c6
  AltForce.withForcedList s5 fun c5 =>
  let s4 := hornerStagePt 5 hb vec c5
  AltForce.withForcedList s4 fun c4 =>
  let s3 := hornerStagePt 4 hb vec c4
  AltForce.withForcedList s3 fun c3 =>
  let s2 := hornerStagePt 3 hb vec c3
  AltForce.withForcedList s2 fun c2 =>
  let s1 := hornerStagePt 2 hb vec c2
  AltForce.withForcedList s1 fun c1 =>
  hornerStagePt 1 hb vec c1
/-- Iterates `hornerT8StepPt hb` across `nSub` macro-steps with spine forcing at every step. -/
def altIterSteps : ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, vec => vec
  | k + 1, hb, vec =>
    let stepVec := hornerT8StepPt hb vec
    AltForce.withForcedList stepVec fun vecNext =>
      altIterSteps k hb vecNext
/-- Ceiling product `⌈a * b / 10 ^ 15⌉` on `10 ^ 15`-scaled `Nat` values. -/
def altMulCeil15 (a b : ℕ) : ℕ :=
  Nat.div (Nat.add 999999999999999 (Nat.mul a b)) wdScale
/-- Iterated ceiling-product loop used by `altPow9Ceil15`. -/
def altPowCeilLoop : ℕ → ℕ → ℕ → ℕ
  | 0, acc, _ => acc
  | k + 1, acc, x => altPowCeilLoop k (altMulCeil15 acc x) x
/-- Certified `10 ^ 15`-scaled upper bound on `(x / 10 ^ 15) ^ 9`. -/
def altPow9Ceil15 (x : ℕ) : ℕ :=
  altPowCeilLoop 8 x x




/-- Builds a list of `k` integer zeros using primitive constructors. -/
def altZeroInts : ℕ → List ℤ
  | 0 => []
  | k + 1 => Int.ofNat 0 :: altZeroInts k
/-- Converts the `w = 1.. d` amplitude tail of `vecFinal` into `10 ^ 12`-scaled
  hit-probability
  lower bounds after subtracting `totalPad15`. -/
def altVecTailToLo12 (totalPad15 : ℕ) : List ℤ → List ℕ
  | [] => []
  | z :: zs =>
    let aLoRaw := Nat.sub (primIntNatAbs z) totalPad15
    AltForce.withForcedNat aLoRaw fun aLo =>
      let pLo15 := Nat.div (Nat.mul aLo aLo) wdScale
      let pLo12 := Nat.div pLo15 1000
      strictNatCons (Nat.sub pLo12 1) (altVecTailToLo12 totalPad15 zs)
/-- Certified `10 ^ 12`-scaled hit-probability lower-bound vector `[pLo(1),..., pLo(min m
  r)]`
  for `1`-stage `(D_{\text{alt}} Z_R)^K` at duration `tau9 / 10 ^ 9` across `nSub`
  macro-steps. -/
def altEvalRowLo12 (m r tau9 nSub : ℕ) : List ℕ :=
  let dRaw := bif Nat.ble m r then m else r
  AltForce.withForcedNat dRaw fun d =>
    let mxRaw := cond (Nat.ble m r) r m
    AltForce.withForcedNat mxRaw fun mx =>
      cond
        (Bool.or (primNatBlt d 1)
          (Bool.or (primNatBlt r 2)
          (Bool.or (primNatBlt 8192 m)
          (Bool.or (primNatBlt 1024 r)
          (Bool.or (Nat.beq tau9 0)
          (Bool.or (primNatBlt 4000000000 tau9)
          (Bool.or (Nat.beq nSub 0) (primNatBlt 16384 nSub))))))))
        []
        (let hPtRaw := Nat.div (Nat.mul tau9 1000000) nSub
        AltForce.withForcedNat hPtRaw fun hPt =>
          cond (primNatBlt hPt 1) []
            (let d1 := Nat.add d 1
            let gNormRaw := (altIsqrt15 (Nat.mul (Nat.mul 4 (Nat.mul d1 d1)) mx)).2
            AltForce.withForcedNat gNormRaw fun gNormHi15 =>
              let hgRaw := altMulCeil15 (Nat.add 2 hPt) gNormHi15
              AltForce.withForcedNat hgRaw fun hgHi15 =>
                cond
                  (Bool.or (primNatBlt 500000000000000 hgHi15)
                    (Bool.not (altCheckHbTight m r 0 d)))
                  []
                  (let hgPow := altPow9Ceil15 hgHi15
                  let truncPad15 := Nat.div (Nat.add 179999 (Nat.mul nSub hgPow)) 180000
                  let gCeil := Nat.div (Nat.add 999999999999999 gNormHi15) wdScale
                  let roundPad15 := Nat.add 256 (Nat.mul nSub (Nat.add 256 (Nat.mul 4 gCeil)))
                  let padRaw := Nat.add truncPad15 roundPad15
                  AltForce.withForcedNat padRaw fun totalPad15 =>
                    let hbRaw := altBuildHbFrom m r hPt 0 d
                    AltForce.withForcedList hbRaw fun hbPt =>
                      let vec0Raw := strictConsInt (Int.ofNat wdScale) (altZeroInts d)
                      AltForce.withForcedList vec0Raw fun vec0 =>
                        let vecFinal := altIterSteps nSub hbPt vec0
                        match vecFinal with
                        | [] => []
                        | _ :: tail => altVecTailToLo12 totalPad15 tail)))



/-- Single-pass `10 ^ 27`-scaled Bellman drift sum `∑_{w=1}^d rowLo12[w-1] * (vR -
  vHist[w-1])`. -/
def altDriftSum27 (vR : ℕ) : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | p :: ps, vhs =>
    match vhs with
    | [] => 0
    | vh :: vhsRest => Nat.add (Nat.mul p (Nat.sub vR vh)) (altDriftSum27 vR ps vhsRest)
/-- Structural helper for `checkAltDirectLoop` (`vRem` first after `:`, `0`
  `WellFounded.fix`). -/
def checkAltDirectLoopAux (m : ℕ) : List ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], _, _, tauRem, nsubRem =>
    match tauRem with
    | [] =>
      match nsubRem with
      | [] => true
      | _ :: _ => false
    | _ :: _ => false
  | vR :: vRest, r, vHist, tauRem, nsubRem =>
    match tauRem with
    | [] => false
    | tau9 :: tauRest =>
      match nsubRem with
      | [] => false
      | nSub :: nsubRest =>
        match vHist with
        | [] => false
        | vPrev :: _ =>
          cond (primNatBlt vR vPrev) false
            (let stepOk :=
              cond (Nat.beq tau9 0)
                (checkEigStep m r vR vPrev)
                (let dRaw := cond (Nat.ble m r) m r
                AltForce.withForcedNat dRaw fun d =>
                  let rowRaw := altEvalRowLo12 m r tau9 nSub
                  AltForce.withForcedList rowRaw fun rowLo12 =>
                    cond
                      (Bool.or (Bool.not (Nat.beq (altListLen rowLo12) d))
                        (Bool.or (Nat.beq (altSumNat rowLo12) 0)
                          (primNatBlt (altListLen vHist) d)))
                      false
                      (let drift27 := altDriftSum27 vR rowLo12 vHist
                      primNatBlt (Nat.mul tau9 1000000000000000000) drift27))
            cond stepOk
              (checkAltDirectLoopAux m vRest (Nat.add r 1) (vR :: vHist) tauRest nsubRest)
              false)
/-- Sub-band Bellman drift checker over `r, r + 1,...` with reverse potential history
  `vHist`. -/
def checkAltDirectLoop (m r : ℕ) (vHist vRem tauRem nsubRem : List ℕ) : Bool :=
  checkAltDirectLoopAux m vRem r vHist tauRem nsubRem
/-- Complete `1`-stage `D_{\text{alt}}` Bellman certificate table checker for `r = 0..
  kMax`. -/
def checkAltDirectTable12 (m kMax : ℕ) (vPot tau9Rows nsubRows : List ℕ) : Bool :=
  cond
    (Bool.or (primNatBlt m 1)
      (Bool.or (primNatBlt 8192 m)
      (Bool.or (primNatBlt kMax 2) (primNatBlt 1024 kMax))))
    false
    (cond
      (Bool.or (Bool.not (Nat.beq (altListLen vPot) (Nat.add kMax 1)))
        (Bool.or (Bool.not (Nat.beq (altListLen tau9Rows) (Nat.sub kMax 1)))
          (Bool.not (Nat.beq (altListLen nsubRows) (Nat.sub kMax 1)))))
      false
      (match vPot with
      | v0 :: v1 :: vRest =>
        cond (Bool.not (Nat.beq v0 0)) false
          (cond (checkEigStep m 1 v1 v0)
            (checkAltDirectLoop m 2 [v1, v0] vRest tau9Rows nsubRows)
            false)
      | _ => false))

/-- Macro-step-aligned query count `nSub * ((tau9 * Nat.sqrt N) / (nSub * 10 ^ 9))`. -/
def altStepCount (tau9 nSub N : ℕ) : ℕ :=
  nSub * ((tau9 * Nat.sqrt N) / (nSub * 1000000000))
/-- Single-stage `(D_{\text{alt}} Z_R)^K` symmetric walk list for `JohnsonWalkSpec`. -/
noncomputable def altStages (tau9 nSub m n : ℕ) :
    List (ℕ × SymOrthogonal (2 ^ n) m) :=
  if hm : 1 ≤ n ∧ 2 * m < 2 ^ n then
    [(altStepCount tau9 nSub (2 ^ n),
      SymOrthogonal.ofSymmInvolution (dAltSymMat (2 ^ n) m)
        (dAltSymMat_transpose (2 ^ n) m)
        (dAltSymMat_mul_self_two_pow hm.1 hm.2))]
  else []
/- ## Section 2: Primitive Bridge Lemmas & Scalar Bounds -/
private theorem altStep_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, altStep_nat_ble_eq_true]
private theorem altStep_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, altStep_nat_ble_eq_true]; omega
private theorem altStep_nat_blt_eq_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  unfold Nat.blt; exact altStep_nat_ble_eq_true
private theorem altStep_nat_blt_eq_false {a b : ℕ} : Nat.blt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, altStep_nat_blt_eq_true]; omega
private theorem altStep_primNatBlt_eq_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  unfold primNatBlt; exact altStep_nat_ble_eq_true
private theorem altStep_primNatBlt_eq_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, altStep_primNatBlt_eq_true]; omega
private theorem altStep_to_beq {u : ℕ → ℕ → Bool}
    (h : ∀ {a b : ℕ}, (u a b = true) = (a = b)) (a b : ℕ) : u a b = (a == b) := by
  rw [Bool.eq_iff_iff, h, beq_iff_eq]
private theorem altStep_nat_beq_eq_true {a b : ℕ} : (a == b) = true ↔ a = b :=
  beq_iff_eq
private theorem altStep_nat_beq_eq_false {a b : ℕ} : (a == b) = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, altStep_nat_beq_eq_true]
private theorem altStep_altListLen_eq : ∀ xs : List ℕ, altListLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (altStep_altListLen_eq xs)
private theorem altStep_bif_ble_min (m r : ℕ) : cond (Nat.ble m r) m r = min m r := by
  cases h : Nat.ble m r
  · simp [cond, Nat.min_eq_right (altStep_nat_ble_eq_false.mp h).le]
  · simp [cond, Nat.min_eq_left (altStep_nat_ble_eq_true.mp h)]
private theorem altStep_bif_ble_max (m r : ℕ) : cond (Nat.ble m r) r m = max m r := by
  cases h : Nat.ble m r
  · simp [cond, Nat.max_eq_left (altStep_nat_ble_eq_false.mp h).le]
  · simp [cond, Nat.max_eq_right (altStep_nat_ble_eq_true.mp h)]
private theorem altStep_cond_true {α : Type} (a b : α) : cond true a b = a := rfl
private theorem altStep_cond_false {α : Type} (a b : α) : cond false a b = b := rfl
private theorem altStep_wdScale_pos : 0 < wdScale := by unfold wdScale; omega
private theorem altStep_wdScaleR_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; norm_num
theorem strictConsInt_eq (x : ℤ) (xs : List ℤ) : strictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.ofNat 0] | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t) =
      Int.ofNat n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.negSucc 0] | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t) =
      Int.negSucc n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl
theorem strictNatCons_eq (x : ℕ) (xs : List ℕ) : strictNatCons x xs = x :: xs := by
  unfold strictNatCons; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]
  cases xs <;> rfl
theorem altIsqrt15_sound (val : ℕ) : ((altIsqrt15 val).1 : ℝ) / wdScaleR ≤ √(val : ℝ) ∧ √(val : ℝ)
    ≤ ((altIsqrt15 val).2 : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := altStep_wdScaleR_pos; unfold altIsqrt15
  rw [altStep_to_beq (fun {a b} ↦ Nat.beq_eq) val 0]
  cases h0 : (val == 0) with
  | true => rw [altStep_cond_true, altStep_nat_beq_eq_true.mp h0]; simp
  | false =>
    rw [altStep_cond_false]; simp only [AltForce.withForcedNat_eq]
    generalize altNewtonLoop 20 (Nat.mul val (Nat.mul wdScale wdScale)) (altInitGuess val) = x
    set target := Nat.mul val (Nat.mul wdScale wdScale); set x1 := Nat.add x 1
    have htarget_eq : (target : ℝ) = (val : ℝ) * wdScaleR ^ 2 := by
      change ((val * (wdScale * wdScale) : ℕ) : ℝ) = (val : ℝ) * wdScaleR ^ 2
      unfold wdScaleR; push_cast; ring
    clear_value target
    cases hok : Bool.and (Nat.ble (Nat.mul x x) target) (primNatBlt target (Nat.mul x1 x1)) with
    | false =>
      rw [altStep_cond_false]
      refine ⟨by simp only [Nat.cast_zero, zero_div]; exact Real.sqrt_nonneg _, ?_⟩
      have hmul_eq : ((Nat.mul val wdScale : ℕ) : ℝ) / wdScaleR = (val : ℝ) := by
        change ((val * wdScale : ℕ) : ℝ) / wdScaleR = (val : ℝ)
        unfold wdScaleR; push_cast; field_simp [hB.ne']
      rw [hmul_eq, Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
      have hle_nat : val ≤ val * val := Nat.le_mul_self val
      calc (val : ℝ) ≤ ((val * val : ℕ) : ℝ) := by exact_mod_cast hle_nat
        _ = (val : ℝ) ^ 2 := by push_cast; ring
    | true =>
      rw [altStep_cond_true]; simp only [Bool.and_eq_true] at hok
      have hx_le : x * x ≤ target := altStep_nat_ble_eq_true.mp hok.1
      have ht_lt : target < (x + 1) * (x + 1) := altStep_primNatBlt_eq_true.mp hok.2
      refine ⟨?_, ?_⟩
      · refine Real.le_sqrt_of_sq_le ?_
        have hxR : ((x * x : ℕ) : ℝ) ≤ (target : ℝ) := (by exact_mod_cast hx_le)
        rw [htarget_eq] at hxR; rw [div_pow, div_le_iff₀ (pow_pos hB 2)]
        calc (x : ℝ) ^ 2 = ((x * x : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (val : ℝ) * wdScaleR ^ 2 := hxR
      · rw [altStep_to_beq (fun {a b} ↦ Nat.beq_eq) (Nat.mul x x) target]
        cases heq : (Nat.mul x x == target) with
        | false =>
          rw [altStep_cond_false, Real.sqrt_le_iff]
          refine ⟨div_nonneg (Nat.cast_nonneg _) hB.le, ?_⟩
          have htR : (target : ℝ) ≤ (((x + 1) * (x + 1) : ℕ) : ℝ) := (by exact_mod_cast ht_lt.le)
          rw [htarget_eq] at htR; rw [div_pow, le_div_iff₀ (pow_pos hB 2)]
          calc (val : ℝ) * wdScaleR ^ 2 ≤ (((x + 1) * (x + 1) : ℕ) : ℝ) := htR
            _ = ((x1 : ℕ) : ℝ) ^ 2 := by dsimp [x1]; push_cast; ring
        | true =>
          rw [altStep_cond_true, Real.sqrt_le_iff]
          refine ⟨div_nonneg (Nat.cast_nonneg _) hB.le, ?_⟩
          have heq_nat : x * x = target := altStep_nat_beq_eq_true.mp heq
          have htR : (val : ℝ) * wdScaleR ^ 2 = ((x * x : ℕ) : ℝ) := by
            rw [← htarget_eq]; exact_mod_cast heq_nat.symm
          rw [div_pow, le_div_iff₀ (pow_pos hB 2), htR]
          calc ((x * x : ℕ) : ℝ) = (x : ℝ) ^ 2 := by push_cast; ring
            _ ≤ (x : ℝ) ^ 2 := le_rfl
private theorem altStep_sum_Icc_one_succ (k : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 (k + 1), f j) = (∑ j ∈ Finset.Icc 1 k, f j) + f (k + 1) := by
  have hset : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : k + 1 ∉ Finset.Icc 1 k := (by simp only [Finset.mem_Icc]; omega)
  rw [hset, Finset.sum_insert hnot, add_comm]
theorem harmSumLo15_le : ∀ k : ℕ, (harmSumLo15 k : ℝ) / wdScaleR ≤ groverHarmonicSqrtSum k
  | 0 => by
    unfold harmSumLo15 groverHarmonicSqrtSum
    have hset : Finset.Icc (1 : ℕ) 0 = ∅ := by ext x; simp
    rw [hset]; simp
  | k + 1 => by
    have hB : (0 : ℝ) < wdScaleR := altStep_wdScaleR_pos; unfold groverHarmonicSqrtSum
    rw [altStep_sum_Icc_one_succ]
    change (harmSumLo15 (k + 1) : ℝ) / wdScaleR ≤ groverHarmonicSqrtSum k + 1 / √((k + 1 : ℕ) : ℝ)
    have ih := harmSumLo15_le k; set hi := (altIsqrt15 (k + 1)).2
    have hhi_ge : √((k + 1 : ℕ) : ℝ) ≤ (hi : ℝ) / wdScaleR := (altIsqrt15_sound (k + 1)).2
    have hsq_pos : (0 : ℝ) < √((k + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos k)
    have hhi_posR : (0 : ℝ) < (hi : ℝ) := by
      have hdiv_pos : 0 < (hi : ℝ) / wdScaleR := lt_of_lt_of_le hsq_pos hhi_ge
      have hm_pos := mul_pos hdiv_pos hB
      rwa [div_mul_cancel₀ _ hB.ne'] at hm_pos
    set q := (wdScale * wdScale) / hi
    have hq_nat : q * hi ≤ wdScale * wdScale := Nat.div_mul_le_self _ _
    have hq_real : (q : ℝ) * (hi : ℝ) ≤ wdScaleR * wdScaleR := by
      unfold wdScaleR
      exact_mod_cast hq_nat
    have hstep_eq : harmSumLo15 (k + 1) = harmSumLo15 k + q := rfl
    clear_value hi q
    have hterm : (q : ℝ) / wdScaleR ≤ 1 / √((k + 1 : ℕ) : ℝ) := by
      calc (q : ℝ) / wdScaleR
          ≤ wdScaleR / (hi : ℝ) := by rw [div_le_div_iff₀ hB hhi_posR]; linarith
        _ = 1 / ((hi : ℝ) / wdScaleR) := by field_simp [hB.ne', hhi_posR.ne']
        _ ≤ 1 / √((k + 1 : ℕ) : ℝ) := one_div_le_one_div_of_le hsq_pos hhi_ge
    rw [hstep_eq, Nat.cast_add, add_div]; exact add_le_add ih hterm
private theorem altStep_ceil_div_mul_ge (n d : ℕ) (hd : 0 < d) : n ≤ (((d - 1) + n) / d) * d := by
  have h := Nat.lt_mul_div_succ ((d - 1) + n) hd; rw [Nat.mul_comm, Nat.succ_mul] at h; omega
private theorem altStep_altMulCeil15_ge (a b : ℕ) :
    ((a : ℝ) / wdScaleR) * ((b : ℝ) / wdScaleR) ≤ (altMulCeil15 a b : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := altStep_wdScaleR_pos
  have hnat : a * b ≤ altMulCeil15 a b * wdScale :=
    altStep_ceil_div_mul_ge (a * b) wdScale altStep_wdScale_pos
  have hreal : (a : ℝ) * (b : ℝ) ≤ (altMulCeil15 a b : ℝ) * wdScaleR := by
    unfold wdScaleR; exact_mod_cast hnat
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hB hB) hB]; nlinarith
private theorem altStep_altPowCeilLoop_zero (acc x : ℕ) : altPowCeilLoop 0 acc x = acc := rfl
private theorem altStep_altPowCeilLoop_succ (k acc x : ℕ) :
    altPowCeilLoop (k + 1) acc x = altPowCeilLoop k (altMulCeil15 acc x) x := rfl
private theorem altStep_altPowCeilLoop_ge (x : ℕ) : ∀ (k acc : ℕ) {p : ℝ}, 0 ≤ p → p ≤ (acc : ℝ) /
    wdScaleR → p * ((x : ℝ) / wdScaleR) ^ k ≤ (altPowCeilLoop k acc x : ℝ) / wdScaleR := by
  intro k
  induction k with
  | zero => intro acc p _ hacc; rw [altStep_altPowCeilLoop_zero, pow_zero, mul_one]; exact hacc
  | succ k ih =>
    intro acc p hp0 hacc; rw [altStep_altPowCeilLoop_succ]
    have hx0 : 0 ≤ (x : ℝ) / wdScaleR := div_nonneg (Nat.cast_nonneg x) altStep_wdScaleR_pos.le
    have hnext : p * ((x : ℝ) / wdScaleR) ≤ (altMulCeil15 acc x : ℝ) / wdScaleR :=
      (mul_le_mul_of_nonneg_right hacc hx0).trans (altStep_altMulCeil15_ge acc x)
    have hrec := ih (altMulCeil15 acc x) (mul_nonneg hp0 hx0) hnext; rwa [pow_succ', ← mul_assoc]
private theorem altStep_altPow9Ceil15_ge (x : ℕ) :
    ((x : ℝ) / wdScaleR) ^ 9 ≤ (altPow9Ceil15 x : ℝ) / wdScaleR := by
  have hx0 : 0 ≤ (x : ℝ) / wdScaleR := div_nonneg (Nat.cast_nonneg x) altStep_wdScaleR_pos.le
  have h := altStep_altPowCeilLoop_ge x 8 x hx0 le_rfl; unfold altPow9Ceil15; rwa [pow_succ']
private theorem altStep_altCheckHbTight_sound (m r : ℕ) :
    ∀ (rem w : ℕ), altCheckHbTight m r w rem = true → ∀ j < rem,
        (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤
          (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1 + 1
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, hchk, j, hj => by
    unfold altCheckHbTight altCheckHbTightAux at hchk; dsimp only at hchk
    generalize hp : altIsqrt15 (Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1))
      (Nat.sub m w)) (Nat.sub r w)) = p at hchk
    cases hble : Nat.ble p.2 (Nat.add p.1 1) with
    | false =>
      rw [hble, altStep_cond_false] at hchk; exact Bool.noConfusion hchk
    | true =>
      rw [hble, altStep_cond_true] at hchk
      rcases j with _ | j'
      · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w) := by
          change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) = 4 * (w + 1) * (m - w) * (r - w)
          simp
        rw [hrad, hp]; exact altStep_nat_ble_eq_true.mp hble
      · have ih := altStep_altCheckHbTight_sound m r rem (w + 1) hchk j' (by omega)
        simpa [show w + 1 + j' = w + (j' + 1) by omega] using ih
private theorem altStep_altBuildHbFrom_length (m r hPt : ℕ) :
    ∀ (rem w : ℕ), (altBuildHbFrom m r hPt w rem).length = rem
  | 0, _ => rfl
  | rem + 1, w => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    exact congrArg Nat.succ (altStep_altBuildHbFrom_length m r hPt rem (w + 1))
private theorem altStep_altBuildHbFrom_getD (m r hPt : ℕ) :
    ∀ (rem w j : ℕ), j < rem → (altBuildHbFrom m r hPt w rem).getD j 0 =
        (((hPt * (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1) /
          wdScale : ℕ) : ℤ)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, 0, _ => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    change (((hPt * (altIsqrt15 (4 * (w + 1) * (m - w) * (r - w))).1) / wdScale : ℕ) : ℤ) = _; simp
  | rem + 1, w, j + 1, hj => by
    dsimp only [altBuildHbFrom, altBuildHbFromAux]; rw [strictConsInt_eq, List.getD_cons_succ]
    have hw : Nat.add w 1 = w + 1 := rfl; rw [hw]
    have ih := altStep_altBuildHbFrom_getD m r hPt rem (w + 1) j (by omega)
    dsimp only [altBuildHbFrom] at ih
    simpa [show w + 1 + j = w + (j + 1) by omega] using ih
private theorem altStep_altZeroInts_length : ∀ k : ℕ, (altZeroInts k).length = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (altStep_altZeroInts_length k)
private theorem altStep_altZeroInts_getD : ∀ (k j : ℕ), (altZeroInts k).getD j 0 = 0
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | k + 1, j + 1 => altStep_altZeroInts_getD k j
theorem altStepCount_le_tau_sqrt (tau9 nSub N : ℕ) :
    (altStepCount tau9 nSub N : ℝ) ≤ ((tau9 : ℝ) / 1000000000) * √(N : ℝ) := by
  by_cases hn0 : nSub = 0
  · subst hn0; simp only [altStepCount, zero_mul, Nat.cast_zero]; positivity
  · have hmul : altStepCount tau9 nSub N * 1000000000 ≤ tau9 * Nat.sqrt N := by
      unfold altStepCount; set q := (tau9 * Nat.sqrt N) / (nSub * 1000000000)
      calc (nSub * q) * 1000000000
          = (nSub * 1000000000) * q := by ring
        _ ≤ tau9 * Nat.sqrt N := Nat.mul_div_le _ _
    have hmR : (altStepCount tau9 nSub N : ℝ) * 1000000000 ≤
        (tau9 : ℝ) * (Nat.sqrt N : ℝ) := by exact_mod_cast hmul
    have hsq : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hn := (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le N); simpa [sq, Nat.cast_mul] using hn
    have h2 : (tau9 : ℝ) * (Nat.sqrt N : ℝ) ≤ (tau9 : ℝ) * √(N : ℝ) :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg tau9)
    linarith
private theorem altStep_altStepCount_substep_bounds {n tau9 nSub : ℕ}
    (hn : altN0 ≤ n) (htau : tau9 ≤ 4000000000) (hnsub1 : 1 ≤ nSub) (hnsub : nSub ≤ 16384) :
    0 ≤ (((tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000) : ℕ) : ℝ) / √(2 ^ n : ℝ) ∧
      (((tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000) : ℕ) : ℝ) / √(2 ^ n : ℝ) ≤
        (((tau9 * 1000000) / nSub + 2 : ℕ) : ℝ) / wdScaleR ∧
      |(((tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000) : ℕ) : ℝ) / √(2 ^ n : ℝ) -
          (((tau9 * 1000000) / nSub : ℕ) : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
  set q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000); set hPt := (tau9 * 1000000) / nSub
  set N := 2 ^ n; have hN_cast : (2 : ℝ) ^ n = (N : ℝ) := (by dsimp [N]; norm_cast)
  rw [hN_cast]; have hn80 : 80000 ≤ n := hn
  have hN_ge : (2 : ℝ) ^ 200 ≤ (N : ℝ) := by
    dsimp [N]; rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (by omega : 200 ≤ n)
  have hsqrtN_ge : (2 : ℝ) ^ 100 ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hN_ge)
  have hsqrtN_pos : 0 < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsqrtN_ge
  have hnsub_pos : (0 : ℝ) < (nSub : ℝ) := (by exact_mod_cast hnsub1)
  have hB : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have hB_pos : (0 : ℝ) < wdScaleR := (by rw [hB]; positivity)
  -- Bound 1: hPt / S ≤ tau9 / (nSub * 10^9) ≤ (hPt + 1) / S
  have hhPt_lo : (hPt : ℝ) / wdScaleR ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hnat : hPt * nSub ≤ tau9 * 1000000 := Nat.div_mul_le_self _ _
    have hR : (hPt : ℝ) * (nSub : ℝ) ≤ (tau9 : ℝ) * 1000000 := (by exact_mod_cast hnat)
    rw [hB, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hhPt_hi : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) ≤ ((hPt + 1 : ℕ) : ℝ) / wdScaleR := by
    have hnat : tau9 * 1000000 < (hPt + 1) * nSub :=
      calc tau9 * 1000000 < nSub * (hPt + 1) := Nat.lt_mul_div_succ _ (by omega : 0 < nSub)
        _ = (hPt + 1) * nSub := Nat.mul_comm _ _
    have hR : (tau9 : ℝ) * 1000000 ≤ ((hPt + 1 : ℕ) : ℝ) * (nSub : ℝ) := (by exact_mod_cast hnat.le)
    rw [hB, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- Bound 2: q / √N ≤ tau9 / (nSub * 10^9) and tau9 / (nSub * 10^9) - q / √N ≤ 1 / S
  have hq_hi : (q : ℝ) / √(N : ℝ) ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hnat : (nSub * 1000000000) * q ≤ tau9 * Nat.sqrt N := Nat.mul_div_le _ _
    have hR : ((nSub : ℝ) * 1000000000) * (q : ℝ) ≤ (tau9 : ℝ) * (Nat.sqrt N : ℝ) := by
      exact_mod_cast hnat
    have hsq : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hn' := (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le N); simpa [sq, Nat.cast_mul] using hn'
    rw [div_le_div_iff₀ hsqrtN_pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg tau9)]
  have hq_lo : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) - (q : ℝ) / √(N : ℝ) ≤ 1 / wdScaleR := by
    set S_N := Nat.sqrt N
    have hS_gt : √(N : ℝ) ≤ (S_N : ℝ) + 1 := by
      rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
      have hlt := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N); push_cast at hlt; linarith
    have hdiv_lt : tau9 * S_N < (q + 1) * (nSub * 1000000000) :=
      calc tau9 * S_N < (nSub * 1000000000) * (q + 1) :=
            Nat.lt_mul_div_succ _ (by positivity : 0 < nSub * 1000000000)
        _ = (q + 1) * (nSub * 1000000000) := Nat.mul_comm _ _
    have hdivR : (tau9 : ℝ) * (S_N : ℝ) ≤ ((q : ℝ) + 1) * ((nSub : ℝ) * 1000000000) := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hdiv_lt.le; push_cast at hc; linarith
    have htauR : (tau9 : ℝ) ≤ 4000000000 := (by exact_mod_cast htau)
    have hnsubR : (nSub : ℝ) ≤ 16384 := (by exact_mod_cast hnsub)
    have hgap : (tau9 : ℝ) * √(N : ℝ) - (q : ℝ) * ((nSub : ℝ) * 1000000000) ≤ 20384000000000 := by
      nlinarith [mul_le_mul_of_nonneg_left hS_gt (Nat.cast_nonneg tau9)]
    have hbig : (20384000000000 : ℝ) * 1000000000000000 ≤
        ((nSub : ℝ) * 1000000000) * √(N : ℝ) := by
      have h1 : (20384000000000 : ℝ) * 1000000000000000 ≤ 1000000000 * (2 : ℝ) ^ 100 := by norm_num
      have h2 : (1 : ℝ) ≤ (nSub : ℝ) := (by exact_mod_cast hnsub1); nlinarith
    rw [hB, div_sub_div _ _ (by positivity) hsqrtN_pos.ne',
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨div_nonneg (Nat.cast_nonneg q) hsqrtN_pos.le, ?_, ?_⟩
  · refine hq_hi.trans (hhPt_hi.trans ?_)
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ _) hB_pos.le
  · rw [abs_le]; constructor
    · linarith [hhPt_lo, hq_lo]
    · have h1 : ((hPt + 1 : ℕ) : ℝ) / wdScaleR - (hPt : ℝ) / wdScaleR = 1 / wdScaleR := by
        push_cast; ring
      linarith [hq_hi, hhPt_hi, h1]
/- ## Section 3: `O(d)` Zipper `hornerZipLoop` & `8`-Stage Horner Rounding Soundness -/
private noncomputable def altStepListToOrbVec (d : ℕ) (xs : List ℤ) : Fin (d + 1) → ℝ :=
  fun a ↦ (xs.getD a.1 0 : ℝ) / wdScaleR
private noncomputable def altStepPtGenMat (d : ℕ) (hb : List ℤ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  tridiagSkewMat d (fun w ↦ (hb.getD w 0 : ℝ) / wdScaleR)
private noncomputable def altStepHornerStageReal {nDim : ℕ} (deg : ℕ)
    (X : Matrix (Fin nDim) (Fin nDim) ℝ) (u c : Fin nDim → ℝ) : Fin nDim → ℝ :=
  u + (1 / (deg : ℝ)) • (X *ᵥ c)
theorem primOfNatForced_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]
theorem primNegSuccForced_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]
theorem primIntNatAbs_eq (z : ℤ) : primIntNatAbs z = Int.natAbs z := by
  cases z <;> rfl
theorem primNegOfNat_eq (x : ℕ) : primNegOfNat x = -(x : ℤ) := by
  cases x with
  | zero => rfl
  | succ k => dsimp only [primNegOfNat]; rw [primNegSuccForced_eq]; rfl
theorem primSubNatNat_eq (m n : ℕ) : primSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  dsimp only [primSubNatNat]
  cases h : Nat.sub n m with
  | zero =>
    dsimp only; rw [primOfNatForced_eq]
    have hnm : n - m = 0 := h; have hmn : Int.ofNat (Nat.sub m n) = ((m - n : ℕ) : ℤ) := rfl
    rw [hmn]; omega
  | succ k =>
    dsimp only; rw [primNegSuccForced_eq]
    have hnm : n - m = k + 1 := h; have hneg : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := rfl
    rw [hneg]; omega
theorem primIntNeg_eq (a : ℤ) : primIntNeg a = -a := by
  cases a with
  | ofNat n => dsimp only [primIntNeg]; rw [primNegOfNat_eq]; rfl
  | negSucc n => dsimp only [primIntNeg]; rw [primOfNatForced_eq]; rfl
theorem primIntAdd_eq (a b : ℤ) : primIntAdd a b = a + b := by
  cases a with
  | ofNat m =>
    have hm : Int.ofNat m = (m : ℤ) := rfl
    cases b with
    | ofNat n =>
      have hn : Int.ofNat n = (n : ℤ) := rfl; dsimp only [primIntAdd]
      rw [primOfNatForced_eq]; have hc : Int.ofNat (Nat.add m n) = ((m + n : ℕ) : ℤ) := rfl
      rw [hc, hm, hn]; omega
    | negSucc n =>
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl; dsimp only [primIntAdd]
      rw [primSubNatNat_eq, hm, hn]; have hs : (Nat.add n 1 : ℤ) = ((n + 1 : ℕ) : ℤ) := rfl
      rw [hs]; omega
  | negSucc m =>
    have hm : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := rfl
    cases b with
    | ofNat n =>
      have hn : Int.ofNat n = (n : ℤ) := rfl; dsimp only [primIntAdd]
      rw [primSubNatNat_eq, hm, hn]; have hs : (Nat.add m 1 : ℤ) = ((m + 1 : ℕ) : ℤ) := rfl
      rw [hs]; omega
    | negSucc n =>
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl; dsimp only [primIntAdd]
      rw [primNegSuccForced_eq]
      have hc : Int.negSucc (Nat.add (Nat.add m n) 1) = -((m + n + 2 : ℕ) : ℤ) := rfl
      rw [hc, hm, hn]; omega
theorem primIntSub_eq (a b : ℤ) : primIntSub a b = a - b := by
  unfold primIntSub; rw [primIntAdd_eq, primIntNeg_eq]; omega
theorem primIntMul_eq (a b : ℤ) : primIntMul a b = a * b := by
  cases a with
  | ofNat m =>
    have hm : Int.ofNat m = (m : ℤ) := rfl
    cases b with
    | ofNat n =>
      have hn : Int.ofNat n = (n : ℤ) := rfl; dsimp only [primIntMul]
      rw [primOfNatForced_eq]; have hc : Int.ofNat (Nat.mul m n) = ((m * n : ℕ) : ℤ) := rfl
      rw [hc, hm, hn]; push_cast; ring
    | negSucc n =>
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl; dsimp only [primIntMul]
      rw [primNegOfNat_eq]; have hc : (Nat.mul m (Nat.add n 1) : ℤ) = ((m * (n + 1) : ℕ) : ℤ) := rfl
      rw [hc, hm, hn]; push_cast; ring
  | negSucc m =>
    have hm : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := rfl
    cases b with
    | ofNat n =>
      have hn : Int.ofNat n = (n : ℤ) := rfl; dsimp only [primIntMul]
      rw [primNegOfNat_eq]; have hc : (Nat.mul (Nat.add m 1) n : ℤ) = (((m + 1) * n : ℕ) : ℤ) := rfl
      rw [hc, hm, hn]; push_cast; ring
    | negSucc n =>
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl; dsimp only [primIntMul]
      rw [primOfNatForced_eq]; have hc : Int.ofNat (Nat.mul (Nat.add m 1) (Nat.add n 1)) =
          (((m + 1) * (n + 1) : ℕ) : ℤ) := rfl
      rw [hc, hm, hn]; push_cast; ring
theorem primIntEdivPos_eq (x : ℤ) {dNat : ℕ} (hd : 0 < dNat) :
    primIntEdivPos x dNat = x / (dNat : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  cases x with
  | ofNat m => dsimp only [primIntEdivPos]; rw [primOfNatForced_eq]; rfl
  | negSucc m => dsimp only [primIntEdivPos]; rw [primNegSuccForced_eq]; rfl
private theorem altStep_hornerZipLoop_length (dNat : ℕ) :
    ∀ (d : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      hb.length = d → vec.length = d + 1 → cur.length = d + 1 →
      (hornerZipLoop dNat prev hb vec cur).length = d + 1
  | 0, prev, [], [v], [c], _, _, _ => by
    dsimp only [hornerZipLoop, hornerZipLoopAux]; rw [strictConsInt_eq]; rfl
  | d + 1, prev, b :: hbRest, v :: vRest, c :: cNext :: cRest, hhb, hvec, hcur => by
    dsimp only [hornerZipLoop, hornerZipLoopAux]; rw [strictConsInt_eq]
    have ih := altStep_hornerZipLoop_length dNat d (primIntMul b c) hbRest vRest (cNext :: cRest)
      (by simpa using hhb) (by simpa using hvec) (by simpa using hcur)
    exact congrArg Nat.succ ih
private theorem altStep_hornerZipLoop_getD {dNat : ℕ} (hdNat : 0 < dNat) :
    ∀ (d : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      hb.length = d → vec.length = d + 1 → cur.length = d + 1 →
      ∀ j ≤ d, (hornerZipLoop dNat prev hb vec cur).getD j 0 = vec.getD j 0 +
            ((if j = 0 then prev else hb.getD (j - 1) 0 * cur.getD (j - 1) 0) -
              (if j < d then hb.getD j 0 * cur.getD (j + 1) 0 else 0)) / (dNat : ℤ)
  | 0, prev, [], [v], [c], _, _, _, j, hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    dsimp only [hornerZipLoop, hornerZipLoopAux]
    rw [strictConsInt_eq, List.getD_cons_zero, primIntAdd_eq, primIntEdivPos_eq _ hdNat]; simp
  | d + 1, prev, b :: hbRest, v :: vRest, c :: cNext :: cRest, hhb, hvec, hcur, 0, _ => by
    dsimp only [hornerZipLoop, hornerZipLoopAux]
    rw [strictConsInt_eq, List.getD_cons_zero, primIntAdd_eq, primIntEdivPos_eq _ hdNat,
      primIntSub_eq, primIntMul_eq]
    have hlt : 0 < d + 1 := Nat.succ_pos d
    simp only [↓reduceIte, hlt, List.getD_cons_zero, List.getD_cons_succ]
  | d + 1, prev, b :: hbRest, v :: vRest, c :: cNext :: cRest, hhb, hvec, hcur, j + 1, hj => by
    dsimp only [hornerZipLoop, hornerZipLoopAux]; rw [strictConsInt_eq, List.getD_cons_succ]
    have ih := altStep_hornerZipLoop_getD hdNat d (primIntMul b c) hbRest vRest (cNext :: cRest)
      (by simpa using hhb) (by simpa using hvec) (by simpa using hcur) j (by omega)
    dsimp only [hornerZipLoop] at ih; rw [ih, primIntMul_eq]
    simp only [List.getD_cons_succ, Nat.add_sub_cancel]; congr 1; congr 1
    rcases j with _ | j'
    · simp
    · simp
private theorem altStep_hornerStagePt_approx {deg d : ℕ} {hb vec cur : List ℤ} (hdeg : 1 ≤ deg)
    (hd : d ≤ 1024) (hhb : hb.length = d) (hvec : vec.length = d + 1) (hcur : cur.length = d + 1)
    : (hornerStagePt deg hb vec cur).length = d + 1 ∧ vecNorm (altStepListToOrbVec d
    (hornerStagePt deg hb vec cur) - altStepHornerStageReal deg (altStepPtGenMat d hb)
    (altStepListToOrbVec d vec) (altStepListToOrbVec d cur)) ≤ 33 / wdScaleR := by
  have hB_pos : (0 : ℝ) < wdScaleR := (by unfold wdScaleR wdScale; positivity)
  have hstage_eq : hornerStagePt deg hb vec cur = hornerZipLoop (deg * wdScale) 0 hb vec cur := by
    unfold hornerStagePt; rw [AltForce.withForcedNat_eq]; rfl
  have hdNat : 0 < deg * wdScale := (by unfold wdScale; omega)
  have hlen : (hornerStagePt deg hb vec cur).length = d + 1 := by
    rw [hstage_eq]; exact altStep_hornerZipLoop_length (deg * wdScale) d 0 hb vec cur hhb hvec hcur
  refine ⟨hlen, ?_⟩
  set out := hornerStagePt deg hb vec cur
  set diff := altStepListToOrbVec d out - altStepHornerStageReal deg (altStepPtGenMat d hb)
    (altStepListToOrbVec d vec) (altStepListToOrbVec d cur)
  have hentry (a : Fin (d + 1)) : |diff a| ≤ 1 / wdScaleR := by
    have ha_le : a.1 ≤ d := (by omega)
    have hget := altStep_hornerZipLoop_getD hdNat d 0 hb vec cur hhb hvec hcur a.1 ha_le
    set num : ℤ := (if a.1 = 0 then 0 else hb.getD (a.1 - 1) 0 * cur.getD (a.1 - 1) 0) - (if a.1 <
      d then hb.getD a.1 0 * cur.getD (a.1 + 1) 0 else 0)
    set D : ℤ := ((deg * wdScale : ℕ) : ℤ)
    have hD_pos : 0 < D := (by dsimp only [D]; exact_mod_cast hdNat)
    have hD_posR : (0 : ℝ) < (D : ℝ) := (by exact_mod_cast hD_pos)
    have hout_eq : out.getD a.1 0 = vec.getD a.1 0 + num / D := (by rw [hstage_eq]; exact hget)
    have hmat_eq : (altStepPtGenMat d hb *ᵥ altStepListToOrbVec d cur) a =
        (num : ℝ) / wdScaleR ^ 2 := by
      unfold altStepPtGenMat; rw [tridiagSkewMat_mulVec_apply]; dsimp only [num]
      by_cases ha0 : 0 < a.1
      · have hne0 : ¬(a.1 = 0) := (by omega); rw [dite_eq_left ha0, ite_eq_right hne0]
        by_cases had : a.1 < d
        · rw [dite_eq_left had, ite_eq_left had]; dsimp only [altStepListToOrbVec]
          push_cast; field_simp [hB_pos.ne']; ring
        · rw [dite_eq_right had, ite_eq_right had]; dsimp only [altStepListToOrbVec]
          push_cast; field_simp [hB_pos.ne']; ring
      · have heq0 : a.1 = 0 := (by omega); rw [dite_eq_right ha0, ite_eq_left heq0]
        by_cases had : a.1 < d
        · rw [dite_eq_left had, ite_eq_left had]; dsimp only [altStepListToOrbVec]
          push_cast; field_simp [hB_pos.ne']; ring
        · rw [dite_eq_right had, ite_eq_right had]; push_cast; field_simp [hB_pos.ne']; ring
    have hDR : (D : ℝ) = (deg : ℝ) * wdScaleR := (by dsimp [D]; unfold wdScaleR; push_cast; rfl)
    have hdeg_pos : (0 : ℝ) < (deg : ℝ) := (by exact_mod_cast hdeg)
    have hdiff_eq : diff a = ((num / D : ℤ) : ℝ) / wdScaleR -
        (num : ℝ) / ((D : ℝ) * wdScaleR) := by
      dsimp [diff, altStepListToOrbVec, altStepHornerStageReal]; rw [hout_eq, hmat_eq, hDR]
      push_cast; field_simp [hB_pos.ne', hdeg_pos.ne']; ring
    have hdiv_mod : D * (num / D) + num % D = num := Int.mul_ediv_add_emod num D
    have hmod0 : 0 ≤ num % D := Int.emod_nonneg num hD_pos.ne'
    have hmod_lt : num % D < D := Int.emod_lt_of_pos num hD_pos
    have hnumR : (num : ℝ) = (D : ℝ) * ((num / D : ℤ) : ℝ) + ((num % D : ℤ) : ℝ) := by
      have hc := congrArg (Int.cast (R := ℝ)) hdiv_mod.symm
      simpa [Int.cast_add, Int.cast_mul] using hc
    have hrem_eq : diff a = -(((num % D : ℤ) : ℝ) / ((D : ℝ) * wdScaleR)) := by
      rw [hdiff_eq, hnumR]; field_simp [hB_pos.ne', hD_posR.ne']; ring
    rw [hrem_eq, abs_neg, abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ (mul_pos hD_posR hB_pos) hB_pos]
    have hm_le : ((num % D : ℤ) : ℝ) ≤ (D : ℝ) := (by exact_mod_cast hmod_lt.le); nlinarith
  rw [vecNorm, Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
  have hsq_le (a : Fin (d + 1)) : (diff a) ^ 2 ≤ (1 / wdScaleR) ^ 2 := by
    have h1 := hentry a; rw [← sq_abs (diff a)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc vecSqNorm diff = ∑ a : Fin (d + 1), (diff a) ^ 2 := rfl
    _ ≤ ∑ _ : Fin (d + 1), (1 / wdScaleR) ^ 2 := Finset.sum_le_sum fun a _ ↦ hsq_le a
    _ = ((d + 1 : ℕ) : ℝ) * (1 / wdScaleR) ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (33 : ℝ) ^ 2 * (1 / wdScaleR) ^ 2 := by
        have hd33 : ((d + 1 : ℕ) : ℝ) ≤ (33 : ℝ) ^ 2 := by
          have : d + 1 ≤ 1089 := (by omega)
          calc ((d + 1 : ℕ) : ℝ) ≤ (1089 : ℝ) := by exact_mod_cast this
            _ = (33 : ℝ) ^ 2 := by norm_num
        exact mul_le_mul_of_nonneg_right hd33 (sq_nonneg _)
    _ = (33 / wdScaleR) ^ 2 := by ring
private theorem altStep_hornerStagePt_err_step {deg d : ℕ} {hb vec c : List ℤ} {cExact : Fin (d +
    1) → ℝ} {err : ℝ} (hdeg : 1 ≤ deg) (hd : d ≤ 1024) (hhb : hb.length = d) (hvec : vec.length =
    d + 1) (hc : c.length = d + 1) (hG : ∀ u, vecNorm (altStepPtGenMat d hb *ᵥ u) ≤ (1 / 2) *
    vecNorm u) (herr : vecNorm (altStepListToOrbVec d c - cExact) ≤ err) : (hornerStagePt deg hb
    vec c).length = d + 1 ∧ vecNorm (altStepListToOrbVec d (hornerStagePt deg hb vec c) -
    altStepHornerStageReal deg (altStepPtGenMat d hb) (altStepListToOrbVec d vec) cExact) ≤ (1 /
    2) * err + 33 / wdScaleR := by
  obtain ⟨hlen, hstage⟩ := altStep_hornerStagePt_approx hdeg hd hhb hvec hc; refine ⟨hlen, ?_⟩
  set u := altStepListToOrbVec d vec; set cInt := altStepListToOrbVec d c
  set outInt := altStepListToOrbVec d (hornerStagePt deg hb vec c)
  have hsplit : outInt - altStepHornerStageReal deg (altStepPtGenMat d hb) u cExact =
      (outInt - altStepHornerStageReal deg (altStepPtGenMat d hb) u cInt) +
        (1 / (deg : ℝ)) • (altStepPtGenMat d hb *ᵥ (cInt - cExact)) := by
    ext i
    simp only [altStepHornerStageReal, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]; ring
  have hdeg_le1 : 1 / (deg : ℝ) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (deg : ℝ) := (by exact_mod_cast hdeg)
    exact div_le_one_of_le₀ h1 (by positivity)
  have hprop : vecNorm ((1 / (deg : ℝ)) • (altStepPtGenMat d hb *ᵥ (cInt - cExact))) ≤
      (1 / 2) * err := by
    rw [vecNorm_smul, abs_of_nonneg (by positivity)]
    calc (1 / (deg : ℝ)) * vecNorm (altStepPtGenMat d hb *ᵥ (cInt - cExact))
        ≤ 1 * vecNorm (altStepPtGenMat d hb *ᵥ (cInt - cExact)) :=
          mul_le_mul_of_nonneg_right hdeg_le1 (vecNorm_nonneg _)
      _ = vecNorm (altStepPtGenMat d hb *ᵥ (cInt - cExact)) := one_mul _
      _ ≤ (1 / 2) * vecNorm (cInt - cExact) := hG _
      _ ≤ (1 / 2) * err := mul_le_mul_of_nonneg_left herr (by norm_num)
  rw [hsplit]
  linarith [vecNorm_add_le (outInt - altStepHornerStageReal deg (altStepPtGenMat d hb) u cInt)
    ((1 / (deg : ℝ)) • (altStepPtGenMat d hb *ᵥ (cInt - cExact))), hstage, hprop]
private theorem altStep_hornerT8Real_eq_taylor8OfMat {nDim : ℕ}
    (X : Matrix (Fin nDim) (Fin nDim) ℝ) (u : Fin nDim → ℝ) :
    let c7 := altStepHornerStageReal 8 X u u; let c6 := altStepHornerStageReal 7 X u c7
    let c5 := altStepHornerStageReal 6 X u c6; let c4 := altStepHornerStageReal 5 X u c5
    let c3 := altStepHornerStageReal 4 X u c4; let c2 := altStepHornerStageReal 3 X u c3
    let c1 := altStepHornerStageReal 2 X u c2
    altStepHornerStageReal 1 X u c1 = taylor8OfMat X *ᵥ u := by
  intro c7 c6 c5 c4 c3 c2 c1; let y : ℕ → Fin nDim → ℝ := fun k ↦ (X ^ k) *ᵥ u
  have hy0 : u = y 0 := (by simp [y])
  have hy_mul (k : ℕ) (a : ℝ) : X *ᵥ (a • y k) = a • y (k + 1) := by
    dsimp [y]; rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ']
  have hy_mul1 (k : ℕ) : X *ᵥ y k = y (k + 1) := by
    dsimp [y]; rw [Matrix.mulVec_mulVec, ← pow_succ']
  have hc7 : c7 = y 0 + ((1 / 8 : ℝ)) • y 1 := by
    dsimp [c7, altStepHornerStageReal]; rw [hy0, hy_mul1]
  have hc6 : c6 = y 0 + (1 / 7 : ℝ) • y 1 + (1 / 56 : ℝ) • y 2 := by
    dsimp [c6, altStepHornerStageReal]; rw [hc7, hy0]
    simp only [Matrix.mulVec_add, hy_mul, hy_mul1, smul_add, smul_smul]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hc5 : c5 = y 0 + (1 / 6 : ℝ) • y 1 + (1 / 42 : ℝ) • y 2 + (1 / 336 : ℝ) • y 3 := by
    dsimp [c5, altStepHornerStageReal]; rw [hc6, hy0]
    simp only [Matrix.mulVec_add, hy_mul, hy_mul1, smul_add, smul_smul]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hc4 : c4 = y 0 + (1 / 5 : ℝ) • y 1 + (1 / 30 : ℝ) • y 2 + (1 / 210 : ℝ) • y 3 +
      (1 / 1680 : ℝ) • y 4 := by
    dsimp [c4, altStepHornerStageReal]; rw [hc5, hy0]
    simp only [Matrix.mulVec_add, hy_mul, hy_mul1, smul_add, smul_smul]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hc3 : c3 = y 0 + (1 / 4 : ℝ) • y 1 + (1 / 20 : ℝ) • y 2 + (1 / 120 : ℝ) • y 3 +
      (1 / 840 : ℝ) • y 4 + (1 / 6720 : ℝ) • y 5 := by
    dsimp [c3, altStepHornerStageReal]; rw [hc4, hy0]
    simp only [Matrix.mulVec_add, hy_mul, hy_mul1, smul_add, smul_smul]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hc2 : c2 = y 0 + (1 / 3 : ℝ) • y 1 + (1 / 12 : ℝ) • y 2 + (1 / 60 : ℝ) • y 3 +
      (1 / 360 : ℝ) • y 4 + (1 / 2520 : ℝ) • y 5 + (1 / 20160 : ℝ) • y 6 := by
    dsimp [c2, altStepHornerStageReal]; rw [hc3, hy0]
    simp only [Matrix.mulVec_add, hy_mul, hy_mul1, smul_add, smul_smul]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hc1 : c1 = y 0 + (1 / 2 : ℝ) • y 1 + (1 / 6 : ℝ) • y 2 + (1 / 24 : ℝ) • y 3 + (1 / 120 : ℝ)
    • y 4 + (1 / 720 : ℝ) • y 5 + (1 / 5040 : ℝ) • y 6 + (1 / 40320 : ℝ) • y 7 := by
    dsimp [c1, altStepHornerStageReal]; rw [hc2, hy0]
    simp only [Matrix.mulVec_add, hy_mul, hy_mul1, smul_add, smul_smul]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  dsimp [altStepHornerStageReal]; rw [hc1, hy0]; unfold taylor8OfMat
  simp only [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.smul_mulVec,
    hy_mul, hy_mul1, smul_add, smul_smul]
  dsimp only [y]; simp only [pow_zero, Matrix.one_mulVec]; ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
private theorem altStep_hornerT8StepPt_approx {d : ℕ} {hb vec : List ℤ} (hd : d ≤ 1024) (hhb :
    hb.length = d) (hvec : vec.length = d + 1) (hG : ∀ u, vecNorm (altStepPtGenMat d hb *ᵥ u) ≤ (1
    / 2) * vecNorm u) : (hornerT8StepPt hb vec).length = d + 1 ∧ vecNorm (altStepListToOrbVec d
    (hornerT8StepPt hb vec) - taylor8OfMat (altStepPtGenMat d hb) *ᵥ altStepListToOrbVec d vec) ≤
    66 / wdScaleR := by
  unfold hornerT8StepPt; simp only [AltForce.withForcedList_eq]
  have h0 : vecNorm (altStepListToOrbVec d vec - altStepListToOrbVec d vec) ≤ 0 := by
    simp [vecNorm_zero]
  obtain ⟨hl7, he7⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 8) hd hhb hvec hvec hG h0
  obtain ⟨hl6, he6⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 7) hd hhb hvec hl7 hG he7
  obtain ⟨hl5, he5⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 6) hd hhb hvec hl6 hG he6
  obtain ⟨hl4, he4⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 5) hd hhb hvec hl5 hG he5
  obtain ⟨hl3, he3⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 4) hd hhb hvec hl4 hG he4
  obtain ⟨hl2, he2⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 3) hd hhb hvec hl3 hG he3
  obtain ⟨hl1, he1⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 2) hd hhb hvec hl2 hG he2
  obtain ⟨hl0, he0⟩ := altStep_hornerStagePt_err_step (by omega : 1 ≤ 1) hd hhb hvec hl1 hG he1
  rw [altStep_hornerT8Real_eq_taylor8OfMat] at he0
  have hB : (0 : ℝ) < wdScaleR := (by unfold wdScaleR wdScale; positivity)
  refine ⟨hl0, he0.trans ?_⟩
  have hnum : (1 / 2 : ℝ) * ((1 / 2) * ((1 / 2) * ((1 / 2) * ((1 / 2) *
      ((1 / 2) * ((1 / 2) * ((1 / 2) * 0 + 33 / wdScaleR) + 33 / wdScaleR) + 33 / wdScaleR) +
      33 / wdScaleR) + 33 / wdScaleR) + 33 / wdScaleR) + 33 / wdScaleR) + 33 / wdScaleR =
      (8415 / 128 : ℝ) / wdScaleR := by ring
  rw [hnum, div_le_div_iff₀ hB hB]; linarith
private theorem altStep_altIterSteps_approx {d : ℕ} {hb : List ℤ}
    (hd : d ≤ 1024) (hhb : hb.length = d)
    (hG : ∀ u, vecNorm (altStepPtGenMat d hb *ᵥ u) ≤ (1 / 2) * vecNorm u) :
    ∀ (s : ℕ) (vec : List ℤ), vec.length = d + 1 → (altIterSteps s hb vec).length = d + 1 ∧
        vecNorm (altStepListToOrbVec d (altIterSteps s hb vec) -
          ((taylor8OfMat (altStepPtGenMat d hb)) ^ s) *ᵥ altStepListToOrbVec d vec) ≤
          (66 * (s : ℝ)) / wdScaleR
  | 0, vec, hvec => by
    simp [altIterSteps, hvec, pow_zero, Matrix.one_mulVec, vecNorm_zero]
  | s + 1, vec, hvec => by
    unfold altIterSteps
    simp only [AltForce.withForcedList_eq]
    obtain ⟨hl1, he1⟩ := altStep_hornerT8StepPt_approx hd hhb hvec hG
    obtain ⟨hls, hes⟩ := altStep_altIterSteps_approx hd hhb hG s (hornerT8StepPt hb vec) hl1
    refine ⟨hls, ?_⟩
    set B := taylor8OfMat (altStepPtGenMat d hb)
    have hskew : (altStepPtGenMat d hb)ᵀ = -altStepPtGenMat d hb := tridiagSkewMat_transpose d _
    have hG1 (u : Fin (d + 1) → ℝ) : vecNorm (altStepPtGenMat d hb *ᵥ u) ≤ vecNorm u :=
      (hG u).trans (by linarith [vecNorm_nonneg u])
    have hBs_contr (w : Fin (d + 1) → ℝ) : vecNorm ((B ^ s) *ᵥ w) ≤ vecNorm w := by
      have hB_contr (u : Fin (d + 1) → ℝ) : vecNorm (B *ᵥ u) ≤ 1 * vecNorm u := by
        rw [one_mul]; exact vecNorm_taylor8OfMat_mulVec_le hskew hG1 u
      simpa using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) hB_contr s w
    have hsplit : altStepListToOrbVec d (altIterSteps s hb (hornerT8StepPt hb vec)) -
        (B ^ (s + 1)) *ᵥ altStepListToOrbVec d vec =
        (altStepListToOrbVec d (altIterSteps s hb (hornerT8StepPt hb vec)) -
          (B ^ s) *ᵥ altStepListToOrbVec d (hornerT8StepPt hb vec)) +
        (B ^ s) *ᵥ (altStepListToOrbVec d (hornerT8StepPt hb vec) -
          B *ᵥ altStepListToOrbVec d vec) := by
      rw [pow_succ, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [hsplit]
    calc vecNorm ((altStepListToOrbVec d (altIterSteps s hb (hornerT8StepPt hb vec)) -
            (B ^ s) *ᵥ altStepListToOrbVec d (hornerT8StepPt hb vec)) +
            (B ^ s) *ᵥ (altStepListToOrbVec d (hornerT8StepPt hb vec) -
              B *ᵥ altStepListToOrbVec d vec))
        ≤ vecNorm (altStepListToOrbVec d (altIterSteps s hb (hornerT8StepPt hb vec)) -
            (B ^ s) *ᵥ altStepListToOrbVec d (hornerT8StepPt hb vec)) +
            vecNorm ((B ^ s) *ᵥ
              (altStepListToOrbVec d (hornerT8StepPt hb vec) - B *ᵥ altStepListToOrbVec d vec)) :=
          vecNorm_add_le _ _
      _ ≤ (66 * (s : ℝ)) / wdScaleR + 66 / wdScaleR :=
          add_le_add hes ((hBs_contr _).trans he1)
      _ = (66 * ((s + 1 : ℕ) : ℝ)) / wdScaleR := by push_cast; ring
/- ## Section 4: Four-Term Trajectory & Horner Soundness of `altEvalRowLo12` -/
private theorem altStep_altVecTailToLo12_length (pad : ℕ) :
    ∀ zs : List ℤ, (altVecTailToLo12 pad zs).length = zs.length
  | [] => rfl
  | z :: zs => by
    unfold altVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact congrArg Nat.succ (altStep_altVecTailToLo12_length pad zs)
private theorem altStep_altVecTailToLo12_getD (pad : ℕ) :
    ∀ (zs : List ℤ) (j : ℕ), j < zs.length → (altVecTailToLo12 pad zs).getD j 0 =
        ((((Int.natAbs (zs.getD j 0) - pad) * (Int.natAbs (zs.getD j 0) - pad)) /
          wdScale) / 1000) - 1
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | z :: zs, 0, _ => by
    unfold altVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq, primIntNatAbs_eq]
    rfl
  | z :: zs, j + 1, hj => by
    unfold altVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact altStep_altVecTailToLo12_getD pad zs j (by simp at hj; omega)
private theorem altStep_cast_natAbs_eq_abs (z : ℤ) : ((Int.natAbs z : ℕ) : ℝ) = |(z : ℝ)| := by
  cases z with
  | ofNat n =>
    change ((n : ℕ) : ℝ) = |((n : ℕ) : ℝ)|; exact (abs_of_nonneg (Nat.cast_nonneg n)).symm
  | negSucc n =>
    have hneg : (Int.negSucc n : ℝ) = -((n + 1 : ℕ) : ℝ) := (by push_cast; ring)
    rw [hneg, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; rfl
private theorem altStep_altVecTailToLo12_entry_le {pad : ℕ} {z : ℤ} {u : ℝ}
    (herr : |u - (z : ℝ) / wdScaleR| ≤ (pad : ℝ) / wdScaleR) :
    (((((Int.natAbs z - pad) * (Int.natAbs z - pad)) / wdScale) / 1000 - 1 : ℕ) : ℝ) /
        1000000000000 ≤ u ^ 2 := by
  have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have hB : (0 : ℝ) < wdScaleR := (by rw [hB_eq]; positivity)
  set aLo : ℕ := Int.natAbs z - pad; set pLo15 : ℕ := (aLo * aLo) / wdScale
  set pLo12 : ℕ := pLo15 / 1000; set out : ℕ := pLo12 - 1
  have haLo_le : (aLo : ℝ) / wdScaleR ≤ |u| := by
    by_cases hle : Int.natAbs z ≤ pad
    · have ha0 : aLo = 0 := Nat.sub_eq_zero_of_le hle; rw [ha0, Nat.cast_zero, zero_div]
      exact abs_nonneg u
    · have hgt : pad < Int.natAbs z := (by omega)
      have haR : (aLo : ℝ) = |(z : ℝ)| - (pad : ℝ) := by
        dsimp [aLo]; rw [Nat.cast_sub hgt.le, altStep_cast_natAbs_eq_abs]
      have habs := abs_le.mp herr
      have hu_ge : |(z : ℝ)| / wdScaleR - (pad : ℝ) / wdScaleR ≤ |u| := by
        rcases le_total 0 (z : ℝ) with hz0 | hz0
        · rw [abs_of_nonneg hz0]; have h1 : u ≤ |u| := le_abs_self u; linarith [habs.1]
        · rw [abs_of_nonpos hz0]; have h1 : -u ≤ |u| := neg_le_abs u
          have hneg_div : -(z : ℝ) / wdScaleR = -((z : ℝ) / wdScaleR) := neg_div _ _
          linarith [habs.2, hneg_div]
      rwa [haR, sub_div]
  have hsq_le : ((aLo : ℝ) / wdScaleR) ^ 2 ≤ u ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) haLo_le 2; rwa [sq_abs] at h1
  have hout_le : out ≤ pLo12 := Nat.sub_le _ _
  have hp12_le : pLo12 * 1000 ≤ pLo15 := Nat.div_mul_le_self _ _
  have hp15_le : pLo15 * wdScale ≤ aLo * aLo := Nat.div_mul_le_self _ _
  have hchain_nat : (out * 1000) * wdScale ≤ aLo * aLo := by
    calc (out * 1000) * wdScale
        ≤ (pLo12 * 1000) * wdScale := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hout_le)
      _ ≤ pLo15 * wdScale := Nat.mul_le_mul_right _ hp12_le
      _ ≤ aLo * aLo := hp15_le
  have hchainR : ((out : ℝ) * 1000) * wdScaleR ≤ (aLo : ℝ) ^ 2 := by
    have hc : (((out * 1000) * wdScale : ℕ) : ℝ) ≤ ((aLo * aLo : ℕ) : ℝ) := by
      exact_mod_cast hchain_nat
    unfold wdScaleR
    calc ((out : ℝ) * 1000) * (wdScale : ℝ)
        = (((out * 1000) * wdScale : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((aLo * aLo : ℕ) : ℝ) := hc
      _ = (aLo : ℝ) ^ 2 := by push_cast; ring
  have hdiv_le : (out : ℝ) / 1000000000000 ≤ ((aLo : ℝ) / wdScaleR) ^ 2 := by
    rw [div_pow, hB_eq, div_le_div_iff₀ (by norm_num) (by norm_num)]
    rw [hB_eq] at hchainR; linarith
  exact hdiv_le.trans hsq_le
private theorem altStep_altEvalRowLo12_eq (m r tau9 nSub : ℕ) : altEvalRowLo12 m r tau9 nSub =
      let d := min m r; let mx := max m r
      cond
        (Bool.or (primNatBlt d 1) (Bool.or (primNatBlt r 2)
          (Bool.or (primNatBlt 8192 m) (Bool.or (primNatBlt 1024 r)
          (Bool.or (tau9 == 0) (Bool.or (primNatBlt 4000000000 tau9)
          (Bool.or (nSub == 0) (primNatBlt 16384 nSub))))))))
        []
        (let hPt := (tau9 * 1000000) / nSub
        cond (primNatBlt hPt 1) []
          (let gNormHi15 := (altIsqrt15 (4 * ((d + 1) * (d + 1)) * mx)).2
          let hgHi15 := altMulCeil15 (2 + hPt) gNormHi15
          cond (Bool.or (primNatBlt 500000000000000 hgHi15) (Bool.not (altCheckHbTight m r 0 d))) []
            (let hgPow := altPow9Ceil15 hgHi15
            let truncPad15 := (179999 + nSub * hgPow) / 180000
            let gCeil := (999999999999999 + gNormHi15) / wdScale
            let roundPad15 := 256 + nSub * (256 + 4 * gCeil)
            let totalPad15 := truncPad15 + roundPad15
            let hbPt := altBuildHbFrom m r hPt 0 d
            let vec0 : List ℤ := (wdScale : ℤ) :: altZeroInts d
            let vecFinal := altIterSteps nSub hbPt vec0
            match vecFinal with
            | [] => []
            | _ :: tail => altVecTailToLo12 totalPad15 tail))) := by
  unfold altEvalRowLo12
  simp only [AltForce.withForcedNat_eq, AltForce.withForcedList_eq, strictConsInt_eq,
    altStep_bif_ble_min, altStep_bif_ble_max, altStep_to_beq (fun {a b} ↦ Nat.beq_eq)]
  rfl
/-- Soundness of `altEvalRowLo12`: every certified entry `w ∈ Icc 1 (min m r)` is a valid
  `10 ^ 12`-scaled lower bound on `symHitProb R` after `altStepCount tau9 nSub (2 ^ n)`
  steps of
  `D_{\text{alt}} Z_R` for all `n ≥ altN0`. -/
theorem altEvalRowLo12_sound {n m r tau9 nSub : ℕ} (hn : altN0 ≤ n) (hd1 : 1 ≤ min m r) (hlen :
    (altEvalRowLo12 m r tau9 nSub).length = min m r) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    {w : ℕ} (hw1 : 1 ≤ w) (hwd : w ≤ min m r) : (((altEvalRowLo12 m r tau9 nSub).getD (w - 1) 0 :
    ℝ) / 1000000000000) ≤ symHitProb R (evalSymStages R (altStages tau9 nSub m n) (u0Vec (2 ^ n)
    m)) w := by
  have hlen_pos : 0 < (altEvalRowLo12 m r tau9 nSub).length := (by omega)
  have heval := altStep_altEvalRowLo12_eq m r tau9 nSub; dsimp only at heval
  set d := min m r; set mx := max m r
  cases hg : Bool.or (primNatBlt d 1)
      (Bool.or (primNatBlt r 2) (Bool.or (primNatBlt 8192 m)
      (Bool.or (primNatBlt 1024 r) (Bool.or (tau9 == 0) (Bool.or (primNatBlt 4000000000 tau9)
      (Bool.or (nSub == 0) (primNatBlt 16384 nSub))))))) with
  | true => rw [hg, altStep_cond_true] at heval; rw [heval] at hlen_pos; simp at hlen_pos
  | false =>
    rw [hg, altStep_cond_false] at heval
    simp only [Bool.or_eq_false_iff, altStep_primNatBlt_eq_false, altStep_nat_beq_eq_false] at hg
    obtain ⟨_, hr2, hm_hi, hr_hi, ht0, htau_hi, hn0, hnsub_hi⟩ := hg
    have htau1 : 1 ≤ tau9 := Nat.pos_of_ne_zero ht0
    have hnsub1 : 1 ≤ nSub := Nat.pos_of_ne_zero hn0
    have hm1 : 1 ≤ m := le_trans hd1 (Nat.min_le_left m r); have hr1 : 1 ≤ r := (by omega)
    have hd_hi : d ≤ 1024 := (Nat.min_le_right m r).trans hr_hi; set hPt := (tau9 * 1000000) / nSub
    cases hh : primNatBlt hPt 1 with
    | true => rw [hh, altStep_cond_true] at heval; rw [heval] at hlen_pos; simp at hlen_pos
    | false =>
      rw [hh, altStep_cond_false] at heval
      have hhPt1 : 1 ≤ hPt := altStep_primNatBlt_eq_false.mp hh
      set gNormHi15 := (altIsqrt15 (4 * ((d + 1) * (d + 1)) * mx)).2
      set hgHi15 := altMulCeil15 (2 + hPt) gNormHi15
      cases hm_chk : Bool.or (primNatBlt 500000000000000 hgHi15)
          (Bool.not (altCheckHbTight m r 0 d)) with
      | true => rw [hm_chk, altStep_cond_true] at heval; rw [heval] at hlen_pos; simp at hlen_pos
      | false =>
        rw [hm_chk, altStep_cond_false] at heval
        simp only [Bool.or_eq_false_iff, altStep_primNatBlt_eq_false, Bool.not_eq_false'] at hm_chk
        obtain ⟨hhg_le, htight⟩ := hm_chk; set hgPow := altPow9Ceil15 hgHi15
        set truncPad15 := (179999 + nSub * hgPow) / 180000
        set gCeil := (999999999999999 + gNormHi15) / wdScale
        set roundPad15 := 256 + nSub * (256 + 4 * gCeil); set totalPad15 := truncPad15 + roundPad15
        set hbPt := altBuildHbFrom m r hPt 0 d; set vec0 : List ℤ := (wdScale : ℤ) :: altZeroInts d
        set vecFinal := altIterSteps nSub hbPt vec0
        have heval_cons (vHead : ℤ) (tail : List ℤ) (hvf : vecFinal = vHead :: tail) :
            altEvalRowLo12 m r tau9 nSub = altVecTailToLo12 totalPad15 tail := by
          have h1 := heval
          dsimp only [d, mx, hPt, gNormHi15, hgHi15, hgPow, truncPad15, gCeil, roundPad15,
            totalPad15, hbPt, vec0, vecFinal] at h1 hvf ⊢
          rw [hvf] at h1; exact h1
        clear heval
        -- Dimension & scale setup
        have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
        have hB_pos : (0 : ℝ) < wdScaleR := altStep_wdScaleR_pos; have hn_num : 80000 ≤ n := hn
        have h1_le_n : 1 ≤ n := (by omega)
        have hpow15 : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
        have h32768 : 32768 = 2 ^ 15 := (by norm_num); have h2mN : 2 * m < 2 ^ n := (by omega)
        have hmrN : m + r ≤ 2 ^ n := (by omega)
        have hN_pos : (0 : ℝ) < (2 ^ n : ℝ) := (by positivity)
        have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := Real.sqrt_pos.mpr hN_pos
        set q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
        set K := altStepCount tau9 nSub (2 ^ n)
        have hK_def : K = altStepCount tau9 nSub (2 ^ n) := rfl; have hK_eq : K = nSub * q := rfl
        have hK_le : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ) := by
          have h1 := altStepCount_le_tau_sqrt tau9 nSub (2 ^ n); push_cast at h1
          have htauR : (tau9 : ℝ) / 1000000000 ≤ 4 := by
            have hc : (tau9 : ℝ) ≤ 4000000000 := (by exact_mod_cast htau_hi); linarith
          exact h1.trans (mul_le_mul_of_nonneg_right htauR hsN_pos.le)
        -- Extract all scalar bounds BEFORE clearing heavy Nat definitions from context
        set G := dAltGenMat m r; set B_norm := (gNormHi15 : ℝ) / wdScaleR
        have hG_le_B : dAltGenNormBound m r ≤ B_norm := by
          unfold dAltGenNormBound; have hs := (altIsqrt15_sound (4 * ((d + 1) * (d + 1)) * mx)).2
          simpa [d, mx, sq] using hs
        have hB_norm_nn : 0 ≤ B_norm := div_nonneg (Nat.cast_nonneg _) hB_pos.le
        have hgCeil_ge : B_norm ≤ (gCeil : ℝ) := by
          have hnat : gNormHi15 ≤ gCeil * wdScale :=
            altStep_ceil_div_mul_ge gNormHi15 wdScale altStep_wdScale_pos
          have hR : (gNormHi15 : ℝ) ≤ (gCeil : ℝ) * wdScaleR := by
            unfold wdScaleR; exact_mod_cast hnat
          rwa [div_le_iff₀ hB_pos]
        have hmul_hg : (((2 + hPt : ℕ) : ℝ) / wdScaleR) * B_norm ≤ (hgHi15 : ℝ) / wdScaleR :=
          altStep_altMulCeil15_ge (2 + hPt) gNormHi15
        have hpow9_hg : ((hgHi15 : ℝ) / wdScaleR) ^ 9 ≤ (hgPow : ℝ) / wdScaleR :=
          altStep_altPow9Ceil15_ge hgHi15
        have hnat_trunc : nSub * hgPow ≤ truncPad15 * 180000 :=
          altStep_ceil_div_mul_ge (nSub * hgPow) 180000 (by omega)
        have hpadR : (totalPad15 : ℝ) = (truncPad15 : ℝ) +
            ((nSub : ℝ) * (4 * (gCeil : ℝ) + 256) + 256) := by
          dsimp only [totalPad15, roundPad15]; push_cast; ring
        have hhg_half : (hgHi15 : ℝ) / wdScaleR ≤ 1 / 2 := by
          rw [hB_eq, div_le_div_iff₀ (by norm_num) (by norm_num)]
          have hc : (hgHi15 : ℝ) ≤ 500000000000000 := (by exact_mod_cast hhg_le); linarith
        clear_value gNormHi15 hgHi15 hgPow truncPad15 gCeil roundPad15 totalPad15 B_norm
        have hG_op (u : Fin (orbDim m r) → ℝ) : vecNorm (G *ᵥ u) ≤ B_norm * vecNorm u :=
          (vecNorm_dAltGenMat_mulVec_le m r u).trans
            (mul_le_mul_of_nonneg_right hG_le_B (vecNorm_nonneg u))
        -- Substep size h_real = q * η
        set η : ℝ := 1 / √(2 ^ n : ℝ); have hη_nn : 0 ≤ η := (by positivity)
        set h_real : ℝ := (q : ℝ) * η
        have hsub_bds := altStep_altStepCount_substep_bounds hn htau_hi hnsub1 hnsub_hi
        have hh_nn : 0 ≤ h_real := mul_nonneg (Nat.cast_nonneg _) hη_nn
        have hh_hi : h_real ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR := by
          have h1 : h_real ≤ ((hPt + 2 : ℕ) : ℝ) / wdScaleR := by
            dsimp [h_real, η, q, hPt]; simpa [div_eq_mul_inv] using hsub_bds.2.1
          rwa [Nat.add_comm hPt 2] at h1
        have hh_diff : |h_real - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
          dsimp [h_real, η, q, hPt]; simpa [div_eq_mul_inv] using hsub_bds.2.2
        have hhPt_le4 : (hPt : ℝ) / wdScaleR ≤ 4 := by
          have hnat : hPt ≤ 4000000000 * 1000000 := by
            dsimp only [hPt]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _ htau_hi)
          rw [hB_eq, div_le_iff₀ (by norm_num)]
          have hR : (hPt : ℝ) ≤ 4000000000000000 := (by exact_mod_cast hnat); linarith
        clear_value hPt
        have hhB_le_hg : h_real * B_norm ≤ (hgHi15 : ℝ) / wdScaleR :=
          (mul_le_mul_of_nonneg_right hh_hi hB_norm_nn).trans hmul_hg
        have hhB_half : h_real * B_norm ≤ 1 / 2 := hhB_le_hg.trans hhg_half
        -- Initial basis vector e0 = altStepListToOrbVec d vec0
        let z0 : Fin (orbDim m r) := ⟨0, by unfold orbDim; omega⟩
        let e0 : Fin (orbDim m r) → ℝ := Pi.single z0 1
        have he0_norm : vecNorm e0 = 1 := by
          unfold vecNorm vecSqNorm; rw [Finset.sum_eq_single z0]
          · dsimp only [e0]; rw [Pi.single_eq_same, one_pow, Real.sqrt_one]
          · intro b _ hb; dsimp only [e0]; rw [Pi.single_eq_of_ne hb, zero_pow two_ne_zero]
          · intro hz; exact absurd (Finset.mem_univ z0) hz
        have hvec0_eq : altStepListToOrbVec d vec0 = e0 := by
          ext ⟨j, hj⟩; rcases j with _ | j'
          · have hbz : (⟨0, hj⟩ : Fin (orbDim m r)) = z0 := rfl; rw [hbz]
            change ((vec0.getD 0 0 : ℝ) / wdScaleR) = e0 z0
            dsimp only [vec0, e0, List.getD_cons_zero]; rw [Pi.single_eq_same]
            unfold wdScaleR wdScale; norm_num
          · have hne : (⟨j' + 1, hj⟩ : Fin (orbDim m r)) ≠ z0 :=
              fun h ↦ Nat.succ_ne_zero j' (congrArg Fin.val h)
            change ((vec0.getD (j' + 1) 0 : ℝ) / wdScaleR) = e0 ⟨j' + 1, hj⟩; dsimp only [vec0, e0]
            rw [List.getD_cons_succ, altStep_altZeroInts_getD, Pi.single_eq_of_ne hne]; simp
        -- Term 1: Continuum trajectory limit
        have hterm1 : vecNorm (((dAltStepOrbMat (2 ^ n) m r) ^ K) *ᵥ u0OrbVecGen (2 ^ n) m r -
            ((taylor8Mat η G) ^ K) *ᵥ e0) ≤ 1 / wdScaleR := by
          simpa [wdScaleR, η, G, e0, z0] using
            vecNorm_dAltStepOrbMat_pow_sub_taylor8_le hn hm1 hm_hi hr1 hr_hi hK_le
        -- Term 2: Substep grouping (`K = nSub * q`)
        set A_mac := (taylor8Mat η G) ^ q; set B_mac := taylor8Mat h_real G
        have hA_mac_contr (x : Fin (orbDim m r) → ℝ) : vecNorm (A_mac *ᵥ x) ≤ vecNorm x := by
          by_cases hq0 : q = 0
          · have hA0 : A_mac = 1 := (by dsimp only [A_mac]; rw [hq0, pow_zero])
            rw [hA0, Matrix.one_mulVec]
          · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq0
            have hηB1 : η * B_norm ≤ 1 := by
              have h1 : 1 * (η * B_norm) ≤ (q : ℝ) * (η * B_norm) := mul_le_mul_of_nonneg_right
                (by exact_mod_cast hq_pos) (mul_nonneg hη_nn hB_norm_nn)
              have h2 : (q : ℝ) * (η * B_norm) = h_real * B_norm := (by dsimp [h_real]; ring)
              linarith
            have h1step (u : Fin (orbDim m r) → ℝ) :
                vecNorm (taylor8Mat η G *ᵥ u) ≤ 1 * vecNorm u := by
              rw [one_mul]; exact vecNorm_taylor8Mat_mulVec_le (dAltGenMat_transpose m r)
                hη_nn hB_norm_nn hG_op hηB1 u
            simpa [A_mac] using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) h1step q x
        have hB_mac_contr (x : Fin (orbDim m r) → ℝ) : vecNorm (B_mac *ᵥ x) ≤ vecNorm x :=
          vecNorm_taylor8Mat_mulVec_le (dAltGenMat_transpose m r) hh_nn hB_norm_nn hG_op
            (by linarith) x
        have hmac_diff (x : Fin (orbDim m r) → ℝ) :
            vecNorm ((A_mac - B_mac) *ᵥ x) ≤ ((hgPow : ℝ) / (180000 * wdScaleR)) * vecNorm x := by
          have hsub := vecNorm_taylor8Mat_substep_le (dAltGenMat_transpose m r) hη_nn hB_norm_nn
            hG_op q hhB_half x
          have hpow9 : (h_real * B_norm) ^ 9 ≤ (hgPow : ℝ) / wdScaleR :=
            (pow_le_pow_left₀ (mul_nonneg hh_nn hB_norm_nn) hhB_le_hg 9).trans hpow9_hg
          have hdiv9 : (h_real * B_norm) ^ 9 / 180000 ≤ (hgPow : ℝ) / (180000 * wdScaleR) := by
            have h1 := div_le_div_of_nonneg_right hpow9 (by norm_num : (0 : ℝ) ≤ 180000)
            rwa [div_div, mul_comm wdScaleR 180000] at h1
          exact hsub.trans (mul_le_mul_of_nonneg_right hdiv9 (vecNorm_nonneg x))
        have hterm2 : vecNorm (((taylor8Mat η G) ^ K) *ᵥ e0 - (B_mac ^ nSub) *ᵥ e0) ≤
            (truncPad15 : ℝ) / wdScaleR := by
          have hpow_mul : (taylor8Mat η G) ^ K = A_mac ^ nSub := by
            rw [hK_eq, mul_comm nSub q, pow_mul]
          rw [hpow_mul]
          have htel := vecNorm_pow_mulVec_sub_le hA_mac_contr hB_mac_contr (by positivity)
            hmac_diff nSub e0 e0
          rw [sub_self, vecNorm_zero, zero_add, he0_norm, mul_one] at htel; refine htel.trans ?_
          have hR : (nSub : ℝ) * (hgPow : ℝ) ≤ (truncPad15 : ℝ) * 180000 := by
            exact_mod_cast hnat_trunc
          rw [show (nSub : ℝ) * ((hgPow : ℝ) / (180000 * wdScaleR)) =
              ((nSub : ℝ) * (hgPow : ℝ)) / (180000 * wdScaleR) by ring,
            div_le_div_iff₀ (mul_pos (by norm_num) hB_pos) hB_pos]
          have hmul := mul_le_mul_of_nonneg_right hR hB_pos.le; linarith
        -- Term 3: Quantized generator `altStepPtGenMat d hbPt` vs `h_real • G`
        have hhb_len : hbPt.length = d := altStep_altBuildHbFrom_length m r hPt d 0
        have hhb_get (j : ℕ) (hj : j < d) : hbPt.getD j 0 = (((hPt * (altIsqrt15 (4 * (j + 1) *
          (m - j) * (r - j))).1) / wdScale : ℕ) : ℤ) := by
          simpa using altStep_altBuildHbFrom_getD m r hPt d 0 j hj
        have hvec0_len : vec0.length = d + 1 := by
          dsimp [vec0]; exact congrArg Nat.succ (altStep_altZeroInts_length d)
        have hvf_def : vecFinal = altIterSteps nSub hbPt vec0 := rfl
        clear_value hbPt vec0 vecFinal
        have hGpt_op (u : Fin (d + 1) → ℝ) :
            vecNorm (altStepPtGenMat d hbPt *ᵥ u) ≤ (1 / 2) * vecNorm u := by
          have hb_le (j : ℕ) (hj : j < d) : |(hbPt.getD j 0 : ℝ) / wdScaleR| ≤ 1 / 4 := by
            have hget' := hhb_get j hj; set rad := 4 * (j + 1) * (m - j) * (r - j)
            set sq := (altIsqrt15 rad).1
            have hsq_le_c : (sq : ℝ) / wdScaleR ≤ dAltCoupling m r j := by
              unfold dAltCoupling; exact (altIsqrt15_sound rad).1
            clear_value sq rad
            set qProd := (hPt * sq) / wdScale; have hget_q : hbPt.getD j 0 = (qProd : ℤ) := hget'
            have hnat : qProd * wdScale ≤ hPt * sq := Nat.div_mul_le_self _ _
            clear_value qProd; clear hget'
            rw [hget_q, Int.cast_natCast, abs_of_nonneg (by positivity)]
            have h1 : (qProd : ℝ) / wdScaleR ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) := by
              have hR : (qProd : ℝ) * wdScaleR ≤ (hPt : ℝ) * (sq : ℝ) := by
                unfold wdScaleR; exact_mod_cast hnat
              rw [div_mul_div_comm, div_le_div_iff₀ hB_pos (mul_pos hB_pos hB_pos)]
              have hmul := mul_le_mul_of_nonneg_right hR hB_pos.le; linarith
            have hc_le : dAltCoupling m r j ≤ (1 / 2) * B_norm := (dAltCoupling_le_half_normBound
              hj).trans (mul_le_mul_of_nonneg_left hG_le_B (by norm_num))
            have hhPt_le : (hPt : ℝ) / wdScaleR ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR :=
              div_le_div_of_nonneg_right (by exact_mod_cast (by omega : hPt ≤ 2 + hPt)) hB_pos.le
            calc (qProd : ℝ) / wdScaleR ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) := h1
              _ ≤ (((2 + hPt : ℕ) : ℝ) / wdScaleR) * ((1 / 2) * B_norm) :=
                mul_le_mul hhPt_le (hsq_le_c.trans hc_le) (by positivity) (by positivity)
              _ = (1 / 2) * ((((2 + hPt : ℕ) : ℝ) / wdScaleR) * B_norm) := by ring
              _ ≤ (1 / 2) * ((hgHi15 : ℝ) / wdScaleR) :=
                mul_le_mul_of_nonneg_left hmul_hg (by norm_num)
              _ ≤ (1 / 2) * (1 / 2) := mul_le_mul_of_nonneg_left hhg_half (by norm_num)
              _ = 1 / 4 := by norm_num
          have h := vecNorm_tridiagSkewMat_mulVec_le (by norm_num : (0 : ℝ) ≤ 1 / 4) hb_le u
          rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at h; exact h
        have hGdiff_op (u : Fin (d + 1) → ℝ) : vecNorm ((h_real • G - altStepPtGenMat d hbPt) *ᵥ
          u) ≤ (((gCeil : ℝ) + 10) / wdScaleR) * vecNorm u := by
          have hsub_mat : h_real • G - altStepPtGenMat d hbPt = tridiagSkewMat d (fun j ↦ h_real *
            dAltCoupling m r j - (hbPt.getD j 0 : ℝ) / wdScaleR) := tridiagSkewMat_smul_sub d
            h_real (dAltCoupling m r) _
          rw [hsub_mat]; have hcoupl_diff (j : ℕ) (hj : j < d) :
              |h_real * dAltCoupling m r j - (hbPt.getD j 0 : ℝ) / wdScaleR| ≤
                ((1 / 2 : ℝ) * (gCeil : ℝ) + 5) / wdScaleR := by
            have hget' := hhb_get j hj; set rad := 4 * (j + 1) * (m - j) * (r - j)
            set sq := (altIsqrt15 rad).1
            have hlo_sq : (sq : ℝ) / wdScaleR ≤ dAltCoupling m r j := (altIsqrt15_sound rad).1
            have hhi_sq : dAltCoupling m r j ≤ ((sq + 1 : ℕ) : ℝ) / wdScaleR := by
              have htight_j : (altIsqrt15 rad).2 ≤ sq + 1 := by
                simpa [rad, sq] using altStep_altCheckHbTight_sound m r d 0 htight j hj
              exact (altIsqrt15_sound rad).2.trans
                (div_le_div_of_nonneg_right (by exact_mod_cast htight_j) hB_pos.le)
            clear_value sq rad
            set qProd := (hPt * sq) / wdScale; have hget_q : hbPt.getD j 0 = (qProd : ℤ) := hget'
            have hlo_nat : qProd * wdScale ≤ hPt * sq := Nat.div_mul_le_self _ _
            have hhi_nat : hPt * sq < (qProd + 1) * wdScale :=
              calc hPt * sq < wdScale * (qProd + 1) := Nat.lt_mul_div_succ _ altStep_wdScale_pos
                _ = (qProd + 1) * wdScale := Nat.mul_comm _ _
            have hloR : (qProd : ℝ) * wdScaleR ≤ (hPt : ℝ) * (sq : ℝ) := by
              unfold wdScaleR; exact_mod_cast hlo_nat
            have hhiR : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd + 1 : ℕ) : ℝ) * wdScaleR := by
              unfold wdScaleR; exact_mod_cast hhi_nat.le
            clear_value qProd; clear hget'
            rw [hget_q, Int.cast_natCast]
            have hc_nn : 0 ≤ dAltCoupling m r j := (by unfold dAltCoupling; positivity)
            have hc_le : dAltCoupling m r j ≤ (1 / 2) * (gCeil : ℝ) :=
              (dAltCoupling_le_half_normBound hj).trans
                (mul_le_mul_of_nonneg_left (hG_le_B.trans hgCeil_ge) (by norm_num))
            have hsq_diff : |dAltCoupling m r j - (sq : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
              rw [abs_of_nonneg (by linarith)]
              have h1 : ((sq + 1 : ℕ) : ℝ) / wdScaleR - (sq : ℝ) / wdScaleR = 1 / wdScaleR := by
                push_cast; ring
              linarith
            have hdiv_err : |((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) -
                (qProd : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
              have hlo_num : (qProd : ℝ) * 1000000000000000 ≤ (hPt : ℝ) * (sq : ℝ) := by
                rwa [hB_eq] at hloR
              have hhi_num : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd : ℝ) + 1) * 1000000000000000 := by
                have h1 := hhiR; rw [hB_eq] at h1; push_cast at h1; exact h1
              rw [hB_eq, div_mul_div_comm]; have hdiff_nn : 0 ≤ ((hPt : ℝ) * (sq : ℝ)) /
                  (1000000000000000 * 1000000000000000) - (qProd : ℝ) / 1000000000000000 := by
                linarith
              rw [abs_of_nonneg hdiff_nn]; linarith
            have hsplit3 : h_real * dAltCoupling m r j - (qProd : ℝ) / wdScaleR =
                (h_real - (hPt : ℝ) / wdScaleR) * dAltCoupling m r j +
                ((hPt : ℝ) / wdScaleR) * (dAltCoupling m r j - (sq : ℝ) / wdScaleR) +
                (((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) -
                  (qProd : ℝ) / wdScaleR) := by ring
            rw [hsplit3]
            have ht1 : |(h_real - (hPt : ℝ) / wdScaleR) * dAltCoupling m r j| ≤
                (1 / wdScaleR) * ((1 / 2) * (gCeil : ℝ)) := by
              rw [abs_mul, abs_of_nonneg hc_nn]
              exact mul_le_mul hh_diff hc_le hc_nn (by positivity)
            have ht2 : |((hPt : ℝ) / wdScaleR) * (dAltCoupling m r j - (sq : ℝ) / wdScaleR)| ≤
                4 * (1 / wdScaleR) := by
              rw [abs_mul, abs_of_nonneg (by positivity)]
              exact mul_le_mul hhPt_le4 hsq_diff (abs_nonneg _) (by norm_num)
            have habs3 := abs_add_three ((h_real - (hPt : ℝ) / wdScaleR) * dAltCoupling m r j)
              (((hPt : ℝ) / wdScaleR) * (dAltCoupling m r j - (sq : ℝ) / wdScaleR)) (((hPt : ℝ) /
              wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR)
            refine habs3.trans ((add_le_add (add_le_add ht1 ht2) hdiv_err).trans (le_of_eq ?_))
            ring
          have h := vecNorm_tridiagSkewMat_mulVec_le (by positivity) hcoupl_diff u
          refine h.trans (le_of_eq ?_)
          ring
        set B_pt := taylor8OfMat (altStepPtGenMat d hbPt)
        have hB_pt_contr (x : Fin (d + 1) → ℝ) : vecNorm (B_pt *ᵥ x) ≤ vecNorm x := by
          have hG1 (u : Fin (d + 1) → ℝ) : vecNorm (altStepPtGenMat d hbPt *ᵥ u) ≤ vecNorm u :=
            (hGpt_op u).trans (by linarith [vecNorm_nonneg u])
          exact vecNorm_taylor8OfMat_mulVec_le
            (tridiagSkewMat_transpose d (fun j ↦ (hbPt.getD j 0 : ℝ) / wdScaleR)) hG1 x
        have hterm3 : vecNorm ((B_mac ^ nSub) *ᵥ e0 - (B_pt ^ nSub) *ᵥ e0) ≤
            ((nSub : ℝ) * (2 * (gCeil : ℝ) + 20)) / wdScaleR := by
          have hhG_half (u : Fin (d + 1) → ℝ) :
              vecNorm ((h_real • G) *ᵥ u) ≤ (1 / 2) * vecNorm u := by
            rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg hh_nn]
            calc h_real * vecNorm (G *ᵥ u)
                ≤ h_real * (B_norm * vecNorm u) := mul_le_mul_of_nonneg_left (hG_op u) hh_nn
              _ = (h_real * B_norm) * vecNorm u := by ring
              _ ≤ (1 / 2) * vecNorm u := mul_le_mul_of_nonneg_right hhB_half (vecNorm_nonneg u)
          have h1mac (u : Fin (d + 1) → ℝ) : vecNorm ((B_mac - B_pt) *ᵥ u) ≤ ((2 * (gCeil : ℝ) +
            20) / wdScaleR) * vecNorm u := by
            have h := vecNorm_taylor8OfMat_sub_mulVec_le hhG_half hGpt_op (by positivity)
              hGdiff_op u
            refine h.trans (le_of_eq ?_)
            ring
          have htel := vecNorm_pow_mulVec_sub_le hB_mac_contr hB_pt_contr (by positivity)
            h1mac nSub e0 e0
          rw [sub_self, vecNorm_zero, zero_add, he0_norm, mul_one] at htel
          refine htel.trans (le_of_eq ?_)
          ring
        -- Term 4: `8`-stage Horner rounding across `nSub` macro-steps
        obtain ⟨hvf_len_raw, hterm4_raw⟩ :=
          altStep_altIterSteps_approx hd_hi hhb_len hGpt_op nSub vec0 hvec0_len
        rw [← hvf_def] at hvf_len_raw hterm4_raw
        have hvf_len : vecFinal.length = d + 1 := hvf_len_raw; rw [hvec0_eq] at hterm4_raw
        change vecNorm (altStepListToOrbVec d vecFinal - (B_pt ^ nSub) *ᵥ e0) ≤
            (66 * (nSub : ℝ)) / wdScaleR at hterm4_raw
        clear_value q K G η h_real A_mac B_mac B_pt
        -- Combine all four `vecNorm` bounds
        set uWalk := ((dAltStepOrbMat (2 ^ n) m r) ^ K) *ᵥ u0OrbVecGen (2 ^ n) m r
        set uInt := altStepListToOrbVec d vecFinal
        have htotal_norm : vecNorm (uWalk - uInt) ≤ (totalPad15 : ℝ) / wdScaleR := by
          let v1 := uWalk - ((taylor8Mat η G) ^ K) *ᵥ e0
          let v2 := ((taylor8Mat η G) ^ K) *ᵥ e0 - (B_mac ^ nSub) *ᵥ e0
          let v3 := (B_mac ^ nSub) *ᵥ e0 - (B_pt ^ nSub) *ᵥ e0; let v4 := (B_pt ^ nSub) *ᵥ e0 - uInt
          have hdecomp : uWalk - uInt = v1 + v2 + v3 + v4 := by
            dsimp only [v1, v2, v3, v4]; ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
          have hv1 : vecNorm v1 ≤ 1 / wdScaleR := hterm1
          have hv2 : vecNorm v2 ≤ (truncPad15 : ℝ) / wdScaleR := hterm2
          have hv3 : vecNorm v3 ≤ ((nSub : ℝ) * (2 * (gCeil : ℝ) + 20)) / wdScaleR := hterm3
          have hv4 : vecNorm v4 ≤ (66 * (nSub : ℝ)) / wdScaleR := by
            dsimp only [v4]; rw [← vecNorm_neg, neg_sub]; exact hterm4_raw
          have htri1 : vecNorm (v1 + v2) ≤ vecNorm v1 + vecNorm v2 := vecNorm_add_le v1 v2
          have htri2 : vecNorm (v1 + v2 + v3) ≤ vecNorm (v1 + v2) + vecNorm v3 :=
            vecNorm_add_le (v1 + v2) v3
          have htri3 : vecNorm (v1 + v2 + v3 + v4) ≤ vecNorm (v1 + v2 + v3) + vecNorm v4 :=
            vecNorm_add_le (v1 + v2 + v3) v4
          rw [hdecomp]
          have hsum_le : 1 / wdScaleR + (truncPad15 : ℝ) / wdScaleR + ((nSub : ℝ) * (2 * (gCeil :
            ℝ) + 20)) / wdScaleR + (66 * (nSub : ℝ)) / wdScaleR ≤ (totalPad15 : ℝ) /
            wdScaleR := by
            have hexp1 : (nSub : ℝ) * (2 * (gCeil : ℝ) + 20) =
                2 * ((nSub : ℝ) * (gCeil : ℝ)) + 20 * (nSub : ℝ) := by ring
            have hexp2 : (nSub : ℝ) * (4 * (gCeil : ℝ) + 256) =
                4 * ((nSub : ℝ) * (gCeil : ℝ)) + 256 * (nSub : ℝ) := by ring
            rw [← add_div, ← add_div, ← add_div]; refine div_le_div_of_nonneg_right ?_ hB_pos.le
            rw [hpadR, hexp1, hexp2]; have hng_nn : 0 ≤ (nSub : ℝ) * (gCeil : ℝ) := (by positivity)
            have hn_nn : 0 ≤ (nSub : ℝ) := Nat.cast_nonneg nSub; linarith
          linarith [htri1, htri2, htri3, hv1, hv2, hv3, hv4, hsum_le]
        -- Extract coordinate `w` and relate to `symHitProb`
        let wFin : Fin (orbDim m r) := ⟨w, by unfold orbDim; omega⟩
        have hw_coord : |uWalk wFin - uInt wFin| ≤ (totalPad15 : ℝ) / wdScaleR :=
          (abs_apply_le_vecNorm (uWalk - uInt) wFin).trans htotal_norm
        rcases hv_cases : vecFinal with _ | ⟨vHead, tail⟩
        · rw [hv_cases] at hvf_len; simp at hvf_len
        · have htail_len : tail.length = d := (by rw [hv_cases] at hvf_len; simpa using hvf_len)
          have hw_sub_lt : w - 1 < tail.length := (by omega)
          have hget_row : (altEvalRowLo12 m r tau9 nSub).getD (w - 1) 0 =
              ((((Int.natAbs (tail.getD (w - 1) 0) - totalPad15) *
                (Int.natAbs (tail.getD (w - 1) 0) - totalPad15)) / wdScale) / 1000) - 1 := by
            rw [heval_cons vHead tail hv_cases]
            exact altStep_altVecTailToLo12_getD totalPad15 tail (w - 1) hw_sub_lt
          have huInt_w : uInt wFin = (tail.getD (w - 1) 0 : ℝ) / wdScaleR := by
            dsimp only [uInt, altStepListToOrbVec, wFin]; rw [hv_cases]
            obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩; simp
          rw [huInt_w] at hw_coord; have hprob_lo := altStep_altVecTailToLo12_entry_le hw_coord
          rw [← hget_row] at hprob_lo
          have hstage_prob : symHitProb R (evalSymStages R (altStages tau9 nSub m n) (u0Vec (2 ^
            n) m)) w = (uWalk wFin) ^ 2 := by
            have hm_cond : 1 ≤ n ∧ 2 * m < 2 ^ n := ⟨h1_le_n, h2mN⟩; unfold altStages
            rw [dite_eq_left hm_cond]
            dsimp only [evalSymStages, SymOrthogonal.ofSymmInvolution, uWalk]; rw [hK_def]; subst hR
            exact symHitProb_evalSymStage_dAlt hmrN (altStepCount tau9 nSub (2 ^ n)) wFin
          rwa [hstage_prob]
/- ## Section 5: Bellman Loop Chaining, Table Soundness, & Cost Bound Soundness -/
theorem checkEigStep_sound {m r vR vPrev : ℕ} (h : checkEigStep m r vR vPrev = true) : (π / 8 + 1
    / 4) / √((m : ℝ) * (r : ℝ)) < (vR : ℝ) / wdScaleR - (vPrev : ℝ) / wdScaleR := by
  have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have hB_pos : (0 : ℝ) < wdScaleR := altStep_wdScaleR_pos; unfold checkEigStep at h
  cases hg1 : Bool.or (primNatBlt r 1) (Nat.ble vR vPrev) with
  | true => rw [hg1, altStep_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg1, altStep_cond_false] at h; dsimp only at h
    simp only [Bool.or_eq_false_iff, altStep_primNatBlt_eq_false, altStep_nat_ble_eq_false] at hg1
    obtain ⟨hr1, hv_lt⟩ := hg1; set sqLo := (altIsqrt15 (Nat.mul m r)).1
    rw [altStep_to_beq (fun {a b} ↦ Nat.beq_eq) sqLo 0] at h
    cases hsq0 : (sqLo == 0) with
    | true => rw [hsq0, altStep_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hsq0, altStep_cond_false] at h
      have hsq_pos_nat : 0 < sqLo := Nat.pos_of_ne_zero (altStep_nat_beq_eq_false.mp hsq0)
      have hsq_le : (sqLo : ℝ) / wdScaleR ≤ √((m : ℝ) * (r : ℝ)) := by
        have hs := (altIsqrt15_sound (m * r)).1; simpa [sqLo, Nat.cast_mul] using hs
      have hineq_nat : 1285398163397449 * wdScale < 2 * ((vR - vPrev) * sqLo) :=
        altStep_primNatBlt_eq_true.mp h
      clear_value sqLo
      have hsq_pos : (0 : ℝ) < (sqLo : ℝ) := (by exact_mod_cast hsq_pos_nat)
      have hmr_sqrt_pos : (0 : ℝ) < √((m : ℝ) * (r : ℝ)) :=
        lt_of_lt_of_le (div_pos hsq_pos hB_pos) hsq_le
      have hpi8 : π / 8 + 1 / 4 < (1285398163397449 : ℝ) / (2 * wdScaleR) := by
        have hp := pi4_lt_p01; rw [hB_eq] at hp ⊢; linarith
      have hdiff_eq : (vR : ℝ) / wdScaleR - (vPrev : ℝ) / wdScaleR =
          ((vR - vPrev : ℕ) : ℝ) / wdScaleR := by
        rw [Nat.cast_sub hv_lt.le, sub_div]
      rw [hdiff_eq, div_lt_iff₀ hmr_sqrt_pos]
      have hineqR : (1285398163397449 : ℝ) * 1000000000000000 ≤
          2 * ((vR - vPrev : ℕ) : ℝ) * (sqLo : ℝ) := by
        unfold wdScale at hineq_nat; have hc : ((1285398163397449 * 1000000000000000 : ℕ) : ℝ) ≤
            ((2 * ((vR - vPrev) * sqLo) : ℕ) : ℝ) := by exact_mod_cast hineq_nat.le
        push_cast at hc; linarith
      calc π / 8 + 1 / 4 < (1285398163397449 : ℝ) / (2 * wdScaleR) := hpi8
        _ ≤ (((vR - vPrev : ℕ) : ℝ) / wdScaleR) * ((sqLo : ℝ) / wdScaleR) := by
            rw [hB_eq, div_mul_div_comm, div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
        _ ≤ (((vR - vPrev : ℕ) : ℝ) / wdScaleR) * √((m : ℝ) * (r : ℝ)) :=
            mul_le_mul_of_nonneg_left hsq_le (div_nonneg (Nat.cast_nonneg _) hB_pos.le)
private theorem altStep_checkAltDirectLoop_cons (m r vPrev vR tau9 nSub : ℕ)
    (vhRest vRest tauRest nsubRest : List ℕ) :
    checkAltDirectLoop m r (vPrev :: vhRest) (vR :: vRest) (tau9 :: tauRest)
        (nSub :: nsubRest) =
      (cond (primNatBlt vR vPrev) false
        (let stepOk :=
           cond (tau9 == 0) (checkEigStep m r vR vPrev)
             (let d := cond (Nat.ble m r) m r
             let rowLo12 := altEvalRowLo12 m r tau9 nSub
             cond (Bool.or (Bool.not (altListLen rowLo12 == d))
                 (Bool.or (altSumNat rowLo12 == 0)
                   (primNatBlt (altListLen (vPrev :: vhRest)) d)))
               false
               (let drift27 := altDriftSum27 vR rowLo12 (vPrev :: vhRest)
               primNatBlt (Nat.mul tau9 1000000000000000000) drift27))
         cond stepOk
           (checkAltDirectLoop m (Nat.add r 1) (vR :: vPrev :: vhRest) vRest tauRest nsubRest)
           false)) := by
  conv_lhs =>
    unfold checkAltDirectLoop checkAltDirectLoopAux
    simp only [AltForce.withForcedNat_eq, AltForce.withForcedList_eq,
      altStep_to_beq (fun {a b} ↦ Nat.beq_eq)]
  rfl
/-- Sub-band chaining theorem for `checkAltDirectLoop`, enabling multi-part `decide +kernel`
  splitting across large `kMax` ranges. -/
theorem checkAltDirectLoop_append (m r : ℕ) (vHist v1 t1 n1 v2 t2 n2 : List ℕ) (hv : v1.length =
    t1.length) (hn : n1.length = t1.length) (h1 : checkAltDirectLoop m r vHist v1 t1 n1 = true)
    (h2 : checkAltDirectLoop m (r + v1.length) (v1.reverse ++ vHist) v2 t2 n2 = true) :
    checkAltDirectLoop m r vHist (v1 ++ v2) (t1 ++ t2) (n1 ++ n2) = true := by
  induction v1 generalizing r vHist t1 n1 with
  | nil =>
    cases t1 with
    | nil =>
      cases n1 with
      | nil => simpa using h2
      | cons _ _ => simp at hn
    | cons _ _ => simp at hv
  | cons vR vRest ih =>
    cases t1 with
    | nil => simp at hv
    | cons tau9 tauRest =>
      cases n1 with
      | nil => simp at hn
      | cons nSub nsubRest =>
        cases vHist with
        | nil => simp [checkAltDirectLoop, checkAltDirectLoopAux] at h1
        | cons vPrev vhRest =>
          simp only [List.cons_append]; rw [altStep_checkAltDirectLoop_cons] at h1 ⊢
          dsimp only at h1 ⊢
          cases hlt : primNatBlt vR vPrev with
          | true => rw [hlt, altStep_cond_true] at h1; exact Bool.noConfusion h1
          | false =>
            rw [hlt, altStep_cond_false] at h1; rw [altStep_cond_false]
            revert h1
            set stepOk : Bool := cond (tau9 == 0)
                (checkEigStep m r vR vPrev)
                (let d := cond (Nat.ble m r) m r
                let rowLo12 := altEvalRowLo12 m r tau9 nSub
                cond (Bool.or (Bool.not (altListLen rowLo12 == d))
                    (Bool.or (altSumNat rowLo12 == 0)
                      (primNatBlt (altListLen (vPrev :: vhRest)) d)))
                  false
                  (let drift27 := altDriftSum27 vR rowLo12 (vPrev :: vhRest)
                  primNatBlt (Nat.mul tau9 1000000000000000000) drift27))
            intro h1
            cases hs : stepOk with
            | false => rw [hs, altStep_cond_false] at h1; exact Bool.noConfusion h1
            | true =>
              rw [hs, altStep_cond_true] at h1; rw [altStep_cond_true]
              have hrev : (vR :: vRest).reverse ++ (vPrev :: vhRest) =
                  vRest.reverse ++ (vR :: vPrev :: vhRest) := by simp [List.reverse_cons]
              have hr_add : r + (vR :: vRest).length = Nat.add r 1 + vRest.length := by simp; omega
              rw [hrev, hr_add] at h2
              exact ih (Nat.add r 1) (vR :: vPrev :: vhRest) tauRest nsubRest
                (by simpa using hv) (by simpa using hn) h1 h2
private theorem altStep_sum_range_succ_shift (f : ℕ → ℕ) :
    ∀ d : ℕ, (∑ j ∈ Finset.range (d + 1), f j) = f 0 + ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by simp
  | d + 1 => by
    rw [Finset.sum_range_succ, altStep_sum_range_succ_shift f d, Finset.sum_range_succ, add_assoc]
private theorem altStep_sum_Icc_one_eq_range (f : ℕ → ℝ) :
    ∀ d : ℕ, (∑ w ∈ Finset.Icc 1 d, f w) = ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by
    have hset : Finset.Icc (1 : ℕ) 0 = ∅ := by ext x; simp
    rw [hset]; simp
  | d + 1 => by
    rw [altStep_sum_Icc_one_succ, altStep_sum_Icc_one_eq_range f d, Finset.sum_range_succ]
private theorem altStep_altSumNat_eq_sum_range :
    ∀ (d : ℕ) (xs : List ℕ), xs.length = d → altSumNat xs = ∑ j ∈ Finset.range d, xs.getD j 0
  | 0, [], _ => by simp [altSumNat]
  | d + 1, x :: xs, hlen => by
    rw [altStep_sum_range_succ_shift]
    have ih := altStep_altSumNat_eq_sum_range d xs (by simpa using hlen)
    simpa [altSumNat] using congrArg (Nat.add x) ih
private theorem altStep_altDriftSum27_eq_sum_range (vR : ℕ) :
    ∀ (d : ℕ) (ps vhs : List ℕ), ps.length = d → d ≤ vhs.length → altDriftSum27 vR ps vhs =
        ∑ j ∈ Finset.range d, ps.getD j 0 * (vR - vhs.getD j 0)
  | 0, [], _, _, _ => by simp [altDriftSum27]
  | d + 1, p :: ps, vh :: vhs, hps, hvhs => by
    rw [altStep_sum_range_succ_shift]
    have ih := altStep_altDriftSum27_eq_sum_range vR d ps vhs
      (by simpa using hps) (by simpa using hvhs)
    simpa [altDriftSum27] using congrArg (Nat.add (p * (vR - vh))) ih
private theorem altStep_checkAltDirectLoop_step_props (m : ℕ) (vPot tau9Rows nsubRows : List ℕ) :
    ∀ (vRem tauRem nsubRem vHist : List ℕ) (r : ℕ), 2 ≤ r → vHist.length = r →
      (∀ j < r, vHist.getD j 0 = vPot.getD (r - 1 - j) 0) →
      (∀ j < vRem.length, vRem.getD j 0 = vPot.getD (r + j) 0) →
      (∀ j < tauRem.length, tauRem.getD j 0 = tau9Rows.getD (r - 2 + j) 0) →
      (∀ j < nsubRem.length, nsubRem.getD j 0 = nsubRows.getD (r - 2 + j) 0) →
      checkAltDirectLoop m r vHist vRem tauRem nsubRem = true →
      ∀ s : ℕ, r ≤ s → s < r + vRem.length → vPot.getD (s - 1) 0 ≤ vPot.getD s 0 ∧
        (tau9Rows.getD (s - 2) 0 = 0 →
          checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true) ∧
        (0 < tau9Rows.getD (s - 2) 0 →
          let d := min m s
          let row := altEvalRowLo12 m s (tau9Rows.getD (s - 2) 0) (nsubRows.getD (s - 2) 0)
          row.length = d ∧ 0 < altSumNat row ∧ tau9Rows.getD (s - 2) 0 * 1000000000000000000 <
              ∑ j ∈ Finset.range d, row.getD j 0 * (vPot.getD s 0 - vPot.getD (s - 1 - j) 0))
  | [], _, _, _, r, _, _, _, _, _, _, _, s, hrs, hslt => by simp at hslt; omega
  | vR :: vRest, [], _, _, _, _, _, _, _, _, _, hchk, _, _, _ => by
    simp [checkAltDirectLoop, checkAltDirectLoopAux] at hchk
  | vR :: vRest, _ :: _, [], _, _, _, _, _, _, _, _, hchk, _, _, _ => by
    simp [checkAltDirectLoop, checkAltDirectLoopAux] at hchk
  | vR :: vRest, tau9 :: tauRest, nSub :: nsubRest, [], r, hr2, hvh_len,
      _, _, _, _, _, _, _, _ => by
    simp at hvh_len; omega
  | vR :: vRest, tau9 :: tauRest, nSub :: nsubRest, vPrev :: vhRest, r, hr2,
      hvh_len, hvh_eq, hv_eq, ht_eq, hn_eq, hchk, s, hrs, hslt => by
    have hvR_eq : vR = vPot.getD r 0 := by simpa using hv_eq 0 (Nat.succ_pos _)
    have hvPrev_eq : vPrev = vPot.getD (r - 1) 0 := by
      simpa using hvh_eq 0 (by omega)
    have htau_eq : tau9 = tau9Rows.getD (r - 2) 0 := by simpa using ht_eq 0 (Nat.succ_pos _)
    have hnsub_eq : nSub = nsubRows.getD (r - 2) 0 := by simpa using hn_eq 0 (Nat.succ_pos _)
    rw [altStep_checkAltDirectLoop_cons] at hchk; dsimp only at hchk
    cases hblt : primNatBlt vR vPrev with
    | true => rw [hblt, altStep_cond_true] at hchk; exact Bool.noConfusion hchk
    | false =>
      rw [hblt, altStep_cond_false] at hchk
      have hv_mono : vPrev ≤ vR := altStep_primNatBlt_eq_false.mp hblt
      revert hchk
      set stepOk : Bool := cond (tau9 == 0)
          (checkEigStep m r vR vPrev)
          (let d := cond (Nat.ble m r) m r
          let rowLo12 := altEvalRowLo12 m r tau9 nSub
          cond (Bool.or (Bool.not (altListLen rowLo12 == d))
              (Bool.or (altSumNat rowLo12 == 0)
                (primNatBlt (altListLen (vPrev :: vhRest)) d)))
            false
            (let drift27 := altDriftSum27 vR rowLo12 (vPrev :: vhRest)
            primNatBlt (Nat.mul tau9 1000000000000000000) drift27))
      intro hchk
      cases hs_ok : stepOk with
      | false => rw [hs_ok, altStep_cond_false] at hchk; exact Bool.noConfusion hchk
      | true =>
        rw [hs_ok, altStep_cond_true] at hchk
        by_cases hsr : s = r
        · subst hsr
          rw [← hvR_eq, ← hvPrev_eq, ← htau_eq, ← hnsub_eq]
          refine ⟨hv_mono, fun ht0 ↦ ?_, fun ht_pos ↦ ?_⟩
          · dsimp only [stepOk] at hs_ok; rw [ht0] at hs_ok
            have hz : (0 == 0) = true := rfl; rw [hz, altStep_cond_true] at hs_ok; exact hs_ok
          · dsimp only [stepOk] at hs_ok
            have ht_f : (tau9 == 0) = false := altStep_nat_beq_eq_false.mpr (Nat.ne_of_gt ht_pos)
            rw [ht_f, altStep_cond_false, altStep_bif_ble_min] at hs_ok; set d := min m s
            set rowLo12 := altEvalRowLo12 m s tau9 nSub
            cases hbad : Bool.or (Bool.not (altListLen rowLo12 == d))
                (Bool.or (altSumNat rowLo12 == 0)
                  (primNatBlt (altListLen (vPrev :: vhRest)) d)) with
            | true => rw [hbad, altStep_cond_true] at hs_ok; exact Bool.noConfusion hs_ok
            | false =>
              rw [hbad, altStep_cond_false] at hs_ok
              clear_value rowLo12
              simp only [Bool.or_eq_false_iff, Bool.not_eq_false', altStep_nat_beq_eq_true,
                altStep_nat_beq_eq_false, altStep_primNatBlt_eq_false,
                altStep_altListLen_eq] at hbad
              obtain ⟨hr_len, hsum_ne, hvh_ge⟩ := hbad
              have hdrift_lt := altStep_primNatBlt_eq_true.mp hs_ok
              rw [altStep_altDriftSum27_eq_sum_range vR d rowLo12 (vPrev :: vhRest) hr_len hvh_ge]
                at hdrift_lt
              have hsum_congr :
                  (∑ j ∈ Finset.range d, rowLo12.getD j 0 * (vR - (vPrev :: vhRest).getD j 0)) =
                  (∑ j ∈ Finset.range d,
                    rowLo12.getD j 0 * (vR - vPot.getD (s - 1 - j) 0)) := by
                refine Finset.sum_congr rfl fun j hj ↦ ?_
                have hj_lt : j < s := (Finset.mem_range.mp hj).trans_le (Nat.min_le_right m s)
                rw [hvh_eq j hj_lt]
              rw [hsum_congr] at hdrift_lt; exact ⟨hr_len, Nat.pos_of_ne_zero hsum_ne, hdrift_lt⟩
        · have hs_ge : r + 1 ≤ s := by omega
          have hs_lt' : s < (r + 1) + vRest.length := by simp at hslt; omega
          exact altStep_checkAltDirectLoop_step_props m vPot tau9Rows nsubRows
            vRest tauRest nsubRest (vR :: vPrev :: vhRest) (r + 1)
            (by omega)
            (by simp [hvh_len])
            (fun j hj ↦ by
              rcases j with _ | j'
              · rw [List.getD_cons_zero, show r + 1 - 1 - 0 = r by omega]
                exact hvR_eq
              · rw [List.getD_cons_succ, show r + 1 - 1 - (j' + 1) = r - 1 - j' by omega]
                exact hvh_eq j' (by omega))
            (fun j hj ↦ by
              have h1 := hv_eq (j + 1) (by simp; omega)
              rw [List.getD_cons_succ, show r + (j + 1) = (r + 1) + j by omega] at h1
              exact h1)
            (fun j hj ↦ by
              have h1 := ht_eq (j + 1) (by simp; omega)
              rw [List.getD_cons_succ, show r - 2 + (j + 1) = (r + 1) - 2 + j by omega] at h1
              exact h1)
            (fun j hj ↦ by
              have h1 := hn_eq (j + 1) (by simp; omega)
              rw [List.getD_cons_succ, show r - 2 + (j + 1) = (r + 1) - 2 + j by omega] at h1
              exact h1)
            hchk s hs_ge hs_lt'
private theorem altStep_checkAltDirectTable12_props {m kMax : ℕ} {vPot tau9Rows nsubRows : List ℕ}
    (h : checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true) : 1 ≤ m ∧ m ≤ 8192 ∧ 2 ≤ kMax
    ∧ kMax ≤ 1024 ∧ vPot.getD 0 0 = 0 ∧ (∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ kMax → vPot.getD r₁ 0 ≤
    vPot.getD r₂ 0) ∧ checkEigStep m 1 (vPot.getD 1 0) (vPot.getD 0 0) = true ∧ (∀ s : ℕ, 2 ≤ s → s
      ≤
    kMax → (tau9Rows.getD (s - 2) 0 = 0 → checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) =
    true) ∧ (0 < tau9Rows.getD (s - 2) 0 →
          let d := min m s
          let row := altEvalRowLo12 m s (tau9Rows.getD (s - 2) 0) (nsubRows.getD (s - 2) 0)
          row.length = d ∧ 0 < altSumNat row ∧ tau9Rows.getD (s - 2) 0 * 1000000000000000000 <
              ∑ j ∈ Finset.range d, row.getD j 0 * (vPot.getD s 0 - vPot.getD (s - 1 - j) 0))) := by
  unfold checkAltDirectTable12 at h
  cases hg1 : Bool.or (primNatBlt m 1)
      (Bool.or (primNatBlt 8192 m) (Bool.or (primNatBlt kMax 2) (primNatBlt 1024 kMax))) with
  | true => rw [hg1, altStep_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg1, altStep_cond_false] at h
    simp only [Bool.or_eq_false_iff, altStep_primNatBlt_eq_false] at hg1
    obtain ⟨hm1, hm8, hk2, hk10⟩ := hg1
    rw [altStep_to_beq (fun {a b} ↦ Nat.beq_eq) (altListLen vPot) (Nat.add kMax 1),
      altStep_to_beq (fun {a b} ↦ Nat.beq_eq) (altListLen tau9Rows) (Nat.sub kMax 1),
      altStep_to_beq (fun {a b} ↦ Nat.beq_eq) (altListLen nsubRows) (Nat.sub kMax 1)] at h
    cases hg2 : Bool.or (Bool.not (altListLen vPot == Nat.add kMax 1))
        (Bool.or (Bool.not (altListLen tau9Rows == Nat.sub kMax 1))
          (Bool.not (altListLen nsubRows == Nat.sub kMax 1))) with
    | true => rw [hg2, altStep_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg2, altStep_cond_false] at h
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', altStep_nat_beq_eq_true,
        altStep_altListLen_eq] at hg2
      obtain ⟨hv_len, ht_len, hn_len⟩ := hg2; rcases hv_cases : vPot with _ | ⟨v0, _ | ⟨v1, vRest⟩⟩
      · rw [hv_cases] at hv_len; simp at hv_len
      · rw [hv_cases] at hv_len; simp at hv_len; omega
      · rw [hv_cases] at h hv_len; dsimp only at h
        rw [altStep_to_beq (fun {a b} ↦ Nat.beq_eq) v0 0] at h
        cases hv0_z : Bool.not (v0 == 0) with
        | true => rw [hv0_z, altStep_cond_true] at h; exact Bool.noConfusion h
        | false =>
          rw [hv0_z, altStep_cond_false] at h
          simp only [Bool.not_eq_false', altStep_nat_beq_eq_true] at hv0_z
          cases heig1 : checkEigStep m 1 v1 v0 with
          | false => rw [heig1, altStep_cond_false] at h; exact Bool.noConfusion h
          | true =>
            rw [heig1, altStep_cond_true] at h
            have hv1_ge : v0 ≤ v1 := by
              unfold checkEigStep at heig1
              cases hg : Bool.or (primNatBlt 1 1) (Nat.ble v1 v0) with
              | true => rw [hg, altStep_cond_true] at heig1; exact Bool.noConfusion heig1
              | false =>
                simp only [Bool.or_eq_false_iff, altStep_nat_ble_eq_false] at hg; exact hg.2.le
            have hrest_len : vRest.length = kMax - 1 := (by simp at hv_len; omega)
            have hloop := altStep_checkAltDirectLoop_step_props m (v0 :: v1 :: vRest)
              tau9Rows nsubRows
              vRest tau9Rows nsubRows [v1, v0] 2
              (by omega) rfl
              (fun j hj ↦ by
                rcases j with _ | _ | j'
                · rfl
                · rfl
                · omega)
              (fun j _ ↦ by
                rw [show 2 + j = (j + 1) + 1 by omega,
                  List.getD_cons_succ, List.getD_cons_succ])
              (fun j _ ↦ by
                rw [show 2 - 2 + j = j by omega])
              (fun j _ ↦ by
                rw [show 2 - 2 + j = j by omega])
              h
            have hstep_mono : ∀ r : ℕ, 1 ≤ r → r ≤ kMax →
                (v0 :: v1 :: vRest).getD (r - 1) 0 ≤ (v0 :: v1 :: vRest).getD r 0 := by
              intro r hr1 hrk; by_cases hr_eq1 : r = 1
              · subst hr_eq1; exact hv1_ge
              · exact (hloop r (by omega) (by omega)).1
            have hmono : ∀ {r₁ r₂ : ℕ}, r₁ ≤ r₂ → r₂ ≤ kMax →
                (v0 :: v1 :: vRest).getD r₁ 0 ≤ (v0 :: v1 :: vRest).getD r₂ 0 := by
              intro r₁ r₂ h12 h2k
              induction h12 with
              | refl => exact le_rfl
              | @step b h1b ih => exact (ih (by omega)).trans (hstep_mono (b + 1) (by omega) h2k)
            exact ⟨hm1, hm8, hk2, hk10, hv0_z, hmono, heig1,
              fun s hs2 hsk ↦ (hloop s hs2 (by omega)).2⟩
theorem checkAltBound12_sound {m k vAtK num den : ℕ} (hm1 : 1 ≤ m) (h : checkAltBound12 m k vAtK
    num den = true) : (vAtK : ℝ) / wdScaleR ≤ (NNRat.divNat num den : ℝ) * (π / 4) *
    groverHarmonicSqrtSum k / √(m : ℝ) := by
  have hB_eq : wdScaleR = 1000000000000000 := (by unfold wdScaleR wdScale; norm_num)
  have hB : (0 : ℝ) < wdScaleR := altStep_wdScaleR_pos; unfold checkAltBound12 at h
  rw [altStep_to_beq (fun {a b} ↦ Nat.beq_eq) den 0] at h
  cases hg : (den == 0) with
  | true => rw [hg, altStep_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg, altStep_cond_false] at h; dsimp only at h
    have hden_pos_nat : 0 < den := Nat.pos_of_ne_zero (altStep_nat_beq_eq_false.mp hg)
    have hden_pos : (0 : ℝ) < (den : ℝ) := (by exact_mod_cast hden_pos_nat)
    set sqrtMHi15 := (altIsqrt15 m).2; set hLo15 := harmSumLo15 k
    have hineq_nat := altStep_nat_ble_eq_true.mp h
    have hsq_ge : √(m : ℝ) ≤ (sqrtMHi15 : ℝ) / wdScaleR := (altIsqrt15_sound m).2
    have hh_le : (hLo15 : ℝ) / wdScaleR ≤ groverHarmonicSqrtSum k := harmSumLo15_le k
    clear_value sqrtMHi15 hLo15
    have hineqR : (vAtK : ℝ) * (sqrtMHi15 : ℝ) * (den : ℝ) ≤
        (num : ℝ) * 785398163397448 * (hLo15 : ℝ) := by
      have hc : ((vAtK * sqrtMHi15 * den : ℕ) : ℝ) ≤
          ((num * 785398163397448 * hLo15 : ℕ) : ℝ) := by exact_mod_cast hineq_nat
      push_cast at hc; exact hc
    have hm_sqrt_pos : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm1)
    have hsq_pos : (0 : ℝ) < (sqrtMHi15 : ℝ) := by
      have hdiv := lt_of_lt_of_le hm_sqrt_pos hsq_ge; have hm_pos := mul_pos hdiv hB
      rwa [div_mul_cancel₀ _ hB.ne'] at hm_pos
    have hpi_ge : (785398163397448 : ℝ) / wdScaleR ≤ π / 4 := pi4_gt_p01.le
    have hrel_eq : (NNRat.divNat num den : ℝ) = (num : ℝ) / (den : ℝ) := by
      rw [NNRat.divNat_eq_div]; push_cast; rfl
    have hstep1 : (vAtK : ℝ) / wdScaleR ≤ ((num : ℝ) / (den : ℝ)) * ((785398163397448 : ℝ) /
      wdScaleR) * ((hLo15 : ℝ) / wdScaleR) / ((sqrtMHi15 : ℝ) / wdScaleR) := by
      have hrhs_eq : ((num : ℝ) / (den : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) * ((hLo15 : ℝ) /
        wdScaleR) / ((sqrtMHi15 : ℝ) / wdScaleR) = ((num : ℝ) * 785398163397448 * (hLo15 : ℝ)) /
        (wdScaleR * (den : ℝ) * (sqrtMHi15 : ℝ)) := by
        field_simp [hden_pos.ne', hsq_pos.ne', hB.ne']
      rw [hrhs_eq, div_le_div_iff₀ hB (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hineqR hB.le]
    have hnum_le : ((num : ℝ) / (den : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) * ((hLo15 : ℝ) /
      wdScaleR) ≤ (NNRat.divNat num den : ℝ) * (π / 4) * groverHarmonicSqrtSum k := by
      rw [hrel_eq]
      have ha : ((num : ℝ) / (den : ℝ)) * ((785398163397448 : ℝ) / wdScaleR) ≤ ((num : ℝ) / (den :
        ℝ)) * (π / 4) := mul_le_mul_of_nonneg_left hpi_ge (by positivity)
      exact mul_le_mul ha hh_le (by positivity) (by positivity)
    have hstep2 := div_le_div_of_nonneg_right hnum_le (div_pos hsq_pos hB).le
    have hnum_nn : 0 ≤ (NNRat.divNat num den : ℝ) * (π / 4) * groverHarmonicSqrtSum k :=
      le_trans (by positivity) hnum_le
    have hstep3 := div_le_div_of_nonneg_left hnum_nn hm_sqrt_pos hsq_ge
    exact (hstep1.trans hstep2).trans hstep3
/- ## Section 6: Turnkey `altWalkSpecOf`, `altWalkSpecExact`, & Parallel Circuit Wrappers -/
private theorem altStep_stagesQueryCount_singleton {α : Type*} (K : ℕ) (D : α) :
    stagesQueryCount [(K, D)] = K :=
  Nat.add_zero K
/-- Exact query-count evaluation for `altStages` without unfolding `altStepCount`. -/
theorem stagesQueryCount_altStages {tau9 nSub m n : ℕ} (hn1 : 1 ≤ n) (h2m : 2 * m < 2 ^ n) :
    stagesQueryCount (altStages tau9 nSub m n) = altStepCount tau9 nSub (2 ^ n) := by
  have hc : 1 ≤ n ∧ 2 * m < 2 ^ n := ⟨hn1, h2m⟩; unfold altStages
  rw [dite_eq_left hc]; exact altStep_stagesQueryCount_singleton _ _
/-- Constructs a certified `JohnsonWalkSpec m k` (`n0 = altN0 = 80000`) from any prefix `k ≤ kMax`
  of a verified `checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true` certificate
  table. -/
noncomputable def altWalkSpecOf (m k kMax : ℕ) (vPot tau9Rows nsubRows : List ℕ)
    (_hk2 : 2 ≤ k) (hk_le : k ≤ kMax)
    (hchk : checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true) :
    JohnsonWalkSpec m k where
  useWalk := fun r ↦ decide (2 ≤ r ∧ 0 < tau9Rows.getD (r - 2) 0)
  n0 := altN0
  hn0 := by unfold altN0; omega
  stages := fun n r ↦
    altStages (tau9Rows.getD (r - 2) 0) (nsubRows.getD (r - 2) 0) m n
  V := fun r ↦ (vPot.getD r 0 : ℝ) / wdScaleR
  hV0 := by
    have hv0 := (altStep_checkAltDirectTable12_props hchk).2.2.2.2.1
    rw [hv0, Nat.cast_zero, zero_div]
  hV_mono := fun {r₁ r₂} h12 h2k ↦ by
    have hB : 0 ≤ wdScaleR := altStep_wdScaleR_pos.le
    have hm := (altStep_checkAltDirectTable12_props hchk).2.2.2.2.2.1 h12 (h2k.trans hk_le)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hB
  hV_eig := fun r hr1 hrk hcase ↦ by
    obtain ⟨_, _, _, _, _, _, heig1, hrows⟩ := altStep_checkAltDirectTable12_props hchk
    rcases hcase with rfl | hf
    · exact checkEigStep_sound heig1
    · simp only [decide_eq_false_iff_not, not_and, not_lt, Nat.le_zero] at hf
      by_cases hr_eq1 : r = 1
      · subst hr_eq1; exact checkEigStep_sound heig1
      · have hr2 : 2 ≤ r := by omega
        exact checkEigStep_sound ((hrows r hr2 (hrk.trans hk_le)).1 (hf hr2))
  pLo := fun r w ↦
    if 1 ≤ w ∧ w ≤ min m r then
      (((altEvalRowLo12 m r (tau9Rows.getD (r - 2) 0) (nsubRows.getD (r - 2) 0)).getD
        (w - 1) 0 : ℝ) / 1000000000000)
    else 0
  hpLo_nonneg := fun r w ↦ by
    split_ifs <;> positivity
  hpLo_sum_pos := fun r hr2 hrk huse ↦ by
    simp only [decide_eq_true_eq] at huse
    obtain ⟨hm1, _, _, _, _, _, _, hrows⟩ := altStep_checkAltDirectTable12_props hchk
    obtain ⟨hr_len, hsum_pos, _⟩ := (hrows r hr2 (hrk.trans hk_le)).2 huse.2
    set d := min m r
    set row := altEvalRowLo12 m r (tau9Rows.getD (r - 2) 0) (nsubRows.getD (r - 2) 0)
    clear_value row
    rw [altStep_altSumNat_eq_sum_range d row hr_len] at hsum_pos
    have hsumR : (0 : ℝ) < ∑ j ∈ Finset.range d, (row.getD j 0 : ℝ) := by
      exact_mod_cast hsum_pos
    rw [altStep_sum_Icc_one_eq_range]
    have hcongr :
        (∑ j ∈ Finset.range d,
          (if 1 ≤ j + 1 ∧ j + 1 ≤ d then (row.getD ((j + 1) - 1) 0 : ℝ) / 1000000000000
           else 0)) =
        (∑ j ∈ Finset.range d, (row.getD j 0 : ℝ)) / 1000000000000 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj_lt : j < d := Finset.mem_range.mp hj
      have hc : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
      rw [ite_eq_left hc]
      simp
    rw [hcongr]
    positivity
  tauSum := fun r ↦ (tau9Rows.getD (r - 2) 0 : ℝ) / 1000000000
  C_step := 0
  hstages_len := fun n r hn0 _ _ _ ↦ by
    obtain ⟨_, hm_hi, _, _, _, _, _, _⟩ := altStep_checkAltDirectTable12_props hchk
    have hn_num : 80000 ≤ n := hn0
    have hpow15 : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have h32768 : 32768 = 2 ^ 15 := by norm_num
    have h2mN : 2 * m < 2 ^ n := by omega
    rw [stagesQueryCount_altStages (by omega) h2mN, add_zero,
      show (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) by push_cast; rfl]
    exact altStepCount_le_tau_sqrt (tau9Rows.getD (r - 2) 0) (nsubRows.getD (r - 2) 0) (2 ^ n)
  hpLo_le := fun n r hn0 hr2 hrk huse R hR w hw ↦ by
    simp only [decide_eq_true_eq] at huse
    obtain ⟨hm1, _, _, _, _, _, _, hrows⟩ := altStep_checkAltDirectTable12_props hchk
    obtain ⟨hr_len, _, _⟩ := (hrows r hr2 (hrk.trans hk_le)).2 huse.2
    rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
    have hc : 1 ≤ w ∧ w ≤ min m r := ⟨hw1, hwd⟩
    rw [ite_eq_left hc]
    exact altEvalRowLo12_sound hn0 (by omega : 1 ≤ min m r) hr_len hR hw1 hwd
  hdrift_lt := fun r hr2 hrk huse ↦ by
    simp only [decide_eq_true_eq] at huse
    obtain ⟨_, _, _, _, _, hmono, _, hrows⟩ := altStep_checkAltDirectTable12_props hchk
    obtain ⟨_, _, hdrift_nat⟩ := (hrows r hr2 (hrk.trans hk_le)).2 huse.2
    set d := min m r
    set row := altEvalRowLo12 m r (tau9Rows.getD (r - 2) 0) (nsubRows.getD (r - 2) 0)
    clear_value row
    have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
    rw [altStep_sum_Icc_one_eq_range]
    have hcongr :
        (∑ j ∈ Finset.range d,
          (if 1 ≤ j + 1 ∧ j + 1 ≤ d then (row.getD ((j + 1) - 1) 0 : ℝ) / 1000000000000 else 0) *
            ((vPot.getD r 0 : ℝ) / wdScaleR - (vPot.getD (r - (j + 1)) 0 : ℝ) / wdScaleR)) =
        (∑ j ∈ Finset.range d,
          (row.getD j 0 : ℝ) * ((vPot.getD r 0 - vPot.getD (r - 1 - j) 0 : ℕ) : ℝ)) /
          (1000000000000 * wdScaleR) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj_lt : j < d := Finset.mem_range.mp hj
      have hc : 1 ≤ j + 1 ∧ j + 1 ≤ d := ⟨by omega, by omega⟩
      rw [ite_eq_left hc]
      have hsub_idx : r - (j + 1) = r - 1 - j := by omega
      have hv_le : vPot.getD (r - 1 - j) 0 ≤ vPot.getD r 0 :=
        hmono (by omega) (hrk.trans hk_le)
      rw [hsub_idx, Nat.cast_sub hv_le]
      simp only [Nat.add_sub_cancel]
      ring
    rw [hcongr, hB_eq]
    have hdriftR : (tau9Rows.getD (r - 2) 0 : ℝ) * 1000000000000000000 <
        ∑ j ∈ Finset.range d,
          (row.getD j 0 : ℝ) * ((vPot.getD r 0 - vPot.getD (r - 1 - j) 0 : ℕ) : ℝ) := by
      exact_mod_cast hdrift_nat
    linarith
/-- Definitional potential projection for `altWalkSpecOf`. -/
theorem altWalkSpecOf_V (m k kMax : ℕ) (vPot tau9Rows nsubRows : List ℕ)
    (hk2 : 2 ≤ k) (hk_le : k ≤ kMax)
    (hchk : checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true) (r : ℕ) :
    (altWalkSpecOf m k kMax vPot tau9Rows nsubRows hk2 hk_le hchk).V r =
      (vPot.getD r 0 : ℝ) / wdScaleR := rfl
/-- Definitional threshold projection for `altWalkSpecOf`. -/
theorem altWalkSpecOf_n0 (m k kMax : ℕ) (vPot tau9Rows nsubRows : List ℕ)
    (hk2 : 2 ≤ k) (hk_le : k ≤ kMax)
    (hchk : checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true) :
    (altWalkSpecOf m k kMax vPot tau9Rows nsubRows hk2 hk_le hchk).n0 = altN0 := rfl
/-- Exact-length specialization of `altWalkSpecOf` when `k = kMax`. -/
noncomputable abbrev altWalkSpecExact (m k : ℕ) (vPot tau9Rows nsubRows : List ℕ)
    (hk2 : 2 ≤ k) (hchk : checkAltDirectTable12 m k vPot tau9Rows nsubRows = true) :
    JohnsonWalkSpec m k :=
  altWalkSpecOf m k k vPot tau9Rows nsubRows hk2 le_rfl hchk
end
public section
open Operator ResourceCounting Real QProg.Notation
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal
/-- Turnkey parallel query-model circuit for a certified `1`-stage `D_{\text{alt}}` cell. -/
noncomputable def altCellCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k kMax : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot tau9Rows nsubRows : List ℕ) (hk2 : 2 ≤ k) (hk_le : k ≤ kMax)
    (hchk : checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true) (n : ℕ) :
    OracleCirc Var (Stage1.qubits n m k) ((n + 1) * m) :=
  johnsonCircuit res hm_grid hk_grid
    (altWalkSpecOf m k kMax vPot tau9Rows nsubRows hk2 hk_le hchk) n
/-- Exact probability-`1` correctness of `altCellCircuit` on `groverTargetSets n k`. -/
theorem altCell_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k kMax : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot tau9Rows nsubRows : List ℕ) (hk2 : 2 ≤ k) (hk_le : k ≤ kMax)
    (hchk : checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true)
    (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))}
    (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;;
      (altCellCircuit res hm_grid hk_grid vPot tau9Rows nsubRows hk2 hk_le hchk n).compile
        qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ :=
  johnsonCircuit_correctness res hm_grid hk_grid
    (altWalkSpecOf m k kMax vPot tau9Rows nsubRows hk2 hk_le hchk) hn hkN hS
/-- Asymptotic relative-cost bound of `altCellCircuit` from `checkAltBound12`. -/
theorem altCell_rel_cost {Var : Type} [DecidableEq Var] (res : Var)
    {m k kMax num den : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot tau9Rows nsubRows : List ℕ) (hk2 : 2 ≤ k) (hk_le : k ≤ kMax)
    (hchk : checkAltDirectTable12 m kMax vPot tau9Rows nsubRows = true)
    (hbnd : checkAltBound12 m k (vPot.getD k 0) num den = true) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n →
      AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ qset ;;
          (altCellCircuit res hm_grid hk_grid vPot tau9Rows nsubRows hk2 hk_le hchk n).compile
            qAssign (groverParallelMarkingOracle m S))
        ((NNRat.divNat num den : ℝ) * vanillaFindAllCost n m k) := by
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have htop : (altWalkSpecOf m k kMax vPot tau9Rows nsubRows hk2 hk_le hchk).V k ≤ (NNRat.divNat
    num den : ℝ) * (π / 4) * groverHarmonicSqrtSum k / √(m : ℝ) := checkAltBound12_sound hm1 hbnd
  exact johnsonCircuit_rel_cost res hm_grid hk_grid
    (altWalkSpecOf m k kMax vPot tau9Rows nsubRows hk2 hk_le hchk) htop
end
end QuantumComputation.Specs.DickeSol
