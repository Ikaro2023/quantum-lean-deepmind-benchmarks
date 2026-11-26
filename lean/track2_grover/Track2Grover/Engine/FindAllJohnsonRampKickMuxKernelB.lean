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

public import Track2Grover.Engine.JohnsonBlockMuxSparseFastT16
/-
# Multi-Segment `T_16` Orbital Kernel & Evaluator (`FindAllJohnsonRampKickMuxKernelB`)
-/
section Sec_FindAllJohnsonRampKickMuxKernelA
namespace QuantumComputation.Specs.DickeSol

@[expose] public section

open Real
open scoped Matrix NNRat NNReal ENNReal



/-- Maps a `10 ^ 15`-scaled integer coordinate list to `Fin (d + 1) → ℝ`. -/
noncomputable def rkmListToOrbVec (d : ℕ) (xs : List ℤ) : Fin (d + 1) → ℝ :=
  fun a ↦ (xs.getD a.1 0 : ℝ) / wdScaleR

/-- Quantized skew-symmetric tridiagonal orbital generator from `hb: List ℤ`. -/
noncomputable def rkmPtGenMat (d : ℕ) (hb : List ℤ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  tridiagSkewMat d (fun w ↦ (hb.getD w 0 : ℝ) / wdScaleR)

/-- Pointwise orbital sign diagonal action induced by `mask: List Bool`. -/
def rkmMaskSignVec (d : ℕ) (mask : List Bool) (u : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun w ↦ (if mask.getD w.1 false then (-1 : ℝ) else 1) * u w

end

public section

open Real
open scoped Matrix NNRat NNReal ENNReal

private theorem rkm_cond_true {α : Type} (a b : α) : cond true a b = a := rfl
private theorem rkm_cond_false {α : Type} (a b : α) : cond false a b = b := rfl

private theorem rkm_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkm_nat_ble_eq_true]

private theorem rkm_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, rkm_nat_ble_eq_true]; omega

private theorem rkm_nat_blt_eq_false {a b : ℕ} : Nat.blt a b = false ↔ b ≤ a := by
  unfold Nat.blt; rw [rkm_nat_ble_eq_false]; omega

private theorem rkm_nat_blt_eq_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  unfold Nat.blt; exact rkm_nat_ble_eq_true

private theorem rkm_primNatBlt_eq {a b : ℕ} : primNatBlt a b = Nat.blt a b := rfl

private theorem rkm_forceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat
  rw [show Nat.add 1 x = x + 1 from Nat.one_add x]

private theorem rkm_forceList_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by
  cases xs <;> rfl

private theorem rkm_strictConsInt_eq (x : ℤ) (xs : List ℤ) :
    highdStrictConsInt x xs = x :: xs := by
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

private theorem rkm_rawIntNeg_eq (x : ℤ) : muxRawIntNeg x = -x := by
  cases x with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ k => rfl
  | negSucc n =>
    dsimp only [muxRawIntNeg]
    rw [primOfNatForced_eq]
    change ((n + 1 : ℕ) : ℤ) = -Int.negSucc n
    omega

theorem rkmBoolListLen_eq : ∀ bs : List Bool, rkmBoolListLen bs = bs.length
  | [] => rfl
  | _ :: bs => by
    unfold rkmBoolListLen
    rw [show Nat.add 1 (rkmBoolListLen bs) = rkmBoolListLen bs + 1 from Nat.one_add _,
      rkmBoolListLen_eq bs]
    rfl

theorem rkmApplyMaskBits_length :
    ∀ (mask : List Bool) (vs : List ℤ), (rkmApplyMaskBits mask vs).length = vs.length
  | [], [] => rfl
  | _ :: _, [] => rfl
  | [], _ :: _ => rfl
  | b :: bs, v :: vs => by
    unfold rkmApplyMaskBits
    rw [rkm_strictConsInt_eq]
    exact congrArg Nat.succ (rkmApplyMaskBits_length bs vs)

theorem rkmApplyMaskBits_getD :
    ∀ (mask : List Bool) (vs : List ℤ) (j : ℕ),
      (rkmApplyMaskBits mask vs).getD j 0 =
        if mask.getD j false then -(vs.getD j 0) else vs.getD j 0
  | [], vs, j => by
    cases vs <;> simp [rkmApplyMaskBits]
  | b :: bs, [], j => by
    simp [rkmApplyMaskBits]
  | b :: bs, v :: vs, 0 => by
    unfold rkmApplyMaskBits
    rw [rkm_strictConsInt_eq]
    cases b <;> simp [rkm_rawIntNeg_eq]
  | b :: bs, v :: vs, j + 1 => by
    unfold rkmApplyMaskBits
    rw [rkm_strictConsInt_eq, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact rkmApplyMaskBits_getD bs vs j

theorem rkmApplyMaskBits_orbVec (d : ℕ) (mask : List Bool) (vs : List ℤ) :
    rkmListToOrbVec d (rkmApplyMaskBits mask vs) =
      rkmMaskSignVec d mask (rkmListToOrbVec d vs) := by
  funext w
  dsimp only [rkmListToOrbVec, rkmMaskSignVec]
  rw [rkmApplyMaskBits_getD]
  cases mask.getD w.1 false <;> simp [neg_div]

theorem vecNorm_rkmMaskSignVec (d : ℕ) (mask : List Bool) (u : Fin (d + 1) → ℝ) :
    vecNorm (rkmMaskSignVec d mask u) = vecNorm u := by
  have hsq : vecSqNorm (rkmMaskSignVec d mask u) = vecSqNorm u := by
    unfold vecSqNorm rkmMaskSignVec
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    split_ifs <;> ring
  unfold vecNorm
  rw [hsq]

theorem rkmMaskSignVec_sub (d : ℕ) (mask : List Bool) (u v : Fin (d + 1) → ℝ) :
    rkmMaskSignVec d mask u - rkmMaskSignVec d mask v = rkmMaskSignVec d mask (u - v) := by
  funext w
  dsimp only [rkmMaskSignVec, Pi.sub_apply]
  ring

private theorem rkm_natMin_eq (a b : ℕ) : highdNatMin a b = min a b := by
  unfold highdNatMin
  cases h : Nat.ble a b
  · simp [cond, Nat.min_eq_right (rkm_nat_ble_eq_false.mp h).le]
  · simp [cond, Nat.min_eq_left (rkm_nat_ble_eq_true.mp h)]

private theorem rkm_altIntLen_eq : ∀ xs : List ℤ, altIntLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (rkm_altIntLen_eq xs)

theorem rkm_getD_eq_zero_of_le :
    ∀ (xs : List ℤ) (j : ℕ), xs.length ≤ j → xs.getD j 0 = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | _ :: xs, j + 1, h => rkm_getD_eq_zero_of_le xs j (by simpa using h)

private theorem rkm_tail_getD : ∀ (xs : List ℤ) (j : ℕ),
    (match xs with | _ :: xt => xt | [] => []).getD j 0 = xs.getD (j + 1) 0
  | [], _ => rfl
  | _ :: _, _ => rfl

private theorem rkm_head_getD (xs : List ℤ) :
    (match xs with | x :: _ => x | [] => Int.ofNat 0) = xs.getD 0 0 := by
  cases xs <;> rfl

private theorem rkm_second_getD (xs : List ℤ) :
    (match xs with | _ :: xn :: _ => xn | _ => Int.ofNat 0) = xs.getD 1 0 := by
  rcases xs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

private theorem rkm_intTdivNat_eq (x : ℤ) (dNat : ℕ) :
    highdIntTdivNat x dNat = Int.tdiv x (Int.ofNat dNat) := by
  cases x with
  | ofNat m =>
    dsimp only [highdIntTdivNat]
    rw [primOfNatForced_eq]; rfl
  | negSucc m =>
    dsimp only [highdIntTdivNat]
    rw [primNegOfNat_eq]
    change -(((m + 1) / dNat : ℕ) : ℤ) = -(Int.ofNat ((m + 1) / dNat)); rfl

private theorem rkm_hornerSlideLoop_length (dNat : ℕ) :
    ∀ (outLen : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      (hornerSlideLoop dNat prev hb vec cur outLen).length = outLen
  | 0, _, _, _, _ => rfl
  | rem + 1, prev, hb, vec, cur => by
    unfold hornerSlideLoop hornerSlideLoopAux
    cases hb with
    | nil =>
      dsimp only; rw [rkm_strictConsInt_eq]
      exact congrArg Nat.succ (rkm_hornerSlideLoop_length dNat rem 0 [] _ _)
    | cons b hbRest =>
      dsimp only; rw [rkm_strictConsInt_eq]
      exact congrArg Nat.succ (rkm_hornerSlideLoop_length dNat rem _ hbRest _ _)

private theorem rkm_hornerSlideLoop_getD (dNat : ℕ) :
    ∀ (outLen : ℕ) (prev : ℤ) (hb vec cur : List ℤ) (j : ℕ),
      j < outLen →
      (hornerSlideLoop dNat prev hb vec cur outLen).getD j 0 =
        vec.getD j 0 +
          Int.tdiv
            ((if j = 0 then prev else hb.getD (j - 1) 0 * cur.getD (j - 1) 0) -
              hb.getD j 0 * cur.getD (j + 1) 0)
            (Int.ofNat dNat)
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, prev, hb, vec, cur, 0, _ => by
    unfold hornerSlideLoop hornerSlideLoopAux
    cases hb with
    | nil =>
      dsimp only; rw [rkm_strictConsInt_eq]
      simp only [primIntAdd_eq, rkm_intTdivNat_eq]
      change (match vec with | v :: _ => v | [] => Int.ofNat 0) +
        Int.tdiv prev (Int.ofNat dNat) = _
      rw [rkm_head_getD]; simp
    | cons b hbRest =>
      dsimp only; rw [rkm_strictConsInt_eq]
      simp only [primIntAdd_eq, primIntSub_eq, primIntMul_eq, rkm_intTdivNat_eq]
      change (match vec with | v :: _ => v | [] => Int.ofNat 0) +
        Int.tdiv (prev - b * (match cur with | _ :: cn :: _ => cn | _ => Int.ofNat 0))
          (Int.ofNat dNat) = _
      rw [rkm_head_getD, rkm_second_getD]; simp
  | rem + 1, prev, hb, vec, cur, j + 1, hj => by
    unfold hornerSlideLoop hornerSlideLoopAux
    set vTail := match vec with | _ :: vt => vt | [] => ([] : List ℤ)
    set c0 := match cur with | c :: _ => c | [] => Int.ofNat 0
    set cTail := match cur with | _ :: ct => ct | [] => ([] : List ℤ)
    have hvT : vTail.getD j 0 = vec.getD (j + 1) 0 := rkm_tail_getD vec j
    have hcT1 : cTail.getD (j + 1) 0 = cur.getD (j + 2) 0 := rkm_tail_getD cur (j + 1)
    cases hb with
    | nil =>
      dsimp only; rw [rkm_strictConsInt_eq]
      change (hornerSlideLoop dNat 0 [] vTail cTail rem).getD j 0 = _
      rw [rkm_hornerSlideLoop_getD dNat rem 0 [] vTail cTail j (by omega), hvT]
      rcases j with _ | j' <;> simp
    | cons b hbRest =>
      dsimp only; rw [rkm_strictConsInt_eq]
      change (hornerSlideLoop dNat (primIntMul b c0) hbRest vTail cTail rem).getD j 0 = _
      rw [primIntMul_eq,
        rkm_hornerSlideLoop_getD dNat rem (b * c0) hbRest vTail cTail j (by omega), hvT, hcT1]
      congr 2
      rcases j with _ | j'
      · rw [show c0 = cur.getD 0 0 from rkm_head_getD cur]; simp
      · have hcTj : cTail.getD j' 0 = cur.getD (j' + 1) 0 := rkm_tail_getD cur j'
        have hj1 : j' + 1 ≠ 0 := Nat.succ_ne_zero j'
        have hj2 : j' + 1 + 1 ≠ 0 := Nat.succ_ne_zero _
        simp only [hj1, hj2, ↓reduceIte, Nat.add_sub_cancel, List.getD_cons_succ]
        rw [hcTj]

private theorem rkm_tdiv_diff_abs_le (num : ℤ) {dNat : ℕ} (hd : 1 ≤ dNat) :
    |((Int.tdiv num (Int.ofNat dNat) : ℤ) : ℝ) - (num : ℝ) / (dNat : ℝ)| ≤ 1 := by
  have hd_pos : (0 : ℝ) < (dNat : ℝ) := by exact_mod_cast hd
  have hcore (A : ℕ) : |((A / dNat : ℕ) : ℝ) - (A : ℝ) / (dNat : ℝ)| ≤ 1 := by
    set q := A / dNat
    have hlo_nat : q * dNat ≤ A := Nat.div_mul_le_self A dNat
    have hhi_nat : A < (q + 1) * dNat := by
      calc A < dNat * (q + 1) := Nat.lt_mul_div_succ A (by omega : 0 < dNat)
        _ = (q + 1) * dNat := Nat.mul_comm _ _
    have hloR : (q : ℝ) * (dNat : ℝ) ≤ (A : ℝ) := by exact_mod_cast hlo_nat
    have hhiR : (A : ℝ) ≤ ((q : ℝ) + 1) * (dNat : ℝ) := by
      have hc : (A : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * (dNat : ℝ) := by exact_mod_cast hhi_nat.le
      push_cast at hc; exact hc
    have hq_le : (q : ℝ) ≤ (A : ℝ) / (dNat : ℝ) := (le_div_iff₀ hd_pos).mpr hloR
    have hq_ge : (A : ℝ) / (dNat : ℝ) - (q : ℝ) ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ hd_pos]; linarith
    rw [abs_le]; constructor <;> linarith
  cases num with
  | ofNat a =>
    have h1 : ((Int.tdiv (Int.ofNat a) (Int.ofNat dNat) : ℤ) : ℝ) = ((a / dNat : ℕ) : ℝ) := by
      change ((Int.ofNat (a / dNat) : ℤ) : ℝ) = ((a / dNat : ℕ) : ℝ)
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    have h2 : ((Int.ofNat a : ℤ) : ℝ) = (a : ℝ) := by
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [h1, h2]; exact hcore a
  | negSucc a =>
    have h1 : ((Int.tdiv (Int.negSucc a) (Int.ofNat dNat) : ℤ) : ℝ) =
        -(((a + 1) / dNat : ℕ) : ℝ) := by
      change ((-(Int.ofNat ((a + 1) / dNat)) : ℤ) : ℝ) = _
      simp only [Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast]
    have h2 : (Int.negSucc a : ℝ) = -((a + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h1, h2, neg_div,
      show -(((a + 1) / dNat : ℕ) : ℝ) - -(((a + 1 : ℕ) : ℝ) / (dNat : ℝ)) =
        -((((a + 1) / dNat : ℕ) : ℝ) - ((a + 1 : ℕ) : ℝ) / (dNat : ℝ)) by ring,
      abs_neg]
    exact hcore (a + 1)

private theorem rkm_hornerStageSlide_chain {deg d k : ℕ} {hb vec cur : List ℤ}
    (hdeg : 1 ≤ deg) (_hk : k ≤ 15) (hd : d ≤ 1024)
    (hhb : hb.length ≤ d) (hvec_max : vec.length ≤ d + 1)
    (hcur_lo : vec.length ≤ cur.length) (hcur_hi : cur.length ≤ vec.length + k) :
    vec.length ≤ (hornerStageSlide deg (d + 1) hb vec cur).length ∧
      (hornerStageSlide deg (d + 1) hb vec cur).length ≤ d + 1 ∧
      (hornerStageSlide deg (d + 1) hb vec cur).length ≤ vec.length + (k + 1) ∧
      vecNorm (rkmListToOrbVec d (hornerStageSlide deg (d + 1) hb vec cur) -
        horner16Step (rkmPtGenMat d hb)
          (rkmListToOrbVec d vec) (rkmListToOrbVec d cur) deg) ≤ 33 / wdScaleR := by
  set out := hornerStageSlide deg (d + 1) hb vec cur
  have hB_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  have hout_def : out = applyHgTdivSlide deg (min (d + 1) (cur.length + 1)) hb vec cur := by
    dsimp [out, hornerStageSlide]
    rw [rkm_forceNat_eq, rkm_natMin_eq, rkm_altIntLen_eq]
  set nxtLen := min (d + 1) (cur.length + 1)
  have hlen : out.length = nxtLen := by
    rw [hout_def]; unfold applyHgTdivSlide; rw [rkm_forceNat_eq]
    exact rkm_hornerSlideLoop_length _ nxtLen 0 hb vec cur
  refine ⟨by rw [hlen]; exact le_min hvec_max (by omega),
    by rw [hlen]; exact Nat.min_le_left _ _,
    by rw [hlen]; exact (Nat.min_le_right _ _).trans (by omega), ?_⟩
  set diff := rkmListToOrbVec d out -
    horner16Step (rkmPtGenMat d hb) (rkmListToOrbVec d vec) (rkmListToOrbVec d cur) deg
  have hentry (a : Fin (d + 1)) : |diff a| ≤ 1 / wdScaleR := by
    set num : ℤ :=
      (if a.1 = 0 then 0 else hb.getD (a.1 - 1) 0 * cur.getD (a.1 - 1) 0) -
        hb.getD a.1 0 * cur.getD (a.1 + 1) 0
    have hmat_eq : (rkmPtGenMat d hb *ᵥ rkmListToOrbVec d cur) a =
        (num : ℝ) / wdScaleR ^ 2 := by
      unfold rkmPtGenMat
      rw [tridiagSkewMat_mulVec_apply]
      by_cases ha0 : 0 < a.1
      · have hne0 : a.1 ≠ 0 := by omega
        rw [dite_eq_left ha0]
        by_cases had : a.1 < d
        · rw [dite_eq_left had]; dsimp only [rkmListToOrbVec, num]
          rw [ite_eq_right hne0]; push_cast; field_simp [hB_pos.ne']; ring
        · rw [dite_eq_right had]; dsimp only [rkmListToOrbVec, num]
          rw [ite_eq_right hne0, rkm_getD_eq_zero_of_le hb a.1 (by omega)]
          push_cast; field_simp [hB_pos.ne']; ring
      · have heq0 : a.1 = 0 := by omega
        rw [dite_eq_right ha0]
        by_cases had : a.1 < d
        · rw [dite_eq_left had]; dsimp only [rkmListToOrbVec, num]
          rw [ite_eq_left heq0]; push_cast; field_simp [hB_pos.ne']; ring
        · rw [dite_eq_right had]; dsimp only [rkmListToOrbVec, num]
          rw [ite_eq_left heq0, rkm_getD_eq_zero_of_le hb a.1 (by omega)]
          push_cast; field_simp [hB_pos.ne']; ring
    by_cases hlt : a.1 < nxtLen
    · have hget : out.getD a.1 0 = vec.getD a.1 0 + Int.tdiv num (Int.ofNat (deg * wdScale)) := by
        rw [hout_def]; unfold applyHgTdivSlide; rw [rkm_forceNat_eq]
        exact rkm_hornerSlideLoop_getD (deg * wdScale) nxtLen 0 hb vec cur a.1 hlt
      set dNat := deg * wdScale
      have hdNat1 : 1 ≤ dNat := by dsimp [dNat]; unfold wdScale; omega
      have hdNatR : (dNat : ℝ) = (deg : ℝ) * wdScaleR := by
        dsimp [dNat]; unfold wdScaleR; push_cast; rfl
      have hdeg_pos : (0 : ℝ) < (deg : ℝ) := by exact_mod_cast hdeg
      have hdiff_eq : diff a =
          (((Int.tdiv num (Int.ofNat dNat) : ℤ) : ℝ) - (num : ℝ) / (dNat : ℝ)) / wdScaleR := by
        dsimp [diff, rkmListToOrbVec, horner16Step]
        simp only [Int.ofNat_eq_natCast] at hget ⊢
        rw [hget, hmat_eq, hdNatR]; push_cast
        field_simp [hB_pos.ne', hdeg_pos.ne']; ring
      rw [hdiff_eq, abs_div, abs_of_pos hB_pos]
      exact div_le_div_of_nonneg_right (rkm_tdiv_diff_abs_le num hdNat1) hB_pos.le
    · have hc_le : cur.length + 1 ≤ a.1 := by
        have : nxtLen = min (d + 1) (cur.length + 1) := rfl
        omega
      have hout_z : out.getD a.1 0 = 0 := rkm_getD_eq_zero_of_le out a.1 (by omega)
      have hvec_z : vec.getD a.1 0 = 0 := rkm_getD_eq_zero_of_le vec a.1 (by omega)
      have hnum0 : num = 0 := by
        dsimp [num]
        rw [rkm_getD_eq_zero_of_le cur (a.1 - 1) (by omega),
          rkm_getD_eq_zero_of_le cur (a.1 + 1) (by omega)]
        split_ifs <;> simp
      have hdiff0 : diff a = 0 := by
        dsimp [diff, rkmListToOrbVec, horner16Step]
        rw [hout_z, hvec_z, hmat_eq, hnum0]; simp
      rw [hdiff0, abs_zero]; positivity
  rw [vecNorm, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hsq_le (a : Fin (d + 1)) : (diff a) ^ 2 ≤ (1 / wdScaleR) ^ 2 := by
    rw [← sq_abs (diff a)]; exact pow_le_pow_left₀ (abs_nonneg _) (hentry a) 2
  calc vecSqNorm diff
      = ∑ a : Fin (d + 1), (diff a) ^ 2 := rfl
    _ ≤ ∑ _ : Fin (d + 1), (1 / wdScaleR) ^ 2 := Finset.sum_le_sum fun a _ ↦ hsq_le a
    _ = ((d + 1 : ℕ) : ℝ) * (1 / wdScaleR) ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (33 : ℝ) ^ 2 * (1 / wdScaleR) ^ 2 := by
        have hd33 : ((d + 1 : ℕ) : ℝ) ≤ (33 : ℝ) ^ 2 := by
          have : d + 1 ≤ 1089 := by omega
          calc ((d + 1 : ℕ) : ℝ) ≤ (1089 : ℝ) := by exact_mod_cast this
            _ = (33 : ℝ) ^ 2 := by norm_num
        exact mul_le_mul_of_nonneg_right hd33 (sq_nonneg _)
    _ = (33 / wdScaleR) ^ 2 := by ring

private theorem rkm_hornerT16SlideStep_approx {d : ℕ} {hb vec : List ℤ}
    (hd : d ≤ 1024) (hhb : hb.length ≤ d) (hvec_max : vec.length ≤ d + 1)
    (hG : ∀ u, vecNorm (rkmPtGenMat d hb *ᵥ u) ≤ (3 / 2) * vecNorm u) :
    (hornerT16SlideStep (d + 1) hb vec).length ≤ d + 1 ∧
      vecNorm (rkmListToOrbVec d (hornerT16SlideStep (d + 1) hb vec) -
        taylor16OfMat (rkmPtGenMat d hb) *ᵥ rkmListToOrbVec d vec) ≤
        (297 / 2) / wdScaleR := by
  unfold hornerT16SlideStep
  simp only [rkm_forceList_eq]
  let mkSt {deg k : ℕ} {cur nxt : List ℤ} (hnxt : nxt = hornerStageSlide deg (d + 1) hb vec cur)
      (hdeg : 1 ≤ deg) (hk : k ≤ 15) (hlo : vec.length ≤ cur.length)
      (hhi : cur.length ≤ vec.length + k) :
      vec.length ≤ nxt.length ∧ nxt.length ≤ d + 1 ∧ nxt.length ≤ vec.length + (k + 1) ∧
        vecNorm (rkmListToOrbVec d nxt -
          horner16Step (rkmPtGenMat d hb) (rkmListToOrbVec d vec) (rkmListToOrbVec d cur) deg) ≤
          33 / wdScaleR := by
    rw [hnxt]; exact rkm_hornerStageSlide_chain hdeg hk hd hhb hvec_max hlo hhi
  let c15 := hornerStageSlide 16 (d + 1) hb vec vec
  have st15 := mkSt (cur := vec) (nxt := c15) rfl (by omega : 1 ≤ 16) (by omega : 0 ≤ 15)
    le_rfl (by omega)
  let c14 := hornerStageSlide 15 (d + 1) hb vec c15
  have st14 := mkSt (cur := c15) (nxt := c14) rfl (by omega : 1 ≤ 15) (by omega : 1 ≤ 15)
    st15.1 st15.2.2.1
  let c13 := hornerStageSlide 14 (d + 1) hb vec c14
  have st13 := mkSt (cur := c14) (nxt := c13) rfl (by omega : 1 ≤ 14) (by omega : 2 ≤ 15)
    st14.1 st14.2.2.1
  let c12 := hornerStageSlide 13 (d + 1) hb vec c13
  have st12 := mkSt (cur := c13) (nxt := c12) rfl (by omega : 1 ≤ 13) (by omega : 3 ≤ 15)
    st13.1 st13.2.2.1
  let c11 := hornerStageSlide 12 (d + 1) hb vec c12
  have st11 := mkSt (cur := c12) (nxt := c11) rfl (by omega : 1 ≤ 12) (by omega : 4 ≤ 15)
    st12.1 st12.2.2.1
  let c10 := hornerStageSlide 11 (d + 1) hb vec c11
  have st10 := mkSt (cur := c11) (nxt := c10) rfl (by omega : 1 ≤ 11) (by omega : 5 ≤ 15)
    st11.1 st11.2.2.1
  let c9 := hornerStageSlide 10 (d + 1) hb vec c10
  have st9 := mkSt (cur := c10) (nxt := c9) rfl (by omega : 1 ≤ 10) (by omega : 6 ≤ 15)
    st10.1 st10.2.2.1
  let c8 := hornerStageSlide 9 (d + 1) hb vec c9
  have st8 := mkSt (cur := c9) (nxt := c8) rfl (by omega : 1 ≤ 9) (by omega : 7 ≤ 15)
    st9.1 st9.2.2.1
  let c7 := hornerStageSlide 8 (d + 1) hb vec c8
  have st7 := mkSt (cur := c8) (nxt := c7) rfl (by omega : 1 ≤ 8) (by omega : 8 ≤ 15)
    st8.1 st8.2.2.1
  let c6 := hornerStageSlide 7 (d + 1) hb vec c7
  have st6 := mkSt (cur := c7) (nxt := c6) rfl (by omega : 1 ≤ 7) (by omega : 9 ≤ 15)
    st7.1 st7.2.2.1
  let c5 := hornerStageSlide 6 (d + 1) hb vec c6
  have st5 := mkSt (cur := c6) (nxt := c5) rfl (by omega : 1 ≤ 6) (by omega : 10 ≤ 15)
    st6.1 st6.2.2.1
  let c4 := hornerStageSlide 5 (d + 1) hb vec c5
  have st4 := mkSt (cur := c5) (nxt := c4) rfl (by omega : 1 ≤ 5) (by omega : 11 ≤ 15)
    st5.1 st5.2.2.1
  let c3 := hornerStageSlide 4 (d + 1) hb vec c4
  have st3 := mkSt (cur := c4) (nxt := c3) rfl (by omega : 1 ≤ 4) (by omega : 12 ≤ 15)
    st4.1 st4.2.2.1
  let c2 := hornerStageSlide 3 (d + 1) hb vec c3
  have st2 := mkSt (cur := c3) (nxt := c2) rfl (by omega : 1 ≤ 3) (by omega : 13 ≤ 15)
    st3.1 st3.2.2.1
  let c1 := hornerStageSlide 2 (d + 1) hb vec c2
  have st1 := mkSt (cur := c2) (nxt := c1) rfl (by omega : 1 ≤ 2) (by omega : 14 ≤ 15)
    st2.1 st2.2.2.1
  let c0 := hornerStageSlide 1 (d + 1) hb vec c1
  have st0 := mkSt (cur := c1) (nxt := c0) rfl (by omega : 1 ≤ 1) (by omega : 15 ≤ 15)
    st1.1 st1.2.2.1
  change c0.length ≤ d + 1 ∧
    vecNorm (rkmListToOrbVec d c0 -
      taylor16OfMat (rkmPtGenMat d hb) *ᵥ rkmListToOrbVec d vec) ≤ (297 / 2) / wdScaleR
  clear_value mkSt c15 c14 c13 c12 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0
  let seq : ℕ → Fin (d + 1) → ℝ := fun k ↦
    match k with
    | 0 => rkmListToOrbVec d vec | 1 => rkmListToOrbVec d c15
    | 2 => rkmListToOrbVec d c14 | 3 => rkmListToOrbVec d c13
    | 4 => rkmListToOrbVec d c12 | 5 => rkmListToOrbVec d c11
    | 6 => rkmListToOrbVec d c10 | 7 => rkmListToOrbVec d c9
    | 8 => rkmListToOrbVec d c8 | 9 => rkmListToOrbVec d c7
    | 10 => rkmListToOrbVec d c6 | 11 => rkmListToOrbVec d c5
    | 12 => rkmListToOrbVec d c4 | 13 => rkmListToOrbVec d c3
    | 14 => rkmListToOrbVec d c2 | 15 => rkmListToOrbVec d c1
    | _ => rkmListToOrbVec d c0
  have hstep : ∀ k < 16,
      vecNorm (seq (k + 1) - horner16Step (rkmPtGenMat d hb)
        (rkmListToOrbVec d vec) (seq k) (16 - k)) ≤ 33 / wdScaleR := by
    intro k hk
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    · exact st15.2.2.2
    · exact st14.2.2.2
    · exact st13.2.2.2
    · exact st12.2.2.2
    · exact st11.2.2.2
    · exact st10.2.2.2
    · exact st9.2.2.2
    · exact st8.2.2.2
    · exact st7.2.2.2
    · exact st6.2.2.2
    · exact st5.2.2.2
    · exact st4.2.2.2
    · exact st3.2.2.2
    · exact st2.2.2.2
    · exact st1.2.2.2
    · exact st0.2.2.2
    · omega
  have hε_nn : (0 : ℝ) ≤ 33 / wdScaleR := by unfold wdScaleR wdScale; positivity
  have hround := vecNorm_horner16_round_le hG hε_nn rfl hstep
  refine ⟨st0.2.1, ?_⟩
  calc vecNorm (rkmListToOrbVec d c0 -
          taylor16OfMat (rkmPtGenMat d hb) *ᵥ rkmListToOrbVec d vec)
      ≤ (9 / 2) * (33 / wdScaleR) := hround
    _ = (297 / 2) / wdScaleR := by ring

theorem rkmIterFullT16_approx {d : ℕ} {hb : List ℤ}
    (hd : d ≤ 1024) (hhb : hb.length ≤ d)
    (hG : ∀ u, vecNorm (rkmPtGenMat d hb *ᵥ u) ≤ (3 / 2) * vecNorm u)
    (s : ℕ) (vec : List ℤ) (hvec : vec.length ≤ d + 1) :
    (muxFastIterFullT16 s (d + 1) hb vec).length ≤ d + 1 ∧
      vecNorm (rkmListToOrbVec d (muxFastIterFullT16 s (d + 1) hb vec) -
        ((taylor16OfMat (rkmPtGenMat d hb)) ^ s) *ᵥ rkmListToOrbVec d vec) ≤
        ((297 / 2) * (s : ℝ)) / wdScaleR := by
  rw [muxFastIterFullT16_eq]
  induction s generalizing vec with
  | zero =>
    simp [altIterFullT16, hvec, pow_zero, Matrix.one_mulVec, vecNorm_zero]
  | succ s ih =>
    unfold altIterFullT16
    simp only [rkm_forceList_eq]
    obtain ⟨hl1, he1⟩ := rkm_hornerT16SlideStep_approx hd hhb hvec hG
    obtain ⟨hls, hes⟩ := ih (hornerT16SlideStep (d + 1) hb vec) hl1
    refine ⟨hls, ?_⟩
    set B := taylor16OfMat (rkmPtGenMat d hb)
    have hskew : (rkmPtGenMat d hb)ᵀ = -rkmPtGenMat d hb := tridiagSkewMat_transpose d _
    have hBs_contr (w : Fin (d + 1) → ℝ) : vecNorm ((B ^ s) *ᵥ w) ≤ vecNorm w := by
      have hB_contr (u : Fin (d + 1) → ℝ) : vecNorm (B *ᵥ u) ≤ 1 * vecNorm u := by
        rw [one_mul]; exact vecNorm_taylor16OfMat_mulVec_le hskew hG u
      simpa using vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) hB_contr s w
    have hsplit : rkmListToOrbVec d (altIterFullT16 s (d + 1) hb
          (hornerT16SlideStep (d + 1) hb vec)) -
        (B ^ (s + 1)) *ᵥ rkmListToOrbVec d vec =
        (rkmListToOrbVec d (altIterFullT16 s (d + 1) hb
            (hornerT16SlideStep (d + 1) hb vec)) -
          (B ^ s) *ᵥ rkmListToOrbVec d (hornerT16SlideStep (d + 1) hb vec)) +
        (B ^ s) *ᵥ (rkmListToOrbVec d (hornerT16SlideStep (d + 1) hb vec) -
          B *ᵥ rkmListToOrbVec d vec) := by
      rw [pow_succ, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      ext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [hsplit]
    calc vecNorm ((rkmListToOrbVec d (altIterFullT16 s (d + 1) hb
              (hornerT16SlideStep (d + 1) hb vec)) -
            (B ^ s) *ᵥ rkmListToOrbVec d (hornerT16SlideStep (d + 1) hb vec)) +
            (B ^ s) *ᵥ (rkmListToOrbVec d (hornerT16SlideStep (d + 1) hb vec) -
              B *ᵥ rkmListToOrbVec d vec))
        ≤ vecNorm (rkmListToOrbVec d (altIterFullT16 s (d + 1) hb
              (hornerT16SlideStep (d + 1) hb vec)) -
            (B ^ s) *ᵥ rkmListToOrbVec d (hornerT16SlideStep (d + 1) hb vec)) +
            vecNorm ((B ^ s) *ᵥ (rkmListToOrbVec d (hornerT16SlideStep (d + 1) hb vec) -
              B *ᵥ rkmListToOrbVec d vec)) := vecNorm_add_le _ _
      _ ≤ ((297 / 2) * (s : ℝ)) / wdScaleR + (297 / 2) / wdScaleR :=
          add_le_add hes ((hBs_contr _).trans he1)
      _ = ((297 / 2) * ((s + 1 : ℕ) : ℝ)) / wdScaleR := by push_cast; ring

theorem rkmTaylor8_sub_taylor16_pow_vec_le {n m r K : ℕ}
    (hn : 80000 ≤ n) (_hm1 : 1 ≤ m) (hm : m ≤ 8192) (_hr1 : 1 ≤ r) (hr : r ≤ 1024)
    (hK : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ))
    {u : Fin (orbDim m r) → ℝ} (hu : vecNorm u ≤ 1) :
    vecNorm (((taylor8Mat (1 / √(2 ^ n : ℝ)) (dAltGenMat m r)) ^ K) *ᵥ u -
      ((taylor16Mat (1 / √(2 ^ n : ℝ)) (dAltGenMat m r)) ^ K) *ᵥ u) ≤
      1 / wdScaleR := by
  set η : ℝ := 1 / √(2 ^ n : ℝ)
  set G := dAltGenMat m r
  set B8 := taylor8Mat η G
  set B16 := taylor16Mat η G
  have hN_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have hsN_ge100 : (2 : ℝ) ^ 100 ≤ √(2 ^ n : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans
      (pow_le_pow_right₀ (by norm_num) (by omega : 200 ≤ n)))
  have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge100
  have hG_bound : ∀ v, vecNorm (G *ᵥ v) ≤ (2 : ℝ) ^ 19 * vecNorm v := by
    intro v
    have hbd : dAltGenNormBound m r ≤ (2 : ℝ) ^ 19 := by
      unfold dAltGenNormBound
      rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩; rw [← pow_mul]
      have hmax : max m r ≤ 8192 := max_le hm (hr.trans (by omega))
      have hnat : 4 * (min m r + 1) ^ 2 * max m r ≤ 4 * 1025 ^ 2 * 8192 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4
          (Nat.pow_le_pow_left (by have := Nat.min_le_right m r; omega) 2)) hmax
      exact (by exact_mod_cast hnat : _ ≤ ((4 * 1025 ^ 2 * 8192 : ℕ) : ℝ)).trans (by norm_num)
    exact (vecNorm_dAltGenMat_mulVec_le m r v).trans
      (mul_le_mul_of_nonneg_right hbd (vecNorm_nonneg v))
  have hηB_le1 : η * (2 : ℝ) ^ 19 ≤ 1 := by
    dsimp only [η]
    rw [one_div_mul_eq_div, div_le_one hsN_pos]
    exact (by norm_num : (2 : ℝ) ^ 19 ≤ (2 : ℝ) ^ 100).trans hsN_ge100
  have hB8_contr : ∀ x, vecNorm (B8 *ᵥ x) ≤ vecNorm x := fun x ↦
    vecNorm_taylor8Mat_mulVec_le (dAltGenMat_transpose m r) (by positivity) (by positivity)
      hG_bound hηB_le1 x
  have hB16_contr : ∀ x, vecNorm (B16 *ᵥ x) ≤ vecNorm x := fun x ↦
    vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose m r) (by positivity) (by positivity)
      hG_bound (hηB_le1.trans (by norm_num)) x
  have hdiff_op : ∀ x, vecNorm ((B8 - B16) *ᵥ x) ≤ ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x := by
    intro x
    set X := η • G
    have hX_op : ∀ v, vecNorm (X *ᵥ v) ≤ (η * (2 : ℝ) ^ 19) * vecNorm v := fun v ↦ by
      dsimp only [X]
      rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg (by positivity : 0 ≤ η)]
      exact (mul_le_mul_of_nonneg_left (hG_bound v) (by positivity)).trans_eq (by ring)
    have hc_sq : (η * (2 : ℝ) ^ 19) ^ 2 = (2 : ℝ) ^ 38 / (2 ^ n : ℝ) := by
      dsimp only [η]; rw [one_div_mul_eq_div, div_pow, Real.sq_sqrt hN_pos.le, ← pow_mul]
    have hpow_le (k : ℕ) (hk : 2 ≤ k) :
        vecNorm ((X ^ k) *ᵥ x) ≤ ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x := by
      have h1 := vecNorm_pow_mulVec_le (by positivity) hX_op k x
      have h2 : (η * (2 : ℝ) ^ 19) ^ k ≤ (η * (2 : ℝ) ^ 19) ^ 2 :=
        pow_le_pow_of_le_one (by positivity) hηB_le1 hk
      rw [hc_sq] at h2
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (vecNorm_nonneg x))
    set t9 := (1 / 362880 : ℝ) • ((X ^ 9) *ᵥ x)
    set t10 := (1 / 3628800 : ℝ) • ((X ^ 10) *ᵥ x)
    set t11 := (1 / 39916800 : ℝ) • ((X ^ 11) *ᵥ x)
    set t12 := (1 / 479001600 : ℝ) • ((X ^ 12) *ᵥ x)
    set t13 := (1 / 6227020800 : ℝ) • ((X ^ 13) *ᵥ x)
    set t14 := (1 / 87178291200 : ℝ) • ((X ^ 14) *ᵥ x)
    set t15 := (1 / 1307674368000 : ℝ) • ((X ^ 15) *ᵥ x)
    set t16 := (1 / 20922789888000 : ℝ) • ((X ^ 16) *ᵥ x)
    have hexp : (B16 - B8) *ᵥ x =
        t9 + (t10 + (t11 + (t12 + (t13 + (t14 + (t15 + t16)))))) := by
      ext idx
      dsimp only [t9, t10, t11, t12, t13, t14, t15, t16, B8, B16, X,
        taylor8Mat, taylor8OfMat, taylor16Mat, taylor16OfMat]
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hneg_eq : (B8 - B16) *ᵥ x = -((B16 - B8) *ᵥ x) := by
      ext idx; simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.neg_apply]; ring
    rw [hneg_eq, vecNorm_neg, hexp]
    have hsm (c : ℝ) (hc0 : 0 ≤ c) (k : ℕ) (hk : 2 ≤ k) :
        vecNorm (c • ((X ^ k) *ᵥ x)) ≤ c * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) := by
      rw [vecNorm_smul, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left (hpow_le k hk) hc0
    have ha1 := vecNorm_add_le t9 (t10 + (t11 + (t12 + (t13 + (t14 + (t15 + t16))))))
    have ha2 := vecNorm_add_le t10 (t11 + (t12 + (t13 + (t14 + (t15 + t16)))))
    have ha3 := vecNorm_add_le t11 (t12 + (t13 + (t14 + (t15 + t16))))
    have ha4 := vecNorm_add_le t12 (t13 + (t14 + (t15 + t16)))
    have ha5 := vecNorm_add_le t13 (t14 + (t15 + t16))
    have ha6 := vecNorm_add_le t14 (t15 + t16)
    have ha7 := vecNorm_add_le t15 t16
    have hb9 : vecNorm t9 ≤ (1 / 362880) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 362880) (by norm_num) 9 (by omega)
    have hb10 : vecNorm t10 ≤ (1 / 3628800) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 3628800) (by norm_num) 10 (by omega)
    have hb11 : vecNorm t11 ≤ (1 / 39916800) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 39916800) (by norm_num) 11 (by omega)
    have hb12 : vecNorm t12 ≤ (1 / 479001600) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 479001600) (by norm_num) 12 (by omega)
    have hb13 : vecNorm t13 ≤ (1 / 6227020800) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 6227020800) (by norm_num) 13 (by omega)
    have hb14 : vecNorm t14 ≤ (1 / 87178291200) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 87178291200) (by norm_num) 14 (by omega)
    have hb15 : vecNorm t15 ≤ (1 / 1307674368000) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 1307674368000) (by norm_num) 15 (by omega)
    have hb16 : vecNorm t16 ≤ (1 / 20922789888000) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x) :=
      hsm (1 / 20922789888000) (by norm_num) 16 (by omega)
    have hnn : 0 ≤ ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x :=
      mul_nonneg (by positivity) (vecNorm_nonneg x)
    linarith [ha1, ha2, ha3, ha4, ha5, ha6, ha7, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16,
      hnn]
  have htel := vecNorm_pow_mulVec_sub_le hB8_contr hB16_contr (by positivity) hdiff_op K u u
  rw [sub_self, vecNorm_zero, zero_add] at htel
  have hsqN : (2 ^ n : ℝ) = √(2 ^ n : ℝ) * √(2 ^ n : ℝ) := (Real.mul_self_sqrt hN_pos.le).symm
  have hstep1 : (K : ℝ) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm u) ≤
      (4 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ) := by
    have h1 : (K : ℝ) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm u) ≤
        (4 * √(2 ^ n : ℝ)) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1) :=
      mul_le_mul hK (mul_le_mul_of_nonneg_left hu (by positivity))
        (mul_nonneg (by positivity) (vecNorm_nonneg u)) (by positivity)
    refine h1.trans_eq ?_
    have hmul : ((4 * √(2 ^ n : ℝ)) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1)) * √(2 ^ n : ℝ) =
        ((4 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ)) * √(2 ^ n : ℝ) := by
      calc ((4 * √(2 ^ n : ℝ)) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1)) * √(2 ^ n : ℝ)
          = (4 * (2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * (√(2 ^ n : ℝ) * √(2 ^ n : ℝ)) := by ring
        _ = (4 * (2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * (2 ^ n : ℝ) := by rw [← hsqN]
        _ = 4 * (2 : ℝ) ^ 38 := div_mul_cancel₀ _ hN_pos.ne'
        _ = ((4 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ)) * √(2 ^ n : ℝ) :=
            (div_mul_cancel₀ _ hsN_pos.ne').symm
    exact mul_right_cancel₀ hsN_pos.ne' hmul
  have hstep2 : (4 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ) ≤ 1 / wdScaleR := by
    have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
    rw [hB_eq, div_le_div_iff₀ hsN_pos (by norm_num)]
    linarith [hsN_ge100, (by norm_num : (4 * (2 : ℝ) ^ 38) * 1000000000000000 ≤ (2 : ℝ) ^ 100)]
  exact htel.trans ((by ring_nf; exact le_rfl :
    (K : ℝ) * ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm u ≤
      (K : ℝ) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm u)).trans (hstep1.trans hstep2))

end
end QuantumComputation.Specs.DickeSol
end Sec_FindAllJohnsonRampKickMuxKernelA
section Sec_FindAllJohnsonRampKickMuxKernelB
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
open Real
open scoped Matrix NNRat NNReal ENNReal
/-- Structural multi-segment `T_16` + `mask` orbital evaluator loop. -/
def rkmEvalSegsLoop (m lTableMax r : ℕ) :
    List ℕ → List ℕ → List ℕ → List (List Bool) → ℕ → ℕ → ℕ → List ℤ → (ℕ × ℕ × List ℤ)
  | [], tauRem, nsubRem, maskRem, _, dEnd, accPad, vec =>
    match tauRem, nsubRem, maskRem with
    | [], [], [] => (dEnd, accPad, vec)
    | _, _, _ => (0, 0, [])
  | lS :: lRest, tau9 :: tauRest, nSub :: nsubRest, mask :: maskRest, lPrev, _, accPad, vec =>
    let mEff := Nat.mul lS m
    let d := highdNatMin mEff r
    cond (Bool.or (primNatBlt lS 1)
      (Bool.or (primNatBlt lS lPrev)
      (Bool.or (primNatBlt lTableMax lS)
      (Bool.or (primNatBlt mEff 1)
      (Bool.or (primNatBlt 8192 mEff)
      (Bool.or (primNatBlt d 1)
      (Bool.or (Nat.beq tau9 0)
      (Bool.or (primNatBlt 4000000000 tau9)
      (Bool.or (Nat.beq nSub 0)
      (Bool.or (primNatBlt 16384 nSub)
        (primNatBlt (Nat.add d 1) (rkmBoolListLen mask))))))))))))
      (0, 0, [])
      (let hPtRaw := Nat.div (Nat.mul tau9 1000000) nSub
       HighDForce.withForcedNat hPtRaw fun hPt =>
         cond (primNatBlt hPt 1)
           (0, 0, [])
           (let maxBRaw := altMaxBHiFrom mEff r 0 d
            HighDForce.withForcedNat maxBRaw fun maxBHi15 =>
              let bCapHi15 := Nat.mul 2 maxBHi15
              let hgRaw := highdMulCeil15 (Nat.add 2 hPt) bCapHi15
              HighDForce.withForcedNat hgRaw fun hgHi15 =>
                cond (Bool.or (primNatBlt 1500000000000000 hgHi15)
                    (Bool.not (altCheckHbTight mEff r 0 d)))
                  (0, 0, [])
                  (let hgPow := altPow17Ceil15 hgHi15
                   let truncPad15 :=
                     Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000
                   let bCapCeil := Nat.div (Nat.add 999999999999999 bCapHi15) wdScale
                   let segPad := Nat.add (Nat.add truncPad15 256)
                     (Nat.mul nSub (Nat.add 256 (Nat.mul 10 bCapCeil)))
                   let nextPadRaw := Nat.add accPad segPad
                   HighDForce.withForcedNat nextPadRaw fun nextPad =>
                     cond (Bool.or (Nat.beq nextPad 0)
                         (primNatBlt 100000000000000 nextPad))
                       (0, 0, [])
                       (let hbRaw := altBuildHbFrom mEff r hPt 0 d
                        HighDForce.withForcedList hbRaw fun hbPt =>
                          let wRaw := muxFastIterFullT16 nSub (Nat.add d 1) hbPt vec
                          HighDForce.withForcedList wRaw fun vWalk =>
                            let kRaw := rkmApplyMaskBits mask vWalk
                            HighDForce.withForcedList kRaw fun vNext =>
                              rkmEvalSegsLoop m lTableMax r lRest tauRest nsubRest maskRest
                                lS d nextPad vNext))))
  | _, _, _, _, _, _, _, _ => (0, 0, [])
/-- Evaluates the `10 ^ 12`-scaled hit-probability lower-bound row of a multi-segment
  width-ramped + prefix-kick `T_16` trajectory. -/
def rkmEvalT16Lo12 (m lTableMax r : ℕ)
    (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool)) : List ℕ :=
  let nSegs := altListLen lSegs
  cond (Bool.or (Nat.beq nSegs 0)
    (Bool.or (primNatBlt 8 nSegs)
    (Bool.or (primNatBlt r 2) (primNatBlt 1024 r))))
    []
    (let res := rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks
       1 0 0 [Int.ofNat wdScale]
     match res with
     | (dEnd, accPad, vecFinal) =>
       cond (Bool.or (Nat.beq dEnd 0) (Nat.beq accPad 0))
         []
         (let padded := altPadRightInts (Nat.add dEnd 1) vecFinal
          match padded with
          | [] => []
          | _ :: tail => altVecTailToLo12 accPad tail))
end
public section
open Real
open scoped Matrix NNRat NNReal ENNReal
private theorem rkmb_cond_true {α : Type} (a b : α) : (cond true a b) = a := rfl
private theorem rkmb_cond_false {α : Type} (a b : α) : (cond false a b) = b := rfl
private theorem rkmb_nat_ble_eq_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkmb_nat_ble_eq_true]
private theorem rkmb_nat_ble_eq_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, rkmb_nat_ble_eq_true]; omega
private theorem rkmb_nat_blt_eq_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  unfold Nat.blt; exact rkmb_nat_ble_eq_true
private theorem rkmb_nat_blt_eq_false {a b : ℕ} : Nat.blt a b = false ↔ b ≤ a := by
  unfold Nat.blt; rw [rkmb_nat_ble_eq_false]; omega
private theorem rkmb_primNatBlt_eq {a b : ℕ} : primNatBlt a b = Nat.blt a b := rfl
private theorem rkmb_nat_beq_eq_true : ∀ {a b : ℕ}, Nat.beq a b = true ↔ a = b
  | 0, 0 => by simp [Nat.beq]
  | 0, _ + 1 => by simp [Nat.beq]
  | _ + 1, 0 => by simp [Nat.beq]
  | a + 1, b + 1 => by simp [Nat.beq, rkmb_nat_beq_eq_true]
private theorem rkmb_nat_beq_eq_false {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, rkmb_nat_beq_eq_true]
theorem rkmb_natMin_eq (a b : ℕ) : highdNatMin a b = min a b := by
  unfold highdNatMin
  cases h : Nat.ble a b
  · simp [cond, Nat.min_eq_right (rkmb_nat_ble_eq_false.mp h).le]
  · simp [cond, Nat.min_eq_left (rkmb_nat_ble_eq_true.mp h)]
theorem rkmb_altListLen_eq : ∀ xs : List ℕ, altListLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (rkmb_altListLen_eq xs)
theorem rkmb_forceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) : HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]
theorem rkmb_forceList_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by
  cases xs <;> rfl
private theorem rkmb_strictConsInt_eq (x : ℤ) (xs : List ℤ) :
    highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.ofNat 0] | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t) =
      Int.ofNat n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]; cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.negSucc 0] | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t) =
      Int.negSucc n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]; cases xs <;> rfl
private theorem rkmb_ceil_div_mul_ge (n d : ℕ) (hd : 0 < d) : n ≤ (((d - 1) + n) / d) * d := by
  have h := Nat.lt_mul_div_succ ((d - 1) + n) hd
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d] at h; omega
private theorem rkmb_mulCeil15_ge (a b : ℕ) :
    ((a : ℝ) / wdScaleR) * ((b : ℝ) / wdScaleR) ≤ (highdMulCeil15 a b : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  have hnat : a * b ≤ highdMulCeil15 a b * wdScale := by
    have h := rkmb_ceil_div_mul_ge (a * b) wdScale (by unfold wdScale; positivity)
    have hsub : wdScale - 1 = 999999999999999 := by unfold wdScale; rfl
    rw [hsub] at h; exact h
  have hreal : (a : ℝ) * (b : ℝ) ≤ (highdMulCeil15 a b : ℝ) * wdScaleR := by
    unfold wdScaleR; exact_mod_cast hnat
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hB hB) hB]
  exact (mul_le_mul_of_nonneg_right hreal hB.le).trans_eq (by ring)
private theorem rkmb_powCeilLoop_ge (x : ℕ) :
    ∀ (k acc : ℕ) {p : ℝ}, 0 ≤ p → p ≤ (acc : ℝ) / wdScaleR →
      p * ((x : ℝ) / wdScaleR) ^ k ≤ (highdPowCeilLoop k acc x : ℝ) / wdScaleR := by
  intro k
  induction k with
  | zero => intro acc p _ hacc; dsimp only [highdPowCeilLoop]; simpa using hacc
  | succ k ih =>
    intro acc p hp0 hacc; dsimp only [highdPowCeilLoop]
    have hx0 : 0 ≤ (x : ℝ) / wdScaleR := by unfold wdScaleR wdScale; positivity
    have hnext : p * ((x : ℝ) / wdScaleR) ≤ (highdMulCeil15 acc x : ℝ) / wdScaleR :=
      (mul_le_mul_of_nonneg_right hacc hx0).trans (rkmb_mulCeil15_ge acc x)
    simpa only [pow_succ', ← mul_assoc] using ih (highdMulCeil15 acc x) (mul_nonneg hp0 hx0) hnext
private theorem rkmb_pow17Ceil15_ge (x : ℕ) :
    ((x : ℝ) / wdScaleR) ^ 17 ≤ (altPow17Ceil15 x : ℝ) / wdScaleR := by
  have hx0 : 0 ≤ (x : ℝ) / wdScaleR := by unfold wdScaleR wdScale; positivity
  dsimp only [altPow17Ceil15]; simpa only [pow_succ'] using rkmb_powCeilLoop_ge x 16 x hx0 le_rfl
private theorem rkmb_maxBHiFrom_ge (m r : ℕ) : ∀ (rem w j : ℕ), j < rem →
      (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤ altMaxBHiFrom m r w rem
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, j, hj => by
    unfold altMaxBHiFrom altMaxBHiFromAux; simp only [rkmb_forceNat_eq, rkmb_primNatBlt_eq]
    set rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    set bHi := (altIsqrt15 rad).2; set rMax := altMaxBHiFromAux m r rem (Nat.add w 1)
    rcases j with _ | j'
    · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) = rad := by
        change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
          4 * (w + 1) * (m - w) * (r - w); simp
      rw [hrad]
      cases hlt : Nat.blt rMax bHi
      · simp only [cond]; exact rkmb_nat_blt_eq_false.mp hlt
      · simp only [cond]; exact le_rfl
    · have ih := rkmb_maxBHiFrom_ge m r rem (w + 1) j' (by omega)
      rw [show w + 1 + j' = w + (j' + 1) by omega] at ih
      have ih' : (altIsqrt15 (4 * (w + (j' + 1) + 1) * (m - (w + (j' + 1))) *
          (r - (w + (j' + 1))))).2 ≤ rMax := ih
      cases hlt : Nat.blt rMax bHi
      · simp only [cond]; exact ih'
      · simp only [cond]; exact ih'.trans (rkmb_nat_blt_eq_true.mp hlt).le
private theorem rkmb_checkHbTight_sound (m r : ℕ) :
    ∀ (rem w : ℕ), altCheckHbTight m r w rem = true → ∀ j < rem,
        (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤
          (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1 + 1
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, hchk, j, hj => by
    unfold altCheckHbTight altCheckHbTightAux at hchk; dsimp only at hchk
    generalize hp : altIsqrt15 (Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1))
      (Nat.sub m w)) (Nat.sub r w)) = p at hchk
    cases hble : Nat.ble p.2 (Nat.add p.1 1) with
    | false => rw [hble, rkmb_cond_false] at hchk; exact Bool.noConfusion hchk
    | true =>
      rw [hble, rkmb_cond_true] at hchk
      rcases j with _ | j'
      · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w) := by
          change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            4 * (w + 1) * (m - w) * (r - w); simp
        rw [hrad, hp]; exact rkmb_nat_ble_eq_true.mp hble
      · simpa [show w + 1 + j' = w + (j' + 1) by omega] using
          rkmb_checkHbTight_sound m r rem (w + 1) hchk j' (by omega)
private theorem rkmb_buildHbFrom_length (m r hPt : ℕ) :
    ∀ (rem w : ℕ), (altBuildHbFrom m r hPt w rem).length = rem
  | 0, _ => rfl
  | rem + 1, w => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    exact congrArg Nat.succ (rkmb_buildHbFrom_length m r hPt rem (w + 1))
private theorem rkmb_buildHbFrom_getD (m r hPt : ℕ) : ∀ (rem w j : ℕ), j < rem →
      (altBuildHbFrom m r hPt w rem).getD j 0 =
        (((hPt * (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1) /
          wdScale : ℕ) : ℤ)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, 0, _ => by
    unfold altBuildHbFrom altBuildHbFromAux; rw [strictConsInt_eq]
    change (((hPt * (altIsqrt15 (4 * (w + 1) * (m - w) * (r - w))).1) / wdScale : ℕ) : ℤ) = _; simp
  | rem + 1, w, j + 1, hj => by
    dsimp only [altBuildHbFrom, altBuildHbFromAux]
    rw [strictConsInt_eq, List.getD_cons_succ, show Nat.add w 1 = w + 1 from rfl]
    have ih := rkmb_buildHbFrom_getD m r hPt rem (w + 1) j (by omega)
    dsimp only [altBuildHbFrom] at ih; simpa [show w + 1 + j = w + (j + 1) by omega] using ih
private theorem rkmb_substep_bounds {n tau9 nSub : ℕ}
    (hn : altN0 ≤ n) (htau : tau9 ≤ 4000000000) (hnsub1 : 1 ≤ nSub) (hnsub : nSub ≤ 16384) :
    let q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
    let hPt := (tau9 * 1000000) / nSub
    0 ≤ (q : ℝ) / √(2 ^ n : ℝ) ∧ (q : ℝ) / √(2 ^ n : ℝ) ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR ∧
      |(q : ℝ) / √(2 ^ n : ℝ) - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
  intro q hPt; set N := 2 ^ n
  have hN_cast : (2 : ℝ) ^ n = (N : ℝ) := by dsimp [N]; norm_cast
  rw [hN_cast]
  have h200 : 200 ≤ n := by unfold altN0 at hn; omega
  have hN_ge : (2 : ℝ) ^ 200 ≤ (N : ℝ) := by
    dsimp [N]; rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_le_pow_right₀ (by norm_num) h200
  have hsqrtN_ge : (2 : ℝ) ^ 100 ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans hN_ge)
  have hsqrtN_pos : 0 < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsqrtN_ge
  have hnsub_pos : (0 : ℝ) < (nSub : ℝ) := by exact_mod_cast hnsub1
  have hB : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB]; positivity
  have hhPt_lo : (hPt : ℝ) / wdScaleR ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hR : (hPt : ℝ) * (nSub : ℝ) ≤ (tau9 : ℝ) * 1000000 := by
      exact_mod_cast Nat.div_mul_le_self (tau9 * 1000000) nSub
    rw [hB, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hhPt_hi : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) ≤ ((hPt + 1 : ℕ) : ℝ) / wdScaleR := by
    have hnat : tau9 * 1000000 < (hPt + 1) * nSub :=
      (Nat.lt_mul_div_succ _ (by omega : 0 < nSub)).trans_eq (Nat.mul_comm _ _)
    have hR : (tau9 : ℝ) * 1000000 ≤ ((hPt + 1 : ℕ) : ℝ) * (nSub : ℝ) := by exact_mod_cast hnat.le
    rw [hB, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hq_hi : (q : ℝ) / √(N : ℝ) ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hR : ((nSub : ℝ) * 1000000000) * (q : ℝ) ≤ (tau9 : ℝ) * (Nat.sqrt N : ℝ) := by
      exact_mod_cast Nat.mul_div_le (tau9 * Nat.sqrt N) (nSub * 1000000000)
    have hsq : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) :=
      Real.le_sqrt_of_sq_le (by simpa [sq, Nat.cast_mul] using
        (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le N))
    rw [div_le_div_iff₀ hsqrtN_pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg tau9)]
  have hq_lo : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) - (q : ℝ) / √(N : ℝ) ≤ 1 / wdScaleR := by
    set S_N := Nat.sqrt N
    have hS_gt : √(N : ℝ) ≤ (S_N : ℝ) + 1 := by
      rw [Real.sqrt_le_iff]; refine ⟨by positivity, ?_⟩
      have hlt := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N); push_cast at hlt; linarith
    have hdiv_lt : tau9 * S_N < (q + 1) * (nSub * 1000000000) :=
      (Nat.lt_mul_div_succ _ (by positivity : 0 < nSub * 1000000000)).trans_eq (Nat.mul_comm _ _)
    have hdivR : (tau9 : ℝ) * (S_N : ℝ) ≤ ((q : ℝ) + 1) * ((nSub : ℝ) * 1000000000) := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hdiv_lt.le; push_cast at hc; linarith
    have htauR : (tau9 : ℝ) ≤ 4000000000 := by exact_mod_cast htau
    have hnsubR : (nSub : ℝ) ≤ 16384 := by exact_mod_cast hnsub
    have hgap : (tau9 : ℝ) * √(N : ℝ) - (q : ℝ) * ((nSub : ℝ) * 1000000000) ≤ 20384000000000 := by
      nlinarith [mul_le_mul_of_nonneg_left hS_gt (Nat.cast_nonneg tau9)]
    have hbig : (20384000000000 : ℝ) * 1000000000000000 ≤
        ((nSub : ℝ) * 1000000000) * √(N : ℝ) := by
      have h1 : (20384000000000 : ℝ) * 1000000000000000 ≤ 1000000000 * (2 : ℝ) ^ 100 := by norm_num
      have h2 : (1 : ℝ) ≤ (nSub : ℝ) := by exact_mod_cast hnsub1
      nlinarith
    rw [hB, div_sub_div _ _ (by positivity) hsqrtN_pos.ne',
      div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine ⟨div_nonneg (Nat.cast_nonneg q) hsqrtN_pos.le,
    hq_hi.trans (hhPt_hi.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast (by omega : hPt + 1 ≤ 2 + hPt)) hB_pos.le)), ?_⟩
  rw [abs_le]; refine ⟨by linarith [hhPt_lo, hq_lo], ?_⟩
  have h1 : ((hPt + 1 : ℕ) : ℝ) / wdScaleR - (hPt : ℝ) / wdScaleR = 1 / wdScaleR := by
    push_cast; ring
  linarith [hq_hi, hhPt_hi, h1]
/-- Single-segment orbital `T_16` + `mask` bound from a unit-bounded continuum vector `uIn`
  and
  quantized integer list `vec`. -/
theorem rkmSingleSegT16_bound {n mEff r tau9 nSub : ℕ} {mask : List Bool} {vec : List ℤ}
    (hn : altN0 ≤ n) (hm1 : 1 ≤ mEff) (hm_hi : mEff ≤ 8192)
    (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024)
    (_htau_pos : 0 < tau9) (htau_hi : tau9 ≤ 4000000000)
    (hnsub_pos : 0 < nSub) (hnsub_hi : nSub ≤ 16384)
    (hhg_le : highdMulCeil15 (2 + (tau9 * 1000000) / nSub)
      (2 * altMaxBHiFrom mEff r 0 (min mEff r)) ≤ 1500000000000000)
    (htight : altCheckHbTight mEff r 0 (min mEff r) = true)
    (hvec_len : vec.length ≤ min mEff r + 1)
    {uIn : Fin (orbDim mEff r) → ℝ} (huIn : vecNorm uIn ≤ 1) :
    let d := min mEff r
    let hPt := (tau9 * 1000000) / nSub
    let bCapHi15 := 2 * altMaxBHiFrom mEff r 0 d
    let hgHi15 := highdMulCeil15 (2 + hPt) bCapHi15
    let truncPad15 := (299999999999999 + nSub * altPow17Ceil15 hgHi15) / 300000000000000
    let bCapCeil := (999999999999999 + bCapHi15) / wdScale
    let segPad := (truncPad15 + 256) + nSub * (256 + 10 * bCapCeil)
    let hbPt := altBuildHbFrom mEff r hPt 0 d
    let vNext := rkmApplyMaskBits mask (muxFastIterFullT16 nSub (d + 1) hbPt vec)
    let K := altStepCount tau9 nSub (2 ^ n)
    ∃ uOut : Fin (orbDim mEff r) → ℝ, vecNorm uOut ≤ 1 ∧ vNext.length ≤ d + 1 ∧
      vecNorm (rkmMaskSignVec d mask (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn) - uOut) +
        vecNorm (uOut - rkmListToOrbVec d vNext) ≤
        vecNorm (uIn - rkmListToOrbVec d vec) + ((segPad : ℝ) - 253) / wdScaleR := by
  intro d hPt bCapHi15 hgHi15 truncPad15 bCapCeil segPad hbPt vNext K
  have hhPt_def : hPt = (tau9 * 1000000) / nSub := rfl
  have hbCapHi_def : bCapHi15 = 2 * altMaxBHiFrom mEff r 0 d := rfl
  have hhg_def : hgHi15 = highdMulCeil15 (2 + hPt) bCapHi15 := rfl
  have htrunc_def :
      truncPad15 = (299999999999999 + nSub * altPow17Ceil15 hgHi15) / 300000000000000 := rfl
  have hbCapCeil_def : bCapCeil = (999999999999999 + bCapHi15) / wdScale := rfl
  have hseg_def : segPad = (truncPad15 + 256) + nSub * (256 + 10 * bCapCeil) := rfl
  have hhbPt_def : hbPt = altBuildHbFrom mEff r hPt 0 d := rfl
  have hvNext_def : vNext = rkmApplyMaskBits mask (muxFastIterFullT16 nSub (d + 1) hbPt vec) := rfl
  have hK_def : K = altStepCount tau9 nSub (2 ^ n) := rfl
  have hhg_le' : hgHi15 ≤ 1500000000000000 := hhg_le
  clear_value hPt bCapHi15 hgHi15 truncPad15 bCapCeil segPad hbPt vNext K
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  have hn80 : 80000 ≤ n := hn
  have hsN_ge100 : (2 : ℝ) ^ 100 ≤ √(2 ^ n : ℝ) :=
    Real.le_sqrt_of_sq_le ((by norm_num : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ 200).trans
      (pow_le_pow_right₀ (by norm_num) (by omega : 200 ≤ n)))
  have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge100
  set q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
  have hK_eq : K = nSub * q := by rw [hK_def]; rfl
  have hK_le : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ) := by
    have h1 : (K : ℝ) ≤ ((tau9 : ℝ) / 1000000000) * √(2 ^ n : ℝ) := by
      rw [hK_def]
      simpa [Nat.cast_pow, Nat.cast_ofNat] using altStepCount_le_tau_sqrt tau9 nSub (2 ^ n)
    have htauR : (tau9 : ℝ) / 1000000000 ≤ 4 := by
      have hc : (tau9 : ℝ) ≤ 4000000000 := by exact_mod_cast htau_hi
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right htauR hsN_pos.le)
  set η : ℝ := 1 / √(2 ^ n : ℝ)
  have hη_nn : 0 ≤ η := by positivity
  set G := dAltGenMat mEff r
  have hcont : vecNorm (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn -
      ((taylor16Mat η G) ^ K) *ᵥ uIn) ≤ (3 / 2) / wdScaleR := by
    have ht8 : vecNorm (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn -
        ((taylor8Mat η G) ^ K) *ᵥ uIn) ≤ 1 / (2 * wdScaleR) := by
      have h := vecNorm_dAltStepOrbMat_pow_sub_taylor8_vec_le hn hm1 hm_hi (by omega) hr_hi
        hK_le (u := uIn) huIn
      rw [sub_self, vecNorm_zero, zero_add] at h; simpa [wdScaleR, η, G] using h
    have ht16 : vecNorm (((taylor8Mat η G) ^ K) *ᵥ uIn -
        ((taylor16Mat η G) ^ K) *ᵥ uIn) ≤ 1 / wdScaleR :=
      rkmTaylor8_sub_taylor16_pow_vec_le hn80 hm1 hm_hi (by omega) hr_hi hK_le huIn
    have hsp : ((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn - ((taylor16Mat η G) ^ K) *ᵥ uIn =
        (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn - ((taylor8Mat η G) ^ K) *ᵥ uIn) +
        (((taylor8Mat η G) ^ K) *ᵥ uIn - ((taylor16Mat η G) ^ K) *ᵥ uIn) :=
      (sub_add_sub_cancel _ _ _).symm
    rw [hsp]
    have htri := vecNorm_add_le
      (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn - ((taylor8Mat η G) ^ K) *ᵥ uIn)
      (((taylor8Mat η G) ^ K) *ᵥ uIn - ((taylor16Mat η G) ^ K) *ᵥ uIn)
    have hsum : 1 / (2 * wdScaleR) + 1 / wdScaleR = (3 / 2) / wdScaleR := by ring
    linarith [htri, ht8, ht16, hsum]
  set B_cap := (bCapHi15 : ℝ) / wdScaleR
  have hBc_nn : 0 ≤ B_cap := div_nonneg (Nat.cast_nonneg _) hB_pos.le
  have hcoupl_cap (j : ℕ) (hj : j < d) : |dAltCoupling mEff r j| ≤ (1 / 2) * B_cap := by
    have hc0 : 0 ≤ dAltCoupling mEff r j := by unfold dAltCoupling; positivity
    rw [abs_of_nonneg hc0]; have hmax_j := rkmb_maxBHiFrom_ge mEff r d 0 j hj
    set rad := 4 * (j + 1) * (mEff - j) * (r - j); have hsq := (altIsqrt15_sound rad).2
    have hmaxR : ((altIsqrt15 rad).2 : ℝ) ≤ (altMaxBHiFrom mEff r 0 d : ℝ) := by
      have : 4 * (0 + j + 1) * (mEff - (0 + j)) * (r - (0 + j)) = rad := by simp [rad]
      rw [this] at hmax_j; exact_mod_cast hmax_j
    calc dAltCoupling mEff r j
        ≤ ((altIsqrt15 rad).2 : ℝ) / wdScaleR := hsq
      _ ≤ (altMaxBHiFrom mEff r 0 d : ℝ) / wdScaleR := div_le_div_of_nonneg_right hmaxR hB_pos.le
      _ = (1 / 2) * B_cap := by dsimp only [B_cap]; rw [hbCapHi_def]; push_cast; ring
  have hG_cap_op (u : Fin (d + 1) → ℝ) : vecNorm (G *ᵥ u) ≤ B_cap * vecNorm u := by
    simpa [G, dAltGenMat, ← mul_assoc] using
      vecNorm_tridiagSkewMat_mulVec_le (mul_nonneg (by norm_num) hBc_nn) hcoupl_cap u
  have hbCapCeil_ge : B_cap ≤ (bCapCeil : ℝ) := by
    have hnat : bCapHi15 ≤ bCapCeil * wdScale := by
      rw [hbCapCeil_def]
      have h := rkmb_ceil_div_mul_ge bCapHi15 wdScale (by unfold wdScale; positivity)
      have hsub : wdScale - 1 = 999999999999999 := by unfold wdScale; rfl
      rw [hsub] at h; exact h
    exact (div_le_iff₀ hB_pos).mpr (by unfold wdScaleR; exact_mod_cast hnat)
  set h_real : ℝ := (q : ℝ) * η
  have hsub_bds := rkmb_substep_bounds hn htau_hi (by omega) hnsub_hi
  have hh_nn : 0 ≤ h_real := mul_nonneg (Nat.cast_nonneg _) hη_nn
  have hh_hi : h_real ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR := by
    rw [hhPt_def]; dsimp only [h_real, η, q]; simpa [div_eq_mul_inv] using hsub_bds.2.1
  have hh_diff : |h_real - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
    rw [hhPt_def]; dsimp only [h_real, η, q]; simpa [div_eq_mul_inv] using hsub_bds.2.2
  have hhBc_mul_ge : (((2 + hPt : ℕ) : ℝ) / wdScaleR) * B_cap ≤ (hgHi15 : ℝ) / wdScaleR := by
    rw [hhg_def]; exact rkmb_mulCeil15_ge (2 + hPt) bCapHi15
  have hhBc_le_hg : h_real * B_cap ≤ (hgHi15 : ℝ) / wdScaleR :=
    (mul_le_mul_of_nonneg_right hh_hi hBc_nn).trans hhBc_mul_ge
  have hhg_32 : (hgHi15 : ℝ) / wdScaleR ≤ 3 / 2 := by
    rw [hB_eq, div_le_div_iff₀ (by norm_num) (by norm_num)]
    have hc : (hgHi15 : ℝ) ≤ 1500000000000000 := by exact_mod_cast hhg_le'
    linarith
  have hhBc_32 : h_real * B_cap ≤ 3 / 2 := hhBc_le_hg.trans hhg_32
  have hhPt_le4 : (hPt : ℝ) / wdScaleR ≤ 4 := by
    have hnat : hPt ≤ 4000000000 * 1000000 := by
      rw [hhPt_def]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _ htau_hi)
    rw [hB_eq, div_le_iff₀ (by norm_num)]
    have hR : (hPt : ℝ) ≤ 4000000000000000 := by exact_mod_cast hnat
    linarith
  have htrunc_ge : (nSub : ℝ) * ((h_real * B_cap) ^ 17 / 300000000000000) ≤
      (truncPad15 : ℝ) / wdScaleR := by
    have hpow17 : (h_real * B_cap) ^ 17 ≤ (altPow17Ceil15 hgHi15 : ℝ) / wdScaleR :=
      (pow_le_pow_left₀ (mul_nonneg hh_nn hBc_nn) hhBc_le_hg 17).trans (rkmb_pow17Ceil15_ge hgHi15)
    have hnat : nSub * altPow17Ceil15 hgHi15 ≤ truncPad15 * 300000000000000 := by
      rw [htrunc_def]; exact rkmb_ceil_div_mul_ge _ 300000000000000 (by norm_num)
    have hR : (nSub : ℝ) * (altPow17Ceil15 hgHi15 : ℝ) ≤ (truncPad15 : ℝ) * 300000000000000 := by
      exact_mod_cast hnat
    have hdiv17 : (h_real * B_cap) ^ 17 / 300000000000000 ≤
        (altPow17Ceil15 hgHi15 : ℝ) / (300000000000000 * wdScaleR) := by
      have h1 := div_le_div_of_nonneg_right hpow17 (by norm_num : (0 : ℝ) ≤ 300000000000000)
      rwa [div_div, mul_comm wdScaleR 300000000000000] at h1
    calc (nSub : ℝ) * ((h_real * B_cap) ^ 17 / 300000000000000)
        ≤ (nSub : ℝ) * ((altPow17Ceil15 hgHi15 : ℝ) / (300000000000000 * wdScaleR)) :=
          mul_le_mul_of_nonneg_left hdiv17 (Nat.cast_nonneg nSub)
      _ ≤ (truncPad15 : ℝ) / wdScaleR := by
          rw [show (nSub : ℝ) * ((altPow17Ceil15 hgHi15 : ℝ) / (300000000000000 * wdScaleR)) =
              ((nSub : ℝ) * (altPow17Ceil15 hgHi15 : ℝ)) / (300000000000000 * wdScaleR) by ring,
            div_le_div_iff₀ (mul_pos (by norm_num) hB_pos) hB_pos,
            show (truncPad15 : ℝ) * (300000000000000 * wdScaleR) =
              ((truncPad15 : ℝ) * 300000000000000) * wdScaleR by ring]
          exact mul_le_mul_of_nonneg_right hR hB_pos.le
  have hhb_len : hbPt.length = d := by rw [hhbPt_def]; exact rkmb_buildHbFrom_length mEff r hPt d 0
  have hGpt_op (u : Fin (d + 1) → ℝ) : vecNorm (rkmPtGenMat d hbPt *ᵥ u) ≤ (3 / 2) * vecNorm u := by
    have hb_le (j : ℕ) (hj : j < d) : |(hbPt.getD j 0 : ℝ) / wdScaleR| ≤ 3 / 4 := by
      have hget' := rkmb_buildHbFrom_getD mEff r hPt d 0 j hj; rw [← hhbPt_def] at hget'
      set rad := 4 * (j + 1) * (mEff - j) * (r - j); set sq := (altIsqrt15 rad).1
      have hget_sq : hbPt.getD j 0 = (((hPt * sq) / wdScale : ℕ) : ℤ) := by
        simpa [rad, sq] using hget'
      have hsq_le_c : (sq : ℝ) / wdScaleR ≤ dAltCoupling mEff r j := (altIsqrt15_sound rad).1
      set qProd := (hPt * sq) / wdScale
      have hR : (qProd : ℝ) * wdScaleR ≤ (hPt : ℝ) * (sq : ℝ) := by
        unfold wdScaleR; exact_mod_cast Nat.div_mul_le_self (hPt * sq) wdScale
      rw [hget_sq, Int.cast_natCast, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hB_pos.le)]
      have h1 : (qProd : ℝ) / wdScaleR ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) := by
        rw [div_mul_div_comm, div_le_div_iff₀ hB_pos (mul_pos hB_pos hB_pos),
          show (qProd : ℝ) * (wdScaleR * wdScaleR) = ((qProd : ℝ) * wdScaleR) * wdScaleR by ring]
        exact mul_le_mul_of_nonneg_right hR hB_pos.le
      have hc_le : dAltCoupling mEff r j ≤ (1 / 2) * B_cap :=
        (le_abs_self _).trans (hcoupl_cap j hj)
      have hhPt_le : (hPt : ℝ) / wdScaleR ≤ ((2 + hPt : ℕ) : ℝ) / wdScaleR :=
        div_le_div_of_nonneg_right (by exact_mod_cast (by omega : hPt ≤ 2 + hPt)) hB_pos.le
      calc (qProd : ℝ) / wdScaleR
          ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) := h1
        _ ≤ (((2 + hPt : ℕ) : ℝ) / wdScaleR) * ((1 / 2) * B_cap) :=
            mul_le_mul hhPt_le (hsq_le_c.trans hc_le)
              (div_nonneg (Nat.cast_nonneg _) hB_pos.le) (div_nonneg (Nat.cast_nonneg _) hB_pos.le)
        _ = (1 / 2) * ((((2 + hPt : ℕ) : ℝ) / wdScaleR) * B_cap) := by ring
        _ ≤ (1 / 2) * ((hgHi15 : ℝ) / wdScaleR) :=
            mul_le_mul_of_nonneg_left hhBc_mul_ge (by norm_num)
        _ ≤ (1 / 2) * (3 / 2) := mul_le_mul_of_nonneg_left hhg_32 (by norm_num)
        _ = 3 / 4 := by norm_num
    have h : vecNorm (rkmPtGenMat d hbPt *ᵥ u) ≤ (2 * (3 / 4)) * vecNorm u :=
      vecNorm_tridiagSkewMat_mulVec_le (by norm_num : (0 : ℝ) ≤ 3 / 4) hb_le u
    exact h.trans (le_of_eq (by ring))
  have hG_diff_op (u : Fin (d + 1) → ℝ) : vecNorm ((h_real • G - rkmPtGenMat d hbPt) *ᵥ u) ≤
        (((bCapCeil : ℝ) + 10) / wdScaleR) * vecNorm u := by
    have hsub_mat : h_real • G - rkmPtGenMat d hbPt = tridiagSkewMat d
          (fun j ↦ h_real * dAltCoupling mEff r j - (hbPt.getD j 0 : ℝ) / wdScaleR) :=
      tridiagSkewMat_smul_sub d h_real (dAltCoupling mEff r)
        (fun w ↦ (hbPt.getD w 0 : ℝ) / wdScaleR)
    rw [hsub_mat]
    have hcoupl_diff (j : ℕ) (hj : j < d) :
        |h_real * dAltCoupling mEff r j - (hbPt.getD j 0 : ℝ) / wdScaleR| ≤
          ((1 / 2 : ℝ) * (bCapCeil : ℝ) + 5) / wdScaleR := by
      have hget' := rkmb_buildHbFrom_getD mEff r hPt d 0 j hj; rw [← hhbPt_def] at hget'
      set rad := 4 * (j + 1) * (mEff - j) * (r - j); set sq := (altIsqrt15 rad).1
      have hget_sq : hbPt.getD j 0 = (((hPt * sq) / wdScale : ℕ) : ℤ) := by
        simpa [rad, sq] using hget'
      have hc_nn : 0 ≤ dAltCoupling mEff r j := by unfold dAltCoupling; positivity
      have hc_le : dAltCoupling mEff r j ≤ (1 / 2) * (bCapCeil : ℝ) :=
        ((le_abs_self _).trans (hcoupl_cap j hj)).trans
          (mul_le_mul_of_nonneg_left hbCapCeil_ge (by norm_num))
      have htight_j : (altIsqrt15 rad).2 ≤ sq + 1 := by
        simpa [rad, sq] using rkmb_checkHbTight_sound mEff r d 0 htight j hj
      have hsq_s := altIsqrt15_sound rad; set qProd := (hPt * sq) / wdScale
      have hloR : (qProd : ℝ) * wdScaleR ≤ (hPt : ℝ) * (sq : ℝ) := by
        unfold wdScaleR; exact_mod_cast Nat.div_mul_le_self (hPt * sq) wdScale
      have hhiR : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd + 1 : ℕ) : ℝ) * wdScaleR := by
        have hnat := (Nat.lt_mul_div_succ (hPt * sq)
          (by unfold wdScale; positivity : 0 < wdScale)).trans_eq (Nat.mul_comm _ _)
        unfold wdScaleR; exact_mod_cast hnat.le
      rw [hget_sq, Int.cast_natCast]
      have hsq_diff : |dAltCoupling mEff r j - (sq : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
        have hlo : (sq : ℝ) / wdScaleR ≤ dAltCoupling mEff r j := hsq_s.1
        have hhi : dAltCoupling mEff r j ≤ ((sq + 1 : ℕ) : ℝ) / wdScaleR :=
          hsq_s.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast htight_j) hB_pos.le)
        rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
        have h1 : ((sq + 1 : ℕ) : ℝ) / wdScaleR - (sq : ℝ) / wdScaleR = 1 / wdScaleR := by
          push_cast; ring
        linarith
      have hdiv_err : |((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) -
          (qProd : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
        have hdiff_nn : 0 ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) -
            (qProd : ℝ) / wdScaleR := by
          rw [div_mul_div_comm, sub_nonneg, div_le_div_iff₀ hB_pos (mul_pos hB_pos hB_pos),
            show (qProd : ℝ) * (wdScaleR * wdScaleR) = ((qProd : ℝ) * wdScaleR) * wdScaleR by ring]
          exact mul_le_mul_of_nonneg_right hloR hB_pos.le
        rw [abs_of_nonneg hdiff_nn]
        have h1 : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd : ℝ) + 1) * wdScaleR := by
          simpa only [Nat.cast_add, Nat.cast_one] using hhiR
        calc ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR
            = ((hPt : ℝ) * (sq : ℝ)) / (wdScaleR * wdScaleR) - (qProd : ℝ) / wdScaleR :=
                by rw [div_mul_div_comm]
          _ ≤ (((qProd : ℝ) + 1) * wdScaleR) / (wdScaleR * wdScaleR) - (qProd : ℝ) / wdScaleR :=
                sub_le_sub_right (div_le_div_of_nonneg_right h1 (mul_nonneg hB_pos.le hB_pos.le)) _
          _ = 1 / wdScaleR := by field_simp [hB_pos.ne']; ring
      set e1 : ℝ := (h_real - (hPt : ℝ) / wdScaleR) * dAltCoupling mEff r j
      set e2 : ℝ := ((hPt : ℝ) / wdScaleR) * (dAltCoupling mEff r j - (sq : ℝ) / wdScaleR)
      set e3 : ℝ := ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR
      have hsp3 : h_real * dAltCoupling mEff r j - (qProd : ℝ) / wdScaleR = e1 + e2 + e3 := by
        dsimp [e1, e2, e3]; ring
      rw [hsp3]
      have ht1 : |e1| ≤ (1 / wdScaleR) * ((1 / 2) * (bCapCeil : ℝ)) := by
        dsimp [e1]; rw [abs_mul, abs_of_nonneg hc_nn]
        exact mul_le_mul hh_diff hc_le hc_nn (div_nonneg (by norm_num) hB_pos.le)
      have ht2 : |e2| ≤ 4 * (1 / wdScaleR) := by
        dsimp [e2]; rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hB_pos.le)]
        exact mul_le_mul hhPt_le4 hsq_diff (abs_nonneg _) (by norm_num)
      have habs12 := abs_add_le e1 e2; have habs123 := abs_add_le (e1 + e2) e3
      have hgoal : (1 / wdScaleR) * ((1 / 2) * (bCapCeil : ℝ)) + 4 * (1 / wdScaleR) +
          1 / wdScaleR = ((1 / 2 : ℝ) * (bCapCeil : ℝ) + 5) / wdScaleR := by ring
      linarith [habs12, habs123, ht1, ht2, hdiv_err, hgoal]
    refine (vecNorm_tridiagSkewMat_mulVec_le (div_nonneg (by positivity) hB_pos.le)
      hcoupl_diff u).trans (le_of_eq (by ring))
  have hhG_32 (u : Fin (d + 1) → ℝ) : vecNorm ((h_real • G) *ᵥ u) ≤ (3 / 2) * vecNorm u := by
    rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg hh_nn]
    exact ((mul_le_mul_of_nonneg_left (hG_cap_op u) hh_nn).trans_eq (by ring)).trans
      (mul_le_mul_of_nonneg_right hhBc_32 (vecNorm_nonneg u))
  set B_mac := taylor16Mat h_real G; set B_pt := taylor16OfMat (rkmPtGenMat d hbPt)
  have hquant_mac (u : Fin (d + 1) → ℝ) :
      vecNorm ((B_mac - B_pt) *ᵥ u) ≤ ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) * vecNorm u :=
    (vecNorm_taylor16OfMat_sub_mulVec_le hhG_32 hGpt_op
      (div_nonneg (by positivity) hB_pos.le) hG_diff_op u).trans (le_of_eq (by ring))
  set A_sub := (taylor16Mat η G) ^ q
  have hBf_nn : 0 ≤ dAltGenNormBound mEff r := by unfold dAltGenNormBound; positivity
  have hBf_hi : dAltGenNormBound mEff r ≤ 200000 := by
    unfold dAltGenNormBound; rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩
    have hnat : 4 * (min mEff r + 1) ^ 2 * max mEff r ≤ 4 * 1025 ^ 2 * 8192 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left (by have := Nat.min_le_right mEff r; omega) 2))
        (Nat.max_le.mpr ⟨hm_hi, by omega⟩)
    exact (by exact_mod_cast hnat : _ ≤ ((4 * 1025 ^ 2 * 8192 : ℕ) : ℝ)).trans (by norm_num)
  have hηBf1 : η * dAltGenNormBound mEff r ≤ 1 := by
    dsimp [η]; rw [one_div_mul_eq_div, div_le_one hsN_pos]
    exact hBf_hi.trans ((by norm_num : (200000 : ℝ) ≤ (2 : ℝ) ^ 100).trans hsN_ge100)
  have hA_sub_contr (u : Fin (d + 1) → ℝ) : vecNorm (A_sub *ᵥ u) ≤ vecNorm u := by
    have h1 (x : Fin (d + 1) → ℝ) : vecNorm (taylor16Mat η G *ᵥ x) ≤ 1 * vecNorm x := by
      rw [one_mul]
      exact vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose mEff r) hη_nn hBf_nn
        (vecNorm_dAltGenMat_mulVec_le mEff r) (hηBf1.trans (by norm_num)) x
    have hp := vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) h1 q u
    rw [one_pow, one_mul] at hp; exact hp
  have hB_mac_contr (u : Fin (d + 1) → ℝ) : vecNorm (B_mac *ᵥ u) ≤ vecNorm u :=
    vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose mEff r) hh_nn hBc_nn hG_cap_op hhBc_32 u
  have hB_pt_contr (u : Fin (d + 1) → ℝ) : vecNorm (B_pt *ᵥ u) ≤ vecNorm u :=
    vecNorm_taylor16OfMat_mulVec_le (tridiagSkewMat_transpose d _) hGpt_op u
  have hmac_diff (u : Fin (d + 1) → ℝ) : vecNorm ((A_sub - B_mac) *ᵥ u) ≤
        ((h_real * B_cap) ^ 17 / 300000000000000) * vecNorm u :=
    vecNorm_taylor16Mat_substep_le (dAltGenMat_transpose mEff r) hη_nn hBc_nn
      hG_cap_op q hhBc_32 u
  have hB_pt_def : B_pt = taylor16OfMat (rkmPtGenMat d hbPt) := rfl
  have hA_sub_def : A_sub = (taylor16Mat η G) ^ q := rfl
  clear_value B_mac B_pt A_sub
  have hterm_mac : vecNorm (((taylor16Mat η G) ^ K) *ᵥ uIn - (B_mac ^ nSub) *ᵥ uIn) ≤
      (truncPad15 : ℝ) / wdScaleR := by
    have hA_pow : A_sub ^ nSub = (taylor16Mat η G) ^ K := by
      rw [hA_sub_def, hK_eq, mul_comm nSub q, pow_mul]
    rw [← hA_pow]
    have htel := vecNorm_pow_mulVec_sub_le hA_sub_contr hB_mac_contr
      (div_nonneg (pow_nonneg (mul_nonneg hh_nn hBc_nn) 17) (by norm_num))
      hmac_diff nSub uIn uIn
    rw [sub_self, vecNorm_zero, zero_add] at htel
    have hmul_u : (nSub : ℝ) * ((h_real * B_cap) ^ 17 / 300000000000000) * vecNorm uIn ≤
        (nSub : ℝ) * ((h_real * B_cap) ^ 17 / 300000000000000) :=
      mul_le_of_le_one_right (by positivity) huIn
    exact (htel.trans hmul_u).trans htrunc_ge
  have hterm_quant : vecNorm ((B_mac ^ nSub) *ᵥ uIn - (B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec) ≤
      vecNorm (uIn - rkmListToOrbVec d vec) +
        ((nSub : ℝ) * (5 * (bCapCeil : ℝ) + 50)) / wdScaleR := by
    have hq_rev (u : Fin (d + 1) → ℝ) :
        vecNorm ((B_pt - B_mac) *ᵥ u) ≤ ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) * vecNorm u := by
      have hneg : (B_pt - B_mac) *ᵥ u = -((B_mac - B_pt) *ᵥ u) := by
        ext idx; simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.neg_apply]; ring
      rw [hneg, vecNorm_neg]; exact hquant_mac u
    have htel := vecNorm_pow_mulVec_sub_le hB_pt_contr hB_mac_contr
      (div_nonneg (by positivity) hB_pos.le) hq_rev nSub (rkmListToOrbVec d vec) uIn
    have hrev1 : vecNorm ((B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec - (B_mac ^ nSub) *ᵥ uIn) =
        vecNorm ((B_mac ^ nSub) *ᵥ uIn - (B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec) := by
      rw [← neg_sub ((B_mac ^ nSub) *ᵥ uIn), vecNorm_neg]
    have hrev2 : vecNorm (rkmListToOrbVec d vec - uIn) =
        vecNorm (uIn - rkmListToOrbVec d vec) := by
      rw [← neg_sub uIn, vecNorm_neg]
    rw [hrev1, hrev2] at htel
    have hmul_u : (nSub : ℝ) * ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) * vecNorm uIn ≤
        ((nSub : ℝ) * (5 * (bCapCeil : ℝ) + 50)) / wdScaleR := by
      have hc0 : 0 ≤ (nSub : ℝ) * ((5 * (bCapCeil : ℝ) + 50) / wdScaleR) :=
        mul_nonneg (Nat.cast_nonneg nSub) (div_nonneg (by positivity) hB_pos.le)
      exact (mul_le_of_le_one_right hc0 huIn).trans_eq (by ring)
    linarith [htel, hmul_u]
  obtain ⟨hvw_len, hterm_iter⟩ :=
    rkmIterFullT16_approx ((Nat.min_le_right mEff r).trans hr_hi) hhb_len.le hGpt_op
      nSub vec hvec_len
  rw [← hB_pt_def] at hterm_iter; set uMac := (B_mac ^ nSub) *ᵥ uIn
  set uOut := rkmMaskSignVec d mask uMac
  refine ⟨uOut, ?_, ?_, ?_⟩
  · rw [vecNorm_rkmMaskSignVec]
    have hpow := vecNorm_pow_mulVec_le (by norm_num : (0 : ℝ) ≤ 1)
      (fun x ↦ by rw [one_mul]; exact hB_mac_contr x) nSub uIn
    rw [one_pow, one_mul] at hpow; exact hpow.trans huIn
  · rw [hvNext_def, rkmApplyMaskBits_length]; exact hvw_len
  · have h1 : vecNorm (rkmMaskSignVec d mask (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn) -
        uOut) ≤ (3 / 2) / wdScaleR + (truncPad15 : ℝ) / wdScaleR := by
      dsimp only [uOut]; rw [rkmMaskSignVec_sub, vecNorm_rkmMaskSignVec]
      have hsp : ((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn - uMac =
          (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn - ((taylor16Mat η G) ^ K) *ᵥ uIn) +
          (((taylor16Mat η G) ^ K) *ᵥ uIn - uMac) :=
        (sub_add_sub_cancel _ _ _).symm
      rw [hsp]; exact (vecNorm_add_le _ _).trans (add_le_add hcont hterm_mac)
    have h2 : vecNorm (uOut - rkmListToOrbVec d vNext) ≤ vecNorm (uIn - rkmListToOrbVec d vec) +
          ((nSub : ℝ) * (5 * (bCapCeil : ℝ) + 50)) / wdScaleR +
          ((297 / 2) * (nSub : ℝ)) / wdScaleR := by
      dsimp only [uOut]
      rw [hvNext_def, rkmApplyMaskBits_orbVec, rkmMaskSignVec_sub, vecNorm_rkmMaskSignVec]
      set vWalk := muxFastIterFullT16 nSub (d + 1) hbPt vec
      have hsp : uMac - rkmListToOrbVec d vWalk = (uMac - (B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec) +
          ((B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec - rkmListToOrbVec d vWalk) :=
        (sub_add_sub_cancel _ _ _).symm
      rw [hsp]
      have hneg : vecNorm ((B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec - rkmListToOrbVec d vWalk) ≤
          ((297 / 2) * (nSub : ℝ)) / wdScaleR := by
        rw [← vecNorm_neg, neg_sub]; exact hterm_iter
      linarith [vecNorm_add_le (uMac - (B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec)
        ((B_pt ^ nSub) *ᵥ rkmListToOrbVec d vec - rkmListToOrbVec d vWalk), hterm_quant, hneg]
    have hsegR : (segPad : ℝ) = ((truncPad15 : ℝ) + 256) +
        (nSub : ℝ) * (256 + 10 * (bCapCeil : ℝ)) := by
      rw [hseg_def]; push_cast; ring
    have hbudget : (3 / 2) / wdScaleR + (truncPad15 : ℝ) / wdScaleR +
        ((nSub : ℝ) * (5 * (bCapCeil : ℝ) + 50)) / wdScaleR +
        ((297 / 2) * (nSub : ℝ)) / wdScaleR ≤ ((segPad : ℝ) - 253) / wdScaleR := by
      rw [← add_div, ← add_div, ← add_div]
      refine div_le_div_of_nonneg_right ?_ hB_pos.le
      rw [hsegR]; have hnSub0 : (0 : ℝ) ≤ (nSub : ℝ) := Nat.cast_nonneg nSub
      have hnb0 : (0 : ℝ) ≤ (nSub : ℝ) * (bCapCeil : ℝ) :=
        mul_nonneg hnSub0 (Nat.cast_nonneg bCapCeil)
      linarith [hnSub0, hnb0]
    linarith [h1, h2, hbudget]
private theorem rkmb_altPadRightInts_length :
    ∀ (targetLen : ℕ) (xs : List ℤ), (altPadRightInts targetLen xs).length = targetLen
  | 0, _ => rfl
  | rem + 1, [] => by
    dsimp only [altPadRightInts]; rw [rkmb_strictConsInt_eq]
    exact congrArg Nat.succ (rkmb_altPadRightInts_length rem [])
  | rem + 1, _ :: xs => by
    dsimp only [altPadRightInts]; rw [rkmb_strictConsInt_eq]
    exact congrArg Nat.succ (rkmb_altPadRightInts_length rem xs)
private theorem rkmb_altPadRightInts_getD :
    ∀ (targetLen : ℕ) (xs : List ℤ), xs.length ≤ targetLen →
      ∀ j : ℕ, (altPadRightInts targetLen xs).getD j 0 = xs.getD j 0
  | 0, [], _, _ => rfl
  | 0, _ :: _, hlen, _ => absurd hlen (Nat.not_le_of_gt (Nat.succ_pos _))
  | rem + 1, [], _, j => by
    dsimp only [altPadRightInts]; rw [rkmb_strictConsInt_eq]
    rcases j with _ | j'
    · rfl
    · exact rkmb_altPadRightInts_getD rem [] (Nat.zero_le _) j'
  | rem + 1, _ :: xs, hlen, j => by
    dsimp only [altPadRightInts]; rw [rkmb_strictConsInt_eq]
    rcases j with _ | j'
    · rfl
    · exact rkmb_altPadRightInts_getD rem xs (by simpa using hlen) j'
private theorem rkmb_vecTailToLo12_length (pad : ℕ) :
    ∀ zs : List ℤ, (altVecTailToLo12 pad zs).length = zs.length
  | [] => rfl
  | _ :: zs => by
    unfold altVecTailToLo12; rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact congrArg Nat.succ (rkmb_vecTailToLo12_length pad zs)
private theorem rkmb_vecTailToLo12_getD (pad : ℕ) : ∀ (zs : List ℤ) (j : ℕ), j < zs.length →
      (altVecTailToLo12 pad zs).getD j 0 =
        ((((Int.natAbs (zs.getD j 0) - pad) * (Int.natAbs (zs.getD j 0) - pad)) /
          wdScale) / 1000) - 1
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, _ => by
    unfold altVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq, primIntNatAbs_eq]; rfl
  | _ :: zs, j + 1, hj => by
    unfold altVecTailToLo12; rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact rkmb_vecTailToLo12_getD pad zs j (by simp at hj; omega)
private theorem rkmb_cast_natAbs_eq_abs (z : ℤ) : ((Int.natAbs z : ℕ) : ℝ) = |(z : ℝ)| := by
  cases z with
  | ofNat n =>
    change ((n : ℕ) : ℝ) = |((n : ℕ) : ℝ)|; exact (abs_of_nonneg (Nat.cast_nonneg n)).symm
  | negSucc n =>
    have hneg : (Int.negSucc n : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hneg, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; rfl
/-- Converts a bounded quantum + integer orbital discrepancy at `w` into the `10 ^
  12`-scaled
  probability bound from `altVecTailToLo12`. -/
theorem rkmPadTailToLo12_sound {dEnd accPad w : ℕ} {vecFinal : List ℤ}
    {uFinal : Fin (dEnd + 1) → ℝ} {errQ sProb : ℝ}
    (hw1 : 1 ≤ w) (hvec_len : vecFinal.length ≤ dEnd + 1)
    (hs_nn : 0 ≤ sProb)
    (htot : errQ + vecNorm (uFinal - rkmListToOrbVec dEnd vecFinal) ≤ (accPad : ℝ) / wdScaleR) :
    let rowOut := match altPadRightInts (dEnd + 1) vecFinal with
      | [] => []
      | _ :: tail => altVecTailToLo12 accPad tail
    rowOut.length = dEnd ∧ (∀ (wFin : Fin (dEnd + 1)), wFin.1 = w → |uFinal wFin| - errQ ≤ sProb →
        w - 1 < rowOut.length → ((rowOut.getD (w - 1) 0 : ℝ) / 1000000000000) ≤ sProb ^ 2) := by
  intro rowOut
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  set padded := altPadRightInts (dEnd + 1) vecFinal
  have hpad_len : padded.length = dEnd + 1 := rkmb_altPadRightInts_length (dEnd + 1) vecFinal
  rcases hp : padded with _ | ⟨_, tail⟩
  · rw [hp] at hpad_len; simp at hpad_len
  · have htail_len : tail.length = dEnd := by rw [hp] at hpad_len; simpa using hpad_len
    have hrow_eq : rowOut = altVecTailToLo12 accPad tail := by
      change (match padded with | [] => [] | _ :: t => altVecTailToLo12 accPad t) = _
      rw [hp]
    have hrow_len : rowOut.length = dEnd := by
      rw [hrow_eq]; exact (rkmb_vecTailToLo12_length accPad tail).trans htail_len
    refine ⟨hrow_len, ?_⟩
    intro wFin hwFin hq_le hw_lt; set z : ℤ := tail.getD (w - 1) 0
    have hz_orb : rkmListToOrbVec dEnd vecFinal wFin = (z : ℝ) / wdScaleR := by
      unfold rkmListToOrbVec; rw [← rkmb_altPadRightInts_getD (dEnd + 1) vecFinal hvec_len wFin.1]
      change (padded.getD wFin.1 0 : ℝ) / wdScaleR = _; rw [hp, hwFin]
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩; simp [z]
    have hcoord : |uFinal wFin - (z : ℝ) / wdScaleR| ≤
        vecNorm (uFinal - rkmListToOrbVec dEnd vecFinal) := by
      rw [← hz_orb]; exact abs_apply_le_vecNorm (uFinal - rkmListToOrbVec dEnd vecFinal) wFin
    set aLo : ℕ := Int.natAbs z - accPad; set pLo15 : ℕ := (aLo * aLo) / wdScale
    set pLo12 : ℕ := pLo15 / 1000; set out : ℕ := pLo12 - 1
    have haLo_le : (aLo : ℝ) / wdScaleR ≤ sProb := by
      by_cases hle : Int.natAbs z ≤ accPad
      · dsimp only [aLo]; rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero, zero_div]; exact hs_nn
      · have hgt : accPad < Int.natAbs z := by omega
        have haR : (aLo : ℝ) = |(z : ℝ)| - (accPad : ℝ) := by
          dsimp [aLo]; rw [Nat.cast_sub hgt.le, rkmb_cast_natAbs_eq_abs]
        have habs_diff : |(z : ℝ) / wdScaleR| - |uFinal wFin| ≤
            |uFinal wFin - (z : ℝ) / wdScaleR| := by
          have h := abs_sub_abs_le_abs_sub ((z : ℝ) / wdScaleR) (uFinal wFin)
          rwa [abs_sub_comm] at h
        have habs_div : |(z : ℝ) / wdScaleR| = |(z : ℝ)| / wdScaleR := by
          rw [abs_div, abs_of_pos hB]
        rw [haR, sub_div, ← habs_div]; linarith [habs_diff, hcoord, htot, hq_le]
    have hsq_le : ((aLo : ℝ) / wdScaleR) ^ 2 ≤ sProb ^ 2 :=
      pow_le_pow_left₀ (by positivity) haLo_le 2
    have hchain_nat : (out * 1000) * wdScale ≤ aLo * aLo :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le pLo12 1))).trans
        ((Nat.mul_le_mul_right _ (Nat.div_mul_le_self pLo15 1000)).trans
          (Nat.div_mul_le_self (aLo * aLo) wdScale))
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
    have hget_row : rowOut.getD (w - 1) 0 = out := by
      rw [hrow_eq]; exact rkmb_vecTailToLo12_getD accPad tail (w - 1) (by omega)
    rw [hget_row]; exact hdiv_le.trans hsq_le
end
end QuantumComputation.Specs.DickeSol
end Sec_FindAllJohnsonRampKickMuxKernelB
