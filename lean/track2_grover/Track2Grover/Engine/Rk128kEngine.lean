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

public import Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

/-
# 128-Segment Variable-Degree Ramp-Kick Orbital Engine (`Rk128kEngine`)

Shared QHL-verified `<= 128`-segment (`C_step = 2149580800`), variable-degree (`1 <= degP <= 64`)
a-posteriori `L1`-norm orbital evaluator and Bellman table bridge at `wdScale = 10 ^ 15` (`0`
kernel reflection, `0` per-substep `Nat.sqrt`, `< 2 ^ 55` intermediates) for `33 <= L <= 64`
and `L <= 128` multi-segment `RampKick128k` cell certificates.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation


















/-- Extracts `lS` list from `segs`. -/
def rkm128kSegLs (segs : List Rkm128kSeg) : List ℕ :=
  match segs with
  | [] => []
  | s :: rest => s.lS :: rkm128kSegLs rest

/-- Extracts `tau9` list from `segs`. -/
def rkm128kSegTaus (segs : List Rkm128kSeg) : List ℕ :=
  match segs with
  | [] => []
  | s :: rest => s.tau9 :: rkm128kSegTaus rest

/-- Extracts `nSub` list from `segs`. -/
def rkm128kSegNsubs (segs : List Rkm128kSeg) : List ℕ :=
  match segs with
  | [] => []
  | s :: rest => s.nSub :: rkm128kSegNsubs rest

/-- Extracts `mask` list from `segs`. -/
def rkm128kSegMasks (segs : List Rkm128kSeg) : List (List Bool) :=
  match segs with
  | [] => []
  | s :: rest => s.mask :: rkm128kSegMasks rest





/-- Looks up the first anchor matching `r` in `anchors`. -/
def rkm128kFindAnchor (r : ℕ) (anchors : List RampKick128kAnchor) : Option RampKick128kAnchor :=
  match anchors with
  | [] => none
  | a :: rest => if a.rAct = r then some a else rkm128kFindAnchor r rest






/-- Unpacked semantic validity of one `<= 128`-segment active row at rung `s`. -/
def RampKick128kActiveValid (m lTableMax s : ℕ) (vPot : List ℕ)
    (segs : List Rkm128kSeg) (row : List ℕ) : Prop :=
  let lEnd := rkm128kLastL 0 segs
  let dEnd := min (lEnd * m) s
  1 ≤ segs.length ∧ segs.length ≤ 128 ∧
    rkm128kCheckSegBounds lTableMax segs 1 = true ∧
    row.length = dEnd ∧
    0 < altSumNat row ∧ altSumNat row ≤ 1000000000000 ∧
    rkm128kWeightedTau9 segs * (1000 * wdScale) +
        (∑ j ∈ Finset.range dEnd, row.getD j 0 * vPot.getD (s - 1 - j) 0) +
        (1000000000000 - altSumNat row) * muxRunningCap vPot s <
      1000000000000 * vPot.getD s 0

/-- Semantic validity bundle for a full `r = 0.. kMax` `<= 128`-segment `RampKick128k`
  table. -/
structure RampKick128kTableValid (m kMax lTableMax : ℕ) (useColdR2 : Bool)
    (vPot : List ℕ) (anchors : List RampKick128kAnchor) : Prop where
  hm1 : 1 ≤ m
  hlMax1 : 1 ≤ lTableMax
  hlMax_hi : lTableMax * m ≤ 8192
  hkMax_lo : 2 ≤ kMax
  hkMax_hi : kMax ≤ 1024
  hv_len : vPot.length = kMax + 1
  hv0 : vPot.getD 0 0 = 0
  heig1 : checkEigStep m 1 (vPot.getD 1 0) (vPot.getD 0 0) = true
  hrows : ∀ s : ℕ, 2 ≤ s → s ≤ kMax →
    match rkm128kFindAnchor s anchors with
    | none =>
      (s = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨
        checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
    | some a =>
      a.rAct = s ∧
      rkm128kEvalRowLo12 m lTableMax s a.segs = a.rowLo12 ∧
      RampKick128kActiveValid m lTableMax s vPot a.segs a.rowLo12

/-- Returns the matching `RampKick128kAnchor` at rung `r`, or a default dummy anchor. -/
def rkm128kAnchorAt (anchors : List RampKick128kAnchor) (r : ℕ) : RampKick128kAnchor :=
  match rkm128kFindAnchor r anchors with
  | some a => a
  | none => ⟨r, [], []⟩

end

public section

open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation

private theorem rkm128k_cond_true {α : Type*} (a b : α) : cond true a b = a := rfl
private theorem rkm128k_cond_false {α : Type*} (a b : α) : cond false a b = b := rfl

private theorem rkm128k_ble_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkm128k_ble_true]

private theorem rkm128k_ble_false {a b : ℕ} : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, rkm128k_ble_true]
  omega

private theorem rkm128k_blt_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  unfold primNatBlt
  rw [rkm128k_ble_true]
  change a + 1 ≤ b ↔ a < b
  omega

private theorem rkm128k_blt_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, rkm128k_blt_true]
  omega

private theorem rkm128k_beq_true : ∀ {a b : ℕ}, Nat.beq a b = true ↔ a = b
  | 0, 0 => by simp [Nat.beq]
  | 0, _ + 1 => by simp [Nat.beq]
  | _ + 1, 0 => by simp [Nat.beq]
  | a + 1, b + 1 => by simp [Nat.beq, rkm128k_beq_true]

private theorem rkm128k_beq_false {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, rkm128k_beq_true]

private theorem rkm128k_strictConsInt_eq (x : ℤ) (xs : List ℤ) :
    highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 => match xs with
        | [] => [Int.ofNat 0]
        | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 => match xs with
        | [] => [Int.ofNat v]
        | h :: t => Int.ofNat v :: h :: t) = Int.ofNat n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 => match xs with
        | [] => [Int.negSucc 0]
        | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 => match xs with
        | [] => [Int.negSucc v]
        | h :: t => Int.negSucc v :: h :: t) = Int.negSucc n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl

private theorem rkm128k_rawNegOfNat_eq (x : ℕ) : muxRawNegOfNat x = primNegOfNat x := by
  cases x with
  | zero => rfl
  | succ k => simp [muxRawNegOfNat, primNegOfNat, primNegSuccForced, Nat.one_add]

private theorem rkm128k_rawSubNatNat_eq (m n : ℕ) : muxRawSubNatNat m n = primSubNatNat m n := by
  unfold muxRawSubNatNat primSubNatNat
  cases Nat.sub n m <;> simp [primOfNatForced, primNegSuccForced, Nat.one_add]

private theorem rkm128k_rawAdd_eq (a b : ℤ) : muxRawIntAdd a b = a + b := by
  have h : muxRawIntAdd a b = primIntAdd a b := by
    cases a <;> cases b <;>
      simp [muxRawIntAdd, primIntAdd, primOfNatForced, primNegSuccForced,
        rkm128k_rawSubNatNat_eq, Nat.one_add]
  rw [h, primIntAdd_eq]

private theorem rkm128k_rawNeg_eq (a : ℤ) : muxRawIntNeg a = primIntNeg a := by
  cases a <;> simp [muxRawIntNeg, primIntNeg, primOfNatForced, rkm128k_rawNegOfNat_eq, Nat.one_add]

private theorem rkm128k_rawSub_eq (a b : ℤ) : muxRawIntSub a b = a - b := by
  have h : muxRawIntSub a b = primIntSub a b := by
    unfold muxRawIntSub primIntSub
    rw [rkm128k_rawNeg_eq, show muxRawIntAdd a (primIntNeg b) = primIntAdd a (primIntNeg b) by
      rw [rkm128k_rawAdd_eq, primIntAdd_eq]]
  rw [h, primIntSub_eq]

private theorem rkm128k_rawMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  have h : muxRawIntMul a b = primIntMul a b := by
    cases a <;> cases b <;>
      simp [muxRawIntMul, primIntMul, primOfNatForced, rkm128k_rawNegOfNat_eq, Nat.one_add]
  rw [h, primIntMul_eq]

private theorem rkm128k_cast_natAbs (z : ℤ) :
    ((primIntNatAbs z : ℕ) : ℝ) = |(z : ℝ)| := by
  rw [primIntNatAbs_eq]
  cases z with
  | ofNat n =>
    change ((n : ℕ) : ℝ) = |((n : ℕ) : ℝ)|
    exact (abs_of_nonneg (Nat.cast_nonneg n)).symm
  | negSucc n =>
    have hneg : (Int.negSucc n : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hneg, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    rfl

private theorem rkm128k_ceilDiv15_mul_ge (n : ℕ) : n ≤ rkm128kCeilDiv15 n * wdScale := by
  change n ≤ ((999999999999999 + n) / wdScale) * wdScale
  have hB : wdScale = 1000000000000000 := rfl
  rw [hB]
  set q := (999999999999999 + n) / 1000000000000000
  have h : 999999999999999 + n < 1000000000000000 * (q + 1) :=
    Nat.lt_mul_div_succ (999999999999999 + n) (by positivity : 0 < 1000000000000000)
  omega

private theorem rkm128k_ceilDiv15_ge (n : ℕ) : (n : ℝ) / wdScaleR ≤ (rkm128kCeilDiv15 n : ℝ) := by
  have hB : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  exact (div_le_iff₀ hB).mpr (by unfold wdScaleR; exact_mod_cast rkm128k_ceilDiv15_mul_ge n)

private theorem rkm128k_ceilDiv15_sq_ge (n : ℕ) :
    (n : ℝ) / wdScaleR ^ 2 ≤ (rkm128kCeilDiv15 n : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  rw [sq, ← div_div]
  exact div_le_div_of_nonneg_right (rkm128k_ceilDiv15_ge n) hB.le

private theorem rkm128k_segListLen_eq :
    ∀ segs : List Rkm128kSeg, rkm128kSegListLen segs = segs.length
  | [] => rfl
  | _ :: rest => by
    unfold rkm128kSegListLen
    rw [show Nat.add 1 (rkm128kSegListLen rest) = rkm128kSegListLen rest + 1 from Nat.one_add _,
      rkm128k_segListLen_eq rest]
    rfl

/-- Unconditional substep chunking law (`bSlide` within a single high-`nSub` segment). -/
theorem rkm128kSubstepLoop_add (k1 k2 d bCapCeil degP : ℕ)
    (hb vec : List ℤ) (accPad : ℕ) :
    rkm128kSubstepLoop (k1 + k2) d bCapCeil degP hb vec accPad =
      let st := rkm128kSubstepLoop k1 d bCapCeil degP hb vec accPad
      rkm128kSubstepLoop k2 d bCapCeil degP hb st.1 st.2 := by
  induction k1 generalizing vec accPad with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ s ih =>
    rw [Nat.succ_add]
    change (match rkm128kSubstep d bCapCeil degP hb vec accPad with
        | (v1, p1) =>
          HighDForce.withForcedList v1 fun vForced =>
            HighDForce.withForcedNat p1 fun pForced =>
              rkm128kSubstepLoop (s + k2) d bCapCeil degP hb vForced pForced) =
      let st := (match rkm128kSubstep d bCapCeil degP hb vec accPad with
        | (v1, p1) =>
          HighDForce.withForcedList v1 fun vForced =>
            HighDForce.withForcedNat p1 fun pForced =>
              rkm128kSubstepLoop s d bCapCeil degP hb vForced pForced)
      rkm128kSubstepLoop k2 d bCapCeil degP hb st.1 st.2
    rcases rkm128kSubstep d bCapCeil degP hb vec accPad with ⟨v1, p1⟩
    dsimp only
    simp only [rkmb_forceList_eq, rkmb_forceNat_eq]
    exact ih v1 p1

private theorem rkm128kRunSegs_true (m lTableMax r : ℕ) (segs : List Rkm128kSeg)
    (lPrev dCur accPad : ℕ) (vec : List ℤ)
    (hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) = true) :
    rkm128kRunSegs m lTableMax r segs lPrev dCur accPad vec = (0, 0, 0, []) := by
  rw [rkm128kRunSegs.eq_def, hg, rkm128k_cond_true]

private theorem rkm128kRunSegs_nil_false (m lTableMax r lPrev dCur accPad : ℕ) (vec : List ℤ)
    (hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) = false) :
    rkm128kRunSegs m lTableMax r [] lPrev dCur accPad vec = (lPrev, dCur, accPad, vec) := by
  rw [rkm128kRunSegs, hg, rkm128k_cond_false]

private theorem rkm128kRunSegs_cons_false (m lTableMax r : ℕ) (seg : Rkm128kSeg)
    (rest : List Rkm128kSeg) (lPrev dCur accPad : ℕ) (vec : List ℤ)
    (hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) = false) :
    rkm128kRunSegs m lTableMax r (seg :: rest) lPrev dCur accPad vec =
      let s1 := rkm128kRunOneSeg m lTableMax r seg lPrev dCur accPad vec
      rkm128kRunSegs m lTableMax r rest s1.1 s1.2.1 s1.2.2.1 s1.2.2.2 := by
  conv_lhs => rw [rkm128kRunSegs]
  rw [hg, rkm128k_cond_false]
  dsimp only
  rcases rkm128kRunOneSeg m lTableMax r seg lPrev dCur accPad vec with ⟨l1, d1, p1, v1⟩
  dsimp only
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq]

/-- Unconditional segment chunking law (`bSlide` across `<= 128` segments with `0` side
  goals). -/
theorem rkm128kRunSegs_append (m lTableMax r : ℕ) (segs1 segs2 : List Rkm128kSeg)
    (lPrev dCur accPad : ℕ) (vec : List ℤ) :
    rkm128kRunSegs m lTableMax r (segs1 ++ segs2) lPrev dCur accPad vec =
      let st := rkm128kRunSegs m lTableMax r segs1 lPrev dCur accPad vec
      rkm128kRunSegs m lTableMax r segs2 st.1 st.2.1 st.2.2.1 st.2.2.2 := by
  induction segs1 generalizing lPrev dCur accPad vec with
  | nil =>
    dsimp only
    rw [List.nil_append]
    cases hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0)
    · rw [rkm128kRunSegs_nil_false m lTableMax r lPrev dCur accPad vec hg]
    · rw [rkm128kRunSegs_true m lTableMax r segs2 lPrev dCur accPad vec hg,
        rkm128kRunSegs_true m lTableMax r [] lPrev dCur accPad vec hg]
      dsimp only
      exact (rkm128kRunSegs_true m lTableMax r segs2 0 0 0 [] rfl).symm
  | cons seg rest ih =>
    dsimp only
    rw [List.cons_append]
    cases hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0)
    · rw [rkm128kRunSegs_cons_false m lTableMax r seg (rest ++ segs2) lPrev dCur accPad vec hg,
        rkm128kRunSegs_cons_false m lTableMax r seg rest lPrev dCur accPad vec hg]
      dsimp only
      exact ih _ _ _ _
    · rw [rkm128kRunSegs_true m lTableMax r (seg :: (rest ++ segs2)) lPrev dCur accPad vec hg,
        rkm128kRunSegs_true m lTableMax r (seg :: rest) lPrev dCur accPad vec hg]
      dsimp only
      exact (rkm128kRunSegs_true m lTableMax r segs2 0 0 0 [] rfl).symm

/-- Certifies `rkm128kEvalRowLo12` from a `bSlide`-computed `rkm128kRunSegs` checkpoint
  state. -/
theorem rkm128kCertRow_of_runSegs {m lTableMax r : ℕ} {segs : List Rkm128kSeg}
    {st : ℕ × ℕ × ℕ × List ℤ} {rowOut : List ℕ}
    (hsegs : Bool.and (Nat.ble 1 (rkm128kSegListLen segs))
      (Bool.and (Nat.ble (rkm128kSegListLen segs) 128)
        (Bool.and (Nat.ble 2 r) (Nat.ble r 1024))) = true)
    (hrun : rkm128kRunSegs m lTableMax r segs 1 0 1 [Int.ofNat wdScale] = st)
    (hfin : rkm128kFinalizeState st = rowOut) :
    rkm128kEvalRowLo12 m lTableMax r segs = rowOut := by
  simp only [Bool.and_eq_true, rkm128k_ble_true] at hsegs
  obtain ⟨hs1, hs32, hr2, hr1024⟩ := hsegs
  unfold rkm128kEvalRowLo12
  dsimp only
  have hg : Bool.or (Nat.beq (rkm128kSegListLen segs) 0)
      (Bool.or (primNatBlt 128 (rkm128kSegListLen segs))
        (Bool.or (primNatBlt r 2) (primNatBlt 1024 r))) = false := by
    simp only [Bool.or_eq_false_iff, rkm128k_beq_false, rkm128k_blt_false]
    exact ⟨by omega, hs32, hr2, hr1024⟩
  rw [hg, rkm128k_cond_false, hrun, hfin]

private theorem rkm128k_sum_range_succ_shift {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    ∀ d : ℕ, (∑ j ∈ Finset.range (d + 1), f j) = f 0 + ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by rw [Nat.zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, add_zero]
  | d + 1 => by
    rw [Finset.sum_range_succ, rkm128k_sum_range_succ_shift f d, Finset.sum_range_succ, add_assoc]

private theorem rkm128k_sum_range_sub (g : ℕ → ℝ) :
    ∀ m : ℕ, (∑ s ∈ Finset.range m, (g (s + 1) - g s)) = g m - g 0
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, rkm128k_sum_range_sub g m]
    ring

private theorem rkm128k_sum_fin_eq_range (f : ℕ → ℝ) :
    ∀ m : ℕ, (∑ a : Fin m, f a.1) = ∑ j ∈ Finset.range m, f j
  | 0 => by simp
  | m + 1 => by
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
      Finset.sum_range_succ, rkm128k_sum_fin_eq_range f m]

private theorem rkm128k_sum_sq_le_sq_sum_abs {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, (f i) ^ 2) ≤ (∑ i ∈ s, |f i|) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa : (f a) ^ 2 = |f a| ^ 2 := (sq_abs (f a)).symm
    have hnn1 : 0 ≤ |f a| := abs_nonneg _
    have hnn2 : 0 ≤ ∑ i ∈ s, |f i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    nlinarith [mul_nonneg hnn1 hnn2]

private theorem rkm128k_vecNorm_le_sum_abs {d : ℕ} (u : Fin (d + 1) → ℝ) :
    vecNorm u ≤ ∑ a : Fin (d + 1), |u a| := by
  rw [vecNorm, Real.sqrt_le_iff]
  exact ⟨Finset.sum_nonneg fun _ _ ↦ abs_nonneg _, rkm128k_sum_sq_le_sq_sum_abs Finset.univ u⟩

private theorem rkm128k_vecNorm_sum_le {d : ℕ} (f : ℕ → Fin d → ℝ) :
    ∀ m : ℕ, vecNorm (∑ k ∈ Finset.range m, f k) ≤ ∑ k ∈ Finset.range m, vecNorm (f k)
  | 0 => by simp [vecNorm_zero]
  | m + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (vecNorm_add_le _ _).trans (add_le_add (rkm128k_vecNorm_sum_le f m) le_rfl)

private theorem rkm128k_mulVec_sum_smul {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (c : ℕ → ℝ) (f : ℕ → Fin d → ℝ) :
    ∀ m : ℕ, H *ᵥ (∑ k ∈ Finset.range m, c k • f k) = ∑ k ∈ Finset.range m, c k • (H *ᵥ f k)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_smul,
      rkm128k_mulVec_sum_smul H c f m, Finset.sum_range_succ]

private theorem rkm128k_vecL1_ge :
    ∀ (xs : List ℤ) (m : ℕ), (∑ j ∈ Finset.range m, |(xs.getD j 0 : ℝ)|) ≤ (rkm128kVecL1 xs : ℝ)
  | [], _ => by simp [rkm128kVecL1]
  | x :: rest, 0 => by unfold rkm128kVecL1; positivity
  | x :: rest, m + 1 => by
    unfold rkm128kVecL1
    rw [rkm128k_sum_range_succ_shift, Nat.add_eq, Nat.cast_add, rkm128k_cast_natAbs]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact add_le_add le_rfl (rkm128k_vecL1_ge rest m)

private theorem rkm128k_vecNorm_le_vecL1 (d : ℕ) (xs : List ℤ) :
    vecNorm (rkmListToOrbVec d xs) ≤ (rkm128kVecL1 xs : ℝ) / wdScaleR := by
  have hB : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  refine (rkm128k_vecNorm_le_sum_abs _).trans ?_
  have h1 : (∑ a : Fin (d + 1), |(rkmListToOrbVec d xs) a|) =
      (∑ j ∈ Finset.range (d + 1), |(xs.getD j 0 : ℝ)|) / wdScaleR := by
    unfold rkmListToOrbVec
    have h2 : (∑ a : Fin (d + 1), |(xs.getD a.1 0 : ℝ) / wdScaleR|) =
        ∑ j ∈ Finset.range (d + 1), (|(xs.getD j 0 : ℝ)| / wdScaleR) := by
      rw [← rkm128k_sum_fin_eq_range (fun j ↦ |(xs.getD j 0 : ℝ)| / wdScaleR)]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [abs_div, abs_of_pos hB]
    rw [h2, ← Finset.sum_div]
  rw [h1]
  exact div_le_div_of_nonneg_right (rkm128k_vecL1_ge xs (d + 1)) hB.le

private theorem rkm128k_vecAdd_length :
    ∀ (xs ys : List ℤ), (rkm128kVecAdd xs ys).length = max xs.length ys.length
  | [], ys => by simp [rkm128kVecAdd]
  | x :: xRest, [] => by simp [rkm128kVecAdd]
  | x :: xRest, y :: yRest => by
    unfold rkm128kVecAdd
    dsimp only
    rw [rkm128k_strictConsInt_eq]
    simp only [List.length_cons, rkm128k_vecAdd_length xRest yRest, Nat.succ_max_succ]

private theorem rkm128k_vecAdd_getD :
    ∀ (xs ys : List ℤ) (j : ℕ), (rkm128kVecAdd xs ys).getD j 0 = xs.getD j 0 + ys.getD j 0
  | [], ys, j => by simp [rkm128kVecAdd]
  | x :: xRest, [], j => by simp [rkm128kVecAdd]
  | x :: xRest, y :: yRest, 0 => by
    unfold rkm128kVecAdd
    dsimp only
    rw [rkm128k_strictConsInt_eq, rkm128k_rawAdd_eq]
    rfl
  | x :: xRest, y :: yRest, j + 1 => by
    unfold rkm128kVecAdd
    dsimp only
    rw [rkm128k_strictConsInt_eq, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact rkm128k_vecAdd_getD xRest yRest j

private theorem rkm128k_vecAdd_orbVec (d : ℕ) (xs ys : List ℤ) :
    rkmListToOrbVec d (rkm128kVecAdd xs ys) = rkmListToOrbVec d xs + rkmListToOrbVec d ys := by
  funext a
  simp only [rkmListToOrbVec, Pi.add_apply, rkm128k_vecAdd_getD, Int.cast_add, add_div]

private def rkm128kMatEntry (prev : ℤ) (hb cur : List ℤ) (j : ℕ) : ℤ :=
  (if j = 0 then prev else hb.getD (j - 1) 0 * cur.getD (j - 1) 0) -
    hb.getD j 0 * cur.getD (j + 1) 0

private theorem rkm128k_matVecL1Loop_ge :
    ∀ (m : ℕ) (prev : ℤ) (hb cur : List ℤ),
      (∑ j ∈ Finset.range m, |(rkm128kMatEntry prev hb cur j : ℝ)|) ≤
        (rkm128kMatVecL1Loop prev hb cur : ℝ)
  | 0, prev, hb, cur => by positivity
  | m + 1, prev, hb, [] => by
    unfold rkm128kMatVecL1Loop
    rw [rkm128k_sum_range_succ_shift, rkm128k_cast_natAbs]
    have h0 : rkm128kMatEntry prev hb [] 0 = prev := by simp [rkm128kMatEntry]
    have hrest : (∑ j ∈ Finset.range m, |(rkm128kMatEntry prev hb [] (j + 1) : ℝ)|) = 0 := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp [rkm128kMatEntry]
    rw [h0, hrest, add_zero]
  | m + 1, prev, [], c0 :: cTail => by
    unfold rkm128kMatVecL1Loop
    rw [rkm128k_sum_range_succ_shift, rkm128k_cast_natAbs]
    have h0 : rkm128kMatEntry prev [] (c0 :: cTail) 0 = prev := by simp [rkm128kMatEntry]
    have hrest : (∑ j ∈ Finset.range m, |(rkm128kMatEntry prev [] (c0 :: cTail) (j + 1) : ℝ)|) =
        0 := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp [rkm128kMatEntry]
    rw [h0, hrest, add_zero]
  | m + 1, prev, b :: hbRest, c0 :: cTail => by
    unfold rkm128kMatVecL1Loop
    dsimp only
    rw [Nat.add_eq, Nat.cast_add, rkm128k_cast_natAbs, rkm128k_rawSub_eq, rkm128k_rawMul_eq,
      primIntMul_eq, rkm128k_sum_range_succ_shift]
    have hc1 : (match cTail with
        | cn :: _ => cn
        | [] => Int.ofNat 0) = cTail.getD 0 0 := by
      cases cTail <;> rfl
    have h0 : rkm128kMatEntry prev (b :: hbRest) (c0 :: cTail) 0 = prev - b * cTail.getD 0 0 := by
      simp [rkm128kMatEntry]
    have hshift (j : ℕ) :
        rkm128kMatEntry prev (b :: hbRest) (c0 :: cTail) (j + 1) =
          rkm128kMatEntry (b * c0) hbRest cTail j := by
      rcases j with _ | j' <;> simp [rkm128kMatEntry]
    rw [h0]
    refine add_le_add ?_ ?_
    · cases cTail <;> exact le_rfl
    · simpa only [hshift] using rkm128k_matVecL1Loop_ge m (b * c0) hbRest cTail

private theorem rkm128k_ptGenMat_mulVec_apply {d : ℕ} {hb : List ℤ} (hhb : hb.length ≤ d)
    (cur : List ℤ) (a : Fin (d + 1)) :
    (rkmPtGenMat d hb *ᵥ rkmListToOrbVec d cur) a =
      (rkm128kMatEntry 0 hb cur a.1 : ℝ) / wdScaleR ^ 2 := by
  have hB : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  unfold rkmPtGenMat
  rw [tridiagSkewMat_mulVec_apply]
  by_cases ha0 : 0 < a.1
  · have hne0 : a.1 ≠ 0 := by omega
    rw [dite_eq_left ha0]
    by_cases had : a.1 < d
    · rw [dite_eq_left had]
      dsimp only [rkmListToOrbVec, rkm128kMatEntry]
      rw [ite_eq_right hne0]
      push_cast
      field_simp [hB.ne']
      ring
    · rw [dite_eq_right had]
      dsimp only [rkmListToOrbVec, rkm128kMatEntry]
      rw [ite_eq_right hne0, rkm_getD_eq_zero_of_le hb a.1 (by omega)]
      push_cast
      field_simp [hB.ne']
      ring
  · have heq0 : a.1 = 0 := by omega
    rw [dite_eq_right ha0]
    by_cases had : a.1 < d
    · rw [dite_eq_left had]
      dsimp only [rkmListToOrbVec, rkm128kMatEntry]
      rw [ite_eq_left heq0]
      push_cast
      field_simp [hB.ne']
      ring
    · rw [dite_eq_right had]
      dsimp only [rkmListToOrbVec, rkm128kMatEntry]
      rw [ite_eq_left heq0, rkm_getD_eq_zero_of_le hb a.1 (by omega)]
      push_cast
      field_simp [hB.ne']
      ring

private theorem rkm128k_ptGenMat_mulVec_le {d : ℕ} {hb : List ℤ} (hhb : hb.length ≤ d)
    (cur : List ℤ) :
    vecNorm (rkmPtGenMat d hb *ᵥ rkmListToOrbVec d cur) ≤
      (rkm128kCeilDiv15 (rkm128kMatVecL1Loop (Int.ofNat 0) hb cur) : ℝ) / wdScaleR := by
  have hB2 : (0 : ℝ) < wdScaleR ^ 2 := by unfold wdScaleR wdScale; positivity
  refine (rkm128k_vecNorm_le_sum_abs _).trans ?_
  have h1 : (∑ a : Fin (d + 1), |(rkmPtGenMat d hb *ᵥ rkmListToOrbVec d cur) a|) =
      (∑ j ∈ Finset.range (d + 1), |(rkm128kMatEntry 0 hb cur j : ℝ)|) / wdScaleR ^ 2 := by
    rw [Finset.sum_div,
      ← rkm128k_sum_fin_eq_range (fun j ↦ |(rkm128kMatEntry 0 hb cur j : ℝ)| / wdScaleR ^ 2)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [rkm128k_ptGenMat_mulVec_apply hhb cur a, abs_div, abs_of_pos hB2]
  rw [h1]
  have h2 := div_le_div_of_nonneg_right (rkm128k_matVecL1Loop_ge (d + 1) 0 hb cur) hB2.le
  exact h2.trans (rkm128k_ceilDiv15_sq_ge (rkm128kMatVecL1Loop 0 hb cur))

private theorem rkm128k_tail_getD : ∀ (xs : List ℤ) (j : ℕ),
    (match xs with
      | _ :: xt => xt
      | [] => []).getD j 0 = xs.getD (j + 1) 0
  | [], _ => rfl
  | _ :: _, _ => rfl

private theorem rkm128k_head_getD (xs : List ℤ) :
    (match xs with
      | x :: _ => x
      | [] => Int.ofNat 0) = xs.getD 0 0 := by
  cases xs <;> rfl

private theorem rkm128k_second_getD (xs : List ℤ) :
    (match xs with
      | _ :: xn :: _ => xn
      | _ => Int.ofNat 0) = xs.getD 1 0 := by
  rcases xs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

private theorem rkm128k_intTdivNat_eq (x : ℤ) (dNat : ℕ) :
    highdIntTdivNat x dNat = Int.tdiv x (Int.ofNat dNat) := by
  cases x with
  | ofNat m =>
    dsimp only [highdIntTdivNat]
    rw [primOfNatForced_eq]
    rfl
  | negSucc m =>
    dsimp only [highdIntTdivNat]
    rw [primNegOfNat_eq]
    change -(((m + 1) / dNat : ℕ) : ℤ) = -(Int.ofNat ((m + 1) / dNat))
    rfl

private theorem rkm128k_hornerSlideLoop_length (dNat : ℕ) :
    ∀ (outLen : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      (hornerSlideLoop dNat prev hb vec cur outLen).length = outLen
  | 0, _, _, _, _ => rfl
  | rem + 1, prev, hb, vec, cur => by
    unfold hornerSlideLoop hornerSlideLoopAux
    cases hb with
    | nil =>
      dsimp only
      rw [rkm128k_strictConsInt_eq]
      exact congrArg Nat.succ (rkm128k_hornerSlideLoop_length dNat rem 0 [] _ _)
    | cons b hbRest =>
      dsimp only
      rw [rkm128k_strictConsInt_eq]
      exact congrArg Nat.succ (rkm128k_hornerSlideLoop_length dNat rem _ hbRest _ _)

private theorem rkm128k_hornerSlideLoop_getD (dNat : ℕ) :
    ∀ (outLen : ℕ) (prev : ℤ) (hb vec cur : List ℤ) (j : ℕ),
      j < outLen →
      (hornerSlideLoop dNat prev hb vec cur outLen).getD j 0 =
        vec.getD j 0 + Int.tdiv (rkm128kMatEntry prev hb cur j) (Int.ofNat dNat)
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, prev, hb, vec, cur, 0, _ => by
    unfold hornerSlideLoop hornerSlideLoopAux
    cases hb with
    | nil =>
      dsimp only
      rw [rkm128k_strictConsInt_eq]
      simp only [primIntAdd_eq, rkm128k_intTdivNat_eq]
      change (match vec with
          | v :: _ => v
          | [] => Int.ofNat 0) + Int.tdiv prev (Int.ofNat dNat) = _
      rw [rkm128k_head_getD]
      simp [rkm128kMatEntry]
    | cons b hbRest =>
      dsimp only
      rw [rkm128k_strictConsInt_eq]
      simp only [primIntAdd_eq, primIntSub_eq, primIntMul_eq, rkm128k_intTdivNat_eq]
      change (match vec with
          | v :: _ => v
          | [] => Int.ofNat 0) +
        Int.tdiv (prev - b * (match cur with
          | _ :: cn :: _ => cn
          | _ => Int.ofNat 0)) (Int.ofNat dNat) = _
      rw [rkm128k_head_getD, rkm128k_second_getD]
      simp [rkm128kMatEntry]
  | rem + 1, prev, hb, vec, cur, j + 1, hj => by
    unfold hornerSlideLoop hornerSlideLoopAux
    set vTail :=
      match vec with
      | _ :: vt => vt
      | [] => ([] : List ℤ)
    set c0 :=
      match cur with
      | c :: _ => c
      | [] => Int.ofNat 0
    set cTail :=
      match cur with
      | _ :: ct => ct
      | [] => ([] : List ℤ)
    have hvT : vTail.getD j 0 = vec.getD (j + 1) 0 := rkm128k_tail_getD vec j
    have hcT1 : cTail.getD (j + 1) 0 = cur.getD (j + 2) 0 := rkm128k_tail_getD cur (j + 1)
    cases hb with
    | nil =>
      dsimp only
      rw [rkm128k_strictConsInt_eq]
      change (hornerSlideLoop dNat 0 [] vTail cTail rem).getD j 0 = _
      rw [rkm128k_hornerSlideLoop_getD dNat rem 0 [] vTail cTail j (by omega), hvT]
      rcases j with _ | j' <;> simp [rkm128kMatEntry]
    | cons b hbRest =>
      dsimp only
      rw [rkm128k_strictConsInt_eq]
      change (hornerSlideLoop dNat (primIntMul b c0) hbRest vTail cTail rem).getD j 0 = _
      rw [primIntMul_eq,
        rkm128k_hornerSlideLoop_getD dNat rem (b * c0) hbRest vTail cTail j (by omega), hvT]
      congr 2
      dsimp only [rkm128kMatEntry]
      rw [hcT1]
      rcases j with _ | j'
      · rw [show c0 = cur.getD 0 0 from rkm128k_head_getD cur]
        simp
      · have hcTj : cTail.getD j' 0 = cur.getD (j' + 1) 0 := rkm128k_tail_getD cur j'
        have hj1 : j' + 1 ≠ 0 := Nat.succ_ne_zero j'
        have hj2 : j' + 1 + 1 ≠ 0 := Nat.succ_ne_zero _
        simp only [hj1, hj2, ↓reduceIte, Nat.add_sub_cancel, List.getD_cons_succ, hcTj]

private theorem rkm128k_tdiv_diff_abs_le (num : ℤ) {dNat : ℕ} (hd : 1 ≤ dNat) :
    |((Int.tdiv num (Int.ofNat dNat) : ℤ) : ℝ) - (num : ℝ) / (dNat : ℝ)| ≤ 1 := by
  have hd_pos : (0 : ℝ) < (dNat : ℝ) := by exact_mod_cast hd
  have hcore (A : ℕ) : |((A / dNat : ℕ) : ℝ) - (A : ℝ) / (dNat : ℝ)| ≤ 1 := by
    set q := A / dNat
    have hlo_nat : q * dNat ≤ A := Nat.div_mul_le_self A dNat
    have hhi_nat : A < (q + 1) * dNat :=
      (Nat.lt_mul_div_succ A (by omega : 0 < dNat)).trans_eq (Nat.mul_comm _ _)
    have hloR : (q : ℝ) * (dNat : ℝ) ≤ (A : ℝ) := by exact_mod_cast hlo_nat
    have hhiR : (A : ℝ) ≤ ((q : ℝ) + 1) * (dNat : ℝ) := by
      have hc : (A : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * (dNat : ℝ) := by exact_mod_cast hhi_nat.le
      push_cast at hc
      exact hc
    have hq_le : (q : ℝ) ≤ (A : ℝ) / (dNat : ℝ) := (le_div_iff₀ hd_pos).mpr hloR
    have hq_ge : (A : ℝ) / (dNat : ℝ) - (q : ℝ) ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ hd_pos]
      linarith
    rw [abs_le]
    constructor <;> linarith
  cases num with
  | ofNat a =>
    have h1 : ((Int.tdiv (Int.ofNat a) (Int.ofNat dNat) : ℤ) : ℝ) = ((a / dNat : ℕ) : ℝ) := by
      change ((Int.ofNat (a / dNat) : ℤ) : ℝ) = ((a / dNat : ℕ) : ℝ)
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    have h2 : ((Int.ofNat a : ℤ) : ℝ) = (a : ℝ) := by
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [h1, h2]
    exact hcore a
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

private theorem rkm128k_altIntLen_eq : ∀ xs : List ℤ, altIntLen xs = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (rkm128k_altIntLen_eq xs)

private theorem rkm128k_stage_zero_approx {deg d : ℕ} {hb cur : List ℤ}
    (hdeg : 1 ≤ deg) (hd : d ≤ 1024) (hhb : hb.length ≤ d) :
    let out := muxFastHornerStage deg (d + 1) hb [] cur
    out.length ≤ d + 1 ∧
      vecNorm (rkmPtGenMat d hb *ᵥ rkmListToOrbVec d cur -
        (deg : ℝ) • rkmListToOrbVec d out) ≤ ((deg : ℝ) * 33) / wdScaleR := by
  intro out
  have hB_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  have hdeg_pos : (0 : ℝ) < (deg : ℝ) := by exact_mod_cast hdeg
  have hout_slide : out = hornerStageSlide deg (d + 1) hb [] cur :=
    muxFastHornerStage_eq deg (d + 1) hb [] cur
  have hout_def : out = applyHgTdivSlide deg (min (d + 1) (cur.length + 1)) hb [] cur := by
    rw [hout_slide]
    unfold hornerStageSlide
    rw [rkmb_forceNat_eq, rkmb_natMin_eq, rkm128k_altIntLen_eq]
  set nxtLen := min (d + 1) (cur.length + 1)
  have hlen : out.length = nxtLen := by
    rw [hout_def]
    unfold applyHgTdivSlide
    rw [rkmb_forceNat_eq]
    exact rkm128k_hornerSlideLoop_length _ nxtLen 0 hb [] cur
  refine ⟨by rw [hlen]; exact Nat.min_le_left _ _, ?_⟩
  set diff := rkmListToOrbVec d out -
    (1 / (deg : ℝ)) • (rkmPtGenMat d hb *ᵥ rkmListToOrbVec d cur)
  have hentry (a : Fin (d + 1)) : |diff a| ≤ 1 / wdScaleR := by
    have hmat := rkm128k_ptGenMat_mulVec_apply hhb cur a
    by_cases hlt : a.1 < nxtLen
    · have hget : out.getD a.1 0 =
          Int.tdiv (rkm128kMatEntry 0 hb cur a.1) (Int.ofNat (deg * wdScale)) := by
        rw [hout_def]
        unfold applyHgTdivSlide
        rw [rkmb_forceNat_eq, show Nat.mul deg wdScale = deg * wdScale from rfl,
          show Int.ofNat 0 = (0 : ℤ) from rfl,
          rkm128k_hornerSlideLoop_getD (deg * wdScale) nxtLen 0 hb [] cur a.1 hlt]
        simp
      set dNat := deg * wdScale
      have hdNat1 : 1 ≤ dNat := by dsimp [dNat]; unfold wdScale; omega
      have hdNatR : (dNat : ℝ) = (deg : ℝ) * wdScaleR := by
        dsimp [dNat]; unfold wdScaleR; push_cast; rfl
      have hdiff_eq : diff a =
          (((Int.tdiv (rkm128kMatEntry 0 hb cur a.1) (Int.ofNat dNat) : ℤ) : ℝ) -
            (rkm128kMatEntry 0 hb cur a.1 : ℝ) / (dNat : ℝ)) / wdScaleR := by
        dsimp [diff, rkmListToOrbVec]
        simp only [Int.ofNat_eq_natCast] at hget ⊢
        rw [hget, hmat, hdNatR]
        field_simp [hB_pos.ne', hdeg_pos.ne']
      rw [hdiff_eq, abs_div, abs_of_pos hB_pos]
      exact div_le_div_of_nonneg_right (rkm128k_tdiv_diff_abs_le _ hdNat1) hB_pos.le
    · have hc_le : cur.length + 1 ≤ a.1 := by
        have : nxtLen = min (d + 1) (cur.length + 1) := rfl
        omega
      have hout_z : out.getD a.1 0 = 0 := rkm_getD_eq_zero_of_le out a.1 (by omega)
      have hnum0 : rkm128kMatEntry 0 hb cur a.1 = 0 := by
        dsimp [rkm128kMatEntry]
        rw [rkm_getD_eq_zero_of_le cur (a.1 - 1) (by omega),
          rkm_getD_eq_zero_of_le cur (a.1 + 1) (by omega)]
        split_ifs <;> simp
      have hdiff0 : diff a = 0 := by
        dsimp [diff, rkmListToOrbVec]
        rw [hout_z, hmat, hnum0]
        simp
      rw [hdiff0, abs_zero]
      positivity
  have hdiff_norm : vecNorm diff ≤ 33 / wdScaleR := by
    rw [vecNorm, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hsq_le (a : Fin (d + 1)) : (diff a) ^ 2 ≤ (1 / wdScaleR) ^ 2 := by
      rw [← sq_abs (diff a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hentry a) 2
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
  have hscale : rkmPtGenMat d hb *ᵥ rkmListToOrbVec d cur - (deg : ℝ) • rkmListToOrbVec d out =
      (-(deg : ℝ)) • diff := by
    ext a
    dsimp only [diff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hdeg_pos.ne']
    ring
  rw [hscale, vecNorm_smul, abs_neg, abs_of_pos hdeg_pos]
  exact (mul_le_mul_of_nonneg_left hdiff_norm hdeg_pos.le).trans_eq (by ring)

private def rkm128kStageSeq (d : ℕ) (hb vec : List ℤ) : ℕ → List ℤ
  | 0 => vec
  | k + 1 => muxFastHornerStage (k + 1) (d + 1) hb [] (rkm128kStageSeq d hb vec k)

private theorem rkm128k_taylorLoop_spec {d : ℕ} {hb vec : List ℤ}
    (hd : d ≤ 1024) (hhb : hb.length ≤ d) :
    ∀ (rem k0 : ℕ) (acc0 : List ℤ) (sum0 : ℕ),
      acc0.length ≤ d + 1 →
      let res := rkm128kTaylorLoop (Nat.add d 1) hb rem (k0 + 1)
        (rkm128kStageSeq d hb vec k0) acc0 sum0
      res.1 = rkm128kStageSeq d hb vec (k0 + rem) ∧
        res.2.1.length ≤ d + 1 ∧
        rkmListToOrbVec d res.2.1 = rkmListToOrbVec d acc0 +
          ∑ j ∈ Finset.range rem, rkmListToOrbVec d (rkm128kStageSeq d hb vec (k0 + 1 + j)) ∧
        (res.2.2 : ℝ) = (sum0 : ℝ) +
          ∑ j ∈ Finset.range rem, (rkm128kVecL1 (rkm128kStageSeq d hb vec (k0 + 1 + j)) : ℝ)
  | 0, k0, acc0, sum0, hacc => by
    simp [rkm128kTaylorLoop, hacc]
  | rem + 1, k0, acc0, sum0, hacc => by
    intro res
    have hres_eq : res = rkm128kTaylorLoop (Nat.add d 1) hb rem (k0 + 1 + 1)
        (rkm128kStageSeq d hb vec (k0 + 1))
        (rkm128kVecAdd acc0 (rkm128kStageSeq d hb vec (k0 + 1)))
        (sum0 + rkm128kVecL1 (rkm128kStageSeq d hb vec (k0 + 1))) := by
      dsimp only [res, rkm128kTaylorLoop]
      rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]
      rfl
    have hnxt_len : (rkm128kStageSeq d hb vec (k0 + 1)).length ≤ d + 1 :=
      (rkm128k_stage_zero_approx (by omega : 1 ≤ k0 + 1) hd hhb).1
    have hacc1 : (rkm128kVecAdd acc0 (rkm128kStageSeq d hb vec (k0 + 1))).length ≤ d + 1 := by
      rw [rkm128k_vecAdd_length]
      exact max_le hacc hnxt_len
    have ih := rkm128k_taylorLoop_spec (vec := vec) hd hhb rem (k0 + 1)
      (rkm128kVecAdd acc0 (rkm128kStageSeq d hb vec (k0 + 1)))
      (sum0 + rkm128kVecL1 (rkm128kStageSeq d hb vec (k0 + 1))) hacc1
    dsimp only at ih
    rw [hres_eq]
    refine ⟨?_, ih.2.1, ?_, ?_⟩
    · rw [ih.1, show k0 + 1 + rem = k0 + (rem + 1) by omega]
    · rw [ih.2.2.1, rkm128k_vecAdd_orbVec, rkm128k_sum_range_succ_shift, add_assoc]
      refine congrArg (rkmListToOrbVec d acc0 + ·) (congrArg₂ (· + ·) rfl ?_)
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      exact congrArg (fun t ↦ rkmListToOrbVec d (rkm128kStageSeq d hb vec t)) (by omega)
    · rw [ih.2.2.2, Nat.cast_add, rkm128k_sum_range_succ_shift, Nat.add_zero, add_assoc]
      congr 2
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show k0 + 1 + 1 + j = k0 + 1 + (j + 1) by omega]

private noncomputable def rkm128kFactInv : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1 / 2
  | 3 => 1 / 6
  | 4 => 1 / 24
  | 5 => 1 / 120
  | 6 => 1 / 720
  | 7 => 1 / 5040
  | 8 => 1 / 40320
  | 9 => 1 / 362880
  | 10 => 1 / 3628800
  | 11 => 1 / 39916800
  | 12 => 1 / 479001600
  | 13 => 1 / 6227020800
  | 14 => 1 / 87178291200
  | 15 => 1 / 1307674368000
  | 16 => 1 / 20922789888000
  | _ + 17 => 0

private lemma rkm128kFactInv_nonneg : ∀ k : ℕ, 0 ≤ rkm128kFactInv k
  | 0 => by norm_num [rkm128kFactInv]
  | 1 => by norm_num [rkm128kFactInv]
  | 2 => by norm_num [rkm128kFactInv]
  | 3 => by norm_num [rkm128kFactInv]
  | 4 => by norm_num [rkm128kFactInv]
  | 5 => by norm_num [rkm128kFactInv]
  | 6 => by norm_num [rkm128kFactInv]
  | 7 => by norm_num [rkm128kFactInv]
  | 8 => by norm_num [rkm128kFactInv]
  | 9 => by norm_num [rkm128kFactInv]
  | 10 => by norm_num [rkm128kFactInv]
  | 11 => by norm_num [rkm128kFactInv]
  | 12 => by norm_num [rkm128kFactInv]
  | 13 => by norm_num [rkm128kFactInv]
  | 14 => by norm_num [rkm128kFactInv]
  | 15 => by norm_num [rkm128kFactInv]
  | 16 => by norm_num [rkm128kFactInv]
  | _ + 17 => by norm_num [rkm128kFactInv]

private theorem rkm128k_taylor16_sub_linear_le {d : ℕ} {X : Matrix (Fin d) (Fin d) ℝ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hX : ∀ u, vecNorm (X *ᵥ u) ≤ c * vecNorm u)
    (v : Fin d → ℝ) :
    vecNorm ((taylor16OfMat X - (1 + X)) *ᵥ v) ≤ c ^ 2 * vecNorm v := by
  have hexp : (taylor16OfMat X - (1 + X)) *ᵥ v =
      ∑ j ∈ Finset.range 15, rkm128kFactInv (j + 2) • ((X ^ (j + 2)) *ᵥ v) := by
    ext i
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      rkm128kFactInv, taylor16OfMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexp]
  refine (rkm128k_vecNorm_sum_le _ 15).trans ?_
  have hterm (j : ℕ) :
      vecNorm (rkm128kFactInv (j + 2) • ((X ^ (j + 2)) *ᵥ v)) ≤
        rkm128kFactInv (j + 2) * (c ^ 2 * vecNorm v) := by
    rw [vecNorm_smul, abs_of_nonneg (rkm128kFactInv_nonneg (j + 2))]
    have hp1 := vecNorm_pow_mulVec_le hc0 hX (j + 2) v
    have hp2 : c ^ (j + 2) ≤ c ^ 2 := pow_le_pow_of_le_one hc0 hc1 (by omega)
    exact mul_le_mul_of_nonneg_left
      (hp1.trans (mul_le_mul_of_nonneg_right hp2 (vecNorm_nonneg v)))
      (rkm128kFactInv_nonneg (j + 2))
  have hsum1 : (∑ j ∈ Finset.range 15, vecNorm (rkm128kFactInv (j + 2) • ((X ^ (j + 2)) *ᵥ v))) ≤
      (∑ j ∈ Finset.range 15, rkm128kFactInv (j + 2)) * (c ^ 2 * vecNorm v) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ ↦ hterm j
  have hcoef : (∑ j ∈ Finset.range 15, rkm128kFactInv (j + 2)) ≤ 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, rkm128kFactInv]
    norm_num
  exact hsum1.trans ((mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg c) (vecNorm_nonneg v))).trans_eq (one_mul _))

private theorem rkm128k_pow_sub_ge_deriv {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) * δ * a ^ j ≤ (a + δ) ^ (j + 1) - a ^ (j + 1)
  | 0 => by simp
  | j + 1 => by
    have ih := rkm128k_pow_sub_ge_deriv ha hδ j
    have hnn : 0 ≤ (a + δ) ^ (j + 1) - a ^ (j + 1) :=
      le_trans (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) (pow_nonneg ha j)) ih
    have hid : (a + δ) ^ (j + 1 + 1) - a ^ (j + 1 + 1) =
        (a + δ) * ((a + δ) ^ (j + 1) - a ^ (j + 1)) + δ * a ^ (j + 1) := by ring
    have hmul : a * (((j + 1 : ℕ) : ℝ) * δ * a ^ j) ≤
        (a + δ) * ((a + δ) ^ (j + 1) - a ^ (j + 1)) :=
      (mul_le_mul_of_nonneg_left ih ha).trans
        (mul_le_mul_of_nonneg_right (by linarith) hnn)
    rw [hid]
    have hlhs : ((j + 1 + 1 : ℕ) : ℝ) * δ * a ^ (j + 1) =
        a * (((j + 1 : ℕ) : ℝ) * δ * a ^ j) + δ * a ^ (j + 1) := by push_cast; ring
    linarith

private theorem rkm128k_pow_sub_le_lip {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (h1 : a + δ ≤ 1) :
    ∀ m : ℕ, (a + δ) ^ m - a ^ m ≤ (m : ℝ) * δ
  | 0 => by simp
  | m + 1 => by
    have ih := rkm128k_pow_sub_le_lip ha hδ h1 m
    have hnn : 0 ≤ (a + δ) ^ m - a ^ m :=
      sub_nonneg.mpr (pow_le_pow_left₀ ha (by linarith) m)
    have ham : a ^ m ≤ 1 := pow_le_one₀ ha (by linarith)
    have hid : (a + δ) ^ (m + 1) - a ^ (m + 1) =
        (a + δ) * ((a + δ) ^ m - a ^ m) + δ * a ^ m := by ring
    have hstep1 : (a + δ) * ((a + δ) ^ m - a ^ m) ≤ 1 * ((m : ℝ) * δ) :=
      mul_le_mul h1 ih hnn zero_le_one
    have hstep2 : δ * a ^ m ≤ δ * 1 := mul_le_mul_of_nonneg_left ham hδ
    rw [hid, Nat.cast_succ]
    linarith

private theorem rkm128k_curve_rem_bounds {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (h1 : a + δ ≤ 1) :
    ∀ j : ℕ,
      0 ≤ (a + δ) ^ (j + 1) - a ^ (j + 1) - ((j + 1 : ℕ) : ℝ) * δ * a ^ j ∧
        (a + δ) ^ (j + 1) - a ^ (j + 1) - ((j + 1 : ℕ) : ℝ) * δ * a ^ j ≤
          ((j + 1 : ℕ) : ℝ) ^ 2 * δ ^ 2
  | 0 => by
    have h0 : (a + δ) ^ (0 + 1) - a ^ (0 + 1) - ((0 + 1 : ℕ) : ℝ) * δ * a ^ 0 = 0 := by
      push_cast
      ring
    rw [h0]
    exact ⟨le_rfl, by positivity⟩
  | j + 1 => by
    obtain ⟨ih0, ih1⟩ := rkm128k_curve_rem_bounds ha hδ h1 j
    set D0 := (a + δ) ^ (j + 1) - a ^ (j + 1) - ((j + 1 : ℕ) : ℝ) * δ * a ^ j
    set D1 := (a + δ) ^ (j + 1 + 1) - a ^ (j + 1 + 1) - ((j + 1 + 1 : ℕ) : ℝ) * δ * a ^ (j + 1)
    have hid : D1 = a * D0 + δ * ((a + δ) ^ (j + 1) - a ^ (j + 1)) := by
      dsimp only [D0, D1]
      push_cast
      ring
    have hlip := rkm128k_pow_sub_le_lip ha hδ h1 (j + 1)
    have hsub_nn : 0 ≤ (a + δ) ^ (j + 1) - a ^ (j + 1) :=
      sub_nonneg.mpr (pow_le_pow_left₀ ha (by linarith) (j + 1))
    refine ⟨by rw [hid]; exact add_nonneg (mul_nonneg ha ih0) (mul_nonneg hδ hsub_nn), ?_⟩
    have ha1 : a ≤ 1 := by linarith
    have hp1 : a * D0 ≤ 1 * (((j + 1 : ℕ) : ℝ) ^ 2 * δ ^ 2) := mul_le_mul ha1 ih1 ih0 zero_le_one
    have hp2 : δ * ((a + δ) ^ (j + 1) - a ^ (j + 1)) ≤ δ * (((j + 1 : ℕ) : ℝ) * δ) :=
      mul_le_mul_of_nonneg_left hlip hδ
    have hsq_step :
        ((j + 1 : ℕ) : ℝ) ^ 2 * δ ^ 2 + δ * (((j + 1 : ℕ) : ℝ) * δ) ≤
          ((j + 1 + 1 : ℕ) : ℝ) ^ 2 * δ ^ 2 := by
      have hcoef : ((j + 1 : ℕ) : ℝ) ^ 2 + ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast
        nlinarith
      exact (by ring : ((j + 1 : ℕ) : ℝ) ^ 2 * δ ^ 2 + δ * (((j + 1 : ℕ) : ℝ) * δ) =
        (((j + 1 : ℕ) : ℝ) ^ 2 + ((j + 1 : ℕ) : ℝ)) * δ ^ 2) ▸
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg δ)
    rw [hid]
    linarith

private theorem rkm128k_contr_curve_tel {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ x, vecNorm (A *ᵥ x) ≤ vecNorm x) (γ : ℕ → Fin d → ℝ) :
    ∀ t : ℕ, vecNorm ((A ^ t) *ᵥ γ 0 - γ t) ≤ ∑ s ∈ Finset.range t, vecNorm (A *ᵥ γ s - γ (s + 1))
  | 0 => by simp [vecNorm_zero]
  | t + 1 => by
    have hsp : (A ^ (t + 1)) *ᵥ γ 0 - γ (t + 1) =
        A *ᵥ ((A ^ t) *ᵥ γ 0 - γ t) + (A *ᵥ γ t - γ (t + 1)) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [hsp, Finset.sum_range_succ]
    exact (vecNorm_add_le _ _).trans
      (add_le_add ((hA _).trans (rkm128k_contr_curve_tel hA γ t)) le_rfl)

private theorem rkm128k_maxBHiFrom_ge (m r : ℕ) :
    ∀ (rem w j : ℕ), j < rem →
      (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤ altMaxBHiFrom m r w rem
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, j, hj => by
    unfold altMaxBHiFrom altMaxBHiFromAux
    simp only [rkmb_forceNat_eq]
    set rad := Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w)
    set bHi := (altIsqrt15 rad).2
    set rMax := altMaxBHiFromAux m r rem (Nat.add w 1)
    rcases j with _ | j'
    · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) = rad := by
        change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
          4 * (w + 1) * (m - w) * (r - w)
        simp
      rw [hrad]
      cases hlt : primNatBlt rMax bHi
      · simp only [cond]
        exact rkm128k_blt_false.mp hlt
      · simp only [cond]
        exact le_rfl
    · have ih := rkm128k_maxBHiFrom_ge m r rem (w + 1) j' (by omega)
      rw [show w + 1 + j' = w + (j' + 1) by omega] at ih
      have ih' : (altIsqrt15 (4 * (w + (j' + 1) + 1) * (m - (w + (j' + 1))) *
          (r - (w + (j' + 1))))).2 ≤ rMax := ih
      cases hlt : primNatBlt rMax bHi
      · simp only [cond]
        exact ih'
      · simp only [cond]
        exact ih'.trans (rkm128k_blt_true.mp hlt).le

private theorem rkm128k_checkHbTight_sound (m r : ℕ) :
    ∀ (rem w : ℕ), altCheckHbTight m r w rem = true → ∀ j < rem,
      (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).2 ≤
        (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1 + 1
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, hchk, j, hj => by
    unfold altCheckHbTight altCheckHbTightAux at hchk
    dsimp only at hchk
    generalize hp : altIsqrt15 (Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1))
      (Nat.sub m w)) (Nat.sub r w)) = p at hchk
    cases hble : Nat.ble p.2 (Nat.add p.1 1) with
    | false =>
      rw [hble, rkm128k_cond_false] at hchk
      exact Bool.noConfusion hchk
    | true =>
      rw [hble, rkm128k_cond_true] at hchk
      rcases j with _ | j'
      · have hrad : 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            Nat.mul (Nat.mul (Nat.mul 4 (Nat.add w 1)) (Nat.sub m w)) (Nat.sub r w) := by
          change 4 * (w + 0 + 1) * (m - (w + 0)) * (r - (w + 0)) =
            4 * (w + 1) * (m - w) * (r - w)
          simp
        rw [hrad, hp]
        exact rkm128k_ble_true.mp hble
      · simpa [show w + 1 + j' = w + (j' + 1) by omega] using
          rkm128k_checkHbTight_sound m r rem (w + 1) hchk j' (by omega)

private theorem rkm128k_buildHbFrom_length (m r hPt : ℕ) :
    ∀ (rem w : ℕ), (altBuildHbFrom m r hPt w rem).length = rem
  | 0, _ => rfl
  | rem + 1, w => by
    unfold altBuildHbFrom altBuildHbFromAux
    rw [strictConsInt_eq]
    exact congrArg Nat.succ (rkm128k_buildHbFrom_length m r hPt rem (w + 1))

private theorem rkm128k_buildHbFrom_getD (m r hPt : ℕ) :
    ∀ (rem w j : ℕ), j < rem →
      (altBuildHbFrom m r hPt w rem).getD j 0 =
        (((hPt * (altIsqrt15 (4 * (w + j + 1) * (m - (w + j)) * (r - (w + j)))).1) /
          wdScale : ℕ) : ℤ)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, w, 0, _ => by
    unfold altBuildHbFrom altBuildHbFromAux
    rw [strictConsInt_eq]
    change (((hPt * (altIsqrt15 (4 * (w + 1) * (m - w) * (r - w))).1) / wdScale : ℕ) : ℤ) = _
    simp
  | rem + 1, w, j + 1, hj => by
    dsimp only [altBuildHbFrom, altBuildHbFromAux]
    rw [strictConsInt_eq, List.getD_cons_succ, show Nat.add w 1 = w + 1 from rfl]
    have ih := rkm128k_buildHbFrom_getD m r hPt rem (w + 1) j (by omega)
    dsimp only [altBuildHbFrom] at ih
    simpa [show w + 1 + j = w + (j + 1) by omega] using ih

private theorem rkm128k_q_bounds {n tau9 nSub : ℕ}
    (hn : 80000 ≤ n) (htau1 : 1 ≤ tau9) (htau : tau9 ≤ 4000000000)
    (hnsub1 : 1 ≤ nSub) (hnsub : nSub ≤ 16384) :
    let q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
    let hPt := (tau9 * 1000000) / nSub
    (2 : ℝ) ^ 150 ≤ (q : ℝ) ∧
      (q : ℝ) ≤ 4 * √(2 ^ n : ℝ) ∧
      |(q : ℝ) / √(2 ^ n : ℝ) - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
  intro q hPt
  set N := 2 ^ n
  have hN_cast : (2 : ℝ) ^ n = (N : ℝ) := by dsimp [N]; norm_cast
  rw [hN_cast]
  have hsN_ge : (2 : ℝ) ^ 201 ≤ √(N : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [← pow_mul, ← hN_cast]
    exact pow_le_pow_right₀ (by norm_num) (by omega : 402 ≤ n)
  have hsN_pos : 0 < √(N : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge
  have hB : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  set S_N := Nat.sqrt N
  have hS_gt : √(N : ℝ) ≤ (S_N : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hlt := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N)
    push_cast at hlt
    linarith
  have hS_le : (S_N : ℝ) ≤ √(N : ℝ) :=
    Real.le_sqrt_of_sq_le (by simpa [sq, Nat.cast_mul] using
      (Nat.cast_le (α := ℝ)).mpr (Nat.sqrt_le N))
  have hdiv_lt : tau9 * S_N < (q + 1) * (nSub * 1000000000) :=
    (Nat.lt_mul_div_succ _ (by positivity : 0 < nSub * 1000000000)).trans_eq (Nat.mul_comm _ _)
  have hdivR : (tau9 : ℝ) * (S_N : ℝ) ≤ ((q : ℝ) + 1) * ((nSub : ℝ) * 1000000000) := by
    have hc := (Nat.cast_le (α := ℝ)).mpr hdiv_lt.le
    push_cast at hc
    linarith
  have htau1R : (1 : ℝ) ≤ (tau9 : ℝ) := by exact_mod_cast htau1
  have htauR : (tau9 : ℝ) ≤ 4000000000 := by exact_mod_cast htau
  have hnsub1R : (1 : ℝ) ≤ (nSub : ℝ) := by exact_mod_cast hnsub1
  have hnsubR : (nSub : ℝ) ≤ 16384 := by exact_mod_cast hnsub
  have hq_lo150 : (2 : ℝ) ^ 150 ≤ (q : ℝ) := by
    have hS200 : (2 : ℝ) ^ 200 ≤ (S_N : ℝ) := by
      linarith [hsN_ge, hS_gt, (by norm_num : (2 : ℝ) ^ 200 + 1 ≤ (2 : ℝ) ^ 201)]
    have hprod_lo : (2 : ℝ) ^ 200 ≤ (tau9 : ℝ) * (S_N : ℝ) := by
      nlinarith
    have hprod_hi : ((q : ℝ) + 1) * ((nSub : ℝ) * 1000000000) ≤
        ((q : ℝ) + 1) * (16384 * 1000000000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hnum : ((2 : ℝ) ^ 150 + 1) * (16384 * 1000000000) ≤ (2 : ℝ) ^ 200 := by norm_num
    linarith
  have hq_div_hi : (q : ℝ) / √(N : ℝ) ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hR : ((nSub : ℝ) * 1000000000) * (q : ℝ) ≤ (tau9 : ℝ) * (S_N : ℝ) := by
      exact_mod_cast Nat.mul_div_le (tau9 * S_N) (nSub * 1000000000)
    rw [div_le_div_iff₀ hsN_pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hS_le (Nat.cast_nonneg tau9)]
  have hq_hi4 : (q : ℝ) ≤ 4 * √(N : ℝ) := by
    have h4 : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact (div_le_iff₀ hsN_pos).mp (hq_div_hi.trans h4)
  have hhPt_lo : (hPt : ℝ) / wdScaleR ≤ (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) := by
    have hR : (hPt : ℝ) * (nSub : ℝ) ≤ (tau9 : ℝ) * 1000000 := by
      exact_mod_cast Nat.div_mul_le_self (tau9 * 1000000) nSub
    rw [hB, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hhPt_hi : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) ≤ ((hPt + 1 : ℕ) : ℝ) / wdScaleR := by
    have hnat : tau9 * 1000000 < (hPt + 1) * nSub :=
      (Nat.lt_mul_div_succ _ (by omega : 0 < nSub)).trans_eq (Nat.mul_comm _ _)
    have hR : (tau9 : ℝ) * 1000000 ≤ ((hPt + 1 : ℕ) : ℝ) * (nSub : ℝ) := by exact_mod_cast hnat.le
    rw [hB, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hq_lo : (tau9 : ℝ) / ((nSub : ℝ) * 1000000000) - (q : ℝ) / √(N : ℝ) ≤ 1 / wdScaleR := by
    have hgap : (tau9 : ℝ) * √(N : ℝ) - (q : ℝ) * ((nSub : ℝ) * 1000000000) ≤
        20384000000000 := by
      nlinarith [mul_le_mul_of_nonneg_left hS_gt (Nat.cast_nonneg tau9)]
    have hbig : (20384000000000 : ℝ) * 1000000000000000 ≤
        ((nSub : ℝ) * 1000000000) * √(N : ℝ) := by
      have h1 : (20384000000000 : ℝ) * 1000000000000000 ≤ 1000000000 * (2 : ℝ) ^ 201 := by
        norm_num
      nlinarith
    rw [hB, div_sub_div _ _ (by positivity) hsN_pos.ne',
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨hq_lo150, hq_hi4, ?_⟩
  rw [abs_le]
  refine ⟨by linarith [hhPt_lo, hq_lo], ?_⟩
  have h1 : ((hPt + 1 : ℕ) : ℝ) / wdScaleR - (hPt : ℝ) / wdScaleR = 1 / wdScaleR := by
    push_cast
    ring
  linarith [hq_div_hi, hhPt_hi, h1]

private theorem rkm128k_gen_diff_op {n mEff r tau9 nSub : ℕ}
    (hn : 80000 ≤ n) (_hm1 : 1 ≤ mEff) (_hm_hi : mEff ≤ 8192)
    (_hr2 : 2 ≤ r) (_hr_hi : r ≤ 1024)
    (htau1 : 1 ≤ tau9) (htau_hi : tau9 ≤ 4000000000)
    (hnsub1 : 1 ≤ nSub) (hnsub_hi : nSub ≤ 16384)
    (htight : altCheckHbTight mEff r 0 (min mEff r) = true) :
    let d := min mEff r
    let q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
    let hPt := (tau9 * 1000000) / nSub
    let bCapCeil := rkm128kCeilDiv15 (2 * altMaxBHiFrom mEff r 0 d)
    let hbPt := altBuildHbFrom mEff r hPt 0 d
    let h_real := (q : ℝ) * (1 / √(2 ^ n : ℝ))
    ∀ u : Fin (d + 1) → ℝ,
      vecNorm ((h_real • dAltGenMat mEff r - rkmPtGenMat d hbPt) *ᵥ u) ≤
        (((bCapCeil : ℝ) + 10) / wdScaleR) * vecNorm u := by
  intro d q hPt bCapCeil hbPt h_real u
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  have hq_bds := rkm128k_q_bounds hn htau1 htau_hi hnsub1 hnsub_hi
  have hh_diff : |h_real - (hPt : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
    dsimp only [h_real, q, hPt]
    simpa [div_eq_mul_inv] using hq_bds.2.2
  have hhPt_le4 : (hPt : ℝ) / wdScaleR ≤ 4 := by
    have hnat : hPt ≤ 4000000000 * 1000000 :=
      (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _ htau_hi)
    rw [hB_eq, div_le_iff₀ (by norm_num)]
    have hR : (hPt : ℝ) ≤ 4000000000000000 := by exact_mod_cast hnat
    linarith
  have hcoupl_cap (j : ℕ) (hj : j < d) : dAltCoupling mEff r j ≤ (1 / 2) * (bCapCeil : ℝ) := by
    have hmax_j := rkm128k_maxBHiFrom_ge mEff r d 0 j hj
    set rad := 4 * (j + 1) * (mEff - j) * (r - j)
    have hsq := (altIsqrt15_sound rad).2
    have hmaxR : ((altIsqrt15 rad).2 : ℝ) ≤ (altMaxBHiFrom mEff r 0 d : ℝ) := by
      have : 4 * (0 + j + 1) * (mEff - (0 + j)) * (r - (0 + j)) = rad := by simp [rad]
      rw [this] at hmax_j
      exact_mod_cast hmax_j
    have hbCeil := rkm128k_ceilDiv15_ge (2 * altMaxBHiFrom mEff r 0 d)
    calc dAltCoupling mEff r j
        ≤ ((altIsqrt15 rad).2 : ℝ) / wdScaleR := hsq
      _ ≤ (altMaxBHiFrom mEff r 0 d : ℝ) / wdScaleR := div_le_div_of_nonneg_right hmaxR hB_pos.le
      _ = (1 / 2) * (((2 * altMaxBHiFrom mEff r 0 d : ℕ) : ℝ) / wdScaleR) := by push_cast; ring
      _ ≤ (1 / 2) * (bCapCeil : ℝ) := mul_le_mul_of_nonneg_left hbCeil (by norm_num)
  have hsub_mat : h_real • dAltGenMat mEff r - rkmPtGenMat d hbPt = tridiagSkewMat d
      (fun j ↦ h_real * dAltCoupling mEff r j - (hbPt.getD j 0 : ℝ) / wdScaleR) :=
    tridiagSkewMat_smul_sub d h_real (dAltCoupling mEff r)
      (fun w ↦ (hbPt.getD w 0 : ℝ) / wdScaleR)
  rw [hsub_mat]
  have hcoupl_diff (j : ℕ) (hj : j < d) :
      |h_real * dAltCoupling mEff r j - (hbPt.getD j 0 : ℝ) / wdScaleR| ≤
        ((1 / 2 : ℝ) * (bCapCeil : ℝ) + 5) / wdScaleR := by
    have hget' := rkm128k_buildHbFrom_getD mEff r hPt d 0 j hj
    set rad := 4 * (j + 1) * (mEff - j) * (r - j)
    set sq := (altIsqrt15 rad).1
    have hget_sq : hbPt.getD j 0 = (((hPt * sq) / wdScale : ℕ) : ℤ) := by
      simpa [hbPt, rad, sq] using hget'
    have hc_nn : 0 ≤ dAltCoupling mEff r j := by unfold dAltCoupling; positivity
    have hc_le := hcoupl_cap j hj
    have htight_j : (altIsqrt15 rad).2 ≤ sq + 1 := by
      simpa [rad, sq] using rkm128k_checkHbTight_sound mEff r d 0 htight j hj
    have hsq_s := altIsqrt15_sound rad
    set qProd := (hPt * sq) / wdScale
    have hloR : (qProd : ℝ) * wdScaleR ≤ (hPt : ℝ) * (sq : ℝ) := by
      unfold wdScaleR
      exact_mod_cast Nat.div_mul_le_self (hPt * sq) wdScale
    have hhiR : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd + 1 : ℕ) : ℝ) * wdScaleR := by
      have hnat := (Nat.lt_mul_div_succ (hPt * sq)
        (by unfold wdScale; positivity : 0 < wdScale)).trans_eq (Nat.mul_comm _ _)
      unfold wdScaleR
      exact_mod_cast hnat.le
    rw [hget_sq, Int.cast_natCast]
    have hsq_diff : |dAltCoupling mEff r j - (sq : ℝ) / wdScaleR| ≤ 1 / wdScaleR := by
      have hhi : dAltCoupling mEff r j ≤ ((sq + 1 : ℕ) : ℝ) / wdScaleR :=
        hsq_s.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast htight_j) hB_pos.le)
      have hlo : (sq : ℝ) / wdScaleR ≤ dAltCoupling mEff r j := hsq_s.1
      rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      have h1 : ((sq + 1 : ℕ) : ℝ) / wdScaleR - (sq : ℝ) / wdScaleR = 1 / wdScaleR := by
        push_cast
        ring
      linarith
    have hdiv_err :
        |((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR| ≤
          1 / wdScaleR := by
      have hdiff_nn : 0 ≤ ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) -
          (qProd : ℝ) / wdScaleR := by
        rw [div_mul_div_comm, sub_nonneg, div_le_div_iff₀ hB_pos (mul_pos hB_pos hB_pos),
          show (qProd : ℝ) * (wdScaleR * wdScaleR) = ((qProd : ℝ) * wdScaleR) * wdScaleR by ring]
        exact mul_le_mul_of_nonneg_right hloR hB_pos.le
      rw [abs_of_nonneg hdiff_nn]
      have h1 : (hPt : ℝ) * (sq : ℝ) ≤ ((qProd : ℝ) + 1) * wdScaleR := by
        simpa only [Nat.cast_add, Nat.cast_one] using hhiR
      calc ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR
          = ((hPt : ℝ) * (sq : ℝ)) / (wdScaleR * wdScaleR) - (qProd : ℝ) / wdScaleR := by
              rw [div_mul_div_comm]
        _ ≤ (((qProd : ℝ) + 1) * wdScaleR) / (wdScaleR * wdScaleR) - (qProd : ℝ) / wdScaleR :=
              sub_le_sub_right (div_le_div_of_nonneg_right h1 (mul_nonneg hB_pos.le hB_pos.le)) _
        _ = 1 / wdScaleR := by field_simp [hB_pos.ne']; ring
    set e1 : ℝ := (h_real - (hPt : ℝ) / wdScaleR) * dAltCoupling mEff r j
    set e2 : ℝ := ((hPt : ℝ) / wdScaleR) * (dAltCoupling mEff r j - (sq : ℝ) / wdScaleR)
    set e3 : ℝ := ((hPt : ℝ) / wdScaleR) * ((sq : ℝ) / wdScaleR) - (qProd : ℝ) / wdScaleR
    have hsp3 : h_real * dAltCoupling mEff r j - (qProd : ℝ) / wdScaleR = e1 + e2 + e3 := by
      dsimp [e1, e2, e3]
      ring
    rw [hsp3]
    have ht1 : |e1| ≤ (1 / wdScaleR) * ((1 / 2) * (bCapCeil : ℝ)) := by
      dsimp [e1]
      rw [abs_mul, abs_of_nonneg hc_nn]
      exact mul_le_mul hh_diff hc_le hc_nn (div_nonneg (by norm_num) hB_pos.le)
    have ht2 : |e2| ≤ 4 * (1 / wdScaleR) := by
      dsimp [e2]
      rw [abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hB_pos.le)]
      exact mul_le_mul hhPt_le4 hsq_diff (abs_nonneg _) (by norm_num)
    have habs12 := abs_add_le e1 e2
    have habs123 := abs_add_le (e1 + e2) e3
    have hgoal : (1 / wdScaleR) * ((1 / 2) * (bCapCeil : ℝ)) + 4 * (1 / wdScaleR) +
        1 / wdScaleR = ((1 / 2 : ℝ) * (bCapCeil : ℝ) + 5) / wdScaleR := by ring
    linarith [habs12, habs123, ht1, ht2, hdiv_err, hgoal]
  refine (vecNorm_tridiagSkewMat_mulVec_le (div_nonneg (by positivity) hB_pos.le)
    hcoupl_diff u).trans (le_of_eq (by ring))

private theorem rkm128k_dAltGen_op {mEff r : ℕ} (hm_hi : mEff ≤ 8192) (hr_hi : r ≤ 1024)
    (v : Fin (orbDim mEff r) → ℝ) :
    vecNorm (dAltGenMat mEff r *ᵥ v) ≤ (2 : ℝ) ^ 19 * vecNorm v := by
  have hbd : dAltGenNormBound mEff r ≤ (2 : ℝ) ^ 19 := by
    unfold dAltGenNormBound
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul]
    have hmax : max mEff r ≤ 8192 := max_le hm_hi (hr_hi.trans (by omega))
    have hnat : 4 * (min mEff r + 1) ^ 2 * max mEff r ≤ 4 * 1025 ^ 2 * 8192 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left (by have := Nat.min_le_right mEff r; omega) 2)) hmax
    exact (by exact_mod_cast hnat : _ ≤ ((4 * 1025 ^ 2 * 8192 : ℕ) : ℝ)).trans (by norm_num)
  exact (vecNorm_dAltGenMat_mulVec_le mEff r v).trans
    (mul_le_mul_of_nonneg_right hbd (vecNorm_nonneg v))

private theorem rkm128kSubstep_sound {n mEff r tau9 nSub degP accPad : ℕ}
    {vec v1 : List ℤ} {p1 : ℕ}
    (hn : 80000 ≤ n) (hm1 : 1 ≤ mEff) (hm_hi : mEff ≤ 8192)
    (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024)
    (htau1 : 1 ≤ tau9) (htau_hi : tau9 ≤ 4000000000)
    (hnsub1 : 1 ≤ nSub) (hnsub_hi : nSub ≤ 16384)
    (hdeg1 : 1 ≤ degP) (hdeg_hi : degP ≤ 64)
    (htight : altCheckHbTight mEff r 0 (min mEff r) = true)
    (hvec_len : vec.length ≤ min mEff r + 1)
    (hstep : rkm128kSubstep (min mEff r)
      (rkm128kCeilDiv15 (2 * altMaxBHiFrom mEff r 0 (min mEff r)))
      degP (altBuildHbFrom mEff r ((tau9 * 1000000) / nSub) 0 (min mEff r)) vec accPad = (v1, p1))
    (hp1_ne : p1 ≠ 0) :
    let d := min mEff r
    let q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
    let η := 1 / √(2 ^ n : ℝ)
    v1.length ≤ d + 1 ∧ accPad ≤ p1 ∧
      vecNorm (((taylor16Mat η (dAltGenMat mEff r)) ^ q) *ᵥ rkmListToOrbVec d vec -
        rkmListToOrbVec d v1) ≤ ((p1 : ℝ) - (accPad : ℝ)) / wdScaleR := by
  intro d q η
  set bCapCeil := rkm128kCeilDiv15 (2 * altMaxBHiFrom mEff r 0 d)
  set hPt := (tau9 * 1000000) / nSub
  set hbPt := altBuildHbFrom mEff r hPt 0 d
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB_pos : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  have hd_hi : d ≤ 1024 := (Nat.min_le_right _ _).trans hr_hi
  have hhb_len : hbPt.length ≤ d := (rkm128k_buildHbFrom_length mEff r hPt d 0).le
  change rkm128kSubstep d bCapCeil degP hbPt vec accPad = (v1, p1) at hstep
  unfold rkm128kSubstep at hstep
  cases hpad0 : Nat.beq accPad 0 with
  | true =>
    rw [hpad0, rkm128k_cond_true] at hstep
    exact absurd (Prod.mk.inj hstep).2.symm hp1_ne
  | false =>
    rw [hpad0, rkm128k_cond_false, rkmb_forceNat_eq] at hstep
    have htl_spec := rkm128k_taylorLoop_spec (vec := vec) hd_hi hhb_len degP 0 vec
      (rkm128kVecL1 vec) hvec_len
    dsimp only at htl_spec
    rcases htl : rkm128kTaylorLoop (Nat.add d 1) hbPt degP 1 vec vec (rkm128kVecL1 vec) with
      ⟨zLast, accEnd, sumZAll⟩
    rw [show rkm128kStageSeq d hbPt vec 0 = vec from rfl, htl] at htl_spec
    rw [htl] at hstep
    dsimp only at hstep
    cases hsum_ov : primNatBlt (Nat.mul 1000 wdScale) sumZAll with
    | true =>
      rw [hsum_ov, rkm128k_cond_true] at hstep
      exact absurd (Prod.mk.inj hstep).2.symm hp1_ne
    | false =>
      rw [hsum_ov, rkm128k_cond_false] at hstep
      set remTail := rkm128kCeilDiv15 (rkm128kMatVecL1Loop (Int.ofNat 0) hbPt zLast)
      set discPad := rkm128kCeilDiv15 (Nat.mul (Nat.add bCapCeil 10) sumZAll)
      set roundPad := Nat.mul 33 degP
      set stepPad := Nat.add remTail (Nat.add discPad (Nat.add roundPad 1))
      set nextPad := Nat.add accPad stepPad
      cases hnp_ov : primNatBlt 100000000000000 nextPad with
      | true =>
        rw [hnp_ov, rkm128k_cond_true] at hstep
        exact absurd (Prod.mk.inj hstep).2.symm hp1_ne
      | false =>
        rw [hnp_ov, rkm128k_cond_false] at hstep
        rcases Prod.mk.inj hstep with ⟨hv1_eq, hp1_eq⟩
        subst hv1_eq
        subst hp1_eq
        obtain ⟨hzLast_eq, hacc_len, hacc_orb, hsum_eq⟩ := htl_spec
        rw [Nat.zero_add] at hzLast_eq
        have hsum_le_nat : sumZAll ≤ 1000 * wdScale := rkm128k_blt_false.mp hsum_ov
        have hsum_le1000 : (sumZAll : ℝ) / wdScaleR ≤ 1000 := by
          rw [div_le_iff₀ hB_pos]
          unfold wdScaleR
          exact_mod_cast hsum_le_nat
        refine ⟨hacc_len, Nat.le_add_right accPad stepPad, ?_⟩
        have hsub_pad : ((nextPad : ℝ) - (accPad : ℝ)) = (stepPad : ℝ) := by
          change ((accPad + stepPad : ℕ) : ℝ) - (accPad : ℝ) = _
          push_cast
          ring
        rw [hsub_pad]
        let uSeq : ℕ → Fin (d + 1) → ℝ := fun k ↦ rkmListToOrbVec d (rkm128kStageSeq d hbPt vec k)
        have huSeq_sum : (∑ k ∈ Finset.range (degP + 1), vecNorm (uSeq k)) ≤
            (sumZAll : ℝ) / wdScaleR := by
          have h1 : (∑ k ∈ Finset.range (degP + 1), vecNorm (uSeq k)) ≤
              ∑ k ∈ Finset.range (degP + 1),
                (rkm128kVecL1 (rkm128kStageSeq d hbPt vec k) : ℝ) / wdScaleR :=
            Finset.sum_le_sum fun k _ ↦ rkm128k_vecNorm_le_vecL1 d _
          rw [← Finset.sum_div,
            rkm128k_sum_range_succ_shift (fun k ↦ (rkm128kVecL1 (rkm128kStageSeq d hbPt vec k) : ℝ))
              degP] at h1
          have hsum_eq' : (sumZAll : ℝ) = (rkm128kVecL1 (rkm128kStageSeq d hbPt vec 0) : ℝ) +
              ∑ j ∈ Finset.range degP,
                (rkm128kVecL1 (rkm128kStageSeq d hbPt vec (j + 1)) : ℝ) := by
            rw [hsum_eq]
            congr 1
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [show 0 + 1 + j = j + 1 by omega]
          rwa [← hsum_eq'] at h1
        have hacc_uSeq : rkmListToOrbVec d accEnd = ∑ k ∈ Finset.range (degP + 1), uSeq k := by
          rw [hacc_orb, rkm128k_sum_range_succ_shift uSeq degP]
          refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ ↦ ?_)
          exact congrArg (fun t ↦ rkmListToOrbVec d (rkm128kStageSeq d hbPt vec t)) (by omega)
        have hq_bds := rkm128k_q_bounds hn htau1 htau_hi hnsub1 hnsub_hi
        have hq150 : (2 : ℝ) ^ 150 ≤ (q : ℝ) := hq_bds.1
        have hq_pos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (by positivity) hq150
        have hq_hi4 : (q : ℝ) ≤ 4 * √(2 ^ n : ℝ) := hq_bds.2.1
        have hN_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
        have hsN_ge : (2 : ℝ) ^ 201 ≤ √(2 ^ n : ℝ) :=
          Real.le_sqrt_of_sq_le (by
            rw [← pow_mul]
            exact pow_le_pow_right₀ (by norm_num) (by omega : 402 ≤ n))
        have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge
        set G := dAltGenMat mEff r
        set H := rkmPtGenMat d hbPt
        set A := taylor16Mat η G
        have hη_nn : 0 ≤ η := by dsimp [η]; positivity
        have hηB_le1 : η * (2 : ℝ) ^ 19 ≤ 1 := by
          dsimp only [η]
          rw [one_div_mul_eq_div, div_le_one hsN_pos]
          exact (by norm_num : (2 : ℝ) ^ 19 ≤ (2 : ℝ) ^ 201).trans hsN_ge
        have hA_contr : ∀ x, vecNorm (A *ᵥ x) ≤ vecNorm x := fun x ↦
          vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose mEff r) hη_nn (by positivity)
            (rkm128k_dAltGen_op hm_hi hr_hi) (hηB_le1.trans (by norm_num)) x
        have hA_nl : ∀ x, vecNorm ((A - (1 + η • G)) *ᵥ x) ≤
            ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * vecNorm x := by
          intro x
          have hX_op (u : Fin (d + 1) → ℝ) :
              vecNorm ((η • G) *ᵥ u) ≤ (η * (2 : ℝ) ^ 19) * vecNorm u := by
            rw [Matrix.smul_mulVec, vecNorm_smul, abs_of_nonneg hη_nn]
            exact (mul_le_mul_of_nonneg_left (rkm128k_dAltGen_op hm_hi hr_hi u) hη_nn).trans_eq
              (by ring)
          have hc_sq : (η * (2 : ℝ) ^ 19) ^ 2 = (2 : ℝ) ^ 38 / (2 ^ n : ℝ) := by
            dsimp only [η]
            rw [one_div_mul_eq_div, div_pow, Real.sq_sqrt hN_pos.le, ← pow_mul]
          simpa only [hc_sq] using
            rkm128k_taylor16_sub_linear_le (by positivity) hηB_le1 hX_op x
        let θ : ℕ → ℝ := fun s ↦ (s : ℝ) / (q : ℝ)
        set δ : ℝ := 1 / (q : ℝ)
        have hδ_pos : 0 < δ := by dsimp [δ]; positivity
        let γ : ℕ → Fin (d + 1) → ℝ := fun s ↦
          ∑ k ∈ Finset.range (degP + 1), ((θ s) ^ k) • uSeq k
        have hγ0 : γ 0 = rkmListToOrbVec d vec := by
          dsimp only [γ, θ]
          rw [Nat.cast_zero, rkm128k_sum_range_succ_shift]
          have hz : (∑ j ∈ Finset.range degP, (((0 : ℝ) / (q : ℝ)) ^ (j + 1)) • uSeq (j + 1)) =
              0 := by
            refine Finset.sum_eq_zero fun j _ ↦ ?_
            simp
          rw [hz, add_zero, pow_zero, one_smul]
          rfl
        have hγq : γ q = rkmListToOrbVec d accEnd := by
          rw [hacc_uSeq]
          dsimp only [γ, θ]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [div_self hq_pos.ne', one_pow, one_smul]
        have hγ_norm (s : ℕ) (hs : s < q) : vecNorm (γ s) ≤ (sumZAll : ℝ) / wdScaleR := by
          have hθ0 : 0 ≤ θ s := div_nonneg (Nat.cast_nonneg s) hq_pos.le
          have hθ1 : θ s ≤ 1 := (div_le_one hq_pos).mpr (by exact_mod_cast hs.le)
          refine (rkm128k_vecNorm_sum_le _ (degP + 1)).trans (le_trans ?_ huSeq_sum)
          refine Finset.sum_le_sum fun k _ ↦ ?_
          rw [vecNorm_smul, abs_of_nonneg (pow_nonneg hθ0 k)]
          exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hθ0 hθ1) (vecNorm_nonneg _)).trans_eq
            (one_mul _)
        set h_real : ℝ := (q : ℝ) * η
        have hG_diff := rkm128k_gen_diff_op hn hm1 hm_hi hr2 hr_hi htau1 htau_hi
          hnsub1 hnsub_hi htight
        dsimp only at hG_diff
        have htail_bd : vecNorm (H *ᵥ uSeq degP) ≤ (remTail : ℝ) / wdScaleR := by
          dsimp only [uSeq, H, remTail]
          rw [← hzLast_eq]
          exact rkm128k_ptGenMat_mulVec_le hhb_len zLast
        have hstep_per_s (s : ℕ) (hs : s < q) :
            vecNorm (A *ᵥ γ s - γ (s + 1)) ≤
              ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000 +
              δ * ((((bCapCeil : ℝ) + 10) / wdScaleR) * ((sumZAll : ℝ) / wdScaleR)) +
              (∑ j ∈ Finset.range degP,
                ((θ (s + 1)) ^ (j + 1) - (θ s) ^ (j + 1)) * (33 / wdScaleR)) +
              δ * ((remTail : ℝ) / wdScaleR) +
              4096000 * δ ^ 2 := by
          have hθ0 : 0 ≤ θ s := div_nonneg (Nat.cast_nonneg s) hq_pos.le
          have hθ_succ : θ (s + 1) = θ s + δ := by
            dsimp only [θ, δ]
            push_cast
            ring
          have hθ1 : θ s + δ ≤ 1 := by
            rw [← hθ_succ]
            exact (div_le_one hq_pos).mpr (by exact_mod_cast hs)
          have hθ_le1 : θ s ≤ 1 := by linarith
          set eNL := (A - (1 + η • G)) *ᵥ γ s
          set eQuant := δ • ((h_real • G - H) *ᵥ γ s)
          set eMain := ∑ j ∈ Finset.range degP,
            (δ * (θ s) ^ j) • (H *ᵥ uSeq j - ((j + 1 : ℕ) : ℝ) • uSeq (j + 1))
          set eTail := (δ * (θ s) ^ degP) • (H *ᵥ uSeq degP)
          set eCurve := ∑ j ∈ Finset.range degP,
            ((θ s + δ) ^ (j + 1) - (θ s) ^ (j + 1) - ((j + 1 : ℕ) : ℝ) * δ * (θ s) ^ j) •
              uSeq (j + 1)
          have hdecomp : A *ᵥ γ s - γ (s + 1) =
              ((eNL + eQuant) + (eMain + eTail)) + (-eCurve) := by
            have hη_eq : η = δ * h_real := by
              dsimp only [δ, h_real]
              field_simp [hq_pos.ne']
            have hHγ : H *ᵥ γ s = (∑ j ∈ Finset.range degP, ((θ s) ^ j) • (H *ᵥ uSeq j)) +
                ((θ s) ^ degP) • (H *ᵥ uSeq degP) := by
              dsimp only [γ]
              rw [rkm128k_mulVec_sum_smul, Finset.sum_range_succ]
            have hγ_s : γ s = uSeq 0 +
                ∑ j ∈ Finset.range degP, ((θ s) ^ (j + 1)) • uSeq (j + 1) := by
              dsimp only [γ]
              rw [rkm128k_sum_range_succ_shift, pow_zero, one_smul]
            have hγ_s1 : γ (s + 1) = uSeq 0 +
                ∑ j ∈ Finset.range degP, ((θ s + δ) ^ (j + 1)) • uSeq (j + 1) := by
              dsimp only [γ]
              rw [rkm128k_sum_range_succ_shift, pow_zero, one_smul, hθ_succ]
            ext i
            dsimp only [eNL, eQuant, eMain, eTail]
            simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
              Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
            have hHγ_i := congrFun hHγ i
            have hγ_s_i := congrFun hγ_s i
            have hγ_s1_i := congrFun hγ_s1 i
            simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
              smul_eq_mul] at hHγ_i hγ_s_i hγ_s1_i
            have heMain_i : (∑ j ∈ Finset.range degP,
                (δ * (θ s) ^ j) • (H *ᵥ uSeq j - ((j + 1 : ℕ) : ℝ) • uSeq (j + 1))) i =
                ∑ j ∈ Finset.range degP,
                  (δ * (θ s) ^ j) * ((H *ᵥ uSeq j) i - ((j + 1 : ℕ) : ℝ) * uSeq (j + 1) i) := by
              simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
            have heCurve_i : eCurve i = ∑ j ∈ Finset.range degP,
                ((θ s + δ) ^ (j + 1) - (θ s) ^ (j + 1) - ((j + 1 : ℕ) : ℝ) * δ * (θ s) ^ j) *
                  uSeq (j + 1) i := by
              dsimp only [eCurve]
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            rw [heMain_i, heCurve_i, hHγ_i, hγ_s_i, hγ_s1_i, hη_eq]
            have hsum_comb :
                (∑ j ∈ Finset.range degP, ((θ s) ^ (j + 1)) * uSeq (j + 1) i) +
                δ * (∑ j ∈ Finset.range degP, ((θ s) ^ j) * (H *ᵥ uSeq j) i) -
                (∑ j ∈ Finset.range degP, ((θ s + δ) ^ (j + 1)) * uSeq (j + 1) i) =
                (∑ j ∈ Finset.range degP,
                  (δ * (θ s) ^ j) * ((H *ᵥ uSeq j) i - ((j + 1 : ℕ) : ℝ) * uSeq (j + 1) i)) -
                (∑ j ∈ Finset.range degP,
                  ((θ s + δ) ^ (j + 1) - (θ s) ^ (j + 1) - ((j + 1 : ℕ) : ℝ) * δ * (θ s) ^ j) *
                    uSeq (j + 1) i) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
                ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              ring
            linarith
          have hb_nl : vecNorm eNL ≤ ((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000 :=
            (hA_nl (γ s)).trans (mul_le_mul_of_nonneg_left
              ((hγ_norm s hs).trans hsum_le1000) (by positivity))
          have hb_quant : vecNorm eQuant ≤
              δ * ((((bCapCeil : ℝ) + 10) / wdScaleR) * ((sumZAll : ℝ) / wdScaleR)) := by
            dsimp only [eQuant]
            rw [vecNorm_smul, abs_of_pos hδ_pos]
            exact mul_le_mul_of_nonneg_left
              ((hG_diff (γ s)).trans (mul_le_mul_of_nonneg_left (hγ_norm s hs) (by positivity)))
              hδ_pos.le
          have hb_main : vecNorm eMain ≤ ∑ j ∈ Finset.range degP,
              ((θ (s + 1)) ^ (j + 1) - (θ s) ^ (j + 1)) * (33 / wdScaleR) := by
            refine (rkm128k_vecNorm_sum_le _ degP).trans (Finset.sum_le_sum fun j _ ↦ ?_)
            rw [vecNorm_smul, abs_of_nonneg (mul_nonneg hδ_pos.le (pow_nonneg hθ0 j)), hθ_succ]
            have hst := (rkm128k_stage_zero_approx (by omega : 1 ≤ j + 1) hd_hi hhb_len
              (cur := rkm128kStageSeq d hbPt vec j)).2
            have hder := rkm128k_pow_sub_ge_deriv hθ0 hδ_pos.le j
            calc (δ * (θ s) ^ j) * vecNorm (H *ᵥ uSeq j - ((j + 1 : ℕ) : ℝ) • uSeq (j + 1))
                ≤ (δ * (θ s) ^ j) * ((((j + 1 : ℕ) : ℝ) * 33) / wdScaleR) :=
                  mul_le_mul_of_nonneg_left hst (mul_nonneg hδ_pos.le (pow_nonneg hθ0 j))
              _ = (((j + 1 : ℕ) : ℝ) * δ * (θ s) ^ j) * (33 / wdScaleR) := by ring
              _ ≤ ((θ s + δ) ^ (j + 1) - (θ s) ^ (j + 1)) * (33 / wdScaleR) :=
                  mul_le_mul_of_nonneg_right hder (by positivity)
          have hb_tail : vecNorm eTail ≤ δ * ((remTail : ℝ) / wdScaleR) := by
            dsimp only [eTail]
            rw [vecNorm_smul, abs_of_nonneg (mul_nonneg hδ_pos.le (pow_nonneg hθ0 degP))]
            have hp_le : δ * (θ s) ^ degP ≤ δ :=
              (mul_le_mul_of_nonneg_left (pow_le_one₀ hθ0 hθ_le1) hδ_pos.le).trans_eq (mul_one _)
            exact (mul_le_mul hp_le htail_bd (vecNorm_nonneg _) hδ_pos.le)
          have hb_curve : vecNorm (-eCurve) ≤ 4096000 * δ ^ 2 := by
            rw [vecNorm_neg]
            have h1 : vecNorm eCurve ≤
                ∑ j ∈ Finset.range degP, (4096 * δ ^ 2) * vecNorm (uSeq (j + 1)) := by
              refine (rkm128k_vecNorm_sum_le _ degP).trans (Finset.sum_le_sum fun j hj ↦ ?_)
              have hj_lt : j < degP := Finset.mem_range.mp hj
              obtain ⟨hc0, hc1⟩ := rkm128k_curve_rem_bounds hθ0 hδ_pos.le hθ1 j
              rw [vecNorm_smul, abs_of_nonneg hc0]
              have hj64 : ((j + 1 : ℕ) : ℝ) ^ 2 ≤ 4096 := by
                have hle : j + 1 ≤ 64 := by omega
                have hR : ((j + 1 : ℕ) : ℝ) ≤ 64 := by exact_mod_cast hle
                nlinarith
              have hc4096 : (θ s + δ) ^ (j + 1) - (θ s) ^ (j + 1) -
                  ((j + 1 : ℕ) : ℝ) * δ * (θ s) ^ j ≤ 4096 * δ ^ 2 :=
                hc1.trans (mul_le_mul_of_nonneg_right hj64 (sq_nonneg δ))
              exact mul_le_mul_of_nonneg_right hc4096 (vecNorm_nonneg _)
            rw [← Finset.mul_sum] at h1
            have hsub_u : (∑ j ∈ Finset.range degP, vecNorm (uSeq (j + 1))) ≤ 1000 := by
              have hshift := rkm128k_sum_range_succ_shift (fun k ↦ vecNorm (uSeq k)) degP
              have h0_nn : 0 ≤ vecNorm (uSeq 0) := vecNorm_nonneg _
              linarith [huSeq_sum, hsum_le1000, hshift, h0_nn]
            exact h1.trans ((mul_le_mul_of_nonneg_left hsub_u (by positivity)).trans_eq (by ring))
          rw [hdecomp]
          have ht1 := vecNorm_add_le ((eNL + eQuant) + (eMain + eTail)) (-eCurve)
          have ht2 := vecNorm_add_le (eNL + eQuant) (eMain + eTail)
          have ht3 := vecNorm_add_le eNL eQuant
          have ht4 := vecNorm_add_le eMain eTail
          linarith
        rw [← hγ0, ← hγq]
        have htel := (rkm128k_contr_curve_tel hA_contr γ q).trans
          (Finset.sum_le_sum fun s hs ↦ hstep_per_s s (Finset.mem_range.mp hs))
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul] at htel
        have hmain_tel :
            (∑ x ∈ Finset.range q, ∑ j ∈ Finset.range degP,
              ((θ (x + 1)) ^ (j + 1) - (θ x) ^ (j + 1)) * (33 / wdScaleR)) =
              (roundPad : ℝ) / wdScaleR := by
          rw [Finset.sum_comm]
          have hinner (j : ℕ) :
              (∑ x ∈ Finset.range q,
                ((θ (x + 1)) ^ (j + 1) - (θ x) ^ (j + 1)) * (33 / wdScaleR)) =
                33 / wdScaleR := by
            rw [← Finset.sum_mul, rkm128k_sum_range_sub (fun x ↦ (θ x) ^ (j + 1)) q]
            dsimp only [θ]
            rw [Nat.cast_zero, div_self hq_pos.ne', zero_div, one_pow,
              zero_pow (Nat.succ_ne_zero j), sub_zero, one_mul]
          simp only [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          dsimp only [roundPad]
          simp only [Nat.mul_eq]
          push_cast
          ring
        have hqδ : (q : ℝ) * δ = 1 := by dsimp [δ]; exact mul_one_div_cancel hq_pos.ne'
        have hnl_tot : (q : ℝ) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000) ≤ (1 / 4) / wdScaleR := by
          have hsqN : (2 ^ n : ℝ) = √(2 ^ n : ℝ) * √(2 ^ n : ℝ) :=
            (Real.mul_self_sqrt hN_pos.le).symm
          have h1 : (q : ℝ) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000) ≤
              (4 * √(2 ^ n : ℝ)) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000) :=
            mul_le_mul_of_nonneg_right hq_hi4 (by positivity)
          have h2 : (4 * √(2 ^ n : ℝ)) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000) =
              (4000 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ) := by
            have hm : ((4 * √(2 ^ n : ℝ)) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000)) *
                √(2 ^ n : ℝ) = ((4000 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ)) * √(2 ^ n : ℝ) := by
              calc ((4 * √(2 ^ n : ℝ)) * (((2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * 1000)) * √(2 ^ n : ℝ)
                  = (4000 * (2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * (√(2 ^ n : ℝ) * √(2 ^ n : ℝ)) := by ring
                _ = (4000 * (2 : ℝ) ^ 38 / (2 ^ n : ℝ)) * (2 ^ n : ℝ) := by rw [← hsqN]
                _ = 4000 * (2 : ℝ) ^ 38 := div_mul_cancel₀ _ hN_pos.ne'
                _ = ((4000 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ)) * √(2 ^ n : ℝ) :=
                    (div_mul_cancel₀ _ hsN_pos.ne').symm
            exact mul_right_cancel₀ hsN_pos.ne' hm
          have h3 : (4000 * (2 : ℝ) ^ 38) / √(2 ^ n : ℝ) ≤ (1 / 4) / wdScaleR := by
            rw [hB_eq, div_le_div_iff₀ hsN_pos (by norm_num)]
            linarith [hsN_ge,
              (by norm_num : (4000 * (2 : ℝ) ^ 38) * 1000000000000000 ≤ (1 / 4) * (2 : ℝ) ^ 201)]
          linarith
        have hquant_tot :
            (q : ℝ) * (δ * ((((bCapCeil : ℝ) + 10) / wdScaleR) * ((sumZAll : ℝ) / wdScaleR))) ≤
              (discPad : ℝ) / wdScaleR := by
          have heq :
              (q : ℝ) * (δ * ((((bCapCeil : ℝ) + 10) / wdScaleR) * ((sumZAll : ℝ) / wdScaleR))) =
                (((bCapCeil + 10) * sumZAll : ℕ) : ℝ) / wdScaleR ^ 2 := by
            rw [← mul_assoc (q : ℝ) δ, hqδ, one_mul]
            push_cast
            ring
          rw [heq]
          exact rkm128k_ceilDiv15_sq_ge ((bCapCeil + 10) * sumZAll)
        have htail_tot : (q : ℝ) * (δ * ((remTail : ℝ) / wdScaleR)) = (remTail : ℝ) / wdScaleR := by
          rw [← mul_assoc, hqδ, one_mul]
        have hcurve_tot : (q : ℝ) * (4096000 * δ ^ 2) ≤ (1 / 4) / wdScaleR := by
          have heq : (q : ℝ) * (4096000 * δ ^ 2) = 4096000 / (q : ℝ) := by
            dsimp only [δ]
            field_simp [hq_pos.ne']
          rw [heq, hB_eq, div_le_div_iff₀ hq_pos (by norm_num)]
          linarith [hq150,
            (by norm_num : (4096000 : ℝ) * 1000000000000000 ≤ (1 / 4) * (2 : ℝ) ^ 150)]
        rw [hmain_tel, htail_tot] at htel
        have hstepR : (stepPad : ℝ) = (remTail : ℝ) + (discPad : ℝ) + (roundPad : ℝ) + 1 := by
          change ((remTail + (discPad + (roundPad + 1)) : ℕ) : ℝ) = _
          push_cast
          ring
        have hbud : (1 / 4) / wdScaleR + (discPad : ℝ) / wdScaleR + (roundPad : ℝ) / wdScaleR +
            (remTail : ℝ) / wdScaleR + (1 / 4) / wdScaleR ≤ (stepPad : ℝ) / wdScaleR := by
          rw [hstepR, ← add_div, ← add_div, ← add_div, ← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hB_pos.le
        linarith [htel, hnl_tot, hquant_tot, hcurve_tot, hbud]

private theorem rkm128kSubstepLoop_zero_pad (d bCapCeil degP : ℕ) (hb : List ℤ) :
    ∀ (rem : ℕ) (v : List ℤ), (rkm128kSubstepLoop rem d bCapCeil degP hb v 0).2 = 0
  | 0, _ => rfl
  | s + 1, v => by
    unfold rkm128kSubstepLoop rkm128kSubstep
    dsimp only [Nat.beq, rkm128k_cond_true]
    rw [rkmb_forceList_eq, rkmb_forceNat_eq]
    exact rkm128kSubstepLoop_zero_pad d bCapCeil degP hb s []

private theorem rkm128kSubstepLoop_sound {n mEff r tau9 nSub degP : ℕ}
    (hn : 80000 ≤ n) (hm1 : 1 ≤ mEff) (hm_hi : mEff ≤ 8192)
    (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024)
    (htau1 : 1 ≤ tau9) (htau_hi : tau9 ≤ 4000000000)
    (hnsub1 : 1 ≤ nSub) (hnsub_hi : nSub ≤ 16384)
    (hdeg1 : 1 ≤ degP) (hdeg_hi : degP ≤ 64)
    (htight : altCheckHbTight mEff r 0 (min mEff r) = true) :
    let d := min mEff r
    let q := (tau9 * Nat.sqrt (2 ^ n)) / (nSub * 1000000000)
    let η := 1 / √(2 ^ n : ℝ)
    let bCapCeil := rkm128kCeilDiv15 (2 * altMaxBHiFrom mEff r 0 d)
    let hbPt := altBuildHbFrom mEff r ((tau9 * 1000000) / nSub) 0 d
    ∀ (rem : ℕ) (vec vOut : List ℤ) (accPad padOut : ℕ) (wIn : Fin (d + 1) → ℝ),
      vec.length ≤ d + 1 →
      rkm128kSubstepLoop rem d bCapCeil degP hbPt vec accPad = (vOut, padOut) →
      padOut ≠ 0 →
      vOut.length ≤ d + 1 ∧ accPad ≤ padOut ∧
        vecNorm (((taylor16Mat η (dAltGenMat mEff r)) ^ (rem * q)) *ᵥ wIn -
          rkmListToOrbVec d vOut) ≤
          vecNorm (wIn - rkmListToOrbVec d vec) + ((padOut : ℝ) - (accPad : ℝ)) / wdScaleR := by
  intro d q η bCapCeil hbPt rem
  have hsN_ge : (2 : ℝ) ^ 201 ≤ √(2 ^ n : ℝ) :=
    Real.le_sqrt_of_sq_le (by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega : 402 ≤ n))
  have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge
  have hηB_le1 : η * (2 : ℝ) ^ 19 ≤ 1 := by
    dsimp only [η]
    rw [one_div_mul_eq_div, div_le_one hsN_pos]
    exact (by norm_num : (2 : ℝ) ^ 19 ≤ (2 : ℝ) ^ 201).trans hsN_ge
  have hA_contr : ∀ x, vecNorm (taylor16Mat η (dAltGenMat mEff r) *ᵥ x) ≤ vecNorm x := fun x ↦
    vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose mEff r) (by dsimp [η]; positivity)
      (by positivity) (rkm128k_dAltGen_op hm_hi hr_hi) (hηB_le1.trans (by norm_num)) x
  have hAq_contr : ∀ x, vecNorm (((taylor16Mat η (dAltGenMat mEff r)) ^ q) *ᵥ x) ≤ vecNorm x :=
    fun x ↦ (vecNorm_pow_mulVec_le zero_le_one
      (fun u ↦ (hA_contr u).trans_eq (one_mul _).symm) q x).trans_eq (by simp)
  induction rem with
  | zero =>
    intro vec vOut accPad padOut wIn hvec hloop _
    unfold rkm128kSubstepLoop at hloop
    rcases Prod.mk.inj hloop with ⟨rfl, rfl⟩
    refine ⟨hvec, le_rfl, ?_⟩
    rw [Nat.zero_mul, pow_zero, Matrix.one_mulVec, sub_self, zero_div, add_zero]
  | succ s ih =>
    intro vec vOut accPad padOut wIn hvec hloop hp_ne
    unfold rkm128kSubstepLoop at hloop
    rcases h1 : rkm128kSubstep d bCapCeil degP hbPt vec accPad with ⟨v1, p1⟩
    rw [h1] at hloop
    dsimp only at hloop
    rw [rkmb_forceList_eq, rkmb_forceNat_eq] at hloop
    have hp1_ne : p1 ≠ 0 := by
      rintro rfl
      have hz := rkm128kSubstepLoop_zero_pad d bCapCeil degP hbPt s v1
      rw [hloop] at hz
      exact hp_ne hz
    obtain ⟨hv1_len, hp1_ge, hstep_err⟩ := rkm128kSubstep_sound hn hm1 hm_hi hr2 hr_hi
      htau1 htau_hi hnsub1 hnsub_hi hdeg1 hdeg_hi htight hvec h1 hp1_ne
    set Aq := (taylor16Mat η (dAltGenMat mEff r)) ^ q
    obtain ⟨hvOut_len, hpOut_ge, hih_err⟩ := ih v1 vOut p1 padOut (Aq *ᵥ wIn) hv1_len hloop hp_ne
    refine ⟨hvOut_len, hp1_ge.trans hpOut_ge, ?_⟩
    have hpow : (taylor16Mat η (dAltGenMat mEff r)) ^ ((s + 1) * q) *ᵥ wIn =
        (taylor16Mat η (dAltGenMat mEff r)) ^ (s * q) *ᵥ (Aq *ᵥ wIn) := by
      rw [Nat.succ_mul, pow_add, ← Matrix.mulVec_mulVec]
    rw [hpow]
    have hw1 : vecNorm (Aq *ᵥ wIn - rkmListToOrbVec d v1) ≤
        vecNorm (wIn - rkmListToOrbVec d vec) + ((p1 : ℝ) - (accPad : ℝ)) / wdScaleR := by
      have hsp : Aq *ᵥ wIn - rkmListToOrbVec d v1 =
          Aq *ᵥ (wIn - rkmListToOrbVec d vec) +
            (Aq *ᵥ rkmListToOrbVec d vec - rkmListToOrbVec d v1) := by
        rw [Matrix.mulVec_sub]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      rw [hsp]
      exact (vecNorm_add_le _ _).trans (add_le_add (hAq_contr _) hstep_err)
    have hpad_add : ((p1 : ℝ) - (accPad : ℝ)) / wdScaleR + ((padOut : ℝ) - (p1 : ℝ)) / wdScaleR =
        ((padOut : ℝ) - (accPad : ℝ)) / wdScaleR := by ring
    linarith [hih_err, hw1, hpad_add]

private theorem rkm128k_if_pos {α : Type*} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    @ite α p inst a b = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem rkm128k_if_neg {α : Type*} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    @ite α p inst a b = b := by
  cases inst with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

private theorem rkm128k_bounds_of_n80 {n x r : ℕ} (hn : 80000 ≤ n) (hx : x ≤ 8192)
    (hr : r ≤ 1024) :
    1 ≤ n ∧ 2 * x < 2 ^ n ∧ 2 * x ≤ 2 ^ n ∧ x + r ≤ 2 ^ n := by
  have h15 : 15 ≤ n := by omega
  have hp : 2 ^ 15 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h15
  have h2x : 2 * x < 2 ^ n :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 hx) (lt_of_lt_of_le (by norm_num : 2 * 8192 < 2 ^ 15) hp)
  exact ⟨by omega, h2x, h2x.le,
    (Nat.add_le_add hx hr).trans ((by norm_num : 8192 + 1024 ≤ 2 ^ 15).trans hp)⟩

private theorem rkm128k_getD_eq_zero :
    ∀ (xs : List ℤ) (k : ℕ), xs.length ≤ k → xs.getD k 0 = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | _ :: xs, k + 1, h => rkm128k_getD_eq_zero xs k (by simpa using h)

private theorem rkm128k_orbEmbedGen_sub (N M : ℕ) (R : Finset (Fin N))
    (x y : Fin (orbDim M R.card) → ℝ) :
    orbEmbedGen N M R (x - y) = orbEmbedGen N M R x - orbEmbedGen N M R y := by
  funext E
  simp only [orbEmbedGen, Pi.sub_apply, sub_div]

private theorem rkm128k_zeroPadOrbVec_sub (M₁ M₂ r : ℕ) (x y : Fin (orbDim M₁ r) → ℝ) :
    zeroPadOrbVec M₁ M₂ r (x - y) = zeroPadOrbVec M₁ M₂ r x - zeroPadOrbVec M₁ M₂ r y := by
  funext u
  by_cases hu : u.1 < orbDim M₁ r <;> simp [zeroPadOrbVec, Pi.sub_apply, hu]

private theorem rkm128k_zeroPadOrbVec_listToOrbVec {M₁ M₂ r : ℕ} {vs : List ℤ}
    (_h12 : M₁ ≤ M₂) (hvs : vs.length ≤ min M₁ r + 1) :
    zeroPadOrbVec M₁ M₂ r (rkmListToOrbVec (min M₁ r) vs) =
      rkmListToOrbVec (min M₂ r) vs := by
  funext u
  unfold zeroPadOrbVec rkmListToOrbVec
  by_cases hu : u.1 < orbDim M₁ r
  · rw [dite_eq_left hu]
  · rw [dite_eq_right hu]
    have hge : vs.length ≤ u.1 := by unfold orbDim at hu; omega
    rw [rkm128k_getD_eq_zero vs u.1 hge]
    simp

private def rkm128kApplyKickIdxsOrb (d : ℕ) : List ℕ → (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ)
  | [], x => x
  | j0 :: rest, x =>
      rkm128kApplyKickIdxsOrb d rest (fun w ↦ (if w.1 ≤ j0 then (-1 : ℝ) else 1) * x w)

private theorem rkm128k_symPrefixKickVec_orbEmbedGen (N M : ℕ) (R : Finset (Fin N)) (j0 : ℕ)
    (x : Fin (orbDim M R.card) → ℝ) :
    symPrefixKickVec R j0 (orbEmbedGen N M R x) =
      orbEmbedGen N M R (fun w ↦ (if w.1 ≤ j0 then (-1 : ℝ) else 1) * x w) := by
  funext E
  dsimp only [symPrefixKickVec, orbEmbedGen]
  split_ifs <;> ring

private theorem rkm128k_evalMuxSymOps_kicks_orbEmbedGen (N M : ℕ) (R : Finset (Fin N)) :
    ∀ (ks : List ℕ) (x : Fin (orbDim M R.card) → ℝ),
      evalMuxSymOps R (ks.map MuxSymOp.prefixKick) (orbEmbedGen N M R x) =
        orbEmbedGen N M R (rkm128kApplyKickIdxsOrb (min M R.card) ks x)
  | [], _ => rfl
  | j0 :: rest, x => by
    simp only [List.map_cons, evalMuxSymOps, rkm128k_symPrefixKickVec_orbEmbedGen]
    exact rkm128k_evalMuxSymOps_kicks_orbEmbedGen N M R rest _

private theorem rkm128k_maskKicksDown_mem_le (mask : List Bool) :
    ∀ (k : ℕ) (flip : Bool) (j : ℕ), j ∈ rkmMaskKicksDown mask k flip → j ≤ k
  | 0, flip, j, hj => by
    unfold rkmMaskKicksDown at hj
    split_ifs at hj <;> simp at hj
    omega
  | k + 1, flip, j, hj => by
    unfold rkmMaskKicksDown at hj
    split_ifs at hj
    · simp only [List.mem_cons] at hj
      rcases hj with rfl | hmem
      · exact le_rfl
      · exact (rkm128k_maskKicksDown_mem_le mask k (Bool.not flip) j hmem).trans (Nat.le_succ k)
    · exact (rkm128k_maskKicksDown_mem_le mask k flip j hj).trans (Nat.le_succ k)

private theorem rkm128k_applyKickIdxsOrb_gt (d : ℕ) :
    ∀ (ks : List ℕ) (x : Fin (d + 1) → ℝ) (w : Fin (d + 1)),
      (∀ j ∈ ks, j < w.1) → rkm128kApplyKickIdxsOrb d ks x w = x w
  | [], _, _, _ => rfl
  | j0 :: rest, x, w, hgt => by
    unfold rkm128kApplyKickIdxsOrb
    rw [rkm128k_applyKickIdxsOrb_gt d rest _ w (fun j hj ↦ hgt j (List.mem_cons_of_mem _ hj))]
    have hnle : ¬ w.1 ≤ j0 := by have := hgt j0 List.mem_cons_self; omega
    simp [hnle]

private theorem rkm128k_applyKickIdxsOrb_maskKicksDown (d : ℕ) (mask : List Bool) :
    ∀ (k : ℕ) (flip : Bool) (x0 x : Fin (d + 1) → ℝ),
      (∀ w : Fin (d + 1), w.1 ≤ k → x w = (if flip then (-1 : ℝ) else 1) * x0 w) →
      ∀ w : Fin (d + 1), w.1 ≤ k →
        rkm128kApplyKickIdxsOrb d (rkmMaskKicksDown mask k flip) x w =
          (if mask.getD w.1 false then (-1 : ℝ) else 1) * x0 w
  | 0, flip, x0, x, hx, w, hw => by
    have hw0 : w.1 = 0 := by omega
    have hxw := hx w hw
    unfold rkmMaskKicksDown
    rw [hw0]
    generalize mask.getD 0 false = b0
    cases flip <;> cases b0
    · rw [rkm128k_if_neg (show rkmBoolXor false false ≠ true by simp [rkmBoolXor])]
      exact hxw
    · rw [rkm128k_if_pos (by rfl : rkmBoolXor false true = true), rkm128kApplyKickIdxsOrb,
        rkm128kApplyKickIdxsOrb, rkm128k_if_pos hw, hxw, rkm128k_if_neg Bool.false_ne_true,
        rkm128k_if_pos (@rfl Bool true)]
      ring
    · rw [rkm128k_if_pos (by rfl : rkmBoolXor true false = true), rkm128kApplyKickIdxsOrb,
        rkm128kApplyKickIdxsOrb, rkm128k_if_pos hw, hxw, rkm128k_if_pos (@rfl Bool true),
        rkm128k_if_neg Bool.false_ne_true]
      ring
    · rw [rkm128k_if_neg (show rkmBoolXor true true ≠ true by simp [rkmBoolXor])]
      exact hxw
  | k + 1, flip, x0, x, hx, w, hw => by
    unfold rkmMaskKicksDown
    by_cases hwk : w.1 ≤ k
    · by_cases hxor : rkmBoolXor flip (mask.getD (k + 1) false) = true
      · rw [rkm128k_if_pos hxor, rkm128kApplyKickIdxsOrb]
        exact rkm128k_applyKickIdxsOrb_maskKicksDown d mask k (Bool.not flip) x0 _
          (fun u hu ↦ by
            have hu1 : u.1 ≤ k + 1 := hu.trans (Nat.le_succ k)
            rw [rkm128k_if_pos hu1, hx u hu1]
            cases flip
            · rw [rkm128k_if_neg Bool.false_ne_true,
                rkm128k_if_pos (by rfl : Bool.not false = true)]
              ring
            · rw [rkm128k_if_pos (@rfl Bool true),
                rkm128k_if_neg (show Bool.not true ≠ true by simp)]
              ring) w hwk
      · rw [rkm128k_if_neg hxor]
        exact rkm128k_applyKickIdxsOrb_maskKicksDown d mask k flip x0 x
          (fun u hu ↦ hx u (hu.trans (Nat.le_succ k))) w hwk
    · have hweq : w.1 = k + 1 := by omega
      have hxw := hx w hw
      have hgt_sub (fl' : Bool) : ∀ j ∈ rkmMaskKicksDown mask k fl', j < w.1 := fun j hj ↦ by
        have := rkm128k_maskKicksDown_mem_le mask k fl' j hj
        omega
      rw [hweq]
      generalize mask.getD (k + 1) false = bk1
      cases flip <;> cases bk1
      · rw [rkm128k_if_neg (show rkmBoolXor false false ≠ true by simp [rkmBoolXor]),
          rkm128k_applyKickIdxsOrb_gt d _ _ w (hgt_sub false)]
        exact hxw
      · rw [rkm128k_if_pos (by rfl : rkmBoolXor false true = true), rkm128kApplyKickIdxsOrb,
          rkm128k_applyKickIdxsOrb_gt d _ _ w (hgt_sub (Bool.not false)), rkm128k_if_pos hw, hxw,
          rkm128k_if_neg Bool.false_ne_true, rkm128k_if_pos (@rfl Bool true)]
        ring
      · rw [rkm128k_if_pos (by rfl : rkmBoolXor true false = true), rkm128kApplyKickIdxsOrb,
          rkm128k_applyKickIdxsOrb_gt d _ _ w (hgt_sub (Bool.not true)), rkm128k_if_pos hw, hxw,
          rkm128k_if_pos (@rfl Bool true), rkm128k_if_neg Bool.false_ne_true]
        ring
      · rw [rkm128k_if_neg (show rkmBoolXor true true ≠ true by simp [rkmBoolXor]),
          rkm128k_applyKickIdxsOrb_gt d _ _ w (hgt_sub true)]
        exact hxw

private theorem rkm128k_evalMuxSymOps_walk_cons {N M : ℕ} (R : Finset (Fin N)) (K : ℕ)
    (D : SymOrthogonal N M) (rest : List (MuxSymOp N M)) (v : SymSubset N M → ℝ) :
    evalMuxSymOps R (.walk K D :: rest) v = evalMuxSymOps R rest (evalSymStage R D.1 K v) := rfl

private theorem rkm128k_ofSymmInvolution_val {N M : ℕ}
    (D : Matrix (SymSubset N M) (SymSubset N M) ℝ) (hsym : Dᵀ = D) (hinv : D * D = 1) :
    (SymOrthogonal.ofSymmInvolution D hsym hinv).1 = D := rfl

private theorem rkm128k_evalWalkAndKicks_orbEmbedGen {N M r K : ℕ} {D : SymOrthogonal N M}
    (hD : D.1 = dAltSymMat N M) {R : Finset (Fin N)} (hR : R.card = r) (hmrN : M + R.card ≤ N)
    (mask : List Bool) (uIn : Fin (orbDim M R.card) → ℝ) :
    evalMuxSymOps R (MuxSymOp.walk K D ::
        (rkmMaskKicksDown mask (min M r) false).map MuxSymOp.prefixKick)
        (orbEmbedGen N M R uIn) =
      orbEmbedGen N M R (rkmMaskSignVec (min M R.card) mask
        (((dAltStepOrbMat N M R.card) ^ K) *ᵥ uIn)) := by
  subst hR
  rw [rkm128k_evalMuxSymOps_walk_cons, hD, evalSymStage_dAltSymMat_orbEmbedGen hmrN K uIn,
    rkm128k_evalMuxSymOps_kicks_orbEmbedGen]
  apply congrArg (orbEmbedGen N M R)
  funext w
  unfold rkmMaskSignVec
  exact rkm128k_applyKickIdxsOrb_maskKicksDown (min M R.card) mask (min M R.card) false _ _
    (fun _ _ ↦ by rw [rkm128k_if_neg Bool.false_ne_true, one_mul]) w (Nat.lt_succ_iff.mp w.2)

private theorem rkm128k_evalSegOps_orbEmbedGen {n m lS tau9 nSub : ℕ} {mask : List Bool}
    {R : Finset (Fin (2 ^ n))} (hn : 80000 ≤ n) (hm_hi : lS * m ≤ 8192)
    (hr_hi : R.card ≤ 1024) (uIn : Fin (orbDim (lS * m) R.card) → ℝ) :
    evalMuxSymOps R (rkmSegOps n m R.card lS tau9 nSub mask)
        (orbEmbedGen (2 ^ n) (lS * m) R uIn) =
      orbEmbedGen (2 ^ n) (lS * m) R (rkmMaskSignVec (min (lS * m) R.card) mask
        (((dAltStepOrbMat (2 ^ n) (lS * m) R.card) ^ altStepCount tau9 nSub (2 ^ n)) *ᵥ uIn)) := by
  obtain ⟨hn1, h2x_lt, _, hmrN⟩ := rkm128k_bounds_of_n80 hn hm_hi hr_hi
  have hhm : 1 ≤ n ∧ 2 * (lS * m) < 2 ^ n := ⟨hn1, h2x_lt⟩
  unfold rkmSegOps
  rw [dite_eq_left hhm]
  exact rkm128k_evalWalkAndKicks_orbEmbedGen (rkm128k_ofSymmInvolution_val _ _ _) rfl hmrN mask uIn

private theorem rkm128kRunOneSeg_guards {m lTableMax r lPrev dCur accPad : ℕ}
    {seg : Rkm128kSeg} {vec : List ℤ} {st : ℕ × ℕ × ℕ × List ℤ}
    (hseg : rkm128kRunOneSeg m lTableMax r seg lPrev dCur accPad vec = st)
    (hne : st.1 ≠ 0) :
    1 ≤ seg.lS ∧ lPrev ≤ seg.lS ∧ seg.lS ≤ lTableMax ∧
      1 ≤ seg.lS * m ∧ seg.lS * m ≤ 8192 := by
  unfold rkm128kRunOneSeg at hseg
  cases hg1 : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) with
  | true => rw [hg1, rkm128k_cond_true] at hseg; exact absurd (congrArg Prod.fst hseg).symm hne
  | false =>
    rw [hg1, rkm128k_cond_false] at hseg
    simp only [Bool.or_eq_false_iff, rkm128k_blt_false] at hg1
    dsimp only at hseg
    revert hseg
    set g2 := Bool.or (primNatBlt seg.lS lPrev)
      (Bool.or (primNatBlt lTableMax seg.lS)
      (Bool.or (primNatBlt (Nat.mul seg.lS m) 1)
      (Bool.or (primNatBlt 8192 (Nat.mul seg.lS m))
      (Bool.or (primNatBlt (highdNatMin (Nat.mul seg.lS m) r) 1)
      (Bool.or (Nat.beq seg.tau9 0)
      (Bool.or (primNatBlt 4000000000 seg.tau9)
      (Bool.or (Nat.beq seg.nSub 0)
      (Bool.or (primNatBlt 16384 seg.nSub)
      (Bool.or (Nat.beq seg.degP 0)
      (Bool.or (primNatBlt 64 seg.degP)
        (primNatBlt (Nat.add (highdNatMin (Nat.mul seg.lS m) r) 1)
          (rkmBoolListLen seg.mask))))))))))))
    intro hseg
    cases hg2 : g2 with
    | true => rw [hg2, rkm128k_cond_true] at hseg; exact absurd (congrArg Prod.fst hseg).symm hne
    | false =>
      simp only [g2, Bool.or_eq_false_iff, rkm128k_blt_false, Nat.mul_eq] at hg2
      exact ⟨hg1.1.trans hg2.1, hg2.1, hg2.2.1, hg2.2.2.1, hg2.2.2.2.1⟩

private theorem rkm128kRunSegs_head_guards {m lTableMax r lPrev dCur accPad : ℕ}
    {seg : Rkm128kSeg} {rest : List Rkm128kSeg} {vec : List ℤ} {st : ℕ × ℕ × ℕ × List ℤ}
    (hres : rkm128kRunSegs m lTableMax r (seg :: rest) lPrev dCur accPad vec = st)
    (hne : st.1 ≠ 0) :
    1 ≤ seg.lS ∧ lPrev ≤ seg.lS ∧ seg.lS ≤ lTableMax ∧
      1 ≤ seg.lS * m ∧ seg.lS * m ≤ 8192 := by
  cases hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) with
  | true =>
    rw [rkm128kRunSegs_true m lTableMax r (seg :: rest) lPrev dCur accPad vec hg] at hres
    exact absurd (congrArg Prod.fst hres).symm hne
  | false =>
    rw [rkm128kRunSegs_cons_false m lTableMax r seg rest lPrev dCur accPad vec hg] at hres
    dsimp only at hres
    rcases h1 : rkm128kRunOneSeg m lTableMax r seg lPrev dCur accPad vec with ⟨l1, d1, p1, v1⟩
    rw [h1] at hres
    dsimp only at hres
    have hl1_ne : l1 ≠ 0 := by
      rintro rfl
      have hz := rkm128kRunSegs_true m lTableMax r rest 0 d1 p1 v1 rfl
      rw [hz] at hres
      exact hne (congrArg Prod.fst hres).symm
    exact rkm128kRunOneSeg_guards h1 hl1_ne

private theorem rkm128kRunOneSeg_sound {n m lTableMax r lPrev dCur accPad lOut dOut padWalk : ℕ}
    {seg : Rkm128kSeg} {vec vNext : List ℤ} {uIn : Fin (orbDim (seg.lS * m) r) → ℝ}
    (hn : 80000 ≤ n) (hr2 : 2 ≤ r) (hr_hi : r ≤ 1024)
    (huIn : vecNorm uIn ≤ 1) (hvec : vec.length ≤ min (seg.lS * m) r + 1)
    (hseg : rkm128kRunOneSeg m lTableMax r seg lPrev dCur accPad vec =
      (lOut, dOut, padWalk, vNext))
    (hlOut : lOut ≠ 0) :
    1 ≤ seg.lS ∧ lPrev ≤ seg.lS ∧ seg.lS ≤ lTableMax ∧
      1 ≤ seg.lS * m ∧ seg.lS * m ≤ 8192 ∧
      lOut = seg.lS ∧ dOut = min (seg.lS * m) r ∧
      padWalk ≠ 0 ∧ vNext.length ≤ min (seg.lS * m) r + 1 ∧
      ∃ uOut : Fin (orbDim (seg.lS * m) r) → ℝ,
        vecNorm uOut ≤ 1 ∧
        vecNorm (rkmMaskSignVec (min (seg.lS * m) r) seg.mask
            (((dAltStepOrbMat (2 ^ n) (seg.lS * m) r) ^
              altStepCount seg.tau9 seg.nSub (2 ^ n)) *ᵥ uIn) - uOut) +
          vecNorm (uOut - rkmListToOrbVec (min (seg.lS * m) r) vNext) ≤
          vecNorm (uIn - rkmListToOrbVec (min (seg.lS * m) r) vec) +
            ((padWalk : ℝ) - (accPad : ℝ) - 1 / 2) / wdScaleR := by
  obtain ⟨hl1, hlPrev, hlMax, hm1, hm_hi⟩ := rkm128kRunOneSeg_guards hseg hlOut
  have hB_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  unfold rkm128kRunOneSeg at hseg
  cases hg1 : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) with
  | true => rw [hg1, rkm128k_cond_true] at hseg; exact absurd (Prod.mk.inj hseg).1.symm hlOut
  | false =>
    rw [hg1, rkm128k_cond_false] at hseg
    dsimp only at hseg
    revert hseg
    set dRaw := highdNatMin (Nat.mul seg.lS m) r
    set g2 := Bool.or (primNatBlt seg.lS lPrev)
      (Bool.or (primNatBlt lTableMax seg.lS)
      (Bool.or (primNatBlt (Nat.mul seg.lS m) 1)
      (Bool.or (primNatBlt 8192 (Nat.mul seg.lS m))
      (Bool.or (primNatBlt dRaw 1)
      (Bool.or (Nat.beq seg.tau9 0)
      (Bool.or (primNatBlt 4000000000 seg.tau9)
      (Bool.or (Nat.beq seg.nSub 0)
      (Bool.or (primNatBlt 16384 seg.nSub)
      (Bool.or (Nat.beq seg.degP 0)
      (Bool.or (primNatBlt 64 seg.degP)
        (primNatBlt (Nat.add dRaw 1) (rkmBoolListLen seg.mask))))))))))))
    intro hseg
    cases hg2 : g2 with
    | true => rw [hg2, rkm128k_cond_true] at hseg; exact absurd (Prod.mk.inj hseg).1.symm hlOut
    | false =>
      rw [hg2, rkm128k_cond_false] at hseg
      simp only [g2, Bool.or_eq_false_iff, rkm128k_blt_false, rkm128k_beq_false] at hg2
      obtain ⟨_, _, _, _, _, htau0, htau_hi, hnsub0, hnsub_hi, hdeg0, hdeg_hi, _⟩ := hg2
      simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at hseg
      cases hg3 : Bool.or (primNatBlt (Nat.div (Nat.mul seg.tau9 1000000) seg.nSub) 1)
          (Bool.not (altCheckHbTight (Nat.mul seg.lS m) r 0 dRaw)) with
      | true => rw [hg3, rkm128k_cond_true] at hseg; exact absurd (Prod.mk.inj hseg).1.symm hlOut
      | false =>
        rw [hg3, rkm128k_cond_false] at hseg
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hg3
        have hd_eq : dRaw = min (seg.lS * m) r := rkmb_natMin_eq (seg.lS * m) r
        have htight : altCheckHbTight (seg.lS * m) r 0 (min (seg.lS * m) r) = true := by
          simpa only [hd_eq, Nat.mul_eq] using hg3.2
        rcases hloop : rkm128kSubstepLoop seg.nSub dRaw
            (rkm128kCeilDiv15 (Nat.mul 2 (altMaxBHiFrom (Nat.mul seg.lS m) r 0 dRaw)))
            seg.degP (altBuildHbFrom (Nat.mul seg.lS m) r
              (Nat.div (Nat.mul seg.tau9 1000000) seg.nSub) 0 dRaw)
            vec (Nat.add accPad 2) with ⟨vWalk, pWalk⟩
        rw [hloop] at hseg
        dsimp only at hseg
        cases hg4 : Bool.or (Nat.beq pWalk 0) (primNatBlt 100000000000000 pWalk) with
        | true => rw [hg4, rkm128k_cond_true] at hseg; exact absurd (Prod.mk.inj hseg).1.symm hlOut
        | false =>
          rw [hg4, rkm128k_cond_false] at hseg
          simp only [Bool.or_eq_false_iff, rkm128k_beq_false] at hg4
          rcases Prod.mk.inj hseg with ⟨rfl, hseg2⟩
          rcases Prod.mk.inj hseg2 with ⟨rfl, hseg3⟩
          rcases Prod.mk.inj hseg3 with ⟨rfl, rfl⟩
          have hloop' : rkm128kSubstepLoop seg.nSub (min (seg.lS * m) r)
              (rkm128kCeilDiv15 (2 * altMaxBHiFrom (seg.lS * m) r 0 (min (seg.lS * m) r)))
              seg.degP (altBuildHbFrom (seg.lS * m) r ((seg.tau9 * 1000000) / seg.nSub) 0
                (min (seg.lS * m) r)) vec (accPad + 2) = (vWalk, pWalk) := by
            simpa only [hd_eq, Nat.mul_eq, Nat.add_eq,
              show ∀ a b, Nat.div a b = a / b from fun _ _ ↦ rfl] using hloop
          obtain ⟨hvWalk_len, _, hsub_err⟩ := rkm128kSubstepLoop_sound hn hm1 hm_hi hr2 hr_hi
            (by omega) htau_hi (by omega) hnsub_hi (by omega) hdeg_hi htight
            seg.nSub vec vWalk (accPad + 2) pWalk uIn hvec hloop' hg4.1
          let mEff := seg.lS * m
          let d := min mEff r
          set K := altStepCount seg.tau9 seg.nSub (2 ^ n)
          set η : ℝ := 1 / √(2 ^ n : ℝ)
          set G := dAltGenMat mEff r
          have hsN_ge : (2 : ℝ) ^ 201 ≤ √(2 ^ n : ℝ) :=
            Real.le_sqrt_of_sq_le (by
              rw [← pow_mul]
              exact pow_le_pow_right₀ (by norm_num) (by omega : 402 ≤ n))
          have hsN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hsN_ge
          have hK_le : (K : ℝ) ≤ 4 * √(2 ^ n : ℝ) := by
            have h1 : (K : ℝ) ≤ ((seg.tau9 : ℝ) / 1000000000) * √(2 ^ n : ℝ) := by
              simpa [K, Nat.cast_pow, Nat.cast_ofNat] using
                altStepCount_le_tau_sqrt seg.tau9 seg.nSub (2 ^ n)
            have htauR : (seg.tau9 : ℝ) / 1000000000 ≤ 4 := by
              have hc : (seg.tau9 : ℝ) ≤ 4000000000 := by exact_mod_cast htau_hi
              linarith
            exact h1.trans (mul_le_mul_of_nonneg_right htauR hsN_pos.le)
          have hcont : vecNorm (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn -
              ((taylor16Mat η G) ^ K) *ᵥ uIn) ≤ (3 / 2) / wdScaleR := by
            have ht8 : vecNorm (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn -
                ((taylor8Mat η G) ^ K) *ᵥ uIn) ≤ 1 / (2 * wdScaleR) := by
              have h := vecNorm_dAltStepOrbMat_pow_sub_taylor8_vec_le hn hm1 hm_hi (by omega) hr_hi
                hK_le (u := uIn) (e := uIn) huIn
              rw [sub_self, vecNorm_zero, zero_add] at h
              simpa [wdScaleR, η, G] using h
            have ht16 : vecNorm (((taylor8Mat η G) ^ K) *ᵥ uIn -
                ((taylor16Mat η G) ^ K) *ᵥ uIn) ≤ 1 / wdScaleR :=
              rkmTaylor8_sub_taylor16_pow_vec_le hn hm1 hm_hi (by omega) hr_hi hK_le huIn
            have hsp : ((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn -
                ((taylor16Mat η G) ^ K) *ᵥ uIn =
                (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn - ((taylor8Mat η G) ^ K) *ᵥ uIn) +
                (((taylor8Mat η G) ^ K) *ᵥ uIn - ((taylor16Mat η G) ^ K) *ᵥ uIn) :=
              (sub_add_sub_cancel _ _ _).symm
            rw [hsp]
            have htri := vecNorm_add_le
              (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn - ((taylor8Mat η G) ^ K) *ᵥ uIn)
              (((taylor8Mat η G) ^ K) *ᵥ uIn - ((taylor16Mat η G) ^ K) *ᵥ uIn)
            have hsum : 1 / (2 * wdScaleR) + 1 / wdScaleR = (3 / 2) / wdScaleR := by ring
            linarith [htri, ht8, ht16, hsum]
          set uMac := ((taylor16Mat η G) ^ K) *ᵥ uIn
          set uOut := rkmMaskSignVec d seg.mask uMac
          have huOut_le1 : vecNorm uOut ≤ 1 := by
            rw [vecNorm_rkmMaskSignVec]
            have hηB_le1 : η * (2 : ℝ) ^ 19 ≤ 1 := by
              dsimp only [η]
              rw [one_div_mul_eq_div, div_le_one hsN_pos]
              exact (by norm_num : (2 : ℝ) ^ 19 ≤ (2 : ℝ) ^ 201).trans hsN_ge
            have hA1 : ∀ x, vecNorm (taylor16Mat η G *ᵥ x) ≤ 1 * vecNorm x := fun x ↦
              (vecNorm_taylor16Mat_mulVec_le (dAltGenMat_transpose mEff r)
                (by dsimp [η]; positivity) (by positivity) (rkm128k_dAltGen_op hm_hi hr_hi)
                (hηB_le1.trans (by norm_num)) x).trans_eq (one_mul _).symm
            exact ((vecNorm_pow_mulVec_le zero_le_one hA1 K uIn).trans_eq (by simp)).trans huIn
          refine ⟨hl1, hlPrev, hlMax, hm1, hm_hi, rfl, hd_eq, hg4.1,
            (rkmApplyMaskBits_length seg.mask vWalk).le.trans hvWalk_len, uOut, huOut_le1, ?_⟩
          have he1 : vecNorm (rkmMaskSignVec d seg.mask
              (((dAltStepOrbMat (2 ^ n) mEff r) ^ K) *ᵥ uIn) - uOut) ≤ (3 / 2) / wdScaleR := by
            dsimp only [uOut]
            rw [rkmMaskSignVec_sub, vecNorm_rkmMaskSignVec]
            exact hcont
          have he2 : vecNorm (uOut - rkmListToOrbVec d (rkmApplyMaskBits seg.mask vWalk)) ≤
              vecNorm (uIn - rkmListToOrbVec d vec) +
                ((pWalk : ℝ) - ((accPad + 2 : ℕ) : ℝ)) / wdScaleR := by
            dsimp only [uOut]
            rw [rkmApplyMaskBits_orbVec, rkmMaskSignVec_sub, vecNorm_rkmMaskSignVec]
            exact hsub_err
          have hbud : (3 / 2) / wdScaleR + ((pWalk : ℝ) - ((accPad + 2 : ℕ) : ℝ)) / wdScaleR =
              ((pWalk : ℝ) - (accPad : ℝ) - 1 / 2) / wdScaleR := by
            push_cast
            ring
          linarith [he1, he2, hbud]

private theorem rkm128kRunSegs_sound {n m lTableMax : ℕ} {R : Finset (Fin (2 ^ n))}
    (hn : 80000 ≤ n) (hr2 : 2 ≤ R.card) (hr_hi : R.card ≤ 1024) :
    ∀ (rest : List Rkm128kSeg) (s0 : Rkm128kSeg)
      (lPrev dCur accPad lOut dOut padOut : ℕ) (vec vecOut : List ℤ)
      (v : SymSubset (2 ^ n) (s0.lS * m) → ℝ)
      (uIn : Fin (orbDim (s0.lS * m) R.card) → ℝ),
      vecNorm uIn ≤ 1 →
      vec.length ≤ min (s0.lS * m) R.card + 1 →
      finVecNorm (v - orbEmbedGen (2 ^ n) (s0.lS * m) R uIn) +
        vecNorm (uIn - rkmListToOrbVec (min (s0.lS * m) R.card) vec) ≤
          ((accPad : ℝ) - 1 / 2) / wdScaleR →
      rkm128kRunSegs m lTableMax R.card (s0 :: rest) lPrev dCur accPad vec =
        (lOut, dOut, padOut, vecOut) →
      lOut ≠ 0 →
      let tailSegs := rkmBuildTailSegs n m R.card (rkm128kSegLs rest) (rkm128kSegTaus rest)
        (rkm128kSegNsubs rest) (rkm128kSegMasks rest)
      let lEnd := rkmEndL s0.lS tailSegs
      1 ≤ s0.lS ∧ lPrev ≤ s0.lS ∧ s0.lS ≤ lTableMax ∧
        rkmSegsMono s0.lS tailSegs ∧
        lEnd ≤ lTableMax ∧ lEnd * m ≤ 8192 ∧
        lOut = lEnd ∧ dOut = min (lEnd * m) R.card ∧
        padOut ≠ 0 ∧ vecOut.length ≤ dOut + 1 ∧
        ∃ uFinal : Fin (orbDim (lEnd * m) R.card) → ℝ,
          finVecNorm (rkmEvalSegs R s0.lS
              (rkmSegOps n m R.card s0.lS s0.tau9 s0.nSub s0.mask) tailSegs v -
              orbEmbedGen (2 ^ n) (lEnd * m) R uFinal) +
            vecNorm (uFinal - rkmListToOrbVec (min (lEnd * m) R.card) vecOut) ≤
              (padOut : ℝ) / wdScaleR := by
  intro rest
  have hB_pos : (0 : ℝ) < wdScaleR := by unfold wdScaleR wdScale; positivity
  induction rest with
  | nil =>
    intro s0 lPrev dCur accPad lOut dOut padOut vec vecOut v uIn huIn hvec herr hres hlOut
    cases hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) with
    | true =>
      rw [rkm128kRunSegs_true m lTableMax R.card [s0] lPrev dCur accPad vec hg] at hres
      exact absurd (Prod.mk.inj hres).1.symm hlOut
    | false =>
      rw [rkm128kRunSegs_cons_false m lTableMax R.card s0 [] lPrev dCur accPad vec hg] at hres
      dsimp only at hres
      rcases h1 : rkm128kRunOneSeg m lTableMax R.card s0 lPrev dCur accPad vec with
        ⟨l1, d1, p1, v1⟩
      rw [h1] at hres
      dsimp only at hres
      have hl1_ne : l1 ≠ 0 := by
        rintro rfl
        have hz : rkm128kRunSegs m lTableMax R.card [] 0 d1 p1 v1 = (0, 0, 0, []) := rfl
        rw [hz] at hres
        exact hlOut (Prod.mk.inj hres).1.symm
      obtain ⟨hl0_1, hlPrev_le, hl0_max, hm0_1, hm0_hi, rfl, rfl, hp1_ne, hv1_len,
        uOut, _, hseg_bd⟩ := rkm128kRunOneSeg_sound hn hr2 hr_hi huIn hvec h1 hl1_ne
      have hg_end : Bool.or (primNatBlt s0.lS 1) (Nat.beq p1 0) = false := by
        simp only [Bool.or_eq_false_iff, rkm128k_blt_false, rkm128k_beq_false]
        exact ⟨hl0_1, hp1_ne⟩
      rw [rkm128kRunSegs_nil_false m lTableMax R.card s0.lS (min (s0.lS * m) R.card) p1 v1
        hg_end] at hres
      rcases Prod.mk.inj hres with ⟨rfl, hres2⟩
      rcases Prod.mk.inj hres2 with ⟨rfl, hres3⟩
      rcases Prod.mk.inj hres3 with ⟨rfl, rfl⟩
      have hmrN : s0.lS * m + R.card ≤ 2 ^ n := (rkm128k_bounds_of_n80 hn hm0_hi hr_hi).2.2.2
      set ops0 := rkmSegOps n m R.card s0.lS s0.tau9 s0.nSub s0.mask
      set vIdeal := evalMuxSymOps R ops0 (orbEmbedGen (2 ^ n) (s0.lS * m) R uIn)
      have hvIdeal := rkm128k_evalSegOps_orbEmbedGen (tau9 := s0.tau9) (nSub := s0.nSub)
        (mask := s0.mask) hn hm0_hi hr_hi uIn
      have hq1 : finVecNorm (evalMuxSymOps R ops0 v - vIdeal) =
          finVecNorm (v - orbEmbedGen (2 ^ n) (s0.lS * m) R uIn) :=
        finVecNorm_evalMuxSymOps_sub R ops0 v _
      have hq2 : finVecNorm (vIdeal - orbEmbedGen (2 ^ n) (s0.lS * m) R uOut) =
          vecNorm (rkmMaskSignVec (min (s0.lS * m) R.card) s0.mask
            (((dAltStepOrbMat (2 ^ n) (s0.lS * m) R.card) ^
              altStepCount s0.tau9 s0.nSub (2 ^ n)) *ᵥ uIn) - uOut) := by
        dsimp only [vIdeal, ops0]
        rw [hvIdeal, ← rkm128k_orbEmbedGen_sub, finVecNorm_orbEmbedGen hmrN]
      have htri : finVecNorm (evalMuxSymOps R ops0 v - orbEmbedGen (2 ^ n) (s0.lS * m) R uOut) ≤
          finVecNorm (evalMuxSymOps R ops0 v - vIdeal) +
            finVecNorm (vIdeal - orbEmbedGen (2 ^ n) (s0.lS * m) R uOut) := by
        rw [(sub_add_sub_cancel _ vIdeal _).symm]
        exact finVecNorm_add_le _ _
      refine ⟨hl0_1, hlPrev_le, hl0_max, trivial, hl0_max, hm0_hi, rfl, rfl, hp1_ne, hv1_len,
        uOut, ?_⟩
      dsimp only [rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
        rkmBuildTailSegs, rkmEndL, rkmEvalSegs]
      have hbud : ((accPad : ℝ) - 1 / 2) / wdScaleR +
          ((p1 : ℝ) - (accPad : ℝ) - 1 / 2) / wdScaleR ≤ (p1 : ℝ) / wdScaleR := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hB_pos.le
      have hfin_bd :
          finVecNorm (evalMuxSymOps R ops0 v - orbEmbedGen (2 ^ n) (s0.lS * m) R uOut) +
            vecNorm (uOut - rkmListToOrbVec (min (s0.lS * m) R.card) v1) ≤
              (p1 : ℝ) / wdScaleR := by
        linarith [htri, hq1, hq2, hseg_bd, herr, hbud]
      exact hfin_bd
  | cons s1 rest2 ih =>
    intro s0 lPrev dCur accPad lOut dOut padOut vec vecOut v uIn huIn hvec herr hres hlOut
    rcases s0 with ⟨l0, tau0, nSub0, deg0, mask0⟩
    rcases s1 with ⟨l1S, tau1, nSub1, deg1, mask1⟩
    dsimp only at v uIn hvec herr ⊢
    cases hg : Bool.or (primNatBlt lPrev 1) (Nat.beq accPad 0) with
    | true =>
      rw [rkm128kRunSegs_true m lTableMax R.card
        (⟨l0, tau0, nSub0, deg0, mask0⟩ :: ⟨l1S, tau1, nSub1, deg1, mask1⟩ :: rest2)
        lPrev dCur accPad vec hg] at hres
      exact absurd (Prod.mk.inj hres).1.symm hlOut
    | false =>
      rw [rkm128kRunSegs_cons_false m lTableMax R.card ⟨l0, tau0, nSub0, deg0, mask0⟩
        (⟨l1S, tau1, nSub1, deg1, mask1⟩ :: rest2) lPrev dCur accPad vec hg] at hres
      dsimp only at hres
      rcases h1 : rkm128kRunOneSeg m lTableMax R.card ⟨l0, tau0, nSub0, deg0, mask0⟩
        lPrev dCur accPad vec with ⟨l1, d1, p1, v1⟩
      rw [h1] at hres
      dsimp only at hres
      have hl1_ne : l1 ≠ 0 := by
        rintro rfl
        have hz : rkm128kRunSegs m lTableMax R.card (⟨l1S, tau1, nSub1, deg1, mask1⟩ :: rest2)
            0 d1 p1 v1 = (0, 0, 0, []) := rfl
        rw [hz] at hres
        exact hlOut (Prod.mk.inj hres).1.symm
      obtain ⟨(hl0_1 : 1 ≤ l0), (hlPrev_le : lPrev ≤ l0), (hl0_max : l0 ≤ lTableMax),
        (hm0_1 : 1 ≤ l0 * m), (hm0_hi : l0 * m ≤ 8192), (hl1_eq : l1 = l0),
        (hd1_eq : d1 = min (l0 * m) R.card), hp1_ne,
        (hv1_len : v1.length ≤ min (l0 * m) R.card + 1),
        (uOut : Fin (orbDim (l0 * m) R.card) → ℝ), huOut_le1, hseg_bd⟩ :=
        rkm128kRunOneSeg_sound hn hr2 hr_hi huIn hvec h1 hl1_ne
      subst l1
      subst d1
      have hres' : rkm128kRunSegs m lTableMax R.card (⟨l1S, tau1, nSub1, deg1, mask1⟩ :: rest2)
          l0 (min (l0 * m) R.card) p1 v1 = (lOut, dOut, padOut, vecOut) := hres
      have hseg_bd' :
          vecNorm (rkmMaskSignVec (min (l0 * m) R.card) mask0
              (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^
                altStepCount tau0 nSub0 (2 ^ n)) *ᵥ uIn) - uOut) +
            vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) v1) ≤
            vecNorm (uIn - rkmListToOrbVec (min (l0 * m) R.card) vec) +
              ((p1 : ℝ) - (accPad : ℝ) - 1 / 2) / wdScaleR := hseg_bd
      obtain ⟨_, (hl01 : l0 ≤ l1S), _, _, (hm1_hi : l1S * m ≤ 8192)⟩ :=
        rkm128kRunSegs_head_guards hres' hlOut
      have hmrN0 : l0 * m + R.card ≤ 2 ^ n := (rkm128k_bounds_of_n80 hn hm0_hi hr_hi).2.2.2
      set ops0 := rkmSegOps n m R.card l0 tau0 nSub0 mask0
      set vAfter := evalMuxSymOps R ops0 v
      set vIdeal := evalMuxSymOps R ops0 (orbEmbedGen (2 ^ n) (l0 * m) R uIn)
      have hvIdeal := rkm128k_evalSegOps_orbEmbedGen (tau9 := tau0) (nSub := nSub0)
        (mask := mask0) hn hm0_hi hr_hi uIn
      have hq1 : finVecNorm (vAfter - vIdeal) =
          finVecNorm (v - orbEmbedGen (2 ^ n) (l0 * m) R uIn) :=
        finVecNorm_evalMuxSymOps_sub R ops0 v _
      have hq2 : finVecNorm (vIdeal - orbEmbedGen (2 ^ n) (l0 * m) R uOut) =
          vecNorm (rkmMaskSignVec (min (l0 * m) R.card) mask0
            (((dAltStepOrbMat (2 ^ n) (l0 * m) R.card) ^
              altStepCount tau0 nSub0 (2 ^ n)) *ᵥ uIn) - uOut) := by
        dsimp only [vIdeal, ops0]
        rw [hvIdeal, ← rkm128k_orbEmbedGen_sub, finVecNorm_orbEmbedGen hmrN0]
      have htri0 : finVecNorm (vAfter - orbEmbedGen (2 ^ n) (l0 * m) R uOut) ≤
          finVecNorm (vAfter - vIdeal) +
            finVecNorm (vIdeal - orbEmbedGen (2 ^ n) (l0 * m) R uOut) := by
        rw [(sub_add_sub_cancel _ vIdeal _).symm]
        exact finVecNorm_add_le _ _
      have herr_after : finVecNorm (vAfter - orbEmbedGen (2 ^ n) (l0 * m) R uOut) +
          vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) v1) ≤
            ((p1 : ℝ) - 1) / wdScaleR := by
        have hsum : ((accPad : ℝ) - 1 / 2) / wdScaleR +
            ((p1 : ℝ) - (accPad : ℝ) - 1 / 2) / wdScaleR = ((p1 : ℝ) - 1) / wdScaleR := by ring
        linarith [htri0, hq1, hq2, hseg_bd', herr, hsum]
      have hv1_len1 : v1.length ≤ min (l1S * m) R.card + 1 :=
        hv1_len.trans (by
          have hmul : l0 * m ≤ l1S * m := Nat.mul_le_mul_right m hl01
          have hmin : min (l0 * m) R.card ≤ min (l1S * m) R.card :=
            le_min ((Nat.min_le_left _ _).trans hmul) (Nat.min_le_right _ _)
          omega)
      by_cases hEq : l0 = l1S
      · subst l1S
        have herr1 : finVecNorm (vAfter - orbEmbedGen (2 ^ n) (l0 * m) R uOut) +
            vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) v1) ≤
              ((p1 : ℝ) - 1 / 2) / wdScaleR :=
          herr_after.trans (div_le_div_of_nonneg_right (by linarith) hB_pos.le)
        obtain ⟨_, _, _, hmono2, hlEnd_max, hlEnd_hi, hlOut_eq, hdOut_eq, hpOut_ne, hvOut_len,
          uFinal, hfin⟩ := ih ⟨l0, tau1, nSub1, deg1, mask1⟩ l0 (min (l0 * m) R.card) p1
            lOut dOut padOut v1 vecOut vAfter uOut huOut_le1 hv1_len herr1 hres' hlOut
        refine ⟨hl0_1, hlPrev_le, hl0_max, ⟨le_rfl, hmono2⟩, hlEnd_max, hlEnd_hi, hlOut_eq,
          hdOut_eq, hpOut_ne, hvOut_len, uFinal, ?_⟩
        dsimp only [rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
          rkmBuildTailSegs, rkmEndL, rkmEvalSegs]
        rw [dite_eq_left rfl]
        exact hfin
      · have hM01 : l0 * m ≤ l1S * m := Nat.mul_le_mul_right m hl01
        have h2M1_N : 2 * (l1S * m) ≤ 2 ^ n := (rkm128k_bounds_of_n80 hn hm1_hi hr_hi).2.2.1
        set v2 := stepUpFrom (2 ^ n) (l0 * m) (l1S * m) *ᵥ vAfter
        set uIn1 := zeroPadOrbVec (l0 * m) (l1S * m) R.card uOut
        have huIn1_norm : vecNorm uIn1 ≤ 1 := by
          rw [vecNorm_zeroPadOrbVec hM01]
          exact huOut_le1
        set vUp := stepUpFrom (2 ^ n) (l0 * m) (l1S * m) *ᵥ
          orbEmbedGen (2 ^ n) (l0 * m) R uOut
        have hiso : finVecNorm (v2 - vUp) =
            finVecNorm (vAfter - orbEmbedGen (2 ^ n) (l0 * m) R uOut) := by
          dsimp only [v2, vUp]
          rw [← Matrix.mulVec_sub,
            finVecNorm_mulVec_of_transpose_mul_self (stepUpFrom_transpose_mul_self hM01 h2M1_N)]
        have hstepUp := finVecNorm_stepUpFrom_orbEmbedGen_sub_le hn hm0_1 hM01 hm1_hi
          (by omega) hr_hi uOut
        have hstepUp_half : finVecNorm (vUp - orbEmbedGen (2 ^ n) (l1S * m) R uIn1) ≤
            (1 / 2) / wdScaleR :=
          hstepUp.trans ((mul_le_mul_of_nonneg_left huOut_le1
            (by unfold wdScale; positivity)).trans_eq (by unfold wdScaleR; ring))
        have htri_v2 : finVecNorm (v2 - orbEmbedGen (2 ^ n) (l1S * m) R uIn1) ≤
            finVecNorm (vAfter - orbEmbedGen (2 ^ n) (l0 * m) R uOut) + (1 / 2) / wdScaleR := by
          have htr := finVecNorm_add_le (v2 - vUp) (vUp - orbEmbedGen (2 ^ n) (l1S * m) R uIn1)
          rw [sub_add_sub_cancel] at htr
          linarith [htr, hiso, hstepUp_half]
        have hpad_orb : vecNorm (uIn1 - rkmListToOrbVec (min (l1S * m) R.card) v1) =
            vecNorm (uOut - rkmListToOrbVec (min (l0 * m) R.card) v1) := by
          dsimp only [uIn1]
          rw [← rkm128k_zeroPadOrbVec_listToOrbVec hM01 hv1_len,
            ← rkm128k_zeroPadOrbVec_sub, vecNorm_zeroPadOrbVec hM01]
        have herr1 : finVecNorm (v2 - orbEmbedGen (2 ^ n) (l1S * m) R uIn1) +
            vecNorm (uIn1 - rkmListToOrbVec (min (l1S * m) R.card) v1) ≤
              ((p1 : ℝ) - 1 / 2) / wdScaleR := by
          have hsum : ((p1 : ℝ) - 1) / wdScaleR + (1 / 2) / wdScaleR =
              ((p1 : ℝ) - 1 / 2) / wdScaleR := by ring
          linarith [htri_v2, hpad_orb, herr_after, hsum]
        obtain ⟨_, _, _, hmono2, hlEnd_max, hlEnd_hi, hlOut_eq, hdOut_eq, hpOut_ne, hvOut_len,
          uFinal, hfin⟩ := ih ⟨l1S, tau1, nSub1, deg1, mask1⟩ l0 (min (l0 * m) R.card) p1
            lOut dOut padOut v1 vecOut v2 uIn1 huIn1_norm hv1_len1 herr1 hres' hlOut
        refine ⟨hl0_1, hlPrev_le, hl0_max, ⟨hl01, hmono2⟩, hlEnd_max, hlEnd_hi, hlOut_eq,
          hdOut_eq, hpOut_ne, hvOut_len, uFinal, ?_⟩
        dsimp only [rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
          rkmBuildTailSegs, rkmEndL, rkmEvalSegs]
        rw [dite_eq_right hEq]
        exact hfin

private theorem rkm128k_altPadRightInts_length :
    ∀ (targetLen : ℕ) (xs : List ℤ), (altPadRightInts targetLen xs).length = targetLen
  | 0, _ => rfl
  | rem + 1, [] => by
    dsimp only [altPadRightInts]
    rw [rkm128k_strictConsInt_eq]
    exact congrArg Nat.succ (rkm128k_altPadRightInts_length rem [])
  | rem + 1, _ :: xs => by
    dsimp only [altPadRightInts]
    rw [rkm128k_strictConsInt_eq]
    exact congrArg Nat.succ (rkm128k_altPadRightInts_length rem xs)

private theorem rkm128k_altPadRightInts_getD :
    ∀ (targetLen : ℕ) (xs : List ℤ), xs.length ≤ targetLen →
      ∀ j : ℕ, (altPadRightInts targetLen xs).getD j 0 = xs.getD j 0
  | 0, [], _, _ => rfl
  | 0, _ :: _, hlen, _ => absurd hlen (Nat.not_le_of_gt (Nat.succ_pos _))
  | rem + 1, [], _, j => by
    dsimp only [altPadRightInts]
    rw [rkm128k_strictConsInt_eq]
    rcases j with _ | j'
    · rfl
    · exact rkm128k_altPadRightInts_getD rem [] (Nat.zero_le _) j'
  | rem + 1, _ :: xs, hlen, j => by
    dsimp only [altPadRightInts]
    rw [rkm128k_strictConsInt_eq]
    rcases j with _ | j'
    · rfl
    · exact rkm128k_altPadRightInts_getD rem xs (by simpa using hlen) j'

private theorem rkm128k_vecTailToLo12_length (pad : ℕ) :
    ∀ zs : List ℤ, (rkm128kVecTailToLo12 pad zs).length = zs.length
  | [] => rfl
  | _ :: zs => by
    unfold rkm128kVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact congrArg Nat.succ (rkm128k_vecTailToLo12_length pad zs)

private theorem rkm128k_vecTailToLo12_getD (pad : ℕ) :
    ∀ (zs : List ℤ) (j : ℕ), j < zs.length →
      (rkm128kVecTailToLo12 pad zs).getD j 0 =
        (((Int.natAbs (zs.getD j 0) - pad) * (Int.natAbs (zs.getD j 0) - pad)) /
          wdScale) / 1000
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, _ => by
    unfold rkm128kVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq, primIntNatAbs_eq]
    rfl
  | _ :: zs, j + 1, hj => by
    unfold rkm128kVecTailToLo12
    rw [AltForce.withForcedNat_eq, strictNatCons_eq]
    exact rkm128k_vecTailToLo12_getD pad zs j (by simp at hj; omega)

private def track2Tail (pad : ℕ) (xs : List ℤ) : List ℕ :=
  match xs with
  | [] => []
  | _ :: tail => rkm128kVecTailToLo12 pad tail

private theorem rkm128kPadTailToLo12_sound {dEnd accPad w : ℕ} {vecFinal : List ℤ}
    {uFinal : Fin (dEnd + 1) → ℝ} {errQ sProb : ℝ}
    (hw1 : 1 ≤ w) (hvec_len : vecFinal.length ≤ dEnd + 1)
    (hs_nn : 0 ≤ sProb)
    (htot : errQ + vecNorm (uFinal - rkmListToOrbVec dEnd vecFinal) ≤ (accPad : ℝ) / wdScaleR) :
    let rowOut := track2Tail accPad (altPadRightInts (dEnd + 1) vecFinal)
    rowOut.length = dEnd ∧
      ∀ (wFin : Fin (dEnd + 1)), wFin.1 = w → |uFinal wFin| - errQ ≤ sProb →
        w - 1 < rowOut.length →
        ((rowOut.getD (w - 1) 0 : ℝ) / 1000000000000) ≤ sProb ^ 2 := by
  intro rowOut
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  have hB : (0 : ℝ) < wdScaleR := by rw [hB_eq]; positivity
  set padded := altPadRightInts (dEnd + 1) vecFinal
  have hpad_len : padded.length = dEnd + 1 := rkm128k_altPadRightInts_length (dEnd + 1) vecFinal
  rcases hp : padded with _ | ⟨_, tail⟩
  · rw [hp] at hpad_len
    simp at hpad_len
  · have htail_len : tail.length = dEnd := by rw [hp] at hpad_len; simpa using hpad_len
    have hrow_eq : rowOut = rkm128kVecTailToLo12 accPad tail := by
      change track2Tail accPad padded = _
      simp only [hp, track2Tail]
    have hrow_len : rowOut.length = dEnd := by
      rw [hrow_eq]
      exact (rkm128k_vecTailToLo12_length accPad tail).trans htail_len
    refine ⟨hrow_len, ?_⟩
    intro wFin hwFin hq_le hw_lt
    set z : ℤ := tail.getD (w - 1) 0
    have hz_orb : rkmListToOrbVec dEnd vecFinal wFin = (z : ℝ) / wdScaleR := by
      unfold rkmListToOrbVec
      rw [← rkm128k_altPadRightInts_getD (dEnd + 1) vecFinal hvec_len wFin.1]
      change (padded.getD wFin.1 0 : ℝ) / wdScaleR = _
      rw [hp, hwFin]
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      simp [z]
    have hcoord : |uFinal wFin - (z : ℝ) / wdScaleR| ≤
        vecNorm (uFinal - rkmListToOrbVec dEnd vecFinal) := by
      rw [← hz_orb]
      exact abs_apply_le_vecNorm (uFinal - rkmListToOrbVec dEnd vecFinal) wFin
    set aLo : ℕ := Int.natAbs z - accPad
    set pLo15 : ℕ := (aLo * aLo) / wdScale
    set out : ℕ := pLo15 / 1000
    have haLo_le : (aLo : ℝ) / wdScaleR ≤ sProb := by
      by_cases hle : Int.natAbs z ≤ accPad
      · dsimp only [aLo]
        rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero, zero_div]
        exact hs_nn
      · have hgt : accPad < Int.natAbs z := by omega
        have haR : (aLo : ℝ) = |(z : ℝ)| - (accPad : ℝ) := by
          dsimp [aLo]
          rw [Nat.cast_sub hgt.le, ← primIntNatAbs_eq, rkm128k_cast_natAbs]
        have habs_diff : |(z : ℝ) / wdScaleR| - |uFinal wFin| ≤
            |uFinal wFin - (z : ℝ) / wdScaleR| := by
          have h := abs_sub_abs_le_abs_sub ((z : ℝ) / wdScaleR) (uFinal wFin)
          rwa [abs_sub_comm] at h
        have habs_div : |(z : ℝ) / wdScaleR| = |(z : ℝ)| / wdScaleR := by
          rw [abs_div, abs_of_pos hB]
        rw [haR, sub_div, ← habs_div]
        linarith [habs_diff, hcoord, htot, hq_le]
    have hsq_le : ((aLo : ℝ) / wdScaleR) ^ 2 ≤ sProb ^ 2 :=
      pow_le_pow_left₀ (by positivity) haLo_le 2
    have hchain_nat : (out * 1000) * wdScale ≤ aLo * aLo :=
      (Nat.mul_le_mul_right _ (Nat.div_mul_le_self pLo15 1000)).trans
        (Nat.div_mul_le_self (aLo * aLo) wdScale)
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
      rw [hB_eq] at hchainR
      linarith
    have hget_row : rowOut.getD (w - 1) 0 = out := by
      rw [hrow_eq]
      exact rkm128k_vecTailToLo12_getD accPad tail (w - 1) (by omega)
    rw [hget_row]
    exact hdiv_le.trans hsq_le

/-- Soundness of `rkm128kEvalRowLo12`: hit probabilities lower-bound `rkmEvalSegs`. -/
theorem rkm128kEvalRowLo12_sound {n m lTableMax : ℕ} {segs : List Rkm128kSeg}
    {R : Finset (Fin (2 ^ n))}
    (hn : 80000 ≤ n)
    (hne : rkm128kEvalRowLo12 m lTableMax R.card segs ≠ []) :
    let ls := rkm128kSegLs segs
    let taus := rkm128kSegTaus segs
    let nsubs := rkm128kSegNsubs segs
    let masks := rkm128kSegMasks segs
    let l0 := ls.headD 1
    let ops0 := rkmSegOps n m R.card l0 (taus.headD 0) (nsubs.headD 0) (masks.headD [])
    let tailSegs := rkmBuildTailSegs n m R.card ls.tail taus.tail nsubs.tail masks.tail
    let lEnd := rkmEndL l0 tailSegs
    let row := rkm128kEvalRowLo12 m lTableMax R.card segs
    1 ≤ l0 ∧
      rkmSegsMono l0 tailSegs ∧
      lEnd ≤ lTableMax ∧
      lEnd * m ≤ 8192 ∧
      row.length = min (lEnd * m) R.card ∧
      ∀ w ∈ Finset.Icc 1 (min (lEnd * m) R.card),
        (row.getD (w - 1) 0 : ℝ) / 1000000000000 ≤
          symHitProb R (rkmEvalSegs R l0 ops0 tailSegs (u0Vec (2 ^ n) (l0 * m))) w := by
  intro ls taus nsubs masks l0 ops0 tailSegs lEnd row
  have hrow_ne : row ≠ [] := hne
  have hrow_def : row = rkm128kEvalRowLo12 m lTableMax R.card segs := rfl
  clear_value row
  unfold rkm128kEvalRowLo12 at hrow_def
  dsimp only at hrow_def
  rw [rkm128k_segListLen_eq] at hrow_def
  cases hg0 : Bool.or (Nat.beq segs.length 0)
      (Bool.or (primNatBlt 128 segs.length)
        (Bool.or (primNatBlt R.card 2) (primNatBlt 1024 R.card))) with
  | true => rw [hg0, rkm128k_cond_true] at hrow_def; exact absurd hrow_def hrow_ne
  | false =>
    rw [hg0, rkm128k_cond_false] at hrow_def
    simp only [Bool.or_eq_false_iff, rkm128k_beq_false, rkm128k_blt_false] at hg0
    obtain ⟨hlen_ne, _, hr2, hr_hi⟩ := hg0
    rcases segs with _ | ⟨s0, rest⟩
    · exact absurd rfl hlen_ne
    · rcases hres : rkm128kRunSegs m lTableMax R.card (s0 :: rest)
          1 0 1 [Int.ofNat wdScale] with ⟨lOut, dEnd, accPad, vecFinal⟩
      rw [hres] at hrow_def
      unfold rkm128kFinalizeState at hrow_def
      dsimp only at hrow_def
      cases hgEnd : Bool.or (Nat.beq lOut 0)
          (Bool.or (Nat.beq dEnd 0) (Nat.beq accPad 0)) with
      | true => rw [hgEnd, rkm128k_cond_true] at hrow_def; exact absurd hrow_def hrow_ne
      | false =>
        rw [hgEnd, rkm128k_cond_false] at hrow_def
        simp only [Bool.or_eq_false_iff, rkm128k_beq_false] at hgEnd
        obtain ⟨hlOut_ne, _, _⟩ := hgEnd
        obtain ⟨_, _, _, hmh1, hmh_hi⟩ := rkm128kRunSegs_head_guards hres hlOut_ne
        let z0 : Fin (orbDim (s0.lS * m) R.card) := ⟨0, Nat.succ_pos _⟩
        let e0 : Fin (orbDim (s0.lS * m) R.card) → ℝ := Pi.single z0 1
        have he0_norm : vecNorm e0 ≤ 1 := by
          refine le_of_eq ?_
          unfold vecNorm vecSqNorm
          rw [Finset.sum_eq_single z0]
          · dsimp [e0]; rw [Pi.single_eq_same, one_pow, Real.sqrt_one]
          · intro b _ hb; dsimp [e0]; rw [Pi.single_eq_of_ne hb, zero_pow two_ne_zero]
          · intro hz; exact absurd (Finset.mem_univ z0) hz
        have he0_list : e0 = rkmListToOrbVec (min (s0.lS * m) R.card) [Int.ofNat wdScale] := by
          funext ⟨j, hj⟩
          rcases j with _ | j'
          · change e0 z0 = _
            dsimp [e0]
            rw [Pi.single_eq_same]
            unfold rkmListToOrbVec wdScaleR wdScale
            norm_num
          · have hne_z : (⟨j' + 1, hj⟩ : Fin (orbDim (s0.lS * m) R.card)) ≠ z0 :=
              fun h ↦ Nat.succ_ne_zero j' (congrArg Fin.val h)
            dsimp only [e0]
            unfold rkmListToOrbVec
            rw [Pi.single_eq_of_ne hne_z]
            simp
        have hmrNh : s0.lS * m + R.card ≤ 2 ^ n := (rkm128k_bounds_of_n80 hn hmh_hi hr_hi).2.2.2
        have hu0_err : finVecNorm (u0Vec (2 ^ n) (s0.lS * m) -
              orbEmbedGen (2 ^ n) (s0.lS * m) R e0) +
            vecNorm (e0 - rkmListToOrbVec (min (s0.lS * m) R.card) [Int.ofNat wdScale]) ≤
              (((1 : ℕ) : ℝ) - 1 / 2) / wdScaleR := by
          rw [← he0_list, sub_self, vecNorm_zero, add_zero,
            ← orbEmbedGen_u0OrbVecGen hmrNh, ← rkm128k_orbEmbedGen_sub,
            finVecNorm_orbEmbedGen hmrNh]
          have hb := vecNorm_u0OrbVecGen_sub_e0_le hn hmh1 hmh_hi (by omega) hr_hi
          dsimp only at hb
          exact hb.trans (by unfold wdScaleR wdScale; norm_num)
        obtain ⟨hl0_1, _, _, hmono, hlEnd_max, hlEnd_hi, _, hdEnd_eq, _, hvOut_len,
          uFinal, htot_err⟩ := rkm128kRunSegs_sound hn hr2 hr_hi rest s0 1 0 1 lOut dEnd accPad
            [Int.ofNat wdScale] vecFinal (u0Vec (2 ^ n) (s0.lS * m)) e0 he0_norm (by simp)
            hu0_err hres hlOut_ne
        subst hdEnd_eq
        simp only [Nat.add_eq] at hrow_def
        dsimp only [ls, taus, nsubs, masks, l0, ops0, tailSegs, lEnd,
          rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
          List.headD_cons, List.tail_cons]
        have hmrN_end : rkmEndL s0.lS (rkmBuildTailSegs n m R.card (rkm128kSegLs rest)
            (rkm128kSegTaus rest) (rkm128kSegNsubs rest) (rkm128kSegMasks rest)) * m + R.card ≤
              2 ^ n := (rkm128k_bounds_of_n80 hn hlEnd_hi hr_hi).2.2.2
        refine ⟨hl0_1, hmono, hlEnd_max, hlEnd_hi, ?_⟩
        set vEnd := rkmEvalSegs R s0.lS
          (rkmSegOps n m R.card s0.lS s0.tau9 s0.nSub s0.mask)
          (rkmBuildTailSegs n m R.card (rkm128kSegLs rest) (rkm128kSegTaus rest)
            (rkm128kSegNsubs rest) (rkm128kSegMasks rest)) (u0Vec (2 ^ n) (s0.lS * m))
        have htail_first := rkm128kPadTailToLo12_sound (w := 1) (sProb := 0)
          le_rfl hvOut_len le_rfl htot_err
        dsimp only at htail_first
        have hrow_named : row = track2Tail accPad (altPadRightInts
            (min (rkmEndL s0.lS (rkmBuildTailSegs n m R.card (rkm128kSegLs rest)
              (rkm128kSegTaus rest) (rkm128kSegNsubs rest) (rkm128kSegMasks rest)) * m) R.card + 1)
            vecFinal) := by
          rw [hrow_def]
          generalize altPadRightInts _ vecFinal = v
          cases v <;> rfl
        rw [← hrow_named] at htail_first
        refine ⟨htail_first.1, fun w hw ↦ ?_⟩
        rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
        let wFin : Fin (orbDim (rkmEndL s0.lS (rkmBuildTailSegs n m R.card (rkm128kSegLs rest)
            (rkm128kSegTaus rest) (rkm128kSegNsubs rest) (rkm128kSegMasks rest)) * m) R.card) :=
          ⟨w, Nat.lt_succ_of_le hwd⟩
        have htail := rkm128kPadTailToLo12_sound (w := w)
          (sProb := √(symHitProb R vEnd w)) hw1 hvOut_len (Real.sqrt_nonneg _) htot_err
        dsimp only at htail
        rw [← hrow_named] at htail
        have hprob_ideal : √(symHitProb R (orbEmbedGen (2 ^ n) _ R uFinal) w) = |uFinal wFin| := by
          have hp := symHitProb_orbEmbedGen hmrN_end uFinal wFin
          dsimp only [wFin] at hp
          rw [hp, Real.sqrt_sq_eq_abs]
        have hprob_ge := sqrt_symHitProb_ge_of_finVecNorm_sub_le R
          (orbEmbedGen (2 ^ n) _ R uFinal) vEnd w
        rw [hprob_ideal] at hprob_ge
        have hle_sq := htail.2 wFin rfl hprob_ge
          (by rw [htail.1]
              exact Nat.sub_lt_left_of_lt_add hw1
                (by rw [Nat.add_comm]; exact Nat.lt_succ_of_le hwd))
        rwa [Real.sq_sqrt (by unfold symHitProb; positivity)] at hle_sq

private theorem rkm128k_max_eq_bif (a b : ℕ) :
    cond (primNatBlt a b) b a = max a b := by
  cases h : primNatBlt a b
  · exact (Nat.max_eq_left (rkm128k_blt_false.mp h)).symm
  · exact (Nat.max_eq_right (rkm128k_blt_true.mp h).le).symm

private theorem rkm128k_checkDrift_to_active {m lTableMax s : ℕ}
    {segs : List Rkm128kSeg} {vPot rowLo12 vHist : List ℕ}
    (hvh_eq : ∀ j < s, vHist.getD j 0 = vPot.getD (s - 1 - j) 0)
    (h : rkm128kCheckDrift m lTableMax s segs (vPot.getD s 0)
      (muxRunningCap vPot s) rowLo12 vHist = true) :
    RampKick128kActiveValid m lTableMax s vPot segs rowLo12 := by
  unfold RampKick128kActiveValid
  dsimp only
  unfold rkm128kCheckDrift at h
  dsimp only at h
  rw [rkm128k_segListLen_eq segs] at h
  cases hg1 : Bool.or (primNatBlt segs.length 1)
      (Bool.or (primNatBlt 128 segs.length)
      (Bool.or (primNatBlt (muxRunningCap vPot s) (vPot.getD s 0))
        (Bool.not (rkm128kCheckSegBounds lTableMax segs 1)))) with
  | true => rw [hg1, rkm128k_cond_true] at h; exact Bool.noConfusion h
  | false =>
    rw [hg1, rkm128k_cond_false] at h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkm128k_blt_false] at hg1
    obtain ⟨hn1, hn32, _, hseg_bds⟩ := hg1
    set lEnd := rkm128kLastL 0 segs
    rw [show Nat.mul lEnd m = lEnd * m from rfl, rkmb_natMin_eq (lEnd * m) s] at h
    set dEnd := min (lEnd * m) s
    cases hg2 : Bool.or (Bool.not (Nat.beq (altListLen rowLo12) dEnd))
        (Bool.or (primNatBlt (altSumNat rowLo12) 1)
        (Bool.or (primNatBlt 1000000000000 (altSumNat rowLo12))
          (primNatBlt (altListLen vHist) dEnd))) with
    | true => rw [hg2, rkm128k_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg2, rkm128k_cond_false] at h
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkm128k_beq_true,
        rkm128k_blt_false, rkmb_altListLen_eq] at hg2
      obtain ⟨hr_len, htot1, htot_le, hvh_ge⟩ := hg2
      have hlt := rkm128k_blt_true.mp h
      rw [muxHitValSum27_eq_sum_range dEnd rowLo12 vHist hr_len hvh_ge] at hlt
      have hsum_eq :
          (∑ j ∈ Finset.range dEnd, rowLo12.getD j 0 * vHist.getD j 0) =
            ∑ j ∈ Finset.range dEnd, rowLo12.getD j 0 * vPot.getD (s - 1 - j) 0 := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hj_lt : j < s := (Finset.mem_range.mp hj).trans_le (Nat.min_le_right _ _)
        rw [hvh_eq j hj_lt]
      rw [hsum_eq] at hlt
      refine ⟨hn1, hn32, hseg_bds, hr_len, htot1, htot_le, ?_⟩
      simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ← add_assoc] at hlt
      exact hlt

private theorem rkm128k_findAnchor_none_of_gt :
    ∀ (anchors : List RampKick128kAnchor) (s : ℕ),
      (∀ a ∈ anchors, s < a.rAct) → rkm128kFindAnchor s anchors = none
  | [], _, _ => rfl
  | a :: rest, s, hgt => by
    have hsa : a.rAct ≠ s := by have := hgt a List.mem_cons_self; omega
    unfold rkm128kFindAnchor
    rw [ite_eq_right hsa]
    exact rkm128k_findAnchor_none_of_gt rest s (fun b hb ↦ hgt b (List.mem_cons_of_mem _ hb))

private theorem rkm128k_checkTableAux_gt :
    ∀ (vRem : List ℕ) (m lTableMax : ℕ) (useColdR2 : Bool)
      (r vCapPrev : ℕ) (vHist : List ℕ) (anchors : List RampKick128kAnchor),
      rkm128kCheckTableAux m lTableMax useColdR2 vRem r vCapPrev vHist anchors = true →
      ∀ a ∈ anchors, r ≤ a.rAct
  | [], _, _, _, _, _, _, anchors, h, a, ha => by
    cases anchors with
    | nil => nomatch ha
    | cons _ _ => simp [rkm128kCheckTableAux] at h
  | vR :: vRest, m, lTableMax, useColdR2, r, vCapPrev, vHist, anchors, h, b, hb => by
    cases vHist with
    | nil => simp [rkm128kCheckTableAux] at h
    | cons vPrev vhRest =>
      unfold rkm128kCheckTableAux at h
      simp only [rkmb_forceNat_eq] at h
      cases anchors with
      | nil => nomatch hb
      | cons a aRest =>
        dsimp only at h
        cases hlt : primNatBlt a.rAct r with
        | true => rw [hlt, rkm128k_cond_true] at h; exact Bool.noConfusion h
        | false =>
          rw [hlt, rkm128k_cond_false] at h
          have hra : r ≤ a.rAct := rkm128k_blt_false.mp hlt
          cases heq : Nat.beq a.rAct r with
          | true =>
            rw [heq, rkm128k_cond_true] at h
            cases hdr : rkm128kCheckDrift m lTableMax r a.segs vR _ a.rowLo12
                (vPrev :: vhRest) with
            | false => rw [hdr, rkm128k_cond_false] at h; exact Bool.noConfusion h
            | true =>
              rw [hdr, rkm128k_cond_true] at h
              simp only [List.mem_cons] at hb
              rcases hb with rfl | hmem
              · exact hra
              · exact (Nat.le_succ r).trans
                  (rkm128k_checkTableAux_gt vRest m lTableMax useColdR2 (r + 1) _ _ aRest h b hmem)
          | false =>
            rw [heq, rkm128k_cond_false] at h
            cases hfb : cond (Bool.and (Nat.beq r 2) useColdR2) (rkmCheckColdR2Step m vR)
                (checkEigStep m r vR vPrev) with
            | false => rw [hfb, rkm128k_cond_false] at h; exact Bool.noConfusion h
            | true =>
              rw [hfb, rkm128k_cond_true] at h
              exact (Nat.le_succ r).trans
                (rkm128k_checkTableAux_gt vRest m lTableMax useColdR2 (r + 1) _ _
                  (a :: aRest) h b hb)

private theorem rkm128k_checkTableAux_props (m lTableMax : ℕ) (useColdR2 : Bool) (vPot : List ℕ) :
    ∀ (vRem : List ℕ) (r : ℕ) (vHist : List ℕ) (anchors : List RampKick128kAnchor),
      1 ≤ r →
      vHist.getD 0 0 = vPot.getD (r - 1) 0 →
      1 ≤ vHist.length →
      (∀ j < r, vHist.getD j 0 = vPot.getD (r - 1 - j) 0) →
      (∀ j < vRem.length, vRem.getD j 0 = vPot.getD (r + j) 0) →
      RampKick128kAnchorsSound m lTableMax anchors →
      rkm128kCheckTableAux m lTableMax useColdR2 vRem r (muxRunningCap vPot (r - 1)) vHist
        anchors = true →
      ∀ s : ℕ, r ≤ s → s < r + vRem.length →
        match rkm128kFindAnchor s anchors with
        | none =>
            (s = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨
              checkEigStep m s (vPot.getD s 0) (vPot.getD (s - 1) 0) = true
        | some a =>
            a.rAct = s ∧
            rkm128kEvalRowLo12 m lTableMax s a.segs = a.rowLo12 ∧
            RampKick128kActiveValid m lTableMax s vPot a.segs a.rowLo12
  | [], _, _, _, _, _, _, _, _, _, _, _, _, hslt => by simp at hslt; omega
  | vR :: vRest, r, vHist, anchors, hr1, hvh0, hvh_len, hvh_eq, hvrem_eq, hasound, hchk,
      s, hrs, hslt => by
    rcases vHist with _ | ⟨vPrev, vhRest⟩
    · simp at hvh_len
    · have hvR_eq : vR = vPot.getD r 0 := by simpa using hvrem_eq 0 (Nat.succ_pos _)
      have hvPrev_eq : vPrev = vPot.getD (r - 1) 0 := by simpa using hvh0
      have hcap_eq : max (muxRunningCap vPot (r - 1)) vR = muxRunningCap vPot r := by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp [muxRunningCap, hvR_eq]
      have hvh_next : ∀ j < r + 1, (vR :: vPrev :: vhRest).getD j 0 = vPot.getD (r - j) 0 := by
        intro j hj
        rcases j with _ | j'
        · simp [hvR_eq]
        · rw [List.getD_cons_succ, hvh_eq j' (by omega)]
          congr 1; omega
      have hvrem_next : ∀ j < vRest.length, vRest.getD j 0 = vPot.getD (r + 1 + j) 0 := by
        intro j hj
        have h1 := hvrem_eq (j + 1) (by simp; omega)
        simpa [show r + (j + 1) = r + 1 + j by omega] using h1
      unfold rkm128kCheckTableAux at hchk
      simp only [rkmb_forceNat_eq, rkm128k_max_eq_bif, hcap_eq] at hchk
      have hfb_prop :
          cond (Bool.and (Nat.beq r 2) useColdR2) (rkmCheckColdR2Step m vR)
            (checkEigStep m r vR vPrev) = true →
          (r = 2 ∧ useColdR2 = true ∧ rkmCheckColdR2Step m (vPot.getD 2 0) = true) ∨
            checkEigStep m r (vPot.getD r 0) (vPot.getD (r - 1) 0) = true := by
        intro hfb
        cases hcond : Bool.and (Nat.beq r 2) useColdR2 with
        | true =>
          rw [hcond, rkm128k_cond_true] at hfb
          simp only [Bool.and_eq_true, rkm128k_beq_true] at hcond
          rcases hcond with ⟨rfl, huc⟩
          exact Or.inl ⟨rfl, huc, by simpa [hvR_eq] using hfb⟩
        | false =>
          rw [hcond, rkm128k_cond_false] at hfb
          exact Or.inr (by simpa [hvR_eq, hvPrev_eq] using hfb)
      rcases anchors with _ | ⟨a, aRest⟩
      · dsimp only at hchk
        cases hfb : cond (Bool.and (Nat.beq r 2) useColdR2) (rkmCheckColdR2Step m vR)
            (checkEigStep m r vR vPrev) with
        | false => rw [hfb, rkm128k_cond_false] at hchk; exact Bool.noConfusion hchk
        | true =>
          rw [hfb, rkm128k_cond_true] at hchk
          by_cases hsr : s = r
          · subst hsr
            simpa [rkm128kFindAnchor] using hfb_prop hfb
          · exact rkm128k_checkTableAux_props m lTableMax useColdR2 vPot vRest (r + 1)
              (vR :: vPrev :: vhRest) [] (by omega)
              (by simp [hvR_eq]) (by simp)
              (fun j hj ↦ by simpa [Nat.add_sub_cancel] using hvh_next j hj)
              hvrem_next trivial
              (by simpa [Nat.add_sub_cancel, show Nat.add r 1 = r + 1 from rfl] using hchk)
              s (by omega) (by simp only [List.length_cons] at hslt; omega)
      · dsimp only at hchk
        cases hlt : primNatBlt a.rAct r with
        | true => rw [hlt, rkm128k_cond_true] at hchk; exact Bool.noConfusion hchk
        | false =>
          rw [hlt, rkm128k_cond_false] at hchk
          cases heq : Nat.beq a.rAct r with
          | true =>
            rw [heq, rkm128k_cond_true] at hchk
            have har_eq : a.rAct = r := rkm128k_beq_true.mp heq
            cases hdr : rkm128kCheckDrift m lTableMax r a.segs vR (muxRunningCap vPot r)
                a.rowLo12 (vPrev :: vhRest) with
            | false => rw [hdr, rkm128k_cond_false] at hchk; exact Bool.noConfusion hchk
            | true =>
              rw [hdr, rkm128k_cond_true] at hchk
              obtain ⟨ha_eval, hrest_sound⟩ := hasound
              by_cases hsr : s = r
              · subst hsr
                unfold rkm128kFindAnchor
                rw [ite_eq_left har_eq]
                dsimp only
                rw [hvR_eq] at hdr
                rw [har_eq] at ha_eval
                exact ⟨har_eq, ha_eval, rkm128k_checkDrift_to_active hvh_eq hdr⟩
              · have hne_as : a.rAct ≠ s := by omega
                unfold rkm128kFindAnchor
                rw [ite_eq_right hne_as]
                exact rkm128k_checkTableAux_props m lTableMax useColdR2 vPot vRest (r + 1)
                  (vR :: vPrev :: vhRest) aRest (by omega)
                  (by simp [hvR_eq]) (by simp)
                  (fun j hj ↦ by simpa [Nat.add_sub_cancel] using hvh_next j hj)
                  hvrem_next hrest_sound
                  (by simpa [Nat.add_sub_cancel, show Nat.add r 1 = r + 1 from rfl] using hchk)
                  s (by omega) (by simp only [List.length_cons] at hslt; omega)
          | false =>
            rw [heq, rkm128k_cond_false] at hchk
            cases hfb : cond (Bool.and (Nat.beq r 2) useColdR2) (rkmCheckColdR2Step m vR)
                (checkEigStep m r vR vPrev) with
            | false => rw [hfb, rkm128k_cond_false] at hchk; exact Bool.noConfusion hchk
            | true =>
              rw [hfb, rkm128k_cond_true] at hchk
              by_cases hsr : s = r
              · subst hsr
                have hall_gt : ∀ b ∈ a :: aRest, s < b.rAct := fun b hb ↦ by
                  have hge := rkm128k_checkTableAux_gt vRest m lTableMax useColdR2 (s + 1) _ _
                    (a :: aRest) (by simpa [show Nat.add s 1 = s + 1 from rfl] using hchk) b hb
                  omega
                rw [rkm128k_findAnchor_none_of_gt (a :: aRest) s hall_gt]
                exact hfb_prop hfb
              · exact rkm128k_checkTableAux_props m lTableMax useColdR2 vPot vRest (r + 1)
                  (vR :: vPrev :: vhRest) (a :: aRest) (by omega)
                  (by simp [hvR_eq]) (by simp)
                  (fun j hj ↦ by simpa [Nat.add_sub_cancel] using hvh_next j hj)
                  hvrem_next hasound
                  (by simpa [Nat.add_sub_cancel, show Nat.add r 1 = r + 1 from rfl] using hchk)
                  s (by omega) (by simp only [List.length_cons] at hslt; omega)

/-- Soundness of `rkm128kCheckTable` combined with `RampKick128kAnchorsSound`. -/
theorem rkm128kCheckTable_sound {m kMax lTableMax : ℕ} {useColdR2 : Bool}
    {vPot : List ℕ} {anchors : List RampKick128kAnchor}
    (hanc : RampKick128kAnchorsSound m lTableMax anchors)
    (hchk : rkm128kCheckTable m kMax lTableMax useColdR2 vPot anchors = true) :
    RampKick128kTableValid m kMax lTableMax useColdR2 vPot anchors := by
  unfold rkm128kCheckTable at hchk
  rw [rkmb_altListLen_eq] at hchk
  cases hg1 : Bool.or (primNatBlt m 1)
      (Bool.or (primNatBlt lTableMax 1)
      (Bool.or (primNatBlt 8192 (Nat.mul lTableMax m))
      (Bool.or (primNatBlt kMax 2)
      (Bool.or (primNatBlt 1024 kMax)
        (Bool.not (Nat.beq vPot.length (Nat.add kMax 1))))))) with
  | true => rw [hg1, rkm128k_cond_true] at hchk; exact Bool.noConfusion hchk
  | false =>
    rw [hg1, rkm128k_cond_false] at hchk
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', rkm128k_blt_false, rkm128k_beq_true] at hg1
    obtain ⟨hm1, hlMax1, hlMax_hi, hk2, hk1024, hv_len⟩ := hg1
    rcases hv_cases : vPot with _ | ⟨v0, _ | ⟨v1, vRest⟩⟩
    · rw [hv_cases] at hv_len; simp at hv_len
    · rw [hv_cases] at hv_len; simp [Nat.add_eq] at hv_len; omega
    · rw [hv_cases] at hchk hv_len
      dsimp only at hchk
      cases hv0_z : Bool.not (Nat.beq v0 0) with
      | true => rw [hv0_z, rkm128k_cond_true] at hchk; exact Bool.noConfusion hchk
      | false =>
        rw [hv0_z, rkm128k_cond_false] at hchk
        simp only [Bool.not_eq_false', rkm128k_beq_true] at hv0_z
        cases heig1 : checkEigStep m 1 v1 v0 with
        | false => rw [heig1, rkm128k_cond_false] at hchk; exact Bool.noConfusion hchk
        | true =>
          rw [heig1, rkm128k_cond_true] at hchk
          have hv1_ge : v0 ≤ v1 := hv0_z ▸ Nat.zero_le v1
          have hcap1 : muxRunningCap (v0 :: v1 :: vRest) 1 = v1 :=
            Nat.max_eq_right hv1_ge
          have hrest_len : vRest.length = kMax - 1 := by simp [Nat.add_eq] at hv_len; omega
          have hrows := rkm128k_checkTableAux_props m lTableMax useColdR2 (v0 :: v1 :: vRest)
            vRest 2 [v1, v0] anchors (by omega) rfl (by simp)
            (fun j hj ↦ by rcases j with _ | _ | _ <;> first | rfl | omega)
            (fun j _ ↦ by
              rw [show 2 + j = (j + 1) + 1 by omega, List.getD_cons_succ, List.getD_cons_succ])
            hanc (by simpa [hcap1] using hchk)
          exact ⟨hm1, hlMax1, hlMax_hi, hk2, hk1024, hv_len, hv0_z, heig1,
            fun s hs2 hsk ↦ hrows s hs2 (by omega)⟩

private theorem rkm128k_segLs_len :
    ∀ segs : List Rkm128kSeg, (rkm128kSegLs segs).length = segs.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (rkm128k_segLs_len rest)

private theorem rkm128k_weightedTau9_eq :
    ∀ segs : List Rkm128kSeg,
      rkm128kWeightedTau9 segs = rkmWeightedTau9 (rkm128kSegLs segs) (rkm128kSegTaus segs)
  | [] => rfl
  | s :: rest => congrArg (Nat.add (Nat.mul s.lS s.tau9)) (rkm128k_weightedTau9_eq rest)

private theorem rkm128k_lastL_mem :
    ∀ (rest : List Rkm128kSeg) (l0 : ℕ), rkm128kLastL l0 rest ∈ l0 :: rkm128kSegLs rest
  | [], _ => List.mem_cons_self
  | s :: rest, _ => List.mem_cons_of_mem _ (rkm128k_lastL_mem rest s.lS)

private theorem rkm128k_findAnchor_mem {r : ℕ} :
    ∀ {anchors : List RampKick128kAnchor} {a : RampKick128kAnchor},
      rkm128kFindAnchor r anchors = some a → a ∈ anchors ∧ a.rAct = r
  | [], _, h => by simp [rkm128kFindAnchor] at h
  | b :: rest, a, h => by
    unfold rkm128kFindAnchor at h
    by_cases hbr : b.rAct = r
    · rw [ite_eq_left hbr] at h
      cases h
      exact ⟨List.mem_cons_self, hbr⟩
    · rw [ite_eq_right hbr] at h
      obtain ⟨hm, hr⟩ := rkm128k_findAnchor_mem h
      exact ⟨List.mem_cons_of_mem b hm, hr⟩

private theorem rkm128k_checkSegsLMax_mem (lMaxCell : ℕ) :
    ∀ (segs : List Rkm128kSeg),
      rkm128kCheckSegsLMax lMaxCell segs = true →
      ∀ x ∈ rkm128kSegLs segs, 1 ≤ x ∧ x ≤ lMaxCell
  | [], _, _, hx => nomatch hx
  | s :: rest, h, x, hx => by
    unfold rkm128kCheckSegsLMax at h
    cases hg : Bool.or (primNatBlt s.lS 1) (primNatBlt lMaxCell s.lS) with
    | true => rw [hg, rkm128k_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg, rkm128k_cond_false] at h
      simp only [Bool.or_eq_false_iff, rkm128k_blt_false] at hg
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hg
      · exact rkm128k_checkSegsLMax_mem lMaxCell rest h x hmem

private theorem rkm128k_checkAnchorsLMax_mem {k lMaxCell : ℕ} :
    ∀ {anchors : List RampKick128kAnchor} {a : RampKick128kAnchor},
      rkm128kCheckAnchorsLMax k lMaxCell anchors = true →
      a ∈ anchors → a.rAct ≤ k → ∀ x ∈ rkm128kSegLs a.segs, 1 ≤ x ∧ x ≤ lMaxCell
  | [], _, _, hm, _ => nomatch hm
  | b :: rest, a, h, hm, hrk => by
    unfold rkm128kCheckAnchorsLMax at h
    dsimp only at h
    cases hok : cond (Nat.ble b.rAct k) (rkm128kCheckSegsLMax lMaxCell b.segs) true with
    | false => rw [hok, rkm128k_cond_false] at h; exact Bool.noConfusion h
    | true =>
      rw [hok, rkm128k_cond_true] at h
      rcases List.mem_cons.mp hm with rfl | hmem
      · rw [rkm128k_ble_true.mpr hrk, rkm128k_cond_true] at hok
        exact rkm128k_checkSegsLMax_mem lMaxCell a.segs hok
      · exact rkm128k_checkAnchorsLMax_mem h hmem hrk

private theorem rkm128k_segsMono_build (n m r lTableMax : ℕ) :
    ∀ (rest : List Rkm128kSeg) (l0 : ℕ),
      rkm128kCheckSegBounds lTableMax rest l0 = true →
      rkmSegsMono l0 (rkmBuildTailSegs n m r (rkm128kSegLs rest) (rkm128kSegTaus rest)
        (rkm128kSegNsubs rest) (rkm128kSegMasks rest))
  | [], _, _ => trivial
  | s1 :: rest, l0, h => by
    unfold rkm128kCheckSegBounds at h
    cases hg : Bool.or (primNatBlt s1.lS 1)
        (Bool.or (primNatBlt s1.lS l0)
        (Bool.or (primNatBlt lTableMax s1.lS)
        (Bool.or (primNatBlt s1.tau9 1) (primNatBlt 4000000000 s1.tau9)))) with
    | true => rw [hg, rkm128k_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg, rkm128k_cond_false] at h
      simp only [Bool.or_eq_false_iff, rkm128k_blt_false] at hg
      exact ⟨hg.2.1, rkm128k_segsMono_build n m r lTableMax rest s1.lS h⟩

private theorem rkm128k_endL_build (n m r : ℕ) :
    ∀ (rest : List Rkm128kSeg) (l0 : ℕ),
      rkmEndL l0 (rkmBuildTailSegs n m r (rkm128kSegLs rest) (rkm128kSegTaus rest)
        (rkm128kSegNsubs rest) (rkm128kSegMasks rest)) = rkm128kLastL l0 rest
  | [], _ => rfl
  | s1 :: rest, _ => rkm128k_endL_build n m r rest s1.lS

private theorem rkm128k_checkSegBounds_le (lTableMax : ℕ) :
    ∀ (segs : List Rkm128kSeg) (lPrev : ℕ),
      rkm128kCheckSegBounds lTableMax segs lPrev = true →
      ∀ x ∈ rkm128kSegLs segs, x ≤ lTableMax
  | [], _, _, _, hx => nomatch hx
  | s :: rest, lPrev, h, x, hx => by
    unfold rkm128kCheckSegBounds at h
    cases hg : Bool.or (primNatBlt s.lS 1)
        (Bool.or (primNatBlt s.lS lPrev)
        (Bool.or (primNatBlt lTableMax s.lS)
        (Bool.or (primNatBlt s.tau9 1) (primNatBlt 4000000000 s.tau9)))) with
    | true => rw [hg, rkm128k_cond_true] at h; exact Bool.noConfusion h
    | false =>
      rw [hg, rkm128k_cond_false] at h
      simp only [Bool.or_eq_false_iff, rkm128k_blt_false] at hg
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hg.2.2.1
      · exact rkm128k_checkSegBounds_le lTableMax rest s.lS h x hmem

private theorem rkm128k_sum_range_nat_shift (f : ℕ → ℕ) :
    ∀ d : ℕ, (∑ j ∈ Finset.range (d + 1), f j) = f 0 + ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by simp
  | d + 1 => by
    rw [Finset.sum_range_succ, rkm128k_sum_range_nat_shift f d, Finset.sum_range_succ, add_assoc]

private theorem rkm128k_sum_Icc_one_eq_range (f : ℕ → ℝ) :
    ∀ d : ℕ, (∑ w ∈ Finset.Icc 1 d, f w) = ∑ j ∈ Finset.range d, f (j + 1)
  | 0 => by
    have hset : Finset.Icc (1 : ℕ) 0 = ∅ := by ext x; simp
    rw [hset]
    simp
  | d + 1 => by
    have hset : Finset.Icc 1 (d + 1) = insert (d + 1) (Finset.Icc 1 d) := by ext x; simp; omega
    rw [hset, Finset.sum_insert (by simp), rkm128k_sum_Icc_one_eq_range f d, Finset.sum_range_succ]
    ring

private theorem rkm128k_altSumNat_eq_sum_range :
    ∀ (d : ℕ) (xs : List ℕ), xs.length = d → altSumNat xs = ∑ j ∈ Finset.range d, xs.getD j 0
  | 0, [], _ => by simp [altSumNat]
  | 0, _ :: _, hlen => by simp at hlen
  | _ + 1, [], hlen => by simp at hlen
  | d + 1, x :: xs, hlen => by
    rw [rkm128k_sum_range_nat_shift]
    simpa [altSumNat] using congrArg (Nat.add x)
      (rkm128k_altSumNat_eq_sum_range d xs (by simpa using hlen))

private def rkm128kUseWalk (anchors : List RampKick128kAnchor) (r : ℕ) : Bool :=
  if r < 2 then false else (rkm128kFindAnchor r anchors).isSome

private theorem rkm128k_active_unpack {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    {vPot : List ℕ} {anchors : List RampKick128kAnchor} (hk_le : k ≤ kMax)
    (htab : RampKick128kTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkm128kCheckAnchorsLMax k lMaxCell anchors = true)
    {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ k) (hwk : rkm128kUseWalk anchors r = true) :
    let a := rkm128kAnchorAt anchors r
    a.rAct = r ∧ rkm128kEvalRowLo12 m lTableMax r a.segs = a.rowLo12 ∧
      rkm128kEvalRowLo12 m lTableMax r a.segs ≠ [] ∧
      RampKick128kActiveValid m lTableMax r vPot a.segs a.rowLo12 ∧
      1 ≤ rkm128kLastL 0 a.segs ∧ rkm128kLastL 0 a.segs ≤ lMaxCell := by
  intro a
  have hnr2 : ¬ r < 2 := by omega
  unfold rkm128kUseWalk at hwk
  rw [ite_eq_right hnr2] at hwk
  have hrow_r := htab.hrows r hr2 (hrk.trans hk_le)
  cases hfind : rkm128kFindAnchor r anchors with
  | none => simp [hfind] at hwk
  | some a0 =>
    rw [hfind] at hrow_r
    have ha_eq : a = a0 := by simp [a, rkm128kAnchorAt, hfind]
    rw [← ha_eq] at hrow_r
    obtain ⟨har, heval, hact⟩ := hrow_r
    have hne : rkm128kEvalRowLo12 m lTableMax r a.segs ≠ [] := by
      rw [heval]
      intro hnil
      have hpos := hact.2.2.2.2.1
      rw [hnil] at hpos
      simp [altSumNat] at hpos
    have hlast : 1 ≤ rkm128kLastL 0 a.segs ∧ rkm128kLastL 0 a.segs ≤ lMaxCell := by
      have hlen1 := hact.1
      rcases hs_cons : a.segs with _ | ⟨sh, st⟩
      · simp [hs_cons] at hlen1
      · have hmem_anc := (rkm128k_findAnchor_mem hfind).1
        rw [← ha_eq] at hmem_anc
        have hall_l := rkm128k_checkAnchorsLMax_mem hlcell hmem_anc (har ▸ hrk)
        exact hall_l _ (by rw [hs_cons]; exact rkm128k_lastL_mem st sh.lS)
    exact ⟨har, heval, hne, hact, hlast.1, hlast.2⟩

private theorem rkm128k_active_drift_lt {m lTableMax r : ℕ} {segs : List Rkm128kSeg}
    {vPot row : List ℕ} (hact : RampKick128kActiveValid m lTableMax r vPot segs row) :
    let d := min (rkm128kLastL 0 segs * m) r
    let pLo := fun w ↦ if 1 ≤ w ∧ w ≤ d then (row.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
    let c := ∑ w ∈ Finset.Icc 1 d, pLo w
    (rkm128kWeightedTau9 segs : ℝ) / 1000000000 +
        (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) +
        (1 - c) * ((muxRunningCap vPot r : ℝ) / wdScaleR) <
      (vPot.getD r 0 : ℝ) / wdScaleR := by
  intro d pLo c
  obtain ⟨_, _, _, hr_len, _, htot_le, hlt_nat⟩ := hact
  have hc_eq : c = (altSumNat row : ℝ) / 1000000000000 := by
    dsimp only [c, pLo]
    rw [rkm128k_sum_Icc_one_eq_range, rkm128k_altSumNat_eq_sum_range d row hr_len,
      Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_lt : j < d := Finset.mem_range.mp hj
    rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  have hhit_eq : (∑ w ∈ Finset.Icc 1 d, pLo w * ((vPot.getD (r - w) 0 : ℝ) / wdScaleR)) =
      ((∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0 : ℕ) : ℝ) /
        (1000000000000 * wdScaleR) := by
    dsimp only [pLo]
    rw [rkm128k_sum_Icc_one_eq_range, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj_lt : j < d := Finset.mem_range.mp hj
    have hsub_idx : r - (j + 1) = r - 1 - j := by omega
    rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel, hsub_idx, Nat.cast_mul]
    ring
  have hdef_eq : 1 - c = ((1000000000000 - altSumNat row : ℕ) : ℝ) / 1000000000000 := by
    rw [hc_eq, Nat.cast_sub htot_le]
    ring
  have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
  rw [hhit_eq, hdef_eq]
  set W9 : ℕ := rkm128kWeightedTau9 segs
  set H27 : ℕ := ∑ j ∈ Finset.range d, row.getD j 0 * vPot.getD (r - 1 - j) 0
  set D12 : ℕ := 1000000000000 - altSumNat row
  set C15 : ℕ := muxRunningCap vPot r
  set VPot : ℕ := vPot.getD r 0
  have hlt_R : (W9 : ℝ) * (1000 * wdScaleR) + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) <
      1000000000000 * (VPot : ℝ) := by
    have hc_lt : ((W9 * (1000 * wdScale) + H27 + D12 * C15 : ℕ) : ℝ) <
        ((1000000000000 * VPot : ℕ) : ℝ) := by exact_mod_cast hlt_nat
    have hB_cast : (wdScale : ℝ) = wdScaleR := rfl
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hB_cast] using hc_lt
  set S27 : ℝ := 1000000000000 * wdScaleR
  have hS27_pos : 0 < S27 := by dsimp [S27]; rw [hB_eq]; positivity
  have hlhs_mul : ((W9 : ℝ) / 1000000000 + (H27 : ℝ) / (1000000000000 * wdScaleR) +
      ((D12 : ℝ) / 1000000000000) * ((C15 : ℝ) / wdScaleR)) * S27 =
      (W9 : ℝ) * (1000 * wdScaleR) + (H27 : ℝ) + (D12 : ℝ) * (C15 : ℝ) := by
    dsimp only [S27]
    rw [hB_eq]
    ring
  have hrhs_mul : ((VPot : ℝ) / wdScaleR) * S27 = 1000000000000 * (VPot : ℝ) := by
    dsimp only [S27]
    rw [hB_eq]
    ring
  exact lt_of_mul_lt_mul_right (by linarith) hS27_pos.le

/-- Builds `JohnsonRampMuxSparseWalkSpec` (`C_step = 2149580800`) from
  `RampKick128kTableValid`. -/
noncomputable def rkm128kWalkSpecOf {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    (hm_grid : m ∈ groverGrid) (vPot : List ℕ) (anchors : List RampKick128kAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKick128kTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkm128kCheckAnchorsLMax k lMaxCell anchors = true) :
    JohnsonRampMuxSparseWalkSpec m k lMaxCell where
  hL_max_pos := hlcell_pos
  hL_max_hi := hlcell_hi
  useWalk := rkm128kUseWalk anchors
  useColdR2 := Bool.and (Bool.and useColdR2 (Bool.not (rkm128kUseWalk anchors 2)))
    (rkmCheckColdR2Step m (vPot.getD 2 0))
  hColdM2 := fun hc ↦ by
    simp only [Bool.and_eq_true] at hc
    exact hm2_cold hc.1.1
  hColdL2 := fun hc ↦ by
    simp only [Bool.and_eq_true] at hc
    exact hl2_cold hc.1.1
  lInit := fun r ↦ (rkm128kSegLs (rkm128kAnchorAt anchors r).segs).headD 1
  lEnd := fun r ↦ rkm128kLastL 0 (rkm128kAnchorAt anchors r).segs
  hlEnd_pos := fun r hr2 hrk hwk ↦ (rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk).2.2.2.2.1
  hlEnd_le := fun r hr2 hrk hwk ↦ (rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk).2.2.2.2.2
  n0 := altN0
  hn0 := by unfold altN0; norm_num
  ops0 := fun n r ↦
    let segs := (rkm128kAnchorAt anchors r).segs
    let ls := rkm128kSegLs segs
    let taus := rkm128kSegTaus segs
    let nsubs := rkm128kSegNsubs segs
    let masks := rkm128kSegMasks segs
    rkmSegOps n m r (ls.headD 1) (taus.headD 0) (nsubs.headD 0) (masks.headD [])
  segsTail := fun n r ↦
    let segs := (rkm128kAnchorAt anchors r).segs
    rkmToRmsSegs (rkmBuildTailSegs n m r
      (rkm128kSegLs segs).tail (rkm128kSegTaus segs).tail
      (rkm128kSegNsubs segs).tail (rkm128kSegMasks segs).tail)
  hsegs_mono := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk
    have hlen1 := hact.1
    have hsegB := hact.2.2.1
    set a := rkm128kAnchorAt anchors r
    rw [rmsSegsMono_rkmToRmsSegs]
    rcases hs_cons : a.segs with _ | ⟨sh, st⟩
    · simp [hs_cons] at hlen1
    · rw [hs_cons] at hsegB
      unfold rkm128kCheckSegBounds at hsegB
      cases hg : Bool.or (primNatBlt sh.lS 1)
          (Bool.or (primNatBlt sh.lS 1)
          (Bool.or (primNatBlt lTableMax sh.lS)
          (Bool.or (primNatBlt sh.tau9 1) (primNatBlt 4000000000 sh.tau9)))) with
      | true => rw [hg, rkm128k_cond_true] at hsegB; exact Bool.noConfusion hsegB
      | false =>
        rw [hg, rkm128k_cond_false] at hsegB
        dsimp only [rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
          List.headD_cons, List.tail_cons]
        exact rkm128k_segsMono_build n m r lTableMax st sh.lS hsegB
  hlEnd_eq := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk
    have hlen1 := hact.1
    set a := rkm128kAnchorAt anchors r
    rw [rmsEndL_rkmToRmsSegs]
    rcases hs_cons : a.segs with _ | ⟨sh, st⟩
    · simp [hs_cons] at hlen1
    · dsimp only [rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
        List.headD_cons, List.tail_cons, rkm128kLastL]
      exact rkm128k_endL_build n m r st sh.lS
  V := fun r ↦ (vPot.getD r 0 : ℝ) / wdScaleR
  hV0 := by rw [htab.hv0, Nat.cast_zero, zero_div]
  hV_nonneg := fun r _ ↦ by unfold wdScaleR wdScale; positivity
  vCap := fun r ↦ (muxRunningCap vPot r : ℝ) / wdScaleR
  hvCap_ge := fun j r hjr _ ↦ by
    have hB : (0 : ℝ) ≤ wdScaleR := by unfold wdScaleR wdScale; positivity
    exact div_le_div_of_nonneg_right (by exact_mod_cast muxRunningCap_ge_of_le vPot hjr) hB
  hV_cold2 := fun hc _ ↦ by
    simp only [Bool.and_eq_true] at hc
    exact rmsCheckColdR2Step_sound hm_grid (hm2_cold hc.1.1) hc.2
  hV_eig := fun r hr1 hrk hor ↦ by
    refine checkEigStep_sound ?_
    rcases hor with rfl | ⟨huw, hncold⟩
    · exact htab.heig1
    · by_cases hr2 : r < 2
      · have hr_eq1 : r = 1 := by omega
        subst hr_eq1
        exact htab.heig1
      · have hr2_ge : 2 ≤ r := by omega
        have huw' := huw
        unfold rkm128kUseWalk at huw'
        rw [ite_eq_right hr2] at huw'
        have hrow_r := htab.hrows r hr2_ge (hrk.trans hk_le)
        cases hfind : rkm128kFindAnchor r anchors with
        | some _ => simp [hfind] at huw'
        | none =>
          rw [hfind] at hrow_r
          rcases hrow_r with ⟨rfl, hc_true, hchk_c⟩ | heig
          · exfalso
            apply hncold
            refine ⟨rfl, ?_⟩
            rw [hc_true, huw, hchk_c]
            rfl
          · exact heig
  pLo := fun r w ↦
    let a := rkm128kAnchorAt anchors r
    let d := min (rkm128kLastL 0 a.segs * m) r
    if 1 ≤ w ∧ w ≤ d then (a.rowLo12.getD (w - 1) 0 : ℝ) / 1000000000000 else 0
  hpLo_nonneg := fun r w ↦ by dsimp only; split_ifs <;> positivity
  hpLo_sum_pos := fun r hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨_, _, _, hr_len, hsum_pos, _, _⟩ := hact
    set a := rkm128kAnchorAt anchors r
    set d := min (rkm128kLastL 0 a.segs * m) r
    rw [rkm128k_sum_Icc_one_eq_range]
    have hcongr : (∑ j ∈ Finset.range d,
          (if 1 ≤ j + 1 ∧ j + 1 ≤ d then (a.rowLo12.getD ((j + 1) - 1) 0 : ℝ) / 1000000000000
           else 0)) = ((altSumNat a.rowLo12 : ℕ) : ℝ) / 1000000000000 := by
      rw [rkm128k_altSumNat_eq_sum_range d a.rowLo12 hr_len, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hj_lt : j < d := Finset.mem_range.mp hj
      rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    rw [hcongr]
    have hsumR : (0 : ℝ) < (altSumNat a.rowLo12 : ℝ) := by exact_mod_cast hsum_pos
    positivity
  tauWeighted := fun r ↦ (rkm128kWeightedTau9 (rkm128kAnchorAt anchors r).segs : ℝ) / 1000000000
  C_step := 2149580800
  hqcount_le := fun n r _ hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk
    obtain ⟨hlen1, hlen32, hsegB, _, _, _, _⟩ := hact
    dsimp only
    set a := rkm128kAnchorAt anchors r
    rw [rmsSegsQueryCount_rkmToRmsSegs, rkm128k_weightedTau9_eq a.segs]
    have hall_le := rkm128k_checkSegBounds_le lTableMax a.segs 1 hsegB
    have hlTab_hi : lTableMax ≤ 8192 := by
      have h1 := Nat.mul_le_mul_left lTableMax htab.hm1
      have hhi := htab.hlMax_hi
      omega
    have hr1024 : r ≤ 1024 := (hrk.trans hk_le).trans htab.hkMax_hi
    have hls_len : (rkm128kSegLs a.segs).length ≤ 128 := (rkm128k_segLs_len a.segs).trans_le hlen32
    have hC_nat : 2 * (rkm128kSegLs a.segs).length * lTableMax * (r + 1) ≤ 2149580800 :=
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hls_len) hlTab_hi)
        (Nat.succ_le_succ hr1024)).trans (by norm_num)
    have hC_real : 2 * ((rkm128kSegLs a.segs).length : ℝ) * (lTableMax : ℝ) * ((r + 1 : ℕ) : ℝ) ≤
        2149580800 := by
      have hc : ((2 * (rkm128kSegLs a.segs).length * lTableMax * (r + 1) : ℕ) : ℝ) ≤
          (2149580800 : ℝ) := by exact_mod_cast hC_nat
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
    rcases hs_cons : a.segs with _ | ⟨sh, st⟩
    · simp [hs_cons] at hlen1
    · rw [hs_cons] at hall_le hC_real
      dsimp only [rkm128kSegLs] at hC_real
      dsimp only [rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
        List.headD_cons, List.tail_cons]
      have hbd := rkmSegsQueryCount_build_le n m r lTableMax sh.lS sh.tau9 sh.nSub sh.mask
        (rkm128kSegLs st) (rkm128kSegTaus st) (rkm128kSegNsubs st) (rkm128kSegMasks st)
        (hall_le sh.lS List.mem_cons_self)
        (fun x hx ↦ hall_le x (List.mem_cons_of_mem sh.lS hx))
      linarith
  hpLo_le := fun n r hn0 hr2 hrk hwk R hR w hw ↦ by
    obtain ⟨_, heval, hne, hact, _, _⟩ := rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk
    have hlen1 := hact.1
    subst hR
    dsimp only
    set a := rkm128kAnchorAt anchors R.card
    rcases Finset.mem_Icc.mp hw with ⟨hw1, hwd⟩
    rw [ite_eq_left ⟨hw1, hwd⟩, symHitProb_evalRampMuxSegs_rkmToRmsSegs]
    have hsound := (rkm128kEvalRowLo12_sound (R := R) hn0 hne).2.2.2.2.2
    have hend_eq : rkmEndL ((rkm128kSegLs a.segs).headD 1)
          (rkmBuildTailSegs n m R.card (rkm128kSegLs a.segs).tail (rkm128kSegTaus a.segs).tail
            (rkm128kSegNsubs a.segs).tail (rkm128kSegMasks a.segs).tail) =
        rkm128kLastL 0 a.segs := by
      rcases hs_cons : a.segs with _ | ⟨sh, st⟩
      · simp [hs_cons] at hlen1
      · dsimp only [rkm128kSegLs, rkm128kSegTaus, rkm128kSegNsubs, rkm128kSegMasks,
          List.headD_cons, List.tail_cons, rkm128kLastL]
        exact rkm128k_endL_build n m R.card st sh.lS
    rw [heval] at hsound
    exact hsound w (by rwa [hend_eq])
  hdrift_ramp_lt := fun r hr2 hrk hwk ↦ by
    obtain ⟨_, _, _, hact, _, _⟩ := rkm128k_active_unpack hk_le htab hlcell hr2 hrk hwk
    exact rkm128k_active_drift_lt hact

/-- Turnkey parallel query-model circuit for a certified `RampKick128k` `(m, k)` cell. -/
noncomputable def rkm128kCellCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKick128kAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKick128kTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkm128kCheckAnchorsLMax k lMaxCell anchors = true) (n : ℕ) :
    OracleCirc Var (Stage1.qubits n (lMaxCell * m) k) ((n + 1) * m) :=
  johnsonRampMuxSparseCircuit res hm_grid hk_grid
    (rkm128kWalkSpecOf hm_grid vPot anchors hk_le hm2_cold hl2_cold hlcell_pos hlcell_hi htab
      hlcell)
    n

/-- Exact probability-`1` correctness of `rkm128kCellCircuit` on `groverTargetSets n k`. -/
theorem rkm128kCell_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKick128kAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKick128kTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkm128kCheckAnchorsLMax k lMaxCell anchors = true)
    (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))}
    (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n (lMaxCell * m) k)) ⦄
    (qset ;;
      (rkm128kCellCircuit res hm_grid hk_grid vPot anchors hk_le hm2_cold hl2_cold
        hlcell_pos hlcell_hi htab hlcell n).compile qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ :=
  johnsonRampMuxSparseCircuit_correctness res hm_grid hk_grid _ hn hkN hS

/-- Asymptotic uniform-average relative-cost bound of `rkm128kCellCircuit` via
  `checkAltBound12`. -/
theorem rkm128kCell_rel_cost {Var : Type} [DecidableEq Var] (res : Var)
    {m k kMax lTableMax lMaxCell : ℕ} {useColdR2 : Bool} {rel : ℚ≥0}
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (vPot : List ℕ) (anchors : List RampKick128kAnchor)
    (hk_le : k ≤ kMax)
    (hm2_cold : useColdR2 = true → 2 ≤ m)
    (hl2_cold : useColdR2 = true → 2 ≤ lMaxCell)
    (hlcell_pos : 1 ≤ lMaxCell)
    (hlcell_hi : lMaxCell * m ≤ 65536)
    (htab : RampKick128kTableValid m kMax lTableMax useColdR2 vPot anchors)
    (hlcell : rkm128kCheckAnchorsLMax k lMaxCell anchors = true)
    (hbnd : ∃ num den : ℕ,
      rel = NNRat.divNat num den ∧ checkAltBound12 m k (vPot.getD k 0) num den = true) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n →
      AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n (lMaxCell * m) k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ qset ;;
            (rkm128kCellCircuit res hm_grid hk_grid vPot anchors hk_le hm2_cold hl2_cold
              hlcell_pos hlcell_hi htab hlcell n).compile qAssign
              (groverParallelMarkingOracle m S))
        ((rel : ℝ) * vanillaFindAllCost n m k) := by
  obtain ⟨num, den, rfl, hb⟩ := hbnd
  exact johnsonRampMuxSparseCircuit_rel_cost res hm_grid hk_grid _
    (checkAltBound12_sound (one_le_of_mem_groverGrid hm_grid) hb)

end

end QuantumComputation.Specs.DickeSol
