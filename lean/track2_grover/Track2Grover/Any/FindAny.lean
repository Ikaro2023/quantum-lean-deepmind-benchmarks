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

public import Track2Grover.Any.Defs
import Track2Grover.Any.OddParityBridge
import QuantumComputation.Maths.Trigonometry
import QuantumComputation.Primitives.Hadamard
import QuantumComputation.Algorithms.Grover.Operators
import QuantumComputation.Algorithms.Grover.Amplitude
import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops

/-!
# Parallel Multi-Target Find-Any Grover Search

Combines odd-parity parallel flag conjugation (`OddParityBridge.lean`) with a stationary 1-call
`.qWhile` eigenvector-locking weak measurement and Mathlib's `Real.pi_gt_d20` lower bound on `π`,
achieving the `(1 / 2 + 1 / π)` asymptotic parallel-round ratio across all `121` dyadic cells of
`groverGrid`.
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
private lemma qhlWhileSucc_val {Var : Type} {d : ℕ}
    (body : CQAssertion (Store Var) d → CQAssertion (Store Var) d)
    (b : Store Var → Prop) [DecidablePred b]
    (n : ℕ) (Θ : CQAssertion (Store Var) d) (σ : Store Var) :
    ((whileRecWP body b (n + 1) Θ) σ).1.1 =
      if b σ then ((body (whileRecWP body b n Θ)) σ).1.1
      else (Θ σ).1.1 := by
  simp only [whileRecWP]
  by_cases h : b σ <;> simp [h]
end

namespace QuantumComputation.Specs.GroverSolution.FindAny

open Operator ResourceCounting Real QProg.Notation
open Matrix (star_eq_conjTranspose conjTranspose_apply mulVec_single_one conjTranspose_mul
  mulVec_diagonal mulVec_mulVec mul_diagonal smul_mulVec mulVec_smul mulVec_add add_mulVec
  one_mulVec col_apply diagonal)
open Complex (ofReal_sum normSq)
open Finset (sum_add_distrib sum_sub_distrib sum_ite_mem univ_inter sum_const mul_sum)
open QRegister (basisBits_extractIndex tensorState)
open OracleDynamicCircuit (compile)
open QProg (measureRegister qAssign)
open CostModel (ofEmbeddedOracle)
open List (prod_cons finRange map_cons)
open Fintype (card_fin)
open Pi (single)
open Nat (clog)
open _root_.Grover (diffuserUnitary diffuserMatrix)
open scoped NNReal NNRat Matrix ENNReal ComplexOrder MatrixOrder QHLExpectation

@[expose] public section

/-- Claimed dyadic grid cells `(m, k)` for `groverFindAny`. -/
def cells (m k : ℕ) : Bool :=
  gridCells m k

theorem cells_nonempty : ∃ m k, cells m k = true :=
  gridCells_nonempty

theorem cells_mem_grid {m k : ℕ} (hmk : cells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid :=
  gridCells_mem_grid hmk

/-- Total qubits used by `FindAny.circuit`. -/
def qubits (n m _k : ℕ) : ℕ :=
  m * (n + 1)

/-- Claimed asymptotic expected parallel-round cost ratio relative to `vanillaFindAnyCost`
(certified via Mathlib's `Real.pi_gt_d20`, within `2.69 × 10⁻²²` of `1 / 2 + 1 / π`). -/
def relCost (_m _k : ℕ) : ℚ≥0 :=
  257079632679489661923 / 314159265358979323846

end

noncomputable section

abbrev unifVec (q : ℕ) : Fin (2 ^ q) → ℂ := fun _ ↦ (1 / √(2 ^ q : ℝ) : ℂ)

lemma hadamard_mulVec_zero (n m : ℕ) :
    ((addrReg n m).embedUnitary (hadamardUnitary (q := m * n))).1 *ᵥ
      (single 0 1 : Fin (2 ^ (m * (n + 1))) → ℂ) =
      (addrReg n m).tensorState (unifVec (m * n)) (single 0 1) := by
  change (addrReg n m).embedMatrix (hadamardMatrix (m * n)) *ᵥ single 0 1 = _
  rw [(addrReg n m).embedMatrix_mulVec_single_factors,
    show (addrReg n m).extractIndex 0 = 0 from (basisBits (m * n)).injective
      (funext fun _ ↦ by
        rw [basisBits_extractIndex]
        simp [basisBits_eq_div_mod]),
    show ((addrReg n m).basisSplitEquiv 0).2 = 0 from
      funext fun _ ↦ by simp [basisBits_eq_div_mod]]
  congr 1
  funext u
  rw [mulVec_single_one, col_apply, hadamardMatrix_apply_zero]

lemma sum_normSq_unifVec (q : ℕ) :
    (∑ u : Fin (2 ^ q), normSq (unifVec q u)) = 1 := by
  dsimp only [unifVec]
  rw [sum_const, Finset.card_univ, card_fin, nsmul_eq_mul, map_div₀, map_one,
    Complex.normSq_ofReal, mul_self_sqrt (by positivity)]
  push_cast
  exact mul_one_div_cancel (by positivity)

def markReadout {Var : Type} (res : Var) (n m : ℕ) (hm : 1 ≤ m) :
    OracleCirc Var (m * (n + 1)) ((n + 1) * m) :=
  .seq (.oracle (fullReg n m)) (qMap res (decOut n m hm))

lemma wp_markReadout {Var : Type} [DecidableEq Var] (res : Var) {n m : ℕ} (hm : 1 ≤ m)
    (S : Finset (Fin (2 ^ n))) (g : ℤ → ℂ) (Φ : CQAssertion (Store Var) (2 ^ (m * (n + 1))))
    (hΦ_eq : ∀ τ, (Φ τ).1.1 = g (τ res) • (1 : Operator (2 ^ (m * (n + 1)))))
    (τ : Store Var) :
    ((wp ((markReadout res n m hm).compile qAssign (groverParallelMarkingOracle m S)) Φ) τ).1.1 =
      postDiag hm S g := by
  let Q := m * (n + 1)
  let oracle := groverParallelMarkingOracle m S
  let mC' := (qMap res (W := (n + 1) * m) (decOut n m hm)).compile qAssign oracle
  let O := (fullReg n m).embedUnitary oracle
  let dg := diagonal fun o : Fin (2 ^ Q) ↦ g ((decOut n m hm o).val : ℤ)
  unfold markReadout
  dsimp only [compile]
  rw [wp_qSeq, wp_qAssign, qhlQAssign_val, show ((wp mC' Φ) τ).1.1 = dg by
    dsimp only [mC', dg]
    rw [wp_qMap res (decOut n m hm) oracle (fun z ↦ g z • (1 : Operator (2 ^ Q))) Φ hΦ_eq τ]
    simp]
  have hO (l : List (Fin m)) (z : Fin (2 ^ Q)) :
      ((l.map fun i ↦ (slotReg n m i).embedMatrix (groverSetMarkingOracle S).1).prod) *ᵥ
        single z (1 : ℂ) = single (appPerms l (markPerm S) z) 1 := by
    induction l with
    | nil => exact one_mulVec _
    | cons i l ih =>
      rw [map_cons, prod_cons, ← mulVec_mulVec, ih,
        (slotReg n m i).embedMatrix_mulVec_single_factors, groverSetMarkingOracle,
        permutationUnitary_mulVec_single, (slotReg n m i).tensorState_single_replaceIndex]
      rfl
  have hdg (c : Fin (2 ^ Q) → ℂ) (x : Fin (2 ^ Q)) :
      diagonal c *ᵥ single x (1 : ℂ) = c x • single x 1 := funext fun y ↦ by
    by_cases h : y = x <;> simp [mulVec_diagonal, h]
  refine Matrix.ext_of_mulVec_single fun j ↦ ?_
  have hOj := (congrArg (· *ᵥ single j (1 : ℂ))
    (fullReg_embedUnitary_groverParallelMarkingOracle S)).trans (hO (finRange m) j)
  dsimp only [dg, postDiag]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hOj, hdg, mulVec_smul, ← hOj, mulVec_mulVec,
    ← star_eq_conjTranspose, O.2.1, one_mulVec, hdg]

def naiveTrial {Var : Type} (res : Var) (n m : ℕ) (hm : 1 ≤ m) :
    OracleCirc Var (m * (n + 1)) ((n + 1) * m) :=
  .seq (qMap res (fun _ ↦ 0))
    (.seq (.step (phaseTag ((addrReg n m).embedUnitary (hadamardUnitary (q := m * n)))))
      (markReadout res n m hm))

lemma wp_naiveTrial {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hm : 1 ≤ m)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) (g : ℤ → ℂ) (a b : ℂ)
    (Φ : CQAssertion (Store Var) (2 ^ (m * (n + 1))))
    (hΦ_eq : ∀ τ, (Φ τ).1.1 = g (τ res) • (1 : Operator (2 ^ (m * (n + 1)))))
    (hg_s : ∀ x ∈ S, g (x.val : ℤ) = a) (hg_f : g (2 ^ n : ℤ) = b) (σ : Store Var) :
    ((wp ((naiveTrial res n m hm).compile qAssign (groverParallelMarkingOracle m S)) Φ) σ).1.1 =
      (a * (oddFrac n m k : ℂ) + b * (1 - (oddFrac n m k : ℂ))) •
        (1 : Operator (2 ^ (m * (n + 1)))) := by
  let Q := m * (n + 1)
  let oracle := groverParallelMarkingOracle m S
  let H := ((addrReg n m).embedUnitary (hadamardUnitary (q := m * n))).1
  unfold naiveTrial
  dsimp only [compile]
  rw [wp_qSeq, wp_qSeq, wp_qMap res (fun _ ↦ 0) oracle
    (fun _ ↦ Hᴴ * postDiag hm S g * H) _ (fun τ ↦ by
      rw [wp_qAssign, wp_phaseTag, qhlQAssign_val,
        wp_markReadout res hm S g Φ hΦ_eq]) σ,
    ← Matrix.smul_one_eq_diagonal]
  congr 1
  rw [sum_decOut_zero hm S g a b hg_s hg_f H (unifVec (m * n)) (hadamard_mulVec_zero n m),
    sum_normSq_unifVec]
  have hmark : (∑ u ∈ oddSet n m S, normSq (unifVec (m * n) u)) = oddFrac n m k := by
    dsimp only [unifVec]
    rw [sum_const, nsmul_eq_mul, map_div₀, map_one, Complex.normSq_ofReal,
      mul_self_sqrt (by positivity), ← div_eq_mul_one_div, card_oddSet_div_two_pow,
      (Finset.mem_powersetCard.mp hS).2]
  rw [hmark]
  push_cast
  ring

lemma oddFrac_bounds {n m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hk_lt : k < 2 ^ n) :
    0 < oddFrac n m k ∧ oddFrac n m k ≤ 1 := by
  unfold oddFrac
  have hdp : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  set r : ℝ := 1 - 2 * (k : ℝ) / (2 ^ n : ℝ)
  have hra : |r| < 1 := abs_lt.mpr ⟨by
      dsimp [r]
      linarith [(div_lt_iff₀ hdp).mpr
        (by exact_mod_cast (by omega : 2 * k < 2 * 2 ^ n) : 2 * (k : ℝ) < 2 * (2 ^ n : ℝ))],
    by
      dsimp [r]
      linarith [div_pos (by exact_mod_cast (by omega : 0 < 2 * k) : (0 : ℝ) < 2 * k) hdp]⟩
  have hpow := abs_lt.mp ((abs_pow r m).trans_lt (pow_lt_one₀ (abs_nonneg r) hra (by omega)))
  exact ⟨by linarith [hpow.2], by linarith [hpow.1]⟩

/-! ## Stationary Eigenvector-Locking Schedule and Trigonometric Bounds -/

def halfAngle (n m k : ℕ) : ℝ := arcsin (sqrt (oddFrac n m k))

def lockSchedule (n m k : ℕ) : ℕ :=
  ⌊π / 8 / sqrt (oddFrac n m k)⌋₊

def nonTargetRatio (n m k : ℕ) : ℝ :=
  cos ((2 * (lockSchedule n m k : ℝ) + 3) * halfAngle n m k) /
    cos ((2 * (lockSchedule n m k : ℝ) + 1) * halfAngle n m k)

def targetRatio (n m k : ℕ) : ℝ :=
  nonTargetRatio n m k * sin ((2 * (lockSchedule n m k : ℝ) + 1) * halfAngle n m k) /
    sin ((2 * (lockSchedule n m k : ℝ) + 3) * halfAngle n m k)

def clampedRatio (n m k : ℕ) : ℝ :=
  max 0 (min 1 (targetRatio n m k))

def lockFailureProb (n m k : ℕ) : ℝ :=
  nonTargetRatio n m k ^ 2

lemma cos_sub_sq_sub_cos_add_sq (x y : ℝ) :
    cos (x - y) ^ 2 - cos (x + y) ^ 2 = sin (2 * x) * sin (2 * y) := by
  rw [cos_sub, cos_add, sin_two_mul, sin_two_mul]
  ring

lemma arcsin_le_add_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) : arcsin x ≤ x + x ^ 2 := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have h3 : x * (1 + x) ^ 3 ≤ 2 := by
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x) (by linarith : 1 + x ≤ 3 / 2) 3]
  rw [arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
    ⟨by nlinarith [pi_gt_three], by nlinarith [pi_gt_three]⟩]
  nlinarith [sin_gt_sub_cube (by positivity : 0 < x + x ^ 2),
    mul_le_mul_of_nonneg_left h3 (sq_nonneg x)]

lemma cos_sq_sub_cos_sq_halfAngle (n m k : ℕ) :
    let K := lockSchedule n m k
    let θ := halfAngle n m k
    cos ((2 * (K : ℝ) + 1) * θ) ^ 2 - cos ((2 * (K : ℝ) + 3) * θ) ^ 2 =
      2 * sin θ * cos θ * sin ((4 * (K : ℝ) + 4) * θ) := by
  intro K θ
  rw [← sin_two_mul, mul_comm (sin _)]
  convert cos_sub_sq_sub_cos_add_sq ((2 * (K : ℝ) + 2) * θ) θ using 3 <;> ring_nf

lemma asymp_schedule_bds {n m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hn : 150 + clog 2 m + clog 2 k ≤ n) :
    k ≠ 2 ^ n ∧
      clampedRatio n m k = targetRatio n m k ∧
      0 ≤ lockFailureProb n m k ∧
      lockFailureProb n m k < 1 ∧
      sin ((2 * (lockSchedule n m k : ℝ) + 3) * halfAngle n m k) ≠ 0 ∧
      cos ((2 * (lockSchedule n m k : ℝ) + 1) * halfAngle n m k) ≠ 0 ∧
      ((lockSchedule n m k : ℝ) + 1 + (1 - lockFailureProb n m k)⁻¹ + 1) ≤
        (π / 8 + 1 / 4) * √((2 ^ n : ℝ) / ((m : ℝ) * (k : ℝ))) + 5 := by
  have h150 : 2 ^ 150 * (m * k) ≤ 2 ^ n := (Nat.mul_le_mul_left (2 ^ 150) (Nat.mul_le_mul
    (Nat.le_pow_clog (by omega : 1 < 2) m) (Nat.le_pow_clog (by omega : 1 < 2) k))).trans
    ((by rw [← mul_assoc, ← Nat.pow_add, ← Nat.pow_add] : 2 ^ 150 * (2 ^ clog 2 m *
      2 ^ clog 2 k) = 2 ^ (150 + clog 2 m + clog 2 k)).le.trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn))
  have hkN2 : 2 * k ≤ 2 ^ n := by
    have : k ≤ m * k := Nat.le_mul_of_pos_left k hm
    omega
  set pO : ℝ := oddFrac n m k
  set R : ℝ := (2 ^ n : ℝ) / ((m : ℝ) * (k : ℝ))
  have hrg : (2 : ℝ) ^ 150 ≤ R := (le_div_iff₀ (by positivity)).mpr (by exact_mod_cast h150)
  have hrp : 0 < R := by linarith only [hrg]
  set x0 : ℝ := 2 * (k : ℝ) / (2 ^ n : ℝ)
  have hx1 : x0 ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hkN2)
  have hbn (r : ℕ) : 1 - (r : ℝ) * x0 ≤ (1 - x0) ^ r ∧
      (1 - x0) ^ r ≤ 1 - (r : ℝ) * x0 + (r : ℝ) ^ 2 * x0 ^ 2 := by
    induction r with
    | zero => simp
    | succ r ih =>
      have h1x : 0 ≤ 1 - x0 := by linarith
      refine ⟨by
          rw [pow_succ]
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right ih.1 h1x], by
          rw [pow_succ]
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right ih.2 h1x, sq_nonneg x0,
            show (0 : ℝ) ≤ (r : ℝ) ^ 2 * x0 ^ 3 by positivity]⟩
  obtain ⟨hlo, hhi⟩ := hbn m
  have hpd : pO = (1 - (1 - x0) ^ m) / 2 := rfl
  have hxR : (m : ℝ) * x0 / 2 = 1 / R := by
    dsimp only [x0, R]
    rw [one_div_div]
    ring
  have hpl : pO * R ≤ 1 := by
    rw [← le_div_iff₀ hrp]
    linarith only [hlo, hpd, hxR]
  have h1 : (1 / R) * (1 - 2 * (1 / R)) ≤ pO := by
    linarith only [hhi, hpd, show (1 / R) * (1 - 2 * (1 / R)) =
        (1 - (1 - (m : ℝ) * x0 + (m : ℝ) ^ 2 * x0 ^ 2)) / 2 by
      rw [← hxR]
      ring]
  have hpg : 1 - 1 / 2 ^ 149 ≤ pO * R := by
    have h2 : (1 / R) * (1 - 1 / 2 ^ 149) ≤ pO :=
      (mul_le_mul_of_nonneg_left (by
        linarith only [show 2 * (1 / R) ≤ 1 / 2 ^ 149 by
          rw [mul_one_div, div_le_iff₀ hrp]
          linarith only [hrg]]) (by positivity)).trans h1
    linarith only [mul_le_mul_of_nonneg_right h2 hrp.le, one_div_mul_cancel hrp.ne',
      show 1 / R * (1 - 1 / 2 ^ 149) * R = (1 / R * R) * (1 - 1 / 2 ^ 149) by ring]
  have hpo : 0 < pO := pos_of_mul_pos_left (by linarith only [hpg] : 0 < pO * R) hrp.le
  set c : ℝ := pO⁻¹
  have hcp : 0 < c := inv_pos.mpr hpo
  have hcr : c * (pO * R) = R := by linear_combination R * inv_mul_cancel₀ hpo.ne'
  have hcg : R ≤ c := by linarith only [mul_le_mul_of_nonneg_left hpl hcp.le, hcr]
  have hqr : (2 : ℝ) ^ 75 ≤ √R := by
    rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 75)]
    exact sqrt_le_sqrt (by linarith only [hrg])
  have hc_ub : c ≤ (√R + 1) ^ 2 := by
    have hR_poly : R ^ 2 ≤ (R - 2) * (√R + 1) ^ 2 := by
      have hid : (R - 2) * (√R + 1) ^ 2 - R ^ 2 =
          (R - 2) * (√R ^ 2 - R) + 2 * (R - 2) * (√R - 1) + (R - 6) := by ring
      rw [sq_sqrt hrp.le, sub_self, mul_zero, zero_add] at hid
      have hpos : 0 ≤ (R - 2) * (√R - 1) :=
        mul_nonneg (by linarith only [hrg]) (by linarith only [hqr])
      linarith only [hid, hpos, hrg]
    have hR2_id : R ^ 2 * ((1 / R) * (1 - 2 * (1 / R))) = R - 2 := by
      linear_combination (R * (1 - 2 * (1 / R)) - 2) * mul_one_div_cancel hrp.ne'
    have hR2_pO : R ^ 2 ≤ R ^ 2 * (pO * (√R + 1) ^ 2) := by
      calc R ^ 2 ≤ (R - 2) * (√R + 1) ^ 2 := hR_poly
        _ = R ^ 2 * (1 / R * (1 - 2 * (1 / R)) * (√R + 1) ^ 2) := by
          rw [← hR2_id, mul_assoc]
        _ ≤ R ^ 2 * (pO * (√R + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h1 (sq_nonneg (√R + 1))) (sq_nonneg R)
    have h1_pO : 1 ≤ pO * (√R + 1) ^ 2 :=
      le_of_mul_le_mul_left (by rwa [mul_one]) (pow_pos hrp 2)
    have hc_mul : c * (pO * (√R + 1) ^ 2) = (√R + 1) ^ 2 := by
      linear_combination (√R + 1) ^ 2 * inv_mul_cancel₀ hpo.ne'
    linarith only [mul_le_mul_of_nonneg_left h1_pO hcp.le, hc_mul]
  set s : ℝ := 1 / √pO
  have hsc : s = √c := by
    dsimp [s, c]
    rw [sqrt_inv, one_div]
  have hs_ub : s ≤ √R + 1 := by
    have hq := sqrt_le_sqrt hc_ub
    rwa [← hsc, sqrt_sq (by linarith only [hqr])] at hq
  have hsR : √R ≤ s := hsc ▸ sqrt_le_sqrt hcg
  have hs16 : 16 ≤ s := by linarith only [hqr, hsR]
  have hs_pos : 0 < s := by linarith only [hs16]
  set θ : ℝ := halfAngle n m k
  set x : ℝ := 1 / s
  have hsx : s * x = 1 := mul_one_div_cancel hs_pos.ne'
  have hsx2 : s * x ^ 2 = x := by rw [sq, ← mul_assoc, hsx, one_mul]
  have hx0 : 0 < x := by positivity
  have hx16 : x ≤ 1 / 16 := one_div_le_one_div_of_le (by norm_num) hs16
  have hθ_eq : θ = arcsin x := by
    dsimp [θ, halfAngle, x, s]
    rw [one_div_one_div]
  have hsin_θ : sin θ = x := by
    rw [hθ_eq, sin_arcsin (by linarith) (by linarith)]
  have hsin_pos : 0 < sin θ := hsin_θ ▸ hx0
  have hxx : x ^ 2 ≤ x / 16 := by
    rw [sq, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hx16 hx0.le
  have hθl : x ≤ θ := by
    rw [hθ_eq]
    exact self_le_arcsin hx0.le (by linarith)
  have hθu : θ ≤ x + x ^ 2 := by
    rw [hθ_eq]
    exact arcsin_le_add_sq hx0.le (by linarith)
  set K : ℕ := lockSchedule n m k
  have hK_eq : K = ⌊π / 8 * s⌋₊ := by
    dsimp [K, lockSchedule, s, pO]
    rw [mul_one_div]
  have hk1 : (K : ℝ) ≤ π / 8 * s := hK_eq ▸ Nat.floor_le (by positivity)
  have hk2 : π / 8 * s < (K : ℝ) + 1 := hK_eq ▸ Nat.lt_floor_add_one _
  set kr : ℝ := (K : ℝ)
  have hk0 : 0 ≤ kr := Nat.cast_nonneg _
  have hθ0 : 0 < θ := hx0.trans_le hθl
  have hθ2 : θ ≤ 2 * x := by linarith
  have hπ := pi_gt_three
  have hπ' := pi_lt_d2
  have hπsx : π * (s * x) = π := by rw [hsx, mul_one]
  have hπsx2 : π * (s * x ^ 2) = π * x := by rw [hsx2]
  have hφ1 : π / 2 ≤ (4 * kr + 4) * θ := by
    linarith [mul_le_mul_of_nonneg_left hθl (by positivity : (0 : ℝ) ≤ π / 8 * s),
      mul_le_mul_of_nonneg_right hk2.le hθ0.le]
  have hφ2 : (4 * kr + 4) * θ ≤ π / 2 + 6 * x := by
    linarith [mul_le_mul_of_nonneg_left hθu (by linarith : (0 : ℝ) ≤ 4 * kr + 4),
      mul_le_mul_of_nonneg_right hk1 (by positivity : (0 : ℝ) ≤ x + x ^ 2),
      mul_le_mul_of_nonneg_right hπ'.le hx0.le]
  have hcos_θ : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : 0 < sin ((2 * kr + 1) * θ) :=
    sin_pos_of_pos_of_lt_pi (mul_pos (by linarith) hθ0) (by linarith)
  have hc1 : 0 < cos ((2 * kr + 1) * θ) :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc2 : 0 ≤ cos ((2 * kr + 2) * θ) :=
    cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hc3 : 0 < cos ((2 * kr + 3) * θ) :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs3 : sin ((2 * kr + 1) * θ) ≤ sin ((2 * kr + 3) * θ) := by
    have htrig := sin_sub_sin ((2 * kr + 3) * θ) ((2 * kr + 1) * θ)
    rw [show ((2 * kr + 3) * θ - (2 * kr + 1) * θ) / 2 = θ by ring,
      show ((2 * kr + 3) * θ + (2 * kr + 1) * θ) / 2 = (2 * kr + 2) * θ by ring] at htrig
    have hpos : 0 ≤ 2 * sin θ * cos ((2 * kr + 2) * θ) :=
      mul_nonneg (mul_nonneg (by norm_num) hsin_pos.le) hc2
    linarith
  have hs3_pos : 0 < sin ((2 * kr + 3) * θ) := hs1.trans_le hs3
  have hs4 : 0 < sin ((4 * kr + 4) * θ) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcdiff : cos ((2 * kr + 1) * θ) ^ 2 - cos ((2 * kr + 3) * θ) ^ 2 =
      2 * (1 / s) * cos θ * sin ((4 * kr + 4) * θ) := by
    rw [show (1 / s : ℝ) = sin θ from hsin_θ.symm]
    exact cos_sq_sub_cos_sq_halfAngle n m k
  have hatt0 : 0 < nonTargetRatio n m k := div_pos hc3 hc1
  have hatt1 : nonTargetRatio n m k < 1 := (div_lt_one hc1).2 <|
    lt_of_pow_lt_pow_left₀ 2 hc1.le <| by
      linarith [hcdiff, mul_pos (mul_pos hx0 hcos_θ) hs4]
  have htr0 : 0 < targetRatio n m k := div_pos (mul_pos hatt0 hs1) hs3_pos
  have htr1 : targetRatio n m k < 1 :=
    (div_lt_one hs3_pos).2 ((mul_lt_of_lt_one_left hs1 hatt1).trans_le hs3)
  have hclamp : clampedRatio n m k = targetRatio n m k := by
    unfold clampedRatio
    rw [min_eq_right htr1.le, max_eq_right htr0.le]
  have hq0 : 0 ≤ lockFailureProb n m k := sq_nonneg _
  have hq1 : lockFailureProb n m k < 1 := pow_lt_one₀ hatt0.le hatt1 two_ne_zero
  have hC : cos ((2 * kr + 3) * θ) ^ 2 ≤ 1 / 2 := by
    linarith [cos_sq ((2 * kr + 3) * θ), cos_nonpos_of_pi_div_two_le_of_le
      (x := 2 * ((2 * kr + 3) * θ)) (by linarith) (by linarith)]
  have hcθ : 1 - 2 * x ^ 2 ≤ cos θ := by
    linarith [one_sub_sq_div_two_le_cos (x := θ), pow_le_pow_left₀ hθ0.le hθ2 2]
  have hsφ : 1 - 18 * x ^ 2 ≤ sin ((4 * kr + 4) * θ) := by
    have h := one_sub_sq_div_two_le_cos (x := (4 * kr + 4) * θ - π / 2)
    rw [cos_sub_pi_div_two] at h
    linarith [pow_le_pow_left₀ (by linarith : 0 ≤ (4 * kr + 4) * θ - π / 2)
      (by linarith : (4 * kr + 4) * θ - π / 2 ≤ 6 * x) 2]
  have hP : 2 * (1 - 20 * x ^ 2) ≤ 2 * cos θ * sin ((4 * kr + 4) * θ) := by
    linarith [mul_le_mul hcθ hsφ (by linarith) hcos_θ.le, pow_nonneg hx0.le 4]
  have hPpos : 0 < 2 * cos θ * sin ((4 * kr + 4) * θ) := by positivity
  have hc1_sq : cos ((2 * kr + 1) * θ) ^ 2 ≠ 0 := pow_ne_zero 2 hc1.ne'
  have hden_pos : 0 < 2 * (1 / s) * cos θ * sin ((4 * kr + 4) * θ) := by positivity
  have hinv : (1 - lockFailureProb n m k)⁻¹ =
      1 + cos ((2 * kr + 3) * θ) ^ 2 /
        (2 * cos θ * sin ((4 * kr + 4) * θ)) * s := by
    have hq_def : lockFailureProb n m k =
        cos ((2 * kr + 3) * θ) ^ 2 / cos ((2 * kr + 1) * θ) ^ 2 := by
      rw [lockFailureProb, nonTargetRatio, div_pow]
    rw [hq_def, one_sub_div hc1_sq, inv_div, hcdiff,
      show cos ((2 * kr + 1) * θ) ^ 2 =
        2 * (1 / s) * cos θ * sin ((4 * kr + 4) * θ) + cos ((2 * kr + 3) * θ) ^ 2 by
        linarith [hcdiff],
      add_div, div_self hden_pos.ne']
    congr 1
    rw [show 2 * (1 / s) * cos θ * sin ((4 * kr + 4) * θ) =
        (2 * cos θ * sin ((4 * kr + 4) * θ)) / s by ring,
      div_div_eq_mul_div, div_mul_eq_mul_div]
  have hfrac : cos ((2 * kr + 3) * θ) ^ 2 /
      (2 * cos θ * sin ((4 * kr + 4) * θ)) * s ≤ s / 4 + 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hPpos]
    linarith [mul_le_mul_of_nonneg_right hC hs_pos.le,
      mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ s / 4 + 1)]
  have htot1 : kr + 1 + (1 - lockFailureProb n m k)⁻¹ + 1 ≤
      (π / 8 + 1 / 4) * s + 4 := by
    linarith [hk1, hinv, hfrac]
  have htot2 : (π / 8 + 1 / 4) * s + 4 ≤ (π / 8 + 1 / 4) * √R + 5 := by
    have h0 := mul_le_mul_of_nonneg_left hs_ub (by linarith only [hπ] : (0 : ℝ) ≤ π / 8 + 1 / 4)
    linarith only [h0, pi_lt_four]
  exact ⟨by omega, hclamp, hq0, hq1, hs3_pos.ne', hc1.ne', htot1.trans htot2⟩

/-! ## Parameterized Flag-Chord Unitary and Stationary Loop Step -/

def chordU (n m k : ℕ) : ℝ := sqrt ((1 + clampedRatio n m k) / 2)

def chordV (n m k : ℕ) : ℝ := sqrt ((1 - clampedRatio n m k) / 2)

lemma clampedRatio_bds (n m k : ℕ) : 0 ≤ clampedRatio n m k ∧ clampedRatio n m k ≤ 1 := by
  unfold clampedRatio
  exact ⟨le_max_left 0 _, max_le (by norm_num) (min_le_left 1 _)⟩

lemma chordU_sq_add_chordV_sq (n m k : ℕ) :
    chordU n m k ^ 2 + chordV n m k ^ 2 = 1 := by
  obtain ⟨h0, h1⟩ := clampedRatio_bds n m k
  dsimp [chordU, chordV]
  rw [sq_sqrt (by linarith), sq_sqrt (by linarith)]
  ring

lemma chordV_sq_sub_chordU_sq (n m k : ℕ) :
    chordV n m k ^ 2 - chordU n m k ^ 2 = -clampedRatio n m k := by
  obtain ⟨h0, h1⟩ := clampedRatio_bds n m k
  dsimp [chordU, chordV]
  rw [sq_sqrt (by linarith), sq_sqrt (by linarith)]
  ring

lemma two_mul_chordU_mul_chordV_sq (n m k : ℕ) :
    (2 * chordU n m k * chordV n m k) ^ 2 = 1 - clampedRatio n m k ^ 2 := by
  obtain ⟨h0, h1⟩ := clampedRatio_bds n m k
  rw [show (2 * chordU n m k * chordV n m k) ^ 2 =
      4 * chordU n m k ^ 2 * chordV n m k ^ 2 by ring]
  dsimp [chordU, chordV]
  rw [sq_sqrt (by linarith), sq_sqrt (by linarith)]
  ring

def flag0ZMat (n m : ℕ) (hm : 1 ≤ m) : Operator (2 ^ (m * (n + 1))) :=
  diagonal fun z ↦ if slotFlag n m z ⟨0, hm⟩ = 0 then (1 : ℂ) else -1

def flipMat (n m : ℕ) : Operator (2 ^ (m * (n + 1))) := (permutationUnitary (flipPerm n m)).1

def chordMat (n m k : ℕ) (hm : 1 ≤ m) : Operator (2 ^ (m * (n + 1))) :=
  (chordU n m k : ℂ) • flag0ZMat n m hm + (chordV n m k : ℂ) • flipMat n m

def chordUnitary (n m k : ℕ) (hm : 1 ≤ m) : Unitary (2 ^ (m * (n + 1))) := by
  refine ⟨chordMat n m k hm, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
  unfold chordMat
  set Z := flag0ZMat n m hm
  set X := flipMat n m
  set u := chordU n m k
  set v := chordV n m k
  have hZc : Zᴴ = Z := by
    dsimp only [Z, flag0ZMat]
    rw [Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun z ↦ by
      by_cases h : slotFlag n m z ⟨0, hm⟩ = 0 <;> simp [h])
  have hZX : Z * X + X * Z = 0 := by
    ext i j
    simp only [Z, X, flag0ZMat, flipMat, Matrix.add_apply, Matrix.diagonal_mul, mul_diagonal,
      Matrix.zero_apply, permutationUnitary_apply]
    by_cases hij : i = flipPerm n m j
    · subst hij
      have h0 : ∀ b : Fin (2 ^ 1), b = 0 ↔ basisBits 1 b 0 = 0 := by decide
      have hf : slotFlag n m (flipPerm n m j) ⟨0, hm⟩ = 0 ↔ slotFlag n m j ⟨0, hm⟩ ≠ 0 := by
        rw [h0, Ne, h0, basisBits_slotFlag, basisBits_slotFlag, basisSplitEquiv_flipPerm]
        exact (by decide : ∀ x : ZMod 2, x + 1 = 0 ↔ x ≠ 0) _
      by_cases h : slotFlag n m j ⟨0, hm⟩ = 0 <;> simp [hf, h]
    · simp [hij]
  have hXc : Xᴴ = X := by
    ext i j
    simp only [X, flipMat, conjTranspose_apply, permutationUnitary_apply]
    by_cases h : i = flipPerm n m j
    · rw [ite_eq_left (by rw [h, flipPerm_involutive n m j]), ite_eq_left h, star_one]
    · rw [ite_eq_right fun h' ↦ h (by rw [h', flipPerm_involutive n m i]), ite_eq_right h,
        star_zero]
  have hZ2 : Z * Z = 1 := by
    dsimp only [Z, flag0ZMat]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg diagonal (funext fun _ ↦ by split_ifs <;> ring)
  have hX2 : X * X = 1 := by
    nth_rw 1 [← hXc]
    rw [← star_eq_conjTranspose]
    exact (permutationUnitary (flipPerm n m)).2.1
  have hsq : ((u : ℂ) • Z + (v : ℂ) • X) * ((u : ℂ) • Z + (v : ℂ) • X) =
      ((u : ℂ) * u + (v : ℂ) * v) • 1 + ((u : ℂ) * v) • (Z * X + X * Z) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hZ2,
      hX2, add_smul, smul_add, mul_comm (v : ℂ) (u : ℂ)]
    abel
  have huv : (u : ℂ) * u + (v : ℂ) * v = 1 := by
    exact_mod_cast (by linear_combination chordU_sq_add_chordV_sq n m k : u * u + v * v = 1)
  rw [show ((u : ℂ) • Z + (v : ℂ) • X)ᴴ = (u : ℂ) • Z + (v : ℂ) • X by
      simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hZc, hXc],
    hsq, hZX, smul_zero, add_zero, huv, one_smul]

abbrev pinHitOp (n m k : ℕ) {q : ℕ} (M : Finset (Fin (2 ^ q)))
    (w : Fin (2 ^ q) → ℂ) (x : Fin (2 ^ q)) : ℂ :=
  if x ∈ M then ((-2 * chordU n m k * chordV n m k : ℝ) : ℂ) * w x else 0

abbrev pinMissOp (n m k : ℕ) {q : ℕ} (M : Finset (Fin (2 ^ q)))
    (w : Fin (2 ^ q) → ℂ) (x : Fin (2 ^ q)) : ℂ :=
  if x ∈ M then ((chordV n m k ^ 2 - chordU n m k ^ 2 : ℝ) : ℂ) * w x else w x

def parityMat (n m k : ℕ) (hm : 1 ≤ m) (S : Finset (Fin (2 ^ n))) :
    Operator (2 ^ (m * (n + 1))) :=
  chordMat n m k hm * sDiagM n m S * chordMat n m k hm

lemma ora_mVec {q : ℕ} (M : Finset (Fin (2 ^ q))) (v : Fin (2 ^ q) → ℂ) (i : Fin (2 ^ q)) :
    (oracleMat M *ᵥ v) i = if i ∈ M then -v i else v i := by
  rw [oracleMat, mulVec_diagonal]
  split_ifs <;> ring

lemma parityMat_mulVec_tensorState {n m k : ℕ} (hm : 1 ≤ m) (S : Finset (Fin (2 ^ n)))
    (w : Fin (2 ^ (m * n)) → ℂ) :
    parityMat n m k hm S *ᵥ (addrReg n m).tensorState w (single 0 1) =
      (addrReg n m).tensorState (pinMissOp n m k (oddSet n m S) w) (single 0 1) +
        (addrReg n m).tensorState (pinHitOp n m k (oddSet n m S) w) (single 1 1) := by
  unfold parityMat
  have hch (v : Fin (2 ^ (m * n)) → ℂ) (e : (addrReg n m).Environment → ZMod 2) (b : Fin (2 ^ 1))
      (hs : ∀ z, ((addrReg n m).basisSplitEquiv z).2 = e → slotFlag n m z ⟨0, hm⟩ = b) :
      chordMat n m k hm *ᵥ (addrReg n m).tensorState v (single e 1) =
        (addrReg n m).tensorState (((chordU n m k : ℂ) * if b = 0 then 1 else -1) • v)
          (single e 1) +
          (addrReg n m).tensorState ((chordV n m k : ℂ) • v) (single (e + 1) 1) := by
    let s : ℂ := if b = 0 then 1 else -1
    rw [chordMat, add_mulVec, smul_mulVec, smul_mulVec, flag0ZMat,
      diagonal_mulVec_tensorState _ (fun _ ↦ s) v e fun z hz ↦ by
        dsimp only [s]
        rw [hs z hz],
      show (fun u ↦ s * v u) = s • v from rfl,
      flipMat, permutationUnitary_flipPerm_mulVec_tensorState v e,
      ← (addrReg n m).tensorState_smul_left, ← (addrReg n m).tensorState_smul_left, smul_smul]
  have hs0 := fun z hE ↦ slotFlag_eq_zero (n := n) z hE ⟨0, hm⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, hch w 0 0 hs0, ite_eq_left rfl, mul_one, zero_add,
    mulVec_add, sDiagM_mulVec_tensorState_zero S ((chordU n m k : ℂ) • w),
    sDiagM_mulVec_tensorState_one S ((chordV n m k : ℂ) • w), mulVec_add,
    hch _ 0 0 hs0, ite_eq_left rfl, zero_add,
    hch _ 1 1 fun z hE ↦ slotFlag_eq_one z hE ⟨0, hm⟩,
    ite_eq_right (by decide : (1 : Fin (2 ^ 1)) ≠ 0), addrEnv_one_add_one]
  have huv : (chordU n m k : ℂ) ^ 2 + (chordV n m k : ℂ) ^ 2 = 1 := by
    exact_mod_cast chordU_sq_add_chordV_sq n m k
  funext z
  simp only [Pi.add_apply, tensorState, Pi.smul_apply, mulVec_smul, smul_eq_mul, ora_mVec,
    pinMissOp, pinHitOp]
  split_ifs
  · push_cast
    ring
  · linear_combination
      w ((addrReg n m).extractIndex z) *
        (single 0 1 : ((addrReg n m).Environment → ZMod 2) → ℂ)
          ((addrReg n m).basisSplitEquiv z).2 * huv

def groverIter {Var : Type} (n m : ℕ) : ℕ → OracleCirc Var (m * (n + 1)) ((n + 1) * m)
  | 0 => .skip
  | K + 1 =>
    .seq (groverIter n m K) (.seq (phaseStep n m) (.step (phaseTag ((addrReg n m).embedUnitary
      (diffuserUnitary (n := m * n))))))

def iterVec {q : ℕ} (M : Finset (Fin (2 ^ q))) : ℕ → (Fin (2 ^ q) → ℂ) → (Fin (2 ^ q) → ℂ)
  | 0, v => v
  | K + 1, v => diffuserMatrix *ᵥ oracleMat M *ᵥ iterVec M K v

def iterMat (n m : ℕ) (S : Finset (Fin (2 ^ n))) : ℕ → Operator (2 ^ (m * (n + 1)))
  | 0 => 1
  | K + 1 =>
    ((addrReg n m).embedUnitary (diffuserUnitary (n := m * n))).1 * sDiagM n m S *
      iterMat n m S K

lemma iMat_tens {n m : ℕ} (S : Finset (Fin (2 ^ n))) (K : ℕ) (v : Fin (2 ^ (m * n)) → ℂ) :
    iterMat n m S K *ᵥ (addrReg n m).tensorState v (single 0 1) =
      (addrReg n m).tensorState (iterVec (oddSet n m S) K v) (single 0 1) := by
  induction K with
  | zero =>
    unfold iterMat iterVec
    simp
  | succ K ih =>
    dsimp only [iterMat, iterVec]
    rw [← mulVec_mulVec, ih, ← mulVec_mulVec, sDiagM_mulVec_tensorState_zero S]
    exact (addrReg n m).embedMatrix_mulVec_tensorState diffuserMatrix _ (single 0 1)

def initState (n m k : ℕ) (S : Finset (Fin (2 ^ n))) : Fin (2 ^ (m * n)) → ℂ :=
  iterVec (oddSet n m S) (lockSchedule n m k + 1) (unifVec (m * n))

def loopState (n m k : ℕ) (S : Finset (Fin (2 ^ n))) : ℕ → Fin (2 ^ (m * n)) → ℂ
  | 0 => initState n m k S
  | r + 1 => diffuserMatrix *ᵥ pinMissOp n m k (oddSet n m S) (loopState n m k S r)

theorem loopState_norms {n m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hn : 150 + clog 2 m + clog 2 k ≤ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) (r : ℕ) :
    (∑ x ∈ oddSet n m S, normSq (pinHitOp n m k (oddSet n m S) (loopState n m k S r) x)) =
      (1 - lockFailureProb n m k) * lockFailureProb n m k ^ r ∧
    (∑ x : Fin (2 ^ (m * n)), normSq (loopState n m k S r x)) = lockFailureProb n m k ^ r := by
  obtain ⟨hk_ne, hclamp, _, _, hsin3, hcos1, _⟩ := asymp_schedule_bds hm hk hn
  have hkN : k ≤ 2 ^ n := by
    have h150 : 2 ^ 150 * (m * k) ≤ 2 ^ n := (Nat.mul_le_mul_left (2 ^ 150) (Nat.mul_le_mul
      (Nat.le_pow_clog (by omega : 1 < 2) m) (Nat.le_pow_clog (by omega : 1 < 2) k))).trans
      ((by rw [← mul_assoc, ← Nat.pow_add, ← Nat.pow_add] : 2 ^ 150 * (2 ^ clog 2 m *
        2 ^ clog 2 k) = 2 ^ (150 + clog 2 m + clog 2 k)).le.trans
        (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn))
    have : k ≤ m * k := Nat.le_mul_of_pos_left k hm
    omega
  have hk_lt : k < 2 ^ n := Nat.lt_of_le_of_ne hkN hk_ne
  obtain ⟨hp0, hp1⟩ := oddFrac_bounds hm hk hk_lt
  let oddTup := oddSet n m S
  have hcv : (oddTup.card : ℝ) / (2 ^ (m * n) : ℝ) = oddFrac n m k := by
    simpa [(Finset.mem_powersetCard.mp hS).2] using card_oddSet_div_two_pow n m S
  set d : ℝ := (2 ^ (m * n) : ℝ)
  set mC : ℝ := (oddTup.card : ℝ)
  set α : ℝ := halfAngle n m k
  set K : ℕ := lockSchedule n m k
  set q₀ : ℝ := nonTargetRatio n m k
  set s : ℝ := targetRatio n m k
  have hdp : 0 < d := by positivity
  have hmp : 0 < mC := by
    rw [(div_eq_iff hdp.ne').mp hcv]
    exact mul_pos hp0 hdp
  have hsqm : √mC ≠ 0 := sqrt_ne_zero'.mpr hmp
  have hmdl : mC / d ≤ 1 := by rwa [hcv]
  have hsa : sin α = √mC / √d := by
    unfold α halfAngle
    rw [← hcv, sin_arcsin (by linarith [sqrt_nonneg (mC / d)])
      (sqrt_le_one.mpr hmdl), sqrt_div hmp.le]
  have hds : √d * sin α = √mC := by
    rw [hsa, mul_div_cancel₀ _ (sqrt_ne_zero'.mpr hdp)]
  have hcs : cos α ^ 2 + sin α ^ 2 = 1 := cos_sq_add_sin_sq α
  let P (w : Fin (2 ^ (m * n)) → ℂ) (A B : ℝ) : Prop :=
    (∀ x ∈ oddTup, w x = ((A / √mC : ℝ) : ℂ)) ∧
      ∑ i : Fin (2 ^ (m * n)), w i = ((√d * (B * cos α + A * sin α) : ℝ) : ℂ)
  have hor {w : Fin (2 ^ (m * n)) → ℂ} {A B : ℝ} (hw : P w A B) :
      ∑ i : Fin (2 ^ (m * n)), (oracleMat oddTup *ᵥ w) i =
        ((√d * (B * cos α - A * sin α) : ℝ) : ℂ) := by
    simp_rw [ora_mVec, show ∀ i : Fin (2 ^ (m * n)), (if i ∈ oddTup then -w i else w i) =
      w i + if i ∈ oddTup then -2 * w i else 0 from fun _ ↦ by split_ifs <;> ring]
    rw [sum_add_distrib, sum_ite_mem, univ_inter, hw.2,
      Finset.sum_congr (s₁ := oddTup) rfl fun u hu ↦ congrArg (-2 * ·) (hw.1 u hu),
      sum_const, nsmul_eq_mul]
    have hR : √d * (B * cos α + A * sin α) + mC * (-2 * (A / √mC)) =
        √d * (B * cos α - A * sin α) := by
      rw [show mC * (-2 * (A / √mC)) = -2 * (mC / √mC) * A by ring, div_sqrt, ← hds]
      ring
    dsimp [mC] at hR ⊢
    exact_mod_cast hR
  have hdiff {w' : Fin (2 ^ (m * n)) → ℂ} {A' B : ℝ}
      (hw1 : ∀ x ∈ oddTup, w' x = ((-A' / √mC : ℝ) : ℂ))
      (hw2 : ∑ i : Fin (2 ^ (m * n)), w' i = ((√d * (B * cos α - A' * sin α) : ℝ) : ℂ)) :
      P (diffuserMatrix *ᵥ w')
        (B * sin (2 * α) + A' * cos (2 * α))
        (B * cos (2 * α) - A' * sin (2 * α)) := by
    set X : ℝ := B * cos α - A' * sin α
    refine ⟨fun x hx ↦ ?_, ?_⟩
    · rw [_root_.Grover.diffuserMatrix_mulVec, hw2, hw1 x hx,
        show (B * sin (2 * α) + A' * cos (2 * α)) / √mC = 2 / d * (√d * X) - (-A' / √mC) by
          rw [show B * sin (2 * α) + A' * cos (2 * α) = 2 * sin α * X + A' by
              dsimp only [X]
              rw [cos_two_mul', sin_two_mul]
              linear_combination A' * hcs,
            add_div, hsa, show 2 * (√mC / √d) * X / √mC + A' / √mC =
              2 * (1 / √d) * X * (√mC / √mC) + A' / √mC by ring,
            div_self hsqm, ← sqrt_div_self']
          ring]
      dsimp [d, X]
      push_cast
      ring
    · rw [_root_.Grover.sum_diffuserMatrix_mulVec, hw2,
        show (B * cos (2 * α) - A' * sin (2 * α)) * cos α +
          (B * sin (2 * α) + A' * cos (2 * α)) * sin α = X by
          dsimp only [X]
          rw [cos_two_mul', sin_two_mul]
          linear_combination X * hcs]
  have hit {w : Fin (2 ^ (m * n)) → ℂ} {A₀ B₀ : ℝ} (hw : P w A₀ B₀) (j : ℕ) :
      P (iterVec oddTup j w)
        (B₀ * sin (2 * (j : ℝ) * α) + A₀ * cos (2 * (j : ℝ) * α))
        (B₀ * cos (2 * (j : ℝ) * α) - A₀ * sin (2 * (j : ℝ) * α)) := by
    induction j with
    | zero =>
      unfold iterVec
      simpa using hw
    | succ j ih =>
      dsimp only [iterVec]
      have hstep := hdiff (A' := B₀ * sin (2 * (j : ℝ) * α) + A₀ * cos (2 * (j : ℝ) * α))
        (B := B₀ * cos (2 * (j : ℝ) * α) - A₀ * sin (2 * (j : ℝ) * α))
        (fun x hx ↦ by
          rw [ora_mVec, ite_eq_left hx, ih.1 x hx]
          push_cast
          ring)
        (hor ih)
      have hθ : 2 * ((j + 1 : ℕ) : ℝ) * α = 2 * (j : ℝ) * α + 2 * α := by
        push_cast
        ring
      rw [hθ, sin_add, cos_add]
      convert hstep using 1 <;> ring
  have hun : P (unifVec (m * n)) (sin α) (cos α) := ⟨fun _ _ ↦ by
      rw [unifVec, hsa, div_right_comm, div_self hsqm]
      dsimp [d]
      push_cast
      rfl,
    by
      dsimp only [unifVec]
      rw [sum_const, Finset.card_univ, card_fin, nsmul_eq_mul,
        show cos α * cos α + sin α * sin α = 1 by linear_combination hcs, mul_one]
      dsimp [d]
      norm_cast
      simpa [div_eq_mul_inv] using div_sqrt (x := (2 ^ (m * n) : ℝ))⟩
  set φ₃ : ℝ := (2 * (K : ℝ) + 3) * α
  set φ₁ : ℝ := (2 * (K : ℝ) + 1) * α
  set A₀ : ℝ := sin φ₃
  set B₀ : ℝ := cos φ₃
  have hinit : P (initState n m k S) A₀ B₀ := by
    unfold initState
    have h0 := hit hun (K + 1)
    have hφ : α + 2 * ((K + 1 : ℕ) : ℝ) * α = φ₃ := by
      dsimp [φ₃]
      push_cast
      ring
    rwa [add_comm (cos α * _), ← sin_add, ← cos_add, hφ] at h0
  have hB₀ : B₀ = q₀ * cos φ₁ := by
    dsimp [B₀, q₀, nonTargetRatio, φ₃, φ₁, K, α]
    exact (div_mul_cancel₀ _ hcos1).symm
  have hsA₀ : s * A₀ = q₀ * sin φ₁ := by
    dsimp [s, targetRatio, q₀, A₀, φ₃, φ₁, K, α]
    exact div_mul_cancel₀ _ hsin3
  have hμ : chordV n m k ^ 2 - chordU n m k ^ 2 = -s :=
    (chordV_sq_sub_chordU_sq n m k).trans (by rw [hclamp])
  have hms {w : Fin (2 ^ (m * n)) → ℂ} {A B : ℝ} (hw : P w A B) :
      P (diffuserMatrix *ᵥ pinMissOp n m k oddTup w)
        (B * sin (2 * α) + s * A * cos (2 * α))
        (B * cos (2 * α) - s * A * sin (2 * α)) := by
    refine hdiff (fun x hx ↦ ?_) ?_
    · rw [pinMissOp, ite_eq_left hx, hμ, hw.1 x hx]
      push_cast
      ring
    · simp_rw [show ∀ i, pinMissOp n m k oddTup w i =
          w i + if i ∈ oddTup then ((-s - 1 : ℝ) : ℂ) * w i else 0 from fun _ ↦ by
        rw [pinMissOp, hμ]
        split_ifs <;> push_cast <;> ring]
      rw [sum_add_distrib, sum_ite_mem, univ_inter, hw.2,
        Finset.sum_congr (s₁ := oddTup) rfl
          (fun u hu ↦ congrArg (((-s - 1 : ℝ) : ℂ) * ·) (hw.1 u hu)),
        sum_const, nsmul_eq_mul]
      have hR : √d * (B * cos α + A * sin α) + mC * ((-s - 1) * (A / √mC)) =
          √d * (B * cos α - s * A * sin α) := by
        rw [show mC * ((-s - 1) * (A / √mC)) = (-s - 1) * (mC / √mC) * A by ring,
          div_sqrt, ← hds]
        ring
      dsimp [mC] at hR ⊢
      exact_mod_cast hR
  have hloop_P (j : ℕ) : P (loopState n m k S j) (q₀ ^ j * A₀) (q₀ ^ j * B₀) := by
    induction j with
    | zero =>
      unfold loopState
      simpa using hinit
    | succ j ih =>
      unfold loopState
      have hstep := hms ih
      have hφ_add : φ₁ + 2 * α = φ₃ := by
        dsimp [φ₁, φ₃]
        ring
      have hA_step : (q₀ ^ j * B₀) * sin (2 * α) + s * (q₀ ^ j * A₀) * cos (2 * α) =
          q₀ ^ (j + 1) * A₀ := by
        calc (q₀ ^ j * B₀) * sin (2 * α) + s * (q₀ ^ j * A₀) * cos (2 * α)
          _ = q₀ ^ j * (q₀ * cos φ₁) * sin (2 * α) +
                q₀ ^ j * (q₀ * sin φ₁) * cos (2 * α) := by
              rw [hB₀, show s * (q₀ ^ j * A₀) = q₀ ^ j * (s * A₀) by ring, hsA₀]
          _ = q₀ ^ (j + 1) * (sin φ₁ * cos (2 * α) + cos φ₁ * sin (2 * α)) := by
              rw [pow_succ]; ring
          _ = q₀ ^ (j + 1) * A₀ := by
              dsimp [A₀]; rw [← sin_add, hφ_add]
      have hB_step : (q₀ ^ j * B₀) * cos (2 * α) - s * (q₀ ^ j * A₀) * sin (2 * α) =
          q₀ ^ (j + 1) * B₀ := by
        calc (q₀ ^ j * B₀) * cos (2 * α) - s * (q₀ ^ j * A₀) * sin (2 * α)
          _ = q₀ ^ j * (q₀ * cos φ₁) * cos (2 * α) -
                q₀ ^ j * (q₀ * sin φ₁) * sin (2 * α) := by
              rw [hB₀, show s * (q₀ ^ j * A₀) = q₀ ^ j * (s * A₀) by ring, hsA₀]
          _ = q₀ ^ (j + 1) * (cos φ₁ * cos (2 * α) - sin φ₁ * sin (2 * α)) := by
              rw [pow_succ]; ring
          _ = q₀ ^ (j + 1) * B₀ := by
              dsimp [B₀]; rw [← cos_add, hφ_add]
      rwa [hA_step, hB_step] at hstep
  have hmark_norm (j : ℕ) :
      (∑ x ∈ oddTup, normSq (loopState n m k S j x)) = lockFailureProb n m k ^ j * A₀ ^ 2 := by
    rw [Finset.sum_congr rfl fun u hu ↦ show normSq (loopState n m k S j u) =
        (q₀ ^ j * A₀) ^ 2 / mC by
        rw [(hloop_P j).1 u hu, Complex.normSq_ofReal, ← sq, div_pow, sq_sqrt hmp.le],
      sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hmp.ne']
    dsimp [lockFailureProb, q₀]
    ring
  have h2uv_A₀ : (2 * chordU n m k * chordV n m k) ^ 2 * A₀ ^ 2 =
      1 - lockFailureProb n m k := by
    rw [two_mul_chordU_mul_chordV_sq, hclamp]
    have h1 : A₀ ^ 2 + B₀ ^ 2 = 1 := sin_sq_add_cos_sq φ₃
    have h2 : sin φ₁ ^ 2 + cos φ₁ ^ 2 = 1 := sin_sq_add_cos_sq φ₁
    dsimp [lockFailureProb, q₀, s] at hB₀ hsA₀ ⊢
    linear_combination h1 - q₀ ^ 2 * h2 - (s * A₀ + q₀ * sin φ₁) * hsA₀ -
      (B₀ + q₀ * cos φ₁) * hB₀
  have hhit_norm (j : ℕ) :
      (∑ x ∈ oddTup, normSq (pinHitOp n m k oddTup (loopState n m k S j) x)) =
        (1 - lockFailureProb n m k) * lockFailureProb n m k ^ j := by
    have hq (x : Fin (2 ^ (m * n))) (hx : x ∈ oddTup) :
        normSq (pinHitOp n m k oddTup (loopState n m k S j) x) =
          (2 * chordU n m k * chordV n m k) ^ 2 * normSq (loopState n m k S j x) := by
      dsimp only [pinHitOp]
      rw [ite_eq_left hx, map_mul, Complex.normSq_ofReal]
      ring
    rw [Finset.sum_congr rfl fun u hu ↦ hq u hu, ← mul_sum, hmark_norm j]
    linear_combination lockFailureProb n m k ^ j * h2uv_A₀
  have hni (J : ℕ) (v : Fin (2 ^ (m * n)) → ℂ) :
      (∑ u : Fin (2 ^ (m * n)), normSq (iterVec oddTup J v u)) =
        ∑ u : Fin (2 ^ (m * n)), normSq (v u) := by
    induction J with
    | zero => rfl
    | succ J ih =>
      change (∑ u : Fin (2 ^ (m * n)), normSq
        ((diffuserUnitary.1 *ᵥ (oracleMat oddTup *ᵥ iterVec oddTup J v)) u)) = _
      rw [sum_normSq_unitary_mulVec, ← ih]
      exact Finset.sum_congr rfl fun u _ ↦ by
        rw [ora_mVec]
        split_ifs <;> simp_all
  have htot_norm (j : ℕ) :
      (∑ x : Fin (2 ^ (m * n)), normSq (loopState n m k S j x)) =
        lockFailureProb n m k ^ j := by
    induction j with
    | zero =>
      dsimp only [loopState, initState]
      rw [pow_zero, hni, sum_normSq_unifVec]
    | succ j ih =>
      dsimp only [loopState]
      change (∑ x : Fin (2 ^ (m * n)), normSq
        ((diffuserUnitary.1 *ᵥ pinMissOp n m k oddTup (loopState n m k S j)) x)) = _
      rw [sum_normSq_unitary_mulVec]
      simp_rw [show ∀ x : Fin (2 ^ (m * n)),
          normSq (pinMissOp n m k oddTup (loopState n m k S j) x) =
            normSq (loopState n m k S j x) -
              if x ∈ oddTup then (2 * chordU n m k * chordV n m k) ^ 2 *
                normSq (loopState n m k S j x)
              else 0 from fun x ↦ by
        dsimp only [pinMissOp]
        split_ifs
        · rw [map_mul, Complex.normSq_ofReal]
          have h1 := chordU_sq_add_chordV_sq n m k
          linear_combination normSq (loopState n m k S j x) *
            ((chordU n m k ^ 2 + chordV n m k ^ 2 + 1) * h1)
        · ring]
      rw [sum_sub_distrib, ih, sum_ite_mem, univ_inter, ← mul_sum, hmark_norm j]
      linear_combination -lockFailureProb n m k ^ j * h2uv_A₀
  exact ⟨hhit_norm r, htot_norm r⟩

/-! ## Stationary Loop Circuit and Weakest-Precondition Calculus -/

abbrev parG {Var : Type} (res : Var) : Store Var → Prop := fun σ ↦ σ res = 0

def setupCirc {Var : Type} (res : Var) (n m k : ℕ) :
    OracleCirc Var (m * (n + 1)) ((n + 1) * m) :=
  .seq (qMap res (fun _ ↦ 0))
    (.seq (.step (phaseTag ((addrReg n m).embedUnitary (hadamardUnitary (q := m * n)))))
      (groverIter n m (lockSchedule n m k + 1)))

def eigLoopBody {Var : Type} (res : Var) (n m k : ℕ) (hm : 1 ≤ m) :
    OracleCirc Var (m * (n + 1)) ((n + 1) * m) :=
  let U := chordUnitary n m k hm
  let D := (addrReg n m).embedUnitary (diffuserUnitary (n := m * n))
  .seq (.seq (.step (phaseTag U)) (.seq (phaseStep n m) (.step (phaseTag U))))
    (.seq (.measure res (flag0Reg n m hm))
      (.qIf (parG res) (.step (phaseTag D)) .skip))

def readoutCirc {Var : Type} (res : Var) (n m : ℕ) (hm : 1 ≤ m) :
    OracleCirc Var (m * (n + 1)) ((n + 1) * m) :=
  .seq (.step (phaseTag (permutationUnitary (flipPerm n m)))) (markReadout res n m hm)

def eigLockCirc {Var : Type} (res : Var) (n m k : ℕ) (hm : 1 ≤ m) :
    OracleCirc Var (m * (n + 1)) ((n + 1) * m) :=
  .seq (.seq (setupCirc res n m k) (.qWhile (parG res) (eigLoopBody res n m k hm)))
    (readoutCirc res n m hm)

def failStepMat (n m k : ℕ) (hm : 1 ≤ m) (S : Finset (Fin (2 ^ n))) :
    Operator (2 ^ (m * (n + 1))) :=
  ((addrReg n m).embedUnitary (diffuserUnitary (n := m * n))).1 *
    (flag0Reg n m hm).basisOutcomeProjector 0 * parityMat n m k hm S

def hitStepMat (n m k : ℕ) (hm : 1 ≤ m) (S : Finset (Fin (2 ^ n))) :
    Operator (2 ^ (m * (n + 1))) :=
  (flag0Reg n m hm).basisOutcomeProjector 1 * parityMat n m k hm S

def initMat (n m k : ℕ) (S : Finset (Fin (2 ^ n))) : Operator (2 ^ (m * (n + 1))) :=
  iterMat n m S (lockSchedule n m k + 1) *
    ((addrReg n m).embedUnitary (hadamardUnitary (q := m * n))).1

lemma failStepMat_pow_mul_initMat_zero {n m k : ℕ} (hm : 1 ≤ m)
    (S : Finset (Fin (2 ^ n))) (r : ℕ) :
    (failStepMat n m k hm S ^ r * initMat n m k S) *ᵥ single 0 1 =
      (addrReg n m).tensorState (loopState n m k S r) (single 0 1) := by
  induction r with
  | zero =>
    rw [pow_zero, one_mul, initMat, ← mulVec_mulVec, hadamard_mulVec_zero, iMat_tens]
    rfl
  | succ r ih =>
    rw [pow_succ', Matrix.mul_assoc, ← mulVec_mulVec, ih]
    unfold failStepMat
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, parityMat_mulVec_tensorState,
      (flag0Reg_basisOutcomeProjector_mulVec hm _ _).1]
    exact (addrReg n m).embedMatrix_mulVec_tensorState diffuserMatrix _ (single 0 1)

lemma wp_eigLoopBody {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hm : 1 ≤ m)
    (S : Finset (Fin (2 ^ n))) (N₀ N₁ : Operator (2 ^ (m * (n + 1))))
    (Ψ : CQAssertion (Store Var) (2 ^ (m * (n + 1))))
    (hΨ : ∀ τ, (Ψ τ).1.1 = if parG res τ then N₀ else N₁) (τ : Store Var) :
    ((wp ((eigLoopBody res n m k hm).compile qAssign (groverParallelMarkingOracle m S)) Ψ) τ).1.1 =
      (failStepMat n m k hm S)ᴴ * N₀ * failStepMat n m k hm S +
        (hitStepMat n m k hm S)ᴴ * N₁ * hitStepMat n m k hm S := by
  let P₀ := (flag0Reg n m hm).basisOutcomeProjector 0
  let P₁ := (flag0Reg n m hm).basisOutcomeProjector 1
  let D := (addrReg n m).embedUnitary (diffuserUnitary (n := m * n))
  let R := chordMat n m k hm
  let M_mid := P₀ * (D.1ᴴ * N₀ * D.1) * P₀ + P₁ * N₁ * P₁
  unfold eigLoopBody
  simp only [compile, wp_qSeq]
  rw [wp_qAssign, wp_phaseTag, qhlQAssign_val,
    wp_phaseStep (m := m) S (Rᴴ * M_mid * R) _ (fun t ↦ by
      have h0 : parG res (Store.subst t res (Int.ofNat (0 : Fin 2).val)) := by simp [parG]
      have h1 : ¬ parG res (Store.subst t res (Int.ofNat (1 : Fin 2).val)) := by simp [parG]
      rw [wp_qAssign, wp_phaseTag, qhlQAssign_val,
        wp_qIf, wp_qAssign, wp_phaseTag, wp_skip,
        wp_measureRegister res (r := flag0Reg n m hm)]
      change (chordUnitary n m k hm).1ᴴ * (∑ o : Fin 2, _) * (chordUnitary n m k hm).1 = _
      rw [Fin.sum_univ_two, ite_eq_left h0, qhlQAssign_val, hΨ _, ite_eq_left h0,
        ite_eq_right h1, hΨ _, ite_eq_right h1]
      rfl) τ]
  dsimp only [failStepMat, hitStepMat, parityMat, chordUnitary, R, M_mid, P₀, P₁, D]
  simp only [Matrix.mul_add, Matrix.add_mul, conjTranspose_mul,
    QRegister.basisOutcomeProjector_conjTranspose, Matrix.mul_assoc]

lemma wp_setupCirc {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (S : Finset (Fin (2 ^ n))) (M₀ M₁ : Operator (2 ^ (m * (n + 1))))
    (Φ : CQAssertion (Store Var) (2 ^ (m * (n + 1))))
    (hΦ : ∀ τ, (Φ τ).1.1 = if parG res τ then M₀ else M₁) (σ : Store Var) :
    ((wp ((setupCirc res n m k).compile qAssign (groverParallelMarkingOracle m S)) Φ) σ).1.1 =
      (((initMat n m k S)ᴴ * M₀ * initMat n m k S) 0 0) •
        (1 : Operator (2 ^ (m * (n + 1)))) := by
  let Q := m * (n + 1)
  let oracle := groverParallelMarkingOracle m S
  let U₀ := initMat n m k S
  have hgIter (J : ℕ) (Ψ : CQAssertion (Store Var) (2 ^ Q)) (τ : Store Var) :
      ((wp ((groverIter n m J).compile qAssign oracle) Ψ) τ).1.1 =
        (iterMat n m S J)ᴴ * (Ψ τ).1.1 * iterMat n m S J := by
    induction J generalizing Ψ with
    | zero =>
      dsimp only [groverIter, iterMat, compile]
      simp
    | succ J ih =>
      dsimp only [groverIter, iterMat, compile]
      let D := (addrReg n m).embedUnitary (diffuserUnitary (n := m * n))
      rw [wp_qSeq, ih]
      have hps : ((wp ((phaseStep n m).compile qAssign oracle)
          (wp (.qAssign (phaseTag D)) Ψ)) τ).1.1 =
          (sDiagM n m S)ᴴ * (D.1ᴴ * (Ψ τ).1.1 * D.1) * sDiagM n m S := by
        unfold phaseStep
        dsimp only [compile]
        set A := flagConj n m
        set Of := (fullReg n m).embedUnitary oracle
        simp only [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
          show A.1ᴴ * (Of.1ᴴ * (A.1ᴴ * (D.1ᴴ * (Ψ τ).1.1 * D.1) * A.1) * Of.1) * A.1 =
            (A.1 * Of.1 * A.1)ᴴ * (D.1ᴴ * (Ψ τ).1.1 * D.1) * (A.1 * Of.1 * A.1) by
            simp only [conjTranspose_mul, Matrix.mul_assoc]]
        rw [flagConj_mul_embed_mul_flagConj]
      rw [wp_qSeq, hps]
      dsimp only [D]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
  unfold setupCirc
  simp only [compile, wp_qSeq]
  rw [wp_qMap res (fun _ ↦ 0) oracle
    (fun z ↦ U₀ᴴ * (if z = 0 then M₀ else M₁) * U₀) _ (fun τ ↦ by
      rw [wp_qAssign, wp_phaseTag, qhlQAssign_val, hgIter, hΦ τ]
      dsimp only [U₀, initMat, parG]
      simp only [conjTranspose_mul, Matrix.mul_assoc]) σ,
    ← Matrix.smul_one_eq_diagonal]
  simp [U₀]

lemma wp_setup_whileActiveWP {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hn : 150 + clog 2 m + clog 2 k ≤ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) (r : ℕ) :
    let oracle := groverParallelMarkingOracle m S
    let setup := (setupCirc res n m k).compile qAssign oracle
    let body := (eigLoopBody res n m k hm).compile qAssign oracle
    wp setup (whileActiveWP (wp body) (parG res) r) =
      CQAssertion.ofProb (lockFailureProb n m k ^ r) := by
  intro oracle setup body
  let Q := m * (n + 1)
  let B₀ := failStepMat n m k hm S
  have hact (j : ℕ) (τ : Store Var) :
      ((whileActiveWP (wp body) (parG res) j) τ).1.1 =
        if parG res τ then (B₀ ^ j)ᴴ * (B₀ ^ j) else 0 := by
    induction j generalizing τ with
    | zero =>
      unfold whileActiveWP
      by_cases h : parG res τ
      · rw [ite_eq_left h, ite_eq_left h, pow_zero, Matrix.conjTranspose_one, mul_one]
        rfl
      · rw [ite_eq_right h, ite_eq_right h]
        rfl
    | succ j ih =>
      unfold whileActiveWP
      by_cases h : parG res τ
      · rw [ite_eq_left h, ite_eq_left h,
          wp_eigLoopBody res hm S ((B₀ ^ j)ᴴ * (B₀ ^ j)) 0 _ ih τ,
          pow_succ B₀ j, conjTranspose_mul]
        dsimp only [B₀]
        simp only [Matrix.mul_zero, zero_mul, add_zero, Matrix.mul_assoc]
      · rw [ite_eq_right h, ite_eq_right h]
        rfl
  obtain ⟨_, _, hq0, hq1, _, _, _⟩ := asymp_schedule_bds hm hk hn
  funext σ
  refine Subtype.ext (Subtype.ext ?_)
  rw [wp_setupCirc res S ((B₀ ^ r)ᴴ * (B₀ ^ r)) 0 _ (hact r) σ,
    CQAssertion.ofProb_apply_of_bounds (lockFailureProb n m k ^ r)
      (pow_nonneg hq0 r) (pow_le_one₀ hq0 hq1.le) σ,
    HermitianMat.val_eq_coe]
  have h1 : postDiag hm S (fun _ ↦ 1) = (1 : Operator (2 ^ Q)) := Matrix.diagonal_one
  have hentry : ((initMat n m k S)ᴴ * ((B₀ ^ r)ᴴ * (B₀ ^ r)) * initMat n m k S) 0 0 =
      ((lockFailureProb n m k ^ r : ℝ) : ℂ) := by
    rw [show (initMat n m k S)ᴴ * ((B₀ ^ r)ᴴ * (B₀ ^ r)) * initMat n m k S =
        (B₀ ^ r * initMat n m k S)ᴴ * postDiag hm S (fun _ ↦ 1) * (B₀ ^ r * initMat n m k S) by
        rw [h1]
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one],
      sum_decOut_zero hm S (fun _ ↦ 1) 1 1 (fun _ _ ↦ rfl) rfl _ _
        (failStepMat_pow_mul_initMat_zero hm S r),
      (loopState_norms hm hk hn hS r).2]
    ring
  rw [hentry]
  simp [← Complex.coe_smul]

def recMat (n m k : ℕ) (hm : 1 ≤ m) (S : Finset (Fin (2 ^ n)))
    (N₁ : Operator (2 ^ (m * (n + 1)))) : ℕ → Operator (2 ^ (m * (n + 1)))
  | 0 => 0
  | r + 1 =>
    (failStepMat n m k hm S)ᴴ * recMat n m k hm S N₁ r * failStepMat n m k hm S +
      (hitStepMat n m k hm S)ᴴ * N₁ * hitStepMat n m k hm S

lemma wp_setup_whileRecWP {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hn : 150 + clog 2 m + clog 2 k ≤ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1))))
    (g : ℤ → ℂ) (hg_s : ∀ x ∈ S, g (x.val : ℤ) = 1) (hg_f : g (2 ^ n : ℤ) = 0)
    (hΘ : ∀ τ, ¬ parG res τ → (Θ τ).1.1 =
      (flipMat n m)ᴴ * postDiag hm S g * flipMat n m)
    (r : ℕ) (σ : Store Var) :
    let oracle := groverParallelMarkingOracle m S
    let setup := (setupCirc res n m k).compile qAssign oracle
    let body := (eigLoopBody res n m k hm).compile qAssign oracle
    ((wp setup (whileRecWP (wp body) (parG res) (r + 1) Θ)) σ).1 =
      1 - (lockFailureProb n m k ^ r) • (1 : HermitianMat (Fin (2 ^ (m * (n + 1)))) ℂ) := by
  intro oracle setup body
  let Q := m * (n + 1)
  let X := flipMat n m
  let D := postDiag hm S g
  let N₁ := Xᴴ * D * X
  let B₀ := failStepMat n m k hm S
  let B₁ := hitStepMat n m k hm S
  let U₀ := initMat n m k S
  have hrec (j : ℕ) (τ : Store Var) :
      ((whileRecWP (wp body) (parG res) (j + 1) Θ) τ).1.1 =
        if parG res τ then recMat n m k hm S N₁ j else N₁ := by
    induction j generalizing τ with
    | zero =>
      rw [qhlWhileSucc_val]
      by_cases h : parG res τ
      · rw [ite_eq_left h, ite_eq_left h]
        change ((wp body ⊥) τ).1.1 = 0
        rw [wp_eigLoopBody res hm S 0 0 ⊥ (fun _ ↦ by simp) τ]
        simp
      · rw [ite_eq_right h, ite_eq_right h, hΘ τ h]
    | succ j ih =>
      rw [qhlWhileSucc_val]
      by_cases h : parG res τ
      · rw [ite_eq_left h, ite_eq_left h,
          wp_eigLoopBody res hm S (recMat n m k hm S N₁ j) N₁ _ ih τ]
        rfl
      · rw [ite_eq_right h, ite_eq_right h, hΘ τ h]
  have hhit (i : ℕ) :
      ((X * B₁ * B₀ ^ i * U₀)ᴴ * D * (X * B₁ * B₀ ^ i * U₀)) 0 0 =
        (((1 - lockFailureProb n m k) * lockFailureProb n m k ^ i : ℝ) : ℂ) := by
    let q0 := pinHitOp n m k (oddSet n m S) (loopState n m k S i)
    have hvec : (X * B₁ * B₀ ^ i * U₀) *ᵥ single 0 1 =
        (addrReg n m).tensorState q0 (single 0 1) := by
      dsimp only [X, B₁, B₀, U₀, hitStepMat, flipMat]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
        failStepMat_pow_mul_initMat_zero hm S i, ← mulVec_mulVec,
        parityMat_mulVec_tensorState, (flag0Reg_basisOutcomeProjector_mulVec hm _ _).2,
        permutationUnitary_flipPerm_mulVec_tensorState _ 1, addrEnv_one_add_one]
    rw [sum_decOut_zero hm S g 1 0 hg_s hg_f _ q0 hvec, (loopState_norms hm hk hn hS i).1]
    ring
  have hpull (m' i : ℕ) :
      ((B₀ ^ i * U₀)ᴴ * recMat n m k hm S N₁ m' * (B₀ ^ i * U₀)) 0 0 =
        ∑ l ∈ Finset.range m',
          (((1 - lockFailureProb n m k) * lockFailureProb n m k ^ (i + l) : ℝ) : ℂ) := by
    induction m' generalizing i with
    | zero =>
      dsimp only [recMat]
      simp
    | succ m' ihm =>
      dsimp only [recMat]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
        show (B₀ ^ i * U₀)ᴴ * (B₀ᴴ * recMat n m k hm S N₁ m' * B₀) * (B₀ ^ i * U₀) =
          (B₀ ^ (i + 1) * U₀)ᴴ * recMat n m k hm S N₁ m' * (B₀ ^ (i + 1) * U₀) by
          rw [pow_succ' B₀ i]
          simp only [conjTranspose_mul, Matrix.mul_assoc],
        show (B₀ ^ i * U₀)ᴴ * (B₁ᴴ * N₁ * B₁) * (B₀ ^ i * U₀) =
          (X * B₁ * B₀ ^ i * U₀)ᴴ * D * (X * B₁ * B₀ ^ i * U₀) by
          dsimp only [N₁]
          simp only [conjTranspose_mul, Matrix.mul_assoc],
        ihm (i + 1), hhit i, Finset.sum_range_succ']
      simp only [Nat.add_zero, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [show l + (i + 1) = i + (l + 1) by omega]
  have hsum_geom (j : ℕ) :
      (∑ l ∈ Finset.range j,
        (((1 - lockFailureProb n m k) * lockFailureProb n m k ^ (0 + l) : ℝ) : ℂ)) =
        ((1 - lockFailureProb n m k ^ j : ℝ) : ℂ) := by
    induction j with
    | zero => simp
    | succ j ihj =>
      rw [Finset.sum_range_succ, ihj, Nat.zero_add, pow_succ]
      push_cast
      ring
  have hentry : ((U₀)ᴴ * recMat n m k hm S N₁ r * U₀) 0 0 =
      ((1 - lockFailureProb n m k ^ r : ℝ) : ℂ) := by
    have h0 := hpull r 0
    rw [pow_zero, one_mul] at h0
    exact h0.trans (hsum_geom r)
  refine Subtype.ext ?_
  rw [wp_setupCirc res S (recMat n m k hm S N₁ r) N₁ _ (hrec r) σ,
    hentry, HermitianMat.val_eq_coe]
  simp [sub_smul, one_smul, ← Complex.coe_smul]

end

public section

attribute [irreducible] naiveTrial eigLockCirc

/-- Parallel query-model circuit writing at least one marked element of `S` into `res`. -/
noncomputable def circuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ qubits n m k)) Var (qubits n m k) ((n + 1) * m) :=
  (if hm : 1 ≤ m then
    if k = 2 ^ n then qMap res (fun _ ↦ ⟨0, by positivity⟩)
    else if n < 150 + clog 2 m + clog 2 k then
      .seq (qMap res (fun _ ↦ failOut n m hm))
        (.qWhile (fun σ ↦ σ res = (2 ^ n : ℤ)) (naiveTrial res n m hm))
    else eigLockCirc res n m k hm
  else .skip : OracleCirc Var (m * (n + 1)) ((n + 1) * m))

/-- Compiled parallel `FindAny` program with initial reset `qset`. -/
noncomputable abbrev program {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : QProg Var (2 ^ qubits n m k) :=
  qset ;; (circuit res n m k).compile QProg.qAssign oracle

/-- `program` writes some `x ∈ S` into `res` with probability `1`. -/
theorem correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (_hn : 1 ≤ n) (hmk : cells m k = true) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ qubits n m k)) ⦄
    program res n m k (groverParallelMarkingOracle m S)
    ⦃ fun σ ↦ ⌜∃ x ∈ S, σ res = x.val⌝ ⦄ := by
  have hpost : (fun σ : Store Var ↦ (⌜∃ x ∈ S, σ res = x.val⌝ :
      Observable (Fin (2 ^ qubits n m k)))) =
      liftPureProp (fun σ ↦ ∃ x ∈ S, σ res = x.val) := by
    funext σ
    by_cases h : ∃ x ∈ S, σ res = x.val <;> simp [liftPureProp, h]
  rw [hpost]
  have hm : 1 ≤ m := one_le_of_mem_groverGrid (cells_mem_grid hmk).1
  have hk : 1 ≤ k := one_le_of_mem_groverGrid (cells_mem_grid hmk).2
  unfold program circuit qubits
  rw [dite_eq_left hm]
  set Q := m * (n + 1)
  let oracle := groverParallelMarkingOracle m S
  let post : CQAssertion (Store Var) (2 ^ Q) := liftPureProp (fun σ ↦ ∃ x ∈ S, σ res = (x.val : ℤ))
  let z0 : Fin (2 ^ Q) := ⟨0, by positivity⟩
  apply Triple.of_eq_wp
  symm
  suffices htop : wp ((if k = 2 ^ n then qMap res (fun _ ↦ z0)
      else if n < 150 + clog 2 m + clog 2 k then
        .seq (qMap res (fun _ ↦ failOut n m hm))
          (.qWhile (fun σ ↦ σ res = (2 ^ n : ℤ)) (naiveTrial res n m hm))
      else eigLockCirc res n m k hm).compile qAssign oracle) post = ⊤ by
    funext σ
    refine Subtype.ext (Subtype.ext ?_)
    change ((wp (qset ;; _) post) σ).1.1 = 1
    rw [wp_qSeq, htop, wp_qSet, qhlQSet_val]
    simp
  by_cases hk_eq : k = 2 ^ n
  · rw [ite_eq_left hk_eq]
    have hx0 : (⟨0, by positivity⟩ : Fin (2 ^ n)) ∈ S := by
      rw [Finset.eq_univ_of_card S (by rw [(Finset.mem_powersetCard.mp hS).2, hk_eq, card_fin])]
      exact Finset.mem_univ _
    funext σ
    refine Subtype.ext (Subtype.ext ?_)
    rw [wp_qMap res (fun _ ↦ z0) oracle
      (fun z ↦ (if ∃ x ∈ S, z = (x.val : ℤ) then (1 : ℂ) else 0) • (1 : Operator (2 ^ Q)))
      post (fun τ ↦ by by_cases hex : ∃ x ∈ S, τ res = (x.val : ℤ) <;> simp [post, hex]) σ,
        ← Matrix.smul_one_eq_diagonal, ite_eq_left ⟨_, hx0, rfl⟩, one_smul, Matrix.one_apply_eq,
        one_smul]
    rfl
  · rw [ite_eq_right hk_eq]
    have hk_lt : k < 2 ^ n := Nat.lt_of_le_of_ne hkN hk_eq
    by_cases hn_lt : n < 150 + clog 2 m + clog 2 k
    · rw [ite_eq_left hn_lt]
      dsimp only [compile]
      let grd : Store Var → Prop := fun σ ↦ σ res = (2 ^ n : ℤ)
      let iP := (qMap res (W := (n + 1) * m) (fun _ ↦ failOut n m hm)).compile qAssign oracle
      let tR := (naiveTrial res n m hm).compile qAssign oracle
      let p := oddFrac n m k
      let q := 1 - p
      obtain ⟨hp0, hp1⟩ := oddFrac_bounds hm hk hk_lt
      have hq0 : 0 ≤ q := sub_nonneg.mpr hp1
      have hq1 : q < 1 := sub_lt_self 1 hp0
      refine CQAssertion.eq_top_of_one_sub_geometric_le q hq0 hq1 (fun _ ↦ 1) (fun σ r ↦ ?_)
      let lC (r : ℕ) (z : ℤ) : ℂ := if z = (2 ^ n : ℤ) then ((1 - (1 - p) ^ r : ℝ) : ℂ)
        else if ∃ x ∈ S, z = (x.val : ℤ) then 1 else 0
      have hnot {r : ℕ} {τ : Store Var} (h : τ res ≠ (2 ^ n : ℤ)) :
          (post τ).1.1 = lC r (τ res) • (1 : Operator (2 ^ Q)) := by
        by_cases hex : ∃ x ∈ S, τ res = (x.val : ℤ) <;> simp [post, lC, h, hex]
      have hrc (r : ℕ) (τ : Store Var) : ((whileRecWP (wp tR) grd (r + 1) post) τ).1.1 =
          lC r (τ res) • (1 : Operator (2 ^ Q)) := by
        induction r generalizing τ with
        | zero =>
          rw [qhlWhileSucc_val]
          by_cases h : τ res = (2 ^ n : ℤ)
          · rw [ite_eq_left (h : grd τ)]
            change ((wp tR ⊥) τ).1.1 = _
            rw [wp_naiveTrial res hm hS (fun _ ↦ 0) 0 0 ⊥ (fun _ ↦ by simp) (fun _ _ ↦ rfl) rfl τ]
            simp [lC, h]
          · rw [ite_eq_right (h : ¬ grd τ), hnot h]
        | succ r ih =>
          rw [qhlWhileSucc_val]
          by_cases h : τ res = (2 ^ n : ℤ)
          · rw [ite_eq_left (h : grd τ), wp_naiveTrial res hm hS (lC r) 1
              ((1 - (1 - p) ^ r : ℝ) : ℂ) _ ih
              (fun x hx ↦ by
                dsimp only [lC]
                rw [ite_eq_right (by exact_mod_cast x.isLt.ne), ite_eq_left ⟨x, hx, rfl⟩])
              (by simp [lC]) τ]
            congr 1
            simp only [lC, h, ↓reduceIte]
            push_cast
            ring
          · rw [ite_eq_right (h : ¬ grd τ), hnot h]
      have heq : ((wp iP (whileRecWP (wp tR) grd (r + 1) post)) σ).1 =
          1 - q ^ r • (1 : HermitianMat (Fin (2 ^ Q)) ℂ) := by
        refine Subtype.ext ?_
        rw [wp_qMap res (fun _ ↦ failOut n m hm) oracle
          (fun z ↦ lC r z • (1 : Operator (2 ^ Q))) _ (hrc r) σ, ← Matrix.smul_one_eq_diagonal,
          HermitianMat.val_eq_coe]
        simp [lC, q, sub_smul, one_smul, ← Complex.coe_smul]
      rw [← heq, wp_qSeq]
      exact wp_mono iP (whileRecWP_le_wp_qWhile grd tR (r + 1) post) σ
    · rw [ite_eq_right hn_lt]
      have hn_ge : 150 + clog 2 m + clog 2 k ≤ n := not_lt.mp hn_lt
      obtain ⟨_, _, hq0, hq1, _, _, _⟩ := asymp_schedule_bds hm hk hn_ge
      unfold eigLockCirc
      dsimp only [compile]
      let setup := (setupCirc res n m k).compile qAssign oracle
      let body := (eigLoopBody res n m k hm).compile qAssign oracle
      let readout := (readoutCirc res n m hm).compile qAssign oracle
      let g (z : ℤ) : ℂ := if ∃ x ∈ S, z = (x.val : ℤ) then 1 else 0
      have hread (τ : Store Var) :
          ((wp readout post) τ).1.1 = (flipMat n m)ᴴ * postDiag hm S g * flipMat n m := by
        unfold readout readoutCirc
        dsimp only [compile]
        rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
          wp_markReadout res hm S g post
            (fun s ↦ by by_cases hex : ∃ x ∈ S, s res = (x.val : ℤ) <;> simp [post, g, hex])]
        rfl
      refine CQAssertion.eq_top_of_one_sub_geometric_le
        (lockFailureProb n m k) hq0 hq1 (fun _ ↦ 1) (fun σ r ↦ ?_)
      have hg_f : g (2 ^ n : ℤ) = 0 := by
        dsimp only [g]
        exact ite_eq_right fun ⟨x, _, hx⟩ ↦
          (by exact_mod_cast x.isLt.ne : (x.val : ℤ) ≠ (2 ^ n : ℤ)) hx.symm
      have heq := wp_setup_whileRecWP res hm hk hn_ge hS (wp readout post) g
        (fun x hx ↦ ite_eq_left ⟨x, hx, rfl⟩) hg_f (fun τ _ ↦ hread τ) r σ
      rw [← heq, wp_qSeq, wp_qSeq]
      exact wp_mono setup (whileRecWP_le_wp_qWhile (parG res) body (r + 1) (wp readout post)) σ

/-- Asymptotic uniform-average expected parallel-round cost bound for `program`. -/
theorem rel_cost_of_margin {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hmk : cells m k = true) (ρ : ℝ)
    (hρ : 0 < ρ * (π / 4) - (π / 8 + 1 / 4)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ program res n m k (groverParallelMarkingOracle m S))
        (ρ * vanillaFindAnyCost n m k) := by
  have hm : 1 ≤ m := one_le_of_mem_groverGrid (cells_mem_grid hmk).1
  have hk : 1 ≤ k := one_le_of_mem_groverGrid (cells_mem_grid hmk).2
  set δ : ℝ := ρ * (π / 4) - (π / 8 + 1 / 4)
  have hδ : 0 < δ := hρ
  obtain ⟨M, hM⟩ := exists_nat_ge ((5 / δ) ^ 2 * ((m : ℝ) * (k : ℝ)))
  refine ⟨max (150 + clog 2 m + clog 2 k) M, fun n hn _ ↦ ?_⟩
  have hn_M : M ≤ n := (le_max_right _ _).trans hn
  have hn : 150 + clog 2 m + clog 2 k ≤ n := (le_max_left _ _).trans hn
  unfold AvgOracleCostBound program circuit qubits
  obtain ⟨hk_ne, _, hq0, hq1, _, _, hwl⟩ := asymp_schedule_bds hm hk hn
  have hn_not_lt : ¬ (n < 150 + clog 2 m + clog 2 k) := not_lt.mpr hn
  let qNN : ℝ≥0 := ⟨lockFailureProb n m k, hq0⟩
  have hqNN1 : qNN < 1 := by exact_mod_cast hq1
  let bd : ℝ≥0 := (lockSchedule n m k : ℝ≥0) + 1 + (1 - qNN)⁻¹ + 1
  refine ⟨fun _ ↦ bd, fun S hS ↦ ?_, ?_⟩
  · rw [dite_eq_left hm, ite_eq_right hk_ne, ite_eq_right hn_not_lt]
    set Q := m * (n + 1)
    let oracle := groverParallelMarkingOracle m S
    let model : CostModel (2 ^ Q) := ofEmbeddedOracle oracle
    have hor := isRealMatrix_groverParallelMarkingOracle m S
    have htag (V : Unitary (2 ^ Q)) : CostBound (Var := Var) model (.qAssign (phaseTag V)) 0 :=
      costBound_qAssign_phaseTag hor V
    have hro : CostBound (Var := Var) model (.qAssign ((fullReg n m).embedUnitary oracle)) 1 := by
      simpa [model] using CostBound.qAssign (Var := Var) model
        ((fullReg n m).embedUnitary oracle)
    have hact : CostBound (Var := Var) model ((phaseStep n m).compile qAssign oracle) 1 :=
      costBound_phaseStep (Var := Var) S
    have hilc (J : ℕ) :
        CostBound (Var := Var) model ((groverIter n m J).compile qAssign oracle) (J : ℝ≥0) := by
      induction J with
      | zero =>
        rw [Nat.cast_zero]
        exact CostBound.skip_zero model
      | succ J ih =>
        dsimp only [groverIter, compile]
        rw [Nat.cast_succ]
        exact ih.seq (by simpa using hact.seq (htag _))
    let setup := (setupCirc res n m k).compile qAssign oracle
    let body := (eigLoopBody res n m k hm).compile qAssign oracle
    let readout := (readoutCirc res n m hm).compile qAssign oracle
    have hsetup_cost : CostBound model setup ((lockSchedule n m k : ℝ≥0) + 1) := by
      unfold setup setupCirc
      dsimp only [compile]
      have h0 := costBound_qMap (Var := Var) res (Q := Q) (fun _ ↦ 0) hor
      have h1 := htag ((addrReg n m).embedUnitary (hadamardUnitary (q := m * n)))
      have h2 := hilc (lockSchedule n m k + 1)
      rw [Nat.cast_succ] at h2
      simpa using h0.seq (h1.seq h2)
    have hbody_cost : CostBound model body 1 := by
      unfold body eigLoopBody
      dsimp only [compile]
      have hmeas : CostBound (Var := Var) model (measureRegister res (flag0Reg n m hm)) 0 := by
        simpa [measureRegister, model, ofEmbeddedOracle] using
          CostBound.qMeasure (Var := Var) model res
            (flag0Reg n m hm).computationalBasisMeasurement.toMeasurement
      have hif : CostBound (Var := Var) model
          (.qIf (parG res) (.qAssign (phaseTag
            ((addrReg n m).embedUnitary (diffuserUnitary (n := m * n))))) .skip) 0 := by
        simpa using CostBound.qIf (parG res) (htag _) (CostBound.skip_zero model)
      simpa using ((htag _).seq (hact.seq (htag _))).seq (hmeas.seq hif)
    have hread_cost : CostBound model readout 1 := by
      unfold readout readoutCirc markReadout
      dsimp only [compile]
      simpa using (htag _).seq (hro.seq (costBound_qMap (Var := Var) res (decOut n m hm) hor))
    have hact_trace (r : ℕ) (state : CQState (Store Var) (2 ^ Q)) :
        (activeIter (parG res) body r ((interp setup).toStateFun state)).trace =
          qNN ^ r * state.trace := by
      have hwp := wp_setup_whileActiveWP res hm hk hn hS r
      ext
      rw [← expect_whileActiveWP, ← expect_wp, hwp,
        expect_ofProb (lockFailureProb n m k ^ r) state
          ⟨pow_nonneg hq0 r, pow_le_one₀ hq0 hq1.le⟩]
      push_cast
      rfl
    have hexp_iter (state : CQState (Store Var) (2 ^ Q)) :
        expectedIterations (parG res) body ((interp setup).toStateFun state) =
          (state.trace : ℝ≥0∞) * (((1 - qNN)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      have hcoe (r : ℕ) :
          ((activeIter (parG res) body r ((interp setup).toStateFun state)).trace : ℝ≥0∞) =
            ((qNN : ℝ≥0∞) ^ r) * state.trace := by
        rw [hact_trace r state, ENNReal.coe_mul, ENNReal.coe_pow]
      rw [expectedIterations, funext hcoe, ENNReal.tsum_mul_right, mul_comm]
      congr 1
      rw [ENNReal.tsum_geometric, ENNReal.coe_inv (tsub_pos_of_lt hqNN1).ne',
        ENNReal.coe_sub, ENNReal.coe_one]
    have hsetup_while :
        CostBound model (setup ;; .qWhile (parG res) body)
          ((lockSchedule n m k : ℝ≥0) + 1 + (1 - qNN)⁻¹) := by
      intro state
      rw [expectedCost_qSeq, ENNReal.coe_add, mul_add]
      refine add_le_add (hsetup_cost state) ?_
      exact (expectedCost_qWhile_le hbody_cost (parG res) _).trans_eq
        (by rw [hexp_iter state, ENNReal.coe_one, mul_one])
    have hqs : CostBound model (qset : QProg Var (2 ^ Q)) 0 := by
      simpa [model] using CostBound.qSet (Var := Var) model
    unfold eigLockCirc
    dsimp only [compile]
    simpa [bd] using hqs.seq (hsetup_while.seq hread_cost)
  · refine le_trans (b := (bd : ℝ)) ?_ ?_
    · simp only [sum_const, nsmul_eq_mul]
      by_cases hcd' : (groverTargetSets n k).card = 0
      · rw [hcd', Nat.cast_zero, zero_mul, zero_div]
        exact NNReal.coe_nonneg _
      · exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hcd')).le
    · have hbd_eq : (bd : ℝ) =
          (lockSchedule n m k : ℝ) + 1 + (1 - lockFailureProb n m k)⁻¹ + 1 := by
        dsimp only [bd, qNN]
        rw [NNReal.coe_add, NNReal.coe_add, NNReal.coe_add, NNReal.coe_inv,
          NNReal.coe_sub hqNN1.le]
        push_cast
        rfl
      have hmk_pos : (0 : ℝ) < (m : ℝ) * (k : ℝ) := by positivity
      have hM_pow : (5 / δ) ^ 2 * ((m : ℝ) * (k : ℝ)) ≤ (2 ^ n : ℝ) :=
        hM.trans (by exact_mod_cast hn_M.trans n.lt_two_pow_self.le)
      set R : ℝ := (2 ^ n : ℝ) / ((m : ℝ) * (k : ℝ))
      have h5_R : 5 / δ ≤ √R := le_sqrt_of_sq_le ((le_div_iff₀ hmk_pos).mpr hM_pow)
      have h5_δ : 5 ≤ δ * √R := by
        have := (div_le_iff₀ hδ).mp h5_R
        linarith
      have hvan : ρ * vanillaFindAnyCost n m k =
          ((π / 8 + 1 / 4) + δ) * √R := by
        unfold vanillaFindAnyCost
        dsimp only [δ, R]
        ring
      linarith [hbd_eq, hwl, h5_δ, hvan]

theorem rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
  (hmk : cells m k = true) :
  ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
    AvgOracleCostBound k
      (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      (fun S ↦ program res n m k (groverParallelMarkingOracle m S))
      (relCost m k * vanillaFindAnyCost n m k) := by
  apply rel_cost_of_margin res hmk
  have hπ20 : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have hcostR : (relCost m k : ℝ) = 257079632679489661923 / 314159265358979323846 := by
    dsimp only [relCost]
    norm_num
  rw [hcostR]
  linarith


end

end QuantumComputation.Specs.GroverSolution.FindAny
