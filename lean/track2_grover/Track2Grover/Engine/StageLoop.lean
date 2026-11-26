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

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import QuantumComputation.Algorithms.Grover.Amplitude
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.Registers.Reset
public import Track2Grover.Engine.SpecDefs
/-
# Register Layout & Multi-Target Stage Loop (`StageLoop`)
-/
section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

section Sec_Registers
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting QProg Matrix
/- ## Dyadic grid membership -/
/-- Computable membership test for `groverGrid = {2^0,..., 2^10}` reducing directly in
  `whnf`. -/
def isGridElem (x : ℕ) : Bool :=
  x == 1 || x == 2 || x == 4 || x == 8 || x == 16 || x == 32 ||
    x == 64 || x == 128 || x == 256 || x == 512 || x == 1024
/-- Computable cell selector claiming all 121 cells of `groverGrid × groverGrid`. -/
def isGridCell (m k : ℕ) : Bool :=
  isGridElem m && isGridElem k
theorem isGridElem_iff (x : ℕ) :
    isGridElem x = true ↔ ∃ i ∈ Finset.range 11, 2 ^ i = x := by
  unfold isGridElem; simp only [Bool.or_eq_true, beq_iff_eq, Finset.mem_range]
  constructor
  · rintro ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨3, by omega, rfl⟩
    · exact ⟨4, by omega, rfl⟩
    · exact ⟨5, by omega, rfl⟩
    · exact ⟨6, by omega, rfl⟩
    · exact ⟨7, by omega, rfl⟩
    · exact ⟨8, by omega, rfl⟩
    · exact ⟨9, by omega, rfl⟩
    · exact ⟨10, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> norm_num
theorem pos_of_isGridElem {x : ℕ} (hx : isGridElem x = true) : 1 ≤ x := by
  obtain ⟨i, _, rfl⟩ := (isGridElem_iff x).1 hx; exact Nat.one_le_two_pow
/- ## Register layout -/
/-- Total qubits `(n + 1) * m + n * k + 1`: `m` oracle slots, `k` memory slots, `1` zero
  wire. -/
def findAllQubits (n m k : ℕ) : ℕ :=
  (n + 1) * m + n * k + 1
/-- The `((n + 1) * m)`-qubit parallel oracle register at wires `0.. (n + 1) * m - 1`. -/
def oracleReg (n m k : ℕ) : QRegister ((n + 1) * m) (findAllQubits n m k) :=
  QRegister.block 0 ((n + 1) * m) (by unfold findAllQubits; omega)
/-- Slot `i: Fin m` within the `((n + 1) * m)`-qubit oracle register. -/
def localSlotReg (n m : ℕ) (i : Fin m) : QRegister (n + 1) ((n + 1) * m) :=
  QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])
/-- Slot `i: Fin m` within the global `findAllQubits n m k`-qubit register. -/
def slotReg (n m k : ℕ) (i : Fin m) : QRegister (n + 1) (findAllQubits n m k) :=
  (oracleReg n m k).compose (localSlotReg n m i)
/-- Marker wire `0` within a single `(n + 1)`-qubit slot. -/
def localMarkerReg (n : ℕ) : QRegister 1 (n + 1) :=
  QRegister.block 0 1 (by omega)
/-- Index wires `1.. n` within a single `(n + 1)`-qubit slot. -/
def localIdxReg (n : ℕ) : QRegister n (n + 1) :=
  QRegister.block 1 n (by omega)
/-- Marker wire of slot `i` in the global register. -/
def markerReg (n m k : ℕ) (i : Fin m) : QRegister 1 (findAllQubits n m k) :=
  (slotReg n m k i).compose (localMarkerReg n)
/-- Index subregister of slot `i` in the global register. -/
def idxReg (n m k : ℕ) (i : Fin m) : QRegister n (findAllQubits n m k) :=
  (slotReg n m k i).compose (localIdxReg n)
/-- Combined `n * k`-qubit target memory register after the oracle slots. -/
def memAllReg (n m k : ℕ) : QRegister (n * k) (findAllQubits n m k) :=
  QRegister.block ((n + 1) * m) (n * k) (by unfold findAllQubits; omega)
/-- Memory slot `j: Fin k` within `memAllReg`. -/
def localMemSlotReg (n k : ℕ) (j : Fin k) : QRegister n (n * k) :=
  QRegister.block (j.val * n) n (by nlinarith [j.isLt])
/-- Memory slot `j: Fin k` within the global register. -/
def memSlotReg (n m k : ℕ) (j : Fin k) : QRegister n (findAllQubits n m k) :=
  (memAllReg n m k).compose (localMemSlotReg n k j)
/-- Dedicated clean `|0⟩` wire at `(n + 1) * m + n * k`, used to clear `res` before
  `.qWhile`. -/
def zeroReg (n m k : ℕ) : QRegister 1 (findAllQubits n m k) :=
  QRegister.block ((n + 1) * m + n * k) 1 (by unfold findAllQubits; omega)
@[simp]
theorem oracleReg_apply_val (n m k : ℕ) (w : Fin ((n + 1) * m)) :
    (oracleReg n m k w).val = w.val := by
  simp only [oracleReg, QRegister.block_apply_val, zero_add]
@[simp]
theorem slotReg_apply_val (n m k : ℕ) (i : Fin m) (w : Fin (n + 1)) :
    (slotReg n m k i w).val = i.val * (n + 1) + w.val := by
  simp only [slotReg, QRegister.compose_apply, oracleReg_apply_val, localSlotReg,
    QRegister.block_apply_val]
@[simp]
theorem markerReg_apply_val (n m k : ℕ) (i : Fin m) (w : Fin 1) :
    (markerReg n m k i w).val = i.val * (n + 1) + w.val := by
  simp only [markerReg, QRegister.compose_apply, slotReg_apply_val, localMarkerReg,
    QRegister.block_apply_val, zero_add]
@[simp]
theorem idxReg_apply_val (n m k : ℕ) (i : Fin m) (w : Fin n) :
    (idxReg n m k i w).val = i.val * (n + 1) + (1 + w.val) := by
  simp only [idxReg, QRegister.compose_apply, slotReg_apply_val, localIdxReg,
    QRegister.block_apply_val]
@[simp]
theorem memAllReg_apply_val (n m k : ℕ) (w : Fin (n * k)) :
    (memAllReg n m k w).val = (n + 1) * m + w.val := by
  simp only [memAllReg, QRegister.block_apply_val]
@[simp]
theorem memSlotReg_apply_val (n m k : ℕ) (j : Fin k) (w : Fin n) :
    (memSlotReg n m k j w).val = (n + 1) * m + (j.val * n + w.val) := by
  simp only [memSlotReg, QRegister.compose_apply, memAllReg_apply_val, localMemSlotReg,
    QRegister.block_apply_val]
@[simp]
theorem zeroReg_apply_val (n m k : ℕ) (w : Fin 1) :
    (zeroReg n m k w).val = (n + 1) * m + n * k + w.val := by
  simp only [zeroReg, QRegister.block_apply_val]
theorem localMarkerReg_disjoint_localIdxReg (n : ℕ) :
    (localMarkerReg n).DisjointWires (localIdxReg n) :=
  QRegister.block_disjoint_of_le 0 1 1 n (by omega) (by omega) (by omega)
theorem localSlotReg_disjoint {n m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (localSlotReg n m i).DisjointWires (localSlotReg n m j) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
  · exact QRegister.block_disjoint_of_le _ _ _ _ _ _ (by nlinarith)
  · exact QRegister.disjoint_comm.2
      (QRegister.block_disjoint_of_le _ _ _ _ _ _ (by nlinarith))
theorem slotReg_disjoint {n m k : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (slotReg n m k i).DisjointWires (slotReg n m k j) := by
  rw [QRegister.disjoint_iff]; intro a b heq
  have hval := congrArg Fin.val heq; simp only [slotReg_apply_val] at hval
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith [a.isLt, b.isLt]
theorem oracleReg_disjoint_memAllReg (n m k : ℕ) :
    (oracleReg n m k).DisjointWires (memAllReg n m k) :=
  QRegister.block_disjoint_of_le 0 ((n + 1) * m) ((n + 1) * m) (n * k) _ _ (by omega)
theorem oracleReg_disjoint_zeroReg (n m k : ℕ) :
    (oracleReg n m k).DisjointWires (zeroReg n m k) :=
  QRegister.block_disjoint_of_le 0 ((n + 1) * m) ((n + 1) * m + n * k) 1 _ _ (by omega)
theorem memAllReg_disjoint_zeroReg (n m k : ℕ) :
    (memAllReg n m k).DisjointWires (zeroReg n m k) :=
  QRegister.block_disjoint_of_le ((n + 1) * m) (n * k) ((n + 1) * m + n * k) 1 _ _ (by omega)
theorem memSlotReg_disjoint {n m k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    (memSlotReg n m k i).DisjointWires (memSlotReg n m k j) := by
  rw [QRegister.disjoint_iff]; intro a b heq
  have hval := congrArg Fin.val heq; simp only [memSlotReg_apply_val] at hval
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith [a.isLt, b.isLt]
/- ## Readout endianness matching `decodeTargets` -/
theorem extractIndex_localMemSlotReg_eq {n k : ℕ} (z : Fin (2 ^ (n * k))) (j : Fin k) :
    (localMemSlotReg n k j).extractIndex z =
      ⟨(z.val / (2 ^ n) ^ j.val) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ := by
  apply (basisBits n).injective
  funext b
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
  simp only [localMemSlotReg, QRegister.block_apply_val]; congr 1; rw [← pow_mul, mul_comm n j.val]
  have hmod : (z.val / 2 ^ (j.val * n) % 2 ^ n) / 2 ^ b.val % 2 =
      (z.val / 2 ^ (j.val * n)) / 2 ^ b.val % 2 := by
    obtain ⟨q, hq⟩ : ∃ q, 2 ^ n = 2 ^ b.val * (2 * q) := by
      refine ⟨2 ^ (n - (b.val + 1)), ?_⟩
      rw [← mul_assoc, ← pow_succ, ← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt b.isLt)]
    rw [hq, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 q)]
  rw [hmod, Nat.div_div_eq_div_mul, ← pow_add]
theorem extractIndex_localSlotReg_eq {n m : ℕ} (z : Fin (2 ^ ((n + 1) * m))) (i : Fin m) :
    (localSlotReg n m i).extractIndex z =
      ⟨(z.val / (2 ^ (n + 1)) ^ i.val) % 2 ^ (n + 1), Nat.mod_lt _ (by positivity)⟩ :=
  extractIndex_localMemSlotReg_eq (n := n + 1) (k := m) z i
theorem extractIndex_localMarkerReg_eq {n : ℕ} (u : Fin (2 ^ (n + 1))) :
    (localMarkerReg n).extractIndex u = ⟨u.val % 2, Nat.mod_lt _ (by positivity)⟩ := by
  apply (basisBits 1).injective
  funext b
  have hb0 : b.val = 0 := by omega
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
  simp only [localMarkerReg, QRegister.block_apply_val, hb0, add_zero, pow_zero, Nat.div_one]
  congr 1
  exact (Nat.mod_mod_of_dvd u.val (by norm_num)).symm
theorem extractIndex_localIdxReg_eq {n : ℕ} (u : Fin (2 ^ (n + 1))) :
    (localIdxReg n).extractIndex u = ⟨(u.val / 2) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ := by
  apply (basisBits n).injective
  funext b
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
  simp only [localIdxReg, QRegister.block_apply_val]; congr 1
  have hu : u.val / 2 < 2 ^ n := by
    have hlt : u.val < 2 * 2 ^ n := by linarith [u.isLt, pow_succ' 2 n]
    omega
  have hp : 2 ^ (1 + b.val) = 2 * 2 ^ b.val := by rw [pow_add, pow_one]
  rw [Nat.mod_eq_of_lt hu, Nat.div_div_eq_div_mul, hp]
/- ## Real matrices and zero-cost `phaseI` wrapper -/
/-- A complex matrix whose entries all have zero imaginary part. -/
def IsRealMatrix {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ a b, (M a b).im = 0
theorem isRealMatrix_one (d : ℕ) : IsRealMatrix (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro a b
  by_cases h : a = b <;> simp [Matrix.one_apply, h]
theorem isRealMatrix_mul {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : IsRealMatrix A) (hB : IsRealMatrix B) : IsRealMatrix (A * B) := by
  intro a b; rw [Matrix.mul_apply, Complex.im_sum]
  exact Finset.sum_eq_zero fun c _ ↦ by
    rw [Complex.mul_im, hA a c, hB c b]; ring
theorem isRealMatrix_listProd {d : ℕ} (L : List (Unitary d))
    (hL : ∀ U ∈ L, IsRealMatrix U.1) : IsRealMatrix (L.prod : Unitary d).1 := by
  induction L with
  | nil => exact isRealMatrix_one d
  | cons U Us ih =>
      rw [List.prod_cons, Submonoid.coe_mul]
      exact isRealMatrix_mul (hL U List.mem_cons_self)
        (ih fun V hV ↦ hL V (List.mem_cons_of_mem U hV))
theorem isRealMatrix_embedMatrix {k n : ℕ} (r : QRegister k n)
    {A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ} (hA : IsRealMatrix A) :
    IsRealMatrix (r.embedMatrix A) := by
  intro a b; rw [QRegister.embedMatrix_apply]
  split_ifs
  · simpa using hA _ _
  · simp
theorem isRealMatrix_permutationUnitary {d : ℕ} (e : Equiv.Perm (Fin d)) :
    IsRealMatrix (permutationUnitary e).1 := by
  intro a b; change (Equiv.Perm.permMatrix ℂ (e⁻¹) a b).im = 0
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]
  split_ifs <;> simp
/-- Multiply a unitary by global phase `i`, leaving projective QHL semantics identical while
  making the matrix purely imaginary on every nonzero real entry so it cannot collide with
  any
  embedded real oracle matrix. -/
noncomputable def phaseI {d : ℕ} (U : Unitary d) : Unitary d :=
  ⟨Complex.I • U.1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hI : Complex.I * star Complex.I = 1 := by simp
    have hU : U.1 * U.1ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact U.2.2
    rw [hI, one_smul, hU]⟩
@[simp]
theorem phaseI_val {d : ℕ} (U : Unitary d) : (phaseI U).1 = Complex.I • U.1 := rfl
@[simp]
theorem phaseI_conj {d : ℕ} (U : Unitary d) (M : HermitianMat (Fin d) ℂ) :
    M.conj (phaseI U).1 = M.conj U.1 := by
  ext1
  simp only [HermitianMat.conj_apply_mat, phaseI_val, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hI : star Complex.I * Complex.I = 1 := by simp
  rw [hI, one_smul]
@[simp]
theorem qAssign_phaseI {Var : Type} {d : ℕ} (U : Unitary d) (Θ : CQAssertion (Store Var) d) :
    Θ.qAssign (phaseI U) = Θ.qAssign U := by
  funext σ
  ext1; ext1
  change ((Θ σ).1.conj (phaseI U).1ᴴ).mat = ((Θ σ).1.conj U.1ᴴ).mat
  simp only [HermitianMat.conj_apply_mat, phaseI_val, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star]
  have hI : Complex.I * star Complex.I = 1 := by simp
  rw [hI, one_smul]
theorem phaseI_ne_of_isRealMatrix {d : ℕ} [NeZero d] {U V : Unitary d}
    (hU : IsRealMatrix U.1) (hV : IsRealMatrix V.1) : phaseI U ≠ V := by
  intro heq
  have hcol : ∃ j : Fin d, U.1 j 0 ≠ 0 := by
    by_contra! hall
    have hunit : (U.1ᴴ * U.1) 0 0 = 1 := by
      have h : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
      simpa using congr($h 0 0)
    rw [Matrix.mul_apply] at hunit; simp [hall] at hunit
  obtain ⟨j, hj⟩ := hcol
  have hre : (U.1 j 0).re ≠ 0 := by intro hre0; exact hj (Complex.ext hre0 (hU j 0))
  have him : ((phaseI U).1 j 0).im = (U.1 j 0).re := by simp [phaseI]
  rw [heq, hV j 0] at him; exact hre him.symm
theorem ofEmbeddedOracle_unitaryCost_phaseI_eq_zero {k Q : ℕ}
    {oracle : Unitary (2 ^ k)} (horacle : IsRealMatrix oracle.1)
    {U : Unitary (2 ^ Q)} (hU : IsRealMatrix U.1) :
    (CostModel.ofEmbeddedOracle (n := Q) oracle).unitaryCost (phaseI U) = 0 := by
  simp only [CostModel.ofEmbeddedOracle, ite_eq_right_iff, one_ne_zero]
  rintro ⟨r, heq⟩
  exact phaseI_ne_of_isRealMatrix hU (isRealMatrix_embedMatrix r horacle) heq
/- ## Conditional bit-flip combinator `xorRegCircuit` (reset and classical-to-quantum write) -/
/-- Bitwise XOR on `Fin (2 ^ Q)` by an additive bit vector `v: BitAssignment Q`. -/
def xorBitsPerm {Q : ℕ} (v : BitAssignment Q) : Equiv.Perm (Fin (2 ^ Q)) :=
  (basisBits Q).symm.permCongr (Equiv.addRight v)
@[simp]
theorem basisBits_xorBitsPerm {Q : ℕ} (v : BitAssignment Q) (z : Fin (2 ^ Q)) :
    basisBits Q (xorBitsPerm v z) = basisBits Q z + v := by
  simp [xorBitsPerm]
theorem xorBitsPerm_zero (Q : ℕ) : xorBitsPerm (0 : BitAssignment Q) = 1 :=
  Equiv.ext fun z ↦ (basisBits Q).injective (by simp)
theorem xorBitsPerm_add {Q : ℕ} (u v : BitAssignment Q) :
    xorBitsPerm u * xorBitsPerm v = xorBitsPerm (u + v) :=
  Equiv.ext fun z ↦
    (basisBits Q).injective (by simp [Equiv.Perm.mul_apply, add_assoc, add_comm u v])
theorem permutationUnitary_mul {d : ℕ} (e₁ e₂ : Equiv.Perm (Fin d)) :
    permutationUnitary e₁ * permutationUnitary e₂ = permutationUnitary (e₁ * e₂) := by
  apply Subtype.ext; rw [Submonoid.coe_mul]
  have hvec (b : Fin d) :
      ((permutationUnitary e₁).1 * (permutationUnitary e₂).1) *ᵥ Pi.single b (1 : ℂ) =
        (permutationUnitary (e₁ * e₂)).1 *ᵥ Pi.single b (1 : ℂ) := by
    rw [← Matrix.mulVec_mulVec, permutationUnitary_mulVec_single, permutationUnitary_mulVec_single,
      permutationUnitary_mulVec_single, Equiv.Perm.mul_apply]
  ext a b
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hvec b) a
@[simp]
theorem permutationUnitary_one (d : ℕ) :
    permutationUnitary (1 : Equiv.Perm (Fin d)) = 1 := by
  apply Subtype.ext; simp [permutationUnitary]
/-- Bit vector toggling the `w`-th logical wire of `r` when bit `w` of `mask` is `1`. -/
def regBitMask {W Q : ℕ} (r : QRegister W Q) (mask : ℕ) (w : Fin W) : BitAssignment Q :=
  if mask.testBit w.val then Pi.single (r w) 1 else 0
/-- Combined bit vector XORing the first `W` bits of `mask` onto `r`. -/
def regMaskVec {W Q : ℕ} (r : QRegister W Q) (mask : ℕ) : BitAssignment Q :=
  ∑ w : Fin W, regBitMask r mask w
theorem regMaskVec_apply_reg {W Q : ℕ} (r : QRegister W Q) (mask : ℕ) (w : Fin W) :
    regMaskVec r mask (r w) = if mask.testBit w.val then 1 else 0 := by
  simp only [regMaskVec, Finset.sum_apply, regBitMask]; rw [Finset.sum_eq_single w]
  · split_ifs <;> simp
  · intro w' _ hw'
    have hne : r w ≠ r w' := fun h ↦ hw' (r.wires.injective h).symm
    split_ifs <;> simp [hne]
  · intro hw; exact (hw (Finset.mem_univ w)).elim
theorem regMaskVec_apply_outside {W Q : ℕ} (r : QRegister W Q) (mask : ℕ) (q : Wire Q)
    (hq : q ∉ Set.range r.wires) :
    regMaskVec r mask q = 0 := by
  simp only [regMaskVec, Finset.sum_apply, regBitMask]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  have hne : q ≠ r w := fun h ↦ hq ⟨w, h.symm⟩
  split_ifs <;> simp [hne]
/-- Auxiliary list-driven conditional bit-flip circuit over a list of logical wire indices. -/
noncomputable def xorRegListCircuit {Var : Type} {W Q oracleWidth : ℕ}
    (res : Var) (extractMask : ℤ → ℕ) (r : QRegister W Q)
    (ws : List (Fin W)) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q oracleWidth :=
  OracleDynamicCircuit.sequence <|
    ws.map fun w ↦
      .qIf (fun σ ↦ (extractMask (σ res)).testBit w.val = true)
        (.step (phaseI (permutationUnitary (xorBitsPerm (Pi.single (r w) 1)))))
        .skip
/-- Flip each wire `r w` (`w: Fin W`) conditioned on `(extractMask (σ res)).testBit w.val`. -/
noncomputable def xorRegCircuit {Var : Type} {W Q oracleWidth : ℕ}
    (res : Var) (extractMask : ℤ → ℕ) (r : QRegister W Q) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q oracleWidth :=
  xorRegListCircuit res extractMask r (List.finRange W)
theorem costBound_xorRegListCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    {oracle : Unitary (2 ^ oracleWidth)} (horacle : IsRealMatrix oracle.1)
    (res : Var) (extractMask : ℤ → ℕ) (r : QRegister W Q) (ws : List (Fin W)) :
    CostBound (CostModel.ofEmbeddedOracle (n := Q) oracle)
      ((xorRegListCircuit res extractMask r ws).compile QProg.qAssign oracle) 0 := by
  let model := CostModel.ofEmbeddedOracle (n := Q) oracle
  induction ws with
  | nil =>
      simpa [xorRegListCircuit] using CostBound.skip_zero model
  | cons w ws ih =>
      simp only [xorRegListCircuit, List.map_cons, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_qIf,
        OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_skip]
      have hstep : CostBound model
          (QProg.qAssign (phaseI (permutationUnitary (xorBitsPerm (Pi.single (r w) 1)))) :
            QProg Var (2 ^ Q)) 0 := by
        have hcost := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero (Q := Q) horacle
          (isRealMatrix_permutationUnitary (xorBitsPerm (Pi.single (r w) 1)))
        simpa [model, hcost] using CostBound.qAssign (Var := Var) model
          (phaseI (permutationUnitary (xorBitsPerm (Pi.single (r w) 1))))
      have hbranch := CostBound.qIf
        (fun σ : Store Var ↦ (extractMask (σ res)).testBit w.val = true)
        hstep (CostBound.skip_zero model)
      simpa [xorRegListCircuit] using CostBound.seq hbranch ih
theorem costBound_xorRegCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    {oracle : Unitary (2 ^ oracleWidth)} (horacle : IsRealMatrix oracle.1)
    (res : Var) (extractMask : ℤ → ℕ) (r : QRegister W Q) :
    CostBound (CostModel.ofEmbeddedOracle (n := Q) oracle)
      ((xorRegCircuit res extractMask r).compile QProg.qAssign oracle) 0 :=
  costBound_xorRegListCircuit horacle res extractMask r (List.finRange W)
theorem wp_xorRegListCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    (oracle : Unitary (2 ^ oracleWidth)) (res : Var) (extractMask : ℤ → ℕ)
    (r : QRegister W Q) (ws : List (Fin W))
    (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    wp ((xorRegListCircuit res extractMask r ws).compile QProg.qAssign oracle) Θ σ =
      (Θ.qAssign (permutationUnitary
        (xorBitsPerm (ws.map (regBitMask r (extractMask (σ res)))).sum))) σ := by
  induction ws generalizing Θ σ with
  | nil =>
      simp [xorRegListCircuit, xorBitsPerm_zero]
  | cons w ws ih =>
      rw [xorRegListCircuit, List.map_cons, OracleDynamicCircuit.sequence_cons, ← xorRegListCircuit]
      simp only [List.map_cons, List.sum_cons, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_qIf, OracleDynamicCircuit.compile_step,
        OracleDynamicCircuit.compile_skip, wp_qSeq, wp_qIf, wp_qAssign, wp_skip, qAssign_phaseI]
      have hsub :
          ∀ Ψ : CQAssertion (Store Var) (2 ^ Q),
            wp ((xorRegListCircuit res extractMask r ws).compile QProg.qAssign oracle) Ψ =
              fun τ ↦ (Ψ.qAssign (permutationUnitary
                (xorBitsPerm (ws.map (regBitMask r (extractMask (τ res)))).sum))) τ := by
        intro Ψ
        funext τ
        exact ih Ψ τ
      rw [hsub]
      by_cases hb : (extractMask (σ res)).testBit w.val = true
      · simp only [hb, ↓reduceIte, regBitMask]
        rw [CQAssertion.qAssign_apply, ← CQAssertion.qAssign_apply, CQAssertion.qAssign_qAssign,
          permutationUnitary_mul, xorBitsPerm_add, add_comm]
      · simp [hb, regBitMask]
theorem wp_xorRegCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    (oracle : Unitary (2 ^ oracleWidth)) (res : Var) (extractMask : ℤ → ℕ)
    (r : QRegister W Q) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    wp ((xorRegCircuit res extractMask r).compile QProg.qAssign oracle) Θ σ =
      (Θ.qAssign (permutationUnitary (xorBitsPerm (regMaskVec r (extractMask (σ res)))))) σ := by
  rw [xorRegCircuit, wp_xorRegListCircuit]
  have hsum : ((List.finRange W).map (regBitMask r (extractMask (σ res)))).sum =
      regMaskVec r (extractMask (σ res)) := by
    rw [regMaskVec, ← Fin.sum_univ_def]
  rw [hsum]
theorem lossless_xorRegListCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    (oracle : Unitary (2 ^ oracleWidth)) (res : Var) (extractMask : ℤ → ℕ)
    (r : QRegister W Q) (ws : List (Fin W)) :
    Lossless ((xorRegListCircuit res extractMask r ws).compile QProg.qAssign oracle) := by
  induction ws with
  | nil =>
      simpa [xorRegListCircuit] using Lossless.skip
  | cons w ws ih =>
      simp only [xorRegListCircuit, List.map_cons, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_qIf,
        OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_skip]
      exact (Lossless.qIf _ (Lossless.qAssign _) Lossless.skip).seq ih
theorem lossless_xorRegCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    (oracle : Unitary (2 ^ oracleWidth)) (res : Var) (extractMask : ℤ → ℕ)
    (r : QRegister W Q) :
    Lossless ((xorRegCircuit res extractMask r).compile QProg.qAssign oracle) :=
  lossless_xorRegListCircuit oracle res extractMask r (List.finRange W)
/- ### Resetting a register to `|0^W⟩` via measurement + `xorRegCircuit` -/
/-- Reset `r` to `|0^W⟩` by measuring `r` into `res` and conditionally flipping set bits. -/
noncomputable def resetRegCircuit {Var : Type} {W Q oracleWidth : ℕ}
    (res : Var) (r : QRegister W Q) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q oracleWidth :=
  .seq (.measure res r) (xorRegCircuit res Int.toNat r)
theorem xorBitsPerm_regMaskVec_eq_replaceIndex_zero {W Q : ℕ} (r : QRegister W Q)
    (o : Fin (2 ^ W)) (z : Fin (2 ^ Q)) (hz : r.extractIndex z = o) :
    xorBitsPerm (regMaskVec r o.val) z = r.replaceIndex z 0 := by
  apply (basisBits Q).injective
  funext q
  rw [basisBits_xorBitsPerm, Pi.add_apply]
  by_cases hq : q ∈ Set.range r.wires
  · obtain ⟨w, rfl⟩ := hq
    rw [regMaskVec_apply_reg, r.basisBits_replaceIndex_apply, basisBits_zero, Pi.zero_apply,
      ← r.basisBits_extractIndex, hz, basisBits_eq_testBit]
    (cases o.val.testBit w.val <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero]); rfl
  · rw [regMaskVec_apply_outside r o.val q hq, add_zero,
      r.basisBits_replaceIndex_of_not_mem _ _ _ hq]
theorem permutationUnitary_regMaskVec_mul_basisOutcomeProjector {W Q : ℕ}
    (r : QRegister W Q) (o : Fin (2 ^ W)) :
    (permutationUnitary (xorBitsPerm (regMaskVec r o.val))).1 * r.basisOutcomeProjector o =
      r.resetKraus o := by
  have hvec (b : Fin (2 ^ Q)) :
      ((permutationUnitary (xorBitsPerm (regMaskVec r o.val))).1 * r.basisOutcomeProjector o) *ᵥ
          Pi.single b (1 : ℂ) =
        r.resetKraus o *ᵥ Pi.single b (1 : ℂ) := by
    rw [← Matrix.mulVec_mulVec, r.basisOutcomeProjector_mulVec_single]
    conv_rhs =>
      rw [← r.tensorState_single_factors b, r.resetKraus_mulVec_tensorState]
    by_cases hb : r.extractIndex b = o
    · rw [ite_eq_left hb, permutationUnitary_mulVec_single,
        xorBitsPerm_regMaskVec_eq_replaceIndex_zero r o b hb]
      have hsingle : (Pi.single (M := fun _ ↦ ℂ) (r.extractIndex b) 1) o = 1 := by simp [hb]
      rw [hsingle, r.tensorState_single_replaceIndex]
    · have hsingle : (Pi.single (M := fun _ ↦ ℂ) (r.extractIndex b) 1) o = 0 :=
        Pi.single_eq_of_ne' hb 1
      rw [ite_eq_right hb, Matrix.mulVec_zero, hsingle]
      have hzero : (Pi.single (M := fun _ ↦ ℂ) (0 : Fin (2 ^ W)) 0) = 0 := by simp
      rw [hzero, r.tensorState_zero_left]
  ext a b
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hvec b) a
theorem wp_resetRegCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    (oracle : Unitary (2 ^ oracleWidth)) (res : Var) (r : QRegister W Q)
    (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    (wp ((resetRegCircuit res r).compile QProg.qAssign oracle) Θ σ).1.mat =
      ∑ o : Fin (2 ^ W),
        (r.resetKraus o)ᴴ * (Θ (Store.subst σ res ↑o.val)).1.mat * r.resetKraus o := by
  simp only [resetRegCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_measure, wp_qSeq]
  rw [wp_measureRegister_coe_ax, HermitianMat.mat_finset_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [HermitianMat.conj_apply_mat,
    r.basisOutcomeProjector_conjTranspose, r.basisOutcomeProjector_conjTranspose, wp_xorRegCircuit]
  have htoNat : ((Store.subst σ res (o.val : Expr Var)) res).toNat = o.val := by simp [Store.subst]
  rw [htoNat]
  let Uo := permutationUnitary (xorBitsPerm (regMaskVec r o.val))
  have hqa : ((Θ.qAssign Uo) (Store.subst σ res ↑o.val)).1.mat =
      Uo.1ᴴ * (Θ (Store.subst σ res ↑o.val)).1.mat * Uo.1 := by
    rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe]
  rw [hqa]
  have hmul : Uo.1 * r.basisOutcomeProjector o = r.resetKraus o :=
    permutationUnitary_regMaskVec_mul_basisOutcomeProjector r o
  calc r.basisOutcomeProjector o *
        (Uo.1ᴴ * (Θ (Store.subst σ res ↑o.val)).1.mat * Uo.1) *
        r.basisOutcomeProjector o
      = (Uo.1 * r.basisOutcomeProjector o)ᴴ * (Θ (Store.subst σ res ↑o.val)).1.mat *
          (Uo.1 * r.basisOutcomeProjector o) := by
          simp only [Matrix.conjTranspose_mul, r.basisOutcomeProjector_conjTranspose,
            Matrix.mul_assoc]
    _ = (r.resetKraus o)ᴴ * (Θ (Store.subst σ res ↑o.val)).1.mat * r.resetKraus o := by rw [hmul]
theorem costBound_resetRegCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    {oracle : Unitary (2 ^ oracleWidth)} (horacle : IsRealMatrix oracle.1)
    (res : Var) (r : QRegister W Q) :
    CostBound (CostModel.ofEmbeddedOracle oracle)
      ((resetRegCircuit res r).compile QProg.qAssign oracle) 0 := by
  simp only [resetRegCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_measure, QProg.measureRegister]
  simpa using CostBound.seq (CostBound.qMeasure _ _ _)
    (costBound_xorRegCircuit horacle res Int.toNat r)
theorem lossless_resetRegCircuit {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ}
    (oracle : Unitary (2 ^ oracleWidth)) (res : Var) (r : QRegister W Q) :
    Lossless ((resetRegCircuit res r).compile QProg.qAssign oracle) := by
  simp only [resetRegCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_measure, QProg.measureRegister]
  exact (Lossless.qMeasure res ⟨r.basisOutcomeProjector, by simp⟩).seq
    (lossless_xorRegCircuit oracle res Int.toNat r)
/- ### Writing a classical index into a clean `|0^W⟩` register -/
theorem xorBitsPerm_regMaskVec_of_clean {W Q : ℕ} (r : QRegister W Q)
    (val : Fin (2 ^ W)) (z : Fin (2 ^ Q)) (hz : r.extractIndex z = 0) :
    xorBitsPerm (regMaskVec r val.val) z = r.replaceIndex z val := by
  apply (basisBits Q).injective
  funext q
  rw [basisBits_xorBitsPerm, Pi.add_apply]
  by_cases hq : q ∈ Set.range r.wires
  · obtain ⟨w, rfl⟩ := hq
    rw [regMaskVec_apply_reg, r.basisBits_replaceIndex_apply, ← r.basisBits_extractIndex, hz,
      basisBits_zero, Pi.zero_apply, zero_add, basisBits_eq_testBit]
  · rw [regMaskVec_apply_outside r val.val q hq, add_zero,
      r.basisBits_replaceIndex_of_not_mem _ _ _ hq]
end QuantumComputation.Specs.GroverFindAll
end
end Sec_Registers
section Sec_MultiTargetAmplitude
section Sec_Unmarking
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting QProg Matrix
/- ## Local and parallel marking oracles (definitionally matching `Grover.lean`) -/

/-- Marking oracle `(b, x) ↦ (b ⊕ [x ∈ S], x)` on `n + 1` qubits. -/
noncomputable abbrev setMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  permutationUnitary (tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)
/-- Parallel `m`-slot marking oracle on `(n + 1) * m` qubits. -/
noncomputable abbrev parallelMarkingOracle {n : ℕ} (m : ℕ)
    (S : Finset (Fin (2 ^ n))) : Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])).embedUnitary
      (setMarkingOracle S)).prod
theorem isRealMatrix_setMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    IsRealMatrix (setMarkingOracle S).1 :=
  isRealMatrix_permutationUnitary _
theorem isRealMatrix_parallelMarkingOracle {n m : ℕ} (S : Finset (Fin (2 ^ n))) :
    IsRealMatrix (parallelMarkingOracle m S).1 := by
  refine isRealMatrix_listProd _ ?_
  intro U hU
  rw [List.mem_ofFn] at hU
  obtain ⟨i, rfl⟩ := hU
  exact isRealMatrix_embedMatrix _ (isRealMatrix_setMarkingOracle S)
/- ## Single-slot `tableAddPerm` bit action -/

/-- Underlying permutation of `setMarkingOracle S` on `Fin (2 ^ (n + 1))`. -/
abbrev slotMarkPerm {n : ℕ} (S : Finset (Fin (2 ^ n))) : Equiv.Perm (Fin (2 ^ (n + 1))) :=
  tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0
theorem splitBasisEquiv_symm_val {n : ℕ} (x : Fin (2 ^ n)) (b : Fin (2 ^ 1)) :
    ((splitBasisEquiv n 1).symm (x, b)).val = b.val + 2 * x.val := by
  simp [splitBasisEquiv, finProdFinEquiv]
theorem extractIndex_localMarkerReg_splitSymm {n : ℕ} (x : Fin (2 ^ n)) (b : Fin (2 ^ 1)) :
    (localMarkerReg n).extractIndex ((splitBasisEquiv n 1).symm (x, b)) = b := by
  ext
  rw [extractIndex_localMarkerReg_eq, splitBasisEquiv_symm_val]
  dsimp only
  have hb : b.val < 2 := b.isLt
  omega
theorem extractIndex_localIdxReg_splitSymm {n : ℕ} (x : Fin (2 ^ n)) (b : Fin (2 ^ 1)) :
    (localIdxReg n).extractIndex ((splitBasisEquiv n 1).symm (x, b)) = x := by
  ext
  rw [extractIndex_localIdxReg_eq, splitBasisEquiv_symm_val]
  dsimp only
  have hb : b.val < 2 := b.isLt
  have hdiv : (b.val + 2 * x.val) / 2 = x.val := by omega
  rw [hdiv, Nat.mod_eq_of_lt x.isLt]
theorem extractIndex_localIdxReg_slotMarkPerm {n : ℕ} (S : Finset (Fin (2 ^ n)))
    (u : Fin (2 ^ (n + 1))) :
    (localIdxReg n).extractIndex (slotMarkPerm S u) = (localIdxReg n).extractIndex u := by
  obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  have hperm : slotMarkPerm S ((splitBasisEquiv n 1).symm (x, b)) =
      (splitBasisEquiv n 1).symm (x, b + if x ∈ S then 1 else 0) := by
    simp [slotMarkPerm, tableAddPerm, addRightShear]
  rw [hperm, extractIndex_localIdxReg_splitSymm, extractIndex_localIdxReg_splitSymm]
theorem extractIndex_localMarkerReg_slotMarkPerm {n : ℕ} (S : Finset (Fin (2 ^ n)))
    (u : Fin (2 ^ (n + 1))) :
    (localMarkerReg n).extractIndex (slotMarkPerm S u) =
      (localMarkerReg n).extractIndex u + if (localIdxReg n).extractIndex u ∈ S then 1 else 0 := by
  obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  have hperm : slotMarkPerm S ((splitBasisEquiv n 1).symm (x, b)) =
      (splitBasisEquiv n 1).symm (x, b + if x ∈ S then 1 else 0) := by
    simp [slotMarkPerm, tableAddPerm, addRightShear]
  rw [hperm, extractIndex_localMarkerReg_splitSymm, extractIndex_localMarkerReg_splitSymm,
    extractIndex_localIdxReg_splitSymm]
theorem basisBits_slotMarkPerm {n : ℕ} (S : Finset (Fin (2 ^ n)))
    (u : Fin (2 ^ (n + 1))) (w : Fin (n + 1)) :
    basisBits (n + 1) (slotMarkPerm S u) w =
      basisBits (n + 1) u w +
        if w.val = 0 ∧ (localIdxReg n).extractIndex u ∈ S then 1 else 0 := by
  by_cases hw0 : w.val = 0
  · have hw : w = localMarkerReg n 0 := Fin.ext (by simp [localMarkerReg, hw0])
    rw [hw, ← (localMarkerReg n).basisBits_extractIndex,
      ← (localMarkerReg n).basisBits_extractIndex, extractIndex_localMarkerReg_slotMarkPerm]
    generalize (localMarkerReg n).extractIndex u = b
    simp only [localMarkerReg, QRegister.block_apply_val, Fin.val_zero, add_zero, true_and]
    by_cases hx : (localIdxReg n).extractIndex u ∈ S
    · simp only [hx, ↓reduceIte]
      fin_cases b <;> (rw [basisBits_eq_div_mod, basisBits_eq_div_mod]; rfl)
    · simp [hx]
  · have hw : w = localIdxReg n ⟨w.val - 1, by omega⟩ :=
      Fin.ext (by simp only [localIdxReg, QRegister.block_apply_val]; omega)
    simp only [hw0, false_and, ↓reduceIte, add_zero]
    rw [hw, ← (localIdxReg n).basisBits_extractIndex, ← (localIdxReg n).basisBits_extractIndex,
      extractIndex_localIdxReg_slotMarkPerm]
/- ## Global parallel marking action on `findAllQubits n m k` -/

theorem embedUnitary_listProd {W Q : ℕ} (r : QRegister W Q) (L : List (Unitary (2 ^ W))) :
    r.embedUnitary L.prod = (L.map r.embedUnitary).prod := by
  induction L with
  | nil => simp
  | cons U Us ih => rw [List.prod_cons, List.map_cons, List.prod_cons, r.embedUnitary_mul, ih]
theorem embedUnitary_parallelMarkingOracle (n m k : ℕ) (S : Finset (Fin (2 ^ n))) :
    (oracleReg n m k).embedUnitary (parallelMarkingOracle m S) =
      (List.ofFn fun i : Fin m ↦ (slotReg n m k i).embedUnitary (setMarkingOracle S)).prod := by
  rw [parallelMarkingOracle, embedUnitary_listProd, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i ↦ ?_))
  exact ((oracleReg n m k).embedUnitary_compose (localSlotReg n m i) (setMarkingOracle S)).symm
theorem markerReg_ne_idxReg {n m k : ℕ} (i i' : Fin m) (w : Fin n) :
    markerReg n m k i 0 ≠ idxReg n m k i' w := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [markerReg_apply_val, idxReg_apply_val, Fin.val_zero, add_zero] at hval
  have hw := w.isLt
  have hmod := congrArg (· % (n + 1)) hval
  rw [Nat.mul_mod_left, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hmod
  omega
theorem markerReg_ne_memSlotReg {n m k : ℕ} (i : Fin m) (j : Fin k) (w : Fin n) :
    markerReg n m k i 0 ≠ memSlotReg n m k j w := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [markerReg_apply_val, memSlotReg_apply_val, Fin.val_zero, add_zero] at hval
  nlinarith [i.isLt]
theorem markerReg_ne_zeroReg {n m k : ℕ} (i : Fin m) :
    markerReg n m k i 0 ≠ zeroReg n m k 0 := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [markerReg_apply_val, zeroReg_apply_val, Fin.val_zero, add_zero] at hval
  nlinarith [i.isLt]
theorem markerReg_injective {n m k : ℕ} {i i' : Fin m}
    (h : markerReg n m k i 0 = markerReg n m k i' 0) : i = i' := by
  have hval := congrArg Fin.val h
  simp only [markerReg_apply_val, Fin.val_zero, add_zero] at hval
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) hval)
/-- Bit vector toggling `markerReg n m k i 0` for each `i ∈ activeSlots` with `x_i ∈ S`. -/
def globalMarkShift (n m k : ℕ) (activeSlots : Finset (Fin m)) (S : Finset (Fin (2 ^ n)))
    (z : Fin (2 ^ findAllQubits n m k)) : BitAssignment (findAllQubits n m k) :=
  ∑ i ∈ activeSlots,
    if (idxReg n m k i).extractIndex z ∈ S then Pi.single (markerReg n m k i 0) 1 else 0
/-- Global basis transformation applying `setMarkingOracle S` across `activeSlots`. -/
def globalMarkOn (n m k : ℕ) (activeSlots : Finset (Fin m)) (S : Finset (Fin (2 ^ n)))
    (z : Fin (2 ^ findAllQubits n m k)) : Fin (2 ^ findAllQubits n m k) :=
  xorBitsPerm (globalMarkShift n m k activeSlots S z) z
/-- Global basis transformation applying `setMarkingOracle S` across all `m` slots. -/
abbrev globalMarkFun (n m k : ℕ) (S : Finset (Fin (2 ^ n)))
    (z : Fin (2 ^ findAllQubits n m k)) : Fin (2 ^ findAllQubits n m k) :=
  globalMarkOn n m k Finset.univ S z
theorem globalMarkShift_apply_outside_markers {n m k : ℕ} (activeSlots : Finset (Fin m))
    (S : Finset (Fin (2 ^ n))) (z : Fin (2 ^ findAllQubits n m k))
    (q : Wire (findAllQubits n m k)) (hq : ∀ i : Fin m, q ≠ markerReg n m k i 0) :
    globalMarkShift n m k activeSlots S z q = 0 := by
  simp only [globalMarkShift, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hne := hq i
  split_ifs <;> simp [hne]
theorem globalMarkShift_apply_marker {n m k : ℕ} (activeSlots : Finset (Fin m))
    (S : Finset (Fin (2 ^ n))) (z : Fin (2 ^ findAllQubits n m k)) (i : Fin m) :
    globalMarkShift n m k activeSlots S z (markerReg n m k i 0) =
      if i ∈ activeSlots ∧ (idxReg n m k i).extractIndex z ∈ S then 1 else 0 := by
  simp only [globalMarkShift, Finset.sum_apply]
  by_cases hi : i ∈ activeSlots
  · rw [Finset.sum_eq_single i]
    · by_cases hx : (idxReg n m k i).extractIndex z ∈ S <;> simp [hi, hx]
    · intro i' _ hi'
      have hne : markerReg n m k i 0 ≠ markerReg n m k i' 0 :=
        fun h ↦ hi' (markerReg_injective h).symm
      split_ifs <;> simp [hne]
    · intro habs
      exact (habs hi).elim
  · simp only [hi, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun i' hi' ↦ ?_
    have hne : markerReg n m k i 0 ≠ markerReg n m k i' 0 := by
      intro h
      exact hi (markerReg_injective h ▸ hi')
    split_ifs <;> simp [hne]
theorem extractIndex_idxReg_globalMarkOn {n m k : ℕ} (activeSlots : Finset (Fin m))
    (S : Finset (Fin (2 ^ n))) (z : Fin (2 ^ findAllQubits n m k)) (i : Fin m) :
    (idxReg n m k i).extractIndex (globalMarkOn n m k activeSlots S z) =
      (idxReg n m k i).extractIndex z := by
  apply (basisBits n).injective
  funext w
  rw [(idxReg n m k i).basisBits_extractIndex, (idxReg n m k i).basisBits_extractIndex,
    globalMarkOn, basisBits_xorBitsPerm, Pi.add_apply,
    globalMarkShift_apply_outside_markers _ _ _ _ (fun i' ↦ (markerReg_ne_idxReg i' i w).symm),
    add_zero]
theorem extractIndex_memSlotReg_globalMarkOn {n m k : ℕ} (activeSlots : Finset (Fin m))
    (S : Finset (Fin (2 ^ n))) (z : Fin (2 ^ findAllQubits n m k)) (j : Fin k) :
    (memSlotReg n m k j).extractIndex (globalMarkOn n m k activeSlots S z) =
      (memSlotReg n m k j).extractIndex z := by
  apply (basisBits n).injective
  funext w
  rw [(memSlotReg n m k j).basisBits_extractIndex, (memSlotReg n m k j).basisBits_extractIndex,
    globalMarkOn, basisBits_xorBitsPerm, Pi.add_apply,
    globalMarkShift_apply_outside_markers _ _ _ _ (fun i' ↦ (markerReg_ne_memSlotReg i' j w).symm),
    add_zero]
theorem extractIndex_zeroReg_globalMarkOn {n m k : ℕ} (activeSlots : Finset (Fin m))
    (S : Finset (Fin (2 ^ n))) (z : Fin (2 ^ findAllQubits n m k)) :
    (zeroReg n m k).extractIndex (globalMarkOn n m k activeSlots S z) =
      (zeroReg n m k).extractIndex z := by
  apply (basisBits 1).injective
  funext w
  have hw0 : w = 0 := Subsingleton.elim w 0
  subst hw0
  rw [(zeroReg n m k).basisBits_extractIndex, (zeroReg n m k).basisBits_extractIndex,
    globalMarkOn, basisBits_xorBitsPerm, Pi.add_apply,
    globalMarkShift_apply_outside_markers _ _ _ _ (fun i' ↦ (markerReg_ne_zeroReg i').symm),
    add_zero]
theorem slotReg_replaceIndex_slotMarkPerm {n m k : ℕ} (S : Finset (Fin (2 ^ n)))
    (i : Fin m) (z : Fin (2 ^ findAllQubits n m k)) :
    (slotReg n m k i).replaceIndex z (slotMarkPerm S ((slotReg n m k i).extractIndex z)) =
      globalMarkOn n m k {i} S z := by
  apply (basisBits (findAllQubits n m k)).injective
  funext q
  rw [globalMarkOn, basisBits_xorBitsPerm, Pi.add_apply]
  by_cases hq : q ∈ Set.range (slotReg n m k i).wires
  · obtain ⟨w, rfl⟩ := hq
    rw [(slotReg n m k i).basisBits_replaceIndex_apply, basisBits_slotMarkPerm,
      (slotReg n m k i).basisBits_extractIndex]
    have hidx : (localIdxReg n).extractIndex ((slotReg n m k i).extractIndex z) =
        (idxReg n m k i).extractIndex z := by
      rw [idxReg, QRegister.extractIndex_compose]
    rw [hidx]
    by_cases hw0 : w.val = 0
    · have hw : w = 0 := Fin.ext hw0
      subst hw
      have hmark : slotReg n m k i 0 = markerReg n m k i 0 := rfl
      rw [hmark, globalMarkShift_apply_marker]
      simp
    · have hne : ∀ i' : Fin m, slotReg n m k i w ≠ markerReg n m k i' 0 := by
        intro i'
        have hidxw : slotReg n m k i w = idxReg n m k i ⟨w.val - 1, by omega⟩ :=
          Fin.ext (by simp only [slotReg_apply_val, idxReg_apply_val]; omega)
        rw [hidxw]
        exact (markerReg_ne_idxReg i' i _).symm
      rw [globalMarkShift_apply_outside_markers _ _ _ _ hne]
      simp [hw0]
  · rw [(slotReg n m k i).basisBits_replaceIndex_of_not_mem _ _ _ hq]
    have hne : q ≠ markerReg n m k i 0 := by
      intro h
      exact hq ⟨0, h.symm⟩
    simp only [globalMarkShift, Finset.sum_singleton]
    split_ifs <;> simp [hne]
theorem slotEmbed_setMarkingOracle_mulVec_single {n m k : ℕ} (S : Finset (Fin (2 ^ n)))
    (i : Fin m) (z : Fin (2 ^ findAllQubits n m k)) :
    ((slotReg n m k i).embedUnitary (setMarkingOracle S)).1 *ᵥ Pi.single z (1 : ℂ) =
      Pi.single (globalMarkOn n m k {i} S z) 1 := by
  rw [QRegister.embedUnitary_val, (slotReg n m k i).embedMatrix_mulVec_single_factors,
    permutationUnitary_mulVec_single, (slotReg n m k i).tensorState_single_replaceIndex,
    slotReg_replaceIndex_slotMarkPerm]
theorem globalMarkOn_cons {n m k : ℕ} (S : Finset (Fin (2 ^ n))) (i : Fin m)
    (activeSlots : Finset (Fin m)) (hi : i ∉ activeSlots)
    (z : Fin (2 ^ findAllQubits n m k)) :
    globalMarkOn n m k {i} S (globalMarkOn n m k activeSlots S z) =
      globalMarkOn n m k (insert i activeSlots) S z := by
  have hshift : globalMarkShift n m k {i} S (globalMarkOn n m k activeSlots S z) =
      globalMarkShift n m k {i} S z := by
    simp only [globalMarkShift, Finset.sum_singleton, extractIndex_idxReg_globalMarkOn]
  apply (basisBits (findAllQubits n m k)).injective
  rw [globalMarkOn, basisBits_xorBitsPerm, hshift, globalMarkOn, basisBits_xorBitsPerm,
    globalMarkOn, basisBits_xorBitsPerm, add_assoc]
  congr 1
  rw [add_comm]
  simp only [globalMarkShift, Finset.sum_insert hi, Finset.sum_singleton]
theorem prod_slotEmbed_mulVec_single {n m k : ℕ} (S : Finset (Fin (2 ^ n)))
    (is : List (Fin m)) (hnd : is.Nodup) (z : Fin (2 ^ findAllQubits n m k)) :
    ((is.map fun i ↦ (slotReg n m k i).embedUnitary (setMarkingOracle S)).prod).1 *ᵥ
        Pi.single z (1 : ℂ) =
      Pi.single (globalMarkOn n m k is.toFinset S z) 1 := by
  induction is with
  | nil =>
      funext a
      simp [Matrix.col_apply, Matrix.one_apply, Pi.single_apply, eq_comm, globalMarkOn,
        globalMarkShift, xorBitsPerm_zero]
  | cons i is ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.prod_cons, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih hnd.2,
        slotEmbed_setMarkingOracle_mulVec_single,
        globalMarkOn_cons S i is.toFinset (by simpa using hnd.1) z, List.toFinset_cons]
theorem parallelMarkingOracle_mulVec_single (n m k : ℕ) (S : Finset (Fin (2 ^ n)))
    (z : Fin (2 ^ findAllQubits n m k)) :
    ((oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 *ᵥ Pi.single z (1 : ℂ) =
      Pi.single (globalMarkFun n m k S z) 1 := by
  rw [embedUnitary_parallelMarkingOracle, List.ofFn_eq_map]
  simpa [globalMarkFun] using prod_slotEmbed_mulVec_single S (List.finRange m)
    (List.nodup_finRange m) z
/- ## Coherent zero-cost unmarking of already-found targets -/

/-- Set of target indices stored in the `activeMem` memory registers of global basis state
  `z`. -/
def memFoundSet (n m k : ℕ) (activeMem : Finset (Fin k))
    (z : Fin (2 ^ findAllQubits n m k)) : Finset (Fin (2 ^ n)) :=
  activeMem.image fun j ↦ (memSlotReg n m k j).extractIndex z
theorem memFoundSet_globalMarkOn {n m k : ℕ} (activeMem : Finset (Fin k))
    (activeSlots : Finset (Fin m)) (S : Finset (Fin (2 ^ n)))
    (z : Fin (2 ^ findAllQubits n m k)) :
    memFoundSet n m k activeMem (globalMarkOn n m k activeSlots S z) =
      memFoundSet n m k activeMem z := by
  simp only [memFoundSet]
  refine Finset.image_congr fun j _ ↦ ?_
  exact extractIndex_memSlotReg_globalMarkOn activeSlots S z j
theorem globalMarkFun_comp {n m k : ℕ} (A B : Finset (Fin (2 ^ n)))
    (z : Fin (2 ^ findAllQubits n m k)) :
    globalMarkShift n m k Finset.univ A (globalMarkFun n m k B z) =
      globalMarkShift n m k Finset.univ A z := by
  funext q
  simp only [globalMarkShift, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [extractIndex_idxReg_globalMarkOn]
/-- Involutive basis transformation flipping `b_i` whenever `x_i ∈ memFoundSet z`. -/
def unmarkFun (n m k : ℕ) (activeMem : Finset (Fin k))
    (z : Fin (2 ^ findAllQubits n m k)) : Fin (2 ^ findAllQubits n m k) :=
  globalMarkFun n m k (memFoundSet n m k activeMem z) z
theorem unmarkFun_involutive (n m k : ℕ) (activeMem : Finset (Fin k)) :
    Function.Involutive (unmarkFun n m k activeMem) := by
  intro z
  set T := memFoundSet n m k activeMem z
  apply (basisBits (findAllQubits n m k)).injective
  funext q
  have h1 : unmarkFun n m k activeMem (unmarkFun n m k activeMem z) =
      xorBitsPerm (globalMarkShift n m k Finset.univ T (globalMarkFun n m k T z))
        (globalMarkFun n m k T z) := by
    simp only [unmarkFun, memFoundSet_globalMarkOn, T]
    rfl
  rw [h1, basisBits_xorBitsPerm, globalMarkFun_comp]
  have h2 : basisBits (findAllQubits n m k) (globalMarkFun n m k T z) =
      basisBits (findAllQubits n m k) z + globalMarkShift n m k Finset.univ T z :=
    basisBits_xorBitsPerm _ _
  rw [h2, Pi.add_apply, Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero, add_zero]
/-- Permutation unitary coherently unmarking every element currently stored in `activeMem`. -/
noncomputable def unmarkUnitary (n m k : ℕ) (activeMem : Finset (Fin k)) :
    Unitary (2 ^ findAllQubits n m k) :=
  permutationUnitary (unmarkFun_involutive n m k activeMem).toPerm
theorem isRealMatrix_unmarkUnitary (n m k : ℕ) (activeMem : Finset (Fin k)) :
    IsRealMatrix (unmarkUnitary n m k activeMem).1 :=
  isRealMatrix_permutationUnitary _
theorem unmarkFun_globalMarkFun_of_subset {n m k : ℕ} (activeMem : Finset (Fin k))
    {S : Finset (Fin (2 ^ n))} (z : Fin (2 ^ findAllQubits n m k))
    (hsub : memFoundSet n m k activeMem z ⊆ S) :
    unmarkFun n m k activeMem (globalMarkFun n m k S z) =
      globalMarkFun n m k (S \ memFoundSet n m k activeMem z) z := by
  set T := memFoundSet n m k activeMem z
  apply (basisBits (findAllQubits n m k)).injective
  funext q
  have h1 : unmarkFun n m k activeMem (globalMarkFun n m k S z) =
      xorBitsPerm (globalMarkShift n m k Finset.univ T (globalMarkFun n m k S z))
        (globalMarkFun n m k S z) := by
    simp only [unmarkFun, memFoundSet_globalMarkOn, T]
    rfl
  have h2 : basisBits (findAllQubits n m k) (globalMarkFun n m k S z) =
      basisBits (findAllQubits n m k) z + globalMarkShift n m k Finset.univ S z :=
    basisBits_xorBitsPerm _ _
  have h3 : basisBits (findAllQubits n m k) (globalMarkFun n m k (S \ T) z) =
      basisBits (findAllQubits n m k) z + globalMarkShift n m k Finset.univ (S \ T) z :=
    basisBits_xorBitsPerm _ _
  rw [h1, basisBits_xorBitsPerm, globalMarkFun_comp, h2, h3,
    Pi.add_apply, Pi.add_apply, Pi.add_apply, add_assoc]
  congr 1
  by_cases hq : ∃ i : Fin m, q = markerReg n m k i 0
  · obtain ⟨i, rfl⟩ := hq
    rw [globalMarkShift_apply_marker, globalMarkShift_apply_marker, globalMarkShift_apply_marker]
    simp only [Finset.mem_univ, true_and, Finset.mem_sdiff]
    by_cases hxT : (idxReg n m k i).extractIndex z ∈ T
    · have hxS : (idxReg n m k i).extractIndex z ∈ S := hsub hxT
      simp only [hxT, hxS, not_true_eq_false, and_false, ↓reduceIte]
      rfl
    · by_cases hxS : (idxReg n m k i).extractIndex z ∈ S <;> simp [hxT, hxS]
  · simp only [not_exists] at hq
    rw [globalMarkShift_apply_outside_markers _ _ _ _ hq,
      globalMarkShift_apply_outside_markers _ _ _ _ hq,
      globalMarkShift_apply_outside_markers _ _ _ _ hq, add_zero]
/-- Diagonal projector onto global basis states where `memSlotReg j` holds `memTuple j` for
  all
  `j ∈ activeMem`. -/
noncomputable def memTupleProj (n m k : ℕ) (activeMem : Finset (Fin k))
    (memTuple : Fin k → Fin (2 ^ n)) : Operator (2 ^ findAllQubits n m k) :=
  Matrix.diagonal fun z ↦
    if ∀ j ∈ activeMem, (memSlotReg n m k j).extractIndex z = memTuple j then 1 else 0
theorem memFoundSet_eq_image_of_memTuple {n m k : ℕ} (activeMem : Finset (Fin k))
    (memTuple : Fin k → Fin (2 ^ n)) (z : Fin (2 ^ findAllQubits n m k))
    (hz : ∀ j ∈ activeMem, (memSlotReg n m k j).extractIndex z = memTuple j) :
    memFoundSet n m k activeMem z = activeMem.image memTuple := by
  simp only [memFoundSet]
  exact Finset.image_congr hz
/-- Key unmarking identity: on the subspace `memTupleProj` where `activeMem` holds `T ⊆ S`,
  following the embedded parallel oracle for `S` by `unmarkUnitary` equals the embedded
  parallel
  oracle for `S \ T` on `memTupleProj`. -/
theorem unmarkUnitary_mul_parallelOracle_mul_proj {n m k : ℕ}
    (activeMem : Finset (Fin k)) (memTuple : Fin k → Fin (2 ^ n))
    {S : Finset (Fin (2 ^ n))} (hsub : activeMem.image memTuple ⊆ S) :
    (unmarkUnitary n m k activeMem).1 *
        ((oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 *
        memTupleProj n m k activeMem memTuple =
      ((oracleReg n m k).embedUnitary (parallelMarkingOracle m (S \ activeMem.image memTuple))).1 *
        memTupleProj n m k activeMem memTuple := by
  have hvec (b : Fin (2 ^ findAllQubits n m k)) :
      ((unmarkUnitary n m k activeMem).1 *
          ((oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 *
          memTupleProj n m k activeMem memTuple) *ᵥ Pi.single b (1 : ℂ) =
        (((oracleReg n m k).embedUnitary
            (parallelMarkingOracle m (S \ activeMem.image memTuple))).1 *
          memTupleProj n m k activeMem memTuple) *ᵥ Pi.single b (1 : ℂ) := by
    by_cases hb : ∀ j ∈ activeMem, (memSlotReg n m k j).extractIndex b = memTuple j
    · have hproj : memTupleProj n m k activeMem memTuple *ᵥ Pi.single b (1 : ℂ) =
          Pi.single b 1 := by
        funext a
        rw [memTupleProj, Matrix.mulVec_diagonal]
        by_cases hab : a = b
        · subst hab; simp only [Pi.single_eq_same, mul_one]; exact ite_eq_left hb
        · simp [hab]
      rw [← Matrix.mulVec_mulVec, hproj, ← Matrix.mulVec_mulVec,
        parallelMarkingOracle_mulVec_single, unmarkUnitary, permutationUnitary_mulVec_single,
        Function.Involutive.coe_toPerm, ← Matrix.mulVec_mulVec, hproj,
        parallelMarkingOracle_mulVec_single]
      have hT := memFoundSet_eq_image_of_memTuple activeMem memTuple b hb
      rw [unmarkFun_globalMarkFun_of_subset activeMem b (hT.symm ▸ hsub), hT]
    · have hproj : memTupleProj n m k activeMem memTuple *ᵥ Pi.single b (1 : ℂ) = 0 := by
        funext a
        rw [memTupleProj, Matrix.mulVec_diagonal]
        by_cases hab : a = b
        · subst hab; simp [hb]
        · simp [hab]
      rw [← Matrix.mulVec_mulVec, hproj, Matrix.mulVec_zero, ← Matrix.mulVec_mulVec, hproj,
        Matrix.mulVec_zero]
  ext a b
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hvec b) a
/-- Single coherent effective oracle call in `OracleDynamicCircuit`: calls `.oracle` once
  and
  applies `phaseI (unmarkUnitary n m k activeMem)` at zero oracle cost. -/
noncomputable def effectiveOracleCircuit {Var : Type} (n m k : ℕ) (activeMem : Finset (Fin k)) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (.oracle (oracleReg n m k)) (.step (phaseI (unmarkUnitary n m k activeMem)))
theorem costBound_effectiveOracleCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (activeMem : Finset (Fin k)) (S : Finset (Fin (2 ^ n))) :
    CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      ((effectiveOracleCircuit (Var := Var) n m k activeMem).compile
        QProg.qAssign (parallelMarkingOracle m S)) 1 := by
  simp only [effectiveOracleCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step]
  have h1 : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (.qAssign ((oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) 1 := by
    simpa using CostBound.qAssign (Var := Var)
      (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      ((oracleReg n m k).embedUnitary (parallelMarkingOracle m S))
  have h0 : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (.qAssign (phaseI (unmarkUnitary n m k activeMem))) 0 := by
    have hcost := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero
      (isRealMatrix_parallelMarkingOracle (m := m) S)
      (isRealMatrix_unmarkUnitary n m k activeMem)
    simpa [hcost] using CostBound.qAssign (Var := Var)
      (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (phaseI (unmarkUnitary n m k activeMem))
  simpa using CostBound.seq h1 h0
theorem lossless_effectiveOracleCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (activeMem : Finset (Fin k)) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    Lossless ((effectiveOracleCircuit (Var := Var) n m k activeMem).compile
      QProg.qAssign oracle) := by
  simp only [effectiveOracleCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step]
  exact (Lossless.qAssign _).seq (Lossless.qAssign _)
end QuantumComputation.Specs.GroverFindAll
end
end Sec_Unmarking
section Sec_MultiTargetAmplitude
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real
open scoped Matrix
/- ## Multi-target Grover recurrence on `Fin (2 ^ n)` -/

/-- Phase-flip matrix `-1` on `A` and `+1` outside `A`. -/
def setOracleMatrix {n : ℕ} (A : Finset (Fin (2 ^ n))) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal fun i ↦ if i ∈ A then -1 else 1
/-- Half-angle `θ / 2 = arcsin √(r / 2^n)` for `r` marked items among `2 ^ n`. -/
noncomputable def halfAngleSet (n r : ℕ) : ℝ :=
  Real.arcsin √((r : ℝ) / 2 ^ n)
/-- Single-slot success probability `sin²((2K + 1) arcsin √(r / 2^n))` after `K` Grover
  rounds. -/
noncomputable def p_succ_set (K n r : ℕ) : ℝ :=
  Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n r) ^ 2
theorem p_succ_set_nonneg (K n r : ℕ) : 0 ≤ p_succ_set K n r :=
  sq_nonneg _
theorem p_succ_set_le_one (K n r : ℕ) : p_succ_set K n r ≤ 1 :=
  Real.sin_sq_le_one _
theorem sin_halfAngleSet {n r : ℕ} (hrN : r ≤ 2 ^ n) :
    Real.sin (halfAngleSet n r) = √((r : ℝ) / 2 ^ n) := by
  apply Real.sin_arcsin
  · linarith [Real.sqrt_nonneg ((r : ℝ) / 2 ^ n)]
  · rw [Real.sqrt_le_one, div_le_one (by positivity)]
    exact_mod_cast hrN
theorem sqrt_dim_mul_sin_halfAngleSet {n r : ℕ} (hrN : r ≤ 2 ^ n) :
    √(2 ^ n : ℝ) * Real.sin (halfAngleSet n r) = √(r : ℝ) := by
  rw [sin_halfAngleSet hrN, Real.sqrt_div (by positivity)]
  have hd : √(2 ^ n : ℝ) ≠ 0 := by positivity
  field_simp
theorem sin_step_set {n r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ 2 ^ n) (k : ℕ) :
    1 / √(r : ℝ) * Real.sin ((2 * (k : ℝ) + 3) * halfAngleSet n r) =
      1 / √(r : ℝ) * Real.sin ((2 * (k : ℝ) + 1) * halfAngleSet n r) +
        2 / (2 ^ n : ℝ) * (√(2 ^ n : ℝ) * Real.cos ((2 * (k : ℝ) + 2) * halfAngleSet n r)) := by
  have htrig := Real.sin_sub_sin
    ((2 * (k : ℝ) + 3) * halfAngleSet n r)
    ((2 * (k : ℝ) + 1) * halfAngleSet n r)
  rw [show ((2 * (k : ℝ) + 3) * halfAngleSet n r -
        (2 * (k : ℝ) + 1) * halfAngleSet n r) / 2 = halfAngleSet n r by ring,
      show ((2 * (k : ℝ) + 3) * halfAngleSet n r +
        (2 * (k : ℝ) + 1) * halfAngleSet n r) / 2 =
        (2 * (k : ℝ) + 2) * halfAngleSet n r by ring] at htrig
  have hsin : Real.sin ((2 * (k : ℝ) + 3) * halfAngleSet n r) =
      Real.sin ((2 * (k : ℝ) + 1) * halfAngleSet n r) +
        2 * Real.sin (halfAngleSet n r) * Real.cos ((2 * (k : ℝ) + 2) * halfAngleSet n r) := by
    linarith
  rw [hsin, mul_add]
  congr 1
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsqrt : √(r : ℝ) ≠ 0 := (Real.sqrt_pos.2 hrpos).ne'
  have hdsqrt : √(2 ^ n : ℝ) ≠ 0 := by positivity
  rw [sin_halfAngleSet hrN, Real.sqrt_div (by positivity)]
  field_simp
  rw [Real.sq_sqrt (by positivity)]
theorem cos_step_set {n r : ℕ} (hrN : r ≤ 2 ^ n) (k : ℕ) :
    √(2 ^ n : ℝ) * Real.cos ((2 * (k : ℝ) + 2) * halfAngleSet n r) =
      √(2 ^ n : ℝ) * Real.cos (2 * (k : ℝ) * halfAngleSet n r) -
        2 * √(r : ℝ) * Real.sin ((2 * (k : ℝ) + 1) * halfAngleSet n r) := by
  have htrig := Real.cos_sub_cos
    (2 * (k : ℝ) * halfAngleSet n r)
    ((2 * (k : ℝ) + 2) * halfAngleSet n r)
  rw [show (2 * (k : ℝ) * halfAngleSet n r +
        (2 * (k : ℝ) + 2) * halfAngleSet n r) / 2 =
        (2 * (k : ℝ) + 1) * halfAngleSet n r by ring,
      show (2 * (k : ℝ) * halfAngleSet n r -
        (2 * (k : ℝ) + 2) * halfAngleSet n r) / 2 = -halfAngleSet n r by ring,
      Real.sin_neg] at htrig
  have hy : Real.cos ((2 * (k : ℝ) + 2) * halfAngleSet n r) =
      Real.cos (2 * (k : ℝ) * halfAngleSet n r) -
        2 * Real.sin ((2 * (k : ℝ) + 1) * halfAngleSet n r) * Real.sin (halfAngleSet n r) := by
    linarith
  rw [hy, mul_sub]
  congr 1
  calc √(2 ^ n : ℝ) *
        (2 * Real.sin ((2 * (k : ℝ) + 1) * halfAngleSet n r) * Real.sin (halfAngleSet n r))
      = 2 * (√(2 ^ n : ℝ) * Real.sin (halfAngleSet n r)) *
          Real.sin ((2 * (k : ℝ) + 1) * halfAngleSet n r) := by ring
    _ = 2 * √(r : ℝ) * Real.sin ((2 * (k : ℝ) + 1) * halfAngleSet n r) := by
        rw [sqrt_dim_mul_sin_halfAngleSet hrN]
theorem setOracleMatrix_mulVec {n : ℕ} (A : Finset (Fin (2 ^ n)))
    (v : Fin (2 ^ n) → ℂ) (i : Fin (2 ^ n)) :
    (setOracleMatrix A *ᵥ v) i = if i ∈ A then -v i else v i := by
  simp [setOracleMatrix, Matrix.mulVec_diagonal]
theorem sum_setOracleMatrix_mulVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (v : Fin (2 ^ n) → ℂ) :
    ∑ i, (setOracleMatrix A *ᵥ v) i = ∑ i, v i - 2 * ∑ x ∈ A, v x := by
  simp_rw [setOracleMatrix_mulVec]
  have hsplit : (fun i : Fin (2 ^ n) ↦ if i ∈ A then -v i else v i) =
      fun i ↦ v i + if i ∈ A then -2 * v i else 0 := by
    funext i
    split_ifs <;> ring
  rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_filter]
  have hfilt : Finset.univ.filter (· ∈ A) = A := by
    ext x
    simp
  rw [hfilt, ← Finset.mul_sum]
  ring
/-- Multi-target Grover state vector after `K` iterations on `A`. -/
noncomputable def groverSetState {n : ℕ} (A : Finset (Fin (2 ^ n))) : ℕ → Fin (2 ^ n) → ℂ
  | 0 => fun _ ↦ (1 / √(2 ^ n : ℝ) : ℝ)
  | K + 1 => Grover.diffuserMatrix *ᵥ setOracleMatrix A *ᵥ groverSetState A K
theorem groverSetState_target_sum {n : ℕ} (A : Finset (Fin (2 ^ n)))
    (hr : 1 ≤ A.card) (hrN : A.card ≤ 2 ^ n) (K : ℕ) :
    (∀ x ∈ A, groverSetState A K x =
        ((1 / √(A.card : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n A.card) : ℝ) : ℂ)) ∧
      ∑ i, groverSetState A K i =
        ((√(2 ^ n : ℝ) * Real.cos (2 * (K : ℝ) * halfAngleSet n A.card) : ℝ) : ℂ) := by
  set r := A.card
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsqrt : √(r : ℝ) ≠ 0 := (Real.sqrt_pos.2 hrpos).ne'
  induction K with
  | zero =>
      constructor
      · intro x _
        simp only [groverSetState, Nat.cast_zero, mul_zero, zero_add, one_mul,
          sin_halfAngleSet hrN, Real.sqrt_div (by positivity)]
        congr 1
        field_simp
      · simp only [groverSetState, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        norm_cast
        simpa [div_eq_mul_inv] using Real.div_sqrt (x := (2 ^ n : ℝ))
  | succ K ih =>
      rcases ih with ⟨htarget, hsum⟩
      have hsumA : ∑ x ∈ A, groverSetState A K x =
          ((√(r : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n r) : ℝ) : ℂ) := by
        rw [Finset.sum_congr rfl htarget, Finset.sum_const, nsmul_eq_mul]
        norm_cast
        have hrr : (r : ℝ) * (1 / √(r : ℝ)) = √(r : ℝ) := by
          rw [mul_one_div, Real.div_sqrt]
        change (r : ℝ) * (1 / √(r : ℝ) * _) = _
        rw [← mul_assoc, hrr]
      constructor
      · intro x hx
        rw [groverSetState, Grover.diffuserMatrix_mulVec, sum_setOracleMatrix_mulVec,
          setOracleMatrix_mulVec, ite_eq_left hx, htarget x hx, hsum, hsumA]
        suffices h :
            2 / (2 ^ n : ℝ) *
                (√(2 ^ n : ℝ) * Real.cos (2 * (K : ℝ) * halfAngleSet n r) -
                  2 * (√(r : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n r))) -
              -(1 / √(r : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n r)) =
            1 / √(r : ℝ) * Real.sin ((2 * ((K + 1 : ℕ) : ℝ) + 1) * halfAngleSet n r) by
          have hC := congrArg Complex.ofReal h
          push_cast at hC ⊢
          exact hC
        rw [show (2 * ((K + 1 : ℕ) : ℝ) + 1) * halfAngleSet n r =
            (2 * (K : ℝ) + 3) * halfAngleSet n r by push_cast; ring,
          sin_step_set hr hrN K, cos_step_set hrN K]
        ring
      · rw [groverSetState, Grover.sum_diffuserMatrix_mulVec, sum_setOracleMatrix_mulVec,
          hsum, hsumA]
        suffices h :
            √(2 ^ n : ℝ) * Real.cos (2 * (K : ℝ) * halfAngleSet n r) -
              2 * (√(r : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n r)) =
            √(2 ^ n : ℝ) * Real.cos (2 * ((K + 1 : ℕ) : ℝ) * halfAngleSet n r) by
          have hC := congrArg Complex.ofReal h
          push_cast at hC ⊢
          exact hC
        rw [show 2 * ((K + 1 : ℕ) : ℝ) * halfAngleSet n r =
            (2 * (K : ℝ) + 2) * halfAngleSet n r by push_cast; ring,
          cos_step_set hrN K]
        ring
theorem sum_normSq_groverSetState_mem {n : ℕ} (A : Finset (Fin (2 ^ n)))
    (hr : 1 ≤ A.card) (hrN : A.card ≤ 2 ^ n) (K : ℕ) :
    ∑ x ∈ A, Complex.normSq (groverSetState A K x) = p_succ_set K n A.card := by
  obtain ⟨htarget, _⟩ := groverSetState_target_sum A hr hrN K
  have hterm : ∀ x ∈ A, Complex.normSq (groverSetState A K x) =
      (1 / (A.card : ℝ)) * p_succ_set K n A.card := by
    intro x hx
    rw [htarget x hx, Complex.normSq_ofReal, p_succ_set]
    have hsq : √(A.card : ℝ) * √(A.card : ℝ) = (A.card : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc (1 / √(A.card : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n A.card)) *
          (1 / √(A.card : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n A.card))
        = (1 / (√(A.card : ℝ) * √(A.card : ℝ))) *
            Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n A.card) ^ 2 := by ring
      _ = (1 / (A.card : ℝ)) *
            Real.sin ((2 * (K : ℝ) + 1) * halfAngleSet n A.card) ^ 2 := by rw [hsq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  have hne : (A.card : ℝ) ≠ 0 := by positivity
  field_simp
theorem sum_normSq_groverSetState_univ {n : ℕ} (A : Finset (Fin (2 ^ n))) (K : ℕ) :
    ∑ x : Fin (2 ^ n), Complex.normSq (groverSetState A K x) = 1 := by
  induction K with
  | zero =>
      simp only [groverSetState, Complex.normSq_ofReal, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have hsq : √(2 ^ n : ℝ) * √(2 ^ n : ℝ) = (2 ^ n : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hd : (2 ^ n : ℝ) ≠ 0 := by positivity
      calc (2 ^ n : ℝ) * (1 / √(2 ^ n : ℝ) * (1 / √(2 ^ n : ℝ)))
          = (2 ^ n : ℝ) / (√(2 ^ n : ℝ) * √(2 ^ n : ℝ)) := by ring
        _ = (2 ^ n : ℝ) / (2 ^ n : ℝ) := by rw [hsq]
        _ = 1 := div_self hd
  | succ K ih =>
      have hO : setOracleMatrix A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
        rw [setOracleMatrix, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
        intro i; split_ifs <;> simp
      rw [groverSetState, ← Grover.diffuserUnitary_coe,
        sum_normSq_unitary_mulVec Grover.diffuserUnitary _,
        sum_normSq_unitary_mulVec ⟨setOracleMatrix A, hO⟩ _, ih]
/- ## Single-slot `(n + 1)`-qubit preparation, Grover iterations, and verification -/

theorem isRealMatrix_hadamardMatrix (q : ℕ) : IsRealMatrix (hadamardMatrix q) := by
  intro i j
  rw [hadamardMatrix_apply, smul_eq_mul]
  have h1 : (1 / √(2 ^ q) : ℂ) = ((1 / √(2 ^ q : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_im]
theorem isRealMatrix_diffuserMatrix (n : ℕ) : IsRealMatrix (Grover.diffuserMatrix (n := n)) := by
  intro i j
  simp only [Grover.diffuserMatrix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
  have h2 : ((2 : ℂ) / 2 ^ n).im = 0 := by
    have : ((2 : ℂ) / 2 ^ n) = ((2 / (2 ^ n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_im]
  by_cases hij : i = j <;> simp [hij, h2]
/-- Marker `|0⟩ ↦ |−⟩` unitary `(H * X)` on `Fin (2 ^ 1)`. -/
noncomputable def markerMinusUnitary : Unitary (2 ^ 1) :=
  hadamardUnitary * permutationUnitary (Equiv.swap (0 : Fin (2 ^ 1)) 1)
/-- Inverse marker unitary `(X * H)` mapping `|−⟩ ↦ |0⟩` on `Fin (2 ^ 1)`. -/
noncomputable def markerMinusInvUnitary : Unitary (2 ^ 1) :=
  permutationUnitary (Equiv.swap (0 : Fin (2 ^ 1)) 1) * hadamardUnitary
theorem markerMinusInv_mul_markerMinus :
    markerMinusInvUnitary * markerMinusUnitary = 1 := by
  apply Subtype.ext
  simp only [markerMinusInvUnitary, markerMinusUnitary, Submonoid.coe_mul, Submonoid.coe_one,
    hadamardUnitary_coe]
  rw [mul_assoc (permutationUnitary _).1 (hadamardMatrix 1),
    ← mul_assoc (hadamardMatrix 1) (hadamardMatrix 1), hadamardMatrix_mul_self 1, one_mul,
    ← Submonoid.coe_mul, permutationUnitary_swap_mul_self, Submonoid.coe_one]
/-- Local `(n + 1)`-qubit preparation unitary mapping `|0⟩_b |0^n⟩_x ↦ |−⟩_b |+^n⟩_x`. -/
noncomputable def slotPrepLocal (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  (localIdxReg n).embedUnitary hadamardUnitary *
    (localMarkerReg n).embedUnitary markerMinusUnitary
/-- Local `(n + 1)`-qubit diffuser on `localIdxReg n`. -/
noncomputable def slotDiffuserLocal (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  (localIdxReg n).embedUnitary Grover.diffuserUnitary
/-- Local `(n + 1)`-qubit marker unpreparation mapping `|−⟩_b ↦ |0⟩_b`. -/
noncomputable def slotUnprepLocal (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  (localMarkerReg n).embedUnitary markerMinusInvUnitary
theorem isRealMatrix_slotPrepLocal (n : ℕ) : IsRealMatrix (slotPrepLocal n).1 :=
  isRealMatrix_mul (isRealMatrix_embedMatrix _ (isRealMatrix_hadamardMatrix n))
    (isRealMatrix_embedMatrix _
      (isRealMatrix_mul (isRealMatrix_hadamardMatrix 1) (isRealMatrix_permutationUnitary _)))
theorem isRealMatrix_slotDiffuserLocal (n : ℕ) : IsRealMatrix (slotDiffuserLocal n).1 :=
  isRealMatrix_embedMatrix _ (isRealMatrix_diffuserMatrix n)
theorem isRealMatrix_slotUnprepLocal (n : ℕ) : IsRealMatrix (slotUnprepLocal n).1 :=
  isRealMatrix_embedMatrix _
    (isRealMatrix_mul (isRealMatrix_permutationUnitary _) (isRealMatrix_hadamardMatrix 1))
/-- Product state `u ↦ v (idx u) * mVec (marker u)` on `Fin (2 ^ (n + 1))`. -/
def slotPairVec {n : ℕ} (v : Fin (2 ^ n) → ℂ) (mVec : Fin (2 ^ 1) → ℂ)
    (u : Fin (2 ^ (n + 1))) : ℂ :=
  v ((localIdxReg n).extractIndex u) * mVec ((localMarkerReg n).extractIndex u)
/-- Marker `|−⟩` vector `(1/√2, -1/√2)` on `Fin (2 ^ 1)`. -/
noncomputable def minusVec : Fin (2 ^ 1) → ℂ :=
  markerMinusUnitary.1 *ᵥ Pi.single 0 1
theorem minusVec_add_one (b : Fin (2 ^ 1)) : minusVec (b + 1) = -minusVec b := by
  have hvec : minusVec = hadamardMatrix 1 *ᵥ Pi.single (1 : Fin (2 ^ 1)) 1 := by
    rw [minusVec, markerMinusUnitary, Submonoid.coe_mul, hadamardUnitary_coe,
      ← Matrix.mulVec_mulVec, permutationUnitary_mulVec_single]
    simp
  have h0 : minusVec 0 = (1 / √2 : ℂ) := by
    have hbit0 : basisBits 1 (0 : Fin (2 ^ 1)) 0 = 0 := by
      rw [basisBits_eq_div_mod]; rfl
    rw [hvec, Matrix.mulVec_single_one, Matrix.col_apply, hadamardMatrix_apply]
    simp [dotProduct, hbit0]
  have h1 : minusVec 1 = -(1 / √2 : ℂ) := by
    have hbit1 : basisBits 1 (1 : Fin (2 ^ 1)) 0 = 1 := by
      rw [basisBits_eq_div_mod]; rfl
    rw [hvec, Matrix.mulVec_single_one, Matrix.col_apply, hadamardMatrix_apply]
    simp [dotProduct, hbit1]
  fin_cases b
  · change minusVec 1 = -minusVec 0; rw [h0, h1]
  · change minusVec 0 = -minusVec 1; rw [h0, h1, neg_neg]
theorem localIdxEmbed_mulVec_slotPairVec {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (v : Fin (2 ^ n) → ℂ) (mVec : Fin (2 ^ 1) → ℂ) :
    (localIdxReg n).embedMatrix M *ᵥ slotPairVec v mVec = slotPairVec (M *ᵥ v) mVec := by
  funext u
  rw [(localIdxReg n).embedMatrix_mulVec_apply]
  change (∑ x : Fin (2 ^ n),
      M ((localIdxReg n).extractIndex u) x *
        slotPairVec v mVec ((localIdxReg n).replaceIndex u x)) = _
  have hterm (x : Fin (2 ^ n)) :
      slotPairVec v mVec ((localIdxReg n).replaceIndex u x) =
        v x * mVec ((localMarkerReg n).extractIndex u) := by
    simp only [slotPairVec, QRegister.extractIndex_replaceIndex,
      (localMarkerReg n).extractIndex_replaceIndex_of_disjoint (localIdxReg n)
        (localMarkerReg_disjoint_localIdxReg n)]
  simp_rw [hterm, ← mul_assoc]
  rw [← Finset.sum_mul]
  rfl
theorem localMarkerEmbed_mulVec_slotPairVec {n : ℕ} (B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
    (v : Fin (2 ^ n) → ℂ) (mVec : Fin (2 ^ 1) → ℂ) :
    (localMarkerReg n).embedMatrix B *ᵥ slotPairVec v mVec = slotPairVec v (B *ᵥ mVec) := by
  funext u
  rw [(localMarkerReg n).embedMatrix_mulVec_apply]
  change (∑ b : Fin (2 ^ 1),
      B ((localMarkerReg n).extractIndex u) b *
        slotPairVec v mVec ((localMarkerReg n).replaceIndex u b)) = _
  have hterm (b : Fin (2 ^ 1)) :
      slotPairVec v mVec ((localMarkerReg n).replaceIndex u b) =
        v ((localIdxReg n).extractIndex u) * mVec b := by
    simp only [slotPairVec, QRegister.extractIndex_replaceIndex,
      (localIdxReg n).extractIndex_replaceIndex_of_disjoint (localMarkerReg n)
        (QRegister.disjoint_comm.1 (localMarkerReg_disjoint_localIdxReg n))]
  simp_rw [hterm]
  rw [slotPairVec, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ by ring
theorem slotMarkPerm_involutive {n : ℕ} (A : Finset (Fin (2 ^ n))) :
    Function.Involutive (slotMarkPerm A) := by
  intro u
  obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  have hstep (b' : Fin (2 ^ 1)) :
      slotMarkPerm A ((splitBasisEquiv n 1).symm (x, b')) =
        (splitBasisEquiv n 1).symm (x, b' + if x ∈ A then 1 else 0) := by
    simp [slotMarkPerm, tableAddPerm, addRightShear]
  rw [hstep, hstep]
  congr 1
  ext
  · rfl
  · by_cases hx : x ∈ A
    · simp only [hx, ↓reduceIte]
      fin_cases b <;> rfl
    · simp [hx]
theorem setMarkingOracle_mulVec_apply {n : ℕ} (A : Finset (Fin (2 ^ n)))
    (ψ : Fin (2 ^ (n + 1)) → ℂ) (u : Fin (2 ^ (n + 1))) :
    ((setMarkingOracle A).1 *ᵥ ψ) u = ψ (slotMarkPerm A u) := by
  change (Equiv.Perm.permMatrix ℂ (slotMarkPerm A)⁻¹ *ᵥ ψ) u = ψ (slotMarkPerm A u)
  rw [Matrix.permMatrix_mulVec]
  exact congrArg ψ (Equiv.Perm.inv_eq_iff_eq.2 (slotMarkPerm_involutive A u).symm)
theorem setMarkingOracle_mulVec_slotPairVec_minus {n : ℕ} (A : Finset (Fin (2 ^ n)))
    (v : Fin (2 ^ n) → ℂ) :
    (setMarkingOracle A).1 *ᵥ slotPairVec v minusVec =
      slotPairVec (setOracleMatrix A *ᵥ v) minusVec := by
  funext u
  rw [setMarkingOracle_mulVec_apply, slotPairVec, extractIndex_localIdxReg_slotMarkPerm,
    extractIndex_localMarkerReg_slotMarkPerm, slotPairVec, setOracleMatrix_mulVec]
  by_cases hx : (localIdxReg n).extractIndex u ∈ A
  · simp only [hx, ↓reduceIte, minusVec_add_one]
    ring
  · simp [hx]
theorem single_zero_eq_slotPairVec (n : ℕ) :
    (Pi.single (0 : Fin (2 ^ (n + 1))) (1 : ℂ)) =
      slotPairVec (Pi.single (0 : Fin (2 ^ n)) 1) (Pi.single (0 : Fin (2 ^ 1)) 1) := by
  funext u
  by_cases hu : u = 0
  · subst hu
    have hx0 : (localIdxReg n).extractIndex 0 = 0 := by ext; simp [extractIndex_localIdxReg_eq]
    have hb0 : (localMarkerReg n).extractIndex 0 = 0 := by
      ext; simp [extractIndex_localMarkerReg_eq]
    simp [slotPairVec, hx0, hb0]
  · simp only [Pi.single_apply, hu, ↓reduceIte, slotPairVec]
    have hnot : ¬((localIdxReg n).extractIndex u = 0 ∧ (localMarkerReg n).extractIndex u = 0) := by
      rintro ⟨hx, hb⟩
      apply hu
      obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
      rw [extractIndex_localIdxReg_splitSymm] at hx
      rw [extractIndex_localMarkerReg_splitSymm] at hb
      subst hx; subst hb
      ext
      simp
    by_cases hx : (localIdxReg n).extractIndex u = 0
    · have hb : (localMarkerReg n).extractIndex u ≠ 0 := fun h ↦ hnot ⟨hx, h⟩
      simp [hx, hb]
    · simp [hx]
/-- Single-slot combined unitary (`slotPrepLocal`, `K` Grover rounds, `slotUnprepLocal`, and
  one verification oracle call). -/
noncomputable def slotFinalUnitary (n : ℕ) (A : Finset (Fin (2 ^ n))) (K : ℕ) :
    Unitary (2 ^ (n + 1)) :=
  setMarkingOracle A * slotUnprepLocal n *
    (slotDiffuserLocal n * setMarkingOracle A) ^ K * slotPrepLocal n
/-- Exact single-slot output state after `slotFinalUnitary n A K` from `|0⟩`: amplitude
  `groverSetState A K x` on `(x, [x ∈ A])`, and `0` on all other `(n + 1)`-qubit basis
  states. -/
noncomputable def slotFinalVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (K : ℕ)
    (u : Fin (2 ^ (n + 1))) : ℂ :=
  if (localMarkerReg n).extractIndex u =
      (if (localIdxReg n).extractIndex u ∈ A then (1 : Fin (2 ^ 1)) else 0) then
    groverSetState A K ((localIdxReg n).extractIndex u)
  else
    0
theorem slotFinalUnitary_mulVec_zero {n : ℕ} (A : Finset (Fin (2 ^ n))) (K : ℕ) :
    (slotFinalUnitary n A K).1 *ᵥ Pi.single (0 : Fin (2 ^ (n + 1))) (1 : ℂ) =
      slotFinalVec A K := by
  have hprep : (slotPrepLocal n).1 *ᵥ Pi.single (0 : Fin (2 ^ (n + 1))) (1 : ℂ) =
      slotPairVec (groverSetState A 0) minusVec := by
    rw [single_zero_eq_slotPairVec, slotPrepLocal, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    simp only [QRegister.embedUnitary_val]
    rw [localMarkerEmbed_mulVec_slotPairVec, ← minusVec, localIdxEmbed_mulVec_slotPairVec]
    congr 1
    funext x
    rw [hadamardUnitary_coe, Matrix.mulVec_single_one, Matrix.col_apply, hadamardMatrix_apply_zero,
      groverSetState]
    simp
  have hiter (t : ℕ) :
      (((slotDiffuserLocal n * setMarkingOracle A) ^ t).1 *ᵥ
          slotPairVec (groverSetState A 0) minusVec) =
        slotPairVec (groverSetState A t) minusVec := by
    induction t with
    | zero => simp
    | succ t ih =>
        rw [pow_succ' (slotDiffuserLocal n * setMarkingOracle A) t, Submonoid.coe_mul,
          ← Matrix.mulVec_mulVec, ih, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          setMarkingOracle_mulVec_slotPairVec_minus, slotDiffuserLocal,
          QRegister.embedUnitary_val, Grover.diffuserUnitary_coe, localIdxEmbed_mulVec_slotPairVec]
        rfl
  have hunprep :
      (slotUnprepLocal n).1 *ᵥ slotPairVec (groverSetState A K) minusVec =
        slotPairVec (groverSetState A K) (Pi.single 0 1) := by
    rw [slotUnprepLocal, QRegister.embedUnitary_val, localMarkerEmbed_mulVec_slotPairVec, minusVec,
      Matrix.mulVec_mulVec]
    have hinv : markerMinusInvUnitary.1 * markerMinusUnitary.1 = 1 :=
      congrArg Subtype.val markerMinusInv_mul_markerMinus
    rw [hinv, Matrix.one_mulVec]
  rw [slotFinalUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hprep,
    Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hiter K,
    Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hunprep]
  funext u
  rw [setMarkingOracle_mulVec_apply, slotPairVec, extractIndex_localIdxReg_slotMarkPerm,
    extractIndex_localMarkerReg_slotMarkPerm, slotFinalVec]
  generalize (localMarkerReg n).extractIndex u = b
  by_cases hx : (localIdxReg n).extractIndex u ∈ A
  · simp only [hx, ↓reduceIte]
    fin_cases b <;> simp
  · simp only [hx, ↓reduceIte, add_zero]
    fin_cases b <;> simp
/-- Zero false positives on a single slot: any outcome with marker `1` and `x ∉ A` has zero
  amplitude in `slotFinalVec A K`. -/
theorem slotFinalVec_eq_zero_of_marker_one_of_not_mem {n : ℕ} {A : Finset (Fin (2 ^ n))}
    {K : ℕ} {u : Fin (2 ^ (n + 1))} (hb : (localMarkerReg n).extractIndex u = 1)
    (hx : (localIdxReg n).extractIndex u ∉ A) :
    slotFinalVec A K u = 0 := by
  simp [slotFinalVec, hb, hx]
theorem sum_normSq_slotFinalVec_univ {n : ℕ} (A : Finset (Fin (2 ^ n))) (K : ℕ) :
    ∑ u : Fin (2 ^ (n + 1)), Complex.normSq (slotFinalVec A K u) = 1 := by
  rw [← slotFinalUnitary_mulVec_zero, sum_normSq_unitary_mulVec (slotFinalUnitary n A K)]
  simp [Pi.single_apply]
theorem sum_normSq_slotFinalVec_marker_one {n : ℕ} (A : Finset (Fin (2 ^ n)))
    (hr : 1 ≤ A.card) (hrN : A.card ≤ 2 ^ n) (K : ℕ) :
    (∑ u : Fin (2 ^ (n + 1)) with (localMarkerReg n).extractIndex u = 1,
        Complex.normSq (slotFinalVec A K u)) =
      p_succ_set K n A.card := by
  have hsub :
      (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦
          (localMarkerReg n).extractIndex u = 1) =
        (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦
          (localMarkerReg n).extractIndex u = 1 ∧ (localIdxReg n).extractIndex u ∈ A) ∪
        (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦
          (localMarkerReg n).extractIndex u = 1 ∧ (localIdxReg n).extractIndex u ∉ A) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  have hdisj : Disjoint
      (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦
        (localMarkerReg n).extractIndex u = 1 ∧ (localIdxReg n).extractIndex u ∈ A)
      (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦
        (localMarkerReg n).extractIndex u = 1 ∧ (localIdxReg n).extractIndex u ∉ A) := by
    rw [Finset.disjoint_filter]
    intro _ _ h1 h2
    exact h2.2 h1.2
  rw [hsub, Finset.sum_union hdisj]
  have hzero :
      (∑ u ∈ Finset.univ.filter (fun u : Fin (2 ^ (n + 1)) ↦
          (localMarkerReg n).extractIndex u = 1 ∧ (localIdxReg n).extractIndex u ∉ A),
        Complex.normSq (slotFinalVec A K u)) = 0 := by
    refine Finset.sum_eq_zero fun u hu ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [slotFinalVec_eq_zero_of_marker_one_of_not_mem hu.1 hu.2, map_zero]
  rw [hzero, add_zero, ← sum_normSq_groverSetState_mem A hr hrN K]
  symm
  refine Finset.sum_bij (fun x _ ↦ (splitBasisEquiv n 1).symm (x, 1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [extractIndex_localMarkerReg_splitSymm, extractIndex_localIdxReg_splitSymm]
    exact ⟨rfl, hx⟩
  · intro x₁ _ x₂ _ heq
    exact congrArg Prod.fst ((splitBasisEquiv n 1).symm.injective heq)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨(localIdxReg n).extractIndex u, hu.2, ?_⟩
    obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
    rw [extractIndex_localMarkerReg_splitSymm] at hu
    rw [extractIndex_localIdxReg_splitSymm, hu.1]
  · intro x hx
    rw [slotFinalVec, extractIndex_localMarkerReg_splitSymm, extractIndex_localIdxReg_splitSymm]
    simp [hx]
theorem sum_normSq_slotFinalVec_marker_zero {n : ℕ} (A : Finset (Fin (2 ^ n)))
    (hr : 1 ≤ A.card) (hrN : A.card ≤ 2 ^ n) (K : ℕ) :
    (∑ u : Fin (2 ^ (n + 1)) with (localMarkerReg n).extractIndex u = 0,
        Complex.normSq (slotFinalVec A K u)) =
      1 - p_succ_set K n A.card := by
  have hpart :
      (Finset.univ : Finset (Fin (2 ^ (n + 1)))) =
        (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦
          (localMarkerReg n).extractIndex u = 0) ∪
        (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦
          (localMarkerReg n).extractIndex u = 1) := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    generalize (localMarkerReg n).extractIndex u = b
    fin_cases b <;> simp
  have hdisj : Disjoint
      (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦ (localMarkerReg n).extractIndex u = 0)
      (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦ (localMarkerReg n).extractIndex u = 1) := by
    rw [Finset.disjoint_filter]
    intro _ _ h0 h1
    rw [h0] at h1
    exact zero_ne_one h1
  have htot := sum_normSq_slotFinalVec_univ A K
  rw [hpart, Finset.sum_union hdisj, sum_normSq_slotFinalVec_marker_one A hr hrN K] at htot
  linarith
/- ## `m`-slot parallel product state on `2 ^ ((n + 1) * m)` -/

/-- Apply the same `(n + 1)`-qubit unitary independently across all `m` slots of
  `oracleReg`. -/
noncomputable def parallelSlotProd {n : ℕ} (m : ℕ) (U : Unitary (2 ^ (n + 1))) :
    Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦ (localSlotReg n m i).embedUnitary U).prod
theorem isRealMatrix_parallelSlotProd {n m : ℕ} {U : Unitary (2 ^ (n + 1))}
    (hU : IsRealMatrix U.1) : IsRealMatrix (parallelSlotProd m U).1 := by
  refine isRealMatrix_listProd _ ?_
  intro V hV
  rw [List.mem_ofFn] at hV
  obtain ⟨i, rfl⟩ := hV
  exact isRealMatrix_embedMatrix _ hU
theorem slotEmbed_comm_listProd {n m : ℕ} (U V : Unitary (2 ^ (n + 1)))
    (i : Fin m) (js : List (Fin m)) (hi : i ∉ js) :
    ((js.map fun j ↦ (localSlotReg n m j).embedUnitary U).prod) *
        (localSlotReg n m i).embedUnitary V =
      (localSlotReg n m i).embedUnitary V *
        ((js.map fun j ↦ (localSlotReg n m j).embedUnitary U).prod) := by
  induction js with
  | nil => simp
  | cons j js ih =>
      rw [List.mem_cons, not_or] at hi
      rw [List.map_cons, List.prod_cons, mul_assoc, ih hi.2, ← mul_assoc,
        ← mul_assoc ((localSlotReg n m i).embedUnitary V)]
      congr 1
      apply Subtype.ext
      exact (localSlotReg n m j).embedMatrix_comm_of_disjoint (localSlotReg n m i)
        (localSlotReg_disjoint (ne_comm.mp hi.1)) U.1 V.1
theorem slotEmbed_listProd_mul {n m : ℕ} (U V : Unitary (2 ^ (n + 1)))
    (is : List (Fin m)) (hnd : is.Nodup) :
    (is.map fun i ↦ (localSlotReg n m i).embedUnitary U).prod *
        (is.map fun i ↦ (localSlotReg n m i).embedUnitary V).prod =
      (is.map fun i ↦ (localSlotReg n m i).embedUnitary (U * V)).prod := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.prod_cons]
      calc ((localSlotReg n m i).embedUnitary U *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary U).prod) *
            ((localSlotReg n m i).embedUnitary V *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary V).prod)
          = (localSlotReg n m i).embedUnitary U *
              ((is.map fun j ↦ (localSlotReg n m j).embedUnitary U).prod *
                (localSlotReg n m i).embedUnitary V) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary V).prod := by group
        _ = (localSlotReg n m i).embedUnitary U *
              ((localSlotReg n m i).embedUnitary V *
                (is.map fun j ↦ (localSlotReg n m j).embedUnitary U).prod) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary V).prod := by
              rw [slotEmbed_comm_listProd U V i is hnd.1]
        _ = ((localSlotReg n m i).embedUnitary U * (localSlotReg n m i).embedUnitary V) *
              ((is.map fun j ↦ (localSlotReg n m j).embedUnitary U).prod *
                (is.map fun j ↦ (localSlotReg n m j).embedUnitary V).prod) := by group
        _ = (localSlotReg n m i).embedUnitary (U * V) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (U * V)).prod := by
              rw [← (localSlotReg n m i).embedUnitary_mul, ih hnd.2]
theorem parallelSlotProd_mul {n m : ℕ} (U V : Unitary (2 ^ (n + 1))) :
    parallelSlotProd m U * parallelSlotProd m V = parallelSlotProd m (U * V) := by
  simp only [parallelSlotProd, List.ofFn_eq_map]
  exact slotEmbed_listProd_mul U V (List.finRange m) (List.nodup_finRange m)
theorem parallelSlotProd_one (n m : ℕ) :
    parallelSlotProd (n := n) m 1 = 1 := by
  simp [parallelSlotProd]
theorem parallelSlotProd_pow {n m : ℕ} (U : Unitary (2 ^ (n + 1))) (K : ℕ) :
    (parallelSlotProd m U) ^ K = parallelSlotProd m (U ^ K) := by
  induction K with
  | zero => rw [pow_zero, pow_zero, parallelSlotProd_one]
  | succ K ih => rw [pow_succ, pow_succ, ih, parallelSlotProd_mul]
/-- Bijection splitting `((n + 1) * m)`-qubit basis states into `m` slot basis states. -/
noncomputable def slotsEquiv (n m : ℕ) :
    Fin (2 ^ ((n + 1) * m)) ≃ (Fin m → Fin (2 ^ (n + 1))) := by
  refine Equiv.ofBijective (fun o i ↦ (localSlotReg n m i).extractIndex o) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro o₁ o₂ h
    apply (basisBits ((n + 1) * m)).injective
    funext w
    have hi_lt : w.val / (n + 1) < m := Nat.div_lt_of_lt_mul w.isLt
    let i : Fin m := ⟨w.val / (n + 1), hi_lt⟩
    let c : Fin (n + 1) := ⟨w.val % (n + 1), Nat.mod_lt _ (by omega)⟩
    have hw_eq : w = localSlotReg n m i c := by
      ext
      simp only [localSlotReg, QRegister.block_apply_val, i, c]
      exact (Nat.div_add_mod' w.val (n + 1)).symm
    have hi_eq : (localSlotReg n m i).extractIndex o₁ = (localSlotReg n m i).extractIndex o₂ :=
      congrFun h i
    rw [hw_eq, ← (localSlotReg n m i).basisBits_extractIndex,
      ← (localSlotReg n m i).basisBits_extractIndex, hi_eq]
  · simp [pow_mul]
@[simp]
theorem slotsEquiv_apply (n m : ℕ) (o : Fin (2 ^ ((n + 1) * m))) (i : Fin m) :
    slotsEquiv n m o i = (localSlotReg n m i).extractIndex o := rfl
/-- Partial tensor-product state where slots in `active` are in state `ψ` and remaining
  slots are
  in `|0⟩`. -/
def partialSlotsVec {n m : ℕ} (active : Finset (Fin m)) (ψ : Fin (2 ^ (n + 1)) → ℂ)
    (o : Fin (2 ^ ((n + 1) * m))) : ℂ :=
  (∏ i ∈ active, ψ ((localSlotReg n m i).extractIndex o)) *
    (∏ i ∈ Finset.univ \ active, if (localSlotReg n m i).extractIndex o = 0 then 1 else 0)
theorem partialSlotsVec_empty {n m : ℕ} (ψ : Fin (2 ^ (n + 1)) → ℂ) :
    partialSlotsVec ∅ ψ = (Pi.single (0 : Fin (2 ^ ((n + 1) * m))) 1) := by
  funext o
  simp only [partialSlotsVec, Finset.prod_empty, one_mul, Finset.sdiff_empty]
  by_cases ho : o = 0
  · subst ho
    have h0 (i : Fin m) : (localSlotReg n m i).extractIndex 0 = 0 := by
      ext; simp [extractIndex_localSlotReg_eq]
    simp [h0]
  · simp only [Pi.single_apply, ho, ↓reduceIte]
    have hex : ∃ i : Fin m, (localSlotReg n m i).extractIndex o ≠ 0 := by
      by_contra! hall
      apply ho
      apply (slotsEquiv n m).injective
      funext i
      rw [slotsEquiv_apply, hall i, slotsEquiv_apply]
      ext; simp [extractIndex_localSlotReg_eq]
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
theorem localSlotEmbed_mulVec_partialSlotsVec {n m : ℕ} (U : Unitary (2 ^ (n + 1)))
    (active : Finset (Fin m)) {i : Fin m} (hi : i ∉ active) :
    (localSlotReg n m i).embedMatrix U.1 *ᵥ partialSlotsVec active (U.1 *ᵥ Pi.single 0 1) =
      partialSlotsVec (insert i active) (U.1 *ᵥ Pi.single 0 1) := by
  set ψ := U.1 *ᵥ Pi.single (0 : Fin (2 ^ (n + 1))) (1 : ℂ)
  funext o
  rw [(localSlotReg n m i).embedMatrix_mulVec_apply]
  change (∑ u : Fin (2 ^ (n + 1)),
      U.1 ((localSlotReg n m i).extractIndex o) u *
        partialSlotsVec active ψ ((localSlotReg n m i).replaceIndex o u)) = _
  have hmem : i ∈ Finset.univ \ active := Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hi⟩
  have hsdiff : Finset.univ \ active = insert i (Finset.univ \ insert i active) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hji : j = i <;> simp [hji, hi]
  have hni : i ∉ Finset.univ \ insert i active := by simp
  have hterm (u : Fin (2 ^ (n + 1))) :
      partialSlotsVec active ψ ((localSlotReg n m i).replaceIndex o u) =
        (if u = 0 then (1 : ℂ) else 0) *
          ((∏ j ∈ active, ψ ((localSlotReg n m j).extractIndex o)) *
            (∏ j ∈ Finset.univ \ insert i active,
              if (localSlotReg n m j).extractIndex o = 0 then 1 else 0)) := by
    simp only [partialSlotsVec]
    have hp1 : (∏ j ∈ active, ψ ((localSlotReg n m j).extractIndex
          ((localSlotReg n m i).replaceIndex o u))) =
        ∏ j ∈ active, ψ ((localSlotReg n m j).extractIndex o) := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hne : j ≠ i := fun h ↦ hi (h ▸ hj)
      rw [(localSlotReg n m j).extractIndex_replaceIndex_of_disjoint (localSlotReg n m i)
        (localSlotReg_disjoint hne)]
    rw [hp1, hsdiff, Finset.prod_insert hni, QRegister.extractIndex_replaceIndex]
    have hp2 : (∏ j ∈ Finset.univ \ insert i active,
          if (localSlotReg n m j).extractIndex ((localSlotReg n m i).replaceIndex o u) = 0 then
            (1 : ℂ) else 0) =
        ∏ j ∈ Finset.univ \ insert i active,
          if (localSlotReg n m j).extractIndex o = 0 then (1 : ℂ) else 0 := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hne : j ≠ i := by
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hj
        exact hj.2.1
      rw [(localSlotReg n m j).extractIndex_replaceIndex_of_disjoint (localSlotReg n m i)
        (localSlotReg_disjoint hne)]
    rw [hp2]
    ring
  simp_rw [hterm]
  rw [Finset.sum_eq_single 0]
  · simp only [↓reduceIte, one_mul, partialSlotsVec, Finset.prod_insert hi]
    have hpsi : U.1 ((localSlotReg n m i).extractIndex o) 0 =
        ψ ((localSlotReg n m i).extractIndex o) := by
      simp [ψ]
    rw [hpsi]
    ring
  · intro u _ hu
    simp [hu]
  · intro habs
    exact (habs (Finset.mem_univ 0)).elim
theorem slotEmbed_listProd_mulVec_zero {n m : ℕ} (U : Unitary (2 ^ (n + 1)))
    (is : List (Fin m)) (hnd : is.Nodup) :
    ((is.map fun i ↦ (localSlotReg n m i).embedUnitary U).prod).1 *ᵥ
        Pi.single (0 : Fin (2 ^ ((n + 1) * m))) (1 : ℂ) =
      partialSlotsVec is.toFinset (U.1 *ᵥ Pi.single 0 1) := by
  induction is with
  | nil =>
      rw [List.map_nil, List.prod_nil, Submonoid.coe_one, Matrix.one_mulVec, List.toFinset_nil,
        partialSlotsVec_empty]
  | cons i is ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.prod_cons, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih hnd.2,
        QRegister.embedUnitary_val,
        localSlotEmbed_mulVec_partialSlotsVec U is.toFinset (by simpa using hnd.1),
        List.toFinset_cons]
/-- Exact `m`-slot parallel output state `o ↦ ∏ i, slotFinalVec A K (slot_i o)`. -/
noncomputable def parallelFinalVec {n : ℕ} (m : ℕ) (A : Finset (Fin (2 ^ n))) (K : ℕ)
    (o : Fin (2 ^ ((n + 1) * m))) : ℂ :=
  ∏ i : Fin m, slotFinalVec A K ((localSlotReg n m i).extractIndex o)
theorem parallelSlotProd_slotFinalUnitary_mulVec_zero {n m : ℕ}
    (A : Finset (Fin (2 ^ n))) (K : ℕ) :
    (parallelSlotProd m (slotFinalUnitary n A K)).1 *ᵥ
        Pi.single (0 : Fin (2 ^ ((n + 1) * m))) (1 : ℂ) =
      parallelFinalVec m A K := by
  rw [parallelSlotProd, List.ofFn_eq_map,
    slotEmbed_listProd_mulVec_zero (slotFinalUnitary n A K) (List.finRange m)
      (List.nodup_finRange m)]
  funext o
  have huniv : (List.finRange m).toFinset = Finset.univ := by ext; simp
  rw [partialSlotsVec, huniv, slotFinalUnitary_mulVec_zero, Finset.sdiff_self, Finset.prod_empty,
    mul_one, parallelFinalVec]
/-- Zero false positives on every slot `i: Fin m` of `parallelFinalVec m A K`. -/
theorem parallelFinalVec_eq_zero_of_slot_false_positive {n m : ℕ}
    {A : Finset (Fin (2 ^ n))} {K : ℕ} {o : Fin (2 ^ ((n + 1) * m))} (i : Fin m)
    (hb : (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex o) = 1)
    (hx : (localIdxReg n).extractIndex ((localSlotReg n m i).extractIndex o) ∉ A) :
    parallelFinalVec m A K o = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i)
    (slotFinalVec_eq_zero_of_marker_one_of_not_mem hb hx)
/-- Exact failure probability `(1 - p_succ_set K n A.card) ^ m` that all `m` marker bits are
  `0`. -/
theorem sum_normSq_parallelFinalVec_all_marker_zero {n m : ℕ} (A : Finset (Fin (2 ^ n)))
    (hr : 1 ≤ A.card) (hrN : A.card ≤ 2 ^ n) (K : ℕ) :
    (∑ o : Fin (2 ^ ((n + 1) * m)) with
        ∀ i : Fin m, (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex o) = 0,
      Complex.normSq (parallelFinalVec m A K o)) =
    (1 - p_succ_set K n A.card) ^ m := by
  let S₀ : Finset (Fin (2 ^ (n + 1))) :=
    Finset.univ.filter fun u ↦ (localMarkerReg n).extractIndex u = 0
  have hbij :
      (∑ o : Fin (2 ^ ((n + 1) * m)) with
          ∀ i : Fin m, (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex o) = 0,
        Complex.normSq (parallelFinalVec m A K o)) =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin m ↦ S₀),
        ∏ i : Fin m, Complex.normSq (slotFinalVec A K (f i)) := by
    refine Finset.sum_bij (fun o _ ↦ slotsEquiv n m o) ?_ ?_ ?_ ?_
    · intro o ho
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
      rw [Fintype.mem_piFinset]
      intro i
      simp [S₀, ho i]
    · intro o₁ _ o₂ _ heq
      exact (slotsEquiv n m).injective heq
    · intro f hf
      refine ⟨(slotsEquiv n m).symm f, ?_, (slotsEquiv n m).apply_symm_apply f⟩
      rw [Fintype.mem_piFinset] at hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      have hi := hf i
      simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have heq : (localSlotReg n m i).extractIndex ((slotsEquiv n m).symm f) = f i := by
        rw [← slotsEquiv_apply, (slotsEquiv n m).apply_symm_apply]
      rw [heq]
      exact hi
    · intro o _
      simp [parallelFinalVec, map_prod]
  have hprod := Finset.prod_univ_sum (t := fun _ : Fin m ↦ S₀)
    (f := fun (_ : Fin m) u ↦ Complex.normSq (slotFinalVec A K u))
  rw [hbij, ← hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    sum_normSq_slotFinalVec_marker_zero A hr hrN K]
end QuantumComputation.Specs.GroverFindAll
end
end Sec_MultiTargetAmplitude
end Sec_MultiTargetAmplitude
section Sec_StageLoop
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

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal ENNReal InnerProductSpace QHLExpectation
/- ## Diagonal subspace projectors and `SupportedOn` invariant -/

/-- Computational-basis projector onto basis indices satisfying `pred`. -/
def diagProj {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred] : Operator d :=
  Matrix.diagonal fun z ↦ if pred z then 1 else 0
@[simp]
theorem diagProj_conjTranspose {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred] :
    (diagProj pred)ᴴ = diagProj pred := by
  rw [diagProj, Matrix.diagonal_conjTranspose]
  congr 1
  ext z
  by_cases hz : pred z <;> simp [hz]
@[simp]
theorem diagProj_mul_self {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred] :
    diagProj pred * diagProj pred = diagProj pred := by
  rw [diagProj, Matrix.diagonal_mul_diagonal]
  congr 1
  ext z
  by_cases hz : pred z <;> simp [hz]
theorem diagProj_mul_mul_diagProj_apply {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred]
    (M : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    (diagProj pred * M * diagProj pred) a b =
      if pred a ∧ pred b then M a b else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp only [diagProj, Matrix.diagonal_apply_eq]
      by_cases ha : pred a <;> by_cases hb : pred b <;> simp [ha, hb]
    · intro x _ hxa
      simp [diagProj, Matrix.diagonal_apply_ne _ (Ne.symm hxa)]
    · intro h; exact (h (Finset.mem_univ a)).elim
  · intro x _ hxb
    simp [diagProj, Matrix.diagonal_apply_ne _ hxb]
  · intro h; exact (h (Finset.mem_univ b)).elim
/-- `diagProj pred` bundled as a quantum `Observable d`. -/
noncomputable def diagObs {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred] :
    Observable (Fin d) :=
  ⟨⟨diagProj pred, diagProj_conjTranspose pred⟩, by
    constructor
    · have h := Matrix.posSemidef_conjTranspose_mul_self (diagProj pred)
      rw [diagProj_conjTranspose, diagProj_mul_self] at h
      exact HermitianMat.zero_le_iff.mpr h
    · apply HermitianMat.le_iff.mpr
      change (1 - diagProj pred).PosSemidef
      rw [diagProj, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
      intro z
      by_cases hz : pred z <;> simp [hz]⟩
theorem diagObs_mat {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred] :
    (diagObs pred).1.mat = diagProj pred := by
  unfold diagObs
  rfl
/-- Store-independent QHL assertion for `diagObs pred`. -/
noncomputable def diagAssertion {Var : Type} {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred] :
    CQAssertion (Store Var) d :=
  fun _ ↦ diagObs pred
/-- A `CQState` is supported on `pred` if every classical branch's density matrix is
  invariant
  under two-sided projection by `diagProj pred`. -/
def SupportedOn {Var : Type} {d : ℕ} (pred : Fin d → Prop) [DecidablePred pred]
    (Δ : CQState (Store Var) d) : Prop :=
  ∀ σ, diagProj pred * (Δ.1 σ).1.mat * diagProj pred = (Δ.1 σ).1.mat
theorem supportedOn_mul_left {Var : Type} {d : ℕ} {pred : Fin d → Prop} [DecidablePred pred]
    {Δ : CQState (Store Var) d} (hΔ : SupportedOn pred Δ) (σ : Store Var) :
    diagProj pred * (Δ.1 σ).1.mat = (Δ.1 σ).1.mat := by
  calc diagProj pred * (Δ.1 σ).1.mat
      = diagProj pred * (diagProj pred * (Δ.1 σ).1.mat * diagProj pred) := by rw [hΔ σ]
    _ = (diagProj pred * diagProj pred) * (Δ.1 σ).1.mat * diagProj pred := by
          simp only [Matrix.mul_assoc]
    _ = (Δ.1 σ).1.mat := by rw [diagProj_mul_self, hΔ σ]
theorem supportedOn_qSet {Var : Type} {d : ℕ} [NeZero d] {pred : Fin d → Prop}
    [DecidablePred pred] (h0 : pred 0) (Δ : CQState (Store Var) d) :
    SupportedOn pred Δ.qSet := by
  intro σ
  rw [Operator.cqState_qSet_mat]
  set tr : ℂ := ((Δ.1 σ).1.trace : ℂ)
  ext a b
  rw [diagProj_mul_mul_diagProj_apply]
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 0
    · subst hb; simp [h0]
    · simp [Ne.symm hb]
  · simp [Ne.symm ha]
theorem expect_of_supportedOn {Var : Type} {d : ℕ} {pred : Fin d → Prop} [DecidablePred pred]
    {Δ : CQState (Store Var) d} (hΔ : SupportedOn pred Δ) {Θ : CQAssertion (Store Var) d} {c : ℝ}
    (hΘ : ∀ σ, diagProj pred * (Θ σ).1.mat * diagProj pred = (c : ℂ) • diagProj pred) :
    𝔼[Δ, Θ] = c * Δ.trace := by
  rw [qcExpectEqTsumStore, qcTraceEqTsumStore, ← tsum_mul_left]
  refine tsum_congr fun σ ↦ ?_
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace]
  have hM := hΔ σ
  have hM_left := supportedOn_mul_left hΔ σ
  have hA := hΘ σ
  set M := (Δ.1 σ).1.mat
  set A := (Θ σ).1.mat
  have htr : (A * M).trace = (c : ℂ) * M.trace :=
    calc (A * M).trace
        = (A * (diagProj pred * M * diagProj pred)).trace := by rw [hM]
      _ = ((A * (diagProj pred * M)) * diagProj pred).trace := by
            simp only [Matrix.mul_assoc]
      _ = (diagProj pred * (A * (diagProj pred * M))).trace :=
            Matrix.trace_mul_comm _ (diagProj pred)
      _ = ((diagProj pred * A * diagProj pred) * M).trace := by
            simp only [Matrix.mul_assoc]
      _ = (((c : ℂ) • diagProj pred) * M).trace := by rw [hA]
      _ = (c : ℂ) * M.trace := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hM_left]
  rw [htr]
  simp
theorem supportedOn_of_expect_diagAssertion_eq_trace {Var : Type} {d : ℕ}
    {pred : Fin d → Prop} [DecidablePred pred] {Δ : CQState (Store Var) d}
    (h : 𝔼[Δ, diagAssertion pred] = Δ.trace) :
    SupportedOn pred Δ := by
  let nPred : Fin d → Prop := fun z ↦ ¬ pred z
  have hsum_obs : (diagObs pred).1 + (diagObs nPred).1 = 1 := by
    ext a b
    simp only [HermitianMat.mat_add, HermitianMat.mat_one, diagObs_mat, diagProj,
      Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply, nPred]
    by_cases hab : a = b
    · subst hab; by_cases hp : pred a <;> simp [hp]
    · simp [hab]
  have hpart : 𝔼[Δ, diagAssertion pred] + 𝔼[Δ, diagAssertion nPred] = Δ.trace := by
    rw [qcExpectEqTsumStore Δ (diagAssertion pred), qcExpectEqTsumStore Δ (diagAssertion nPred),
      ← (qcSummableExpectStore Δ (diagAssertion pred)).tsum_add
        (qcSummableExpectStore Δ (diagAssertion nPred)),
      qcTraceEqTsumStore]
    refine tsum_congr fun σ ↦ ?_
    rw [← inner_add_left]
    change ⟪(diagObs pred).1 + (diagObs nPred).1, (Δ.1 σ).1⟫_ℝ = _
    rw [hsum_obs, HermitianMat.one_inner]
  have hzero_exp : 𝔼[Δ, diagAssertion nPred] = 0 := by linarith
  intro σ
  have hzero_σ : ⟪(diagObs nPred).1, (Δ.1 σ).1⟫_ℝ = 0 := by
    apply le_antisymm
    · have hle := Summable.le_tsum (qcSummableExpectStore Δ (diagAssertion nPred)) σ
        (fun τ _ ↦ expect_term_nonneg Δ (diagAssertion nPred) τ)
      rw [← qcExpectEqTsumStore, hzero_exp] at hle
      exact hle
    · exact expect_term_nonneg Δ (diagAssertion nPred) σ
  set M := (Δ.1 σ).1.mat
  have hpos : M.PosSemidef := (Δ.1 σ).posSemidef_val
  have hdiag_zero : ∀ z : Fin d, ¬ pred z → M z z = 0 := by
    have htr : ∑ z : Fin d, (if ¬ pred z then (M z z).re else 0) = 0 := by
      rw [HermitianMat.inner_eq_re_trace, RCLike.re_eq_complex_re, diagObs_mat, diagProj] at hzero_σ
      have hmul : (Matrix.diagonal (fun z ↦ if nPred z then (1 : ℂ) else 0) * M).trace.re =
          ∑ z : Fin d, (if ¬ pred z then (M z z).re else 0) := by
        rw [Matrix.trace, Complex.re_sum]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [Matrix.diag_apply, Matrix.diagonal_mul]
        by_cases hp : pred z <;> simp [nPred, hp]
      linarith
    have hnn : ∀ z ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ (if ¬ pred z then (M z z).re else 0) := by
      intro z _
      by_cases hp : pred z <;> simp [hp, (Complex.nonneg_iff.1 hpos.diag_nonneg).1]
    intro z hz
    have hre0 : (M z z).re = 0 := by
      have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 htr z (Finset.mem_univ z)
      simpa [hz] using hz0
    have him0 : (M z z).im = 0 := (Complex.nonneg_iff.1 hpos.diag_nonneg).2.symm
    exact Complex.ext hre0 him0
  have hcol_zero : ∀ z : Fin d, ¬ pred z → ∀ a : Fin d, M a z = 0 := by
    intro z hz a
    have hdot : star (Pi.single z (1 : ℂ)) ⬝ᵥ M *ᵥ Pi.single z (1 : ℂ) = 0 := by
      simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hdiag_zero z hz
    have hmv := hpos.dotProduct_mulVec_zero_iff.1 hdot
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hmv a
  have hrow_zero : ∀ z : Fin d, ¬ pred z → ∀ b : Fin d, M z b = 0 := by
    intro z hz b
    have hH : M b z = 0 := hcol_zero z hz b
    have := congrFun (congrFun hpos.isHermitian.eq z) b
    simpa [Matrix.conjTranspose_apply, hH] using this.symm
  ext a b
  rw [diagProj_mul_mul_diagProj_apply]
  by_cases ha : pred a
  · by_cases hb : pred b
    · simp [ha, hb]
    · simp [ha, hb, hcol_zero b hb a]
  · simp [ha, hrow_zero a ha b]
/- ## Stage basis invariant and readout decoding -/

/-- Active memory slot indices `{0,..., j - 1}` already populated at stage `j`. -/
def activeMemSlots (k j : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun l : Fin k ↦ l.val < j
@[simp]
theorem mem_activeMemSlots {k j : ℕ} {l : Fin k} :
    l ∈ activeMemSlots k j ↔ l.val < j := by
  simp [activeMemSlots]
theorem card_activeMemSlots {k j : ℕ} (hj : j ≤ k) :
    (activeMemSlots k j).card = j := by
  have hbij : (activeMemSlots k j).card = (Finset.range j).card := by
    refine Finset.card_bij (fun l _ ↦ l.val) ?_ ?_ ?_
    · intro l hl
      exact Finset.mem_range.2 (mem_activeMemSlots.1 hl)
    · intro l₁ _ l₂ _ h
      exact Fin.ext h
    · intro x hx
      rw [Finset.mem_range] at hx
      exact ⟨⟨x, lt_of_lt_of_le hx hj⟩, mem_activeMemSlots.2 hx, rfl⟩
  rw [hbij, Finset.card_range]
/-- Valid computational-basis states at the start of stage `j`:
  `oracleReg` is `0`, `mem_0.. mem_{j-1}` hold `j` pairwise distinct elements of `S`, and
  `mem_j.. mem_{k-1}` are `0`. -/
def ValidStageBasis (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (z : Fin (2 ^ findAllQubits n m k)) : Prop :=
  (oracleReg n m k).extractIndex z = 0 ∧
  (∀ l : Fin k, l.val < j → (memSlotReg n m k l).extractIndex z ∈ S) ∧
  (∀ l₁ l₂ : Fin k, l₁.val < j → l₂.val < j →
    (memSlotReg n m k l₁).extractIndex z = (memSlotReg n m k l₂).extractIndex z → l₁ = l₂) ∧
  (∀ l : Fin k, j ≤ l.val → (memSlotReg n m k l).extractIndex z = 0)
instance instDecidablePredValidStageBasis (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    DecidablePred (ValidStageBasis n m k S j) := by
  intro z
  unfold ValidStageBasis
  infer_instance
theorem extractIndex_zero {q Q : ℕ} (r : QRegister q Q) : r.extractIndex 0 = 0 := by
  apply (basisBits q).injective
  funext i
  rw [r.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
  simp
theorem validStageBasis_zero (n m k : ℕ) (S : Finset (Fin (2 ^ n))) :
    ValidStageBasis n m k S 0 0 := by
  refine ⟨extractIndex_zero _, ?_, ?_, ?_⟩
  · intro l hl; omega
  · intro l₁ _ hl₁; omega
  · intro l _
    exact extractIndex_zero _
theorem validStageBasis_memFoundSet_subset {n m k j : ℕ} {S : Finset (Fin (2 ^ n))}
    {z : Fin (2 ^ findAllQubits n m k)} (hz : ValidStageBasis n m k S j z) :
    memFoundSet n m k (activeMemSlots k j) z ⊆ S := by
  intro x hx
  simp only [memFoundSet, Finset.mem_image, mem_activeMemSlots] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  exact hz.2.1 l hl
theorem validStageBasis_card_sdiff {n m k j : ℕ} {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hj : j ≤ k) {z : Fin (2 ^ findAllQubits n m k)}
    (hz : ValidStageBasis n m k S j z) :
    (S \ memFoundSet n m k (activeMemSlots k j) z).card = k - j := by
  have hsub := validStageBasis_memFoundSet_subset hz
  have hcardT : (memFoundSet n m k (activeMemSlots k j) z).card = j := by
    rw [memFoundSet, Finset.card_image_of_injOn]
    · exact card_activeMemSlots hj
    · intro l₁ hl₁ l₂ hl₂ heq
      exact hz.2.2.1 l₁ l₂ (mem_activeMemSlots.1 hl₁) (mem_activeMemSlots.1 hl₂) heq
  have hadd := Finset.card_sdiff_add_card_eq_card hsub
  omega
theorem validStageBasis_write_succ {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (j : Fin k)
    {z : Fin (2 ^ findAllQubits n m k)} (hz : ValidStageBasis n m k S j.val z)
    {x : Fin (2 ^ n)} (hx : x ∈ S \ memFoundSet n m k (activeMemSlots k j.val) z) :
    ValidStageBasis n m k S (j.val + 1) ((memSlotReg n m k j).replaceIndex z x) := by
  rw [Finset.mem_sdiff] at hx
  have hdisj_or : (oracleReg n m k).DisjointWires (memSlotReg n m k j) :=
    (oracleReg_disjoint_memAllReg n m k).compose_right (localMemSlotReg n k j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(oracleReg n m k).extractIndex_replaceIndex_of_disjoint _ hdisj_or]
    exact hz.1
  · intro l hl
    by_cases hlj : l = j
    · subst l
      rw [QRegister.extractIndex_replaceIndex]
      exact hx.1
    · have hlt : l.val < j.val := by omega
      rw [(memSlotReg n m k l).extractIndex_replaceIndex_of_disjoint _ (memSlotReg_disjoint hlj)]
      exact hz.2.1 l hlt
  · intro l₁ l₂ hl₁ hl₂ heq
    by_cases h1 : l₁ = j
    · subst l₁
      by_cases h2 : l₂ = j
      · exact h2.symm
      · exfalso
        have hlt2 : l₂.val < j.val := by omega
        rw [QRegister.extractIndex_replaceIndex,
          (memSlotReg n m k l₂).extractIndex_replaceIndex_of_disjoint _
            (memSlotReg_disjoint h2)] at heq
        apply hx.2
        rw [memFoundSet, Finset.mem_image]
        exact ⟨l₂, mem_activeMemSlots.2 hlt2, heq.symm⟩
    · by_cases h2 : l₂ = j
      · subst l₂
        exfalso
        have hlt1 : l₁.val < j.val := by omega
        rw [QRegister.extractIndex_replaceIndex,
          (memSlotReg n m k l₁).extractIndex_replaceIndex_of_disjoint _
            (memSlotReg_disjoint h1)] at heq
        apply hx.2
        rw [memFoundSet, Finset.mem_image]
        exact ⟨l₁, mem_activeMemSlots.2 hlt1, heq⟩
      · have hlt1 : l₁.val < j.val := by omega
        have hlt2 : l₂.val < j.val := by omega
        rw [(memSlotReg n m k l₁).extractIndex_replaceIndex_of_disjoint _
              (memSlotReg_disjoint h1),
            (memSlotReg n m k l₂).extractIndex_replaceIndex_of_disjoint _
              (memSlotReg_disjoint h2)] at heq
        exact hz.2.2.1 l₁ l₂ hlt1 hlt2 heq
  · intro l hl
    have hlj : l ≠ j := fun h ↦ by subst l; omega
    rw [(memSlotReg n m k l).extractIndex_replaceIndex_of_disjoint _ (memSlotReg_disjoint hlj)]
    exact hz.2.2.2 l (by omega)
/-- Mirror of `Specs.decodeTargets` (`rfl`-equal). -/
def decodeTargetsLocal (n k : ℕ) (z : ℤ) : Finset (Fin (2 ^ n)) :=
  (Finset.range k).image fun i ↦
    ⟨(z.toNat / (2 ^ n) ^ i) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
theorem decodeTargetsLocal_memAllReg_eq {n m k : ℕ} {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) {z : Fin (2 ^ findAllQubits n m k)}
    (hz : ValidStageBasis n m k S k z) :
    decodeTargetsLocal n k (((memAllReg n m k).extractIndex z).val : ℤ) = S := by
  set w := (memAllReg n m k).extractIndex z
  have himg : decodeTargetsLocal n k (w.val : ℤ) =
      Finset.univ.image (fun l : Fin k ↦ (memSlotReg n m k l).extractIndex z) := by
    ext x
    simp only [decodeTargetsLocal, Int.toNat_natCast, Finset.mem_image, Finset.mem_range,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [memSlotReg, QRegister.extractIndex_compose, extractIndex_localMemSlotReg_eq]
    · rintro ⟨l, rfl⟩
      refine ⟨l.val, l.isLt, ?_⟩
      rw [memSlotReg, QRegister.extractIndex_compose, extractIndex_localMemSlotReg_eq]
  rw [himg]
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨l, _, rfl⟩ := hx
    exact hz.2.1 l l.isLt
  · rw [hScard, Finset.card_image_of_injective]
    · simp
    · intro l₁ l₂ heq
      exact hz.2.2.1 l₁ l₂ l₁.isLt l₂.isLt heq
/- ## Classical slot extraction from `res` after parallel verification -/

/-- Base-`2^(n+1)` digit `i` of a natural number `v` (matching `localSlotReg n m i`). -/
def slotValNat (n v i : ℕ) : ℕ :=
  (v / (2 ^ (n + 1)) ^ i) % 2 ^ (n + 1)
/-- Whether slot `i` has marker bit `1` in measurement outcome `v`. -/
def slotMarkedNat (n v i : ℕ) : Bool :=
  decide (slotValNat n v i % 2 = 1)
/-- Index bits `1..n` of slot `i` in measurement outcome `v`. -/
def slotIdxNat (n v i : ℕ) : ℕ :=
  (slotValNat n v i / 2) % 2 ^ n
/-- List of slot positions `i < m` whose marker bit is `1`. -/
def markedSlotsList (n m v : ℕ) : List ℕ :=
  (List.range m).filter (slotMarkedNat n v)
/-- Whether at least one of the `m` parallel slots has marker bit `1`. -/
def hasMarkedSlotNat (n m v : ℕ) : Bool :=
  !(markedSlotsList n m v).isEmpty
/-- Extract the `n`-bit index of the first marked slot from classical store value `z: ℤ`. -/
def extractMarkedIdx (n m : ℕ) (z : ℤ) : ℕ :=
  match markedSlotsList n m z.toNat with
  | [] => 0
  | i :: _ => slotIdxNat n z.toNat i
theorem extractMarkedIdx_lt (n m : ℕ) (z : ℤ) :
    extractMarkedIdx n m z < 2 ^ n := by
  unfold extractMarkedIdx
  split
  · positivity
  · exact Nat.mod_lt _ (by positivity)
theorem hasMarkedSlotNat_zero (n m : ℕ) :
    hasMarkedSlotNat n m 0 = false := by
  have hnil : markedSlotsList n m 0 = [] := by
    rw [markedSlotsList, List.filter_eq_nil_iff]
    intro i _
    simp [slotMarkedNat, slotValNat]
  simp [hasMarkedSlotNat, hnil]
theorem slotValNat_eq_extractIndex {n m : ℕ} (o : Fin (2 ^ ((n + 1) * m))) (i : Fin m) :
    slotValNat n o.val i.val = ((localSlotReg n m i).extractIndex o).val := by
  rw [extractIndex_localSlotReg_eq]
  rfl
theorem slotMarkedNat_eq_true_iff {n m : ℕ} (o : Fin (2 ^ ((n + 1) * m))) (i : Fin m) :
    slotMarkedNat n o.val i.val = true ↔
      (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex o) = 1 := by
  rw [slotMarkedNat, decide_eq_true_iff, slotValNat_eq_extractIndex,
    extractIndex_localMarkerReg_eq, Fin.ext_iff]
  rfl
theorem hasMarkedSlotNat_eq_false_iff {n m : ℕ} (o : Fin (2 ^ ((n + 1) * m))) :
    hasMarkedSlotNat n m o.val = false ↔
      ∀ i : Fin m, (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex o) = 0 := by
  simp only [hasMarkedSlotNat, Bool.not_eq_false', List.isEmpty_iff, markedSlotsList,
    List.filter_eq_nil_iff, List.mem_range]
  constructor
  · intro hall i
    have hf := hall i.val i.isLt
    have hne1 : (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex o) ≠ 1 := by
      intro h1
      exact hf ((slotMarkedNat_eq_true_iff o i).2 h1)
    generalize (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex o) = b at hne1 ⊢
    fin_cases b
    · rfl
    · exact (hne1 rfl).elim
  · intro hall i hi
    let iFin : Fin m := ⟨i, hi⟩
    have h0 := hall iFin
    intro ht
    have h1 := (slotMarkedNat_eq_true_iff o iFin).1 ht
    rw [h0] at h1
    exact zero_ne_one h1
theorem sum_normSq_parallelFinalVec_univ {n m : ℕ} (A : Finset (Fin (2 ^ n))) (K : ℕ) :
    ∑ o : Fin (2 ^ ((n + 1) * m)), Complex.normSq (parallelFinalVec m A K o) = 1 := by
  rw [← parallelSlotProd_slotFinalUnitary_mulVec_zero,
    sum_normSq_unitary_mulVec (parallelSlotProd m (slotFinalUnitary n A K))]
  simp [Pi.single_apply]
theorem sum_normSq_parallelFinalVec_hasMarked_false {n m : ℕ} (A : Finset (Fin (2 ^ n)))
    (hr : 1 ≤ A.card) (hrN : A.card ≤ 2 ^ n) (K : ℕ) :
    (∑ o : Fin (2 ^ ((n + 1) * m)) with hasMarkedSlotNat n m o.val = false,
      Complex.normSq (parallelFinalVec m A K o)) =
    (1 - p_succ_set K n A.card) ^ m := by
  rw [← sum_normSq_parallelFinalVec_all_marker_zero A hr hrN K]
  congr 1
  ext o
  simp [hasMarkedSlotNat_eq_false_iff]
theorem sum_normSq_parallelFinalVec_hasMarked_true {n m : ℕ} (A : Finset (Fin (2 ^ n)))
    (hr : 1 ≤ A.card) (hrN : A.card ≤ 2 ^ n) (K : ℕ) :
    (∑ o : Fin (2 ^ ((n + 1) * m)) with hasMarkedSlotNat n m o.val = true,
      Complex.normSq (parallelFinalVec m A K o)) =
    1 - (1 - p_succ_set K n A.card) ^ m := by
  have hpart : (Finset.univ : Finset (Fin (2 ^ ((n + 1) * m)))) =
      (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦ hasMarkedSlotNat n m o.val = false) ∪
      (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦ hasMarkedSlotNat n m o.val = true) := by
    ext o
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    cases hasMarkedSlotNat n m o.val <;> simp
  have hdisj : Disjoint
      (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦ hasMarkedSlotNat n m o.val = false)
      (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦ hasMarkedSlotNat n m o.val = true) := by
    rw [Finset.disjoint_filter]
    intro _ _ h0 h1
    rw [h0] at h1
    exact Bool.noConfusion h1
  have htot := sum_normSq_parallelFinalVec_univ (m := m) A K
  rw [hpart, Finset.sum_union hdisj,
    sum_normSq_parallelFinalVec_hasMarked_false A hr hrN K] at htot
  linarith
theorem extractMarkedIdx_mem_of_parallelFinalVec_ne_zero {n m : ℕ}
    {A : Finset (Fin (2 ^ n))} {K : ℕ} {o : Fin (2 ^ ((n + 1) * m))}
    (hmark : hasMarkedSlotNat n m o.val = true)
    (hne : parallelFinalVec m A K o ≠ 0) :
    (⟨extractMarkedIdx n m (o.val : ℤ),
      extractMarkedIdx_lt n m (o.val : ℤ)⟩ : Fin (2 ^ n)) ∈ A := by
  unfold hasMarkedSlotNat at hmark
  rw [Bool.not_eq_true', List.isEmpty_eq_false_iff] at hmark
  cases hlist : markedSlotsList n m o.val with
  | nil => exact (hmark hlist).elim
  | cons i rest =>
      have hmem : i ∈ markedSlotsList n m o.val := by rw [hlist]; exact List.mem_cons_self
      rw [markedSlotsList, List.mem_filter, List.mem_range] at hmem
      let iFin : Fin m := ⟨i, hmem.1⟩
      have hb1 : (localMarkerReg n).extractIndex ((localSlotReg n m iFin).extractIndex o) = 1 :=
        (slotMarkedNat_eq_true_iff o iFin).1 hmem.2
      have hex : extractMarkedIdx n m (o.val : ℤ) = slotIdxNat n o.val i := by
        simp [extractMarkedIdx, Int.toNat_natCast, hlist]
      have hidx : (⟨extractMarkedIdx n m (o.val : ℤ),
            extractMarkedIdx_lt n m (o.val : ℤ)⟩ : Fin (2 ^ n)) =
          (localIdxReg n).extractIndex ((localSlotReg n m iFin).extractIndex o) := by
        ext
        dsimp only
        rw [hex, slotIdxNat]
        change slotValNat n o.val iFin.val / 2 % 2 ^ n = _
        rw [slotValNat_eq_extractIndex, extractIndex_localIdxReg_eq]
      rw [hidx]
      by_contra hnot
      exact hne (parallelFinalVec_eq_zero_of_slot_false_positive iFin hb1 hnot)
/- ## Stage dynamic circuit and unitary core reduction -/

/-- One parallel Grover iteration using the unmarked effective oracle and `m`-slot parallel
  diffuser. -/
noncomputable def groverIterCircuit {Var : Type} (n m k : ℕ) (activeMem : Finset (Fin k)) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (effectiveOracleCircuit n m k activeMem)
    (.step (phaseI ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)))))
/-- `K` coherent Grover iterations followed by marker unpreparation and one verification
  query. -/
noncomputable def searchCoreCircuit {Var : Type} (n m k : ℕ) (activeMem : Finset (Fin k))
    (K : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (.step (phaseI ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n)))))
    (.seq (OracleDynamicCircuit.sequence (List.replicate K (groverIterCircuit n m k activeMem)))
      (.seq (.step (phaseI
          ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n)))))
        (effectiveOracleCircuit n m k activeMem)))
/-- Body of stage `j`'s repeat-until-success loop: run `searchCoreCircuit` and measure+reset
  `oracleReg` into `res`. -/
noncomputable def attemptBodyCircuit {Var : Type} (res : Var) (n m k : ℕ) (j : Fin k) (K : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (searchCoreCircuit n m k (activeMemSlots k j.val) K)
    (resetRegCircuit res (oracleReg n m k))
/-- Loop continuation condition: no parallel slot reported marker bit `1`. -/
def stageGuard {Var : Type} (res : Var) (n m : ℕ) (σ : Store Var) : Prop :=
  hasMarkedSlotNat n m (σ res).toNat = false
instance instDecidablePredStageGuard {Var : Type} (res : Var) (n m : ℕ) :
    DecidablePred (stageGuard res n m) := by
  intro σ
  unfold stageGuard
  infer_instance
/-- Full circuit for stage `j`: initialize `res:= 0` by measuring clean `oracleReg`, repeat
  `attemptBodyCircuit` until `hasMarkedSlotNat` becomes `true`, then write the harvested
  target
  into clean `memSlotReg j`. -/
noncomputable def stageCircuit {Var : Type} (res : Var) (n m k : ℕ) (j : Fin k) (K : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (.measure res (oracleReg n m k))
    (.seq (.qWhile (stageGuard res n m) (attemptBodyCircuit res n m k j K))
      (xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j)))
/-- Sequence of the last `rem` stages `k - rem.. k - 1`. -/
noncomputable def stagesRemCircuit {Var : Type} (res : Var)
    (iterFn : ℕ → ℕ → ℕ → ℕ) (n m k : ℕ) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | 0 => .skip
  | rem + 1 =>
      if h : k - (rem + 1) < k then
        .seq (stageCircuit res n m k ⟨k - (rem + 1), h⟩ (iterFn m n (rem + 1)))
          (stagesRemCircuit res iterFn n m k rem)
      else
        .skip
/-- Full `FindAll` circuit: run all `k` stages `0.. k - 1`, then measure `memAllReg` into
  `res`.
  Marked `abbrev` so `groverFindAllProgram` retains `ReducibilityHints.regular(37)`. -/
noncomputable abbrev findAllCircuit {Var : Type} (res : Var)
    (iterFn : ℕ → ℕ → ℕ → ℕ) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (stagesRemCircuit res iterFn n m k k)
    (.measure res (memAllReg n m k))
/- ### CostBound of `attemptBodyCircuit` -/

theorem costBound_groverIterLoop {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (activeMem : Finset (Fin k)) (S : Finset (Fin (2 ^ n))) (K : ℕ) :
    CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      ((OracleDynamicCircuit.sequence
          (List.replicate K (groverIterCircuit (Var := Var) n m k activeMem))).compile
        QProg.qAssign (parallelMarkingOracle m S))
      (K : ℝ≥0) := by
  induction K with
  | zero =>
      simpa using CostBound.skip_zero (Var := Var)
        (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
  | succ K ih =>
      rw [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      have hdiff : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
          (.qAssign (phaseI ((oracleReg n m k).embedUnitary
              (parallelSlotProd m (slotDiffuserLocal n))))) 0 := by
        have hc := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero
          (U := (oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)))
          (isRealMatrix_parallelMarkingOracle (m := m) S)
          (isRealMatrix_embedMatrix _
            (isRealMatrix_parallelSlotProd (isRealMatrix_slotDiffuserLocal n)))
        simpa [hc] using CostBound.qAssign (Var := Var)
          (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
          (phaseI ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n))))
      have hiter : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
          ((groverIterCircuit (Var := Var) n m k activeMem).compile
            QProg.qAssign (parallelMarkingOracle m S)) 1 := by
        simp only [groverIterCircuit, OracleDynamicCircuit.compile_seq,
          OracleDynamicCircuit.compile_step]
        simpa using CostBound.seq (costBound_effectiveOracleCircuit n m k activeMem S) hdiff
      have hseq := CostBound.seq hiter ih
      simpa [Nat.cast_add, Nat.cast_one, add_comm] using hseq
theorem costBound_attemptBodyCircuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ)
    (j : Fin k) (K : ℕ) (S : Finset (Fin (2 ^ n))) :
    CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      ((attemptBodyCircuit res n m k j K).compile QProg.qAssign (parallelMarkingOracle m S))
      ((K : ℝ≥0) + 1) := by
  have horacle := isRealMatrix_parallelMarkingOracle (m := m) S
  have hprep : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (.qAssign (phaseI ((oracleReg n m k).embedUnitary
          (parallelSlotProd m (slotPrepLocal n))))) 0 := by
    have hc := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero
      (U := (oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))) horacle
      (isRealMatrix_embedMatrix _ (isRealMatrix_parallelSlotProd (isRealMatrix_slotPrepLocal n)))
    simpa [hc] using CostBound.qAssign (Var := Var)
      (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (phaseI ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))))
  have hunprep : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (.qAssign (phaseI ((oracleReg n m k).embedUnitary
          (parallelSlotProd m (slotUnprepLocal n))))) 0 := by
    have hc := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero
      (U := (oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n))) horacle
      (isRealMatrix_embedMatrix _ (isRealMatrix_parallelSlotProd (isRealMatrix_slotUnprepLocal n)))
    simpa [hc] using CostBound.qAssign (Var := Var)
      (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (phaseI ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n))))
  have hloop := costBound_groverIterLoop (Var := Var) n m k (activeMemSlots k j.val) S K
  have hver := costBound_effectiveOracleCircuit (Var := Var) n m k (activeMemSlots k j.val) S
  have hreset := costBound_resetRegCircuit horacle res (oracleReg n m k)
  simp only [attemptBodyCircuit, searchCoreCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step]
  simpa using CostBound.seq
    (CostBound.seq hprep (CostBound.seq hloop (CostBound.seq hunprep hver))) hreset
/- ### Unitary core `wp` reduction and `attemptBodyCircuit` action on `ValidStageBasis` -/

/-- Effective global unitary corresponding to `searchCoreCircuit` (with `phaseI` stripped). -/
noncomputable def searchCoreUnitary (n m k : ℕ) (activeMem : Finset (Fin k))
    (S : Finset (Fin (2 ^ n))) (K : ℕ) : Unitary (2 ^ findAllQubits n m k) :=
  let Oeff : Unitary (2 ^ findAllQubits n m k) :=
    unmarkUnitary n m k activeMem * (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)
  let Dglob : Unitary (2 ^ findAllQubits n m k) :=
    (oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n))
  let Pglob : Unitary (2 ^ findAllQubits n m k) :=
    (oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))
  let Uglob : Unitary (2 ^ findAllQubits n m k) :=
    (oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n))
  Oeff * Uglob * (Dglob * Oeff) ^ K * Pglob
theorem wp_replicate_qAssign {Var : Type} [DecidableEq Var] {Q w : ℕ}
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
    (oracle : Unitary (2 ^ w)) (U : Unitary (2 ^ Q))
    (hc : ∀ Θ : CQAssertion (Store Var) (2 ^ Q),
      wp (c.compile QProg.qAssign oracle) Θ = Θ.qAssign U)
    (K : ℕ) (Θ : CQAssertion (Store Var) (2 ^ Q)) :
    wp ((OracleDynamicCircuit.sequence (List.replicate K c)).compile QProg.qAssign oracle) Θ =
      Θ.qAssign (U ^ K) := by
  induction K generalizing Θ with
  | zero =>
      simp only [List.replicate_zero, OracleDynamicCircuit.sequence_nil,
        OracleDynamicCircuit.compile_skip, wp_skip, pow_zero, CQAssertion.qAssign_one]
  | succ K ih =>
      rw [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq, wp_qSeq, ih, hc, CQAssertion.qAssign_qAssign, ← pow_succ]
theorem wp_groverIterCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (activeMem : Finset (Fin k)) (S : Finset (Fin (2 ^ n)))
    (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) :
    wp ((groverIterCircuit (Var := Var) n m k activeMem).compile
        QProg.qAssign (parallelMarkingOracle m S)) Θ =
      Θ.qAssign ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
        (unmarkUnitary n m k activeMem *
          (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) := by
  rw [groverIterCircuit, effectiveOracleCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_oracle,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_step,
    wp_qSeq, wp_qSeq, wp_qAssign, wp_qAssign, wp_qAssign, qAssign_phaseI, qAssign_phaseI,
    CQAssertion.qAssign_qAssign, CQAssertion.qAssign_qAssign]
theorem wp_groverIterLoop {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (activeMem : Finset (Fin k)) (S : Finset (Fin (2 ^ n))) (K : ℕ)
    (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) :
    wp ((OracleDynamicCircuit.sequence
          (List.replicate K (groverIterCircuit (Var := Var) n m k activeMem))).compile
        QProg.qAssign (parallelMarkingOracle m S)) Θ =
      Θ.qAssign (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
        (unmarkUnitary n m k activeMem *
          (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) ^ K) :=
  wp_replicate_qAssign _ _ _ (wp_groverIterCircuit n m k activeMem S) K Θ
theorem wp_searchCoreCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (activeMem : Finset (Fin k)) (S : Finset (Fin (2 ^ n))) (K : ℕ)
    (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) :
    wp ((searchCoreCircuit (Var := Var) n m k activeMem K).compile
        QProg.qAssign (parallelMarkingOracle m S)) Θ =
      Θ.qAssign (searchCoreUnitary n m k activeMem S K) := by
  simp only [searchCoreCircuit, effectiveOracleCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle,
    wp_qSeq, wp_groverIterLoop, wp_qAssign, qAssign_phaseI]
  simp only [CQAssertion.qAssign_qAssign, searchCoreUnitary, mul_assoc]
theorem oracleEmbed_comm_memTupleProj {n m k : ℕ} (activeMem : Finset (Fin k))
    (memTuple : Fin k → Fin (2 ^ n))
    (A : Matrix (Fin (2 ^ ((n + 1) * m))) (Fin (2 ^ ((n + 1) * m))) ℂ) :
    (oracleReg n m k).embedMatrix A * memTupleProj n m k activeMem memTuple =
      memTupleProj n m k activeMem memTuple * (oracleReg n m k).embedMatrix A := by
  ext a b
  rw [memTupleProj, Matrix.mul_diagonal, Matrix.diagonal_mul,
    QRegister.embedMatrix_apply_of_agreeOutside]
  by_cases hag : (oracleReg n m k).AgreeOutside a b
  · have hmem_eq : (∀ j ∈ activeMem, (memSlotReg n m k j).extractIndex a = memTuple j) ↔
        (∀ j ∈ activeMem, (memSlotReg n m k j).extractIndex b = memTuple j) := by
      refine forall₂_congr fun j _ ↦ ?_
      have hdisj : (memSlotReg n m k j).DisjointWires (oracleReg n m k) :=
        QRegister.disjoint_comm.1
          ((oracleReg_disjoint_memAllReg n m k).compose_right (localMemSlotReg n k j))
      have hex : (memSlotReg n m k j).extractIndex a = (memSlotReg n m k j).extractIndex b := by
        apply (basisBits n).injective
        funext w
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        exact hag _ (Set.disjoint_left.1 hdisj ⟨w, rfl⟩)
      rw [hex]
    simp [hag, hmem_eq]
  · simp [hag]
theorem embedUnitary_pow {q Q : ℕ} (r : QRegister q Q) (U : Unitary (2 ^ q)) (t : ℕ) :
    r.embedUnitary (U ^ t) = (r.embedUnitary U) ^ t := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, pow_succ, r.embedUnitary_mul, ih]
theorem searchCoreUnitary_mul_memTupleProj {n m k : ℕ} (activeMem : Finset (Fin k))
    (memTuple : Fin k → Fin (2 ^ n)) {S : Finset (Fin (2 ^ n))}
    (hsub : activeMem.image memTuple ⊆ S) (K : ℕ) :
    (searchCoreUnitary n m k activeMem S K).1 * memTupleProj n m k activeMem memTuple =
      ((oracleReg n m k).embedUnitary
          (parallelSlotProd m (slotFinalUnitary n (S \ activeMem.image memTuple) K))).1 *
        memTupleProj n m k activeMem memTuple := by
  set P := memTupleProj n m k activeMem memTuple
  set A := S \ activeMem.image memTuple
  have hOeff : (unmarkUnitary n m k activeMem *
        (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 * P =
      ((oracleReg n m k).embedUnitary (parallelMarkingOracle m A)).1 * P := by
    rw [Submonoid.coe_mul]
    exact unmarkUnitary_mul_parallelOracle_mul_proj activeMem memTuple hsub
  have hcomm (V : Unitary (2 ^ ((n + 1) * m))) :
      ((oracleReg n m k).embedUnitary V).1 * P = P * ((oracleReg n m k).embedUnitary V).1 :=
    oracleEmbed_comm_memTupleProj activeMem memTuple V.1
  have hpow (t : ℕ) :
      (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
          (unmarkUnitary n m k activeMem *
            (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) ^ t).1 * P =
        (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
            (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ t).1 * P := by
    induction t with
    | zero => simp
    | succ t ih =>
        have hstepL : (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
              (unmarkUnitary n m k activeMem *
                (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) ^ (t + 1)).1 =
            ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n))).1 *
              (unmarkUnitary n m k activeMem *
                (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 *
              (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                (unmarkUnitary n m k activeMem *
                  (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) ^ t).1 := by
          rw [pow_succ' _ t, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc]
        have hstepR : (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
              (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ (t + 1)).1 =
            ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n))).1 *
              ((oracleReg n m k).embedUnitary (parallelMarkingOracle m A)).1 *
              (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ t).1 := by
          rw [pow_succ' _ t, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc]
        calc _ = ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n))).1 *
                  (unmarkUnitary n m k activeMem *
                    (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 *
                  ((((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                    (unmarkUnitary n m k activeMem *
                      (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) ^ t).1 * P) := by
                rw [hstepL, Matrix.mul_assoc]
          _ = ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n))).1 *
                ((unmarkUnitary n m k activeMem *
                  (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 * P) *
                (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                  (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ t).1 := by
                rw [ih]
                have hcPow : (((oracleReg n m k).embedUnitary
                      (parallelSlotProd m (slotDiffuserLocal n)) *
                    (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ t).1 * P =
                    P * (((oracleReg n m k).embedUnitary
                      (parallelSlotProd m (slotDiffuserLocal n)) *
                    (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ t).1 := by
                  rw [← (oracleReg n m k).embedUnitary_mul, ← embedUnitary_pow]
                  exact hcomm _
                rw [hcPow, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
          _ = _ := by
                have hcPow : (((oracleReg n m k).embedUnitary
                      (parallelSlotProd m (slotDiffuserLocal n)) *
                    (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ t).1 * P =
                    P * (((oracleReg n m k).embedUnitary
                      (parallelSlotProd m (slotDiffuserLocal n)) *
                    (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ t).1 := by
                  rw [← (oracleReg n m k).embedUnitary_mul, ← embedUnitary_pow]
                  exact hcomm _
                rw [hOeff, hstepR]
                simp only [Matrix.mul_assoc]
                rw [hcPow]
  have hparA : parallelMarkingOracle m A = parallelSlotProd m (setMarkingOracle A) := rfl
  have hcomb :
      (oracleReg n m k).embedUnitary (parallelMarkingOracle m A) *
        (oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n)) *
        ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
          (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K *
        (oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n)) =
      (oracleReg n m k).embedUnitary (parallelSlotProd m (slotFinalUnitary n A K)) := by
    rw [hparA, ← (oracleReg n m k).embedUnitary_mul, parallelSlotProd_mul,
      ← (oracleReg n m k).embedUnitary_mul, parallelSlotProd_mul,
      ← embedUnitary_pow, parallelSlotProd_pow,
      ← (oracleReg n m k).embedUnitary_mul, ← (oracleReg n m k).embedUnitary_mul,
      parallelSlotProd_mul, parallelSlotProd_mul, slotFinalUnitary]
  calc (searchCoreUnitary n m k activeMem S K).1 * P
      = (unmarkUnitary n m k activeMem *
            (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 *
          ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n))).1 *
          (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
            (unmarkUnitary n m k activeMem *
              (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) ^ K).1 *
          (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))).1 * P) := by
          simp only [searchCoreUnitary, Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (unmarkUnitary n m k activeMem *
            (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 *
          ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n))).1 *
          ((((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
            (unmarkUnitary n m k activeMem *
              (oracleReg n m k).embedUnitary (parallelMarkingOracle m S))) ^ K).1 * P) *
          ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))).1 := by
          rw [hcomm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = ((unmarkUnitary n m k activeMem *
            (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1 * P) *
          ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n))).1 *
          (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
            (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K).1 *
          ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))).1 := by
          rw [hpow K]
          have hcPow : (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K).1 * P =
              P * (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K).1 := by
            rw [← (oracleReg n m k).embedUnitary_mul, ← embedUnitary_pow]
            exact hcomm _
          rw [hcPow]
          have hcU := hcomm (parallelSlotProd m (slotUnprepLocal n))
          simp only [Matrix.mul_assoc] at hcU ⊢
          rw [← Matrix.mul_assoc ((oracleReg n m k).embedUnitary
              (parallelSlotProd m (slotUnprepLocal n))).1 P, hcU]
          simp only [Matrix.mul_assoc]
    _ = ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotFinalUnitary n A K))).1 * P := by
          rw [hOeff]
          have hc1 := hcomm (parallelSlotProd m (slotUnprepLocal n))
          have hc2 : (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K).1 * P =
              P * (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K).1 := by
            rw [← (oracleReg n m k).embedUnitary_mul, ← embedUnitary_pow]
            exact hcomm _
          have hc3 := hcomm (parallelSlotProd m (slotPrepLocal n))
          have hpull :
              (((oracleReg n m k).embedUnitary (parallelMarkingOracle m A)).1 * P) *
                ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n))).1 *
                (((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                  (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K).1 *
                ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))).1 =
              (((oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) *
                (oracleReg n m k).embedUnitary (parallelSlotProd m (slotUnprepLocal n)) *
                ((oracleReg n m k).embedUnitary (parallelSlotProd m (slotDiffuserLocal n)) *
                  (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K *
                (oracleReg n m k).embedUnitary (parallelSlotProd m (slotPrepLocal n))).1 * P := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P ((oracleReg n m k).embedUnitary
                (parallelSlotProd m (slotUnprepLocal n))).1, ← hc1]
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P (((oracleReg n m k).embedUnitary
                (parallelSlotProd m (slotDiffuserLocal n)) *
              (oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) ^ K).1, ← hc2]
            simp only [Matrix.mul_assoc]
            rw [← hc3]
          rw [hpull, hcomb]
theorem resetKraus_searchCoreUnitary_mulVec_single {n m k j : ℕ}
    {S : Finset (Fin (2 ^ n))} {z : Fin (2 ^ findAllQubits n m k)}
    (hz : ValidStageBasis n m k S j z) (K : ℕ) (o : Fin (2 ^ ((n + 1) * m))) :
    (oracleReg n m k).resetKraus o *ᵥ
        ((searchCoreUnitary n m k (activeMemSlots k j) S K).1 *ᵥ Pi.single z 1) =
      parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j) z) K o • Pi.single z 1 := by
  let memTuple : Fin k → Fin (2 ^ n) := fun l ↦ (memSlotReg n m k l).extractIndex z
  have himg : (activeMemSlots k j).image memTuple = memFoundSet n m k (activeMemSlots k j) z :=
    rfl
  have hsub : (activeMemSlots k j).image memTuple ⊆ S := validStageBasis_memFoundSet_subset hz
  have hproj : memTupleProj n m k (activeMemSlots k j) memTuple *ᵥ Pi.single z (1 : ℂ) =
      Pi.single z 1 := by
    funext a
    rw [memTupleProj, Matrix.mulVec_diagonal]
    by_cases hab : a = z
    · subst hab; simp [memTuple]
    · simp [hab]
  have hcore : (searchCoreUnitary n m k (activeMemSlots k j) S K).1 *ᵥ Pi.single z (1 : ℂ) =
      (oracleReg n m k).embedMatrix
        (parallelSlotProd m
          (slotFinalUnitary n (S \ memFoundSet n m k (activeMemSlots k j) z) K)).1 *ᵥ
          Pi.single z 1 := by
    rw [← hproj, Matrix.mulVec_mulVec, searchCoreUnitary_mul_memTupleProj _ _ hsub K,
      ← Matrix.mulVec_mulVec, hproj, QRegister.embedUnitary_val, himg]
  rw [hcore, (oracleReg n m k).embedMatrix_mulVec_single_factors, hz.1,
    (oracleReg n m k).resetKraus_mulVec_tensorState,
    parallelSlotProd_slotFinalUnitary_mulVec_zero]
  have hsingle : (Pi.single (0 : Fin (2 ^ ((n + 1) * m)))
        (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j) z) K o)) =
      parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j) z) K o •
        Pi.single ((oracleReg n m k).extractIndex z) (1 : ℂ) := by
    rw [hz.1]
    funext u
    by_cases hu : u = 0 <;> simp [hu]
  rw [hsingle, (oracleReg n m k).tensorState_smul_left,
    (oracleReg n m k).tensorState_single_factors]
/-- Bilinear entry helper `(Aᴴ * B * A) a b = star (A *ᵥ e_a) ⬝ᵥ (B *ᵥ (A *ᵥ e_b))`. -/
theorem conjTranspose_mul_mul_apply_single {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin d) :
    (Aᴴ * B * A) a b =
      star (A *ᵥ Pi.single a 1) ⬝ᵥ (B *ᵥ (A *ᵥ Pi.single b 1)) := by
  have hcol : (Aᴴ * B * A) a b = ((Aᴴ * (B * A)) *ᵥ Pi.single b 1) a := by
    rw [Matrix.mul_assoc, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp [Pi.single_apply]
theorem wp_attemptBodyCircuit_apply_of_valid {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (j : Fin k) (K : ℕ) {S : Finset (Fin (2 ^ n))}
    (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var)
    {a b : Fin (2 ^ findAllQubits n m k)}
    (ha : ValidStageBasis n m k S j.val a) (hb : ValidStageBasis n m k S j.val b) :
    (wp ((attemptBodyCircuit res n m k j K).compile QProg.qAssign (parallelMarkingOracle m S))
        Θ σ).1.mat a b =
      ∑ o : Fin (2 ^ ((n + 1) * m)),
        star (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o) *
          parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) b) K o *
          (Θ (Store.subst σ res ↑o.val)).1.mat a b := by
  simp only [attemptBodyCircuit, OracleDynamicCircuit.compile_seq, wp_qSeq, wp_searchCoreCircuit]
  rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
    wp_resetRegCircuit, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  have hassoc : (searchCoreUnitary n m k (activeMemSlots k j.val) S K).1ᴴ *
        (((oracleReg n m k).resetKraus o)ᴴ *
          (Θ (Store.subst σ res ↑o.val)).1.mat *
          (oracleReg n m k).resetKraus o) *
        (searchCoreUnitary n m k (activeMemSlots k j.val) S K).1 =
      (((oracleReg n m k).resetKraus o *
          (searchCoreUnitary n m k (activeMemSlots k j.val) S K).1)ᴴ *
        (Θ (Store.subst σ res ↑o.val)).1.mat *
        ((oracleReg n m k).resetKraus o *
          (searchCoreUnitary n m k (activeMemSlots k j.val) S K).1)) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hassoc, conjTranspose_mul_mul_apply_single,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    resetKraus_searchCoreUnitary_mulVec_single ha K o,
    resetKraus_searchCoreUnitary_mulVec_single hb K o]
  simp only [Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Matrix.mulVec_single_one]
  have hdot : star (Pi.single a (1 : ℂ)) ⬝ᵥ (Θ (Store.subst σ res ↑o.val)).1.mat.col b =
      (Θ (Store.subst σ res ↑o.val)).1.mat a b := by
    simp [dotProduct, Pi.single_apply]
  rw [hdot]
  ring
theorem star_mul_self_eq_normSq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [RCLike.star_def, mul_comm, Complex.mul_conj]
/- ### `whileActiveWP` and `whileRecWP` exact projected identities -/

theorem diagProj_whileActiveWP_attemptBody {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (j : Fin k) (K : ℕ) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hkN : k ≤ 2 ^ n) (t : ℕ) (σ : Store Var) :
    diagProj (ValidStageBasis n m k S j.val) *
        (whileActiveWP
          (wp ((attemptBodyCircuit res n m k j K).compile
            QProg.qAssign (parallelMarkingOracle m S)))
          (stageGuard res n m) t σ).1.mat *
        diagProj (ValidStageBasis n m k S j.val) =
      ((if stageGuard res n m σ then
          (((1 - p_succ_set K n (k - j.val)) ^ m) ^ t : ℝ)
        else (0 : ℝ)) : ℂ) • diagProj (ValidStageBasis n m k S j.val) := by
  set q := (1 - p_succ_set K n (k - j.val)) ^ m
  induction t generalizing σ with
  | zero =>
      rw [whileActiveWP]
      by_cases hg : stageGuard res n m σ
      · simp [hg]
      · simp [hg]
  | succ t ih =>
      rw [whileActiveWP]
      by_cases hg : stageGuard res n m σ
      · simp only [hg, ↓reduceIte]
        ext a b
        rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]
        by_cases ha : ValidStageBasis n m k S j.val a
        · by_cases hb : ValidStageBasis n m k S j.val b
          · simp only [ha, hb, and_self, ↓reduceIte]
            rw [wp_attemptBodyCircuit_apply_of_valid res j K _ σ ha hb]
            have hterm (o : Fin (2 ^ ((n + 1) * m))) :
                (whileActiveWP
                    (wp ((attemptBodyCircuit res n m k j K).compile
                      QProg.qAssign (parallelMarkingOracle m S)))
                    (stageGuard res n m) t (Store.subst σ res ↑o.val)).1.mat a b =
                  if hasMarkedSlotNat n m o.val = false then
                    if a = b then ((q ^ t : ℝ) : ℂ) else 0
                  else 0 := by
              have hih := congrFun (congrFun (ih (Store.subst σ res ↑o.val)) a) b
              rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply, diagProj,
                Matrix.diagonal_apply] at hih
              simp only [ha, hb, and_self, ↓reduceIte] at hih
              rw [hih]
              simp only [stageGuard]
              by_cases hab : a = b <;> simp [hab]
            simp_rw [hterm]
            by_cases hab : a = b
            · subst hab
              simp only [diagProj, Matrix.diagonal_apply, ha, ↓reduceIte, smul_eq_mul, mul_one,
                mul_ite, mul_zero, ← Finset.sum_filter, ← Finset.sum_mul, star_mul_self_eq_normSq]
              rw [← Complex.ofReal_sum]
              have hcardA : (S \ memFoundSet n m k (activeMemSlots k j.val) a).card = k - j.val :=
                validStageBasis_card_sdiff hScard (le_of_lt j.isLt) ha
              have hr1 : 1 ≤ (S \ memFoundSet n m k (activeMemSlots k j.val) a).card := by
                rw [hcardA]; omega
              have hrN : (S \ memFoundSet n m k (activeMemSlots k j.val) a).card ≤ 2 ^ n := by
                rw [hcardA]; omega
              rw [sum_normSq_parallelFinalVec_hasMarked_false _ hr1 hrN K, hcardA]
              push_cast [q, pow_succ']
              ring
            · simp [hab, diagProj]
          · simp [ha, hb, diagProj, show a ≠ b from fun h ↦ hb (h ▸ ha)]
        · simp [ha, diagProj, Matrix.diagonal_apply]
      · simp [hg]
theorem wp_writeMem_diagAssertion_apply_of_valid {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (j : Fin k) (K : ℕ) {S : Finset (Fin (2 ^ n))}
    (o : Fin (2 ^ ((n + 1) * m))) (σ : Store Var)
    {a b : Fin (2 ^ findAllQubits n m k)}
    (ha : ValidStageBasis n m k S j.val a) (hb : ValidStageBasis n m k S j.val b)
    (hmark : hasMarkedSlotNat n m o.val = true) :
    star (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o) *
        parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) b) K o *
        (wp ((xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j)).compile
              QProg.qAssign (parallelMarkingOracle m S))
            (diagAssertion (ValidStageBasis n m k S (j.val + 1)))
            (Store.subst σ res ↑o.val)).1.mat a b =
      if a = b then
        (Complex.normSq
          (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o) : ℂ)
      else 0 := by
  rw [wp_xorRegCircuit]
  set σ' := Store.subst σ res (o.val : Expr Var)
  have hσ' : σ' res = (o.val : ℤ) := by simp [σ']
  let xStar : Fin (2 ^ n) := ⟨extractMarkedIdx n m (o.val : ℤ), extractMarkedIdx_lt n m (o.val : ℤ)⟩
  have hperm : regMaskVec (memSlotReg n m k j) (extractMarkedIdx n m (σ' res)) =
      regMaskVec (memSlotReg n m k j) xStar.val := by rw [hσ']
  rw [hperm]
  let U := permutationUnitary (xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val))
  have hmat : ((diagAssertion (ValidStageBasis n m k S (j.val + 1))).qAssign U σ').1.mat a b =
      (diagProj (ValidStageBasis n m k S (j.val + 1)))
        (xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val) a)
        (xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val) b) := by
    rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
      conjTranspose_mul_mul_apply_single, permutationUnitary_mulVec_single,
      permutationUnitary_mulVec_single]
    simp [diagAssertion, diagObs_mat, Matrix.col_apply, dotProduct, Pi.single_apply]
  rw [hmat]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, star_mul_self_eq_normSq]
    by_cases hzero : parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o = 0
    · simp [hzero]
    · have hxmem : xStar ∈ S \ memFoundSet n m k (activeMemSlots k j.val) a :=
        extractMarkedIdx_mem_of_parallelFinalVec_ne_zero hmark hzero
      have hrep := xorBitsPerm_regMaskVec_of_clean (memSlotReg n m k j) xStar a (ha.2.2.2 j le_rfl)
      rw [hrep]
      have hv := validStageBasis_write_succ j ha hxmem
      simp [diagProj, hv]
  · have hne : xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val) a ≠
        xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val) b :=
      fun h ↦ hab ((xorBitsPerm _).injective h)
    simp [hab, diagProj, hne]
theorem diagProj_whileRecWP_stage {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (j : Fin k) (K : ℕ) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hkN : k ≤ 2 ^ n) (t : ℕ) (σ : Store Var)
    (hg : stageGuard res n m σ) :
    diagProj (ValidStageBasis n m k S j.val) *
        (whileRecWP
          (wp ((attemptBodyCircuit res n m k j K).compile
            QProg.qAssign (parallelMarkingOracle m S)))
          (stageGuard res n m) (t + 1)
          (wp ((xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j)).compile
                QProg.qAssign (parallelMarkingOracle m S))
              (diagAssertion (ValidStageBasis n m k S (j.val + 1)))) σ).1.mat *
        diagProj (ValidStageBasis n m k S j.val) =
      ((1 - ((1 - p_succ_set K n (k - j.val)) ^ m) ^ t : ℝ) : ℂ) •
        diagProj (ValidStageBasis n m k S j.val) := by
  set Ψ := wp ((xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j)).compile
      QProg.qAssign (parallelMarkingOracle m S))
      (diagAssertion (ValidStageBasis n m k S (j.val + 1)))
  set q := (1 - p_succ_set K n (k - j.val)) ^ m
  induction t generalizing σ with
  | zero =>
      have hbot : wp ((attemptBodyCircuit res n m k j K).compile
          QProg.qAssign (parallelMarkingOracle m S)) ⊥ = ⊥ := by
        simp only [attemptBodyCircuit, OracleDynamicCircuit.compile_seq, wp_qSeq,
          wp_searchCoreCircuit]
        have hr_all : wp ((resetRegCircuit res (oracleReg n m k)).compile
            QProg.qAssign (parallelMarkingOracle m S)) ⊥ = ⊥ := by
          funext ν
          ext1; ext x y
          rw [wp_resetRegCircuit]
          simp
        rw [hr_all, CQAssertion.qAssign_bot]
      simp [whileRecWP, hg, hbot]
  | succ t ih =>
      ext a b
      rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]
      rw [whileRecWP]
      simp only [hg, ↓reduceIte]
      by_cases ha : ValidStageBasis n m k S j.val a
      · by_cases hb : ValidStageBasis n m k S j.val b
        · simp only [ha, hb, and_self, ↓reduceIte]
          rw [wp_attemptBodyCircuit_apply_of_valid res j K _ σ ha hb]
          have hsplit : (Finset.univ : Finset (Fin (2 ^ ((n + 1) * m)))) =
              (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦
                hasMarkedSlotNat n m o.val = false) ∪
              (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦
                hasMarkedSlotNat n m o.val = true) := by
            ext o
            simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
            cases hasMarkedSlotNat n m o.val <;> simp
          have hdisj : Disjoint
              (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦
                hasMarkedSlotNat n m o.val = false)
              (Finset.univ.filter fun o : Fin (2 ^ ((n + 1) * m)) ↦
                hasMarkedSlotNat n m o.val = true) := by
            rw [Finset.disjoint_filter]
            intro _ _ h0 h1; rw [h0] at h1; exact Bool.noConfusion h1
          rw [hsplit, Finset.sum_union hdisj]
          have hfalse_term : ∀ o ∈ Finset.univ.filter (fun o : Fin (2 ^ ((n + 1) * m)) ↦
                hasMarkedSlotNat n m o.val = false),
              star (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o) *
                parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) b) K o *
                (whileRecWP
                  (wp ((attemptBodyCircuit res n m k j K).compile
                    QProg.qAssign (parallelMarkingOracle m S)))
                  (stageGuard res n m) (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat a b =
              if a = b then
                (Complex.normSq
                  (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o) : ℂ) *
                  ((1 - q ^ t : ℝ) : ℂ)
              else 0 := by
            intro o ho
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
            have hg' : stageGuard res n m (Store.subst σ res ↑o.val) := by
              simp [stageGuard, ho]
            have hih := congrFun (congrFun (ih (Store.subst σ res ↑o.val) hg') a) b
            rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply, diagProj,
              Matrix.diagonal_apply] at hih
            simp only [ha, hb, and_self, ↓reduceIte] at hih
            rw [hih]
            by_cases hab : a = b
            · subst hab
              rw [star_mul_self_eq_normSq]
              simp
            · simp [hab]
          have htrue_term : ∀ o ∈ Finset.univ.filter (fun o : Fin (2 ^ ((n + 1) * m)) ↦
                hasMarkedSlotNat n m o.val = true),
              star (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o) *
                parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) b) K o *
                (whileRecWP
                  (wp ((attemptBodyCircuit res n m k j K).compile
                    QProg.qAssign (parallelMarkingOracle m S)))
                  (stageGuard res n m) (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat a b =
              if a = b then
                (Complex.normSq
                  (parallelFinalVec m (S \ memFoundSet n m k (activeMemSlots k j.val) a) K o) : ℂ)
              else 0 := by
            intro o ho
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
            have hng' : ¬ stageGuard res n m (Store.subst σ res ↑o.val) := by
              simp [stageGuard, ho]
            rw [whileRecWP_succ_apply_of_not _ hng']
            exact wp_writeMem_diagAssertion_apply_of_valid res j K o σ ha hb ho
          rw [Finset.sum_congr rfl hfalse_term, Finset.sum_congr rfl htrue_term]
          by_cases hab : a = b
          · subst hab
            simp only [diagProj, Matrix.diagonal_apply, ha, ↓reduceIte, smul_eq_mul, mul_one,
              ← Finset.sum_mul, ← Complex.ofReal_sum]
            have hcardA : (S \ memFoundSet n m k (activeMemSlots k j.val) a).card = k - j.val :=
              validStageBasis_card_sdiff hScard (le_of_lt j.isLt) ha
            have hr1 : 1 ≤ (S \ memFoundSet n m k (activeMemSlots k j.val) a).card := by
              rw [hcardA]; omega
            have hrN : (S \ memFoundSet n m k (activeMemSlots k j.val) a).card ≤ 2 ^ n := by
              rw [hcardA]; omega
            rw [sum_normSq_parallelFinalVec_hasMarked_false _ hr1 hrN K,
              sum_normSq_parallelFinalVec_hasMarked_true _ hr1 hrN K, hcardA]
            push_cast [q, pow_succ']
            ring
          · simp [hab, diagProj]
        · simp [ha, hb, diagProj, show a ≠ b from fun h ↦ hb (h ▸ ha)]
      · simp [ha, diagProj, Matrix.diagonal_apply]
theorem diagProj_wp_measureInit {Var : Type} [DecidableEq Var] (res : Var)
    {n m k j : ℕ} {S : Finset (Fin (2 ^ n))}
    (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var) :
    diagProj (ValidStageBasis n m k S j) *
        (wp (QProg.measureRegister res (oracleReg n m k)) Θ σ).1.mat *
        diagProj (ValidStageBasis n m k S j) =
      diagProj (ValidStageBasis n m k S j) * (Θ (Store.subst σ res 0)).1.mat *
        diagProj (ValidStageBasis n m k S j) := by
  have hproj_o (o : Fin (2 ^ ((n + 1) * m))) :
      (oracleReg n m k).basisOutcomeProjector o =
        diagProj (fun z ↦ (oracleReg n m k).extractIndex z = o) :=
    (oracleReg n m k).basisOutcomeProjector_eq_diagonal o
  ext a b
  rw [diagProj_mul_mul_diagProj_apply, diagProj_mul_mul_diagProj_apply]
  by_cases hvalid : ValidStageBasis n m k S j a ∧ ValidStageBasis n m k S j b
  · obtain ⟨ha, hb⟩ := hvalid
    simp only [ha, hb, and_self, ↓reduceIte]
    rw [wp_measureRegister_coe_ax, HermitianMat.mat_finset_sum,
      Matrix.sum_apply, Finset.sum_eq_single 0]
    · simp only [Nat.cast_zero, Fin.val_zero, HermitianMat.conj_apply_mat,
        QRegister.basisOutcomeProjector_conjTranspose]
      rw [hproj_o, diagProj_mul_mul_diagProj_apply]
      simp [ha.1, hb.1]
    · intro o _ ho
      simp only [HermitianMat.conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose]
      rw [hproj_o, diagProj_mul_mul_diagProj_apply]
      have hne : (oracleReg n m k).extractIndex a ≠ o := by rw [ha.1]; exact ho.symm
      simp [hne]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  · simp [hvalid]
/- ## Single-stage transition theorem and multi-stage induction -/

theorem stage_transition {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hkN : k ≤ 2 ^ n) (j : Fin k) (K : ℕ)
    (hp_pos : 0 < p_succ_set K n (k - j.val))
    {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)}
    (hΔ : SupportedOn (ValidStageBasis n m k S j.val) Δ) :
    let prog := (stageCircuit res n m k j K).compile QProg.qAssign (parallelMarkingOracle m S)
    let q := (1 - p_succ_set K n (k - j.val)) ^ m
    SupportedOn (ValidStageBasis n m k S (j.val + 1)) ((interp prog).toStateFun Δ) ∧
      ((interp prog).toStateFun Δ).trace = Δ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
        stateMass Δ * ENNReal.ofReal (((K : ℝ) + 1) / (1 - q)) := by
  intro prog q
  have hp_le : p_succ_set K n (k - j.val) ≤ 1 := p_succ_set_le_one K n (k - j.val)
  have h1mp_nn : 0 ≤ 1 - p_succ_set K n (k - j.val) := by linarith
  have h1mp_lt : 1 - p_succ_set K n (k - j.val) < 1 := by linarith
  have hq_nn : 0 ≤ q := pow_nonneg h1mp_nn m
  have hq_lt : q < 1 := pow_lt_one₀ h1mp_nn h1mp_lt (by omega)
  have h1mq_pos : 0 < 1 - q := by linarith
  set cInit : QProg Var (2 ^ findAllQubits n m k) := QProg.measureRegister res (oracleReg n m k)
  set cBody : QProg Var (2 ^ findAllQubits n m k) :=
    (attemptBodyCircuit res n m k j K).compile QProg.qAssign (parallelMarkingOracle m S)
  set cLoop : QProg Var (2 ^ findAllQubits n m k) := .qWhile (stageGuard res n m) cBody
  set cWrite : QProg Var (2 ^ findAllQubits n m k) :=
    (xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j)).compile
      QProg.qAssign (parallelMarkingOracle m S)
  have hprog_eq : prog = (cInit ;; (cLoop ;; cWrite)) := rfl
  set Δmid := (interp cInit).toStateFun Δ
  set Δout := (interp prog).toStateFun Δ
  -- Part 1 & 2: Expectation of `diagAssertion (j + 1)` at `Δout` equals `Δ.trace`.
  have hexp_ge (t : ℕ) : (1 - q ^ t) * Δ.trace ≤
      𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] := by
    have hle_wp : whileRecWP (wp cBody) (stageGuard res n m) (t + 1)
          (wp cWrite (diagAssertion (ValidStageBasis n m k S (j.val + 1)))) ≤
        wp cLoop (wp cWrite (diagAssertion (ValidStageBasis n m k S (j.val + 1)))) :=
      whileRecWP_le_wp_qWhile _ _ (t + 1) _
    have hexp1 : 𝔼[Δmid, whileRecWP (wp cBody) (stageGuard res n m) (t + 1)
          (wp cWrite (diagAssertion (ValidStageBasis n m k S (j.val + 1))))] ≤
        𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] := by
      rw [← wp_expectation_eq prog Δ, hprog_eq, wp_qSeq, wp_expectation_eq cInit Δ, wp_qSeq]
      exact expect_mono le_rfl hle_wp
    rw [← wp_expectation_eq cInit Δ] at hexp1
    have hproj_eq : ∀ σ, diagProj (ValidStageBasis n m k S j.val) *
        (wp cInit (whileRecWP (wp cBody) (stageGuard res n m) (t + 1)
          (wp cWrite (diagAssertion (ValidStageBasis n m k S (j.val + 1))))) σ).1.mat *
        diagProj (ValidStageBasis n m k S j.val) =
        ((1 - q ^ t : ℝ) : ℂ) • diagProj (ValidStageBasis n m k S j.val) := by
      intro σ
      rw [diagProj_wp_measureInit]
      have hg0 : stageGuard res n m (Store.subst σ res 0) := by
        simp [stageGuard, hasMarkedSlotNat_zero]
      exact diagProj_whileRecWP_stage res j K hScard hkN t (Store.subst σ res 0) hg0
    rw [expect_of_supportedOn hΔ hproj_eq] at hexp1
    exact hexp1
  have htend :
      Filter.Tendsto (fun t : ℕ ↦ (1 - q ^ t) * (Δ.trace : ℝ)) Filter.atTop
        (nhds (Δ.trace : ℝ)) := by
    have hp0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
    have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub hp0).mul
      (tendsto_const_nhds (x := (Δ.trace : ℝ)))
    simpa using h1
  have htrace_le1 : 𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] ≤ Δout.trace := by
    rw [← expect_top Δout]
    exact expect_mono le_rfl le_top
  have htrace_le2 : (Δout.trace : ℝ) ≤ Δ.trace :=
    NNReal.coe_le_coe.mpr ((interp prog).trace_toStateFun_le Δ)
  have hge_lim : (Δ.trace : ℝ) ≤ 𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] :=
    le_of_tendsto' htend hexp_ge
  have htrace_eq : Δout.trace = Δ.trace :=
    NNReal.coe_inj.mp (le_antisymm htrace_le2 (hge_lim.trans htrace_le1))
  have hexp_eq : 𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] = Δout.trace :=
    le_antisymm htrace_le1 (by rw [htrace_eq]; exact hge_lim)
  have hsupp_out : SupportedOn (ValidStageBasis n m k S (j.val + 1)) Δout :=
    supportedOn_of_expect_diagAssertion_eq_trace hexp_eq
  -- Part 3: Expected cost bound via `whileActiveWP`
  have hact_mass (t : ℕ) :
      stateMass (activeIter (stageGuard res n m) cBody t Δmid) =
        stateMass Δ * (ENNReal.ofReal q) ^ t := by
    rw [← ofReal_expect_whileActiveWP, ← wp_expectation_eq cInit Δ]
    have hproj_act : ∀ σ, diagProj (ValidStageBasis n m k S j.val) *
        (wp cInit (whileActiveWP (wp cBody) (stageGuard res n m) t) σ).1.mat *
        diagProj (ValidStageBasis n m k S j.val) =
        ((q ^ t : ℝ) : ℂ) • diagProj (ValidStageBasis n m k S j.val) := by
      intro σ
      rw [diagProj_wp_measureInit]
      have hg0 : stageGuard res n m (Store.subst σ res 0) := by
        simp [stageGuard, hasMarkedSlotNat_zero]
      have hact := diagProj_whileActiveWP_attemptBody (m := m) res j K hScard hkN t
        (Store.subst σ res 0)
      simpa [hg0, q] using hact
    rw [expect_of_supportedOn hΔ hproj_act, mul_comm, stateMass_eq_ofReal_trace,
      ENNReal.ofReal_mul Δ.trace_nonneg, ENNReal.ofReal_pow hq_nn]
  have hexp_iter : expectedIterations (stageGuard res n m) cBody Δmid =
      stateMass Δ * ENNReal.ofReal ((1 - q)⁻¹) := by
    rw [expectedIterations]
    simp_rw [hact_mass]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq_nn,
      ENNReal.ofReal_inv_of_pos h1mq_pos]
  have hcost : expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (((K : ℝ) + 1) / (1 - q)) := by
    let model : CostModel (2 ^ findAllQubits n m k) :=
      CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)
    rw [hprog_eq, expectedCost_qSeq, expectedCost_qSeq]
    have hc_init : expectedCost model cInit Δ = 0 := by
      simp [cInit, QProg.measureRegister, model]
    have hc_write : expectedCost model cWrite ((interp cLoop).toStateFun Δmid) = 0 := by
      have hcb := costBound_xorRegCircuit (isRealMatrix_parallelMarkingOracle (m := m) S)
        res (extractMarkedIdx n m) (memSlotReg n m k j) ((interp cLoop).toStateFun Δmid)
      simpa using hcb
    have hc_loop : expectedCost model cLoop Δmid ≤
        stateMass Δ * ENNReal.ofReal (((K : ℝ) + 1) / (1 - q)) := by
      have hbody := costBound_attemptBodyCircuit (Var := Var) res n m k j K S
      calc expectedCost model cLoop Δmid
          ≤ expectedIterations (stageGuard res n m) cBody Δmid *
              (((K : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) :=
            expectedCost_qWhile_le hbody _ Δmid
        _ = stateMass Δ * (ENNReal.ofReal ((1 - q)⁻¹) * ENNReal.ofReal ((K : ℝ) + 1)) := by
            rw [hexp_iter, mul_assoc]
            congr 2
            have hk_coe : (((K : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((K : ℝ) + 1) := by
              rw [← ENNReal.ofReal_coe_nnreal]
              push_cast
              rfl
            exact hk_coe
        _ = stateMass Δ * ENNReal.ofReal (((K : ℝ) + 1) / (1 - q)) := by
            congr 1
            rw [← ENNReal.ofReal_mul (inv_nonneg.2 h1mq_pos.le), inv_mul_eq_div]
    rw [hc_init, hc_write, zero_add, add_zero]
    exact hc_loop
  exact ⟨hsupp_out, htrace_eq, hcost⟩
/-- Per-stage oracle cost expression `(K + 1) / (1 - (1 - p_succ_set K n r) ^ m)`. -/
noncomputable def stageExpectedCost (iterFn : ℕ → ℕ → ℕ → ℕ) (m n r : ℕ) : ℝ :=
  ((iterFn m n r : ℝ) + 1) / (1 - (1 - p_succ_set (iterFn m n r) n r) ^ m)
theorem stagesRemCircuit_transition {Var : Type} [DecidableEq Var] (res : Var)
    (iterFn : ℕ → ℕ → ℕ → ℕ) {n m k : ℕ} (hm : 1 ≤ m) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hkN : k ≤ 2 ^ n)
    (hp_pos : ∀ r, 1 ≤ r → r ≤ k → 0 < p_succ_set (iterFn m n r) n r) :
    ∀ rem ≤ k, ∀ Δ : CQState (Store Var) (2 ^ findAllQubits n m k),
      SupportedOn (ValidStageBasis n m k S (k - rem)) Δ →
      let prog := (stagesRemCircuit res iterFn n m k rem).compile
        QProg.qAssign (parallelMarkingOracle m S)
      SupportedOn (ValidStageBasis n m k S k) ((interp prog).toStateFun Δ) ∧
        ((interp prog).toStateFun Δ).trace = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
          stateMass Δ *
            ENNReal.ofReal (∑ r ∈ Finset.Icc 1 rem, stageExpectedCost iterFn m n r) := by
  intro rem
  induction rem with
  | zero =>
      intro _ Δ hΔ
      have hempty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, ENNReal.ofReal_zero, mul_zero]
      refine ⟨hΔ, rfl, ?_⟩
      simp [stagesRemCircuit]
  | succ rem ih =>
      intro hrem Δ hΔ
      have hklt : k - (rem + 1) < k := by omega
      simp only [stagesRemCircuit, hklt, ↓reduceDIte, OracleDynamicCircuit.compile_seq,
        interp_qSeq, QMonad.Q.toStateFun_bind, expectedCost_qSeq]
      let j : Fin k := ⟨k - (rem + 1), hklt⟩
      have hj_rem : k - j.val = rem + 1 := by dsimp only [j]; omega
      have hsucc_eq : j.val + 1 = k - rem := by dsimp only [j]; omega
      have hp1 : 0 < p_succ_set (iterFn m n (rem + 1)) n (k - j.val) := by
        rw [hj_rem]
        exact hp_pos (rem + 1) (by omega) hrem
      obtain ⟨hsupp1, htr1, hcost1⟩ :=
        stage_transition res hm hScard hkN j (iterFn m n (rem + 1)) hp1 hΔ
      rw [hsucc_eq] at hsupp1
      set Δ₁ := (interp ((stageCircuit res n m k j (iterFn m n (rem + 1))).compile
        QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ
      obtain ⟨hsupp2, htr2, hcost2⟩ := ih (by omega) Δ₁ hsupp1
      refine ⟨hsupp2, htr2.trans htr1, ?_⟩
      have hmass1 : stateMass Δ₁ = stateMass Δ := by
        rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr1]
      have hc1_nn : 0 ≤ stageExpectedCost iterFn m n (rem + 1) := by
        unfold stageExpectedCost
        apply div_nonneg (by positivity)
        have hp_le := p_succ_set_le_one (iterFn m n (rem + 1)) n (rem + 1)
        have h1mp_lt : 1 - p_succ_set (iterFn m n (rem + 1)) n (rem + 1) < 1 := by
          linarith [hp_pos (rem + 1) (by omega) hrem]
        have hq_lt : (1 - p_succ_set (iterFn m n (rem + 1)) n (rem + 1)) ^ m < 1 :=
          pow_lt_one₀ (by linarith) h1mp_lt (by omega)
        linarith
      have hsum_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 rem, stageExpectedCost iterFn m n r := by
        refine Finset.sum_nonneg fun r hr ↦ ?_
        rw [Finset.mem_Icc] at hr
        unfold stageExpectedCost
        apply div_nonneg (by positivity)
        have hp_le := p_succ_set_le_one (iterFn m n r) n r
        have h1mp_lt : 1 - p_succ_set (iterFn m n r) n r < 1 := by
          linarith [hp_pos r hr.1 (hr.2.trans (by omega))]
        have hq_lt : (1 - p_succ_set (iterFn m n r) n r) ^ m < 1 :=
          pow_lt_one₀ (by linarith) h1mp_lt (by omega)
        linarith
      rw [hj_rem] at hcost1
      calc _ ≤ stateMass Δ * ENNReal.ofReal (stageExpectedCost iterFn m n (rem + 1)) +
              stateMass Δ₁ * ENNReal.ofReal
                (∑ r ∈ Finset.Icc 1 rem, stageExpectedCost iterFn m n r) :=
            add_le_add hcost1 hcost2
        _ = stateMass Δ *
              (ENNReal.ofReal (∑ r ∈ Finset.Icc 1 rem, stageExpectedCost iterFn m n r) +
                ENNReal.ofReal (stageExpectedCost iterFn m n (rem + 1))) := by
            rw [hmass1, mul_add, add_comm]
        _ = stateMass Δ * ENNReal.ofReal
              (∑ r ∈ Finset.Icc 1 (rem + 1), stageExpectedCost iterFn m n r) := by
            rw [← ENNReal.ofReal_add hsum_nn hc1_nn,
              Finset.sum_Icc_succ_top (by omega : 1 ≤ rem + 1)]
/- ## Parametric `findAllCircuit` total correctness and cost bound -/

theorem diagProj_wp_finalReadout {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hScard : S.card = k) (σ : Store Var) :
    diagProj (ValidStageBasis n m k S k) *
        (wp (QProg.measureRegister res (memAllReg n m k))
          (liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)) σ).1.mat *
        diagProj (ValidStageBasis n m k S k) =
      ((1 : ℝ) : ℂ) • diagProj (ValidStageBasis n m k S k) := by
  have hproj_w (w : Fin (2 ^ (n * k))) :
      (memAllReg n m k).basisOutcomeProjector w =
        diagProj (fun z ↦ (memAllReg n m k).extractIndex z = w) :=
    (memAllReg n m k).basisOutcomeProjector_eq_diagonal w
  ext a b
  rw [diagProj_mul_mul_diagProj_apply, Complex.ofReal_one, one_smul]
  by_cases hvalid : ValidStageBasis n m k S k a ∧ ValidStageBasis n m k S k b
  · obtain ⟨ha, hb⟩ := hvalid
    simp only [ha, hb, and_self, ↓reduceIte]
    rw [wp_measureRegister_coe_ax, HermitianMat.mat_finset_sum, Matrix.sum_apply]
    have hterm : ∀ w ∈ (Finset.univ : Finset (Fin (2 ^ (n * k)))),
        ((HermitianMat.conj ((memAllReg n m k).basisOutcomeProjector w)ᴴ
          ((liftPureProp (d := 2 ^ findAllQubits n m k)
              (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
              (Store.subst σ res ↑w.val)).1)).mat) a b =
        if w = (memAllReg n m k).extractIndex a ∧ a = b then (1 : ℂ) else 0 := by
      intro w _
      rw [HermitianMat.conj_apply_mat]
      simp only [QRegister.basisOutcomeProjector_conjTranspose]
      rw [hproj_w, diagProj_mul_mul_diagProj_apply]
      by_cases hw : (memAllReg n m k).extractIndex a = w
      · subst hw
        have hdec := decodeTargetsLocal_memAllReg_eq hScard ha
        have hprop : (liftPureProp (d := 2 ^ findAllQubits n m k)
            (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
            (Store.subst σ res ↑((memAllReg n m k).extractIndex a).val)).1.mat = 1 := by
          simp [liftPureProp, hdec]
        rw [hprop]
        by_cases hab : a = b
        · subst hab; simp
        · simp [hab]
      · simp [hw, Ne.symm hw]
    rw [Finset.sum_congr rfl hterm]
    by_cases hab : a = b
    · subst hab
      simp [diagProj, ha]
    · simp [hab, diagProj]
  · rw [diagProj, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      have hna : ¬ ValidStageBasis n m k S k a := fun ha ↦ hvalid ⟨ha, ha⟩
      simp [hna]
    · simp [hvalid, hab]
theorem findAllProgram_correctness {Var : Type} [DecidableEq Var] (res : Var)
    (iterFn : ℕ → ℕ → ℕ → ℕ) {n m k : ℕ} (hm : 1 ≤ m) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hkN : k ≤ 2 ^ n)
    (hp_pos : ∀ r, 1 ≤ r → r ≤ k → 0 < p_succ_set (iterFn m n r) n r) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) ⦄
    (QProg.qSet ;; (findAllCircuit res iterFn n m k).compile QProg.qAssign
      (parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄ := by
  intro Δ
  rw [expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet]
  simp only [findAllCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_measure, interp_qSeq, QMonad.Q.toStateFun_bind]
  have h0 : SupportedOn (ValidStageBasis n m k S (k - k)) Δ.qSet := by
    rw [Nat.sub_self]
    exact supportedOn_qSet (validStageBasis_zero n m k S) Δ
  obtain ⟨hsupp_k, htr_k, _⟩ :=
    stagesRemCircuit_transition res iterFn hm hScard hkN hp_pos k le_rfl Δ.qSet h0
  set Δ_k := (interp ((stagesRemCircuit res iterFn n m k k).compile
    QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ.qSet
  rw [← wp_expectation_eq (QProg.measureRegister res (memAllReg n m k)) Δ_k,
    expect_of_supportedOn hsupp_k (diagProj_wp_finalReadout res hScard),
    one_mul, htr_k, CQState.trace_qSet]
theorem findAllProgram_costBound {Var : Type} [DecidableEq Var] (res : Var)
    (iterFn : ℕ → ℕ → ℕ → ℕ) {n m k : ℕ} (hm : 1 ≤ m) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (hkN : k ≤ 2 ^ n)
    (hp_pos : ∀ r, 1 ≤ r → r ≤ k → 0 < p_succ_set (iterFn m n r) n r)
    {B : ℝ≥0} (hB : ∑ r ∈ Finset.Icc 1 k, stageExpectedCost iterFn m n r ≤ B) :
    CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (QProg.qSet ;; (findAllCircuit (Var := Var) res iterFn n m k).compile QProg.qAssign
        (parallelMarkingOracle m S))
      B := by
  intro Δ
  let model : CostModel (2 ^ findAllQubits n m k) :=
    CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)
  rw [expectedCost_qSeq, interp_qSet, QMonad.Q.toStateFun_qSet]
  have hqset : expectedCost model QProg.qSet Δ = 0 := by
    simp [model]
  rw [hqset, zero_add]
  simp only [findAllCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_measure, expectedCost_qSeq]
  have hmeas : expectedCost model (QProg.measureRegister res (memAllReg n m k))
      ((interp ((stagesRemCircuit res iterFn n m k k).compile
        QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ.qSet) = 0 := by
    simp [QProg.measureRegister, model]
  rw [hmeas, add_zero]
  have h0 : SupportedOn (ValidStageBasis n m k S (k - k)) Δ.qSet := by
    rw [Nat.sub_self]
    exact supportedOn_qSet (validStageBasis_zero n m k S) Δ
  obtain ⟨_, _, hcost⟩ :=
    stagesRemCircuit_transition res iterFn hm hScard hkN hp_pos k le_rfl Δ.qSet h0
  have hmass : stateMass Δ.qSet = stateMass Δ := by
    rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, CQState.trace_qSet]
  rw [hmass] at hcost
  refine hcost.trans ?_
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hB
end QuantumComputation.Specs.GroverFindAll
end
end Sec_StageLoop
