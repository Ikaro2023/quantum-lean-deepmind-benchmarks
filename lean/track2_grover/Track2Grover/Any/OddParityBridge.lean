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

/-!
# Parallel Marking-Oracle to Odd-Parity Phase-Oracle Bridge

Shared register geometry, flag-basis conjugation, odd-parity target-tuple subset density, and
zero-cost single-variable measurement and lookup combinators for parallel Grover search.

All circuit and QHL helpers are polymorphic in `{Var : Type} [DecidableEq Var]` and reuse
`phaseTag`, `groverSetMarkingOracle`, and `groverParallelMarkingOracle` from
`QuantumComputationSpecs.Algorithms.Grover.Solution.Defs`.
-/

section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

@[expose] public section

namespace QuantumComputation.Specs.GroverSolution

open Operator ResourceCounting Real
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val DisjointWires tensorState whole)
open Matrix (star_eq_conjTranspose conjTranspose_apply mulVec_single_one conjTranspose_mul
  mulVec_diagonal mulVec_mulVec mul_diagonal col_apply diagonal)
open Complex (ofReal_sum normSq)
open Finset (sum_add_distrib sum_sub_distrib sum_eq_zero sum_ite_mem prod_eq_one univ_inter
  sum_const mul_sum)
open List (mem_finRange prod_cons finRange map_cons)
open Fintype (sum_eq_single sum_prod_type)
open Equiv (Perm swap)
open Pi (single)
open scoped Matrix NNReal ENNReal ComplexOrder MatrixOrder QProg.Notation

/-- Shorthand for a query-model dynamic circuit on `Q` qubits calling a `W`-qubit oracle. -/
abbrev OracleCirc (Var : Type) (Q W : ℕ) :=
  OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q W

/-! ## Slot, Full-Oracle, and Address Register Geometry -/

/-- The `j`-th `(n + 1)`-qubit marking-oracle slot inside an `(m * (n + 1))`-qubit register:
wire `0` of the slot is marker bit `b_j` and wires `1..n` hold address `x_j`. -/
abbrev slotReg (n m : ℕ) (j : Fin m) : QRegister (n + 1) (m * (n + 1)) :=
  QRegister.block (j.val * (n + 1)) (n + 1) (by nlinarith [j.isLt])

theorem slotReg_apply (n m : ℕ) (j : Fin m) (w : Fin (n + 1)) :
    slotReg n m j w = finProdFinEquiv (j, w) := by
  ext
  simp only [slotReg, QRegister.block_apply_val, finProdFinEquiv_apply_val]
  ring

theorem slotReg_disjointWires {n m : ℕ} {a b : Fin m} (hab : a ≠ b) :
    (slotReg n m a).DisjointWires (slotReg n m b) := by
  refine QRegister.disjoint_iff.mpr fun w₁ w₂ heq ↦ ?_
  rw [slotReg_apply, slotReg_apply] at heq
  exact hab (congrArg Prod.fst (finProdFinEquiv.injective heq))

/-- Identity-ordered `((n + 1) * m)`-wire view of all `m * (n + 1)` slot wires for `.oracle`. -/
abbrev fullReg (n m : ℕ) : QRegister ((n + 1) * m) (m * (n + 1)) :=
  QRegister.block 0 ((n + 1) * m) (by linarith)

theorem fullReg_embedUnitary_groverParallelMarkingOracle {n m : ℕ}
    (S : Finset (Fin (2 ^ n))) :
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 =
      ((finRange m).map fun i ↦ (slotReg n m i).embedMatrix (groverSetMarkingOracle S).1).prod := by
  have hp (l : List (Unitary (2 ^ ((n + 1) * m)))) :
      (fullReg n m).embedUnitary l.prod = (l.map (fullReg n m).embedUnitary).prod := by
    induction l <;> simp [prod_cons, *]
  unfold groverParallelMarkingOracle
  rw [List.ofFn_eq_map, hp, Submonoid.coe_list_prod, List.map_map, List.map_map]
  refine congrArg List.prod (congrArg (List.map · (finRange m)) (funext fun i ↦ ?_))
  simp only [Function.comp_apply, ← QRegister.embedUnitary_compose, embedUnitary_val]
  refine congrArg (QRegister.embedMatrix · _) ?_
  ext
  simp [fullReg, slotReg]

theorem splitBasisEquiv_fst_mul_two_add_snd (n : ℕ) (u : Fin (2 ^ (n + 1))) :
    (splitBasisEquiv n 1 u).1.val * 2 + (splitBasisEquiv n 1 u).2.val = u.val := by
  simp only [splitBasisEquiv, Equiv.trans_apply, finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat,
    finCongr_apply, Fin.val_cast, pow_one]
  omega

/-- Joint `(m * n)`-qubit address subregister selecting wires `1..n` across all `m` slots,
leaving the `m` marker wires `slotReg n m j 0` as its physical-wire environment. -/
abbrev addrReg (n m : ℕ) : QRegister (m * n) (m * (n + 1)) :=
  ⟨finProdFinEquiv.symm.toEmbedding.trans <| (Function.Embedding.prodMap (.refl _)
    ((Fin.natAddEmb 1).trans (Fin.castLEEmb (by omega)))).trans finProdFinEquiv.toEmbedding⟩

/-- Equivalence between joint `(m * n)`-qubit computational-basis indices and `m`-tuples of
`n`-bit domain addresses. -/
abbrev addrEquiv (n m : ℕ) : Fin (2 ^ (m * n)) ≃ (Fin m → Fin (2 ^ n)) :=
  (basisBits (m * n)).trans <| ((Equiv.arrowCongr finProdFinEquiv (Equiv.refl
    (ZMod 2))).symm).trans <| (Equiv.curry (Fin m) (Fin n) (ZMod 2)).trans <| Equiv.piCongrRight
    (fun _ ↦ (basisBits n).symm)

/-- Address component `x_j ∈ Fin (2 ^ n)` of slot `j` in global basis index `z`. -/
abbrev slotAddr (n m : ℕ) (z : Fin (2 ^ (m * (n + 1)))) (j : Fin m) : Fin (2 ^ n) :=
  (splitBasisEquiv n 1 ((slotReg n m j).extractIndex z)).1

/-- Marker bit `b_j ∈ Fin 2` of slot `j` in global basis index `z`. -/
abbrev slotFlag (n m : ℕ) (z : Fin (2 ^ (m * (n + 1)))) (j : Fin m) : Fin (2 ^ 1) :=
  (splitBasisEquiv n 1 ((slotReg n m j).extractIndex z)).2

theorem addrReg_apply (n m : ℕ) (j : Fin m) (r : Fin n) :
    addrReg n m (finProdFinEquiv (j, r)) = slotReg n m j r.succ := by
  rw [slotReg_apply]
  dsimp [addrReg]
  rw [Equiv.symm_apply_apply]
  congr 1
  ext <;> simp [Nat.add_comm]

theorem addrEquiv_extractIndex (n m : ℕ) (z : Fin (2 ^ (m * (n + 1)))) (j : Fin m) :
    addrEquiv n m ((addrReg n m).extractIndex z) j = slotAddr n m z j := by
  apply (basisBits n).injective
  funext r
  have hL (u : Fin (2 ^ (m * n))) :
      basisBits n (addrEquiv n m u j) r = basisBits (m * n) u (finProdFinEquiv (j, r)) := by
    simp [addrEquiv]
  set u := (slotReg n m j).extractIndex z
  rw [hL, basisBits_extractIndex, addrReg_apply]
  change basisBits (m * (n + 1)) z (slotReg n m j r.succ) = basisBits n (splitBasisEquiv n 1 u).1 r
  rw [← basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod, Fin.val_succ,
    pow_succ' 2 r.val, ← Nat.div_div_eq_div_mul _ 2 (2 ^ r.val)]
  have hadd := splitBasisEquiv_fst_mul_two_add_snd n u
  have hlt := (splitBasisEquiv n 1 u).2.isLt
  exact congrArg Nat.cast (congrArg (fun x ↦ (x / 2 ^ r.val) % 2) (by omega))

theorem basisBits_slotFlag (n m : ℕ) (z : Fin (2 ^ (m * (n + 1)))) (j : Fin m) :
    basisBits 1 (slotFlag n m z j) 0 =
      ((addrReg n m).basisSplitEquiv z).2 ⟨slotReg n m j 0, by
        rintro ⟨u, hu⟩
        obtain ⟨⟨j', r⟩, rfl⟩ := finProdFinEquiv.surjective u
        have hu' : addrReg n m (finProdFinEquiv (j', r)) = slotReg n m j 0 := hu
        rw [addrReg_apply, slotReg_apply, slotReg_apply] at hu'
        exact Fin.succ_ne_zero r (congrArg Prod.snd (finProdFinEquiv.injective hu'))⟩ := by
  unfold slotFlag
  rw [QRegister.basisSplitEquiv_apply_snd, ← basisBits_extractIndex, basisBits_eq_div_mod,
    basisBits_eq_div_mod]
  congr 1
  have hadd := splitBasisEquiv_fst_mul_two_add_snd n ((slotReg n m j).extractIndex z)
  have hlt := (splitBasisEquiv n 1 ((slotReg n m j).extractIndex z)).2.isLt
  simp only [Fin.val_zero, pow_zero, Nat.div_one]
  omega

theorem slotFlag_eq_zero {n m : ℕ} (z : Fin (2 ^ (m * (n + 1))))
    (hE : ((addrReg n m).basisSplitEquiv z).2 = 0) (j : Fin m) :
    slotFlag n m z j = 0 := by
  rw [(by decide : ∀ b : Fin (2 ^ 1), b = 0 ↔ basisBits 1 b 0 = 0),
    basisBits_slotFlag, hE, Pi.zero_apply]

theorem slotFlag_eq_one {n m : ℕ} (z : Fin (2 ^ (m * (n + 1))))
    (hE : ((addrReg n m).basisSplitEquiv z).2 = 1) (j : Fin m) :
    slotFlag n m z j = 1 := by
  rw [(by decide : ∀ b : Fin (2 ^ 1), b = 1 ↔ basisBits 1 b 0 = 1),
    basisBits_slotFlag, hE, Pi.one_apply]

/-! ## Flag-Basis Conjugation and Single-Slot Phase Oracle -/

/-- Basis permutation `(x, b) ↦ (x, b ⊕ [x ∈ S])` underlying `groverSetMarkingOracle S`. -/
abbrev markPerm {n : ℕ} (S : Finset (Fin (2 ^ n))) : Perm (Fin (2 ^ (n + 1))) :=
  tableAddPerm (fun x : Fin (2 ^ n) ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)

theorem splitBasisEquiv_markPerm {n : ℕ} (S : Finset (Fin (2 ^ n))) (v : Fin (2 ^ (n + 1))) :
    splitBasisEquiv n 1 (markPerm S v) =
      ((splitBasisEquiv n 1 v).1,
        (splitBasisEquiv n 1 v).2 + if (splitBasisEquiv n 1 v).1 ∈ S then 1 else 0) := by
  simp [markPerm, tableAddPerm, addRightShear]

/-- Conjugated single-slot diagonal entries: `-1` when `x ∈ S` and `b = 0`, and `+1` otherwise
(in particular, `+1` for every `x` whenever `b = 1`). -/
abbrev slotDiag (n : ℕ) (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (n + 1))) : ℂ :=
  if (splitBasisEquiv n 1 u).1 ∈ S ∧ (splitBasisEquiv n 1 u).2 = 0 then (-1 : ℂ) else 1

/-- Symmetric sign kernel `[[1, -1], [-1, -1]]` mapping `|0⟩ ↦ |−⟩` and `|1⟩ ↦ -|+⟩`. -/
abbrev flagSign (a b : Fin (2 ^ 1)) : ℤ :=
  if a = 0 ∧ b = 0 then 1 else -1

/-- Single-slot involutive real unitary acting on the marker wire as `(1 / √2) * flagSign`
(`|0⟩ ↦ |−⟩`, `|1⟩ ↦ -|+⟩`) while preserving the `n`-bit address. -/
noncomputable abbrev flagWMat (n : ℕ) : Operator (2 ^ (n + 1)) :=
  fun u v ↦
    if (splitBasisEquiv n 1 u).1 = (splitBasisEquiv n 1 v).1 then
      (1 / √2 : ℂ) * (flagSign (splitBasisEquiv n 1 u).2 (splitBasisEquiv n 1 v).2 : ℂ)
    else 0

theorem flagW_conj (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    flagWMat n * (groverSetMarkingOracle S).1 * flagWMat n = diagonal (slotDiag n S) := by
  unfold groverSetMarkingOracle
  ext u v
  rw [Matrix.mul_apply, ← (splitBasisEquiv n 1).symm.sum_comp, sum_prod_type]
  have hm1 (k : Fin (2 ^ (n + 1))) :
      (flagWMat n * (permutationUnitary (markPerm S)).1) u k = flagWMat n u (markPerm S k) := by
    rw [Matrix.mul_apply,
      sum_eq_single (markPerm S k) (fun w hw ↦ by
        rw [permutationUnitary_apply, ite_eq_right hw, mul_zero]),
      permutationUnitary_apply, ite_eq_left rfl, mul_one]
  simp_rw [hm1]
  dsimp only [flagWMat]
  simp_rw [splitBasisEquiv_markPerm, Equiv.apply_symm_apply]
  set xu := (splitBasisEquiv n 1 u).1
  set bu := (splitBasisEquiv n 1 u).2
  set xv := (splitBasisEquiv n 1 v).1
  set bv := (splitBasisEquiv n 1 v).2
  set δ : Fin (2 ^ 1) := if xu ∈ S then 1 else 0
  rw [sum_eq_single xu (fun x hx ↦ sum_eq_zero fun b _ ↦ by
    rw [ite_eq_right (Ne.symm hx), zero_mul])]
  open Classical in
  refine if h1 : xu = xv then ?_ else (by
    have huv : u ≠ v := fun huv ↦ h1 (congrArg (fun z ↦ (splitBasisEquiv n 1 z).1) huv)
    rw [Matrix.diagonal_apply_ne _ huv]
    exact sum_eq_zero fun b _ ↦ by rw [ite_eq_right h1, mul_zero])
  have hsm :
      (∑ b : Fin (2 ^ 1),
        (if xu = xu then
          (1 / √2 : ℂ) * (flagSign bu (b + if xu ∈ S then 1 else 0) : ℂ)
         else 0) *
        (if xu = xv then (1 / √2 : ℂ) * (flagSign b bv : ℂ) else 0)) =
      ((1 / √2 : ℂ) * (1 / √2 : ℂ)) *
        ((∑ b : Fin (2 ^ 1), flagSign bu (b + δ) * flagSign b bv : ℤ) : ℂ) := by
    rw [Int.cast_sum, mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [ite_eq_left rfl, ite_eq_left h1, Int.cast_mul]
    ring
  have hPδ : (xu ∈ S ∧ bu = 0) ↔ (δ = 1 ∧ bu = 0) := by
    by_cases hS : xu ∈ S <;> simp [δ, hS]
  have hfs : ∀ δ b₁ b₂ : Fin (2 ^ 1),
      (∑ k : Fin (2 ^ 1), flagSign b₁ (k + δ) * flagSign k b₂) =
        if b₁ = b₂ then (if δ = 1 ∧ b₁ = 0 then -2 else 2) else 0 := by
    decide
  rw [hsm, hfs, complex_one_div_sqrt_mul_self 2 (by norm_num)]
  open Classical in
  refine if hb : bu = bv then (by
    have huv : u = v := (splitBasisEquiv n 1).injective (Prod.ext h1 hb)
    rw [ite_eq_left hb, ← huv, Matrix.diagonal_apply_eq]
    change _ = if xu ∈ S ∧ bu = 0 then (-1 : ℂ) else 1
    rw [if_congr hPδ rfl rfl]
    by_cases hδ : δ = 1 ∧ bu = 0 <;> simp only [hδ, ↓reduceIte] <;> norm_num)
  else (by
    have huv : u ≠ v := fun huv ↦ hb (congrArg (fun z ↦ (splitBasisEquiv n 1 z).2) huv)
    rw [ite_eq_right hb, Matrix.diagonal_apply_ne _ huv]
    norm_num)

/-- Product of `flagWMat n` across all `m` parallel oracle slots. -/
noncomputable abbrev flagConj (n m : ℕ) : Unitary (2 ^ (m * (n + 1))) := by
  refine ((finRange m).map fun i ↦ (slotReg n m i).embedUnitary ⟨flagWMat n, ?_⟩).prod
  have h0 := flagW_conj n ∅
  have hO : (groverSetMarkingOracle (∅ : Finset (Fin (2 ^ n)))).1 = 1 := by
    ext i j
    rw [groverSetMarkingOracle, permutationUnitary_apply,
      show markPerm (∅ : Finset (Fin (2 ^ n))) j = j from
        (splitBasisEquiv n 1).injective (by simp),
      Matrix.one_apply]
  have hcj : (flagWMat n)ᴴ = flagWMat n := by
    ext u v
    dsimp only [conjTranspose_apply, flagWMat]
    open Classical in
    refine if h : (splitBasisEquiv n 1 u).1 = (splitBasisEquiv n 1 v).1 then (by
      rw [ite_eq_left h.symm, ite_eq_left h,
        (by decide : ∀ x y : Fin (2 ^ 1), flagSign x y = flagSign y x)]
      generalize flagSign (splitBasisEquiv n 1 u).2 (splitBasisEquiv n 1 v).2 = s
      simp)
    else (by rw [ite_eq_right (Ne.symm h), ite_eq_right h, star_zero])
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, hcj]
  rw [hO, mul_one, show diagonal (slotDiag n ∅) = 1 by
    ext i j
    simp [slotDiag, Matrix.diagonal_apply, Matrix.one_apply]] at h0
  exact h0

/-! ## Odd-Parity Target-Tuple Subset, Density, and Phase Step -/

/-- Address `m`-tuples `(x_0, ..., x_{m - 1})` containing an odd number of elements of `S`. -/
abbrev oddSet (n m : ℕ) (S : Finset (Fin (2 ^ n))) : Finset (Fin (2 ^ (m * n))) :=
  Finset.univ.filter fun u ↦ (∏ j : Fin m, if addrEquiv n m u j ∈ S then (-1 : ℤ) else 1) = -1

theorem prod_ite_neg_one_or_one {α : Type*} (s : Finset α)
    (P : α → Prop) [DecidablePred P] :
    (∏ j ∈ s, if P j then (-1 : ℤ) else 1) = -1 ∨
      (∏ j ∈ s, if P j then (-1 : ℤ) else 1) = 1 := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact .inr rfl
  | cons a s _ ih =>
    rw [Finset.prod_cons]
    rcases ih with h | h <;> by_cases hP : P a <;> simp [h, hP]

/-- Exact fraction `(1 - (1 - 2k / 2^n)^m) / 2` of `m`-tuples in `(Fin (2 ^ n))^m` hitting a
`k`-element target set an odd number of times. -/
noncomputable def oddFrac (n m k : ℕ) : ℝ :=
  (1 - (1 - 2 * (k : ℝ) / (2 ^ n : ℝ)) ^ m) / 2

theorem card_oddSet_div_two_pow (n m : ℕ) (S : Finset (Fin (2 ^ n))) :
    ((oddSet n m S).card : ℝ) / (2 ^ (m * n) : ℝ) = oddFrac n m S.card := by
  let g (x : Fin (2 ^ n)) : ℝ := if x ∈ S then -1 else 1
  have htm (u : Fin (2 ^ (m * n))) :
      (if u ∈ oddSet n m S then (2 : ℝ) else 0) = 1 - ∏ j : Fin m, g (addrEquiv n m u j) := by
    simp_rw [show ∀ x, g x = ((if x ∈ S then (-1 : ℤ) else 1 : ℤ) : ℝ) from fun _ ↦ by
      dsimp only [g]
      split_ifs <;> norm_num, ← Int.cast_prod]
    simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases prod_ite_neg_one_or_one Finset.univ
      (fun j : Fin m ↦ addrEquiv n m u j ∈ S) with h | h <;> rw [h] <;> norm_num
  have hce : 2 * ((oddSet n m S).card : ℝ) =
      (2 ^ (m * n) : ℝ) - ((2 ^ n : ℝ) - 2 * (S.card : ℝ)) ^ m := by
    rw [show 2 * ((oddSet n m S).card : ℝ) =
        ∑ u : Fin (2 ^ (m * n)), if u ∈ oddSet n m S then (2 : ℝ) else 0 by
      rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_comm]]
    simp_rw [htm]
    rw [sum_sub_distrib,
      (addrEquiv n m).sum_comp (fun f : Fin m → Fin (2 ^ n) ↦ ∏ j, g (f j)),
      ← Fintype.sum_pow g m,
      show ∑ x : Fin (2 ^ n), g x = (2 ^ n : ℝ) - 2 * (S.card : ℝ) by
        simp_rw [show ∀ x, g x = 1 - if x ∈ S then (2 : ℝ) else 0 from fun _ ↦ by
          dsimp only [g]
          split_ifs <;> norm_num]
        rw [sum_sub_distrib]
        simp [sum_ite_mem, univ_inter, mul_comm]]
    simp
  unfold oddFrac
  rw [div_eq_iff (by positivity)]
  linarith [hce, show ((2 ^ n : ℝ) - 2 * (S.card : ℝ)) ^ m =
      (1 - 2 * (S.card : ℝ) / (2 ^ n : ℝ)) ^ m * (2 ^ (m * n) : ℝ) by
    rw [show (2 ^ (m * n) : ℝ) = (2 ^ n : ℝ) ^ m by rw [mul_comm, pow_mul], ← mul_pow]
    congr 1
    field_simp]

/-- Diagonal phase-flip operator on `2 ^ q` basis states for marked subset `M`. -/
abbrev oracleMat {q : ℕ} (M : Finset (Fin (2 ^ q))) : Operator (2 ^ q) :=
  diagonal fun u ↦ if u ∈ M then -1 else 1

/-- Full `(m * (n + 1))`-qubit diagonal matrix produced by conjugating
`groverParallelMarkingOracle m S` with `flagConj n m`. -/
noncomputable def sDiagM (n m : ℕ) (S : Finset (Fin (2 ^ n))) : Operator (2 ^ (m * (n + 1))) :=
  diagonal fun z ↦ ∏ j : Fin m, slotDiag n S ((slotReg n m j).extractIndex z)

theorem flagConj_mul_embed_mul_flagConj {n m : ℕ} (S : Finset (Fin (2 ^ n))) :
    (flagConj n m).1 * ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 *
      (flagConj n m).1 = sDiagM n m S := by
  dsimp only [flagConj]
  rw [fullReg_embedUnitary_groverParallelMarkingOracle, Submonoid.coe_list_prod, List.map_map]
  let emb (B : Operator (2 ^ (n + 1))) (l : List (Fin m)) :=
    (l.map fun i ↦ (slotReg n m i).embedMatrix B).prod
  have epc {i : Fin m} {l : List (Fin m)} (hi : i ∉ l) (B₁ B₂ : Operator (2 ^ (n + 1))) :
      (slotReg n m i).embedMatrix B₁ * emb B₂ l = emb B₂ l * (slotReg n m i).embedMatrix B₁ := by
    induction l with
    | nil => simp [emb]
    | cons j l ih =>
      simp only [List.mem_cons, not_or] at hi
      dsimp only [emb] at *
      simp only [map_cons, prod_cons]
      rw [← mul_assoc, QRegister.embedMatrix_comm_of_disjoint _ _ (slotReg_disjointWires hi.1),
        mul_assoc, ih hi.2, ← mul_assoc]
  have epm {l : List (Fin m)} (hl : l.Nodup) (B₁ B₂ : Operator (2 ^ (n + 1))) :
      emb B₁ l * emb B₂ l = emb (B₁ * B₂) l := by
    induction l with
    | nil => simp [emb]
    | cons i l ih =>
      rcases List.nodup_cons.mp hl with ⟨hil, hl'⟩
      dsimp only [emb] at *
      simp only [map_cons, prod_cons]
      rw [mul_assoc, ← mul_assoc (l.map _).prod, ← epc hil B₂ B₁, mul_assoc,
        ← mul_assoc ((slotReg n m i).embedMatrix B₁), ← QRegister.embedMatrix_mul, ih hl']
  have epd (l : List (Fin m)) :
      emb (diagonal (slotDiag n S)) l =
        diagonal fun z ↦ (l.map fun i ↦ slotDiag n S ((slotReg n m i).extractIndex z)).prod := by
    induction l with
    | nil => simp [emb, Matrix.diagonal_one]
    | cons i l ih =>
      dsimp only [emb] at *
      simp only [map_cons, prod_cons]
      rw [QRegister.embedMatrix_diagonal, ih, Matrix.diagonal_mul_diagonal]
  have hnd := List.nodup_finRange m
  change emb (flagWMat n) (finRange m) * emb (groverSetMarkingOracle S).1 (finRange m) *
    emb (flagWMat n) (finRange m) = _
  rw [epm hnd, epm hnd, flagW_conj n S, epd, sDiagM]
  exact congrArg diagonal (funext fun _ ↦ (Fin.prod_univ_def _).symm)

/-- Single parallel-oracle call conjugated on both sides by `phaseTag (flagConj n m)`. -/
noncomputable def phaseStep {Var : Type} (n m : ℕ) :
    OracleCirc Var (m * (n + 1)) ((n + 1) * m) :=
  .seq (.step (phaseTag (flagConj n m)))
    (.seq (.oracle (fullReg n m)) (.step (phaseTag (flagConj n m))))

theorem wp_phaseStep {Var : Type} [DecidableEq Var] {n m : ℕ} (S : Finset (Fin (2 ^ n)))
    (M : Operator (2 ^ (m * (n + 1))))
    (Φ : CQAssertion (Store Var) (2 ^ (m * (n + 1)))) (hΦ : ∀ τ, (Φ τ).1.1 = M) (σ : Store Var) :
    ((wp ((phaseStep n m).compile qAssign (groverParallelMarkingOracle m S)) Φ) σ).1.1 =
      (sDiagM n m S)ᴴ * M * sDiagM n m S := by
  unfold phaseStep
  dsimp only [compile]
  set A := flagConj n m
  set Of := (fullReg n m).embedUnitary (groverParallelMarkingOracle m S)
  simp only [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, hΦ,
    show A.1ᴴ * (Of.1ᴴ * (A.1ᴴ * M * A.1) * Of.1) * A.1 =
      (A.1 * Of.1 * A.1)ᴴ * M * (A.1 * Of.1 * A.1) by
      simp only [conjTranspose_mul, Matrix.mul_assoc]]
  rw [flagConj_mul_embed_mul_flagConj]

theorem costBound_phaseStep {Var : Type} [DecidableEq Var] {n m : ℕ}
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((phaseStep n m).compile qAssign (groverParallelMarkingOracle m S)) 1 := by
  unfold phaseStep
  dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have htag := costBound_qAssign_phaseTag (Var := Var) hor (flagConj n m)
  have hcall :
      CostBound (Var := Var)
        (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (.qAssign ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S))) 1 := by
    simpa using
      CostBound.qAssign (Var := Var)
        (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S))
  simpa using htag.seq (hcall.seq htag)

theorem diagonal_mulVec_tensorState {n m : ℕ}
    (d : Fin (2 ^ (m * (n + 1))) → ℂ) (c : Fin (2 ^ (m * n)) → ℂ)
    (v : Fin (2 ^ (m * n)) → ℂ) (e : (addrReg n m).Environment → ZMod 2)
    (hd : ∀ z, ((addrReg n m).basisSplitEquiv z).2 = e → d z = c ((addrReg n m).extractIndex z)) :
    diagonal d *ᵥ (addrReg n m).tensorState v (single e 1) =
      (addrReg n m).tensorState (fun u ↦ c u * v u) (single e 1) := by
  funext z
  rw [mulVec_diagonal]
  dsimp only [tensorState]
  by_cases h : ((addrReg n m).basisSplitEquiv z).2 = e
  · rw [hd z h, h, Pi.single_eq_same, mul_one, mul_one]
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero, mul_zero]

theorem sDiagM_mulVec_tensorState_zero {n m : ℕ} (S : Finset (Fin (2 ^ n)))
    (v : Fin (2 ^ (m * n)) → ℂ) :
    sDiagM n m S *ᵥ (addrReg n m).tensorState v (single 0 1) =
      (addrReg n m).tensorState (oracleMat (oddSet n m S) *ᵥ v) (single 0 1) := by
  rw [sDiagM, diagonal_mulVec_tensorState _ (fun u ↦ if u ∈ oddSet n m S then -1 else 1) v _
    fun z hE ↦ ?_]
  · congr 1
    funext u
    rw [oracleMat, mulVec_diagonal]
  · have hf (j : Fin m) :
        slotDiag n S ((slotReg n m j).extractIndex z) =
          ((if addrEquiv n m ((addrReg n m).extractIndex z) j ∈ S then
              (-1 : ℤ)
            else 1 : ℤ) : ℂ) := by
      unfold slotDiag
      rw [show (splitBasisEquiv n 1 ((slotReg n m j).extractIndex z)).1 =
            addrEquiv n m ((addrReg n m).extractIndex z) j from
          (addrEquiv_extractIndex n m z j).symm,
        show (splitBasisEquiv n 1 ((slotReg n m j).extractIndex z)).2 = 0 from
          slotFlag_eq_zero z hE j]
      split_ifs <;> simp_all
    simp_rw [hf, ← Int.cast_prod]
    simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases prod_ite_neg_one_or_one Finset.univ
      (fun j : Fin m ↦ addrEquiv n m ((addrReg n m).extractIndex z) j ∈ S) with h | h <;>
      rw [h] <;> norm_num

theorem sDiagM_mulVec_tensorState_one {n m : ℕ} (S : Finset (Fin (2 ^ n)))
    (v : Fin (2 ^ (m * n)) → ℂ) :
    sDiagM n m S *ᵥ (addrReg n m).tensorState v (single 1 1) =
      (addrReg n m).tensorState v (single 1 1) := by
  rw [sDiagM, diagonal_mulVec_tensorState _ (fun _ ↦ 1) v 1 fun z hE ↦
    prod_eq_one fun j _ ↦ by
      unfold slotDiag
      rw [show (splitBasisEquiv n 1 ((slotReg n m j).extractIndex z)).2 = 1 from
          slotFlag_eq_one z hE j,
        ite_eq_right fun h ↦ (by decide : (1 : Fin (2 ^ 1)) ≠ 0) h.2]]
  simp only [one_mul]

/-! ## Joint Flag-Flip Permutation and First-Slot Flag Probe -/

/-- Singleton register selecting slot `0`'s marker bit `b_0`. -/
def flag0Reg (n m : ℕ) (hm : 1 ≤ m) : QRegister 1 (m * (n + 1)) :=
  QRegister.singleton (slotReg n m ⟨0, hm⟩ 0)

/-- Basis permutation flipping all `m` environment flag bits simultaneously (`e ↦ e + 1`) while
leaving the `(m * n)`-qubit `addrReg` invariant. -/
noncomputable def flipPerm (n m : ℕ) : Perm (Fin (2 ^ (m * (n + 1)))) :=
  (addrReg n m).basisSplitEquiv.trans <|
    (Equiv.prodCongr (.refl _) (Equiv.addRight 1)).trans (addrReg n m).basisSplitEquiv.symm

@[simp]
theorem addrEnv_one_add_one {n m : ℕ} :
    (1 : (addrReg n m).Environment → ZMod 2) + 1 = 0 :=
  funext fun _ ↦ CharTwo.add_self_eq_zero (1 : ZMod 2)

@[simp]
theorem addrEnv_add_two {n m : ℕ} (e : (addrReg n m).Environment → ZMod 2) :
    e + 1 + 1 = e := by
  rw [add_assoc, addrEnv_one_add_one, add_zero]

@[simp]
theorem basisSplitEquiv_flipPerm (n m : ℕ) (z : Fin (2 ^ (m * (n + 1)))) :
    (addrReg n m).basisSplitEquiv (flipPerm n m z) =
      (((addrReg n m).basisSplitEquiv z).1, ((addrReg n m).basisSplitEquiv z).2 + 1) := by
  unfold flipPerm
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Equiv.coe_addRight]
  rfl

theorem flipPerm_involutive (n m : ℕ) : Function.Involutive (flipPerm n m) :=
  fun z ↦ (addrReg n m).basisSplitEquiv.injective (by
    rw [basisSplitEquiv_flipPerm, basisSplitEquiv_flipPerm]
    exact Prod.ext rfl (addrEnv_add_two _))

theorem permutationUnitary_flipPerm_mulVec_tensorState {n m : ℕ}
    (v : Fin (2 ^ (m * n)) → ℂ) (e : (addrReg n m).Environment → ZMod 2) :
    (permutationUnitary (flipPerm n m)).1 *ᵥ (addrReg n m).tensorState v (single e 1) =
      (addrReg n m).tensorState v (single (e + 1) 1) := by
  funext z
  dsimp only [permutationUnitary]
  rw [Matrix.permMatrix_mulVec, Function.comp_apply,
    show (flipPerm n m)⁻¹ z = flipPerm n m z by
      simpa [Equiv.symm_apply_eq] using (flipPerm_involutive n m z).symm]
  dsimp only [tensorState]
  rw [← QRegister.basisSplitEquiv_apply_fst, basisSplitEquiv_flipPerm,
    QRegister.basisSplitEquiv_apply_fst]
  dsimp only
  by_cases h : ((addrReg n m).basisSplitEquiv z).2 = e + 1
  · rw [show ((addrReg n m).basisSplitEquiv z).2 + 1 = e by rw [h, addrEnv_add_two], h,
      Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (show ((addrReg n m).basisSplitEquiv z).2 + 1 ≠ e from
        fun h' ↦ h (by rw [← h', addrEnv_add_two])), Pi.single_eq_of_ne h, mul_zero]

theorem flag0Reg_basisOutcomeProjector_mulVec {n m : ℕ} (hm : 1 ≤ m)
    (v₀ v₁ : Fin (2 ^ (m * n)) → ℂ) :
    let r := addrReg n m
    let ψ := r.tensorState v₀ (single 0 1) + r.tensorState v₁ (single 1 1)
    (flag0Reg n m hm).basisOutcomeProjector 0 *ᵥ ψ = r.tensorState v₀ (single 0 1) ∧
      (flag0Reg n m hm).basisOutcomeProjector 1 *ᵥ ψ = r.tensorState v₁ (single 1 1) := by
  intro r ψ
  have hfl (z : Fin (2 ^ (m * (n + 1)))) :
      (flag0Reg n m hm).extractIndex z = slotFlag n m z ⟨0, hm⟩ :=
    (basisBits 1).injective (funext fun i ↦ by
      fin_cases i
      rw [show (⟨0, by decide⟩ : Fin 1) = 0 from rfl, basisBits_slotFlag, basisBits_extractIndex]
      rfl)
  have h0 : (flag0Reg n m hm).basisOutcomeProjector 0 *ᵥ ψ = r.tensorState v₀ (single 0 1) := by
    dsimp only [r, ψ]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mulVec_add,
      diagonal_mulVec_tensorState _ (fun _ ↦ 1) v₀ 0 fun z hz ↦ by
        rw [hfl z, slotFlag_eq_zero z hz ⟨0, hm⟩, ite_eq_left rfl],
      diagonal_mulVec_tensorState _ (fun _ ↦ 0) v₁ 1 fun z hz ↦ by
        rw [hfl z, slotFlag_eq_one z hz ⟨0, hm⟩,
          ite_eq_right (by decide : (1 : Fin (2 ^ 1)) ≠ 0)]]
    simp only [one_mul, zero_mul, Pi.zero_def.symm, (addrReg n m).tensorState_zero_left, add_zero]
  refine ⟨h0, add_left_cancel (a := r.tensorState v₀ (single 0 1)) ?_⟩
  nth_rw 1 [← h0]
  rw [← Matrix.add_mulVec,
    show (flag0Reg n m hm).basisOutcomeProjector 0 +
        (flag0Reg n m hm).basisOutcomeProjector 1 = 1 by
      simpa [Fin.sum_univ_two] using (flag0Reg n m hm).sum_basisOutcomeProjector,
    Matrix.one_mulVec]

/-! ## Zero-Cost Single-Variable Dispatch, State Mapping, and Odd-Parity Readout -/

/-- Branch dispatch on classical variable `res` over a finite list of outcomes in `Fin D`. -/
def dispFin {Step Var : Type} (res : Var) {Q W D : ℕ}
    (br : Fin D → OracleDynamicCircuit Step Var Q W) :
    List (Fin D) → OracleDynamicCircuit Step Var Q W
  | [] => .skip
  | o :: rest => .qIf (fun σ ↦ σ res = (o.val : ℤ)) (br o) (dispFin res br rest)

theorem wp_measureRegister {Var : Type} [DecidableEq Var] (res : Var) {Q k : ℕ}
    (r : QRegister k Q) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) :
    ((wp (measureRegister res r) Θ) σ).1.1 =
      ∑ o : Fin (2 ^ k),
        r.basisOutcomeProjector o *
          (Θ (Store.subst σ res (Int.ofNat o.val))).1.1 *
          r.basisOutcomeProjector o := by
  unfold measureRegister
  rw [wp_qMeasure, CQAssertion.qMeasure_coe, HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  simp [QRegister.computationalBasisMeasurement_apply, HermitianMat.val_eq_coe,
    HermitianMat.conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose]

/-- Zero-query measure-swap-remeasure gadget mapping computational-basis outcome `o` to `f o` in
both the `Q`-qubit register and classical variable `res`. -/
noncomputable def qMap {Var : Type} (res : Var) {Q W : ℕ}
    (f : Fin (2 ^ Q) → Fin (2 ^ Q)) : OracleCirc Var Q W :=
  .seq (.measure res (whole Q))
    (dispFin res
      (fun o ↦ .seq (.step (phaseTag (permutationUnitary (swap o (f o))))) (.measure res (whole Q)))
      (finRange (2 ^ Q)))

theorem wp_qMap {Var : Type} [DecidableEq Var] (res : Var) {Q W : ℕ}
    (f : Fin (2 ^ Q) → Fin (2 ^ Q)) (oracle : Unitary (2 ^ W))
    (H : ℤ → Operator (2 ^ Q)) (Φ : CQAssertion (Store Var) (2 ^ Q))
    (hΦ : ∀ τ, (Φ τ).1.1 = H (τ res)) (σ : Store Var) :
    ((wp ((qMap res f).compile qAssign oracle) Φ) σ).1.1 =
      diagonal (fun o : Fin (2 ^ Q) ↦ H (f o).val (f o) (f o)) := by
  have hmeas {Ψ : CQAssertion (Store Var) (2 ^ Q)} {d : Fin (2 ^ Q) → ℂ}
      (hΨ : ∀ u : Fin (2 ^ Q), ∀ τ, τ res = (u.val : ℤ) → (Ψ τ).1.1 u u = d u)
      (τ : Store Var) : ((wp (measureRegister res (whole Q)) Ψ) τ).1.1 = diagonal d := by
    rw [wp_measureRegister res (whole Q) Ψ τ, ← Matrix.sum_single_eq_diagonal]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [QRegister.basisOutcomeProjector, QRegister.whole_embedMatrix, compProj_mul_mul,
      hΨ u _ (by simp), compProj, Matrix.smul_single, smul_eq_mul, mul_one]
  unfold qMap
  dsimp only [compile]
  rw [wp_qSeq]
  refine hmeas (fun o τ hτ ↦ ?_) σ
  let br (o : Fin (2 ^ Q)) : OracleCirc Var Q W :=
    .seq (.step (phaseTag (permutationUnitary (swap o (f o))))) (.measure res (whole Q))
  have hd (l : List (Fin (2 ^ Q))) (ho : o ∈ l) :
      wp ((dispFin res br l).compile qAssign oracle) Φ τ =
        wp ((br o).compile qAssign oracle) Φ τ := by
    induction l with
    | nil => cases ho
    | cons x _ ih =>
      simp only [dispFin, compile, wp]
      by_cases h : o = x
      · subst h
        simp [hτ]
      · simp only [show τ res ≠ (x.val : ℤ) from
          fun heq ↦ h (Fin.ext (Int.ofNat.inj (hτ.symm.trans heq))), ↓reduceIte]
        exact ih (List.mem_of_ne_of_mem h ho)
  rw [hd (finRange (2 ^ Q)) (mem_finRange o)]
  dsimp only [br, compile]
  rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
    hmeas (fun u s hs ↦ by rw [hΦ s, hs]), Matrix.mul_apply,
    sum_eq_single (f o) (fun x hx ↦ by simp [mul_diagonal, permutationUnitary_apply, hx])]
  simp [mul_diagonal, conjTranspose_apply, permutationUnitary_apply]

theorem costBound_qMap {Var : Type} [DecidableEq Var] (res : Var) {Q W : ℕ}
    (f : Fin (2 ^ Q) → Fin (2 ^ Q)) {oracle : Unitary (2 ^ W)}
    (horacle : IsRealMatrix oracle.1) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
      ((qMap res f).compile qAssign oracle) 0 := by
  unfold qMap
  dsimp only [compile]
  have hmeas : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
      (measureRegister res (whole Q)) 0 := by
    simpa [measureRegister, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) (CostModel.ofEmbeddedOracle oracle)
        res (whole Q).computationalBasisMeasurement.toMeasurement
  have hdisp (l : List (Fin (2 ^ Q))) :
      CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
        ((dispFin res
          (fun o ↦ .seq (.step (phaseTag (permutationUnitary (swap o (f o)))))
            (.measure res (whole Q))) l).compile qAssign oracle) 0 := by
    induction l with
    | nil => exact CostBound.skip_zero _
    | cons hd _ ih =>
      dsimp only [dispFin, compile]
      have hbr : CostBound (Var := Var) (d := 2 ^ Q) (CostModel.ofEmbeddedOracle oracle)
          (.qAssign (phaseTag (permutationUnitary (swap hd (f hd)))) ;;
            measureRegister res (whole Q)) 0 := by
        simpa using
          (costBound_qAssign_phaseTag (Var := Var) horacle
            (permutationUnitary (swap hd (f hd)))).seq hmeas
      simpa using CostBound.qIf _ hbr ih
  simpa using hmeas.seq (hdisp (finRange (2 ^ Q)))

/-- Apply a slot-local permutation across a list of slot indices from right to left. -/
noncomputable abbrev appPerms {n m : ℕ} (l : List (Fin m)) (e : Perm (Fin (2 ^ (n + 1))))
    (z : Fin (2 ^ (m * (n + 1)))) : Fin (2 ^ (m * (n + 1))) :=
  l.foldr (fun i acc ↦ (slotReg n m i).replaceIndex acc (e ((slotReg n m i).extractIndex acc))) z

/-- Sentinel failure index `2 ^ n` outside `Fin (2 ^ n)` inside `Fin (2 ^ (m * (n + 1)))`. -/
abbrev failOut (n m : ℕ) (hm : 1 ≤ m) : Fin (2 ^ (m * (n + 1))) :=
  ⟨2 ^ n, Nat.pow_lt_pow_right (by omega : 1 < 2) (by nlinarith)⟩

/-- Classical odd-parity readout map: when an odd number of the `m` slot flags equal `1`, returns
the address `x_j < 2 ^ n` of a `1`-flagged slot; otherwise returns `failOut n m hm = 2 ^ n`. -/
noncomputable abbrev decOut (n m : ℕ) (hm : 1 ≤ m)
    (z : Fin (2 ^ (m * (n + 1)))) : Fin (2 ^ (m * (n + 1))) :=
  open Classical in
  if (∏ j : Fin m, if slotFlag n m z j = 1 then (-1 : ℤ) else 1) = -1 then
    if h : ∃ j : Fin m, slotFlag n m z j = 1 then
      ⟨(slotAddr n m z h.choose).val,
        lt_trans (slotAddr n m z h.choose).isLt
          (Nat.pow_lt_pow_right (by omega : 1 < 2) (by nlinarith))⟩
    else 0
  else failOut n m hm

/-- Diagonal readout observable after applying `groverParallelMarkingOracle m S` and `decOut`. -/
noncomputable abbrev postDiag {n m : ℕ} (hm : 1 ≤ m)
    (S : Finset (Fin (2 ^ n))) (g : ℤ → ℂ) : Operator (2 ^ (m * (n + 1))) :=
  diagonal fun z ↦ g ((decOut n m hm (appPerms (finRange m) (markPerm S) z)).val : ℤ)

theorem sum_decOut_zero {n m : ℕ} (hm : 1 ≤ m) (S : Finset (Fin (2 ^ n)))
    (g : ℤ → ℂ) (a b : ℂ)
    (hg_s : ∀ x ∈ S, g (x.val : ℤ) = a) (hg_f : g (2 ^ n : ℤ) = b)
    (U : Operator (2 ^ (m * (n + 1)))) (w : Fin (2 ^ (m * n)) → ℂ)
    (hU : U *ᵥ single 0 1 = (addrReg n m).tensorState w (single 0 1)) :
    (Uᴴ * postDiag hm S g * U) 0 0 =
      (a - b) * ((∑ u ∈ oddSet n m S, normSq (w u) : ℝ) : ℂ) +
        b * ((∑ u : Fin (2 ^ (m * n)), normSq (w u) : ℝ) : ℂ) := by
  let r := addrReg n m
  let oddTuples := oddSet n m S
  let f : Fin (2 ^ (m * (n + 1))) → ℂ := fun z ↦
    g ((decOut n m hm (appPerms (finRange m) (markPerm S) z)).val : ℤ) *
      (normSq (r.tensorState w (single 0 1) z) : ℂ)
  have h0 : (Uᴴ * postDiag hm S g * U) 0 0 = ∑ z : Fin (2 ^ (m * (n + 1))), f z := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    dsimp only [f, r]
    rw [mul_diagonal, conjTranspose_apply, ← col_apply U 0 z, ← mulVec_single_one, hU,
      Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
    ring
  rw [h0, ← r.basisSplitEquiv.symm.sum_comp f, sum_prod_type]
  have hin (u : Fin (2 ^ (m * n))) :
      (∑ e : r.Environment → ZMod 2, f (r.basisSplitEquiv.symm (u, e))) =
        (if u ∈ oddTuples then a else b) * (normSq (w u) : ℂ) := by
    rw [sum_eq_single 0 (fun e he ↦ by
      dsimp only [f, tensorState]
      rw [show (r.basisSplitEquiv (r.basisSplitEquiv.symm (u, e))).2 = e by
            rw [Equiv.apply_symm_apply],
        Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero, Complex.ofReal_zero, mul_zero])]
    set z := r.basisSplitEquiv.symm (u, 0)
    have hz1 : r.extractIndex z = u := by simp [← QRegister.basisSplitEquiv_apply_fst, z]
    have hz2 : (r.basisSplitEquiv z).2 = 0 := by simp [z]
    dsimp only [f, tensorState]
    rw [hz1, hz2, Pi.single_eq_same, mul_one]
    congr 1
    have hxs (j : Fin m) :
        (slotReg n m j).extractIndex (appPerms (finRange m) (markPerm S) z) =
          markPerm S ((slotReg n m j).extractIndex z) := by
      suffices ∀ l : List (Fin m), l.Nodup →
          (slotReg n m j).extractIndex (appPerms l (markPerm S) z) =
            if j ∈ l then markPerm S ((slotReg n m j).extractIndex z)
            else (slotReg n m j).extractIndex z by
        simpa [mem_finRange] using this (finRange m) (List.nodup_finRange m)
      intro l hl
      induction l with
      | nil => simp [appPerms]
      | cons i l ih =>
        rcases List.nodup_cons.mp hl with ⟨hil, hl'⟩
        rw [appPerms, List.foldr_cons]
        by_cases hji : j = i
        · subst hji
          rw [QRegister.extractIndex_replaceIndex, ih hl', ite_eq_right hil,
            ite_eq_left List.mem_cons_self]
        · rw [QRegister.extractIndex_replaceIndex_of_disjoint _ _ (slotReg_disjointWires hji),
            ih hl']
          simp [List.mem_cons, hji]
    set z' := appPerms (finRange m) (markPerm S) z
    have hslt (j : Fin m) :
        splitBasisEquiv n 1 ((slotReg n m j).extractIndex z') =
          (addrEquiv n m u j, if addrEquiv n m u j ∈ S then 1 else 0) := by
      rw [hxs j, splitBasisEquiv_markPerm,
        show (splitBasisEquiv n 1 _).1 = addrEquiv n m u j from
          (addrEquiv_extractIndex n m z j).symm.trans (congrArg (addrEquiv n m · j) hz1),
        show (splitBasisEquiv n 1 _).2 = 0 from slotFlag_eq_zero z hz2 j,
        zero_add]
    have hfli (j : Fin m) : slotFlag n m z' j = 1 ↔ addrEquiv n m u j ∈ S := by
      simp [slotFlag, hslt j]
    have hodi : (∏ j : Fin m, if slotFlag n m z' j = 1 then (-1 : ℤ) else 1) = -1 ↔
        u ∈ oddSet n m S := by
      simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.prod_congr rfl fun j _ ↦ if_congr (hfli j) rfl rfl]
    unfold decOut
    open Classical in
    by_cases hodd : (∏ j : Fin m, if slotFlag n m z' j = 1 then (-1 : ℤ) else 1) = -1
    · have hex : ∃ j : Fin m, slotFlag n m z' j = 1 := by
        by_contra! hall
        exact absurd (hodd.symm.trans (prod_eq_one fun j _ ↦ ite_eq_right (hall j))) (by decide)
      rw [ite_eq_left hodd, dite_eq_left hex, ite_eq_left (hodi.mp hodd)]
      refine hg_s (slotAddr n m z' hex.choose) ?_
      unfold slotAddr
      rw [hslt hex.choose]
      exact (hfli _).mp hex.choose_spec
    · rw [ite_eq_right hodd, ite_eq_right (mt hodi.mpr hodd)]
      exact_mod_cast hg_f
  simp_rw [hin, show ∀ u : Fin (2 ^ (m * n)),
    (if u ∈ oddTuples then a else b) * (normSq (w u) : ℂ) =
      (if u ∈ oddTuples then (a - b) * (normSq (w u) : ℂ) else 0) + b * (normSq (w u) : ℂ) from
    fun _ ↦ by split_ifs <;> ring]
  rw [sum_add_distrib, sum_ite_mem, univ_inter, ← mul_sum, ← mul_sum, ← ofReal_sum, ← ofReal_sum]

end QuantumComputation.Specs.GroverSolution
