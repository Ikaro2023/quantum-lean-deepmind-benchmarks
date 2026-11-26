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

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.List.Dedup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import QuantumComputation.Algorithms.Grover.Amplitude
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Maths.Trigonometry
public import QuantumComputation.Primitives.Hadamard
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.PowerLawCost
public import Track2Grover.Engine.SpecDefs
public import Track2Grover.Engine.DeflateFunctor
/-
# Subset Eigen-Lock & Multi-Tap AGL1 QHL (`MultiTapStage2AGL1QHL`)
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

section Sec_Defs
@[expose] public section
namespace QuantumComputation.Specs.GroverSol
open Operator ResourceCounting Real
open scoped Matrix NNReal NNRat
/- ## Exact Spec Mirrors (`rfl` bridge with `QuantumComputation.Specs`) -/

/-- Marking oracle for a subset `S ⊆ Fin (2 ^ n)` acting on `n + 1` qubits. -/
noncomputable def groverSetMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  permutationUnitary (tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)
/-- Synchronous `m`-slot parallel marking oracle for `S ⊆ Fin (2 ^ n)` on `(n + 1) * m`
  qubits. -/
noncomputable def groverParallelMarkingOracle {n : ℕ} (m : ℕ)
    (S : Finset (Fin (2 ^ n))) : Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])).embedUnitary
      (groverSetMarkingOracle S)).prod
/-- All `k`-element target subsets of `Fin (2 ^ n)`. -/
def groverTargetSets (n k : ℕ) : Finset (Finset (Fin (2 ^ n))) :=
  (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k
/-- Decode up to `k` indices in `Fin (2 ^ n)` from the first `k` base-`2 ^ n` digits of
  `z.toNat`. -/
def decodeTargets (n k : ℕ) (z : ℤ) : Finset (Fin (2 ^ n)) :=
  (Finset.range k).image fun i ↦
    ⟨(z.toNat / (2 ^ n) ^ i) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
/-- Uniform-average expected oracle cost bound across all `S ∈ groverTargetSets n k`. -/
def AvgOracleCostBound {Var : Type} [DecidableEq Var] {d n : ℕ} [NeZero d] (k : ℕ)
    (costModel : Finset (Fin (2 ^ n)) → CostModel d)
    (prog : Finset (Fin (2 ^ n)) → QProg Var d) (bound : ℝ) : Prop :=
  ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
    (∀ S ∈ groverTargetSets n k, CostBound (costModel S) (prog S) (q S)) ∧
    (∑ S ∈ groverTargetSets n k, (q S : ℝ)) / (groverTargetSets n k).card ≤ bound
/-- Harmonic inverse-square-root sum `∑_{r=1}^k 1 / √r`. -/
noncomputable def groverHarmonicSqrtSum (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 k, 1 / √r
/-- Reference parallel single-find query scale `(π / 4) * √(2 ^ n / (m * k))`. -/
noncomputable def vanillaFindAnyCost (n m k : ℕ) : ℝ :=
  (π / 4) * √((2 ^ n : ℝ) / (m * k))
/-- Reference unpartitioned coupon-collecting parallel query scale. -/
noncomputable def vanillaFindAllCost (n m k : ℕ) : ℝ :=
  (π / 4) * groverHarmonicSqrtSum k * √((2 ^ n : ℝ) / m)
/-- Dyadic parameter grid `{1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024}`. -/
def groverGrid : Finset ℕ :=
  (Finset.range 11).image (fun i : ℕ ↦ 2 ^ i)
/- ## Dyadic Grid Selectors and Membership Lemmas -/

/-- Full `11 × 11` dyadic grid selector claiming every `(m, k) ∈ groverGrid × groverGrid`. -/
def gridCells (m k : ℕ) : Bool :=
  decide (m ∈ groverGrid) && decide (k ∈ groverGrid)
theorem one_le_of_mem_groverGrid {x : ℕ} (hx : x ∈ groverGrid) : 1 ≤ x := by
  simp only [groverGrid, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Nat.one_le_two_pow
theorem gridCells_nonempty : ∃ m k, gridCells m k = true := by
  have h1 : 1 ∈ groverGrid :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  exact ⟨1, 1, by simp [gridCells, h1]⟩
theorem gridCells_mem_grid {m k : ℕ} (hmk : gridCells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid := by
  simpa [gridCells] using hmk
/- ## Global-Phase Unitary Tagging for `CostModel.ofEmbeddedOracle` -/

/-- Every entry of `A` has zero imaginary part. -/
abbrev IsRealMatrix {d : ℕ} (A : Operator d) : Prop :=
  ∀ i j : Fin d, (A i j).im = 0
/-- Multiply real unitaries by global phase `Complex.I` so they never
  coincide matrix-wise with a real embedded marking oracle while acting identically under
  `wp`. -/
noncomputable def phaseTag {d : ℕ} (V : Unitary d) : Unitary d :=
  open Classical in
  if IsRealMatrix V.1 then
    ⟨Complex.I • V.1, by
      rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm,
        show (Complex.I : ℂ) * star Complex.I = 1 by simp, one_smul]
      exact V.2.2⟩
  else V
@[simp]
theorem wp_phaseTag {Var : Type} {d : ℕ} (V : Unitary d) (θ : CQAssertion (Store Var) d) :
    CQAssertion.qAssign (phaseTag V) θ = CQAssertion.qAssign V θ := by
  unfold phaseTag
  split_ifs
  · funext σ
    refine Subtype.ext (Subtype.ext ?_)
    rw [qhlQAssign_val, qhlQAssign_val]
    change (Complex.I • V.1)ᴴ * (θ σ).1.1 * (Complex.I • V.1) = _
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show star (Complex.I : ℂ) * Complex.I = 1 by simp, one_smul]
  · rfl
theorem permutationUnitary_apply {d : ℕ} (e : Equiv.Perm (Fin d)) (i j : Fin d) :
    (permutationUnitary e).1 i j = if i = e j then 1 else 0 := by
  have h := congrFun (permutationUnitary_smul_col e j 1) i
  simpa [Matrix.col_apply, Pi.single_apply] using h
theorem isRealMatrix_permutationUnitary {d : ℕ} (e : Equiv.Perm (Fin d)) :
    IsRealMatrix (permutationUnitary e).1 := fun i j ↦ by
  rw [permutationUnitary_apply]
  split_ifs <;> simp
theorem isRealMatrix_embedMatrix {w q : ℕ} (r : QRegister w q) {A : Operator (2 ^ w)}
    (hA : IsRealMatrix A) : IsRealMatrix (r.embedMatrix A) := fun i j ↦ by
  rw [QRegister.embedMatrix_apply]
  split_ifs <;> simp [hA (r.extractIndex i) (r.extractIndex j)]
theorem isRealMatrix_groverSetMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    IsRealMatrix (groverSetMarkingOracle S).1 :=
  isRealMatrix_permutationUnitary _
theorem isRealMatrix_listProd {d : ℕ} {l : List (Unitary d)}
    (hl : ∀ U ∈ l, IsRealMatrix U.1) : IsRealMatrix l.prod.1 := by
  induction l with
  | nil =>
    intro i j
    by_cases h : i = j <;> simp [h]
  | cons U Us ih =>
    intro i j
    rw [List.prod_cons, Submonoid.coe_mul]
    simp only [Matrix.mul_apply, Complex.im_sum]
    exact Finset.sum_eq_zero fun k _ ↦ by
      rw [Complex.mul_im, hl U List.mem_cons_self i k,
        ih (fun V hV ↦ hl V (List.mem_cons_of_mem U hV)) k j]
      ring
theorem isRealMatrix_groverParallelMarkingOracle {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    IsRealMatrix (groverParallelMarkingOracle m S).1 := by
  refine isRealMatrix_listProd fun U hU ↦ ?_
  rw [List.mem_ofFn] at hU
  obtain ⟨i, rfl⟩ := hU
  rw [QRegister.embedUnitary_val]
  exact isRealMatrix_embedMatrix _ (isRealMatrix_groverSetMarkingOracle S)
theorem ofEmbeddedOracle_unitaryCost_phaseTag_eq_zero {w q : ℕ}
    {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1)
    (V : Unitary (2 ^ q)) :
    (CostModel.ofEmbeddedOracle oracle).unitaryCost (phaseTag V) = 0 := by
  unfold CostModel.ofEmbeddedOracle
  dsimp only
  refine ite_eq_right fun ⟨r, hr⟩ ↦ ?_
  have hR : IsRealMatrix (phaseTag V).1 := by
    rw [hr, QRegister.embedUnitary_val]
    exact isRealMatrix_embedMatrix r horacle
  unfold phaseTag at hR
  split_ifs at hR with hV
  · have hV0 : V.1 = 0 := Matrix.ext fun i j ↦
      Complex.ext (by simpa using hR i j) (by simpa using hV i j)
    have hun := congrFun (congrFun V.2.2 (0 : Fin (2 ^ q))) (0 : Fin (2 ^ q))
    simp [hV0] at hun
  · exact hV hR
theorem costBound_qAssign_phaseTag {Var : Type} [DecidableEq Var] {w q : ℕ}
    {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1)
    (V : Unitary (2 ^ q)) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle) (.qAssign (phaseTag V)) 0 := by
  simpa [ofEmbeddedOracle_unitaryCost_phaseTag_eq_zero horacle V] using
    CostBound.qAssign (Var := Var) (CostModel.ofEmbeddedOracle oracle) (phaseTag V)
end QuantumComputation.Specs.GroverSol
end
end Sec_Defs
section Sec_SubsetEigLock
section Sec_OddParityBridge
@[expose] public section
namespace QuantumComputation.Specs.GroverSol
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
/- ## Slot, Full-Oracle, and Address Register Geometry -/

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
/-- Identity-ordered `((n + 1) * m)`-wire view of all `m * (n + 1)` slot wires for
  `.oracle`. -/
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
  rw [(show ∀ b : Fin (2 ^ 1), b = 0 ↔ basisBits 1 b 0 = 0 by
      intro b; rw [basisBits_eq_div_mod]; fin_cases b
      · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
      · exact ⟨fun h ↦ (nomatch h), fun h ↦ (nomatch h)⟩),
    basisBits_slotFlag, hE, Pi.zero_apply]
theorem slotFlag_eq_one {n m : ℕ} (z : Fin (2 ^ (m * (n + 1))))
    (hE : ((addrReg n m).basisSplitEquiv z).2 = 1) (j : Fin m) :
    slotFlag n m z j = 1 := by
  rw [(show ∀ b : Fin (2 ^ 1), b = 1 ↔ basisBits 1 b 0 = 1 by
      intro b; rw [basisBits_eq_div_mod]; fin_cases b
      · exact ⟨fun h ↦ (nomatch h), fun h ↦ (nomatch h)⟩
      · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩),
    basisBits_slotFlag, hE, Pi.one_apply]
/- ## Flag-Basis Conjugation and Single-Slot Phase Oracle -/

/-- Basis permutation `(x, b) ↦ (x, b ⊕ [x ∈ S])` underlying `groverSetMarkingOracle S`. -/
abbrev markPerm {n : ℕ} (S : Finset (Fin (2 ^ n))) : Perm (Fin (2 ^ (n + 1))) :=
  tableAddPerm (fun x : Fin (2 ^ n) ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)
theorem splitBasisEquiv_markPerm {n : ℕ} (S : Finset (Fin (2 ^ n))) (v : Fin (2 ^ (n + 1))) :
    splitBasisEquiv n 1 (markPerm S v) =
      ((splitBasisEquiv n 1 v).1,
        (splitBasisEquiv n 1 v).2 + if (splitBasisEquiv n 1 v).1 ∈ S then 1 else 0) := by
  simp [markPerm, tableAddPerm, addRightShear]
/-- Conjugated single-slot diagonal entries: `-1` when `x ∈ S` and `b = 0`, and `+1`
  otherwise
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
    intro δ b₁ b₂
    have hs : (∑ k : Fin (2 ^ 1), flagSign b₁ (k + δ) * flagSign k b₂) =
        flagSign b₁ (0 + δ) * flagSign 0 b₂ +
          flagSign b₁ (1 + δ) * flagSign 1 b₂ := Fin.sum_univ_two _
    rw [hs]; fin_cases δ <;> fin_cases b₁ <;> fin_cases b₂ <;> rfl
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
/- ## Odd-Parity Target-Tuple Subset, Density, and Phase Step -/

/-- Address `m`-tuples `(x_0,..., x_{m - 1})` containing an odd number of elements of `S`. -/
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
        ite_eq_right fun h ↦ (fun h0 : (1 : Fin (2 ^ 1)) = 0 ↦ nomatch h0) h.2]]
  simp only [one_mul]
/- ## Joint Flag-Flip Permutation and First-Slot Flag Probe -/

/-- Singleton register selecting slot `0`'s marker bit `b_0`. -/
def flag0Reg (n m : ℕ) (hm : 1 ≤ m) : QRegister 1 (m * (n + 1)) :=
  QRegister.singleton (slotReg n m ⟨0, hm⟩ 0)
/-- Basis permutation flipping all `m` environment flag bits simultaneously (`e ↦ e + 1`)
  while
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
      rw [show (⟨0, Nat.zero_lt_one⟩ : Fin 1) = 0 from rfl,
        basisBits_slotFlag, basisBits_extractIndex]
      rfl)
  have h0 : (flag0Reg n m hm).basisOutcomeProjector 0 *ᵥ ψ = r.tensorState v₀ (single 0 1) := by
    dsimp only [r, ψ]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mulVec_add,
      diagonal_mulVec_tensorState _ (fun _ ↦ 1) v₀ 0 fun z hz ↦ by
        rw [hfl z, slotFlag_eq_zero z hz ⟨0, hm⟩, ite_eq_left rfl],
      diagonal_mulVec_tensorState _ (fun _ ↦ 0) v₁ 1 fun z hz ↦ by
        rw [hfl z, slotFlag_eq_one z hz ⟨0, hm⟩,
          ite_eq_right (fun h0 : (1 : Fin (2 ^ 1)) = 0 ↦ nomatch h0)]]
    simp only [one_mul, zero_mul, Pi.zero_def.symm, (addrReg n m).tensorState_zero_left, add_zero]
  refine ⟨h0, add_left_cancel (a := r.tensorState v₀ (single 0 1)) ?_⟩
  nth_rw 1 [← h0]
  rw [← Matrix.add_mulVec,
    show (flag0Reg n m hm).basisOutcomeProjector 0 +
        (flag0Reg n m hm).basisOutcomeProjector 1 = 1 by
      simpa [Fin.sum_univ_two] using (flag0Reg n m hm).sum_basisOutcomeProjector,
    Matrix.one_mulVec]
/- ## Zero-Cost Single-Variable Dispatch, State Mapping, and Odd-Parity Readout -/

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
  rw [wp_measureRegister_coe_ax, HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  simp [ HermitianMat.val_eq_coe,
    HermitianMat.conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose]
/-- Zero-query measure-swap-remeasure gadget mapping computational-basis outcome `o` to `f
  o` in
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
        res (whole Q).regBasisMeas
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
end QuantumComputation.Specs.GroverSol
end
end Sec_OddParityBridge
section Sec_FindAllBridge
@[expose] public section
namespace QuantumComputation.Specs.GroverSol
open Operator ResourceCounting Real
open QProg (qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val DisjointWires)
open Matrix (mulVec_mulVec diagonal)
open List (mem_finRange prod_cons finRange map_cons)
open Fintype (sum_eq_single sum_prod_type)
open Equiv (Perm)
open Pi (single)
open scoped Matrix NNReal ENNReal ComplexOrder MatrixOrder QProg.Notation
/- ## Low/High Register Splitting and `workMemState` Product Vectors -/

/-- Little-endian split of a `(W + M)`-qubit basis index into low `W` wires (`block 0 W`)
  and
  high `M` wires (`block W M`). -/
abbrev lowHighEquiv (W M : ℕ) : Fin (2 ^ (W + M)) ≃ Fin (2 ^ W) × Fin (2 ^ M) :=
  (finCongr (by rw [Nat.add_comm])).trans
    ((splitBasisEquiv M W).trans (Equiv.prodComm _ _))
theorem lowHighEquiv_fst_val (W M : ℕ) (z : Fin (2 ^ (W + M))) :
    ((lowHighEquiv W M z).1).val = z.val % 2 ^ W := by
  simp [lowHighEquiv, splitBasisEquiv, finProdFinEquiv_symm_apply, Fin.modNat]
theorem lowHighEquiv_snd_val (W M : ℕ) (z : Fin (2 ^ (W + M))) :
    ((lowHighEquiv W M z).2).val = z.val / 2 ^ W := by
  simp [lowHighEquiv, splitBasisEquiv, finProdFinEquiv_symm_apply, Fin.divNat]
@[simp]
theorem lowHighEquiv_zero (W M : ℕ) : lowHighEquiv W M 0 = (0, 0) :=
  Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp))
/-- Low `W`-wire block inside a `(W + M)`-wire register. -/
abbrev lowBlock (W M : ℕ) : QRegister W (W + M) :=
  QRegister.block 0 W (by omega)
/-- High `M`-wire block inside a `(W + M)`-wire register. -/
abbrev highBlock (W M : ℕ) : QRegister M (W + M) :=
  QRegister.block W M (by omega)
theorem extractIndex_lowBlock (W M : ℕ) (z : Fin (2 ^ (W + M))) :
    (lowBlock W M).extractIndex z = (lowHighEquiv W M z).1 := by
  apply (basisBits W).injective
  funext q
  rw [basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit, lowHighEquiv_fst_val]
  have hq : (lowBlock W M q).val = q.val := by simp [lowBlock]
  rw [hq, Nat.testBit_mod_two_pow]
  simp [q.isLt]
theorem extractIndex_highBlock (W M : ℕ) (z : Fin (2 ^ (W + M))) :
    (highBlock W M).extractIndex z = (lowHighEquiv W M z).2 := by
  apply (basisBits M).injective
  funext q
  rw [basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit, lowHighEquiv_snd_val]
  have hq : (highBlock W M q).val = q.val + W := by
    simp only [highBlock, QRegister.block_apply_val]
    omega
  rw [hq, Nat.testBit_div_two_pow]
theorem agreeOutside_lowBlock_iff (W M : ℕ) (i j : Fin (2 ^ (W + M))) :
    (lowBlock W M).AgreeOutside i j ↔ (lowHighEquiv W M i).2 = (lowHighEquiv W M j).2 := by
  constructor
  · intro h
    rw [← extractIndex_highBlock, ← extractIndex_highBlock]
    apply (basisBits M).injective
    funext q
    rw [basisBits_extractIndex, basisBits_extractIndex]
    refine h (highBlock W M q) ?_
    rintro ⟨p, hp⟩
    have hp' := congrArg Fin.val hp
    simp only [lowBlock, highBlock, QRegister.block_apply_val] at hp'
    omega
  · intro h p hp
    have hpW : W ≤ p.val := by
      by_contra hlt
      exact hp ⟨⟨p.val, by omega⟩, Fin.ext (by simp [lowBlock])⟩
    let q : Fin M := ⟨p.val - W, by omega⟩
    have hpq : p = highBlock W M q :=
      Fin.ext (by simp only [highBlock, QRegister.block_apply_val, q]; omega)
    rw [hpq, ← basisBits_extractIndex, ← basisBits_extractIndex,
      extractIndex_highBlock, extractIndex_highBlock, h]
theorem agreeOutside_highBlock_iff (W M : ℕ) (i j : Fin (2 ^ (W + M))) :
    (highBlock W M).AgreeOutside i j ↔ (lowHighEquiv W M i).1 = (lowHighEquiv W M j).1 := by
  constructor
  · intro h
    rw [← extractIndex_lowBlock, ← extractIndex_lowBlock]
    apply (basisBits W).injective
    funext q
    rw [basisBits_extractIndex, basisBits_extractIndex]
    refine h (lowBlock W M q) ?_
    rintro ⟨p, hp⟩
    have hp' := congrArg Fin.val hp
    simp only [lowBlock, highBlock, QRegister.block_apply_val] at hp'
    omega
  · intro h p hp
    have hpW : p.val < W := by
      by_contra hge
      exact hp ⟨⟨p.val - W, by omega⟩,
        Fin.ext (by simp only [highBlock, QRegister.block_apply_val]; omega)⟩
    let q : Fin W := ⟨p.val, hpW⟩
    have hpq : p = lowBlock W M q := Fin.ext (by simp [lowBlock, q])
    rw [hpq, ← basisBits_extractIndex, ← basisBits_extractIndex,
      extractIndex_lowBlock, extractIndex_lowBlock, h]
/-- Tensor-product amplitude vector on `W + M` qubits for a low-block state `ψ` and
  high-block
  state `φ`. -/
def workMemState {W M : ℕ} (ψ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ)
    (z : Fin (2 ^ (W + M))) : ℂ :=
  ψ (lowHighEquiv W M z).1 * φ (lowHighEquiv W M z).2
theorem workMemState_single {W M : ℕ} (w : Fin (2 ^ W)) (μ : Fin (2 ^ M)) :
    workMemState (single w 1) (single μ 1) = single ((lowHighEquiv W M).symm (w, μ)) 1 := by
  funext z
  dsimp only [workMemState]
  by_cases hz : z = (lowHighEquiv W M).symm (w, μ)
  · subst hz
    rw [Equiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne hz]
    have hne : lowHighEquiv W M z ≠ (w, μ) := fun h ↦ hz ((lowHighEquiv W M).eq_symm_apply.mpr h)
    by_cases hw : (lowHighEquiv W M z).1 = w
    · have hμ : (lowHighEquiv W M z).2 ≠ μ := fun h2 ↦ hne (Prod.ext hw h2)
      rw [Pi.single_eq_of_ne hμ, mul_zero]
    · rw [Pi.single_eq_of_ne hw, zero_mul]
@[simp]
theorem workMemState_zero (W M : ℕ) :
    workMemState (single (0 : Fin (2 ^ W)) 1) (single (0 : Fin (2 ^ M)) 1) = single 0 1 := by
  rw [workMemState_single, ← lowHighEquiv_zero W M, Equiv.symm_apply_apply]
theorem embedMatrix_lowBlock_mulVec_workMemState {W M : ℕ}
    (A : Operator (2 ^ W)) (ψ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    (lowBlock W M).embedMatrix A *ᵥ workMemState ψ φ = workMemState (A *ᵥ ψ) φ := by
  funext z
  rw [Matrix.mulVec, dotProduct]
  let g (y : Fin (2 ^ (W + M))) : ℂ := (lowBlock W M).embedMatrix A z y * workMemState ψ φ y
  change ∑ y, g y = _
  rw [← (lowHighEquiv W M).symm.sum_comp g, sum_prod_type]
  dsimp only [g, workMemState]
  simp_rw [QRegister.embedMatrix_apply_of_agreeOutside, agreeOutside_lowBlock_iff,
    extractIndex_lowBlock, Equiv.apply_symm_apply]
  have hsum (w : Fin (2 ^ W)) :
      (∑ μ : Fin (2 ^ M),
        (A (lowHighEquiv W M z).1 w * if (lowHighEquiv W M z).2 = μ then 1 else 0) *
          (ψ w * φ μ)) =
        (A (lowHighEquiv W M z).1 w * ψ w) * φ (lowHighEquiv W M z).2 := by
    rw [sum_eq_single (lowHighEquiv W M z).2
      (fun μ hμ ↦ by rw [ite_eq_right (Ne.symm hμ), mul_zero, zero_mul])]
    rw [ite_eq_left rfl, mul_one]
    ring
  simp_rw [hsum, ← Finset.sum_mul]
  rfl
theorem embedMatrix_highBlock_mulVec_workMemState {W M : ℕ}
    (B : Operator (2 ^ M)) (ψ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    (highBlock W M).embedMatrix B *ᵥ workMemState ψ φ = workMemState ψ (B *ᵥ φ) := by
  funext z
  rw [Matrix.mulVec, dotProduct]
  let g (y : Fin (2 ^ (W + M))) : ℂ := (highBlock W M).embedMatrix B z y * workMemState ψ φ y
  change ∑ y, g y = _
  rw [← (lowHighEquiv W M).symm.sum_comp g, sum_prod_type, Finset.sum_comm]
  dsimp only [g, workMemState]
  simp_rw [QRegister.embedMatrix_apply_of_agreeOutside, agreeOutside_highBlock_iff,
    extractIndex_highBlock, Equiv.apply_symm_apply]
  have hsum (μ : Fin (2 ^ M)) :
      (∑ w : Fin (2 ^ W),
        (B (lowHighEquiv W M z).2 μ * if (lowHighEquiv W M z).1 = w then 1 else 0) *
          (ψ w * φ μ)) =
        ψ (lowHighEquiv W M z).1 * (B (lowHighEquiv W M z).2 μ * φ μ) := by
    rw [sum_eq_single (lowHighEquiv W M z).1
      (fun w hw ↦ by rw [ite_eq_right (Ne.symm hw), mul_zero, zero_mul])]
    rw [ite_eq_left rfl, mul_one]
    ring
  simp_rw [hsum, ← Finset.mul_sum]
  rfl
/- ## `memReg` Layout, `decodeTargets` Bridge, and Reversible Target Recording -/

/-- Work register (`m * (n + 1)` oracle-slot wires) inside a `Q`-qubit `FindAll` state. -/
abbrev workReg (n m Q : ℕ) (hQ : m * (n + 1) ≤ Q) : QRegister (m * (n + 1)) Q :=
  QRegister.block 0 (m * (n + 1)) (by omega)
/-- Oracle-ordered `((n + 1) * m)`-wire view of `workReg` for `.oracle` nodes. -/
abbrev workFullReg (n m Q : ℕ) (hQ : m * (n + 1) ≤ Q) : QRegister ((n + 1) * m) Q :=
  (workReg n m Q hQ).compose (fullReg n m)
/-- Combined `(m * (n + 1) + k * n)`-qubit work + memory block inside `Q` qubits. -/
abbrev workMemReg (n m k Q : ℕ) (hQ : m * (n + 1) + k * n ≤ Q) :
    QRegister (m * (n + 1) + k * n) Q :=
  QRegister.block 0 (m * (n + 1) + k * n) (by omega)
theorem addrEquiv_eq_div_pow_mod (n k : ℕ) (μ : Fin (2 ^ (k * n))) (i : Fin k) :
    addrEquiv n k μ i = ⟨(μ.val / (2 ^ n) ^ i.val) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ := by
  apply (basisBits n).injective
  funext r
  have hL : basisBits n (addrEquiv n k μ i) r = basisBits (k * n) μ (finProdFinEquiv (i, r)) := by
    simp [addrEquiv]
  rw [hL, basisBits_eq_testBit, basisBits_eq_testBit]
  simp only [finProdFinEquiv_apply_val, Nat.testBit_mod_two_pow, r.isLt, decide_true, Bool.true_and]
  rw [← pow_mul, Nat.testBit_div_two_pow, show r.val + n * i.val = i.val * n + r.val by ring]
theorem decodeTargets_ofNat_eq_image_addrEquiv (n k : ℕ) (μ : Fin (2 ^ (k * n))) :
    decodeTargets n k (Int.ofNat μ.val) = Finset.univ.image (addrEquiv n k μ) := by
  ext x
  dsimp only [decodeTargets, Int.toNat]
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, addrEquiv_eq_div_pow_mod n k μ ⟨a, ha⟩⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, (addrEquiv_eq_div_pow_mod n k μ i).symm⟩
theorem decodeTargets_ofNat_eq_of_subset_of_injective {n k : ℕ}
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (μ : Fin (2 ^ (k * n)))
    (hmem : ∀ i : Fin k, addrEquiv n k μ i ∈ S)
    (hinj : Function.Injective (addrEquiv n k μ)) :
    decodeTargets n k (Int.ofNat μ.val) = S := by
  rw [decodeTargets_ofNat_eq_image_addrEquiv]
  refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _ ↦ hmem i) ?_
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hcard]
/-- Reversible out-of-place slotwise addition `(w, mTuple) ↦ (w, mTuple + δ w)` from a
  `W`-qubit
  work block into the `k` `n`-bit slots of `memReg`. -/
abbrev memAddPerm {W n k : ℕ} (δ : Fin (2 ^ W) → Fin k → Fin (2 ^ n)) :
    Perm (Fin (2 ^ (W + k * n))) :=
  (lowHighEquiv W (k * n)).trans <|
    ((Equiv.prodCongr (.refl _) (addrEquiv n k)).trans <|
      (addRightShear δ).trans <|
        (Equiv.prodCongr (.refl _) (addrEquiv n k).symm)).trans
      (lowHighEquiv W (k * n)).symm
@[simp]
theorem lowHighEquiv_memAddPerm {W n k : ℕ} (δ : Fin (2 ^ W) → Fin k → Fin (2 ^ n))
    (z : Fin (2 ^ (W + k * n))) :
    lowHighEquiv W (k * n) (memAddPerm δ z) =
      ((lowHighEquiv W (k * n) z).1,
        (addrEquiv n k).symm
          (addrEquiv n k (lowHighEquiv W (k * n) z).2 + δ (lowHighEquiv W (k * n) z).1)) := by
  simp [memAddPerm, addRightShear]
theorem permutationUnitary_memAddPerm_mulVec_single {W n k : ℕ}
    (δ : Fin (2 ^ W) → Fin k → Fin (2 ^ n)) (w : Fin (2 ^ W)) (μ : Fin (2 ^ (k * n))) :
    (permutationUnitary (memAddPerm δ)).1 *ᵥ workMemState (single w 1) (single μ 1) =
      workMemState (single w 1) (single ((addrEquiv n k).symm (addrEquiv n k μ + δ w)) 1) := by
  rw [workMemState_single, permutationUnitary_mulVec_single, workMemState_single]
  refine congrArg (single · 1) ((lowHighEquiv W (k * n)).injective ?_)
  rw [lowHighEquiv_memAddPerm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
/-- Prefix `{0,..., s - 1}` of active slots in `Fin k`. -/
def memPrefix (k s : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i : Fin k ↦ i.val < s
/-- Set of targets currently stored in the active slots of `μ: Fin (2 ^ (k * n))`. -/
def memSeen (n k : ℕ) (active : Finset (Fin k)) (μ : Fin (2 ^ (k * n))) : Finset (Fin (2 ^ n)) :=
  active.image (addrEquiv n k μ)
/-- Slot increment writing `hits w` sequentially into `memReg` slots `s, s + 1,...`. -/
def batchDelta {W n k : ℕ} (s : ℕ) (hits : Fin (2 ^ W) → List (Fin (2 ^ n)))
    (w : Fin (2 ^ W)) (j : Fin k) : Fin (2 ^ n) :=
  if s ≤ j.val then ((hits w)[j.val - s]?).getD 0 else 0
/-- Reversible multi-slot write recording a batch `hits w` starting at slot index `s`. -/
abbrev memWriteBatchPerm {W n k : ℕ} (s : ℕ) (hits : Fin (2 ^ W) → List (Fin (2 ^ n))) :
    Perm (Fin (2 ^ (W + k * n))) :=
  memAddPerm (batchDelta s hits)
/-- Invariant predicate that the first `s` slots of `μ` hold `s` pairwise-distinct elements
  of `S`
  and all remaining slots `≥ s` are clean (`0`). -/
def MemPrefixValid {n k : ℕ} (S : Finset (Fin (2 ^ n))) (s : ℕ) (μ : Fin (2 ^ (k * n))) : Prop :=
  s ≤ k ∧
    (∀ i : Fin k, i.val < s → addrEquiv n k μ i ∈ S) ∧
    (∀ i j : Fin k, i.val < s → j.val < s → addrEquiv n k μ i = addrEquiv n k μ j → i = j) ∧
    (∀ i : Fin k, s ≤ i.val → addrEquiv n k μ i = 0)
theorem memPrefixValid_zero {n k : ℕ} (S : Finset (Fin (2 ^ n))) :
    MemPrefixValid S 0 (0 : Fin (2 ^ (k * n))) := by
  refine ⟨Nat.zero_le k, fun _ hi ↦ absurd hi (Nat.not_lt_zero _),
    fun _ _ hi _ _ ↦ absurd hi (Nat.not_lt_zero _), fun i _ ↦ ?_⟩
  apply (basisBits n).injective
  funext r
  simp [addrEquiv]
theorem decodeTargets_eq_of_memPrefixValid_full {n k : ℕ} {S : Finset (Fin (2 ^ n))}
    (hcard : S.card = k) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S k μ) :
    decodeTargets n k (Int.ofNat μ.val) = S :=
  decodeTargets_ofNat_eq_of_subset_of_injective hcard μ
    (fun i ↦ hval.2.1 i i.isLt)
    (fun i j hij ↦ hval.2.2.1 i j i.isLt j.isLt hij)
theorem card_memSeen_of_memPrefixValid {n k s : ℕ} {S : Finset (Fin (2 ^ n))}
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s μ) :
    (memSeen n k (memPrefix k s) μ).card = s ∧ memSeen n k (memPrefix k s) μ ⊆ S := by
  refine ⟨?_, Finset.image_subset_iff.mpr fun i hi ↦ ?_⟩
  · rw [memSeen, Finset.card_image_of_injOn]
    · have hbij : (memPrefix k s).card = (Finset.range s).card := by
        refine Finset.card_bij (fun i _ ↦ i.val)
          (fun i hi ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
          (fun i₁ _ i₂ _ h ↦ Fin.ext h)
          (fun a ha ↦ ⟨⟨a, lt_of_lt_of_le (Finset.mem_range.mp ha) hval.1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ha⟩, rfl⟩)
      rw [hbij, Finset.card_range]
    · intro i hi j hj hij
      exact hval.2.2.1 i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij
  · exact hval.2.1 i (Finset.mem_filter.mp hi).2
theorem memPrefixValid_batchAdvance {W n k s : ℕ} {S : Finset (Fin (2 ^ n))}
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s μ)
    (hits : Fin (2 ^ W) → List (Fin (2 ^ n))) (w : Fin (2 ^ W))
    (hnodup : (hits w).Nodup) (hlen : s + (hits w).length ≤ k)
    (hnew : ∀ x ∈ hits w, x ∈ S \ memSeen n k (memPrefix k s) μ) :
    MemPrefixValid S (s + (hits w).length)
      ((addrEquiv n k).symm (addrEquiv n k μ + batchDelta s hits w)) := by
  set μ' := (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s hits w)
  have hslot (i : Fin k) : addrEquiv n k μ' i = addrEquiv n k μ i + batchDelta s hits w i := by
    dsimp only [μ']
    rw [Equiv.apply_symm_apply, Pi.add_apply]
  have hlt (i : Fin k) (hi : i.val < s) : addrEquiv n k μ' i = addrEquiv n k μ i := by
    rw [hslot i, batchDelta, ite_eq_right (not_le.mpr hi), add_zero]
  have hmid (i : Fin k) (hlo : s ≤ i.val) (hhi : i.val < s + (hits w).length) :
      addrEquiv n k μ' i = (hits w)[i.val - s]'(by omega) := by
    rw [hslot i, hval.2.2.2 i hlo, zero_add, batchDelta, ite_eq_left hlo,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hge (i : Fin k) (hi : s + (hits w).length ≤ i.val) : addrEquiv n k μ' i = 0 := by
    have hlo : s ≤ i.val := by omega
    rw [hslot i, hval.2.2.2 i hlo, zero_add, batchDelta, ite_eq_left hlo,
      List.getElem?_eq_none (by omega), Option.getD_none]
  refine ⟨hlen, fun i hi ↦ ?_, fun i j hi hj hij ↦ ?_, hge⟩
  · by_cases his : i.val < s
    · rw [hlt i his]
      exact hval.2.1 i his
    · rw [hmid i (le_of_not_gt his) hi]
      exact (Finset.mem_sdiff.mp (hnew _ (List.getElem_mem _))).1
  · by_cases his : i.val < s
    · by_cases hjs : j.val < s
      · rw [hlt i his, hlt j hjs] at hij
        exact hval.2.2.1 i j his hjs hij
      · rw [hlt i his, hmid j (le_of_not_gt hjs) hj] at hij
        have hmem_j : (hits w)[j.val - s]'(by omega) ∈ hits w := List.getElem_mem _
        have hmemS := (Finset.mem_sdiff.mp (hnew _ hmem_j)).2
        exfalso
        refine hmemS ?_
        rw [← hij]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, his⟩, rfl⟩
    · by_cases hjs : j.val < s
      · rw [hmid i (le_of_not_gt his) hi, hlt j hjs] at hij
        have hmem_i : (hits w)[i.val - s]'(by omega) ∈ hits w := List.getElem_mem _
        have hmemS := (Finset.mem_sdiff.mp (hnew _ hmem_i)).2
        exfalso
        refine hmemS ?_
        rw [hij]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjs⟩, rfl⟩
      · rw [hmid i (le_of_not_gt his) hi, hmid j (le_of_not_gt hjs) hj] at hij
        have hidx := (List.Nodup.getElem_inj_iff hnodup).mp hij
        exact Fin.ext (by omega)
/- ## Deflated Parallel Marking Conjugation (`S \ memSeen`) -/

/-- Lift a local basis permutation on `2 ^ w` states to the global `2 ^ q` basis via `r`. -/
noncomputable def liftPerm {w q : ℕ} (r : QRegister w q) (e : Perm (Fin (2 ^ w))) :
    Perm (Fin (2 ^ q)) :=
  r.basisSplitEquiv.trans ((Equiv.prodCongr e (.refl _)).trans r.basisSplitEquiv.symm)
theorem liftPerm_apply_eq_replaceIndex {w q : ℕ} (r : QRegister w q) (e : Perm (Fin (2 ^ w)))
    (z : Fin (2 ^ q)) :
    liftPerm r e z = r.replaceIndex z (e (r.extractIndex z)) := by
  apply r.basisSplitEquiv.injective
  rw [QRegister.basisSplitEquiv_replaceIndex]
  simp [liftPerm, Prod.map, ← QRegister.basisSplitEquiv_apply_fst]
theorem permutationUnitary_mul {d : ℕ} (e₁ e₂ : Perm (Fin d)) :
    permutationUnitary (e₁ * e₂) = permutationUnitary e₁ * permutationUnitary e₂ := by
  apply Subtype.ext
  ext i j
  rw [Submonoid.coe_mul, Matrix.mul_apply, permutationUnitary_apply,
    sum_eq_single (e₂ j) (fun k hk ↦ by
      rw [permutationUnitary_apply, permutationUnitary_apply, ite_eq_right hk, mul_zero])]
  rw [permutationUnitary_apply, permutationUnitary_apply, ite_eq_left rfl, mul_one,
    Equiv.Perm.mul_apply]
theorem embedUnitary_permutationUnitary {w q : ℕ} (r : QRegister w q) (e : Perm (Fin (2 ^ w))) :
    r.embedUnitary (permutationUnitary e) = permutationUnitary (liftPerm r e) := by
  apply Subtype.ext
  ext i j
  rw [embedUnitary_val, QRegister.embedMatrix_apply, permutationUnitary_apply,
    permutationUnitary_apply]
  have heq : (i = liftPerm r e j) ↔
      (r.extractIndex i = e (r.extractIndex j) ∧
        (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2) := by
    rw [← r.basisSplitEquiv.apply_eq_iff_eq, Prod.ext_iff]
    simp [liftPerm, ← QRegister.basisSplitEquiv_apply_fst]
  by_cases h1 : r.extractIndex i = e (r.extractIndex j) <;>
    by_cases h2 : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2 <;>
    simp [heq, h1, h2]
theorem liftPerm_comm_of_disjoint {w₁ w₂ q : ℕ} {r₁ : QRegister w₁ q} {r₂ : QRegister w₂ q}
    (hdisj : r₁.DisjointWires r₂) (e₁ : Perm (Fin (2 ^ w₁))) (e₂ : Perm (Fin (2 ^ w₂))) :
    liftPerm r₁ e₁ * liftPerm r₂ e₂ = liftPerm r₂ e₂ * liftPerm r₁ e₁ := by
  have hU : permutationUnitary (liftPerm r₁ e₁ * liftPerm r₂ e₂) =
      permutationUnitary (liftPerm r₂ e₂ * liftPerm r₁ e₁) := by
    rw [permutationUnitary_mul, permutationUnitary_mul, ← embedUnitary_permutationUnitary,
      ← embedUnitary_permutationUnitary]
    apply Subtype.ext
    simp only [Submonoid.coe_mul, embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hdisj _ _
  apply Equiv.ext
  intro z
  have hz := congrFun (permutationUnitary_mulVec_single (liftPerm r₁ e₁ * liftPerm r₂ e₂) z 1)
    ((liftPerm r₂ e₂ * liftPerm r₁ e₁) z)
  rw [hU, permutationUnitary_mulVec_single, Pi.single_eq_same] at hz
  by_contra hne
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at hz
  exact one_ne_zero hz
/-- Basis permutation on `m * (n + 1)` qubits applying `markPerm T` across all `m` slots. -/
noncomputable def parallelMarkPerm (n m : ℕ) (T : Finset (Fin (2 ^ n))) :
    Perm (Fin (2 ^ (m * (n + 1)))) :=
  ((finRange m).map fun i ↦ liftPerm (slotReg n m i) (markPerm T)).prod
theorem fullReg_embedUnitary_eq_permutationUnitary {n m : ℕ} (T : Finset (Fin (2 ^ n))) :
    (fullReg n m).embedUnitary (groverParallelMarkingOracle m T) =
      permutationUnitary (parallelMarkPerm n m T) := by
  have hprod (l : List (Perm (Fin (2 ^ (m * (n + 1)))))) :
      permutationUnitary l.prod = (l.map permutationUnitary).prod := by
    induction l with
    | nil =>
      apply Subtype.ext
      ext i j
      rw [List.prod_nil, List.map_nil, List.prod_nil, Submonoid.coe_one,
        permutationUnitary_apply, Matrix.one_apply]
      rfl
    | cons e es ih =>
      rw [prod_cons, map_cons, prod_cons, permutationUnitary_mul, ih]
  apply Subtype.ext
  rw [fullReg_embedUnitary_groverParallelMarkingOracle, parallelMarkPerm, hprod,
    Submonoid.coe_list_prod]
  simp only [List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ ↦ ?_)
  simp only [Function.comp_apply, groverSetMarkingOracle, ← embedUnitary_permutationUnitary,
    embedUnitary_val]
theorem parallelMarkPerm_apply_eq_appPerms {n m : ℕ} (T : Finset (Fin (2 ^ n)))
    (z : Fin (2 ^ (m * (n + 1)))) :
    parallelMarkPerm n m T z = appPerms (finRange m) (markPerm T) z := by
  unfold parallelMarkPerm appPerms
  generalize finRange m = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [map_cons, prod_cons, List.foldr_cons, Equiv.Perm.mul_apply, ih,
      liftPerm_apply_eq_replaceIndex]
theorem markPerm_mul_markPerm_of_subset {n : ℕ} {T S : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) :
    markPerm T * markPerm S = markPerm (S \ T) := by
  ext v : 1
  apply (splitBasisEquiv n 1).injective
  rw [Equiv.Perm.mul_apply, splitBasisEquiv_markPerm, splitBasisEquiv_markPerm,
    splitBasisEquiv_markPerm]
  refine Prod.ext rfl ?_
  set x := (splitBasisEquiv n 1 v).1
  set b := (splitBasisEquiv n 1 v).2
  by_cases hT : x ∈ T
  · have hS : x ∈ S := hTS hT
    have hST : x ∉ S \ T := fun h ↦ (Finset.mem_sdiff.mp h).2 hT
    simp only [hT, hS, hST, ↓reduceIte, add_zero]
    refine Fin.ext ?_; change ((b.val + 1) % 2 + 1) % 2 = b.val
    have := b.isLt; omega
  · have hST : x ∈ S \ T ↔ x ∈ S := by simp [Finset.mem_sdiff, hT]
    simp [hT, hST]
theorem parallelMarkPerm_mul_of_subset {n m : ℕ} {T S : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) :
    parallelMarkPerm n m T * parallelMarkPerm n m S = parallelMarkPerm n m (S \ T) := by
  unfold parallelMarkPerm
  let f (A : Finset (Fin (2 ^ n))) (l : List (Fin m)) :=
    (l.map fun i ↦ liftPerm (slotReg n m i) (markPerm A)).prod
  have hcomm {i : Fin m} {l : List (Fin m)} (hi : i ∉ l) (A B : Finset (Fin (2 ^ n))) :
      liftPerm (slotReg n m i) (markPerm A) * f B l =
        f B l * liftPerm (slotReg n m i) (markPerm A) := by
    induction l with
    | nil => simp [f]
    | cons j l ih =>
      simp only [List.mem_cons, not_or] at hi
      dsimp only [f] at *
      rw [map_cons, prod_cons, ← mul_assoc,
        liftPerm_comm_of_disjoint (slotReg_disjointWires hi.1), mul_assoc, ih hi.2, ← mul_assoc]
  have hmul {l : List (Fin m)} (hl : l.Nodup) :
      f T l * f S l = f (S \ T) l := by
    induction l with
    | nil => simp [f]
    | cons i l ih =>
      rcases List.nodup_cons.mp hl with ⟨hil, hl'⟩
      dsimp only [f] at *
      have hlift :
          liftPerm (slotReg n m i) (markPerm T) * liftPerm (slotReg n m i) (markPerm S) =
            liftPerm (slotReg n m i) (markPerm (S \ T)) := by
        apply Equiv.ext
        intro z
        apply (slotReg n m i).basisSplitEquiv.injective
        simp [liftPerm, Prod.map, ← markPerm_mul_markPerm_of_subset hTS]
      rw [map_cons, prod_cons, map_cons, prod_cons, map_cons, prod_cons,
        mul_assoc, ← mul_assoc (f T l), ← hcomm hil S T, mul_assoc, ih hl',
        ← mul_assoc, hlift]
  exact hmul (List.nodup_finRange m)
/-- `S`-independent reversible unmarking permutation comparing all `m` oracle slots in
  `workReg`
  against the active `memReg` slots `active`. -/
noncomputable def unmarkPerm (n m k : ℕ) (active : Finset (Fin k)) :
    Perm (Fin (2 ^ (m * (n + 1) + k * n))) :=
  (lowHighEquiv (m * (n + 1)) (k * n)).trans <|
    (Equiv.prodComm _ _).trans <|
      (Equiv.prodShear (.refl _) (fun μ ↦ parallelMarkPerm n m (memSeen n k active μ))).trans <|
        (Equiv.prodComm _ _).trans (lowHighEquiv (m * (n + 1)) (k * n)).symm
@[simp]
theorem lowHighEquiv_unmarkPerm (n m k : ℕ) (active : Finset (Fin k))
    (z : Fin (2 ^ (m * (n + 1) + k * n))) :
    lowHighEquiv (m * (n + 1)) (k * n) (unmarkPerm n m k active z) =
      (parallelMarkPerm n m (memSeen n k active (lowHighEquiv (m * (n + 1)) (k * n) z).2)
        (lowHighEquiv (m * (n + 1)) (k * n) z).1,
        (lowHighEquiv (m * (n + 1)) (k * n) z).2) := by
  simp [unmarkPerm]
theorem permutationUnitary_unmarkPerm_mulVec_workMemState {n m k : ℕ}
    (active : Finset (Fin k)) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n))) :
    (permutationUnitary (unmarkPerm n m k active)).1 *ᵥ workMemState ψ (single μ 1) =
      workMemState ((permutationUnitary (parallelMarkPerm n m (memSeen n k active μ))).1 *ᵥ ψ)
        (single μ 1) := by
  funext z
  rw [Matrix.mulVec, dotProduct]
  let eμ : Fin (2 ^ (k * n)) → ℂ := single μ 1
  let g (y : Fin (2 ^ (m * (n + 1) + k * n))) : ℂ :=
    (permutationUnitary (unmarkPerm n m k active)).1 z y * workMemState ψ eμ y
  change ∑ y, g y = _
  rw [← (lowHighEquiv (m * (n + 1)) (k * n)).symm.sum_comp g, sum_prod_type]
  dsimp only [g, workMemState]
  simp_rw [Equiv.apply_symm_apply]
  have hsum (w : Fin (2 ^ (m * (n + 1)))) :
      (∑ μ' : Fin (2 ^ (k * n)),
        (permutationUnitary (unmarkPerm n m k active)).1 z
            ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w, μ')) *
          (ψ w * eμ μ')) =
        ((permutationUnitary (parallelMarkPerm n m (memSeen n k active μ))).1
            (lowHighEquiv (m * (n + 1)) (k * n) z).1 w * ψ w) *
          eμ (lowHighEquiv (m * (n + 1)) (k * n) z).2 := by
    dsimp only [eμ]
    rw [sum_eq_single μ (fun μ' hμ' ↦ by rw [Pi.single_eq_of_ne hμ', mul_zero, mul_zero])]
    rw [Pi.single_eq_same, mul_one, permutationUnitary_apply, permutationUnitary_apply]
    have heq :
        (z = unmarkPerm n m k active ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w, μ))) ↔
          ((lowHighEquiv (m * (n + 1)) (k * n) z).1 =
              parallelMarkPerm n m (memSeen n k active μ) w ∧
            (lowHighEquiv (m * (n + 1)) (k * n) z).2 = μ) := by
      rw [← (lowHighEquiv (m * (n + 1)) (k * n)).apply_eq_iff_eq, lowHighEquiv_unmarkPerm,
        Equiv.apply_symm_apply, Prod.ext_iff]
    by_cases h2 : (lowHighEquiv (m * (n + 1)) (k * n) z).2 = μ
    · rw [h2, Pi.single_eq_same, mul_one, if_congr (heq.trans (and_iff_left h2)) rfl rfl]
    · rw [Pi.single_eq_of_ne h2, mul_zero,
        ite_eq_right (fun hz ↦ h2 (heq.mp hz).2), zero_mul]
  simp_rw [hsum, ← Finset.sum_mul]
  rfl
theorem unmark_mul_parallelOracle_workMemState {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k))
    (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k active μ ⊆ S) :
    (permutationUnitary (unmarkPerm n m k active)).1 *ᵥ
        ((lowBlock (m * (n + 1)) (k * n)).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ
            workMemState ψ (single μ 1)) =
      workMemState
        (((fullReg n m).embedUnitary
          (groverParallelMarkingOracle m (S \ memSeen n k active μ))).1 *ᵥ ψ)
        (single μ 1) := by
  rw [embedMatrix_lowBlock_mulVec_workMemState,
    permutationUnitary_unmarkPerm_mulVec_workMemState,
    fullReg_embedUnitary_eq_permutationUnitary S,
    fullReg_embedUnitary_eq_permutationUnitary (S \ memSeen n k active μ),
    mulVec_mulVec, ← Submonoid.coe_mul, ← permutationUnitary_mul,
    parallelMarkPerm_mul_of_subset hsub]
/-- Single deflated parallel marking-oracle call on `Q` qubits (`CostBound... 1`). -/
noncomputable def deflatedOracle {Var : Type} {n m k Q : ℕ}
    (hQ : m * (n + 1) + k * n ≤ Q) (active : Finset (Fin k)) :
    OracleCirc Var Q ((n + 1) * m) :=
  .seq (.oracle (workFullReg n m Q (by omega)))
    (.step (phaseTag ((workMemReg n m k Q hQ).embedUnitary
      (permutationUnitary (unmarkPerm n m k active)))))
/-- Single deflated odd-parity phase-oracle step on `Q` qubits (`CostBound... 1`). -/
noncomputable def deflatedPhaseStep {Var : Type} {n m k Q : ℕ}
    (hQ : m * (n + 1) + k * n ≤ Q) (active : Finset (Fin k)) :
    OracleCirc Var Q ((n + 1) * m) :=
  let fc := (workReg n m Q (by omega)).embedUnitary (flagConj n m)
  .seq (.step (phaseTag fc)) (.seq (deflatedOracle hQ active) (.step (phaseTag fc)))
theorem costBound_deflatedOracle {Var : Type} [DecidableEq Var] {n m k Q : ℕ}
    (hQ : m * (n + 1) + k * n ≤ Q) (active : Finset (Fin k))
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((deflatedOracle hQ active).compile qAssign (groverParallelMarkingOracle m S)) 1 := by
  unfold deflatedOracle
  dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hcall := CostBound.qAssign (Var := Var)
    (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    ((workFullReg n m Q (by omega)).embedUnitary (groverParallelMarkingOracle m S))
  rw [CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, Nat.cast_one] at hcall
  have htag := costBound_qAssign_phaseTag (Var := Var) hor
    ((workMemReg n m k Q hQ).embedUnitary (permutationUnitary (unmarkPerm n m k active)))
  simpa using hcall.seq htag
theorem costBound_deflatedPhaseStep {Var : Type} [DecidableEq Var] {n m k Q : ℕ}
    (hQ : m * (n + 1) + k * n ≤ Q) (active : Finset (Fin k))
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((deflatedPhaseStep hQ active).compile qAssign (groverParallelMarkingOracle m S)) 1 := by
  unfold deflatedPhaseStep
  dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have htag := costBound_qAssign_phaseTag (Var := Var) hor
    ((workReg n m Q (by omega)).embedUnitary (flagConj n m))
  simpa using htag.seq ((costBound_deflatedOracle hQ active S).seq htag)
theorem deflatedPhaseMat_mulVec_workMemState {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k))
    (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k active μ ⊆ S) :
    let W := m * (n + 1)
    let M := k * n
    let fc := (lowBlock W M).embedMatrix (flagConj n m).1
    let orac := (lowBlock W M).embedMatrix
      ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
    let unm := (permutationUnitary (unmarkPerm n m k active)).1
    (fc * unm * orac * fc) *ᵥ workMemState ψ (single μ 1) =
      workMemState (sDiagM n m (S \ memSeen n k active μ) *ᵥ ψ) (single μ 1) := by
  intro W M fc orac unm
  dsimp only [fc, orac, unm]
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    embedMatrix_lowBlock_mulVec_workMemState,
    unmark_mul_parallelOracle_workMemState active _ μ hsub,
    embedMatrix_lowBlock_mulVec_workMemState, mulVec_mulVec, mulVec_mulVec,
    flagConj_mul_embed_mul_flagConj]
/- ## `b`-Group Slot Partition (`b * g = m`), `Fin.find` Readout, and `Sym(R)` Uniformity -/

/-- Contiguous `(g * (n + 1))`-qubit subregister for group `c: Fin b` when `b * g = m`. -/
abbrev groupReg {n m b g : ℕ} (hbg : b * g = m) (c : Fin b) :
    QRegister (g * (n + 1)) (m * (n + 1)) :=
  QRegister.block (c.val * (g * (n + 1))) (g * (n + 1)) <| by
    calc c.val * (g * (n + 1)) + g * (n + 1)
        = (c.val + 1) * g * (n + 1) := by ring
      _ ≤ (b * g) * (n + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right g (Nat.succ_le_of_lt c.isLt))
      _ = m * (n + 1) := by rw [hbg]
theorem groupReg_disjointWires {n m b g : ℕ} (hbg : b * g = m) {c₁ c₂ : Fin b} (hne : c₁ ≠ c₂) :
    (groupReg (n := n) hbg c₁).DisjointWires (groupReg (n := n) hbg c₂) := by
  refine QRegister.disjoint_iff.mpr fun w₁ w₂ heq ↦ ?_
  have hw := congrArg Fin.val heq
  simp only [groupReg, QRegister.block_apply_val] at hw
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have hle := Nat.mul_le_mul_right (g * (n + 1)) (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at hle
    have h1 := w₁.isLt
    omega
  · have hle := Nat.mul_le_mul_right (g * (n + 1)) (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at hle
    have h2 := w₂.isLt
    omega
theorem groupReg_compose_slotReg {n m b g : ℕ} (hbg : b * g = m) (c : Fin b) (j : Fin g) :
    (groupReg (n := n) hbg c).compose (slotReg n g j) =
      slotReg n m (finCongr hbg (finProdFinEquiv (c, j))) := by
  ext w
  change ((groupReg (n := n) hbg c) (slotReg n g j w)).val =
    (slotReg n m (finCongr hbg (finProdFinEquiv (c, j))) w).val
  simp only [groupReg, slotReg, QRegister.block_apply_val, finCongr_apply, Fin.val_cast,
    finProdFinEquiv_apply_val]
  ring
theorem sDiagM_eq_prod_groupReg {n m b g : ℕ} (hbg : b * g = m) (R : Finset (Fin (2 ^ n))) :
    sDiagM n m R =
      ((finRange b).map fun c ↦ (groupReg hbg c).embedMatrix (sDiagM n g R)).prod := by
  have hprod_diag (l : List (Fin b)) :
      ((l.map fun c ↦ (groupReg hbg c).embedMatrix (sDiagM n g R)).prod) =
        diagonal fun z ↦
          (l.map fun c ↦
            ∏ j : Fin g,
              slotDiag n R
                ((slotReg n g j).extractIndex ((groupReg hbg c).extractIndex z))).prod := by
    induction l with
    | nil => simp [Matrix.diagonal_one]
    | cons c l ih =>
      rw [map_cons, prod_cons, ih, sDiagM, QRegister.embedMatrix_diagonal,
        Matrix.diagonal_mul_diagonal]
      rfl
  rw [hprod_diag, sDiagM]
  refine congrArg diagonal (funext fun z ↦ ?_)
  rw [← Fin.prod_univ_def]
  let e : Fin b × Fin g ≃ Fin m := finProdFinEquiv.trans (finCongr hbg)
  rw [← e.prod_comp, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun c _ ↦ Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← QRegister.extractIndex_compose, groupReg_compose_slotReg]
  rfl
theorem extractIndex_slotReg_parallelMarkPerm {n m : ℕ} (R : Finset (Fin (2 ^ n)))
    (u : Fin (2 ^ (m * (n + 1)))) (i : Fin m) :
    (slotReg n m i).extractIndex (parallelMarkPerm n m R u) =
      markPerm R ((slotReg n m i).extractIndex u) := by
  rw [parallelMarkPerm_apply_eq_appPerms]
  suffices ∀ l : List (Fin m), l.Nodup →
      (slotReg n m i).extractIndex (appPerms l (markPerm R) u) =
        if i ∈ l then markPerm R ((slotReg n m i).extractIndex u)
        else (slotReg n m i).extractIndex u by
    simpa [mem_finRange] using this (finRange m) (List.nodup_finRange m)
  intro l hl
  induction l with
  | nil => simp [appPerms]
  | cons a l ih =>
    rcases List.nodup_cons.mp hl with ⟨hal, hl'⟩
    rw [appPerms, List.foldr_cons]
    by_cases hia : i = a
    · subst hia
      rw [QRegister.extractIndex_replaceIndex, ih hl', ite_eq_right hal,
        ite_eq_left List.mem_cons_self]
    · rw [QRegister.extractIndex_replaceIndex_of_disjoint _ _ (slotReg_disjointWires hia),
        ih hl']
      simp [List.mem_cons, hia]
theorem extractIndex_groupReg_parallelMarkPerm {n m b g : ℕ} (hbg : b * g = m)
    (R : Finset (Fin (2 ^ n))) (w : Fin (2 ^ (m * (n + 1)))) (c : Fin b) :
    (groupReg hbg c).extractIndex (parallelMarkPerm n m R w) =
      parallelMarkPerm n g R ((groupReg hbg c).extractIndex w) := by
  apply (basisBits (g * (n + 1))).injective
  funext q
  obtain ⟨⟨j, r⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [← slotReg_apply n g j r, ← QRegister.basisBits_extractIndex,
    ← QRegister.basisBits_extractIndex, ← QRegister.extractIndex_compose,
    groupReg_compose_slotReg, extractIndex_slotReg_parallelMarkPerm,
    ← groupReg_compose_slotReg, QRegister.extractIndex_compose,
    extractIndex_slotReg_parallelMarkPerm]
/-- Computable odd-parity group readout via `Fin.find`: returns `some x_j` for the least
  slot `j`
  with `slotFlag n g z j = 1` when the `g` slot flags have odd parity, and `none` otherwise. -/
def firstMarkedAddr (n g : ℕ) (z : Fin (2 ^ (g * (n + 1)))) : Option (Fin (2 ^ n)) :=
  if hodd : (∏ j : Fin g, if slotFlag n g z j = 1 then (-1 : ℤ) else 1) = -1 then
    some (slotAddr n g z (Fin.find (fun j : Fin g ↦ slotFlag n g z j = 1) (by
      by_contra! hall
      exact absurd (hodd.symm.trans (Finset.prod_eq_one fun j _ ↦ ite_eq_right (hall j)))
        (by decide))))
  else none
/-- Idealized `Fin.find` first-hit map on `g`-tuples `u ∈ oddSet n g R` (`none` outside
  `oddSet`). -/
def firstTupleHit (n g : ℕ) (R : Finset (Fin (2 ^ n)))
    (u : Fin (2 ^ (g * n))) : Option (Fin (2 ^ n)) :=
  if hodd : u ∈ oddSet n g R then
    some (addrEquiv n g u (Fin.find (fun j : Fin g ↦ addrEquiv n g u j ∈ R) (by
      have hp : (∏ j : Fin g, if addrEquiv n g u j ∈ R then (-1 : ℤ) else 1) = -1 :=
        (Finset.mem_filter.mp hodd).2
      by_contra! hall
      exact absurd (hp.symm.trans (Finset.prod_eq_one fun j _ ↦ ite_eq_right (hall j)))
        (by decide))))
  else none
theorem firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit {n g : ℕ}
    (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (g * (n + 1))))
    (hE : ((addrReg n g).basisSplitEquiv z).2 = 0) :
    firstMarkedAddr n g (parallelMarkPerm n g R z) =
      firstTupleHit n g R ((addrReg n g).extractIndex z) := by
  set u := (addrReg n g).extractIndex z
  set z' := parallelMarkPerm n g R z
  have hslt (j : Fin g) :
      splitBasisEquiv n 1 ((slotReg n g j).extractIndex z') =
        (addrEquiv n g u j, if addrEquiv n g u j ∈ R then 1 else 0) := by
    rw [extractIndex_slotReg_parallelMarkPerm, splitBasisEquiv_markPerm,
      show (splitBasisEquiv n 1 ((slotReg n g j).extractIndex z)).1 = addrEquiv n g u j from
        (addrEquiv_extractIndex n g z j).symm,
      show (splitBasisEquiv n 1 ((slotReg n g j).extractIndex z)).2 = 0 from
        slotFlag_eq_zero z hE j,
      zero_add]
  have hfl (j : Fin g) : slotFlag n g z' j = 1 ↔ addrEquiv n g u j ∈ R := by
    simp [slotFlag, hslt j]
  have had (j : Fin g) : slotAddr n g z' j = addrEquiv n g u j := by
    simp [slotAddr, hslt j]
  have hodd_iff :
      ((∏ j : Fin g, if slotFlag n g z' j = 1 then (-1 : ℤ) else 1) = -1) ↔
        u ∈ oddSet n g R := by
    simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.prod_congr rfl fun j _ ↦ if_congr (hfl j) rfl rfl]
  unfold firstMarkedAddr firstTupleHit
  by_cases hu : u ∈ oddSet n g R
  · have hodd : (∏ j : Fin g, if slotFlag n g z' j = 1 then (-1 : ℤ) else 1) = -1 :=
      hodd_iff.mpr hu
    rw [dite_eq_left hodd, dite_eq_left hu]
    congr 1
    rw [had]
    exact congrArg (addrEquiv n g u) (Fin.find_congr' fun {j} ↦ hfl j)
  · have hodd : (∏ j : Fin g, if slotFlag n g z' j = 1 then (-1 : ℤ) else 1) ≠ -1 :=
      mt hodd_iff.mp hu
    rw [dite_eq_right hodd, dite_eq_right hu]
theorem isSome_firstTupleHit_iff {n g : ℕ} (R : Finset (Fin (2 ^ n)))
    (u : Fin (2 ^ (g * n))) :
    (firstTupleHit n g R u).isSome ↔ u ∈ oddSet n g R := by
  unfold firstTupleHit
  split_ifs with h <;> simp [h]
theorem mem_of_firstTupleHit_eq_some {n g : ℕ} {R : Finset (Fin (2 ^ n))}
    {u : Fin (2 ^ (g * n))} {x : Fin (2 ^ n)}
    (hx : firstTupleHit n g R u = some x) :
    u ∈ oddSet n g R ∧ x ∈ R := by
  unfold firstTupleHit at hx
  split_ifs at hx with hu
  have hxeq := Option.some.inj hx
  rw [← hxeq]
  exact ⟨hu, Fin.find_spec (p := fun j : Fin g ↦ addrEquiv n g u j ∈ R) _⟩
theorem card_oddSet_filter_firstTupleHit_eq {n g : ℕ} {R : Finset (Fin (2 ^ n))}
    {x y : Fin (2 ^ n)} (hx : x ∈ R) (hy : y ∈ R) :
    ((oddSet n g R).filter fun u ↦ firstTupleHit n g R u = some x).card =
      ((oddSet n g R).filter fun u ↦ firstTupleHit n g R u = some y).card := by
  let τ : Perm (Fin (2 ^ n)) := Equiv.swap x y
  have hτR (a : Fin (2 ^ n)) : τ a ∈ R ↔ a ∈ R := by
    dsimp only [τ]
    by_cases hax : a = x
    · subst hax
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ ↦ hx, fun _ ↦ hy⟩
    · by_cases hay : a = y
      · subst hay
        rw [Equiv.swap_apply_right]
        exact ⟨fun _ ↦ hy, fun _ ↦ hx⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hax hay]
  let φ (u : Fin (2 ^ (g * n))) : Fin (2 ^ (g * n)) :=
    (addrEquiv n g).symm (fun j ↦ τ (addrEquiv n g u j))
  have hφ_inv (u : Fin (2 ^ (g * n))) : φ (φ u) = u := by
    apply (addrEquiv n g).injective
    funext j
    dsimp only [φ, τ]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.swap_apply_self]
  have hφ_odd (u : Fin (2 ^ (g * n))) : φ u ∈ oddSet n g R ↔ u ∈ oddSet n g R := by
    simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and, φ, Equiv.apply_symm_apply]
    rw [Finset.prod_congr rfl fun j _ ↦ if_congr (hτR _) rfl rfl]
  have hφ_app (u : Fin (2 ^ (g * n))) (j : Fin g) :
      addrEquiv n g (φ u) j = τ (addrEquiv n g u j) := by
    dsimp only [φ]
    rw [Equiv.apply_symm_apply]
  have hφ_hit (u : Fin (2 ^ (g * n))) :
      firstTupleHit n g R (φ u) = (firstTupleHit n g R u).map τ := by
    unfold firstTupleHit
    by_cases hu : u ∈ oddSet n g R
    · have hφu : φ u ∈ oddSet n g R := (hφ_odd u).mpr hu
      rw [dite_eq_left hφu, dite_eq_left hu, Option.map_some]
      congr 1
      rw [hφ_app u]
      refine congrArg (fun j ↦ τ (addrEquiv n g u j)) (Fin.find_congr' fun {j} ↦ ?_)
      rw [hφ_app u]
      exact hτR _
    · have hφu : φ u ∉ oddSet n g R := mt (hφ_odd u).mp hu
      rw [dite_eq_right hφu, dite_eq_right hu, Option.map_none]
  refine Finset.card_bij (fun u _ ↦ φ u) (fun u hu ↦ ?_) (fun u₁ _ u₂ _ heq ↦ ?_) (fun v hv ↦ ?_)
  · rcases Finset.mem_filter.mp hu with ⟨hu_odd, hu_hit⟩
    refine Finset.mem_filter.mpr ⟨(hφ_odd u).mpr hu_odd, ?_⟩
    rw [hφ_hit, hu_hit, Option.map_some]
    simp [τ]
  · rw [← hφ_inv u₁, heq, hφ_inv u₂]
  · rcases Finset.mem_filter.mp hv with ⟨hv_odd, hv_hit⟩
    refine ⟨φ v, Finset.mem_filter.mpr ⟨(hφ_odd v).mpr hv_odd, ?_⟩, hφ_inv v⟩
    rw [hφ_hit, hv_hit, Option.map_some]
    simp [τ]
theorem card_mul_card_oddSet_filter_firstTupleHit {n g : ℕ} {R : Finset (Fin (2 ^ n))}
    {x : Fin (2 ^ n)} (hx : x ∈ R) :
    R.card * ((oddSet n g R).filter fun u ↦ firstTupleHit n g R u = some x).card =
      (oddSet n g R).card := by
  have hpart :
      (oddSet n g R).card =
        ∑ y ∈ R, ((oddSet n g R).filter fun u ↦ firstTupleHit n g R u = some y).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext u
      constructor
      · intro hu
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((isSome_firstTupleHit_iff R u).mpr hu)
        exact Finset.mem_biUnion.mpr ⟨y, (mem_of_firstTupleHit_eq_some hy).2,
          Finset.mem_filter.mpr ⟨hu, hy⟩⟩
      · intro hu
        rcases Finset.mem_biUnion.mp hu with ⟨y, _, huy⟩
        exact (Finset.mem_filter.mp huy).1
    · intro y₁ _ y₂ _ hne
      refine Finset.disjoint_left.mpr fun u hu₁ hu₂ ↦ ?_
      have h1 := (Finset.mem_filter.mp hu₁).2
      have h2 := (Finset.mem_filter.mp hu₂).2
      exact hne (Option.some.inj (h1.symm.trans h2))
  rw [hpart, Finset.sum_congr rfl fun y hy ↦ (card_oddSet_filter_firstTupleHit_eq hx hy).symm,
    Finset.sum_const, smul_eq_mul]
/-- Deduplicated list of distinct marked addresses discovered across all `b` groups of `g`
  slots. -/
def groupHits {n m b g : ℕ} (hbg : b * g = m) (w : Fin (2 ^ (m * (n + 1)))) :
    List (Fin (2 ^ n)) :=
  ((finRange b).filterMap fun c ↦ firstMarkedAddr n g ((groupReg hbg c).extractIndex w)).dedup
theorem nodup_groupHits {n m b g : ℕ} (hbg : b * g = m) (w : Fin (2 ^ (m * (n + 1)))) :
    (groupHits hbg w).Nodup :=
  List.nodup_dedup _
theorem mem_of_mem_groupHits_parallelMarkPerm {n m b g : ℕ} (hbg : b * g = m)
    {R : Finset (Fin (2 ^ n))} {w : Fin (2 ^ (m * (n + 1)))}
    (hflags : ∀ c : Fin b, ((addrReg n g).basisSplitEquiv ((groupReg hbg c).extractIndex w)).2 = 0)
    {x : Fin (2 ^ n)} (hx : x ∈ groupHits hbg (parallelMarkPerm n m R w)) :
    x ∈ R := by
  unfold groupHits at hx
  rw [List.mem_dedup, List.mem_filterMap] at hx
  obtain ⟨c, _, hc⟩ := hx
  rw [extractIndex_groupReg_parallelMarkPerm,
    firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R _ (hflags c)] at hc
  exact (mem_of_firstTupleHit_eq_some hc).2
end QuantumComputation.Specs.GroverSol
end
end Sec_FindAllBridge
section Sec_SubsetEigLock
@[expose] public section
namespace QuantumComputation.Specs.GroverSol
open Operator Real
open QRegister (tensorState)
open Matrix (diagonal mulVec_diagonal star_eq_conjTranspose conjTranspose_apply)
open Complex (normSq)
open Pi (single)
open scoped Matrix NNReal NNRat
/- ## Grid Upper Bound and Harmonic Decomposition of `vanillaFindAllCost` -/

theorem le_1024_of_mem_groverGrid {x : ℕ} (hx : x ∈ groverGrid) : x ≤ 1024 := by
  simp only [groverGrid, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact (Nat.pow_le_pow_right (by omega) (by omega : i ≤ 10)).trans (by norm_num)
theorem vanillaFindAllCost_eq_sum_vanillaFindAnyCost (n m k : ℕ) :
    vanillaFindAllCost n m k = ∑ s : Fin k, vanillaFindAnyCost n m (k - s.val) := by
  unfold vanillaFindAllCost groverHarmonicSqrtSum vanillaFindAnyCost
  rw [Finset.mul_sum, Finset.sum_mul]
  have hterm (r : ℕ) :
      π / 4 * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (m : ℝ)) =
        π / 4 * √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) := by
    rw [mul_assoc, one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 2
    rw [inv_mul_eq_div, div_div]
  simp_rw [hterm]
  symm
  refine Finset.sum_bij (fun (s : Fin k) _ ↦ k - s.val)
    (fun s _ ↦ Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    (fun s₁ _ s₂ _ h ↦ Fin.ext (by omega))
    (fun r hr ↦ ?_)
    (fun _ _ ↦ rfl)
  rcases Finset.mem_Icc.mp hr with ⟨hr1, hrk⟩
  exact ⟨⟨k - r, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
/- ## Positivity and Collision Bounds for `oddFrac` -/

theorem oddFrac_pos_lt_one {n m r : ℕ} (hm : 1 ≤ m) (hr1 : 1 ≤ r) (hrN : r < 2 ^ n) :
    0 < oddFrac n m r ∧ oddFrac n m r < 1 := by
  unfold oddFrac
  set y : ℝ := 1 - 2 * (r : ℝ) / (2 ^ n : ℝ)
  have hN : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hr_lt : (r : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hrN
  have hy_lt : y < 1 := by
    dsimp only [y]
    linarith [div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr_pos) hN]
  have hy_gt : -1 < y := by
    dsimp only [y]
    have h2 : 2 * (r : ℝ) / (2 ^ n : ℝ) < 2 := by
      rw [div_lt_iff₀ hN]
      linarith
    linarith
  have habs : |y| < 1 := abs_lt.mpr ⟨hy_gt, hy_lt⟩
  have hpow_abs : |y ^ m| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg y) habs (by omega)
  rcases abs_lt.mp hpow_abs with ⟨hym_gt, hym_lt⟩
  exact ⟨by linarith, by linarith⟩
theorem one_sub_pow_bounds (m : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - (m : ℝ) * y ≤ (1 - y) ^ m ∧
      (1 - y) ^ m ≤ 1 - (m : ℝ) * y + ((m : ℝ) * y) ^ 2 / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1y : 0 ≤ 1 - y := by linarith
    rcases ih with ⟨ih_lo, ih_hi⟩
    push_cast
    constructor
    · have hmul := mul_le_mul_of_nonneg_right ih_lo h1y
      rw [pow_succ]
      nlinarith [sq_nonneg y]
    · have hmul := mul_le_mul_of_nonneg_right ih_hi h1y
      rw [pow_succ]
      have hdiff :
          (1 - ((m : ℝ) + 1) * y + (((m : ℝ) + 1) * y) ^ 2 / 2) -
            (1 - (m : ℝ) * y + ((m : ℝ) * y) ^ 2 / 2) * (1 - y) =
          y ^ 2 / 2 + (m : ℝ) ^ 2 * y ^ 3 / 2 := by ring
      have hnonneg : 0 ≤ y ^ 2 / 2 + (m : ℝ) ^ 2 * y ^ 3 / 2 := by positivity
      linarith
theorem oddFrac_sandwich {n m r : ℕ} (hrN : 2 * r ≤ 2 ^ n) :
    let p₀ : ℝ := ((m : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)
    p₀ * (1 - p₀) ≤ oddFrac n m r ∧ oddFrac n m r ≤ p₀ := by
  intro p₀
  have hN : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  set y : ℝ := 2 * (r : ℝ) / (2 ^ n : ℝ)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by
    dsimp only [y]
    rw [div_le_one hN]
    exact_mod_cast hrN
  have hmy : (m : ℝ) * y = 2 * p₀ := by
    dsimp only [y, p₀]
    ring
  rcases one_sub_pow_bounds m hy0 hy1 with ⟨hlo, hhi⟩
  rw [hmy] at hlo hhi
  unfold oddFrac
  change p₀ * (1 - p₀) ≤ (1 - (1 - y) ^ m) / 2 ∧ (1 - (1 - y) ^ m) / 2 ≤ p₀
  exact ⟨by nlinarith, by linarith⟩
/- ## Density-Parametrized Stationary Stationary-chord Schedule and Query Bounds -/

/-- Half-angle `θ = arcsin(√p)` for marked-subset density `p`. -/
noncomputable def subHalfAngle (p : ℝ) : ℝ :=
  arcsin √p
/-- Asymptotically optimal initial Grover schedule `⌊(π / 8) / √p⌋₊`. -/
noncomputable def subSchedule (p : ℝ) : ℕ :=
  ⌊π / 8 * (1 / √p)⌋₊
/-- Ratio of unmarked amplitudes across one Grover step at half-angle `subHalfAngle p`. -/
noncomputable def subNonTargetRatio (p : ℝ) (K : ℕ) : ℝ :=
  cos ((2 * (K : ℝ) + 3) * subHalfAngle p) / cos ((2 * (K : ℝ) + 1) * subHalfAngle p)
/-- Weak-measurement attenuation parameter `s` locking onto `subsetGroverState` at `K`. -/
noncomputable def subTargetRatio (p : ℝ) (K : ℕ) : ℝ :=
  subNonTargetRatio p K * sin ((2 * (K : ℝ) + 1) * subHalfAngle p) /
    sin ((2 * (K : ℝ) + 3) * subHalfAngle p)
/-- Per-iteration survival probability `q = subNonTargetRatio p K ^ 2` of the recovery loop. -/
noncomputable def subFailProb (p : ℝ) (K : ℕ) : ℝ :=
  subNonTargetRatio p K ^ 2
theorem subFailProb_nonneg (p : ℝ) (K : ℕ) : 0 ≤ subFailProb p K :=
  sq_nonneg _
private lemma cos_sub_sq_sub_cos_add_sq' (x y : ℝ) :
    cos (x - y) ^ 2 - cos (x + y) ^ 2 = sin (2 * x) * sin (2 * y) := by
  rw [cos_sub, cos_add, sin_two_mul, sin_two_mul]
  ring
private lemma arcsin_le_add_sq' {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    arcsin x ≤ x + x ^ 2 := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have h3 : x * (1 + x) ^ 3 ≤ 2 := by
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x) (by linarith : 1 + x ≤ 3 / 2) 3]
  rw [arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
    ⟨by nlinarith [pi_gt_three], by nlinarith [pi_gt_three]⟩]
  nlinarith [sin_gt_sub_cube (by positivity : 0 < x + x ^ 2),
    mul_le_mul_of_nonneg_left h3 (sq_nonneg x)]
private lemma cos_sq_sub_cos_sq_subHalfAngle (p : ℝ) (K : ℕ) :
    cos ((2 * (K : ℝ) + 1) * subHalfAngle p) ^ 2 -
        cos ((2 * (K : ℝ) + 3) * subHalfAngle p) ^ 2 =
      2 * sin (subHalfAngle p) * cos (subHalfAngle p) *
        sin ((4 * (K : ℝ) + 4) * subHalfAngle p) := by
  rw [← sin_two_mul, mul_comm (sin _)]
  convert cos_sub_sq_sub_cos_add_sq'
    ((2 * (K : ℝ) + 2) * subHalfAngle p) (subHalfAngle p) using 3 <;> ring_nf
/-- Stationary recovery hypotheses and total stage query bound
  `(K + 1) + (1 - q)⁻¹ + 1 ≤ (π / 8 + 1 / 4) * (1 / √p) + 4`
  whenever `0 < p` and `16 ≤ 1 / √p`. -/
theorem subSchedule_hyps_le {p : ℝ} (hp0 : 0 < p) (hs16 : 16 ≤ 1 / √p) :
    let K := subSchedule p
    (0 < subTargetRatio p K ∧
      subTargetRatio p K < 1 ∧
      sin ((2 * (K : ℝ) + 3) * subHalfAngle p) ≠ 0 ∧
      cos ((2 * (K : ℝ) + 1) * subHalfAngle p) ≠ 0 ∧
      subFailProb p K < 1) ∧
    (K : ℝ) + 2 + (1 - subFailProb p K)⁻¹ ≤
      (π / 8 + 1 / 4) * (1 / √p) + 4 := by
  intro K
  set s := 1 / √p with hs_def
  set x := √p with hx_def
  have hx0 : 0 < x := Real.sqrt_pos.mpr hp0
  have hs0 : 0 < s := by positivity
  have hsx : s * x = 1 := one_div_mul_cancel hx0.ne'
  have hsx2 : s * x ^ 2 = x := by rw [sq, ← mul_assoc, hsx, one_mul]
  have hx1 : x ≤ 1 / 16 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) hs16
    rwa [one_div_one_div] at h
  have hxx : x ^ 2 ≤ x / 16 := by
    rw [sq, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hx1 hx0.le
  set θ := subHalfAngle p with hθ_def
  have hsinθ : sin θ = x := Real.sin_arcsin (by linarith) (by linarith)
  have hθl : x ≤ θ := self_le_arcsin hx0.le (by linarith)
  have hθu : θ ≤ x + x ^ 2 := arcsin_le_add_sq' hx0.le (by linarith)
  have hθ0 : 0 < θ := hx0.trans_le hθl
  have hθ2 : θ ≤ 2 * x := by linarith
  have hk1 : (K : ℝ) ≤ π / 8 * s := Nat.floor_le (by positivity)
  have hk2 : π / 8 * s < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hπ := pi_gt_three
  have hπ' := pi_lt_d2
  have hπsx : π * (s * x) = π := by rw [hsx, mul_one]
  have hπsx2 : π * (s * x ^ 2) = π * x := by rw [hsx2]
  have hφ1 : π / 2 ≤ (4 * (K : ℝ) + 4) * θ := by
    linarith [mul_le_mul_of_nonneg_left hθl (by positivity : (0 : ℝ) ≤ π / 8 * s),
      mul_le_mul_of_nonneg_right hk2.le hθ0.le]
  have hφ2 : (4 * (K : ℝ) + 4) * θ ≤ π / 2 + 6 * x := by
    linarith [mul_le_mul_of_nonneg_left hθu (by linarith : (0 : ℝ) ≤ 4 * (K : ℝ) + 4),
      mul_le_mul_of_nonneg_right hk1 (by positivity : (0 : ℝ) ≤ x + x ^ 2),
      mul_le_mul_of_nonneg_right hπ'.le hx0.le]
  have hcθ_pos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : 0 < sin ((2 * (K : ℝ) + 1) * θ) :=
    sin_pos_of_pos_of_lt_pi (mul_pos (by linarith) hθ0) (by linarith)
  have hc1 : 0 < cos ((2 * (K : ℝ) + 1) * θ) :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc2 : 0 ≤ cos ((2 * (K : ℝ) + 2) * θ) :=
    cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hc3 : 0 < cos ((2 * (K : ℝ) + 3) * θ) :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs3 : 0 < sin ((2 * (K : ℝ) + 3) * θ) :=
    sin_pos_of_pos_of_lt_pi (mul_pos (by linarith) hθ0) (by linarith)
  have hs4 : 0 < sin ((4 * (K : ℝ) + 4) * θ) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1_le_hs3 : sin ((2 * (K : ℝ) + 1) * θ) ≤ sin ((2 * (K : ℝ) + 3) * θ) := by
    have htrig := Real.sin_sub_sin ((2 * (K : ℝ) + 3) * θ) ((2 * (K : ℝ) + 1) * θ)
    rw [show ((2 * (K : ℝ) + 3) * θ - (2 * (K : ℝ) + 1) * θ) / 2 = θ by ring,
      show ((2 * (K : ℝ) + 3) * θ + (2 * (K : ℝ) + 1) * θ) / 2 =
        (2 * (K : ℝ) + 2) * θ by ring] at htrig
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc2) (hsinθ.symm ▸ hx0.le)]
  have hatt0 : 0 < subNonTargetRatio p K := div_pos hc3 hc1
  have hcdiff := cos_sq_sub_cos_sq_subHalfAngle p K
  rw [← hθ_def, hsinθ] at hcdiff
  have hatt1 : subNonTargetRatio p K < 1 := (div_lt_one hc1).2 <|
    lt_of_pow_lt_pow_left₀ 2 hc1.le <| by
      nlinarith [mul_pos (mul_pos hx0 hcθ_pos) hs4]
  have hq_lt1 : subFailProb p K < 1 := pow_lt_one₀ hatt0.le hatt1 two_ne_zero
  have htr_pos : 0 < subTargetRatio p K := by
    rw [subTargetRatio]
    exact div_pos (mul_pos hatt0 hs1) hs3
  have htr_lt1 : subTargetRatio p K < 1 := by
    rw [subTargetRatio, div_lt_one hs3]
    exact (mul_lt_of_lt_one_left hs1 hatt1).trans_le hs1_le_hs3
  refine ⟨⟨htr_pos, htr_lt1, hs3.ne', hc1.ne', hq_lt1⟩, ?_⟩
  have h1q_pos : 0 < 1 - subFailProb p K := sub_pos.mpr hq_lt1
  have hinv_eq : (1 - subFailProb p K)⁻¹ = 1 + subFailProb p K / (1 - subFailProb p K) := by
    field_simp [h1q_pos.ne']
    ring
  have hc1_sq : cos ((2 * (K : ℝ) + 1) * θ) ^ 2 ≠ 0 := pow_ne_zero 2 hc1.ne'
  have hPpos : 0 < 2 * cos θ * sin ((4 * (K : ℝ) + 4) * θ) := by positivity
  have hratio_eq :
      subFailProb p K / (1 - subFailProb p K) =
        cos ((2 * (K : ℝ) + 3) * θ) ^ 2 * s /
          (2 * cos θ * sin ((4 * (K : ℝ) + 4) * θ)) := by
    rw [subFailProb, subNonTargetRatio, ← hθ_def, div_pow, one_sub_div hc1_sq,
      div_div_div_cancel_right₀ hc1_sq, hcdiff]
    have hxs : 2 * x * cos θ * sin ((4 * (K : ℝ) + 4) * θ) =
        (2 * cos θ * sin ((4 * (K : ℝ) + 4) * θ)) / s := by
      rw [eq_div_iff hs0.ne']
      calc 2 * x * cos θ * sin ((4 * (K : ℝ) + 4) * θ) * s
          = 2 * cos θ * sin ((4 * (K : ℝ) + 4) * θ) * (s * x) := by ring
        _ = 2 * cos θ * sin ((4 * (K : ℝ) + 4) * θ) := by rw [hsx, mul_one]
    rw [hxs, div_div_eq_mul_div]
  have hC : cos ((2 * (K : ℝ) + 3) * θ) ^ 2 ≤ 1 / 2 := by
    linarith [cos_sq ((2 * (K : ℝ) + 3) * θ), cos_nonpos_of_pi_div_two_le_of_le
      (x := 2 * ((2 * (K : ℝ) + 3) * θ)) (by linarith) (by linarith)]
  have hcθ : 1 - 2 * x ^ 2 ≤ cos θ := by
    linarith [one_sub_sq_div_two_le_cos (x := θ), pow_le_pow_left₀ hθ0.le hθ2 2]
  have hsφ : 1 - 18 * x ^ 2 ≤ sin ((4 * (K : ℝ) + 4) * θ) := by
    have h := one_sub_sq_div_two_le_cos (x := (4 * (K : ℝ) + 4) * θ - π / 2)
    rw [cos_sub_pi_div_two] at h
    linarith [pow_le_pow_left₀ (by linarith : 0 ≤ (4 * (K : ℝ) + 4) * θ - π / 2)
      (by linarith : (4 * (K : ℝ) + 4) * θ - π / 2 ≤ 6 * x) 2]
  have hP : 2 * (1 - 20 * x ^ 2) ≤ 2 * cos θ * sin ((4 * (K : ℝ) + 4) * θ) := by
    linarith [mul_le_mul hcθ hsφ (by linarith) hcθ_pos.le, pow_nonneg hx0.le 4]
  have hfrac :
      cos ((2 * (K : ℝ) + 3) * θ) ^ 2 * s /
          (2 * cos θ * sin ((4 * (K : ℝ) + 4) * θ)) ≤
        s / 4 + 1 := by
    rw [div_le_iff₀ hPpos]
    linarith [mul_le_mul_of_nonneg_right hC hs0.le,
      mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ s / 4 + 1)]
  rw [hinv_eq, hratio_eq]
  linarith
/-- Certified rational upper bound on `1 / 2 + 1 / π` across all `121/121` cells. -/
def stage1RelCost : ℚ≥0 :=
  514159265358979323847 / 628318530717958647692
theorem stageCost_le_stage1RelCost {n m k r : ℕ} (hn : 200 ≤ n)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    let p := oddFrac n m r
    let K := subSchedule p
    (0 < subTargetRatio p K ∧
      subTargetRatio p K < 1 ∧
      sin ((2 * (K : ℝ) + 3) * subHalfAngle p) ≠ 0 ∧
      cos ((2 * (K : ℝ) + 1) * subHalfAngle p) ≠ 0 ∧
      subFailProb p K < 1) ∧
    (K : ℝ) + 2 + (1 - subFailProb p K)⁻¹ ≤
      (stage1RelCost : ℝ) * vanillaFindAnyCost n m r := by
  intro p K
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  have hr_hi : r ≤ 1024 := hrk.trans hk_hi
  have h2r_le : 2 * r ≤ 2 ^ n := by
    calc 2 * r ≤ 2 * 1024 := by omega
      _ ≤ 2 ^ 200 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hr_lt : r < 2 ^ n := by omega
  have hp_pos : 0 < p := (oddFrac_pos_lt_one hm1 hr1 hr_lt).1
  set p₀ : ℝ := ((m : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)
  set S₀ : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))
  have hmr_pos : (0 : ℝ) < (m : ℝ) * (r : ℝ) := by positivity
  have hmr_le : (m : ℝ) * (r : ℝ) ≤ 2 ^ 20 := by
    have : m * r ≤ 1024 * 1024 := Nat.mul_le_mul hm_hi hr_hi
    calc (m : ℝ) * (r : ℝ) = ((m * r : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((1024 * 1024 : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 ^ 20 := by norm_num
  have h2n_ge : (2 : ℝ) ^ 200 ≤ (2 ^ n : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega) hn
  have hS0_sq : S₀ ^ 2 = (2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)) :=
    Real.sq_sqrt (by positivity)
  have hS0_sq_ge : (2 : ℝ) ^ 180 ≤ S₀ ^ 2 := by
    rw [hS0_sq, le_div_iff₀ hmr_pos]
    calc (2 : ℝ) ^ 180 * ((m : ℝ) * (r : ℝ))
        ≤ (2 : ℝ) ^ 180 * (2 : ℝ) ^ 20 := mul_le_mul_of_nonneg_left hmr_le (by positivity)
      _ = (2 : ℝ) ^ 200 := by norm_num
      _ ≤ (2 ^ n : ℝ) := h2n_ge
  have hS0_ge : (2 : ℝ) ^ 90 ≤ S₀ := by
    have h90 : ((2 : ℝ) ^ 90) ^ 2 = (2 : ℝ) ^ 180 := by norm_num
    nlinarith [Real.sqrt_nonneg ((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))]
  rcases oddFrac_sandwich (m := m) h2r_le with ⟨hp_lo, hp_hi⟩
  change p₀ * (1 - p₀) ≤ p at hp_lo
  change p ≤ p₀ at hp_hi
  have hp0_inv : p₀ * S₀ ^ 2 = 1 := by
    rw [hS0_sq]
    dsimp only [p₀]
    field_simp [hmr_pos.ne']
  have h1_div_sqrt_ge : S₀ ≤ 1 / √p := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hp_pos)]
    have hle : √p ≤ √p₀ := Real.sqrt_le_sqrt hp_hi
    have hmul : S₀ * √p₀ = 1 := by
      have hsq : (S₀ * √p₀) ^ 2 = 1 := by
        rw [mul_pow, hS0_sq, Real.sq_sqrt (by positivity)]
        dsimp only [p₀]
        field_simp [hmr_pos.ne']
      nlinarith [show 0 ≤ S₀ * √p₀ by positivity]
    nlinarith [show (0 : ℝ) ≤ S₀ by positivity]
  have hs16 : 16 ≤ 1 / √p := by
    calc (16 : ℝ) ≤ (2 : ℝ) ^ 90 := by norm_num
      _ ≤ S₀ := hS0_ge
      _ ≤ 1 / √p := h1_div_sqrt_ge
  have h1_div_sqrt_le : 1 / √p ≤ S₀ + 1 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hp_pos)]
    suffices hsq : 1 ≤ ((S₀ + 1) * √p) ^ 2 by
      nlinarith [show 0 ≤ (S₀ + 1) * √p by positivity]
    rw [mul_pow, Real.sq_sqrt hp_pos.le]
    have hp0_eq : p₀ = 1 / S₀ ^ 2 := by
      rw [eq_div_iff (by positivity)]
      exact hp0_inv
    have hpoly : 1 ≤ (S₀ + 1) ^ 2 * (p₀ * (1 - p₀)) := by
      rw [hp0_eq, ← sub_nonneg]
      have hS4 : (0 : ℝ) < S₀ ^ 4 := by positivity
      have hnum :
          (S₀ + 1) ^ 2 * (1 / S₀ ^ 2 * (1 - 1 / S₀ ^ 2)) - 1 =
            (2 * S₀ ^ 3 - 2 * S₀ - 1) / S₀ ^ 4 := by
        field_simp [show S₀ ≠ 0 by positivity]
        ring
      rw [hnum]
      refine div_nonneg ?_ hS4.le
      have hS2 : (2 : ℝ) ≤ S₀ := le_trans (by norm_num) hS0_ge
      nlinarith
    exact hpoly.trans (mul_le_mul_of_nonneg_left hp_lo (sq_nonneg _))
  obtain ⟨hhyps, hqbound⟩ := subSchedule_hyps_le hp_pos hs16
  refine ⟨hhyps, ?_⟩
  have hπ_lo : (314159265358979323846 : ℝ) / 10 ^ 20 < π := by
    simpa [ show (3.14159265358979323846 : ℝ) = 314159265358979323846 / 10 ^ 20 by norm_num ]
      using Real.pi_gt_d20
  have hπ_hi : π < 4 := Real.pi_lt_four
  have hstage_le : (K : ℝ) + 2 + (1 - subFailProb p K)⁻¹ ≤ (π / 8 + 1 / 4) * S₀ + 5 := by
    have h1 : (π / 8 + 1 / 4) * (1 / √p) ≤ (π / 8 + 1 / 4) * (S₀ + 1) :=
      mul_le_mul_of_nonneg_left h1_div_sqrt_le (by positivity)
    linarith
  unfold vanillaFindAnyCost stage1RelCost
  push_cast
  have hc_margin :
      1 / (8 * (10 : ℝ) ^ 20) <
        ((514159265358979323847 : ℝ) / 628318530717958647692) * (π / 4) - (π / 8 + 1 / 4) := by
    have hcoef :
        (0 : ℝ) < (514159265358979323847 : ℝ) / 628318530717958647692 / 4 - 1 / 8 := by
      norm_num
    have hrat :
        ((514159265358979323847 : ℝ) / 628318530717958647692 / 4 - 1 / 8) *
            ((314159265358979323846 : ℝ) / 10 ^ 20) - 1 / 4 =
          1 / (8 * (10 : ℝ) ^ 20) := by
      norm_num
    nlinarith [mul_lt_mul_of_pos_left hπ_lo hcoef]
  have h5 : (5 : ℝ) ≤ (1 / (8 * (10 : ℝ) ^ 20)) * S₀ := by
    calc (5 : ℝ) ≤ (1 / (8 * (10 : ℝ) ^ 20)) * (2 : ℝ) ^ 90 := by norm_num
      _ ≤ (1 / (8 * (10 : ℝ) ^ 20)) * S₀ :=
          mul_le_mul_of_nonneg_left hS0_ge (by positivity)
  have hslack :
      (5 : ℝ) < (((514159265358979323847 : ℝ) / 628318530717958647692) * (π / 4) -
        (π / 8 + 1 / 4)) * S₀ :=
    lt_of_le_of_lt h5 (mul_lt_mul_of_pos_right hc_margin (by positivity))
  linarith
/- ## Subset Grover State and Kraus Eigenvector Analysis -/

/-- Grover state on `2 ^ q` basis states after `t` iterations for marked subset `M`. -/
noncomputable def subsetGroverState {q : ℕ} (M : Finset (Fin (2 ^ q))) : ℕ → Fin (2 ^ q) → ℂ
  | 0 => fun _ ↦ (1 / √(2 ^ q : ℝ) : ℝ)
  | t + 1 => Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ subsetGroverState M t)
/-- Diagonal failure Kraus operator on `Fin (2 ^ q)` scaling `M` by `-s` and `Mᶜ` by `1`. -/
noncomputable def subsetKraus0 {q : ℕ} (M : Finset (Fin (2 ^ q))) (s : ℝ) : Operator (2 ^ q) :=
  diagonal fun u ↦ if u ∈ M then (-s : ℂ) else 1
/-- Diagonal success Kraus operator on `Fin (2 ^ q)` scaling `M` by `-√(1 - s²)` and `Mᶜ` by
  `0`. -/
noncomputable def subsetKraus1 {q : ℕ} (M : Finset (Fin (2 ^ q))) (s : ℝ) : Operator (2 ^ q) :=
  diagonal fun u ↦ if u ∈ M then (-√(1 - s ^ 2) : ℂ) else 0
theorem subsetGroverState_apply {q : ℕ} (M : Finset (Fin (2 ^ q)))
    (h0 : 0 < M.card) (hlt : M.card < 2 ^ q) (t : ℕ) (u : Fin (2 ^ q)) :
    let p : ℝ := (M.card : ℝ) / (2 ^ q : ℝ)
    let θ : ℝ := subHalfAngle p
    subsetGroverState M t u =
      if u ∈ M then ((sin ((2 * (t : ℝ) + 1) * θ) / √(M.card : ℝ) : ℝ) : ℂ)
      else ((cos ((2 * (t : ℝ) + 1) * θ) / √((2 ^ q : ℝ) - (M.card : ℝ)) : ℝ) : ℂ) := by
  set D : ℝ := (2 ^ q : ℝ)
  set cM : ℝ := (M.card : ℝ)
  have hD_pos : 0 < D := by positivity
  have hcM_pos : 0 < cM := by dsimp only [cM]; exact_mod_cast h0
  have hcMc_pos : 0 < D - cM := sub_pos.mpr (by dsimp only [D, cM]; exact_mod_cast hlt)
  set p : ℝ := cM / D
  set θ : ℝ := subHalfAngle p
  have hp0 : 0 < p := div_pos hcM_pos hD_pos
  have hp1 : p < 1 := (div_lt_one hD_pos).mpr (by dsimp only [D, cM]; exact_mod_cast hlt)
  have hsinθ : sin θ = √cM / √D := by
    rw [show θ = arcsin √p from rfl,
      Real.sin_arcsin (by linarith [Real.sqrt_nonneg p])
        (Real.sqrt_le_one.mpr hp1.le),
      Real.sqrt_div hcM_pos.le]
  have hcosθ : cos θ = √(D - cM) / √D := by
    rw [show θ = arcsin √p from rfl, Real.cos_arcsin, Real.sq_sqrt hp0.le]
    have hsub : 1 - p = (D - cM) / D := by
      dsimp only [p]
      field_simp [hD_pos.ne']
    rw [hsub, Real.sqrt_div hcMc_pos.le]
  induction t generalizing u with
  | zero =>
    dsimp only [subsetGroverState]
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
    split_ifs with hu
    · congr 1
      rw [hsinθ, div_div, mul_comm (√D) (√cM), ← div_div,
        div_self (Real.sqrt_pos.mpr hcM_pos).ne']
    · congr 1
      rw [hcosθ, div_div, mul_comm (√D) (√(D - cM)), ← div_div,
        div_self (Real.sqrt_pos.mpr hcMc_pos).ne']
  | succ t ih =>
    dsimp only [subsetGroverState]
    rw [Grover.diffuserMatrix_mulVec]
    set a_t : ℝ := sin ((2 * (t : ℝ) + 1) * θ) / √cM
    set b_t : ℝ := cos ((2 * (t : ℝ) + 1) * θ) / √(D - cM)
    have horac (v : Fin (2 ^ q)) :
        (oracleMat M *ᵥ subsetGroverState M t) v =
          if v ∈ M then ((-a_t : ℝ) : ℂ) else ((b_t : ℝ) : ℂ) := by
      rw [oracleMat, mulVec_diagonal, ih v]
      change (if v ∈ M then (-1 : ℂ) else 1) *
          (if v ∈ M then ((a_t : ℝ) : ℂ) else ((b_t : ℝ) : ℂ)) =
        if v ∈ M then ((-a_t : ℝ) : ℂ) else ((b_t : ℝ) : ℂ)
      by_cases hv : v ∈ M <;> simp [hv, Complex.ofReal_neg]
    have hite (j : Fin (2 ^ q)) :
        (if j ∈ M then ((-a_t : ℝ) : ℂ) else ((b_t : ℝ) : ℂ)) =
          ((b_t : ℝ) : ℂ) + if j ∈ M then ((-a_t - b_t : ℝ) : ℂ) else 0 := by
      by_cases hj : j ∈ M <;> simp [hj]
    have hsum :
        ∑ j : Fin (2 ^ q), (oracleMat M *ᵥ subsetGroverState M t) j =
          ((√D * cos ((2 * (t : ℝ) + 2) * θ) : ℝ) : ℂ) := by
      simp_rw [horac, hite, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      have hreal :
          D * b_t + cM * (-a_t - b_t) = √D * cos ((2 * (t : ℝ) + 2) * θ) := by
        have h1 : cM * a_t = √D * (sin θ * sin ((2 * (t : ℝ) + 1) * θ)) := by
          dsimp only [a_t]
          rw [hsinθ, mul_div_assoc', div_eq_iff (Real.sqrt_pos.mpr hcM_pos).ne']
          calc cM * sin ((2 * (t : ℝ) + 1) * θ)
              = (√cM * √cM) * sin ((2 * (t : ℝ) + 1) * θ) := by
                  rw [Real.mul_self_sqrt hcM_pos.le]
            _ = √D * (√cM / √D * sin ((2 * (t : ℝ) + 1) * θ)) * √cM := by
                  rw [← mul_assoc (√D), mul_div_cancel₀ _ (Real.sqrt_pos.mpr hD_pos).ne']
                  ring
        have h2 : (D - cM) * b_t = √D * (cos θ * cos ((2 * (t : ℝ) + 1) * θ)) := by
          dsimp only [b_t]
          rw [hcosθ, mul_div_assoc', div_eq_iff (Real.sqrt_pos.mpr hcMc_pos).ne']
          calc (D - cM) * cos ((2 * (t : ℝ) + 1) * θ)
              = (√(D - cM) * √(D - cM)) * cos ((2 * (t : ℝ) + 1) * θ) := by
                  rw [Real.mul_self_sqrt hcMc_pos.le]
            _ = √D * (√(D - cM) / √D * cos ((2 * (t : ℝ) + 1) * θ)) * √(D - cM) := by
                  rw [← mul_assoc (√D), mul_div_cancel₀ _ (Real.sqrt_pos.mpr hD_pos).ne']
                  ring
        have hadd : cos ((2 * (t : ℝ) + 2) * θ) =
            cos θ * cos ((2 * (t : ℝ) + 1) * θ) - sin θ * sin ((2 * (t : ℝ) + 1) * θ) := by
          rw [show (2 * (t : ℝ) + 2) * θ = θ + (2 * (t : ℝ) + 1) * θ by ring, Real.cos_add]
        have hexp : D * b_t + cM * (-a_t - b_t) = (D - cM) * b_t - cM * a_t := by ring
        rw [hexp, h2, h1, hadd]
        ring
      rw [← hreal]
      dsimp only [D, cM]
      push_cast
      ring
    rw [hsum, horac u, show (2 : ℂ) / (2 ^ q : ℂ) = ((2 / D : ℝ) : ℂ) by push_cast [D]; rfl,
      show 2 * ((t + 1 : ℕ) : ℝ) + 1 = 2 * (t : ℝ) + 3 by push_cast; ring]
    have h2D : (2 / D) * (√D * cos ((2 * (t : ℝ) + 2) * θ)) =
        (2 / √D) * cos ((2 * (t : ℝ) + 2) * θ) := by
      have h2_eq : 2 / D * √D = 2 / √D := by
        rw [div_mul_eq_mul_div, div_eq_div_iff hD_pos.ne' (Real.sqrt_pos.mpr hD_pos).ne',
          mul_assoc, Real.mul_self_sqrt hD_pos.le]
      rw [← mul_assoc, h2_eq]
    by_cases hu : u ∈ M
    · rw [ite_eq_left hu, ite_eq_left hu, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
      congr 1
      rw [h2D]
      have h2M : 2 / √D = 2 * sin θ / √cM := by
        rw [hsinθ]
        field_simp [(Real.sqrt_pos.mpr hcM_pos).ne', (Real.sqrt_pos.mpr hD_pos).ne']
      have hsin_step : sin ((2 * (t : ℝ) + 3) * θ) =
          2 * sin θ * cos ((2 * (t : ℝ) + 2) * θ) + sin ((2 * (t : ℝ) + 1) * θ) := by
        have hs := Real.sin_sub_sin ((2 * (t : ℝ) + 3) * θ) ((2 * (t : ℝ) + 1) * θ)
        rw [show ((2 * (t : ℝ) + 3) * θ - (2 * (t : ℝ) + 1) * θ) / 2 = θ by ring,
          show ((2 * (t : ℝ) + 3) * θ + (2 * (t : ℝ) + 1) * θ) / 2 =
            (2 * (t : ℝ) + 2) * θ by ring] at hs
        linarith
      dsimp only [a_t]
      rw [h2M, hsin_step]
      ring
    · rw [ite_eq_right hu, ite_eq_right hu, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
      congr 1
      rw [h2D]
      have h2Mc : 2 / √D = 2 * cos θ / √(D - cM) := by
        rw [hcosθ]
        field_simp [(Real.sqrt_pos.mpr hcMc_pos).ne', (Real.sqrt_pos.mpr hD_pos).ne']
      have hcos_step : cos ((2 * (t : ℝ) + 3) * θ) =
          2 * cos θ * cos ((2 * (t : ℝ) + 2) * θ) - cos ((2 * (t : ℝ) + 1) * θ) := by
        have hc := Real.cos_add_cos ((2 * (t : ℝ) + 3) * θ) ((2 * (t : ℝ) + 1) * θ)
        rw [show ((2 * (t : ℝ) + 3) * θ + (2 * (t : ℝ) + 1) * θ) / 2 =
            (2 * (t : ℝ) + 2) * θ by ring,
          show ((2 * (t : ℝ) + 3) * θ - (2 * (t : ℝ) + 1) * θ) / 2 = θ by ring] at hc
        linarith
      dsimp only [b_t]
      rw [h2Mc, hcos_step]
      ring
theorem sum_normSq_subsetGroverState {q : ℕ} (M : Finset (Fin (2 ^ q)))
    (h0 : 0 < M.card) (hlt : M.card < 2 ^ q) (t : ℕ) :
    (∑ u : Fin (2 ^ q), normSq (subsetGroverState M t u)) = 1 ∧
      (∑ u : Fin (2 ^ q), normSq ((oracleMat M *ᵥ subsetGroverState M t) u)) = 1 := by
  set D : ℝ := (2 ^ q : ℝ)
  set cM : ℝ := (M.card : ℝ)
  have hcM_pos : 0 < cM := by dsimp only [cM]; exact_mod_cast h0
  have hcMc_pos : 0 < D - cM := sub_pos.mpr (by dsimp only [D, cM]; exact_mod_cast hlt)
  set θ : ℝ := subHalfAngle (cM / D)
  set s_sq : ℝ := sin ((2 * (t : ℝ) + 1) * θ) ^ 2 / cM
  set c_sq : ℝ := cos ((2 * (t : ℝ) + 1) * θ) ^ 2 / (D - cM)
  have h1 : (∑ u : Fin (2 ^ q), normSq (subsetGroverState M t u)) = 1 := by
    have hterm (u : Fin (2 ^ q)) :
        normSq (subsetGroverState M t u) = c_sq + if u ∈ M then s_sq - c_sq else 0 := by
      rw [subsetGroverState_apply M h0 hlt t u]
      change normSq (if u ∈ M then
          ((sin ((2 * (t : ℝ) + 1) * θ) / √cM : ℝ) : ℂ)
        else ((cos ((2 * (t : ℝ) + 1) * θ) / √(D - cM) : ℝ) : ℂ)) = _
      by_cases hu : u ∈ M
      · rw [ite_eq_left hu, ite_eq_left hu, Complex.normSq_ofReal]
        dsimp only [s_sq, c_sq]
        rw [div_mul_div_comm, Real.mul_self_sqrt hcM_pos.le, ← sq]
        ring
      · rw [ite_eq_right hu, ite_eq_right hu, Complex.normSq_ofReal]
        dsimp only [c_sq]
        rw [div_mul_div_comm, Real.mul_self_sqrt hcMc_pos.le, ← sq, add_zero]
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    push_cast
    change D * c_sq + cM * (s_sq - c_sq) = 1
    have hlin : D * c_sq + cM * (s_sq - c_sq) = cM * s_sq + (D - cM) * c_sq := by ring
    rw [hlin]
    dsimp only [s_sq, c_sq]
    rw [mul_div_cancel₀ _ hcM_pos.ne', mul_div_cancel₀ _ hcMc_pos.ne', Real.sin_sq_add_cos_sq]
  refine ⟨h1, ?_⟩
  rw [← h1]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [oracleMat, mulVec_diagonal]
  by_cases hu : u ∈ M <;> simp [hu]
theorem subsetKraus0_mulVec_subsetGroverState {q : ℕ} (M : Finset (Fin (2 ^ q)))
    (h0 : 0 < M.card) (hlt : M.card < 2 ^ q) (K : ℕ)
    (hsin3 : sin ((2 * (K : ℝ) + 3) * subHalfAngle ((M.card : ℝ) / (2 ^ q : ℝ))) ≠ 0)
    (hcos1 : cos ((2 * (K : ℝ) + 1) * subHalfAngle ((M.card : ℝ) / (2 ^ q : ℝ))) ≠ 0) :
    let p : ℝ := (M.card : ℝ) / (2 ^ q : ℝ)
    subsetKraus0 M (subTargetRatio p K) *ᵥ subsetGroverState M (K + 1) =
      (subNonTargetRatio p K : ℂ) • (oracleMat M *ᵥ subsetGroverState M K) := by
  intro p
  funext u
  rw [subsetKraus0, mulVec_diagonal, Pi.smul_apply, oracleMat, mulVec_diagonal, smul_eq_mul,
    subsetGroverState_apply M h0 hlt (K + 1) u, subsetGroverState_apply M h0 hlt K u,
    show 2 * ((K + 1 : ℕ) : ℝ) + 1 = 2 * (K : ℝ) + 3 by push_cast; ring]
  by_cases hu : u ∈ M
  · simp only [hu, ↓reduceIte]
    have hr :
        -subTargetRatio p K *
            (sin ((2 * (K : ℝ) + 3) * subHalfAngle p) / √(M.card : ℝ)) =
          subNonTargetRatio p K *
            (-1 * (sin ((2 * (K : ℝ) + 1) * subHalfAngle p) / √(M.card : ℝ))) := by
      rw [subTargetRatio, neg_mul, div_mul_div_comm,
        mul_comm (sin ((2 * (K : ℝ) + 3) * subHalfAngle p)), mul_div_mul_right _ _ hsin3]
      ring
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
      show (-↑(subTargetRatio p K) : ℂ) = ((-subTargetRatio p K : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    exact congrArg Complex.ofReal hr
  · simp only [hu, ↓reduceIte, one_mul]
    have hr :
        cos ((2 * (K : ℝ) + 3) * subHalfAngle p) / √((2 ^ q : ℝ) - (M.card : ℝ)) =
          subNonTargetRatio p K *
            (cos ((2 * (K : ℝ) + 1) * subHalfAngle p) / √((2 ^ q : ℝ) - (M.card : ℝ))) := by
      rw [subNonTargetRatio, div_mul_div_comm,
        mul_comm (cos ((2 * (K : ℝ) + 1) * subHalfAngle p)), mul_div_mul_right _ _ hcos1]
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal hr
theorem sum_normSq_subsetKraus1_subsetGroverState {q : ℕ} (M : Finset (Fin (2 ^ q)))
    (h0 : 0 < M.card) (hlt : M.card < 2 ^ q) (K : ℕ)
    (hs_le1 : (subTargetRatio ((M.card : ℝ) / (2 ^ q : ℝ)) K) ^ 2 ≤ 1)
    (hsin3 : sin ((2 * (K : ℝ) + 3) * subHalfAngle ((M.card : ℝ) / (2 ^ q : ℝ))) ≠ 0)
    (hcos1 : cos ((2 * (K : ℝ) + 1) * subHalfAngle ((M.card : ℝ) / (2 ^ q : ℝ))) ≠ 0) :
    let p : ℝ := (M.card : ℝ) / (2 ^ q : ℝ)
    let v1 := subsetKraus1 M (subTargetRatio p K) *ᵥ subsetGroverState M (K + 1)
    (∀ u ∉ M, v1 u = 0) ∧ (∑ u : Fin (2 ^ q), normSq (v1 u)) = 1 - subFailProb p K := by
  intro p v1
  set s := subTargetRatio p K
  refine ⟨fun u hu ↦ by simp [v1, subsetKraus1, mulVec_diagonal, hu], ?_⟩
  have h0_vec := subsetKraus0_mulVec_subsetGroverState M h0 hlt K hsin3 hcos1
  have hpyth (u : Fin (2 ^ q)) :
      normSq ((subsetKraus0 M s *ᵥ subsetGroverState M (K + 1)) u) + normSq (v1 u) =
        normSq (subsetGroverState M (K + 1) u) := by
    dsimp only [v1]
    rw [subsetKraus0, subsetKraus1, mulVec_diagonal, mulVec_diagonal]
    by_cases hu : u ∈ M
    · rw [ite_eq_left hu, ite_eq_left hu, Complex.normSq_mul, Complex.normSq_mul, ← add_mul,
        Complex.normSq_neg, Complex.normSq_neg, Complex.normSq_ofReal, Complex.normSq_ofReal,
        ← sq, ← sq, Real.sq_sqrt (by dsimp only [s, p]; linarith),
        show s ^ 2 + (1 - s ^ 2) = 1 by ring, one_mul]
    · rw [ite_eq_right hu, ite_eq_right hu, one_mul, zero_mul, Complex.normSq_zero, add_zero]
  have hsum_pyth :
      (∑ u : Fin (2 ^ q), normSq ((subsetKraus0 M s *ᵥ subsetGroverState M (K + 1)) u)) +
        (∑ u : Fin (2 ^ q), normSq (v1 u)) = 1 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun u _ ↦ hpyth u,
      (sum_normSq_subsetGroverState M h0 hlt (K + 1)).1]
  have hsum_k0 :
      (∑ u : Fin (2 ^ q), normSq ((subsetKraus0 M s *ᵥ subsetGroverState M (K + 1)) u)) =
        subFailProb p K := by
    dsimp only [s]
    rw [h0_vec]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      ← Finset.mul_sum, (sum_normSq_subsetGroverState M h0 hlt K).2, mul_one]
    rw [subFailProb, sq]
  linarith
/- ## Collective `m`-Flag Involutive Chord Unitary -/

theorem addrEnv_zero_ne_one {n m : ℕ} (hm : 1 ≤ m) :
    (0 : (addrReg n m).Environment → ZMod 2) ≠ 1 := by
  let w₀ : (addrReg n m).Environment := ⟨slotReg n m ⟨0, hm⟩ 0, by
    rintro ⟨u, hu⟩
    obtain ⟨⟨j', r⟩, rfl⟩ := finProdFinEquiv.surjective u
    have hu' : addrReg n m (finProdFinEquiv (j', r)) = slotReg n m ⟨0, hm⟩ 0 := hu
    rw [addrReg_apply, slotReg_apply, slotReg_apply] at hu'
    exact Fin.succ_ne_zero r (congrArg Prod.snd (finProdFinEquiv.injective hu'))⟩
  intro h
  have hw := congrFun h w₀
  exact zero_ne_one hw
/-- Entries of the symmetric `2 × 2` reflection `[[c, t], [t, -c]]` on `{0, 1}` in
  `(addrReg n m).Environment → ZMod 2`, acting as identity on all other flag assignments. -/
noncomputable def chordEnvFun (n m : ℕ) (c t : ℝ)
    (a b : (addrReg n m).Environment → ZMod 2) : ℂ :=
  if a = 0 then
    if b = 0 then (c : ℂ) else if b = 1 then (t : ℂ) else 0
  else if a = 1 then
    if b = 0 then (t : ℂ) else if b = 1 then -(c : ℂ) else 0
  else if a = b then 1 else 0
/-- Matrix form of `chordEnvFun` on `(addrReg n m).Environment → ZMod 2`. -/
noncomputable def chordEnvMat (n m : ℕ) (c t : ℝ) :
    Matrix ((addrReg n m).Environment → ZMod 2) ((addrReg n m).Environment → ZMod 2) ℂ :=
  chordEnvFun n m c t
theorem chordEnvMat_conjTranspose (n m : ℕ) (hm : 1 ≤ m) (c t : ℝ) :
    (chordEnvMat n m c t)ᴴ = chordEnvMat n m c t := by
  have h01 := addrEnv_zero_ne_one (n := n) hm
  have h10 : (1 : (addrReg n m).Environment → ZMod 2) ≠ 0 := h01.symm
  ext a b
  rw [conjTranspose_apply]
  dsimp only [chordEnvMat]
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; simp [chordEnvFun]
    · by_cases hb1 : b = 1
      · subst hb1; simp [chordEnvFun, h10]
      · simp [chordEnvFun, hb0, hb1]
  · by_cases ha1 : a = 1
    · subst ha1
      by_cases hb0 : b = 0
      · subst hb0; simp [chordEnvFun, h10]
      · by_cases hb1 : b = 1
        · subst hb1; simp [chordEnvFun, h10]
        · simp [chordEnvFun, hb0, hb1, h10]
    · by_cases hb0 : b = 0
      · subst hb0; simp [chordEnvFun, ha0, ha1]
      · by_cases hb1 : b = 1
        · subst hb1; simp [chordEnvFun, ha0, ha1, h10]
        · by_cases hab : a = b
          · subst hab; simp [chordEnvFun, ha0, ha1]
          · simp [chordEnvFun, ha0, ha1, hb0, hb1, hab, Ne.symm hab]
theorem chordEnvMat_mul_self (n m : ℕ) (hm : 1 ≤ m) {c t : ℝ} (hct : c ^ 2 + t ^ 2 = 1) :
    chordEnvMat n m c t * chordEnvMat n m c t = 1 := by
  have h01 := addrEnv_zero_ne_one (n := n) hm
  have h10 : (1 : (addrReg n m).Environment → ZMod 2) ≠ 0 := h01.symm
  have hctC : (c : ℂ) ^ 2 + (t : ℂ) ^ 2 = 1 := by
    calc (c : ℂ) ^ 2 + (t : ℂ) ^ 2 = ((c ^ 2 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
      _ = 1 := by rw [hct]; push_cast; rfl
  have hsum01 (f : ((addrReg n m).Environment → ZMod 2) → ℂ)
      (hz : ∀ k, k ≠ 0 → k ≠ 1 → f k = 0) :
      (∑ k, f k) = f 0 + f 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h10, Finset.mem_univ 1⟩),
      Finset.sum_eq_zero (fun k hk ↦ by
        rcases Finset.mem_erase.mp hk with ⟨hk1, hk0'⟩
        exact hz k (Finset.mem_erase.mp hk0').1 hk1),
      add_zero]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  dsimp only [chordEnvMat]
  by_cases ha0 : a = 0
  · subst ha0
    rw [hsum01 _ (fun k hk0 hk1 ↦ by simp [chordEnvFun, hk0, hk1])]
    by_cases hb0 : b = 0
    · subst hb0
      simp only [chordEnvFun, ↓reduceIte, h10]
      linear_combination hctC
    · by_cases hb1 : b = 1
      · subst hb1
        simp only [chordEnvFun, ↓reduceIte, h01, h10]
        ring
      · simp [chordEnvFun, hb0, hb1, h10, Ne.symm hb0]
  · by_cases ha1 : a = 1
    · subst ha1
      rw [hsum01 _ (fun k hk0 hk1 ↦ by simp [chordEnvFun, hk0, hk1, h10])]
      by_cases hb0 : b = 0
      · subst hb0
        simp only [chordEnvFun, ↓reduceIte, h10]
        ring
      · by_cases hb1 : b = 1
        · subst hb1
          simp only [chordEnvFun, ↓reduceIte, h10]
          linear_combination hctC
        · simp [chordEnvFun, hb0, hb1, h10, Ne.symm hb1]
    · rw [Fintype.sum_eq_single a (fun k hk ↦ by
        dsimp only [chordEnvFun]
        rw [ite_eq_right ha0, ite_eq_right ha1, ite_eq_right hk.symm, zero_mul])]
      dsimp only [chordEnvFun]
      rw [ite_eq_right ha0, ite_eq_right ha1, ite_eq_left rfl, one_mul,
        ite_eq_right ha0, ite_eq_right ha1]
/-- Involutive collective chord unitary on `m * (n + 1)` qubits for parameter `0 ≤ s ≤ 1`,
  rotating the `(0, 1)` environment flag subspace with `c = √((1 + s) / 2)`, `t = √((1 - s)
  / 2)`. -/
noncomputable def chordUnitary (n m : ℕ) (hm : 1 ≤ m) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Unitary (2 ^ (m * (n + 1))) :=
  let c := √((1 + s) / 2)
  let t := √((1 - s) / 2)
  let M : Operator (2 ^ (m * (n + 1))) := fun i j ↦
    if ((addrReg n m).basisSplitEquiv i).1 = ((addrReg n m).basisSplitEquiv j).1 then
      chordEnvFun n m c t ((addrReg n m).basisSplitEquiv i).2 ((addrReg n m).basisSplitEquiv j).2
    else 0
  ⟨M, by
    have hct : c ^ 2 + t ^ 2 = 1 := by
      dsimp only [c, t]
      rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
      ring
    have hcj : Mᴴ = M := by
      ext i j
      rw [conjTranspose_apply]
      dsimp only [M]
      by_cases h1 : ((addrReg n m).basisSplitEquiv i).1 = ((addrReg n m).basisSplitEquiv j).1
      · rw [ite_eq_left h1.symm, ite_eq_left h1]
        change (chordEnvMat n m c t)ᴴ
          ((addrReg n m).basisSplitEquiv i).2 ((addrReg n m).basisSplitEquiv j).2 =
          chordEnvMat n m c t
            ((addrReg n m).basisSplitEquiv i).2 ((addrReg n m).basisSplitEquiv j).2
        rw [chordEnvMat_conjTranspose n m hm]
      · rw [ite_eq_right (Ne.symm h1), ite_eq_right h1, star_zero]
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, hcj]
    ext i j
    rw [Matrix.mul_apply, ← (addrReg n m).basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
    dsimp only [M]
    simp_rw [Equiv.apply_symm_apply]
    rw [Fintype.sum_eq_single ((addrReg n m).basisSplitEquiv i).1
      (fun u hu ↦ Finset.sum_eq_zero fun e _ ↦ by rw [ite_eq_right hu.symm, zero_mul])]
    by_cases h1 : ((addrReg n m).basisSplitEquiv i).1 = ((addrReg n m).basisSplitEquiv j).1
    · rw [Finset.sum_congr rfl fun e _ ↦ by rw [ite_eq_left rfl, ite_eq_left h1]]
      change (chordEnvMat n m c t * chordEnvMat n m c t)
        ((addrReg n m).basisSplitEquiv i).2 ((addrReg n m).basisSplitEquiv j).2 = _
      rw [chordEnvMat_mul_self n m hm hct, Matrix.one_apply, Matrix.one_apply]
      have heq : (i = j) ↔
          ((addrReg n m).basisSplitEquiv i).2 = ((addrReg n m).basisSplitEquiv j).2 := by
        rw [← (addrReg n m).basisSplitEquiv.apply_eq_iff_eq, Prod.ext_iff, and_iff_right h1]
      exact if_congr heq.symm rfl rfl
    · have hij : i ≠ j := fun h ↦ h1 (congrArg (fun z ↦ ((addrReg n m).basisSplitEquiv z).1) h)
      rw [Matrix.one_apply_ne hij]
      exact Finset.sum_eq_zero fun e _ ↦ by rw [ite_eq_right h1, mul_zero]⟩
theorem chordUnitary_mulVec_tensorState {n m : ℕ} (hm : 1 ≤ m) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (v : Fin (2 ^ (m * n)) → ℂ) :
    let c : ℂ := (√((1 + s) / 2) : ℝ)
    let t : ℂ := (√((1 - s) / 2) : ℝ)
    let C := (chordUnitary n m hm s hs0 hs1).1
    let r := addrReg n m
    C *ᵥ r.tensorState v (single 0 1) =
        r.tensorState (c • v) (single 0 1) + r.tensorState (t • v) (single 1 1) ∧
      C *ᵥ r.tensorState v (single 1 1) =
        r.tensorState (t • v) (single 0 1) + r.tensorState ((-c) • v) (single 1 1) := by
  intro c t C r
  have h01 := addrEnv_zero_ne_one (n := n) hm
  have h10 : (1 : r.Environment → ZMod 2) ≠ 0 := h01.symm
  have hgen (e₀ : r.Environment → ZMod 2) :
      C *ᵥ r.tensorState v (single e₀ 1) =
        fun z ↦ v (r.extractIndex z) * chordEnvFun n m √((1 + s) / 2) √((1 - s) / 2)
          (r.basisSplitEquiv z).2 e₀ := by
    funext z
    rw [Matrix.mulVec, dotProduct]
    let g (y : Fin (2 ^ (m * (n + 1)))) : ℂ := C z y * r.tensorState v (single e₀ 1) y
    change ∑ y, g y = _
    rw [← r.basisSplitEquiv.symm.sum_comp g, Fintype.sum_prod_type]
    dsimp only [g, C, r, chordUnitary, tensorState]
    simp_rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    rw [Fintype.sum_eq_single ((addrReg n m).basisSplitEquiv z).1
      (fun u hu ↦ Finset.sum_eq_zero fun e _ ↦ by rw [ite_eq_right hu.symm, zero_mul])]
    rw [Fintype.sum_eq_single e₀
      (fun e he ↦ by rw [Pi.single_eq_of_ne he, mul_zero, mul_zero])]
    rw [ite_eq_left rfl, Pi.single_eq_same, mul_one, mul_comm]
  constructor
  · rw [hgen 0]
    funext z
    dsimp only [c, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tensorState, chordEnvFun]
    by_cases he0 : (r.basisSplitEquiv z).2 = 0
    · simp only [he0, ↓reduceIte, Pi.single_eq_same, Pi.single_eq_of_ne h01]
      ring
    · by_cases he1 : (r.basisSplitEquiv z).2 = 1
      · simp only [he1, h10, ↓reduceIte, Pi.single_eq_same, Pi.single_eq_of_ne h10]
        ring
      · simp only [he0, he1, ↓reduceIte, Pi.single_eq_of_ne he0, Pi.single_eq_of_ne he1]
        ring
  · rw [hgen 1]
    funext z
    dsimp only [c, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tensorState, chordEnvFun]
    by_cases he0 : (r.basisSplitEquiv z).2 = 0
    · simp only [he0, h10, ↓reduceIte, Pi.single_eq_same, Pi.single_eq_of_ne h01]
      ring
    · by_cases he1 : (r.basisSplitEquiv z).2 = 1
      · simp only [he1, h10, ↓reduceIte, Pi.single_eq_same, Pi.single_eq_of_ne h10]
        ring
      · simp only [he0, he1, ↓reduceIte, Pi.single_eq_of_ne he0, Pi.single_eq_of_ne he1]
        ring
theorem chord_sDiagM_chord_mulVec_zero {n m : ℕ} (hm : 1 ≤ m) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (R : Finset (Fin (2 ^ n))) (v : Fin (2 ^ (m * n)) → ℂ) :
    let C := (chordUnitary n m hm s hs0 hs1).1
    let r := addrReg n m
    C *ᵥ (sDiagM n m R *ᵥ (C *ᵥ r.tensorState v (single 0 1))) =
      r.tensorState (subsetKraus0 (oddSet n m R) s *ᵥ v) (single 0 1) +
        r.tensorState (subsetKraus1 (oddSet n m R) s *ᵥ v) (single 1 1) := by
  intro C r
  rw [(chordUnitary_mulVec_tensorState hm hs0 hs1 v).1, Matrix.mulVec_add,
    sDiagM_mulVec_tensorState_zero, sDiagM_mulVec_tensorState_one, Matrix.mulVec_add,
    (chordUnitary_mulVec_tensorState hm hs0 hs1
      (oracleMat (oddSet n m R) *ᵥ ((√((1 + s) / 2) : ℂ) • v))).1,
    (chordUnitary_mulVec_tensorState hm hs0 hs1 ((√((1 - s) / 2) : ℂ) • v)).2,
    show ∀ a₁ b₁ a₂ b₂ : Fin (2 ^ (m * (n + 1))) → ℂ,
      (a₁ + b₁) + (a₂ + b₂) = (a₁ + a₂) + (b₁ + b₂) from fun _ _ _ _ ↦ by abel,
    ← r.tensorState_add_left, ← r.tensorState_add_left]
  set cR : ℝ := √((1 + s) / 2) with hcR_def
  set tR : ℝ := √((1 - s) / 2) with htR_def
  have hc_sq : cR ^ 2 = (1 + s) / 2 := Real.sq_sqrt (by linarith)
  have ht_sq : tR ^ 2 = (1 - s) / 2 := Real.sq_sqrt (by linarith)
  have h2ct : 2 * cR * tR = √(1 - s ^ 2) := by
    have hsqrt4 : √(4 : ℝ) = 2 := by norm_num
    calc 2 * cR * tR
        = √(4 : ℝ) * √(((1 + s) / 2) * ((1 - s) / 2)) := by
            rw [hsqrt4, hcR_def, htR_def, Real.sqrt_mul (by linarith), mul_assoc]
      _ = √(1 - s ^ 2) := by
            rw [← Real.sqrt_mul (by norm_num)]
            congr 1
            ring
  have hdiffC : (tR : ℂ) ^ 2 - (cR : ℂ) ^ 2 = -(s : ℂ) := by
    have h : tR ^ 2 - cR ^ 2 = -s := by rw [ht_sq, hc_sq]; ring
    calc (tR : ℂ) ^ 2 - (cR : ℂ) ^ 2 = ((tR ^ 2 - cR ^ 2 : ℝ) : ℂ) := by push_cast; ring
      _ = -(s : ℂ) := by rw [h]; push_cast; rfl
  have hsumC : (cR : ℂ) ^ 2 + (cR : ℂ) * 0 + (tR : ℂ) ^ 2 = 1 := by
    have h : cR ^ 2 + tR ^ 2 = 1 := by rw [hc_sq, ht_sq]; ring
    calc (cR : ℂ) ^ 2 + (cR : ℂ) * 0 + (tR : ℂ) ^ 2
        = ((cR ^ 2 + tR ^ 2 : ℝ) : ℂ) := by push_cast; ring
      _ = 1 := by rw [h]; push_cast; rfl
  have hprodC : -(2 * (cR : ℂ) * (tR : ℂ)) = -(√(1 - s ^ 2) : ℂ) := by
    calc -(2 * (cR : ℂ) * (tR : ℂ)) = ((-(2 * cR * tR) : ℝ) : ℂ) := by push_cast; ring
      _ = -(√(1 - s ^ 2) : ℂ) := by rw [h2ct]; push_cast; rfl
  congr 1
  · congr 1
    funext u
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, oracleMat, subsetKraus0, mulVec_diagonal]
    by_cases hu : u ∈ oddSet n m R
    · rw [ite_eq_left hu, ite_eq_left hu]
      linear_combination v u * hdiffC
    · rw [ite_eq_right hu, ite_eq_right hu]
      linear_combination v u * hsumC
  · congr 1
    funext u
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, oracleMat, subsetKraus1, mulVec_diagonal]
    by_cases hu : u ∈ oddSet n m R
    · rw [ite_eq_left hu, ite_eq_left hu]
      linear_combination v u * hprodC
    · rw [ite_eq_right hu, ite_eq_right hu]
      ring
end QuantumComputation.Specs.GroverSol
end
end Sec_SubsetEigLock
end Sec_SubsetEigLock
section Sec_Stage1EigLock
section Sec_Stage1EigLock
section Sec_FindAllStage1
namespace QuantumComputation.Specs.GroverSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal mul_diagonal mulVec_diagonal mulVec_mulVec mulVec_single_one col_apply
  conjTranspose_apply)
open Complex (normSq ofReal_sum)
open Fintype (sum_eq_single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation
  InnerProductSpace
@[expose] public section
/- ## Diagonal Observables and `MemPrefixValid` Stage Assertions -/
noncomputable def realDiagObs {d : ℕ} (f : Fin d → ℝ)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) : Observable (Fin d) :=
  ⟨∑ z : Fin d, f z • cqCompProjHerm z,
    Finset.sum_nonneg fun z _ ↦ smul_nonneg (h0 z) (cqCompProjHerm_nonneg z),
    calc ∑ z : Fin d, f z • cqCompProjHerm z
        ≤ ∑ z : Fin d, (1 : ℝ) • cqCompProjHerm z :=
          Finset.sum_le_sum fun z _ ↦
            smul_le_smul_of_nonneg_right (h1 z) (cqCompProjHerm_nonneg z)
      _ = 1 := by
          ext1
          simp [HermitianMat.mat_finset_sum]⟩
lemma realDiagObs_mat {d : ℕ} (f : Fin d → ℝ) (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) :
    (realDiagObs f h0 h1).1.1 = diagonal (fun z ↦ (f z : ℂ)) := by
  rw [realDiagObs, HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum,
    ← Matrix.sum_single_eq_diagonal]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [HermitianMat.mat_smul, cqCompProjHerm_mat, compProj, Matrix.smul_single,
    Complex.real_smul, mul_one]
lemma observable_diag_real_bounds {d : ℕ} (O : Observable (Fin d)) (c : Fin d → ℂ) (hO : O.1.1 =
    diagonal c) (z : Fin d) : c z = ((c z).re : ℂ) ∧ 0 ≤ (c z).re ∧ (c z).re ≤ 1 := by
  have hself : star (O.1.1 z z) = O.1.1 z z := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun O.1.2 z) z
  rw [hO, Matrix.diagonal_apply_eq] at hself
  have hre : c z = ((c z).re : ℂ) := (Complex.conj_eq_iff_re.mp hself).symm
  have htr (A : HermitianMat (Fin d) ℂ) (g : Fin d → ℂ) (hA : A.1 = diagonal g) :
      ⟪A, cqCompProjHerm z⟫_ℝ = (g z).re := by
    rw [HermitianMat.inner_eq_re_trace]
    have hmat : A.mat * (cqCompProjHerm z).mat = Matrix.single z z (g z) := by
      change A.1 * compProj z = _; rw [hA, compProj]; ext i j
      rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]; by_cases h : z = i ∧ z = j
      · rcases h with ⟨rfl, rfl⟩; simp
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    rw [hmat]; dsimp only [Matrix.trace, Matrix.diag]
    rw [sum_eq_single z (fun x hx ↦ by
      rw [Matrix.single_apply, ite_eq_right (fun h ↦ hx h.1.symm)])]
    rw [Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩]; rfl
  have h0 : 0 ≤ (c z).re := by
    rw [← htr O.1 c hO]; exact HermitianMat.inner_ge_zero O.2.1 (cqCompProjHerm_nonneg z)
  have h1 : (c z).re ≤ 1 := by
    have hle := HermitianMat.inner_mono' (cqCompProjHerm_nonneg z) O.2.2
    rwa [htr O.1 c hO, htr 1 (fun _ ↦ 1) Matrix.diagonal_one.symm, Complex.one_re] at hle
  exact ⟨hre, h0, h1⟩
lemma realDiagObs_le_of_mat {d : ℕ} {f g : Fin d → ℝ} {hf0 : ∀ z, 0 ≤ f z} {hf1 : ∀ z, f z ≤ 1}
    (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1) {O : Observable (Fin d)}
    (hO : O.1.1 = diagonal (fun z ↦ (g z : ℂ))) (hfg : ∀ z, f z ≤ g z) :
    realDiagObs f hf0 hf1 ≤ O := by
  have hO_eq : O = realDiagObs g hg0 hg1 :=
    Subtype.ext (HermitianMat.ext (hO.trans (realDiagObs_mat g hg0 hg1).symm))
  rw [hO_eq]
  exact Finset.sum_le_sum fun z _ ↦ smul_le_smul_of_nonneg_right (hfg z) (cqCompProjHerm_nonneg z)
lemma le_realDiagObs_of_mat {d : ℕ} {f g : Fin d → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    {hg0 : ∀ z, 0 ≤ g z} {hg1 : ∀ z, g z ≤ 1} {O : Observable (Fin d)}
    (hO : O.1.1 = diagonal (fun z ↦ (f z : ℂ))) (hfg : ∀ z, f z ≤ g z) :
    O ≤ realDiagObs g hg0 hg1 := by
  have hO_eq : O = realDiagObs f hf0 hf1 :=
    Subtype.ext (HermitianMat.ext (hO.trans (realDiagObs_mat f hf0 hf1).symm))
  rw [hO_eq]
  exact Finset.sum_le_sum fun z _ ↦ smul_le_smul_of_nonneg_right (hfg z) (cqCompProjHerm_nonneg z)
noncomputable def validInd (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) : ℝ :=
  open Classical in
  if MemPrefixValid S j (lowHighEquiv (m * (n + 1)) (k * n) z).2 then 1 else 0
noncomputable def invalidInd (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) : ℝ :=
  open Classical in
  if MemPrefixValid S j (lowHighEquiv (m * (n + 1)) (k * n) z).2 then 0 else 1
lemma validInd_bounds (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ) (z : Fin (2 ^ (m * (n + 1) +
    k * n))) : 0 ≤ validInd n m k S j z ∧ validInd n m k S j z ≤ 1 := by
  unfold validInd; split_ifs <;> constructor <;> norm_num
lemma invalidInd_bounds (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ) (z : Fin (2 ^ (m * (n +
    1) + k * n))) : 0 ≤ invalidInd n m k S j z ∧ invalidInd n m k S j z ≤ 1 := by
  unfold invalidInd; split_ifs <;> constructor <;> norm_num
noncomputable def validObs {Var : Type} (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
  fun _ ↦ realDiagObs (validInd n m k S j)
    (fun z ↦ (validInd_bounds n m k S j z).1)
    (fun z ↦ (validInd_bounds n m k S j z).2)
noncomputable def invalidObs {Var : Type} (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
  fun _ ↦ realDiagObs (invalidInd n m k S j)
    (fun z ↦ (invalidInd_bounds n m k S j z).1)
    (fun z ↦ (invalidInd_bounds n m k S j z).2)
noncomputable def scaledValidObs {Var : Type} (n m k : ℕ) (S : Finset (Fin (2 ^ n)))
    (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
  fun _ ↦ realDiagObs (fun z ↦ c * validInd n m k S j z)
    (fun z ↦ mul_nonneg hc0 (validInd_bounds n m k S j z).1)
    (fun z ↦ by nlinarith [validInd_bounds n m k S j z])
lemma scaledValidObs_smul {Var : Type} (n m k : ℕ) (S : Finset (Fin (2 ^ n)))
    (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (σ : Store Var) :
    (scaledValidObs n m k S j c hc0 hc1 σ).1 = c • (validObs n m k S j σ).1 := by
  dsimp only [scaledValidObs, validObs, realDiagObs]; rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun z _ ↦ mul_smul c (validInd n m k S j z) (cqCompProjHerm z)
lemma scaledValid_add_invalid_le_one {Var : Type} (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (σ : Store Var) : (scaledValidObs n m k S j c hc0 hc1
    σ).1 + (invalidObs n m k S j σ).1 ≤ 1 := by
  dsimp only [scaledValidObs, invalidObs, realDiagObs]; rw [← Finset.sum_add_distrib]
  calc ∑ z, ((c * validInd n m k S j z) • cqCompProjHerm z + invalidInd n m k S j z •
        cqCompProjHerm z) = ∑ z, (c * validInd n m k S j z + invalidInd n m k S j z) •
        cqCompProjHerm z := Finset.sum_congr rfl fun z _ ↦ (add_smul _ _ _).symm
    _ ≤ ∑ z, (1 : ℝ) • cqCompProjHerm z := by
        refine Finset.sum_le_sum fun z _ ↦
          smul_le_smul_of_nonneg_right ?_ (cqCompProjHerm_nonneg z)
        unfold validInd invalidInd; split_ifs <;> linarith
    _ = 1 := by ext1; simp [HermitianMat.mat_finset_sum]
lemma validObs_add_invalidObs_eq_top {Var : Type} (n m k : ℕ)
    (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    (validObs (Var := Var) n m k S j).add (invalidObs n m k S j)
      (fun σ ↦ by
        have h := scaledValid_add_invalid_le_one n m k S j 1 zero_le_one le_rfl σ
        rwa [scaledValidObs_smul, one_smul] at h) = ⊤ := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  change (validObs n m k S j σ).1.1 + (invalidObs n m k S j σ).1.1 = 1
  dsimp only [validObs, invalidObs]; rw [realDiagObs_mat, realDiagObs_mat]; ext z₁ z₂
  rw [Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : z₁ = z₂
  · subst h; simp only [↓reduceIte, validInd, invalidInd]; split_ifs <;> norm_num
  · simp [h]
lemma expect_invalidObs_eq_zero {Var : Type} {n m k : ℕ} {S : Finset (Fin (2 ^ n))} {j : ℕ} {Δ :
    CQState (Store Var) (2 ^ (m * (n + 1) + k * n))} (hV : 𝔼[Δ, validObs n m k S j] = Δ.trace) :
      𝔼[Δ,
    invalidObs n m k S j] = 0 := by
  have htop : 𝔼[Δ, (validObs (Var := Var) n m k S j).add (invalidObs n m k S j)
      (fun σ ↦ by
        have h := scaledValid_add_invalid_le_one n m k S j 1 zero_le_one le_rfl σ
        rwa [scaledValidObs_smul, one_smul] at h)] = Δ.trace := by
    rw [validObs_add_invalidObs_eq_top, expect_top]
  rw [expect_assertion_add] at htop; linarith
lemma validState_step {Var : Type} [DecidableEq Var] {n m k j j' : ℕ} {S : Finset (Fin (2 ^ n))}
    {P : QProg Var (2 ^ (m * (n + 1) + k * n))} {Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k *
      n))} (hV
    : 𝔼[Δ, validObs n m k S j] = Δ.trace) (hwp : validObs n m k S j ≤ wp P (validObs n m k S j'))
    :
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
/- ## Quadratic Forms, Register Identities, and Zero-Cost Work Reset -/
private noncomputable def vecQuad {d : ℕ} (A : Operator d) (ψ : Fin d → ℂ) : ℂ :=
  star ψ ⬝ᵥ (A *ᵥ ψ)
private lemma vecQuad_single {d : ℕ} (A : Operator d) (z : Fin d) :
    A z z = vecQuad A (Pi.single z 1) := by
  simp [vecQuad]
private lemma vecQuad_conj {d : ℕ} (U A : Operator d) (ψ : Fin d → ℂ) :
    vecQuad (Uᴴ * A * U) ψ = vecQuad A (U *ᵥ ψ) := by
  unfold vecQuad; rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]; set v := A *ᵥ (U *ᵥ ψ)
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
private lemma vecQuad_smul {d : ℕ} (A : Operator d) (c : ℝ) (ψ : Fin d → ℂ) :
    vecQuad A ((c : ℂ) • ψ) = ((c ^ 2 : ℝ) : ℂ) * vecQuad A ψ := by
  unfold vecQuad; rw [Matrix.mulVec_smul]
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Complex.star_def,
    map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ ↦ by push_cast; ring
private lemma vecQuad_diagonal {d : ℕ} (g : Fin d → ℂ) (ψ : Fin d → ℂ) :
    vecQuad (diagonal g) ψ = ∑ z : Fin d, (normSq (ψ z) : ℂ) * g z := by
  unfold vecQuad; simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def]; ring
private lemma workMemState_add_left {W M : ℕ} (ψ₁ ψ₂ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (ψ₁ + ψ₂) φ = workMemState ψ₁ φ + workMemState ψ₂ φ := by
  funext z; dsimp only [workMemState, Pi.add_apply]; ring
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
noncomputable def mapAndMeasureLow {Var : Type} (res : Var) (W M O : ℕ)
    (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M))) : OracleCirc Var (W + M) O :=
  .seq (qMap res g) (.measure res (lowBlock W M))
private lemma costBound_mapAndMeasureLow {Var : Type} [DecidableEq Var] (res : Var) {W M O : ℕ} (g
    : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M))) {oracle : Unitary (2 ^ O)} (hor : IsRealMatrix
    oracle.1) : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle) ((mapAndMeasureLow res
    W M O g).compile qAssign oracle) 0 := by
  unfold mapAndMeasureLow; dsimp only [compile]
  have hmeas : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
      (measureRegister res (lowBlock W M)) 0 := by
    simpa [measureRegister, CostModel.ofEmbeddedOracle] using CostBound.qMeasure (Var := Var)
      (CostModel.ofEmbeddedOracle oracle) res (lowBlock W M).regBasisMeas
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
private lemma wp_mapAndMeasureLow_bot {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M))) (oracle : Unitary (2 ^ O)) :
    wp ((mapAndMeasureLow res W M O g).compile qAssign oracle) ⊥ = ⊥ := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  change ((wp ((mapAndMeasureLow res W M O g).compile qAssign oracle) ⊥) σ).1.1 = 0
  rw [wp_mapAndMeasureLow res g oracle (fun _ ↦ 0) ⊥ (fun _ ↦ rfl) σ]; simp
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
def resetWorkFn (W M : ℕ) (z : Fin (2 ^ (W + M))) : Fin (2 ^ (W + M)) :=
  (lowHighEquiv W M).symm (0, (lowHighEquiv W M z).2)
noncomputable def workReset {Var : Type} (res : Var) (W M O : ℕ) :
    OracleCirc Var (W + M) O :=
  mapAndMeasureLow res W M O (resetWorkFn W M)
/- ## Shared Deflated Verification Write (`markAndWrite`) -/
noncomputable def markAndWrite {Var : Type} (n m k : ℕ) (s : Fin k) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedOracle le_rfl (memPrefix k s.val))
    (.step (phaseTag (permutationUnitary
      (memWriteBatchPerm s.val (fun w ↦ (firstMarkedAddr n m w).toList)))))
private lemma costBound_markAndWrite {Var : Type} [DecidableEq Var] (n m k : ℕ) (s : Fin k) (S :
    Finset (Fin (2 ^ n))) : CostBound (Var := Var) (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((markAndWrite n m k s).compile qAssign
    (groverParallelMarkingOracle m S)) 1 := by
  unfold markAndWrite; dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  simpa using (costBound_deflatedOracle (Var := Var) le_rfl (memPrefix k s.val) S).seq
    (costBound_qAssign_phaseTag (Var := Var) hor _)
private lemma vecQuad_markAndWrite {Var : Type} [DecidableEq Var] {n m k : ℕ} {S : Finset (Fin (2
    ^ n))} (s : Fin k) (v : Fin (2 ^ (m * n)) → ℂ) (μ : Fin (2 ^ (k * n))) (hval : MemPrefixValid
    S s.val μ) (g : Fin (2 ^ (m * (n + 1) + k * n)) → ℂ) (G : CQAssertion (Store Var) (2 ^ (m * (n +
      1) +
    k * n))) (σ : Store Var) (hG : (G σ).1.1 = diagonal g) :
    let R := S \ memSeen n k (memPrefix k s.val) μ
    let hits := fun w : Fin (2 ^ (m * (n + 1))) ↦ (firstMarkedAddr n m w).toList
    let w_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (m * (n + 1))) :=
      parallelMarkPerm n m R ((addrReg n m).basisSplitEquiv.symm (u, 0))
    let μ_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (k * n)) :=
      (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s.val hits (w_of u))
    vecQuad (((wp ((markAndWrite (Var := Var) n m k s).compile qAssign
      (groverParallelMarkingOracle m S)) G) σ).1.1) (workMemState ((addrReg n m).tensorState v
      (Pi.single 0 1)) (Pi.single μ 1)) = ∑ u : Fin (2 ^ (m * n)), (normSq (v u) : ℂ) * g
      ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) := by
  intro R hits w_of μ_of
  have hsub : memSeen n k (memPrefix k s.val) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
  unfold markAndWrite; dsimp only [compile]
  rw [wp_qSeq, wp_deflatedOracle_vecQuad (memPrefix k s.val) _ μ hsub,
    wp_qAssign, wp_phaseTag, qhlQAssign_val, hG, vecQuad_conj, vecQuad_diagonal]
  let W := m * (n + 1); let M := k * n; let perm := memWriteBatchPerm (k := k) s.val hits
  let ψ_mark := (permutationUnitary (parallelMarkPerm n m R)).1 *ᵥ
    (addrReg n m).tensorState v (Pi.single 0 1)
  let ψ_out := (permutationUnitary perm).1 *ᵥ workMemState ψ_mark (Pi.single μ 1)
  change ∑ z : Fin (2 ^ (W + M)), (normSq (ψ_out z) : ℂ) * g z = _; have hψ_mark (w : Fin (2 ^ W)) :
      ψ_mark w =
        let p := (addrReg n m).basisSplitEquiv ((parallelMarkPerm n m R).symm w)
        if p.2 = 0 then v p.1 else 0 := by
    dsimp only [ψ_mark]
    rw [Matrix.mulVec, dotProduct, sum_eq_single ((parallelMarkPerm n m R).symm w)
      (fun y hy ↦ by
        rw [permutationUnitary_apply,
          ite_eq_right (fun h ↦ hy ((parallelMarkPerm n m R).eq_symm_apply.mpr h.symm)),
          zero_mul])]
    rw [permutationUnitary_apply, Equiv.apply_symm_apply, ite_eq_left rfl, one_mul]
    dsimp only [QRegister.tensorState]; rw [← QRegister.basisSplitEquiv_apply_fst]
    by_cases h0 : ((addrReg n m).basisSplitEquiv ((parallelMarkPerm n m R).symm w)).2 = 0
    · rw [h0, Pi.single_eq_same, mul_one, ite_eq_left rfl]
    · rw [Pi.single_eq_of_ne h0, mul_zero, ite_eq_right h0]
  have hψ_out (z : Fin (2 ^ (W + M))) :
      ψ_out z =
        let pq := lowHighEquiv W M (perm.symm z)
        if pq.2 = μ then ψ_mark pq.1 else 0 := by
    dsimp only [ψ_out]
    rw [Matrix.mulVec, dotProduct, sum_eq_single (perm.symm z)
      (fun y hy ↦ by
        rw [permutationUnitary_apply,
          ite_eq_right (fun h ↦ hy (perm.eq_symm_apply.mpr h.symm)), zero_mul])]
    rw [permutationUnitary_apply, Equiv.apply_symm_apply, ite_eq_left rfl, one_mul]
    dsimp only [workMemState]; by_cases hμ : (lowHighEquiv W M (perm.symm z)).2 = μ
    · rw [hμ, Pi.single_eq_same, mul_one, ite_eq_left rfl]
    · rw [Pi.single_eq_of_ne hμ, mul_zero, ite_eq_right hμ]
  rw [← Equiv.sum_comp perm (fun z ↦ (normSq (ψ_out z) : ℂ) * g z)]
  simp_rw [hψ_out, Equiv.symm_apply_apply]; rw [← (lowHighEquiv W M).symm.sum_comp]
  simp_rw [Equiv.apply_symm_apply]; rw [Fintype.sum_prod_type]
  have hrow (w : Fin (2 ^ W)) : (∑ μ' : Fin (2 ^ M), (normSq (if μ' = μ then ψ_mark w else 0) :
    ℂ) * g (perm ((lowHighEquiv W M).symm (w, μ')))) = (normSq (ψ_mark w) : ℂ) * g (perm
    ((lowHighEquiv W M).symm (w, μ))) := by
    rw [sum_eq_single μ (fun μ' hμ' ↦ by
      rw [ite_eq_right hμ', Complex.normSq_zero, Complex.ofReal_zero, zero_mul])]
    rw [ite_eq_left rfl]
  simp_rw [hrow]
  let bij : Fin (2 ^ W) ≃ Fin (2 ^ (m * n)) × ((addrReg n m).Environment → ZMod 2) :=
    (parallelMarkPerm n m R).symm.trans (addrReg n m).basisSplitEquiv
  rw [← bij.symm.sum_comp, Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [sum_eq_single 0 (fun e he ↦ by
    have hb : (addrReg n m).basisSplitEquiv ((parallelMarkPerm n m R).symm (bij.symm (u, e))) =
        (u, e) := bij.apply_symm_apply (u, e)
    rw [hψ_mark, hb, ite_eq_right he, Complex.normSq_zero, Complex.ofReal_zero, zero_mul])]
  have hbij0 : bij.symm (u, 0) = w_of u := (by dsimp only [bij, w_of]; simp)
  have hb0 : (addrReg n m).basisSplitEquiv ((parallelMarkPerm n m R).symm (w_of u)) = (u, 0) := by
    rw [← hbij0]; exact bij.apply_symm_apply (u, 0)
  rw [hbij0, hψ_mark, hb0, ite_eq_left rfl]; congr 2
  apply (lowHighEquiv W M).injective; dsimp only [W, M, perm, memWriteBatchPerm, μ_of]
  rw [lowHighEquiv_memAddPerm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
private lemma markAndWrite_outcome_props {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (s : Fin k) {μ :
    Fin (2 ^ (k * n))} (hval : MemPrefixValid S s.val μ) (u : Fin (2 ^ (m * n))) :
    let R := S \ memSeen n k (memPrefix k s.val) μ
    let hits := fun w : Fin (2 ^ (m * (n + 1))) ↦ (firstMarkedAddr n m w).toList
    let w_u := parallelMarkPerm n m R ((addrReg n m).basisSplitEquiv.symm (u, 0))
    let μ_u := (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s.val hits w_u)
    (firstMarkedAddr n m w_u = firstTupleHit n m R u) ∧ (u ∈ oddSet n m R → (firstMarkedAddr n m
      w_u).isSome = true ∧ MemPrefixValid S (s.val + 1) μ_u) ∧ (u ∉ oddSet n m R →
      (firstMarkedAddr n m w_u).isSome = false ∧ μ_u = μ) := by
  intro R hits w_u μ_u; set z₀ := (addrReg n m).basisSplitEquiv.symm (u, 0)
  have hz0_fst : (addrReg n m).extractIndex z₀ = u := by
    simp [← QRegister.basisSplitEquiv_apply_fst, z₀]
  have hz0_snd : ((addrReg n m).basisSplitEquiv z₀).2 = 0 := (by simp [z₀])
  have hfma : firstMarkedAddr n m w_u = firstTupleHit n m R u := by
    simpa [w_u, hz0_fst] using firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R z₀ hz0_snd
  refine ⟨hfma, fun hu ↦ ?_, fun hu ↦ ?_⟩
  · have his : (firstTupleHit n m R u).isSome = true := (isSome_firstTupleHit_iff R u).mpr hu
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp his
    have hxR : x ∈ R := (mem_of_firstTupleHit_eq_some hx).2
    have hhits : hits w_u = [x] := (by simp [hits, hfma, hx])
    have hadv := memPrefixValid_batchAdvance hval hits w_u
      (by rw [hhits]; exact List.nodup_singleton x)
      (by rw [hhits, List.length_singleton]; exact s.isLt)
      (by rw [hhits]; intro y hy; rw [List.mem_singleton.mp hy]; exact hxR)
    rw [hhits, List.length_singleton] at hadv; exact ⟨by rw [hfma, his], hadv⟩
  · have hnone : firstTupleHit n m R u = none :=
      Option.not_isSome_iff_eq_none.mp (mt (isSome_firstTupleHit_iff R u).mp hu)
    have hhits : hits w_u = [] := (by simp [hits, hfma, hnone])
    have hδ : batchDelta (k := k) s.val hits w_u = 0 := (by funext j; simp [batchDelta, hhits])
    exact ⟨by simp [hfma, hnone], by
      dsimp only [μ_u]
      rw [hδ, add_zero, Equiv.symm_apply_apply]⟩
/- ## Hadamard Preparation on `addrReg` -/
private lemma hadamard_mulVec_zero (q : ℕ) (M : Finset (Fin (2 ^ q))) :
    hadamardMatrix q *ᵥ (Pi.single 0 1 : Fin (2 ^ q) → ℂ) = subsetGroverState M 0 := by
  funext u; rw [mulVec_single_one, col_apply, hadamardMatrix_apply_zero]; simp [subsetGroverState]
private lemma embed_addrReg_mulVec_zero {n m : ℕ} (A : Operator (2 ^ (m * n)))
    (v : Fin (2 ^ (m * n)) → ℂ) :
    (addrReg n m).embedMatrix A *ᵥ (addrReg n m).tensorState v (Pi.single 0 1) =
      (addrReg n m).tensorState (A *ᵥ v) (Pi.single 0 1) :=
  (addrReg n m).embedMatrix_mulVec_tensorState A v (Pi.single 0 1)
private lemma tensorState_zero_zero (n m : ℕ) : (addrReg n m).tensorState (Pi.single 0 1)
    (Pi.single 0 1) = (Pi.single 0 1 : Fin (2 ^ (m * (n + 1))) → ℂ) := by
  funext z; dsimp only [QRegister.tensorState]; rw [← QRegister.basisSplitEquiv_apply_fst]
  have hz0 : (addrReg n m).basisSplitEquiv 0 = (0, 0) := by
    apply Prod.ext
    · apply (basisBits (m * n)).injective; funext i; simp
    · funext e; simp
  by_cases hz : z = 0
  · subst hz; rw [hz0, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne hz]
    have hne : (addrReg n m).basisSplitEquiv z ≠ (0, 0) :=
      fun h ↦ hz ((addrReg n m).basisSplitEquiv.injective (h.trans hz0.symm))
    by_cases h1 : ((addrReg n m).basisSplitEquiv z).1 = 0
    · have h2 : ((addrReg n m).basisSplitEquiv z).2 ≠ 0 := fun h2 ↦ hne (Prod.ext h1 h2)
      rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]
/- ## Naive Single-Query Bernoulli Stage (`n < 200`, `k < 2 ^ n`) -/
def naiveOutFn (n m k : ℕ) (hm : 1 ≤ m)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) : Fin (2 ^ (m * (n + 1) + k * n)) :=
  let pq := lowHighEquiv (m * (n + 1)) (k * n) z
  let w' : Fin (2 ^ (m * (n + 1))) :=
    if (firstMarkedAddr n m pq.1).isSome then
      ⟨1, Nat.one_lt_two_pow (by nlinarith)⟩
    else 0
  (lowHighEquiv (m * (n + 1)) (k * n)).symm (w', pq.2)
noncomputable def naiveBody {Var : Type} (res : Var) (n m k : ℕ)
    (hm : 1 ≤ m) (s : Fin k) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  .seq (workReset res W M ((n + 1) * m))
    (.seq (.step (phaseTag ((lowBlock W M).embedUnitary
        ((addrReg n m).embedUnitary hadamardUnitary))))
      (.seq (markAndWrite n m k s)
        (mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k hm))))
noncomputable def naiveStage {Var : Type} (res : Var) (n m k : ℕ)
    (hm : 1 ≤ m) (s : Fin k) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (workReset res (m * (n + 1)) (k * n) ((n + 1) * m))
    (.qWhile (fun σ ↦ σ res = 0) (naiveBody res n m k hm s))
lemma wp_naiveStage_ge {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) (hm : 1 ≤ m) (hk_lt
    : k < 2 ^ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k) : validObs (Var :=
    Var) n m k S s.val ≤ wp ((naiveStage res n m k hm s).compile qAssign
    (groverParallelMarkingOracle m S)) (validObs n m k S (s.val + 1)) := by
  let W := m * (n + 1); let M := k * n; let oracle := groverParallelMarkingOracle m S
  let guard : Store Var → Prop := fun σ ↦ σ res = 0
  let bodyP := (naiveBody (Var := Var) res n m k hm s).compile qAssign oracle
  let post := validObs (Var := Var) n m k S (s.val + 1); set r := k - s.val
  have hr1 : 1 ≤ r := (by omega); have hr_lt : r < 2 ^ n := (by omega)
  set p := oddFrac n m r; have hp_bounds := oddFrac_pos_lt_one (n := n) hm hr1 hr_lt; set q := 1 - p
  have hq0 : 0 ≤ q := (by linarith [hp_bounds.2]); have hq1 : q < 1 := (by linarith [hp_bounds.1])
  have hunroll (t : ℕ) : ∃ d_t : Fin (2 ^ (W + M)) → ℝ, (∀ z, 0 ≤ d_t z ∧ d_t z ≤ 1) ∧ (∀ z, (1 -
    q ^ t) * validInd n m k S s.val z ≤ d_t z) ∧ ∀ τ, (whileRecWP (wp bodyP) guard (t + 1) post
    τ).1.1 = if τ res = 0 then diagonal (fun z ↦ (d_t z : ℂ)) else diagonal (fun z ↦ (validInd n m
    k S (s.val + 1) z : ℂ)) := by
    induction t with
    | zero =>
      refine ⟨fun _ ↦ 0, fun _ ↦ ⟨le_rfl, zero_le_one⟩, fun z ↦ by simp, fun τ ↦ ?_⟩
      rw [qhlWhileSucc_val]; by_cases hτ : τ res = 0
      · rw [ite_eq_left hτ, ite_eq_left hτ]
        have hbot : whileRecWP (wp bodyP) guard 0 post = ⊥ := rfl
        have hwp0 : wp bodyP ⊥ = ⊥ := by
          dsimp only [bodyP, naiveBody, workReset, markAndWrite, deflatedOracle, compile]
          simp [wp_qSeq, wp_qAssign, wp_mapAndMeasureLow_bot]
        rw [hbot, hwp0]; ext i j; simp [Matrix.diagonal_apply]
      · rw [ite_eq_right hτ, ite_eq_right hτ]; dsimp only [post, validObs]; rw [realDiagObs_mat]
    | succ t ih =>
      rcases ih with ⟨d_t, hd_bounds, hd_ge, hd_mat⟩
      let H_prev (val : ℤ) : Operator (2 ^ (W + M)) := if val = 0 then diagonal (fun z ↦ (d_t z :
        ℂ)) else diagonal (fun z ↦ (validInd n m k S (s.val + 1) z : ℂ))
      let g_chk (z : Fin (2 ^ (W + M))) : ℝ :=
        let z' := naiveOutFn n m k hm z
        if ((lowHighEquiv W M z').1).val = 0 then d_t z'
        else validInd n m k S (s.val + 1) z'
      have hchk (τ' : Store Var) : ((wp ((mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k
        hm)).compile qAssign oracle) (whileRecWP (wp bodyP) guard (t + 1) post)) τ').1.1 =
        diagonal (fun z ↦ (g_chk z : ℂ)) := by
        rw [wp_mapAndMeasureLow res _ oracle H_prev _ hd_mat τ']
        refine congrArg diagonal (funext fun z ↦ ?_)
        dsimp only [H_prev, g_chk]
        by_cases h0 : ((lowHighEquiv W M (naiveOutFn n m k hm z)).1).val = 0
        · have h0' : (Int.ofNat ((lowHighEquiv W M (naiveOutFn n m k hm z)).1).val) = 0 := by
            rw [h0]; rfl
          rw [ite_eq_left h0', ite_eq_left h0, Matrix.diagonal_apply_eq]
        · have h0' : (Int.ofNat ((lowHighEquiv W M (naiveOutFn n m k hm z)).1).val) ≠ 0 :=
            fun h ↦ h0 (Int.ofNat.inj h)
          rw [ite_eq_right h0', ite_eq_right h0, Matrix.diagonal_apply_eq]
      let innerP := (OracleDynamicCircuit.seq (.step (phaseTag ((lowBlock W M).embedUnitary
        ((addrReg n m).embedUnitary hadamardUnitary)))) (.seq (markAndWrite n m k s)
        (mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k hm)))).compile qAssign oracle
      let M_inner : Operator (2 ^ (W + M)) :=
        ((wp innerP (whileRecWP (wp bodyP) guard (t + 1) post)) (fun _ ↦ 0)).1.1
      have hinner_const (τ' : Store Var) :
          ((wp innerP (whileRecWP (wp bodyP) guard (t + 1) post)) τ').1.1 = M_inner := by
        dsimp only [innerP, M_inner, compile]; rw [wp_qSeq, wp_qSeq]
        have hmeas_eq : wp ((mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k hm)).compile
          qAssign oracle) (whileRecWP (wp bodyP) guard (t + 1) post) τ' = wp ((mapAndMeasureLow
          res W M ((n + 1) * m) (naiveOutFn n m k hm)).compile qAssign oracle) (whileRecWP (wp
          bodyP) guard (t + 1) post) (fun _ ↦ 0) := Subtype.ext (HermitianMat.ext ((hchk τ').trans
          (hchk (fun _ ↦ 0)).symm))
        have hmw_eq := wp_eq_of_pureUnitary (P := (markAndWrite (Var := Var) n m k s).compile
          qAssign oracle) ⟨⟨trivial, trivial⟩, trivial⟩ hmeas_eq
        have hH_eq := wp_eq_of_pureUnitary (P := (.step (phaseTag ((lowBlock W M).embedUnitary
          ((addrReg n m).embedUnitary hadamardUnitary))) : OracleCirc Var (W + M) ((n + 1) *
          m)).compile qAssign oracle) trivial hmw_eq
        exact congrArg (fun O : Observable _ ↦ O.1.1) hH_eq
      let d_next (z : Fin (2 ^ (W + M))) : ℝ :=
        (M_inner (resetWorkFn W M z) (resetWorkFn W M z)).re
      have hbody_diag (τ' : Store Var) : ((wp bodyP (whileRecWP (wp bodyP) guard (t + 1) post))
        τ').1.1 = diagonal (fun z ↦ M_inner (resetWorkFn W M z) (resetWorkFn W M z)) := by
        change ((wp ((OracleDynamicCircuit.seq (workReset res W M ((n + 1) * m)) _).compile
          qAssign oracle) _) τ').1.1 = _
        dsimp only [compile]; rw [wp_qSeq]
        exact wp_mapAndMeasureLow res (resetWorkFn W M) oracle (fun _ ↦ M_inner) _ hinner_const τ'
      have hdiag_real (z : Fin (2 ^ (W + M))) : M_inner (resetWorkFn W M z) (resetWorkFn W M z) =
        (d_next z : ℂ) ∧ 0 ≤ d_next z ∧ d_next z ≤ 1 := observable_diag_real_bounds (wp bodyP
        (whileRecWP (wp bodyP) guard (t + 1) post) (fun _ ↦ 0)) (fun y ↦ M_inner (resetWorkFn W M
        y) (resetWorkFn W M y)) (hbody_diag (fun _ ↦ 0)) z
      refine ⟨d_next, fun z ↦ ⟨(hdiag_real z).2.1, (hdiag_real z).2.2⟩, fun z ↦ ?_, fun τ ↦ ?_⟩
      · open Classical in
        by_cases hval : MemPrefixValid S s.val (lowHighEquiv W M z).2
        · set μ := (lowHighEquiv W M z).2
          have hvalid_z : validInd n m k S s.val z = 1 := by unfold validInd; exact ite_eq_left hval
          rw [hvalid_z, mul_one]
          have hreset_eq : resetWorkFn W M z = (lowHighEquiv W M).symm (0, μ) := rfl
          have hval_eval : M_inner (resetWorkFn W M z) (resetWorkFn W M z) =
              ((p + (1 - p) * d_t ((lowHighEquiv W M).symm (0, μ)) : ℝ) : ℂ) := by
            rw [hreset_eq, vecQuad_single M_inner, ← workMemState_single]
            dsimp only [M_inner, innerP, compile]
            rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
              QRegister.embedUnitary_val, QRegister.embedUnitary_val,
              embedMatrix_lowBlock_mulVec_workMemState, ← tensorState_zero_zero n m,
              embed_addrReg_mulVec_zero, hadamardUnitary_coe, hadamard_mulVec_zero (m * n) (oddSet
              n m (S \ memSeen n k (memPrefix k s.val) μ)), wp_qSeq, vecQuad_markAndWrite s _ μ
              hval (fun y ↦ (g_chk y : ℂ)) _ _ (hchk _)]
            set R := S \ memSeen n k (memPrefix k s.val) μ
            have hR_card : R.card = r := by
              have hcm := card_memSeen_of_memPrefixValid hval
              rw [Finset.card_sdiff_of_subset hcm.2, hcard, hcm.1]
            have hp_R : ((oddSet n m R).card : ℝ) / (2 ^ (m * n) : ℝ) = p := by
              rw [card_oddSet_div_two_pow n m R, hR_card]
            let w_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (m * (n + 1))) :=
              parallelMarkPerm n m R ((addrReg n m).basisSplitEquiv.symm (u, 0))
            let μ_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (k * n)) :=
              (addrEquiv n k).symm (addrEquiv n k μ +
                batchDelta s.val (fun w ↦ (firstMarkedAddr n m w).toList) (w_of u))
            have hterm (u : Fin (2 ^ (m * n))) : (normSq (subsetGroverState (oddSet n m R) 0 u) :
              ℂ) * (g_chk ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) : ℂ) = ((1
              / (2 ^ (m * n) : ℝ) * if u ∈ oddSet n m R then 1 else d_t ((lowHighEquiv W M).symm
              (0, μ)) : ℝ) : ℂ) := by
              have hprops := markAndWrite_outcome_props s hval u
              have hnsq : normSq (subsetGroverState (oddSet n m R) 0 u) =
                  1 / (2 ^ (m * n) : ℝ) := by
                dsimp only [subsetGroverState]
                rw [Complex.normSq_ofReal, div_mul_div_comm, one_mul,
                  Real.mul_self_sqrt (by positivity)]
              rw [hnsq]; by_cases hu : u ∈ oddSet n m R
              · rcases hprops.2.1 hu with ⟨his, hadv⟩
                have hout : naiveOutFn n m k hm ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of
                  u, μ_of u)) = (lowHighEquiv (m * (n + 1)) (k * n)).symm (⟨1, Nat.one_lt_two_pow
                  (by nlinarith)⟩, μ_of u) := by
                  unfold naiveOutFn; dsimp only [R, w_of, μ_of] at his ⊢
                  rw [Equiv.apply_symm_apply, ite_eq_left his]
                have hg1 : g_chk ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) =
                    1 := by
                  dsimp only [W, M, R, g_chk, w_of, μ_of] at hout hadv ⊢
                  rw [hout, Equiv.apply_symm_apply, ite_eq_right (by norm_num)]
                  unfold validInd; rw [Equiv.apply_symm_apply, ite_eq_left hadv]
                rw [hg1, ite_eq_left hu]; push_cast; ring
              · rcases hprops.2.2 hu with ⟨his, hμ_eq⟩
                have hout : naiveOutFn n m k hm ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of
                  u, μ_of u)) = (lowHighEquiv (m * (n + 1)) (k * n)).symm (0, μ) := by
                  unfold naiveOutFn; dsimp only [R, w_of, μ_of] at his hμ_eq ⊢
                  have hnot : ¬ (firstMarkedAddr n m
                      (parallelMarkPerm n m (S \ memSeen n k (memPrefix k s.val) μ)
                        ((addrReg n m).basisSplitEquiv.symm (u, 0)))).isSome = true := by
                    rw [his]; simp
                  rw [Equiv.apply_symm_apply, ite_eq_right hnot, hμ_eq]
                have hg0 : g_chk ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) =
                    d_t ((lowHighEquiv W M).symm (0, μ)) := by
                  dsimp only [W, M, R, g_chk, w_of, μ_of] at hout ⊢
                  rw [hout, Equiv.apply_symm_apply, Fin.val_zero, ite_eq_left rfl]
                rw [hg0, ite_eq_right hu]; push_cast; ring
            rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← ofReal_sum]; congr 1
            have hite (u : Fin (2 ^ (m * n))) : 1 / (2 ^ (m * n) : ℝ) * (if u ∈ oddSet n m R then
              (1 : ℝ) else d_t ((lowHighEquiv W M).symm (0, μ))) = (1 / (2 ^ (m * n) : ℝ)) * d_t
              ((lowHighEquiv W M).symm (0, μ)) + if u ∈ oddSet n m R then (1 / (2 ^ (m * n) :
              ℝ)) * (1 - d_t ((lowHighEquiv W M).symm (0, μ))) else 0 := by
              by_cases hu : u ∈ oddSet n m R
              · rw [ite_eq_left hu, ite_eq_left hu]; ring
              · rw [ite_eq_right hu, ite_eq_right hu]; ring
            simp_rw [hite, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
              nsmul_eq_mul]
            push_cast; have hD_ne : (2 ^ (m * n) : ℝ) ≠ 0 := (by positivity)
            have hp_mul : ((oddSet n m R).card : ℝ) * (1 / (2 ^ (m * n) : ℝ)) = p := by
              rw [mul_one_div, hp_R]
            calc (2 : ℝ) ^ (m * n) * (1 / 2 ^ (m * n) * d_t ((lowHighEquiv W M).symm (0, μ))) +
                  ((oddSet n m R).card : ℝ) *
                    (1 / 2 ^ (m * n) * (1 - d_t ((lowHighEquiv W M).symm (0, μ))))
                = (2 ^ (m * n) * (1 / 2 ^ (m * n))) * d_t ((lowHighEquiv W M).symm (0, μ)) +
                    (((oddSet n m R).card : ℝ) * (1 / (2 ^ (m * n) : ℝ))) *
                      (1 - d_t ((lowHighEquiv W M).symm (0, μ))) := by ring
              _ = p + (1 - p) * d_t ((lowHighEquiv W M).symm (0, μ)) := by
                    rw [mul_one_div_cancel hD_ne, hp_mul]; ring
          have hd_eq : d_next z = p + (1 - p) * d_t ((lowHighEquiv W M).symm (0, μ)) := by
            have h1 := (hdiag_real z).1.symm.trans hval_eval; exact Complex.ofReal_injective h1
          have hd_ih := hd_ge ((lowHighEquiv W M).symm (0, μ))
          have hv0 : validInd n m k S s.val ((lowHighEquiv W M).symm (0, μ)) = 1 := by
            unfold validInd; rw [Equiv.apply_symm_apply, ite_eq_left hval]
          rw [hv0, mul_one] at hd_ih; rw [hd_eq, pow_succ]; have h1p : 0 ≤ 1 - p := hq0
          have hstep : p + (1 - p) * (1 - q ^ t) = 1 - q ^ t * q := (by dsimp only [q]; ring)
          nlinarith [mul_le_mul_of_nonneg_left hd_ih h1p]
        · have hv0 : validInd n m k S s.val z = 0 := (by unfold validInd; exact ite_eq_right hval)
          rw [hv0, mul_zero]; exact (hdiag_real z).2.1
      · rw [qhlWhileSucc_val]; by_cases hτ : τ res = 0
        · rw [ite_eq_left hτ, ite_eq_left hτ, hbody_diag]
          exact congrArg diagonal (funext fun z ↦ (hdiag_real z).1)
        · rw [ite_eq_right hτ, ite_eq_right hτ]; dsimp only [post, validObs]; rw [realDiagObs_mat]
  intro σ
  have hgeom : ∀ t : ℕ, (validObs (Var := Var) n m k S s.val σ).1 - q ^ t • (validObs (Var := Var)
    n m k S s.val σ).1 ≤ (wp ((naiveStage res n m k hm s).compile qAssign oracle) post σ).1 := by
    intro t; rcases hunroll t with ⟨d_t, hd_bounds, hd_ge, hd_mat⟩
    have hsub_eq : (validObs (Var := Var) n m k S s.val σ).1 - q ^ t • (validObs (Var := Var) n m
      k S s.val σ).1 = (scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t) (sub_nonneg.mpr
      (pow_le_one₀ hq0 hq1.le)) (sub_le_self 1 (pow_nonneg hq0 t)) σ).1 := by
      rw [scaledValidObs_smul, sub_smul, one_smul]
    rw [hsub_eq]
    have hle_unroll : scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t) (sub_nonneg.mpr
      (pow_le_one₀ hq0 hq1.le)) (sub_le_self 1 (pow_nonneg hq0 t)) σ ≤ wp ((workReset res W M
      ((n + 1) * m)).compile qAssign oracle) (whileRecWP (wp bodyP) guard (t + 1) post) σ := by
      have hw := wp_mapAndMeasureLow res (resetWorkFn W M) oracle (fun val ↦ if val = 0 then
        diagonal (fun z ↦ (d_t z : ℂ)) else diagonal (fun z ↦ (validInd n m k S (s.val + 1) z :
        ℂ))) (whileRecWP (wp bodyP) guard (t + 1) post) hd_mat σ
      have hw' : ((wp ((workReset res W M ((n + 1) * m)).compile qAssign oracle)
          (whileRecWP (wp bodyP) guard (t + 1) post)) σ).1.1 =
          diagonal (fun z ↦ (d_t (resetWorkFn W M z) : ℂ)) := by
        rw [workReset, hw]; refine congrArg diagonal (funext fun z ↦ ?_)
        have h0 : Int.ofNat ((lowHighEquiv W M (resetWorkFn W M z)).1).val = 0 := by
          simp [resetWorkFn]
        rw [ite_eq_left h0, Matrix.diagonal_apply_eq]
      refine realDiagObs_le_of_mat (fun z ↦ (hd_bounds _).1) (fun z ↦ (hd_bounds _).2) hw'
        fun z ↦ ?_
      have hsnd : (lowHighEquiv (m * (n + 1)) (k * n) (resetWorkFn W M z)).2 =
          (lowHighEquiv (m * (n + 1)) (k * n) z).2 := by
        dsimp only [W, M, resetWorkFn]; rw [Equiv.apply_symm_apply]
      have hv_eq : validInd n m k S s.val (resetWorkFn W M z) = validInd n m k S s.val z := by
        open Classical in
        by_cases hv : MemPrefixValid S s.val (lowHighEquiv (m * (n + 1)) (k * n) z).2
        · have hv' : MemPrefixValid S s.val
              (lowHighEquiv (m * (n + 1)) (k * n) (resetWorkFn W M z)).2 := hsnd.symm ▸ hv
          unfold validInd; rw [ite_eq_left hv', ite_eq_left hv]
        · have hv' : ¬ MemPrefixValid S s.val
              (lowHighEquiv (m * (n + 1)) (k * n) (resetWorkFn W M z)).2 := hsnd.symm ▸ hv
          unfold validInd; rw [ite_eq_right hv', ite_eq_right hv]
      rw [← hv_eq]; exact hd_ge (resetWorkFn W M z)
    have hmon := wp_mono ((workReset res W M ((n + 1) * m)).compile qAssign oracle)
      (whileRecWP_le_wp_qWhile guard bodyP (t + 1) post) σ
    exact Subtype.coe_le_coe.mpr (hle_unroll.trans hmon)
  exact Subtype.coe_le_coe.mp (hermitian_le_of_geometric_sub_smul_le q hq0 hq1 _ _ _ hgeom)
/- ## Stationary Eigenvector-Locking Stage (`200 ≤ n`, `k < 2 ^ n`) -/
noncomputable def groverSubIter {Var : Type} (n m k : ℕ) (active : Finset (Fin k)) :
    ℕ → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | 0 => .skip
  | t + 1 =>
      .seq (groverSubIter n m k active t)
        (.seq (deflatedPhaseStep le_rfl active)
          (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
            ((addrReg n m).embedUnitary Grover.diffuserUnitary)))))
noncomputable def eigSetup {Var : Type} (res : Var) (n m k : ℕ)
    (s : Fin k) (K : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  let active := memPrefix k s.val
  .seq (workReset res W M ((n + 1) * m))
    (.seq (.step (phaseTag ((lowBlock W M).embedUnitary
        ((addrReg n m).embedUnitary hadamardUnitary))))
      (.seq (groverSubIter n m k active K)
        (deflatedPhaseStep le_rfl active)))
noncomputable def eigBody {Var : Type} (res : Var) (n m k : ℕ) (hm : 1 ≤ m)
    (s : Fin k) (cRatio : ℝ) (hc0 : 0 ≤ cRatio) (hc1 : cRatio ≤ 1) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  let active := memPrefix k s.val
  let diff := (lowBlock W M).embedUnitary ((addrReg n m).embedUnitary Grover.diffuserUnitary)
  let ch := (lowBlock W M).embedUnitary (chordUnitary n m hm cRatio hc0 hc1)
  .seq (.step (phaseTag diff))
    (.seq (.step (phaseTag ch))
      (.seq (deflatedPhaseStep le_rfl active)
        (.seq (.step (phaseTag ch))
          (.measure res ((lowBlock W M).compose (flag0Reg n m hm))))))
noncomputable def eigReadout {Var : Type} (n m k : ℕ) (s : Fin k) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
      (permutationUnitary (flipPerm n m)))))
    (markAndWrite n m k s)
noncomputable def eigLockStage {Var : Type} (res : Var) (n m k : ℕ)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn : 200 ≤ n) (s : Fin k) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let r := k - s.val
  let p := oddFrac n m r
  let K := subSchedule p
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
  .seq (eigSetup res n m k s K)
    (.seq (.qWhile (fun σ ↦ σ res = 0)
        (eigBody res n m k hm1 s (subTargetRatio p K) hhyps.1.le hhyps.2.1.le))
      (eigReadout n m k s))
private lemma pureUnitary_groverSubIter {Var : Type} (n m k : ℕ)
    (active : Finset (Fin k)) (oracle : Unitary (2 ^ ((n + 1) * m))) (t : ℕ) :
    PureUnitaryProg ((groverSubIter (Var := Var) n m k active t).compile qAssign oracle) := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih, ⟨trivial, ⟨trivial, trivial⟩, trivial⟩, trivial⟩
private lemma costBound_groverSubIter {Var : Type} [DecidableEq Var] (n m k : ℕ) (active : Finset
    (Fin k)) (S : Finset (Fin (2 ^ n))) (t : ℕ) : CostBound (Var := Var)
    (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) ((groverSubIter n m k active
    t).compile qAssign (groverParallelMarkingOracle m S)) (t : ℝ≥0) := by
  induction t with
  | zero =>
    simpa [groverSubIter, compile] using CostBound.skip_zero (Var := Var) (d := 2 ^ (m * (n + 1) +
      k * n)) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
  | succ t ih =>
    unfold groverSubIter; dsimp only [compile]
    have hor := isRealMatrix_groverParallelMarkingOracle m S
    have hstep := (costBound_deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
      (Q := m * (n + 1) + k * n) le_rfl active S).seq
      (costBound_qAssign_phaseTag (Var := Var) hor ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
          ((addrReg n m).embedUnitary Grover.diffuserUnitary)))
    simpa [Nat.cast_add, Nat.cast_one] using ih.seq hstep
private lemma costBound_eigSetup {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) (s : Fin
    k) (K : ℕ) (S : Finset (Fin (2 ^ n))) : CostBound (Var := Var) (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((eigSetup res n m k s K).compile qAssign
    (groverParallelMarkingOracle m S)) ((K + 1 : ℕ) : ℝ≥0) := by
  unfold eigSetup workReset; dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have h0 := costBound_mapAndMeasureLow (Var := Var) res (resetWorkFn (m * (n + 1)) (k * n)) hor
  have hH := costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary ((addrReg n m).embedUnitary hadamardUnitary))
  have hK := costBound_groverSubIter (Var := Var) n m k (memPrefix k s.val) S K
  have hph := costBound_deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
    (Q := m * (n + 1) + k * n) le_rfl (memPrefix k s.val) S
  simpa [Nat.cast_add, Nat.cast_one] using h0.seq (hH.seq (hK.seq hph))
private lemma costBound_eigBody {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) (hm : 1 ≤
    m) (s : Fin k) (cRatio : ℝ) (hc0 : 0 ≤ cRatio) (hc1 : cRatio ≤ 1) (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    ((eigBody res n m k hm s cRatio hc0 hc1).compile qAssign (groverParallelMarkingOracle m S))
    1 := by
  unfold eigBody; dsimp only [compile]; have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hd := costBound_qAssign_phaseTag (Var := Var) hor ((lowBlock (m * (n + 1)) (k *
    n)).embedUnitary ((addrReg n m).embedUnitary Grover.diffuserUnitary))
  have hc := costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (chordUnitary n m hm cRatio hc0 hc1))
  have hp := costBound_deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
    (Q := m * (n + 1) + k * n) le_rfl (memPrefix k s.val) S
  have hm_cost : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m
    S)) (measureRegister res ((lowBlock (m * (n + 1)) (k * n)).compose (flag0Reg n m hm))) 0 := by
    simpa [measureRegister, CostModel.ofEmbeddedOracle] using CostBound.qMeasure (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) res _
  simpa using hd.seq (hc.seq (hp.seq (hc.seq hm_cost)))
private lemma costBound_eigReadout {Var : Type} [DecidableEq Var] (n m k : ℕ) (s : Fin k) (S :
    Finset (Fin (2 ^ n))) : CostBound (Var := Var) (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((eigReadout n m k s).compile qAssign
    (groverParallelMarkingOracle m S)) 1 := by
  unfold eigReadout; dsimp only [compile]; have hor := isRealMatrix_groverParallelMarkingOracle m S
  simpa using (costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (permutationUnitary (flipPerm n m)))).seq
    (costBound_markAndWrite (Var := Var) n m k s S)
private lemma vecQuad_groverSubIter {Var : Type} [DecidableEq Var] {n m k : ℕ} {S : Finset (Fin (2
    ^ n))} (s : Fin k) (μ : Fin (2 ^ (k * n))) (hval : MemPrefixValid S s.val μ) (t : ℕ) (Θ :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) :
    let R := S \ memSeen n k (memPrefix k s.val) μ
    vecQuad (((wp ((OracleDynamicCircuit.seq (.step (phaseTag ((lowBlock (m * (n + 1)) (k *
      n)).embedUnitary ((addrReg n m).embedUnitary hadamardUnitary)))) (groverSubIter n m k
      (memPrefix k s.val) t)).compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState (Pi.single 0 1) (Pi.single μ 1)) = vecQuad ((Θ σ).1.1) (workMemState ((addrReg
      n m).tensorState (subsetGroverState (oddSet n m R) t) (Pi.single 0 1)) (Pi.single μ
      1)) := by
  intro R
  have hsub : memSeen n k (memPrefix k s.val) μ ⊆ S := (card_memSeen_of_memPrefixValid hval).2
  induction t generalizing Θ with
  | zero =>
    dsimp only [groverSubIter, compile]
    rw [wp_qSeq, wp_skip, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      embedMatrix_lowBlock_mulVec_workMemState, ← tensorState_zero_zero n m,
      embed_addrReg_mulVec_zero, hadamardUnitary_coe, hadamard_mulVec_zero (m * n) (oddSet n m R)]
  | succ t ih =>
    have hassoc : wp ((OracleDynamicCircuit.seq (.step (phaseTag ((lowBlock (m * (n + 1)) (k *
      n)).embedUnitary ((addrReg n m).embedUnitary hadamardUnitary)))) (groverSubIter n m k
      (memPrefix k s.val) (t + 1))).compile qAssign (groverParallelMarkingOracle m S)) Θ = wp
      ((OracleDynamicCircuit.seq (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
      ((addrReg n m).embedUnitary hadamardUnitary)))) (groverSubIter n m k (memPrefix k s.val)
      t)).compile qAssign (groverParallelMarkingOracle m S)) (wp ((OracleDynamicCircuit.seq
      (deflatedPhaseStep le_rfl (memPrefix k s.val)) (.step (phaseTag ((lowBlock (m * (n + 1))
      (k * n)).embedUnitary ((addrReg n m).embedUnitary Grover.diffuserUnitary))))).compile
      qAssign (groverParallelMarkingOracle m S)) Θ) := by
      simp [groverSubIter, compile, wp_qSeq]
    rw [hassoc, ih]; dsimp only [compile]
    rw [wp_qSeq, wp_deflatedPhaseStep_vecQuad (memPrefix k s.val) _ μ hsub,
      sDiagM_mulVec_tensorState_zero, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      vecQuad_conj, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      embedMatrix_lowBlock_mulVec_workMemState, embed_addrReg_mulVec_zero]; rfl
private lemma flag0FullReg_projector_mulVec_workMemState {n m k : ℕ} (hm : 1 ≤ m) (o : Fin (2 ^
    1)) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (φ : Fin (2 ^ (k * n)) → ℂ) : ((lowBlock (m * (n + 1))
    (k * n)).compose (flag0Reg n m hm)).basisOutcomeProjector o *ᵥ workMemState ψ φ = workMemState
    ((flag0Reg n m hm).basisOutcomeProjector o *ᵥ ψ) φ := by
  funext z
  rw [QRegister.basisOutcomeProjector_eq_diagonal, mulVec_diagonal]; dsimp only [workMemState]
  rw [QRegister.extractIndex_compose, extractIndex_lowBlock,
    QRegister.basisOutcomeProjector_eq_diagonal, mulVec_diagonal]; ring
private lemma sum_normSq_workMemState_tensor_zero {n m k : ℕ} (v : Fin (2 ^ (m * n)) → ℂ) (μ : Fin
    (2 ^ (k * n))) : (∑ z : Fin (2 ^ (m * (n + 1) + k * n)), normSq (workMemState ((addrReg n
    m).tensorState v (Pi.single 0 1)) (Pi.single μ 1) z)) = ∑ u : Fin (2 ^ (m * n)), normSq (v
    u) := by
  let W := m * (n + 1); let M := k * n
  let f (z : Fin (2 ^ (W + M))) :=
    normSq (workMemState ((addrReg n m).tensorState v (Pi.single 0 1)) (Pi.single μ 1) z)
  change ∑ z, f z = _; rw [← (lowHighEquiv W M).symm.sum_comp f, Fintype.sum_prod_type]
  have h1 (w : Fin (2 ^ W)) : (∑ μ' : Fin (2 ^ M), f ((lowHighEquiv W M).symm (w, μ'))) = normSq
    ((addrReg n m).tensorState v (Pi.single 0 1) w) := by
    rw [sum_eq_single μ (fun μ' hμ' ↦ by
      dsimp only [f, workMemState]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hμ', mul_zero, Complex.normSq_zero])]
    dsimp only [f, workMemState]; rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  simp_rw [h1]; rw [← (addrReg n m).basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [sum_eq_single 0 (fun e he ↦ by
    dsimp only [Function.comp_apply, QRegister.tensorState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero])]
  dsimp only [Function.comp_apply, QRegister.tensorState]
  rw [ ← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
private lemma vecQuad_eigBody_step {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) (hm_grid
    : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard
    : S.card = k) (s : Fin k) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s.val μ) (Ψ :
    CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (τ : Store Var) :
    let r := k - s.val; let p := oddFrac n m r; let K := subSchedule p
    let hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    let hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
    let R := S \ memSeen n k (memPrefix k s.val) μ; let M_odd := oddSet n m R
    let cRatio := subTargetRatio p K; let φ_K := oracleMat M_odd *ᵥ subsetGroverState M_odd K
    let v₁ := subsetKraus1 M_odd cRatio *ᵥ subsetGroverState M_odd (K + 1)
    let ψ_init := workMemState ((addrReg n m).tensorState φ_K (Pi.single 0 1)) (Pi.single μ 1)
    let ψ_exit := workMemState ((addrReg n m).tensorState v₁ (Pi.single 1 1)) (Pi.single μ 1)
    vecQuad (((wp ((eigBody res n m k hm1 s cRatio hhyps.1.le hhyps.2.1.le).compile qAssign
      (groverParallelMarkingOracle m S)) Ψ) τ).1.1) ψ_init = (subFailProb p K : ℂ) * vecQuad ((Ψ
      (Store.subst τ res 0)).1.1) ψ_init + vecQuad ((Ψ (Store.subst τ res 1)).1.1) ψ_exit := by
  intro r p K hm1 hhyps R M_odd cRatio φ_K v₁ ψ_init ψ_exit
  have hcm := card_memSeen_of_memPrefixValid hval
  have hR_card : R.card = r := (by rw [Finset.card_sdiff_of_subset hcm.2, hcard, hcm.1])
  have hp_eq : ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ)) = p := by
    rw [card_oddSet_div_two_pow n m R, hR_card]
  have h2r_le : 2 * r ≤ 2 ^ n := by
    have hk_hi := le_1024_of_mem_groverGrid hk_grid
    calc 2 * r ≤ 2 * 1024 := by omega
      _ ≤ 2 ^ 200 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hp_pos_lt := oddFrac_pos_lt_one (n := n) hm1 (by omega : 1 ≤ r) (by omega : r < 2 ^ n)
  have hM0 : 0 < M_odd.card := by
    by_contra! h0
    have h0' : M_odd.card = 0 := (by omega); have hp0 : p = 0 := (by rw [← hp_eq, h0']; simp)
    linarith [hp_pos_lt.1]
  have hMlt : M_odd.card < 2 ^ (m * n) := by
    by_contra! hge
    have hp1 : 1 ≤ p := by
      rw [← hp_eq]; exact ( one_le_div (by positivity)).mpr (by exact_mod_cast hge)
    linarith [hp_pos_lt.2]
  have hsin3 : sin ((2 * (K : ℝ) + 3) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
      0 := by
    rw [hp_eq]; exact hhyps.2.2.1
  have hcos1 : cos ((2 * (K : ℝ) + 1) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
      0 := by
    rw [hp_eq]; exact hhyps.2.2.2.1
  have hkraus0 : subsetKraus0 M_odd cRatio *ᵥ subsetGroverState M_odd (K + 1) =
      (subNonTargetRatio p K : ℂ) • φ_K := by
    have hk0 := subsetKraus0_mulVec_subsetGroverState M_odd hM0 hMlt K hsin3 hcos1
    dsimp only at hk0; simpa only [hp_eq] using hk0
  unfold eigBody; dsimp only [compile]
  rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
    QRegister.embedUnitary_val, QRegister.embedUnitary_val,
    embedMatrix_lowBlock_mulVec_workMemState, embed_addrReg_mulVec_zero]
  change vecQuad _ (workMemState ((addrReg n m).tensorState
    (subsetGroverState M_odd (K + 1)) (Pi.single 0 1)) (Pi.single μ 1)) = _
  rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
    QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
    wp_qSeq, wp_deflatedPhaseStep_vecQuad (memPrefix k s.val) _ μ hcm.2,
    wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
    QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
    chord_sDiagM_chord_mulVec_zero hm1 hhyps.1.le hhyps.2.1.le R (subsetGroverState M_odd (K + 1)),
    hkraus0, (addrReg n m).tensorState_smul_left, workMemState_add_left, workMemState_smul_left]
  set ψ_tot := (subNonTargetRatio p K : ℂ) • ψ_init + ψ_exit; rw [wp_measureRegister]
  let reg0 := (lowBlock (m * (n + 1)) (k * n)).compose (flag0Reg n m hm1)
  have hsum2 : (∑ o : Fin (2 ^ 1), reg0.basisOutcomeProjector o * (Ψ (Store.subst τ res (Int.ofNat
    o.val))).1.1 * reg0.basisOutcomeProjector o) = reg0.basisOutcomeProjector 0 * (Ψ (Store.subst
    τ res 0)).1.1 * reg0.basisOutcomeProjector 0 + reg0.basisOutcomeProjector 1 * (Ψ (Store.subst
    τ res 1)).1.1 * reg0.basisOutcomeProjector 1 := Fin.sum_univ_two fun o : Fin 2 ↦
    reg0.basisOutcomeProjector o * (Ψ (Store.subst τ res (Int.ofNat o.val))).1.1 *
    reg0.basisOutcomeProjector o
  rw [hsum2]; have hadd_quad (A B : Operator (2 ^ (m * (n + 1) + k * n))) (ψ : Fin _ → ℂ) :
      vecQuad (A + B) ψ = vecQuad A ψ + vecQuad B ψ := by
    simp [vecQuad, Matrix.add_mulVec, dotProduct_add]
  rw [hadd_quad]
  have hp0_adj : (reg0.basisOutcomeProjector 0)ᴴ = reg0.basisOutcomeProjector 0 :=
    QRegister.basisOutcomeProjector_conjTranspose reg0 0
  have hp1_adj : (reg0.basisOutcomeProjector 1)ᴴ = reg0.basisOutcomeProjector 1 :=
    QRegister.basisOutcomeProjector_conjTranspose reg0 1
  nth_rw 1 [← hp0_adj]; nth_rw 1 [← hp1_adj]; rw [vecQuad_conj, vecQuad_conj]
  have hproj := flag0Reg_basisOutcomeProjector_mulVec hm1 ((subNonTargetRatio p K : ℂ) • φ_K) v₁
  have hp0_vec : reg0.basisOutcomeProjector 0 *ᵥ ψ_tot = (subNonTargetRatio p K : ℂ) • ψ_init := by
    dsimp only [ψ_tot, ψ_init, ψ_exit, reg0]
    rw [← workMemState_smul_left, ← (addrReg n m).tensorState_smul_left,
      ← workMemState_add_left, flag0FullReg_projector_mulVec_workMemState, hproj.1,
      (addrReg n m).tensorState_smul_left, workMemState_smul_left]
  have hp1_vec : reg0.basisOutcomeProjector 1 *ᵥ ψ_tot = ψ_exit := by
    dsimp only [ψ_tot, ψ_init, ψ_exit, reg0]
    rw [← workMemState_smul_left, ← (addrReg n m).tensorState_smul_left,
      ← workMemState_add_left, flag0FullReg_projector_mulVec_workMemState, hproj.2]
  rw [hp0_vec, hp1_vec, vecQuad_smul]; rfl
lemma eigLockStage_wp_and_active {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn : 200 ≤ n)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k) :
    let r := k - s.val; let p := oddFrac n m r; let K := subSchedule p
    let hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    let hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
    let oracle := groverParallelMarkingOracle m S
    let setupP := (eigSetup (Var := Var) res n m k s K).compile qAssign oracle
    let bodyP := (eigBody (Var := Var) res n m k hm1 s (subTargetRatio p K)
      hhyps.1.le hhyps.2.1.le).compile qAssign oracle
    let guard : Store Var → Prop := fun σ ↦ σ res = 0; let q := subFailProb p K
    validObs (Var := Var) n m k S s.val ≤ wp ((eigLockStage res n m k hm_grid hk_grid hn
      s).compile qAssign oracle) (validObs n m k S (s.val + 1)) ∧ ∀ t : ℕ, wp setupP
      (whileActiveWP (wp bodyP) guard t) ≤ (scaledValidObs n m k S s.val (q ^ t) (pow_nonneg
      (subFailProb_nonneg p K) t) (pow_le_one₀ (subFailProb_nonneg p K) hhyps.2.2.2.2.le)).add
      (invalidObs n m k S s.val) (scaledValid_add_invalid_le_one n m k S s.val (q ^ t) _ _) := by
  intro r p K hm1 hhyps oracle setupP bodyP guard q; let W := m * (n + 1); let M := k * n
  let readoutP := (eigReadout (Var := Var) n m k s).compile qAssign oracle
  let post := validObs (Var := Var) n m k S (s.val + 1); let Θ_read := wp readoutP post
  have hΘ_const : ∃ M_read : Operator (2 ^ (W + M)), ∀ τ, (Θ_read τ).1.1 = M_read := by
    refine ⟨(Θ_read (fun _ ↦ 0)).1.1, fun τ ↦ ?_⟩
    have hread_eq := wp_eq_of_pureUnitary (P := readoutP) ⟨trivial, ⟨trivial, trivial⟩, trivial⟩
      (rfl : post τ = post (fun _ ↦ 0))
    exact congrArg (fun O : Observable _ ↦ O.1.1) hread_eq
  rcases hΘ_const with ⟨M_read, hM_read⟩
  have hbody_const (Ψ : CQAssertion (Store Var) (2 ^ (W + M))) (H : ℤ → Operator (2 ^ (W + M))) (hΨ
    : ∀ τ,
    (Ψ τ).1.1 = H (τ res)) : ∃ M_b : Operator (2 ^ (W + M)), ∀ τ, ((wp bodyP Ψ) τ).1.1 = M_b := by
    refine ⟨((wp bodyP Ψ) (fun _ ↦ 0)).1.1, fun τ ↦ ?_⟩
    let reg0 := (lowBlock (m * (n + 1)) (k * n)).compose (flag0Reg n m hm1)
    have hmeas (τ' : Store Var) : ((wp (measureRegister res reg0) Ψ) τ').1.1 = ∑ o : Fin (2 ^ 1),
      reg0.basisOutcomeProjector o * H (Int.ofNat o.val) * reg0.basisOutcomeProjector o := by
      rw [wp_measureRegister]; exact Finset.sum_congr rfl fun o _ ↦ by rw [hΨ]; simp [Store.subst]
    have hmeas_obs : wp (measureRegister res reg0) Ψ τ = wp (measureRegister res reg0) Ψ (fun _ ↦
      0) := Subtype.ext (HermitianMat.ext ((hmeas τ).trans (hmeas (fun _ ↦ 0)).symm))
    let diffU := (lowBlock (m * (n + 1)) (k * n)).embedUnitary
      ((addrReg n m).embedUnitary Grover.diffuserUnitary)
    let chU := (lowBlock (m * (n + 1)) (k * n)).embedUnitary
      (chordUnitary n m hm1 (subTargetRatio p K) hhyps.1.le hhyps.2.1.le)
    let phP := (deflatedPhaseStep (Var := Var) (Q := m * (n + 1) + k * n) le_rfl
      (memPrefix k s.val)).compile qAssign oracle
    have h1 := wp_eq_of_pureUnitary (P := .qAssign (phaseTag chU)) trivial hmeas_obs
    have h2 := wp_eq_of_pureUnitary (P := phP) ⟨trivial, ⟨trivial, trivial⟩, trivial⟩ h1
    have h3 := wp_eq_of_pureUnitary (P := .qAssign (phaseTag chU)) trivial h2
    have h4 := wp_eq_of_pureUnitary (P := .qAssign (phaseTag diffU)) trivial h3
    dsimp only [bodyP, eigBody, compile]; rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qSeq]
    exact congrArg (fun O : Observable _ ↦ O.1.1) h4
  have hsetup_diag (Ψ : CQAssertion (Store Var) (2 ^ (W + M)))
      (M_0 M_1 : Operator (2 ^ (W + M)))
      (hΨ : ∀ τ, (Ψ τ).1.1 = if τ res = 0 then M_0 else M_1) :
      ∃ d_s : Fin (2 ^ (W + M)) → ℝ, (∀ z, 0 ≤ d_s z ∧ d_s z ≤ 1) ∧
        (∀ τ, ((wp setupP Ψ) τ).1.1 = diagonal (fun z ↦ (d_s z : ℂ))) ∧
        ∀ z, MemPrefixValid S s.val (lowHighEquiv W M z).2 → (d_s z : ℂ) =
            let μ := (lowHighEquiv W M z).2; let R := S \ memSeen n k (memPrefix k s.val) μ
            let M_odd := oddSet n m R
            vecQuad M_0
              (workMemState ((addrReg n m).tensorState
                  (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
                (Pi.single μ 1)) := by
    let tailC : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) := .seq (.step (phaseTag
      ((lowBlock (m * (n + 1)) (k * n)).embedUnitary ((addrReg n m).embedUnitary
      hadamardUnitary)))) (.seq (groverSubIter n m k (memPrefix k s.val) K) (deflatedPhaseStep
      le_rfl (memPrefix k s.val)))
    let tailP := tailC.compile qAssign oracle
    have htail_pure : PureUnitaryProg tailP := ⟨trivial, pureUnitary_groverSubIter n m k
      (memPrefix k s.val) oracle K, trivial, ⟨trivial, trivial⟩, trivial⟩
    let N_0 : Operator (2 ^ (W + M)) := ((wp tailP Ψ) (fun _ ↦ 0)).1.1
    let N_1 : Operator (2 ^ (W + M)) := ((wp tailP Ψ) (fun _ ↦ 1)).1.1
    have hN_dep (τ : Store Var) : ((wp tailP Ψ) τ).1.1 = if τ res = 0 then N_0 else N_1 := by
      by_cases h0 : τ res = 0
      · rw [ite_eq_left h0]
        have hΨ0 : Ψ τ = Ψ (fun _ ↦ 0) := Subtype.ext (HermitianMat.ext (by
          change (Ψ τ).1.1 = (Ψ (fun _ ↦ 0)).1.1
          rw [hΨ τ, hΨ (fun _ ↦ 0), ite_eq_left h0, ite_eq_left rfl]))
        exact congrArg (fun O : Observable _ ↦ O.1.1) (wp_eq_of_pureUnitary htail_pure hΨ0)
      · rw [ite_eq_right h0]
        have hΨ1 : Ψ τ = Ψ (fun _ ↦ 1) := Subtype.ext (HermitianMat.ext (by
          change (Ψ τ).1.1 = (Ψ (fun _ ↦ 1)).1.1
          rw [hΨ τ, hΨ (fun _ ↦ 1), ite_eq_right h0, ite_eq_right (by omega : (1 : ℤ) ≠ 0)]))
        exact congrArg (fun O : Observable _ ↦ O.1.1) (wp_eq_of_pureUnitary htail_pure hΨ1)
    have hN_val (μ : Fin (2 ^ M)) (hval : MemPrefixValid S s.val μ) :
        N_0 ((lowHighEquiv W M).symm (0, μ)) ((lowHighEquiv W M).symm (0, μ)) =
          let R := S \ memSeen n k (memPrefix k s.val) μ; let M_odd := oddSet n m R
          vecQuad M_0
            (workMemState ((addrReg n m).tensorState
                (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
              (Pi.single μ 1)) := by
      rw [vecQuad_single N_0, ← workMemState_single]
      have hassoc : wp tailP Ψ = wp ((OracleDynamicCircuit.seq (.step (phaseTag ((lowBlock (m *
        (n + 1)) (k * n)).embedUnitary ((addrReg n m).embedUnitary hadamardUnitary))))
        (groverSubIter n m k (memPrefix k s.val) K)).compile qAssign oracle) (wp
        ((deflatedPhaseStep le_rfl (memPrefix k s.val)).compile qAssign oracle) Ψ) := by
        dsimp only [tailP, tailC, compile]; rw [wp_qSeq, wp_qSeq, wp_qSeq]
      dsimp only [N_0]
      rw [hassoc, vecQuad_groverSubIter s μ hval K _ (fun _ ↦ 0), wp_deflatedPhaseStep_vecQuad
        (memPrefix k s.val) _ μ (card_memSeen_of_memPrefixValid hval).2,
        sDiagM_mulVec_tensorState_zero, hΨ (fun _ ↦ 0), ite_eq_left rfl]
    have hwp_s (τ : Store Var) : ((wp setupP Ψ) τ).1.1 = diagonal (fun z ↦ N_0 (resetWorkFn W M z)
      (resetWorkFn W M z)) := by
      have hseq : wp setupP Ψ = wp ((workReset res (m * (n + 1)) (k * n) ((n + 1) * m)).compile
        qAssign oracle) (wp tailP Ψ) := by
        dsimp only [setupP, eigSetup, tailP, tailC, compile]; rw [wp_qSeq]
      rw [hseq, workReset, wp_mapAndMeasureLow res (resetWorkFn W M) oracle
          (fun val ↦ if val = 0 then N_0 else N_1) (wp tailP Ψ) hN_dep τ]
      refine congrArg diagonal (funext fun z ↦ ?_)
      have h0 : Int.ofNat ((lowHighEquiv W M (resetWorkFn W M z)).1).val = 0 := by
        simp [resetWorkFn]
      rw [ite_eq_left h0]
    let d_s (z : Fin (2 ^ (W + M))) : ℝ := (N_0 (resetWorkFn W M z) (resetWorkFn W M z)).re
    have hreal_bounds (z : Fin (2 ^ (W + M))) : N_0 (resetWorkFn W M z) (resetWorkFn W M z) = (d_s
      z : ℂ) ∧ 0 ≤ d_s z ∧ d_s z ≤ 1 := observable_diag_real_bounds (wp setupP Ψ (fun _ ↦ 0)) (fun
      y ↦ N_0 (resetWorkFn W M y) (resetWorkFn W M y)) (hwp_s (fun _ ↦ 0)) z
    refine ⟨d_s, fun z ↦ ⟨(hreal_bounds z).2.1, (hreal_bounds z).2.2⟩, fun τ ↦ (hwp_s τ).trans
      (congrArg diagonal (funext fun z ↦ (hreal_bounds z).1)), fun z hval ↦ ?_⟩
    rw [← (hreal_bounds z).1]; exact hN_val (lowHighEquiv W M z).2 hval
  -- Active-mass survival induction on t
  have hact_mat (t : ℕ) :
      ∃ A_t : Operator (2 ^ (W + M)),
        (∀ τ, (whileActiveWP (wp bodyP) guard t τ).1.1 = if τ res = 0 then A_t else 0) ∧
        ∀ μ : Fin (2 ^ M), MemPrefixValid S s.val μ →
          let R := S \ memSeen n k (memPrefix k s.val) μ; let M_odd := oddSet n m R
          vecQuad A_t
            (workMemState ((addrReg n m).tensorState
                (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
              (Pi.single μ 1)) = ((q ^ t : ℝ) : ℂ) := by
    induction t with
    | zero =>
      refine ⟨1, fun τ ↦ by by_cases h : τ res = 0 <;> simp [whileActiveWP, guard, h],
        fun μ hval ↦ ?_⟩
      intro R M_odd
      have h1 : (1 : Operator (2 ^ (W + M))) = diagonal (fun _ ↦ (1 : ℂ)) := by
        ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
      rw [h1, vecQuad_diagonal]; simp_rw [mul_one]; rw [← ofReal_sum]; dsimp only [W, M]
      rw [sum_normSq_workMemState_tensor_zero]; have hcm := card_memSeen_of_memPrefixValid hval
      have hR_card : R.card = r := (by rw [Finset.card_sdiff_of_subset hcm.2, hcard, hcm.1])
      have hp_eq : ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ)) = p := by
        rw [card_oddSet_div_two_pow n m R, hR_card]
      have h2r_le : 2 * r ≤ 2 ^ n := by
        have hk_hi := le_1024_of_mem_groverGrid hk_grid
        calc 2 * r ≤ 2 * 1024 := by omega
          _ ≤ 2 ^ 200 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      have hp_pos_lt := oddFrac_pos_lt_one (n := n) hm1 (by omega : 1 ≤ r) (by omega : r < 2 ^ n)
      have hM0 : 0 < M_odd.card := by
        by_contra! h0
        have hp0 : p = 0 := (by rw [← hp_eq, show M_odd.card = 0 by omega]; simp)
        linarith [hp_pos_lt.1]
      have hMlt : M_odd.card < 2 ^ (m * n) := by
        by_contra! hge
        have hp1 : 1 ≤ p := by
          rw [← hp_eq]; exact (one_le_div (by positivity)).mpr (by exact_mod_cast hge)
        linarith [hp_pos_lt.2]
      rw [(sum_normSq_subsetGroverState M_odd hM0 hMlt K).2, pow_zero]
    | succ t ih =>
      rcases ih with ⟨A_t, hA_dep, hA_val⟩; rcases hbody_const (whileActiveWP (wp bodyP) guard t)
        (fun val ↦ if val = 0 then A_t else 0) hA_dep with ⟨M_b, hM_b⟩
      refine ⟨M_b, fun τ ↦ ?_, fun μ hval ↦ ?_⟩
      · dsimp only [whileActiveWP]; by_cases hτ : guard τ
        · have hτ0 : τ res = 0 := hτ; rw [ite_eq_left hτ, ite_eq_left hτ0, hM_b]
        · have hτ0 : τ res ≠ 0 := hτ; rw [ite_eq_right hτ, ite_eq_right hτ0]; rfl
      · intro R M_odd
        rw [← hM_b (fun _ ↦ 0), vecQuad_eigBody_step res hm_grid hk_grid hn hcard s hval]
        have hs0 : (whileActiveWP (wp bodyP) guard t
            (Store.subst (fun _ : Var ↦ (0 : ℤ)) res 0)).1.1 = A_t := by
          rw [hA_dep]; simp [Store.subst]
        have hs1 : (whileActiveWP (wp bodyP) guard t
            (Store.subst (fun _ : Var ↦ (0 : ℤ)) res 1)).1.1 = 0 := by
          rw [hA_dep]; simp [Store.subst]
        rw [hs0, hs1, hA_val μ hval, show vecQuad 0 _ = 0 by simp [vecQuad], add_zero, pow_succ']
        push_cast; rfl
  -- Unrolled correctness induction on t
  have hread_val (μ : Fin (2 ^ M)) (hval : MemPrefixValid S s.val μ) :
      let R := S \ memSeen n k (memPrefix k s.val) μ; let M_odd := oddSet n m R
      let v₁ := subsetKraus1 M_odd (subTargetRatio p K) *ᵥ subsetGroverState M_odd (K + 1)
      vecQuad M_read
        (workMemState ((addrReg n m).tensorState v₁ (Pi.single 1 1)) (Pi.single μ 1)) =
        ((1 - q : ℝ) : ℂ) := by
    intro R M_odd v₁; have hcm := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = r := (by rw [Finset.card_sdiff_of_subset hcm.2, hcard, hcm.1])
    have hp_eq : ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ)) = p := by
      rw [card_oddSet_div_two_pow n m R, hR_card]
    have h2r_le : 2 * r ≤ 2 ^ n := by
      have hk_hi := le_1024_of_mem_groverGrid hk_grid
      calc 2 * r ≤ 2 * 1024 := by omega
        _ ≤ 2 ^ 200 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have hp_pos_lt := oddFrac_pos_lt_one (n := n) hm1 (by omega : 1 ≤ r) (by omega : r < 2 ^ n)
    have hM0 : 0 < M_odd.card := by
      by_contra! h0
      have hp0 : p = 0 := (by rw [← hp_eq, show M_odd.card = 0 by omega]; simp)
      linarith [hp_pos_lt.1]
    have hMlt : M_odd.card < 2 ^ (m * n) := by
      by_contra! hge
      have hp1 : 1 ≤ p := by
        rw [← hp_eq]; exact (one_le_div (by positivity)).mpr (by exact_mod_cast hge)
      linarith [hp_pos_lt.2]
    have hs_le1 : (subTargetRatio ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ)) K) ^ 2 ≤ 1 := by
      rw [hp_eq]; nlinarith [hhyps.1, hhyps.2.1]
    have hsin3 : sin ((2 * (K : ℝ) + 3) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
        0 := by
      rw [hp_eq]; exact hhyps.2.2.1
    have hcos1 : cos ((2 * (K : ℝ) + 1) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
        0 := by
      rw [hp_eq]; exact hhyps.2.2.2.1
    have hk1 := sum_normSq_subsetKraus1_subsetGroverState M_odd hM0 hMlt K hs_le1 hsin3 hcos1
    dsimp only at hk1; simp only [hp_eq] at hk1; rw [← hM_read (fun _ ↦ 0)]
    dsimp only [Θ_read, readoutP, eigReadout, compile]
    rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
      QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      permutationUnitary_flipPerm_mulVec_tensorState, addrEnv_one_add_one, vecQuad_markAndWrite s
      v₁ μ hval (fun z ↦ (validInd n m k S (s.val + 1) z : ℂ)) post (fun _ ↦ 0) (realDiagObs_mat _
      _ _)]
    let w_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (m * (n + 1))) :=
      parallelMarkPerm n m R ((addrReg n m).basisSplitEquiv.symm (u, 0))
    let μ_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (k * n)) := (addrEquiv n k).symm (addrEquiv n k
      μ + batchDelta s.val (fun w ↦ (firstMarkedAddr n m w).toList) (w_of u))
    have hterm (u : Fin (2 ^ (m * n))) : (normSq (v₁ u) : ℂ) * (validInd n m k S (s.val + 1)
      ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) : ℂ) = (normSq (v₁ u) :
      ℂ) := by
      by_cases hu : u ∈ M_odd
      · have hadv := (markAndWrite_outcome_props s hval u).2.1 hu
        have hv1 : validInd n m k S (s.val + 1)
            ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) = 1 := by
          unfold validInd; rw [Equiv.apply_symm_apply, ite_eq_left hadv.2]
        rw [hv1, Complex.ofReal_one, mul_one]
      · dsimp only [v₁]; rw [hk1.1 u hu, Complex.normSq_zero, Complex.ofReal_zero, zero_mul]
    rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← ofReal_sum, hk1.2]
  have hrec_mat (t : ℕ) :
      ∃ B_t : Operator (2 ^ (W + M)), (∀ τ, (whileRecWP (wp bodyP) guard (t + 1) Θ_read τ).1.1 =
          if τ res = 0 then B_t else M_read) ∧
        ∀ μ : Fin (2 ^ M), MemPrefixValid S s.val μ →
          let R := S \ memSeen n k (memPrefix k s.val) μ; let M_odd := oddSet n m R
          vecQuad B_t
            (workMemState ((addrReg n m).tensorState
                (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
              (Pi.single μ 1)) = ((1 - q ^ t : ℝ) : ℂ) := by
    induction t with
    | zero =>
      rcases hbody_const (whileRecWP (wp bodyP) guard 0 Θ_read)
        (fun _ ↦ 0) (fun _ ↦ rfl) with ⟨M_b0, hM_b0⟩
      refine ⟨M_b0, fun τ ↦ ?_, fun μ hval ↦ ?_⟩
      · rw [qhlWhileSucc_val]; by_cases hτ : τ res = 0
        · rw [ite_eq_left hτ, ite_eq_left hτ, hM_b0]
        · rw [ite_eq_right hτ, ite_eq_right hτ, hM_read]
      · intro R M_odd
        rw [← hM_b0 (fun _ ↦ 0), vecQuad_eigBody_step res hm_grid hk_grid hn hcard s hval]
        change (q : ℂ) * vecQuad 0 _ + vecQuad 0 _ = ((1 - q ^ 0 : ℝ) : ℂ); simp [vecQuad]
    | succ t ih =>
      rcases ih with ⟨B_t, hB_dep, hB_val⟩
      rcases hbody_const (whileRecWP (wp bodyP) guard (t + 1) Θ_read)
        (fun val ↦ if val = 0 then B_t else M_read) hB_dep with ⟨M_b, hM_b⟩
      refine ⟨M_b, fun τ ↦ ?_, fun μ hval ↦ ?_⟩
      · rw [qhlWhileSucc_val]; by_cases hτ : τ res = 0
        · rw [ite_eq_left hτ, ite_eq_left hτ, hM_b]
        · rw [ite_eq_right hτ, ite_eq_right hτ, hM_read]
      · intro R M_odd
        rw [← hM_b (fun _ ↦ 0), vecQuad_eigBody_step res hm_grid hk_grid hn hcard s hval]
        have hs0 : (whileRecWP (wp bodyP) guard (t + 1) Θ_read
            (Store.subst (fun _ : Var ↦ (0 : ℤ)) res 0)).1.1 = B_t := by
          rw [hB_dep]; simp [Store.subst]
        have hs1 : (whileRecWP (wp bodyP) guard (t + 1) Θ_read
            (Store.subst (fun _ : Var ↦ (0 : ℤ)) res 1)).1.1 = M_read := by
          rw [hB_dep]; simp [Store.subst]
        rw [hs0, hs1, hB_val μ hval, hread_val μ hval, pow_succ']; push_cast; ring
  have hq0 : 0 ≤ q := subFailProb_nonneg p K; have hq1 : q < 1 := hhyps.2.2.2.2
  refine ⟨fun σ ↦ ?_, fun t σ ↦ ?_⟩
  · have hgeom : ∀ t : ℕ, (validObs (Var := Var) n m k S s.val σ).1 -
            q ^ t • (validObs (Var := Var) n m k S s.val σ).1 ≤
          (wp ((eigLockStage res n m k hm_grid hk_grid hn s).compile qAssign oracle) post σ).1 := by
      intro t; rcases hrec_mat t with ⟨B_t, hB_dep, hB_val⟩
      rcases hsetup_diag (whileRecWP (wp bodyP) guard (t + 1) Θ_read) B_t M_read hB_dep with
        ⟨d_s, hd_bounds, hd_mat, hd_val⟩
      have hsub_eq : (validObs (Var := Var) n m k S s.val σ).1 - q ^ t • (validObs (Var := Var) n
        m k S s.val σ).1 = (scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t) (sub_nonneg.mpr
        (pow_le_one₀ hq0 hq1.le)) (sub_le_self 1 (pow_nonneg hq0 t)) σ).1 := by
        rw [scaledValidObs_smul, sub_smul, one_smul]
      rw [hsub_eq]
      have hle_unroll : scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t) (sub_nonneg.mpr
        (pow_le_one₀ hq0 hq1.le)) (sub_le_self 1 (pow_nonneg hq0 t)) σ ≤ wp setupP (whileRecWP (wp
        bodyP) guard (t + 1) Θ_read) σ := by
        refine realDiagObs_le_of_mat (fun z ↦ (hd_bounds z).1) (fun z ↦ (hd_bounds z).2)
          (hd_mat σ) fun z ↦ ?_
        open Classical in
        by_cases hval : MemPrefixValid S s.val (lowHighEquiv W M z).2
        · have hv1 : validInd n m k S s.val z = 1 := (by unfold validInd; exact ite_eq_left hval)
          have hdeq : d_s z = 1 - q ^ t :=
            Complex.ofReal_injective ((hd_val z hval).trans (hB_val _ hval))
          rw [hv1, mul_one, hdeq]
        · have hv0 : validInd n m k S s.val z = 0 := (by unfold validInd; exact ite_eq_right hval)
          rw [hv0, mul_zero]; exact (hd_bounds z).1
      have hstage_eq : wp ((eigLockStage res n m k hm_grid hk_grid hn s).compile qAssign oracle)
        post = wp setupP (wp (.qWhile guard bodyP) Θ_read) := by
        dsimp only [eigLockStage, setupP, bodyP, Θ_read, readoutP, guard, compile]
        rw [wp_qSeq, wp_qSeq]
      rw [hstage_eq]
      have hmon := wp_mono setupP (whileRecWP_le_wp_qWhile guard bodyP (t + 1) Θ_read) σ
      exact Subtype.coe_le_coe.mpr (hle_unroll.trans hmon)
    exact Subtype.coe_le_coe.mp (hermitian_le_of_geometric_sub_smul_le q hq0 hq1 _ _ _ hgeom)
  · rcases hact_mat t with ⟨A_t, hA_dep, hA_val⟩
    rcases hsetup_diag (whileActiveWP (wp bodyP) guard t) A_t 0 hA_dep with
      ⟨d_s, hd_bounds, hd_mat, hd_val⟩
    let rhs := (scaledValidObs (Var := Var) n m k S s.val (q ^ t)
      (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)).add (invalidObs n m k S s.val)
      (scaledValid_add_invalid_le_one n m k S s.val (q ^ t) _ _)
    let f_rhs (z : Fin (2 ^ (W + M))) : ℝ :=
      q ^ t * validInd n m k S s.val z + invalidInd n m k S s.val z
    have hf_bounds (z : Fin (2 ^ (W + M))) : 0 ≤ f_rhs z ∧ f_rhs z ≤ 1 := by
      dsimp only [f_rhs]; have hqt0 : 0 ≤ q ^ t := pow_nonneg hq0 t
      have hqt1 : q ^ t ≤ 1 := pow_le_one₀ hq0 hq1.le; unfold validInd invalidInd
      split_ifs <;> constructor <;> linarith
    have hrhs_eq : rhs σ = realDiagObs f_rhs (fun z ↦ (hf_bounds z).1)
        (fun z ↦ (hf_bounds z).2) := by
      apply Subtype.ext; apply HermitianMat.ext
      change (scaledValidObs n m k S s.val (q ^ t) _ _ σ).1.1 +
        (invalidObs n m k S s.val σ).1.1 = (realDiagObs f_rhs _ _).1.1
      dsimp only [scaledValidObs, invalidObs]
      rw [realDiagObs_mat, realDiagObs_mat, realDiagObs_mat]; ext z₁ z₂
      rw [Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases h : z₁ = z₂
      · subst h; simp [f_rhs]
      · simp [h]
    change _ ≤ rhs σ; rw [hrhs_eq]
    refine le_realDiagObs_of_mat (fun z ↦ (hd_bounds z).1) (fun z ↦ (hd_bounds z).2)
      (hd_mat σ) fun z ↦ ?_
    dsimp only [f_rhs]
    open Classical in
    by_cases hval : MemPrefixValid S s.val (lowHighEquiv W M z).2
    · have hv1 : validInd n m k S s.val z = 1 := (by unfold validInd; exact ite_eq_left hval)
      have hi0 : invalidInd n m k S s.val z = 0 := (by unfold invalidInd; exact ite_eq_left hval)
      have hdeq : d_s z = q ^ t := Complex.ofReal_injective ((hd_val z hval).trans (hA_val _ hval))
      rw [hv1, hi0, mul_one, add_zero, hdeq]
    · have hv0 : validInd n m k S s.val z = 0 := (by unfold validInd; exact ite_eq_right hval)
      have hi1 : invalidInd n m k S s.val z = 1 := (by unfold invalidInd; exact ite_eq_right hval)
      rw [hv0, hi1, mul_zero, zero_add]; exact (hd_bounds z).2
noncomputable def stageCostReal (n m r : ℕ) : ℝ :=
  let p := oddFrac n m r
  let K := subSchedule p
  (K : ℝ) + 2 + (1 - subFailProb p K)⁻¹
lemma expectedCost_eigLockStage_le {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) (hm_grid
    : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard
    : S.card = k) (s : Fin k) {Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))} (hV : 𝔼[Δ,
      validObs n
    m k S s.val] = Δ.trace) : expectedCost (CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) ((eigLockStage res n m k hm_grid hk_grid hn s).compile
    qAssign (groverParallelMarkingOracle m S)) Δ ≤ stateMass Δ * ENNReal.ofReal (stageCostReal n m
    (k - s.val)) := by
  set r := k - s.val; set p := oddFrac n m r; set K := subSchedule p; set q := subFailProb p K
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
  have hq0 : 0 ≤ q := subFailProb_nonneg p K; have hq1 : q < 1 := hhyps.2.2.2.2
  have h1q_pos : 0 < 1 - q := sub_pos.mpr hq1; let oracle := groverParallelMarkingOracle m S
  let model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
  let setupP := (eigSetup (Var := Var) res n m k s K).compile qAssign oracle
  let bodyP := (eigBody (Var := Var) res n m k hm1 s (subTargetRatio p K)
    hhyps.1.le hhyps.2.1.le).compile qAssign oracle
  let readoutP := (eigReadout (Var := Var) n m k s).compile qAssign oracle
  let guard : Store Var → Prop := fun σ ↦ σ res = 0
  have hact := (eigLockStage_wp_and_active res hm_grid hk_grid hn hcard s).2
  have hinv0 : 𝔼[Δ, invalidObs n m k S s.val] = 0 := expect_invalidObs_eq_zero hV
  set Δ₁ := (interp setupP).toStateFun Δ; set Δ₂ := (interp (.qWhile guard bodyP)).toStateFun Δ₁
  have hsetup_le : expectedCost model setupP Δ ≤ stateMass Δ * ((K + 1 : ℕ) : ℝ≥0∞) := by
    simpa using costBound_eigSetup (Var := Var) res n m k s K S Δ
  have hread_le : expectedCost model readoutP Δ₂ ≤ stateMass Δ * 1 := by
    have h1 := costBound_eigReadout (Var := Var) n m k s S Δ₂
    have hm2 : stateMass Δ₂ ≤ stateMass Δ :=
      (stateMass_interp_le (.qWhile guard bodyP) Δ₁).trans (stateMass_interp_le setupP Δ)
    simpa using h1.trans (mul_le_mul_of_nonneg_right hm2 zero_le)
  have hiter_le (t : ℕ) :
      stateMass (activeIter guard bodyP t Δ₁) ≤ stateMass Δ * (ENNReal.ofReal q) ^ t := by
    rw [← ofReal_expect_whileActiveWP, ← wp_expectation_eq setupP Δ]
    have hexp_le : 𝔼[Δ, wp setupP (whileActiveWP (wp bodyP) guard t)] ≤ q ^ t * Δ.trace := by
      calc 𝔼[Δ, wp setupP (whileActiveWP (wp bodyP) guard t)] ≤ 𝔼[Δ, (scaledValidObs n m k S s.val
            (q ^ t) (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)).add (invalidObs n m k S s.val)
            (scaledValid_add_invalid_le_one n m k S s.val (q ^ t) _ _)] := expect_mono le_rfl
            (hact t)
        _ = 𝔼[Δ, scaledValidObs n m k S s.val (q ^ t)
              (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)] +
            𝔼[Δ, invalidObs n m k S s.val] :=
            expect_assertion_add _ _ _ _
        _ = q ^ t * 𝔼[Δ, validObs n m k S s.val] + 0 := by
            rw [hinv0, expect_eq_mul_of_apply_eq_smul Δ (q ^ t)
              (scaledValidObs_smul n m k S s.val (q ^ t) _ _)]
        _ = q ^ t * Δ.trace := by rw [hV, add_zero]
    calc ENNReal.ofReal 𝔼[Δ, wp setupP (whileActiveWP (wp bodyP) guard t)]
        ≤ ENNReal.ofReal (q ^ t * Δ.trace) := ENNReal.ofReal_le_ofReal hexp_le
      _ = stateMass Δ * (ENNReal.ofReal q) ^ t := by
          rw [mul_comm, ENNReal.ofReal_mul Δ.trace.coe_nonneg,
            ← stateMass_eq_ofReal_trace, ENNReal.ofReal_pow hq0]
  have hwhile_le : expectedCost model (.qWhile guard bodyP) Δ₁ ≤ stateMass Δ * ENNReal.ofReal (1 -
    q)⁻¹ := by
    have hb := costBound_eigBody (Var := Var) res n m k hm1 s (subTargetRatio p K)
      hhyps.1.le hhyps.2.1.le S
    calc expectedCost model (.qWhile guard bodyP) Δ₁
        ≤ expectedIterations guard bodyP Δ₁ * (1 : ℝ≥0) := expectedCost_qWhile_le hb guard Δ₁
      _ = ∑' t : ℕ, stateMass (activeIter guard bodyP t Δ₁) := by
          simp [expectedIterations, stateMass]
      _ ≤ ∑' t : ℕ, stateMass Δ * (ENNReal.ofReal q) ^ t := ENNReal.tsum_le_tsum hiter_le
      _ = stateMass Δ * (1 - ENNReal.ofReal q)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = stateMass Δ * ENNReal.ofReal (1 - q)⁻¹ := by
          have hsub : 1 - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
            simpa using (ENNReal.ofReal_sub 1 hq0).symm
          rw [hsub, ENNReal.ofReal_inv_of_pos h1q_pos]
  change expectedCost model (setupP ;; (.qWhile guard bodyP ;; readoutP)) Δ ≤ _
  rw [expectedCost_qSeq, expectedCost_qSeq]
  calc expectedCost model setupP Δ + (expectedCost model (.qWhile guard bodyP) Δ₁ + expectedCost
        model readoutP Δ₂) ≤ stateMass Δ * ((K + 1 : ℕ) : ℝ≥0∞) + (stateMass Δ * ENNReal.ofReal
        (1 - q)⁻¹ + stateMass Δ * 1) := add_le_add hsetup_le (add_le_add hwhile_le hread_le)
    _ = stateMass Δ *
          (((K + 1 : ℕ) : ℝ≥0∞) + ENNReal.ofReal (1 - q)⁻¹ + 1) := by ring
    _ = stateMass Δ * ENNReal.ofReal (stageCostReal n m r) := by
        congr 1
        have hK1 : ((K + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((K : ℝ) + 1) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg K) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one]
        have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        rw [hK1, h1, ← ENNReal.ofReal_add (by positivity) (inv_nonneg.mpr h1q_pos.le),
          ← ENNReal.ofReal_add (by positivity) zero_le_one]
        dsimp only [stageCostReal, p, K, q]; congr 1; ring
lemma wp_qSet_validObs_zero {Var : Type} [DecidableEq Var] (n m k : ℕ) (S : Finset (Fin (2 ^ n)))
    : wp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n))) (validObs n m k S 0) = ⊤ := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  change ((wp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n))) (validObs n m k S 0)) σ).1.1 = 1
  rw [wp_qSet, qhlQSet_val]; dsimp only [validObs]
  rw [realDiagObs_mat, Matrix.diagonal_apply_eq]
  have h0 : (lowHighEquiv (m * (n + 1)) (k * n) 0).2 = 0 := (by rw [lowHighEquiv_zero])
  have hv0 : validInd n m k S 0 0 = 1 := by
    unfold validInd; rw [h0, ite_eq_left (memPrefixValid_zero S)]
  rw [hv0]; simp
lemma validObs_le_wp_measure_decodeTargets {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) : validObs (Var := Var) n m k S k ≤ wp
    (measureRegister res (highBlock (m * (n + 1)) (k * n))) (liftPureProp (fun σ ↦ decodeTargets n
    k (σ res) = S)) := by
  let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
    liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)
  intro σ
  let f_dec (z : Fin (2 ^ (m * (n + 1) + k * n))) : ℝ := open Classical in if decodeTargets n k
    (Int.ofNat ((lowHighEquiv (m * (n + 1)) (k * n) z).2).val) = S then 1 else 0
  have hf_b (z : Fin (2 ^ (m * (n + 1) + k * n))) : 0 ≤ f_dec z ∧ f_dec z ≤ 1 := by
    dsimp only [f_dec]; split_ifs <;> constructor <;> norm_num
  have hmat : ((wp (measureRegister res (highBlock (m * (n + 1)) (k * n))) post) σ).1.1 =
      diagonal (fun z ↦ (f_dec z : ℂ)) := by
    rw [wp_measureRegister]; ext z₁ z₂; rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hz : z₁ = z₂
    · subst hz; let o₀ := (lowHighEquiv (m * (n + 1)) (k * n) z₁).2
      rw [sum_eq_single o₀ (fun o ho ↦ by
        rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
          extractIndex_highBlock, ite_eq_right (Ne.symm ho), mul_zero])]
      rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
        extractIndex_highBlock, ite_eq_left rfl, one_mul, mul_one]
      dsimp only [post, f_dec]; rw [liftPureProp_apply]
      have hsubst : Store.subst σ res (Int.ofNat o₀.val) res = Int.ofNat o₀.val := by
        simp [Store.subst]
      open Classical in
      by_cases hd : decodeTargets n k (Int.ofNat o₀.val) = S
      · have hd' : decodeTargets n k (Store.subst σ res (Int.ofNat o₀.val) res) = S :=
          hsubst.symm ▸ hd
        rw [ite_eq_left hd', ite_eq_left hd]; simp
      · have hd' : ¬ decodeTargets n k (Store.subst σ res (Int.ofNat o₀.val) res) = S :=
          hsubst.symm ▸ hd
        rw [ite_eq_right hd', ite_eq_right hd]; simp
    · simp only [hz, ↓reduceIte]; refine Finset.sum_eq_zero fun o _ ↦ ?_
      rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul]
      dsimp only [post]; rw [liftPureProp_apply]
      by_cases hd : decodeTargets n k (Store.subst σ res (Int.ofNat o.val) res) = S
      · rw [ite_eq_left hd]; simp [hz]
      · rw [ite_eq_right hd]; simp
  refine realDiagObs_le_of_mat (fun z ↦ (hf_b z).1) (fun z ↦ (hf_b z).2) hmat fun z ↦ ?_
  dsimp only [validInd, f_dec]
  open Classical in
  by_cases hv : MemPrefixValid S k (lowHighEquiv (m * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hv, ite_eq_left (decodeTargets_eq_of_memPrefixValid_full hcard hv)]
  · rw [ite_eq_right hv]; exact (hf_b z).1
end
/- ## Multi-Stage Fallback (`Stage1`) -/
namespace Stage1
@[expose] public section
/-- Claimed dyadic grid cells `(m, k)` for `groverFindAll` (`121 / 121` cells of
  `groverGrid`). -/
def cells (m k : ℕ) : Bool :=
  gridCells m k
theorem cells_nonempty : ∃ m k, cells m k = true :=
  gridCells_nonempty
theorem cells_mem_grid {m k : ℕ} (hmk : cells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid :=
  gridCells_mem_grid hmk
/-- Total qubits used by `Stage1.circuit`: `m * (n + 1)` work qubits + `k * n` archive
  qubits. -/
def qubits (n m k : ℕ) : ℕ :=
  m * (n + 1) + k * n
/-- Claimed asymptotic expected parallel-round cost ratio relative to `vanillaFindAllCost`. -/
def relCost (_m _k : ℕ) : ℚ≥0 :=
  stage1RelCost
def allTargetsIdx (n k : ℕ) (hk : k = 2 ^ n) : Fin (2 ^ (k * n)) :=
  (addrEquiv n k).symm (fun i : Fin k ↦ ⟨i.val, hk ▸ i.isLt⟩)
noncomputable def fullSpaceCirc {Var : Type} (res : Var) (n m k : ℕ)
    (hk : k = 2 ^ n) : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  let W := m * (n + 1)
  let M := k * n
  .seq (.step (phaseTag ((highBlock W M).embedUnitary
      (permutationUnitary (Equiv.swap 0 (allTargetsIdx n k hk))))))
    (.measure res (highBlock W M))
noncomputable def stageDispatch {Var : Type} (res : Var) (n m k : ℕ)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (s : Fin k) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  if hn200 : 200 ≤ n then
    eigLockStage res n m k hm_grid hk_grid hn200 s
  else
    naiveStage res n m k (one_le_of_mem_groverGrid hm_grid) s
noncomputable def stagesFrom {Var : Type} (res : Var) (n m k : ℕ)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) :
    (j : ℕ) → OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)
  | j =>
      if hj : j < k then
        .seq (stageDispatch res n m k hm_grid hk_grid ⟨j, hj⟩)
          (stagesFrom res n m k hm_grid hk_grid (j + 1))
      else .skip
termination_by j => k - j
/-- Parallel query-model circuit encoding all `k` marked elements of `S` into `res`. -/
noncomputable def circuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleCirc Var (qubits n m k) ((n + 1) * m) :=
  if hcell : m ∈ groverGrid ∧ k ∈ groverGrid then
    if _hn1 : 1 ≤ n then
      if hk_eq : k = 2 ^ n then
        fullSpaceCirc res n m k hk_eq
      else
        .seq (stagesFrom res n m k hcell.1 hcell.2 0)
          (.measure res (highBlock (m * (n + 1)) (k * n)))
    else .skip
  else .skip
private lemma wp_stagesFrom_ge {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hk_lt : k < 2 ^ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k → validObs (Var := Var) n m k S j ≤
        wp ((stagesFrom res n m k hm_grid hk_grid j).compile qAssign
            (groverParallelMarkingOracle m S))
          (validObs n m k S k)
  | 0, j, hd, _ => by
    have hjeq : j = k := by omega
    subst hjeq
    rw [stagesFrom]; simp
  | d + 1, j, hd, _ => by
    have hj : j < k := by omega
    rw [stagesFrom, dite_eq_left hj]; dsimp only [compile]; rw [wp_qSeq]
    have hih := wp_stagesFrom_ge res hm_grid hk_grid hk_lt hcard d (j + 1)
      (by omega) (by omega)
    have hstage : validObs (Var := Var) n m k S j ≤
        wp ((stageDispatch res n m k hm_grid hk_grid ⟨j, hj⟩).compile qAssign
            (groverParallelMarkingOracle m S))
          (validObs n m k S (j + 1)) := by
      unfold stageDispatch
      by_cases hn200 : 200 ≤ n
      · rw [dite_eq_left hn200]
        exact (eigLockStage_wp_and_active res hm_grid hk_grid hn200 hcard ⟨j, hj⟩).1
      · rw [dite_eq_right hn200]
        exact wp_naiveStage_ge res (one_le_of_mem_groverGrid hm_grid) hk_lt hcard ⟨j, hj⟩
    exact hstage.trans (wp_mono _ hih)
private lemma expectedCost_stagesFrom_le {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k → ∀ Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
        𝔼[Δ, validObs n m k S j] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          ((stagesFrom res n m k hm_grid hk_grid j).compile qAssign
            (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ * ∑ r ∈ Finset.Icc 1 (k - j), ENNReal.ofReal (stageCostReal n m r)
  | 0, j, hd, _, Δ, _ => by
    have hjeq : j = k := by omega
    subst hjeq
    rw [stagesFrom]; simp
  | d + 1, j, hd, _, Δ, hV => by
    have hj : j < k := by omega
    rw [stagesFrom, dite_eq_left hj]; dsimp only [compile]; rw [expectedCost_qSeq]
    have hdisp_eq : stageDispatch (Var := Var) res n m k hm_grid hk_grid ⟨j, hj⟩ =
        eigLockStage res n m k hm_grid hk_grid hn200 ⟨j, hj⟩ := by
      unfold stageDispatch; rw [dite_eq_left hn200]
    rw [hdisp_eq]
    let stageP := (eigLockStage (Var := Var) res n m k hm_grid hk_grid hn200 ⟨j, hj⟩).compile
      qAssign (groverParallelMarkingOracle m S)
    have hwp_st := (eigLockStage_wp_and_active (Var := Var) res hm_grid hk_grid hn200 hcard
      ⟨j, hj⟩).1
    have hstep_V := validState_step hV hwp_st
    have hcost_st := expectedCost_eigLockStage_le res hm_grid hk_grid hn200 hcard ⟨j, hj⟩ hV
    have hih := expectedCost_stagesFrom_le res hm_grid hk_grid hn200 hcard d (j + 1)
      (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
    rw [hstep_V.2] at hih
    calc expectedCost _ stageP Δ + expectedCost _ _ ((interp stageP).toStateFun Δ)
        ≤ stateMass Δ * ENNReal.ofReal (stageCostReal n m (k - j)) + stateMass Δ *
              ∑ r ∈ Finset.Icc 1 (k - (j + 1)), ENNReal.ofReal (stageCostReal n m r) :=
          add_le_add hcost_st hih
      _ = stateMass Δ *
            (∑ r ∈ Finset.Icc 1 (k - (j + 1)), ENNReal.ofReal (stageCostReal n m r) +
              ENNReal.ofReal (stageCostReal n m (k - j))) := by ring
      _ = stateMass Δ *
            ∑ r ∈ Finset.Icc 1 (k - j), ENNReal.ofReal (stageCostReal n m r) := by
          have hk_sub : k - j = (k - (j + 1)) + 1 := by omega
          rw [hk_sub, Finset.sum_Icc_succ_top (by omega)]
/-- `Stage1.circuit` recovers the full marked set `S` via `decodeTargets n k (σ res) = S`
  with
  probability `1` on every claimed cell `(m, k)` of `groverGrid`. -/
theorem correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hn : 1 ≤ n)
    (hmk : cells m k = true) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ qubits n m k)) ⦄
    (qset ;; (circuit res n m k).compile qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S) ⦄ := by
  unfold circuit qubits; have hgrid := cells_mem_grid hmk
  have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
  let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
    liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)
  refine Triple.of_eq_wp ?_
  symm; rw [dite_eq_left hgrid, dite_eq_left hn]
  by_cases hk_eq : k = 2 ^ n
  · rw [dite_eq_left hk_eq]
    have hS_univ : S = Finset.univ := Finset.eq_univ_of_card S (by simp [hcard, hk_eq])
    let μ_all := allTargetsIdx n k hk_eq
    have hdec_all : decodeTargets n k (Int.ofNat μ_all.val) = S := by
      refine decodeTargets_ofNat_eq_of_subset_of_injective hcard μ_all
        (fun i ↦ by rw [hS_univ]; exact Finset.mem_univ _)
        (fun i j hij ↦ ?_)
      dsimp only [μ_all, allTargetsIdx] at hij; rw [Equiv.apply_symm_apply] at hij
      exact Fin.ext (Fin.mk.inj hij)
    funext σ; apply Subtype.ext; apply HermitianMat.ext
    change ((wp (qset ;; (fullSpaceCirc res n m k hk_eq).compile qAssign
        (groverParallelMarkingOracle m S)) post) σ).1.1 = 1
    dsimp only [fullSpaceCirc, compile]
    rw [wp_qSeq, wp_qSet, qhlQSet_val, wp_qSeq, wp_qAssign, wp_phaseTag,
      qhlQAssign_val]
    let M_meas := ((wp (measureRegister res (highBlock (m * (n + 1)) (k * n))) post) σ).1.1
    let U_sw := (highBlock (m * (n + 1)) (k * n)).embedUnitary
      (permutationUnitary (Equiv.swap 0 μ_all))
    let M_conj : Operator (2 ^ (m * (n + 1) + k * n)) := U_sw.1ᴴ * M_meas * U_sw.1
    change (M_conj 0 0) • (1 : Operator (2 ^ (m * (n + 1) + k * n))) = 1
    rw [vecQuad_single M_conj 0]; dsimp only [M_conj, U_sw]
    rw [vecQuad_conj, ← workMemState_zero, QRegister.embedUnitary_val,
      embedMatrix_highBlock_mulVec_workMemState, permutationUnitary_mulVec_single,
      Equiv.swap_apply_left, workMemState_single, ← vecQuad_single M_meas]
    dsimp only [M_meas]; rw [wp_measureRegister, Matrix.sum_apply]
    let z_all := (lowHighEquiv (m * (n + 1)) (k * n)).symm (0, μ_all)
    have hsum : (∑ o : Fin (2 ^ (k * n)), ((highBlock (m * (n + 1)) (k * n)).basisOutcomeProjector
      o * (post (Store.subst σ res (Int.ofNat o.val))).1.1 * (highBlock (m * (n + 1)) (k *
      n)).basisOutcomeProjector o) z_all z_all) = 1 := by
      rw [sum_eq_single μ_all (fun o ho ↦ by
        rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
          extractIndex_highBlock]
        dsimp only [z_all]
        rw [Equiv.apply_symm_apply, ite_eq_right (Ne.symm ho), mul_zero])]
      rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
        extractIndex_highBlock]
      dsimp only [z_all, post]; rw [Equiv.apply_symm_apply, ite_eq_left rfl, liftPureProp_apply]
      have hs : decodeTargets n k (Store.subst σ res (Int.ofNat μ_all.val) res) = S := by
        simpa [Store.subst] using hdec_all
      rw [ite_eq_left hs]; simp
    rw [hsum, one_smul]
  · rw [dite_eq_right hk_eq]; have hk_lt : k < 2 ^ n := lt_of_le_of_ne hkN hk_eq
    dsimp only [compile]; rw [wp_qSeq, wp_qSeq]
    have hmeas_ge : validObs (Var := Var) n m k S k ≤ wp (measureRegister res (highBlock (m * (n +
      1)) (k * n))) post := validObs_le_wp_measure_decodeTargets res hcard
    have hst_ge := wp_stagesFrom_ge (Var := Var) res hgrid.1 hgrid.2 hk_lt hcard k 0
      (by omega) (by omega)
    have htot_ge : validObs (Var := Var) n m k S 0 ≤ wp ((stagesFrom res n m k hgrid.1 hgrid.2
      0).compile qAssign (groverParallelMarkingOracle m S)) (wp (measureRegister res (highBlock
      (m * (n + 1)) (k * n))) post) := hst_ge.trans (wp_mono _ hmeas_ge)
    have hqset_ge := (wp_qSet_validObs_zero (Var := Var) n m k S).symm.le.trans
      (wp_mono .qSet htot_ge)
    exact top_unique hqset_ge
/-- Asymptotic uniform-average expected parallel-round cost bound for `Stage1.circuit`
  relative
  to `vanillaFindAllCost` across all `121 / 121` cells of `groverGrid`. -/
theorem rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ} (hmk : cells m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound (Var := Var) (d := 2 ^ qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ qset ;; (circuit res n m k).compile qAssign (groverParallelMarkingOracle m S))
        (relCost m k * vanillaFindAllCost n m k) := by
  have hgrid := cells_mem_grid hmk; have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hgrid.2
  refine ⟨200, fun n hn200 hkN ↦ ?_⟩
  unfold qubits; have hn1 : 1 ≤ n := (by omega)
  have hk_lt : k < 2 ^ n := by
    calc k ≤ 1024 := hk_hi
      _ < 2 ^ 200 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn200
  have hk_ne : k ≠ 2 ^ n := hk_lt.ne
  let q_val : ℝ≥0 := ∑ s : Fin k, Real.toNNReal (stageCostReal n m (k - s.val))
  refine ⟨fun _ ↦ q_val, fun S hS state ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    let oracle := groverParallelMarkingOracle m S
    let model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
    change expectedCost model (qset ;; ((circuit (Var := Var) res n m k).compile qAssign oracle :
      QProg Var (2 ^ (m * (n + 1) + k * n)))) state ≤ stateMass state * (q_val : ℝ≥0∞)
    have hcirc : ((circuit (Var := Var) res n m k).compile qAssign oracle : QProg Var (2 ^ (m *
      (n + 1) + k * n))) = ((stagesFrom res n m k hgrid.1 hgrid.2 0).compile qAssign oracle ;;
      measureRegister res (highBlock (m * (n + 1)) (k * n))) := by
      unfold circuit; dsimp only [qubits]
      rw [dite_eq_left hgrid, dite_eq_left hn1, dite_eq_right hk_ne]; rfl
    rw [hcirc, expectedCost_qSeq, expectedCost_qSet]; have hreset0 : model.resetCost = 0 := rfl
    simp only [hreset0, Nat.cast_zero, mul_zero, zero_add]; rw [expectedCost_qSeq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n m k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]; rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
      exact congrArg NNReal.toReal (CQState.trace_qSet state).symm
    have hmass0 : stateMass Δ₀ = stateMass state := Lossless.qSet state
    have hmeas0 : expectedCost model (measureRegister res (highBlock (m * (n + 1)) (k * n)))
        ((interp ((stagesFrom res n m k hgrid.1 hgrid.2 0).compile qAssign oracle)).toStateFun
          Δ₀) = 0 := by
      have hm_cb : CostBound (Var := Var) model
          (measureRegister res (highBlock (m * (n + 1)) (k * n))) 0 := by
        simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
          CostBound.qMeasure (Var := Var) model res _
      exact nonpos_iff_eq_zero.mp (by simpa using hm_cb _)
    rw [hmeas0, add_zero]
    have hst := expectedCost_stagesFrom_le res hgrid.1 hgrid.2 hn200 hcard k 0
      (by omega) (by omega) Δ₀ hV0
    rw [Nat.sub_zero, hmass0] at hst; refine hst.trans ?_
    gcongr
    dsimp only [q_val]; rw [ENNReal.ofNNReal_finsetSum]; refine le_of_eq ?_
    symm
    refine Finset.sum_bij (fun (s : Fin k) _ ↦ k - s.val)
      (fun s _ ↦ Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun s₁ _ s₂ _ h ↦ Fin.ext (by omega))
      (fun r hr ↦ ?_)
      (fun s _ ↦ ?_)
    · rcases Finset.mem_Icc.mp hr with ⟨hr1, hrk⟩
      exact ⟨⟨k - r, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
    · rfl
  · have hsum_le : (q_val : ℝ) ≤ (relCost m k : ℝ) * vanillaFindAllCost n m k := by
      dsimp only [q_val, relCost]
      rw [NNReal.coe_sum, vanillaFindAllCost_eq_sum_vanillaFindAnyCost, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ ↦ ?_
      have hsc := stageCost_le_stage1RelCost (r := k - s.val) hn200 hgrid.1 hgrid.2
        (by omega) (by omega)
      have h0 : 0 ≤ stageCostReal n m (k - s.val) := by
        dsimp only [stageCostReal]
        have h1q : 0 < 1 - subFailProb (oddFrac n m (k - s.val)) (subSchedule (oddFrac n m (k -
          s.val))) := sub_pos.mpr hsc.1.2.2.2.2
        positivity
      rw [Real.coe_toNNReal _ h0]; exact hsc.2
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      have hc : (groverTargetSets n k).card = Nat.choose (2 ^ n) k := (by simp [groverTargetSets])
      rw [hc]; exact_mod_cast Nat.choose_pos hkN
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']; exact hsum_le
end
end Stage1
end QuantumComputation.Specs.GroverSol
end Sec_FindAllStage1
section Sec_Stage1EigLock
@[expose] public section
namespace QuantumComputation.Specs.GroverSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open scoped NNReal NNRat ENNReal QHLExpectation
/-- For `n ≥ 600` on `groverGrid`, `stageCostReal n m r` is nonnegative and bounded above by
  `(π / 8 + 1 / 4) * √(2 ^ n / (m * r)) + 5`. -/
theorem stageCostReal_le_linear_S0 {n m k r : ℕ} (hn : 600 ≤ n) (hm_grid : m ∈ groverGrid)
    (hk_grid : k ∈ groverGrid) (hr1 : 1 ≤ r) (hrk : r ≤ k) : 0 ≤ stageCostReal n m r ∧
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
  rcases oddFrac_sandwich (m := m) h2r_le with ⟨hp_lo, hp_hi⟩
  change p₀ * (1 - p₀) ≤ p at hp_lo; change p ≤ p₀ at hp_hi
  have hp0_inv : p₀ * S₀ ^ 2 = 1 := (by rw [hS0_sq]; dsimp only [p₀]; field_simp [hmr_pos.ne'])
  have h1_div_sqrt_ge : S₀ ≤ 1 / √p := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hp_pos)]; have hle : √p ≤ √p₀ := Real.sqrt_le_sqrt hp_hi
    have hmul : S₀ * √p₀ = 1 := by
      have hsq : (S₀ * √p₀) ^ 2 = 1 := by
        rw [mul_pow, hS0_sq, Real.sq_sqrt (by positivity)]
        dsimp only [p₀]; field_simp [hmr_pos.ne']
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
      have hnum : (S₀ + 1) ^ 2 * (1 / S₀ ^ 2 * (1 - 1 / S₀ ^ 2)) - 1 = (2 * S₀ ^ 3 - 2 * S₀ - 1) /
        S₀ ^ 4 := by
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
  refine ⟨hnn, ?_⟩
  have hπ_hi : π < 4 := Real.pi_lt_four; dsimp only [stageCostReal, p, K]
  have h1 : (π / 8 + 1 / 4) * (1 / √p) ≤ (π / 8 + 1 / 4) * (S₀ + 1) :=
    mul_le_mul_of_nonneg_left h1_div_sqrt_le (by positivity)
  linarith
namespace Stage1
/-- Claimed asymptotic expected parallel-round cost ratio relative to
  `vanillaFindAllCost` for `Stage1.circuit` (via Mathlib's `Real.pi_gt_d20`). -/
def relCostEigLock (_m _k : ℕ) : ℚ≥0 :=
  stage1RelCost
/-- Expected parallel-round cost bound for `stagesFrom` across remaining stages `j.. k - 1`
  whenever `200 ≤ n`. -/
theorem expectedCost_stagesFrom_eigLock_le {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hn200 : 200 ≤ n) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k →
      ∀ Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
        𝔼[Δ, validObs n m k S j] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          ((stagesFrom res n m k hm_grid hk_grid j).compile qAssign
            (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ *
            ∑ r ∈ Finset.Icc 1 (k - j), ENNReal.ofReal (stageCostReal n m r)
  | 0, j, hd, _, Δ, _ => by
    have hjeq : j = k := by omega
    subst hjeq
    rw [stagesFrom]; simp
  | d + 1, j, hd, _, Δ, hV => by
    have hj : j < k := by omega
    rw [stagesFrom, dite_eq_left hj]; dsimp only [compile]; rw [expectedCost_qSeq]
    have hdisp_eq : stageDispatch (Var := Var) res n m k hm_grid hk_grid ⟨j, hj⟩ =
        eigLockStage res n m k hm_grid hk_grid hn200 ⟨j, hj⟩ := by
      unfold stageDispatch; rw [dite_eq_left hn200]
    rw [hdisp_eq]
    let stageP := (eigLockStage (Var := Var) res n m k hm_grid hk_grid hn200 ⟨j, hj⟩).compile
      qAssign (groverParallelMarkingOracle m S)
    have hwp_st := (eigLockStage_wp_and_active (Var := Var) res hm_grid hk_grid hn200 hcard
      ⟨j, hj⟩).1
    have hstep_V := validState_step hV hwp_st
    have hcost_st := expectedCost_eigLockStage_le res hm_grid hk_grid hn200 hcard ⟨j, hj⟩ hV
    have hih := expectedCost_stagesFrom_eigLock_le res hm_grid hk_grid hn200 hcard d (j + 1)
      (by omega) (by omega) ((interp stageP).toStateFun Δ) hstep_V.1
    rw [hstep_V.2] at hih
    calc expectedCost _ stageP Δ + expectedCost _ _ ((interp stageP).toStateFun Δ)
        ≤ stateMass Δ * ENNReal.ofReal (stageCostReal n m (k - j)) + stateMass Δ *
              ∑ r ∈ Finset.Icc 1 (k - (j + 1)), ENNReal.ofReal (stageCostReal n m r) :=
          add_le_add hcost_st hih
      _ = stateMass Δ *
            (∑ r ∈ Finset.Icc 1 (k - (j + 1)), ENNReal.ofReal (stageCostReal n m r) +
              ENNReal.ofReal (stageCostReal n m (k - j))) := by ring
      _ = stateMass Δ *
            ∑ r ∈ Finset.Icc 1 (k - j), ENNReal.ofReal (stageCostReal n m r) := by
          have hk_sub : k - j = (k - (j + 1)) + 1 := by omega
          rw [hk_sub, Finset.sum_Icc_succ_top (by omega)]
/-- Asymptotic uniform-average expected parallel-round cost bound for `Stage1.circuit`
  across all claimed cells `(m, k)` of `groverGrid` via Mathlib's `Real.pi_gt_d20`. -/
theorem rel_cost_eigLock {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hmk : cells m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      AvgOracleCostBound (Var := Var) (d := 2 ^ qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ qset ;; (circuit res n m k).compile qAssign (groverParallelMarkingOracle m S))
        (relCostEigLock m k * vanillaFindAllCost n m k) := by
  have hgrid := cells_mem_grid hmk; have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hgrid.1
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hgrid.1
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hgrid.2
  set δ : ℝ := (stage1RelCost : ℝ) * (π / 4) - (π / 8 + 1 / 4)
  have hδ : 0 < δ := by
    have hπ20 : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
    have hcostR : (stage1RelCost : ℝ) = 514159265358979323847 / 628318530717958647692 := by
      dsimp only [stage1RelCost]; norm_num
    dsimp only [δ]; rw [hcostR]; linarith
  obtain ⟨M, hM⟩ := exists_nat_ge ((5 / δ) ^ 2 * (16 ^ 5 : ℝ))
  refine ⟨max 600 M, fun n hn hkN ↦ ?_⟩
  have hn600 : 600 ≤ n := (le_max_left _ _).trans hn
  have hn_M : M ≤ n := (le_max_right _ _).trans hn; have hn200 : 200 ≤ n := (by omega)
  unfold qubits; have hn1 : 1 ≤ n := (by omega)
  have hk_lt : k < 2 ^ n := by
    calc k ≤ 1024 := hk_hi
      _ < 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hk_ne : k ≠ 2 ^ n := hk_lt.ne
  let q_val : ℝ≥0 := ∑ s : Fin k, Real.toNNReal (stageCostReal n m (k - s.val))
  refine ⟨fun _ ↦ q_val, fun S hS state ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    let oracle := groverParallelMarkingOracle m S
    let model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
    change expectedCost model (qset ;; ((circuit (Var := Var) res n m k).compile qAssign oracle :
      QProg Var (2 ^ (m * (n + 1) + k * n)))) state ≤ stateMass state * (q_val : ℝ≥0∞)
    have hcirc : ((circuit (Var := Var) res n m k).compile qAssign oracle : QProg Var (2 ^ (m *
      (n + 1) + k * n))) = ((stagesFrom res n m k hgrid.1 hgrid.2 0).compile qAssign oracle ;;
      measureRegister res (highBlock (m * (n + 1)) (k * n))) := by
      unfold circuit; dsimp only [qubits]
      rw [dite_eq_left hgrid, dite_eq_left hn1, dite_eq_right hk_ne]; rfl
    rw [hcirc, expectedCost_qSeq, expectedCost_qSet]; have hreset0 : model.resetCost = 0 := rfl
    simp only [hreset0, Nat.cast_zero, mul_zero, zero_add]; rw [expectedCost_qSeq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n m k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]; rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
      exact congrArg NNReal.toReal (CQState.trace_qSet state).symm
    have hmass0 : stateMass Δ₀ = stateMass state := Lossless.qSet state
    have hmeas0 : expectedCost model (measureRegister res (highBlock (m * (n + 1)) (k * n)))
        ((interp ((stagesFrom res n m k hgrid.1 hgrid.2 0).compile qAssign oracle)).toStateFun
          Δ₀) = 0 := by
      have hm_cb : CostBound (Var := Var) model
          (measureRegister res (highBlock (m * (n + 1)) (k * n))) 0 := by
        simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
          CostBound.qMeasure (Var := Var) model res _
      exact nonpos_iff_eq_zero.mp (by simpa using hm_cb _)
    rw [hmeas0, add_zero]
    have hst := expectedCost_stagesFrom_eigLock_le res hgrid.1 hgrid.2 hn200 hcard k 0
      (by omega) (by omega) Δ₀ hV0
    rw [Nat.sub_zero, hmass0] at hst; refine hst.trans ?_
    gcongr
    dsimp only [q_val]; rw [ENNReal.ofNNReal_finsetSum]; refine le_of_eq ?_
    symm
    refine Finset.sum_bij (fun (s : Fin k) _ ↦ k - s.val)
      (fun s _ ↦ Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun s₁ _ s₂ _ h ↦ Fin.ext (by omega))
      (fun r hr ↦ ?_)
      (fun _ _ ↦ rfl)
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrk⟩
    exact ⟨⟨k - r, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
  · have hsum_le : (q_val : ℝ) ≤ (relCostEigLock m k : ℝ) * vanillaFindAllCost n m k := by
      dsimp only [q_val, relCostEigLock]
      rw [NNReal.coe_sum, vanillaFindAllCost_eq_sum_vanillaFindAnyCost, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ ↦ ?_
      set r := k - s.val; have hr1 : 1 ≤ r := (by omega); have hrk : r ≤ k := (by omega)
      have hr_hi : r ≤ 1024 := hrk.trans hk_hi
      have hsc := stageCostReal_le_linear_S0 (r := r) hn600 hgrid.1 hgrid.2 hr1 hrk
      rw [Real.coe_toNNReal _ hsc.1]
      have hmr_pos : (0 : ℝ) < (m : ℝ) * (r : ℝ) :=
        mul_pos (Nat.cast_pos.mpr hm1) (Nat.cast_pos.mpr hr1)
      have hmr_le : (m : ℝ) * (r : ℝ) ≤ 16 ^ 5 := by
        have : m * r ≤ 1024 * 1024 := Nat.mul_le_mul hm_hi hr_hi
        calc (m : ℝ) * (r : ℝ) = ((m * r : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ ((1024 * 1024 : ℕ) : ℝ) := by exact_mod_cast this
          _ = 16 ^ 5 := by norm_num
      have hM_pow : (5 / δ) ^ 2 * ((m : ℝ) * (r : ℝ)) ≤ (2 ^ n : ℝ) := by
        calc (5 / δ) ^ 2 * ((m : ℝ) * (r : ℝ))
            ≤ (5 / δ) ^ 2 * (16 ^ 5 : ℝ) := mul_le_mul_of_nonneg_left hmr_le (sq_nonneg _)
          _ ≤ (M : ℝ) := hM
          _ ≤ (2 ^ n : ℝ) := by exact_mod_cast hn_M.trans n.lt_two_pow_self.le
      set S₀ : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))
      have h5_S0 : 5 / δ ≤ S₀ := Real.le_sqrt_of_sq_le ((le_div_iff₀ hmr_pos).mpr hM_pow)
      have h5_δ : 5 ≤ δ * S₀ := (by have := (div_le_iff₀ hδ).mp h5_S0; linarith)
      have hvan : (stage1RelCost : ℝ) * vanillaFindAnyCost n m r =
          ((π / 8 + 1 / 4) + δ) * S₀ := by
        unfold vanillaFindAnyCost; dsimp only [δ, S₀]; ring
      linarith [hsc.2, h5_δ, hvan]
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      have hc : (groverTargetSets n k).card = Nat.choose (2 ^ n) k := (by simp [groverTargetSets])
      rw [hc]; exact_mod_cast Nat.choose_pos hkN
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']; exact hsum_le
end Stage1
end QuantumComputation.Specs.GroverSol
end
end Sec_Stage1EigLock
end Sec_Stage1EigLock
end Sec_Stage1EigLock
section Sec_MultiTapStage2AGL1QHL
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
namespace QuantumComputation.Specs.GroverFindAll.MultiTapStage2
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open QuantumComputation.Specs.GroverFindAll
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation
  Topology
/- ## 1. Kraus Slice Marginal State, `embedOracleCirc`, and Global `resetAllCircuit` -/
/-- Kraus slice matrix projecting global basis states with environment `env` onto `Fin (2 ^
  q)`. -/
noncomputable def envSliceIso {q Q : ℕ} (r : QRegister q Q) (env : r.Environment → ZMod 2) :
    Matrix (Fin (2 ^ q)) (Fin (2 ^ Q)) ℂ :=
  fun a g ↦ if r.basisSplitEquiv g = (a, env) then 1 else 0
theorem sum_conjTranspose_mul_envSliceIso {q Q : ℕ} (r : QRegister q Q) (A : Matrix (Fin (2 ^ q))
    (Fin (2 ^ q)) ℂ) : (∑ env : r.Environment → ZMod 2, (envSliceIso r env)ᴴ * A * envSliceIso r
    env) = r.embedMatrix A := by
  ext g₁ g₂; rw [Matrix.sum_apply, QRegister.embedMatrix_apply]
  rw [Finset.sum_eq_single (r.basisSplitEquiv g₁).2]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (r.extractIndex g₂)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (r.extractIndex g₁)]
      · have h1 : (envSliceIso r (r.basisSplitEquiv g₁).2)ᴴ g₁ (r.extractIndex g₁) = 1 := by
          have hg₁ : r.basisSplitEquiv g₁ = (r.extractIndex g₁, (r.basisSplitEquiv g₁).2) :=
            Prod.ext (r.basisSplitEquiv_apply_fst g₁) rfl
          change star (if r.basisSplitEquiv g₁ = (r.extractIndex g₁, (r.basisSplitEquiv g₁).2)
            then (1 : ℂ) else 0) = 1
          rw [ite_eq_left hg₁, star_one]
        rw [h1, one_mul]; by_cases henv : (r.basisSplitEquiv g₁).2 = (r.basisSplitEquiv g₂).2
        · have hg₂ : r.basisSplitEquiv g₂ = (r.extractIndex g₂, (r.basisSplitEquiv g₁).2) :=
            Prod.ext (r.basisSplitEquiv_apply_fst g₂) henv.symm
          change A (r.extractIndex g₁) (r.extractIndex g₂) * (if r.basisSplitEquiv g₂ =
            (r.extractIndex g₂, (r.basisSplitEquiv g₁).2) then 1 else 0) = A (r.extractIndex g₁)
            (r.extractIndex g₂) * (if (r.basisSplitEquiv g₁).2 = (r.basisSplitEquiv g₂).2 then 1
            else 0)
          rw [ite_eq_left hg₂, ite_eq_left henv]
        · have hne : r.basisSplitEquiv g₂ ≠ (r.extractIndex g₂, (r.basisSplitEquiv g₁).2) :=
            fun h ↦ henv (congrArg Prod.snd h).symm
          change A (r.extractIndex g₁) (r.extractIndex g₂) * (if r.basisSplitEquiv g₂ =
            (r.extractIndex g₂, (r.basisSplitEquiv g₁).2) then 1 else 0) = A (r.extractIndex g₁)
            (r.extractIndex g₂) * (if (r.basisSplitEquiv g₁).2 = (r.basisSplitEquiv g₂).2 then 1
            else 0)
          rw [ite_eq_right hne, ite_eq_right henv]
      · intro a _ ha
        have hne : r.basisSplitEquiv g₁ ≠ (a, (r.basisSplitEquiv g₁).2) := by
          intro h; have hf := congrArg Prod.fst h
          rw [r.basisSplitEquiv_apply_fst g₁] at hf; exact ha hf.symm
        simp [envSliceIso, Matrix.conjTranspose_apply, hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro b _ hb
      have hne : r.basisSplitEquiv g₂ ≠ (b, (r.basisSplitEquiv g₁).2) := by
        intro h; have hf := congrArg Prod.fst h
        rw [r.basisSplitEquiv_apply_fst g₂] at hf; exact hb hf.symm
      simp [envSliceIso, hne]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro env _ henv; rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [Matrix.mul_apply]
    have h0 : (∑ a : Fin (2 ^ q), ((envSliceIso r env)ᴴ g₁ a * A a b)) = 0 := by
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      have hne : r.basisSplitEquiv g₁ ≠ (a, env) := fun h ↦ henv (congrArg Prod.snd h).symm
      simp [envSliceIso, Matrix.conjTranspose_apply, hne]
    rw [h0, zero_mul]
  · intro h; exact (h (Finset.mem_univ _)).elim
/-- Lift a local `HermitianMat` onto subregister `r` via Kraus slices. -/
noncomputable def liftHermitian {q Q : ℕ} (r : QRegister q Q)
    (H : HermitianMat (Fin (2 ^ q)) ℂ) : HermitianMat (Fin (2 ^ Q)) ℂ :=
  ∑ env : r.Environment → ZMod 2, HermitianMat.conj (envSliceIso r env)ᴴ H
@[simp]
theorem liftHermitian_mat {q Q : ℕ} (r : QRegister q Q) (H : HermitianMat (Fin (2 ^ q)) ℂ) :
    (liftHermitian r H).1 = r.embedMatrix H.1 := by
  change (liftHermitian r H).mat = r.embedMatrix H.1
  rw [liftHermitian, HermitianMat.mat_finset_sum]
  simp_rw [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose]
  exact sum_conjTranspose_mul_envSliceIso r H.1
@[simp]
theorem liftHermitian_zero {q Q : ℕ} (r : QRegister q Q) : liftHermitian r 0 = 0 := by
  apply HermitianMat.ext; change (liftHermitian r 0).1 = 0
  rw [liftHermitian_mat]; exact r.embedMatrix_zero
@[simp]
theorem liftHermitian_one {q Q : ℕ} (r : QRegister q Q) : liftHermitian r 1 = 1 := by
  apply HermitianMat.ext; change (liftHermitian r 1).1 = 1
  rw [liftHermitian_mat]; exact r.embedMatrix_one
theorem liftHermitian_mono {q Q : ℕ} (r : QRegister q Q) :
    Monotone (liftHermitian r) :=
  fun _ _ hAB ↦ Finset.sum_le_sum fun _ _ ↦ HermitianMat.conj_mono hAB
/-- Lift a local `Observable (2 ^ q)` to `Observable (2 ^ Q)` on subregister `r`. -/
noncomputable def liftObservable {q Q : ℕ} (r : QRegister q Q)
    (o : Observable (Fin (2 ^ q))) : Observable (Fin (2 ^ Q)) :=
  ⟨liftHermitian r o.1,
    (liftHermitian_zero r).symm.trans_le (liftHermitian_mono r o.2.1),
    (liftHermitian_mono r o.2.2).trans_eq (liftHermitian_one r)⟩
@[simp]
theorem liftObservable_mat {q Q : ℕ} (r : QRegister q Q) (o : Observable (Fin (2 ^ q))) :
    (liftObservable r o).1.1 = r.embedMatrix o.1.1 :=
  liftHermitian_mat r o.1
theorem liftObservable_mono {q Q : ℕ} (r : QRegister q Q) :
    Monotone (liftObservable r) :=
  fun _ _ h ↦ liftHermitian_mono r h
theorem liftObservable_continuous {q Q : ℕ} (r : QRegister q Q) :
    Continuous (liftObservable r) := by
  have hfMat : Continuous (fun o : Observable (Fin (2 ^ q)) ↦ (liftObservable r o).1.1) := by
    simp_rw [liftObservable_mat]; refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simp_rw [QRegister.embedMatrix_apply]
    have hval : Continuous (fun o : Observable (Fin (2 ^ q)) ↦ o.1.1) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact ((continuous_apply (r.extractIndex j)).comp
      ((continuous_apply (r.extractIndex i)).comp hval)).mul continuous_const
  exact Continuous.subtype_mk (Continuous.subtype_mk hfMat _) _
theorem liftObservable_ωSup {q Q : ℕ} (r : QRegister q Q)
    (ch : OmegaCompletePartialOrder.Chain (Observable (Fin (2 ^ q)))) :
    liftObservable r (OmegaCompletePartialOrder.ωSup ch) =
      OmegaCompletePartialOrder.ωSup (ch.map ⟨liftObservable r, liftObservable_mono r⟩) :=
  tendsto_nhds_unique
    (((liftObservable_continuous r).tendsto _).comp (OmegaCompletePartialOrder.tendsto_ωSup ch))
    (OmegaCompletePartialOrder.tendsto_ωSup _)
/-- Pointwise store lift of a local `CQAssertion` onto subregister `r`. -/
noncomputable def liftAssertion {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (Θ : CQAssertion (Store Var) (2 ^ q)) : CQAssertion (Store Var) (2 ^ Q) :=
  fun σ ↦ liftObservable r (Θ σ)
@[simp]
theorem liftAssertion_apply {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (Θ : CQAssertion (Store Var) (2 ^ q)) (σ : Store Var) :
    liftAssertion r Θ σ = liftObservable r (Θ σ) := rfl
theorem liftAssertion_liftPureProp {Var : Type} {q Q : ℕ} (r : QRegister q Q) (P : Store Var →
    Prop) : liftAssertion r (liftPureProp P : CQAssertion (Store Var) (2 ^ q)) = liftPureProp P :=
      by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  change (liftObservable r (liftPureProp P σ)).1.1 = (liftPureProp P σ).1.1
  rw [liftObservable_mat, liftPureProp_apply, liftPureProp_apply]
  open Classical in
  by_cases h : P σ <;> simp [h]
/-- Partial trace of a global `HermitianMat` onto subregister `r`. -/
noncomputable def marginalHermitian {q Q : ℕ} (r : QRegister q Q)
    (H : HermitianMat (Fin (2 ^ Q)) ℂ) : HermitianMat (Fin (2 ^ q)) ℂ :=
  ∑ env : r.Environment → ZMod 2, HermitianMat.conj (envSliceIso r env) H
@[simp]
theorem marginalHermitian_zero {q Q : ℕ} (r : QRegister q Q) : marginalHermitian r 0 = 0 := by
  apply HermitianMat.ext; change (marginalHermitian r 0).mat = 0
  rw [marginalHermitian, HermitianMat.mat_finset_sum]; simp
theorem liftHermitian_inner_eq {q Q : ℕ} (r : QRegister q Q)
    (A : HermitianMat (Fin (2 ^ q)) ℂ) (B : HermitianMat (Fin (2 ^ Q)) ℂ) :
    ⟪liftHermitian r A, B⟫_ℝ = ⟪A, marginalHermitian r B⟫_ℝ := by
  simp only [liftHermitian, marginalHermitian, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun env _ ↦ ?_
  rw [HermitianMat.inner_conj_left, Matrix.conjTranspose_conjTranspose]
theorem marginalHermitian_nonneg {q Q : ℕ} (r : QRegister q Q)
    {B : HermitianMat (Fin (2 ^ Q)) ℂ} (hB : 0 ≤ B) :
    0 ≤ marginalHermitian r B :=
  Finset.sum_nonneg fun env _ ↦ B.conj_nonneg (envSliceIso r env) hB
@[simp]
theorem marginalHermitian_trace {q Q : ℕ} (r : QRegister q Q) (B : HermitianMat (Fin (2 ^ Q)) ℂ) :
    (marginalHermitian r B).trace = B.trace := by
  have h := liftHermitian_inner_eq r 1 B
  rw [liftHermitian_one, HermitianMat.one_inner, HermitianMat.one_inner] at h; exact h.symm
/-- Marginal partial density operator on subregister `r`. -/
noncomputable def marginalPDO {q Q : ℕ} (r : QRegister q Q) (ρ : 𝒟 (Fin (2 ^ Q))) :
    𝒟 (Fin (2 ^ q)) :=
  ⟨marginalHermitian r ρ.1, marginalHermitian_nonneg r ρ.2.1,
    (marginalHermitian_trace r ρ.1).trans_le ρ.2.2⟩
/-- Marginal classical-quantum state on subregister `r`. -/
noncomputable def marginalState {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (Δ : CQState (Store Var) (2 ^ Q)) : CQState (Store Var) (2 ^ q) :=
  ⟨fun σ ↦ marginalPDO r (Δ.1 σ), by
    rcases Δ.2 with ⟨c, hc, hc1⟩
    have htr : (fun σ ↦ (marginalPDO r (Δ.1 σ)).trace) = fun σ ↦ (Δ.1 σ).trace :=
      funext fun σ ↦ NNReal.coe_inj.mp (marginalHermitian_trace r (Δ.1 σ).1)
    exact ⟨c, htr ▸ hc, hc1⟩⟩
@[simp]
theorem trace_marginalState {Var : Type} {q Q : ℕ} (r : QRegister q Q) (Δ : CQState (Store Var) (2 ^
    Q)) :
    (marginalState r Δ).trace = Δ.trace := by
  apply NNReal.coe_inj.mp
  rw [qcTraceEqTsumStore, qcTraceEqTsumStore]
  exact tsum_congr fun σ ↦ marginalHermitian_trace r (Δ.1 σ).1
@[simp]
theorem stateMass_marginalState {Var : Type} {q Q : ℕ} (r : QRegister q Q) (Δ : CQState (Store Var)
    (2 ^
    Q)) : stateMass (marginalState r Δ) = stateMass Δ := by
  rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, trace_marginalState]
theorem expect_liftAssertion_eq_marginalState {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (Δ : CQState (Store Var) (2 ^ Q)) (Θ : CQAssertion (Store Var) (2 ^ q)) :
    𝔼[Δ, liftAssertion r Θ] = 𝔼[marginalState r Δ, Θ] := by
  simp_rw [qcExpectEqTsumStore]; exact tsum_congr fun σ ↦ liftHermitian_inner_eq r (Θ σ).1 (Δ.1 σ).1
theorem marginalState_trueState {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (cond : Store Var → Prop) [DecidablePred cond] (Δ : CQState (Store Var) (2 ^ Q)) :
    marginalState r (Δ.cqTrueSt cond) = (marginalState r Δ).cqTrueSt cond := by
  apply Subtype.ext; funext σ; apply Subtype.ext
  change marginalHermitian r ((Δ.cqTrueSt cond).1 σ).1 = (((marginalState r Δ).cqTrueSt cond).1 σ).1
  by_cases h : cond σ <;> simp [CQState.cqTrueSt, marginalState, marginalPDO, h]
theorem marginalState_falseState {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    (cond : Store Var → Prop) [DecidablePred cond] (Δ : CQState (Store Var) (2 ^ Q)) :
    marginalState r (Δ.cqFalseSt cond) = (marginalState r Δ).cqFalseSt cond := by
  apply Subtype.ext; funext σ; apply Subtype.ext
  change marginalHermitian r ((Δ.cqFalseSt cond).1 σ).1 =
    (((marginalState r Δ).cqFalseSt cond).1 σ).1
  by_cases h : cond σ <;> simp [CQState.cqFalseSt, marginalState, marginalPDO, h]
theorem pdo_eq_of_forall_obs_inner_eq {d : ℕ} {ρ₁ ρ₂ : 𝒟 (Fin d)}
    (h : ∀ o : Observable (Fin d), ⟪o.1, ρ₁.1⟫_ℝ = ⟪o.1, ρ₂.1⟫_ℝ) : ρ₁ = ρ₂ := by
  have hle1 (ρ : 𝒟 (Fin d)) : ρ.1 ≤ 1 := (HermitianMat.le_trace_smul_one ρ.2.1).trans
      (by simpa using smul_le_smul_of_nonneg_right ρ.2.2 (zero_le_one' (HermitianMat (Fin d) ℂ)))
  have h1 := h ⟨ρ₁.1, ρ₁.2.1, hle1 ρ₁⟩; have h2 := h ⟨ρ₂.1, ρ₂.2.1, hle1 ρ₂⟩
  have hdiff : ⟪ρ₁.1 - ρ₂.1, ρ₁.1 - ρ₂.1⟫_ℝ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; dsimp only at h1 h2; linarith
  exact Subtype.ext (sub_eq_zero.mp (inner_self_eq_zero.mp hdiff))
theorem cqState_eq_of_forall_expect_eq {Var : Type} {d : ℕ} {Δ₁ Δ₂ : CQState (Store Var) d} (h : ∀ Θ
    :
    CQAssertion (Store Var) d, 𝔼[Δ₁, Θ] = 𝔼[Δ₂, Θ]) : Δ₁ = Δ₂ := by
  open Classical in
  apply Subtype.ext; funext σ₀; refine pdo_eq_of_forall_obs_inner_eq fun o ↦ ?_
  let Θ : CQAssertion (Store Var) d := fun σ ↦ if σ = σ₀ then o else 0
  have heval (Δ : CQState (Store Var) d) : 𝔼[Δ, Θ] = ⟪o.1, (Δ.1 σ₀).1⟫_ℝ := by
    rw [qcExpectEqTsumStore, tsum_eq_single σ₀]
    · simp [Θ]
    · intro σ hσ; simp [Θ, hσ]
  have hΘ := h Θ; rwa [heval Δ₁, heval Δ₂] at hΘ
/-- Embed a `q`-qubit `OracleDynamicCircuit` into subregister `r: QRegister q Q`,
  phase-tagging
  non-oracle `.step` unitaries so real marking oracles incur zero non-oracle cost. -/
noncomputable def embedOracleCirc {Var : Type} {q Q w : ℕ} (r : QRegister q Q) :
    OracleDynamicCircuit (Unitary (2 ^ q)) Var q w →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w
  | .step U => .step (GroverSol.phaseTag (r.embedUnitary U))
  | .oracle emb => .oracle (r.compose emb)
  | .measure x reg => .measure x (r.compose reg)
  | .skip => .skip
  | .seq c₁ c₂ => .seq (embedOracleCirc r c₁) (embedOracleCirc r c₂)
  | @OracleDynamicCircuit.qIf _ _ _ _ b _ c₁ c₂ =>
      .qIf b (embedOracleCirc r c₁) (embedOracleCirc r c₂)
  | @OracleDynamicCircuit.qWhile _ _ _ _ b _ body =>
      .qWhile b (embedOracleCirc r body)
theorem zeroStepCost_embedOracleCirc {Var : Type} {q Q w : ℕ} (r : QRegister q Q) (c :
    OracleDynamicCircuit (Unitary (2 ^ q)) Var q w) : ZeroStepCost (embedOracleCirc r c) := by
  induction c with
  | «skip» => trivial
  | «step» U =>
      intro oracle horacle
      exact GroverSol.ofEmbeddedOracle_unitaryCost_phaseTag_eq_zero horacle
        (r.embedUnitary U)
  | «oracle» _ => trivial
  | «measure» _ _ => trivial
  | «seq» _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | «qIf» _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | «qWhile» _ _ ih => exact ih
theorem wp_embedOracleCirc_liftAssertion {Var : Type} [DecidableEq Var] {q Q w : ℕ} (r : QRegister
    q Q) (c : OracleDynamicCircuit (Unitary (2 ^ q)) Var q w) (O : Unitary (2 ^ w)) (Θ :
    CQAssertion (Store Var) (2 ^ q)) : wp ((embedOracleCirc r c).compile QProg.qAssign O)
      (liftAssertion r
    Θ) = liftAssertion r (wp (c.compile QProg.qAssign O) Θ) := by
  induction c generalizing Θ with
  | «step» U =>
      funext σ; refine Subtype.ext (Subtype.ext ?_)
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [wp_qAssign, GroverSol.wp_phaseTag, qhlQAssign_val,
        liftAssertion_apply, liftObservable_mat, liftAssertion_apply, liftObservable_mat,
        wp_qAssign, qhlQAssign_val, QRegister.embedUnitary_val,
        ← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, ← r.embedMatrix_mul]
  | oracle emb =>
      funext σ; refine Subtype.ext (Subtype.ext ?_)
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [wp_qAssign, qhlQAssign_val, QRegister.embedUnitary_compose,
        QRegister.embedUnitary_val, liftAssertion_apply, liftObservable_mat,
        liftAssertion_apply, liftObservable_mat, wp_qAssign, qhlQAssign_val,
        ← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, ← r.embedMatrix_mul]
  | measure x reg =>
      funext σ; refine Subtype.ext (HermitianMat.ext ?_)
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      change (∑ o : Fin (2 ^ _), HermitianMat.conj ((r.compose reg).basisOutcomeProjector o)ᴴ
            (liftAssertion r Θ (σ.subst x o.1)).1).mat =
        (liftObservable r ((wp (QProg.measureRegister x reg) Θ) σ)).1.1
      rw [liftObservable_mat, wp_measureRegister_coe_ax]
      change (∑ o : Fin (2 ^ _), HermitianMat.conj ((r.compose reg).basisOutcomeProjector o)ᴴ
        (liftAssertion r Θ (σ.subst x o.1)).1).mat = r.embedMatrix (∑ o : Fin (2 ^ _),
        HermitianMat.conj (reg.basisOutcomeProjector o)ᴴ (Θ (σ.subst x o.1)).1).mat
      rw [HermitianMat.mat_finset_sum, HermitianMat.mat_finset_sum, r.embedMatrix_sum]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      have hproj : (r.compose reg).basisOutcomeProjector o =
          r.embedMatrix (reg.basisOutcomeProjector o) := by
        unfold QRegister.basisOutcomeProjector
        exact QRegister.embedMatrix_compose r reg (compProj o)
      rw [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
        HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose, liftAssertion_apply, ←
        HermitianMat.val_eq_coe, ← HermitianMat.val_eq_coe, liftObservable_mat, hproj, ←
        r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, ← r.embedMatrix_mul]
  | «skip» => rfl
  | seq c₁ c₂ ih₁ ih₂ =>
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]; rw [wp_qSeq, wp_qSeq, ih₂, ih₁]
  | qIf b c₁ c₂ ih₁ ih₂ =>
      funext σ; dsimp only [embedOracleCirc, OracleDynamicCircuit.compile, wp_qIf]
      by_cases hb : b σ <;> simp [hb, ih₁, ih₂, liftAssertion]
  | qWhile b body ih =>
      let bodyG := (embedOracleCirc r body).compile QProg.qAssign O
      let bodyL := body.compile QProg.qAssign O
      have hrec (t : ℕ) : whileRecWP (wp bodyG) b t (liftAssertion r Θ) = liftAssertion r
        (whileRecWP (wp bodyL) b t Θ) := by
        induction t with
        | zero => funext σ; apply Subtype.ext; exact (liftHermitian_zero r).symm
        | succ t iht =>
            funext σ; dsimp only [whileRecWP]; by_cases hb : b σ
            · rw [ite_eq_left hb, iht, ih]; simp [liftAssertion, hb, bodyL]
            · simp [hb, liftAssertion]
      funext σ; dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [wp_qWhile, wp_qWhile, liftAssertion_apply, OmegaCompletePartialOrder.Pi.ωSup_apply,
        OmegaCompletePartialOrder.Pi.ωSup_apply, liftObservable_ωSup]
      congr 1; exact DFunLike.ext _ _ fun t ↦ congrFun (hrec t) σ
theorem marginalState_interp_embedOracleCirc {Var : Type} [DecidableEq Var] {q Q w : ℕ} (r :
    QRegister q Q) (c : OracleDynamicCircuit (Unitary (2 ^ q)) Var q w) (O : Unitary (2 ^ w)) (Δ :
    CQState (Store Var) (2 ^ Q)) : marginalState r ((interp ((embedOracleCirc r c).compile
      QProg.qAssign
    O)).toStateFun Δ) = (interp (c.compile QProg.qAssign O)).toStateFun (marginalState r Δ) := by
  refine cqState_eq_of_forall_expect_eq fun Θ ↦ ?_
  rw [← expect_liftAssertion_eq_marginalState, ← wp_expectation_eq,
    wp_embedOracleCirc_liftAssertion, expect_liftAssertion_eq_marginalState, wp_expectation_eq]
theorem expectedCost_embedOracleCirc_le {Var : Type} [DecidableEq Var] {q Q w : ℕ} (r : QRegister
    q Q) (c : OracleDynamicCircuit (Unitary (2 ^ q)) Var q w) {O : Unitary (2 ^ w)} (hO :
    GroverSol.IsRealMatrix O.1) (Δ : CQState (Store Var) (2 ^ Q)) : expectedCost
    (CostModel.ofEmbeddedOracle O) ((embedOracleCirc r c).compile QProg.qAssign O) Δ ≤
    expectedCost (CostModel.ofEmbeddedOracle O) (c.compile QProg.qAssign O) (marginalState r
    Δ) := by
  induction c generalizing Δ with
  | «step» U =>
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [expectedCost_qAssign, GroverSol.ofEmbeddedOracle_unitaryCost_phaseTag_eq_zero hO]
      simp
  | oracle emb =>
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [expectedCost_qAssign, expectedCost_qAssign,
        CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary,
        CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, trace_marginalState]
  | measure x reg =>
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile, measureRegister]; simp
  | «skip» => simp [embedOracleCirc, OracleDynamicCircuit.compile]
  | seq c₁ c₂ ih₁ ih₂ =>
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [expectedCost_qSeq, expectedCost_qSeq, ← marginalState_interp_embedOracleCirc]
      exact add_le_add (ih₁ Δ) (ih₂ _)
  | qIf b c₁ c₂ ih₁ ih₂ =>
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [cqExpectedCostIf, cqExpectedCostIf, ← marginalState_trueState, ← marginalState_falseState]
      exact add_le_add (ih₁ _) (ih₂ _)
  | qWhile b body ih =>
      let bodyG := (embedOracleCirc r body).compile QProg.qAssign O
      let bodyL := body.compile QProg.qAssign O
      dsimp only [embedOracleCirc, OracleDynamicCircuit.compile]
      rw [expectedCost_qWhile, expectedCost_qWhile]; refine iSup_le fun t ↦ le_iSup_of_le t ?_
      have hrec (n : ℕ) (δ : CQState (Store Var) (2 ^ Q)) : whileRecCost (expectedCost
        (CostModel.ofEmbeddedOracle O) bodyG) ((interp bodyG).toStateFun) b n δ ≤ whileRecCost
        (expectedCost (CostModel.ofEmbeddedOracle O) bodyL) ((interp bodyL).toStateFun) b n
        (marginalState r δ) := by
        induction n generalizing δ with
        | zero => simp
        | succ n ihn =>
            rw [cqWhileRecCostSuc, cqWhileRecCostSuc, ← marginalState_trueState]
            have hstep := ihn ((interp bodyG).toStateFun (δ.cqTrueSt b))
            rw [marginalState_interp_embedOracleCirc r body O (δ.cqTrueSt b)] at hstep
            exact add_le_add (ih (δ.cqTrueSt b)) hstep
      exact hrec t Δ
@[simp]
theorem extractIndex_zero_reg {W Q : ℕ} (r : QRegister W Q) :
    r.extractIndex (0 : Fin (2 ^ Q)) = 0 := by
  apply (basisBits W).injective; funext i
  rw [r.basisBits_extractIndex, basisBits_zero, basisBits_zero]; rfl
/-- Full `Q`-wire identity register `QRegister.block 0 Q (Nat.zero_add Q).le`. -/
def allWiresReg (Q : ℕ) : QRegister Q Q :=
  QRegister.block 0 Q (Nat.zero_add Q).le
@[simp]
theorem extractIndex_allWiresReg {Q : ℕ} (z : Fin (2 ^ Q)) :
    (allWiresReg Q).extractIndex z = z := by
  apply (basisBits Q).injective; funext i; rw [(allWiresReg Q).basisBits_extractIndex]
  have hw : (allWiresReg Q) i = i := Fin.ext (by simp [allWiresReg]); rw [hw]
/-- Zero-oracle-cost full-register reset restoring `|0 ^ Q⟩` on any incoming `CQState`. -/
noncomputable def resetAllCircuit {Var : Type} {Q w : ℕ} (res : Var) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w :=
  resetRegCircuit res (allWiresReg Q)
theorem zeroStepCost_resetAllCircuit {Var : Type} {Q w : ℕ} (res : Var) :
    ZeroStepCost (resetAllCircuit (Q := Q) (w := w) res) :=
  zeroStepCost_resetRegCircuit res (allWiresReg Q)
theorem basisOutcomeProjector_eq_diagProj {W Q : ℕ} (r : QRegister W Q) (o : Fin (2 ^ W)) :
    r.basisOutcomeProjector o = diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = o) := by
  have hvec (b : Fin (2 ^ Q)) : r.basisOutcomeProjector o *ᵥ Pi.single b (1 : ℂ) = diagProj (fun z
    : Fin (2 ^ Q) ↦ r.extractIndex z = o) *ᵥ Pi.single b (1 : ℂ) := by
    rw [r.basisOutcomeProjector_mulVec_single]; funext a
    simp only [diagProj, Matrix.mulVec_diagonal, Pi.single_apply]; by_cases hab : a = b
    · subst hab; by_cases hex : r.extractIndex a = o <;> simp [hex]
    · by_cases hex : r.extractIndex b = o <;> simp [hab, hex]
  ext a b; simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hvec b) a
theorem permutationUnitary_conjTranspose {d : ℕ} (e : Equiv.Perm (Fin d)) :
    (permutationUnitary e).1ᴴ = (permutationUnitary e.symm).1 := by
  have hmul : (permutationUnitary e).1 * (permutationUnitary e.symm).1 = 1 := by
    have hv (x : Fin d) : ((permutationUnitary e).1 * (permutationUnitary e.symm).1) *ᵥ Pi.single
      x (1 : ℂ) = (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ Pi.single x (1 : ℂ) := by
      rw [← Matrix.mulVec_mulVec, permutationUnitary_mulVec_single,
        permutationUnitary_mulVec_single, Equiv.apply_symm_apply, Matrix.one_mulVec]
    ext a b; simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hv b) a
  calc (permutationUnitary e).1ᴴ = (permutationUnitary e).1ᴴ * 1 := (Matrix.mul_one _).symm
    _ = (permutationUnitary e).1ᴴ *
          ((permutationUnitary e).1 * (permutationUnitary e.symm).1) := by rw [hmul]
    _ = ((permutationUnitary e).1ᴴ * (permutationUnitary e).1) *
          (permutationUnitary e.symm).1 := (Matrix.mul_assoc _ _ _).symm
    _ = 1 * (permutationUnitary e.symm).1 := by
          rw [← Matrix.star_eq_conjTranspose, (permutationUnitary e).2.1]
    _ = (permutationUnitary e.symm).1 := Matrix.one_mul _
theorem conj_permutationUnitary_diagProj {d : ℕ} (e : Equiv.Perm (Fin d)) (P : Fin d → Prop)
    [DecidablePred P] : (permutationUnitary e).1ᴴ * diagProj P * (permutationUnitary e).1 =
    diagProj (fun z ↦ P (e z)) := by
  have hv (x : Fin d) : ((permutationUnitary e).1ᴴ * diagProj P * (permutationUnitary e).1) *ᵥ
    Pi.single x (1 : ℂ) = diagProj (fun z ↦ P (e z)) *ᵥ Pi.single x (1 : ℂ) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      permutationUnitary_mulVec_single]
    have hd : diagProj P *ᵥ Pi.single (e x) (1 : ℂ) =
        (if P (e x) then (1 : ℂ) else 0) • Pi.single (e x) (1 : ℂ) := by
      funext a; simp only [diagProj, Matrix.mulVec_diagonal, Pi.single_apply]
      by_cases ha : a = e x <;> by_cases hp : P (e x) <;> simp [ha, hp]
    have hd2 : diagProj (fun z ↦ P (e z)) *ᵥ Pi.single x (1 : ℂ) =
        (if P (e x) then (1 : ℂ) else 0) • Pi.single x (1 : ℂ) := by
      funext a; simp only [diagProj, Matrix.mulVec_diagonal, Pi.single_apply]
      by_cases ha : a = x <;> by_cases hp : P (e x) <;> simp [ha, hp]
    rw [hd, hd2, Matrix.mulVec_smul, permutationUnitary_conjTranspose,
      permutationUnitary_mulVec_single, Equiv.symm_apply_apply]
  ext a b; simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hv b) a
theorem diagObs_mono {d : ℕ} {P₁ P₂ : Fin d → Prop} [DecidablePred P₁] [DecidablePred P₂] (h : ∀ z
    : Fin d, P₁ z → P₂ z) : diagObs P₁ ≤ diagObs P₂ := by
  apply Subtype.mk_le_mk.mpr; apply HermitianMat.le_iff.mpr
  change (diagProj P₂ - diagProj P₁).PosSemidef
  have hsub : diagProj P₂ - diagProj P₁ = Matrix.diagonal (fun z : Fin d ↦ (if P₂ z then (1 : ℂ)
    else 0) - (if P₁ z then (1 : ℂ) else 0)) := by
    ext i j; by_cases hij : i = j <;> simp [diagProj, hij]
  rw [hsub, Matrix.posSemidef_diagonal_iff]; intro z; by_cases h1 : P₁ z
  · simp [h1, h z h1]
  · by_cases h2 : P₂ z <;> simp [h1, h2]
theorem wp_qAssign_permutationUnitary_diagAssertion {Var : Type} {d : ℕ} (e : Equiv.Perm (Fin d))
    (P : Fin d → Prop) [DecidablePred P] : CQAssertion.qAssign (permutationUnitary e)
    (diagAssertion (Var := Var) P) = diagAssertion (fun z ↦ P (e z)) := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
    diagAssertion, diagObs_mat, diagAssertion, diagObs_mat, conj_permutationUnitary_diagProj]
theorem wp_resetRegCircuit_top_le {Var : Type} [DecidableEq Var] {W Q w : ℕ} (res : Var) (r :
    QRegister W Q) (oracle : Unitary (2 ^ w)) : (⊤ : CQAssertion (Store Var) (2 ^ Q)) ≤ wp
    ((resetRegCircuit res r).compile QProg.qAssign oracle) (diagAssertion (fun z : Fin (2 ^ Q) ↦
    r.extractIndex z = 0)) := by
  intro σ; apply le_of_eq; apply Subtype.ext; apply HermitianMat.ext
  have htop : ((⊤ : CQAssertion (Store Var) (2 ^ Q)) σ).1.mat = 1 := (by simp)
  change ((⊤ : CQAssertion (Store Var) (2 ^ Q)) σ).1.mat = (wp ((resetRegCircuit res r).compile
    QProg.qAssign oracle) (diagAssertion (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = 0)) σ).1.mat
  rw [htop, wp_resetRegCircuit]; have hterm (o : Fin (2 ^ W)) :
      (r.resetKraus o)ᴴ * diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = 0) *
        r.resetKraus o = diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = o) := by
    have hmul_k : diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = 0) * r.resetKraus o =
        r.resetKraus o := by
      have hv (x : Fin (2 ^ Q)) : (diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = 0) *
        r.resetKraus o) *ᵥ Pi.single x (1 : ℂ) = r.resetKraus o *ᵥ Pi.single x (1 : ℂ) := by
        rw [← Matrix.mulVec_mulVec, ← permutationUnitary_regMaskVec_mul_basisOutcomeProjector,
          ← Matrix.mulVec_mulVec, r.basisOutcomeProjector_mulVec_single]
        by_cases hx : r.extractIndex x = o
        · rw [ite_eq_left hx, permutationUnitary_mulVec_single,
            xorBitsPerm_regMaskVec_eq_replaceIndex_zero r o x hx]
          have hz0 : r.extractIndex (r.replaceIndex x 0) = 0 := r.extractIndex_replaceIndex x 0
          funext c; by_cases hc : c = r.replaceIndex x 0
          · subst hc; simp [diagProj, hz0]
          · simp [diagProj, hc]
        · simp [hx]
      ext i j; simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (hv j) i
    rw [Matrix.mul_assoc, hmul_k, ← permutationUnitary_regMaskVec_mul_basisOutcomeProjector]
    set Uo := permutationUnitary (xorBitsPerm (regMaskVec r o.val))
    calc (Uo.1 * r.basisOutcomeProjector o)ᴴ * (Uo.1 * r.basisOutcomeProjector o)
        = (r.basisOutcomeProjector o)ᴴ * (Uo.1ᴴ * Uo.1) * r.basisOutcomeProjector o := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = r.basisOutcomeProjector o * r.basisOutcomeProjector o := by
            have hU : Uo.1ᴴ * Uo.1 = 1 := (by rw [← Matrix.star_eq_conjTranspose, Uo.2.1])
            rw [hU, Matrix.mul_one, r.basisOutcomeProjector_conjTranspose]
      _ = diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = o) := by
            rw [basisOutcomeProjector_eq_diagProj, diagProj_mul_self]
  simp_rw [diagAssertion, diagObs_mat, hterm]; ext a b; rw [Matrix.sum_apply]; by_cases hab : a = b
  · subst hab; rw [Finset.sum_eq_single (r.extractIndex a)]
    · simp [diagProj]
    · intro o _ hne; simp [diagProj, Ne.symm hne]
    · intro habs; exact (habs (Finset.mem_univ _)).elim
  · simp [diagProj, hab]
theorem resetAllCircuit_transition {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var) {oracle :
    Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1) (Ξ : CQState (Store Var) (2 ^ Q)) :
    let prog := (resetAllCircuit res).compile QProg.qAssign oracle
    let Ξ' := (interp prog).toStateFun Ξ
    expectedCost (CostModel.ofEmbeddedOracle oracle) prog Ξ = 0 ∧ Ξ'.trace = Ξ.trace ∧ stateMass
      Ξ' = stateMass Ξ ∧ SupportedOn (· = (0 : Fin (2 ^ Q))) Ξ' := by
  intro prog Ξ'
  have hcost : expectedCost (CostModel.ofEmbeddedOracle oracle) prog Ξ = 0 := nonpos_iff_eq_zero.mp
      (by simpa [prog, resetAllCircuit] using
        costBound_resetRegCircuit horacle res (allWiresReg Q) Ξ)
  have hwp : (⊤ : CQAssertion (Store Var) (2 ^ Q)) ≤
      wp prog (diagAssertion (· = (0 : Fin (2 ^ Q)))) := by
    have h1 := wp_resetRegCircuit_top_le (Var := Var) res (allWiresReg Q) oracle
    have hd : diagAssertion (Var := Var)
        (fun z : Fin (2 ^ Q) ↦ (allWiresReg Q).extractIndex z = 0) ≤
        diagAssertion (· = (0 : Fin (2 ^ Q))) :=
      fun _ ↦ diagObs_mono fun z hz ↦ (extractIndex_allWiresReg z).symm.trans hz
    exact h1.trans (wp_mono prog hd)
  have hge : (Ξ.trace : ℝ) ≤ 𝔼[Ξ', diagAssertion (· = (0 : Fin (2 ^ Q)))] := by
    rw [← expect_top Ξ, ← wp_expectation_eq prog Ξ]; exact expect_mono le_rfl hwp
  have hle1 : 𝔼[Ξ', diagAssertion (· = (0 : Fin (2 ^ Q)))] ≤ Ξ'.trace := by
    rw [← expect_top Ξ']; exact expect_mono le_rfl le_top
  have hle2 : Ξ'.trace ≤ Ξ.trace := (interp prog).trace_toStateFun_le Ξ
  have htr : Ξ'.trace = Ξ.trace := le_antisymm hle2 (NNReal.coe_le_coe.mp (hge.trans hle1))
  have hexp : 𝔼[Ξ', diagAssertion (· = (0 : Fin (2 ^ Q)))] = Ξ'.trace :=
    le_antisymm hle1 (by simpa [htr] using hge)
  have hmass : stateMass Ξ' = stateMass Ξ := by
    rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr]
  exact ⟨hcost, htr, hmass, supportedOn_of_expect_diagAssertion_eq_trace hexp⟩
theorem supportedOn_zero_marginalState {Var : Type} {q Q : ℕ} (r : QRegister q Q)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ) :
    SupportedOn (· = (0 : Fin (2 ^ q))) (marginalState r Δ) := by
  apply supportedOn_of_expect_diagAssertion_eq_trace
  rw [← expect_liftAssertion_eq_marginalState, trace_marginalState]
  have hev := expect_of_supportedOn hΔ
    (Θ := liftAssertion r (diagAssertion (· = (0 : Fin (2 ^ q))))) (c := 1) fun σ ↦ by
      ext a b; rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]; by_cases hab : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := hab
        simp only [and_self, ↓reduceIte, diagProj, Matrix.diagonal_apply, smul_eq_mul, mul_one,
          Complex.ofReal_one]
        have hl : (liftAssertion r (diagAssertion (· = (0 : Fin (2 ^ q)))) σ).1.mat =
            r.embedMatrix (diagProj (· = (0 : Fin (2 ^ q)))) := by
          rw [liftAssertion_apply, ← HermitianMat.val_eq_coe, liftObservable_mat,
            HermitianMat.val_eq_coe, diagAssertion, diagObs_mat]
        change (liftAssertion r (diagAssertion (· = (0 : Fin (2 ^ q)))) σ).1.mat 0 0 = 1
        have hag0 : r.AgreeOutside 0 0 := fun _ _ ↦ rfl
        rw [hl, QRegister.embedMatrix_apply_of_agreeOutside, extractIndex_zero_reg]
        simp [diagProj, hag0]
      · simp only [hab, ↓reduceIte, diagProj, Matrix.diagonal_apply]; by_cases heq : a = b
        · subst heq; have hne : a ≠ 0 := fun h ↦ hab ⟨h, h⟩; simp [hne]
        · simp [heq]
  simpa using hev
theorem cqState_eq_qSet_of_supportedOn_zero {Var : Type} {d : ℕ} [NeZero d] {δ : CQState (Store Var)
    d}
    (hδ : SupportedOn (· = (0 : Fin d)) δ) : δ = δ.qSet := by
  apply Subtype.ext; funext σ; apply Subtype.ext; apply HermitianMat.ext
  change (δ.1 σ).1.mat = Matrix.single 0 0 ((δ.1 σ).1.trace : ℂ); have hmat := hδ σ
  have hentry (i j : Fin d) (hij : ¬ (i = 0 ∧ j = 0)) : (δ.1 σ).1.mat i j = 0 := by
    have h1 := congrFun (congrFun hmat i) j; rw [diagProj_mul_mul_diagProj_apply] at h1
    simpa [hij] using h1.symm
  have h00 : (δ.1 σ).1.mat 0 0 = ((δ.1 σ).1.trace : ℂ) := by
    have hself : star ((δ.1 σ).1.mat 0 0) = (δ.1 σ).1.mat 0 0 := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (δ.1 σ).1.2 0) 0
    have hre_eq : (δ.1 σ).1.mat 0 0 = (((δ.1 σ).1.mat 0 0).re : ℂ) :=
      (Complex.conj_eq_iff_re.mp hself).symm
    have htr : (δ.1 σ).1.trace = ((δ.1 σ).1.mat 0 0).re := by
      rw [HermitianMat.trace_eq_re_trace]; dsimp only [Matrix.trace, Matrix.diag]
      rw [Finset.sum_eq_single 0 (fun x _ hx ↦ hentry x x (fun h ↦ hx h.1)) (fun h ↦ (h
        (Finset.mem_univ _)).elim)]; rfl
    rw [htr, ← hre_eq]
  ext i j; rw [Matrix.single_apply]; by_cases hij : i = 0 ∧ j = 0
  · rcases hij with ⟨rfl, rfl⟩; simp only [and_self, ↓reduceIte]; exact h00
  · have hij' : ¬ (0 = i ∧ 0 = j) := fun ⟨h1, h2⟩ ↦ hij ⟨h1.symm, h2.symm⟩
    rw [ite_eq_right hij']; exact hentry i j hij
/-- Overwrite classical variable `res` with `(val.val: ℤ)` on any incoming quantum state by
  resetting `r`, XORing `val` onto `r`, and measuring `r` into `res` (`0` oracle queries). -/
noncomputable def setClassicalValCircuit {Var : Type} {W Q w : ℕ} (res : Var)
    (r : QRegister W Q) (val : Fin (2 ^ W)) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w :=
  .seq (resetRegCircuit res r)
    (.seq (.step (phaseI (permutationUnitary (xorBitsPerm (regMaskVec r val.val)))))
      (.measure res r))
theorem zeroStepCost_setClassicalValCircuit {Var : Type} {W Q w : ℕ} (res : Var)
    (r : QRegister W Q) (val : Fin (2 ^ W)) :
    ZeroStepCost (setClassicalValCircuit (w := w) res r val) :=
  ⟨zeroStepCost_resetRegCircuit res r, zeroStepCost_step_phaseI (isRealMatrix_permutationUnitary _),
    trivial⟩
theorem setClassicalValCircuit_transition {Var : Type} [DecidableEq Var] {W Q w : ℕ} (res : Var)
    (r : QRegister W Q) (val : Fin (2 ^ W)) {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix
    oracle.1) {P : Store Var → Prop} (hP : ∀ σ : Store Var, P (σ.subst res (val.val : ℤ))) (Ξ :
    CQState (Store Var) (2 ^ Q)) :
    let prog := (setClassicalValCircuit res r val).compile QProg.qAssign oracle
    𝔼[(interp prog).toStateFun Ξ, liftPureProp P] = Ξ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle oracle) prog Ξ = 0 := by
  intro prog; let model := CostModel.ofEmbeddedOracle (n := Q) oracle
  have hcost : expectedCost model prog Ξ = 0 := by
    dsimp only [prog, setClassicalValCircuit]
    simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
      OracleDynamicCircuit.compile_measure, QProg.measureRegister, expectedCost_qSeq,
      expectedCost_qAssign, expectedCost_qMeasure]
    have hc_rst : expectedCost model ((resetRegCircuit res r).compile QProg.qAssign oracle) Ξ = 0 :=
      nonpos_iff_eq_zero.mp (by simpa [model] using costBound_resetRegCircuit horacle res r Ξ)
    have hc_xor := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle
      (isRealMatrix_permutationUnitary (xorBitsPerm (regMaskVec r val.val)))
    rw [hc_rst, hc_xor]; simp [model, CostModel.ofEmbeddedOracle]
  have hwp_meas : diagAssertion (Var := Var) (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = val) ≤
      wp (QProg.measureRegister res r) (liftPureProp P) := by
    intro τ; rw [QProg.measureRegister, wp_qMeasure]
    change (diagObs (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = val)).1 ≤ ∑ o : Fin (2 ^ W),
      HermitianMat.conj (r.basisOutcomeProjector o)ᴴ (liftPureProp P (Store.subst τ res ↑o.val)).1
    have hnn (o : Fin (2 ^ W)) : 0 ≤ HermitianMat.conj (r.basisOutcomeProjector o)ᴴ (liftPureProp
      P (Store.subst τ res ↑o.val)).1 := HermitianMat.conj_nonneg _ (liftPureProp P (Store.subst τ
      res ↑o.val)).2.1
    refine le_trans ?_ (Finset.single_le_sum (fun o _ ↦ hnn o) (Finset.mem_univ val))
    have hP_τ : P (Store.subst τ res ↑val.val) := hP τ; have hval_top :
        (liftPureProp (Var := Var) (d := 2 ^ Q) P (Store.subst τ res ↑val.val)).1 = 1 := by
      open Classical in
      rw [liftPureProp_apply, ite_eq_left hP_τ]; rfl
    rw [hval_top]; apply le_of_eq; apply HermitianMat.ext
    rw [diagObs_mat, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
      r.basisOutcomeProjector_conjTranspose, HermitianMat.mat_one, Matrix.mul_one,
      basisOutcomeProjector_eq_diagProj, diagProj_mul_self]
  let U_val := permutationUnitary (xorBitsPerm (regMaskVec r val.val))
  have hwp_xor : diagAssertion (Var := Var) (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = 0) ≤
      wp (QProg.qAssign (phaseI U_val))
        (diagAssertion (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = val)) := by
    rw [wp_qAssign, qAssign_phaseI, wp_qAssign_permutationUnitary_diagAssertion]; intro τ
    refine diagObs_mono fun z hz0 ↦ ?_
    rw [xorBitsPerm_regMaskVec_of_clean r val z hz0]; exact r.extractIndex_replaceIndex z val
  have hwp_all : (⊤ : CQAssertion (Store Var) (2 ^ Q)) ≤ wp prog (liftPureProp P) := by
    dsimp only [prog, setClassicalValCircuit]
    simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
      OracleDynamicCircuit.compile_measure, wp_qSeq]
    exact (wp_resetRegCircuit_top_le res r oracle).trans
      (wp_mono _ (hwp_xor.trans (wp_mono _ hwp_meas)))
  have hge : (Ξ.trace : ℝ) ≤ 𝔼[(interp prog).toStateFun Ξ, liftPureProp P] := by
    rw [← expect_top Ξ, ← wp_expectation_eq]; exact expect_mono le_rfl hwp_all
  have hle : 𝔼[(interp prog).toStateFun Ξ, liftPureProp P] ≤ Ξ.trace := by
    calc 𝔼[(interp prog).toStateFun Ξ, liftPureProp P]
        ≤ 𝔼[(interp prog).toStateFun Ξ, ⊤] := expect_mono le_rfl le_top
      _ = ((interp prog).toStateFun Ξ).trace := expect_top _
      _ ≤ Ξ.trace := NNReal.coe_le_coe.mpr ((interp prog).trace_toStateFun_le Ξ)
  exact ⟨le_antisymm hle hge, hcost⟩
/-- Base-`2 ^ n` natural encoding of a list of indices in `Fin (2 ^ n)`. -/
def encodeListNat (n : ℕ) : List (Fin (2 ^ n)) → ℕ
  | [] => 0
  | x :: xs => x.val + 2 ^ n * encodeListNat n xs
theorem encodeListNat_lt (n : ℕ) : ∀ L : List (Fin (2 ^ n)),
    encodeListNat n L < (2 ^ n) ^ L.length
  | [] => by simp [encodeListNat]
  | x :: xs => by
      simp only [encodeListNat, List.length_cons, pow_succ']
      have hx := x.isLt
      have ih := encodeListNat_lt n xs
      nlinarith
theorem encodeListNat_digit (n : ℕ) : ∀ (L : List (Fin (2 ^ n))) (i : ℕ) (hi : i < L.length),
    (encodeListNat n L / (2 ^ n) ^ i) % 2 ^ n = (L[i]).val
  | [], _, hi => by simp at hi
  | x :: xs, 0, _ => by
      simp only [encodeListNat, pow_zero, Nat.div_one, List.getElem_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.isLt]
  | x :: xs, i + 1, hi => by
      simp only [encodeListNat, pow_succ', List.getElem_cons_succ]
      rw [← Nat.div_div_eq_div_mul]
      have hdiv : (x.val + 2 ^ n * encodeListNat n xs) / 2 ^ n = encodeListNat n xs := by
        rw [add_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt x.isLt, add_zero]
      rw [hdiv]
      exact encodeListNat_digit n xs i (by simpa using hi)
/-- Canonical `n * k`-bit encoding of a `Finset (Fin (2 ^ n))` via `S.toList.take k`. -/
noncomputable def encodeFinsetVal (n k : ℕ) (S : Finset (Fin (2 ^ n))) : Fin (2 ^ (n * k)) :=
  ⟨encodeListNat n (S.toList.take k), by
    have hlt := encodeListNat_lt n (S.toList.take k)
    have hlen : (S.toList.take k).length ≤ k := List.length_take_le k S.toList
    calc encodeListNat n (S.toList.take k)
        < (2 ^ n) ^ (S.toList.take k).length := hlt
      _ ≤ (2 ^ n) ^ k := Nat.pow_le_pow_right (by positivity) hlen
      _ = 2 ^ (n * k) := (pow_mul 2 n k).symm⟩
theorem decodeTargetsLocal_encodeFinsetVal {n k : ℕ} {S : Finset (Fin (2 ^ n))} (hScard : S.card =
    k) : decodeTargetsLocal n k ((encodeFinsetVal n k S).val : ℤ) = S := by
  have hlen : S.toList.length = k := (by rw [Finset.length_toList, hScard])
  have htake : S.toList.take k = S.toList := List.take_of_length_le hlen.le; ext y
  simp only [decodeTargetsLocal, encodeFinsetVal, htake, Int.toNat_natCast, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi_len : i < S.toList.length := hlen ▸ hi
    have hdig := encodeListNat_digit n S.toList i hi_len
    have heq : (⟨(encodeListNat n S.toList / (2 ^ n) ^ i) % 2 ^ n,
        Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ n)) = S.toList[i] := Fin.ext hdig
    rw [heq]; exact Finset.mem_toList.mp (List.getElem_mem hi_len)
  · intro hy; have hy_mem : y ∈ S.toList := Finset.mem_toList.mpr hy
    obtain ⟨i, hi_len, hget⟩ := List.getElem_of_mem hy_mem; refine ⟨i, hlen ▸ hi_len, ?_⟩
    exact Fin.ext ((encodeListNat_digit n S.toList i hi_len).trans (congrArg Fin.val hget))
theorem decodeTargetsLocal_mod_pow (n k : ℕ) (z : ℤ) :
    decodeTargetsLocal n k (((z.toNat % 2 ^ (n * k) : ℕ) : ℤ)) = decodeTargetsLocal n k z := by
  ext y; simp only [decodeTargetsLocal, Int.toNat_natCast, Finset.mem_image, Finset.mem_range]
  refine exists_congr fun i ↦ and_congr_right fun hi ↦ ?_
  suffices hdig : ((z.toNat % 2 ^ (n * k)) / (2 ^ n) ^ i) % 2 ^ n =
      (z.toNat / (2 ^ n) ^ i) % 2 ^ n by
    have hfin : (⟨((z.toNat % 2 ^ (n * k)) / (2 ^ n) ^ i) % 2 ^ n,
        Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ n)) =
        ⟨(z.toNat / (2 ^ n) ^ i) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ := Fin.ext hdig
    rw [hfin]
  let M := (2 ^ n) ^ i; let B := 2 ^ n; have hM : 0 < M := (by positivity)
  have hB : 0 < B := (by positivity)
  have hdvd : M * B ∣ 2 ^ (n * k) := by
    refine ⟨(2 ^ n) ^ (k - 1 - i), ?_⟩
    rw [pow_mul, show M * B * (2 ^ n) ^ (k - 1 - i) =
      (2 ^ n) ^ (i + 1 + (k - 1 - i)) by dsimp [M, B]; rw [pow_add, pow_add, pow_one]]
    congr 1; omega
  have hmod_div (x : ℕ) : (x % (M * B)) / M = (x / M) % B := by
    have h1 : x = M * (x / M) + x % M := (Nat.div_add_mod x M).symm
    have h2 : x / M = B * ((x / M) / B) + (x / M) % B := (Nat.div_add_mod (x / M) B).symm
    have hrem_lt : M * ((x / M) % B) + x % M < M * B := by
      have hmM : x % M < M := Nat.mod_lt x hM; have hmB : (x / M) % B < B := Nat.mod_lt (x / M) hB
      nlinarith
    have hx_eq : x = (M * B) * ((x / M) / B) + (M * ((x / M) % B) + x % M) := by
      calc x = M * (B * ((x / M) / B) + (x / M) % B) + x % M := by rw [← h2, ← h1]
        _ = (M * B) * ((x / M) / B) + (M * ((x / M) % B) + x % M) := by ring
    have hmod_eq : x % (M * B) = M * ((x / M) % B) + x % M := by
      conv_lhs => rw [hx_eq]
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
    rw [hmod_eq, Nat.mul_add_div hM, Nat.div_eq_of_lt (Nat.mod_lt x hM), add_zero]
  change ((z.toNat % 2 ^ (n * k)) / M) % B = (z.toNat / M) % B
  rw [← hmod_div (z.toNat % 2 ^ (n * k)), ← hmod_div z.toNat, Nat.mod_mod_of_dvd z.toNat hdvd]
/- ## 2. `GF(2 ^ n)` Affine Shuffling (`permOracleCirc`) & Zero-Slack Boole Collision Bound -/
/-- Affine bijection `x ↦ a * x + b` on a field `K` for a nonzero unit `a: Kˣ`. -/
def fieldAffinePerm {K : Type*} [Field K] (a : Kˣ) (b : K) : Equiv.Perm K where
  toFun x := (a : K) * x + b
  invFun y := (↑a⁻¹ : K) * (y - b)
  left_inv x := by simp
  right_inv y := by simp
@[simp]
theorem fieldAffinePerm_apply {K : Type*} [Field K] (a : Kˣ) (b x : K) :
    fieldAffinePerm a b x = (a : K) * x + b := rfl
theorem pair_eq_pair_iff_cases {α : Type*} [DecidableEq α] {u v y₀ y₁ : α} (huv : u ≠ v) : ({u, v}
    : Finset α) = {y₀, y₁} ↔ (u = y₀ ∧ v = y₁) ∨ (u = y₁ ∧ v = y₀) := by
  constructor
  · intro heq
    have hu : u = y₀ ∨ u = y₁ := by
      have hmem : u ∈ ({y₀, y₁} : Finset α) := heq ▸ Finset.mem_insert_self u {v}; simpa using hmem
    have hv : v = y₀ ∨ v = y₁ := by
      have hmem : v ∈ ({y₀, y₁} : Finset α) :=
        heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
      simpa using hmem
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (huv rfl).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm u v
theorem finset_map_symm_map {α β : Type*} (e : α ≃ β) (S : Finset α) :
    (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  rw [Finset.map_map]
  have hid : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl _ := by
    ext x; exact e.symm_apply_apply x
  rw [hid, Finset.map_refl]
theorem card_fiber_fieldAffinePerm {K : Type*} [Field K] [Fintype K] [DecidableEq K] {A B : Finset
    K} (hA : A.card = 2) (hB : B.card = 2) : ((Finset.univ : Finset (Kˣ × K)).filter (fun p ↦
    A.map (fieldAffinePerm p.1 p.2).toEmbedding = B)).card = 2 := by
  obtain ⟨x₀, x₁, hx, rfl⟩ := Finset.card_eq_two.mp hA
  obtain ⟨y₀, y₁, hy, rfl⟩ := Finset.card_eq_two.mp hB; have hdx : x₀ - x₁ ≠ 0 := sub_ne_zero.mpr hx
  have hdy01 : y₀ - y₁ ≠ 0 := sub_ne_zero.mpr hy
  have hdy10 : y₁ - y₀ ≠ 0 := sub_ne_zero.mpr hy.symm
  let u₀₁ : Kˣ := Units.mk0 ((y₀ - y₁) * (x₀ - x₁)⁻¹) (mul_ne_zero hdy01 (inv_ne_zero hdx))
  let u₁₀ : Kˣ := Units.mk0 ((y₁ - y₀) * (x₀ - x₁)⁻¹) (mul_ne_zero hdy10 (inv_ne_zero hdx))
  let p₀₁ : Kˣ × K := (u₀₁, y₀ - (u₀₁ : K) * x₀); let p₁₀ : Kˣ × K := (u₁₀, y₁ - (u₁₀ : K) * x₀)
  have huniq {w₀ w₁ : K} (hw : w₀ ≠ w₁) (p : Kˣ × K) : ((p.1 : K) * x₀ + p.2 = w₀ ∧ (p.1 : K) *
    x₁ + p.2 = w₁) ↔ (p.1 : K) = (w₀ - w₁) * (x₀ - x₁)⁻¹ ∧ p.2 = w₀ - (p.1 : K) * x₀ := by
    constructor
    · rintro ⟨h0, h1⟩
      have hsub : (p.1 : K) * (x₀ - x₁) = w₀ - w₁ := (by linear_combination h0 - h1)
      have ha : (p.1 : K) = (w₀ - w₁) * (x₀ - x₁)⁻¹ := by
        calc (p.1 : K) = (p.1 : K) * (x₀ - x₁) * (x₀ - x₁)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hdx, mul_one]
          _ = (w₀ - w₁) * (x₀ - x₁)⁻¹ := by rw [hsub]
      exact ⟨ha, by linear_combination h0⟩
    · rintro ⟨ha, hb⟩
      refine ⟨by rw [hb]; ring, ?_⟩
      calc (p.1 : K) * x₁ + p.2 = w₀ - (p.1 : K) * (x₀ - x₁) := by rw [hb]; ring
        _ = w₀ - (w₀ - w₁) * ((x₀ - x₁)⁻¹ * (x₀ - x₁)) := by rw [ha, mul_assoc]
        _ = w₁ := by rw [inv_mul_cancel₀ hdx]; ring
  have hfib : (Finset.univ : Finset (Kˣ × K)).filter (fun p ↦ ({x₀, x₁} : Finset K).map
    (fieldAffinePerm p.1 p.2).toEmbedding = {y₀, y₁}) = {p₀₁, p₁₀} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.map_insert,
      Finset.map_singleton, Equiv.coe_toEmbedding, fieldAffinePerm_apply, Finset.mem_insert,
      Finset.mem_singleton]
    have hne : (p.1 : K) * x₀ + p.2 ≠ (p.1 : K) * x₁ + p.2 :=
      fun h ↦ hx ((fieldAffinePerm p.1 p.2).injective h)
    rw [pair_eq_pair_iff_cases hne, huniq hy p, huniq hy.symm p]; constructor
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · left; have hp1 : p.1 = u₀₁ := Units.ext (show (p.1 : K) = (u₀₁ : K) from ha)
        exact Prod.ext hp1 (by dsimp only [p₀₁]; rw [hb, hp1])
      · right; have hp1 : p.1 = u₁₀ := Units.ext (show (p.1 : K) = (u₁₀ : K) from ha)
        exact Prod.ext hp1 (by dsimp only [p₁₀]; rw [hb, hp1])
    · rintro (rfl | rfl)
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
  have hp_ne : p₀₁ ≠ p₁₀ := by
    intro heq; have h0 : (p₀₁.1 : K) * x₀ + p₀₁.2 = y₀ := (by dsimp only [p₀₁]; ring)
    have h1 : (p₁₀.1 : K) * x₀ + p₁₀.2 = y₁ := (by dsimp only [p₁₀]; ring)
    rw [heq] at h0; exact hy (h0.symm.trans h1)
  rw [hfib, Finset.card_pair hp_ne]
theorem sum_fieldAffinePerm_eq_two_mul_sum_powersetCard {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {A : Finset K} (hA : A.card = 2) (f : Finset K → ℝ) : (∑ p : Kˣ × K, f (A.map
    (fieldAffinePerm p.1 p.2).toEmbedding)) = 2 * ∑ B ∈ (Finset.univ : Finset K).powersetCard 2, f
    B := by
  let g : Kˣ × K → Finset K := fun p ↦ A.map (fieldAffinePerm p.1 p.2).toEmbedding
  have hmaps : ∀ p ∈ (Finset.univ : Finset (Kˣ × K)),
      g p ∈ (Finset.univ : Finset K).powersetCard 2 := by
    intro p _; rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, by simp [g, hA]⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB ↦ ?_
  have hBcard : B.card = 2 := (Finset.mem_powersetCard.mp hB).2
  calc (∑ i ∈ Finset.univ.filter (fun p ↦ g p = B), f (A.map (fieldAffinePerm i.1
        i.2).toEmbedding)) = ∑ _i ∈ Finset.univ.filter (fun p ↦ g p = B), f B := Finset.sum_congr
        rfl fun i hi ↦ congrArg f (Finset.mem_filter.mp hi).2
    _ = 2 * f B := by rw [Finset.sum_const, card_fiber_fieldAffinePerm hA hBcard, two_smul, two_mul]
namespace GF2nForallA
scoped instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable scoped instance (n : ℕ) : DecidableEq (GaloisField 2 n) :=
  Classical.typeDecidableEq (GaloisField 2 n)
noncomputable scoped instance (n : ℕ) : Fintype (GaloisField 2 n) :=
  Fintype.ofFinite (GaloisField 2 n)
/-- Noncanonical bijection `GaloisField 2 n ≃ Fin (2 ^ n)` for `n ≠ 0`. -/
noncomputable def gfEquivFin {n : ℕ} (hn : n ≠ 0) : GaloisField 2 n ≃ Fin (2 ^ n) :=
  Finite.equivFinOfCardEq (GaloisField.card 2 n hn)
/-- Bijection splitting a `2 * n`-bit seed index into `(Fin (2 ^ n)) × (Fin (2 ^ n))`. -/
def splitSeedEquiv (n : ℕ) : Fin (2 ^ (2 * n)) ≃ Fin (2 ^ n) × Fin (2 ^ n) :=
  (finCongr (by rw [two_mul, pow_add])).trans finProdFinEquiv.symm
/-- Bijection decoding `u: Fin (2 ^ (2 * n))` into `(a_raw, b) ∈ GF(2 ^ n) × GF(2 ^ n)`. -/
noncomputable def seedToGFPair {n : ℕ} (hn : n ≠ 0) :
    Fin (2 ^ (2 * n)) ≃ GaloisField 2 n × GaloisField 2 n :=
  (splitSeedEquiv n).trans ((gfEquivFin hn).symm.prodCongr (gfEquivFin hn).symm)
/-- Transported 2-transitive affine permutation on `Fin (2 ^ n)`. -/
noncomputable def finAffinePerm {n : ℕ} (hn : n ≠ 0) (a : (GaloisField 2 n)ˣ)
    (b : GaloisField 2 n) : Equiv.Perm (Fin (2 ^ n)) :=
  (gfEquivFin hn).symm.trans ((fieldAffinePerm a b).trans (gfEquivFin hn))
theorem sum_finAffinePerm_eq_two_mul_sum_targetSets {n : ℕ} (hn : n ≠ 0) {A : Finset (Fin (2 ^
    n))} (hA : A.card = 2) (f : Finset (Fin (2 ^ n)) → ℝ) : (∑ p : (GaloisField 2 n)ˣ ×
    GaloisField 2 n, f (A.map (finAffinePerm hn p.1 p.2).toEmbedding)) = 2 * ∑ B ∈
    GroverSol.groverTargetSets n 2, f B := by
  let e := gfEquivFin hn; let A_gf : Finset (GaloisField 2 n) := A.map e.symm.toEmbedding
  have hA_gf : A_gf.card = 2 := (by simp [A_gf, hA])
  have hmap (p : (GaloisField 2 n)ˣ × GaloisField 2 n) : A.map (finAffinePerm hn p.1
    p.2).toEmbedding = (A_gf.map (fieldAffinePerm p.1 p.2).toEmbedding).map e.toEmbedding := by
    simp only [A_gf, Finset.map_map]; congr 1
  simp_rw [hmap]
  rw [sum_fieldAffinePerm_eq_two_mul_sum_powersetCard hA_gf (fun S ↦ f (S.map e.toEmbedding))]
  congr 1; unfold GroverSol.groverTargetSets
  refine Finset.sum_bij (fun S _ ↦ S.map e.toEmbedding) ?_ ?_ ?_ ?_
  · intro S hS; rw [Finset.mem_powersetCard] at hS ⊢; exact ⟨Finset.subset_univ _, by simp [hS.2]⟩
  · intro S₁ _ S₂ _ heq
    simpa only [finset_map_symm_map] using congrArg (·.map e.symm.toEmbedding) heq
  · intro B hB; refine ⟨B.map e.symm.toEmbedding, ?_, finset_map_symm_map e.symm B⟩
    rw [Finset.mem_powersetCard] at hB ⊢; exact ⟨Finset.subset_univ _, by simp [hB.2]⟩
  · intro _ _; rfl
theorem card_fiber_finAffinePerm {n : ℕ} (hn : n ≠ 0) {A B : Finset (Fin (2 ^ n))} (hA : A.card =
    2) (hB : B.card = 2) : ((Finset.univ : Finset ((GaloisField 2 n)ˣ × GaloisField 2 n)).filter
    (fun p ↦ A.map (finAffinePerm hn p.1 p.2).toEmbedding = B)).card = 2 := by
  have hsum := sum_finAffinePerm_eq_two_mul_sum_targetSets hn hA
    (fun C ↦ if C = B then (1 : ℝ) else 0)
  have hBmem : B ∈ GroverSol.groverTargetSets n 2 := by
    rw [GroverSol.groverTargetSets, Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, hB⟩
  rw [Finset.sum_ite_eq' _ B, ite_eq_left hBmem, mul_one, ← Finset.sum_filter] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum; exact_mod_cast hsum
end GF2nForallA
open scoped GF2nForallA
/-- Single-slot index wire permutation `(x, b) ↦ (perm x, b)` on `Fin (2 ^ (n + 1))`. -/
def slotIdxPerm {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) : Equiv.Perm (Fin (2 ^ (n + 1))) :=
  (splitBasisEquiv n 1).trans ((perm.prodCongr (Equiv.refl _)).trans (splitBasisEquiv n 1).symm)
theorem slotIdxPerm_conj_slotMarkPerm {n : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) (A : Finset (Fin
    (2 ^ n))) : slotIdxPerm perm * slotMarkPerm A * slotIdxPerm perm.symm = slotMarkPerm (A.map
    perm.toEmbedding) := by
  ext u : 1; obtain ⟨⟨y, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  have hmark (S : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) (b' : Fin (2 ^ 1)) :
      slotMarkPerm S ((splitBasisEquiv n 1).symm (x, b')) =
        (splitBasisEquiv n 1).symm (x, b' + if x ∈ S then 1 else 0) := by
    simp [slotMarkPerm, tableAddPerm, addRightShear]
  have hidx (σ : Equiv.Perm (Fin (2 ^ n))) (x : Fin (2 ^ n)) (b' : Fin (2 ^ 1)) : slotIdxPerm σ
    ((splitBasisEquiv n 1).symm (x, b')) = (splitBasisEquiv n 1).symm (σ x, b') := by
    simp [slotIdxPerm]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hidx perm.symm y b, hmark A (perm.symm y) b,
    hidx perm (perm.symm y) _, Equiv.apply_symm_apply, hmark (A.map perm.toEmbedding) y b]
  have hmem : (perm.symm y ∈ A) ↔ (y ∈ A.map perm.toEmbedding) := by
    constructor
    · intro hy; exact Finset.mem_map.mpr ⟨perm.symm y, hy, perm.apply_symm_apply y⟩
    · intro hy; rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩; simpa using hx
  by_cases hy : y ∈ A.map perm.toEmbedding
  · rw [ite_eq_left (hmem.mpr hy), ite_eq_left hy]
  · rw [ite_eq_right (mt hmem.mp hy), ite_eq_right hy]
/-- Parallel `m`-slot index-permutation unitary across all `(n + 1)`-qubit oracle slots. -/
noncomputable def parallelIdxUnitary {n : ℕ} (m : ℕ) (perm : Equiv.Perm (Fin (2 ^ n))) :
    Unitary (2 ^ ((n + 1) * m)) :=
  parallelSlotProd m (permutationUnitary (slotIdxPerm perm))
theorem isRealMatrix_parallelIdxUnitary {n m : ℕ} (perm : Equiv.Perm (Fin (2 ^ n))) :
    IsRealMatrix (parallelIdxUnitary m perm).1 :=
  isRealMatrix_parallelSlotProd (isRealMatrix_permutationUnitary _)
theorem parallelIdxUnitary_conj_parallelMarkingOracle {n m : ℕ} (perm : Equiv.Perm (Fin (2 ^ n)))
    (A : Finset (Fin (2 ^ n))) : parallelIdxUnitary m perm * parallelMarkingOracle m A *
    parallelIdxUnitary m perm.symm = parallelMarkingOracle m (A.map perm.toEmbedding) := by
  change parallelSlotProd m (permutationUnitary (slotIdxPerm perm)) * parallelSlotProd m
    (setMarkingOracle A) * parallelSlotProd m (permutationUnitary (slotIdxPerm perm.symm)) =
    parallelSlotProd m (setMarkingOracle (A.map perm.toEmbedding))
  rw [parallelSlotProd_mul, parallelSlotProd_mul]; congr 1
  rw [setMarkingOracle, setMarkingOracle, permutationUnitary_mul, permutationUnitary_mul,
    slotIdxPerm_conj_slotMarkPerm]
theorem interp_qAssign_phaseI_seq_phaseI {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (U₁ U₂ U₃ : Unitary d) :
    interp (QProg.qAssign (phaseI U₁) ;; (QProg.qAssign U₂ ;; QProg.qAssign (phaseI U₃)) :
        QProg Var d) =
      interp (QProg.qAssign (U₃ * U₂ * U₁) : QProg Var d) := by
  apply qMonad_ext; intro Δ
  rw [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSeq, QMonad.Q.toStateFun_bind,
    interp_qAssign, interp_qAssign, interp_qAssign, interp_qAssign]
  change CQState.qAssign (phaseI U₃) (CQState.qAssign U₂ (CQState.qAssign (phaseI U₁) Δ)) =
    CQState.qAssign (U₃ * U₂ * U₁) Δ
  rw [cqState_qAssign_phaseI, cqState_qAssign_phaseI, cqState_qAssign_comp, cqState_qAssign_comp,
    mul_assoc]
/-- Functorial oracle-index permutation: conjugates every `.oracle reg` node by `perm`. -/
noncomputable def permOracleCirc {Var : Type} {Q : ℕ} (n m : ℕ)
    (perm : Equiv.Perm (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | .skip => .skip
  | .step U => .step U
  | .oracle reg =>
      .seq (.step (phaseI (reg.embedUnitary (parallelIdxUnitary m perm.symm))))
        (.seq (.oracle reg) (.step (phaseI (reg.embedUnitary (parallelIdxUnitary m perm)))))
  | .measure v reg => .measure v reg
  | .seq c₁ c₂ => .seq (permOracleCirc n m perm c₁) (permOracleCirc n m perm c₂)
  | @OracleDynamicCircuit.qIf _ _ _ _ b inst c₁ c₂ =>
      @OracleDynamicCircuit.qIf _ _ _ _ b inst
        (permOracleCirc n m perm c₁) (permOracleCirc n m perm c₂)
  | @OracleDynamicCircuit.qWhile _ _ _ _ b inst c =>
      @OracleDynamicCircuit.qWhile _ _ _ _ b inst (permOracleCirc n m perm c)
theorem zeroStepCost_permOracleCirc {Var : Type} {Q : ℕ} (n m : ℕ) (perm : Equiv.Perm (Fin (2 ^
    n))) {c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)} (hc : ZeroStepCost c) :
    ZeroStepCost (permOracleCirc n m perm c) := by
  induction c with
  | «skip» => trivial
  | «step» _ => exact hc
  | «oracle» reg =>
      exact ⟨zeroStepCost_step_phaseI (isRealMatrix_embedMatrix reg
        (isRealMatrix_parallelIdxUnitary perm.symm)), trivial, zeroStepCost_step_phaseI
        (isRealMatrix_embedMatrix reg (isRealMatrix_parallelIdxUnitary perm))⟩
  | «measure» _ _ => trivial
  | «seq» _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | «qIf» _ _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | «qWhile» _ _ ih => exact ih hc
theorem interp_permOracleCirc {Var : Type} [DecidableEq Var] {Q : ℕ} (n m : ℕ)
    (perm : Equiv.Perm (Fin (2 ^ n))) (A : Finset (Fin (2 ^ n)))
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) :
    interp ((permOracleCirc n m perm c).compile QProg.qAssign (parallelMarkingOracle m A)) =
      interp (c.compile QProg.qAssign (parallelMarkingOracle m (A.map perm.toEmbedding))) := by
  induction c with
  | «skip» => simp only [permOracleCirc, OracleDynamicCircuit.compile_skip]
  | «step» _ => simp only [permOracleCirc, OracleDynamicCircuit.compile_step]
  | «oracle» reg =>
      simp only [permOracleCirc, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step]
      rw [interp_qAssign_phaseI_seq_phaseI, ← reg.embedUnitary_mul, ← reg.embedUnitary_mul,
        parallelIdxUnitary_conj_parallelMarkingOracle]
  | «measure» _ _ => simp only [permOracleCirc, OracleDynamicCircuit.compile_measure]
  | «seq» _ _ ih₁ ih₂ =>
      simp only [permOracleCirc, OracleDynamicCircuit.compile_seq, interp_qSeq, ih₁, ih₂]
  | «qIf» _ _ _ ih₁ ih₂ =>
      simp only [permOracleCirc, OracleDynamicCircuit.compile_qIf, interp_qIf, ih₁, ih₂]
  | «qWhile» _ _ ih =>
      simp only [permOracleCirc, OracleDynamicCircuit.compile_qWhile, interp_qWhile, ih]
theorem expectedCost_permOracleCirc {Var : Type} [DecidableEq Var] {Q : ℕ} (n m : ℕ)
    (perm : Equiv.Perm (Fin (2 ^ n))) (A : Finset (Fin (2 ^ n)))
    {c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)} (hc : ZeroStepCost c) :
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A))
        ((permOracleCirc n m perm c).compile QProg.qAssign (parallelMarkingOracle m A)) =
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m (A.map perm.toEmbedding)))
        (c.compile QProg.qAssign (parallelMarkingOracle m (A.map perm.toEmbedding))) := by
  induction c with
  | «skip» => funext Δ; simp [permOracleCirc]
  | «step» _ =>
      funext Δ; simp only [permOracleCirc, OracleDynamicCircuit.compile_step, expectedCost_qAssign]
      rw [hc (isRealMatrix_parallelMarkingOracle A),
        hc (isRealMatrix_parallelMarkingOracle (A.map perm.toEmbedding))]
  | «oracle» reg =>
      funext Δ
      simp only [permOracleCirc, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step,
        expectedCost_qSeq, expectedCost_qAssign]
      have h0_pre : (CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m A)).unitaryCost
        (phaseI (reg.embedUnitary (parallelIdxUnitary m perm.symm))) = 0 :=
        ofEmbeddedOracle_unitaryCost_phaseI_eq_zero (isRealMatrix_parallelMarkingOracle A)
        (isRealMatrix_embedMatrix reg (isRealMatrix_parallelIdxUnitary perm.symm))
      have h0_post : (CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m A)).unitaryCost
        (phaseI (reg.embedUnitary (parallelIdxUnitary m perm))) = 0 :=
        ofEmbeddedOracle_unitaryCost_phaseI_eq_zero (isRealMatrix_parallelMarkingOracle A)
        (isRealMatrix_embedMatrix reg (isRealMatrix_parallelIdxUnitary perm))
      have h1 : (CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m A)).unitaryCost
          (reg.embedUnitary (parallelMarkingOracle m A)) = 1 :=
        CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary (parallelMarkingOracle m A) reg
      have h2 : (CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m (A.map
        perm.toEmbedding))).unitaryCost (reg.embedUnitary (parallelMarkingOracle m (A.map
        perm.toEmbedding))) = 1 := CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary
        (parallelMarkingOracle m (A.map perm.toEmbedding)) reg
      rw [h0_pre, h0_post, h1, h2]; simp
  | «measure» _ _ =>
      funext Δ
      simp only [permOracleCirc, OracleDynamicCircuit.compile_measure, QProg.measureRegister,
        expectedCost_qMeasure, CostModel.ofEmbeddedOracle]
  | «seq» c₁ _ ih₁ ih₂ =>
      funext Δ
      simp only [permOracleCirc, OracleDynamicCircuit.compile_seq, expectedCost_qSeq,
        ih₁ hc.1, ih₂ hc.2, interp_permOracleCirc n m perm A c₁]
  | «qIf» _ _ _ ih₁ ih₂ =>
      funext Δ
      simp only [permOracleCirc, OracleDynamicCircuit.compile_qIf, cqExpectedCostIf,
        ih₁ hc.1, ih₂ hc.2]
  | «qWhile» _ c ih =>
      funext Δ
      simp only [permOracleCirc, OracleDynamicCircuit.compile_qWhile, expectedCost_qWhile,
        ih hc, interp_permOracleCirc n m perm A c]
/-- Bijection splitting `Fin (2 ^ n)` (`s + d = n`) into low `s` intra-subcube bits and high
  `d`
  subcube-index bits. -/
def subcubeSplitEquiv {n : ℕ} (s d : ℕ) (hsd : s + d = n) :
    Fin (2 ^ n) ≃ Fin (2 ^ s) × Fin (2 ^ d) :=
  (finCongr (by rw [hsd])).trans (GroverSol.lowHighEquiv s d)
/-- The `2 ^ s`-element fiber of `Fin (2 ^ n)` lying in subcube `q: Fin (2 ^ d)`. -/
def subcubeFiber {n : ℕ} (s d : ℕ) (hsd : s + d = n) (q : Fin (2 ^ d)) :
    Finset (Fin (2 ^ n)) :=
  (Finset.univ : Finset (Fin (2 ^ s))).map
    ⟨fun a ↦ (subcubeSplitEquiv s d hsd).symm (a, q),
      fun _ _ h ↦ by simpa using congrArg Prod.fst ((subcubeSplitEquiv s d hsd).symm.injective h)⟩
theorem mem_subcubeFiber_iff {n s d : ℕ} (hsd : s + d = n) (q : Fin (2 ^ d)) (y : Fin (2 ^ n)) : y
    ∈ subcubeFiber s d hsd q ↔ (subcubeSplitEquiv s d hsd y).2 = q := by
  simp only [subcubeFiber, Finset.mem_map, Finset.mem_univ, true_and]; constructor
  · rintro ⟨a, rfl⟩
    change ((subcubeSplitEquiv s d hsd) ((subcubeSplitEquiv s d hsd).symm (a, q))).2 = q
    rw [Equiv.apply_symm_apply]
  · intro hq; refine ⟨(subcubeSplitEquiv s d hsd y).1, ?_⟩
    exact (subcubeSplitEquiv s d hsd).symm_apply_eq.mpr (Prod.ext rfl hq.symm)
theorem two_mul_choose_two_two_pow_all (s : ℕ) : 2 * (2 ^ s).choose 2 = 2 ^ s * (2 ^ s - 1) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · rw [Nat.choose_two_right, mul_comm]; apply Nat.div_mul_cancel
    have hpow : 2 ^ s = 2 * 2 ^ (s - 1) := by
      conv_lhs => rw [show s = 1 + (s - 1) by omega, pow_add, pow_one]
    rw [hpow, mul_assoc]; exact dvd_mul_right 2 _
/-- Unordered pairs in `Fin (2 ^ n)` sharing the same high-`d`-bit subcube index. -/
noncomputable def collidingPairs {n : ℕ} (s d : ℕ) (hsd : s + d = n) :
    Finset (Finset (Fin (2 ^ n))) :=
  (Finset.univ : Finset (Fin (2 ^ d))).biUnion
    (fun q ↦ (subcubeFiber s d hsd q).powersetCard 2)
theorem two_mul_card_collidingPairs {n s d : ℕ} (hsd : s + d = n) :
    2 * (collidingPairs s d hsd).card = 2 ^ n * (2 ^ s - 1) := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (2 ^ d))))
      (fun q ↦ (subcubeFiber s d hsd q).powersetCard 2) := by
    intro q₁ _ q₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro B hB1 hB2
    rw [Finset.mem_powersetCard] at hB1 hB2
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    have h1 := (mem_subcubeFiber_iff hsd q₁ y).mp (hB1.1 hy)
    have h2 := (mem_subcubeFiber_iff hsd q₂ y).mp (hB2.1 hy); exact hne (h1.symm.trans h2)
  rw [collidingPairs, Finset.card_biUnion hdisj]; have hcard_q (q : Fin (2 ^ d)) :
      ((subcubeFiber s d hsd q).powersetCard 2).card = (2 ^ s).choose 2 := by
    rw [Finset.card_powersetCard, subcubeFiber, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  simp_rw [hcard_q]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← mul_assoc, mul_comm 2
    (2 ^ d), mul_assoc, two_mul_choose_two_two_pow_all, ← mul_assoc, ← pow_add, add_comm d s, hsd]
/-- Predicate that a `2 * n`-bit seed `u` has `a_raw ≠ 0` and maps `R` injectively into the
  `2 ^ d`
  subcubes. -/
def IsCFSeed {n : ℕ} (hn : n ≠ 0) (s d : ℕ) (hsd : s + d = n)
    (R : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (2 * n))) : Prop :=
  ∃ ha : (GF2nForallA.seedToGFPair hn u).1 ≠ 0,
    Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2)
      ((R.map (GF2nForallA.finAffinePerm hn
        (Units.mk0 (GF2nForallA.seedToGFPair hn u).1 ha)
        (GF2nForallA.seedToGFPair hn u).2).toEmbedding : Finset (Fin (2 ^ n))) :
          Set (Fin (2 ^ n)))
theorem card_badSeeds_le_boole {n s d : ℕ} (hn : n ≠ 0) (hsd : s + d = n) {R : Finset (Fin (2 ^
    n))} (hr2 : 2 ≤ R.card) : open Classical in ((Finset.univ : Finset (Fin (2 ^ (2 * n)))).filter
    (fun u ↦ ¬ IsCFSeed hn s d hsd R u)).card ≤ 2 ^ n * R.card.choose 2 * 2 ^ s := by
  classical
  let zeroSeeds : Finset (Fin (2 ^ (2 * n))) := (Finset.univ : Finset (GaloisField 2 n)).image
    (fun b ↦ (GF2nForallA.seedToGFPair hn).symm (0, b))
  let unitToSeed : (GaloisField 2 n)ˣ × GaloisField 2 n → Fin (2 ^ (2 * n)) :=
    fun p ↦ (GF2nForallA.seedToGFPair hn).symm ((p.1 : GaloisField 2 n), p.2)
  have hunit_inj : Function.Injective unitToSeed := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    have hp := (GF2nForallA.seedToGFPair hn).symm.injective h
    injection hp with ha hb
    exact Prod.ext (Units.ext ha) hb
  let pairBad (P : Finset (Fin (2 ^ n))) : Finset (Fin (2 ^ (2 * n))) := (((Finset.univ : Finset
    ((GaloisField 2 n)ˣ × GaloisField 2 n)).filter (fun p ↦ P.map (GF2nForallA.finAffinePerm hn
    p.1 p.2).toEmbedding ∈ collidingPairs s d hsd)).image unitToSeed)
  have hsub : (Finset.univ : Finset (Fin (2 ^ (2 * n)))).filter (fun u ↦ ¬ IsCFSeed hn s d hsd R
    u) ⊆ zeroSeeds ∪ (R.powersetCard 2).biUnion pairBad := by
    intro u hu; rw [Finset.mem_filter] at hu
    have hnot : ¬ IsCFSeed hn s d hsd R u := hu.2; rw [Finset.mem_union]
    by_cases ha : (GF2nForallA.seedToGFPair hn u).1 = 0
    · left; rw [Finset.mem_image]; refine ⟨(GF2nForallA.seedToGFPair hn u).2, Finset.mem_univ _, ?_⟩
      exact (GF2nForallA.seedToGFPair hn).symm_apply_eq.mpr (Prod.ext ha.symm rfl)
    · right; let a_u : (GaloisField 2 n)ˣ := Units.mk0 (GF2nForallA.seedToGFPair hn u).1 ha
      let b_u : GaloisField 2 n := (GF2nForallA.seedToGFPair hn u).2
      let perm := GF2nForallA.finAffinePerm hn a_u b_u
      have hninj : ¬ Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2) ((R.map perm.toEmbedding
        : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))) := fun hinj ↦ hnot ⟨ha, hinj⟩
      rw [Set.InjOn] at hninj
      push Not at hninj
      obtain ⟨y₁, hy₁, y₂, hy₂, hq, hy_ne⟩ := hninj; rw [Finset.mem_coe, Finset.mem_map] at hy₁ hy₂
      obtain ⟨x₁, hx₁, hx₁_eq⟩ := hy₁; obtain ⟨x₂, hx₂, hx₂_eq⟩ := hy₂
      have hx_ne : x₁ ≠ x₂ := fun h ↦ hy_ne (hx₁_eq ▸ hx₂_eq ▸ congrArg _ h)
      let P : Finset (Fin (2 ^ n)) := {x₁, x₂}
      have hP_mem : P ∈ R.powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.insert_subset hx₁ (Finset.singleton_subset_iff.mpr hx₂),
          Finset.card_pair hx_ne⟩
      rw [Finset.mem_biUnion]; refine ⟨P, hP_mem, Finset.mem_image.mpr ⟨(a_u, b_u), ?_, ?_⟩⟩
      · rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        have hmapP : P.map perm.toEmbedding = {y₁, y₂} := by
          simp only [P, Finset.map_insert, Finset.map_singleton]; rw [hx₁_eq, hx₂_eq]
        rw [hmapP, collidingPairs, Finset.mem_biUnion]
        refine ⟨(subcubeSplitEquiv s d hsd y₁).2, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_powersetCard]; refine ⟨?_, Finset.card_pair hy_ne⟩
        refine Finset.insert_subset ((mem_subcubeFiber_iff hsd _ y₁).mpr rfl) ?_
        rw [Finset.singleton_subset_iff, mem_subcubeFiber_iff hsd]; exact hq.symm
      · exact (GF2nForallA.seedToGFPair hn).symm_apply_apply u
  have hzero_card : zeroSeeds.card ≤ 2 ^ n := by
    calc zeroSeeds.card ≤ (Finset.univ : Finset (GaloisField 2 n)).card := Finset.card_image_le
      _ = Fintype.card (GaloisField 2 n) := Finset.card_univ
      _ = Nat.card (GaloisField 2 n) := Nat.card_eq_fintype_card.symm
      _ = 2 ^ n := GaloisField.card 2 n hn
  have hpair_card (P : Finset (Fin (2 ^ n))) (hP : P ∈ R.powersetCard 2) :
      (pairBad P).card = 2 ^ n * (2 ^ s - 1) := by
    have hP2 : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
    let g : (GaloisField 2 n)ˣ × GaloisField 2 n → Finset (Fin (2 ^ n)) :=
      fun p ↦ P.map (GF2nForallA.finAffinePerm hn p.1 p.2).toEmbedding
    dsimp only [pairBad]; rw [Finset.card_image_of_injective _ hunit_inj]
    have hdecomp : (Finset.univ : Finset ((GaloisField 2 n)ˣ × GaloisField 2 n)).filter (fun p ↦ g
      p ∈ collidingPairs s d hsd) = (collidingPairs s d hsd).biUnion (fun B ↦ Finset.univ.filter
      (fun p ↦ g p = B)) := by
      ext p; simp [g]
    have hdisj : Set.PairwiseDisjoint (↑(collidingPairs s d hsd))
        (fun B ↦ Finset.univ.filter (fun p ↦ g p = B)) := by
      intro B₁ _ B₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro p hp₁ hp₂
      exact hne ((Finset.mem_filter.mp hp₁).2.symm.trans (Finset.mem_filter.mp hp₂).2)
    have hfib_card (B : Finset (Fin (2 ^ n))) (hB : B ∈ collidingPairs s d hsd) :
        (Finset.univ.filter (fun p ↦ g p = B)).card = 2 := by
      rw [collidingPairs, Finset.mem_biUnion] at hB; obtain ⟨q, _, hBq⟩ := hB
      exact GF2nForallA.card_fiber_finAffinePerm hn hP2 (Finset.mem_powersetCard.mp hBq).2
    rw [hdecomp, Finset.card_biUnion hdisj, Finset.sum_congr rfl hfib_card,
      Finset.sum_const, smul_eq_mul, mul_comm, two_mul_card_collidingPairs hsd]
  have hbi_card : ((R.powersetCard 2).biUnion pairBad).card ≤
      R.card.choose 2 * (2 ^ n * (2 ^ s - 1)) := by
    calc ((R.powersetCard 2).biUnion pairBad).card
        ≤ ∑ P ∈ R.powersetCard 2, (pairBad P).card := Finset.card_biUnion_le
      _ = ∑ _P ∈ R.powersetCard 2, (2 ^ n * (2 ^ s - 1)) := Finset.sum_congr rfl hpair_card
      _ = R.card.choose 2 * (2 ^ n * (2 ^ s - 1)) := by
          rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
  have hchoose_pos : 1 ≤ R.card.choose 2 := Nat.choose_pos hr2
  have hs_pos : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hs_sub : 1 + (2 ^ s - 1) = 2 ^ s := Nat.add_sub_of_le hs_pos
  calc ((Finset.univ : Finset (Fin (2 ^ (2 * n)))).filter
          (fun u ↦ ¬ IsCFSeed hn s d hsd R u)).card
      ≤ (zeroSeeds ∪ (R.powersetCard 2).biUnion pairBad).card := Finset.card_le_card hsub
    _ ≤ zeroSeeds.card + ((R.powersetCard 2).biUnion pairBad).card := Finset.card_union_le _ _
    _ ≤ 2 ^ n + R.card.choose 2 * (2 ^ n * (2 ^ s - 1)) := add_le_add hzero_card hbi_card
    _ ≤ R.card.choose 2 * 2 ^ n + R.card.choose 2 * 2 ^ n * (2 ^ s - 1) := by
        have h1 : 2 ^ n ≤ R.card.choose 2 * 2 ^ n := Nat.le_mul_of_pos_left (2 ^ n) hchoose_pos
        nlinarith
    _ = 2 ^ n * R.card.choose 2 * (1 + (2 ^ s - 1)) := by ring
    _ = 2 ^ n * R.card.choose 2 * 2 ^ s := by rw [hs_sub]
/-- Exact zero-slack Boole subcube collision + degenerate-seed fraction bound:
  at most `min 1 (r.choose 2 / 2 ^ d)` of the `2 ^ (2 * n)` seeds fail `IsCFSeed`. -/
theorem badSeeds_div_le_min_boole {n s d : ℕ} (hn : n ≠ 0) (hsd : s + d = n) {R : Finset (Fin (2 ^
    n))} (hr2 : 2 ≤ R.card) : open Classical in (((Finset.univ : Finset (Fin (2 ^ (2 *
    n)))).filter (fun u ↦ ¬ IsCFSeed hn s d hsd R u)).card : ℝ) / (2 ^ (2 * n) : ℝ) ≤ min 1
    ((R.card.choose 2 : ℝ) / (2 ^ d : ℝ)) := by
  classical
  set bad := (Finset.univ : Finset (Fin (2 ^ (2 * n)))).filter (fun u ↦ ¬ IsCFSeed hn s d hsd R u)
  refine le_min ?_ ?_
  · rw [div_le_one (by positivity)]
    have hle : bad.card ≤ 2 ^ (2 * n) := by
      calc bad.card ≤ (Finset.univ : Finset (Fin (2 ^ (2 * n)))).card := Finset.card_le_univ _
        _ = 2 ^ (2 * n) := by simp
    exact_mod_cast hle
  · have hboole := card_badSeeds_le_boole hn hsd hr2
    have hpow : (2 ^ (2 * n) : ℝ) = (2 ^ n : ℝ) * (2 ^ s : ℝ) * (2 ^ d : ℝ) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (bad.card : ℝ) * (2 ^ d : ℝ)
        ≤ ((2 ^ n * R.card.choose 2 * 2 ^ s : ℕ) : ℝ) * (2 ^ d : ℝ) := by gcongr
      _ = (R.card.choose 2 : ℝ) * (2 ^ (2 * n) : ℝ) := by rw [hpow]; push_cast; ring
/- ## 3. Clean-State Embedded Measurement & Uniform `2 * n`-Bit Seed Sampling -/
theorem trueState_trace_eq_expect_liftPureProp {Var : Type} {d : ℕ} (B : Store Var → Prop)
    [DecidablePred B] (Γ : CQState (Store Var) d) :
    ((Γ.cqTrueSt B).trace : ℝ) = 𝔼[Γ, liftPureProp B] := by
  rw [qcTraceEqTsumStore, qcExpectEqTsumStore]; refine tsum_congr fun σ ↦ ?_
  by_cases hB : B σ
  · simp [CQState.cqTrueSt_coe, liftPureProp_apply, hB, HermitianMat.one_inner]
  · simp [CQState.cqTrueSt_coe, liftPureProp_apply, hB]
theorem expect_of_supportedOn_zero {Var : Type} {d : ℕ} [NeZero d] {Δ : CQState (Store Var) d} (hΔ :
    SupportedOn (· = (0 : Fin d)) Δ) {Θ : CQAssertion (Store Var) d} {c : ℝ} (hΘ : ∀ σ, (Θ σ).1.mat
      0 0 =
    (c : ℂ)) : 𝔼[Δ, Θ] = c * Δ.trace := by
  refine expect_of_supportedOn hΔ fun σ ↦ ?_
  ext a b; rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]; by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    simp only [and_self, ↓reduceIte, diagProj, Matrix.diagonal_apply, smul_eq_mul, mul_one]
    exact hΘ σ
  · simp only [hab, ↓reduceIte]; by_cases heq : a = b
    · subst heq; have hne : a ≠ 0 := fun h ↦ hab ⟨h, h⟩; simp [diagProj, hne]
    · simp [diagProj, heq]
theorem eq_replaceIndex_zero_iff {W Q : ℕ} (r : QRegister W Q) (o : Fin (2 ^ W)) (z : Fin (2 ^ Q))
    : (r.extractIndex z = o ∧ r.AgreeOutside z 0) ↔ z = r.replaceIndex 0 o := by
  constructor
  · rintro ⟨hex, hag⟩
    apply (basisBits Q).injective; funext w; by_cases hw : w ∈ Set.range r
    · obtain ⟨i, rfl⟩ := hw; rw [← r.basisBits_extractIndex, hex, r.basisBits_replaceIndex_apply]
    · rw [hag w hw, r.basisBits_replaceIndex_of_not_mem 0 o w hw]
  · rintro rfl
    refine ⟨r.extractIndex_replaceIndex 0 o, fun w hw ↦ ?_⟩
    exact r.basisBits_replaceIndex_of_not_mem 0 o w hw
/-- General `sliceState` Born-rule trace identity after applying `r.embedUnitary U` to a `|0
  ^ Q⟩`
  state and measuring `r` into `res`. -/
theorem embedUnitary_measure_sliceState_trace {Var : Type} [DecidableEq Var] {W Q : ℕ} (res : Var)
    (r : QRegister W Q) (U : Unitary (2 ^ W)) {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (·
      = (0
    : Fin (2 ^ Q))) Δ) {v : ℕ} (hv : v < 2 ^ W) :
    let o : Fin (2 ^ W) := ⟨v, hv⟩
    let prog : QProg Var (2 ^ Q) :=
      QProg.qAssign (r.embedUnitary U) ;; QProg.measureRegister res r
    ((sliceState res 0 W v ((interp prog).toStateFun Δ)).trace : ℝ) =
      Complex.normSq ((U.1 *ᵥ Pi.single 0 1) o) * Δ.trace := by
  intro o prog; let B : Store Var → Prop := fun σ ↦ ((σ res).toNat / 2 ^ 0) % 2 ^ W = v
  change ((((interp prog).toStateFun Δ).cqTrueSt B).trace : ℝ) = _
  rw [trueState_trace_eq_expect_liftPureProp, ← wp_expectation_eq]
  refine expect_of_supportedOn_zero hΔ fun σ ↦ ?_
  have hmeas_mat : (wp (QProg.measureRegister res r) (liftPureProp B) σ).1.mat = diagProj (fun z :
    Fin (2 ^ Q) ↦ r.extractIndex z = o) := by
    rw [QProg.measureRegister, wp_qMeasure]
    change (∑ o' : Fin (2 ^ W), HermitianMat.conj (r.basisOutcomeProjector o')ᴴ (liftPureProp B
      (Store.subst σ res ↑o'.val)).1).mat = diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = o)
    rw [HermitianMat.mat_finset_sum, Finset.sum_eq_single o]
    · have hBo : B (Store.subst σ res ↑o.val) := (by simp [B, o, Store.subst, Nat.mod_eq_of_lt hv])
      have htop :
          (liftPureProp (Var := Var) (d := 2 ^ Q) B (Store.subst σ res ↑o.val)).1 = 1 := by
        open Classical in
        rw [liftPureProp_apply, ite_eq_left hBo]; rfl
      rw [htop, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
        r.basisOutcomeProjector_conjTranspose, HermitianMat.mat_one, Matrix.mul_one,
        basisOutcomeProjector_eq_diagProj, diagProj_mul_self]
    · intro o' _ hne
      have hBo' : ¬ B (Store.subst σ res ↑o'.val) := by
        have hval : ((Store.subst σ res ↑o'.val res).toNat / 2 ^ 0) % 2 ^ W = o'.val := by
          simp [Store.subst, Nat.mod_eq_of_lt o'.isLt]
        intro hB; have heq : o'.val = o.val := hval.symm.trans hB; exact hne (Fin.ext heq)
      have hbot :
          (liftPureProp (Var := Var) (d := 2 ^ Q) B (Store.subst σ res ↑o'.val)).1 = 0 := by
        open Classical in
        rw [liftPureProp_apply, ite_eq_right hBo']; rfl
      rw [hbot]; simp
    · intro habs; exact (habs (Finset.mem_univ o)).elim
  set E := r.embedMatrix U.1; set P := diagProj (fun z : Fin (2 ^ Q) ↦ r.extractIndex z = o)
  have hwp_mat : (wp prog (liftPureProp B) σ).1.mat = Eᴴ * P * E := by
    dsimp only [prog, E, P]
    rw [wp_qSeq, wp_qAssign, ← HermitianMat.val_eq_coe, qhlQAssign_val,
      HermitianMat.val_eq_coe, QRegister.embedUnitary_val, hmeas_mat]
  rw [hwp_mat]; rw [Matrix.mul_apply, Finset.sum_eq_single (r.replaceIndex 0 o)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (r.replaceIndex 0 o)]
    · have hex : r.extractIndex (r.replaceIndex 0 o) = o := r.extractIndex_replaceIndex 0 o
      have hag : r.AgreeOutside (r.replaceIndex 0 o) 0 :=
        ((eq_replaceIndex_zero_iff r o (r.replaceIndex 0 o)).mpr rfl).2
      have hE0 : E (r.replaceIndex 0 o) 0 = (U.1 *ᵥ Pi.single 0 1) o := by
        dsimp only [E]
        rw [QRegister.embedMatrix_apply_of_agreeOutside, ite_eq_left hag, mul_one, hex,
          extractIndex_zero_reg, Matrix.mulVec_single_one, Matrix.col_apply]
      have hP0 : P (r.replaceIndex 0 o) (r.replaceIndex 0 o) = 1 := (by simp [P, diagProj, hex])
      rw [Matrix.conjTranspose_apply, hE0, hP0, mul_one, Complex.star_def, Complex.conj_mul',
        ← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
    · intro x _ hne; simp [P, diagProj, hne]
    · intro habs; exact (habs (Finset.mem_univ _)).elim
  · intro z _ hne; rw [Matrix.mul_apply, Finset.sum_eq_single z]
    · by_cases hex : r.extractIndex z = o
      · have hnag : ¬ r.AgreeOutside z 0 := fun hag ↦
          hne ((eq_replaceIndex_zero_iff r o z).mp ⟨hex, hag⟩)
        have hEz : E z 0 = 0 := by
          have hneq_env : (r.basisSplitEquiv z).2 ≠ (r.basisSplitEquiv 0).2 :=
            fun heq ↦ hnag fun w hw ↦ congrFun heq ⟨w, hw⟩
          dsimp only [E]; rw [QRegister.embedMatrix_apply]
          simp only [hneq_env, ↓reduceIte, mul_zero]
        rw [hEz, mul_zero]
      · have hPz : P z z = 0 := (by simp [P, diagProj, hex]); rw [hPz, mul_zero, zero_mul]
    · intro x _ hxz; simp [P, diagProj, hxz]
    · intro habs; exact (habs (Finset.mem_univ z)).elim
  · intro habs; exact (habs (Finset.mem_univ _)).elim
/-- Sample a uniform `2 * n`-bit seed in `QRegister.block 0 (2 * n)` (`0` oracle queries). -/
noncomputable def sampleSeedCircuit {Var : Type} (res : Var) (n Q w : ℕ) (hseed : 2 * n ≤ Q) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w :=
  let r : QRegister (2 * n) Q := QRegister.block 0 (2 * n) (by omega)
  .seq (.step (phaseI (r.embedUnitary (hadamardUnitary (q := 2 * n))))) (.measure res r)
theorem zeroStepCost_sampleSeedCircuit {Var : Type} (res : Var) (n Q w : ℕ) (hseed : 2 * n ≤ Q) :
    ZeroStepCost (sampleSeedCircuit (Var := Var) res n Q w hseed) := by
  dsimp only [sampleSeedCircuit]
  exact ⟨zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _
    (by rw [hadamardUnitary_coe]; exact isRealMatrix_hadamardMatrix (2 * n))),
    trivial⟩
theorem expectedCost_sampleSeedCircuit {Var : Type} [DecidableEq Var] (res : Var) (n Q w : ℕ)
    (hseed : 2 * n ≤ Q) {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1) (Δ : CQState
    (Store Var) (2 ^ Q)) : expectedCost (CostModel.ofEmbeddedOracle oracle) ((sampleSeedCircuit res
      n Q w
    hseed).compile QProg.qAssign oracle) Δ = 0 := by
  have hc0 := (zeroStepCost_sampleSeedCircuit (Var := Var) res n Q w hseed).1 horacle
  dsimp only [sampleSeedCircuit]
  simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
    OracleDynamicCircuit.compile_measure, QProg.measureRegister, expectedCost_qSeq,
    expectedCost_qAssign, expectedCost_qMeasure]
  rw [hc0]; simp [CostModel.ofEmbeddedOracle]
theorem sampleSeed_sliceState_trace {Var : Type} [DecidableEq Var] (res : Var) (n Q w : ℕ) (hseed
    : 2 * n ≤ Q) (oracle : Unitary (2 ^ w)) {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· =
      (0 :
    Fin (2 ^ Q))) Δ) {uVal : ℕ} (hu : uVal < 2 ^ (2 * n)) : ((sliceState res 0 (2 * n) uVal
    ((interp ((sampleSeedCircuit res n Q w hseed).compile QProg.qAssign oracle)).toStateFun
    Δ)).trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Δ.trace := by
  let r : QRegister (2 * n) Q := QRegister.block 0 (2 * n) (by omega)
  have hinterp : ((interp ((sampleSeedCircuit res n Q w hseed).compile QProg.qAssign
    oracle)).toStateFun Δ) = ((interp (QProg.qAssign (r.embedUnitary (hadamardUnitary (q := 2 *
    n))) ;; QProg.measureRegister res r)).toStateFun Δ) := by
    dsimp only [sampleSeedCircuit, OracleDynamicCircuit.compile, r]
    simp only [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qAssign,
      QMonad.Q.toStateFun_qAssign, cqState_qAssign_phaseI]
  rw [hinterp, embedUnitary_measure_sliceState_trace res r (hadamardUnitary (q := 2 * n)) hΔ hu]
  congr 1
  rw [hadamardUnitary_coe, Matrix.mulVec_single_one, Matrix.col_apply, hadamardMatrix_apply_zero,
    ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.normSq_ofReal]
  have hsq : √(2 ^ (2 * n) : ℝ) * √(2 ^ (2 * n) : ℝ) = (2 ^ (2 * n) : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  calc (1 / √(2 ^ (2 * n) : ℝ)) * (1 / √(2 ^ (2 * n) : ℝ))
      = 1 / (√(2 ^ (2 * n) : ℝ) * √(2 ^ (2 * n) : ℝ)) := by ring
    _ = 1 / (2 ^ (2 * n) : ℝ) := by rw [hsq]
/- ## 4. Subcube Parallel Grover Pass (`subcubePassCircuit`) & CF Binomial Expectation -/
/-- Low `(s + 1)` wires (marker wire `0` + low `s` intra-subcube address wires) inside an
  `(n + 1)`-qubit slot (`s + d = n`). -/
def lowSubSlotReg {n : ℕ} (s d : ℕ) (hsd : s + d = n) : QRegister (s + 1) (n + 1) :=
  QRegister.block 0 (s + 1) (by omega)
/-- High `d` subcube-index wires `s + 1.. s + d` inside an `(n + 1)`-qubit slot (`s + d =
  n`). -/
def highSubIdxReg {n : ℕ} (s d : ℕ) (hsd : s + d = n) : QRegister d (n + 1) :=
  QRegister.block (s + 1) d (by omega)
/-- Bijection `Fin (2 ^ (n + 1)) ≃ Fin (2 ^ (s + 1)) × Fin (2 ^ d)` matching `lowSubSlotReg`
  and
  `highSubIdxReg`. -/
def subSlotSplitEquiv {n : ℕ} (s d : ℕ) (hsd : s + d = n) :
    Fin (2 ^ (n + 1)) ≃ Fin (2 ^ (s + 1)) × Fin (2 ^ d) :=
  (finCongr (congrArg (2 ^ ·) (by omega : n + 1 = (s + 1) + d))).trans
    (GroverSol.lowHighEquiv (s + 1) d)
theorem extractIndex_lowSubSlotReg {n s d : ℕ} (hsd : s + d = n) (u : Fin (2 ^ (n + 1))) :
    (lowSubSlotReg s d hsd).extractIndex u = (subSlotSplitEquiv s d hsd u).1 := by
  apply (basisBits (s + 1)).injective; funext i
  rw [(lowSubSlotReg s d hsd).basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit]
  have hi : (lowSubSlotReg s d hsd i).val = i.val := (by simp [lowSubSlotReg])
  have hfst := GroverSol.lowHighEquiv_fst_val (s + 1) d
    (finCongr (congrArg (2 ^ ·) (by omega : n + 1 = (s + 1) + d)) u)
  rw [show (subSlotSplitEquiv s d hsd u).1.val = u.val % 2 ^ (s + 1) from hfst, hi,
    Nat.testBit_mod_two_pow]; simp [i.isLt]
theorem extractIndex_highSubIdxReg {n s d : ℕ} (hsd : s + d = n) (u : Fin (2 ^ (n + 1))) :
    (highSubIdxReg s d hsd).extractIndex u = (subSlotSplitEquiv s d hsd u).2 := by
  apply (basisBits d).injective; funext i
  rw [(highSubIdxReg s d hsd).basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit]
  have hi : (highSubIdxReg s d hsd i).val = i.val + (s + 1) := by
    simp only [highSubIdxReg, QRegister.block_apply_val]; omega
  have hsnd := GroverSol.lowHighEquiv_snd_val (s + 1) d
    (finCongr (congrArg (2 ^ ·) (by omega : n + 1 = (s + 1) + d)) u)
  rw [show (subSlotSplitEquiv s d hsd u).2.val = u.val / 2 ^ (s + 1) from hsnd, hi,
    Nat.testBit_div_two_pow]
theorem extractIndex_localMarkerReg_subSlot {n s d : ℕ} (hsd : s + d = n) (u : Fin (2 ^ (n + 1)))
    : (localMarkerReg n).extractIndex u = (localMarkerReg s).extractIndex ((lowSubSlotReg s d
    hsd).extractIndex u) := by
  apply (basisBits 1).injective; funext i
  rw [(localMarkerReg n).basisBits_extractIndex, (localMarkerReg s).basisBits_extractIndex,
    (lowSubSlotReg s d hsd).basisBits_extractIndex]
  have hw : (localMarkerReg n) i = (lowSubSlotReg s d hsd) ((localMarkerReg s) i) :=
    Fin.ext (by simp [localMarkerReg, lowSubSlotReg])
  rw [hw]
theorem subcubeSplitEquiv_localIdxReg {n s d : ℕ} (hsd : s + d = n) (u : Fin (2 ^ (n + 1))) :
    subcubeSplitEquiv s d hsd ((localIdxReg n).extractIndex u) = ((localIdxReg s).extractIndex
    ((lowSubSlotReg s d hsd).extractIndex u), (highSubIdxReg s d hsd).extractIndex u) := by
  let hpow : 2 ^ n = 2 ^ (s + d) := congrArg (2 ^ ·) hsd.symm; ext : 1
  · change (GroverSol.lowHighEquiv s d (finCongr hpow ((localIdxReg n).extractIndex u))).1 = _
    rw [← GroverSol.extractIndex_lowBlock s d]; apply (basisBits s).injective; funext j
    rw [(GroverSol.lowBlock s d).basisBits_extractIndex,
      (localIdxReg s).basisBits_extractIndex, (lowSubSlotReg s d hsd).basisBits_extractIndex]
    have h1 : basisBits (s + d) (finCongr hpow ((localIdxReg n).extractIndex u))
        (GroverSol.lowBlock s d j) =
        basisBits n ((localIdxReg n).extractIndex u) ⟨j.val, by omega⟩ := by
      have hbit : ((finCongr hpow ((localIdxReg n).extractIndex u)).val).testBit
          (GroverSol.lowBlock s d j).val =
          ((localIdxReg n).extractIndex u).val.testBit j.val := by
        simp only [finCongr_apply, Fin.val_cast, GroverSol.lowBlock,
          QRegister.block_apply_val, zero_add]
      rw [basisBits_eq_testBit, basisBits_eq_testBit]
      exact congrArg (fun b ↦ if b = true then 1 else 0) hbit
    rw [h1, (localIdxReg n).basisBits_extractIndex]
    have hw : (localIdxReg n) ⟨j.val, by omega⟩ = (lowSubSlotReg s d hsd) ((localIdxReg s) j) :=
      Fin.ext (by simp [localIdxReg, lowSubSlotReg])
    rw [hw]
  · change (GroverSol.lowHighEquiv s d (finCongr hpow ((localIdxReg n).extractIndex u))).2 = _
    rw [← GroverSol.extractIndex_highBlock s d]; apply (basisBits d).injective; funext j
    rw [(GroverSol.highBlock s d).basisBits_extractIndex,
      (highSubIdxReg s d hsd).basisBits_extractIndex]
    have h1 : basisBits (s + d) (finCongr hpow ((localIdxReg n).extractIndex u))
        (GroverSol.highBlock s d j) =
        basisBits n ((localIdxReg n).extractIndex u) ⟨j.val + s, by omega⟩ := by
      have hq : (GroverSol.highBlock s d j).val = j.val + s := by
        simp only [GroverSol.highBlock, QRegister.block_apply_val]; omega
      have hbit : ((finCongr hpow ((localIdxReg n).extractIndex u)).val).testBit
          (GroverSol.highBlock s d j).val =
          ((localIdxReg n).extractIndex u).val.testBit (j.val + s) := by
        simp only [finCongr_apply, Fin.val_cast, hq]
      rw [basisBits_eq_testBit, basisBits_eq_testBit]
      exact congrArg (fun b ↦ if b = true then 1 else 0) hbit
    rw [h1, (localIdxReg n).basisBits_extractIndex]
    have hw : (localIdxReg n) ⟨j.val + s, by omega⟩ = (highSubIdxReg s d hsd) j := by
      apply Fin.ext; simp only [localIdxReg, highSubIdxReg, QRegister.block_apply_val]; omega
    rw [hw]
theorem disjoint_lowSubSlotReg_highSubIdxReg {n s d : ℕ} (hsd : s + d = n) :
    (lowSubSlotReg s d hsd).DisjointWires (highSubIdxReg s d hsd) := by
  rw [QRegister.disjoint_iff]; intro i j hij; have hv := congrArg Fin.val hij
  simp only [lowSubSlotReg, highSubIdxReg, QRegister.block_apply_val] at hv; omega
/-- Slice `{a: Fin (2 ^ s) | (a, q) ∈ B}` of `B ⊆ Fin (2 ^ n)` inside subcube `q: Fin (2 ^
  d)`. -/
def subcubeSlice {n : ℕ} (s d : ℕ) (hsd : s + d = n)
    (B : Finset (Fin (2 ^ n))) (q : Fin (2 ^ d)) : Finset (Fin (2 ^ s)) :=
  (Finset.univ : Finset (Fin (2 ^ s))).filter fun a ↦ (subcubeSplitEquiv s d hsd).symm (a, q) ∈ B
/-- Single-slot vector with `(s + 1)`-qubit state `ψ` on `lowSubSlotReg` and computational
  basis
  `|q⟩` on `highSubIdxReg`. -/
def subSlotPairVec {n : ℕ} (s d : ℕ) (hsd : s + d = n)
    (ψ : Fin (2 ^ (s + 1)) → ℂ) (q : Fin (2 ^ d)) (u : Fin (2 ^ (n + 1))) : ℂ :=
  if (highSubIdxReg s d hsd).extractIndex u = q then
    ψ ((lowSubSlotReg s d hsd).extractIndex u)
  else
    0
theorem subSlotInit_mulVec_zero {n s d : ℕ} (hsd : s + d = n) (q : Fin (2 ^ d)) : ((highSubIdxReg
    s d hsd).embedMatrix (permutationUnitary (Equiv.swap 0 q)).1 *ᵥ Pi.single (0 : Fin (2 ^ (n +
    1))) (1 : ℂ)) = subSlotPairVec s d hsd (Pi.single 0 1) q := by
  funext u; rw [(highSubIdxReg s d hsd).embedMatrix_mulVec_apply]
  change (∑ b : Fin (2 ^ d), (permutationUnitary (Equiv.swap 0 q)).1 ((highSubIdxReg s d
    hsd).extractIndex u) b * (Pi.single (0 : Fin (2 ^ (n + 1))) (1 : ℂ) : Fin (2 ^ (n + 1)) → ℂ)
    ((highSubIdxReg s d hsd).replaceIndex u b)) = _
  rw [Finset.sum_eq_single 0]
  · have hperm0 : (permutationUnitary (Equiv.swap 0 q)).1 ((highSubIdxReg s d hsd).extractIndex u)
      0 = if (highSubIdxReg s d hsd).extractIndex u = q then 1 else 0 := by
      rw [GroverSol.permutationUnitary_apply, Equiv.swap_apply_left]
    rw [hperm0]; by_cases hq : (highSubIdxReg s d hsd).extractIndex u = q
    · rw [ite_eq_left hq, one_mul, subSlotPairVec, ite_eq_left hq]
      by_cases hlow : (lowSubSlotReg s d hsd).extractIndex u = 0
      · have hrep0 : (highSubIdxReg s d hsd).replaceIndex u 0 = 0 := by
          apply (subSlotSplitEquiv s d hsd).injective; ext : 1
          · rw [← extractIndex_lowSubSlotReg hsd, ← extractIndex_lowSubSlotReg hsd, (lowSubSlotReg
              s d hsd).extractIndex_replaceIndex_of_disjoint (highSubIdxReg s d hsd)
              (disjoint_lowSubSlotReg_highSubIdxReg hsd), hlow, extractIndex_zero_reg]
          · rw [← extractIndex_highSubIdxReg hsd, ← extractIndex_highSubIdxReg hsd,
              QRegister.extractIndex_replaceIndex, extractIndex_zero_reg]
        rw [hrep0, hlow, Pi.single_eq_same, Pi.single_eq_same]
      · have hrep_ne : (highSubIdxReg s d hsd).replaceIndex u 0 ≠ 0 := by
          intro h0; apply hlow; have h1 := congrArg (lowSubSlotReg s d hsd).extractIndex h0
          rw [(lowSubSlotReg s d hsd).extractIndex_replaceIndex_of_disjoint (highSubIdxReg s d
            hsd) (disjoint_lowSubSlotReg_highSubIdxReg hsd), extractIndex_zero_reg] at h1; exact h1
        rw [Pi.single_eq_of_ne hrep_ne, Pi.single_eq_of_ne hlow]
    · rw [ite_eq_right hq, zero_mul, subSlotPairVec, ite_eq_right hq]
  · intro b _ hb
    have hrep_ne : (highSubIdxReg s d hsd).replaceIndex u b ≠ 0 := by
      intro h0; apply hb; have h1 := congrArg (highSubIdxReg s d hsd).extractIndex h0
      rw [QRegister.extractIndex_replaceIndex, extractIndex_zero_reg] at h1; exact h1
    rw [Pi.single_eq_of_ne hrep_ne, mul_zero]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim
theorem lowSubSlotEmbed_mulVec_subSlotPairVec {n s d : ℕ} (hsd : s + d = n) (M : Matrix (Fin (2 ^
    (s + 1))) (Fin (2 ^ (s + 1))) ℂ) (ψ : Fin (2 ^ (s + 1)) → ℂ) (q : Fin (2 ^ d)) :
    (lowSubSlotReg s d hsd).embedMatrix M *ᵥ subSlotPairVec s d hsd ψ q = subSlotPairVec s d hsd
    (M *ᵥ ψ) q := by
  funext u; rw [(lowSubSlotReg s d hsd).embedMatrix_mulVec_apply]
  change (∑ v : Fin (2 ^ (s + 1)), M ((lowSubSlotReg s d hsd).extractIndex u) v *
        subSlotPairVec s d hsd ψ q ((lowSubSlotReg s d hsd).replaceIndex u v)) = _
  have hhigh (v : Fin (2 ^ (s + 1))) : (highSubIdxReg s d hsd).extractIndex ((lowSubSlotReg s d
    hsd).replaceIndex u v) = (highSubIdxReg s d hsd).extractIndex u := (highSubIdxReg s d
    hsd).extractIndex_replaceIndex_of_disjoint (lowSubSlotReg s d hsd) (QRegister.disjoint_comm.mp
    (disjoint_lowSubSlotReg_highSubIdxReg hsd)) u v
  by_cases hq : (highSubIdxReg s d hsd).extractIndex u = q
  · simp only [subSlotPairVec, hhigh, hq, ↓reduceIte, QRegister.extractIndex_replaceIndex]; rfl
  · simp only [subSlotPairVec, hhigh, hq, ↓reduceIte, mul_zero, Finset.sum_const_zero]
theorem setMarkingOracle_mulVec_subSlotPairVec {n s d : ℕ} (hsd : s + d = n)
    (B : Finset (Fin (2 ^ n))) (ψ : Fin (2 ^ (s + 1)) → ℂ) (q : Fin (2 ^ d)) :
    (setMarkingOracle B).1 *ᵥ subSlotPairVec s d hsd ψ q =
      subSlotPairVec s d hsd ((setMarkingOracle (subcubeSlice s d hsd B q)).1 *ᵥ ψ) q := by
  have hfst_s (v : Fin (2 ^ (s + 1))) :
      (splitBasisEquiv s 1 v).1 = (localIdxReg s).extractIndex v := by
    obtain ⟨⟨x, y⟩, rfl⟩ := (splitBasisEquiv s 1).symm.surjective v
    rw [Equiv.apply_symm_apply, extractIndex_localIdxReg_splitSymm]
  have hsnd_s (v : Fin (2 ^ (s + 1))) :
      (splitBasisEquiv s 1 v).2 = (localMarkerReg s).extractIndex v := by
    obtain ⟨⟨x, y⟩, rfl⟩ := (splitBasisEquiv s 1).symm.surjective v
    rw [Equiv.apply_symm_apply, extractIndex_localMarkerReg_splitSymm]
  funext u
  rw [setMarkingOracle_mulVec_apply]; have hidx := extractIndex_localIdxReg_slotMarkPerm B u
  have hmk := extractIndex_localMarkerReg_slotMarkPerm B u
  have hsplit_u := subcubeSplitEquiv_localIdxReg hsd u
  have hsplit_m := subcubeSplitEquiv_localIdxReg hsd (slotMarkPerm B u)
  rw [hidx, hsplit_u] at hsplit_m
  have hhigh_eq : (highSubIdxReg s d hsd).extractIndex (slotMarkPerm B u) =
      (highSubIdxReg s d hsd).extractIndex u := (congrArg Prod.snd hsplit_m).symm
  by_cases hq : (highSubIdxReg s d hsd).extractIndex u = q
  · rw [subSlotPairVec, hhigh_eq, ite_eq_left hq, subSlotPairVec, ite_eq_left hq,
      setMarkingOracle_mulVec_apply]
    congr 1
    obtain ⟨⟨a, b⟩, hlow_eq⟩ :=
      (splitBasisEquiv s 1).symm.surjective ((lowSubSlotReg s d hsd).extractIndex u)
    have hmem_iff : (localIdxReg n).extractIndex u ∈ B ↔ a ∈ subcubeSlice s d hsd B q := by
      have hloc_u : (localIdxReg n).extractIndex u = (subcubeSplitEquiv s d hsd).symm (a, q) := by
        apply (subcubeSplitEquiv s d hsd).injective
        rw [hsplit_u, ← hlow_eq, extractIndex_localIdxReg_splitSymm, hq, Equiv.apply_symm_apply]
      rw [hloc_u]; simp [subcubeSlice]
    apply (splitBasisEquiv s 1).injective; apply Prod.ext
    · have hfst_m : (localIdxReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex
        (slotMarkPerm B u)) = (localIdxReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex
        u) := (congrArg Prod.fst hsplit_m).symm
      rw [hfst_s, hfst_s, hfst_m, ← hlow_eq, extractIndex_localIdxReg_slotMarkPerm]
    · rw [hsnd_s, hsnd_s, ← extractIndex_localMarkerReg_subSlot hsd, hmk,
        extractIndex_localMarkerReg_subSlot hsd, ← hlow_eq,
        extractIndex_localMarkerReg_slotMarkPerm,
        extractIndex_localMarkerReg_splitSymm, extractIndex_localIdxReg_splitSymm]
      by_cases ha : a ∈ subcubeSlice s d hsd B q
      · simp [ha, hmem_iff.mpr ha]
      · have hnb : (localIdxReg n).extractIndex u ∉ B := fun hb ↦ ha (hmem_iff.mp hb)
        simp [ha, hnb]
  · rw [subSlotPairVec, hhigh_eq, ite_eq_right hq, subSlotPairVec, ite_eq_right hq]
/-- Per-slot subcube combined unitary on `Fin (2 ^ (n + 1))` for subcube `q: Fin (2 ^ d)`. -/
noncomputable def subSlotFinalUnitary {n : ℕ} (s d : ℕ) (hsd : s + d = n)
    (B : Finset (Fin (2 ^ n))) (q : Fin (2 ^ d)) (K : ℕ) : Unitary (2 ^ (n + 1)) :=
  setMarkingOracle B *
    (lowSubSlotReg s d hsd).embedUnitary (slotUnprepLocal s) *
    ((lowSubSlotReg s d hsd).embedUnitary (slotDiffuserLocal s) * setMarkingOracle B) ^ K *
    ((lowSubSlotReg s d hsd).embedUnitary (slotPrepLocal s) *
      (highSubIdxReg s d hsd).embedUnitary (permutationUnitary (Equiv.swap 0 q)))
theorem subSlotFinalUnitary_mulVec_zero {n s d : ℕ} (hsd : s + d = n) (B : Finset (Fin (2 ^ n)))
    (q : Fin (2 ^ d)) (K : ℕ) : (subSlotFinalUnitary s d hsd B q K).1 *ᵥ Pi.single (0 : Fin (2 ^
    (n + 1))) (1 : ℂ) = subSlotPairVec s d hsd (slotFinalVec (subcubeSlice s d hsd B q) K) q := by
  let A_q := subcubeSlice s d hsd B q
  have hstep (t : ℕ) (ψ : Fin (2 ^ (s + 1)) → ℂ) : ((((lowSubSlotReg s d hsd).embedUnitary
    (slotDiffuserLocal s) * setMarkingOracle B) ^ t).1 *ᵥ subSlotPairVec s d hsd ψ q) =
    subSlotPairVec s d hsd (((slotDiffuserLocal s * setMarkingOracle A_q) ^ t).1 *ᵥ ψ) q := by
    induction t with
    | zero => simp
    | succ t ih =>
        rw [pow_succ' ((lowSubSlotReg s d hsd).embedUnitary (slotDiffuserLocal s) *
          setMarkingOracle B) t, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih, Submonoid.coe_mul,
          ← Matrix.mulVec_mulVec, setMarkingOracle_mulVec_subSlotPairVec,
          QRegister.embedUnitary_val, lowSubSlotEmbed_mulVec_subSlotPairVec, pow_succ'
          (slotDiffuserLocal s * setMarkingOracle A_q) t, Submonoid.coe_mul, ←
          Matrix.mulVec_mulVec, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  simp only [subSlotFinalUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    QRegister.embedUnitary_val]
  rw [subSlotInit_mulVec_zero hsd q, lowSubSlotEmbed_mulVec_subSlotPairVec, hstep K,
    lowSubSlotEmbed_mulVec_subSlotPairVec, setMarkingOracle_mulVec_subSlotPairVec]
  congr 2; dsimp only [A_q]
  rw [← slotFinalUnitary_mulVec_zero (subcubeSlice s d hsd B q) K, slotFinalUnitary]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
/-- Apply a slot-dependent `(n + 1)`-qubit unitary `U i` independently across all `m` slots. -/
noncomputable def parallelSlotHetero {n m : ℕ} (U : Fin m → Unitary (2 ^ (n + 1))) :
    Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦ (localSlotReg n m i).embedUnitary (U i)).prod
theorem isRealMatrix_parallelSlotHetero {n m : ℕ} {U : Fin m → Unitary (2 ^ (n + 1))}
    (hU : ∀ i : Fin m, IsRealMatrix (U i).1) : IsRealMatrix (parallelSlotHetero U).1 := by
  refine isRealMatrix_listProd _ fun V hV ↦ ?_
  rw [List.mem_ofFn] at hV; obtain ⟨i, rfl⟩ := hV; exact isRealMatrix_embedMatrix _ (hU i)
theorem slotHetero_comm_listProd {n m : ℕ} (U : Fin m → Unitary (2 ^ (n + 1))) (V : Unitary (2 ^
    (n + 1))) (i : Fin m) (js : List (Fin m)) (hi : i ∉ js) : ((js.map fun j ↦ (localSlotReg n m
    j).embedUnitary (U j)).prod) * (localSlotReg n m i).embedUnitary V = (localSlotReg n m
    i).embedUnitary V * ((js.map fun j ↦ (localSlotReg n m j).embedUnitary (U j)).prod) := by
  induction js with
  | nil => simp
  | cons j js ih =>
      rw [List.mem_cons, not_or] at hi
      rw [List.map_cons, List.prod_cons, mul_assoc, ih hi.2, ← mul_assoc,
        ← mul_assoc ((localSlotReg n m i).embedUnitary V)]
      congr 1; apply Subtype.ext
      exact (localSlotReg n m j).embedMatrix_comm_of_disjoint (localSlotReg n m i)
        (localSlotReg_disjoint (ne_comm.mp hi.1)) (U j).1 V.1
theorem slotHetero_listProd_mul {n m : ℕ} (U V : Fin m → Unitary (2 ^ (n + 1))) (is : List (Fin
    m)) (hnd : is.Nodup) : (is.map fun i ↦ (localSlotReg n m i).embedUnitary (U i)).prod * (is.map
    fun i ↦ (localSlotReg n m i).embedUnitary (V i)).prod = (is.map fun i ↦ (localSlotReg n m
    i).embedUnitary (U i * V i)).prod := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [List.nodup_cons] at hnd; simp only [List.map_cons, List.prod_cons]
      calc ((localSlotReg n m i).embedUnitary (U i) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (U j)).prod) *
            ((localSlotReg n m i).embedUnitary (V i) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (V j)).prod)
          = (localSlotReg n m i).embedUnitary (U i) *
              ((is.map fun j ↦ (localSlotReg n m j).embedUnitary (U j)).prod *
                (localSlotReg n m i).embedUnitary (V i)) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (V j)).prod := by group
        _ = (localSlotReg n m i).embedUnitary (U i) *
              ((localSlotReg n m i).embedUnitary (V i) *
                (is.map fun j ↦ (localSlotReg n m j).embedUnitary (U j)).prod) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (V j)).prod := by
              rw [slotHetero_comm_listProd U (V i) i is hnd.1]
        _ = ((localSlotReg n m i).embedUnitary (U i) *
              (localSlotReg n m i).embedUnitary (V i)) *
              ((is.map fun j ↦ (localSlotReg n m j).embedUnitary (U j)).prod *
                (is.map fun j ↦ (localSlotReg n m j).embedUnitary (V j)).prod) := by group
        _ = (localSlotReg n m i).embedUnitary (U i * V i) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (U j * V j)).prod := by
              rw [← (localSlotReg n m i).embedUnitary_mul, ih hnd.2]
theorem parallelSlotHetero_mul {n m : ℕ} (U V : Fin m → Unitary (2 ^ (n + 1))) :
    parallelSlotHetero U * parallelSlotHetero V = parallelSlotHetero (fun i ↦ U i * V i) := by
  simp only [parallelSlotHetero, List.ofFn_eq_map]
  exact slotHetero_listProd_mul U V (List.finRange m) (List.nodup_finRange m)
theorem parallelSlotHetero_one (n m : ℕ) :
    parallelSlotHetero (n := n) (m := m) (fun _ ↦ 1) = 1 := by
  simp [parallelSlotHetero]
theorem parallelSlotHetero_pow {n m : ℕ} (U : Fin m → Unitary (2 ^ (n + 1))) (K : ℕ) :
    (parallelSlotHetero U) ^ K = parallelSlotHetero (fun i ↦ (U i) ^ K) := by
  induction K with
  | zero => rw [pow_zero]; simp [parallelSlotHetero_one]
  | succ K ih => rw [pow_succ, ih, parallelSlotHetero_mul]; simp_rw [← pow_succ]
/-- Partial tensor-product state where slots in `active` hold `ψ i` and remaining slots hold
  `|0⟩`. -/
def partialHeteroVec {n m : ℕ} (active : Finset (Fin m)) (ψ : Fin m → Fin (2 ^ (n + 1)) → ℂ)
    (o : Fin (2 ^ ((n + 1) * m))) : ℂ :=
  (∏ i ∈ active, ψ i ((localSlotReg n m i).extractIndex o)) *
    (∏ i ∈ Finset.univ \ active, if (localSlotReg n m i).extractIndex o = 0 then 1 else 0)
theorem partialHeteroVec_empty {n m : ℕ} (ψ : Fin m → Fin (2 ^ (n + 1)) → ℂ) :
    partialHeteroVec ∅ ψ = Pi.single (0 : Fin (2 ^ ((n + 1) * m))) 1 :=
  partialSlotsVec_empty (n := n) (m := m) 0
theorem localSlotEmbed_mulVec_partialHeteroVec {n m : ℕ} (U : Fin m → Unitary (2 ^ (n + 1)))
    (active : Finset (Fin m)) {i : Fin m} (hi : i ∉ active) : (localSlotReg n m i).embedMatrix (U
    i).1 *ᵥ partialHeteroVec active (fun j ↦ (U j).1 *ᵥ Pi.single 0 1) = partialHeteroVec (insert
    i active) (fun j ↦ (U j).1 *ᵥ Pi.single 0 1) := by
  set ψ : Fin m → Fin (2 ^ (n + 1)) → ℂ := fun j ↦ (U j).1 *ᵥ Pi.single 0 1; funext o
  rw [(localSlotReg n m i).embedMatrix_mulVec_apply]
  have hsdiff : Finset.univ \ active = insert i (Finset.univ \ insert i active) := by
    ext j; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hji : j = i <;> simp [hji, hi]
  have hni : i ∉ Finset.univ \ insert i active := (by simp)
  have hterm (u : Fin (2 ^ (n + 1))) : partialHeteroVec active ψ ((localSlotReg n m
    i).replaceIndex o u) = (if u = 0 then (1 : ℂ) else 0) * ((∏ j ∈ active, ψ j ((localSlotReg n m
    j).extractIndex o)) * (∏ j ∈ Finset.univ \ insert i active, if (localSlotReg n m
    j).extractIndex o = 0 then 1 else 0)) := by
    simp only [partialHeteroVec]
    have hp1 : (∏ j ∈ active, ψ j ((localSlotReg n m j).extractIndex ((localSlotReg n m
      i).replaceIndex o u))) = ∏ j ∈ active, ψ j ((localSlotReg n m j).extractIndex o) := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hne : j ≠ i := fun h ↦ hi (h ▸ hj)
      rw [(localSlotReg n m j).extractIndex_replaceIndex_of_disjoint (localSlotReg n m i)
        (localSlotReg_disjoint hne)]
    rw [hp1, hsdiff, Finset.prod_insert hni, QRegister.extractIndex_replaceIndex]
    have hp2 : (∏ j ∈ Finset.univ \ insert i active, if (localSlotReg n m j).extractIndex
      ((localSlotReg n m i).replaceIndex o u) = 0 then (1 : ℂ) else 0) = ∏ j ∈ Finset.univ \
      insert i active, if (localSlotReg n m j).extractIndex o = 0 then (1 : ℂ) else 0 := by
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hne : j ≠ i := by
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hj; exact hj.2.1
      rw [(localSlotReg n m j).extractIndex_replaceIndex_of_disjoint (localSlotReg n m i)
        (localSlotReg_disjoint hne)]
    rw [hp2]; ring
  change (∑ u : Fin (2 ^ (n + 1)), (U i).1 ((localSlotReg n m i).extractIndex o) u *
        partialHeteroVec active ψ ((localSlotReg n m i).replaceIndex o u)) = _
  simp_rw [hterm]; rw [Finset.sum_eq_single 0]
  · simp only [↓reduceIte, one_mul, partialHeteroVec, Finset.prod_insert hi]
    have hpsi : (U i).1 ((localSlotReg n m i).extractIndex o) 0 =
        ψ i ((localSlotReg n m i).extractIndex o) := by simp [ψ]
    rw [hpsi]; ring
  · intro u _ hu; simp [hu]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim
theorem parallelSlotHetero_mulVec_zero {n m : ℕ} (U : Fin m → Unitary (2 ^ (n + 1))) :
    (parallelSlotHetero U).1 *ᵥ Pi.single (0 : Fin (2 ^ ((n + 1) * m))) (1 : ℂ) =
      fun o ↦ ∏ i : Fin m, ((U i).1 *ᵥ Pi.single 0 1) ((localSlotReg n m i).extractIndex o) := by
  have hrec (is : List (Fin m)) (hnd : is.Nodup) : ((is.map fun i ↦ (localSlotReg n m
    i).embedUnitary (U i)).prod).1 *ᵥ Pi.single (0 : Fin (2 ^ ((n + 1) * m))) (1 : ℂ) =
    partialHeteroVec is.toFinset (fun j ↦ (U j).1 *ᵥ Pi.single 0 1) := by
    induction is with
    | nil =>
        rw [List.map_nil, List.prod_nil, Submonoid.coe_one, Matrix.one_mulVec, List.toFinset_nil,
          partialHeteroVec_empty]
    | cons i is ih =>
        rw [List.nodup_cons] at hnd
        rw [List.map_cons, List.prod_cons, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih hnd.2,
          QRegister.embedUnitary_val,
          localSlotEmbed_mulVec_partialHeteroVec U is.toFinset (by simpa using hnd.1),
          List.toFinset_cons]
  rw [parallelSlotHetero, List.ofFn_eq_map, hrec (List.finRange m) (List.nodup_finRange m)]
  funext o; have huniv : (List.finRange m).toFinset = Finset.univ := (by ext; simp)
  rw [partialHeteroVec, huniv, Finset.sdiff_self, Finset.prod_empty, mul_one]
/-- `K`-iteration Grover oracle-diffuser loop on `oracleRegQ`. -/
noncomputable def groverLoopCirc {Var : Type} {Q w : ℕ}
    (oracleRegQ : QRegister w Q) (diffStep : Unitary (2 ^ w)) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w
  | 0 => .skip
  | K + 1 =>
      .seq (.seq (.oracle oracleRegQ) (.step (phaseI (oracleRegQ.embedUnitary diffStep))))
        (groverLoopCirc oracleRegQ diffStep K)
theorem zeroStepCost_groverLoopCirc {Var : Type} {Q w : ℕ} (oracleRegQ : QRegister w Q) {diffStep
    : Unitary (2 ^ w)} (hd : IsRealMatrix diffStep.1) (K : ℕ) : ZeroStepCost (groverLoopCirc (Var
    := Var) oracleRegQ diffStep K) := by
  induction K with
  | zero => trivial
  | succ K ih =>
      exact ⟨⟨trivial, zeroStepCost_step_phaseI (isRealMatrix_embedMatrix oracleRegQ hd)⟩, ih⟩
theorem interp_groverLoopCirc {Var : Type} [DecidableEq Var] {Q w : ℕ} (oracleRegQ : QRegister w
    Q) (diffStep O : Unitary (2 ^ w)) (K : ℕ) (Δ : CQState (Store Var) (2 ^ Q)) : (interp
      ((groverLoopCirc
    oracleRegQ diffStep K).compile QProg.qAssign O)).toStateFun Δ = CQState.qAssign
    (oracleRegQ.embedUnitary ((diffStep * O) ^ K)) Δ := by
  induction K generalizing Δ with
  | zero =>
      simp only [groverLoopCirc, OracleDynamicCircuit.compile_skip, pow_zero,
        QRegister.embedUnitary_one]
      apply Subtype.ext; funext σ; apply Subtype.ext; ext1
      change (Δ.1 σ).1.mat = ((Δ.1 σ).1.conj (1 : Unitary (2 ^ Q)).1).mat; simp
  | succ K ih =>
      simp only [groverLoopCirc, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step,
        interp_qSeq, QMonad.Q.toStateFun_bind, interp_qAssign, QMonad.Q.toStateFun_qAssign]
      rw [cqState_qAssign_phaseI, cqState_qAssign_comp, ← oracleRegQ.embedUnitary_mul, ih,
        cqState_qAssign_comp, ← oracleRegQ.embedUnitary_mul, ← pow_succ]
theorem expectedCost_groverLoopCirc {Var : Type} [DecidableEq Var] {Q w : ℕ} (oracleRegQ :
    QRegister w Q) {diffStep : Unitary (2 ^ w)} (hd : IsRealMatrix diffStep.1) {O : Unitary (2 ^
    w)} (hO : IsRealMatrix O.1) (K : ℕ) (Δ : CQState (Store Var) (2 ^ Q)) : expectedCost
    (CostModel.ofEmbeddedOracle O) ((groverLoopCirc oracleRegQ diffStep K).compile QProg.qAssign
    O) Δ = stateMass Δ * (K : ℝ≥0∞) := by
  induction K generalizing Δ with
  | zero => simp [groverLoopCirc]
  | succ K ih =>
      let model := CostModel.ofEmbeddedOracle (n := Q) O
      simp only [groverLoopCirc, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_step,
        expectedCost_qSeq, expectedCost_qAssign]
      have h1 : model.unitaryCost (oracleRegQ.embedUnitary O) = 1 :=
        CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary O oracleRegQ
      have h0 : model.unitaryCost (phaseI (oracleRegQ.embedUnitary diffStep)) = 0 :=
        ofEmbeddedOracle_unitaryCost_phaseI_eq_zero hO (isRealMatrix_embedMatrix oracleRegQ hd)
      rw [h1, h0, ih]
      simp only [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qAssign,
        QMonad.Q.toStateFun_qAssign, stateMass_qAssign]
      push_cast; ring
/-- Contiguous `((n + 1) * m)`-qubit oracle block `0.. (n + 1) * m - 1` inside `Q` qubits. -/
def subcubeOracleReg (n m Q : ℕ) (horQ : (n + 1) * m ≤ Q) : QRegister ((n + 1) * m) Q :=
  QRegister.block 0 ((n + 1) * m) (by omega)
/-- Per-slot subcube preparation unitary across all `m` oracle slots (`m = 2 ^ d`, `s + d =
  n`). -/
noncomputable def subcubePrepUnitary {n : ℕ} (m s d : ℕ) (hsd : s + d = n) (hm : m = 2 ^ d) :
    Unitary (2 ^ ((n + 1) * m)) :=
  parallelSlotHetero fun i : Fin m ↦
    (lowSubSlotReg s d hsd).embedUnitary (slotPrepLocal s) *
      (highSubIdxReg s d hsd).embedUnitary (permutationUnitary (Equiv.swap 0 (finCongr hm i)))
/-- Per-slot subcube Grover diffuser unitary across all `m` oracle slots (`s + d = n`). -/
noncomputable def subcubeDiffUnitary {n : ℕ} (m s d : ℕ) (hsd : s + d = n) :
    Unitary (2 ^ ((n + 1) * m)) :=
  parallelSlotHetero fun _ : Fin m ↦ (lowSubSlotReg s d hsd).embedUnitary (slotDiffuserLocal s)
/-- Per-slot subcube unpreparation unitary across all `m` oracle slots (`s + d = n`). -/
noncomputable def subcubeUnprepUnitary {n : ℕ} (m s d : ℕ) (hsd : s + d = n) :
    Unitary (2 ^ ((n + 1) * m)) :=
  parallelSlotHetero fun _ : Fin m ↦ (lowSubSlotReg s d hsd).embedUnitary (slotUnprepLocal s)
/-- Combined `m`-slot subcube Grover-and-verify unitary before measurement. -/
noncomputable def subcubePassUnitary {n : ℕ} (m s d : ℕ) (hsd : s + d = n) (hm : m = 2 ^ d)
    (B : Finset (Fin (2 ^ n))) (K : ℕ) : Unitary (2 ^ ((n + 1) * m)) :=
  parallelSlotHetero fun i : Fin m ↦ subSlotFinalUnitary s d hsd B (finCongr hm i) K
/-- Subcube parallel Grover pass on `subcubeOracleReg n m Q horQ` (`s + d = n`, `m = 2 ^
  d`),
  using `K + 1` parallel oracle calls (`K` Grover steps + `1` verification call) and
  measuring
  `subcubeOracleReg n m Q horQ` into `res`. -/
noncomputable def subcubePassCircuit {Var : Type} (res : Var) (n m s d Q : ℕ)
    (hsd : s + d = n) (hm : m = 2 ^ d) (horQ : (n + 1) * m ≤ Q) (K : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  .seq (.step (phaseI ((subcubeOracleReg n m Q horQ).embedUnitary
      (subcubePrepUnitary m s d hsd hm))))
    (.seq (groverLoopCirc (subcubeOracleReg n m Q horQ) (subcubeDiffUnitary m s d hsd) K)
      (.seq (.step (phaseI ((subcubeOracleReg n m Q horQ).embedUnitary
          (subcubeUnprepUnitary m s d hsd))))
        (.seq (.oracle (subcubeOracleReg n m Q horQ))
          (.measure res (subcubeOracleReg n m Q horQ)))))
theorem isRealMatrix_slotPrepLocal_sub (s : ℕ) : IsRealMatrix (slotPrepLocal s).1 := by
  dsimp only [slotPrepLocal]
  rw [Submonoid.coe_mul, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  refine isRealMatrix_mul (isRealMatrix_embedMatrix _ ?_) (isRealMatrix_embedMatrix _ ?_)
  · rw [hadamardUnitary_coe]; exact isRealMatrix_hadamardMatrix s
  · dsimp only [markerMinusUnitary]; rw [Submonoid.coe_mul, hadamardUnitary_coe]
    exact isRealMatrix_mul (isRealMatrix_hadamardMatrix 1) (isRealMatrix_permutationUnitary _)
theorem isRealMatrix_slotDiffuserLocal_sub (s : ℕ) : IsRealMatrix (slotDiffuserLocal s).1 := by
  dsimp only [slotDiffuserLocal]; rw [QRegister.embedUnitary_val, Grover.diffuserUnitary_coe]
  exact isRealMatrix_embedMatrix _ (isRealMatrix_diffuserMatrix s)
theorem isRealMatrix_slotUnprepLocal_sub (s : ℕ) : IsRealMatrix (slotUnprepLocal s).1 := by
  dsimp only [slotUnprepLocal, markerMinusInvUnitary]
  rw [QRegister.embedUnitary_val, Submonoid.coe_mul, hadamardUnitary_coe]
  exact isRealMatrix_embedMatrix _
    (isRealMatrix_mul (isRealMatrix_permutationUnitary _) (isRealMatrix_hadamardMatrix 1))
theorem zeroStepCost_subcubePassCircuit {Var : Type} (res : Var) (n m s d Q : ℕ)
    (hsd : s + d = n) (hm : m = 2 ^ d) (horQ : (n + 1) * m ≤ Q) (K : ℕ) :
    ZeroStepCost (subcubePassCircuit (Var := Var) res n m s d Q hsd hm horQ K) := by
  have hprep : IsRealMatrix (subcubePrepUnitary m s d hsd hm).1 := by
    rw [subcubePrepUnitary]
    exact isRealMatrix_parallelSlotHetero fun i ↦ by
      rw [Submonoid.coe_mul, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
      exact isRealMatrix_mul (isRealMatrix_embedMatrix _ (isRealMatrix_slotPrepLocal_sub s))
        (isRealMatrix_embedMatrix _ (isRealMatrix_permutationUnitary _))
  have hdiff : IsRealMatrix (subcubeDiffUnitary m s d hsd).1 := by
    rw [subcubeDiffUnitary]
    exact isRealMatrix_parallelSlotHetero fun _ ↦ by
      rw [QRegister.embedUnitary_val]
      exact isRealMatrix_embedMatrix _ (isRealMatrix_slotDiffuserLocal_sub s)
  have hunprep : IsRealMatrix (subcubeUnprepUnitary m s d hsd).1 := by
    rw [subcubeUnprepUnitary]
    exact isRealMatrix_parallelSlotHetero fun _ ↦ by
      rw [QRegister.embedUnitary_val]
      exact isRealMatrix_embedMatrix _ (isRealMatrix_slotUnprepLocal_sub s)
  rw [subcubePassCircuit]
  exact ⟨zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _ hprep), zeroStepCost_groverLoopCirc
    _ hdiff K, zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _ hunprep), trivial, trivial⟩
theorem expectedCost_subcubePassCircuit {Var : Type} [DecidableEq Var] (res : Var) (n m s d Q : ℕ)
    (hsd : s + d = n) (hm : m = 2 ^ d) (horQ : (n + 1) * m ≤ Q) (K : ℕ) (B : Finset (Fin (2 ^ n)))
    (Δ : CQState (Store Var) (2 ^ Q)) : expectedCost (CostModel.ofEmbeddedOracle
      (parallelMarkingOracle m
    B)) ((subcubePassCircuit res n m s d Q hsd hm horQ K).compile QProg.qAssign
    (parallelMarkingOracle m B)) Δ = stateMass Δ * ENNReal.ofReal ((K : ℝ) + 1) := by
  have hO : IsRealMatrix (parallelMarkingOracle m B).1 := isRealMatrix_parallelMarkingOracle B
  have hzc := zeroStepCost_subcubePassCircuit (Var := Var) res n m s d Q hsd hm horQ K
  have hdiff : IsRealMatrix (subcubeDiffUnitary m s d hsd).1 := by
    rw [subcubeDiffUnitary]
    exact isRealMatrix_parallelSlotHetero fun _ ↦ by
      rw [QRegister.embedUnitary_val]
      exact isRealMatrix_embedMatrix _ (isRealMatrix_slotDiffuserLocal_sub s)
  rw [subcubePassCircuit]
  simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
    OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_measure,
    QProg.measureRegister, expectedCost_qSeq, expectedCost_qAssign, expectedCost_qMeasure]
  rw [hzc.1 hO, hzc.2.2.1 hO, expectedCost_groverLoopCirc _ hdiff hO K,
    CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, interp_groverLoopCirc]
  simp only [CharP.cast_eq_zero, mul_zero, interp_qAssign,
    QMonad.Q.toStateFun_qAssign, stateMass_qAssign, CQState.qAssign_qAssign, Nat.cast_one, mul_one,
    CostModel.ofEmbeddedOracle_measurementCost, add_zero, zero_add]
  have hK : (K : ℝ≥0∞) + 1 = ENNReal.ofReal ((K : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  nth_rw 2 [← mul_one (stateMass Δ)]; rw [← mul_add, hK]
/-- Output amplitude vector on `Fin (2 ^ ((n + 1) * m))` before measurement in
  `subcubePassCircuit`. -/
noncomputable def subcubeParallelVec {n m : ℕ} (s d : ℕ) (hsd : s + d = n) (hm : m = 2 ^ d)
    (B : Finset (Fin (2 ^ n))) (K : ℕ) (w : Fin (2 ^ ((n + 1) * m))) : ℂ :=
  ∏ i : Fin m,
    subSlotPairVec s d hsd (slotFinalVec (subcubeSlice s d hsd B (finCongr hm i)) K)
      (finCongr hm i) ((localSlotReg n m i).extractIndex w)
theorem subcubePassUnitary_eq {n m s d : ℕ} (hsd : s + d = n) (hm : m = 2 ^ d) (B : Finset (Fin (2
    ^ n))) (K : ℕ) : ((parallelMarkingOracle m B * subcubeUnprepUnitary m s d hsd) *
    (subcubeDiffUnitary m s d hsd * parallelMarkingOracle m B) ^ K) * subcubePrepUnitary m s d hsd
    hm = subcubePassUnitary m s d hsd hm B K := by
  have hO_eq :
      parallelMarkingOracle m B = parallelSlotHetero (fun _ : Fin m ↦ setMarkingOracle B) := by
    have hreg (i : Fin m) :
        QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt]) = localSlotReg n m i := by
      rw [localSlotReg]
    exact congrArg List.prod (congrArg List.ofFn (funext fun i ↦ congrArg (fun r ↦ r.embedUnitary
      (setMarkingOracle B)) (hreg i)))
  rw [hO_eq, subcubeUnprepUnitary, subcubeDiffUnitary, subcubePrepUnitary, subcubePassUnitary,
    parallelSlotHetero_mul, parallelSlotHetero_mul, parallelSlotHetero_pow,
    parallelSlotHetero_mul, parallelSlotHetero_mul]
  apply congrArg parallelSlotHetero; funext i; simp only [subSlotFinalUnitary, mul_assoc]
theorem passCircuit_toStateFun_of_eq {Var : Type} [DecidableEq Var] {W Q : ℕ}
    (res : Var) (r : QRegister W Q) (prep diff unprep O U_tot : Unitary (2 ^ W))
    (K : ℕ) (hU : ((O * unprep) * (diff * O) ^ K) * prep = U_tot)
    (Δ : CQState (Store Var) (2 ^ Q)) :
    (interp ((OracleDynamicCircuit.seq (.step (phaseI (r.embedUnitary prep)))
      (.seq (groverLoopCirc r diff K)
        (.seq (.step (phaseI (r.embedUnitary unprep)))
          (.seq (.oracle r) (.measure res r))))).compile QProg.qAssign O)).toStateFun Δ =
    (interp (QProg.qAssign (r.embedUnitary U_tot) ;;
      QProg.measureRegister res r)).toStateFun Δ := by
  simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
    OracleDynamicCircuit.compile_oracle, OracleDynamicCircuit.compile_measure,
    interp_qSeq, QMonad.Q.toStateFun_bind, interp_qAssign, QMonad.Q.toStateFun_qAssign]
  congr 1
  rw [cqState_qAssign_phaseI, cqState_qAssign_phaseI, interp_groverLoopCirc,
    cqState_qAssign_comp, ← r.embedUnitary_mul, cqState_qAssign_comp, ← r.embedUnitary_mul,
    cqState_qAssign_comp, ← r.embedUnitary_mul, hU]
theorem subcubePassCircuit_interp_eq {Var : Type} [DecidableEq Var]
    (res : Var) (n m s d Q : ℕ) (hsd : s + d = n) (hm : m = 2 ^ d)
    (horQ : (n + 1) * m ≤ Q) (K : ℕ) (B : Finset (Fin (2 ^ n)))
    (Δ : CQState (Store Var) (2 ^ Q)) :
    (interp ((subcubePassCircuit res n m s d Q hsd hm horQ K).compile QProg.qAssign
      (parallelMarkingOracle m B))).toStateFun Δ =
    (interp (QProg.qAssign ((subcubeOracleReg n m Q horQ).embedUnitary
        (subcubePassUnitary m s d hsd hm B K)) ;;
      QProg.measureRegister res (subcubeOracleReg n m Q horQ))).toStateFun Δ := by
  dsimp only [subcubePassCircuit]
  exact passCircuit_toStateFun_of_eq res (subcubeOracleReg n m Q horQ) (subcubePrepUnitary m s d
    hsd hm) (subcubeDiffUnitary m s d hsd) (subcubeUnprepUnitary m s d hsd) (parallelMarkingOracle
    m B) (subcubePassUnitary m s d hsd hm B K) K (subcubePassUnitary_eq hsd hm B K) Δ
theorem subcubePassUnitary_mulVec_zero {n m s d : ℕ} (hsd : s + d = n) (hm : m = 2 ^ d) (B :
    Finset (Fin (2 ^ n))) (K : ℕ) (o : Fin (2 ^ ((n + 1) * m))) : ((subcubePassUnitary m s d hsd
    hm B K).1 *ᵥ Pi.single 0 1) o = subcubeParallelVec s d hsd hm B K o := by
  rw [subcubePassUnitary]
  have hvec := congrFun (parallelSlotHetero_mulVec_zero
    (fun i : Fin m ↦ subSlotFinalUnitary s d hsd B (finCongr hm i) K)) o
  rw [hvec, subcubeParallelVec]; refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [subSlotFinalUnitary_mulVec_zero]
theorem subcubePass_sliceState_trace {Var : Type} [DecidableEq Var] (res : Var) (n m s d Q : ℕ)
    (hsd : s + d = n) (hm : m = 2 ^ d) (horQ : (n + 1) * m ≤ Q) (K : ℕ) (B : Finset (Fin (2 ^ n)))
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ) {wVal : ℕ} (hw :
      wVal <
    2 ^ ((n + 1) * m)) :
    let w : Fin (2 ^ ((n + 1) * m)) := ⟨wVal, hw⟩
    ((sliceState res 0 ((n + 1) * m) wVal ((interp ((subcubePassCircuit res n m s d Q hsd hm horQ
      K).compile QProg.qAssign (parallelMarkingOracle m B))).toStateFun Δ)).trace : ℝ) =
      Complex.normSq (subcubeParallelVec s d hsd hm B K w) * Δ.trace := by
  intro w
  rw [subcubePassCircuit_interp_eq, embedUnitary_measure_sliceState_trace res (subcubeOracleReg n
    m Q horQ) (subcubePassUnitary m s d hsd hm B K) hΔ hw, subcubePassUnitary_mulVec_zero hsd hm B
    K ⟨wVal, hw⟩]
/-- Set of marked `n`-bit addresses extracted from the marker-`1` slots of an `((n + 1) *
  m)`-bit
  oracle-register outcome `w`. -/
def hitSetOfOracleOutcome (n m : ℕ) (w : Fin (2 ^ ((n + 1) * m))) : Finset (Fin (2 ^ n)) :=
  ((Finset.univ : Finset (Fin m)).filter fun i ↦
    (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex w) = 1).image
    fun i ↦ (localIdxReg n).extractIndex ((localSlotReg n m i).extractIndex w)
theorem subSlotPairVec_normSq_sum_filter {n s d : ℕ} (hsd : s + d = n)
    (A : Finset (Fin (2 ^ s))) (q : Fin (2 ^ d)) (K : ℕ) (b : Fin (2 ^ 1)) :
    (∑ u : Fin (2 ^ (n + 1)) with (localMarkerReg n).extractIndex u = b,
        Complex.normSq (subSlotPairVec s d hsd (slotFinalVec A K) q u)) =
      ∑ v : Fin (2 ^ (s + 1)) with (localMarkerReg s).extractIndex v = b,
        Complex.normSq (slotFinalVec A K v) := by
  let S_sub : Finset (Fin (2 ^ (n + 1))) := Finset.univ.filter fun u ↦ (localMarkerReg
    n).extractIndex u = b ∧ (highSubIdxReg s d hsd).extractIndex u = q
  have hsub_eq : (∑ u : Fin (2 ^ (n + 1)) with (localMarkerReg n).extractIndex u = b,
    Complex.normSq (subSlotPairVec s d hsd (slotFinalVec A K) q u)) = ∑ u ∈ S_sub, Complex.normSq
    (subSlotPairVec s d hsd (slotFinalVec A K) q u) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro u hu; rw [Finset.mem_filter] at hu ⊢; exact ⟨Finset.mem_univ _, hu.2.1⟩
    · intro u hu hnot; rw [Finset.mem_filter] at hu
      have hnq : (highSubIdxReg s d hsd).extractIndex u ≠ q :=
        fun hq ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2, hq⟩)
      simp [subSlotPairVec, hnq]
  rw [hsub_eq]
  let emb (v : Fin (2 ^ (s + 1))) : Fin (2 ^ (n + 1)) := (subSlotSplitEquiv s d hsd).symm (v, q)
  have hex_low (v : Fin (2 ^ (s + 1))) : (lowSubSlotReg s d hsd).extractIndex (emb v) = v := by
    rw [extractIndex_lowSubSlotReg hsd]; simp [emb]
  have hex_high (v : Fin (2 ^ (s + 1))) : (highSubIdxReg s d hsd).extractIndex (emb v) = q := by
    rw [extractIndex_highSubIdxReg hsd]; simp [emb]
  symm
  refine Finset.sum_bij (fun v _ ↦ emb v) ?_ ?_ ?_ ?_
  · intro v hv; rw [Finset.mem_filter] at hv ⊢; refine ⟨Finset.mem_univ _, ?_, hex_high v⟩
    rw [extractIndex_localMarkerReg_subSlot hsd, hex_low]; exact hv.2
  · intro v₁ _ v₂ _ heq; exact congrArg Prod.fst ((subSlotSplitEquiv s d hsd).symm.injective heq)
  · intro u hu; rw [Finset.mem_filter] at hu
    refine ⟨(lowSubSlotReg s d hsd).extractIndex u, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (extractIndex_localMarkerReg_subSlot hsd u) ▸ hu.2.1⟩
    · apply (subSlotSplitEquiv s d hsd).injective
      rw [← Prod.eta (subSlotSplitEquiv s d hsd u), ← extractIndex_lowSubSlotReg hsd, ←
        extractIndex_highSubIdxReg hsd, hu.2.2]; simp [emb]
  · intro v _; simp [subSlotPairVec, hex_high v, hex_low v]
theorem subSlotPairVec_normSq_sum_univ {n s d : ℕ} (hsd : s + d = n) (A : Finset (Fin (2 ^ s))) (q
    : Fin (2 ^ d)) (K : ℕ) : (∑ u : Fin (2 ^ (n + 1)), Complex.normSq (subSlotPairVec s d hsd
    (slotFinalVec A K) q u)) = 1 := by
  have hpart (W : ℕ) (f : Fin (2 ^ (W + 1)) → ℝ) : (∑ u : Fin (2 ^ (W + 1)), f u) = (∑ u : Fin (2
    ^ (W + 1)) with (localMarkerReg W).extractIndex u = 0, f u) + (∑ u : Fin (2 ^ (W + 1)) with
    (localMarkerReg W).extractIndex u = 1, f u) := by
    have hunion : (Finset.univ : Finset (Fin (2 ^ (W + 1)))) =
        (Finset.univ.filter fun u ↦ (localMarkerReg W).extractIndex u = 0) ∪
          (Finset.univ.filter fun u ↦ (localMarkerReg W).extractIndex u = 1) := by
      ext u; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      generalize (localMarkerReg W).extractIndex u = b; fin_cases b <;> simp
    have hdisj : Disjoint
        (Finset.univ.filter fun u : Fin (2 ^ (W + 1)) ↦ (localMarkerReg W).extractIndex u = 0)
        (Finset.univ.filter fun u : Fin (2 ^ (W + 1)) ↦ (localMarkerReg W).extractIndex u = 1) := by
      rw [Finset.disjoint_filter]; intro _ _ h0 h1; exact zero_ne_one (h0.symm.trans h1)
    conv_lhs => rw [hunion]
    exact Finset.sum_union hdisj
  rw [hpart n, subSlotPairVec_normSq_sum_filter hsd A q K 0, subSlotPairVec_normSq_sum_filter hsd
    A q K 1, ← hpart s]; exact sum_normSq_slotFinalVec_univ A K
theorem sum_normSq_subcubeParallelVec_univ {n m s d : ℕ} (hsd : s + d = n) (hm : m = 2 ^ d) (B :
    Finset (Fin (2 ^ n))) (K : ℕ) : (∑ w : Fin (2 ^ ((n + 1) * m)), Complex.normSq
    (subcubeParallelVec s d hsd hm B K w)) = 1 := by
  let φ (i : Fin m) (u : Fin (2 ^ (n + 1))) : ℝ := Complex.normSq (subSlotPairVec s d hsd
    (slotFinalVec (subcubeSlice s d hsd B (finCongr hm i)) K) (finCongr hm i) u)
  have hbij : (∑ w : Fin (2 ^ ((n + 1) * m)), Complex.normSq (subcubeParallelVec s d hsd hm B K
    w)) = ∑ f : Fin m → Fin (2 ^ (n + 1)), ∏ i : Fin m, φ i (f i) := by
    refine Fintype.sum_equiv (slotsEquiv n m) _ _ fun w ↦ ?_
    simp [subcubeParallelVec, map_prod, φ]
  rw [hbij, ← Fintype.prod_sum]; refine Finset.prod_eq_one fun i _ ↦ ?_
  exact subSlotPairVec_normSq_sum_univ hsd _ (finCongr hm i) K
/-- Zero false positives on every seed: whenever `subcubeParallelVec s d hsd hm B K w ≠ 0`,
  every
  hit decoded by `hitSetOfOracleOutcome n m w` lies in `B`. -/
theorem hitSetOfOracleOutcome_subset_of_ne_zero {n m s d : ℕ} (hsd : s + d = n) (hm : m = 2 ^ d)
    {B : Finset (Fin (2 ^ n))} {K : ℕ} {w : Fin (2 ^ ((n + 1) * m))} (hne : subcubeParallelVec s d
    hsd hm B K w ≠ 0) : hitSetOfOracleOutcome n m w ⊆ B := by
  intro y hy; rw [hitSetOfOracleOutcome, Finset.mem_image] at hy; obtain ⟨i, hi_filt, rfl⟩ := hy
  have hmk1 : (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex w) = 1 :=
    (Finset.mem_filter.mp hi_filt).2
  let u_i := (localSlotReg n m i).extractIndex w
  have hu_ne : subSlotPairVec s d hsd (slotFinalVec (subcubeSlice s d hsd B (finCongr hm i)) K)
    (finCongr hm i) u_i ≠ 0 := fun h0 ↦ hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hq : (highSubIdxReg s d hsd).extractIndex u_i = finCongr hm i := by
    by_contra hnq
    exact hu_ne (by rw [subSlotPairVec, ite_eq_right hnq])
  have hslot_ne : slotFinalVec (subcubeSlice s d hsd B (finCongr hm i)) K
      ((lowSubSlotReg s d hsd).extractIndex u_i) ≠ 0 := by
    rwa [subSlotPairVec, ite_eq_left hq] at hu_ne
  have hmk_s : (localMarkerReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex u_i) = 1 :=
    (extractIndex_localMarkerReg_subSlot hsd u_i).symm.trans hmk1
  have hmem_slice : (localIdxReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex u_i) ∈
      subcubeSlice s d hsd B (finCongr hm i) := by
    by_contra hnot
    exact hslot_ne (slotFinalVec_eq_zero_of_marker_one_of_not_mem hmk_s hnot)
  rw [subcubeSlice, Finset.mem_filter] at hmem_slice
  have hsplit := subcubeSplitEquiv_localIdxReg hsd u_i; rw [hq] at hsplit
  have heq : (localIdxReg n).extractIndex u_i = (subcubeSplitEquiv s d hsd).symm
        ((localIdxReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex u_i), finCongr hm i) :=
    (subcubeSplitEquiv s d hsd).eq_symm_apply.mpr hsplit
  rw [heq]; exact hmem_slice.2
theorem card_subcubeSlice_eq_one_of_injOn {n s d : ℕ} (hsd : s + d = n) {B : Finset (Fin (2 ^ n))}
    (hcf : Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2) (B : Set (Fin (2 ^ n)))) {y : Fin
    (2 ^ n)} (hy : y ∈ B) : subcubeSlice s d hsd B (subcubeSplitEquiv s d hsd y).2 =
    {(subcubeSplitEquiv s d hsd y).1} := by
  ext a
  simp only [subcubeSlice, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hmem
    have hy' : (subcubeSplitEquiv s d hsd).symm (a, (subcubeSplitEquiv s d hsd y).2) = y := by
      refine hcf hmem hy ?_
      simp
    exact congrArg Prod.fst ((subcubeSplitEquiv s d hsd).symm_apply_eq.mp hy')
  · rintro rfl
    simpa using hy
/-- Exact Binomial(`B.card`, `1 - p_succ_set K s 1`) residual-count expectation on any
  subcube-collision-free set `B`. -/
theorem sum_normSq_subcubeParallelVec_cf {n m s d : ℕ} (hsd : s + d = n) (hm : m = 2 ^ d) {B :
    Finset (Fin (2 ^ n))} (hcf : Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2) (B : Set (Fin
    (2 ^ n)))) (K : ℕ) (g : ℕ → ℝ) : (∑ w : Fin (2 ^ ((n + 1) * m)), Complex.normSq
    (subcubeParallelVec s d hsd hm B K w) * g (B \ hitSetOfOracleOutcome n m w).card) = ∑ j ∈
    Finset.range (B.card + 1), (B.card.choose j : ℝ) * (1 - p_succ_set K s 1) ^ j * (p_succ_set K
    s 1) ^ (B.card - j) * g j := by
  classical
  let slotOf (y : Fin (2 ^ n)) : Fin m := (finCongr hm).symm (subcubeSplitEquiv s d hsd y).2
  have hslot_inj : Set.InjOn slotOf (B : Set (Fin (2 ^ n))) := by
    intro y₁ hy₁ y₂ hy₂ h; exact hcf hy₁ hy₂ ((finCongr hm).symm.injective h)
  let I : Finset (Fin m) := B.image slotOf
  have hI_card : I.card = B.card := Finset.card_image_of_injOn hslot_inj; let p := p_succ_set K s 1
  let ψ (i : Fin m) : Fin (2 ^ (n + 1)) → ℂ :=
    subSlotPairVec s d hsd (slotFinalVec (subcubeSlice s d hsd B (finCongr hm i)) K) (finCongr hm i)
  let zSet (w : Fin (2 ^ ((n + 1) * m))) : Finset (Fin m) := Finset.univ.filter fun i ↦
    (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex w) = 0
  have hempty_slice (i : Fin m) (hi : i ∉ I) : subcubeSlice s d hsd B (finCongr hm i) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]; intro a ha
    rw [subcubeSlice, Finset.mem_filter] at ha; apply hi; rw [Finset.mem_image]
    refine ⟨(subcubeSplitEquiv s d hsd).symm (a, finCongr hm i), ha.2, ?_⟩
    simp [slotOf]
  have hres_card (w : Fin (2 ^ ((n + 1) * m))) (hne : subcubeParallelVec s d hsd hm B K w ≠ 0) :
    (B \ hitSetOfOracleOutcome n m w).card = (I ∩ zSet w).card := by
    refine Finset.card_bij (fun y _ ↦ slotOf y) ?_ ?_ ?_
    · intro y hy; rw [Finset.mem_sdiff] at hy; rw [Finset.mem_inter, Finset.mem_image]
      refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
      rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
      generalize hmk :
        (localMarkerReg n).extractIndex ((localSlotReg n m (slotOf y)).extractIndex w) = b
      fin_cases b
      · rfl
      · exfalso; apply hy.2; let i := slotOf y; let u_i := (localSlotReg n m i).extractIndex w
        have hu_ne : ψ i u_i ≠ 0 := fun h0 ↦ hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
        have hq : (highSubIdxReg s d hsd).extractIndex u_i = finCongr hm i := by
          by_contra hnq
          exact hu_ne (by dsimp only [ψ]; rw [subSlotPairVec, ite_eq_right hnq])
        have hmk_s : (localMarkerReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex u_i) =
          1 := (extractIndex_localMarkerReg_subSlot hsd u_i).symm.trans hmk
        have hslot_ne : slotFinalVec (subcubeSlice s d hsd B (finCongr hm i)) K
            ((lowSubSlotReg s d hsd).extractIndex u_i) ≠ 0 := by
          dsimp only [ψ] at hu_ne; rwa [subSlotPairVec, ite_eq_left hq] at hu_ne
        have hmem_sl : (localIdxReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex u_i) ∈
            subcubeSlice s d hsd B (finCongr hm i) := by
          by_contra hnot
          exact hslot_ne (slotFinalVec_eq_zero_of_marker_one_of_not_mem hmk_s hnot)
        rw [subcubeSlice, Finset.mem_filter] at hmem_sl
        have hsplit := subcubeSplitEquiv_localIdxReg hsd u_i; rw [hq] at hsplit
        have hy_out : (localIdxReg n).extractIndex u_i = y := by
          refine hcf ?_ hy.1 ?_
          · rw [(subcubeSplitEquiv s d hsd).eq_symm_apply.mpr hsplit]; exact hmem_sl.2
          · dsimp only; rw [hsplit]; simp [i, slotOf]
        rw [hitSetOfOracleOutcome, Finset.mem_image]
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmk⟩, hy_out⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      exact hslot_inj (Finset.mem_sdiff.mp hy₁).1 (Finset.mem_sdiff.mp hy₂).1 heq
    · intro i hi; rw [Finset.mem_inter] at hi; obtain ⟨y, hyB, rfl⟩ := Finset.mem_image.mp hi.1
      refine ⟨y, Finset.mem_sdiff.mpr ⟨hyB, ?_⟩, rfl⟩
      intro hy_hit; rw [hitSetOfOracleOutcome, Finset.mem_image] at hy_hit
      obtain ⟨i', hi'_filt, hy_eq⟩ := hy_hit
      have hmk1 : (localMarkerReg n).extractIndex ((localSlotReg n m i').extractIndex w) = 1 :=
        (Finset.mem_filter.mp hi'_filt).2
      let u_i' := (localSlotReg n m i').extractIndex w
      have hu_ne : ψ i' u_i' ≠ 0 := fun h0 ↦ hne (Finset.prod_eq_zero (Finset.mem_univ i') h0)
      have hq' : (highSubIdxReg s d hsd).extractIndex u_i' = finCongr hm i' := by
        by_contra hnq
        exact hu_ne (by dsimp only [ψ]; rw [subSlotPairVec, ite_eq_right hnq])
      have hsplit' := subcubeSplitEquiv_localIdxReg hsd u_i'; rw [hy_eq, hq'] at hsplit'
      have hi'_eq : i' = slotOf y := (by dsimp only [slotOf]; rw [congrArg Prod.snd hsplit']; simp)
      have hmk0 : (localMarkerReg n).extractIndex ((localSlotReg n m (slotOf y)).extractIndex w) =
        0 := (Finset.mem_filter.mp hi.2).2
      rw [hi'_eq] at hmk1; exact zero_ne_one (hmk0.symm.trans hmk1)
  have hreplace : (∑ w : Fin (2 ^ ((n + 1) * m)), Complex.normSq (subcubeParallelVec s d hsd hm B
    K w) * g (B \ hitSetOfOracleOutcome n m w).card) = ∑ w : Fin (2 ^ ((n + 1) * m)),
    Complex.normSq (subcubeParallelVec s d hsd hm B K w) * g (I ∩ zSet w).card := by
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    by_cases hne : subcubeParallelVec s d hsd hm B K w = 0
    · simp [hne]
    · rw [hres_card w hne]
  rw [hreplace]
  have hzero_out (w : Fin (2 ^ ((n + 1) * m))) (hsub : ¬ (Finset.univ \ I ⊆ zSet w)) :
      subcubeParallelVec s d hsd hm B K w = 0 := by
    rw [Finset.subset_iff] at hsub
    push Not at hsub
    obtain ⟨i, hi_out, hi_nz⟩ := hsub; have hi_not_I : i ∉ I := (Finset.mem_sdiff.mp hi_out).2
    have hmk_ne0 : (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex w) ≠ 0 :=
      fun h0 ↦ hi_nz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
    have hmk1 : (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex w) = 1 := by
      generalize
        (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex w) = b at hmk_ne0 ⊢
      fin_cases b
      · exact (hmk_ne0 rfl).elim
      · rfl
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    let u_i := (localSlotReg n m i).extractIndex w
    by_cases hq : (highSubIdxReg s d hsd).extractIndex u_i = finCongr hm i
    · rw [subSlotPairVec, ite_eq_left hq]
      have hmk_s : (localMarkerReg s).extractIndex ((lowSubSlotReg s d hsd).extractIndex u_i) = 1 :=
        (extractIndex_localMarkerReg_subSlot hsd u_i).symm.trans hmk1
      rw [hempty_slice i hi_not_I]
      exact slotFinalVec_eq_zero_of_marker_one_of_not_mem hmk_s (Finset.notMem_empty _)
    · rw [subSlotPairVec, ite_eq_right hq]
  have hfiber : (∑ w : Fin (2 ^ ((n + 1) * m)), Complex.normSq (subcubeParallelVec s d hsd hm B K
    w) * g (I ∩ zSet w).card) = ∑ Z ∈ (Finset.univ : Finset (Fin m)).powerset, (∑ w ∈
    Finset.univ.filter (fun w ↦ zSet w = Z), Complex.normSq (subcubeParallelVec s d hsd hm B K
    w)) * g (I ∩ Z).card := by
    have hmaps : ∀ w ∈ (Finset.univ : Finset (Fin (2 ^ ((n + 1) * m)))), zSet w ∈ (Finset.univ :
      Finset (Fin m)).powerset := fun w _ ↦ Finset.mem_powerset.mpr (Finset.subset_univ _)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]; refine Finset.sum_congr rfl fun Z _ ↦ ?_
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [(Finset.mem_filter.mp hw).2]
  rw [hfiber]
  have hZ_eval (J : Finset (Fin m)) (hJI : J ⊆ I) : (∑ w ∈ Finset.univ.filter (fun w ↦ zSet w =
    (Finset.univ \ I) ∪ J), Complex.normSq (subcubeParallelVec s d hsd hm B K w)) = (1 - p) ^
    J.card * p ^ (B.card - J.card) := by
    let Z := (Finset.univ \ I) ∪ J
    let S_slot (i : Fin m) : Finset (Fin (2 ^ (n + 1))) :=
      Finset.univ.filter fun u ↦ (localMarkerReg n).extractIndex u = if i ∈ Z then 0 else 1
    have hbij : (∑ w ∈ Finset.univ.filter (fun w ↦ zSet w = Z), Complex.normSq (subcubeParallelVec
      s d hsd hm B K w)) = ∑ f ∈ Fintype.piFinset S_slot, ∏ i : Fin m, Complex.normSq (ψ i (f
      i)) := by
      refine Finset.sum_bij (fun w _ ↦ slotsEquiv n m w) ?_ ?_ ?_ ?_
      · intro w hw; have hwZ : zSet w = Z := (Finset.mem_filter.mp hw).2
        rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        by_cases hiZ : i ∈ Z
        · have hi0 : i ∈ zSet w := hwZ ▸ hiZ; simpa [hiZ] using (Finset.mem_filter.mp hi0).2
        · have hi_n0 : i ∉ zSet w := hwZ ▸ hiZ
          have hne0 : (localMarkerReg n).extractIndex (slotsEquiv n m w i) ≠ 0 :=
            fun h0 ↦ hi_n0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
          simp only [hiZ, ↓reduceIte]
          generalize (localMarkerReg n).extractIndex (slotsEquiv n m w i) = b at hne0 ⊢; fin_cases b
          · exact (hne0 rfl).elim
          · rfl
      · intro w₁ _ w₂ _ heq; exact (slotsEquiv n m).injective heq
      · intro f hf; refine ⟨(slotsEquiv n m).symm f, ?_, (slotsEquiv n m).apply_symm_apply f⟩
        rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        ext i; have hfi := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hf i)).2
        have hslot_f : (localSlotReg n m i).extractIndex ((slotsEquiv n m).symm f) = f i := by
          rw [← slotsEquiv_apply, (slotsEquiv n m).apply_symm_apply]
        simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and, hslot_f]
        by_cases hiZ : i ∈ Z
        · simp [hiZ] at hfi; simp [hiZ, hfi]
        · simp [hiZ] at hfi; simp [hiZ, hfi]
      · intro w _; simp [subcubeParallelVec, map_prod, ψ]
    rw [hbij, ← Finset.prod_univ_sum S_slot (fun i u ↦ Complex.normSq (ψ i u))]
    have hslot_val (i : Fin m) : (∑ u ∈ S_slot i, Complex.normSq (ψ i u)) = if i ∉ I then 1 else
      if i ∈ J then 1 - p else p := by
      by_cases hiI : i ∈ I
      · obtain ⟨y, hyB, rfl⟩ := Finset.mem_image.mp hiI
        have hq_eq : finCongr hm (slotOf y) = (subcubeSplitEquiv s d hsd y).2 := (by simp [slotOf])
        have hsl_card : (subcubeSlice s d hsd B (finCongr hm (slotOf y))).card = 1 := by
          rw [hq_eq, card_subcubeSlice_eq_one_of_injOn hsd hcf hyB, Finset.card_singleton]
        have hr1 : 1 ≤ (subcubeSlice s d hsd B (finCongr hm (slotOf y))).card := (by omega)
        have hrN : (subcubeSlice s d hsd B (finCongr hm (slotOf y))).card ≤ 2 ^ s :=
          hsl_card.le.trans Nat.one_le_two_pow
        by_cases hiJ : slotOf y ∈ J
        · have hiZ : slotOf y ∈ Z := Finset.mem_union_right _ hiJ
          simp only [hiI, not_true_eq_false, ↓reduceIte, hiJ, S_slot, hiZ]
          rw [subSlotPairVec_normSq_sum_filter hsd _ _ K 0,
            sum_normSq_slotFinalVec_marker_zero _ hr1 hrN K, hsl_card]
        · have hiZ : slotOf y ∉ Z := (by simp [Z, hiI, hiJ])
          simp only [hiI, not_true_eq_false, ↓reduceIte, hiJ, S_slot, hiZ]
          rw [subSlotPairVec_normSq_sum_filter hsd _ _ K 1,
            sum_normSq_slotFinalVec_marker_one _ hr1 hrN K, hsl_card]
      · have hiZ : i ∈ Z := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiI⟩)
        simp only [hiI, not_false_eq_true, ↓reduceIte, S_slot, hiZ]
        have h1_zero : (∑ u : Fin (2 ^ (n + 1)) with (localMarkerReg n).extractIndex u = 1,
            Complex.normSq (ψ i u)) = 0 := by
          rw [subSlotPairVec_normSq_sum_filter hsd _ _ K 1, hempty_slice i hiI]
          refine Finset.sum_eq_zero fun v hv ↦ ?_
          rw [slotFinalVec_eq_zero_of_marker_one_of_not_mem (Finset.mem_filter.mp hv).2
            (Finset.notMem_empty _), map_zero]
        have htot := subSlotPairVec_normSq_sum_univ hsd
          (subcubeSlice s d hsd B (finCongr hm i)) (finCongr hm i) K
        have hpart : (∑ u : Fin (2 ^ (n + 1)), Complex.normSq (ψ i u)) = (∑ u : Fin (2 ^ (n + 1))
          with (localMarkerReg n).extractIndex u = 0, Complex.normSq (ψ i u)) + (∑ u : Fin (2 ^
          (n + 1)) with (localMarkerReg n).extractIndex u = 1, Complex.normSq (ψ i u)) := by
          have hunion : (Finset.univ : Finset (Fin (2 ^ (n + 1)))) =
              (Finset.univ.filter fun u ↦ (localMarkerReg n).extractIndex u = 0) ∪
                (Finset.univ.filter fun u ↦ (localMarkerReg n).extractIndex u = 1) := by
            ext u
            simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
            generalize (localMarkerReg n).extractIndex u = b; fin_cases b <;> simp
          have hdisj : Disjoint (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦ (localMarkerReg
            n).extractIndex u = 0) (Finset.univ.filter fun u : Fin (2 ^ (n + 1)) ↦ (localMarkerReg
            n).extractIndex u = 1) := by
            rw [Finset.disjoint_filter]; intro _ _ h0 h1; exact zero_ne_one (h0.symm.trans h1)
          conv_lhs => rw [hunion]
          exact Finset.sum_union hdisj
        linarith
    simp_rw [hslot_val]
    have hsplit_univ : (Finset.univ : Finset (Fin m)) = (Finset.univ \ I) ∪ I :=
      (Finset.sdiff_union_of_subset (Finset.subset_univ I)).symm
    have hdisj1 : Disjoint (Finset.univ \ I) I := Finset.sdiff_disjoint
    rw [hsplit_univ, Finset.prod_union hdisj1]
    have hp_out : (∏ i ∈ Finset.univ \ I,
        if i ∉ I then (1 : ℝ) else if i ∈ J then 1 - p else p) = 1 :=
      Finset.prod_eq_one fun i hi ↦ by simp [(Finset.mem_sdiff.mp hi).2]
    rw [hp_out, one_mul]; have hsplit_I : I = J ∪ (I \ J) := (Finset.union_sdiff_of_subset hJI).symm
    have hdisj2 : Disjoint J (I \ J) := disjoint_sdiff_self_right
    have hprod_I : (∏ i ∈ I, if i ∉ I then (1 : ℝ) else if i ∈ J then 1 - p else p) = (∏ i ∈ J, if
      i ∉ I then (1 : ℝ) else if i ∈ J then 1 - p else p) * (∏ i ∈ I \ J, if i ∉ I then (1 : ℝ)
      else if i ∈ J then 1 - p else p) := by
      rw [← Finset.prod_union hdisj2, ← hsplit_I]
    rw [hprod_I]; have hp_J : (∏ i ∈ J, if i ∉ I then (1 : ℝ) else if i ∈ J then 1 - p else p) =
        (1 - p) ^ J.card := by
      calc (∏ i ∈ J, if i ∉ I then (1 : ℝ) else if i ∈ J then 1 - p else p)
          = ∏ _i ∈ J, (1 - p) := Finset.prod_congr rfl fun i hi ↦ by simp [hJI hi, hi]
        _ = (1 - p) ^ J.card := by rw [Finset.prod_const]
    have hp_sdiff : (∏ i ∈ I \ J, if i ∉ I then (1 : ℝ) else if i ∈ J then 1 - p else p) =
        p ^ (B.card - J.card) := by
      calc (∏ i ∈ I \ J, if i ∉ I then (1 : ℝ) else if i ∈ J then 1 - p else p)
          = ∏ _i ∈ I \ J, p := Finset.prod_congr rfl fun i hi ↦ by
              have hmem := Finset.mem_sdiff.mp hi; simp [hmem.1, hmem.2]
        _ = p ^ (B.card - J.card) := by
            rw [Finset.prod_const, Finset.card_sdiff_of_subset hJI, hI_card]
    rw [hp_J, hp_sdiff]
  have hsum_I : (∑ Z ∈ (Finset.univ : Finset (Fin m)).powerset, (∑ w ∈ Finset.univ.filter (fun w ↦
    zSet w = Z), Complex.normSq (subcubeParallelVec s d hsd hm B K w)) * g (I ∩ Z).card) = ∑ J ∈
    I.powerset, (1 - p) ^ J.card * p ^ (B.card - J.card) * g J.card := by
    let liftJ (J : Finset (Fin m)) : Finset (Fin m) := (Finset.univ \ I) ∪ J
    have hsub_pow : I.powerset.image liftJ ⊆ (Finset.univ : Finset (Fin m)).powerset := by
      intro Z hZ; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    have hrest_zero : ∀ Z ∈ (Finset.univ : Finset (Fin m)).powerset, Z ∉ I.powerset.image liftJ →
        (∑ w ∈ Finset.univ.filter (fun w ↦ zSet w = Z),
          Complex.normSq (subcubeParallelVec s d hsd hm B K w)) * g (I ∩ Z).card = 0 := by
      intro Z _ hnot
      have hnsub : ¬ (Finset.univ \ I ⊆ Z) := by
        intro hsub; apply hnot; rw [Finset.mem_image]
        refine ⟨I ∩ Z, Finset.mem_powerset.mpr Finset.inter_subset_left, ?_⟩
        ext i
        simp only [liftJ, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_inter]
        by_cases hiI : i ∈ I
        · simp [hiI]
        · exact ⟨fun h ↦ hsub (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiI⟩), fun _ ↦ Or.inl hiI⟩
      have hw0 : (∑ w ∈ Finset.univ.filter (fun w ↦ zSet w = Z),
          Complex.normSq (subcubeParallelVec s d hsd hm B K w)) = 0 := by
        refine Finset.sum_eq_zero fun w hw ↦ ?_
        have hwZ : zSet w = Z := (Finset.mem_filter.mp hw).2
        rw [hzero_out w (hwZ.symm ▸ hnsub), map_zero]
      rw [hw0, zero_mul]
    rw [← Finset.sum_subset hsub_pow hrest_zero]
    have hinj_lift : Set.InjOn liftJ (I.powerset : Set (Finset (Fin m))) := by
      intro J₁ hJ₁ J₂ hJ₂ heq; have h1 : J₁ ⊆ I := Finset.mem_powerset.mp hJ₁
      have h2 : J₂ ⊆ I := Finset.mem_powerset.mp hJ₂; ext i; constructor
      · intro hi; have hmem : i ∈ liftJ J₂ := heq ▸ Finset.mem_union_right _ hi
        rcases Finset.mem_union.mp hmem with hout | hin
        · exact ((Finset.mem_sdiff.mp hout).2 (h1 hi)).elim
        · exact hin
      · intro hi; have hmem : i ∈ liftJ J₁ := heq.symm ▸ Finset.mem_union_right _ hi
        rcases Finset.mem_union.mp hmem with hout | hin
        · exact ((Finset.mem_sdiff.mp hout).2 (h2 hi)).elim
        · exact hin
    rw [Finset.sum_image hinj_lift]; refine Finset.sum_congr rfl fun J hJ ↦ ?_
    have hJI : J ⊆ I := Finset.mem_powerset.mp hJ
    have hinter_eq : I ∩ liftJ J = J := by
      ext i
      simp only [liftJ, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      by_cases hiI : i ∈ I
      · simp [hiI]
      · have hiJ : i ∉ J := fun h ↦ hiI (hJI h); simp [hiI, hiJ]
    rw [hinter_eq, hZ_eval J hJI]
  rw [hsum_I]; have hpow_part : I.powerset =
      (Finset.range (B.card + 1)).biUnion (fun j ↦ I.powersetCard j) := by
    ext J
    simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · intro hJI
      exact ⟨J.card, Nat.lt_succ_of_le ((Finset.card_le_card hJI).trans_eq hI_card), hJI, rfl⟩
    · rintro ⟨_, _, hJI, _⟩
      exact hJI
  have hdisj_card : Set.PairwiseDisjoint (↑(Finset.range (B.card + 1)))
      (fun j ↦ I.powersetCard j) := by
    intro j₁ _ j₂ _ hne; change Disjoint _ _; rw [Finset.disjoint_left]; intro J h1 h2
    exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
  rw [hpow_part, Finset.sum_biUnion hdisj_card]; refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hconst : ∀ J ∈ I.powersetCard j, (1 - p) ^ J.card * p ^ (B.card - J.card) * g J.card =
        (1 - p) ^ j * p ^ (B.card - j) * g j :=
    fun J hJ ↦ by rw [(Finset.mem_powersetCard.mp hJ).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, hI_card,
    nsmul_eq_mul]; ring
/- ## 5. `fuel = 0` `Stage1EigLock` Finisher & `(m, 2)` Pointwise Wrapper -/
theorem wp_stagesFrom_ge_pub {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ GroverSol.groverGrid)
    (hk_grid : k ∈ GroverSol.groverGrid) (hk_lt : k < 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k →
      GroverSol.validObs (Var := Var) n m k S j ≤
        wp ((GroverSol.Stage1.stagesFrom res n m k hm_grid hk_grid j).compile QProg.qAssign
            (GroverSol.groverParallelMarkingOracle m S))
          (GroverSol.validObs n m k S k)
  | 0, j, hd, _ => by
      have hjeq : j = k := by omega
      subst hjeq
      rw [GroverSol.Stage1.stagesFrom]; simp
  | d + 1, j, hd, _ => by
      have hj : j < k := by omega
      rw [GroverSol.Stage1.stagesFrom, dite_eq_left hj]
      dsimp only [OracleDynamicCircuit.compile]; rw [wp_qSeq]
      have hih := wp_stagesFrom_ge_pub res hm_grid hk_grid hk_lt hcard d (j + 1)
        (by omega) (by omega)
      have hstage : GroverSol.validObs (Var := Var) n m k S j ≤
          wp ((GroverSol.Stage1.stageDispatch res n m k hm_grid hk_grid ⟨j, hj⟩).compile
              QProg.qAssign (GroverSol.groverParallelMarkingOracle m S))
            (GroverSol.validObs n m k S (j + 1)) := by
        unfold GroverSol.Stage1.stageDispatch
        by_cases hn200 : 200 ≤ n
        · rw [dite_eq_left hn200]
          exact (GroverSol.eigLockStage_wp_and_active res hm_grid hk_grid hn200 hcard
            ⟨j, hj⟩).1
        · rw [dite_eq_right hn200]
          exact GroverSol.wp_naiveStage_ge res
            (GroverSol.one_le_of_mem_groverGrid hm_grid) hk_lt hcard ⟨j, hj⟩
      exact hstage.trans (wp_mono _ hih)
/-- Archive index `μ_T: Fin (2 ^ (k * n))` placing `T.toList` in slots `0.. T.card - 1` and
  `0`
  in remaining slots. -/
noncomputable def prefixArchiveIdx (n k : ℕ) (T : Finset (Fin (2 ^ n))) : Fin (2 ^ (k * n)) :=
  (GroverSol.addrEquiv n k).symm fun i : Fin k ↦
    if h : i.val < T.toList.length then T.toList[i.val] else 0
theorem memPrefixValid_prefixArchiveIdx {n k : ℕ} {S T : Finset (Fin (2 ^ n))} (hS : S.card = k)
    (hTS : T ⊆ S) : GroverSol.MemPrefixValid S T.card (prefixArchiveIdx n k T) := by
  have hlen : T.toList.length = T.card := Finset.length_toList T
  have hcard_le : T.card ≤ k := hS ▸ Finset.card_le_card hTS
  have hslot (i : Fin k) : GroverSol.addrEquiv n k (prefixArchiveIdx n k T) i = if h : i.val
    < T.toList.length then T.toList[i.val] else 0 := by
    dsimp only [prefixArchiveIdx]; rw [Equiv.apply_symm_apply]
  refine ⟨hcard_le, fun i hi ↦ ?_, fun i j hi hj hij ↦ ?_, fun i hi ↦ ?_⟩
  · have hi' : i.val < T.toList.length := hlen ▸ hi; rw [hslot i, dite_eq_left hi']
    exact hTS (Finset.mem_toList.mp (List.getElem_mem hi'))
  · have hi' : i.val < T.toList.length := hlen ▸ hi; have hj' : j.val < T.toList.length := hlen ▸ hj
    rw [hslot i, dite_eq_left hi', hslot j, dite_eq_left hj'] at hij
    have hfin : (⟨i.val, hi'⟩ : Fin T.toList.length) = ⟨j.val, hj'⟩ :=
      (List.nodup_iff_injective_getElem.mp (Finset.nodup_toList T)) hij
    exact Fin.ext (by simpa using congrArg Fin.val hfin)
  · have hni : ¬ i.val < T.toList.length := (by omega); rw [hslot i, dite_eq_right hni]
/-- `fuel = 0` circuit running `Stage1.stagesFrom` from `j = T.card` (`0` queries when
  `T.card = k`) inside `findAllQubits n m k ≤ Q` qubits. -/
noncomputable def stage2Fuel0Circuit {Var : Type} (res : Var) (n m k Q : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hQ : findAllQubits n m k ≤ Q) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  if T.card = k then
    let memK : QRegister (n * k) Q := QRegister.block 0 (n * k)
      (by unfold findAllQubits at hQ; omega)
    setClassicalValCircuit res memK (encodeFinsetVal n k T)
  else
    let subS1 : QRegister (m * (n + 1) + k * n) Q :=
      QRegister.block 0 (m * (n + 1) + k * n)
        (by unfold findAllQubits at hQ; nlinarith)
    let zT : Fin (2 ^ (m * (n + 1) + k * n)) :=
      (GroverSol.lowHighEquiv (m * (n + 1)) (k * n)).symm (0, prefixArchiveIdx n k T)
    let localS1 : OracleDynamicCircuit (Unitary (2 ^ (m * (n + 1) + k * n))) Var
        (m * (n + 1) + k * n) ((n + 1) * m) :=
      .seq (.step (GroverSol.phaseTag (permutationUnitary (Equiv.swap 0 zT))))
        (.seq (GroverSol.Stage1.stagesFrom res n m k hm_grid hk_grid T.card)
          (.measure res (GroverSol.highBlock (m * (n + 1)) (k * n))))
    .seq (resetAllCircuit res) (embedOracleCirc subS1 localS1)
theorem zeroStepCost_stage2Fuel0Circuit {Var : Type} (res : Var) (n m k Q : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hQ : findAllQubits n m k ≤ Q) (T : Finset (Fin (2 ^ n))) :
    ZeroStepCost (stage2Fuel0Circuit (Var := Var) res n m k Q hm_grid hk_grid hQ T) := by
  dsimp only [stage2Fuel0Circuit]; split_ifs
  · exact zeroStepCost_setClassicalValCircuit _ _ _
  · exact ⟨zeroStepCost_resetAllCircuit res, zeroStepCost_embedOracleCirc _ _⟩
theorem stageCostReal_le_818309887 {n m k i : ℕ} (hn : 600 ≤ n) (hm_grid : m ∈
    GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid) (hi1 : 1 ≤ i) (hik : i ≤
    k) : 0 ≤ GroverSol.stageCostReal n m i ∧ GroverSol.stageCostReal n m i ≤ (818309887
    / 10 ^ 9 : ℝ) * (1 / √(i : ℝ)) * ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ))) := by
  obtain ⟨hnn, hlin⟩ := GroverSol.stageCostReal_le_linear_S0 hn hm_grid hk_grid hi1 hik
  refine ⟨hnn, ?_⟩
  have hm1 : 1 ≤ m := GroverSol.one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := GroverSol.le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := GroverSol.le_1024_of_mem_groverGrid hk_grid
  have hi_hi : i ≤ 1024 := hik.trans hk_hi
  have hpi_lo : (31415926535 / 10 ^ 10 : ℝ) < π := (by linarith [Real.pi_gt_d20])
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hc_gap : 1 / 2 + 1 / π + (5 / 10 ^ 10 : ℝ) ≤ (818309887 / 10 ^ 9 : ℝ) := by
    have hinv : 1 / π ≤ (10 ^ 10 / 31415926535 : ℝ) := by
      rw [div_le_div_iff₀ hpi_pos (by norm_num)]; linarith
    linarith
  let S_mi : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (i : ℝ)))
  have hmi_pos : (0 : ℝ) < (m : ℝ) * (i : ℝ) := (by positivity)
  have hmi_le : (m : ℝ) * (i : ℝ) ≤ (2 ^ 20 : ℝ) := by
    have hnat : m * i ≤ 1024 * 1024 := Nat.mul_le_mul hm_hi hi_hi
    calc (m : ℝ) * (i : ℝ) = ((m * i : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((1024 * 1024 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2 ^ 20 : ℝ) := by norm_num
  have h2n_ge : (2 ^ 100 : ℝ) ≤ (2 ^ n : ℝ) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hS_sq_ge : ((2 ^ 40 : ℝ)) ^ 2 ≤ S_mi ^ 2 := by
    rw [Real.sq_sqrt (by positivity), le_div_iff₀ hmi_pos]
    calc ((2 ^ 40 : ℝ)) ^ 2 * ((m : ℝ) * (i : ℝ))
        ≤ ((2 ^ 40 : ℝ)) ^ 2 * (2 ^ 20 : ℝ) := mul_le_mul_of_nonneg_left hmi_le (by positivity)
      _ = (2 ^ 100 : ℝ) := by norm_num
      _ ≤ (2 ^ n : ℝ) := h2n_ge
  have hS_ge : (2 ^ 40 : ℝ) ≤ S_mi := by
    nlinarith [Real.sqrt_nonneg ((2 ^ n : ℝ) / ((m : ℝ) * (i : ℝ)))]
  have h5_le : (5 : ℝ) ≤ (5 / 10 ^ 10 : ℝ) * ((π / 4) * S_mi) := by
    have hbig : (10 ^ 12 : ℝ) ≤ (2 ^ 40 : ℝ) := (by norm_num); nlinarith [Real.pi_gt_three]
  have hS_split : (1 / √(i : ℝ)) * √((2 ^ n : ℝ) / (m : ℝ)) = S_mi := by
    dsimp only [S_mi]; rw [one_div_mul_eq_div, ← Real.sqrt_div (by positivity), div_div]
  calc GroverSol.stageCostReal n m i ≤ (π / 8 + 1 / 4) * S_mi + 5 := hlin
    _ ≤ (1 / 2 + 1 / π) * ((π / 4) * S_mi) + (5 / 10 ^ 10 : ℝ) * ((π / 4) * S_mi) := by
        have hid : (π / 8 + 1 / 4) * S_mi = (1 / 2 + 1 / π) * ((π / 4) * S_mi) := by
          field_simp [hpi_pos.ne']; ring
        linarith
    _ = (1 / 2 + 1 / π + (5 / 10 ^ 10 : ℝ)) * ((π / 4) * S_mi) := by ring
    _ ≤ (818309887 / 10 ^ 9 : ℝ) * ((π / 4) * S_mi) :=
        mul_le_mul_of_nonneg_right hc_gap (by positivity)
    _ = (818309887 / 10 ^ 9 : ℝ) * (1 / √(i : ℝ)) * ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ))) := by
        rw [← hS_split]; ring
/-- `fuel = 0` soundness: recovers `S` with probability `1` from any `T ⊆ S` and incoming
  `Ξ` in `≤ (818309887 / 10 ^ 9) * groverHarmonicSqrtSum (S \ T).card * ((π / 4) * √(2 ^ n /
  m))`
  expected parallel oracle calls for all `600 ≤ n`. -/
theorem stage2Fuel0_transition {Var : Type} [DecidableEq Var] (res : Var) {n m k Q : ℕ} (hn : 600
    ≤ n) (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid) (hQ :
    findAllQubits n m k ≤ Q) {S T : Finset (Fin (2 ^ n))} (hS : S.card = k) (hTS : T ⊆ S) (Ξ :
    CQState (Store Var) (2 ^ Q)) :
    let prog := (stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T).compile QProg.qAssign
      (parallelMarkingOracle m S)
    let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
    𝔼[(interp prog).toStateFun Ξ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Ξ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Ξ ≤
      stateMass Ξ * ENNReal.ofReal ((818309887 / 10 ^ 9 : ℝ) *
      GroverSol.groverHarmonicSqrtSum (S \ T).card * unit) := by
  intro prog unit
  have hO_eq : parallelMarkingOracle m S = GroverSol.groverParallelMarkingOracle m S := rfl
  have hdec_eq : decodeTargetsLocal n k = GroverSol.decodeTargets n k := rfl
  have horacle : IsRealMatrix (parallelMarkingOracle m S).1 := isRealMatrix_parallelMarkingOracle S
  dsimp only [prog, stage2Fuel0Circuit]; split_ifs with hTcard
  · have hTeq : T = S := Finset.eq_of_subset_of_card_le hTS (by omega); subst hTeq
    have htr := setClassicalValCircuit_transition res
      (QRegister.block 0 (n * k) (by unfold findAllQubits at hQ; omega))
      (encodeFinsetVal n k T) horacle
      (P := fun τ ↦ decodeTargetsLocal n k (τ res) = T)
      (fun σ ↦ by simp [Store.subst, decodeTargetsLocal_encodeFinsetVal hS]) Ξ
    refine ⟨htr.1, ?_⟩
    rw [htr.2]; exact zero_le
  · let subS1 : QRegister (m * (n + 1) + k * n) Q :=
      QRegister.block 0 (m * (n + 1) + k * n) (by unfold findAllQubits at hQ; nlinarith)
    let zT : Fin (2 ^ (m * (n + 1) + k * n)) :=
      (GroverSol.lowHighEquiv (m * (n + 1)) (k * n)).symm (0, prefixArchiveIdx n k T)
    let initP : QProg Var (2 ^ (m * (n + 1) + k * n)) :=
      QProg.qAssign (GroverSol.phaseTag (permutationUnitary (Equiv.swap 0 zT)))
    let stagesP : QProg Var (2 ^ (m * (n + 1) + k * n)) :=
      (GroverSol.Stage1.stagesFrom res n m k hm_grid hk_grid T.card).compile QProg.qAssign
        (GroverSol.groverParallelMarkingOracle m S)
    let measP : QProg Var (2 ^ (m * (n + 1) + k * n)) :=
      QProg.measureRegister res (GroverSol.highBlock (m * (n + 1)) (k * n))
    let localS1 : OracleDynamicCircuit (Unitary (2 ^ (m * (n + 1) + k * n))) Var (m * (n + 1) +
      k * n) ((n + 1) * m) := .seq (.step (GroverSol.phaseTag (permutationUnitary (Equiv.swap
      0 zT)))) (.seq (GroverSol.Stage1.stagesFrom res n m k hm_grid hk_grid T.card) (.measure
      res (GroverSol.highBlock (m * (n + 1)) (k * n))))
    have hrst := resetAllCircuit_transition res horacle Ξ
    set Ξ₁ := (interp ((resetAllCircuit res).compile QProg.qAssign
      (parallelMarkingOracle m S))).toStateFun Ξ
    let γ₀ := marginalState subS1 Ξ₁
    have hγ₀_supp : SupportedOn (· = (0 : Fin (2 ^ (m * (n + 1) + k * n)))) γ₀ :=
      supportedOn_zero_marginalState subS1 hrst.2.2.2
    let γ₁ := (interp initP).toStateFun γ₀; have hvalid_zT : GroverSol.MemPrefixValid S T.card
        (GroverSol.lowHighEquiv (m * (n + 1)) (k * n) zT).2 := by
      simp only [zT, Equiv.apply_symm_apply]; exact memPrefixValid_prefixArchiveIdx hS hTS
    have htr1 : γ₁.trace = γ₀.trace := by
      dsimp only [γ₁, initP]
      rw [interp_qAssign, QMonad.Q.toStateFun_qAssign, CQState.trace_qAssign]
    have hV_γ₁ : 𝔼[γ₁, GroverSol.validObs n m k S T.card] = γ₁.trace := by
      rw [htr1, ← wp_expectation_eq]; have hexp := expect_of_supportedOn_zero hγ₀_supp
        (Θ := wp initP (GroverSol.validObs n m k S T.card)) (c := 1) fun σ ↦ by
          dsimp only [initP]
          set U := (permutationUnitary (Equiv.swap (0 : Fin (2 ^ (m * (n + 1) + k * n))) zT)).1
          have hwp_mat : ((wp (QProg.qAssign (GroverSol.phaseTag (permutationUnitary
            (Equiv.swap 0 zT)))) (GroverSol.validObs n m k S T.card) σ).1).mat = Uᴴ *
            Matrix.diagonal (fun z ↦ (GroverSol.validInd n m k S T.card z : ℂ)) * U := by
            rw [wp_qAssign, GroverSol.wp_phaseTag, ← HermitianMat.val_eq_coe,
              qhlQAssign_val, GroverSol.validObs,
              GroverSol.realDiagObs_mat]
          rw [hwp_mat, Matrix.mul_apply, Finset.sum_eq_single zT]
          · rw [Matrix.mul_apply, Finset.sum_eq_single zT]
            · have hU0 : U zT 0 = 1 := (by simp [U, GroverSol.permutationUnitary_apply])
              rw [Matrix.conjTranspose_apply, hU0, star_one, one_mul, mul_one,
                Matrix.diagonal_apply_eq, GroverSol.validInd, ite_eq_left hvalid_zT,
                Complex.ofReal_one]
            · intro x _ hne; simp [Matrix.diagonal_apply_ne _ hne]
            · intro habs; exact (habs (Finset.mem_univ zT)).elim
          · intro z _ hne
            have hUz : U z 0 = 0 := (by simp [U, GroverSol.permutationUnitary_apply, hne])
            rw [hUz, mul_zero]
          · intro habs; exact (habs (Finset.mem_univ zT)).elim
      linarith
    have hk_lt : k < 2 ^ n := by
      have hk1024 := GroverSol.le_1024_of_mem_groverGrid hk_grid
      calc k ≤ 1024 := hk1024
        _ < 2 ^ 20 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have hT_le : T.card ≤ k := hS ▸ Finset.card_le_card hTS
    have hwp_st := wp_stagesFrom_ge_pub (Var := Var) res hm_grid hk_grid hk_lt hS
      (k - T.card) T.card rfl hT_le
    have hstep_V := GroverSol.validState_step hV_γ₁ hwp_st
    let γ₂ := (interp stagesP).toStateFun γ₁
    have hwp_meas := GroverSol.validObs_le_wp_measure_decodeTargets (Var := Var) (m := m)
      res hS
    let postLocal : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
      liftPureProp (fun τ ↦ GroverSol.decodeTargets n k (τ res) = S)
    have hlift_post : liftAssertion subS1 postLocal = liftPureProp (d := 2 ^ Q) (fun τ ↦
      decodeTargetsLocal n k (τ res) = S) := by
      dsimp only [postLocal]; rw [← hdec_eq]; exact liftAssertion_liftPureProp subS1 _
    have hm_γ₁ : stateMass γ₁ = stateMass Ξ := by
      dsimp only [γ₁, initP, γ₀]
      rw [interp_qAssign, QMonad.Q.toStateFun_qAssign, stateMass_qAssign, stateMass_marginalState,
        hrst.2.2.1]
    have hcorr_eq : 𝔼[(interp (OracleDynamicCircuit.compile QProg.qAssign (parallelMarkingOracle m
      S) (.seq (resetAllCircuit res) (embedOracleCirc subS1 localS1)))).toStateFun Ξ, liftPureProp
      (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace := by
      simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
      change 𝔼[(interp ((embedOracleCirc subS1 localS1).compile QProg.qAssign
        (parallelMarkingOracle m S))).toStateFun Ξ₁, _] = Ξ.trace
      rw [← hlift_post, expect_liftAssertion_eq_marginalState,
        marginalState_interp_embedOracleCirc, hO_eq]
      dsimp only [localS1, OracleDynamicCircuit.compile]
      rw [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSeq, QMonad.Q.toStateFun_bind]
      change 𝔼[(interp measP).toStateFun γ₂, postLocal] = Ξ.trace
      have hge : (γ₂.trace : ℝ) ≤ 𝔼[(interp measP).toStateFun γ₂, postLocal] := by
        rw [← hstep_V.1, ← wp_expectation_eq measP γ₂ postLocal]; exact expect_mono le_rfl hwp_meas
      have hle1 : 𝔼[(interp measP).toStateFun γ₂, postLocal] ≤
          ((interp measP).toStateFun γ₂).trace := by
        rw [← expect_top ((interp measP).toStateFun γ₂)]; exact expect_mono le_rfl le_top
      have hle2 : (((interp measP).toStateFun γ₂).trace : ℝ) ≤ γ₂.trace :=
        NNReal.coe_le_coe.mpr ((interp measP).trace_toStateFun_le γ₂)
      have htr_γ₂ : (γ₂.trace : ℝ) = Ξ.trace := by
        have hge_γ₂ : (γ₁.trace : ℝ) ≤ γ₂.trace := by
          rw [← hstep_V.1, ← hV_γ₁, ← wp_expectation_eq stagesP γ₁ (GroverSol.validObs n m k
            S k)]; exact expect_mono le_rfl hwp_st
        have hle_γ₂ : (γ₂.trace : ℝ) ≤ γ₁.trace :=
          NNReal.coe_le_coe.mpr ((interp stagesP).trace_toStateFun_le γ₁)
        have htr_γ₀ : (γ₀.trace : ℝ) = Ξ.trace :=
          congrArg NNReal.toReal ((trace_marginalState subS1 Ξ₁).trans hrst.2.1)
        have htr1_r : (γ₁.trace : ℝ) = γ₀.trace := congrArg NNReal.toReal htr1
        linarith
      linarith
    refine ⟨hcorr_eq, ?_⟩
    simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]; rw [hrst.1, zero_add]
    have horacleG : GroverSol.IsRealMatrix (GroverSol.groverParallelMarkingOracle m S).1
      := GroverSol.isRealMatrix_groverParallelMarkingOracle m S
    have hcost_emb := expectedCost_embedOracleCirc_le subS1 localS1 horacleG Ξ₁; rw [hO_eq]
    refine hcost_emb.trans ?_
    dsimp only [localS1, OracleDynamicCircuit.compile]; rw [expectedCost_qSeq, expectedCost_qSeq]
    have hc_init : expectedCost (CostModel.ofEmbeddedOracle
        (GroverSol.groverParallelMarkingOracle m S)) initP γ₀ = 0 := by
      dsimp only [initP]
      rw [expectedCost_qAssign, GroverSol.ofEmbeddedOracle_unitaryCost_phaseTag_eq_zero
        horacleG]; simp
    have hc_meas : expectedCost (CostModel.ofEmbeddedOracle
        (GroverSol.groverParallelMarkingOracle m S)) measP γ₂ = 0 := by
      dsimp only [measP, QProg.measureRegister]; simp [CostModel.ofEmbeddedOracle]
    change expectedCost _ initP γ₀ + (expectedCost _ stagesP γ₁ + expectedCost _ measP γ₂) ≤ _
    rw [hc_init, hc_meas, zero_add, add_zero]
    have hc_st := GroverSol.Stage1.expectedCost_stagesFrom_eigLock_le res hm_grid hk_grid
      (by omega : 200 ≤ n) hS (k - T.card) T.card rfl hT_le γ₁ hV_γ₁
    rw [hm_γ₁] at hc_st
    have hsdiff_card : k - T.card = (S \ T).card := by
      have hadd := Finset.card_sdiff_add_card_eq_card hTS; omega
    rw [hsdiff_card] at hc_st; refine hc_st.trans (mul_le_mul_right ?_ (stateMass Ξ))
    have hsum_le : (∑ r ∈ Finset.Icc 1 (S \ T).card, ENNReal.ofReal (GroverSol.stageCostReal
      n m r)) ≤ ENNReal.ofReal ((818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum (S
      \ T).card * unit) := by
      have hnn_term : ∀ r ∈ Finset.Icc 1 (S \ T).card, 0 ≤ GroverSol.stageCostReal n m r := by
        intro r hr; rw [Finset.mem_Icc] at hr
        exact (stageCostReal_le_818309887 hn hm_grid hk_grid hr.1
          (hr.2.trans (hsdiff_card ▸ Nat.sub_le k T.card))).1
      rw [← ENNReal.ofReal_sum_of_nonneg hnn_term]; apply ENNReal.ofReal_le_ofReal
      rw [GroverSol.groverHarmonicSqrtSum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun r hr ↦ ?_
      rw [Finset.mem_Icc] at hr
      exact (stageCostReal_le_818309887 hn hm_grid hk_grid hr.1
        (hr.2.trans (hsdiff_card ▸ Nat.sub_le k T.card))).2
    exact hsum_le
/-- Pointwise `∀ (S, T)` (`|S \ T| = 2`) wrapper lifting any uniform-average `(m, 2)`
  circuit
  `cAvg2` into a `Q`-qubit `r = 2` subroutine via one `GF(2 ^ n)` affine shuffle,
  `deflateCirc`, and `Stage1` `a_raw = 0` fallback (`0` extra ancilla qubits). -/
noncomputable def deflatedForallTwoFromAvgCircuit {Var : Type}
    (res : Var) (n m k Q : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hQ : findAllQubits n m k ≤ Q)
    (cAvg2 : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m 2)) Var
      (findAllQubits n m 2) ((n + 1) * m))
    (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  if hn0 : n = 0 then
    stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
  else
    let hseed : 2 * n ≤ Q := by unfold findAllQubits at hQ; exact le_trans (by nlinarith [hm2]) hQ
    let sub2 : QRegister (findAllQubits n m 2) Q :=
      QRegister.block 0 (findAllQubits n m 2)
        (by unfold findAllQubits at hQ ⊢; exact le_trans (by nlinarith [hk2]) hQ)
    let memK : QRegister (n * k) Q :=
      QRegister.block 0 (n * k) (by unfold findAllQubits at hQ; nlinarith)
    .seq (resetAllCircuit res)
      (.seq (sampleSeedCircuit res n Q ((n + 1) * m) hseed)
        (dispBits res (2 * n) 0 fun uVal ↦
          if hu : uVal < 2 ^ (2 * n) then
            let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
            if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
              stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
            else
              let perm := GF2nForallA.finAffinePerm hn0
                (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
                (GF2nForallA.seedToGFPair hn0 u).2
              .seq (resetAllCircuit res)
                (.seq (deflateCirc n m T (permOracleCirc n m perm (embedOracleCirc sub2 cAvg2)))
                  (dispBits res (2 * n) 0 fun wVal ↦
                    let R_dec :=
                      (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding
                    setClassicalValCircuit res memK (encodeFinsetVal n k (T ∪ R_dec))))
          else .skip))
theorem zeroStepCost_deflatedForallTwoFromAvgCircuit {Var : Type} (res : Var) (n m k Q : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid) (hm2 : 2 ≤
    m) (hk2 : 2 ≤ k) (hQ : findAllQubits n m k ≤ Q) (cAvg2 : OracleDynamicCircuit (Unitary (2 ^
    findAllQubits n m 2)) Var (findAllQubits n m 2) ((n + 1) * m)) (T : Finset (Fin (2 ^ n))) :
    ZeroStepCost (deflatedForallTwoFromAvgCircuit res n m k Q hm_grid hk_grid hm2 hk2 hQ cAvg2
    T) := by
  dsimp only [deflatedForallTwoFromAvgCircuit]; split_ifs with hn0
  · exact zeroStepCost_stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
  · refine ⟨zeroStepCost_resetAllCircuit res, zeroStepCost_sampleSeedCircuit _ _ _ _ _,
      zeroStepCost_dispBits res (2 * n) 0 _ fun uVal _ ↦ ?_⟩
    by_cases hu : uVal < 2 ^ (2 * n)
    · rw [dite_eq_left hu]; split_ifs with ha
      · exact zeroStepCost_stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
      · exact ⟨zeroStepCost_resetAllCircuit res, zeroStepCost_deflateCirc n m T
            (zeroStepCost_permOracleCirc n m _ (zeroStepCost_embedOracleCirc _ cAvg2)),
          zeroStepCost_dispBits res (2 * n) 0 _ fun _ _ ↦ zeroStepCost_setClassicalValCircuit _ _ _⟩
    · rw [dite_eq_right hu]
      trivial
/-- Helper: expectation distributes over `dispBits` exactly like `expectedCost_dispBits`. -/
theorem expect_dispBits {Var : Type} [DecidableEq Var] {Q w : ℕ} (oracle : Unitary (2 ^ w)) (res :
    Var) (W off : ℕ) (f : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) (Θ : CQAssertion
      (Store Var)
    (2 ^ Q)) (Δ : CQState (Store Var) (2 ^ Q)) : 𝔼[(interp ((dispBits res W off f).compile
      QProg.qAssign
    oracle)).toStateFun Δ, Θ] = ∑ v ∈ Finset.range (2 ^ W), 𝔼[(interp ((f v).compile QProg.qAssign
    oracle)).toStateFun (sliceState res off W v Δ), Θ] := by
  have hexpect_add (cond : Store Var → Prop) [DecidablePred cond] (p₁ p₂ : QProg Var (2 ^ Q)) (Γ :
    CQState (Store Var) (2 ^ Q)) : 𝔼[(interp (.qIf cond p₁ p₂)).toStateFun Γ, Θ] = 𝔼[(interp
    p₁).toStateFun (Γ.cqTrueSt cond), Θ] + 𝔼[(interp p₂).toStateFun (Γ.cqFalseSt cond), Θ] := by
    rw [← wp_expectation_eq, ← wp_expectation_eq, ← wp_expectation_eq, wp_qIf]
    rw [qcExpectEqTsumStore, qcExpectEqTsumStore, qcExpectEqTsumStore, ← (qcSummableExpectStore
      (Γ.cqTrueSt cond) (wp p₁ Θ)).tsum_add (qcSummableExpectStore (Γ.cqFalseSt cond) (wp p₂ Θ))]
    refine tsum_congr fun σ ↦ ?_
    by_cases hc : cond σ <;> simp [CQState.cqTrueSt_coe, CQState.cqFalseSt_coe, hc]
  induction W generalizing off f Δ with
  | zero => simp [dispBits, sliceState_zero]
  | succ W ih =>
      simp only [dispBits, OracleDynamicCircuit.compile_qIf]; rw [hexpect_add, ih, ih]
      simp_rw [sliceState_succ_odd, sliceState_succ_even]
      rw [pow_succ', ← sum_range_two_mul_even_odd (2 ^ W) (fun u ↦ 𝔼[(interp ((f u).compile
        QProg.qAssign oracle)).toStateFun (sliceState res off (W + 1) u Δ), Θ])]
/-- Helper: any `CQState` with `.trace = 0` is identically `0`. -/
theorem cqState_eq_zero_of_trace_eq_zero {Var : Type} {d : ℕ}
    {Γ : CQState (Store Var) d} (htr : (Γ.trace : ℝ) = 0) : Γ = 0 := by
  apply Subtype.ext; funext σ; apply Subtype.ext; apply HermitianMat.ext
  have htr_σ : (Γ.1 σ).1.trace = 0 := by
    have h0 : (Γ σ).trace = 0 :=
      nonpos_iff_eq_zero.mp ((Γ.trace_apply_le_trace σ).trans_eq (NNReal.coe_eq_zero.mp htr))
    exact NNReal.coe_eq_zero.mpr h0
  set M := (Γ.1 σ).1.mat; have hpos : M.PosSemidef := (Γ.1 σ).posSemidef_val
  have hdiag0 (z : Fin d) : M z z = 0 := by
    have hsum : ∑ i : Fin d, (M i i).re = 0 := by
      rw [HermitianMat.trace_eq_re_trace] at htr_σ; dsimp only [M]
      simpa [Matrix.trace, Complex.re_sum] using htr_σ
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ (M i i).re :=
      fun i _ ↦ (Complex.nonneg_iff.mp hpos.diag_nonneg).1
    have hre0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum z (Finset.mem_univ z)
    have him0 : (M z z).im = 0 := (Complex.nonneg_iff.mp hpos.diag_nonneg).2.symm
    exact Complex.ext hre0 him0
  ext a b
  have hdot : star (Pi.single b (1 : ℂ)) ⬝ᵥ M *ᵥ Pi.single b (1 : ℂ) = 0 := by
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hdiag0 b
  have hmv := hpos.dotProduct_mulVec_zero_iff.mp hdot
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hmv a
theorem interp_toStateFun_zero {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] (p : QProg Var d)
    : (interp p).toStateFun (0 : CQState (Store Var) d) = 0 := by
  apply cqState_eq_zero_of_trace_eq_zero
  exact NNReal.coe_eq_zero.mpr
    (nonpos_iff_eq_zero.mp (((interp p).trace_toStateFun_le 0).trans_eq CQState.trace_zero))
/-- Helper: `expectedCost` on the zero `CQState` is `0` for any compiled
  `OracleDynamicCircuit`. -/
theorem expectedCost_zero_cqState {Var : Type} [DecidableEq Var] {Q w : ℕ} (model : CostModel (2 ^
    Q)) (oracle : Unitary (2 ^ w)) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) :
    expectedCost model (c.compile QProg.qAssign oracle) (0 : CQState (Store Var) (2 ^ Q)) = 0 := by
  induction c with
  | «skip» => simp
  | «step» _ => simp
  | «oracle» _ => simp
  | «measure» _ _ => simp [QProg.measureRegister]
  | «seq» c₁ _ ih₁ ih₂ =>
      simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq, ih₁,
        interp_toStateFun_zero, ih₂, add_zero]
  | «qIf» b _ _ ih₁ ih₂ =>
      have ht0 : (0 : CQState (Store Var) (2 ^ Q)).cqTrueSt b = 0 := by
        apply Subtype.ext; funext σ; simp [CQState.cqTrueSt_coe]
      have hf0 : (0 : CQState (Store Var) (2 ^ Q)).cqFalseSt b = 0 := by
        apply Subtype.ext; funext σ; simp [CQState.cqFalseSt_coe]
      simp only [OracleDynamicCircuit.compile_qIf, cqExpectedCostIf, ht0, hf0, ih₁, ih₂, add_zero]
  | «qWhile» b body ih =>
      simp only [OracleDynamicCircuit.compile_qWhile, expectedCost_qWhile]
      have hrec (t : ℕ) : whileRecCost (expectedCost model (body.compile QProg.qAssign oracle))
        ((interp (body.compile QProg.qAssign oracle)).toStateFun) b t 0 = 0 := by
        induction t with
        | zero => simp
        | succ t iht =>
            have ht0 : (0 : CQState (Store Var) (2 ^ Q)).cqTrueSt b = 0 := by
              apply Subtype.ext; funext σ; simp [CQState.cqTrueSt_coe]
            rw [cqWhileRecCostSuc, ht0, ih, interp_toStateFun_zero, iht, add_zero]
      simp [hrec]
/-- Pointwise soundness of `deflatedForallTwoFromAvgCircuit`: wraps any `(m, 2)`
  average-cost
  circuit certified at unit cost `uAvg ≥ 0` into a pointwise `∀ (S, T)` (`|S \ T| = 2`)
  subroutine
  costing at most `(uAvg + 1 / 10 ^ 9) * ((π / 4) * √(2 ^ n / m))` for all `600 ≤ n`. -/
theorem deflatedForallTwoFromAvg_transition {Var : Type} [DecidableEq Var]
    (res : Var) {n m k Q : ℕ} (hn : 600 ≤ n)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hQ : findAllQubits n m k ≤ Q)
    (cAvg2 : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m 2)) Var
      (findAllQubits n m 2) ((n + 1) * m))
    {uAvg : ℝ} (huAvg_nn : 0 ≤ uAvg)
    (hcorr2 : ∀ B ∈ GroverSol.groverTargetSets n 2,
      (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m 2)) ≤
        wp (QProg.qSet ;;
          cAvg2.compile QProg.qAssign (GroverSol.groverParallelMarkingOracle m B))
          (liftPureProp (fun τ ↦ GroverSol.decodeTargets n 2 (τ res) = B)))
    (havg2 : GroverSol.AvgOracleCostBound (Var := Var) 2
      (fun B ↦ CostModel.ofEmbeddedOracle (GroverSol.groverParallelMarkingOracle m B))
      (fun B ↦ QProg.qSet ;; cAvg2.compile QProg.qAssign
        (GroverSol.groverParallelMarkingOracle m B))
      (uAvg * ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ)))))
    {S T : Finset (Fin (2 ^ n))} (hS : S.card = k) (hTS : T ⊆ S) (hST2 : (S \ T).card = 2)
    (Ξ : CQState (Store Var) (2 ^ Q)) :
    let prog :=
      (deflatedForallTwoFromAvgCircuit res n m k Q hm_grid hk_grid hm2 hk2 hQ cAvg2 T).compile
        QProg.qAssign (parallelMarkingOracle m S)
    let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
    𝔼[(interp prog).toStateFun Ξ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Ξ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Ξ ≤
      stateMass Ξ * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := by
  intro prog unit; have hn0 : n ≠ 0 := (by omega)
  have horacle : IsRealMatrix (parallelMarkingOracle m S).1 := isRealMatrix_parallelMarkingOracle S
  let hseed : 2 * n ≤ Q := by unfold findAllQubits at hQ; nlinarith
  let sub2 : QRegister (findAllQubits n m 2) Q :=
    QRegister.block 0 (findAllQubits n m 2) (by unfold findAllQubits at hQ ⊢; nlinarith)
  let memK : QRegister (n * k) Q :=
    QRegister.block 0 (n * k) (by unfold findAllQubits at hQ; nlinarith)
  let R := S \ T
  obtain ⟨q, hq_bound, hq_avg⟩ := havg2; dsimp only [prog, deflatedForallTwoFromAvgCircuit]
  rw [dite_eq_right hn0]; have hrst0 := resetAllCircuit_transition res horacle Ξ
  set Ξ₁ := (interp ((resetAllCircuit res).compile QProg.qAssign
    (parallelMarkingOracle m S))).toStateFun Ξ
  set Ξ₂ := (interp ((sampleSeedCircuit res n Q ((n + 1) * m) hseed).compile QProg.qAssign
    (parallelMarkingOracle m S))).toStateFun Ξ₁
  let postS : CQAssertion (Store Var) (2 ^ Q) := liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ
    res) = S)
  let modelS := CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m S)
  let branchFn (uVal : ℕ) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
    if hu : uVal < 2 ^ (2 * n) then
      let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
      if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
        stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
      else
        let perm := GF2nForallA.finAffinePerm hn0 (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1
          ha) (GF2nForallA.seedToGFPair hn0 u).2
        .seq (resetAllCircuit res)
          (.seq (deflateCirc n m T (permOracleCirc n m perm (embedOracleCirc sub2 cAvg2)))
            (dispBits res (2 * n) 0 fun wVal ↦
              let R_dec := (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding
              setClassicalValCircuit res memK (encodeFinsetVal n k (T ∪ R_dec))))
    else .skip
  have hbranch (uVal : ℕ) (hu : uVal < 2 ^ (2 * n)) :
      let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩; let Δ_sl := sliceState res 0 (2 * n) uVal Ξ₂
      𝔼[(interp ((branchFn uVal).compile QProg.qAssign (parallelMarkingOracle m S))).toStateFun
          Δ_sl, postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace ∧
        expectedCost modelS
          ((branchFn uVal).compile QProg.qAssign (parallelMarkingOracle m S)) Δ_sl ≤
          stateMass Ξ * ENNReal.ofReal ((1 / (2 ^ (2 * n) : ℝ)) *
            if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
              (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit
            else
              (q (R.map (GF2nForallA.finAffinePerm hn0
                (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
                (GF2nForallA.seedToGFPair hn0 u).2).toEmbedding) : ℝ)) := by
    intro u Δ_sl
    have htr_sl : (Δ_sl.trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
      have hs := sampleSeed_sliceState_trace res n Q ((n + 1) * m) hseed
        (parallelMarkingOracle m S) hrst0.2.2.2 hu
      rw [hrst0.2.1] at hs; exact hs
    have hmass_sl : stateMass Δ_sl = stateMass Ξ * ENNReal.ofReal (1 / (2 ^ (2 * n) : ℝ)) := by
      rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_sl, mul_comm,
        ENNReal.ofReal_mul (CQState.trace_nonneg _)]
    dsimp only [branchFn]; rw [dite_eq_left hu]
    by_cases ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0
    · rw [dite_eq_left ha, dite_eq_left ha]
      obtain ⟨hc_f0, hcost_f0⟩ := stage2Fuel0_transition res hn hm_grid hk_grid hQ hS hTS Δ_sl
      rw [hST2] at hcost_f0; refine ⟨hc_f0.trans htr_sl, hcost_f0.trans ?_⟩
      rw [hmass_sl, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    · rw [dite_eq_right ha, dite_eq_right ha]
      let perm := GF2nForallA.finAffinePerm hn0 (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
        (GF2nForallA.seedToGFPair hn0 u).2
      let B := R.map perm.toEmbedding
      have hB_mem : B ∈ GroverSol.groverTargetSets n 2 := by
        rw [GroverSol.groverTargetSets, Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, by simp [B, R, hST2]⟩
      have hrst_u := resetAllCircuit_transition res horacle Δ_sl
      set Δ_u := (interp ((resetAllCircuit res).compile QProg.qAssign
        (parallelMarkingOracle m S))).toStateFun Δ_sl
      let cEmb := embedOracleCirc sub2 cAvg2; let γ_u := marginalState sub2 Δ_u
      have hγ_supp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n m 2))) γ_u :=
        supportedOn_zero_marginalState sub2 hrst_u.2.2.2
      have hγ_qset : γ_u = (interp QProg.qSet).toStateFun γ_u := by
        rw [interp_qSet]; exact cqState_eq_qSet_of_supportedOn_zero hγ_supp
      let postB_loc : CQAssertion (Store Var) (2 ^ findAllQubits n m 2) :=
        liftPureProp (fun τ ↦ GroverSol.decodeTargets n 2 (τ res) = B)
      let postB_glob : CQAssertion (Store Var) (2 ^ Q) :=
        liftPureProp (fun τ ↦ decodeTargetsLocal n 2 (τ res) = B)
      have hliftB : liftAssertion sub2 postB_loc = postB_glob := liftAssertion_liftPureProp sub2 _
      let afterC := (interp ((deflateCirc n m T (permOracleCirc n m perm cEmb)).compile
        QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ_u
      have hafterC_B : 𝔼[afterC, postB_glob] = (Δ_u.trace : ℝ) := by
        dsimp only [afterC]
        rw [interp_deflateCirc n m hTS, interp_permOracleCirc n m perm R cEmb,
          ← hliftB, expect_liftAssertion_eq_marginalState, marginalState_interp_embedOracleCirc]
        have hprog_qset : (interp (cAvg2.compile QProg.qAssign (parallelMarkingOracle m
          B))).toStateFun γ_u = (interp (QProg.qSet ;; cAvg2.compile QProg.qAssign
          (GroverSol.groverParallelMarkingOracle m B))).toStateFun γ_u := by
          rw [interp_qSeq, QMonad.Q.toStateFun_bind, ← hγ_qset]; rfl
        rw [hprog_qset]
        have hge : (γ_u.trace : ℝ) ≤ 𝔼[(interp (QProg.qSet ;; cAvg2.compile QProg.qAssign
              (GroverSol.groverParallelMarkingOracle m B))).toStateFun γ_u, postB_loc] := by
          rw [← expect_top γ_u, ← wp_expectation_eq]; exact expect_mono le_rfl (hcorr2 B hB_mem)
        have hle1 : 𝔼[(interp (QProg.qSet ;; cAvg2.compile QProg.qAssign
            (GroverSol.groverParallelMarkingOracle m B))).toStateFun γ_u, postB_loc] ≤
            (((interp (QProg.qSet ;; cAvg2.compile QProg.qAssign
              (GroverSol.groverParallelMarkingOracle m B))).toStateFun γ_u).trace : ℝ) := by
          rw [← expect_top _]; exact expect_mono le_rfl le_top
        have hle2 : (((interp (QProg.qSet ;; cAvg2.compile QProg.qAssign
            (GroverSol.groverParallelMarkingOracle m B))).toStateFun γ_u).trace : ℝ) ≤
            γ_u.trace := by
          exact_mod_cast (interp _).trace_toStateFun_le γ_u
        have htr_γ : (γ_u.trace : ℝ) = Δ_u.trace := (by dsimp only [γ_u]; rw [trace_marginalState])
        linarith
      let writeDisp := dispBits (Q := Q) (w := (n + 1) * m) res (2 * n) 0 fun wVal ↦
        let R_dec := (decodeTargetsLocal n 2 (wVal : ℤ)).map perm.symm.toEmbedding
        setClassicalValCircuit res memK (encodeFinsetVal n k (T ∪ R_dec))
      have hwp_write : postB_glob ≤
          wp (writeDisp.compile QProg.qAssign (parallelMarkingOracle m S)) postS := by
        intro τ; rw [wp_dispBits]
        open Classical in
        by_cases hBτ : decodeTargetsLocal n 2 (τ res) = B
        · have hw_dec : decodeTargetsLocal n 2
              ((((τ res).toNat / 2 ^ 0) % 2 ^ (2 * n) : ℕ) : ℤ) = B := by
            rw [pow_zero, Nat.div_one, show 2 * n = n * 2 by ring, decodeTargetsLocal_mod_pow, hBτ]
          have hset_eq : T ∪ B.map perm.symm.toEmbedding = S := by
            have hRB : B.map perm.symm.toEmbedding = R := finset_map_symm_map perm R; rw [hRB]
            exact Finset.union_sdiff_of_subset hTS
          dsimp only; rw [hw_dec, hset_eq]; have hwp_top : (⊤ : CQAssertion (Store Var) (2 ^ Q)) ≤
              wp ((setClassicalValCircuit res memK (encodeFinsetVal n k S)).compile QProg.qAssign
                (parallelMarkingOracle m S)) postS := by
            have hmeas_le : diagAssertion (Var := Var) (fun z : Fin (2 ^ Q) ↦ memK.extractIndex z
              = encodeFinsetVal n k S) ≤ wp (QProg.measureRegister res memK) postS := by
              intro σ; rw [QProg.measureRegister, wp_qMeasure]
              change (diagObs _).1 ≤ ∑ o : Fin (2 ^ (n * k)), HermitianMat.conj
                (memK.basisOutcomeProjector o)ᴴ (postS (Store.subst σ res ↑o.val)).1
              refine le_trans ?_ (Finset.single_le_sum (fun o _ ↦ HermitianMat.conj_nonneg _
                (postS _).2.1) (Finset.mem_univ (encodeFinsetVal n k S)))
              have hpS : decodeTargetsLocal n k
                  (Store.subst σ res ↑(encodeFinsetVal n k S).val res) = S := by
                simp [Store.subst, decodeTargetsLocal_encodeFinsetVal hS]
              have h1 : (postS (Store.subst σ res ↑(encodeFinsetVal n k S).val)).1 = 1 := by
                dsimp only [postS]; rw [liftPureProp_apply, ite_eq_left hpS]; rfl
              rw [h1]; apply le_of_eq; apply HermitianMat.ext
              rw [diagObs_mat, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
                memK.basisOutcomeProjector_conjTranspose, HermitianMat.mat_one, Matrix.mul_one,
                basisOutcomeProjector_eq_diagProj, diagProj_mul_self]
            let U_v := permutationUnitary
              (xorBitsPerm (regMaskVec memK (encodeFinsetVal n k S).val))
            have hxor_le : diagAssertion (Var := Var) (fun z : Fin (2 ^ Q) ↦ memK.extractIndex z =
              0) ≤ wp (QProg.qAssign (phaseI U_v)) (diagAssertion (fun z ↦ memK.extractIndex z =
              encodeFinsetVal n k S)) := by
              rw [wp_qAssign, qAssign_phaseI, wp_qAssign_permutationUnitary_diagAssertion]; intro σ
              refine diagObs_mono fun z hz0 ↦ ?_
              rw [xorBitsPerm_regMaskVec_of_clean memK _ z hz0]
              exact memK.extractIndex_replaceIndex z _
            dsimp only [setClassicalValCircuit]
            simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
              OracleDynamicCircuit.compile_measure, wp_qSeq]
            exact (wp_resetRegCircuit_top_le res memK _).trans
              (wp_mono _ (hxor_le.trans (wp_mono _ hmeas_le)))
          exact le_top.trans (hwp_top τ)
        · have h0 : (postB_glob τ).1 = 0 := by
            dsimp only [postB_glob]; rw [liftPureProp_apply, ite_eq_right hBτ]; rfl
          change (postB_glob τ).1 ≤ _; rw [h0]; exact (wp _ postS τ).2.1
      have hcorr_u : 𝔼[(interp (OracleDynamicCircuit.compile QProg.qAssign (parallelMarkingOracle
        m S) (.seq (resetAllCircuit res) (.seq (deflateCirc n m T (permOracleCirc n m perm cEmb))
        writeDisp)))).toStateFun Δ_sl, postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
        simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
        change 𝔼[(interp (writeDisp.compile QProg.qAssign (parallelMarkingOracle m S))).toStateFun
          afterC, postS] = _
        have hge : (Δ_u.trace : ℝ) ≤ 𝔼[(interp (writeDisp.compile QProg.qAssign
          (parallelMarkingOracle m S))).toStateFun afterC, postS] := by
          rw [← hafterC_B, ← wp_expectation_eq (writeDisp.compile QProg.qAssign
            (parallelMarkingOracle m S)) afterC]; exact expect_mono le_rfl hwp_write
        have hle1 : 𝔼[(interp (writeDisp.compile QProg.qAssign (parallelMarkingOracle m
          S))).toStateFun afterC, postS] ≤ (((interp (writeDisp.compile QProg.qAssign
          (parallelMarkingOracle m S))).toStateFun afterC).trace : ℝ) := by
          rw [← expect_top _]; exact expect_mono le_rfl le_top
        have hle2 : (((interp (writeDisp.compile QProg.qAssign
            (parallelMarkingOracle m S))).toStateFun afterC).trace : ℝ) ≤ afterC.trace := by
          exact_mod_cast (interp _).trace_toStateFun_le afterC
        have hle3 : (afterC.trace : ℝ) ≤ Δ_u.trace := by
          exact_mod_cast (interp _).trace_toStateFun_le Δ_u
        have htr_u : (Δ_u.trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
          rw [hrst_u.2.1, htr_sl]
        linarith
      refine ⟨hcorr_u, ?_⟩
      simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]; rw [hrst_u.1, zero_add]
      have hcost_write : expectedCost modelS
          (writeDisp.compile QProg.qAssign (parallelMarkingOracle m S)) afterC = 0 := by
        dsimp only [writeDisp]; rw [expectedCost_dispBits]
        refine Finset.sum_eq_zero fun wVal _ ↦ ?_
        exact (setClassicalValCircuit_transition res memK _ horacle
          (P := fun _ ↦ True) (fun _ ↦ trivial) _).2
      change expectedCost modelS ((deflateCirc n m T (permOracleCirc n m perm cEmb)).compile
        QProg.qAssign (parallelMarkingOracle m S)) Δ_u + expectedCost modelS (writeDisp.compile
        QProg.qAssign (parallelMarkingOracle m S)) afterC ≤ _
      rw [hcost_write, add_zero]
      have hzc_perm :=
        zeroStepCost_permOracleCirc n m perm (zeroStepCost_embedOracleCirc sub2 cAvg2)
      have hcost_def := congrFun (expectedCost_deflateCirc n m hTS hzc_perm) Δ_u
      have hcost_perm := congrFun (expectedCost_permOracleCirc n m perm R
        (zeroStepCost_embedOracleCirc sub2 cAvg2)) Δ_u
      dsimp only [modelS]; rw [hcost_def, hcost_perm]
      have horB : GroverSol.IsRealMatrix (GroverSol.groverParallelMarkingOracle m B).1 :=
        GroverSol.isRealMatrix_groverParallelMarkingOracle m B
      have hcost_emb := expectedCost_embedOracleCirc_le sub2 cAvg2 horB Δ_u
      refine hcost_emb.trans ?_
      have hcost_qset : expectedCost (CostModel.ofEmbeddedOracle
        (GroverSol.groverParallelMarkingOracle m B)) (cAvg2.compile QProg.qAssign
        (GroverSol.groverParallelMarkingOracle m B)) (marginalState sub2 Δ_u) = expectedCost
        (CostModel.ofEmbeddedOracle (GroverSol.groverParallelMarkingOracle m B)) (QProg.qSet
        ;; cAvg2.compile QProg.qAssign (GroverSol.groverParallelMarkingOracle m B)) γ_u := by
        dsimp only [γ_u]
        rw [expectedCost_qSeq, expectedCost_qSet, CostModel.ofEmbeddedOracle_resetCost,
          Nat.cast_zero, mul_zero, zero_add]
        dsimp only [γ_u] at hγ_qset; rw [← hγ_qset]
      rw [hcost_qset]; have hcb := hq_bound B hB_mem γ_u
      have hm_γ : stateMass γ_u = stateMass Ξ * ENNReal.ofReal (1 / (2 ^ (2 * n) : ℝ)) := by
        dsimp only [γ_u]; rw [stateMass_marginalState, hrst_u.2.2.1, hmass_sl]
      change _ ≤ stateMass γ_u * _ at hcb
      rw [hm_γ, ENNReal.coe_nnreal_eq, mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hcb
      exact hcb
  refine ⟨?_, ?_⟩
  · simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
    change 𝔼[(interp ((dispBits res (2 * n) 0 branchFn).compile QProg.qAssign
      (parallelMarkingOracle m S))).toStateFun Ξ₂, postS] = Ξ.trace
    rw [expect_dispBits]
    have hterms : ∀ uVal ∈ Finset.range (2 ^ (2 * n)), 𝔼[(interp ((branchFn uVal).compile
      QProg.qAssign (parallelMarkingOracle m S))).toStateFun (sliceState res 0 (2 * n) uVal Ξ₂),
      postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := fun uVal hu ↦ (hbranch uVal
      (Finset.mem_range.mp hu)).1
    rw [Finset.sum_congr rfl hterms, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc]
    have hpow_ne : (2 ^ (2 * n) : ℝ) ≠ 0 := (by positivity)
    rw [mul_one_div_cancel hpow_ne, one_mul]
  · simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
    change expectedCost modelS _ Ξ + (expectedCost modelS _ Ξ₁ + expectedCost modelS ((dispBits
      res (2 * n) 0 branchFn).compile QProg.qAssign (parallelMarkingOracle m S)) Ξ₂) ≤ _
    rw [hrst0.1, expectedCost_sampleSeedCircuit res n Q ((n + 1) * m) hseed horacle Ξ₁,
      zero_add, zero_add, expectedCost_dispBits]
    let termR (u : Fin (2 ^ (2 * n))) : ℝ := (1 / (2 ^ (2 * n) : ℝ)) * if ha :
      (GF2nForallA.seedToGFPair hn0 u).1 = 0 then (818309887 / 10 ^ 9 : ℝ) *
      GroverSol.groverHarmonicSqrtSum 2 * unit else (q (R.map (GF2nForallA.finAffinePerm hn0
      (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha) (GF2nForallA.seedToGFPair hn0
      u).2).toEmbedding) : ℝ)
    have hterm_nn (u : Fin (2 ^ (2 * n))) : 0 ≤ termR u := by
      dsimp only [termR]; refine mul_nonneg (by positivity) ?_
      split_ifs
      · have hh2 : 0 ≤ GroverSol.groverHarmonicSqrtSum 2 :=
          Finset.sum_nonneg fun _ _ ↦ by positivity
        have hu_pos : 0 ≤ unit := (by dsimp [unit]; positivity); positivity
      · exact NNReal.coe_nonneg _
    calc (∑ uVal ∈ Finset.range (2 ^ (2 * n)), expectedCost modelS ((branchFn uVal).compile
          QProg.qAssign (parallelMarkingOracle m S)) (sliceState res 0 (2 * n) uVal Ξ₂)) ≤ ∑ uVal
          ∈ Finset.range (2 ^ (2 * n)), stateMass Ξ * ENNReal.ofReal (if hu : uVal < 2 ^ (2 * n)
          then termR ⟨uVal, hu⟩ else 0) := by
          refine Finset.sum_le_sum fun uVal hu ↦ ?_
          have hlt := Finset.mem_range.mp hu; rw [dite_eq_left hlt]; exact (hbranch uVal hlt).2
      _ = stateMass Ξ * ∑ u : Fin (2 ^ (2 * n)), ENNReal.ofReal (termR u) := by
          rw [← Finset.mul_sum]; congr 1
          refine Finset.sum_bij (fun uVal hu ↦ ⟨uVal, Finset.mem_range.mp hu⟩)
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ congrArg Fin.val h)
            (fun u _ ↦ ⟨u.val, Finset.mem_range.mpr u.isLt, rfl⟩)
            fun uVal hu ↦ by simp [Finset.mem_range.mp hu]
      _ = stateMass Ξ * ENNReal.ofReal (∑ u : Fin (2 ^ (2 * n)), termR u) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun u _ ↦ hterm_nn u]
      _ ≤ stateMass Ξ * ENNReal.ofReal ((uAvg + 1 / 10 ^ 9) * unit) := by
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) (stateMass Ξ)
          dsimp only [termR]; rw [← Finset.mul_sum]
          let fPair (p : GaloisField 2 n × GaloisField 2 n) : ℝ := if ha : p.1 = 0 then (818309887
            / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit else (q (R.map
            (GF2nForallA.finAffinePerm hn0 (Units.mk0 p.1 ha) p.2).toEmbedding) : ℝ)
          have hsum_pair : (∑ u : Fin (2 ^ (2 * n)), if ha : (GF2nForallA.seedToGFPair hn0 u).1 =
            0 then (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit else
            (q (R.map (GF2nForallA.finAffinePerm hn0 (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1
            ha) (GF2nForallA.seedToGFPair hn0 u).2).toEmbedding) : ℝ)) = ∑ p : GaloisField 2 n ×
            GaloisField 2 n, fPair p := Fintype.sum_equiv (GF2nForallA.seedToGFPair hn0) _ fPair
            fun _ ↦ rfl
          rw [hsum_pair, Fintype.sum_prod_type]
          have hsplit0 : (∑ a : GaloisField 2 n, ∑ b : GaloisField 2 n, fPair (a, b)) = (∑ b :
            GaloisField 2 n, fPair (0, b)) + ∑ a ∈ (Finset.univ : Finset (GaloisField 2 n)).erase
            0, ∑ b : GaloisField 2 n, fPair (a, b) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : GaloisField 2 n))]
          rw [hsplit0]; have h0_sum : (∑ b : GaloisField 2 n, fPair (0, b)) = (2 ^ n : ℝ) *
                ((818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 * unit) := by
            dsimp only [fPair]
            simp only [↓reduceDIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0]; push_cast; rfl
          have hunit_sum : (∑ a ∈ (Finset.univ : Finset (GaloisField 2 n)).erase 0, ∑ b :
            GaloisField 2 n, fPair (a, b)) = ∑ p : (GaloisField 2 n)ˣ × GaloisField 2 n, (q (R.map
            (GF2nForallA.finAffinePerm hn0 p.1 p.2).toEmbedding) : ℝ) := by
            rw [Fintype.sum_prod_type]; symm
            refine Finset.sum_bij (fun a _ ↦ (a : GaloisField 2 n)) ?_ ?_ ?_ ?_
            · intro a _; exact Finset.mem_erase.mpr ⟨Units.ne_zero a, Finset.mem_univ _⟩
            · intro _ _ _ _ h; exact Units.ext h
            · intro a ha; exact ⟨Units.mk0 a (Finset.mem_erase.mp ha).1, Finset.mem_univ _, rfl⟩
            · intro a _; refine Finset.sum_congr rfl fun b _ ↦ ?_
              have hne : (a : GaloisField 2 n) ≠ 0 := Units.ne_zero a; dsimp only [fPair]
              rw [dite_eq_right hne]
              have hmk : Units.mk0 (a : GaloisField 2 n) hne = a := Units.ext rfl; rw [hmk]
          rw [h0_sum, hunit_sum, GF2nForallA.sum_finAffinePerm_eq_two_mul_sum_targetSets hn0
              (show R.card = 2 from hST2) (fun B ↦ (q B : ℝ))]
          have hcard2_pos : (0 : ℝ) < ((GroverSol.groverTargetSets n 2).card : ℝ) := by
            have hc_nat : 0 < (GroverSol.groverTargetSets n 2).card := by
              rw [GroverSol.groverTargetSets, Finset.card_powersetCard, Finset.card_univ,
                Fintype.card_fin]
              exact Nat.choose_pos (by calc 2 ≤ 2 ^ 20 := by norm_num
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega))
            exact_mod_cast hc_nat
          have hsum_q_le : 2 * ∑ B ∈ GroverSol.groverTargetSets n 2, (q B : ℝ) ≤ (2 ^ (2 * n)
            : ℝ) * (uAvg * unit) := by
            have h1 := (div_le_iff₀ hcard2_pos).mp hq_avg
            have h2card : (2 : ℝ) * ((GroverSol.groverTargetSets n 2).card : ℝ) ≤
                (2 ^ (2 * n) : ℝ) := by
              have hnat : 2 * (GroverSol.groverTargetSets n 2).card ≤ 2 ^ (2 * n) := by
                rw [GroverSol.groverTargetSets, Finset.card_powersetCard, Finset.card_univ,
                  Fintype.card_fin, two_mul_choose_two_two_pow_all, two_mul, pow_add]
                exact Nat.mul_le_mul_left (2 ^ n) (Nat.sub_le (2 ^ n) 1)
              exact_mod_cast hnat
            have hu_nn : 0 ≤ uAvg * unit := (by dsimp [unit]; positivity)
            calc 2 * ∑ B ∈ GroverSol.groverTargetSets n 2, (q B : ℝ)
                ≤ 2 * (uAvg * unit * (GroverSol.groverTargetSets n 2).card) :=
                  mul_le_mul_of_nonneg_left h1 zero_le_two
              _ = (2 * (GroverSol.groverTargetSets n 2).card) * (uAvg * unit) := by ring
              _ ≤ (2 ^ (2 * n) : ℝ) * (uAvg * unit) := mul_le_mul_of_nonneg_right h2card hu_nn
          have htail_le : (2 ^ n : ℝ) * ((818309887 / 10 ^ 9 : ℝ) *
            GroverSol.groverHarmonicSqrtSum 2 * unit) ≤ (2 ^ (2 * n) : ℝ) * ((1 / 10 ^ 9 :
            ℝ) * unit) := by
            have hh2_le : GroverSol.groverHarmonicSqrtSum 2 ≤ 2 := by
              have h12 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := (by ext x; simp; omega)
              rw [GroverSol.groverHarmonicSqrtSum, h12, Finset.sum_pair (by omega),
                Nat.cast_one, Real.sqrt_one, div_one, Nat.cast_ofNat]
              have hs2 : (1 : ℝ) ≤ √(2 : ℝ) := by
                nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
              have hinv2 : 1 / √(2 : ℝ) ≤ 1 := div_le_one_of_le₀ hs2 (by positivity); linarith
            have hpow_big : (2 * 10 ^ 9 : ℝ) ≤ (2 ^ n : ℝ) := by
              calc (2 * 10 ^ 9 : ℝ) ≤ (2 ^ 32 : ℝ) := by norm_num
                _ ≤ (2 ^ n : ℝ) := pow_le_pow_right₀ (by norm_num) (by omega)
            have h2n_2 : (2 ^ (2 * n) : ℝ) = (2 ^ n : ℝ) * (2 ^ n : ℝ) := (by rw [two_mul, pow_add])
            have hu_nn : 0 ≤ unit := (by dsimp [unit]; positivity)
            have hcoef : (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum 2 ≤ 2 := by
              nlinarith
            rw [h2n_2]
            calc (2 ^ n : ℝ) * ((818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum
                  2 * unit) ≤ (2 ^ n : ℝ) * (2 * unit) := mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hcoef hu_nn) (by positivity)
              _ = (2 ^ n : ℝ) * ((2 * 10 ^ 9) * ((1 / 10 ^ 9 : ℝ) * unit)) := by ring
              _ ≤ (2 ^ n : ℝ) * ((2 ^ n : ℝ) * ((1 / 10 ^ 9 : ℝ) * unit)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hpow_big (by positivity)) (by positivity)
              _ = (2 ^ n : ℝ) * (2 ^ n : ℝ) * ((1 / 10 ^ 9 : ℝ) * unit) := by ring
          have hpow_pos : (0 : ℝ) < (2 ^ (2 * n) : ℝ) := (by positivity)
          calc (1 / (2 ^ (2 * n) : ℝ)) * ((2 ^ n : ℝ) * ((818309887 / 10 ^ 9 : ℝ) *
                GroverSol.groverHarmonicSqrtSum 2 * unit) + 2 * ∑ B ∈
                GroverSol.groverTargetSets n 2, (q B : ℝ)) ≤ (1 / (2 ^ (2 * n) : ℝ)) * ((2 ^
                (2 * n) : ℝ) * ((1 / 10 ^ 9 : ℝ) * unit) + (2 ^ (2 * n) : ℝ) * (uAvg * unit)) :=
                mul_le_mul_of_nonneg_left (add_le_add htail_le hsum_q_le) (by positivity)
            _ = (uAvg + 1 / 10 ^ 9) * unit := by field_simp [hpow_pos.ne']; ring
/- ## 6. Multi-Layer `AGL(1, GF(2 ^ n))` Subcube Finisher (`stage2FromSetCircuit`) -/
/-- `fuel`-layer `AGL(1, GF(2 ^ n))` subcube coupon-collector circuit on `Q` qubits
  (`findAllQubits n m k ≤ Q`, `0` extra ancilla qubits, zero `.qWhile` loops outside
  `Stage1`). -/
noncomputable def stage2FromSetCircuit {Var : Type}
    (res : Var) (n m d k Q : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm : m = 2 ^ d) (hd_le : d ≤ n) (hQ : findAllQubits n m k ≤ Q)
    (optTwo :
      Option (Finset (Fin (2 ^ n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)))
    (stepCfg : ℕ → ℕ → Option ℕ) (useSelf2 : ℕ → Bool) :
    ℕ → Finset (Fin (2 ^ n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | fuel, T =>
      let r := k - T.card
      if r == 2 && useSelf2 fuel then
        match optTwo with
        | some cTwo => cTwo T
        | none => stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
      else
        match fuel with
        | 0 => stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
        | f + 1 =>
            if r < 2 then
              stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
            else
              match stepCfg f r with
              | none =>
                  stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg
                    useSelf2 f T
              | some K =>
                  if hn0 : n = 0 then
                    stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
                  else if hm2 : 2 ≤ m then
                    let s := n - d
                    let hsd : s + d = n := Nat.sub_add_cancel hd_le
                    let hseed : 2 * n ≤ Q := by unfold findAllQubits at hQ; nlinarith
                    let horQ : (n + 1) * m ≤ Q := by unfold findAllQubits at hQ; omega
                    .seq (resetAllCircuit res)
                      (.seq (sampleSeedCircuit res n Q ((n + 1) * m) hseed)
                        (dispBits res (2 * n) 0 fun uVal ↦
                          if hu : uVal < 2 ^ (2 * n) then
                            let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
                            if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
                              stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo
                                stepCfg useSelf2 f T
                            else
                              let perm := GF2nForallA.finAffinePerm hn0
                                (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
                                (GF2nForallA.seedToGFPair hn0 u).2
                              .seq (resetAllCircuit res)
                                (.seq
                                  (deflateCirc n m T
                                    (permOracleCirc n m perm
                                      (subcubePassCircuit res n m s d Q hsd hm horQ K)))
                                  (dispBits res ((n + 1) * m) 0 fun wVal ↦
                                    if hw : wVal < 2 ^ ((n + 1) * m) then
                                      let H := (hitSetOfOracleOutcome n m ⟨wVal, hw⟩).map
                                        perm.symm.toEmbedding
                                      stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ
                                        optTwo stepCfg useSelf2 f (T ∪ H)
                                    else .skip))
                          else .skip))
                  else
                    stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg
                      useSelf2 f T
theorem zeroStepCost_stage2FromSetCircuit {Var : Type}
    (res : Var) (n m d k Q : ℕ)
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm : m = 2 ^ d) (hd_le : d ≤ n) (hQ : findAllQubits n m k ≤ Q)
    (optTwo :
      Option (Finset (Fin (2 ^ n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)))
    (hopt0 : ∀ cTwo, optTwo = some cTwo → ∀ T, ZeroStepCost (cTwo T))
    (stepCfg : ℕ → ℕ → Option ℕ) (useSelf2 : ℕ → Bool) :
    ∀ (fuel : ℕ) (T : Finset (Fin (2 ^ n))),
      ZeroStepCost
        (stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg useSelf2
          fuel T)
  | fuel, T => by
      rw [stage2FromSetCircuit.eq_def]
      dsimp only
      by_cases hself : ((k - T.card == 2 && useSelf2 fuel) = true)
      · rw [ite_eq_left hself]
        cases hopt : optTwo with
        | none => exact zeroStepCost_stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
        | some cTwo => exact hopt0 cTwo hopt T
      · rw [ite_eq_right hself]
        cases fuel with
        | zero => exact zeroStepCost_stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
        | succ f =>
            dsimp only
            by_cases hrlt : k - T.card < 2
            · rw [ite_eq_left hrlt]
              exact zeroStepCost_stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
            · rw [ite_eq_right hrlt]
              cases hcfg : stepCfg f (k - T.card) with
              | none =>
                  exact zeroStepCost_stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ
                    optTwo hopt0 stepCfg useSelf2 f T
              | some K =>
                  dsimp only
                  by_cases hn0 : n = 0
                  · rw [dite_eq_left hn0]
                    exact zeroStepCost_stage2Fuel0Circuit res n m k Q hm_grid hk_grid hQ T
                  · rw [dite_eq_right hn0]
                    by_cases hm2 : 2 ≤ m
                    · rw [dite_eq_left hm2]
                      refine ⟨zeroStepCost_resetAllCircuit res,
                        zeroStepCost_sampleSeedCircuit _ _ _ _ _,
                        zeroStepCost_dispBits res (2 * n) 0 _ fun uVal _ ↦ ?_⟩
                      by_cases hu : uVal < 2 ^ (2 * n)
                      · rw [dite_eq_left hu]
                        by_cases ha : (GF2nForallA.seedToGFPair hn0 ⟨uVal, hu⟩).1 = 0
                        · rw [dite_eq_left ha]
                          exact zeroStepCost_stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm
                            hd_le hQ optTwo hopt0 stepCfg useSelf2 f T
                        · rw [dite_eq_right ha]
                          refine ⟨zeroStepCost_resetAllCircuit res,
                            zeroStepCost_deflateCirc n m T
                              (zeroStepCost_permOracleCirc n m _
                                (zeroStepCost_subcubePassCircuit _ _ _ _ _ _ _ _ _ _)),
                            zeroStepCost_dispBits res ((n + 1) * m) 0 _ fun wVal _ ↦ ?_⟩
                          by_cases hw : wVal < 2 ^ ((n + 1) * m)
                          · rw [dite_eq_left hw]
                            exact zeroStepCost_stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm
                              hd_le hQ optTwo hopt0 stepCfg useSelf2 f _
                          · rw [dite_eq_right hw]
                            trivial
                      · rw [dite_eq_right hu]
                        trivial
                    · rw [dite_eq_right hm2]
                      exact zeroStepCost_stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le
                        hQ optTwo hopt0 stepCfg useSelf2 f T
theorem stage2FromSet_permPass_step {Var : Type} [DecidableEq Var] (res : Var) {n m d k Q : ℕ}
    (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid) (hm2 : 2 ≤
    m) (hm : m = 2 ^ d) (hd_le : d ≤ n) (hQ : findAllQubits n m k ≤ Q) (optTwo : Option (Finset
    (Fin (2 ^ n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))) (stepCfg : ℕ → ℕ
    → Option ℕ) (useSelf2 : ℕ → Bool) (v : ℕ → ℕ → ℝ) (f K : ℕ) (horQ : (n + 1) * m ≤ Q) (hv_nn_f
    : ∀ r ≤ k, 0 ≤ v f r) (hv_mono_f : ∀ i j, i ≤ j → j ≤ k → v f i ≤ v f j) (ih_f : ∀ {S T :
    Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S → ∀ Ξ : CQState (Store Var) (2 ^ Q),
        let prog :=
          (stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg
            useSelf2 f T).compile QProg.qAssign (parallelMarkingOracle m S)
        𝔼[(interp prog).toStateFun Ξ,
            liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace ∧
          expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Ξ ≤
            stateMass Ξ * ENNReal.ofReal (v f (S \ T).card * ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ)))))
    {S T : Finset (Fin (2 ^ n))} (hS : S.card = k) (hTS : T ⊆ S)
    (perm : Equiv.Perm (Fin (2 ^ n)))
    {Ξ Δ_sl : CQState (Store Var) (2 ^ Q)}
    (htr_sl : (Δ_sl.trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace) :
    open Classical in
    let circ :=
      OracleDynamicCircuit.seq (resetAllCircuit res)
        (.seq (deflateCirc n m T (permOracleCirc n m perm
              (subcubePassCircuit res n m (n - d) d Q (Nat.sub_add_cancel hd_le) hm horQ K)))
          (dispBits res ((n + 1) * m) 0 fun wVal ↦
            if hw : wVal < 2 ^ ((n + 1) * m) then
              let H := (hitSetOfOracleOutcome n m ⟨wVal, hw⟩).map perm.symm.toEmbedding
              stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg
                useSelf2 f (T ∪ H)
            else .skip))
    𝔼[(interp (circ.compile QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ_sl,
      liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = (1 / (2 ^ (2 * n) : ℝ)) *
      Ξ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (circ.compile QProg.qAssign (parallelMarkingOracle m S)) Δ_sl ≤ stateMass Ξ * ENNReal.ofReal
      ((1 / (2 ^ (2 * n) : ℝ)) * (((K : ℝ) + 1) / ((π / 4) * √(2 ^ (n - d) : ℝ)) + (if Set.InjOn
      (fun y ↦ (subcubeSplitEquiv (n - d) d (Nat.sub_add_cancel hd_le) y).2) (((S \ T).map
      perm.toEmbedding : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))) then ∑ j ∈ Finset.range ((S \
      T).card + 1), ((S \ T).card.choose j : ℝ) * (1 - p_succ_set K (n - d) 1) ^ j * (p_succ_set K
      (n - d) 1) ^ ((S \ T).card - j) * v f j else v f (S \ T).card)) * ((π / 4) * √((2 ^ n : ℝ) /
      (m : ℝ)))) := by
  classical
  intro circ; let s := n - d; have hsd : s + d = n := Nat.sub_add_cancel hd_le; let R := S \ T
  let r := R.card
  have hr_eq : k - T.card = r := by
    dsimp only [r, R]; have hadd := Finset.card_sdiff_add_card_eq_card hTS; omega
  have hr_le : r ≤ k := (by rw [← hr_eq]; exact Nat.sub_le k T.card)
  let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
  have hm_pos : (0 : ℝ) < m := (by exact_mod_cast (show 0 < m by omega))
  have hu_nn : 0 ≤ unit := (by dsimp [unit]; positivity)
  have hu_pos : 0 < unit := by
    dsimp [unit]; exact mul_pos (div_pos Real.pi_pos (by norm_num))
      (Real.sqrt_pos.mpr (div_pos (by positivity) hm_pos))
  have hunit_s : (π / 4) * √(2 ^ s : ℝ) = unit := by
    dsimp only [unit]; congr 1
    have hdiv : (2 ^ n : ℝ) / (m : ℝ) = (2 ^ s : ℝ) := by
      rw [hm, Nat.cast_pow, Nat.cast_ofNat, ← hsd, pow_add]
      exact mul_div_cancel_right₀ _ (by positivity)
    rw [hdiv]
  let eCF : ℝ := ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * (1 - p_succ_set K s 1) ^ j *
    (p_succ_set K s 1) ^ (r - j) * v f j
  have heCF_nn : 0 ≤ eCF := by
    dsimp only [eCF]; refine Finset.sum_nonneg fun j hj ↦ ?_
    have hjk : j ≤ k := (by have := Finset.mem_range.mp hj; omega)
    have hp0 := p_succ_set_nonneg K s 1
    have hp1 : 0 ≤ 1 - p_succ_set K s 1 := sub_nonneg.mpr (p_succ_set_le_one K s 1)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp1 j)) (pow_nonneg hp0
      _)) (hv_nn_f j hjk)
  have horacle : IsRealMatrix (parallelMarkingOracle m S).1 := isRealMatrix_parallelMarkingOracle S
  let postS : CQAssertion (Store Var) (2 ^ Q) := liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ
    res) = S)
  let modelS := CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m S)
  have hmass_sl : stateMass Δ_sl = stateMass Ξ * ENNReal.ofReal (1 / (2 ^ (2 * n) : ℝ)) := by
    rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_sl, mul_comm,
      ENNReal.ofReal_mul (CQState.trace_nonneg _)]
  let B := R.map perm.toEmbedding; have hrst_u := resetAllCircuit_transition res horacle Δ_sl
  set Δ_u := (interp ((resetAllCircuit res).compile QProg.qAssign
    (parallelMarkingOracle m S))).toStateFun Δ_sl
  let passC := subcubePassCircuit (Var := Var) res n m s d Q hsd hm horQ K
  let defPass := deflateCirc n m T (permOracleCirc n m perm passC)
  set Γ_u := (interp (defPass.compile QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ_u
  have hΓ_eq : Γ_u = (interp (passC.compile QProg.qAssign
      (parallelMarkingOracle m B))).toStateFun Δ_u := by
    dsimp only [Γ_u, defPass]
    rw [interp_deflateCirc n m hTS, interp_permOracleCirc n m perm R passC]
  let wBranch (wVal : ℕ) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
    if hw : wVal < 2 ^ ((n + 1) * m) then
      let H := (hitSetOfOracleOutcome n m ⟨wVal, hw⟩).map perm.symm.toEmbedding
      stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg
        useSelf2 f (T ∪ H)
    else .skip
  have hwBranch (wVal : ℕ) (hw : wVal < 2 ^ ((n + 1) * m)) :
      let w : Fin (2 ^ ((n + 1) * m)) := ⟨wVal, hw⟩
      let Γ_w := sliceState res 0 ((n + 1) * m) wVal Γ_u
      𝔼[(interp ((wBranch wVal).compile QProg.qAssign
          (parallelMarkingOracle m S))).toStateFun Γ_w, postS] =
        Complex.normSq (subcubeParallelVec s d hsd hm B K w) * (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace ∧
        expectedCost modelS
          ((wBranch wVal).compile QProg.qAssign (parallelMarkingOracle m S)) Γ_w ≤
          stateMass Ξ * ENNReal.ofReal
            ((1 / (2 ^ (2 * n) : ℝ)) * Complex.normSq (subcubeParallelVec s d hsd hm B K w) *
              v f (B \ hitSetOfOracleOutcome n m w).card * unit) := by
    intro w Γ_w; let H := (hitSetOfOracleOutcome n m w).map perm.symm.toEmbedding
    have htr_w : (Γ_w.trace : ℝ) = Complex.normSq (subcubeParallelVec s d hsd hm B K w) *
          ((1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace) := by
      dsimp only [Γ_w]
      rw [hΓ_eq, subcubePass_sliceState_trace res n m s d Q hsd hm horQ K B hrst_u.2.2.2 hw,
        hrst_u.2.1, htr_sl]
    dsimp only [wBranch]; rw [dite_eq_left hw]
    by_cases hψ0 : subcubeParallelVec s d hsd hm B K w = 0
    · have htr0 : (Γ_w.trace : ℝ) = 0 := (by rw [htr_w, hψ0, map_zero, zero_mul])
      have hΓ0 : Γ_w = 0 := cqState_eq_zero_of_trace_eq_zero htr0
      rw [hΓ0, hψ0, map_zero, zero_mul, zero_mul, interp_toStateFun_zero, expect_zero_state,
        expectedCost_zero_cqState]; exact ⟨rfl, zero_le⟩
    · have hhit_sub : hitSetOfOracleOutcome n m w ⊆ B :=
        hitSetOfOracleOutcome_subset_of_ne_zero hsd hm hψ0
      have hH_sub_R : H ⊆ R := by
        have h1 : H ⊆ B.map perm.symm.toEmbedding := Finset.map_subset_map.mpr hhit_sub
        rwa [finset_map_symm_map perm R] at h1
      have hTH_sub_S : T ∪ H ⊆ S := Finset.union_subset hTS (hH_sub_R.trans Finset.sdiff_subset)
      have hsdiff_eq : (S \ (T ∪ H)).card = (B \ hitSetOfOracleOutcome n m w).card := by
        have hset : S \ (T ∪ H) = R \ H := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_union, R]
          exact ⟨fun ⟨hS', hn⟩ ↦ ⟨⟨hS', fun hT ↦ hn (Or.inl hT)⟩, fun hH ↦ hn (Or.inr hH)⟩,
            fun ⟨⟨hS', hnT⟩, hnH⟩ ↦ ⟨hS', fun h ↦ h.elim hnT hnH⟩⟩
        rw [hset]
        have hmap_sdiff : (R \ H).map perm.toEmbedding = B \ hitSetOfOracleOutcome n m w := by
          ext y; simp only [Finset.mem_map, Finset.mem_sdiff, B, H, Equiv.coe_toEmbedding]
          constructor
          · rintro ⟨x, ⟨hxR, hxH⟩, rfl⟩
            refine ⟨⟨x, hxR, rfl⟩, fun hy_hit ↦ hxH ⟨perm x, hy_hit, perm.symm_apply_apply x⟩⟩
          · rintro ⟨⟨x, hxR, rfl⟩, hy_nhit⟩
            refine ⟨x, ⟨hxR, ?_⟩, rfl⟩
            rintro ⟨y', hy', hx_eq⟩
            apply hy_nhit; have hy'_eq : y' = perm x := (by simp [← hx_eq]); exact hy'_eq ▸ hy'
        rw [← Finset.card_map perm.toEmbedding, hmap_sdiff]
      obtain ⟨hcorr_w, hcost_w⟩ := ih_f hS hTH_sub_S Γ_w; rw [hsdiff_eq] at hcost_w
      have hm_w : stateMass Γ_w = stateMass Ξ * ENNReal.ofReal ((1 / (2 ^ (2 * n) : ℝ)) *
              Complex.normSq (subcubeParallelVec s d hsd hm B K w)) := by
        rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_w]
        have heq_r : Complex.normSq (subcubeParallelVec s d hsd hm B K w) *
            ((1 / (2 ^ (2 * n) : ℝ)) * (Ξ.trace : ℝ)) =
            (Ξ.trace : ℝ) * ((1 / (2 ^ (2 * n) : ℝ)) *
              Complex.normSq (subcubeParallelVec s d hsd hm B K w)) := by ring
        rw [heq_r, ENNReal.ofReal_mul (CQState.trace_nonneg _)]
      refine ⟨by rw [hcorr_w, htr_w]; ring, hcost_w.trans ?_⟩
      rw [hm_w, mul_assoc,
        ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (Complex.normSq_nonneg _))]
      refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
      exact le_of_eq (by dsimp only [unit]; ring)
  refine ⟨?_, ?_⟩
  · dsimp only [circ]
    simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
    change 𝔼[(interp ((dispBits res ((n + 1) * m) 0 wBranch).compile
      QProg.qAssign (parallelMarkingOracle m S))).toStateFun Γ_u, postS] = _
    rw [expect_dispBits]
    have hw_sum : (∑ wVal ∈ Finset.range (2 ^ ((n + 1) * m)), 𝔼[(interp ((wBranch wVal).compile
      QProg.qAssign (parallelMarkingOracle m S))).toStateFun (sliceState res 0 ((n + 1) * m) wVal
      Γ_u), postS]) = (∑ w : Fin (2 ^ ((n + 1) * m)), Complex.normSq (subcubeParallelVec s d hsd
      hm B K w)) * ((1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace) := by
      rw [Finset.sum_mul]; refine Finset.sum_bij (fun wVal h ↦ ⟨wVal, Finset.mem_range.mp h⟩)
        (fun _ _ ↦ Finset.mem_univ _)
        (fun _ _ _ _ h ↦ congrArg Fin.val h)
        (fun w _ ↦ ⟨w.val, Finset.mem_range.mpr w.isLt, rfl⟩)
        fun wVal h ↦ by rw [(hwBranch wVal (Finset.mem_range.mp h)).1]; ring
    rw [hw_sum, sum_normSq_subcubeParallelVec_univ hsd hm B K, one_mul]
  · dsimp only [circ]; simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
    rw [hrst_u.1, zero_add]
    have hzc_pass := zeroStepCost_subcubePassCircuit (Var := Var) res n m s d Q hsd hm horQ K
    have hzc_perm := zeroStepCost_permOracleCirc n m perm hzc_pass
    have hc_def : expectedCost modelS (defPass.compile QProg.qAssign (parallelMarkingOracle m S))
      Δ_u = stateMass Ξ * ENNReal.ofReal ((1 / (2 ^ (2 * n) : ℝ)) * (((K : ℝ) + 1) / ((π / 4) *
      √(2 ^ s : ℝ))) * unit) := by
      dsimp only [modelS, defPass]
      rw [congrFun (expectedCost_deflateCirc n m hTS hzc_perm) Δ_u, congrFun
        (expectedCost_permOracleCirc n m perm R hzc_pass) Δ_u, expectedCost_subcubePassCircuit,
        hrst_u.2.2.1, hmass_sl, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2; rw [hunit_s, mul_assoc, div_mul_cancel₀ _ hu_pos.ne']
    change expectedCost modelS (defPass.compile QProg.qAssign (parallelMarkingOracle m S)) Δ_u +
      expectedCost modelS ((dispBits res ((n + 1) * m) 0 wBranch).compile QProg.qAssign
      (parallelMarkingOracle m S)) Γ_u ≤ stateMass Ξ * ENNReal.ofReal ((1 / (2 ^ (2 * n) : ℝ)) *
      (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ)) + (if Set.InjOn (fun y ↦ (subcubeSplitEquiv s d
      hsd y).2) (B : Set (Fin (2 ^ n))) then eCF else v f r)) * unit)
    rw [hc_def, expectedCost_dispBits]
    let wTerm (w : Fin (2 ^ ((n + 1) * m))) : ℝ := (1 / (2 ^ (2 * n) : ℝ)) * Complex.normSq
      (subcubeParallelVec s d hsd hm B K w) * v f (B \ hitSetOfOracleOutcome n m w).card * unit
    have hwTerm_nn (w : Fin (2 ^ ((n + 1) * m))) : 0 ≤ wTerm w := by
      dsimp only [wTerm]
      have hcard_le : (B \ hitSetOfOracleOutcome n m w).card ≤ k := by
        calc (B \ hitSetOfOracleOutcome n m w).card
            ≤ B.card := Finset.card_le_card Finset.sdiff_subset
          _ = r := by simp [B, r]
          _ ≤ k := hr_le
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Complex.normSq_nonneg _)) (hv_nn_f
        _ hcard_le)) hu_nn
    have hw_cost_le : (∑ wVal ∈ Finset.range (2 ^ ((n + 1) * m)), expectedCost modelS ((wBranch
      wVal).compile QProg.qAssign (parallelMarkingOracle m S)) (sliceState res 0 ((n + 1) * m)
      wVal Γ_u)) ≤ stateMass Ξ * ENNReal.ofReal (∑ w : Fin (2 ^ ((n + 1) * m)), wTerm w) := by
      calc (∑ wVal ∈ Finset.range (2 ^ ((n + 1) * m)), expectedCost modelS ((wBranch wVal).compile
            QProg.qAssign (parallelMarkingOracle m S)) (sliceState res 0 ((n + 1) * m) wVal Γ_u))
            ≤ ∑ wVal ∈ Finset.range (2 ^ ((n + 1) * m)), stateMass Ξ * ENNReal.ofReal (if hw :
            wVal < 2 ^ ((n + 1) * m) then wTerm ⟨wVal, hw⟩ else 0) := by
            refine Finset.sum_le_sum fun wVal h ↦ ?_
            have hlt := Finset.mem_range.mp h; rw [dite_eq_left hlt]; exact (hwBranch wVal hlt).2
        _ = stateMass Ξ * ∑ w : Fin (2 ^ ((n + 1) * m)), ENNReal.ofReal (wTerm w) := by
            rw [← Finset.mul_sum]; congr 1
            refine Finset.sum_bij (fun wVal h ↦ ⟨wVal, Finset.mem_range.mp h⟩)
              (fun _ _ ↦ Finset.mem_univ _)
              (fun _ _ _ _ h ↦ congrArg Fin.val h)
              (fun w _ ↦ ⟨w.val, Finset.mem_range.mpr w.isLt, rfl⟩)
              fun wVal h ↦ by simp [Finset.mem_range.mp h]
        _ = stateMass Ξ * ENNReal.ofReal (∑ w : Fin (2 ^ ((n + 1) * m)), wTerm w) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun w _ ↦ hwTerm_nn w]
    have hw_sum_bound : (∑ w : Fin (2 ^ ((n + 1) * m)), wTerm w) ≤ (1 / (2 ^ (2 * n) : ℝ)) * (if
      Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2) (B : Set (Fin (2 ^ n))) then eCF else v
      f r) * unit := by
      have hpull : (∑ w : Fin (2 ^ ((n + 1) * m)), wTerm w) = (1 / (2 ^ (2 * n) : ℝ)) * (∑ w : Fin
        (2 ^ ((n + 1) * m)), Complex.normSq (subcubeParallelVec s d hsd hm B K w) * v f (B \
        hitSetOfOracleOutcome n m w).card) * unit := by
        dsimp only [wTerm]; rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hpull]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hu_nn
      by_cases hcf : Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2) (B : Set (Fin (2 ^ n)))
      · rw [ite_eq_left hcf]; have hB_card : B.card = r := (by simp [B, r])
        rw [sum_normSq_subcubeParallelVec_cf hsd hm hcf K (v f), hB_card]
      · rw [ite_eq_right hcf]
        calc (∑ w : Fin (2 ^ ((n + 1) * m)), Complex.normSq (subcubeParallelVec s d hsd hm B K
              w) * v f (B \ hitSetOfOracleOutcome n m w).card) ≤ ∑ w : Fin (2 ^ ((n + 1) * m)),
              Complex.normSq (subcubeParallelVec s d hsd hm B K w) * v f r := by
              refine Finset.sum_le_sum fun w _ ↦ ?_
              have hc_le : (B \ hitSetOfOracleOutcome n m w).card ≤ r := by
                calc (B \ hitSetOfOracleOutcome n m w).card
                    ≤ B.card := Finset.card_le_card Finset.sdiff_subset
                  _ = r := by simp [B, r]
              exact mul_le_mul_of_nonneg_left
                (hv_mono_f _ r hc_le hr_le) (Complex.normSq_nonneg _)
          _ = (∑ w : Fin (2 ^ ((n + 1) * m)),
                Complex.normSq (subcubeParallelVec s d hsd hm B K w)) * v f r :=
              (Finset.sum_mul _ _ _).symm
          _ = v f r := by rw [sum_normSq_subcubeParallelVec_univ hsd hm B K, one_mul]
    calc stateMass Ξ * ENNReal.ofReal ((1 / (2 ^ (2 * n) : ℝ)) * (((K : ℝ) + 1) / ((π / 4) * √(2 ^
          s : ℝ))) * unit) + ∑ wVal ∈ Finset.range (2 ^ ((n + 1) * m)), expectedCost modelS
          ((wBranch wVal).compile QProg.qAssign (parallelMarkingOracle m S)) (sliceState res 0
          ((n + 1) * m) wVal Γ_u) ≤ stateMass Ξ * ENNReal.ofReal ((1 / (2 ^ (2 * n) : ℝ)) * (((K :
          ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ))) * unit) + stateMass Ξ * ENNReal.ofReal ((1 / (2 ^
          (2 * n) : ℝ)) * (if Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2) (B : Set (Fin (2
          ^ n))) then eCF else v f r) * unit) := add_le_add le_rfl (hw_cost_le.trans
          (mul_le_mul_right (ENNReal.ofReal_le_ofReal hw_sum_bound) _))
      _ = stateMass Ξ * ENNReal.ofReal
            ((1 / (2 ^ (2 * n) : ℝ)) * (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ)) +
                (if Set.InjOn (fun y ↦ (subcubeSplitEquiv s d hsd y).2)
                    (B : Set (Fin (2 ^ n))) then
                  eCF
                else v f r)) * unit) := by
          have hpass_nn : 0 ≤ (1 / (2 ^ (2 * n) : ℝ)) *
                (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ))) * unit :=
            mul_nonneg
              (mul_nonneg (by positivity)
                (by rw [hunit_s]; exact div_nonneg (by positivity) hu_pos.le))
              hu_nn
          have hcont_nn : 0 ≤ (1 / (2 ^ (2 * n) : ℝ)) * (if Set.InjOn (fun y ↦ (subcubeSplitEquiv
            s d hsd y).2) (B : Set (Fin (2 ^ n))) then eCF else v f r) * unit := by
            refine mul_nonneg (mul_nonneg (by positivity) ?_) hu_nn
            split_ifs
            · exact heCF_nn
            · exact hv_nn_f r hr_le
          rw [← mul_add, ← ENNReal.ofReal_add hpass_nn hcont_nn]; congr 2; ring
theorem stage2FromSet_someK_step {Var : Type} [DecidableEq Var] (res : Var) {n m d k Q : ℕ} (hn0 :
    n ≠ 0) (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hm : m = 2 ^ d) (hd_le : d ≤ n) (hQ : findAllQubits n m k ≤ Q) (hseed : 2 * n ≤
    Q) (horQ : (n + 1) * m ≤ Q) (optTwo : Option (Finset (Fin (2 ^ n)) → OracleDynamicCircuit
    (Unitary (2 ^ Q)) Var Q ((n + 1) * m))) (stepCfg : ℕ → ℕ → Option ℕ) (useSelf2 : ℕ → Bool) (v
    : ℕ → ℕ → ℝ) (f K : ℕ) (hv_nn_f : ∀ r ≤ k, 0 ≤ v f r) (hv_mono_f : ∀ i j, i ≤ j → j ≤ k → v f
    i ≤ v f j) (ih_f : ∀ {S T : Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S → ∀ Ξ : CQState (Store
      Var) (2 ^
    Q),
        let prog :=
          (stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg
            useSelf2 f T).compile QProg.qAssign (parallelMarkingOracle m S)
        𝔼[(interp prog).toStateFun Ξ,
            liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace ∧
          expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Ξ ≤
            stateMass Ξ * ENNReal.ofReal (v f (S \ T).card * ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ)))))
    {S T : Finset (Fin (2 ^ n))} (hS : S.card = k) (hTS : T ⊆ S) (hr2 : 2 ≤ (S \ T).card)
    (hstep_K : ∀ pBad : ℝ, 0 ≤ pBad → pBad ≤ min 1 (((S \ T).card.choose 2 : ℝ) / (2 ^ d : ℝ)) →
      ((K : ℝ) + 1) / ((π / 4) * √(2 ^ (n - d) : ℝ)) +
        (1 - pBad) * (∑ j ∈ Finset.range ((S \ T).card + 1),
          ((S \ T).card.choose j : ℝ) * (1 - p_succ_set K (n - d) 1) ^ j *
            (p_succ_set K (n - d) 1) ^ ((S \ T).card - j) * v f j) +
        pBad * v f (S \ T).card ≤ v (f + 1) (S \ T).card)
    (Ξ : CQState (Store Var) (2 ^ Q)) :
    let circ :=
      OracleDynamicCircuit.seq (resetAllCircuit res)
        (.seq (sampleSeedCircuit res n Q ((n + 1) * m) hseed)
          (dispBits res (2 * n) 0 fun uVal ↦
            if hu : uVal < 2 ^ (2 * n) then
              let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
              if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
                stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo
                  stepCfg useSelf2 f T
              else
                let perm := GF2nForallA.finAffinePerm hn0
                  (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
                  (GF2nForallA.seedToGFPair hn0 u).2
                .seq (resetAllCircuit res) (.seq (deflateCirc n m T (permOracleCirc n m perm
                        (subcubePassCircuit res n m (n - d) d Q (Nat.sub_add_cancel hd_le) hm
                          horQ K)))
                    (dispBits res ((n + 1) * m) 0 fun wVal ↦
                      if hw : wVal < 2 ^ ((n + 1) * m) then
                        let H := (hitSetOfOracleOutcome n m ⟨wVal, hw⟩).map
                          perm.symm.toEmbedding
                        stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ
                          optTwo stepCfg useSelf2 f (T ∪ H)
                      else .skip))
            else .skip))
    𝔼[(interp (circ.compile QProg.qAssign (parallelMarkingOracle m S))).toStateFun Ξ, liftPureProp
      (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace ∧ expectedCost
      (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) (circ.compile QProg.qAssign
      (parallelMarkingOracle m S)) Ξ ≤ stateMass Ξ * ENNReal.ofReal (v (f + 1) (S \ T).card * ((π
      / 4) * √((2 ^ n : ℝ) / (m : ℝ)))) := by
  intro circ; let s := n - d; have hsd : s + d = n := Nat.sub_add_cancel hd_le; let R := S \ T
  let r := R.card
  have hr_eq : k - T.card = r := by
    dsimp only [r, R]; have hadd := Finset.card_sdiff_add_card_eq_card hTS; omega
  have hr_le : r ≤ k := (by rw [← hr_eq]; exact Nat.sub_le k T.card)
  let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
  have hm_pos : (0 : ℝ) < m := (by exact_mod_cast (show 0 < m by omega))
  have hu_nn : 0 ≤ unit := (by dsimp [unit]; positivity)
  have hu_pos : 0 < unit := by
    dsimp [unit]; exact mul_pos (div_pos Real.pi_pos (by norm_num))
      (Real.sqrt_pos.mpr (div_pos (by positivity) hm_pos))
  have hunit_s : (π / 4) * √(2 ^ s : ℝ) = unit := by
    dsimp only [unit]; congr 1
    have hdiv : (2 ^ n : ℝ) / (m : ℝ) = (2 ^ s : ℝ) := by
      rw [hm, Nat.cast_pow, Nat.cast_ofNat, ← hsd, pow_add]
      exact mul_div_cancel_right₀ _ (by positivity)
    rw [hdiv]
  let eCF : ℝ := ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * (1 - p_succ_set K s 1) ^ j *
    (p_succ_set K s 1) ^ (r - j) * v f j
  have heCF_nn : 0 ≤ eCF := by
    dsimp only [eCF]; refine Finset.sum_nonneg fun j hj ↦ ?_
    have hjk : j ≤ k := (by have := Finset.mem_range.mp hj; omega)
    have hp0 := p_succ_set_nonneg K s 1
    have hp1 : 0 ≤ 1 - p_succ_set K s 1 := sub_nonneg.mpr (p_succ_set_le_one K s 1)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp1 j)) (pow_nonneg hp0
      _)) (hv_nn_f j hjk)
  have horacle : IsRealMatrix (parallelMarkingOracle m S).1 := isRealMatrix_parallelMarkingOracle S
  let postS : CQAssertion (Store Var) (2 ^ Q) := liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ
    res) = S)
  let modelS := CostModel.ofEmbeddedOracle (n := Q) (parallelMarkingOracle m S)
  have hrst0 := resetAllCircuit_transition res horacle Ξ
  set Ξ₁ := (interp ((resetAllCircuit res).compile QProg.qAssign
    (parallelMarkingOracle m S))).toStateFun Ξ
  set Ξ₂ := (interp ((sampleSeedCircuit res n Q ((n + 1) * m) hseed).compile
    QProg.qAssign (parallelMarkingOracle m S))).toStateFun Ξ₁
  let uBranch (uVal : ℕ) : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
    if hu : uVal < 2 ^ (2 * n) then
      let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩
      if ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0 then
        stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg useSelf2 f T
      else
        let perm := GF2nForallA.finAffinePerm hn0 (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1
          ha) (GF2nForallA.seedToGFPair hn0 u).2
        .seq (resetAllCircuit res)
          (.seq (deflateCirc n m T
              (permOracleCirc n m perm (subcubePassCircuit res n m s d Q hsd hm horQ K)))
            (dispBits res ((n + 1) * m) 0 fun wVal ↦
              if hw : wVal < 2 ^ ((n + 1) * m) then
                let H := (hitSetOfOracleOutcome n m ⟨wVal, hw⟩).map perm.symm.toEmbedding
                stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo
                  stepCfg useSelf2 f (T ∪ H)
              else .skip))
    else .skip
  have huBranch (uVal : ℕ) (hu : uVal < 2 ^ (2 * n)) :
      open Classical in
      let u : Fin (2 ^ (2 * n)) := ⟨uVal, hu⟩; let Δ_sl := sliceState res 0 (2 * n) uVal Ξ₂
      𝔼[(interp ((uBranch uVal).compile QProg.qAssign
          (parallelMarkingOracle m S))).toStateFun Δ_sl, postS] =
        (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace ∧
        expectedCost modelS
          ((uBranch uVal).compile QProg.qAssign (parallelMarkingOracle m S)) Δ_sl ≤
          stateMass Ξ * ENNReal.ofReal
            ((1 / (2 ^ (2 * n) : ℝ)) * (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ)) +
                (if IsCFSeed hn0 s d hsd R u then eCF else v f r)) * unit) := by
    classical
    intro u Δ_sl
    have htr_sl : (Δ_sl.trace : ℝ) = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := by
      have hs_tr := sampleSeed_sliceState_trace res n Q ((n + 1) * m) hseed
        (parallelMarkingOracle m S) hrst0.2.2.2 hu
      rw [hrst0.2.1] at hs_tr; exact hs_tr
    have hmass_sl : stateMass Δ_sl = stateMass Ξ * ENNReal.ofReal (1 / (2 ^ (2 * n) : ℝ)) := by
      rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_sl, mul_comm,
        ENNReal.ofReal_mul (CQState.trace_nonneg _)]
    dsimp only [uBranch]; rw [dite_eq_left hu]; by_cases ha : (GF2nForallA.seedToGFPair hn0 u).1 = 0
    · rw [dite_eq_left ha]; have hncf : ¬ IsCFSeed hn0 s d hsd R u := fun ⟨ha', _⟩ ↦ ha' ha
      rw [ite_eq_right hncf]; obtain ⟨hc_f, hcost_f⟩ := ih_f hS hTS Δ_sl
      refine ⟨hc_f.trans htr_sl, hcost_f.trans ?_⟩
      rw [hmass_sl, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) (stateMass Ξ)
      have hpass_nn : 0 ≤ ((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ)) := by
        rw [hunit_s]; exact div_nonneg (by positivity) hu_pos.le
      change (1 / (2 ^ (2 * n) : ℝ)) * (v f r * unit) ≤ _
      have h1 : (1 / (2 ^ (2 * n) : ℝ)) * (v f r * unit) =
          (1 / (2 ^ (2 * n) : ℝ)) * v f r * unit := by ring
      have h2 : (1 / (2 ^ (2 * n) : ℝ)) *
            (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ)) + v f r) * unit =
          (1 / (2 ^ (2 * n) : ℝ)) * v f r * unit + (1 / (2 ^ (2 * n) : ℝ)) *
              (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ))) * unit := by ring
      rw [h1, h2]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by positivity) hpass_nn) hu_nn)
    · rw [dite_eq_right ha]
      let perm := GF2nForallA.finAffinePerm hn0 (Units.mk0 (GF2nForallA.seedToGFPair hn0 u).1 ha)
        (GF2nForallA.seedToGFPair hn0 u).2
      obtain ⟨hc_p, hcost_p⟩ := stage2FromSet_permPass_step res hm_grid hk_grid hm2 hm hd_le hQ
        optTwo stepCfg useSelf2 v f K horQ hv_nn_f hv_mono_f ih_f hS hTS perm htr_sl
      refine ⟨hc_p, hcost_p.trans ?_⟩
      refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
      apply le_of_eq; dsimp only [s, R, r, eCF, unit]; congr 2; congr 1
      have hiff : Set.InjOn (fun y ↦ (subcubeSplitEquiv (n - d) d (Nat.sub_add_cancel hd_le) y).2)
        (((S \ T).map perm.toEmbedding : Finset (Fin (2 ^ n))) : Set (Fin (2 ^ n))) ↔ IsCFSeed hn0
        (n - d) d (Nat.sub_add_cancel hd_le) (S \ T) u := by
        dsimp only [IsCFSeed, perm]; exact ⟨fun hinj ↦ ⟨ha, hinj⟩, fun ⟨_, hinj⟩ ↦ hinj⟩
      by_cases h : IsCFSeed hn0 (n - d) d (Nat.sub_add_cancel hd_le) (S \ T) u
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]
  refine ⟨?_, ?_⟩
  · dsimp only [circ]
    simp only [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
    change 𝔼[(interp ((dispBits res (2 * n) 0 uBranch).compile QProg.qAssign
      (parallelMarkingOracle m S))).toStateFun Ξ₂, postS] = Ξ.trace
    rw [expect_dispBits]
    have hterms : ∀ uVal ∈ Finset.range (2 ^ (2 * n)), 𝔼[(interp ((uBranch uVal).compile
      QProg.qAssign (parallelMarkingOracle m S))).toStateFun (sliceState res 0 (2 * n) uVal Ξ₂),
      postS] = (1 / (2 ^ (2 * n) : ℝ)) * Ξ.trace := fun uVal hu ↦ (huBranch uVal
      (Finset.mem_range.mp hu)).1
    rw [Finset.sum_congr rfl hterms, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc]
    have hpow_ne : (2 ^ (2 * n) : ℝ) ≠ 0 := (by positivity)
    rw [mul_one_div_cancel hpow_ne, one_mul]
  · classical
    dsimp only [circ]; simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
    change expectedCost modelS _ Ξ + (expectedCost modelS _ Ξ₁ + expectedCost modelS ((dispBits
      res (2 * n) 0 uBranch).compile QProg.qAssign (parallelMarkingOracle m S)) Ξ₂) ≤ _
    rw [hrst0.1, expectedCost_sampleSeedCircuit res n Q ((n + 1) * m) hseed horacle Ξ₁,
      zero_add, zero_add, expectedCost_dispBits]
    let seedTerm (u : Fin (2 ^ (2 * n))) : ℝ := (1 / (2 ^ (2 * n) : ℝ)) * (((K : ℝ) + 1) / ((π /
      4) * √(2 ^ s : ℝ)) + (if IsCFSeed hn0 s d hsd R u then eCF else v f r)) * unit
    have hseedTerm_nn (u : Fin (2 ^ (2 * n))) : 0 ≤ seedTerm u := by
      dsimp only [seedTerm]; refine mul_nonneg (mul_nonneg (by positivity) (add_nonneg ?_ ?_)) hu_nn
      · rw [hunit_s]; exact div_nonneg (by positivity) hu_pos.le
      · split_ifs
        · exact heCF_nn
        · exact hv_nn_f r hr_le
    calc (∑ uVal ∈ Finset.range (2 ^ (2 * n)), expectedCost modelS ((uBranch uVal).compile
          QProg.qAssign (parallelMarkingOracle m S)) (sliceState res 0 (2 * n) uVal Ξ₂)) ≤ ∑ uVal
          ∈ Finset.range (2 ^ (2 * n)), stateMass Ξ * ENNReal.ofReal (if hu : uVal < 2 ^ (2 * n)
          then seedTerm ⟨uVal, hu⟩ else 0) := by
          refine Finset.sum_le_sum fun uVal hu ↦ ?_
          have hlt := Finset.mem_range.mp hu; rw [dite_eq_left hlt]; exact (huBranch uVal hlt).2
      _ = stateMass Ξ * ∑ u : Fin (2 ^ (2 * n)), ENNReal.ofReal (seedTerm u) := by
          rw [← Finset.mul_sum]; congr 1
          refine Finset.sum_bij (fun uVal hu ↦ ⟨uVal, Finset.mem_range.mp hu⟩)
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ congrArg Fin.val h)
            (fun u _ ↦ ⟨u.val, Finset.mem_range.mpr u.isLt, rfl⟩)
            fun uVal hu ↦ by simp [Finset.mem_range.mp hu]
      _ = stateMass Ξ * ENNReal.ofReal (∑ u : Fin (2 ^ (2 * n)), seedTerm u) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun u _ ↦ hseedTerm_nn u]
      _ ≤ stateMass Ξ * ENNReal.ofReal (v (f + 1) r * unit) := by
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
          let bad := (Finset.univ : Finset (Fin (2 ^ (2 * n)))).filter
            (fun u ↦ ¬ IsCFSeed hn0 s d hsd R u)
          let good := (Finset.univ : Finset (Fin (2 ^ (2 * n)))).filter
            (fun u ↦ IsCFSeed hn0 s d hsd R u)
          let pBad : ℝ := (bad.card : ℝ) / (2 ^ (2 * n) : ℝ)
          have hpBad_nn : 0 ≤ pBad := (by dsimp [pBad]; positivity)
          have hpBad_hi : pBad ≤ min 1 ((r.choose 2 : ℝ) / (2 ^ d : ℝ)) :=
            badSeeds_div_le_min_boole hn0 hsd hr2
          have hunion_ug : (Finset.univ : Finset (Fin (2 ^ (2 * n)))) = good ∪ bad := by
            dsimp only [good, bad]; ext u
            simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
            exact Classical.em _
          have hdisj_ug : Disjoint good bad := by
            rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2 h1
          have hcard_ug : (good.card : ℝ) + (bad.card : ℝ) = (2 ^ (2 * n) : ℝ) := by
            have hc : good.card + bad.card = 2 ^ (2 * n) := by
              rw [← Finset.card_union_of_disjoint hdisj_ug, ← hunion_ug,
                Finset.card_univ, Fintype.card_fin]
            exact_mod_cast hc
          have hgood_div : (good.card : ℝ) / (2 ^ (2 * n) : ℝ) = 1 - pBad := by
            dsimp only [pBad]; have hpow_ne : (2 ^ (2 * n) : ℝ) ≠ 0 := (by positivity)
            rw [eq_sub_iff_add_eq, ← add_div, hcard_ug, div_self hpow_ne]
          have hseed_eval : (∑ u : Fin (2 ^ (2 * n)), seedTerm u) = (((K : ℝ) + 1) / ((π / 4) *
            √(2 ^ s : ℝ)) + (1 - pBad) * eCF + pBad * v f r) * unit := by
            have hpull : (∑ u : Fin (2 ^ (2 * n)), seedTerm u) = (1 / (2 ^ (2 * n) : ℝ)) * (∑ u :
              Fin (2 ^ (2 * n)), (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ)) + if IsCFSeed hn0 s d
              hsd R u then eCF else v f r)) * unit := by
              dsimp only [seedTerm]; rw [Finset.mul_sum, Finset.sum_mul]
            rw [hpull]; congr 1
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
            have hsplit_ug : (∑ u : Fin (2 ^ (2 * n)), if IsCFSeed hn0 s d hsd R u then eCF else v
              f r) = (∑ u ∈ good, if IsCFSeed hn0 s d hsd R u then eCF else v f r) + (∑ u ∈ bad,
              if IsCFSeed hn0 s d hsd R u then eCF else v f r) := by
              rw [hunion_ug, Finset.sum_union hdisj_ug]
            have hsg : (∑ u ∈ good, if IsCFSeed hn0 s d hsd R u then eCF else v f r) =
                (good.card : ℝ) * eCF := by
              calc (∑ u ∈ good, if IsCFSeed hn0 s d hsd R u then eCF else v f r) = ∑ _u ∈ good,
                    eCF := Finset.sum_congr rfl fun u hu ↦ ite_eq_left (Finset.mem_filter.mp hu).2
                _ = (good.card : ℝ) * eCF := by rw [Finset.sum_const, nsmul_eq_mul]
            have hsb : (∑ u ∈ bad, if IsCFSeed hn0 s d hsd R u then eCF else v f r) =
                (bad.card : ℝ) * v f r := by
              calc (∑ u ∈ bad, if IsCFSeed hn0 s d hsd R u then eCF else v f r) = ∑ _u ∈ bad, v f
                    r := Finset.sum_congr rfl fun u hu ↦ ite_eq_right (Finset.mem_filter.mp hu).2
                _ = (bad.card : ℝ) * v f r := by rw [Finset.sum_const, nsmul_eq_mul]
            rw [hsplit_ug, hsg, hsb]; have hpow_ne : (2 ^ (2 * n) : ℝ) ≠ 0 := (by positivity)
            have hg_eq : (1 / (2 ^ (2 * n) : ℝ)) * (good.card : ℝ) = 1 - pBad := by
              rw [one_div_mul_eq_div, hgood_div]
            have hb_eq : (1 / (2 ^ (2 * n) : ℝ)) * (bad.card : ℝ) = pBad := by
              rw [one_div_mul_eq_div]
            calc 1 / (2 ^ (2 * n) : ℝ) *
                  ((2 ^ (2 * n) : ℝ) * (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ))) +
                    ((good.card : ℝ) * eCF + (bad.card : ℝ) * v f r))
                = ((1 / (2 ^ (2 * n) : ℝ)) * (2 ^ (2 * n) : ℝ)) *
                    (((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ))) +
                  ((1 / (2 ^ (2 * n) : ℝ)) * (good.card : ℝ)) * eCF +
                  ((1 / (2 ^ (2 * n) : ℝ)) * (bad.card : ℝ)) * v f r := by ring
              _ = ((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ)) +
                  (1 - pBad) * eCF + pBad * v f r := by
                  rw [one_div_mul_cancel hpow_ne, one_mul, hg_eq, hb_eq]
          rw [hseed_eval]; exact mul_le_mul_of_nonneg_right (hstep_K pBad hpBad_nn hpBad_hi) hu_nn
/-- Pointwise `∀ (S, T)` soundness and Bellman cost induction for `stage2FromSetCircuit`
  across
  all `fuel` layers (`600 ≤ n`, `m = 2 ^ d`, `2 ≤ m`). -/
theorem stage2FromSet_transition {Var : Type} [DecidableEq Var] (res : Var) {n m d k Q : ℕ} (hn :
    600 ≤ n) (hm_grid : m ∈ GroverSol.groverGrid) (hk_grid : k ∈ GroverSol.groverGrid)
    (hm2 : 2 ≤ m) (hm : m = 2 ^ d) (hd_le : d ≤ n) (hQ : findAllQubits n m k ≤ Q) (optTwo : Option
    (Finset (Fin (2 ^ n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))) (stepCfg
    : ℕ → ℕ → Option ℕ) (useSelf2 : ℕ → Bool) (v : ℕ → ℕ → ℝ) (fuel : ℕ) (hv_nn : ∀ f ≤ fuel, ∀ r
    ≤ k, 0 ≤ v f r) (hv_mono : ∀ f < fuel, ∀ i j, i ≤ j → j ≤ k → v f i ≤ v f j) (hv_self2 : ∀ f ≤
    fuel, useSelf2 f = true → ∃ cTwo, optTwo = some cTwo ∧ ∀ S : Finset (Fin (2 ^ n)), S.card = k
    → ∀ T ⊆ S, (S \ T).card = 2 → ∀ Ξ : CQState (Store Var) (2 ^ Q), 𝔼[(interp ((cTwo T).compile
    QProg.qAssign (parallelMarkingOracle m S))).toStateFun Ξ, liftPureProp (fun τ ↦
    decodeTargetsLocal n k (τ res) = S)] = Ξ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle
    (parallelMarkingOracle m S)) ((cTwo T).compile QProg.qAssign (parallelMarkingOracle m S)) Ξ ≤
    stateMass Ξ * ENNReal.ofReal (v f 2 * ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ))))) (hv_base : ∀ r ≤
    k, ¬ (r = 2 ∧ useSelf2 0 = true) → (818309887 / 10 ^ 9 : ℝ) *
    GroverSol.groverHarmonicSqrtSum r ≤ v 0 r) (hv_r_lt2 : ∀ f < fuel, ∀ r < 2, r ≤ k →
    (818309887 / 10 ^ 9 : ℝ) * GroverSol.groverHarmonicSqrtSum r ≤ v (f + 1) r) (hv_keep : ∀
    f < fuel, ∀ r, 2 ≤ r → r ≤ k → ¬ (r = 2 ∧ useSelf2 (f + 1) = true) → stepCfg f r = none → v f
    r ≤ v (f + 1) r) (hv_step : ∀ f < fuel, ∀ r, 2 ≤ r → r ≤ k → ¬ (r = 2 ∧ useSelf2 (f + 1) =
    true) → ∀ K, stepCfg f r = some K → ∀ pBad : ℝ, 0 ≤ pBad → pBad ≤ min 1 ((r.choose 2 : ℝ) / (2
    ^ d : ℝ)) → ((K : ℝ) + 1) / ((π / 4) * √(2 ^ (n - d) : ℝ)) + (1 - pBad) * (∑ j ∈ Finset.range
    (r + 1), (r.choose j : ℝ) * (1 - p_succ_set K (n - d) 1) ^ j * (p_succ_set K (n - d) 1) ^ (r -
    j) * v f j) + pBad * v f r ≤ v (f + 1) r) : ∀ {S T : Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S
    → ∀ Ξ : CQState (Store Var) (2 ^ Q),
        let prog :=
          (stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo stepCfg useSelf2
            fuel T).compile QProg.qAssign (parallelMarkingOracle m S)
        𝔼[(interp prog).toStateFun Ξ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Ξ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Ξ ≤
          stateMass Ξ * ENNReal.ofReal (v fuel (S \ T).card * ((π / 4) * √((2 ^ n : ℝ) / (m :
          ℝ)))) := by
  induction fuel with
  | zero =>
      intro S T hS hTS Ξ; let r := (S \ T).card
      have hr_eq : k - T.card = r := (by have hadd := Finset.card_sdiff_add_card_eq_card hTS; omega)
      have hr_le : r ≤ k := (by rw [← hr_eq]; exact Nat.sub_le k T.card)
      let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
      have hu_nn : 0 ≤ unit := (by dsimp [unit]; positivity)
      rw [stage2FromSetCircuit.eq_def]; dsimp only; rw [hr_eq]
      by_cases hself : (r == 2 && useSelf2 0) = true
      · rw [ite_eq_left hself]; simp only [Bool.and_eq_true, beq_iff_eq] at hself
        obtain ⟨cTwo, hopt, hcTwo⟩ := hv_self2 0 le_rfl hself.2
        have hcard2 : (S \ T).card = 2 := hself.1; rw [hopt, hcard2]
        exact hcTwo S hS T hTS hcard2 Ξ
      · rw [ite_eq_right hself]
        have hnself : ¬ (r = 2 ∧ useSelf2 0 = true) := by
          rintro ⟨hr2, hu0⟩; apply hself; simp [hr2, hu0]
        obtain ⟨hcorr0, hcost0⟩ := stage2Fuel0_transition res hn hm_grid hk_grid hQ hS hTS Ξ
        refine ⟨hcorr0, hcost0.trans ?_⟩
        exact mul_le_mul_right
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hv_base r hr_le hnself) hu_nn)) _
  | succ f ih =>
      have ih_f :
          ∀ {S T : Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S → ∀ Ξ : CQState (Store Var) (2 ^ Q),
              let prog := (stage2FromSetCircuit res n m d k Q hm_grid hk_grid hm hd_le hQ optTwo
                stepCfg useSelf2 f T).compile QProg.qAssign (parallelMarkingOracle m S)
              𝔼[(interp prog).toStateFun Ξ,
                  liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace ∧
                expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Ξ ≤
                  stateMass Ξ *
                    ENNReal.ofReal (v f (S \ T).card * ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ)))) :=
        ih
          (fun f' hf' ↦ hv_nn f' (Nat.le_succ_of_le hf'))
          (fun f' hf' ↦ hv_mono f' (Nat.lt_succ_of_lt hf'))
          (fun f' hf' ↦ hv_self2 f' (Nat.le_succ_of_le hf'))
          (fun f' hf' ↦ hv_r_lt2 f' (Nat.lt_succ_of_lt hf'))
          (fun f' hf' ↦ hv_keep f' (Nat.lt_succ_of_lt hf'))
          (fun f' hf' ↦ hv_step f' (Nat.lt_succ_of_lt hf'))
      intro S T hS hTS Ξ; let R := S \ T; let r := R.card
      have hr_eq : k - T.card = r := by
        dsimp only [r, R]; have hadd := Finset.card_sdiff_add_card_eq_card hTS; omega
      have hr_le : r ≤ k := (by rw [← hr_eq]; exact Nat.sub_le k T.card)
      let unit := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
      have hm_pos : (0 : ℝ) < m := (by exact_mod_cast (show 0 < m by omega))
      have hu_nn : 0 ≤ unit := (by dsimp [unit]; positivity)
      have hu_pos : 0 < unit := by
        dsimp [unit]; exact mul_pos (div_pos Real.pi_pos (by norm_num))
          (Real.sqrt_pos.mpr (div_pos (by positivity) hm_pos))
      rw [stage2FromSetCircuit.eq_def]; dsimp only; rw [hr_eq]
      by_cases hself : (r == 2 && useSelf2 (f + 1)) = true
      · rw [ite_eq_left hself]; simp only [Bool.and_eq_true, beq_iff_eq] at hself
        obtain ⟨cTwo, hopt, hcTwo⟩ := hv_self2 (f + 1) le_rfl hself.2
        have hcard2 : (S \ T).card = 2 := hself.1; rw [hopt, hcard2]
        exact hcTwo S hS T hTS hcard2 Ξ
      · rw [ite_eq_right hself]
        have hnself : ¬ (r = 2 ∧ useSelf2 (f + 1) = true) := by
          rintro ⟨hr2, huf⟩; apply hself; simp [hr2, huf]
        by_cases hrlt : r < 2
        · rw [ite_eq_left hrlt]
          obtain ⟨hcorr0, hcost0⟩ := stage2Fuel0_transition res hn hm_grid hk_grid hQ hS hTS Ξ
          refine ⟨hcorr0, hcost0.trans ?_⟩
          exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hv_r_lt2 f
            (Nat.lt_succ_self f) r hrlt hr_le) hu_nn)) _
        · rw [ite_eq_right hrlt]; have hr2 : 2 ≤ r := (by omega)
          cases hcfg : stepCfg f r with
          | none =>
              obtain ⟨hcorr_prev, hcost_prev⟩ := ih_f hS hTS Ξ
              refine ⟨hcorr_prev, hcost_prev.trans ?_⟩
              exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
                (hv_keep f (Nat.lt_succ_self f) r hr2 hr_le hnself hcfg) hu_nn)) _
          | some K =>
              dsimp only; have hn0 : n ≠ 0 := (by omega); rw [dite_eq_right hn0, dite_eq_left hm2]
              exact stage2FromSet_someK_step res hn0 hm_grid hk_grid hm2 hm hd_le hQ
                (by unfold findAllQubits at hQ; nlinarith)
                (by unfold findAllQubits at hQ; omega)
                optTwo stepCfg useSelf2 v f K
                (hv_nn f (Nat.le_succ f)) (hv_mono f (Nat.lt_succ_self f))
                ih_f hS hTS hr2
                (hv_step f (Nat.lt_succ_self f) r hr2 hr_le hnself K hcfg) Ξ
/-- Grover step count `K:= ⌊(phi2Q6 / 10 ^ 6) / (2 * halfAngleSet s 1)⌋` for a `10 ^
  6`-scaled
  target rotation angle `phi2Q6` on a `2 ^ s`-element subcube. -/
noncomputable def kStepOfPhi2Q6 (s phi2Q6 : ℕ) : ℕ :=
  Nat.floor (((phi2Q6 : ℝ) / 1000000) / (2 * halfAngleSet s 1))
/-- Angle-enclosure and normalized query-cost bounds for `K:= kStepOfPhi2Q6 s phi2Q6`
  whenever
  `84 ≤ s` (satisfied for all `n ≥ 600` and `d ≤ 10`), matching `MultiTapCert.q6AngleIv18`
  and
  `MultiTapCert.agl1Step_bound` verbatim. -/
theorem kStepOfPhi2Q6_bounds {s phi2Q6 : ℕ} (hs : 84 ≤ s) :
    let K := kStepOfPhi2Q6 s phi2Q6
    (((phi2Q6 : ℝ) * 10 ^ 12 - 10 ^ 6) / 10 ^ 18 ≤ (2 * (K : ℝ) + 1) * halfAngleSet s 1) ∧ ((2 *
      (K : ℝ) + 1) * halfAngleSet s 1 ≤ ((phi2Q6 : ℝ) * 10 ^ 12 + 10 ^ 6) / 10 ^ 18) ∧ (((K : ℝ) +
      1) / ((π / 4) * √(2 ^ s : ℝ)) ≤ 2 * (((phi2Q6 : ℝ) * 10 ^ 12 + 10 ^ 6) / 10 ^ 18) / π) := by
  intro K; set θ := halfAngleSet s 1
  set φ := (phi2Q6 : ℝ) / 1000000; have h1_le : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hsin_θ : Real.sin θ = 1 / √(2 ^ s : ℝ) := by
    rw [sin_halfAngleSet h1_le, Nat.cast_one, Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hsin_pos : 0 < Real.sin θ := (by rw [hsin_θ]; positivity)
  have hθ_nonneg : 0 ≤ θ := Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  have hθ_pi2 : θ ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hθ_pos : 0 < θ := by
    by_contra hle
    have h0 : θ = 0 := le_antisymm (not_lt.mp hle) hθ_nonneg; rw [h0, Real.sin_zero] at hsin_pos
    exact lt_irrefl 0 hsin_pos
  have h2θ_pos : 0 < 2 * θ := (by positivity)
  have hsin_le_θ : 1 / √(2 ^ s : ℝ) ≤ θ := (by rw [← hsin_θ]; exact Real.sin_le hθ_nonneg)
  have hjordan := Real.mul_le_sin hθ_nonneg hθ_pi2; rw [hsin_θ] at hjordan
  have hsqrt_ge : (2 ^ 42 : ℝ) ≤ √(2 ^ s : ℝ) := by
    have hsq : ((2 ^ 42 : ℝ)) ^ 2 ≤ (2 ^ s : ℝ) := by
      calc ((2 ^ 42 : ℝ)) ^ 2 = (2 ^ 84 : ℝ) := by norm_num
        _ ≤ (2 ^ s : ℝ) := pow_le_pow_right₀ (by norm_num) hs
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 ^ s by positivity), Real.sqrt_nonneg (2 ^ s : ℝ)]
  have h2θ_le : 2 * θ ≤ (10 ^ 6 : ℝ) / 10 ^ 18 := by
    have hpi_pos : (0 : ℝ) < π := Real.pi_pos; have hpi_hi : π < 4 := Real.pi_lt_four
    have h1 : θ ≤ (π / 2) * (1 / √(2 ^ s : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hjordan (show (0 : ℝ) ≤ π / 2 by positivity)
      have hc : (π / 2) * (2 / π * θ) = θ := (by field_simp [hpi_pos.ne']); linarith
    have h2 : 1 / √(2 ^ s : ℝ) ≤ 1 / (2 ^ 42 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hsqrt_ge
    have h3 : (π / 2) * (1 / √(2 ^ s : ℝ)) ≤ 2 * (1 / (2 ^ 42 : ℝ)) := by
      calc (π / 2) * (1 / √(2 ^ s : ℝ))
          ≤ (π / 2) * (1 / (2 ^ 42 : ℝ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 2 * (1 / (2 ^ 42 : ℝ)) := by nlinarith
    have h4 : 4 * (1 / (2 ^ 42 : ℝ)) ≤ (10 ^ 6 : ℝ) / 10 ^ 18 := (by norm_num); linarith
  have hθ_le : θ ≤ (10 ^ 6 : ℝ) / 10 ^ 18 := (by linarith)
  have hφ_nn : 0 ≤ φ := div_nonneg (Nat.cast_nonneg phi2Q6) (by norm_num)
  have hfloor_lo : (K : ℝ) * (2 * θ) ≤ φ := by
    have hfl : (K : ℝ) ≤ φ / (2 * θ) := Nat.floor_le (div_nonneg hφ_nn h2θ_pos.le)
    exact (le_div_iff₀ h2θ_pos).mp hfl
  have hfloor_hi : φ < ((K : ℝ) + 1) * (2 * θ) := by
    have hlt := Nat.lt_floor_add_one (φ / (2 * θ)); exact (div_lt_iff₀ h2θ_pos).mp hlt
  have hφ_lo_eq : ((phi2Q6 : ℝ) * 10 ^ 12 - 10 ^ 6) / 10 ^ 18 = φ - (10 ^ 6 : ℝ) / 10 ^ 18 := by
    dsimp only [φ]; ring
  have hφ_hi_eq : ((phi2Q6 : ℝ) * 10 ^ 12 + 10 ^ 6) / 10 ^ 18 = φ + (10 ^ 6 : ℝ) / 10 ^ 18 := by
    dsimp only [φ]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hφ_lo_eq]; linarith
  · rw [hφ_hi_eq]; linarith
  · rw [hφ_hi_eq]; have hpi_pos : (0 : ℝ) < π := Real.pi_pos
    have hK_div : ((K : ℝ) + 1) / √(2 ^ s : ℝ) ≤ ((K : ℝ) + 1) * θ := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsin_le_θ (by positivity)
    have h2K1_θ : 2 * (((K : ℝ) + 1) * θ) ≤ φ + (10 ^ 6 : ℝ) / 10 ^ 18 := (by linarith)
    calc ((K : ℝ) + 1) / ((π / 4) * √(2 ^ s : ℝ))
        = (4 / π) * (((K : ℝ) + 1) / √(2 ^ s : ℝ)) := by field_simp [hpi_pos.ne']
      _ ≤ (4 / π) * (((K : ℝ) + 1) * θ) := mul_le_mul_of_nonneg_left hK_div (by positivity)
      _ = (2 / π) * (2 * (((K : ℝ) + 1) * θ)) := by ring
      _ ≤ (2 / π) * (φ + (10 ^ 6 : ℝ) / 10 ^ 18) :=
          mul_le_mul_of_nonneg_left h2K1_θ (by positivity)
      _ = 2 * (φ + (10 ^ 6 : ℝ) / 10 ^ 18) / π := by ring
end QuantumComputation.Specs.GroverFindAll.MultiTapStage2
end
end Sec_MultiTapStage2AGL1QHL
