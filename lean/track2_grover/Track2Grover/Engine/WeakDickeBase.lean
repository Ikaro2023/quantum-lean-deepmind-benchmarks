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

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.PowerLawCost
public import QuantumComputation.Circuits.DynamicCircuit
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.Dedup
public import QuantumComputation.Algorithms.Grover.Amplitude
public import QuantumComputation.Maths.Trigonometry
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.Algorithms.Grover.Operators
public import QuantumComputation.Primitives.Hadamard
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Track2Grover.Engine.SpecDefs

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

section WD_Defs
section
open Operator
open scoped Matrix
private theorem wp_measureRegister_coe {Var : Type} [DecidableEq Var] {n k : ℕ}
    (res : Var) (r : QRegister k n) (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) :
    (wp (QProg.measureRegister res r) Θ σ).1 =
      ∑ o : Fin (2 ^ k),
        HermitianMat.conj (r.basisOutcomeProjector o)ᴴ
          (Θ (Store.subst σ res ↑o.val)).1 :=
  rfl
end

@[expose] public section

namespace QuantumComputation.Specs.DickeSol

open Operator ResourceCounting Real
open scoped Matrix NNReal NNRat

/-! ## Exact Spec Mirrors (`rfl` bridge with `QuantumComputation.Specs`) -/

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

/-! ## Dyadic Grid Selectors and Membership Lemmas -/

/-- Full `11 × 11` dyadic grid selector claiming every `(m, k) ∈ groverGrid × groverGrid`. -/
def gridCells (m k : ℕ) : Bool :=
  decide (m ∈ groverGrid) && decide (k ∈ groverGrid)

theorem one_le_of_mem_groverGrid {x : ℕ} (hx : x ∈ groverGrid) : 1 ≤ x := by
  simp only [groverGrid, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact Nat.one_le_two_pow

theorem gridCells_nonempty : ∃ m k, gridCells m k = true :=
  ⟨1, 1, by simp only [gridCells, groverGrid, Bool.and_eq_true, decide_eq_true_eq,
    Finset.mem_image, Finset.mem_range]; exact ⟨⟨0, by omega, rfl⟩, ⟨0, by omega, rfl⟩⟩⟩

theorem gridCells_mem_grid {m k : ℕ} (hmk : gridCells m k = true) :
    m ∈ groverGrid ∧ k ∈ groverGrid := by
  simpa [gridCells] using hmk

/-! ## Global-Phase Unitary Tagging for `CostModel.ofEmbeddedOracle` -/

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

theorem wdExpectItePartition {Var : Type} {d : ℕ}
    (b : Store Var → Prop) [DecidablePred b] (Δ : CQState (Store Var) d) (θt θf : CQAssertion (Store
      Var) d) :
    expect Δ (fun σ ↦ if b σ then θt σ else θf σ) =
      expect (Δ.restrict b) θt + expect (Δ.restrict (¬ b ·)) θf :=
  expect_ite_partition b Δ θt θf

theorem wdActiveIter0 {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d) (state : CQState (Store
      Var) d) :
    activeIter guard body 0 state = state.restrict guard :=
  activeIter_zero guard body state

theorem wdActiveIterS {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d) (n : ℕ)
    (state : CQState (Store Var) d) :
    activeIter guard body (n + 1) state =
      activeIter guard body n ((interp body).toStateFun (state.restrict guard)) :=
  activeIter_succ guard body n state

theorem wdExpectedCostIf {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (model : CostModel d) (condition : Store Var → Prop) [DecidablePred condition]
    (yes no : QProg Var d) (state : CQState (Store Var) d) :
    expectedCost model (.qIf condition yes no) state =
      expectedCost model yes (state.restrict condition) +
        expectedCost model no (state.restrict (¬ condition ·)) :=
  expectedCost_qIf model condition yes no state

end QuantumComputation.Specs.DickeSol

namespace CQState

variable {Var : Type} {d : ℕ}

/-- Classical-quantum state restricted to stores satisfying `cond`. -/
noncomputable abbrev wdTrueSt (cond : Store Var → Prop) [DecidablePred cond]
    (Δ : CQState (Store Var) d) : CQState (Store Var) d :=
  Δ.restrict cond

/-- Classical-quantum state restricted to stores falsifying `cond`. -/
noncomputable abbrev wdFalseSt (cond : Store Var → Prop) [DecidablePred cond]
    (Δ : CQState (Store Var) d) : CQState (Store Var) d :=
  Δ.restrict (¬ cond ·)

end CQState
end
end WD_Defs

section WD_OddParityBridge
@[expose] public section

namespace QuantumComputation.Specs.DickeSol

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
  apply (basisBits 1).injective; funext i; rw [Subsingleton.elim i 0, basisBits_slotFlag]
  rw [hE, Pi.zero_apply, basisBits_eq_div_mod]; simp

theorem slotFlag_eq_one {n m : ℕ} (z : Fin (2 ^ (m * (n + 1))))
    (hE : ((addrReg n m).basisSplitEquiv z).2 = 1) (j : Fin m) :
    slotFlag n m z j = 1 := by
  apply (basisBits 1).injective; funext i; rw [Subsingleton.elim i 0, basisBits_slotFlag]
  rw [hE, Pi.one_apply, basisBits_eq_div_mod]; simp

/-! ## Flag-Basis Conjugation and Single-Slot Phase Oracle -/

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
    rw [ite_eq_left rfl, ite_eq_left h1, Int.cast_mul]; ring
  have hPδ : (xu ∈ S ∧ bu = 0) ↔ (δ = 1 ∧ bu = 0) := by
    by_cases hS : xu ∈ S <;> simp [δ, hS]
  have hfs : ∀ δ b₁ b₂ : Fin (2 ^ 1),
      (∑ k : Fin (2 ^ 1), flagSign b₁ (k + δ) * flagSign k b₂) =
        if b₁ = b₂ then (if δ = 1 ∧ b₁ = 0 then -2 else 2) else 0 := by
    intro δ b₁ b₂
    have hc (q : Fin (2 ^ 1)) : q = 0 ∨ q = 1 := by
      rcases q with ⟨v, hv⟩; change v < 2 at hv; interval_cases v
      · exact Or.inl (Fin.ext (by simp))
      · exact Or.inr (Fin.ext (by simp))
    have h01 : (0 : Fin (2 ^ 1)) ≠ 1 := fun h ↦ by have v := congrArg Fin.val h; simp at v
    have h11 : (1 : Fin (2 ^ 1)) + 1 = 0 := Fin.ext (by simp)
    have huniv : (Finset.univ : Finset (Fin (2 ^ 1))) = {0, 1} := by ext q; simp [hc q]
    rw [huniv, Finset.sum_pair h01]
    rcases hc δ with rfl | rfl <;> rcases hc b₁ with rfl | rfl <;>
      rcases hc b₂ with rfl | rfl <;>
      simp only [zero_add, add_zero, h11, flagSign, h01, h01.symm, and_self, and_false,
        false_and, ↓reduceIte] <;> norm_num
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
    rw [ite_eq_right hb, Matrix.diagonal_apply_ne _ huv]; norm_num)

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
      generalize flagSign (splitBasisEquiv n 1 u).2 (splitBasisEquiv n 1 v).2 = s; simp)
    else (by rw [ite_eq_right (Ne.symm h), ite_eq_right h, star_zero])
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, hcj]
  rw [hO, mul_one, show diagonal (slotDiag n ∅) = 1 by
    ext i j
    simp [slotDiag, Matrix.diagonal_apply, Matrix.one_apply]] at h0
  exact h0

/-! ## Odd-Parity Target-Tuple Subset, Density, and Phase Step -/

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
        ite_eq_right fun h ↦ by have v := congrArg Fin.val h.2; simp at v]]
  simp only [one_mul]

/-! ## Joint Flag-Flip Permutation and First-Slot Flag Probe -/

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
      rw [show (⟨0, by omega⟩ : Fin 1) = 0 from rfl, basisBits_slotFlag, basisBits_extractIndex]
      rfl)
  have h0 : (flag0Reg n m hm).basisOutcomeProjector 0 *ᵥ ψ = r.tensorState v₀ (single 0 1) := by
    dsimp only [r, ψ]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mulVec_add,
      diagonal_mulVec_tensorState _ (fun _ ↦ 1) v₀ 0 fun z hz ↦ by
        rw [hfl z, slotFlag_eq_zero z hz ⟨0, hm⟩, ite_eq_left rfl],
      diagonal_mulVec_tensorState _ (fun _ ↦ 0) v₁ 1 fun z hz ↦ by
        rw [hfl z, slotFlag_eq_one z hz ⟨0, hm⟩,
          ite_eq_right fun h ↦ by have v := congrArg Fin.val h; simp at v]]
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
  rw [HermitianMat.val_eq_coe, wp_measureRegister_coe, HermitianMat.mat_finset_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  simp [HermitianMat.val_eq_coe,
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
        res ((whole Q).computationalBasisMeasurement : Measurement (2 ^ Q) (2 ^ Q))
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

end QuantumComputation.Specs.DickeSol
end
end WD_OddParityBridge

section WD_FindAllBridge
@[expose] public section

namespace QuantumComputation.Specs.DickeSol

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

/-! ## Low/High Register Splitting and `workMemState` Product Vectors -/

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

/-! ## `memReg` Layout, `decodeTargets` Bridge, and Reversible Target Recording -/

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

/-! ## Deflated Parallel Marking Conjugation (`S \ memSeen`) -/

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
    exact Fin.ext (by have hb : b.val < 2 := b.isLt; simp only [Fin.val_add, Fin.val_one]; omega)
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

/-! ## `b`-Group Slot Partition (`b * g = m`), `Fin.find` Readout, and `Sym(R)` Uniformity -/

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

end QuantumComputation.Specs.DickeSol
end
end WD_FindAllBridge

section WD_SubsetEigLock
@[expose] public section

namespace QuantumComputation.Specs.DickeSol

open Operator Real
open QRegister (tensorState)
open Matrix (diagonal mulVec_diagonal star_eq_conjTranspose conjTranspose_apply)
open Complex (normSq)
open Pi (single)
open scoped Matrix NNReal NNRat

/-! ## Grid Upper Bound and Harmonic Decomposition of `vanillaFindAllCost` -/

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

/-! ## Positivity and Collision Bounds for `oddFrac` -/

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

/-! ## Density-Parametrized Stationary Stationary-chord Schedule and Query Bounds -/

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

/-! ## Subset Grover State and Kraus Eigenvector Analysis -/

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

/-! ## Collective `m`-Flag Involutive Chord Unitary -/

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

end QuantumComputation.Specs.DickeSol
end
end WD_SubsetEigLock

section WD_FindAllBatchRound

namespace QuantumComputation.Specs.DickeSol

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
open scoped Matrix NNReal ENNReal ComplexOrder MatrixOrder QProg.Notation InnerProductSpace
  QHLExpectation

@[expose] public section

/-! ## Multi-Target Grover Success Probabilities and i.i.d. Group/Coupon Laws -/

/-- Exact Grover success probability after `K` iterations on `t` marked items out of `D`. -/
noncomputable def p_succ_frac (K t D : ℕ) : ℝ :=
  Real.sin ((2 * (K : ℝ) + 1) * Real.arcsin (√((t : ℝ) / (D : ℝ)))) ^ 2

@[simp]
theorem p_succ_frac_zero_mid (K D : ℕ) : p_succ_frac K 0 D = 0 := by
  simp [p_succ_frac]

/-- Single-group odd-parity Grover success probability after `K` iterations on `g` slots
  with `r`
  remaining targets, depending on `R` only through `r = R.card` (`card_oddSet_div_two_pow`). -/
noncomputable def groupSuccProb (n g r K : ℕ) : ℝ :=
  Real.sin ((2 * (K : ℝ) + 1) * Real.arcsin (√(oddFrac n g r))) ^ 2

theorem p_succ_frac_card_oddSet_eq_groupSuccProb (n g K : ℕ) (R : Finset (Fin (2 ^ n))) :
    p_succ_frac K (oddSet n g R).card (2 ^ (g * n)) = groupSuccProb n g R.card K := by
  unfold p_succ_frac groupSuccProb
  rw [Nat.cast_pow, Nat.cast_ofNat, card_oddSet_div_two_pow]

theorem groupSuccProb_nonneg (n g r K : ℕ) : 0 ≤ groupSuccProb n g r K :=
  sq_nonneg _

theorem groupSuccProb_le_one (n g r K : ℕ) : groupSuccProb n g r K ≤ 1 :=
  Real.sin_sq_le_one _

/-- Single-group readout probability on `Option (Fin (2 ^ n))` after `K` Grover iterations:
  hits each `x ∈ R` uniformly with probability `groupSuccProb n g R.card K / R.card`, and
  returns
  `none` with probability `1 - groupSuccProb n g R.card K`. -/
noncomputable def groupDrawProb (n g : ℕ) (R : Finset (Fin (2 ^ n))) (K : ℕ) :
    Option (Fin (2 ^ n)) → ℝ
  | none => 1 - groupSuccProb n g R.card K
  | some x => if x ∈ R then groupSuccProb n g R.card K / (R.card : ℝ) else 0

/-- Product probability of `b` independent single-group readouts on
  `Fin b → Option (Fin (2 ^ n))`. -/
noncomputable def iidTupleProb {b : ℕ} (n g : ℕ) (R : Finset (Fin (2 ^ n))) (K : ℕ)
    (os : Fin b → Option (Fin (2 ^ n))) : ℝ :=
  ∏ c : Fin b, groupDrawProb n g R K (os c)

/-- Deduplicated list of newly discovered targets from a `b`-tuple of `Option` group
  readouts. -/
def tupleNewHits {n b : ℕ} (os : Fin b → Option (Fin (2 ^ n))) : List (Fin (2 ^ n)) :=
  ((finRange b).filterMap os).dedup

/-- Canonical `R`-independent single-group coupon draw on `Option (Fin r)`. -/
noncomputable def couponDrawProb (n g r K : ℕ) : Option (Fin r) → ℝ
  | none => 1 - groupSuccProb n g r K
  | some _ => groupSuccProb n g r K / (r : ℝ)

/-- Canonical `R`-independent `b`-fold product coupon law on `Fin b → Option (Fin r)`. -/
noncomputable def iidCouponProb {b : ℕ} (n g r K : ℕ) (cs : Fin b → Option (Fin r)) : ℝ :=
  ∏ c : Fin b, couponDrawProb n g r K (cs c)

theorem couponDrawProb_nonneg (n g r K : ℕ) (o : Option (Fin r)) :
    0 ≤ couponDrawProb n g r K o := by
  cases o with
  | none => exact sub_nonneg.mpr (groupSuccProb_le_one n g r K)
  | some _ => exact div_nonneg (groupSuccProb_nonneg n g r K) (Nat.cast_nonneg _)

theorem sum_couponDrawProb_eq_one (n g r K : ℕ) :
    (∑ o : Option (Fin r), couponDrawProb n g r K o) = 1 := by
  rw [Fintype.sum_option]
  dsimp only [couponDrawProb]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [groupSuccProb, oddFrac]
  · have hpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
    rw [mul_div_cancel₀ _ hpos.ne']
    ring

theorem iidCouponProb_nonneg {b : ℕ} (n g r K : ℕ) (cs : Fin b → Option (Fin r)) :
    0 ≤ iidCouponProb n g r K cs :=
  Finset.prod_nonneg fun c _ ↦ couponDrawProb_nonneg n g r K (cs c)

theorem sum_iidCouponProb_eq_one {b : ℕ} (n g r K : ℕ) :
    (∑ cs : Fin b → Option (Fin r), iidCouponProb n g r K cs) = 1 := by
  unfold iidCouponProb
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun _ _ ↦ sum_couponDrawProb_eq_one n g r K

private lemma dedup_length_filterMap_option_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) {γ : Type*} (l : List γ) (g : γ → Option α) :
    ((l.filterMap fun c ↦ (g c).map f).dedup).length = ((l.filterMap g).dedup).length := by
  have hmap : l.filterMap (fun c ↦ (g c).map f) = (l.filterMap g).map f := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases hga : g a <;> simp [hga, ih]
  rw [hmap, List.dedup_map_of_injective hf, List.length_map]

/-- Any function of the distinct-hit count `(tupleNewHits os).length` under `iidTupleProb n
  g R K`
  equals the canonical `R`-independent expectation over `cs: Fin b → Option (Fin R.card)`. -/
theorem sum_iidTupleProb_length_eq_sum_iidCouponProb {b : ℕ} (n g : ℕ)
    (R : Finset (Fin (2 ^ n))) (K : ℕ) (h : ℕ → ℝ) :
    (∑ os : Fin b → Option (Fin (2 ^ n)), iidTupleProb n g R K os * h (tupleNewHits os).length) =
      ∑ cs : Fin b → Option (Fin R.card),
        iidCouponProb n g R.card K cs * h (((finRange b).filterMap cs).dedup).length := by
  let e : Fin R.card ≃ R := (Finset.equivFin R).symm
  let emb (i : Fin R.card) : Fin (2 ^ n) := (e i).1
  have hemb : Function.Injective emb := fun i j hij ↦ e.injective (Subtype.ext hij)
  let lift (cs : Fin b → Option (Fin R.card)) : Fin b → Option (Fin (2 ^ n)) :=
    fun c ↦ (cs c).map emb
  have hlift_inj : Function.Injective lift := by
    intro cs₁ cs₂ heq
    funext c
    exact Option.map_injective hemb (congrFun heq c)
  have hprob (cs : Fin b → Option (Fin R.card)) :
      iidTupleProb n g R K (lift cs) = iidCouponProb n g R.card K cs := by
    unfold iidTupleProb iidCouponProb
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    dsimp only [lift]
    cases hcs : cs c with
    | none => rfl
    | some i =>
      dsimp only [Option.map, groupDrawProb, couponDrawProb]
      exact ite_eq_left (e i).2
  have hlen (cs : Fin b → Option (Fin R.card)) :
      (tupleNewHits (lift cs)).length = (((finRange b).filterMap cs).dedup).length :=
    dedup_length_filterMap_option_map hemb (finRange b) cs
  simp_rw [← hprob, ← hlen]
  rw [← Finset.sum_image (f := fun os ↦ iidTupleProb n g R K os * h (tupleNewHits os).length)
    (s := Finset.univ) (g := lift) (fun _ _ _ _ heq ↦ hlift_inj heq)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun os _ hos ↦ ?_
  have hzero : iidTupleProb n g R K os = 0 := by
    by_contra hne
    apply hos
    have hall (c : Fin b) : ∀ x, os c = some x → x ∈ R := by
      intro x hx
      by_contra hxR
      apply hne
      unfold iidTupleProb
      refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
      rw [hx, groupDrawProb, ite_eq_right hxR]
    let cs : Fin b → Option (Fin R.card) := fun c ↦
      match hosc : os c with
      | none => none
      | some x => some (e.symm ⟨x, hall c x hosc⟩)
    refine Finset.mem_image.mpr ⟨cs, Finset.mem_univ _, funext fun c ↦ ?_⟩
    dsimp only [lift, cs]
    split
    · rename_i hosc
      rw [hosc]
      rfl
    · rename_i x hosc
      dsimp only [Option.map, emb]
      rw [Equiv.apply_symm_apply]
      exact hosc.symm
  rw [hzero, zero_mul]

/-- Write a batch `L: List (Fin (2 ^ n))` sequentially into `memReg` starting at slot `s`. -/
def writeMemBatch {n k : ℕ} (s : ℕ) (L : List (Fin (2 ^ n)))
    (μ : Fin (2 ^ (k * n))) : Fin (2 ^ (k * n)) :=
  (addrEquiv n k).symm
    (addrEquiv n k μ + fun j ↦ if s ≤ j.val then (L[j.val - s]?).getD 0 else 0)

theorem memPrefixValid_writeMemBatch {n k s : ℕ} {S : Finset (Fin (2 ^ n))}
    (hcard : S.card = k) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s μ)
    {L : List (Fin (2 ^ n))} (hnodup : L.Nodup)
    (hnew : ∀ x ∈ L, x ∈ S \ memSeen n k (memPrefix k s) μ) :
    s + L.length ≤ k ∧ MemPrefixValid S (s + L.length) (writeMemBatch s L μ) := by
  have hseen := card_memSeen_of_memPrefixValid hval
  have hadd := Finset.card_sdiff_add_card_eq_card hseen.2
  have hsub : L.toFinset ⊆ S \ memSeen n k (memPrefix k s) μ := fun x hx ↦
    hnew x (List.mem_toFinset.mp hx)
  have hlenL : L.length ≤ (S \ memSeen n k (memPrefix k s) μ).card := by
    rw [← List.toFinset_card_of_nodup hnodup]
    exact Finset.card_le_card hsub
  have hlen : s + L.length ≤ k := by omega
  exact ⟨hlen, memPrefixValid_batchAdvance (W := 0) hval (fun _ ↦ L) 0 hnodup hlen hnew⟩

/-- Global basis index pairing `w: Fin (2 ^ (m * (n + 1)))` on `workReg` with
  `μ: Fin (2 ^ (k * n))` on `memReg`. -/
def workMemIdx (n m k : ℕ) (w : Fin (2 ^ (m * (n + 1)))) (μ : Fin (2 ^ (k * n))) :
    Fin (2 ^ (m * (n + 1) + k * n)) :=
  (lowHighEquiv (m * (n + 1)) (k * n)).symm (w, μ)

@[simp]
theorem lowHighEquiv_workMemIdx (n m k : ℕ) (w : Fin (2 ^ (m * (n + 1))))
    (μ : Fin (2 ^ (k * n))) :
    lowHighEquiv (m * (n + 1)) (k * n) (workMemIdx n m k w μ) = (w, μ) :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem workMemIdx_zero (n m k : ℕ) : workMemIdx n m k 0 0 = 0 := by
  unfold workMemIdx
  rw [← lowHighEquiv_zero (m * (n + 1)) (k * n), Equiv.symm_apply_apply]

/-- Clamped updated active target count `min k (active + (groupHits hbg w).length)`,
  embedded as a
  computational-basis index in `Fin (2 ^ (m * (n + 1)))`. -/
def batchNextCount {n m k b g : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n)
    (hbg : b * g = m) (active : ℕ) (w : Fin (2 ^ (m * (n + 1)))) :
    Fin (2 ^ (m * (n + 1))) :=
  ⟨min k (active + (groupHits hbg w).length), by
    have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
    have hklt : k < 2 ^ (n + 1) := by
      rw [pow_succ]
      omega
    have hpow : 2 ^ (n + 1) ≤ 2 ^ (m * (n + 1)) :=
      Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_left (n + 1) hm)
    exact lt_of_le_of_lt (Nat.min_le_left _ _) (lt_of_lt_of_le hklt hpow)⟩

end

public section

/-! ## Multi-Target Grover State Evolution and Single-Group Fiber Probabilities -/

private noncomputable def groverMultiReal {q : ℕ} (M : Finset (Fin (2 ^ q))) :
    ℕ → Fin (2 ^ q) → ℝ
  | 0 => fun _ ↦ 1 / √(2 ^ q : ℝ)
  | k + 1 => fun u ↦
      let w := fun v : Fin (2 ^ q) ↦
        if v ∈ M then -groverMultiReal M k v else groverMultiReal M k v
      (2 / (2 ^ q : ℝ)) * (∑ v : Fin (2 ^ q), w v) - w u

/-- Multi-target Grover state vector on `q` qubits after `k` iterations of `(D * O_M)`. -/
noncomputable def groverMultiState {q : ℕ} (M : Finset (Fin (2 ^ q))) :
    ℕ → Fin (2 ^ q) → ℂ
  | 0 => fun _ ↦ (1 / √(2 ^ q : ℝ) : ℂ)
  | k + 1 => Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ groverMultiState M k)

lemma groverMultiState_succ {q : ℕ} (M : Finset (Fin (2 ^ q))) (k : ℕ) :
    groverMultiState M (k + 1) =
      Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ groverMultiState M k) := by rfl

lemma groverMultiState_zero_eq_hadamard_mulVec {q : ℕ} (M : Finset (Fin (2 ^ q))) :
    groverMultiState M 0 = hadamardMatrix q *ᵥ single 0 1 := by
  funext u
  have h := congrFun (mulVec_single_one (hadamardMatrix q) 0) u
  rw [h, col_apply, hadamardMatrix_apply_zero]
  simp [groverMultiState]

private noncomputable def oracleMat_unitary {q : ℕ} (M : Finset (Fin (2 ^ q))) :
    Unitary (2 ^ q) :=
  ⟨oracleMat M, by
    rw [oracleMat, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro u
    split_ifs <;> simp⟩

lemma sum_normSq_groverMultiState_eq_one {q : ℕ} (M : Finset (Fin (2 ^ q))) (k : ℕ) :
    (∑ u : Fin (2 ^ q), normSq (groverMultiState M k u)) = 1 := by
  induction k with
  | zero =>
    rw [groverMultiState_zero_eq_hadamard_mulVec]
    have hu := sum_normSq_unitary_mulVec (hadamardUnitary (q := q)) (single 0 1)
    change (∑ i, normSq ((hadamardMatrix q *ᵥ single 0 1) i)) = _ at hu
    rw [hu, sum_eq_single 0 (fun u hu ↦ by rw [Pi.single_eq_of_ne hu, Complex.normSq_zero])]
    simp
  | succ k ih =>
    rw [groverMultiState_succ]
    have h1 :=
      sum_normSq_unitary_mulVec Grover.diffuserUnitary (oracleMat M *ᵥ groverMultiState M k)
    change (∑ i, normSq ((Grover.diffuserMatrix *ᵥ (oracleMat M *ᵥ groverMultiState M k)) i)) = _
      at h1
    have h2 := sum_normSq_unitary_mulVec (oracleMat_unitary M) (groverMultiState M k)
    change (∑ i, normSq ((oracleMat M *ᵥ groverMultiState M k) i)) = _ at h2
    rw [h1, h2, ih]

private lemma groverMultiState_eq_ofReal {q : ℕ} (M : Finset (Fin (2 ^ q))) (k : ℕ)
    (u : Fin (2 ^ q)) : groverMultiState M k u = (groverMultiReal M k u : ℂ) := by
  induction k generalizing u with
  | zero => simp [groverMultiState, groverMultiReal]
  | succ k ih =>
    unfold groverMultiState groverMultiReal
    have horac (v : Fin (2 ^ q)) :
        (oracleMat M *ᵥ groverMultiState M k) v =
          ((if v ∈ M then -groverMultiReal M k v else groverMultiReal M k v : ℝ) : ℂ) := by
      rw [oracleMat, mulVec_diagonal, ih v]
      split_ifs <;> push_cast <;> ring
    rw [Grover.diffuserMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Matrix.mulVec, dotProduct]
    simp only [Matrix.of_apply, horac, ← Finset.mul_sum]
    push_cast; rfl

private lemma groverMultiReal_eq_of_mem {q : ℕ} {M : Finset (Fin (2 ^ q))} (k : ℕ)
    {u₁ u₂ : Fin (2 ^ q)} (h₁ : u₁ ∈ M) (h₂ : u₂ ∈ M) :
    groverMultiReal M k u₁ = groverMultiReal M k u₂ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold groverMultiReal
    dsimp only
    rw [ite_eq_left h₁, ite_eq_left h₂, ih]

private lemma groverMultiReal_sums {q : ℕ} (M : Finset (Fin (2 ^ q))) (k : ℕ) :
    let θ := Real.arcsin (√((M.card : ℝ) / (2 ^ q : ℝ)))
    (∑ u ∈ M, groverMultiReal M k u) = √(M.card : ℝ) * Real.sin ((2 * (k : ℝ) + 1) * θ) ∧
      (∑ u : Fin (2 ^ q), groverMultiReal M k u) = √(2 ^ q : ℝ) * Real.cos (2 * (k : ℝ) * θ) := by
  intro θ
  set D : ℝ := (2 ^ q : ℝ)
  set t : ℝ := (M.card : ℝ)
  have hD_pos : 0 < D := by positivity
  have ht_nonneg : 0 ≤ t := Nat.cast_nonneg _
  have ht_le_D : t ≤ D := by
    have hc : M.card ≤ (Finset.univ : Finset (Fin (2 ^ q))).card := Finset.card_le_univ M
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have hcast : (M.card : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := Nat.cast_le.mpr hc
    simpa [t, D] using hcast
  have hfrac_nonneg : 0 ≤ t / D := div_nonneg ht_nonneg hD_pos.le
  have hfrac_le_one : t / D ≤ 1 := (div_le_one hD_pos).mpr ht_le_D
  have hsinθ : Real.sin θ = √(t / D) :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg (t / D)]) (Real.sqrt_le_one.mpr hfrac_le_one)
  have hsinθ_sq : Real.sin θ ^ 2 = t / D := by
    rw [hsinθ, Real.sq_sqrt hfrac_nonneg]
  have hsqrt_sin : √D * Real.sin θ = √t := by
    rw [hsinθ, Real.sqrt_div ht_nonneg, mul_div_cancel₀ _ (Real.sqrt_pos.mpr hD_pos).ne']
  have hcs : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := Real.cos_sq' θ
  induction k with
  | zero =>
    constructor
    · simp only [groverMultiReal, Finset.sum_const, nsmul_eq_mul, Nat.cast_zero, mul_zero,
        zero_add, one_mul]
      change t * (1 / √D) = √t * Real.sin θ
      rw [hsinθ, Real.sqrt_div ht_nonneg, mul_one_div]
      nth_rw 1 [← Real.mul_self_sqrt ht_nonneg]
      ring
    · simp only [groverMultiReal, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_mul,
        Real.cos_zero, mul_one]
      change D * (1 / √D) = √D
      nth_rw 1 [← Real.mul_self_sqrt hD_pos.le]
      field_simp
  | succ k ih =>
    rcases ih with ⟨ihM, ihAll⟩
    let w : Fin (2 ^ q) → ℝ := fun v ↦
      if v ∈ M then -groverMultiReal M k v else groverMultiReal M k v
    have hw_split (v : Fin (2 ^ q)) :
        w v = groverMultiReal M k v - if v ∈ M then 2 * groverMultiReal M k v else 0 := by
      dsimp only [w]
      split_ifs <;> ring
    have hsum_w : (∑ v : Fin (2 ^ q), w v) =
        (∑ v : Fin (2 ^ q), groverMultiReal M k v) - 2 * (∑ v ∈ M, groverMultiReal M k v) := by
      simp_rw [hw_split]
      rw [sum_sub_distrib, sum_ite_mem, univ_inter, ← mul_sum]
    set α : ℝ := 2 * (k : ℝ) * θ
    have hsin_step :
        Real.sin ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) =
          2 * Real.sin θ * Real.cos α + (1 - 4 * Real.sin θ ^ 2) * Real.sin (α + θ) := by
      rw [show (2 * ((k + 1 : ℕ) : ℝ) + 1) * θ = (α + θ) + (θ + θ) by push_cast; ring,
        Real.sin_add, Real.cos_add, Real.sin_add, Real.cos_add, Real.sin_add]
      linear_combination (Real.sin α * Real.cos θ + 3 * Real.cos α * Real.sin θ) * hcs
    have hcos_step :
        Real.cos (2 * ((k + 1 : ℕ) : ℝ) * θ) =
          Real.cos α - 2 * Real.sin θ * Real.sin (α + θ) := by
      rw [show 2 * ((k + 1 : ℕ) : ℝ) * θ = α + (θ + θ) by push_cast; ring,
        Real.cos_add, Real.cos_add, Real.sin_add, Real.sin_add]
      linear_combination Real.cos α * hcs
    have hα1 : (2 * (k : ℝ) + 1) * θ = α + θ := by ring
    constructor
    · have hM_step :
          (∑ u ∈ M, groverMultiReal M (k + 1) u) =
            t * ((2 / D) * (∑ v : Fin (2 ^ q), w v)) + ∑ u ∈ M, groverMultiReal M k u := by
        conv_lhs =>
          arg 2
          ext u
          rw [groverMultiReal]
        have hmem (u : Fin (2 ^ q)) (hu : u ∈ M) :
            (2 / (2 ^ q : ℝ)) * (∑ v : Fin (2 ^ q), w v) -
                (if u ∈ M then -groverMultiReal M k u else groverMultiReal M k u) =
              (2 / D) * (∑ v : Fin (2 ^ q), w v) + groverMultiReal M k u := by
          change (2 / D) * (∑ v : Fin (2 ^ q), w v) - _ = _
          rw [ite_eq_left hu]
          ring
        rw [Finset.sum_congr rfl hmem, sum_add_distrib, sum_const, nsmul_eq_mul]
      rw [hM_step, hsum_w, ihAll, ihM, hα1, hsin_step,
        show t * (2 / D * (√D * Real.cos α - 2 * (√t * Real.sin (α + θ)))) =
          2 * (t / D) * (√D * Real.cos α - 2 * √t * Real.sin (α + θ)) by ring,
        ← hsinθ_sq]
      linear_combination (2 * Real.sin θ * Real.cos α) * hsqrt_sin
    · have hall_step :
          (∑ u : Fin (2 ^ q), groverMultiReal M (k + 1) u) = ∑ v : Fin (2 ^ q), w v := by
        unfold groverMultiReal
        change (∑ u : Fin (2 ^ q), ((2 / D) * (∑ v : Fin (2 ^ q), w v) - w u)) = _
        rw [sum_sub_distrib, sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow, Nat.cast_ofNat]
        change D * (2 / D * ∑ v, w v) - ∑ v, w v = ∑ v, w v
        field_simp
        ring
      rw [hall_step, hsum_w, ihAll, ihM, hα1, hcos_step, ← hsqrt_sin]
      ring

private lemma card_mul_normSq_groverMultiState_of_mem {q : ℕ} {M : Finset (Fin (2 ^ q))}
    (K : ℕ) {u : Fin (2 ^ q)} (hu : u ∈ M) :
    (M.card : ℝ) * normSq (groverMultiState M K u) = p_succ_frac K M.card (2 ^ q) := by
  have hsum := (groverMultiReal_sums M K).1
  have hconst : (∑ v ∈ M, groverMultiReal M K v) = (M.card : ℝ) * groverMultiReal M K u := by
    rw [Finset.sum_congr rfl fun v hv ↦ groverMultiReal_eq_of_mem K hv hu, sum_const, nsmul_eq_mul]
  rw [hconst] at hsum
  have hsq := congrArg (· ^ 2) hsum
  have hpos : (0 : ℝ) < (M.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨u, hu⟩)
  rw [mul_pow, mul_pow, Real.sq_sqrt hpos.le] at hsq
  have hnsq : normSq (groverMultiState M K u) = groverMultiReal M K u ^ 2 := by
    rw [groverMultiState_eq_ofReal, Complex.normSq_ofReal, sq]
  rw [hnsq, p_succ_frac, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_left_cancel₀ hpos.ne' (by linarith)

lemma sum_mem_normSq_groverMultiState_eq_p_succ_frac {q : ℕ}
    (M : Finset (Fin (2 ^ q))) (K : ℕ) :
    (∑ u ∈ M, normSq (groverMultiState M K u)) = p_succ_frac K M.card (2 ^ q) := by
  rcases Finset.eq_empty_or_nonempty M with rfl | ⟨u₀, hu₀⟩
  · simp
  · have hconst (u : Fin (2 ^ q)) (hu : u ∈ M) :
        normSq (groverMultiState M K u) = normSq (groverMultiState M K u₀) := by
      rw [groverMultiState_eq_ofReal, groverMultiState_eq_ofReal,
        groverMultiReal_eq_of_mem K hu hu₀]
    rw [Finset.sum_congr rfl hconst, sum_const, nsmul_eq_mul]
    exact card_mul_normSq_groverMultiState_of_mem K hu₀

private lemma sum_normSq_filter_firstTupleHit_eq_groupDrawProb (n g : ℕ)
    (R : Finset (Fin (2 ^ n))) (K : ℕ) (o : Option (Fin (2 ^ n))) :
    (∑ u : Fin (2 ^ (g * n)) with firstTupleHit n g R u = o,
      normSq (groverMultiState (oddSet n g R) K u)) = groupDrawProb n g R K o := by
  set M := oddSet n g R
  cases o with
  | none =>
    have hiff (u : Fin (2 ^ (g * n))) : firstTupleHit n g R u = none ↔ u ∉ M := by
      rw [← Option.not_isSome_iff_eq_none, isSome_firstTupleHit_iff]
    have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M)
      (fun u ↦ normSq (groverMultiState M K u))
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at hpart
    have hfilt : (Finset.univ.filter fun u ↦ firstTupleHit n g R u = none) =
        Finset.univ.filter (· ∉ M) := Finset.filter_congr fun u _ ↦ hiff u
    rw [sum_mem_normSq_groverMultiState_eq_p_succ_frac M K,
      sum_normSq_groverMultiState_eq_one M K,
      p_succ_frac_card_oddSet_eq_groupSuccProb] at hpart
    rw [hfilt]
    dsimp only [groupDrawProb]
    linarith
  | some x =>
    dsimp only [groupDrawProb]
    by_cases hx : x ∈ R
    · rw [ite_eq_left hx]
      have hpos : (0 : ℝ) < (R.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x, hx⟩)
      have hsub : (Finset.univ.filter fun u ↦ firstTupleHit n g R u = some x) =
          M.filter fun u ↦ firstTupleHit n g R u = some x := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h ↦ ⟨(mem_of_firstTupleHit_eq_some h).1, h⟩, fun h ↦ h.2⟩
      rw [hsub]
      rcases Finset.eq_empty_or_nonempty M with hMe | ⟨u₀, hu₀⟩
      · have hcard0 : M.card = 0 := Finset.card_eq_zero.mpr hMe
        rw [hMe, Finset.filter_empty, Finset.sum_empty,
          ← p_succ_frac_card_oddSet_eq_groupSuccProb, show (oddSet n g R).card = 0 from hcard0,
          p_succ_frac_zero_mid, zero_div]
      · have hconst (u : Fin (2 ^ (g * n)))
            (hu : u ∈ M.filter fun u ↦ firstTupleHit n g R u = some x) :
            normSq (groverMultiState M K u) = normSq (groverMultiState M K u₀) := by
          rw [groverMultiState_eq_ofReal, groverMultiState_eq_ofReal,
            groverMultiReal_eq_of_mem K (Finset.mem_filter.mp hu).1 hu₀]
        rw [Finset.sum_congr rfl hconst, sum_const, nsmul_eq_mul, eq_div_iff hpos.ne']
        have hcard_mul := card_mul_card_oddSet_filter_firstTupleHit (n := n) (g := g) hx
        have hcast : ((R.card : ℝ) *
            ((M.filter fun u ↦ firstTupleHit n g R u = some x).card : ℝ)) = (M.card : ℝ) := by
          exact_mod_cast hcard_mul
        calc ((M.filter fun u ↦ firstTupleHit n g R u = some x).card : ℝ) *
              normSq (groverMultiState M K u₀) * (R.card : ℝ)
            = ((R.card : ℝ) *
                ((M.filter fun u ↦ firstTupleHit n g R u = some x).card : ℝ)) *
                normSq (groverMultiState M K u₀) := by ring
          _ = (M.card : ℝ) * normSq (groverMultiState M K u₀) := by rw [hcast]
          _ = p_succ_frac K M.card (2 ^ (g * n)) :=
              card_mul_normSq_groverMultiState_of_mem K hu₀
          _ = groupSuccProb n g R.card K := p_succ_frac_card_oddSet_eq_groupSuccProb n g K R
    · rw [ite_eq_right hx]
      refine Finset.sum_eq_zero fun u hu ↦ ?_
      exact absurd (mem_of_firstTupleHit_eq_some (Finset.mem_filter.mp hu).2).2 hx

/-! ## `b`-Group Disjoint Register Factorization (`hbg: b * g = m`) -/

/-- Equivalence splitting `m * (n + 1)` work wires into `b` groups of `g * (n + 1)` wires. -/
def groupSplitEquiv {n m b g : ℕ} (hbg : b * g = m) :
    Fin (2 ^ (m * (n + 1))) ≃ (Fin b → Fin (2 ^ (g * (n + 1)))) :=
  (finCongr (by rw [← hbg, Nat.mul_assoc])).trans (addrEquiv (g * (n + 1)) b)

theorem groupSplitEquiv_apply {n m b g : ℕ} (hbg : b * g = m)
    (w : Fin (2 ^ (m * (n + 1)))) (c : Fin b) :
    groupSplitEquiv hbg w c = (groupReg hbg c).extractIndex w := by
  apply (basisBits (g * (n + 1))).injective
  funext r
  have hL :
      basisBits (g * (n + 1)) (groupSplitEquiv hbg w c) r =
        basisBits (b * (g * (n + 1)))
          (finCongr (by rw [← hbg, Nat.mul_assoc]) w) (finProdFinEquiv (c, r)) := by
    simp [groupSplitEquiv, addrEquiv]
  rw [hL, basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
  simp only [finCongr_apply, Fin.val_cast, groupReg, QRegister.block_apply_val,
    finProdFinEquiv_apply_val]
  exact congrArg Nat.cast (congrArg (fun t ↦ (w.val / 2 ^ t) % 2) (by ring))

/-- Homogeneous `b`-fold tensor product state across `groupReg hbg c` (`c: Fin b`). -/
noncomputable def groupProdState {n m b g : ℕ} (hbg : b * g = m)
    (ξ : Fin (2 ^ (g * (n + 1))) → ℂ) : Fin (2 ^ (m * (n + 1))) → ℂ :=
  fun w ↦ ∏ c : Fin b, ξ ((groupReg hbg c).extractIndex w)

theorem groupProdState_single_zero {n m b g : ℕ} (hbg : b * g = m) :
    groupProdState (n := n) hbg (single 0 1) = single 0 1 := by
  have hex0 (c : Fin b) : (groupReg (n := n) hbg c).extractIndex 0 = 0 := by
    apply (basisBits (g * (n + 1))).injective
    funext r
    simp [basisBits_extractIndex]
  funext w
  unfold groupProdState
  by_cases hw : w = 0
  · subst hw
    simp [hex0]
  · rw [Pi.single_eq_of_ne hw]
    have hne : ∃ c : Fin b, (groupReg hbg c).extractIndex w ≠ 0 := by
      by_contra! hall
      apply hw
      apply (groupSplitEquiv hbg).injective
      funext c
      rw [groupSplitEquiv_apply, groupSplitEquiv_apply, hall c, hex0 c]
    obtain ⟨c, hc⟩ := hne
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    exact Pi.single_eq_of_ne (M := fun _ ↦ ℂ) hc (1 : ℂ)

lemma embedMatrix_groupReg_mulVec_prod {n m b g : ℕ} (hbg : b * g = m)
    (A : Matrix (Fin (2 ^ (g * (n + 1)))) (Fin (2 ^ (g * (n + 1)))) ℂ) (c₀ : Fin b)
    (f : Fin b → Fin (2 ^ (g * (n + 1))) → ℂ) :
    (groupReg hbg c₀).embedMatrix A *ᵥ
        (fun w ↦ ∏ c : Fin b, f c ((groupReg hbg c).extractIndex w)) =
      fun w ↦ ∏ c : Fin b,
        (if c = c₀ then A *ᵥ f c₀ else f c) ((groupReg hbg c).extractIndex w) := by
  funext w
  rw [QRegister.embedMatrix_mulVec_apply]
  let r₀ := groupReg (n := n) hbg c₀
  have hterm (u : Fin (2 ^ (g * (n + 1)))) :
      (∏ c : Fin b,
        f c ((groupReg hbg c).extractIndex (r₀.basisSplitEquiv.symm (u, (r₀.basisSplitEquiv w).2))))
        = f c₀ u * ∏ c ∈ Finset.univ.erase c₀, f c ((groupReg hbg c).extractIndex w) := by
    set w' := r₀.basisSplitEquiv.symm (u, (r₀.basisSplitEquiv w).2)
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c₀)]
    congr 1
    · have hex : r₀.extractIndex w' = u := by
        rw [← QRegister.basisSplitEquiv_apply_fst]
        dsimp only [w']
        rw [Equiv.apply_symm_apply]
      exact congrArg (f c₀) hex
    · refine Finset.prod_congr rfl fun c hc ↦ ?_
      have hne : c ≠ c₀ := Finset.ne_of_mem_erase hc
      have henv : (r₀.basisSplitEquiv w').2 = (r₀.basisSplitEquiv w).2 := by
        dsimp only [w']
        rw [Equiv.apply_symm_apply]
      have hagree : r₀.AgreeOutside w' w :=
        (QRegister.basisSplit_environment_eq_iff r₀ w' w).mp henv
      have hdisj := groupReg_disjointWires (n := n) hbg hne
      have hex_eq : (groupReg hbg c).extractIndex w' = (groupReg hbg c).extractIndex w := by
        apply (basisBits (g * (n + 1))).injective
        funext j
        rw [basisBits_extractIndex, basisBits_extractIndex]
        refine hagree _ ?_
        rintro ⟨j₀, hj₀⟩
        exact QRegister.disjoint_iff.mp hdisj j j₀ hj₀.symm
      exact congrArg (f c) hex_eq
  have hsum :
      (∑ u : Fin (2 ^ (g * (n + 1))),
        A (r₀.extractIndex w) u *
          ∏ c : Fin b,
            f c ((groupReg hbg c).extractIndex
              (r₀.basisSplitEquiv.symm (u, (r₀.basisSplitEquiv w).2)))) =
        ((A *ᵥ f c₀) (r₀.extractIndex w)) *
          ∏ c ∈ Finset.univ.erase c₀, f c ((groupReg hbg c).extractIndex w) := by
    change _ = (∑ u, A (r₀.extractIndex w) u * f c₀ u) * _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [hterm u, mul_assoc]
  refine hsum.trans ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c₀), ite_eq_left rfl]
  exact congrArg ((A *ᵥ f c₀) (r₀.extractIndex w) * ·)
    (Finset.prod_congr rfl fun c hc ↦
      congrFun (ite_eq_right (Finset.ne_of_mem_erase hc)).symm _)

theorem prod_groupReg_embedMatrix_mulVec_groupProdState {n m b g : ℕ} (hbg : b * g = m)
    (A : Matrix (Fin (2 ^ (g * (n + 1)))) (Fin (2 ^ (g * (n + 1)))) ℂ)
    (ξ : Fin (2 ^ (g * (n + 1))) → ℂ) :
    ((finRange b).map fun c ↦ (groupReg hbg c).embedMatrix A).prod *ᵥ groupProdState hbg ξ =
      groupProdState hbg (A *ᵥ ξ) := by
  suffices ∀ (l : List (Fin b)), l.Nodup →
      ((l.map fun c ↦ (groupReg hbg c).embedMatrix A).prod) *ᵥ
          (fun w ↦ ∏ c : Fin b, ξ ((groupReg hbg c).extractIndex w)) =
        fun w ↦ ∏ c : Fin b, (if c ∈ l then A *ᵥ ξ else ξ) ((groupReg hbg c).extractIndex w) by
    unfold groupProdState
    rw [this (finRange b) (List.nodup_finRange b)]
    funext w
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    rw [ite_eq_left (mem_finRange c)]
  intro l hl
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]
    funext w
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    rw [ite_eq_right List.not_mem_nil]
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

/-- Simultaneous address Hadamard preparation across all `b` groups on `workReg`. -/
noncomputable def groupPrepUnitary {n m b g : ℕ} (hbg : b * g = m) :
    Unitary (2 ^ (m * (n + 1))) :=
  ((finRange b).map fun c ↦
    (groupReg hbg c).embedUnitary ((addrReg n g).embedUnitary hadamardUnitary)).prod

/-- Simultaneous `(g * n)`-qubit Grover diffuser across all `b` groups on `workReg`. -/
noncomputable def groupDiffuserUnitary {n m b g : ℕ} (hbg : b * g = m) :
    Unitary (2 ^ (m * (n + 1))) :=
  ((finRange b).map fun c ↦
    (groupReg hbg c).embedUnitary ((addrReg n g).embedUnitary Grover.diffuserUnitary)).prod

/-! ## Zero-Ancilla Single-`res` Count-Advance & Work-Reset Gadget and `batchRound` -/

/-- Zero-query gadget on `W + M` qubits measuring `lowBlock W M` into `res`, updating `res`
  to
  `(f o).val` for outcome `o: Fin (2 ^ W)`, and resetting `lowBlock W M` to `|0⟩` while
  leaving
  `highBlock W M` untouched. -/
noncomputable def setCountAndResetWork {Var : Type} (res : Var) {W M O : ℕ}
    (f : Fin (2 ^ W) → Fin (2 ^ W)) : OracleCirc Var (W + M) O :=
  let r := lowBlock W M
  .seq (.measure res r)
    (dispFin res
      (fun o ↦
        .seq (.step (phaseTag (r.embedUnitary (permutationUnitary (swap o (f o))))))
          (.seq (.measure res r)
            (.step (phaseTag (r.embedUnitary (permutationUnitary (swap (f o) 0)))))))
      (finRange (2 ^ W)))

theorem costBound_setCountAndResetWork {Var : Type} [DecidableEq Var] (res : Var) {W M O : ℕ}
    (f : Fin (2 ^ W) → Fin (2 ^ W)) {oracle : Unitary (2 ^ O)}
    (horacle : IsRealMatrix oracle.1) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle (n := W + M) oracle)
      ((setCountAndResetWork (M := M) res f).compile qAssign oracle) 0 := by
  unfold setCountAndResetWork
  dsimp only [compile]
  have hmeas : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (n := W + M) oracle)
      (measureRegister res (lowBlock W M)) 0 := by
    simpa [measureRegister, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) (CostModel.ofEmbeddedOracle (n := W + M) oracle)
        res ((lowBlock W M).computationalBasisMeasurement :
          Measurement (2 ^ (W + M)) (2 ^ W))
  let br (o : Fin (2 ^ W)) : OracleCirc Var (W + M) O :=
    .seq (.step (phaseTag ((lowBlock W M).embedUnitary (permutationUnitary (swap o (f o))))))
      (.seq (.measure res (lowBlock W M))
        (.step (phaseTag ((lowBlock W M).embedUnitary (permutationUnitary (swap (f o) 0))))))
  suffices hd : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (n := W + M) oracle)
      ((dispFin res br (finRange (2 ^ W))).compile qAssign oracle) 0 by
    simpa using hmeas.seq hd
  generalize finRange (2 ^ W) = l
  induction l with
  | nil => exact CostBound.skip_zero _
  | cons hd _ ih =>
    dsimp only [dispFin, br, compile]
    have h1 := costBound_qAssign_phaseTag (Var := Var) horacle
      ((lowBlock W M).embedUnitary (permutationUnitary (swap hd (f hd))))
    have h2 := costBound_qAssign_phaseTag (Var := Var) horacle
      ((lowBlock W M).embedUnitary (permutationUnitary (swap (f hd) 0)))
    have hbr : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (n := W + M) oracle)
        (.qAssign (phaseTag ((lowBlock W M).embedUnitary (permutationUnitary (swap hd (f hd))))) ;;
          (measureRegister res (lowBlock W M) ;;
            .qAssign (phaseTag
              ((lowBlock W M).embedUnitary (permutationUnitary (swap (f hd) 0)))))) 0 := by
      simpa using h1.seq (hmeas.seq h2)
    simpa using CostBound.qIf _ hbr ih

private lemma resetKrausLocal_eq {W : ℕ} (f : Fin (2 ^ W) → Fin (2 ^ W))
    (o u : Fin (2 ^ W)) :
    (permutationUnitary (swap (f o) 0)).1 * compProj u *
        (permutationUnitary (swap o (f o))).1 * compProj o =
      if u = f o then Matrix.single 0 o 1 else 0 := by
  ext i j
  let M := (permutationUnitary (swap (f o) 0)).1 * compProj u *
    (permutationUnitary (swap o (f o))).1 * compProj o
  have hj : M i j = (M *ᵥ single j 1) i := by rw [mulVec_single_one, col_apply]
  change M i j = _
  rw [hj]
  dsimp only [M]
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, compProj_mulVec o (single j 1)]
  by_cases hjo : j = o
  · subst hjo
    rw [Pi.single_eq_same, permutationUnitary_mulVec_single, Equiv.swap_apply_left,
      compProj_mulVec u (single (f j) 1)]
    by_cases hu : u = f j
    · subst hu
      rw [ite_eq_left rfl, Pi.single_eq_same, permutationUnitary_mulVec_single,
        Equiv.swap_apply_left, Matrix.single_apply]
      by_cases hi0 : i = 0
      · subst hi0
        simp
      · simp [hi0, Ne.symm hi0]
    · rw [ite_eq_right hu, Pi.single_eq_of_ne hu, Pi.single_zero, Matrix.mulVec_zero,
        Matrix.zero_apply, Pi.zero_apply]
  · rw [Pi.single_eq_of_ne (Ne.symm hjo), Pi.single_zero,
      Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, Pi.zero_apply]
    split_ifs
    · rw [Matrix.single_apply, ite_eq_right (fun h ↦ hjo h.2.symm)]
    · simp

theorem wp_setCountAndResetWork {Var : Type} [DecidableEq Var] (res : Var) {W M O : ℕ}
    (f : Fin (2 ^ W) → Fin (2 ^ W)) (oracle : Unitary (2 ^ O))
    (Θ : CQAssertion (Store Var) (2 ^ (W + M))) (σ : Store Var) :
    ((wp ((setCountAndResetWork res f).compile qAssign oracle) Θ) σ).1.1 =
      ∑ o : Fin (2 ^ W),
        ((lowBlock W M).embedMatrix (Matrix.single 0 o 1))ᴴ *
          (Θ (Store.subst σ res (Int.ofNat (f o).val))).1.1 *
          (lowBlock W M).embedMatrix (Matrix.single 0 o 1) := by
  let r := lowBlock W M
  unfold setCountAndResetWork
  dsimp only [compile]
  rw [wp_qSeq, wp_measureRegister res r _ σ]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  set τ := Store.subst σ res (Int.ofNat o.val)
  have hτ : τ res = (o.val : ℤ) := by simp [τ]
  let br (x : Fin (2 ^ W)) : OracleCirc Var (W + M) O :=
    .seq (.step (phaseTag (r.embedUnitary (permutationUnitary (swap x (f x))))))
      (.seq (.measure res r)
        (.step (phaseTag (r.embedUnitary (permutationUnitary (swap (f x) 0))))))
  have hd (l : List (Fin (2 ^ W))) (ho : o ∈ l) :
      wp ((dispFin res br l).compile qAssign oracle) Θ τ =
        wp ((br o).compile qAssign oracle) Θ τ := by
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
  rw [hd (finRange (2 ^ W)) (mem_finRange o)]
  dsimp only [br, compile]
  rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val,
    wp_qSeq, wp_measureRegister res r _ τ]
  simp only [wp_qAssign, wp_phaseTag, qhlQAssign_val, embedUnitary_val, τ,
    Store.subst_subst_same_const]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  have hterm (u : Fin (2 ^ W)) :
      r.basisOutcomeProjector o *
          ((r.embedMatrix (permutationUnitary (swap o (f o))).1)ᴴ *
            (r.basisOutcomeProjector u *
              ((r.embedMatrix (permutationUnitary (swap (f o) 0)).1)ᴴ *
                (Θ (Store.subst σ res (Int.ofNat u.val))).1.1 *
                r.embedMatrix (permutationUnitary (swap (f o) 0)).1) *
              r.basisOutcomeProjector u) *
            r.embedMatrix (permutationUnitary (swap o (f o))).1) *
          r.basisOutcomeProjector o =
        if u = f o then
          (r.embedMatrix (Matrix.single 0 o 1))ᴴ *
            (Θ (Store.subst σ res (Int.ofNat u.val))).1.1 *
            r.embedMatrix (Matrix.single 0 o 1)
        else 0 := by
    have hK :
        r.embedMatrix (permutationUnitary (swap (f o) 0)).1 * r.basisOutcomeProjector u *
            r.embedMatrix (permutationUnitary (swap o (f o))).1 * r.basisOutcomeProjector o =
          r.embedMatrix
            ((permutationUnitary (swap (f o) 0)).1 * compProj u *
              (permutationUnitary (swap o (f o))).1 * compProj o) := by
      simp only [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_mul]
    have hassoc :
        r.basisOutcomeProjector o *
            ((r.embedMatrix (permutationUnitary (swap o (f o))).1)ᴴ *
              (r.basisOutcomeProjector u *
                ((r.embedMatrix (permutationUnitary (swap (f o) 0)).1)ᴴ *
                  (Θ (Store.subst σ res (Int.ofNat u.val))).1.1 *
                  r.embedMatrix (permutationUnitary (swap (f o) 0)).1) *
                r.basisOutcomeProjector u) *
              r.embedMatrix (permutationUnitary (swap o (f o))).1) *
            r.basisOutcomeProjector o =
          (r.embedMatrix (permutationUnitary (swap (f o) 0)).1 * r.basisOutcomeProjector u *
              r.embedMatrix (permutationUnitary (swap o (f o))).1 * r.basisOutcomeProjector o)ᴴ *
            (Θ (Store.subst σ res (Int.ofNat u.val))).1.1 *
            (r.embedMatrix (permutationUnitary (swap (f o) 0)).1 * r.basisOutcomeProjector u *
              r.embedMatrix (permutationUnitary (swap o (f o))).1 * r.basisOutcomeProjector o) := by
      simp only [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose, Matrix.mul_assoc]
    rw [hassoc, hK, resetKrausLocal_eq]
    split_ifs
    · rfl
    · simp
  simp_rw [hterm]
  rw [sum_eq_single (f o) (fun u hu ↦ ite_eq_right hu), ite_eq_left rfl]

/-- One simultaneous `b`-group Grover iteration (`deflatedPhaseStep` +
  `groupDiffuserUnitary`). -/
noncomputable def batchGroverStep {Var : Type} {n m k b g : ℕ}
    (hbg : b * g = m) (active : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k active))
    (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (groupDiffuserUnitary hbg))))

/-- `K` consecutive simultaneous `b`-group Grover iterations. -/
noncomputable def batchGroverLoop {Var : Type} {n m k b g : ℕ}
    (hbg : b * g = m) (active K : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  OracleDynamicCircuit.sequence (List.replicate K (batchGroverStep hbg active))

/-- Complete `S`-free simultaneous `b`-group projective Grover batch round on
  `m * (n + 1) + k * n` qubits (`K` phase calls + `1` clean readout call = `K + 1` oracle
  calls). -/
noncomputable def batchRound {Var : Type} (res : Var) {n m k b g : ℕ}
    (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hbg : b * g = m) (active K : ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (groupPrepUnitary hbg))))
    (.seq (batchGroverLoop hbg active K)
      (.seq (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active))
        (.seq (.step (phaseTag (permutationUnitary (memWriteBatchPerm active (groupHits hbg)))))
          (setCountAndResetWork res (batchNextCount hm hkN hbg active)))))

theorem costBound_batchRound {Var : Type} [DecidableEq Var] (res : Var) {n m k b g : ℕ}
    (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hbg : b * g = m) (active K : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((batchRound res hm hkN hbg active K).compile qAssign (groverParallelMarkingOracle m S))
      (K + 1) := by
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hloop : ∀ j : ℕ,
      CostBound (Var := Var)
        (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        ((batchGroverLoop (k := k) hbg active j).compile qAssign (groverParallelMarkingOracle m S))
        j := by
    intro j
    unfold batchGroverLoop
    induction j with
    | zero =>
      simpa using CostBound.skip_zero (Var := Var)
        (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    | succ j ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold batchGroverStep
      dsimp only [compile]
      have hstep : CostBound (Var := Var)
          (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          ((deflatedPhaseStep (m := m) (k := k) le_rfl (memPrefix k active)).compile qAssign
              (groverParallelMarkingOracle m S) ;;
            .qAssign (phaseTag
              ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (groupDiffuserUnitary hbg)))) 1 := by
        simpa using (costBound_deflatedPhaseStep le_rfl (memPrefix k active) S).seq
          (costBound_qAssign_phaseTag (Var := Var) hor _)
      exact (hstep.seq ih).mono (by rw [← NNReal.coe_le_coe]; push_cast; linarith)
  unfold batchRound
  dsimp only [compile]
  have hprep := costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (groupPrepUnitary hbg))
  have hread := costBound_deflatedOracle (Var := Var) (m := m) (k := k)
    le_rfl (memPrefix k active) S
  have hwrite := costBound_qAssign_phaseTag (Var := Var) hor
    (permutationUnitary (memWriteBatchPerm (W := m * (n + 1)) (n := n) (k := k)
      active (groupHits (n := n) hbg)))
  have hreset := costBound_setCountAndResetWork (Var := Var) (M := k * n) res
    (batchNextCount hm hkN hbg active) hor
  exact (hprep.seq ((hloop K).seq (hread.seq (hwrite.seq hreset)))).mono (by simp)

/-! ## One-Round `wp`, `validMemAssertion` Invariant, and `CQState` Occupancy Transition -/

def UnitaryEffect {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (c : QProg Var d) (U : Operator d) : Prop :=
  ∀ (Ψ : CQAssertion (Store Var) d) (σ : Store Var), ((wp c Ψ) σ).1.1 = Uᴴ * (Ψ σ).1.1 * U

lemma unitaryEffect_apply {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {c : QProg Var d} {U : Operator d} (h : UnitaryEffect c U)
    (Ψ : CQAssertion (Store Var) d) (σ : Store Var) :
    ((wp c Ψ) σ).1.1 = Uᴴ * (Ψ σ).1.1 * U :=
  h Ψ σ

lemma unitaryEffect_skip {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] :
    UnitaryEffect (.skip : QProg Var d) 1 := fun _ _ ↦ by simp

lemma unitaryEffect_qAssign {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (V : Unitary d) : UnitaryEffect (.qAssign V : QProg Var d) V.1 :=
  fun Ψ σ ↦ qhlQAssign_val V Ψ σ

lemma unitaryEffect_phaseTag {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (V : Unitary d) : UnitaryEffect (.qAssign (phaseTag V) : QProg Var d) V.1 := fun Ψ σ ↦ by
  rw [wp_qAssign, wp_phaseTag]
  exact qhlQAssign_val V Ψ σ

lemma unitaryEffect_seq {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {c₁ c₂ : QProg Var d} {U₁ U₂ : Operator d}
    (h₁ : UnitaryEffect c₁ U₁) (h₂ : UnitaryEffect c₂ U₂) :
    UnitaryEffect (c₁ ;; c₂) (U₂ * U₁) := fun Ψ σ ↦ by
  rw [wp_qSeq, h₁ (wp c₂ Ψ) σ, h₂ Ψ σ, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private lemma workReg_eq_lowBlock (n m k : ℕ) :
    workReg n m (m * (n + 1) + k * n) (by omega) = lowBlock (m * (n + 1)) (k * n) := rfl

private lemma workMemReg_eq_whole (n m k : ℕ) :
    workMemReg n m k (m * (n + 1) + k * n) le_rfl = whole (m * (n + 1) + k * n) := by
  ext i
  simp [workMemReg]

lemma workFullReg_embedUnitary_eq (n m k : ℕ) (U : Unitary (2 ^ ((n + 1) * m))) :
    ((workFullReg n m (m * (n + 1) + k * n) (by omega)).embedUnitary U).1 =
      (lowBlock (m * (n + 1)) (k * n)).embedMatrix ((fullReg n m).embedUnitary U).1 := by
  have hcomp : workFullReg n m (m * (n + 1) + k * n) (by omega) =
      (lowBlock (m * (n + 1)) (k * n)).compose (fullReg n m) := by
    ext i
    simp [workFullReg, lowBlock, fullReg]
  rw [hcomp, QRegister.embedUnitary_compose, embedUnitary_val]

private noncomputable def batchUnitaryPre {n m k b g : ℕ}
    (hbg : b * g = m) (S : Finset (Fin (2 ^ n))) (active K : ℕ) :
    Operator (2 ^ (m * (n + 1) + k * n)) :=
  let W := m * (n + 1)
  let M := k * n
  let fc := (lowBlock W M).embedMatrix (flagConj n m).1
  let orac := (lowBlock W M).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (lowBlock W M).embedMatrix (groupDiffuserUnitary hbg).1
  let readOp := unm * orac
  let prepOp := (lowBlock W M).embedMatrix (groupPrepUnitary hbg).1
  let writeOp := (permutationUnitary
    (memWriteBatchPerm (W := W) (n := n) (k := k) active (groupHits (n := n) hbg))).1
  writeOp * readOp * ((diffOp * phaseOp) ^ K) * prepOp

private lemma unitaryEffect_batchPrefix {Var : Type} [DecidableEq Var] {n m k b g : ℕ}
    (hbg : b * g = m) (S : Finset (Fin (2 ^ n))) (active K : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let pref : OracleCirc Var (W + M) ((n + 1) * m) :=
      .seq (.step (phaseTag ((lowBlock W M).embedUnitary (groupPrepUnitary hbg))))
        (.seq (batchGroverLoop hbg active K)
          (.seq (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active))
            (.step (phaseTag (permutationUnitary
              (memWriteBatchPerm (W := W) (n := n) (k := k) active (groupHits (n := n) hbg)))))))
    UnitaryEffect (pref.compile qAssign (groverParallelMarkingOracle m S))
      (batchUnitaryPre hbg S active K) := by
  intro W M pref
  have hread : UnitaryEffect
      ((deflatedOracle (Var := Var) (m := m) (k := k) le_rfl (memPrefix k active)).compile qAssign
        (groverParallelMarkingOracle m S))
      ((permutationUnitary (unmarkPerm n m k (memPrefix k active))).1 *
        (lowBlock W M).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1) := by
    unfold deflatedOracle
    dsimp only [compile]
    rw [workMemReg_eq_whole, QRegister.whole_embedUnitary]
    have h1 := unitaryEffect_qAssign (Var := Var)
      ((workFullReg n m (W + M) (by omega)).embedUnitary (groverParallelMarkingOracle m S))
    rw [workFullReg_embedUnitary_eq] at h1
    exact unitaryEffect_seq h1 (unitaryEffect_phaseTag _)
  have hphase : UnitaryEffect
      ((deflatedPhaseStep (Var := Var) (m := m) (k := k) le_rfl (memPrefix k active)).compile
        qAssign (groverParallelMarkingOracle m S))
      ((lowBlock W M).embedMatrix (flagConj n m).1 *
        (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1 *
        (lowBlock W M).embedMatrix
          ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 *
        (lowBlock W M).embedMatrix (flagConj n m).1) := by
    unfold deflatedPhaseStep
    dsimp only [compile]
    rw [workReg_eq_lowBlock]
    have hfc := unitaryEffect_phaseTag (Var := Var) ((lowBlock W M).embedUnitary (flagConj n m))
    rw [embedUnitary_val] at hfc
    have h12 := unitaryEffect_seq hfc (unitaryEffect_seq hread hfc)
    simpa only [Matrix.mul_assoc] using h12
  have hloop (j : ℕ) : UnitaryEffect
      ((batchGroverLoop (Var := Var) (k := k) hbg active j).compile qAssign
        (groverParallelMarkingOracle m S))
      (((lowBlock W M).embedMatrix (groupDiffuserUnitary hbg).1 *
        ((lowBlock W M).embedMatrix (flagConj n m).1 *
          (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1 *
          (lowBlock W M).embedMatrix
            ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1 *
          (lowBlock W M).embedMatrix (flagConj n m).1)) ^ j) := by
    unfold batchGroverLoop
    induction j with
    | zero => simpa using unitaryEffect_skip (Var := Var) (d := 2 ^ (W + M))
    | succ j ih =>
      simp only [List.replicate_succ, OracleDynamicCircuit.sequence_cons,
        OracleDynamicCircuit.compile_seq]
      unfold batchGroverStep
      dsimp only [compile]
      have hdiff := unitaryEffect_phaseTag (Var := Var)
        ((lowBlock W M).embedUnitary (groupDiffuserUnitary hbg))
      rw [embedUnitary_val] at hdiff
      have hstep := unitaryEffect_seq hphase hdiff
      rw [pow_succ]
      exact unitaryEffect_seq hstep ih
  dsimp only [pref, compile]
  have hprep := unitaryEffect_phaseTag (Var := Var)
    ((lowBlock W M).embedUnitary (groupPrepUnitary hbg))
  rw [embedUnitary_val] at hprep
  have hwrite := unitaryEffect_phaseTag (Var := Var)
    (permutationUnitary
      (memWriteBatchPerm (W := W) (n := n) (k := k) active (groupHits (n := n) hbg)))
  unfold batchUnitaryPre
  dsimp only
  simpa only [Matrix.mul_assoc] using
    unitaryEffect_seq hprep (unitaryEffect_seq (hloop K) (unitaryEffect_seq hread hwrite))

lemma krausLowBlock_mulVec_memAddPerm {W n k : ℕ}
    (δ : Fin (2 ^ W) → Fin k → Fin (2 ^ n)) (ψ : Fin (2 ^ W) → ℂ)
    (μ : Fin (2 ^ (k * n))) (o : Fin (2 ^ W)) :
    (lowBlock W (k * n)).embedMatrix (Matrix.single 0 o 1) *ᵥ
        ((permutationUnitary (memAddPerm δ)).1 *ᵥ workMemState ψ (single μ 1)) =
      ψ o • single
        ((lowHighEquiv W (k * n)).symm (0, (addrEquiv n k).symm (addrEquiv n k μ + δ o))) 1 := by
  have hexp : workMemState ψ (single μ 1) =
      ∑ w : Fin (2 ^ W), ψ w • workMemState (single w 1) (single μ 1) := by
    funext z
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, workMemState]
    rw [sum_eq_single (lowHighEquiv W (k * n) z).1
      (fun w hw ↦ by rw [Pi.single_eq_of_ne (Ne.symm hw), zero_mul, mul_zero])]
    rw [Pi.single_eq_same, one_mul]
  rw [hexp, Matrix.mulVec_sum_smul, Matrix.mulVec_sum_smul]
  simp_rw [permutationUnitary_memAddPerm_mulVec_single, embedMatrix_lowBlock_mulVec_workMemState]
  have hsing (w : Fin (2 ^ W)) :
      (Matrix.single (0 : Fin (2 ^ W)) o (1 : ℂ)) *ᵥ single w 1 =
        if w = o then single 0 1 else 0 := by
    funext i
    rw [mulVec_single_one, col_apply, Matrix.single_apply]
    by_cases hwo : w = o
    · subst hwo
      by_cases hi : i = 0
      · subst hi
        simp
      · simp [hi, Ne.symm hi]
    · simp [Ne.symm hwo, hwo]
  rw [sum_eq_single o (fun w hw ↦ by
    rw [hsing w, ite_eq_right hw]
    have hz : workMemState (0 : Fin (2 ^ W) → ℂ)
        (single ((addrEquiv n k).symm (addrEquiv n k μ + δ w)) 1) = 0 := by
      funext z
      simp [workMemState]
    rw [hz, smul_zero])]
  rw [hsing o, ite_eq_left rfl, workMemState_single]

lemma parallelMarkPerm_involutive {n m : ℕ} (R : Finset (Fin (2 ^ n)))
    (w : Fin (2 ^ (m * (n + 1)))) :
    parallelMarkPerm n m R (parallelMarkPerm n m R w) = w := by
  have hmul := parallelMarkPerm_mul_of_subset (n := n) (m := m) (Finset.Subset.rfl : R ⊆ R)
  rw [sdiff_self, Finset.bot_eq_empty] at hmul
  have hemp : parallelMarkPerm n m (∅ : Finset (Fin (2 ^ n))) = 1 := by
    have hm0 : markPerm (∅ : Finset (Fin (2 ^ n))) = 1 := by
      ext v : 1
      apply (splitBasisEquiv n 1).injective
      simp
    have hl0 (i : Fin m) : liftPerm (slotReg n m i) (1 : Perm (Fin (2 ^ (n + 1)))) = 1 := by
      ext z : 1
      rw [liftPerm_apply_eq_replaceIndex, Equiv.Perm.one_apply, QRegister.replaceIndex_extractIndex,
        Equiv.Perm.one_apply]
    unfold parallelMarkPerm
    simp [hm0, hl0]
  rw [hemp] at hmul
  exact congrArg (fun (e : Perm _) ↦ e w) hmul

private lemma krausLowBlock_mul_batchUnitaryPre_mulVec {n m k b g : ℕ}
    (hbg : b * g = m) {S : Finset (Fin (2 ^ n))} {active : ℕ} (K : ℕ)
    {μ : Fin (2 ^ (k * n))} (hsub : memSeen n k (memPrefix k active) μ ⊆ S)
    (o : Fin (2 ^ (m * (n + 1)))) :
    let R := S \ memSeen n k (memPrefix k active) μ
    (lowBlock (m * (n + 1)) (k * n)).embedMatrix (Matrix.single 0 o 1) *ᵥ
        (batchUnitaryPre hbg S active K *ᵥ single (workMemIdx n m k 0 μ) 1) =
      groupProdState hbg
          ((addrReg n g).tensorState (groverMultiState (oddSet n g R) K) (single 0 1))
          (parallelMarkPerm n m R o) •
        single (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg o) μ)) 1 := by
  intro R
  let ξ (j : ℕ) : Fin (2 ^ (g * (n + 1))) → ℂ :=
    (addrReg n g).tensorState (groverMultiState (oddSet n g R) j) (single 0 1)
  have hex0 : (addrReg n g).extractIndex 0 = 0 := by
    apply (basisBits (g * n)).injective
    funext r
    simp [basisBits_extractIndex]
  have henv0 : ((addrReg n g).basisSplitEquiv 0).2 = 0 := by
    funext e
    simp [QRegister.basisSplitEquiv]
  have hprep_vec :
      (lowBlock (m * (n + 1)) (k * n)).embedMatrix (groupPrepUnitary hbg).1 *ᵥ
          single (workMemIdx n m k 0 μ) 1 =
        workMemState (groupProdState hbg (ξ 0)) (single μ 1) := by
    rw [workMemIdx, ← workMemState_single, embedMatrix_lowBlock_mulVec_workMemState,
      ← groupProdState_single_zero hbg]
    have hcoe : (groupPrepUnitary hbg).1 =
        ((finRange b).map fun c ↦
          (groupReg hbg c).embedMatrix
            ((addrReg n g).embedMatrix (hadamardMatrix (g * n)))).prod := by
      unfold groupPrepUnitary
      rw [Submonoid.coe_list_prod, List.map_map]
      refine congrArg List.prod (List.map_congr_left fun c _ ↦ ?_)
      simp [embedUnitary_val]
    rw [hcoe, prod_groupReg_embedMatrix_mulVec_groupProdState,
      QRegister.embedMatrix_mulVec_single_factors, hex0, henv0,
      ← groverMultiState_zero_eq_hadamard_mulVec (oddSet n g R)]
  let fc := (lowBlock (m * (n + 1)) (k * n)).embedMatrix (flagConj n m).1
  let orac := (lowBlock (m * (n + 1)) (k * n)).embedMatrix
    ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)).1
  let unm := (permutationUnitary (unmarkPerm n m k (memPrefix k active))).1
  let phaseOp := fc * unm * orac * fc
  let diffOp := (lowBlock (m * (n + 1)) (k * n)).embedMatrix (groupDiffuserUnitary hbg).1
  have hdiff_coe : (groupDiffuserUnitary hbg).1 =
      ((finRange b).map fun c ↦
        (groupReg hbg c).embedMatrix ((addrReg n g).embedMatrix Grover.diffuserMatrix)).prod := by
    unfold groupDiffuserUnitary
    rw [Submonoid.coe_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun c _ ↦ ?_)
    simp [embedUnitary_val]
  have hiter (j : ℕ) :
      ((diffOp * phaseOp) ^ j) *ᵥ workMemState (groupProdState hbg (ξ 0)) (single μ 1) =
        workMemState (groupProdState hbg (ξ j)) (single μ 1) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, ← mulVec_mulVec,
        deflatedPhaseMat_mulVec_workMemState (memPrefix k active) _ μ hsub,
        show S \ memSeen n k (memPrefix k active) μ = R from rfl,
        sDiagM_eq_prod_groupReg hbg R, prod_groupReg_embedMatrix_mulVec_groupProdState,
        sDiagM_mulVec_tensorState_zero, embedMatrix_lowBlock_mulVec_workMemState,
        hdiff_coe, prod_groupReg_embedMatrix_mulVec_groupProdState,
        QRegister.embedMatrix_mulVec_tensorState]
      rfl
  have hperm_apply (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (w : Fin (2 ^ (m * (n + 1)))) :
      ((permutationUnitary (parallelMarkPerm n m R)).1 *ᵥ ψ) w =
        ψ (parallelMarkPerm n m R w) := by
    rw [Matrix.mulVec, dotProduct,
      sum_eq_single (parallelMarkPerm n m R w) (fun y hy ↦ by
        rw [permutationUnitary_apply,
          ite_eq_right (fun h ↦ hy (by
            have h2 := congrArg (parallelMarkPerm n m R) h
            rw [parallelMarkPerm_involutive] at h2
            exact h2.symm)),
          zero_mul])]
    rw [permutationUnitary_apply, ite_eq_left (parallelMarkPerm_involutive R w).symm, one_mul]
  unfold batchUnitaryPre
  dsimp only
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hprep_vec, hiter K,
    ← mulVec_mulVec _ unm orac,
    unmark_mul_parallelOracle_workMemState (memPrefix k active) _ μ hsub,
    show S \ memSeen n k (memPrefix k active) μ = R from rfl,
    fullReg_embedUnitary_eq_permutationUnitary R,
    krausLowBlock_mulVec_memAddPerm, hperm_apply]
  rfl

private lemma batchReadout_support_valid {n m k b g : ℕ}
    (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hbg : b * g = m) {active K : ℕ}
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
    {o : Fin (2 ^ (m * (n + 1)))}
    (hamp : groupProdState hbg
      ((addrReg n g).tensorState
        (groverMultiState (oddSet n g (S \ memSeen n k (memPrefix k active) μ)) K) (single 0 1))
      (parallelMarkPerm n m (S \ memSeen n k (memPrefix k active) μ) o) ≠ 0) :
    active + (groupHits hbg o).length ≤ k ∧
      (batchNextCount hm hkN hbg active o).val = active + (groupHits hbg o).length ∧
      MemPrefixValid S (active + (groupHits hbg o).length)
        (writeMemBatch active (groupHits hbg o) μ) := by
  set R := S \ memSeen n k (memPrefix k active) μ
  set w := parallelMarkPerm n m R o
  have hflags (c : Fin b) :
      ((addrReg n g).basisSplitEquiv ((groupReg hbg c).extractIndex w)).2 = 0 := by
    by_contra hc
    apply hamp
    unfold groupProdState
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    simp [tensorState, Pi.single_eq_of_ne hc]
  have hnew : ∀ x ∈ groupHits hbg o, x ∈ R := by
    intro x hx
    have ho : o = parallelMarkPerm n m R w := (parallelMarkPerm_involutive R o).symm
    rw [ho] at hx
    exact mem_of_mem_groupHits_parallelMarkPerm hbg hflags hx
  obtain ⟨hlen, hval'⟩ :=
    memPrefixValid_writeMemBatch hcard hval (nodup_groupHits hbg o) hnew
  exact ⟨hlen, Nat.min_eq_right hlen, hval'⟩

private lemma sum_normSq_batchReadout_groupHits {n m b g : ℕ} (hbg : b * g = m)
    (R : Finset (Fin (2 ^ n))) (K : ℕ) (F : List (Fin (2 ^ n)) → ℂ) :
    (∑ o : Fin (2 ^ (m * (n + 1))),
      (normSq (groupProdState hbg
        ((addrReg n g).tensorState (groverMultiState (oddSet n g R) K) (single 0 1))
        (parallelMarkPerm n m R o)) : ℂ) * F (groupHits hbg o)) =
      ∑ os : Fin b → Option (Fin (2 ^ n)),
        (iidTupleProb n g R K os : ℂ) * F (tupleNewHits os) := by
  let ξ := (addrReg n g).tensorState (groverMultiState (oddSet n g R) K) (single 0 1)
  let hitZ (z : Fin (2 ^ (g * (n + 1)))) : Option (Fin (2 ^ n)) :=
    firstMarkedAddr n g (parallelMarkPerm n g R z)
  have hsingle (opt : Option (Fin (2 ^ n))) :
      (∑ z : Fin (2 ^ (g * (n + 1))), if hitZ z = opt then (normSq (ξ z) : ℂ) else 0) =
        (groupDrawProb n g R K opt : ℂ) := by
    let term (z : Fin (2 ^ (g * (n + 1)))) : ℂ :=
      if hitZ z = opt then (normSq (ξ z) : ℂ) else 0
    change ∑ z, term z = _
    rw [← (addrReg n g).basisSplitEquiv.symm.sum_comp term, sum_prod_type]
    have hinner (u : Fin (2 ^ (g * n))) :
        (∑ e : (addrReg n g).Environment → ZMod 2,
          term ((addrReg n g).basisSplitEquiv.symm (u, e))) =
          if firstTupleHit n g R u = opt then
            (normSq (groverMultiState (oddSet n g R) K u) : ℂ)
          else 0 := by
      rw [sum_eq_single 0 (fun e he ↦ by
        dsimp only [term, ξ, tensorState]
        rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero,
          Complex.ofReal_zero, ite_self])]
      dsimp only [term, hitZ, ξ, tensorState]
      have hE : ((addrReg n g).basisSplitEquiv
          ((addrReg n g).basisSplitEquiv.symm (u, 0))).2 = 0 := by
        rw [Equiv.apply_symm_apply]
      have hex : (addrReg n g).extractIndex
          ((addrReg n g).basisSplitEquiv.symm (u, 0)) = u := by
        rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
      rw [if_congr
        (congrArg (· = opt) (firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R _ hE)).to_iff
        rfl rfl, hex, hE, Pi.single_eq_same, mul_one]
    simp_rw [hinner, ← Finset.sum_filter, ← Complex.ofReal_sum,
      sum_normSq_filter_firstTupleHit_eq_groupDrawProb]
  have h1 :
      (∑ o : Fin (2 ^ (m * (n + 1))),
        (normSq (groupProdState hbg ξ (parallelMarkPerm n m R o)) : ℂ) * F (groupHits hbg o)) =
      ∑ w : Fin (2 ^ (m * (n + 1))),
        (normSq (groupProdState hbg ξ w) : ℂ) * F (groupHits hbg (parallelMarkPerm n m R w)) := by
    rw [← Equiv.sum_comp (parallelMarkPerm n m R)]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [parallelMarkPerm_involutive]
  rw [h1, ← (groupSplitEquiv hbg).symm.sum_comp]
  have h2 (zs : Fin b → Fin (2 ^ (g * (n + 1)))) :
      (normSq (groupProdState hbg ξ ((groupSplitEquiv hbg).symm zs)) : ℂ) *
          F (groupHits hbg (parallelMarkPerm n m R ((groupSplitEquiv hbg).symm zs))) =
        (∏ c : Fin b, (normSq (ξ (zs c)) : ℂ)) *
          F (((finRange b).filterMap (hitZ ∘ zs)).dedup) := by
    have hex (c : Fin b) :
        (groupReg hbg c).extractIndex ((groupSplitEquiv hbg).symm zs) = zs c := by
      rw [← groupSplitEquiv_apply hbg, Equiv.apply_symm_apply]
    have hprod :
        (normSq (groupProdState hbg ξ ((groupSplitEquiv hbg).symm zs)) : ℂ) =
          ∏ c : Fin b, (normSq (ξ (zs c)) : ℂ) := by
      unfold groupProdState
      simp_rw [hex, map_prod, Complex.ofReal_prod]
    have hhits :
        groupHits hbg (parallelMarkPerm n m R ((groupSplitEquiv hbg).symm zs)) =
          ((finRange b).filterMap (hitZ ∘ zs)).dedup := by
      unfold groupHits
      congr 1
      refine List.filterMap_congr fun c _ ↦ ?_
      rw [extractIndex_groupReg_parallelMarkPerm, hex]
      rfl
    rw [hprod, hhits]
  simp_rw [h2]
  symm
  have hrhs' (os : Fin b → Option (Fin (2 ^ n))) :
      (iidTupleProb n g R K os : ℂ) * F (tupleNewHits os) =
        ∑ zs : Fin b → Fin (2 ^ (g * (n + 1))),
          (∏ c : Fin b, if hitZ (zs c) = os c then (normSq (ξ (zs c)) : ℂ) else 0) *
            F (tupleNewHits os) := by
    unfold iidTupleProb
    rw [Complex.ofReal_prod]
    simp_rw [← hsingle]
    rw [Fintype.prod_sum, Finset.sum_mul]
  simp_rw [hrhs']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun zs _ ↦ ?_
  rw [sum_eq_single (hitZ ∘ zs) (fun os hos ↦ ?_)]
  · simp only [Function.comp_apply, ite_true, tupleNewHits]
  · obtain ⟨c, hc⟩ : ∃ c : Fin b, hitZ (zs c) ≠ os c := by
      by_contra! hall
      exact hos (funext fun c ↦ (hall c).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ c) (ite_eq_right hc), zero_mul]

lemma diag_eq_star_single_dotProduct_mulVec {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (idx : Fin d) :
    A idx idx = star (single idx 1) ⬝ᵥ (A *ᵥ single idx 1) := by
  rw [mulVec_single_one, dotProduct,
    sum_eq_single idx (fun j hj ↦ by
      rw [Pi.star_apply, Pi.single_eq_of_ne hj, star_zero, zero_mul])]
  simp [col_apply]

/-- Exact one-round `wp` diagonal entry on `(workMemIdx n m k 0 μ, workMemIdx n m k 0 μ)`
  for an
  arbitrary postcondition `Θ: CQAssertion` when `S.card = k` and `MemPrefixValid S active
  μ`. -/
theorem wp_batchRound_workMemIdx {Var : Type} [DecidableEq Var] (res : Var) {n m k b g : ℕ}
    (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hbg : b * g = m) (active K : ℕ)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) :
    ((wp ((batchRound res hm hkN hbg active K).compile qAssign (groverParallelMarkingOracle m S))
        Θ) σ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      ∑ o : Fin (2 ^ (m * (n + 1))),
        (normSq (groupProdState hbg
          ((addrReg n g).tensorState
            (groverMultiState (oddSet n g (S \ memSeen n k (memPrefix k active) μ)) K)
            (single 0 1))
          (parallelMarkPerm n m (S \ memSeen n k (memPrefix k active) μ) o)) : ℂ) *
          (Θ (Store.subst σ res
            (Int.ofNat (active + (groupHits hbg o).length)))).1.1
              (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg o) μ))
              (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg o) μ)) := by
  let W := m * (n + 1)
  let M := k * n
  let pref : OracleCirc Var (W + M) ((n + 1) * m) :=
    .seq (.step (phaseTag ((lowBlock W M).embedUnitary (groupPrepUnitary hbg))))
      (.seq (batchGroverLoop hbg active K)
        (.seq (deflatedOracle (m := m) (k := k) le_rfl (memPrefix k active))
          (.step (phaseTag (permutationUnitary
            (memWriteBatchPerm (W := W) (n := n) (k := k) active (groupHits (n := n) hbg)))))))
  let postReset := (setCountAndResetWork (Var := Var) (W := W) (M := M) (O := (n + 1) * m)
    res (batchNextCount hm hkN hbg active)).compile qAssign (groverParallelMarkingOracle m S)
  have hwp_eq :
      wp ((batchRound (Var := Var) res hm hkN hbg active K).compile qAssign
          (groverParallelMarkingOracle m S)) Θ =
        wp (pref.compile qAssign (groverParallelMarkingOracle m S)) (wp postReset Θ) := by
    unfold batchRound
    dsimp only [pref, postReset, compile]
    simp only [wp_qSeq]
    rfl
  have hmat :
      ((wp ((batchRound res hm hkN hbg active K).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
        ∑ o : Fin (2 ^ W),
          ((lowBlock W M).embedMatrix (Matrix.single 0 o 1) * batchUnitaryPre hbg S active K)ᴴ *
            (Θ (Store.subst σ res (Int.ofNat (batchNextCount hm hkN hbg active o).val))).1.1 *
            ((lowBlock W M).embedMatrix (Matrix.single 0 o 1) *
              batchUnitaryPre hbg S active K) := by
    rw [hwp_eq,
      unitaryEffect_apply (unitaryEffect_batchPrefix (Var := Var) hbg S active K)
        (wp postReset Θ) σ,
      wp_setCountAndResetWork]
    exact (Matrix.sum_conjTranspose_mul_mul_mul Finset.univ _ _ _).symm
  rw [hmat]
  refine (diag_eq_star_single_dotProduct_mulVec _ (workMemIdx n m k 0 μ)).trans ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  have hsub := (card_memSeen_of_memPrefixValid hval).2
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  set K_op := (lowBlock W M).embedMatrix (Matrix.single 0 o 1) * batchUnitaryPre hbg S active K
  set idx := workMemIdx n m k 0 μ
  set idx' := workMemIdx n m k 0 (writeMemBatch active (groupHits hbg o) μ)
  set α := groupProdState hbg
    ((addrReg n g).tensorState
      (groverMultiState (oddSet n g (S \ memSeen n k (memPrefix k active) μ)) K) (single 0 1))
    (parallelMarkPerm n m (S \ memSeen n k (memPrefix k active) μ) o)
  have hKv : K_op *ᵥ single idx 1 = α • single idx' 1 := by
    dsimp only [K_op, idx, idx', α]
    rw [← mulVec_mulVec]
    exact krausLowBlock_mul_batchUnitaryPre_mulVec hbg K hsub o
  have hquad (B : Matrix (Fin (2 ^ (W + M))) (Fin (2 ^ (W + M))) ℂ) :
      star (single idx 1) ⬝ᵥ ((K_opᴴ * B * K_op) *ᵥ single idx 1) =
        (normSq α : ℂ) * B idx' idx' := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star,
      hKv, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
      ← diag_eq_star_single_dotProduct_mulVec B idx', smul_eq_mul, smul_eq_mul, ← mul_assoc,
      RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [hquad]
  by_cases hα : α = 0
  · rw [hα, Complex.normSq_zero, Complex.ofReal_zero, zero_mul, zero_mul]
  · obtain ⟨_, hcnt, _⟩ := batchReadout_support_valid hm hkN hbg hcard hval hα
    rw [hcnt]

/-- Invariant-preserving one-round `wp` transition: whenever `Θ` evaluates to `(h s: ℂ)` on
  every
  valid `(workMemIdx n m k 0 μ')` with `τ res = s`, one `batchRound` at occupancy `active`
  evaluates
  to the `R`-independent `Fin (k - active)` i.i.d. coupon expectation of `h`. -/
theorem wp_batchRound_workMemIdx_of_invariant {Var : Type} [DecidableEq Var] (res : Var)
    {n m k b g : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hbg : b * g = m) (active K : ℕ)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S active μ)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (h : ℕ → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (μ' : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ' →
        (Θ τ).1.1 (workMemIdx n m k 0 μ') (workMemIdx n m k 0 μ') = (h s : ℂ))
    (σ : Store Var) :
    ((wp ((batchRound res hm hkN hbg active K).compile qAssign (groverParallelMarkingOracle m S))
        Θ) σ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
      (((∑ cs : Fin b → Option (Fin (k - active)),
        iidCouponProb n g (k - active) K cs *
          h (active + (((finRange b).filterMap cs).dedup).length)) : ℝ) : ℂ) := by
  rw [wp_batchRound_workMemIdx res hm hkN hbg active K hcard hval Θ σ]
  set R := S \ memSeen n k (memPrefix k active) μ
  have hterm (o : Fin (2 ^ (m * (n + 1)))) :
      (normSq (groupProdState hbg
        ((addrReg n g).tensorState (groverMultiState (oddSet n g R) K) (single 0 1))
        (parallelMarkPerm n m R o)) : ℂ) *
        (Θ (Store.subst σ res (Int.ofNat (active + (groupHits hbg o).length)))).1.1
          (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg o) μ))
          (workMemIdx n m k 0 (writeMemBatch active (groupHits hbg o) μ)) =
      (normSq (groupProdState hbg
        ((addrReg n g).tensorState (groverMultiState (oddSet n g R) K) (single 0 1))
        (parallelMarkPerm n m R o)) : ℂ) *
        (h (active + (groupHits hbg o).length) : ℂ) := by
    set α := groupProdState hbg
      ((addrReg n g).tensorState (groverMultiState (oddSet n g R) K) (single 0 1))
      (parallelMarkPerm n m R o)
    by_cases hα : α = 0
    · rw [hα, Complex.normSq_zero, Complex.ofReal_zero, zero_mul, zero_mul]
    · obtain ⟨hlen, _, hval'⟩ := batchReadout_support_valid hm hkN hbg hcard hval hα
      rw [hΘ (active + (groupHits hbg o).length) _ _ hlen (by simp) hval']
  simp_rw [hterm]
  rw [sum_normSq_batchReadout_groupHits hbg R K (fun L ↦ (h (active + L.length) : ℂ))]
  simp_rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum,
    sum_iidTupleProb_length_eq_sum_iidCouponProb n g R K (fun d ↦ h (active + d))]
  have hseen := card_memSeen_of_memPrefixValid hval
  have hadd : R.card + (memSeen n k (memPrefix k active) μ).card = S.card :=
    Finset.card_sdiff_add_card_eq_card hseen.2
  have hrcard : R.card = k - active := by omega
  congr 1
  let eqv : (Fin b → Option (Fin R.card)) ≃ (Fin b → Option (Fin (k - active))) :=
    Equiv.piCongrRight fun _ ↦ Equiv.optionCongr (finCongr hrcard)
  rw [← eqv.sum_comp]
  refine Finset.sum_congr rfl fun cs _ ↦ ?_
  have hp : iidCouponProb n g R.card K cs = iidCouponProb n g (k - active) K (eqv cs) := by
    unfold iidCouponProb
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    cases hcs : cs c <;> simp [eqv, couponDrawProb, hrcard, hcs]
  have hl : (((finRange b).filterMap (eqv cs)).dedup).length =
      (((finRange b).filterMap cs).dedup).length :=
    dedup_length_filterMap_option_map (finCongr hrcard).injective (finRange b) cs
  rw [hp, hl]

/-! ## Turnkey Multi-Round Coupon-Collector Circuit and Drift Theorems -/

/-- Multi-branch loop body dispatching `σ res = active` (`active: Fin k`) to
  `batchRound res hm hkN (hbg active.val active.isLt) active.val (K active.val)` with
  per-occupancy
  slot partitioning `b active * g active = m`. -/
noncomputable def findAllBatchBody {Var : Type} (res : Var) {n m k : ℕ}
    (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ} (hbg : ∀ s < k, b s * g s = m)
    (K : ℕ → ℕ) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  dispFin res (fun s : Fin k ↦ batchRound res hm hkN (hbg s.val s.isLt) s.val (K s.val))
    (finRange k)

/-- Multi-round coupon-collector tail circuit (`s < k - 1` batch `.qWhile` loop + `s = k -
  1`
  `lastStage` + final `memReg` readout into `res`), composable after any `S`-valid
  initializer. -/
noncomputable def findAllBatchTail {Var : Type} (res : Var) {n m k : ℕ}
    (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ} (hbg : ∀ s < k, b s * g s = m)
    (K : ℕ → ℕ)
    (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (.qWhile (fun σ ↦ σ res < ((k - 1 : ℕ) : ℤ)) (findAllBatchBody res hm hkN hbg K))
    (.seq (.qIf (fun σ ↦ σ res = ((k - 1 : ℕ) : ℤ)) lastStage .skip)
      (.measure res (highBlock (m * (n + 1)) (k * n))))

/-- Hybrid `S`-free multi-round coupon-collector circuit with a custom `r = 1` tail stage:
  loops `findAllBatchBody` while `σ res < ((k - 1: ℕ): ℤ)` (`r = k - s ≥ 2`), runs
  `lastStage` if
  `σ res = ((k - 1: ℕ): ℤ)` (and `.skip` if the batch loop already jumped straight to `k`),
  and
  measures `memReg` (`highBlock`) into `res`. -/
noncomputable def findAllBatchWithLast {Var : Type} (res : Var) {n m k : ℕ}
    (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ} (hbg : ∀ s < k, b s * g s = m)
    (K : ℕ → ℕ)
    (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m)) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (.measure res (lowBlock (m * (n + 1)) (k * n)))
    (findAllBatchTail res hm hkN hbg K lastStage)

private lemma dedup_filterMap_fin_length_le {b r : ℕ} (cs : Fin b → Option (Fin r)) :
    (((finRange b).filterMap cs).dedup).length ≤ r := by
  have hnd : (((finRange b).filterMap cs).dedup).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_univ _).trans (by simp)

lemma ofReal_smul_one_eq_smul_one {d : ℕ} (r : ℝ) :
    (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) = r • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext i j
  simp [Complex.real_smul]

private lemma sum_range_ite_zero_mul (k : ℕ) (f : ℕ → ℝ) :
    (∑ s ∈ Finset.range (k + 1), (if s = 0 then (1 : ℝ) else 0) * f s) = f 0 := by
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range (k + 1)) 0,
    ite_eq_left (Finset.mem_range.mpr (Nat.succ_pos k))]

private lemma wp_qSet_measure_lowBlock_apply_mat {Var : Type} [DecidableEq Var] (res : Var)
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
    · subst ho
      rw [ite_eq_left rfl, Pi.single_eq_same, workMemState_zero]
    · rw [ite_eq_right ho, Pi.single_eq_of_ne ho, Pi.single_zero]
      funext z
      simp [workMemState]
  rw [sum_eq_single 0 (fun o ho ↦ by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj o, ite_eq_right ho,
      Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero])]
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj 0, ite_eq_left rfl,
    Matrix.dotProduct_mulVec, ← QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.vecMul_conjTranspose, star_star, hproj 0, ite_eq_left rfl]
  refine (diag_eq_star_single_dotProduct_mulVec _ 0).symm.trans ?_
  simp [HermitianMat.val_eq_coe]

private lemma wp_dispFin_apply_of_lt {Var : Type} [DecidableEq Var] (res : Var)
    {k Q O : ℕ} (f : Fin k → OracleCirc Var Q O) (oracle : Unitary (2 ^ O))
    (Θ : CQAssertion (Store Var) (2 ^ Q)) {s : ℕ} (hs : s < k)
    {τ : Store Var} (hτ : τ res = (s : ℤ)) :
    wp ((dispFin res f (finRange k)).compile qAssign oracle) Θ τ =
      wp ((f ⟨s, hs⟩).compile qAssign oracle) Θ τ := by
  set s₀ : Fin k := ⟨s, hs⟩
  have hmem : s₀ ∈ finRange k := mem_finRange s₀
  generalize finRange k = l at hmem
  induction l with
  | nil => cases hmem
  | cons x _ ih =>
    simp only [dispFin, compile, wp]
    by_cases h : s₀ = x
    · subst h
      simp [hτ, s₀]
    · have hne : τ res ≠ (x.val : ℤ) :=
        fun heq ↦ h (Fin.ext (Int.ofNat.inj (hτ.symm.trans heq)))
      simp only [hne, ↓reduceIte]
      exact ih (List.mem_of_ne_of_mem h hmem)

private lemma wp_measure_highBlock_workMemIdx_full {Var : Type} [DecidableEq Var] (res : Var)
    (n m : ℕ) {k : ℕ} {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (τ : Store Var) (μ : Fin (2 ^ (k * n))) (hval : MemPrefixValid S k μ) :
    ((wp (measureRegister res (highBlock (m * (n + 1)) (k * n)))
        (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S)) τ).1.1
      (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1 := by
  let W := m * (n + 1)
  let M := k * n
  let post := liftPureProp (Var := Var) (d := 2 ^ (W + M))
    fun σ ↦ decodeTargets n k (σ res) = S
  have hproj (o : Fin (2 ^ M)) :
      (highBlock W M).basisOutcomeProjector o *ᵥ single (workMemIdx n m k 0 μ) 1 =
        if o = μ then single (workMemIdx n m k 0 μ) 1 else 0 := by
    rw [QRegister.basisOutcomeProjector, workMemIdx, ← workMemState_single,
      embedMatrix_highBlock_mulVec_workMemState, compProj_mulVec]
    by_cases ho : o = μ
    · subst ho
      rw [ite_eq_left rfl, Pi.single_eq_same, workMemState_single]
    · rw [ite_eq_right ho, Pi.single_eq_of_ne ho, Pi.single_zero]
      funext z
      simp [workMemState]
  change ((wp (measureRegister res (highBlock W M)) post) τ).1.1
    (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1
  rw [wp_measureRegister]
  refine (diag_eq_star_single_dotProduct_mulVec _ (workMemIdx n m k 0 μ)).trans ?_
  rw [Matrix.sum_mulVec, dotProduct_sum, sum_eq_single μ (fun o ho ↦ by
      rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj o, ite_eq_right ho,
        Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero])]
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hproj μ, ite_eq_left rfl,
    Matrix.dotProduct_mulVec, ← QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.vecMul_conjTranspose, star_star, hproj μ, ite_eq_left rfl]
  refine (diag_eq_star_single_dotProduct_mulVec _ (workMemIdx n m k 0 μ)).symm.trans ?_
  have hdec : decodeTargets n k (μ.val : ℤ) = S :=
    decodeTargets_eq_of_memPrefixValid_full hcard hval
  simp [post, hdec, HermitianMat.val_eq_coe]

private noncomputable def whileRecProb (n k k_stop : ℕ) (b g K : ℕ → ℕ)
    (base : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t + 1, s =>
      if s < k_stop then
        ∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            whileRecProb n k k_stop b g K base t
              (s + (((finRange (b s)).filterMap cs).dedup).length)
      else base s

private lemma whileRecProb_bounds {n k k_stop : ℕ} {b g K : ℕ → ℕ} {base : ℕ → ℝ}
    (hbase : ∀ s, 0 ≤ base s ∧ base s ≤ 1) :
    (∀ t s, 0 ≤ whileRecProb n k k_stop b g K base t s ∧
      whileRecProb n k k_stop b g K base t s ≤ 1) ∧
      ∀ t s, whileRecProb n k k_stop b g K base t s ≤
        whileRecProb n k k_stop b g K base (t + 1) s := by
  have hbnd : ∀ t s, 0 ≤ whileRecProb n k k_stop b g K base t s ∧
      whileRecProb n k k_stop b g K base t s ≤ 1 := by
    intro t
    induction t with
    | zero => exact fun _ ↦ ⟨le_rfl, zero_le_one⟩
    | succ t ih =>
      intro s
      rw [whileRecProb]
      split_ifs
      · refine ⟨Finset.sum_nonneg fun cs _ ↦
          mul_nonneg (iidCouponProb_nonneg _ _ _ _ _) (ih _).1, ?_⟩
        calc (∑ cs : Fin (b s) → Option (Fin (k - s)),
              iidCouponProb n (g s) (k - s) (K s) cs *
                whileRecProb n k k_stop b g K base t
                  (s + (((finRange (b s)).filterMap cs).dedup).length))
            ≤ ∑ cs : Fin (b s) → Option (Fin (k - s)),
                iidCouponProb n (g s) (k - s) (K s) cs * 1 :=
              Finset.sum_le_sum fun cs _ ↦
                mul_le_mul_of_nonneg_left (ih _).2 (iidCouponProb_nonneg _ _ _ _ _)
          _ = 1 := by simp [sum_iidCouponProb_eq_one]
      · exact hbase s
  refine ⟨hbnd, fun t ↦ ?_⟩
  induction t with
  | zero => exact fun s ↦ (hbnd 1 s).1
  | succ t ih =>
    intro s
    rw [whileRecProb, whileRecProb]
    split_ifs
    · exact Finset.sum_le_sum fun cs _ ↦
        mul_le_mul_of_nonneg_left (ih _) (iidCouponProb_nonneg _ _ _ _ _)
    · exact le_rfl

private lemma whileRecWP_workMemIdx_eq {Var : Type} [DecidableEq Var] (res : Var)
    {n m k k_stop : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hstop : k_stop ≤ k)
    {b g : ℕ → ℕ} (hbg : ∀ s < k, b s * g s = m) (K : ℕ → ℕ)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (base : ℕ → ℝ)
    (hΘ : ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      ¬ s < k_stop → s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
        (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (base s : ℂ))
    (t : ℕ) :
    ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
        (whileRecWP
            (wp ((findAllBatchBody res hm hkN hbg K).compile qAssign
              (groverParallelMarkingOracle m S)))
            (fun σ ↦ σ res < (k_stop : ℤ)) t Θ τ).1.1
          (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
          (whileRecProb n k k_stop b g K base t s : ℂ) := by
  let guard : Store Var → Prop := fun σ ↦ σ res < (k_stop : ℤ)
  let body := (findAllBatchBody (Var := Var) res hm hkN hbg K).compile qAssign
    (groverParallelMarkingOracle m S)
  induction t with
  | zero =>
    intro s τ μ _ _ _
    dsimp only [whileRecWP, whileRecProb]
    simp
  | succ t ih =>
    intro s τ μ hs hτ hval
    dsimp only [whileRecWP, whileRecProb]
    by_cases hlt : s < k_stop
    · have hsk : s < k := lt_of_lt_of_le hlt hstop
      have hg : guard τ := by
        dsimp only [guard]
        rw [hτ]
        exact_mod_cast hlt
      rw [ite_eq_left hg, ite_eq_left hlt]
      have hdisp : wp body (whileRecWP (wp body) guard t Θ) τ =
          wp ((batchRound res hm hkN (hbg s hsk) s (K s)).compile qAssign
            (groverParallelMarkingOracle m S)) (whileRecWP (wp body) guard t Θ) τ :=
        wp_dispFin_apply_of_lt res _ _ _ hsk hτ
      rw [hdisp]
      exact wp_batchRound_workMemIdx_of_invariant res hm hkN (hbg s hsk) s (K s) hcard hval
        (whileRecWP (wp body) guard t Θ) (whileRecProb n k k_stop b g K base t) ih τ
    · have hng : ¬ guard τ := by
        dsimp only [guard]
        rw [hτ]
        omega
      rw [ite_eq_right hng, ite_eq_right hlt, hΘ s τ μ hlt hs hτ hval]

/-- Total correctness (`wp = ⊤`) of `.qSet;; (initStage.seq findAllBatchTail)` from any
  nonnegative potential `V: ℕ → ℝ` (`0 ≤ V s` for `s ≤ k`) satisfying the `s < k - 1` coupon
  drift
  inequality, given an initializer occupancy law `P` on `0.. k`. -/
theorem wp_init_seq_findAllBatchTail_of_drift {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (K : ℕ → ℕ)
    (initStage lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (P : ℕ → ℝ) (hP_nonneg : ∀ s ≤ k, 0 ≤ P s)
    (hP_sum : (∑ s ∈ Finset.range (k + 1), P s) = 1)
    (hinit_wp : ∀ (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (f : ℕ → ℝ),
      (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
        s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (f s : ℂ)) →
        ∀ σ : Store Var,
          ((wp (.qSet ;; initStage.compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
            ((∑ s ∈ Finset.range (k + 1), P s * f s : ℝ) : ℂ) •
              (1 : Operator (2 ^ (m * (n + 1) + k * n))))
    (hlast_wp : ∀ (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ →
        ((wp (lastStage.compile qAssign (groverParallelMarkingOracle m S))
            (wp (measureRegister res (highBlock (m * (n + 1)) (k * n)))
              (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S))) τ).1.1
          (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1)
    (V : ℕ → ℝ) (hV_nonneg : ∀ s ≤ k, 0 ≤ V s)
    (hV_drift : ∀ s < k - 1,
      ((K s + 1 : ℕ) : ℝ) +
        (∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            V (s + (((finRange (b s)).filterMap cs).dedup).length)) ≤ V s) :
    wp (.qSet ;;
          ((initStage.seq (findAllBatchTail res hm hkN hbg K lastStage)).compile qAssign
            (groverParallelMarkingOracle m S)))
        (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S) = ⊤ := by
  let W := m * (n + 1)
  let M := k * n
  let k_stop := k - 1
  let guard : Store Var → Prop := fun σ ↦ σ res < (k_stop : ℤ)
  let initProg := initStage.compile qAssign (groverParallelMarkingOracle m S)
  let body := (findAllBatchBody (Var := Var) res hm hkN hbg K).compile qAssign
    (groverParallelMarkingOracle m S)
  let lastProg := lastStage.compile qAssign (groverParallelMarkingOracle m S)
  let tailProg : QProg Var (2 ^ (W + M)) :=
    .qIf (fun σ ↦ σ res = (k_stop : ℤ)) lastProg .skip ;; measureRegister res (highBlock W M)
  let post := liftPureProp (Var := Var) (d := 2 ^ (W + M)) fun σ ↦ decodeTargets n k (σ res) = S
  let postTail := wp tailProg post
  have htail : ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ M)),
      ¬ s < k_stop → s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
        (postTail τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = ((1 : ℝ) : ℂ) := by
    intro s τ μ hlt hle hτ hval
    dsimp only [postTail, tailProg]
    rw [Complex.ofReal_one]
    by_cases hsk : s = k - 1
    · rw [hsk] at hτ hval
      simp only [wp_qSeq, wp_qIf, k_stop, hτ, ↓reduceIte]
      exact hlast_wp τ μ hτ hval
    · have hs_eq : s = k := by omega
      rw [hs_eq] at hτ hval
      have hnc : τ res ≠ (k_stop : ℤ) := by rw [hτ]; omega
      simp only [wp_qSeq, wp_qIf, hnc, ↓reduceIte, wp_skip]
      exact wp_measure_highBlock_workMemIdx_full res n m hcard τ μ hval
  have hind := whileRecWP_workMemIdx_eq res hm hkN (Nat.sub_le k 1) hbg K hcard postTail
    (fun _ ↦ 1) htail
  rcases whileRecProb_bounds (n := n) (k := k) (k_stop := k_stop) (b := b) (g := g) (K := K)
    (base := fun _ ↦ 1) (fun _ ↦ ⟨zero_le_one, le_rfl⟩) with ⟨_, hmono⟩
  let Q (t s : ℕ) : ℝ := 1 - whileRecProb n k k_stop b g K (fun _ ↦ 1) (t + 1) s
  have hQ_anti (t s : ℕ) : Q (t + 1) s ≤ Q t s := sub_le_sub_left (hmono (t + 1) s) 1
  have hQ_zero (s : ℕ) : Q 0 s = if s < k_stop then 1 else 0 := by
    dsimp only [Q]
    rw [whileRecProb]
    split_ifs with hlt
    · have h0 : ∀ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            whileRecProb n k k_stop b g K (fun _ ↦ 1) 0
              (s + (((finRange (b s)).filterMap cs).dedup).length) = 0 := by
        intro cs
        rw [whileRecProb, mul_zero]
      simp_rw [h0, Finset.sum_const_zero, sub_zero]
    · exact sub_self 1
  have hQ_step (t s : ℕ) :
      Q (t + 1) s =
        if s < k_stop then
          ∑ cs : Fin (b s) → Option (Fin (k - s)),
            iidCouponProb n (g s) (k - s) (K s) cs *
              Q t (s + (((finRange (b s)).filterMap cs).dedup).length)
        else 0 := by
    dsimp only [Q]
    conv_lhs => rw [whileRecProb]
    split_ifs with hlt
    · nth_rw 1 [← sum_iidCouponProb_eq_one (b := b s) n (g s) (k - s) (K s)]
      rw [← sum_sub_distrib]
      refine Finset.sum_congr rfl fun cs _ ↦ ?_
      ring
    · exact sub_self 1
  have hQ_sum_le (T : ℕ) : ∀ s ≤ k, (∑ j ∈ Finset.range T, Q j s) ≤ V s := by
    induction T with
    | zero => exact fun s hs ↦ by simpa using hV_nonneg s hs
    | succ T ihT =>
      intro s hs
      rw [Finset.sum_range_succ']
      by_cases hlt : s < k_stop
      · simp_rw [hQ_step _ s, ite_eq_left hlt, hQ_zero s, ite_eq_left hlt]
        rw [← Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        have h1 : (1 : ℝ) ≤ ((K s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (K s)
        have h2 :
            (∑ cs : Fin (b s) → Option (Fin (k - s)),
              iidCouponProb n (g s) (k - s) (K s) cs *
                (∑ j ∈ Finset.range T,
                  Q j (s + (((finRange (b s)).filterMap cs).dedup).length))) ≤
              ∑ cs : Fin (b s) → Option (Fin (k - s)),
                iidCouponProb n (g s) (k - s) (K s) cs *
                  V (s + (((finRange (b s)).filterMap cs).dedup).length) := by
          refine Finset.sum_le_sum fun cs _ ↦
            mul_le_mul_of_nonneg_left (ihT _ ?_) (iidCouponProb_nonneg _ _ _ _ _)
          have hdl := dedup_filterMap_fin_length_le cs
          omega
        linarith [hV_drift s hlt]
      · simp_rw [hQ_step _ s, ite_eq_right hlt, hQ_zero s, ite_eq_right hlt,
          Finset.sum_const_zero, add_zero]
        exact hV_nonneg s hs
  set V_avg : ℝ := ∑ s ∈ Finset.range (k + 1), P s * V s
  set prog : QProg Var (2 ^ (W + M)) := .qSet ;; (initProg ;; (.qWhile guard body ;; tailProg))
  change wp prog post = ⊤
  refine le_antisymm le_top fun σ ↦ ?_
  have hstep_le (T : ℕ) :
      ((1 - V_avg / ((T + 1 : ℕ) : ℝ)) • (1 : HermitianMat (Fin (2 ^ (W + M))) ℂ)) ≤
        ((wp prog post) σ).1 := by
    have hpos : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
    have hT_mul (s : ℕ) (hs : s ≤ k) : Q T s * ((T + 1 : ℕ) : ℝ) ≤ V s := by
      have hanti_le : ∀ j ∈ Finset.range (T + 1), Q T s ≤ Q j s := fun j hj ↦
        (antitone_nat_of_succ_le (f := fun i ↦ Q i s) (fun i ↦ hQ_anti i s))
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      calc Q T s * ((T + 1 : ℕ) : ℝ)
          = ∑ _ ∈ Finset.range (T + 1), Q T s := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ j ∈ Finset.range (T + 1), Q j s := Finset.sum_le_sum hanti_le
        _ ≤ V s := hQ_sum_le (T + 1) s hs
    have hQ_avg_le :
        (∑ s ∈ Finset.range (k + 1), P s * Q T s) ≤ V_avg / ((T + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hpos, Finset.sum_mul]
      refine Finset.sum_le_sum fun s hs_mem ↦ ?_
      have hs : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs_mem)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hT_mul s hs) (hP_nonneg s hs)
    have hr_eq :
        (∑ s ∈ Finset.range (k + 1),
          P s * whileRecProb n k k_stop b g K (fun _ ↦ 1) (T + 1) s) =
          1 - ∑ s ∈ Finset.range (k + 1), P s * Q T s := by
      have hcongr (s : ℕ) :
          P s * whileRecProb n k k_stop b g K (fun _ ↦ 1) (T + 1) s = P s - P s * Q T s := by
        dsimp only [Q]
        ring
      simp_rw [hcongr]
      rw [Finset.sum_sub_distrib, hP_sum]
    have hr_ge :
        1 - V_avg / ((T + 1 : ℕ) : ℝ) ≤
          ∑ s ∈ Finset.range (k + 1),
            P s * whileRecProb n k k_stop b g K (fun _ ↦ 1) (T + 1) s := by
      linarith
    have happrox_le :
        wp (.qSet ;; initProg)
          (whileRecWP (wp body) guard (T + 1) postTail) ≤ wp prog post := by
      dsimp only [prog]
      simp only [wp_qSeq]
      exact wp_mono .qSet (wp_mono initProg
        (whileRecWP_le_wp_qWhile guard body (T + 1) postTail))
    have hmat_eq :
        ((wp (.qSet ;; initProg)
            (whileRecWP (wp body) guard (T + 1) postTail)) σ).1 =
          (∑ s ∈ Finset.range (k + 1),
            P s * whileRecProb n k k_stop b g K (fun _ ↦ 1) (T + 1) s) •
              (1 : HermitianMat (Fin (2 ^ (W + M))) ℂ) := by
      apply Subtype.ext
      rw [hinit_wp (whileRecWP (wp body) guard (T + 1) postTail)
          (whileRecProb n k k_stop b g K (fun _ ↦ 1) (T + 1)) (hind (T + 1)) σ,
        HermitianMat.val_eq_coe, HermitianMat.mat_smul, HermitianMat.mat_one]
      exact ofReal_smul_one_eq_smul_one _
    calc (1 - V_avg / ((T + 1 : ℕ) : ℝ)) • (1 : HermitianMat (Fin (2 ^ (W + M))) ℂ)
        ≤ (∑ s ∈ Finset.range (k + 1),
            P s * whileRecProb n k k_stop b g K (fun _ ↦ 1) (T + 1) s) •
              (1 : HermitianMat (Fin (2 ^ (W + M))) ℂ) :=
          smul_le_smul_of_nonneg_right hr_ge zero_le_one
      _ = ((wp (.qSet ;; initProg)
            (whileRecWP (wp body) guard (T + 1) postTail)) σ).1 := hmat_eq.symm
      _ ≤ ((wp prog post) σ).1 := happrox_le σ
  have htend_div :
      Filter.Tendsto (fun T : ℕ ↦ V_avg / ((T + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := V_avg)).mul
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)))
  have htend_smul :
      Filter.Tendsto
        (fun T : ℕ ↦ (1 - V_avg / ((T + 1 : ℕ) : ℝ)) • (1 : HermitianMat (Fin (2 ^ (W + M))) ℂ))
        Filter.atTop (nhds ((1 - 0 : ℝ) • (1 : HermitianMat (Fin (2 ^ (W + M))) ℂ))) :=
    (tendsto_const_nhds.sub htend_div).smul_const _
  have hlim := le_of_tendsto htend_smul (Filter.Eventually.of_forall hstep_le)
  rw [sub_zero, one_smul] at hlim
  exact Subtype.coe_le_coe.mp hlim

/-- Total correctness (`wp = ⊤`) of `qset;; findAllBatchWithLast` (`1 ≤ k`) from any
  nonnegative
  potential `V: ℕ → ℝ` (`0 ≤ V s` for `s ≤ k`) satisfying the `s < k - 1` coupon drift
  inequality
  and a total-correctness hypothesis `hlast_wp` on `lastStage` when `τ res = k - 1`. -/
theorem wp_findAllBatchWithLast_of_drift {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) (_hk : 1 ≤ k) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (K : ℕ → ℕ)
    (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (hlast_wp : ∀ (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ →
        ((wp (lastStage.compile qAssign (groverParallelMarkingOracle m S))
            (wp (measureRegister res (highBlock (m * (n + 1)) (k * n)))
              (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S))) τ).1.1
          (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1)
    (V : ℕ → ℝ) (hV_nonneg : ∀ s ≤ k, 0 ≤ V s)
    (hV_drift : ∀ s < k - 1,
      ((K s + 1 : ℕ) : ℝ) +
        (∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            V (s + (((finRange (b s)).filterMap cs).dedup).length)) ≤ V s) :
    wp (.qSet ;; (findAllBatchWithLast res hm hkN hbg K lastStage).compile qAssign
          (groverParallelMarkingOracle m S))
        (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S) = ⊤ := by
  refine wp_init_seq_findAllBatchTail_of_drift res hm hkN hbg K
    (.measure res (lowBlock (m * (n + 1)) (k * n))) lastStage hcard
    (fun s ↦ if s = 0 then 1 else 0)
    (fun _ _ ↦ by split_ifs <;> norm_num)
    (by
      have h := sum_range_ite_zero_mul k (fun _ ↦ 1)
      simp_all)
    (fun Θ f hΘ σ ↦ ?_)
    hlast_wp V hV_nonneg hV_drift
  dsimp only [compile]
  rw [wp_qSet_measure_lowBlock_apply_mat, ← workMemIdx_zero n m k,
    hΘ 0 (Store.subst σ res 0) 0 (Nat.zero_le k) (by simp) (memPrefixValid_zero S),
    sum_range_ite_zero_mul]

private noncomputable def driftPotMax (n k k_stop : ℕ) (b g K : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | r + 1 =>
      let s := k - (r + 1)
      if s < k_stop then
        driftPotMax n k k_stop b g K r +
          ((K s + 1 : ℕ) : ℝ) /
            (∑ cs : Fin (b s) → Option (Fin (k - s)) with
                1 ≤ (((finRange (b s)).filterMap cs).dedup).length,
              iidCouponProb n (g s) (k - s) (K s) cs)
      else driftPotMax n k k_stop b g K r

private lemma exists_driftPot_of_pos {n k k_stop : ℕ} (hstop : k_stop ≤ k)
    {b g K : ℕ → ℕ} (hb : ∀ s < k_stop, 1 ≤ b s)
    (hpos : ∀ s < k_stop, 0 < groupSuccProb n (g s) (k - s) (K s)) :
    ∃ V : ℕ → ℝ, (∀ s ≤ k, 0 ≤ V s) ∧
      ∀ s < k_stop,
        ((K s + 1 : ℕ) : ℝ) +
          (∑ cs : Fin (b s) → Option (Fin (k - s)),
            iidCouponProb n (g s) (k - s) (K s) cs *
              V (s + (((finRange (b s)).filterMap cs).dedup).length)) ≤ V s := by
  have hp_prog : ∀ s (hs : s < k_stop),
      0 < ∑ cs : Fin (b s) → Option (Fin (k - s)) with
          1 ≤ (((finRange (b s)).filterMap cs).dedup).length,
        iidCouponProb n (g s) (k - s) (K s) cs := by
    intro s hs
    have hsk : s < k := lt_of_lt_of_le hs hstop
    let i₀ : Fin (k - s) := ⟨0, by omega⟩
    let cs₀ : Fin (b s) → Option (Fin (k - s)) := fun _ ↦ some i₀
    have hlen₀ : 1 ≤ (((finRange (b s)).filterMap cs₀).dedup).length := by
      have hmem : i₀ ∈ ((finRange (b s)).filterMap cs₀).dedup := by
        rw [List.mem_dedup, List.mem_filterMap]
        exact ⟨⟨0, hb s hs⟩, mem_finRange _, rfl⟩
      exact List.length_pos_of_mem hmem
    have hcs₀_pos : 0 < iidCouponProb n (g s) (k - s) (K s) cs₀ := by
      unfold iidCouponProb
      refine Finset.prod_pos fun _ _ ↦ ?_
      dsimp only [cs₀, couponDrawProb]
      exact div_pos (hpos s hs) (by exact_mod_cast (by omega : 0 < k - s))
    exact lt_of_lt_of_le hcs₀_pos (Finset.single_le_sum
      (fun cs _ ↦ iidCouponProb_nonneg _ _ _ _ cs)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ cs₀, hlen₀⟩))
  have hstep_pot (r : ℕ) :
      driftPotMax n k k_stop b g K r ≤ driftPotMax n k k_stop b g K (r + 1) := by
    rw [driftPotMax]
    split_ifs with hs
    · exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (hp_prog _ hs).le)
    · exact le_rfl
  have hmono_pot : Monotone (driftPotMax n k k_stop b g K) := monotone_nat_of_le_succ hstep_pot
  have hnonneg_pot (r : ℕ) : 0 ≤ driftPotMax n k k_stop b g K r := by
    simpa [driftPotMax] using hmono_pot (Nat.zero_le r)
  let V (s : ℕ) : ℝ := driftPotMax n k k_stop b g K (k - s)
  refine ⟨V, fun s _ ↦ hnonneg_pot (k - s), fun s hs ↦ ?_⟩
  have hsk : s < k := lt_of_lt_of_le hs hstop
  obtain ⟨r, hr⟩ : ∃ r, k - s = r + 1 := ⟨k - s - 1, by omega⟩
  have hs_eq : k - (r + 1) = s := by omega
  set p := ∑ cs : Fin (b s) → Option (Fin (k - s)) with
      1 ≤ (((finRange (b s)).filterMap cs).dedup).length,
    iidCouponProb n (g s) (k - s) (K s) cs
  set M_r := driftPotMax n k k_stop b g K r
  have hp_pos : 0 < p := hp_prog s hs
  have hstep_gen (r' s' : ℕ) (h_eq : k - (r' + 1) = s') :
      driftPotMax n k k_stop b g K (r' + 1) =
        if s' < k_stop then
          driftPotMax n k k_stop b g K r' +
            ((K s' + 1 : ℕ) : ℝ) /
              (∑ cs : Fin (b s') → Option (Fin (k - s')) with
                  1 ≤ (((finRange (b s')).filterMap cs).dedup).length,
                iidCouponProb n (g s') (k - s') (K s') cs)
        else driftPotMax n k k_stop b g K r' := by
    subst h_eq
    rw [driftPotMax]
  have hVs : V s = M_r + ((K s + 1 : ℕ) : ℝ) / p := by
    dsimp only [V]
    rw [hr, hstep_gen r s hs_eq, ite_eq_left hs]
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun cs : Fin (b s) → Option (Fin (k - s)) ↦
      1 ≤ (((finRange (b s)).filterMap cs).dedup).length)
    (fun cs ↦ iidCouponProb n (g s) (k - s) (K s) cs *
      V (s + (((finRange (b s)).filterMap cs).dedup).length))
  have hp_part := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun cs : Fin (b s) → Option (Fin (k - s)) ↦
      1 ≤ (((finRange (b s)).filterMap cs).dedup).length)
    (fun cs ↦ iidCouponProb n (g s) (k - s) (K s) cs)
  rw [sum_iidCouponProb_eq_one] at hp_part
  have hprog_le :
      (∑ cs : Fin (b s) → Option (Fin (k - s)) with
          1 ≤ (((finRange (b s)).filterMap cs).dedup).length,
        iidCouponProb n (g s) (k - s) (K s) cs *
          V (s + (((finRange (b s)).filterMap cs).dedup).length)) ≤ p * M_r := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun cs hcs ↦ ?_
    have h1 : 1 ≤ (((finRange (b s)).filterMap cs).dedup).length := (Finset.mem_filter.mp hcs).2
    have h2 := dedup_filterMap_fin_length_le cs
    exact mul_le_mul_of_nonneg_left
      (hmono_pot (by omega : k - (s + (((finRange (b s)).filterMap cs).dedup).length) ≤ r))
      (iidCouponProb_nonneg _ _ _ _ _)
  have hstay_eq :
      (∑ cs : Fin (b s) → Option (Fin (k - s)) with
          ¬ 1 ≤ (((finRange (b s)).filterMap cs).dedup).length,
        iidCouponProb n (g s) (k - s) (K s) cs *
          V (s + (((finRange (b s)).filterMap cs).dedup).length)) = (1 - p) * V s := by
    have h0 (cs : Fin (b s) → Option (Fin (k - s)))
        (hcs : cs ∈ Finset.univ.filter
          fun cs ↦ ¬ 1 ≤ (((finRange (b s)).filterMap cs).dedup).length) :
        iidCouponProb n (g s) (k - s) (K s) cs *
          V (s + (((finRange (b s)).filterMap cs).dedup).length) =
          iidCouponProb n (g s) (k - s) (K s) cs * V s := by
      have hl : (((finRange (b s)).filterMap cs).dedup).length = 0 := by
        have := (Finset.mem_filter.mp hcs).2
        omega
      rw [hl, add_zero]
    rw [Finset.sum_congr rfl h0, ← Finset.sum_mul]
    have hnot : (∑ cs : Fin (b s) → Option (Fin (k - s)) with
        ¬ 1 ≤ (((finRange (b s)).filterMap cs).dedup).length,
      iidCouponProb n (g s) (k - s) (K s) cs) = 1 - p := by linarith
    rw [hnot]
  rw [sub_mul, one_mul] at hstay_eq
  have hkey : p * V s = p * M_r + ((K s + 1 : ℕ) : ℝ) := by
    rw [hVs, mul_add, mul_div_cancel₀ _ hp_pos.ne']
  linarith

/-- Total correctness (`wp = ⊤`) of `.qSet;; (initStage.seq findAllBatchTail)` (`1 ≤ k`)
  whenever
  every batch-loop occupancy `s < k - 1` has `1 ≤ b s` and `0 < groupSuccProb n (g s) (k -
  s) (K s)`,
  `initStage` satisfies `hinit_wp` under occupancy law `P`, and `lastStage` satisfies
  `hlast_wp`. -/
theorem wp_init_seq_findAllBatchTail_eq_top {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) (_hk : 1 ≤ k) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (hb : ∀ s < k - 1, 1 ≤ b s) (K : ℕ → ℕ)
    (initStage lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (P : ℕ → ℝ) (hP_nonneg : ∀ s ≤ k, 0 ≤ P s)
    (hP_sum : (∑ s ∈ Finset.range (k + 1), P s) = 1)
    (hinit_wp : ∀ (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (f : ℕ → ℝ),
      (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
        s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (f s : ℂ)) →
        ∀ σ : Store Var,
          ((wp (.qSet ;; initStage.compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
            ((∑ s ∈ Finset.range (k + 1), P s * f s : ℝ) : ℂ) •
              (1 : Operator (2 ^ (m * (n + 1) + k * n))))
    (hpos : ∀ s < k - 1, 0 < groupSuccProb n (g s) (k - s) (K s))
    (hlast_wp : ∀ (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ →
        ((wp (lastStage.compile qAssign (groverParallelMarkingOracle m S))
            (wp (measureRegister res (highBlock (m * (n + 1)) (k * n)))
              (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S))) τ).1.1
          (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1) :
    wp (.qSet ;;
          ((initStage.seq (findAllBatchTail res hm hkN hbg K lastStage)).compile qAssign
            (groverParallelMarkingOracle m S)))
        (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S) = ⊤ := by
  obtain ⟨V, hV_nonneg, hV_drift⟩ := exists_driftPot_of_pos (Nat.sub_le k 1) hb hpos
  exact wp_init_seq_findAllBatchTail_of_drift res hm hkN hbg K initStage lastStage hcard
    P hP_nonneg hP_sum hinit_wp hlast_wp V hV_nonneg hV_drift

/-- Total correctness (`wp = ⊤`) of `qset;; findAllBatchWithLast` (`1 ≤ k`) whenever every
  batch-loop occupancy `s < k - 1` has `1 ≤ b s` and `0 < groupSuccProb n (g s) (k - s) (K
  s)`
  and `lastStage` satisfies `hlast_wp` on `τ res = k - 1`. -/
theorem wp_findAllBatchWithLast_eq_top {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (hb : ∀ s < k - 1, 1 ≤ b s) (K : ℕ → ℕ)
    (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (hpos : ∀ s < k - 1, 0 < groupSuccProb n (g s) (k - s) (K s))
    (hlast_wp : ∀ (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ →
        ((wp (lastStage.compile qAssign (groverParallelMarkingOracle m S))
            (wp (measureRegister res (highBlock (m * (n + 1)) (k * n)))
              (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S))) τ).1.1
          (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1) :
    wp (.qSet ;; (findAllBatchWithLast res hm hkN hbg K lastStage).compile qAssign
          (groverParallelMarkingOracle m S))
        (liftPureProp fun σ ↦ decodeTargets n k (σ res) = S) = ⊤ := by
  obtain ⟨V, hV_nonneg, hV_drift⟩ := exists_driftPot_of_pos (Nat.sub_le k 1) hb hpos
  exact wp_findAllBatchWithLast_of_drift res hm hk hkN hbg K lastStage hcard hlast_wp
    V hV_nonneg hV_drift

private noncomputable def iterWP {Var : Type} {d : ℕ}
    (F : CQAssertion (Store Var) d → CQAssertion (Store Var) d)
    (guard : Store Var → Prop) [DecidablePred guard] :
    ℕ → CQAssertion (Store Var) d → CQAssertion (Store Var) d
  | 0, Ψ => fun σ ↦ if guard σ then Ψ σ else 0
  | t + 1, Ψ => fun σ ↦ if guard σ then F (iterWP F guard t Ψ) σ else 0

private lemma expect_iterWP {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d)
    (t : ℕ) (state : CQState (Store Var) d) (Ψ : CQAssertion (Store Var) d) :
    𝔼[state, iterWP (wp body) guard t Ψ] = 𝔼[activeIter guard body t state, Ψ] := by
  induction t generalizing state with
  | zero =>
    have h0 : iterWP (wp body) guard 0 Ψ =
        fun σ ↦ if guard σ then Ψ σ else (⊥ : CQAssertion (Store Var) d) σ := rfl
    rw [h0, wdExpectItePartition, expect_bot, add_zero, wdActiveIter0]
  | succ t ih =>
    have hs : iterWP (wp body) guard (t + 1) Ψ =
        fun σ ↦ if guard σ then wp body (iterWP (wp body) guard t Ψ) σ
          else (⊥ : CQAssertion (Store Var) d) σ := rfl
    rw [hs, wdExpectItePartition, expect_bot, add_zero, wp_expectation_eq, ih, wdActiveIterS]

private noncomputable def occProb (n k k_stop : ℕ) (b g K : ℕ → ℕ) (target : ℕ) : ℕ → ℕ → ℝ
  | 0, s => if s < k_stop then (if s = target then 1 else 0) else 0
  | t + 1, s =>
      if s < k_stop then
        ∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            occProb n k k_stop b g K target t
              (s + (((finRange (b s)).filterMap cs).dedup).length)
      else 0

private lemma occProb_bounds (n k k_stop : ℕ) (b g K : ℕ → ℕ) (target t s : ℕ) :
    0 ≤ occProb n k k_stop b g K target t s ∧ occProb n k k_stop b g K target t s ≤ 1 := by
  induction t generalizing s with
  | zero =>
    rw [occProb]
    split_ifs <;> norm_num
  | succ t ih =>
    rw [occProb]
    split_ifs
    · refine ⟨Finset.sum_nonneg fun cs _ ↦
        mul_nonneg (iidCouponProb_nonneg _ _ _ _ _) (ih _).1, ?_⟩
      calc (∑ cs : Fin (b s) → Option (Fin (k - s)),
            iidCouponProb n (g s) (k - s) (K s) cs *
              occProb n k k_stop b g K target t
                (s + (((finRange (b s)).filterMap cs).dedup).length))
          ≤ ∑ cs : Fin (b s) → Option (Fin (k - s)),
              iidCouponProb n (g s) (k - s) (K s) cs * 1 :=
            Finset.sum_le_sum fun cs _ ↦
              mul_le_mul_of_nonneg_left (ih _).2 (iidCouponProb_nonneg _ _ _ _ _)
        _ = 1 := by simp [sum_iidCouponProb_eq_one]
    · exact ⟨le_rfl, zero_le_one⟩

private noncomputable def stepCostBatch (n k k_stop : ℕ) (b g K : ℕ → ℕ) (t s : ℕ) : ℝ :=
  ∑ x : Fin k, occProb n k k_stop b g K x.val t s * ((K x.val + 1 : ℕ) : ℝ)

private lemma stepCostBatch_nonneg (n k k_stop : ℕ) (b g K : ℕ → ℕ) (t s : ℕ) :
    0 ≤ stepCostBatch n k k_stop b g K t s :=
  Finset.sum_nonneg fun x _ ↦
    mul_nonneg (occProb_bounds n k k_stop b g K x.val t s).1 (Nat.cast_nonneg _)

private lemma stepCostBatch_zero {n k k_stop : ℕ} (hstop : k_stop ≤ k) (b g K : ℕ → ℕ) (s : ℕ) :
    stepCostBatch n k k_stop b g K 0 s = if s < k_stop then ((K s + 1 : ℕ) : ℝ) else 0 := by
  dsimp only [stepCostBatch]
  conv_lhs =>
    arg 2
    ext x
    rw [occProb]
  split_ifs with hlt
  · rw [sum_eq_single ⟨s, lt_of_lt_of_le hlt hstop⟩ (fun x hx ↦ by
      have hne : s ≠ x.val := fun heq ↦ hx (Fin.ext heq.symm)
      rw [ite_eq_right hne, zero_mul])]
    simp
  · simp

private lemma stepCostBatch_succ (n k k_stop : ℕ) (b g K : ℕ → ℕ) (t s : ℕ) :
    stepCostBatch n k k_stop b g K (t + 1) s =
      if s < k_stop then
        ∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            stepCostBatch n k k_stop b g K t
              (s + (((finRange (b s)).filterMap cs).dedup).length)
      else 0 := by
  dsimp only [stepCostBatch]
  conv_lhs =>
    arg 2
    ext x
    rw [occProb]
  split_ifs with hlt
  · simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · simp

private lemma expectedCost_findAllBatchBody_le {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (K : ℕ → ℕ) (S : Finset (Fin (2 ^ n)))
    (Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))) :
    expectedCost
      (CostModel.ofEmbeddedOracle (n := m * (n + 1) + k * n) (groverParallelMarkingOracle m S))
      ((findAllBatchBody (Var := Var) res hm hkN hbg K).compile qAssign
        (groverParallelMarkingOracle m S)) Δ ≤
      ∑ x : Fin k,
        stateMass (Δ.wdTrueSt fun σ ↦ σ res = (x.val : ℤ)) *
          ((K x.val + 1 : ℕ) : ℝ≥0∞) := by
  set model := CostModel.ofEmbeddedOracle (n := m * (n + 1) + k * n)
    (groverParallelMarkingOracle m S)
  dsimp only [findAllBatchBody]
  rw [Fin.sum_univ_def]
  suffices ∀ (l : List (Fin k)) (Δ' : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))),
      expectedCost model
        ((dispFin res (fun s : Fin k ↦
          batchRound res hm hkN (hbg s.val s.isLt) s.val (K s.val)) l).compile
          qAssign (groverParallelMarkingOracle m S)) Δ' ≤
        (l.map fun x : Fin k ↦
          stateMass (Δ'.wdTrueSt fun σ ↦ σ res = (x.val : ℤ)) *
            ((K x.val + 1 : ℕ) : ℝ≥0∞)).sum from
    this (finRange k) Δ
  intro l
  induction l with
  | nil =>
    intro Δ'
    simp [dispFin]
  | cons x l ih =>
    intro Δ'
    simp only [dispFin, compile, map_cons, List.sum_cons, expectedCost]
    have hbr := costBound_batchRound (Var := Var) res hm hkN (hbg x.val x.isLt) x.val (K x.val) S
      (Δ'.wdTrueSt fun σ ↦ σ res = (x.val : ℤ))
    have hsub (y : Fin k) :
        stateMass
          (((Δ'.wdFalseSt fun σ ↦ σ res = (x.val : ℤ))).wdTrueSt
            fun σ ↦ σ res = (y.val : ℤ)) ≤
          stateMass (Δ'.wdTrueSt fun σ ↦ σ res = (y.val : ℤ)) := by
      refine stateMass_mono fun σ ↦ ?_
      simp only [CQState.wdTrueSt, CQState.wdFalseSt, CQState.restrict]
      split_ifs <;> simp
    have htail : ∀ l' : List (Fin k),
        (l'.map fun y : Fin k ↦
          stateMass
             (((Δ'.wdFalseSt fun σ ↦ σ res = (x.val : ℤ))).wdTrueSt
              fun σ ↦ σ res = (y.val : ℤ)) *
            ((K y.val + 1 : ℕ) : ℝ≥0∞)).sum ≤
          (l'.map fun y : Fin k ↦
            stateMass (Δ'.wdTrueSt fun σ ↦ σ res = (y.val : ℤ)) *
              ((K y.val + 1 : ℕ) : ℝ≥0∞)).sum := by
      intro l'
      induction l' with
      | nil => simp
      | cons y l'' ihl =>
        simp only [map_cons, List.sum_cons]
        exact add_le_add (mul_le_mul_of_nonneg_right (hsub y) zero_le) ihl
    exact add_le_add (by simpa [Nat.cast_add] using hbr) ((ih _).trans (htail l))

private lemma sum_range_expectedCost_init_batch_le {Var : Type} [DecidableEq Var] (res : Var)
    {n m k k_stop : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) (hstop : k_stop ≤ k)
    {b g : ℕ → ℕ} (hbg : ∀ s < k, b s * g s = m) (K : ℕ → ℕ)
    (initStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (P : ℕ → ℝ) (hP_nonneg : ∀ s ≤ k, 0 ≤ P s)
    (hP_sum : (∑ s ∈ Finset.range (k + 1), P s) = 1)
    (hinit_wp : ∀ (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (f : ℕ → ℝ),
      (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
        s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (f s : ℂ)) →
        ∀ σ : Store Var,
          ((wp (.qSet ;; initStage.compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
            ((∑ s ∈ Finset.range (k + 1), P s * f s : ℝ) : ℂ) •
              (1 : Operator (2 ^ (m * (n + 1) + k * n))))
    (initial : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))) (T : ℕ) :
    let W := m * (n + 1)
    let M := k * n
    let model := CostModel.ofEmbeddedOracle (n := W + M) (groverParallelMarkingOracle m S)
    let guard : Store Var → Prop := fun σ ↦ σ res < (k_stop : ℤ)
    let initProg := initStage.compile qAssign (groverParallelMarkingOracle m S)
    let body := (findAllBatchBody (Var := Var) res hm hkN hbg K).compile qAssign
      (groverParallelMarkingOracle m S)
    let state₁ := (interp initProg).toStateFun
      ((interp (.qSet : QProg Var (2 ^ (W + M)))).toStateFun initial)
    (∑ t ∈ Finset.range T, expectedCost model body (activeIter guard body t state₁)) ≤
      stateMass initial *
        ENNReal.ofReal
          (∑ t ∈ Finset.range T,
            ∑ s ∈ Finset.range (k + 1), P s * stepCostBatch n k k_stop b g K t s) := by
  let W := m * (n + 1)
  let M := k * n
  set model := CostModel.ofEmbeddedOracle (n := W + M) (groverParallelMarkingOracle m S)
  let guard : Store Var → Prop := fun σ ↦ σ res < (k_stop : ℤ)
  let initProg := initStage.compile qAssign (groverParallelMarkingOracle m S)
  let body := (findAllBatchBody (Var := Var) res hm hkN hbg K).compile qAssign
    (groverParallelMarkingOracle m S)
  set state₁ := (interp initProg).toStateFun
    ((interp (.qSet : QProg Var (2 ^ (W + M)))).toStateFun initial)
  have hind (x : Fin k) (t : ℕ) :
      ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ M)),
        s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (iterWP (wp body) guard t
              (liftPureProp fun σ ↦ σ res = (x.val : ℤ)) τ).1.1
            (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) =
            (occProb n k k_stop b g K x.val t s : ℂ) := by
    induction t with
    | zero =>
      intro s τ μ _ hτ _
      dsimp only [iterWP, occProb]
      by_cases hlt : s < k_stop
      · have hg : guard τ := by
          dsimp only [guard]
          rw [hτ]
          exact_mod_cast hlt
        rw [ite_eq_left hg, ite_eq_left hlt]
        by_cases hsx : s = x.val
        · have hτx : τ res = (x.val : ℤ) := by rw [hτ, hsx]
          simp [hsx, hτx]
        · have hτx : τ res ≠ (x.val : ℤ) :=
            fun heq ↦ hsx (Int.ofNat.inj (hτ.symm.trans heq))
          simp [hsx, hτx]
      · have hng : ¬ guard τ := by
          dsimp only [guard]
          rw [hτ]
          omega
        rw [ite_eq_right hng, ite_eq_right hlt]
        simp
    | succ t ih =>
      intro s τ μ hs hτ hval
      dsimp only [iterWP, occProb]
      by_cases hlt : s < k_stop
      · have hsk : s < k := lt_of_lt_of_le hlt hstop
        have hg : guard τ := by
          dsimp only [guard]
          rw [hτ]
          exact_mod_cast hlt
        rw [ite_eq_left hg, ite_eq_left hlt]
        have hdisp :
            wp body (iterWP (wp body) guard t (liftPureProp fun σ ↦ σ res = (x.val : ℤ))) τ =
              wp ((batchRound res hm hkN (hbg s hsk) s (K s)).compile qAssign
                (groverParallelMarkingOracle m S))
                (iterWP (wp body) guard t (liftPureProp fun σ ↦ σ res = (x.val : ℤ))) τ :=
          wp_dispFin_apply_of_lt res _ _ _ hsk hτ
        rw [hdisp]
        exact wp_batchRound_workMemIdx_of_invariant res hm hkN (hbg s hsk) s (K s) hcard hval
          (iterWP (wp body) guard t (liftPureProp fun σ ↦ σ res = (x.val : ℤ)))
          (occProb n k k_stop b g K x.val t) ih τ
      · have hng : ¬ guard τ := by
          dsimp only [guard]
          rw [hτ]
          omega
        rw [ite_eq_right hng, ite_eq_right hlt]
        simp
  let occAvg (x : Fin k) (t : ℕ) : ℝ :=
    ∑ s ∈ Finset.range (k + 1), P s * occProb n k k_stop b g K x.val t s
  have hoccAvg_bnds (x : Fin k) (t : ℕ) : 0 ≤ occAvg x t ∧ occAvg x t ≤ 1 := by
    refine ⟨Finset.sum_nonneg fun s hs ↦
      mul_nonneg (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
        (occProb_bounds _ _ _ _ _ _ _ _ _).1, ?_⟩
    calc occAvg x t
        ≤ ∑ s ∈ Finset.range (k + 1), P s * 1 :=
          Finset.sum_le_sum fun s hs ↦
            mul_le_mul_of_nonneg_left (occProb_bounds _ _ _ _ _ _ _ _ _).2
              (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
      _ = 1 := by simp [hP_sum]
  have hocc_mass (t : ℕ) (x : Fin k) :
      stateMass ((activeIter guard body t state₁).wdTrueSt fun σ ↦ σ res = (x.val : ℤ)) =
        stateMass initial * ENNReal.ofReal (occAvg x t) := by
    have htrue :
        stateMass ((activeIter guard body t state₁).wdTrueSt fun σ ↦ σ res = (x.val : ℤ)) =
          ENNReal.ofReal
            𝔼[activeIter guard body t state₁, liftPureProp fun σ ↦ σ res = (x.val : ℤ)] := by
      have hp : liftPureProp (d := 2 ^ (W + M)) (fun σ : Store Var ↦ σ res = (x.val : ℤ)) =
          fun σ ↦ if σ res = (x.val : ℤ) then (⊤ : CQAssertion (Store Var) (2 ^ (W + M))) σ
            else (⊥ : CQAssertion (Store Var) (2 ^ (W + M))) σ := by
        funext σ
        by_cases h : σ res = (x.val : ℤ) <;> simp [h]
      rw [hp, wdExpectItePartition, expect_top, expect_bot, add_zero, stateMass_eq_ofReal_trace]
    have hwp_const :
        wp (.qSet ;; initProg)
          (iterWP (wp body) guard t (liftPureProp fun σ ↦ σ res = (x.val : ℤ))) =
          constAssertion (occAvg x t) := by
      funext σ
      apply Subtype.ext
      apply Subtype.ext
      have hbnd := hoccAvg_bnds x t
      rw [hinit_wp _ (occProb n k k_stop b g K x.val t) (hind x t) σ,
        constAssertion_apply_of_bounds _ hbnd.1 hbnd.2,
        HermitianMat.val_eq_coe, HermitianMat.mat_smul, HermitianMat.mat_one]
      exact ofReal_smul_one_eq_smul_one _
    have hexp :
        𝔼[activeIter guard body t state₁, liftPureProp fun σ ↦ σ res = (x.val : ℤ)] =
          occAvg x t * initial.trace := by
      rw [← expect_iterWP]
      dsimp only [state₁]
      rw [← wp_expectation_eq initProg, ← wp_expectation_eq .qSet, ← wp_qSeq, hwp_const,
        expect_constAssertion _ initial (hoccAvg_bnds x t)]
    rw [htrue, hexp, mul_comm, ENNReal.ofReal_mul initial.trace_nonneg,
      ← stateMass_eq_ofReal_trace]
  calc (∑ t ∈ Finset.range T, expectedCost model body (activeIter guard body t state₁))
      ≤ ∑ t ∈ Finset.range T,
          ∑ x : Fin k,
            stateMass ((activeIter guard body t state₁).wdTrueSt fun σ ↦ σ res = (x.val : ℤ)) *
              ((K x.val + 1 : ℕ) : ℝ≥0∞) :=
        Finset.sum_le_sum fun t _ ↦ expectedCost_findAllBatchBody_le res hm hkN hbg K S _
    _ = stateMass initial *
          ENNReal.ofReal
            (∑ t ∈ Finset.range T,
              ∑ s ∈ Finset.range (k + 1), P s * stepCostBatch n k k_stop b g K t s) := by
        simp_rw [hocc_mass, mul_assoc, ← Finset.mul_sum]
        have hstep_eq (t : ℕ) :
            (∑ x : Fin k, occAvg x t * ((K x.val + 1 : ℕ) : ℝ)) =
              ∑ s ∈ Finset.range (k + 1), P s * stepCostBatch n k k_stop b g K t s := by
          dsimp only [occAvg, stepCostBatch]
          simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        have hstep_nonneg (t : ℕ) :
            0 ≤ ∑ s ∈ Finset.range (k + 1), P s * stepCostBatch n k k_stop b g K t s :=
          Finset.sum_nonneg fun s hs ↦
            mul_nonneg (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
              (stepCostBatch_nonneg _ _ _ _ _ _ t s)
        have hstep_enn (t : ℕ) :
            (∑ x : Fin k,
              ENNReal.ofReal (occAvg x t) * ((K x.val + 1 : ℕ) : ℝ≥0∞)) =
              ENNReal.ofReal
                (∑ s ∈ Finset.range (k + 1), P s * stepCostBatch n k k_stop b g K t s) := by
          rw [← hstep_eq t, ENNReal.ofReal_sum_of_nonneg fun x _ ↦
            mul_nonneg (hoccAvg_bnds x t).1 (Nat.cast_nonneg _)]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [ENNReal.ofReal_mul (hoccAvg_bnds x t).1, ENNReal.ofReal_natCast]
        simp_rw [hstep_enn]
        rw [← ENNReal.ofReal_sum_of_nonneg fun t _ ↦ hstep_nonneg t]

/-- Expected parallel-oracle cost bound (`CostBound... V₀`) of `.qSet;; (initStage.seq
  findAllBatchTail)` from any potential `V: ℕ → ℝ` (`0 ≤ V s` for `s ≤ k`, `c_last ≤ V (k -
  1)`,
  `c_init + ∑ s ≤ k, P s * V s ≤ V₀`) satisfying the `s < k - 1` coupon drift inequality,
  given an
  initializer with cost bound `c_init` and occupancy law `P`. -/
theorem costBound_init_seq_findAllBatchTail_of_drift {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (K : ℕ → ℕ)
    (initStage lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (P : ℕ → ℝ) (hP_nonneg : ∀ s ≤ k, 0 ≤ P s)
    (hP_sum : (∑ s ∈ Finset.range (k + 1), P s) = 1)
    (hinit_wp : ∀ (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (f : ℕ → ℝ),
      (∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ (k * n))),
        s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (Θ τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (f s : ℂ)) →
        ∀ σ : Store Var,
          ((wp (.qSet ;; initStage.compile qAssign (groverParallelMarkingOracle m S)) Θ) σ).1.1 =
            ((∑ s ∈ Finset.range (k + 1), P s * f s : ℝ) : ℂ) •
              (1 : Operator (2 ^ (m * (n + 1) + k * n))))
    (c_init : ℝ≥0)
    (hinit_cost : CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      (initStage.compile qAssign (groverParallelMarkingOracle m S)) c_init)
    (validLastAssn : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)))
    (hvalid_last : ∀ (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ →
        (validLastAssn τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1)
    (c_last : ℝ≥0)
    (hlast_cost : ∀ Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
      𝔼[Δ, validLastAssn] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          (lastStage.compile qAssign (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ * (c_last : ℝ≥0∞))
    (V : ℕ → ℝ) (V₀ : ℝ≥0)
    (hV_nonneg : ∀ s ≤ k, 0 ≤ V s)
    (hV_last : (c_last : ℝ) ≤ V (k - 1))
    (hV_drift : ∀ s < k - 1,
      ((K s + 1 : ℕ) : ℝ) +
        (∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            V (s + (((finRange (b s)).filterMap cs).dedup).length)) ≤ V s)
    (hV0 : (c_init : ℝ) + (∑ s ∈ Finset.range (k + 1), P s * V s) ≤ (V₀ : ℝ)) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      (.qSet ;;
        ((initStage.seq (findAllBatchTail res hm hkN hbg K lastStage)).compile qAssign
          (groverParallelMarkingOracle m S)))
      V₀ := by
  let W := m * (n + 1)
  let M := k * n
  set model := CostModel.ofEmbeddedOracle (n := W + M) (groverParallelMarkingOracle m S)
  let guard₁ : Store Var → Prop := fun σ ↦ σ res < ((k - 1 : ℕ) : ℤ)
  let cond₁ : Store Var → Prop := fun σ ↦ σ res = ((k - 1 : ℕ) : ℤ)
  let initProg := initStage.compile qAssign (groverParallelMarkingOracle m S)
  let body := (findAllBatchBody (Var := Var) res hm hkN hbg K).compile qAssign
    (groverParallelMarkingOracle m S)
  let lastProg := lastStage.compile qAssign (groverParallelMarkingOracle m S)
  let exitAssn : CQAssertion (Store Var) (2 ^ (W + M)) := liftPureProp cond₁
  let exitValidAssn : CQAssertion (Store Var) (2 ^ (W + M)) :=
    fun σ ↦ if cond₁ σ then validLastAssn σ else (⊥ : CQAssertion (Store Var) (2 ^ (W + M))) σ
  let exitBase (s : ℕ) : ℝ := if s = k - 1 then 1 else 0
  let exitP := whileRecProb n k (k - 1) b g K exitBase
  have hexit_bnds : ∀ t s, 0 ≤ exitP t s ∧ exitP t s ≤ 1 :=
    (whileRecProb_bounds (n := n) (k := k) (k_stop := k - 1) (b := b) (g := g) (K := K)
      (base := exitBase) fun _ ↦ by dsimp only [exitBase]; split_ifs <;> norm_num).1
  let hybridCost (T s : ℕ) : ℝ :=
    (∑ t ∈ Finset.range T, stepCostBatch n k (k - 1) b g K t s) + exitP T s * (c_last : ℝ)
  have hhybrid_le (T : ℕ) : ∀ s ≤ k, hybridCost T s ≤ V s := by
    induction T with
    | zero =>
      intro s hs
      dsimp only [hybridCost, exitP]
      rw [whileRecProb, Finset.range_zero, Finset.sum_empty, zero_mul, add_zero]
      exact hV_nonneg s hs
    | succ T ihT =>
      intro s hs
      dsimp only [hybridCost, exitP]
      rw [Finset.sum_range_succ', stepCostBatch_zero (Nat.sub_le k 1) b g K s]
      by_cases hlt : s < k - 1
      · simp_rw [stepCostBatch_succ n k (k - 1) b g K _ s, ite_eq_left hlt]
        rw [← Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        rw [whileRecProb, ite_eq_left hlt, Finset.sum_mul]
        simp_rw [mul_assoc]
        have hcomb :
            (∑ cs : Fin (b s) → Option (Fin (k - s)),
              iidCouponProb n (g s) (k - s) (K s) cs *
                (∑ t ∈ Finset.range T,
                  stepCostBatch n k (k - 1) b g K t
                    (s + (((finRange (b s)).filterMap cs).dedup).length))) +
            (∑ cs : Fin (b s) → Option (Fin (k - s)),
              iidCouponProb n (g s) (k - s) (K s) cs *
                (exitP T (s + (((finRange (b s)).filterMap cs).dedup).length) * (c_last : ℝ))) =
            ∑ cs : Fin (b s) → Option (Fin (k - s)),
              iidCouponProb n (g s) (k - s) (K s) cs *
                hybridCost T (s + (((finRange (b s)).filterMap cs).dedup).length) := by
          rw [← sum_add_distrib]
          refine Finset.sum_congr rfl fun cs _ ↦ ?_
          dsimp only [hybridCost]
          ring
        have hle_sum :
            (∑ cs : Fin (b s) → Option (Fin (k - s)),
              iidCouponProb n (g s) (k - s) (K s) cs *
                hybridCost T (s + (((finRange (b s)).filterMap cs).dedup).length)) ≤
              ∑ cs : Fin (b s) → Option (Fin (k - s)),
                iidCouponProb n (g s) (k - s) (K s) cs *
                  V (s + (((finRange (b s)).filterMap cs).dedup).length) := by
          refine Finset.sum_le_sum fun cs _ ↦
            mul_le_mul_of_nonneg_left (ihT _ ?_) (iidCouponProb_nonneg _ _ _ _ _)
          have hdl := dedup_filterMap_fin_length_le cs
          omega
        change _ + (∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            (exitP T (s + (((finRange (b s)).filterMap cs).dedup).length) * (c_last : ℝ))) ≤ V s
        linarith [hV_drift s hlt]
      · simp_rw [stepCostBatch_succ n k (k - 1) b g K _ s, ite_eq_right hlt,
          Finset.sum_const_zero, add_zero]
        rw [zero_add, whileRecProb, ite_eq_right hlt]
        dsimp only [exitBase]
        by_cases hsk : s = k - 1
        · subst hsk
          rw [ite_eq_left rfl, one_mul]
          exact hV_last
        · rw [ite_eq_right hsk, zero_mul]
          exact hV_nonneg s hs
  intro initial
  dsimp only [findAllBatchTail, compile]
  have hqset_zero : expectedCost model (.qSet : QProg Var (2 ^ (W + M))) initial = 0 := by
    simp [model, CostModel.ofEmbeddedOracle]
  have hm2_zero : ∀ Δ : CQState (Store Var) (2 ^ (W + M)),
      expectedCost model (measureRegister res (highBlock W M)) Δ = 0 := by
    intro Δ
    simp [measureRegister, model, CostModel.ofEmbeddedOracle]
  simp only [expectedCost_qSeq]
  rw [hqset_zero, zero_add, hm2_zero, add_zero]
  set state₀ := (interp (.qSet : QProg Var (2 ^ (W + M)))).toStateFun initial
  set state₁ := (interp initProg).toStateFun state₀
  set state₂ := (interp (.qWhile guard₁ body)).toStateFun state₁
  let exitAvg (t : ℕ) : ℝ := ∑ s ∈ Finset.range (k + 1), P s * exitP t s
  have hexitAvg_bnds (t : ℕ) : 0 ≤ exitAvg t ∧ exitAvg t ≤ 1 := by
    refine ⟨Finset.sum_nonneg fun s hs ↦
      mul_nonneg (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))) (hexit_bnds t s).1,
      ?_⟩
    calc exitAvg t
        ≤ ∑ s ∈ Finset.range (k + 1), P s * 1 :=
          Finset.sum_le_sum fun s hs ↦
            mul_le_mul_of_nonneg_left (hexit_bnds t s).2
              (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
      _ = 1 := by simp [hP_sum]
  have htend_gen (Θ_exit : CQAssertion (Store Var) (2 ^ (W + M)))
      (hΘ_exit : ∀ (s : ℕ) (τ : Store Var) (μ : Fin (2 ^ M)),
        ¬ s < k - 1 → s ≤ k → τ res = (s : ℤ) → MemPrefixValid S s μ →
          (Θ_exit τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = (exitBase s : ℂ)) :
      Filter.Tendsto (fun t ↦ exitAvg t * initial.trace)
        Filter.atTop (nhds 𝔼[state₁, wp (.qWhile guard₁ body) Θ_exit]) := by
    have hexp_iter (t : ℕ) :
        𝔼[state₁, whileRecWP (wp body) guard₁ t Θ_exit] = exitAvg t * initial.trace := by
      have hwp_const :
          wp (.qSet ;; initProg)
            (whileRecWP (wp body) guard₁ t Θ_exit) = constAssertion (exitAvg t) := by
        funext σ
        apply Subtype.ext
        apply Subtype.ext
        have hbnd := hexitAvg_bnds t
        have hind_exit := whileRecWP_workMemIdx_eq res hm hkN (Nat.sub_le k 1) hbg K hcard
          Θ_exit exitBase hΘ_exit t
        rw [hinit_wp _ (exitP t) hind_exit σ,
          constAssertion_apply_of_bounds _ hbnd.1 hbnd.2,
          HermitianMat.val_eq_coe, HermitianMat.mat_smul, HermitianMat.mat_one]
        exact ofReal_smul_one_eq_smul_one _
      dsimp only [state₁, state₀]
      rw [← wp_expectation_eq initProg, ← wp_expectation_eq .qSet, ← wp_qSeq, hwp_const,
        expect_constAssertion _ initial (hexitAvg_bnds t)]
    have hc := tendsto_expect_assertion_ωSup
      (whileRecWP.chain (wp body) (wp_mono body) guard₁ Θ_exit) state₁
    simpa only [whileRecWP.chain_apply, hexp_iter, ← wp_qWhile] using hc
  set E_exit := 𝔼[state₁, wp (.qWhile guard₁ body) exitAssn]
  have htend_exit :
      Filter.Tendsto (fun t ↦ exitAvg t * initial.trace) Filter.atTop (nhds E_exit) := by
    refine htend_gen exitAssn fun s τ μ _ _ hτ _ ↦ ?_
    by_cases hsk : s = k - 1
    · have hc : cond₁ τ := by dsimp only [cond₁]; rw [hτ, hsk]
      simp [exitAssn, exitBase, hc, hsk]
    · have hnc : ¬ cond₁ τ := fun heq ↦ hsk (Int.ofNat.inj (hτ.symm.trans heq))
      simp [exitAssn, exitBase, hnc, hsk]
  have htend_valid :
      Filter.Tendsto (fun t ↦ exitAvg t * initial.trace)
        Filter.atTop (nhds 𝔼[state₁, wp (.qWhile guard₁ body) exitValidAssn]) := by
    refine htend_gen exitValidAssn fun s τ μ _ _ hτ hval ↦ ?_
    by_cases hsk : s = k - 1
    · rw [hsk] at hτ hval
      have hc : cond₁ τ := hτ
      simp only [exitValidAssn, exitBase, hc, hsk, ↓reduceIte, Complex.ofReal_one]
      exact hvalid_last τ μ hτ hval
    · have hnc : ¬ cond₁ τ := fun heq ↦ hsk (Int.ofNat.inj (hτ.symm.trans heq))
      simp [exitValidAssn, exitBase, hnc, hsk]
  have hexit_nonneg : 0 ≤ E_exit := by
    have hneg := le_of_tendsto htend_exit.neg (Filter.Eventually.of_forall fun t ↦
      neg_nonpos.mpr (mul_nonneg (hexitAvg_bnds t).1 initial.trace_nonneg))
    linarith
  have htrace_true : ((state₂.wdTrueSt cond₁).trace : ℝ) = E_exit := by
    have hp : exitAssn =
        fun σ ↦ if cond₁ σ then (⊤ : CQAssertion (Store Var) (2 ^ (W + M))) σ
          else (⊥ : CQAssertion (Store Var) (2 ^ (W + M))) σ := by
      funext σ
      by_cases h : cond₁ σ <;> simp [exitAssn, h]
    dsimp only [E_exit, state₂]
    rw [wp_expectation_eq, hp, wdExpectItePartition, expect_top, expect_bot, add_zero]
  have hexit_mass : stateMass (state₂.wdTrueSt cond₁) = ENNReal.ofReal E_exit := by
    rw [stateMass_eq_ofReal_trace, htrace_true]
  have hvalid_state₂ : 𝔼[state₂.wdTrueSt cond₁, validLastAssn] =
      (state₂.wdTrueSt cond₁).trace := by
    have heq := tendsto_nhds_unique htend_valid htend_exit
    dsimp only [state₂, exitValidAssn] at heq ⊢
    rw [wp_expectation_eq, wdExpectItePartition, expect_bot, add_zero] at heq
    exact heq.trans htrace_true.symm
  let stepAvg (t : ℕ) : ℝ :=
    ∑ s ∈ Finset.range (k + 1), P s * stepCostBatch n k (k - 1) b g K t s
  have hstepAvg_nonneg (t : ℕ) : 0 ≤ stepAvg t :=
    Finset.sum_nonneg fun s hs ↦
      mul_nonneg (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
        (stepCostBatch_nonneg _ _ _ _ _ _ t s)
  let V_tail : ℝ := ∑ s ∈ Finset.range (k + 1), P s * V s
  have hV_tail_nonneg : 0 ≤ V_tail :=
    Finset.sum_nonneg fun s hs ↦
      mul_nonneg (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
        (hV_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
  have hhybrid_avg_le (T : ℕ) :
      (∑ t ∈ Finset.range T, stepAvg t) + exitAvg T * (c_last : ℝ) ≤ V_tail := by
    have hrew :
        (∑ t ∈ Finset.range T, stepAvg t) + exitAvg T * (c_last : ℝ) =
          ∑ s ∈ Finset.range (k + 1), P s * hybridCost T s := by
      dsimp only [stepAvg, exitAvg, hybridCost]
      rw [Finset.sum_comm, Finset.sum_mul, ← sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [← Finset.mul_sum]
      ring
    rw [hrew]
    exact Finset.sum_le_sum fun s hs ↦
      mul_le_mul_of_nonneg_left
        (hhybrid_le T s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
        (hP_nonneg s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
  set A := initial.trace * V_tail
  set B := E_exit * (c_last : ℝ)
  have hB_nonneg : 0 ≤ B := mul_nonneg hexit_nonneg c_last.coe_nonneg
  have hSB_le (T₁ : ℕ) :
      initial.trace * (∑ t ∈ Finset.range T₁, stepAvg t) + B ≤ A := by
    set S₁ := initial.trace * (∑ t ∈ Finset.range T₁, stepAvg t)
    have htend_shift := htend_exit.comp (Filter.tendsto_add_atTop_nat T₁)
    have htend_sum :
        Filter.Tendsto (fun d : ℕ ↦ S₁ + (exitAvg (d + T₁) * initial.trace) * (c_last : ℝ))
          Filter.atTop (nhds (S₁ + B)) :=
      tendsto_const_nhds.add (htend_shift.mul_const (c_last : ℝ))
    refine le_of_tendsto htend_sum (Filter.Eventually.of_forall fun d ↦ ?_)
    have hsub : Finset.range T₁ ⊆ Finset.range (d + T₁) :=
      Finset.range_mono (Nat.le_add_left T₁ d)
    have hmon :
        (∑ t ∈ Finset.range T₁, stepAvg t) ≤ ∑ t ∈ Finset.range (d + T₁), stepAvg t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ ↦ hstepAvg_nonneg t
    have hhyb := hhybrid_avg_le (d + T₁)
    have hmul := mul_le_mul_of_nonneg_left hmon initial.trace_nonneg
    have htot := mul_le_mul_of_nonneg_left hhyb initial.trace_nonneg
    dsimp only [S₁, A] at hmul htot ⊢
    linarith
  have hAB_nonneg : 0 ≤ A - B := by
    have h0 := hSB_le 0
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add] at h0
    linarith
  have hloop_le : expectedCost model (.qWhile guard₁ body) state₁ ≤ ENNReal.ofReal (A - B) := by
    rw [expectedCost_qWhile_eq_tsum, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun T₁ ↦ ?_
    calc _ ≤ stateMass initial * ENNReal.ofReal (∑ t ∈ Finset.range T₁, stepAvg t) :=
          sum_range_expectedCost_init_batch_le res hm hkN (Nat.sub_le k 1) hbg K initStage hcard
            P hP_nonneg hP_sum hinit_wp initial T₁
      _ = ENNReal.ofReal (initial.trace * ∑ t ∈ Finset.range T₁, stepAvg t) := by
          rw [stateMass_eq_ofReal_trace, ENNReal.ofReal_mul initial.trace_nonneg]
      _ ≤ ENNReal.ofReal (A - B) :=
          ENNReal.ofReal_le_ofReal (by linarith [hSB_le T₁])
  have htail_le : expectedCost model (.qIf cond₁ lastProg .skip) state₂ ≤ ENNReal.ofReal B := by
    rw [wdExpectedCostIf]
    have hskip : expectedCost model (.skip : QProg Var (2 ^ (W + M)))
        (state₂.wdFalseSt cond₁) = 0 := by simp
    rw [hskip, add_zero]
    calc expectedCost model lastProg (state₂.wdTrueSt cond₁)
        ≤ stateMass (state₂.wdTrueSt cond₁) * (c_last : ℝ≥0∞) :=
          hlast_cost _ hvalid_state₂
      _ = ENNReal.ofReal B := by
          dsimp only [B]
          rw [hexit_mass, ENNReal.ofReal_mul hexit_nonneg, ENNReal.ofReal_coe_nnreal]
  have hinit_le :
      expectedCost model initProg state₀ ≤ ENNReal.ofReal (initial.trace * (c_init : ℝ)) := by
    calc expectedCost model initProg state₀
        ≤ stateMass state₀ * (c_init : ℝ≥0∞) := hinit_cost state₀
      _ ≤ stateMass initial * (c_init : ℝ≥0∞) :=
          mul_le_mul_of_nonneg_right
            (stateMass_interp_le (.qSet : QProg Var (2 ^ (W + M))) initial) zero_le
      _ = ENNReal.ofReal (initial.trace * (c_init : ℝ)) := by
          rw [ENNReal.ofReal_mul initial.trace_nonneg, ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_coe_nnreal]
  have hA_nonneg : 0 ≤ A := mul_nonneg initial.trace_nonneg hV_tail_nonneg
  have hC_nonneg : 0 ≤ initial.trace * (c_init : ℝ) :=
    mul_nonneg initial.trace_nonneg c_init.coe_nonneg
  calc expectedCost model initProg state₀ +
        (expectedCost model (.qWhile guard₁ body) state₁ +
          expectedCost model (.qIf cond₁ lastProg .skip) state₂)
      ≤ ENNReal.ofReal (initial.trace * (c_init : ℝ)) +
          (ENNReal.ofReal (A - B) + ENNReal.ofReal B) :=
        add_le_add hinit_le (add_le_add hloop_le htail_le)
    _ = ENNReal.ofReal (initial.trace * ((c_init : ℝ) + V_tail)) := by
        rw [← ENNReal.ofReal_add hAB_nonneg hB_nonneg, sub_add_cancel,
          ← ENNReal.ofReal_add hC_nonneg hA_nonneg]
        dsimp only [A]
        rw [← mul_add]
    _ ≤ ENNReal.ofReal (initial.trace * (V₀ : ℝ)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hV0 initial.trace_nonneg)
    _ = stateMass initial * (V₀ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul initial.trace_nonneg, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_coe_nnreal]

/-- Expected parallel-oracle cost bound (`CostBound... V₀`) of `qset;; findAllBatchWithLast`
  from any potential `V: ℕ → ℝ` (`0 ≤ V s` for `s ≤ k`, `c_last ≤ V (k - 1)`, `V 0 ≤ V₀`)
  satisfying
  the `s < k - 1` coupon drift inequality `(K s + 1) + E[V(s + Δ)] ≤ V s` and an
  invariant-guarded
  cost bound of `c_last` on `lastStage` under `validLastAssn`. -/
theorem costBound_findAllBatchWithLast_of_drift {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n) {b g : ℕ → ℕ}
    (hbg : ∀ s < k, b s * g s = m) (K : ℕ → ℕ)
    (lastStage : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m))
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (validLastAssn : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)))
    (hvalid_last : ∀ (τ : Store Var) (μ : Fin (2 ^ (k * n))),
      τ res = ((k - 1 : ℕ) : ℤ) → MemPrefixValid S (k - 1) μ →
        (validLastAssn τ).1.1 (workMemIdx n m k 0 μ) (workMemIdx n m k 0 μ) = 1)
    (c_last : ℝ≥0)
    (hlast_cost : ∀ Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n)),
      𝔼[Δ, validLastAssn] = Δ.trace →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          (lastStage.compile qAssign (groverParallelMarkingOracle m S)) Δ ≤
          stateMass Δ * (c_last : ℝ≥0∞))
    (V : ℕ → ℝ) (V₀ : ℝ≥0)
    (hV_nonneg : ∀ s ≤ k, 0 ≤ V s)
    (hV_last : (c_last : ℝ) ≤ V (k - 1))
    (hV_drift : ∀ s < k - 1,
      ((K s + 1 : ℕ) : ℝ) +
        (∑ cs : Fin (b s) → Option (Fin (k - s)),
          iidCouponProb n (g s) (k - s) (K s) cs *
            V (s + (((finRange (b s)).filterMap cs).dedup).length)) ≤ V s)
    (hV0 : V 0 ≤ (V₀ : ℝ)) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      (.qSet ;; (findAllBatchWithLast res hm hkN hbg K lastStage).compile qAssign
        (groverParallelMarkingOracle m S))
      V₀ := by
  let W := m * (n + 1)
  let M := k * n
  refine costBound_init_seq_findAllBatchTail_of_drift res hm hkN hbg K
    (.measure res (lowBlock W M)) lastStage hcard
    (fun s ↦ if s = 0 then 1 else 0)
    (fun _ _ ↦ by split_ifs <;> norm_num)
    (by
      have h := sum_range_ite_zero_mul k fun _ ↦ (1 : ℝ)
      simp_all)
    (fun Θ f hΘ σ ↦ ?_)
    0
    (fun Δ ↦ by simp [compile, measureRegister, CostModel.ofEmbeddedOracle])
    validLastAssn hvalid_last c_last hlast_cost V V₀ hV_nonneg hV_last hV_drift ?_
  · rw [compile, wp_qSet_measure_lowBlock_apply_mat, ← workMemIdx_zero n m k,
      hΘ 0 (Store.subst σ res 0) 0 (Nat.zero_le k) (by simp) (memPrefixValid_zero S),
      sum_range_ite_zero_mul]
  · rw [NNReal.coe_zero, zero_add, sum_range_ite_zero_mul]
    exact hV0

end

end QuantumComputation.Specs.DickeSol
end WD_FindAllBatchRound


section WD_FindAllStage1

namespace QuantumComputation.Specs.DickeSol

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

/-! ## Diagonal Observables and `MemPrefixValid` Stage Assertions -/

/-- Computational-basis projector `|o⟩⟨o|` as a `HermitianMat`. -/
noncomputable def compProjHermitian {d : ℕ} (o : Fin d) : HermitianMat (Fin d) ℂ :=
  ⟨compProj o, compProj_isHermitian o⟩

@[simp]
theorem compProjHermitian_mat {d : ℕ} (o : Fin d) :
    (compProjHermitian o).mat = compProj o := rfl

@[simp]
theorem compProjHermitian_nonneg {d : ℕ} (o : Fin d) :
    0 ≤ compProjHermitian o := compProj_nonneg o

@[simp]
theorem compProjHermitian_le_one {d : ℕ} (o : Fin d) :
    compProjHermitian o ≤ 1 := compProj_le_one o

noncomputable def realDiagObs {d : ℕ} (f : Fin d → ℝ)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) : Observable (Fin d) :=
  ⟨∑ z : Fin d, f z • compProjHermitian z,
    Finset.sum_nonneg fun z _ ↦ smul_nonneg (h0 z) (compProjHermitian_nonneg z),
    calc ∑ z : Fin d, f z • compProjHermitian z
        ≤ ∑ z : Fin d, (1 : ℝ) • compProjHermitian z :=
          Finset.sum_le_sum fun z _ ↦
            smul_le_smul_of_nonneg_right (h1 z) (compProjHermitian_nonneg z)
      _ = 1 := by
          ext1
          simp [HermitianMat.mat_finset_sum]⟩

lemma realDiagObs_mat {d : ℕ} (f : Fin d → ℝ)
    (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) :
    (realDiagObs f h0 h1).1.1 = diagonal (fun z ↦ (f z : ℂ)) := by
  rw [realDiagObs, HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum,
    ← Matrix.sum_single_eq_diagonal]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [HermitianMat.mat_smul, compProjHermitian_mat, compProj, Matrix.smul_single,
    Complex.real_smul, mul_one]

lemma observable_diag_real_bounds {d : ℕ} (O : Observable (Fin d)) (c : Fin d → ℂ)
    (hO : O.1.1 = diagonal c) (z : Fin d) :
    c z = ((c z).re : ℂ) ∧ 0 ≤ (c z).re ∧ (c z).re ≤ 1 := by
  have hself : star (O.1.1 z z) = O.1.1 z z := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun O.1.2 z) z
  rw [hO, Matrix.diagonal_apply_eq] at hself
  have hre : c z = ((c z).re : ℂ) := (Complex.conj_eq_iff_re.mp hself).symm
  have htr (A : HermitianMat (Fin d) ℂ) (g : Fin d → ℂ) (hA : A.1 = diagonal g) :
      ⟪A, compProjHermitian z⟫_ℝ = (g z).re := by
    rw [HermitianMat.inner_eq_re_trace]
    have hmat : A.mat * (compProjHermitian z).mat = Matrix.single z z (g z) := by
      change A.1 * compProj z = _
      rw [hA, compProj]
      ext i j
      rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
      by_cases h : z = i ∧ z = j
      · rcases h with ⟨rfl, rfl⟩; simp
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    rw [hmat]
    dsimp only [Matrix.trace, Matrix.diag]
    rw [sum_eq_single z (fun x hx ↦ by
      rw [Matrix.single_apply, ite_eq_right (fun h ↦ hx h.1.symm)])]
    rw [Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩]
    rfl
  have h0 : 0 ≤ (c z).re := by
    rw [← htr O.1 c hO]
    exact HermitianMat.inner_ge_zero O.2.1 (compProjHermitian_nonneg z)
  have h1 : (c z).re ≤ 1 := by
    have hle := HermitianMat.inner_mono' (compProjHermitian_nonneg z) O.2.2
    rwa [htr O.1 c hO, htr 1 (fun _ ↦ 1) Matrix.diagonal_one.symm, Complex.one_re] at hle
  exact ⟨hre, h0, h1⟩

lemma realDiagObs_le_of_mat {d : ℕ} {f g : Fin d → ℝ}
    {hf0 : ∀ z, 0 ≤ f z} {hf1 : ∀ z, f z ≤ 1}
    (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    {O : Observable (Fin d)} (hO : O.1.1 = diagonal (fun z ↦ (g z : ℂ)))
    (hfg : ∀ z, f z ≤ g z) :
    realDiagObs f hf0 hf1 ≤ O := by
  have hO_eq : O = realDiagObs g hg0 hg1 :=
    Subtype.ext (HermitianMat.ext (hO.trans (realDiagObs_mat g hg0 hg1).symm))
  rw [hO_eq]
  exact Finset.sum_le_sum fun z _ ↦
    smul_le_smul_of_nonneg_right (hfg z) (compProjHermitian_nonneg z)

lemma le_realDiagObs_of_mat {d : ℕ} {f g : Fin d → ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    {hg0 : ∀ z, 0 ≤ g z} {hg1 : ∀ z, g z ≤ 1}
    {O : Observable (Fin d)} (hO : O.1.1 = diagonal (fun z ↦ (f z : ℂ)))
    (hfg : ∀ z, f z ≤ g z) :
    O ≤ realDiagObs g hg0 hg1 := by
  have hO_eq : O = realDiagObs f hf0 hf1 :=
    Subtype.ext (HermitianMat.ext (hO.trans (realDiagObs_mat f hf0 hf1).symm))
  rw [hO_eq]
  exact Finset.sum_le_sum fun z _ ↦
    smul_le_smul_of_nonneg_right (hfg z) (compProjHermitian_nonneg z)

noncomputable def validInd (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) : ℝ :=
  open Classical in
  if MemPrefixValid S j (lowHighEquiv (m * (n + 1)) (k * n) z).2 then 1 else 0

noncomputable def invalidInd (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) : ℝ :=
  open Classical in
  if MemPrefixValid S j (lowHighEquiv (m * (n + 1)) (k * n) z).2 then 0 else 1

lemma validInd_bounds (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) :
    0 ≤ validInd n m k S j z ∧ validInd n m k S j z ≤ 1 := by
  unfold validInd
  split_ifs <;> constructor <;> norm_num

lemma invalidInd_bounds (n m k : ℕ) (S : Finset (Fin (2 ^ n))) (j : ℕ)
    (z : Fin (2 ^ (m * (n + 1) + k * n))) :
    0 ≤ invalidInd n m k S j z ∧ invalidInd n m k S j z ≤ 1 := by
  unfold invalidInd
  split_ifs <;> constructor <;> norm_num

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
  dsimp only [scaledValidObs, validObs, realDiagObs]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun z _ ↦
    mul_smul c (validInd n m k S j z) (compProjHermitian z)

lemma scaledValid_add_invalid_le_one {Var : Type} (n m k : ℕ)
    (S : Finset (Fin (2 ^ n))) (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (σ : Store Var) :
    (scaledValidObs n m k S j c hc0 hc1 σ).1 + (invalidObs n m k S j σ).1 ≤ 1 := by
  dsimp only [scaledValidObs, invalidObs, realDiagObs]
  rw [← Finset.sum_add_distrib]
  calc ∑ z, ((c * validInd n m k S j z) • compProjHermitian z +
        invalidInd n m k S j z • compProjHermitian z)
      = ∑ z, (c * validInd n m k S j z + invalidInd n m k S j z) • compProjHermitian z :=
        Finset.sum_congr rfl fun z _ ↦ (add_smul _ _ _).symm
    _ ≤ ∑ z, (1 : ℝ) • compProjHermitian z := by
        refine Finset.sum_le_sum fun z _ ↦
          smul_le_smul_of_nonneg_right ?_ (compProjHermitian_nonneg z)
        unfold validInd invalidInd
        split_ifs <;> linarith
    _ = 1 := by
        ext1
        simp [HermitianMat.mat_finset_sum]

lemma validObs_add_invalidObs_eq_top {Var : Type} (n m k : ℕ)
    (S : Finset (Fin (2 ^ n))) (j : ℕ) :
    (validObs (Var := Var) n m k S j).add (invalidObs n m k S j)
      (fun σ ↦ by
        have h := scaledValid_add_invalid_le_one n m k S j 1 zero_le_one le_rfl σ
        rwa [scaledValidObs_smul, one_smul] at h) = ⊤ := by
  funext σ
  apply Subtype.ext
  apply HermitianMat.ext
  change (validObs n m k S j σ).1.1 + (invalidObs n m k S j σ).1.1 = 1
  dsimp only [validObs, invalidObs]
  rw [realDiagObs_mat, realDiagObs_mat]
  ext z₁ z₂
  rw [Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : z₁ = z₂
  · subst h
    simp only [↓reduceIte, validInd, invalidInd]
    split_ifs <;> norm_num
  · simp [h]

lemma expect_invalidObs_eq_zero {Var : Type} {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} {j : ℕ} {Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))}
    (hV : 𝔼[Δ, validObs n m k S j] = Δ.trace) :
    𝔼[Δ, invalidObs n m k S j] = 0 := by
  have htop : 𝔼[Δ, (validObs (Var := Var) n m k S j).add (invalidObs n m k S j)
      (fun σ ↦ by
        have h := scaledValid_add_invalid_le_one n m k S j 1 zero_le_one le_rfl σ
        rwa [scaledValidObs_smul, one_smul] at h)] = Δ.trace := by
    rw [validObs_add_invalidObs_eq_top, expect_top]
  rw [expect_assertion_add] at htop
  linarith

lemma validState_step {Var : Type} [DecidableEq Var] {n m k j j' : ℕ}
    {S : Finset (Fin (2 ^ n))} {P : QProg Var (2 ^ (m * (n + 1) + k * n))}
    {Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))}
    (hV : 𝔼[Δ, validObs n m k S j] = Δ.trace)
    (hwp : validObs n m k S j ≤ wp P (validObs n m k S j')) :
    let Δ' := (interp P).toStateFun Δ
    𝔼[Δ', validObs n m k S j'] = Δ'.trace ∧ stateMass Δ' = stateMass Δ := by
  intro Δ'
  have h1 : (Δ.trace : ℝ) ≤ 𝔼[Δ', validObs n m k S j'] := by
    rw [← hV, ← wp_expectation_eq]
    exact expect_mono le_rfl hwp
  have h2 : 𝔼[Δ', validObs n m k S j'] ≤ (Δ'.trace : ℝ) := by
    rw [← expect_top Δ']
    exact expect_mono le_rfl le_top
  have h3 : (Δ'.trace : ℝ) ≤ (Δ.trace : ℝ) := by
    exact_mod_cast (interp P).trace_toStateFun_le Δ
  refine ⟨by linarith, ?_⟩
  rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace,
    show (Δ'.trace : ℝ) = Δ.trace by linarith]

/-! ## Quadratic Forms, Register Identities, and Zero-Cost Work Reset -/

private noncomputable def vecQuad {d : ℕ} (A : Operator d) (ψ : Fin d → ℂ) : ℂ :=
  star ψ ⬝ᵥ (A *ᵥ ψ)

private lemma vecQuad_single {d : ℕ} (A : Operator d) (z : Fin d) :
    A z z = vecQuad A (Pi.single z 1) := by
  simp [vecQuad]

private lemma vecQuad_conj {d : ℕ} (U A : Operator d) (ψ : Fin d → ℂ) :
    vecQuad (Uᴴ * A * U) ψ = vecQuad A (U *ᵥ ψ) := by
  unfold vecQuad
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
  set v := A *ᵥ (U *ᵥ ψ)
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, star_mul']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring

private lemma vecQuad_smul {d : ℕ} (A : Operator d) (c : ℝ) (ψ : Fin d → ℂ) :
    vecQuad A ((c : ℂ) • ψ) = ((c ^ 2 : ℝ) : ℂ) * vecQuad A ψ := by
  unfold vecQuad
  rw [Matrix.mulVec_smul]
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Complex.star_def,
    map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ ↦ by push_cast; ring

private lemma vecQuad_diagonal {d : ℕ} (g : Fin d → ℂ) (ψ : Fin d → ℂ) :
    vecQuad (diagonal g) ψ = ∑ z : Fin d, (normSq (ψ z) : ℂ) * g z := by
  unfold vecQuad
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
  ring

private lemma workMemState_add_left {W M : ℕ} (ψ₁ ψ₂ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (ψ₁ + ψ₂) φ = workMemState ψ₁ φ + workMemState ψ₂ φ := by
  funext z
  dsimp only [workMemState, Pi.add_apply]
  ring

private lemma workMemState_smul_left {W M : ℕ} (c : ℂ) (ψ : Fin (2 ^ W) → ℂ) (φ : Fin (2 ^ M) → ℂ) :
    workMemState (c • ψ) φ = c • workMemState ψ φ := by
  funext z
  dsimp only [workMemState, Pi.smul_apply, smul_eq_mul]
  ring

private lemma workReg_eq_lowBlk1 (n m k : ℕ) :
    workReg n m (m * (n + 1) + k * n) (by omega) = lowBlock (m * (n + 1)) (k * n) := by
  ext i
  simp

private lemma workMemReg_eq_whl1 (n m k : ℕ) :
    workMemReg n m k (m * (n + 1) + k * n) le_rfl = QRegister.whole (m * (n + 1) + k * n) := by
  ext i
  simp

private lemma wp_deflatedOracle_vecQuad {Var : Type} [DecidableEq Var] {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k))
    (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k active μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) :
    vecQuad
      (((wp ((deflatedOracle (Var := Var) (n := n) (m := m) (k := k)
          (Q := m * (n + 1) + k * n) le_rfl active).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState ψ (Pi.single μ 1)) =
    vecQuad ((Θ σ).1.1)
      (workMemState
        ((permutationUnitary (parallelMarkPerm n m (S \ memSeen n k active μ))).1 *ᵥ ψ)
        (Pi.single μ 1)) := by
  unfold deflatedOracle
  dsimp only [compile]
  rw [wp_qSeq, wp_qAssign, wp_qAssign, wp_phaseTag, qhlQAssign_val,
    qhlQAssign_val, vecQuad_conj, vecQuad_conj]
  simp only [workFullReg, workReg_eq_lowBlk1, workMemReg_eq_whl1,
    QRegister.embedUnitary_compose, QRegister.whole_embedUnitary]
  rw [QRegister.embedUnitary_val (lowBlock (m * (n + 1)) (k * n)),
    unmark_mul_parallelOracle_workMemState active ψ μ hsub,
    fullReg_embedUnitary_eq_permutationUnitary]

private lemma wp_deflatedPhaseStep_vecQuad {Var : Type} [DecidableEq Var] {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (active : Finset (Fin k))
    (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (μ : Fin (2 ^ (k * n)))
    (hsub : memSeen n k active μ ⊆ S)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) :
    vecQuad
      (((wp ((deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
          (Q := m * (n + 1) + k * n) le_rfl active).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState ψ (Pi.single μ 1)) =
    vecQuad ((Θ σ).1.1)
      (workMemState (sDiagM n m (S \ memSeen n k active μ) *ᵥ ψ) (Pi.single μ 1)) := by
  unfold deflatedPhaseStep deflatedOracle
  dsimp only [compile]
  rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qAssign, wp_qAssign, wp_qAssign, wp_qAssign,
    wp_phaseTag, wp_phaseTag, wp_phaseTag]
  simp only [qhlQAssign_val, vecQuad_conj, workFullReg, workReg_eq_lowBlk1,
    workMemReg_eq_whl1, QRegister.embedUnitary_compose, QRegister.whole_embedUnitary]
  rw [QRegister.embedUnitary_val (lowBlock (m * (n + 1)) (k * n)),
    QRegister.embedUnitary_val (lowBlock (m * (n + 1)) (k * n))]
  have hmat := deflatedPhaseMat_mulVec_workMemState active ψ μ hsub
  dsimp only at hmat
  rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmat]

noncomputable def mapAndMeasureLow {Var : Type} (res : Var) (W M O : ℕ)
    (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M))) : OracleCirc Var (W + M) O :=
  .seq (qMap res g) (.measure res (lowBlock W M))

private lemma costBound_mapAndMeasureLow {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M)))
    {oracle : Unitary (2 ^ O)} (hor : IsRealMatrix oracle.1) :
    CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
      ((mapAndMeasureLow res W M O g).compile qAssign oracle) 0 := by
  unfold mapAndMeasureLow
  dsimp only [compile]
  have hmeas : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
      (measureRegister res (lowBlock W M)) 0 := by
    simpa [measureRegister, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) (CostModel.ofEmbeddedOracle oracle)
        res ((lowBlock W M).computationalBasisMeasurement :
          Measurement (2 ^ (W + M)) (2 ^ W))
  simpa using (costBound_qMap (Var := Var) res g hor).seq hmeas

private lemma wp_mapAndMeasureLow {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M)))
    (oracle : Unitary (2 ^ O)) (H : ℤ → Operator (2 ^ (W + M)))
    (Φ : CQAssertion (Store Var) (2 ^ (W + M))) (hΦ : ∀ τ, (Φ τ).1.1 = H (τ res)) (σ : Store Var) :
    ((wp ((mapAndMeasureLow res W M O g).compile qAssign oracle) Φ) σ).1.1 =
      diagonal (fun z : Fin (2 ^ (W + M)) ↦
        H (Int.ofNat ((lowHighEquiv W M (g z)).1).val) (g z) (g z)) := by
  unfold mapAndMeasureLow
  dsimp only [compile]
  rw [wp_qSeq]
  let M_meas : Operator (2 ^ (W + M)) :=
    ∑ o : Fin (2 ^ W),
      (lowBlock W M).basisOutcomeProjector o * H (Int.ofNat o.val) *
        (lowBlock W M).basisOutcomeProjector o
  have hmeas (τ : Store Var) :
      ((wp (measureRegister res (lowBlock W M)) Φ) τ).1.1 = M_meas := by
    rw [wp_measureRegister]
    exact Finset.sum_congr rfl fun o _ ↦ by rw [hΦ]; simp [Store.subst]
  rw [wp_qMap res g oracle (fun _ ↦ M_meas) _ hmeas σ]
  refine congrArg diagonal (funext fun z ↦ ?_)
  dsimp only [M_meas]
  rw [Matrix.sum_apply]
  let o₀ : Fin (2 ^ W) := (lowHighEquiv W M (g z)).1
  rw [sum_eq_single o₀ (fun o ho ↦ by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
      extractIndex_lowBlock, ite_eq_right (Ne.symm ho), mul_zero])]
  rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
    extractIndex_lowBlock, ite_eq_left rfl, one_mul, mul_one]

private lemma wp_mapAndMeasureLow_bot {Var : Type} [DecidableEq Var] (res : Var)
    {W M O : ℕ} (g : Fin (2 ^ (W + M)) → Fin (2 ^ (W + M))) (oracle : Unitary (2 ^ O)) :
    wp ((mapAndMeasureLow res W M O g).compile qAssign oracle) ⊥ = ⊥ := by
  funext σ
  apply Subtype.ext
  apply HermitianMat.ext
  change ((wp ((mapAndMeasureLow res W M O g).compile qAssign oracle) ⊥) σ).1.1 = 0
  rw [wp_mapAndMeasureLow res g oracle (fun _ ↦ 0) ⊥ (fun _ ↦ rfl) σ]
  simp

private def PureUnitaryProg {Var : Type} {d : ℕ} : QProg Var d → Prop
  | .skip => True
  | .qAssign _ => True
  | .qSeq c₁ c₂ => PureUnitaryProg c₁ ∧ PureUnitaryProg c₂
  | _ => False

private lemma wp_eq_of_pureUnitary {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {P : QProg Var d} (hP : PureUnitaryProg P) {Θ₁ Θ₂ : CQAssertion (Store Var) d}
    {σ₁ σ₂ : Store Var} (h : Θ₁ σ₁ = Θ₂ σ₂) :
    wp P Θ₁ σ₁ = wp P Θ₂ σ₂ := by
  induction P generalizing Θ₁ Θ₂ with
  | «skip» => exact h
  | qAssign U =>
    rw [wp_qAssign, wp_qAssign, CQAssertion.qAssign_apply, CQAssertion.qAssign_apply, h]
  | qSeq c₁ c₂ ih₁ ih₂ =>
    rw [wp_qSeq, wp_qSeq]
    exact ih₁ hP.1 (ih₂ hP.2 h)
  | _ => cases hP

def resetWorkFn (W M : ℕ) (z : Fin (2 ^ (W + M))) : Fin (2 ^ (W + M)) :=
  (lowHighEquiv W M).symm (0, (lowHighEquiv W M z).2)

noncomputable def workReset {Var : Type} (res : Var) (W M O : ℕ) :
    OracleCirc Var (W + M) O :=
  mapAndMeasureLow res W M O (resetWorkFn W M)

/-! ## Shared Deflated Verification Write (`markAndWrite`) -/

noncomputable def markAndWrite {Var : Type} (n m k : ℕ) (s : Fin k) :
    OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
  .seq (deflatedOracle le_rfl (memPrefix k s.val))
    (.step (phaseTag (permutationUnitary
      (memWriteBatchPerm s.val (fun w ↦ (firstMarkedAddr n m w).toList)))))

private lemma costBound_markAndWrite {Var : Type} [DecidableEq Var] (n m k : ℕ) (s : Fin k)
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((markAndWrite n m k s).compile qAssign (groverParallelMarkingOracle m S)) 1 := by
  unfold markAndWrite
  dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  simpa using (costBound_deflatedOracle (Var := Var) le_rfl (memPrefix k s.val) S).seq
    (costBound_qAssign_phaseTag (Var := Var) hor _)

private lemma vecQuad_markAndWrite {Var : Type} [DecidableEq Var] {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (s : Fin k) (v : Fin (2 ^ (m * n)) → ℂ)
    (μ : Fin (2 ^ (k * n))) (hval : MemPrefixValid S s.val μ)
    (g : Fin (2 ^ (m * (n + 1) + k * n)) → ℂ)
    (G : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var)
    (hG : (G σ).1.1 = diagonal g) :
    let R := S \ memSeen n k (memPrefix k s.val) μ
    let hits := fun w : Fin (2 ^ (m * (n + 1))) ↦ (firstMarkedAddr n m w).toList
    let w_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (m * (n + 1))) :=
      parallelMarkPerm n m R ((addrReg n m).basisSplitEquiv.symm (u, 0))
    let μ_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (k * n)) :=
      (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s.val hits (w_of u))
    vecQuad
      (((wp ((markAndWrite (Var := Var) n m k s).compile qAssign
          (groverParallelMarkingOracle m S)) G) σ).1.1)
      (workMemState ((addrReg n m).tensorState v (Pi.single 0 1)) (Pi.single μ 1)) =
    ∑ u : Fin (2 ^ (m * n)),
      (normSq (v u) : ℂ) *
        g ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) := by
  intro R hits w_of μ_of
  have hsub : memSeen n k (memPrefix k s.val) μ ⊆ S :=
    (card_memSeen_of_memPrefixValid hval).2
  unfold markAndWrite
  dsimp only [compile]
  rw [wp_qSeq, wp_deflatedOracle_vecQuad (memPrefix k s.val) _ μ hsub,
    wp_qAssign, wp_phaseTag, qhlQAssign_val, hG, vecQuad_conj, vecQuad_diagonal]
  let W := m * (n + 1)
  let M := k * n
  let perm := memWriteBatchPerm (k := k) s.val hits
  let ψ_mark := (permutationUnitary (parallelMarkPerm n m R)).1 *ᵥ
    (addrReg n m).tensorState v (Pi.single 0 1)
  let ψ_out := (permutationUnitary perm).1 *ᵥ workMemState ψ_mark (Pi.single μ 1)
  change ∑ z : Fin (2 ^ (W + M)), (normSq (ψ_out z) : ℂ) * g z = _
  have hψ_mark (w : Fin (2 ^ W)) :
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
    dsimp only [QRegister.tensorState]
    rw [← QRegister.basisSplitEquiv_apply_fst]
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
    dsimp only [workMemState]
    by_cases hμ : (lowHighEquiv W M (perm.symm z)).2 = μ
    · rw [hμ, Pi.single_eq_same, mul_one, ite_eq_left rfl]
    · rw [Pi.single_eq_of_ne hμ, mul_zero, ite_eq_right hμ]
  rw [← Equiv.sum_comp perm (fun z ↦ (normSq (ψ_out z) : ℂ) * g z)]
  simp_rw [hψ_out, Equiv.symm_apply_apply]
  rw [← (lowHighEquiv W M).symm.sum_comp]
  simp_rw [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  have hrow (w : Fin (2 ^ W)) :
      (∑ μ' : Fin (2 ^ M),
        (normSq (if μ' = μ then ψ_mark w else 0) : ℂ) *
          g (perm ((lowHighEquiv W M).symm (w, μ')))) =
        (normSq (ψ_mark w) : ℂ) * g (perm ((lowHighEquiv W M).symm (w, μ))) := by
    rw [sum_eq_single μ (fun μ' hμ' ↦ by
      rw [ite_eq_right hμ', Complex.normSq_zero, Complex.ofReal_zero, zero_mul])]
    rw [ite_eq_left rfl]
  simp_rw [hrow]
  let bij : Fin (2 ^ W) ≃ Fin (2 ^ (m * n)) × ((addrReg n m).Environment → ZMod 2) :=
    (parallelMarkPerm n m R).symm.trans (addrReg n m).basisSplitEquiv
  rw [← bij.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [sum_eq_single 0 (fun e he ↦ by
    have hb : (addrReg n m).basisSplitEquiv ((parallelMarkPerm n m R).symm (bij.symm (u, e))) =
        (u, e) := bij.apply_symm_apply (u, e)
    rw [hψ_mark, hb, ite_eq_right he, Complex.normSq_zero, Complex.ofReal_zero, zero_mul])]
  have hbij0 : bij.symm (u, 0) = w_of u := by
    dsimp only [bij, w_of]
    simp
  have hb0 : (addrReg n m).basisSplitEquiv ((parallelMarkPerm n m R).symm (w_of u)) = (u, 0) := by
    rw [← hbij0]
    exact bij.apply_symm_apply (u, 0)
  rw [hbij0, hψ_mark, hb0, ite_eq_left rfl]
  congr 2
  apply (lowHighEquiv W M).injective
  dsimp only [W, M, perm, memWriteBatchPerm, μ_of]
  rw [lowHighEquiv_memAddPerm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private lemma markAndWrite_outcome_props {n m k : ℕ} {S : Finset (Fin (2 ^ n))}
    (s : Fin k) {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s.val μ)
    (u : Fin (2 ^ (m * n))) :
    let R := S \ memSeen n k (memPrefix k s.val) μ
    let hits := fun w : Fin (2 ^ (m * (n + 1))) ↦ (firstMarkedAddr n m w).toList
    let w_u := parallelMarkPerm n m R ((addrReg n m).basisSplitEquiv.symm (u, 0))
    let μ_u := (addrEquiv n k).symm (addrEquiv n k μ + batchDelta s.val hits w_u)
    (firstMarkedAddr n m w_u = firstTupleHit n m R u) ∧
      (u ∈ oddSet n m R →
        (firstMarkedAddr n m w_u).isSome = true ∧ MemPrefixValid S (s.val + 1) μ_u) ∧
      (u ∉ oddSet n m R →
        (firstMarkedAddr n m w_u).isSome = false ∧ μ_u = μ) := by
  intro R hits w_u μ_u
  set z₀ := (addrReg n m).basisSplitEquiv.symm (u, 0)
  have hz0_fst : (addrReg n m).extractIndex z₀ = u := by
    simp [← QRegister.basisSplitEquiv_apply_fst, z₀]
  have hz0_snd : ((addrReg n m).basisSplitEquiv z₀).2 = 0 := by simp [z₀]
  have hfma : firstMarkedAddr n m w_u = firstTupleHit n m R u := by
    simpa [w_u, hz0_fst] using firstMarkedAddr_parallelMarkPerm_eq_firstTupleHit R z₀ hz0_snd
  refine ⟨hfma, fun hu ↦ ?_, fun hu ↦ ?_⟩
  · have his : (firstTupleHit n m R u).isSome = true := (isSome_firstTupleHit_iff R u).mpr hu
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp his
    have hxR : x ∈ R := (mem_of_firstTupleHit_eq_some hx).2
    have hhits : hits w_u = [x] := by simp [hits, hfma, hx]
    have hadv := memPrefixValid_batchAdvance hval hits w_u
      (by rw [hhits]; exact List.nodup_singleton x)
      (by rw [hhits, List.length_singleton]; exact s.isLt)
      (by rw [hhits]; intro y hy; rw [List.mem_singleton.mp hy]; exact hxR)
    rw [hhits, List.length_singleton] at hadv
    exact ⟨by rw [hfma, his], hadv⟩
  · have hnone : firstTupleHit n m R u = none :=
      Option.not_isSome_iff_eq_none.mp (mt (isSome_firstTupleHit_iff R u).mp hu)
    have hhits : hits w_u = [] := by simp [hits, hfma, hnone]
    have hδ : batchDelta (k := k) s.val hits w_u = 0 := by
      funext j
      simp [batchDelta, hhits]
    exact ⟨by simp [hfma, hnone], by
      dsimp only [μ_u]
      rw [hδ, add_zero, Equiv.symm_apply_apply]⟩

/-! ## Hadamard Preparation on `addrReg` -/

private lemma hadamard_mulVec_zero (q : ℕ) (M : Finset (Fin (2 ^ q))) :
    hadamardMatrix q *ᵥ (Pi.single 0 1 : Fin (2 ^ q) → ℂ) = subsetGroverState M 0 := by
  funext u
  rw [mulVec_single_one, col_apply, hadamardMatrix_apply_zero]
  simp [subsetGroverState]

private lemma embed_addrReg_mulVec_zero {n m : ℕ} (A : Operator (2 ^ (m * n)))
    (v : Fin (2 ^ (m * n)) → ℂ) :
    (addrReg n m).embedMatrix A *ᵥ (addrReg n m).tensorState v (Pi.single 0 1) =
      (addrReg n m).tensorState (A *ᵥ v) (Pi.single 0 1) :=
  (addrReg n m).embedMatrix_mulVec_tensorState A v (Pi.single 0 1)

private lemma tensorState_zero_zero (n m : ℕ) :
    (addrReg n m).tensorState (Pi.single 0 1) (Pi.single 0 1) =
      (Pi.single 0 1 : Fin (2 ^ (m * (n + 1))) → ℂ) := by
  funext z
  dsimp only [QRegister.tensorState]
  rw [← QRegister.basisSplitEquiv_apply_fst]
  have hz0 : (addrReg n m).basisSplitEquiv 0 = (0, 0) := by
    apply Prod.ext
    · apply (basisBits (m * n)).injective
      funext i
      simp
    · funext e
      simp
  by_cases hz : z = 0
  · subst hz
    rw [hz0, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne hz]
    have hne : (addrReg n m).basisSplitEquiv z ≠ (0, 0) :=
      fun h ↦ hz ((addrReg n m).basisSplitEquiv.injective (h.trans hz0.symm))
    by_cases h1 : ((addrReg n m).basisSplitEquiv z).1 = 0
    · have h2 : ((addrReg n m).basisSplitEquiv z).2 ≠ 0 := fun h2 ↦ hne (Prod.ext h1 h2)
      rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]

/-! ## Naive Single-Query Bernoulli Stage (`n < 200`, `k < 2 ^ n`) -/

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

lemma wp_naiveStage_ge {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm : 1 ≤ m) (hk_lt : k < 2 ^ n)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k) :
    validObs (Var := Var) n m k S s.val ≤
      wp ((naiveStage res n m k hm s).compile qAssign (groverParallelMarkingOracle m S))
        (validObs n m k S (s.val + 1)) := by
  let W := m * (n + 1)
  let M := k * n
  let oracle := groverParallelMarkingOracle m S
  let guard : Store Var → Prop := fun σ ↦ σ res = 0
  let bodyP := (naiveBody (Var := Var) res n m k hm s).compile qAssign oracle
  let post := validObs (Var := Var) n m k S (s.val + 1)
  set r := k - s.val
  have hr1 : 1 ≤ r := by omega
  have hr_lt : r < 2 ^ n := by omega
  set p := oddFrac n m r
  have hp_bounds := oddFrac_pos_lt_one (n := n) hm hr1 hr_lt
  set q := 1 - p
  have hq0 : 0 ≤ q := by linarith [hp_bounds.2]
  have hq1 : q < 1 := by linarith [hp_bounds.1]
  have hunroll (t : ℕ) :
      ∃ d_t : Fin (2 ^ (W + M)) → ℝ,
        (∀ z, 0 ≤ d_t z ∧ d_t z ≤ 1) ∧
        (∀ z, (1 - q ^ t) * validInd n m k S s.val z ≤ d_t z) ∧
        ∀ τ, (whileRecWP (wp bodyP) guard (t + 1) post τ).1.1 =
          if τ res = 0 then diagonal (fun z ↦ (d_t z : ℂ))
          else diagonal (fun z ↦ (validInd n m k S (s.val + 1) z : ℂ)) := by
    induction t with
    | zero =>
      refine ⟨fun _ ↦ 0, fun _ ↦ ⟨le_rfl, zero_le_one⟩, fun z ↦ by simp, fun τ ↦ ?_⟩
      rw [qhlWhileSucc_val]
      by_cases hτ : τ res = 0
      · rw [ite_eq_left hτ, ite_eq_left hτ]
        have hbot : whileRecWP (wp bodyP) guard 0 post = ⊥ := rfl
        have hwp0 : wp bodyP ⊥ = ⊥ := by
          dsimp only [bodyP, naiveBody, workReset, markAndWrite, deflatedOracle, compile]
          simp [wp_qSeq, wp_qAssign, wp_mapAndMeasureLow_bot]
        rw [hbot, hwp0]
        ext i j
        simp [Matrix.diagonal_apply]
      · rw [ite_eq_right hτ, ite_eq_right hτ]
        dsimp only [post, validObs]
        rw [realDiagObs_mat]
    | succ t ih =>
      rcases ih with ⟨d_t, hd_bounds, hd_ge, hd_mat⟩
      let H_prev (val : ℤ) : Operator (2 ^ (W + M)) :=
        if val = 0 then diagonal (fun z ↦ (d_t z : ℂ))
        else diagonal (fun z ↦ (validInd n m k S (s.val + 1) z : ℂ))
      let g_chk (z : Fin (2 ^ (W + M))) : ℝ :=
        let z' := naiveOutFn n m k hm z
        if ((lowHighEquiv W M z').1).val = 0 then d_t z'
        else validInd n m k S (s.val + 1) z'
      have hchk (τ' : Store Var) :
          ((wp ((mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k hm)).compile
              qAssign oracle) (whileRecWP (wp bodyP) guard (t + 1) post)) τ').1.1 =
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
      let innerP :=
        (OracleDynamicCircuit.seq
          (.step (phaseTag ((lowBlock W M).embedUnitary
            ((addrReg n m).embedUnitary hadamardUnitary))))
          (.seq (markAndWrite n m k s)
            (mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k hm)))).compile
          qAssign oracle
      let M_inner : Operator (2 ^ (W + M)) :=
        ((wp innerP (whileRecWP (wp bodyP) guard (t + 1) post)) (fun _ ↦ 0)).1.1
      have hinner_const (τ' : Store Var) :
          ((wp innerP (whileRecWP (wp bodyP) guard (t + 1) post)) τ').1.1 = M_inner := by
        dsimp only [innerP, M_inner, compile]
        rw [wp_qSeq, wp_qSeq]
        have hmeas_eq :
            wp ((mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k hm)).compile
                qAssign oracle) (whileRecWP (wp bodyP) guard (t + 1) post) τ' =
              wp ((mapAndMeasureLow res W M ((n + 1) * m) (naiveOutFn n m k hm)).compile
                qAssign oracle) (whileRecWP (wp bodyP) guard (t + 1) post) (fun _ ↦ 0) :=
          Subtype.ext (HermitianMat.ext ((hchk τ').trans (hchk (fun _ ↦ 0)).symm))
        have hmw_eq := wp_eq_of_pureUnitary
          (P := (markAndWrite (Var := Var) n m k s).compile qAssign oracle)
          ⟨⟨trivial, trivial⟩, trivial⟩ hmeas_eq
        have hH_eq := wp_eq_of_pureUnitary
          (P := (.step (phaseTag ((lowBlock W M).embedUnitary
            ((addrReg n m).embedUnitary hadamardUnitary))) :
              OracleCirc Var (W + M) ((n + 1) * m)).compile qAssign oracle)
          trivial hmw_eq
        exact congrArg (fun O : Observable _ ↦ O.1.1) hH_eq
      let d_next (z : Fin (2 ^ (W + M))) : ℝ :=
        (M_inner (resetWorkFn W M z) (resetWorkFn W M z)).re
      have hbody_diag (τ' : Store Var) :
          ((wp bodyP (whileRecWP (wp bodyP) guard (t + 1) post)) τ').1.1 =
            diagonal (fun z ↦ M_inner (resetWorkFn W M z) (resetWorkFn W M z)) := by
        change ((wp ((OracleDynamicCircuit.seq (workReset res W M ((n + 1) * m)) _).compile
          qAssign oracle) _) τ').1.1 = _
        dsimp only [compile]
        rw [wp_qSeq]
        exact wp_mapAndMeasureLow res (resetWorkFn W M) oracle (fun _ ↦ M_inner) _
          hinner_const τ'
      have hdiag_real (z : Fin (2 ^ (W + M))) :
          M_inner (resetWorkFn W M z) (resetWorkFn W M z) = (d_next z : ℂ) ∧
            0 ≤ d_next z ∧ d_next z ≤ 1 :=
        observable_diag_real_bounds
          (wp bodyP (whileRecWP (wp bodyP) guard (t + 1) post) (fun _ ↦ 0))
          (fun y ↦ M_inner (resetWorkFn W M y) (resetWorkFn W M y))
          (hbody_diag (fun _ ↦ 0)) z
      refine ⟨d_next, fun z ↦ ⟨(hdiag_real z).2.1, (hdiag_real z).2.2⟩, fun z ↦ ?_, fun τ ↦ ?_⟩
      · open Classical in
        by_cases hval : MemPrefixValid S s.val (lowHighEquiv W M z).2
        · set μ := (lowHighEquiv W M z).2
          have hvalid_z : validInd n m k S s.val z = 1 := by
            unfold validInd
            exact ite_eq_left hval
          rw [hvalid_z, mul_one]
          have hreset_eq : resetWorkFn W M z = (lowHighEquiv W M).symm (0, μ) := rfl
          have hval_eval : M_inner (resetWorkFn W M z) (resetWorkFn W M z) =
              ((p + (1 - p) * d_t ((lowHighEquiv W M).symm (0, μ)) : ℝ) : ℂ) := by
            rw [hreset_eq, vecQuad_single M_inner, ← workMemState_single]
            dsimp only [M_inner, innerP, compile]
            rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
              QRegister.embedUnitary_val, QRegister.embedUnitary_val,
              embedMatrix_lowBlock_mulVec_workMemState, ← tensorState_zero_zero n m,
              embed_addrReg_mulVec_zero, hadamardUnitary_coe,
              hadamard_mulVec_zero (m * n)
                (oddSet n m (S \ memSeen n k (memPrefix k s.val) μ)),
              wp_qSeq,
              vecQuad_markAndWrite s _ μ hval (fun y ↦ (g_chk y : ℂ)) _ _ (hchk _)]
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
            have hterm (u : Fin (2 ^ (m * n))) :
                (normSq (subsetGroverState (oddSet n m R) 0 u) : ℂ) *
                  (g_chk ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) : ℂ) =
                  ((1 / (2 ^ (m * n) : ℝ) *
                    if u ∈ oddSet n m R then 1
                    else d_t ((lowHighEquiv W M).symm (0, μ)) : ℝ) : ℂ) := by
              have hprops := markAndWrite_outcome_props s hval u
              have hnsq : normSq (subsetGroverState (oddSet n m R) 0 u) =
                  1 / (2 ^ (m * n) : ℝ) := by
                dsimp only [subsetGroverState]
                rw [Complex.normSq_ofReal, div_mul_div_comm, one_mul,
                  Real.mul_self_sqrt (by positivity)]
              rw [hnsq]
              by_cases hu : u ∈ oddSet n m R
              · rcases hprops.2.1 hu with ⟨his, hadv⟩
                have hout : naiveOutFn n m k hm
                    ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) =
                    (lowHighEquiv (m * (n + 1)) (k * n)).symm
                      (⟨1, Nat.one_lt_two_pow (by nlinarith)⟩, μ_of u) := by
                  unfold naiveOutFn
                  dsimp only [R, w_of, μ_of] at his ⊢
                  rw [Equiv.apply_symm_apply, ite_eq_left his]
                have hg1 : g_chk ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) =
                    1 := by
                  dsimp only [W, M, R, g_chk, w_of, μ_of] at hout hadv ⊢
                  rw [hout, Equiv.apply_symm_apply, ite_eq_right (by norm_num)]
                  unfold validInd
                  rw [Equiv.apply_symm_apply, ite_eq_left hadv]
                rw [hg1, ite_eq_left hu]
                push_cast
                ring
              · rcases hprops.2.2 hu with ⟨his, hμ_eq⟩
                have hout : naiveOutFn n m k hm
                    ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) =
                    (lowHighEquiv (m * (n + 1)) (k * n)).symm (0, μ) := by
                  unfold naiveOutFn
                  dsimp only [R, w_of, μ_of] at his hμ_eq ⊢
                  have hnot : ¬ (firstMarkedAddr n m
                      (parallelMarkPerm n m (S \ memSeen n k (memPrefix k s.val) μ)
                        ((addrReg n m).basisSplitEquiv.symm (u, 0)))).isSome = true := by
                    rw [his]; simp
                  rw [Equiv.apply_symm_apply, ite_eq_right hnot, hμ_eq]
                have hg0 : g_chk ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) =
                    d_t ((lowHighEquiv W M).symm (0, μ)) := by
                  dsimp only [W, M, R, g_chk, w_of, μ_of] at hout ⊢
                  rw [hout, Equiv.apply_symm_apply, Fin.val_zero, ite_eq_left rfl]
                rw [hg0, ite_eq_right hu]
                push_cast
                ring
            rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← ofReal_sum]
            congr 1
            have hite (u : Fin (2 ^ (m * n))) :
                1 / (2 ^ (m * n) : ℝ) *
                  (if u ∈ oddSet n m R then (1 : ℝ)
                    else d_t ((lowHighEquiv W M).symm (0, μ))) =
                (1 / (2 ^ (m * n) : ℝ)) * d_t ((lowHighEquiv W M).symm (0, μ)) +
                  if u ∈ oddSet n m R then
                    (1 / (2 ^ (m * n) : ℝ)) * (1 - d_t ((lowHighEquiv W M).symm (0, μ)))
                  else 0 := by
              by_cases hu : u ∈ oddSet n m R
              · rw [ite_eq_left hu, ite_eq_left hu]; ring
              · rw [ite_eq_right hu, ite_eq_right hu]; ring
            simp_rw [hite, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
              nsmul_eq_mul]
            push_cast
            have hD_ne : (2 ^ (m * n) : ℝ) ≠ 0 := by positivity
            have hp_mul : ((oddSet n m R).card : ℝ) * (1 / (2 ^ (m * n) : ℝ)) = p := by
              rw [mul_one_div, hp_R]
            calc (2 : ℝ) ^ (m * n) * (1 / 2 ^ (m * n) * d_t ((lowHighEquiv W M).symm (0, μ))) +
                  ((oddSet n m R).card : ℝ) *
                    (1 / 2 ^ (m * n) * (1 - d_t ((lowHighEquiv W M).symm (0, μ))))
                = (2 ^ (m * n) * (1 / 2 ^ (m * n))) * d_t ((lowHighEquiv W M).symm (0, μ)) +
                    (((oddSet n m R).card : ℝ) * (1 / (2 ^ (m * n) : ℝ))) *
                      (1 - d_t ((lowHighEquiv W M).symm (0, μ))) := by ring
              _ = p + (1 - p) * d_t ((lowHighEquiv W M).symm (0, μ)) := by
                    rw [mul_one_div_cancel hD_ne, hp_mul]
                    ring
          have hd_eq : d_next z = p + (1 - p) * d_t ((lowHighEquiv W M).symm (0, μ)) := by
            have h1 := (hdiag_real z).1.symm.trans hval_eval
            exact Complex.ofReal_injective h1
          have hd_ih := hd_ge ((lowHighEquiv W M).symm (0, μ))
          have hv0 : validInd n m k S s.val ((lowHighEquiv W M).symm (0, μ)) = 1 := by
            unfold validInd
            rw [Equiv.apply_symm_apply, ite_eq_left hval]
          rw [hv0, mul_one] at hd_ih
          rw [hd_eq, pow_succ]
          have h1p : 0 ≤ 1 - p := hq0
          have hstep : p + (1 - p) * (1 - q ^ t) = 1 - q ^ t * q := by
            dsimp only [q]
            ring
          nlinarith [mul_le_mul_of_nonneg_left hd_ih h1p]
        · have hv0 : validInd n m k S s.val z = 0 := by
            unfold validInd
            exact ite_eq_right hval
          rw [hv0, mul_zero]
          exact (hdiag_real z).2.1
      · rw [qhlWhileSucc_val]
        by_cases hτ : τ res = 0
        · rw [ite_eq_left hτ, ite_eq_left hτ, hbody_diag]
          exact congrArg diagonal (funext fun z ↦ (hdiag_real z).1)
        · rw [ite_eq_right hτ, ite_eq_right hτ]
          dsimp only [post, validObs]
          rw [realDiagObs_mat]
  intro σ
  have hgeom : ∀ t : ℕ,
      (validObs (Var := Var) n m k S s.val σ).1 -
          q ^ t • (validObs (Var := Var) n m k S s.val σ).1 ≤
        (wp ((naiveStage res n m k hm s).compile qAssign oracle) post σ).1 := by
    intro t
    rcases hunroll t with ⟨d_t, hd_bounds, hd_ge, hd_mat⟩
    have hsub_eq :
        (validObs (Var := Var) n m k S s.val σ).1 -
            q ^ t • (validObs (Var := Var) n m k S s.val σ).1 =
          (scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t)
            (sub_nonneg.mpr (pow_le_one₀ hq0 hq1.le))
            (sub_le_self 1 (pow_nonneg hq0 t)) σ).1 := by
      rw [scaledValidObs_smul, sub_smul, one_smul]
    rw [hsub_eq]
    have hle_unroll :
        scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t)
          (sub_nonneg.mpr (pow_le_one₀ hq0 hq1.le))
          (sub_le_self 1 (pow_nonneg hq0 t)) σ ≤
        wp ((workReset res W M ((n + 1) * m)).compile qAssign oracle)
          (whileRecWP (wp bodyP) guard (t + 1) post) σ := by
      have hw := wp_mapAndMeasureLow res (resetWorkFn W M) oracle
        (fun val ↦ if val = 0 then diagonal (fun z ↦ (d_t z : ℂ))
          else diagonal (fun z ↦ (validInd n m k S (s.val + 1) z : ℂ)))
        (whileRecWP (wp bodyP) guard (t + 1) post) hd_mat σ
      have hw' : ((wp ((workReset res W M ((n + 1) * m)).compile qAssign oracle)
          (whileRecWP (wp bodyP) guard (t + 1) post)) σ).1.1 =
          diagonal (fun z ↦ (d_t (resetWorkFn W M z) : ℂ)) := by
        rw [workReset, hw]
        refine congrArg diagonal (funext fun z ↦ ?_)
        have h0 : Int.ofNat ((lowHighEquiv W M (resetWorkFn W M z)).1).val = 0 := by
          simp [resetWorkFn]
        rw [ite_eq_left h0, Matrix.diagonal_apply_eq]
      refine realDiagObs_le_of_mat (fun z ↦ (hd_bounds _).1) (fun z ↦ (hd_bounds _).2) hw'
        fun z ↦ ?_
      have hsnd : (lowHighEquiv (m * (n + 1)) (k * n) (resetWorkFn W M z)).2 =
          (lowHighEquiv (m * (n + 1)) (k * n) z).2 := by
        dsimp only [W, M, resetWorkFn]
        rw [Equiv.apply_symm_apply]
      have hv_eq : validInd n m k S s.val (resetWorkFn W M z) = validInd n m k S s.val z := by
        open Classical in
        by_cases hv : MemPrefixValid S s.val (lowHighEquiv (m * (n + 1)) (k * n) z).2
        · have hv' : MemPrefixValid S s.val
              (lowHighEquiv (m * (n + 1)) (k * n) (resetWorkFn W M z)).2 := hsnd.symm ▸ hv
          unfold validInd
          rw [ite_eq_left hv', ite_eq_left hv]
        · have hv' : ¬ MemPrefixValid S s.val
              (lowHighEquiv (m * (n + 1)) (k * n) (resetWorkFn W M z)).2 := hsnd.symm ▸ hv
          unfold validInd
          rw [ite_eq_right hv', ite_eq_right hv]
      rw [← hv_eq]
      exact hd_ge (resetWorkFn W M z)
    have hmon := wp_mono ((workReset res W M ((n + 1) * m)).compile qAssign oracle)
      (whileRecWP_le_wp_qWhile guard bodyP (t + 1) post) σ
    exact Subtype.coe_le_coe.mpr (hle_unroll.trans hmon)
  exact Subtype.coe_le_coe.mp
    (hermitian_le_of_geometric_sub_smul_le q hq0 hq1 _ _ _ hgeom)

/-! ## Stationary Eigenvector-Locking Stage (`200 ≤ n`, `k < 2 ^ n`) -/

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

private lemma costBound_groverSubIter {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (active : Finset (Fin k)) (S : Finset (Fin (2 ^ n))) (t : ℕ) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((groverSubIter n m k active t).compile qAssign (groverParallelMarkingOracle m S))
      (t : ℝ≥0) := by
  induction t with
  | zero =>
    simpa [groverSubIter, compile] using
      CostBound.skip_zero (Var := Var) (d := 2 ^ (m * (n + 1) + k * n))
        (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
  | succ t ih =>
    unfold groverSubIter
    dsimp only [compile]
    have hor := isRealMatrix_groverParallelMarkingOracle m S
    have hstep := (costBound_deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
      (Q := m * (n + 1) + k * n) le_rfl active S).seq
      (costBound_qAssign_phaseTag (Var := Var) hor
        ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
          ((addrReg n m).embedUnitary Grover.diffuserUnitary)))
    simpa [Nat.cast_add, Nat.cast_one] using ih.seq hstep

private lemma costBound_eigSetup {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ)
    (s : Fin k) (K : ℕ) (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((eigSetup res n m k s K).compile qAssign (groverParallelMarkingOracle m S))
      ((K + 1 : ℕ) : ℝ≥0) := by
  unfold eigSetup workReset
  dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have h0 := costBound_mapAndMeasureLow (Var := Var) res (resetWorkFn (m * (n + 1)) (k * n)) hor
  have hH := costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary ((addrReg n m).embedUnitary hadamardUnitary))
  have hK := costBound_groverSubIter (Var := Var) n m k (memPrefix k s.val) S K
  have hph := costBound_deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
    (Q := m * (n + 1) + k * n) le_rfl (memPrefix k s.val) S
  simpa [Nat.cast_add, Nat.cast_one] using h0.seq (hH.seq (hK.seq hph))

private lemma costBound_eigBody {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ)
    (hm : 1 ≤ m) (s : Fin k) (cRatio : ℝ) (hc0 : 0 ≤ cRatio) (hc1 : cRatio ≤ 1)
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((eigBody res n m k hm s cRatio hc0 hc1).compile qAssign (groverParallelMarkingOracle m S))
      1 := by
  unfold eigBody
  dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  have hd := costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
      ((addrReg n m).embedUnitary Grover.diffuserUnitary))
  have hc := costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (chordUnitary n m hm cRatio hc0 hc1))
  have hp := costBound_deflatedPhaseStep (Var := Var) (n := n) (m := m) (k := k)
    (Q := m * (n + 1) + k * n) le_rfl (memPrefix k s.val) S
  have hm_cost : CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      (measureRegister res ((lowBlock (m * (n + 1)) (k * n)).compose (flag0Reg n m hm))) 0 := by
    simpa [measureRegister, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var)
        (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) res _
  simpa using hd.seq (hc.seq (hp.seq (hc.seq hm_cost)))

private lemma costBound_eigReadout {Var : Type} [DecidableEq Var] (n m k : ℕ) (s : Fin k)
    (S : Finset (Fin (2 ^ n))) :
    CostBound (Var := Var)
      (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((eigReadout n m k s).compile qAssign (groverParallelMarkingOracle m S)) 1 := by
  unfold eigReadout
  dsimp only [compile]
  have hor := isRealMatrix_groverParallelMarkingOracle m S
  simpa using (costBound_qAssign_phaseTag (Var := Var) hor
    ((lowBlock (m * (n + 1)) (k * n)).embedUnitary (permutationUnitary (flipPerm n m)))).seq
    (costBound_markAndWrite (Var := Var) n m k s S)

private lemma vecQuad_groverSubIter {Var : Type} [DecidableEq Var] {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (s : Fin k) (μ : Fin (2 ^ (k * n)))
    (hval : MemPrefixValid S s.val μ) (t : ℕ)
    (Θ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (σ : Store Var) :
    let R := S \ memSeen n k (memPrefix k s.val) μ
    vecQuad
      (((wp ((OracleDynamicCircuit.seq
          (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
            ((addrReg n m).embedUnitary hadamardUnitary))))
          (groverSubIter n m k (memPrefix k s.val) t)).compile qAssign
          (groverParallelMarkingOracle m S)) Θ) σ).1.1)
      (workMemState (Pi.single 0 1) (Pi.single μ 1)) =
    vecQuad ((Θ σ).1.1)
      (workMemState
        ((addrReg n m).tensorState (subsetGroverState (oddSet n m R) t) (Pi.single 0 1))
        (Pi.single μ 1)) := by
  intro R
  have hsub : memSeen n k (memPrefix k s.val) μ ⊆ S :=
    (card_memSeen_of_memPrefixValid hval).2
  induction t generalizing Θ with
  | zero =>
    dsimp only [groverSubIter, compile]
    rw [wp_qSeq, wp_skip, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      embedMatrix_lowBlock_mulVec_workMemState, ← tensorState_zero_zero n m,
      embed_addrReg_mulVec_zero, hadamardUnitary_coe,
      hadamard_mulVec_zero (m * n) (oddSet n m R)]
  | succ t ih =>
    have hassoc :
        wp ((OracleDynamicCircuit.seq
            (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
              ((addrReg n m).embedUnitary hadamardUnitary))))
            (groverSubIter n m k (memPrefix k s.val) (t + 1))).compile qAssign
            (groverParallelMarkingOracle m S)) Θ =
        wp ((OracleDynamicCircuit.seq
            (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
              ((addrReg n m).embedUnitary hadamardUnitary))))
            (groverSubIter n m k (memPrefix k s.val) t)).compile qAssign
            (groverParallelMarkingOracle m S))
          (wp ((OracleDynamicCircuit.seq
            (deflatedPhaseStep le_rfl (memPrefix k s.val))
            (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
              ((addrReg n m).embedUnitary Grover.diffuserUnitary))))).compile qAssign
            (groverParallelMarkingOracle m S)) Θ) := by
      simp [groverSubIter, compile, wp_qSeq]
    rw [hassoc, ih]
    dsimp only [compile]
    rw [wp_qSeq, wp_deflatedPhaseStep_vecQuad (memPrefix k s.val) _ μ hsub,
      sDiagM_mulVec_tensorState_zero, wp_qAssign, wp_phaseTag, qhlQAssign_val,
      vecQuad_conj, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      embedMatrix_lowBlock_mulVec_workMemState, embed_addrReg_mulVec_zero]
    rfl

private lemma flag0FullReg_projector_mulVec_workMemState {n m k : ℕ} (hm : 1 ≤ m)
    (o : Fin (2 ^ 1)) (ψ : Fin (2 ^ (m * (n + 1))) → ℂ) (φ : Fin (2 ^ (k * n)) → ℂ) :
    ((lowBlock (m * (n + 1)) (k * n)).compose (flag0Reg n m hm)).basisOutcomeProjector o *ᵥ
        workMemState ψ φ =
      workMemState ((flag0Reg n m hm).basisOutcomeProjector o *ᵥ ψ) φ := by
  funext z
  rw [QRegister.basisOutcomeProjector_eq_diagonal, mulVec_diagonal]
  dsimp only [workMemState]
  rw [QRegister.extractIndex_compose, extractIndex_lowBlock,
    QRegister.basisOutcomeProjector_eq_diagonal, mulVec_diagonal]
  ring

private lemma sum_normSq_workMemState_tensor_zero {n m k : ℕ}
    (v : Fin (2 ^ (m * n)) → ℂ) (μ : Fin (2 ^ (k * n))) :
    (∑ z : Fin (2 ^ (m * (n + 1) + k * n)),
      normSq (workMemState ((addrReg n m).tensorState v (Pi.single 0 1)) (Pi.single μ 1) z)) =
      ∑ u : Fin (2 ^ (m * n)), normSq (v u) := by
  let W := m * (n + 1)
  let M := k * n
  let f (z : Fin (2 ^ (W + M))) :=
    normSq (workMemState ((addrReg n m).tensorState v (Pi.single 0 1)) (Pi.single μ 1) z)
  change ∑ z, f z = _
  rw [← (lowHighEquiv W M).symm.sum_comp f, Fintype.sum_prod_type]
  have h1 (w : Fin (2 ^ W)) :
      (∑ μ' : Fin (2 ^ M), f ((lowHighEquiv W M).symm (w, μ'))) =
        normSq ((addrReg n m).tensorState v (Pi.single 0 1) w) := by
    rw [sum_eq_single μ (fun μ' hμ' ↦ by
      dsimp only [f, workMemState]
      rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne hμ', mul_zero, Complex.normSq_zero])]
    dsimp only [f, workMemState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  simp_rw [h1]
  rw [← (addrReg n m).basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [sum_eq_single 0 (fun e he ↦ by
    dsimp only [Function.comp_apply, QRegister.tensorState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne he, mul_zero, Complex.normSq_zero])]
  dsimp only [Function.comp_apply, QRegister.tensorState]
  rw [ ← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply,
    Pi.single_eq_same, mul_one]

private lemma vecQuad_eigBody_step {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn : 200 ≤ n)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k)
    {μ : Fin (2 ^ (k * n))} (hval : MemPrefixValid S s.val μ)
    (Ψ : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n))) (τ : Store Var) :
    let r := k - s.val
    let p := oddFrac n m r
    let K := subSchedule p
    let hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    let hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
    let R := S \ memSeen n k (memPrefix k s.val) μ
    let M_odd := oddSet n m R
    let cRatio := subTargetRatio p K
    let φ_K := oracleMat M_odd *ᵥ subsetGroverState M_odd K
    let v₁ := subsetKraus1 M_odd cRatio *ᵥ subsetGroverState M_odd (K + 1)
    let ψ_init := workMemState ((addrReg n m).tensorState φ_K (Pi.single 0 1)) (Pi.single μ 1)
    let ψ_exit := workMemState ((addrReg n m).tensorState v₁ (Pi.single 1 1)) (Pi.single μ 1)
    vecQuad
      (((wp ((eigBody res n m k hm1 s cRatio hhyps.1.le hhyps.2.1.le).compile qAssign
          (groverParallelMarkingOracle m S)) Ψ) τ).1.1) ψ_init =
      (subFailProb p K : ℂ) * vecQuad ((Ψ (Store.subst τ res 0)).1.1) ψ_init +
        vecQuad ((Ψ (Store.subst τ res 1)).1.1) ψ_exit := by
  intro r p K hm1 hhyps R M_odd cRatio φ_K v₁ ψ_init ψ_exit
  have hcm := card_memSeen_of_memPrefixValid hval
  have hR_card : R.card = r := by rw [Finset.card_sdiff_of_subset hcm.2, hcard, hcm.1]
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
    have h0' : M_odd.card = 0 := by omega
    have hp0 : p = 0 := by rw [← hp_eq, h0']; simp
    linarith [hp_pos_lt.1]
  have hMlt : M_odd.card < 2 ^ (m * n) := by
    by_contra! hge
    have hp1 : 1 ≤ p := by
      rw [← hp_eq]
      exact ( one_le_div (by positivity)).mpr (by exact_mod_cast hge)
    linarith [hp_pos_lt.2]
  have hsin3 : sin ((2 * (K : ℝ) + 3) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
      0 := by
    rw [hp_eq]
    exact hhyps.2.2.1
  have hcos1 : cos ((2 * (K : ℝ) + 1) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
      0 := by
    rw [hp_eq]
    exact hhyps.2.2.2.1
  have hkraus0 : subsetKraus0 M_odd cRatio *ᵥ subsetGroverState M_odd (K + 1) =
      (subNonTargetRatio p K : ℂ) • φ_K := by
    have hk0 := subsetKraus0_mulVec_subsetGroverState M_odd hM0 hMlt K hsin3 hcos1
    dsimp only at hk0
    simpa only [hp_eq] using hk0
  unfold eigBody
  dsimp only [compile]
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
    chord_sDiagM_chord_mulVec_zero hm1 hhyps.1.le hhyps.2.1.le R
      (subsetGroverState M_odd (K + 1)),
    hkraus0, (addrReg n m).tensorState_smul_left, workMemState_add_left, workMemState_smul_left]
  set ψ_tot := (subNonTargetRatio p K : ℂ) • ψ_init + ψ_exit
  rw [wp_measureRegister]
  let reg0 := (lowBlock (m * (n + 1)) (k * n)).compose (flag0Reg n m hm1)
  have hsum2 :
      (∑ o : Fin (2 ^ 1),
        reg0.basisOutcomeProjector o * (Ψ (Store.subst τ res (Int.ofNat o.val))).1.1 *
          reg0.basisOutcomeProjector o) =
      reg0.basisOutcomeProjector 0 * (Ψ (Store.subst τ res 0)).1.1 * reg0.basisOutcomeProjector 0 +
        reg0.basisOutcomeProjector 1 * (Ψ (Store.subst τ res 1)).1.1 *
          reg0.basisOutcomeProjector 1 :=
    Fin.sum_univ_two fun o : Fin 2 ↦
      reg0.basisOutcomeProjector o * (Ψ (Store.subst τ res (Int.ofNat o.val))).1.1 *
        reg0.basisOutcomeProjector o
  rw [hsum2]
  have hadd_quad (A B : Operator (2 ^ (m * (n + 1) + k * n))) (ψ : Fin _ → ℂ) :
      vecQuad (A + B) ψ = vecQuad A ψ + vecQuad B ψ := by
    simp [vecQuad, Matrix.add_mulVec, dotProduct_add]
  rw [hadd_quad]
  have hp0_adj : (reg0.basisOutcomeProjector 0)ᴴ = reg0.basisOutcomeProjector 0 :=
    QRegister.basisOutcomeProjector_conjTranspose reg0 0
  have hp1_adj : (reg0.basisOutcomeProjector 1)ᴴ = reg0.basisOutcomeProjector 1 :=
    QRegister.basisOutcomeProjector_conjTranspose reg0 1
  nth_rw 1 [← hp0_adj]
  nth_rw 1 [← hp1_adj]
  rw [vecQuad_conj, vecQuad_conj]
  have hproj := flag0Reg_basisOutcomeProjector_mulVec hm1
    ((subNonTargetRatio p K : ℂ) • φ_K) v₁
  have hp0_vec : reg0.basisOutcomeProjector 0 *ᵥ ψ_tot = (subNonTargetRatio p K : ℂ) • ψ_init := by
    dsimp only [ψ_tot, ψ_init, ψ_exit, reg0]
    rw [← workMemState_smul_left, ← (addrReg n m).tensorState_smul_left,
      ← workMemState_add_left, flag0FullReg_projector_mulVec_workMemState, hproj.1,
      (addrReg n m).tensorState_smul_left, workMemState_smul_left]
  have hp1_vec : reg0.basisOutcomeProjector 1 *ᵥ ψ_tot = ψ_exit := by
    dsimp only [ψ_tot, ψ_init, ψ_exit, reg0]
    rw [← workMemState_smul_left, ← (addrReg n m).tensorState_smul_left,
      ← workMemState_add_left, flag0FullReg_projector_mulVec_workMemState, hproj.2]
  rw [hp0_vec, hp1_vec, vecQuad_smul]
  rfl

lemma eigLockStage_wp_and_active {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn : 200 ≤ n)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k) :
    let r := k - s.val
    let p := oddFrac n m r
    let K := subSchedule p
    let hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    let hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
    let oracle := groverParallelMarkingOracle m S
    let setupP := (eigSetup (Var := Var) res n m k s K).compile qAssign oracle
    let bodyP := (eigBody (Var := Var) res n m k hm1 s (subTargetRatio p K)
      hhyps.1.le hhyps.2.1.le).compile qAssign oracle
    let guard : Store Var → Prop := fun σ ↦ σ res = 0
    let q := subFailProb p K
    validObs (Var := Var) n m k S s.val ≤
      wp ((eigLockStage res n m k hm_grid hk_grid hn s).compile qAssign oracle)
        (validObs n m k S (s.val + 1)) ∧
    ∀ t : ℕ,
      wp setupP (whileActiveWP (wp bodyP) guard t) ≤
        (scaledValidObs n m k S s.val (q ^ t)
          (pow_nonneg (subFailProb_nonneg p K) t)
          (pow_le_one₀ (subFailProb_nonneg p K) hhyps.2.2.2.2.le)).add
          (invalidObs n m k S s.val)
          (scaledValid_add_invalid_le_one n m k S s.val (q ^ t) _ _) := by
  intro r p K hm1 hhyps oracle setupP bodyP guard q
  let W := m * (n + 1)
  let M := k * n
  let readoutP := (eigReadout (Var := Var) n m k s).compile qAssign oracle
  let post := validObs (Var := Var) n m k S (s.val + 1)
  let Θ_read := wp readoutP post
  have hΘ_const : ∃ M_read : Operator (2 ^ (W + M)), ∀ τ, (Θ_read τ).1.1 = M_read := by
    refine ⟨(Θ_read (fun _ ↦ 0)).1.1, fun τ ↦ ?_⟩
    have hread_eq := wp_eq_of_pureUnitary (P := readoutP) ⟨trivial, ⟨trivial, trivial⟩, trivial⟩
      (rfl : post τ = post (fun _ ↦ 0))
    exact congrArg (fun O : Observable _ ↦ O.1.1) hread_eq
  rcases hΘ_const with ⟨M_read, hM_read⟩
  have hbody_const (Ψ : CQAssertion (Store Var) (2 ^ (W + M)))
      (H : ℤ → Operator (2 ^ (W + M))) (hΨ : ∀ τ, (Ψ τ).1.1 = H (τ res)) :
      ∃ M_b : Operator (2 ^ (W + M)), ∀ τ, ((wp bodyP Ψ) τ).1.1 = M_b := by
    refine ⟨((wp bodyP Ψ) (fun _ ↦ 0)).1.1, fun τ ↦ ?_⟩
    let reg0 := (lowBlock (m * (n + 1)) (k * n)).compose (flag0Reg n m hm1)
    have hmeas (τ' : Store Var) :
        ((wp (measureRegister res reg0) Ψ) τ').1.1 =
          ∑ o : Fin (2 ^ 1),
            reg0.basisOutcomeProjector o * H (Int.ofNat o.val) * reg0.basisOutcomeProjector o := by
      rw [wp_measureRegister]
      exact Finset.sum_congr rfl fun o _ ↦ by rw [hΨ]; simp [Store.subst]
    have hmeas_obs : wp (measureRegister res reg0) Ψ τ =
        wp (measureRegister res reg0) Ψ (fun _ ↦ 0) :=
      Subtype.ext (HermitianMat.ext ((hmeas τ).trans (hmeas (fun _ ↦ 0)).symm))
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
    dsimp only [bodyP, eigBody, compile]
    rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qSeq]
    exact congrArg (fun O : Observable _ ↦ O.1.1) h4
  have hsetup_diag (Ψ : CQAssertion (Store Var) (2 ^ (W + M)))
      (M_0 M_1 : Operator (2 ^ (W + M)))
      (hΨ : ∀ τ, (Ψ τ).1.1 = if τ res = 0 then M_0 else M_1) :
      ∃ d_s : Fin (2 ^ (W + M)) → ℝ,
        (∀ z, 0 ≤ d_s z ∧ d_s z ≤ 1) ∧
        (∀ τ, ((wp setupP Ψ) τ).1.1 = diagonal (fun z ↦ (d_s z : ℂ))) ∧
        ∀ z, MemPrefixValid S s.val (lowHighEquiv W M z).2 →
          (d_s z : ℂ) =
            let μ := (lowHighEquiv W M z).2
            let R := S \ memSeen n k (memPrefix k s.val) μ
            let M_odd := oddSet n m R
            vecQuad M_0
              (workMemState
                ((addrReg n m).tensorState
                  (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
                (Pi.single μ 1)) := by
    let tailC : OracleCirc Var (m * (n + 1) + k * n) ((n + 1) * m) :=
      .seq (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
          ((addrReg n m).embedUnitary hadamardUnitary))))
        (.seq (groverSubIter n m k (memPrefix k s.val) K)
          (deflatedPhaseStep le_rfl (memPrefix k s.val)))
    let tailP := tailC.compile qAssign oracle
    have htail_pure : PureUnitaryProg tailP :=
      ⟨trivial, pureUnitary_groverSubIter n m k (memPrefix k s.val) oracle K,
        trivial, ⟨trivial, trivial⟩, trivial⟩
    let N_0 : Operator (2 ^ (W + M)) := ((wp tailP Ψ) (fun _ ↦ 0)).1.1
    let N_1 : Operator (2 ^ (W + M)) := ((wp tailP Ψ) (fun _ ↦ 1)).1.1
    have hN_dep (τ : Store Var) :
        ((wp tailP Ψ) τ).1.1 = if τ res = 0 then N_0 else N_1 := by
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
          let R := S \ memSeen n k (memPrefix k s.val) μ
          let M_odd := oddSet n m R
          vecQuad M_0
            (workMemState
              ((addrReg n m).tensorState
                (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
              (Pi.single μ 1)) := by
      rw [vecQuad_single N_0, ← workMemState_single]
      have hassoc :
          wp tailP Ψ =
            wp ((OracleDynamicCircuit.seq
              (.step (phaseTag ((lowBlock (m * (n + 1)) (k * n)).embedUnitary
                ((addrReg n m).embedUnitary hadamardUnitary))))
              (groverSubIter n m k (memPrefix k s.val) K)).compile qAssign oracle)
              (wp ((deflatedPhaseStep le_rfl (memPrefix k s.val)).compile qAssign oracle) Ψ) := by
        dsimp only [tailP, tailC, compile]
        rw [wp_qSeq, wp_qSeq, wp_qSeq]
      dsimp only [N_0]
      rw [hassoc, vecQuad_groverSubIter s μ hval K _ (fun _ ↦ 0),
        wp_deflatedPhaseStep_vecQuad (memPrefix k s.val) _ μ
          (card_memSeen_of_memPrefixValid hval).2,
        sDiagM_mulVec_tensorState_zero, hΨ (fun _ ↦ 0), ite_eq_left rfl]
    have hwp_s (τ : Store Var) :
        ((wp setupP Ψ) τ).1.1 =
          diagonal (fun z ↦ N_0 (resetWorkFn W M z) (resetWorkFn W M z)) := by
      have hseq : wp setupP Ψ =
          wp ((workReset res (m * (n + 1)) (k * n) ((n + 1) * m)).compile qAssign oracle)
            (wp tailP Ψ) := by
        dsimp only [setupP, eigSetup, tailP, tailC, compile]
        rw [wp_qSeq]
      rw [hseq, workReset,
        wp_mapAndMeasureLow res (resetWorkFn W M) oracle
          (fun val ↦ if val = 0 then N_0 else N_1) (wp tailP Ψ) hN_dep τ]
      refine congrArg diagonal (funext fun z ↦ ?_)
      have h0 : Int.ofNat ((lowHighEquiv W M (resetWorkFn W M z)).1).val = 0 := by
        simp [resetWorkFn]
      rw [ite_eq_left h0]
    let d_s (z : Fin (2 ^ (W + M))) : ℝ := (N_0 (resetWorkFn W M z) (resetWorkFn W M z)).re
    have hreal_bounds (z : Fin (2 ^ (W + M))) :
        N_0 (resetWorkFn W M z) (resetWorkFn W M z) = (d_s z : ℂ) ∧
          0 ≤ d_s z ∧ d_s z ≤ 1 :=
      observable_diag_real_bounds (wp setupP Ψ (fun _ ↦ 0))
        (fun y ↦ N_0 (resetWorkFn W M y) (resetWorkFn W M y)) (hwp_s (fun _ ↦ 0)) z
    refine ⟨d_s, fun z ↦ ⟨(hreal_bounds z).2.1, (hreal_bounds z).2.2⟩,
      fun τ ↦ (hwp_s τ).trans (congrArg diagonal (funext fun z ↦ (hreal_bounds z).1)),
      fun z hval ↦ ?_⟩
    rw [← (hreal_bounds z).1]
    exact hN_val (lowHighEquiv W M z).2 hval
  -- Active-mass survival induction on t
  have hact_mat (t : ℕ) :
      ∃ A_t : Operator (2 ^ (W + M)),
        (∀ τ, (whileActiveWP (wp bodyP) guard t τ).1.1 = if τ res = 0 then A_t else 0) ∧
        ∀ μ : Fin (2 ^ M), MemPrefixValid S s.val μ →
          let R := S \ memSeen n k (memPrefix k s.val) μ
          let M_odd := oddSet n m R
          vecQuad A_t
            (workMemState
              ((addrReg n m).tensorState
                (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
              (Pi.single μ 1)) = ((q ^ t : ℝ) : ℂ) := by
    induction t with
    | zero =>
      refine ⟨1, fun τ ↦ by by_cases h : τ res = 0 <;> simp [whileActiveWP, guard, h],
        fun μ hval ↦ ?_⟩
      intro R M_odd
      have h1 : (1 : Operator (2 ^ (W + M))) = diagonal (fun _ ↦ (1 : ℂ)) := by
        ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
      rw [h1, vecQuad_diagonal]
      simp_rw [mul_one]
      rw [← ofReal_sum]
      dsimp only [W, M]
      rw [sum_normSq_workMemState_tensor_zero]
      have hcm := card_memSeen_of_memPrefixValid hval
      have hR_card : R.card = r := by rw [Finset.card_sdiff_of_subset hcm.2, hcard, hcm.1]
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
        have hp0 : p = 0 := by rw [← hp_eq, show M_odd.card = 0 by omega]; simp
        linarith [hp_pos_lt.1]
      have hMlt : M_odd.card < 2 ^ (m * n) := by
        by_contra! hge
        have hp1 : 1 ≤ p := by
          rw [← hp_eq]
          exact (one_le_div (by positivity)).mpr (by exact_mod_cast hge)
        linarith [hp_pos_lt.2]
      rw [(sum_normSq_subsetGroverState M_odd hM0 hMlt K).2, pow_zero]
    | succ t ih =>
      rcases ih with ⟨A_t, hA_dep, hA_val⟩
      rcases hbody_const (whileActiveWP (wp bodyP) guard t)
        (fun val ↦ if val = 0 then A_t else 0) hA_dep with ⟨M_b, hM_b⟩
      refine ⟨M_b, fun τ ↦ ?_, fun μ hval ↦ ?_⟩
      · dsimp only [whileActiveWP]
        by_cases hτ : guard τ
        · have hτ0 : τ res = 0 := hτ
          rw [ite_eq_left hτ, ite_eq_left hτ0, hM_b]
        · have hτ0 : τ res ≠ 0 := hτ
          rw [ite_eq_right hτ, ite_eq_right hτ0]
          rfl
      · intro R M_odd
        rw [← hM_b (fun _ ↦ 0), vecQuad_eigBody_step res hm_grid hk_grid hn hcard s hval]
        have hs0 : (whileActiveWP (wp bodyP) guard t
            (Store.subst (fun _ : Var ↦ (0 : ℤ)) res 0)).1.1 = A_t := by
          rw [hA_dep]; simp [Store.subst]
        have hs1 : (whileActiveWP (wp bodyP) guard t
            (Store.subst (fun _ : Var ↦ (0 : ℤ)) res 1)).1.1 = 0 := by
          rw [hA_dep]; simp [Store.subst]
        rw [hs0, hs1, hA_val μ hval, show vecQuad 0 _ = 0 by simp [vecQuad], add_zero, pow_succ']
        push_cast
        rfl
  -- Unrolled correctness induction on t
  have hread_val (μ : Fin (2 ^ M)) (hval : MemPrefixValid S s.val μ) :
      let R := S \ memSeen n k (memPrefix k s.val) μ
      let M_odd := oddSet n m R
      let v₁ := subsetKraus1 M_odd (subTargetRatio p K) *ᵥ subsetGroverState M_odd (K + 1)
      vecQuad M_read
        (workMemState ((addrReg n m).tensorState v₁ (Pi.single 1 1)) (Pi.single μ 1)) =
        ((1 - q : ℝ) : ℂ) := by
    intro R M_odd v₁
    have hcm := card_memSeen_of_memPrefixValid hval
    have hR_card : R.card = r := by rw [Finset.card_sdiff_of_subset hcm.2, hcard, hcm.1]
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
      have hp0 : p = 0 := by rw [← hp_eq, show M_odd.card = 0 by omega]; simp
      linarith [hp_pos_lt.1]
    have hMlt : M_odd.card < 2 ^ (m * n) := by
      by_contra! hge
      have hp1 : 1 ≤ p := by
        rw [← hp_eq]
        exact (one_le_div (by positivity)).mpr (by exact_mod_cast hge)
      linarith [hp_pos_lt.2]
    have hs_le1 : (subTargetRatio ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ)) K) ^ 2 ≤ 1 := by
      rw [hp_eq]
      nlinarith [hhyps.1, hhyps.2.1]
    have hsin3 : sin ((2 * (K : ℝ) + 3) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
        0 := by
      rw [hp_eq]; exact hhyps.2.2.1
    have hcos1 : cos ((2 * (K : ℝ) + 1) * subHalfAngle ((M_odd.card : ℝ) / (2 ^ (m * n) : ℝ))) ≠
        0 := by
      rw [hp_eq]; exact hhyps.2.2.2.1
    have hk1 := sum_normSq_subsetKraus1_subsetGroverState M_odd hM0 hMlt K hs_le1 hsin3 hcos1
    dsimp only at hk1
    simp only [hp_eq] at hk1
    rw [← hM_read (fun _ ↦ 0)]
    dsimp only [Θ_read, readoutP, eigReadout, compile]
    rw [wp_qSeq, wp_qAssign, wp_phaseTag, qhlQAssign_val, vecQuad_conj,
      QRegister.embedUnitary_val, embedMatrix_lowBlock_mulVec_workMemState,
      permutationUnitary_flipPerm_mulVec_tensorState, addrEnv_one_add_one,
      vecQuad_markAndWrite s v₁ μ hval
        (fun z ↦ (validInd n m k S (s.val + 1) z : ℂ)) post (fun _ ↦ 0)
        (realDiagObs_mat _ _ _)]
    let w_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (m * (n + 1))) :=
      parallelMarkPerm n m R ((addrReg n m).basisSplitEquiv.symm (u, 0))
    let μ_of (u : Fin (2 ^ (m * n))) : Fin (2 ^ (k * n)) :=
      (addrEquiv n k).symm (addrEquiv n k μ +
        batchDelta s.val (fun w ↦ (firstMarkedAddr n m w).toList) (w_of u))
    have hterm (u : Fin (2 ^ (m * n))) :
        (normSq (v₁ u) : ℂ) *
          (validInd n m k S (s.val + 1)
            ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) : ℂ) =
          (normSq (v₁ u) : ℂ) := by
      by_cases hu : u ∈ M_odd
      · have hadv := (markAndWrite_outcome_props s hval u).2.1 hu
        have hv1 : validInd n m k S (s.val + 1)
            ((lowHighEquiv (m * (n + 1)) (k * n)).symm (w_of u, μ_of u)) = 1 := by
          unfold validInd
          rw [Equiv.apply_symm_apply, ite_eq_left hadv.2]
        rw [hv1, Complex.ofReal_one, mul_one]
      · dsimp only [v₁]
        rw [hk1.1 u hu, Complex.normSq_zero, Complex.ofReal_zero, zero_mul]
    rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← ofReal_sum, hk1.2]
  have hrec_mat (t : ℕ) :
      ∃ B_t : Operator (2 ^ (W + M)),
        (∀ τ, (whileRecWP (wp bodyP) guard (t + 1) Θ_read τ).1.1 =
          if τ res = 0 then B_t else M_read) ∧
        ∀ μ : Fin (2 ^ M), MemPrefixValid S s.val μ →
          let R := S \ memSeen n k (memPrefix k s.val) μ
          let M_odd := oddSet n m R
          vecQuad B_t
            (workMemState
              ((addrReg n m).tensorState
                (oracleMat M_odd *ᵥ subsetGroverState M_odd K) (Pi.single 0 1))
              (Pi.single μ 1)) = ((1 - q ^ t : ℝ) : ℂ) := by
    induction t with
    | zero =>
      rcases hbody_const (whileRecWP (wp bodyP) guard 0 Θ_read)
        (fun _ ↦ 0) (fun _ ↦ rfl) with ⟨M_b0, hM_b0⟩
      refine ⟨M_b0, fun τ ↦ ?_, fun μ hval ↦ ?_⟩
      · rw [qhlWhileSucc_val]
        by_cases hτ : τ res = 0
        · rw [ite_eq_left hτ, ite_eq_left hτ, hM_b0]
        · rw [ite_eq_right hτ, ite_eq_right hτ, hM_read]
      · intro R M_odd
        rw [← hM_b0 (fun _ ↦ 0), vecQuad_eigBody_step res hm_grid hk_grid hn hcard s hval]
        change (q : ℂ) * vecQuad 0 _ + vecQuad 0 _ = ((1 - q ^ 0 : ℝ) : ℂ)
        simp [vecQuad]
    | succ t ih =>
      rcases ih with ⟨B_t, hB_dep, hB_val⟩
      rcases hbody_const (whileRecWP (wp bodyP) guard (t + 1) Θ_read)
        (fun val ↦ if val = 0 then B_t else M_read) hB_dep with ⟨M_b, hM_b⟩
      refine ⟨M_b, fun τ ↦ ?_, fun μ hval ↦ ?_⟩
      · rw [qhlWhileSucc_val]
        by_cases hτ : τ res = 0
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
        rw [hs0, hs1, hB_val μ hval, hread_val μ hval, pow_succ']
        push_cast
        ring
  have hq0 : 0 ≤ q := subFailProb_nonneg p K
  have hq1 : q < 1 := hhyps.2.2.2.2
  refine ⟨fun σ ↦ ?_, fun t σ ↦ ?_⟩
  · have hgeom : ∀ t : ℕ,
        (validObs (Var := Var) n m k S s.val σ).1 -
            q ^ t • (validObs (Var := Var) n m k S s.val σ).1 ≤
          (wp ((eigLockStage res n m k hm_grid hk_grid hn s).compile qAssign oracle) post σ).1 := by
      intro t
      rcases hrec_mat t with ⟨B_t, hB_dep, hB_val⟩
      rcases hsetup_diag (whileRecWP (wp bodyP) guard (t + 1) Θ_read) B_t M_read hB_dep with
        ⟨d_s, hd_bounds, hd_mat, hd_val⟩
      have hsub_eq :
          (validObs (Var := Var) n m k S s.val σ).1 -
              q ^ t • (validObs (Var := Var) n m k S s.val σ).1 =
            (scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t)
              (sub_nonneg.mpr (pow_le_one₀ hq0 hq1.le))
              (sub_le_self 1 (pow_nonneg hq0 t)) σ).1 := by
        rw [scaledValidObs_smul, sub_smul, one_smul]
      rw [hsub_eq]
      have hle_unroll :
          scaledValidObs (Var := Var) n m k S s.val (1 - q ^ t)
            (sub_nonneg.mpr (pow_le_one₀ hq0 hq1.le))
            (sub_le_self 1 (pow_nonneg hq0 t)) σ ≤
          wp setupP (whileRecWP (wp bodyP) guard (t + 1) Θ_read) σ := by
        refine realDiagObs_le_of_mat (fun z ↦ (hd_bounds z).1) (fun z ↦ (hd_bounds z).2)
          (hd_mat σ) fun z ↦ ?_
        open Classical in
        by_cases hval : MemPrefixValid S s.val (lowHighEquiv W M z).2
        · have hv1 : validInd n m k S s.val z = 1 := by
            unfold validInd
            exact ite_eq_left hval
          have hdeq : d_s z = 1 - q ^ t :=
            Complex.ofReal_injective ((hd_val z hval).trans (hB_val _ hval))
          rw [hv1, mul_one, hdeq]
        · have hv0 : validInd n m k S s.val z = 0 := by
            unfold validInd
            exact ite_eq_right hval
          rw [hv0, mul_zero]
          exact (hd_bounds z).1
      have hstage_eq :
          wp ((eigLockStage res n m k hm_grid hk_grid hn s).compile qAssign oracle) post =
            wp setupP (wp (.qWhile guard bodyP) Θ_read) := by
        dsimp only [eigLockStage, setupP, bodyP, Θ_read, readoutP, guard, compile]
        rw [wp_qSeq, wp_qSeq]
      rw [hstage_eq]
      have hmon := wp_mono setupP (whileRecWP_le_wp_qWhile guard bodyP (t + 1) Θ_read) σ
      exact Subtype.coe_le_coe.mpr (hle_unroll.trans hmon)
    exact Subtype.coe_le_coe.mp
      (hermitian_le_of_geometric_sub_smul_le q hq0 hq1 _ _ _ hgeom)
  · rcases hact_mat t with ⟨A_t, hA_dep, hA_val⟩
    rcases hsetup_diag (whileActiveWP (wp bodyP) guard t) A_t 0 hA_dep with
      ⟨d_s, hd_bounds, hd_mat, hd_val⟩
    let rhs := (scaledValidObs (Var := Var) n m k S s.val (q ^ t)
      (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)).add (invalidObs n m k S s.val)
      (scaledValid_add_invalid_le_one n m k S s.val (q ^ t) _ _)
    let f_rhs (z : Fin (2 ^ (W + M))) : ℝ :=
      q ^ t * validInd n m k S s.val z + invalidInd n m k S s.val z
    have hf_bounds (z : Fin (2 ^ (W + M))) : 0 ≤ f_rhs z ∧ f_rhs z ≤ 1 := by
      dsimp only [f_rhs]
      have hqt0 : 0 ≤ q ^ t := pow_nonneg hq0 t
      have hqt1 : q ^ t ≤ 1 := pow_le_one₀ hq0 hq1.le
      unfold validInd invalidInd
      split_ifs <;> constructor <;> linarith
    have hrhs_eq : rhs σ = realDiagObs f_rhs (fun z ↦ (hf_bounds z).1)
        (fun z ↦ (hf_bounds z).2) := by
      apply Subtype.ext
      apply HermitianMat.ext
      change (scaledValidObs n m k S s.val (q ^ t) _ _ σ).1.1 +
        (invalidObs n m k S s.val σ).1.1 = (realDiagObs f_rhs _ _).1.1
      dsimp only [scaledValidObs, invalidObs]
      rw [realDiagObs_mat, realDiagObs_mat, realDiagObs_mat]
      ext z₁ z₂
      rw [Matrix.add_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases h : z₁ = z₂
      · subst h; simp [f_rhs]
      · simp [h]
    change _ ≤ rhs σ
    rw [hrhs_eq]
    refine le_realDiagObs_of_mat (fun z ↦ (hd_bounds z).1) (fun z ↦ (hd_bounds z).2)
      (hd_mat σ) fun z ↦ ?_
    dsimp only [f_rhs]
    open Classical in
    by_cases hval : MemPrefixValid S s.val (lowHighEquiv W M z).2
    · have hv1 : validInd n m k S s.val z = 1 := by
        unfold validInd; exact ite_eq_left hval
      have hi0 : invalidInd n m k S s.val z = 0 := by
        unfold invalidInd; exact ite_eq_left hval
      have hdeq : d_s z = q ^ t :=
        Complex.ofReal_injective ((hd_val z hval).trans (hA_val _ hval))
      rw [hv1, hi0, mul_one, add_zero, hdeq]
    · have hv0 : validInd n m k S s.val z = 0 := by
        unfold validInd; exact ite_eq_right hval
      have hi1 : invalidInd n m k S s.val z = 1 := by
        unfold invalidInd; exact ite_eq_right hval
      rw [hv0, hi1, mul_zero, zero_add]
      exact (hd_bounds z).2

noncomputable def stageCostReal (n m r : ℕ) : ℝ :=
  let p := oddFrac n m r
  let K := subSchedule p
  (K : ℝ) + 2 + (1 - subFailProb p K)⁻¹

lemma expectedCost_eigLockStage_le {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn : 200 ≤ n)
    {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (s : Fin k)
    {Δ : CQState (Store Var) (2 ^ (m * (n + 1) + k * n))}
    (hV : 𝔼[Δ, validObs n m k S s.val] = Δ.trace) :
    expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((eigLockStage res n m k hm_grid hk_grid hn s).compile qAssign
        (groverParallelMarkingOracle m S)) Δ ≤
      stateMass Δ * ENNReal.ofReal (stageCostReal n m (k - s.val)) := by
  set r := k - s.val
  set p := oddFrac n m r
  set K := subSchedule p
  set q := subFailProb p K
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hhyps := (stageCost_le_stage1RelCost (r := r) hn hm_grid hk_grid (by omega) (by omega)).1
  have hq0 : 0 ≤ q := subFailProb_nonneg p K
  have hq1 : q < 1 := hhyps.2.2.2.2
  have h1q_pos : 0 < 1 - q := sub_pos.mpr hq1
  let oracle := groverParallelMarkingOracle m S
  let model : CostModel (2 ^ (m * (n + 1) + k * n)) := CostModel.ofEmbeddedOracle oracle
  let setupP := (eigSetup (Var := Var) res n m k s K).compile qAssign oracle
  let bodyP := (eigBody (Var := Var) res n m k hm1 s (subTargetRatio p K)
    hhyps.1.le hhyps.2.1.le).compile qAssign oracle
  let readoutP := (eigReadout (Var := Var) n m k s).compile qAssign oracle
  let guard : Store Var → Prop := fun σ ↦ σ res = 0
  have hact := (eigLockStage_wp_and_active res hm_grid hk_grid hn hcard s).2
  have hinv0 : 𝔼[Δ, invalidObs n m k S s.val] = 0 := expect_invalidObs_eq_zero hV
  set Δ₁ := (interp setupP).toStateFun Δ
  set Δ₂ := (interp (.qWhile guard bodyP)).toStateFun Δ₁
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
      calc 𝔼[Δ, wp setupP (whileActiveWP (wp bodyP) guard t)]
          ≤ 𝔼[Δ, (scaledValidObs n m k S s.val (q ^ t)
              (pow_nonneg hq0 t) (pow_le_one₀ hq0 hq1.le)).add
              (invalidObs n m k S s.val)
              (scaledValid_add_invalid_le_one n m k S s.val (q ^ t) _ _)] :=
            expect_mono le_rfl (hact t)
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
          rw [mul_comm, ENNReal.ofReal_mul (by exact_mod_cast Δ.trace_nonneg),
            ← stateMass_eq_ofReal_trace, ENNReal.ofReal_pow hq0]
  have hwhile_le :
      expectedCost model (.qWhile guard bodyP) Δ₁ ≤
        stateMass Δ * ENNReal.ofReal (1 - q)⁻¹ := by
    have hb := costBound_eigBody (Var := Var) res n m k hm1 s (subTargetRatio p K)
      hhyps.1.le hhyps.2.1.le S
    calc expectedCost model (.qWhile guard bodyP) Δ₁
        ≤ expectedIterations guard bodyP Δ₁ * (1 : ℝ≥0) :=
          expectedCost_qWhile_le hb guard Δ₁
      _ = ∑' t : ℕ, stateMass (activeIter guard bodyP t Δ₁) := by
          simp [expectedIterations]
      _ ≤ ∑' t : ℕ, stateMass Δ * (ENNReal.ofReal q) ^ t :=
          ENNReal.tsum_le_tsum hiter_le
      _ = stateMass Δ * (1 - ENNReal.ofReal q)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = stateMass Δ * ENNReal.ofReal (1 - q)⁻¹ := by
          have hsub : 1 - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
            simpa using (ENNReal.ofReal_sub 1 hq0).symm
          rw [hsub, ENNReal.ofReal_inv_of_pos h1q_pos]
  change expectedCost model (setupP ;; (.qWhile guard bodyP ;; readoutP)) Δ ≤ _
  rw [expectedCost_qSeq, expectedCost_qSeq]
  calc expectedCost model setupP Δ +
        (expectedCost model (.qWhile guard bodyP) Δ₁ + expectedCost model readoutP Δ₂)
      ≤ stateMass Δ * ((K + 1 : ℕ) : ℝ≥0∞) +
          (stateMass Δ * ENNReal.ofReal (1 - q)⁻¹ + stateMass Δ * 1) :=
        add_le_add hsetup_le (add_le_add hwhile_le hread_le)
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
        dsimp only [stageCostReal, p, K, q]
        congr 1
        ring

lemma wp_qSet_validObs_zero {Var : Type} [DecidableEq Var] (n m k : ℕ)
    (S : Finset (Fin (2 ^ n))) :
    wp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n))) (validObs n m k S 0) = ⊤ := by
  funext σ
  apply Subtype.ext
  apply HermitianMat.ext
  change ((wp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n))) (validObs n m k S 0)) σ).1.1 = 1
  rw [wp_qSet, qhlQSet_val]
  dsimp only [validObs]
  rw [realDiagObs_mat, Matrix.diagonal_apply_eq]
  have h0 : (lowHighEquiv (m * (n + 1)) (k * n) 0).2 = 0 := by
    rw [lowHighEquiv_zero]
  have hv0 : validInd n m k S 0 0 = 1 := by
    unfold validInd
    rw [h0, ite_eq_left (memPrefixValid_zero S)]
  rw [hv0]
  simp

lemma validObs_le_wp_measure_decodeTargets {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) :
    validObs (Var := Var) n m k S k ≤
      wp (measureRegister res (highBlock (m * (n + 1)) (k * n)))
        (liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)) := by
  let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
    liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)
  intro σ
  let f_dec (z : Fin (2 ^ (m * (n + 1) + k * n))) : ℝ :=
    open Classical in
    if decodeTargets n k (Int.ofNat ((lowHighEquiv (m * (n + 1)) (k * n) z).2).val) = S then 1
    else 0
  have hf_b (z : Fin (2 ^ (m * (n + 1) + k * n))) : 0 ≤ f_dec z ∧ f_dec z ≤ 1 := by
    dsimp only [f_dec]; split_ifs <;> constructor <;> norm_num
  have hmat : ((wp (measureRegister res (highBlock (m * (n + 1)) (k * n))) post) σ).1.1 =
      diagonal (fun z ↦ (f_dec z : ℂ)) := by
    rw [wp_measureRegister]
    ext z₁ z₂
    rw [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hz : z₁ = z₂
    · subst hz
      let o₀ := (lowHighEquiv (m * (n + 1)) (k * n) z₁).2
      rw [sum_eq_single o₀ (fun o ho ↦ by
        rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
          extractIndex_highBlock, ite_eq_right (Ne.symm ho), mul_zero])]
      rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
        extractIndex_highBlock, ite_eq_left rfl, one_mul, mul_one]
      dsimp only [post, f_dec]
      rw [liftPureProp_apply]
      have hsubst : Store.subst σ res (Int.ofNat o₀.val) res = Int.ofNat o₀.val := by
        simp [Store.subst]
      open Classical in
      by_cases hd : decodeTargets n k (Int.ofNat o₀.val) = S
      · have hd' : decodeTargets n k (Store.subst σ res (Int.ofNat o₀.val) res) = S :=
          hsubst.symm ▸ hd
        rw [ite_eq_left hd', ite_eq_left hd]
        simp
      · have hd' : ¬ decodeTargets n k (Store.subst σ res (Int.ofNat o₀.val) res) = S :=
          hsubst.symm ▸ hd
        rw [ite_eq_right hd', ite_eq_right hd]
        simp
    · simp only [hz, ↓reduceIte]
      refine Finset.sum_eq_zero fun o _ ↦ ?_
      rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul]
      dsimp only [post]
      rw [liftPureProp_apply]
      by_cases hd : decodeTargets n k (Store.subst σ res (Int.ofNat o.val) res) = S
      · rw [ite_eq_left hd]
        simp [hz]
      · rw [ite_eq_right hd]
        simp
  refine realDiagObs_le_of_mat (fun z ↦ (hf_b z).1) (fun z ↦ (hf_b z).2) hmat fun z ↦ ?_
  dsimp only [validInd, f_dec]
  open Classical in
  by_cases hv : MemPrefixValid S k (lowHighEquiv (m * (n + 1)) (k * n) z).2
  · rw [ite_eq_left hv, ite_eq_left (decodeTargets_eq_of_memPrefixValid_full hcard hv)]
  · rw [ite_eq_right hv]
    exact (hf_b z).1

end

/-! ## Multi-Stage Fallback (`Stage1`) -/

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
    ∀ d : ℕ, ∀ j : ℕ, k - j = d → j ≤ k →
      validObs (Var := Var) n m k S j ≤
        wp ((stagesFrom res n m k hm_grid hk_grid j).compile qAssign
            (groverParallelMarkingOracle m S))
          (validObs n m k S k)
  | 0, j, hd, _ => by
    have hjeq : j = k := by omega
    subst hjeq
    rw [stagesFrom]
    simp
  | d + 1, j, hd, _ => by
    have hj : j < k := by omega
    rw [stagesFrom, dite_eq_left hj]
    dsimp only [compile]
    rw [wp_qSeq]
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
    rw [stagesFrom]
    simp
  | d + 1, j, hd, _, Δ, hV => by
    have hj : j < k := by omega
    rw [stagesFrom, dite_eq_left hj]
    dsimp only [compile]
    rw [expectedCost_qSeq]
    have hdisp_eq : stageDispatch (Var := Var) res n m k hm_grid hk_grid ⟨j, hj⟩ =
        eigLockStage res n m k hm_grid hk_grid hn200 ⟨j, hj⟩ := by
      unfold stageDispatch
      rw [dite_eq_left hn200]
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
        ≤ stateMass Δ * ENNReal.ofReal (stageCostReal n m (k - j)) +
            stateMass Δ *
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
  unfold circuit qubits
  have hgrid := cells_mem_grid hmk
  have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
  let post : CQAssertion (Store Var) (2 ^ (m * (n + 1) + k * n)) :=
    liftPureProp (fun σ ↦ decodeTargets n k (σ res) = S)
  refine Triple.of_eq_wp ?_
  symm
  rw [dite_eq_left hgrid, dite_eq_left hn]
  by_cases hk_eq : k = 2 ^ n
  · rw [dite_eq_left hk_eq]
    have hS_univ : S = Finset.univ :=
      Finset.eq_univ_of_card S (by simp [hcard, hk_eq])
    let μ_all := allTargetsIdx n k hk_eq
    have hdec_all : decodeTargets n k (Int.ofNat μ_all.val) = S := by
      refine decodeTargets_ofNat_eq_of_subset_of_injective hcard μ_all
        (fun i ↦ by rw [hS_univ]; exact Finset.mem_univ _)
        (fun i j hij ↦ ?_)
      dsimp only [μ_all, allTargetsIdx] at hij
      rw [Equiv.apply_symm_apply] at hij
      exact Fin.ext (Fin.mk.inj hij)
    funext σ
    apply Subtype.ext
    apply HermitianMat.ext
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
    rw [vecQuad_single M_conj 0]
    dsimp only [M_conj, U_sw]
    rw [vecQuad_conj, ← workMemState_zero,
      QRegister.embedUnitary_val, embedMatrix_highBlock_mulVec_workMemState,
      permutationUnitary_mulVec_single, Equiv.swap_apply_left, workMemState_single,
      ← vecQuad_single M_meas]
    dsimp only [M_meas]
    rw [wp_measureRegister, Matrix.sum_apply]
    let z_all := (lowHighEquiv (m * (n + 1)) (k * n)).symm (0, μ_all)
    have hsum :
        (∑ o : Fin (2 ^ (k * n)),
          ((highBlock (m * (n + 1)) (k * n)).basisOutcomeProjector o *
            (post (Store.subst σ res (Int.ofNat o.val))).1.1 *
            (highBlock (m * (n + 1)) (k * n)).basisOutcomeProjector o) z_all z_all) = 1 := by
      rw [sum_eq_single μ_all (fun o ho ↦ by
        rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
          extractIndex_highBlock]
        dsimp only [z_all]
        rw [Equiv.apply_symm_apply, ite_eq_right (Ne.symm ho), mul_zero])]
      rw [QRegister.basisOutcomeProjector_eq_diagonal, mul_diagonal, Matrix.diagonal_mul,
        extractIndex_highBlock]
      dsimp only [z_all, post]
      rw [Equiv.apply_symm_apply, ite_eq_left rfl, liftPureProp_apply]
      have hs : decodeTargets n k (Store.subst σ res (Int.ofNat μ_all.val) res) = S := by
        simpa [Store.subst] using hdec_all
      rw [ite_eq_left hs]
      simp
    rw [hsum, one_smul]
  · rw [dite_eq_right hk_eq]
    have hk_lt : k < 2 ^ n := lt_of_le_of_ne hkN hk_eq
    dsimp only [compile]
    rw [wp_qSeq, wp_qSeq]
    have hmeas_ge : validObs (Var := Var) n m k S k ≤
        wp (measureRegister res (highBlock (m * (n + 1)) (k * n))) post :=
      validObs_le_wp_measure_decodeTargets res hcard
    have hst_ge := wp_stagesFrom_ge (Var := Var) res hgrid.1 hgrid.2 hk_lt hcard k 0
      (by omega) (by omega)
    have htot_ge : validObs (Var := Var) n m k S 0 ≤
        wp ((stagesFrom res n m k hgrid.1 hgrid.2 0).compile qAssign
            (groverParallelMarkingOracle m S))
          (wp (measureRegister res (highBlock (m * (n + 1)) (k * n))) post) :=
      hst_ge.trans (wp_mono _ hmeas_ge)
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
  have hgrid := cells_mem_grid hmk
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hgrid.2
  refine ⟨200, fun n hn200 hkN ↦ ?_⟩
  unfold qubits
  have hn1 : 1 ≤ n := by omega
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
    change expectedCost model
      (qset ;; ((circuit (Var := Var) res n m k).compile qAssign oracle :
        QProg Var (2 ^ (m * (n + 1) + k * n)))) state ≤
      stateMass state * (q_val : ℝ≥0∞)
    have hcirc : ((circuit (Var := Var) res n m k).compile qAssign oracle :
        QProg Var (2 ^ (m * (n + 1) + k * n))) =
        ((stagesFrom res n m k hgrid.1 hgrid.2 0).compile qAssign oracle ;;
          measureRegister res (highBlock (m * (n + 1)) (k * n))) := by
      unfold circuit
      dsimp only [qubits]
      rw [dite_eq_left hgrid, dite_eq_left hn1, dite_eq_right hk_ne]
      rfl
    rw [hcirc, expectedCost_qSeq, expectedCost_qSet]
    have hreset0 : model.resetCost = 0 := rfl
    simp only [hreset0, Nat.cast_zero, mul_zero, zero_add]
    rw [expectedCost_qSeq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n m k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]
      rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
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
    rw [Nat.sub_zero, hmass0] at hst
    refine hst.trans ?_
    gcongr
    dsimp only [q_val]
    rw [ENNReal.ofNNReal_finsetSum]
    refine le_of_eq ?_
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
        have h1q : 0 < 1 - subFailProb (oddFrac n m (k - s.val))
            (subSchedule (oddFrac n m (k - s.val))) :=
          sub_pos.mpr hsc.1.2.2.2.2
        positivity
      rw [Real.coe_toNNReal _ h0]
      exact hsc.2
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      have hc : (groverTargetSets n k).card = Nat.choose (2 ^ n) k := by
        simp [groverTargetSets]
      rw [hc]
      exact_mod_cast Nat.choose_pos hkN
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']
    exact hsum_le

end

end Stage1

end QuantumComputation.Specs.DickeSol
end WD_FindAllStage1

section WD_Stage1EigLock

@[expose] public section

namespace QuantumComputation.Specs.DickeSol

open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open scoped NNReal NNRat ENNReal QHLExpectation

/-- For `n ≥ 600` on `groverGrid`, `stageCostReal n m r` is nonnegative and bounded above by
  `(π / 8 + 1 / 4) * √(2 ^ n / (m * r)) + 5`. -/
theorem stageCostReal_le_linear_S0 {n m k r : ℕ} (hn : 600 ≤ n)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    0 ≤ stageCostReal n m r ∧
      stageCostReal n m r ≤
        (π / 8 + 1 / 4) * √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) + 5 := by
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  have hr_hi : r ≤ 1024 := hrk.trans hk_hi
  have h2r_le : 2 * r ≤ 2 ^ n := by
    calc 2 * r ≤ 2 * 1024 := by omega
      _ ≤ 2 ^ 12 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hr_lt : r < 2 ^ n := by omega
  set p := oddFrac n m r
  set K := subSchedule p
  have hp_pos : 0 < p := (oddFrac_pos_lt_one hm1 hr1 hr_lt).1
  set p₀ : ℝ := ((m : ℝ) * (r : ℝ)) / (2 ^ n : ℝ)
  set S₀ : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)))
  have hmr_pos : (0 : ℝ) < (m : ℝ) * (r : ℝ) := by positivity
  have hmr_le : (m : ℝ) * (r : ℝ) ≤ 16 ^ 5 := by
    have : m * r ≤ 1024 * 1024 := Nat.mul_le_mul hm_hi hr_hi
    calc (m : ℝ) * (r : ℝ) = ((m * r : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((1024 * 1024 : ℕ) : ℝ) := by exact_mod_cast this
      _ = 16 ^ 5 := by norm_num
  have h2n_ge : (16 ^ 150 : ℝ) ≤ (2 ^ n : ℝ) := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hS0_sq : S₀ ^ 2 = (2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)) :=
    Real.sq_sqrt (by positivity)
  have hS0_sq_ge : (16 : ℝ) ^ 145 ≤ S₀ ^ 2 := by
    rw [hS0_sq, le_div_iff₀ hmr_pos]
    calc (16 : ℝ) ^ 145 * ((m : ℝ) * (r : ℝ))
        ≤ (16 : ℝ) ^ 145 * (16 : ℝ) ^ 5 := mul_le_mul_of_nonneg_left hmr_le (by positivity)
      _ = (16 : ℝ) ^ 150 := by norm_num
      _ ≤ (2 ^ n : ℝ) := h2n_ge
  have hS0_ge : (4 : ℝ) ^ 145 ≤ S₀ := by
    have h145 : ((4 : ℝ) ^ 145) ^ 2 = (16 : ℝ) ^ 145 := by norm_num
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
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq hmul
  have hs16 : 16 ≤ 1 / √p := by
    calc (16 : ℝ) ≤ (4 : ℝ) ^ 145 := by norm_num
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
      have hdecomp : 2 * S₀ ^ 3 - 2 * S₀ - 1 =
          (S₀ - 2) * (2 * S₀ ^ 2 + 4 * S₀ + 6) + 11 := by ring
      rw [hdecomp]
      have hsub : 0 ≤ S₀ - 2 := by linarith
      positivity
    exact hpoly.trans (mul_le_mul_of_nonneg_left hp_lo (sq_nonneg _))
  obtain ⟨hhyps, hqbound⟩ := subSchedule_hyps_le hp_pos hs16
  have h1q_pos : 0 < 1 - subFailProb p K := sub_pos.mpr hhyps.2.2.2.2
  have hnn : 0 ≤ stageCostReal n m r := by
    dsimp only [stageCostReal, p, K]
    positivity
  refine ⟨hnn, ?_⟩
  have hπ_hi : π < 4 := Real.pi_lt_four
  dsimp only [stageCostReal, p, K]
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
    rw [stagesFrom]
    simp
  | d + 1, j, hd, _, Δ, hV => by
    have hj : j < k := by omega
    rw [stagesFrom, dite_eq_left hj]
    dsimp only [compile]
    rw [expectedCost_qSeq]
    have hdisp_eq : stageDispatch (Var := Var) res n m k hm_grid hk_grid ⟨j, hj⟩ =
        eigLockStage res n m k hm_grid hk_grid hn200 ⟨j, hj⟩ := by
      unfold stageDispatch
      rw [dite_eq_left hn200]
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
        ≤ stateMass Δ * ENNReal.ofReal (stageCostReal n m (k - j)) +
            stateMass Δ *
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
  have hgrid := cells_mem_grid hmk
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hgrid.1
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
  have hn_M : M ≤ n := (le_max_right _ _).trans hn
  have hn200 : 200 ≤ n := by omega
  unfold qubits
  have hn1 : 1 ≤ n := by omega
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
    change expectedCost model
      (qset ;; ((circuit (Var := Var) res n m k).compile qAssign oracle :
        QProg Var (2 ^ (m * (n + 1) + k * n)))) state ≤
      stateMass state * (q_val : ℝ≥0∞)
    have hcirc : ((circuit (Var := Var) res n m k).compile qAssign oracle :
        QProg Var (2 ^ (m * (n + 1) + k * n))) =
        ((stagesFrom res n m k hgrid.1 hgrid.2 0).compile qAssign oracle ;;
          measureRegister res (highBlock (m * (n + 1)) (k * n))) := by
      unfold circuit
      dsimp only [qubits]
      rw [dite_eq_left hgrid, dite_eq_left hn1, dite_eq_right hk_ne]
      rfl
    rw [hcirc, expectedCost_qSeq, expectedCost_qSet]
    have hreset0 : model.resetCost = 0 := rfl
    simp only [hreset0, Nat.cast_zero, mul_zero, zero_add]
    rw [expectedCost_qSeq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ (m * (n + 1) + k * n)))).toStateFun state
    have hV0 : 𝔼[Δ₀, validObs n m k S 0] = Δ₀.trace := by
      dsimp only [Δ₀]
      rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
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
    rw [Nat.sub_zero, hmass0] at hst
    refine hst.trans ?_
    gcongr
    dsimp only [q_val]
    rw [ENNReal.ofNNReal_finsetSum]
    refine le_of_eq ?_
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
      set r := k - s.val
      have hr1 : 1 ≤ r := by omega
      have hrk : r ≤ k := by omega
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
      have h5_δ : 5 ≤ δ * S₀ := by
        have := (div_le_iff₀ hδ).mp h5_S0
        linarith
      have hvan : (stage1RelCost : ℝ) * vanillaFindAnyCost n m r =
          ((π / 8 + 1 / 4) + δ) * S₀ := by
        unfold vanillaFindAnyCost; dsimp only [δ, S₀]; ring
      linarith [hsc.2, h5_δ, hvan]
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      have hc : (groverTargetSets n k).card = Nat.choose (2 ^ n) k := by
        simp [groverTargetSets]
      rw [hc]
      exact_mod_cast Nat.choose_pos hkN
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']
    exact hsum_le

end Stage1

end QuantumComputation.Specs.DickeSol
end
end WD_Stage1EigLock
