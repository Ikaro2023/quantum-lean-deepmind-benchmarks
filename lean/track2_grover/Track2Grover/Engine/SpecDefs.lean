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
public import QuantumComputation.Maths.Tsum
public import QuantumComputation.QuantumHoareLogic.Semantics
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Maths.Trigonometry
public import QuantumComputation.Algorithms.Grover.Cost
public import QuantumComputation.Algorithms.Grover.Verification
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.BitVec
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.NumberTheory.Niven

@[expose] public section

open Store (Expr)

/-- Retain `𝔼[Δ, θ]` expectation notation. -/
scoped[QHLExpectation] notation (priority := low) "𝔼[" Δ ", " θ "]" => expect Δ θ

section
open Operator
open scoped QHLExpectation

variable {Var : Type} {d : ℕ}

open Classical in
/-- Lift a classical predicate to a zero-one quantum assertion. -/
noncomputable def liftPureProp (p : Store Var → Prop) : CQAssertion (Store Var) d :=
  fun σ ↦ if p σ then (1 : Observable (Fin d)) else 0

open Classical in
/-- Pointwise evaluation of `liftPureProp`. -/
@[simp, grind =]
lemma liftPureProp_apply (p : Store Var → Prop) (σ : Store Var) :
    liftPureProp (d := d) p σ = if p σ then 1 else 0 := rfl

/-- Expectation of `liftPureProp` equals restricted state trace. -/
theorem expect_liftPureProp (p : Store Var → Prop) [DecidablePred p]
    (Δ : CQState (Store Var) d) :
    𝔼[Δ, liftPureProp p] = (Δ.restrict p).trace :=
  expect_ofProp p Δ

end

section
open Operator
open scoped QHLExpectation

variable {Var : Type*} {d : ℕ}

/-- Constant observable assertion shim. -/
noncomputable abbrev constAssertion (c : ℝ) : CQAssertion (Store Var) d :=
  CQAssertion.ofProb c

/-- Pointwise matrix evaluation of `constAssertion`. -/
lemma constAssertion_apply_of_bounds (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (σ : Store Var) :
    ((constAssertion c : CQAssertion (Store Var) d) σ).1 = c • (1 : HermitianMat (Fin d) ℂ) :=
  CQAssertion.ofProb_apply_of_bounds c hc0 hc1 σ

/-- Expectation of `constAssertion` against a `CQState`. -/
theorem expect_constAssertion (constant : ℝ) (state : CQState (Store Var) d)
    (hconstant : 0 ≤ constant ∧ constant ≤ 1) :
    𝔼[state ⊨ constAssertion constant] = constant * state.trace :=
  expect_ofProb constant state hconstant

end

namespace QuantumComputation.Specs.GroverAuxDefs

open Operator ResourceCounting Real
open scoped NNReal NNRat

section

variable {Var : Type} [Fintype Var] [DecidableEq Var]

/-- The Grover angle `θ`, such that `sin(θ / 2) = 1 / √dim`. -/
noncomputable def groverAngle (dim : ℕ) : ℝ :=
  2 * Real.arcsin (1 / √dim)

/-- Success probability of Grover's algorithm after `K` iterations:
  `p_succ(K, dim) = sin^2((2K + 1) / 2 * θ)` where `sin(θ / 2) = 1 / √dim`. -/
noncomputable def p_succ (K : ℕ) (dim : ℕ) : ℝ :=
  (Real.sin ((2 * (K : ℝ) + 1) / 2 * groverAngle dim)) ^ 2

/-- Postcondition: the classical variable `res` holds the target index `target.val`. -/
noncomputable def isTargetAssertion {n : ℕ} (res : Var) (target : Fin (2 ^ n)) :
    CQAssertion (Store Var) (2 ^ n) :=
  liftPureProp (fun σ ↦ σ res = target.val)

/-- Marked-state phase-oracle unitary flipping the phase of `|target⟩`. -/
noncomputable def groverOracleUnitary {n : ℕ} (target : Fin (2 ^ n)) : Unitary (2 ^ n) :=
  ⟨Matrix.diagonal (fun i ↦ if i = target then -1 else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Pi.star_apply, RCLike.star_def, ite_mul, neg_mul, one_mul, Matrix.diagonal_eq_one]
    funext i
    by_cases h : i = target <;> simp [h]⟩

end

variable {Var : Type} [DecidableEq Var]

/-- Marking oracle for a subset `S ⊆ Fin (2 ^ n)` acting on `n + 1` qubits.
  Under `tableAddPerm` (`finProdFinEquiv: (x, b) ↦ b + 2 * x`) and the little-endian
  `QRegister`
  convention, logical wire `0` is the marker bit `b` and logical wires `1..n` hold the
  `n`-bit index
  `x`, mapping basis state `(b, x)` to `(b ⊕ [x ∈ S], x)`. A phase flip (`b` in `|−⟩`), a
  candidate
  check, and a weak measurement each take one call, without uncomputation. -/
noncomputable def groverSetMarkingOracle {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  permutationUnitary (tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0)

/-- Single-target marking oracle `(b, x) ↦ (b ⊕ [x = target], x)` on `n + 1` qubits,
  specializing
  `groverSetMarkingOracle` to `{target}` (marker bit on wire `0`, index `x` on wires
  `1..n`). -/
noncomputable abbrev groverMarkingOracle {n : ℕ} (target : Fin (2 ^ n)) : Unitary (2 ^ (n + 1)) :=
  groverSetMarkingOracle {target}

/-- Synchronous `m`-slot parallel marking oracle for `S ⊆ Fin (2 ^ n)` on `(n + 1) * m`
  qubits
  (`n + 1` wires at `m = 1`), representing one parallel query round of `m` independent
  copies of
  `groverSetMarkingOracle S` on pairwise disjoint `(n + 1)`-qubit subregisters of a shared
  quantum
  state (Zalka's parallel query model).
  Within the `((n + 1) * m)`-wire oracle register, slot `i: Fin m` occupies logical wires
  `i * (n + 1).. i * (n + 1) + n`: logical wire `i * (n + 1)` is the marker bit `b_i` and
  the next
  `n` wires are `x_i`. Rounds using fewer than `m` active queries route unused marker wires
  to
  ancillas in `|+⟩`, on which `groverSetMarkingOracle S` acts as the identity for every `S`. -/
noncomputable def groverParallelMarkingOracle {n : ℕ} (m : ℕ)
    (S : Finset (Fin (2 ^ n))) : Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])).embedUnitary
      (groverSetMarkingOracle S)).prod

/-- All `k`-element target subsets of `Fin (2 ^ n)`. -/
def groverTargetSets (n k : ℕ) : Finset (Finset (Fin (2 ^ n))) :=
  (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k

/-- Decode up to `k` indices in `Fin (2 ^ n)` from the first `k` base-`2 ^ n` digits
  (`n`-bit
  chunks) of `z.toNat`. -/
def decodeTargets (n k : ℕ) (z : ℤ) : Finset (Fin (2 ^ n)) :=
  (Finset.range k).image fun i ↦
    ⟨(z.toNat / (2 ^ n) ^ i) % 2 ^ n, Nat.mod_lt _ (by positivity)⟩

/-- The predicate that `bound` is the uniform-average expected oracle cost bound across all
  `S ∈ groverTargetSets n k`. -/
def AvgOracleCostBound {d n : ℕ} [NeZero d] (k : ℕ)
    (costModel : Finset (Fin (2 ^ n)) → CostModel d)
    (prog : Finset (Fin (2 ^ n)) → QProg Var d) (bound : ℝ) : Prop :=
  ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
    (∀ S ∈ groverTargetSets n k, CostBound (costModel S) (prog S) (q S)) ∧
    (∑ S ∈ groverTargetSets n k, (q S : ℝ)) / (groverTargetSets n k).card ≤ bound

/-- Harmonic inverse-square-root sum `∑_{r=1}^k 1 / √r` appearing in sequential
  coupon-collecting
  multi-target Grover search. -/
noncomputable def groverHarmonicSqrtSum (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 k, 1 / √r

/-- Reference parallel single-find query scale `(π / 4) * √(2 ^ n / (m * k))` for finding
  any one
  of `k` marked items with `m` parallel queries per round. -/
noncomputable def vanillaFindAnyCost (n m k : ℕ) : ℝ :=
  (π / 4) * √((2 ^ n : ℝ) / (m * k))

/-- Reference unpartitioned coupon-collecting parallel query scale
  `(π / 4) * (∑_{r=1}^k 1 / √r) * √(2 ^ n / m)` for finding all `k` marked items
  sequentially across
  `k` stages with `m` parallel queries per round. -/
noncomputable def vanillaFindAllCost (n m k : ℕ) : ℝ :=
  (π / 4) * groverHarmonicSqrtSum k * √((2 ^ n : ℝ) / m)

end QuantumComputation.Specs.GroverAuxDefs

/-!
## Layer 0 Fast-Check Helpers (`GroverFastCheck`)
Algorithm-neutral `#eval` helpers for `((n + 1) * m)`-wire oracle register bounds,
disjointness,
and `ℚ≥0 -> ppm` ceiling arithmetic (`1_000_000` ppm = ratio `1.0`).
-/
namespace GroverFastCheck

def checkOracleRegisterWidth (n m numWires : ℕ) : Bool :=
  decide (numWires == (n + 1) * m)

def checkRegNodup (wires : List ℕ) : Bool :=
  decide wires.Nodup

def checkQubitBounds (totalQubits : ℕ) (regs : List (List ℕ)) : Bool :=
  regs.all fun r => checkRegNodup r && r.all (fun w => decide (w < totalQubits))

def checkPairwiseDisjoint (regs : List (List ℕ)) : Bool :=
  let flat := regs.flatten
  decide flat.Nodup

def ppmCeilOfRat (num den : ℕ) : ℕ :=
  if den == 0 then 0 else (1000000 * num + den - 1) / den

end GroverFastCheck

namespace CQState

/-- Real-valued trace of a `CQState` is nonnegative. -/
theorem trace_nonneg {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) :
    0 ≤ (Δ.trace : ℝ) :=
  Δ.trace.coe_nonneg

/-- Restriction of `Δ` to classical stores satisfying `cond`. -/
@[simps]
noncomputable def cqTrueSt {Var : Type} {d : ℕ} (cond : Store Var → Prop)
    [DecidablePred cond] (Δ : CQState (Store Var) d) : CQState (Store Var) d :=
  ⟨fun σ ↦ if cond σ then Δ.1 σ else 0,
    exists_hasSum_of_trace_le Δ _ fun σ ↦ by
      split_ifs <;> simp⟩

/-- Restriction of `Δ` to classical stores refuting `cond`. -/
@[simps]
noncomputable def cqFalseSt {Var : Type} {d : ℕ} (cond : Store Var → Prop)
    [DecidablePred cond] (Δ : CQState (Store Var) d) : CQState (Store Var) d :=
  ⟨fun σ ↦ if cond σ then 0 else Δ.1 σ,
    exists_hasSum_of_trace_le Δ _ fun σ ↦ by
      split_ifs <;> simp⟩

@[gcongr]
theorem cqTrueSt_mono {Var : Type} {d : ℕ} (cond : Store Var → Prop)
    [DecidablePred cond] {Δ₁ Δ₂ : CQState (Store Var) d} (h : Δ₁ ≤ Δ₂) :
    Δ₁.cqTrueSt cond ≤ Δ₂.cqTrueSt cond := fun σ ↦ by
  dsimp only [cqTrueSt]
  split_ifs
  exacts [h σ, le_rfl]

@[gcongr]
theorem cqFalseSt_mono {Var : Type} {d : ℕ} (cond : Store Var → Prop)
    [DecidablePred cond] {Δ₁ Δ₂ : CQState (Store Var) d} (h : Δ₁ ≤ Δ₂) :
    Δ₁.cqFalseSt cond ≤ Δ₂.cqFalseSt cond := fun σ ↦ by
  dsimp only [cqFalseSt]
  split_ifs
  exacts [le_rfl, h σ]

theorem trace_cqTrueSt_add_trace_cqFalseSt {Var : Type} {d : ℕ}
    (cond : Store Var → Prop) [DecidablePred cond] (Δ : CQState (Store Var) d) :
    (Δ.cqTrueSt cond).trace + (Δ.cqFalseSt cond).trace = Δ.trace := by
  symm
  refine Δ.trace_eq_of_hasSum_trace ?_
  convert (Δ.cqTrueSt cond).hasSum_trace.add (Δ.cqFalseSt cond).hasSum_trace using 1
  ext σ
  simp only [cqTrueSt_coe, cqFalseSt_coe]
  split_ifs <;> simp

end CQState

/-- Weakest-precondition expectation identity (`expect_wp`). -/
alias wp_expectation_eq := expect_wp

namespace ResourceCounting

open scoped ENNReal in
/-- Total mass of `state` in `ℝ≥0∞`, definitionally equal to `↑state.trace`. -/
noncomputable abbrev stateMass {Var : Type} {d : ℕ} (state : CQState (Store Var) d) :
    ℝ≥0∞ :=
  state.trace

end ResourceCounting

/-- Equivalence between `QProg.Lossless` and `stateMass` conservation. -/
theorem QProg.lossless_iff_stateMass {Var : Type} {d : ℕ} [DecidableEq Var] [NeZero d]
    {program : QProg Var d} :
    program.Lossless ↔
      ∀ state, ResourceCounting.stateMass ((interp program).toStateFun state) =
        ResourceCounting.stateMass state :=
  ⟨fun h state ↦ congrArg ENNReal.ofNNReal (h.trace_eq state),
   fun h ↦ .of_trace_eq fun state ↦ ENNReal.coe_inj.mp (h state)⟩

alias ⟨QProg.Lossless.stateMass_eq, QProg.Lossless.of_stateMass_eq⟩ :=
  QProg.lossless_iff_stateMass

namespace ResourceCounting

export QProg (Lossless)

namespace Lossless

export QProg.Lossless («skip» assign qAssign qSet qMeasure seq qIf
  of_wp_top of_wp_eq_top qWhile stateMass_eq of_stateMass_eq)

end Lossless

end ResourceCounting

/-- Coerce a `QProg.Lossless` proof to its `stateMass` conservation equality. -/
instance instCoeFunLosslessStateMass {Var : Type} {instDec : DecidableEq Var}
    {d : ℕ} {instNZ : NeZero d} {program : QProg Var d} :
    CoeFun (@QProg.Lossless Var instDec d instNZ program)
      (fun _ ↦ ∀ state : CQState (Store Var) d,
        ResourceCounting.stateMass ((@interp Var instDec d instNZ program).toStateFun state) =
          ResourceCounting.stateMass state) :=
  ⟨fun h ↦ @QProg.Lossless.stateMass_eq Var d instDec instNZ program h⟩

section QHLBridgeAux

open Operator ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal ENNReal QHLExpectation

namespace Operator

/-- Computational-basis projector `|o⟩⟨o|` bundled as a `HermitianMat`. -/
noncomputable def cqCompProjHerm {d : ℕ} (o : Fin d) : HermitianMat (Fin d) ℂ :=
  ⟨compProj o, compProj_isHermitian o⟩

@[simp]
theorem cqCompProjHerm_mat {d : ℕ} (o : Fin d) :
    (cqCompProjHerm o).mat = compProj o := rfl

@[simp]
theorem cqCompProjHerm_nonneg {d : ℕ} (o : Fin d) :
    0 ≤ cqCompProjHerm o := compProj_nonneg o

@[simp]
theorem cqCompProjHerm_le_one {d : ℕ} (o : Fin d) :
    cqCompProjHerm o ≤ 1 := compProj_le_one o

@[simp]
lemma cqState_qSet_mat {Var : Type} {d : ℕ} [NeZero d] (Δ : CQState (Store Var) d)
    (σ : Store Var) :
    (Δ.qSet.1 σ).1.mat = Matrix.single 0 0 ((Δ.1 σ).1.trace : ℂ) := rfl

@[simp]
lemma cqState_qSet_val1 {Var : Type} {d : ℕ} [NeZero d] (Δ : CQState (Store Var) d)
    (σ : Store Var) :
    (Δ.qSet.1 σ).1.1 = Matrix.single 0 0 ((Δ.1 σ).1.trace : ℂ) := rfl

@[simp]
lemma cqState_qSet_trace {Var : Type} {d : ℕ} [NeZero d] (Δ : CQState (Store Var) d)
    (σ : Store Var) :
    (Δ.qSet.1 σ).1.trace = (Δ.1 σ).1.trace := by
  rw [HermitianMat.trace_eq_re_trace, cqState_qSet_mat, RCLike.re_eq_complex_re,
    Matrix.trace, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim

end Operator

theorem cqExpect_ite_split {Var : Type} {d : ℕ}
    (b : Store Var → Prop) [DecidablePred b] (Δ : CQState (Store Var) d)
    (θt θf : CQAssertion (Store Var) d) :
    𝔼[Δ, fun σ ↦ if b σ then θt σ else θf σ] =
      𝔼[Δ.cqTrueSt b, θt] + 𝔼[Δ.cqFalseSt b, θf] :=
  (expect_ite_partition b Δ θt θf).trans <|
    congrArg₂ (· + ·)
      (congrArg (fun x ↦ 𝔼[x, θt])
        (Subtype.ext (funext fun σ ↦ by by_cases h : b σ <;> simp [CQState.cqTrueSt, h])))
      (congrArg (fun x ↦ 𝔼[x, θf])
        (Subtype.ext (funext fun σ ↦ by by_cases h : b σ <;> simp [CQState.cqFalseSt, h])))

/-- Restrict a classical-quantum assertion branchwise onto zero ancillas of `rAnc`. -/
noncomputable def cqRestrictZeroAncilla {Var : Type} {n m : ℕ}
    (M : CQAssertion (Store Var) (2 ^ n)) (rAnc : QRegister m n) : CQAssertion (Store Var) (2 ^ n)
      :=
  fun σ ↦ ⟨HermitianMat.conj (rAnc.basisOutcomeProjector 0) (M σ).1, by
    constructor
    · exact (M σ).1.conj_nonneg (rAnc.basisOutcomeProjector 0) (M σ).2.1
    · have h1 : HermitianMat.conj (rAnc.basisOutcomeProjector 0) 1 =
          (rAnc.basisOutcomeObservable 0).1 := by
        apply HermitianMat.ext
        simp [HermitianMat.conj_apply_mat]
      exact (HermitianMat.conj_mono (M σ).2.2).trans
        (h1.le.trans (rAnc.basisOutcomeObservable 0).2.2)⟩

@[simp]
theorem cqRestrictZeroAncilla_coe {Var : Type} {n m : ℕ}
    (M : CQAssertion (Store Var) (2 ^ n)) (rAnc : QRegister m n) (σ : Store Var) :
    (cqRestrictZeroAncilla M rAnc σ).1 =
      (M σ).1.conj (rAnc.basisOutcomeProjector 0) := rfl

namespace QMonad.Q

@[simp high]
theorem cqToStateFunIf {Var : Type} {d : ℕ} (cond : Store Var → Prop)
    [DecidablePred cond] (S₁ S₂ : QMonad.Q (Store Var) d Unit) (Δ : CQState (Store Var) d) :
    (QMonad.Q.cqIf cond S₁ S₂).toStateFun Δ =
      (S₁.toStateFun (Δ.cqTrueSt cond)).add (S₂.toStateFun (Δ.cqFalseSt cond))
        (by
          grw [S₁.trace_toStateFun_le, S₂.trace_toStateFun_le,
            CQState.trace_cqTrueSt_add_trace_cqFalseSt, CQState.trace_le_one]) :=
  Subtype.ext <| funext fun σ ↦ Subtype.ext <|
    (congrArg (fun x : CQState (Store Var) d ↦ (x.1 σ).1)
        (QMonad.Q.toStateFun_cqIf cond S₁ S₂ Δ)).trans <|
      congrArg₂ (· + ·)
        (congrArg (fun x : CQState (Store Var) d ↦ ((S₁.toStateFun x).1 σ).1)
          (Subtype.ext (funext fun τ ↦ by by_cases h : cond τ <;> simp [CQState.cqTrueSt, h])))
        (congrArg (fun x : CQState (Store Var) d ↦ ((S₂.toStateFun x).1 σ).1)
          (Subtype.ext (funext fun τ ↦ by by_cases h : cond τ <;> simp [CQState.cqFalseSt, h])))

end QMonad.Q

namespace ResourceCounting

theorem stateMass_eq_ofReal_trace {Var : Type} {d : ℕ} (state : CQState (Store Var) d) :
    stateMass state = ENNReal.ofReal (state.trace : ℝ) :=
  ENNReal.ofReal_coe_nnreal.symm

theorem stateMass_eq_tsum {Var : Type} {d : ℕ} (state : CQState (Store Var) d) :
    stateMass state = ∑' store, ENNReal.ofReal ((state.1 store).1.trace) := by
  rw [stateMass_eq_ofReal_trace, state.coe_trace_eq_tsum]
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun store ↦ (state.1 store).trace_val_nonneg) state.summable_trace_val

@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem stateMass_ne_top {Var : Type} {d : ℕ} (state : CQState (Store Var) d) : stateMass state ≠ ⊤
    :=
  ENNReal.coe_ne_top

theorem ofReal_expect_top {Var : Type} {d : ℕ} (state : CQState (Store Var) d) :
    ENNReal.ofReal 𝔼[state ⊨ ⊤] = stateMass state := by
  rw [expect_top, stateMass_eq_ofReal_trace]

@[simp]
theorem stateMass_zero {Var : Type} {d : ℕ} : stateMass (0 : CQState (Store Var) d) = 0 := by
  simp [stateMass]

@[gcongr]
theorem stateMass_mono {Var : Type} {d : ℕ} {left right : CQState (Store Var) d} (h : left ≤ right)
    :
    stateMass left ≤ stateMass right :=
  ENNReal.coe_le_coe.mpr (CQState.trace_mono h)

theorem stateMass_interp_le {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (program : QProg Var d) (state : CQState (Store Var) d) :
    stateMass ((interp program).toStateFun state) ≤ stateMass state :=
  ENNReal.coe_le_coe.mpr ((interp program).trace_toStateFun_le state)

theorem stateMass_add {Var : Type} {d : ℕ}
    (left right sum : CQState (Store Var) d)
    (hsum : ∀ store, (sum.1 store).1 = (left.1 store).1 + (right.1 store).1) :
    stateMass sum = stateMass left + stateMass right := by
  simp only [stateMass_eq_tsum]
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun store ↦ ?_
  rw [hsum store, HermitianMat.trace_add,
    ENNReal.ofReal_add (left.1 store).trace_val_nonneg (right.1 store).trace_val_nonneg]

theorem stateMass_restrict_add_stateMass_restrict_not {Var : Type} {d : ℕ}
    (condition : Store Var → Prop) [DecidablePred condition] (state : CQState (Store Var) d) :
    stateMass (state.restrict condition) + stateMass (state.restrict (¬ condition ·)) =
      stateMass state := by
  rw [stateMass, stateMass, stateMass]
  exact (ENNReal.coe_add _ _).symm.trans
    (congrArg _ (state.trace_restrict_add_trace_restrict_not condition))

theorem stateMass_restrict_le {Var : Type} {d : ℕ}
    (condition : Store Var → Prop) [DecidablePred condition] (state : CQState (Store Var) d) :
    stateMass (state.restrict condition) ≤ stateMass state :=
  stateMass_mono (state.restrict_le condition)

@[simp]
theorem stateMass_assign {Var : Type} [DecidableEq Var] {d : ℕ}
    (Δ : CQState (Store Var) d) (x : Var) (e : Expr Var) :
    stateMass (Δ.assign x e) = stateMass Δ :=
  congrArg ENNReal.ofNNReal (CQState.trace_assign x e Δ)

@[simp]
theorem stateMass_qAssign {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) (unitary : Unitary d) :
    stateMass (Δ.qAssign unitary) = stateMass Δ :=
  congrArg ENNReal.ofNNReal (CQState.trace_qAssign unitary Δ)

@[simp]
theorem stateMass_qSet {Var : Type} {d : ℕ} [NeZero d] (Δ : CQState (Store Var) d) :
    stateMass Δ.qSet = stateMass Δ :=
  congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)

@[simp]
theorem stateMass_qMeasurement {Var : Type} [DecidableEq Var] {d outcomes : ℕ}
    (Δ : CQState (Store Var) d) (x : Var) (measurement : CompleteMeasurement d outcomes) :
    stateMass (Δ.qMeasurement x measurement.toMeasurement) = stateMass Δ :=
  congrArg ENNReal.ofNNReal (CQState.trace_qMeasurement_of_complete x measurement Δ)

theorem antitone_stateMass_activeIter {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (state : CQState (Store Var) d) :
    Antitone fun n ↦ stateMass (activeIter guard body n state) :=
  fun _ _ h ↦ ENNReal.coe_le_coe.mpr (antitone_trace_activeIter guard body state h)

theorem stateMass_whileRec_succ {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (n : ℕ) (state : CQState (Store Var) d) :
    stateMass ((QMonad.Q.whileRec (interp body) guard (n + 1)).toStateFun state) =
      stateMass ((QMonad.Q.whileRec (interp body) guard n).toStateFun
          ((interp body).toStateFun (state.restrict guard))) +
        stateMass (state.restrict (¬ guard ·)) := by
  rw [stateMass, stateMass, stateMass, ← ENNReal.coe_add]
  exact congrArg ENNReal.ofNNReal (trace_whileRec_succ guard body n state)

theorem stateMass_eq_whileRec_add_activeIter {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard]
    {body : QProg Var d} (hbody : Lossless body) (n : ℕ) (state : CQState (Store Var) d) :
    stateMass state =
      stateMass ((QMonad.Q.whileRec (interp body) guard (n + 1)).toStateFun state) +
        stateMass (activeIter guard body n state) := by
  rw [stateMass, stateMass, stateMass, ← ENNReal.coe_add]
  exact congrArg ENNReal.ofNNReal (trace_eq_whileRec_add_activeIter guard hbody n state)

theorem stateMass_qWhile_of_tendsto_zero {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} (hbody : Lossless body) {state : CQState (Store Var) d}
    (htendsto : Filter.Tendsto (fun n ↦ stateMass (activeIter guard body n state))
      Filter.atTop (nhds 0)) :
    stateMass ((interp (.qWhile guard body)).toStateFun state) = stateMass state :=
  congrArg ENNReal.ofNNReal <| trace_qWhile_of_tendsto_zero hbody <|
    ENNReal.tendsto_coe.mp (by simpa [stateMass] using htendsto)

theorem stateMass_qWhile_of_expectedIterations_ne_top {Var : Type} [DecidableEq Var] {d : ℕ}
    [NeZero d] {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d}
    (hbody : Lossless body) {state : CQState (Store Var) d} (h : expectedIterations guard body state
      ≠ ⊤) :
    stateMass ((interp (.qWhile guard body)).toStateFun state) = stateMass state :=
  congrArg ENNReal.ofNNReal (trace_qWhile_of_expectedIterations_ne_top hbody h)

theorem ofReal_expect_whileActiveWP {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (n : ℕ) (state : CQState (Store Var) d) :
    ENNReal.ofReal 𝔼[state ⊨ whileActiveWP (wp body) guard n] =
      stateMass (activeIter guard body n state) := by
  rw [expect_whileActiveWP, ENNReal.ofReal_coe_nnreal]

theorem stateMass_restrict_assign {Var : Type} [DecidableEq Var] {d : ℕ}
    {guard : Store Var → Prop} [DecidablePred guard] {x : Var} {e : Expr Var}
    (h : ∀ store, guard (Store.subst store x e)) (state : CQState (Store Var) d) :
    stateMass ((state.assign x e).restrict guard) = stateMass state := by
  simp [CQState.restrict_assign, h]

theorem stateMass_restrict_interp_of_wp_eq {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d}
    {p : ℝ≥0} (hp : p ≤ 1) (hbody : Lossless body)
    (hwp : wp body (fun store ↦ ⌜¬ guard store⌝) = constAssertion p)
    (state : CQState (Store Var) d) :
    stateMass (((interp body).toStateFun state).restrict guard) = (1 - p) * stateMass state := by
  rw [stateMass, stateMass, ← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_mul]
  exact congrArg ENNReal.ofNNReal (trace_restrict_interp_of_wp_eq hp hbody hwp state)

@[simp high]
theorem cqWhileRecCostSuc {Var : Type} {d : ℕ}
    (bodyCost : CQState (Store Var) d → ℝ≥0∞) (bodySem : CQState (Store Var) d → CQState (Store Var)
      d)
    (condition : Store Var → Prop) [DecidablePred condition] (n : ℕ)
    (state : CQState (Store Var) d) :
    whileRecCost bodyCost bodySem condition (n + 1) state =
      bodyCost (state.cqTrueSt condition) +
        whileRecCost bodyCost bodySem condition n
          (bodySem (state.cqTrueSt condition)) := rfl

@[simp high]
theorem cqExpectedCostIf {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (model : CostModel d) (condition : Store Var → Prop) [DecidablePred condition]
    (yes no : QProg Var d) (state : CQState (Store Var) d) :
    expectedCost model (.qIf condition yes no) state =
      expectedCost model yes (state.cqTrueSt condition) +
        expectedCost model no (state.cqFalseSt condition) :=
  (expectedCost_qIf model condition yes no state).trans <|
    congrArg₂ (· + ·)
      (congrArg (expectedCost model yes)
        (Subtype.ext (funext fun σ ↦ by by_cases h : condition σ <;> simp [CQState.cqTrueSt, h])))
      (congrArg (expectedCost model no)
        (Subtype.ext (funext fun σ ↦ by by_cases h : condition σ <;> simp [CQState.cqFalseSt, h])))

theorem stateMass_cqTrue_cqFalse_split {Var : Type} {d : ℕ}
    (condition : Store Var → Prop) [DecidablePred condition] (state : CQState (Store Var) d) :
    stateMass (state.cqTrueSt condition) + stateMass (state.cqFalseSt condition) =
      stateMass state := by
  rw [stateMass, stateMass, stateMass]
  exact (ENNReal.coe_add _ _).symm.trans
    (congrArg _ (state.trace_cqTrueSt_add_trace_cqFalseSt condition))

theorem stateMass_cqTrueSt_le {Var : Type} {d : ℕ}
    (condition : Store Var → Prop) [DecidablePred condition] (state : CQState (Store Var) d) :
    stateMass (state.cqTrueSt condition) ≤ stateMass state :=
  le_self_add.trans_eq (stateMass_cqTrue_cqFalse_split condition state)

@[simp high]
theorem cqActiveIter_z {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d)
    (state : CQState (Store Var) d) :
    activeIter guard body 0 state = state.cqTrueSt guard := rfl

theorem cqActiveIterSuc {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d) (n : ℕ)
    (state : CQState (Store Var) d) :
    activeIter guard body (n + 1) state =
      activeIter guard body n ((interp body).toStateFun (state.cqTrueSt guard)) := rfl

theorem cqActiveIterSuc' {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d) (n : ℕ)
    (state : CQState (Store Var) d) :
    activeIter guard body (n + 1) state =
      ((interp body).toStateFun (activeIter guard body n state)).cqTrueSt guard :=
  Function.iterate_succ_apply' _ _ _

theorem cqStateMass_whileRecSuc {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d) (n : ℕ)
    (state : CQState (Store Var) d) :
    stateMass ((QMonad.Q.whileRec (interp body) guard (n + 1)).toStateFun state) =
      stateMass ((QMonad.Q.whileRec (interp body) guard n).toStateFun
          ((interp body).toStateFun (state.cqTrueSt guard))) +
        stateMass (state.cqFalseSt guard) :=
  (stateMass_whileRec_succ guard body n state).trans <|
    congrArg₂ (· + ·)
      (congrArg (fun x ↦ stateMass ((QMonad.Q.whileRec (interp body) guard n).toStateFun
          ((interp body).toStateFun x)))
        (Subtype.ext (funext fun σ ↦ by by_cases h : guard σ <;> simp [CQState.cqTrueSt, h])))
      (congrArg stateMass
        (Subtype.ext (funext fun σ ↦ by by_cases h : guard σ <;> simp [CQState.cqFalseSt, h])))

theorem stateMass_cqTrueSt_assign {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {guard : Store Var → Prop} [DecidablePred guard] {x : Var} {e : Expr Var}
    (h : ∀ store, guard (Store.subst store x e)) (state : CQState (Store Var) d) :
    stateMass ((state.assign x e).cqTrueSt guard) = stateMass state := by
  rw [← cqActiveIter_z guard .skip, ← ofReal_expect_whileActiveWP, expect_assign,
    ← ofReal_expect_top state]
  refine congrArg ENNReal.ofReal (congrArg (expect state) ?_)
  funext store
  simp [CQAssertion.subst, whileActiveWP, h store]

theorem cqExpectedIters_eq_geometric {Var : Type} [DecidableEq Var] {d : ℕ}
    [NeZero d] {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d}
    {state : CQState (Store Var) d} {q : ℝ≥0∞}
    (h : ∀ n, stateMass (activeIter guard body (n + 1) state) =
      q * stateMass (activeIter guard body n state)) :
    expectedIterations guard body state =
      stateMass (state.cqTrueSt guard) * (1 - q)⁻¹ :=
  expectedIterations_eq_geometric h

theorem stateMass_cqTrueSt_interp_of_wp_eq {Var : Type} [DecidableEq Var] {d : ℕ}
    [NeZero d] {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d}
    {p : ℝ≥0} (hp : p ≤ 1) (hbody : Lossless body)
    (hwp : wp body (liftPureProp (fun store ↦ ¬ guard store)) = constAssertion p)
    (state : CQState (Store Var) d) :
    stateMass (((interp body).toStateFun state).cqTrueSt guard) =
      (1 - p) * stateMass state := by
  set output := (interp body).toStateFun state
  have hnot :
      liftPureProp (d := d) (fun store ↦ ¬ guard store) = fun store ↦
        if guard store then (⊥ : CQAssertion (Store Var) d) store
        else (⊤ : CQAssertion (Store Var) d) store := by
    funext store
    by_cases h : guard store <;> simp [h]
  have hexit : stateMass (output.cqFalseSt guard) = p * stateMass state := by
    have h := wp_expectation_eq body state (liftPureProp fun store ↦ ¬ guard store)
    rw [hwp, expect_constAssertion p state ⟨p.2, by exact_mod_cast hp⟩,
      hnot, cqExpect_ite_split, expect_bot, zero_add, expect_top] at h
    rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul p.coe_nonneg]
    exact congrArg ENNReal.ofReal h.symm
  calc
    stateMass (output.cqTrueSt guard) =
        stateMass output - stateMass (output.cqFalseSt guard) :=
      ENNReal.eq_sub_of_add_eq (stateMass_ne_top _)
        (stateMass_cqTrue_cqFalse_split guard output)
    _ = stateMass state - p * stateMass state := by rw [hbody.stateMass_eq, hexit]
    _ = (1 - p) * stateMass state := by
      rw [ENNReal.sub_mul fun _ _ ↦ stateMass_ne_top state, one_mul]

theorem cqExpectedIters_eq_of_wp_eq {Var : Type} [DecidableEq Var] {d : ℕ}
    [NeZero d] {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d}
    {p : ℝ≥0} (hp : p ≤ 1) (hbody : Lossless body)
    (hwp : wp body (liftPureProp (fun store ↦ ¬ guard store)) = constAssertion p)
    (state : CQState (Store Var) d) :
    expectedIterations guard body state =
      stateMass (state.cqTrueSt guard) * (p : ℝ≥0∞)⁻¹ := by
  rw [cqExpectedIters_eq_geometric (q := 1 - p) fun n ↦ by
      rw [cqActiveIterSuc']
      exact stateMass_cqTrueSt_interp_of_wp_eq hp hbody hwp _,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (by exact_mod_cast hp)]

end ResourceCounting

end QHLBridgeAux

open scoped Matrix in
open Operator QProg in
/-- Root-level `wp` of `measureRegister`. -/
theorem wp_measureRegister_coe_ax {Var : Type} [DecidableEq Var] {n k : ℕ}
    (res : Var) (r : QRegister k n) (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) :
    (wp (measureRegister res r) Θ σ).1 =
      ∑ o : Fin (2 ^ k),
        HermitianMat.conj (r.basisOutcomeProjector o)ᴴ
          (Θ (Store.subst σ res ↑o.val)).1 :=
  rfl

namespace QRegister

open Operator in
/-- Computational-basis `Measurement` on `r`. -/
noncomputable abbrev regBasisMeas {k n : ℕ} (r : QRegister k n) :
    Measurement (2 ^ n) (2 ^ k) :=
  (r.computationalBasisMeasurement : Measurement (2 ^ n) (2 ^ k))

end QRegister
