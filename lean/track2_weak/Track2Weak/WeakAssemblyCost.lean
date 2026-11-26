module

public import Track2Weak.WeakWalkFilter
import all Track2Grover.Engine.WeakDickeCore
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

/-! Expected oracle cost of a stopped chain, computed on its actual no-click trajectory. -/
@[expose] public section
namespace QuantumComputation.Specs.DickeSol

open Operator ResourceCounting QProg.Notation Matrix
open scoped Matrix NNReal QHLExpectation

def stoppedChain {Var I : Type} (res : Var) {d : ℕ}
    (stage : I → QProg Var d) (finish : QProg Var d) : List I → QProg Var d
  | [] => finish
  | i :: rest => stage i ;; .qIf (fun σ ↦ σ res = 1) finish (stoppedChain res stage finish rest)

noncomputable def workMass {W : ℕ} (v : Fin (2^W) → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

theorem workMass_lift_orbit {n m : ℕ} {S : Finset (Fin (2^n))}
    (h : m + S.card ≤ 2^n) (x : Fin (orbDim m S.card) → ℝ) :
    workMass (liftSymVec n m (orbEmbedGen (2^n) m S x)) = vecSqNorm x := by
  let y := orbEmbedGen (2^n) m S x
  let J := symInjMat n m
  have hJ : Jᵀ * J = 1 := symInjMat_transpose_mul_self n m
  have hy : (J *ᵥ y) ⬝ᵥ (J *ᵥ y) = y ⬝ᵥ y := by
    rw [← dotProduct_transpose_mulVec, mulVec_mulVec, hJ, one_mulVec]
  calc workMass (liftSymVec n m y) = (J *ᵥ y) ⬝ᵥ (J *ᵥ y) := by
        simp [workMass, liftSymVec, J, dotProduct, Complex.normSq_ofReal, sq]
    _ = _ := hy.trans (by simpa [vecSqNorm, dotProduct, y, sq] using dot_orbEmbedGen h x x)

def stoppedMax {I : Type} (price : I → ℕ) (readPrice : ℕ) : List I → ℕ
  | [] => readPrice
  | i :: rest => price i + stoppedMax price readPrice rest

theorem stoppedMax_ge_read {I : Type} (price : I → ℕ) (readPrice : ℕ) (rows : List I) :
    readPrice ≤ stoppedMax price readPrice rows := by
  induction rows with
  | nil => exact le_rfl
  | cons i rows ih => exact ih.trans (Nat.le_add_left _ _)

noncomputable def stoppedTime {X I : Type} {W : ℕ}
    (rep : X → Fin (2^W) → ℂ) (keep : I → X → X) (hit : I → X → Fin (2^W) → ℂ)
    (price : I → ℕ) (readPrice : ℕ) : List I → X → ℝ
  | [], x => readPrice * workMass (rep x)
  | i :: rows, x => price i * workMass (rep x) + readPrice * workMass (hit i x) +
      stoppedTime rep keep hit price readPrice rows (keep i x)

private theorem weak_const_quad {Var : Type} {W M : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (σ : Store Var) (v : Fin (2^W) → ℂ) (μ : Fin (2^M)) :
    rmsVecQuad ((constAssertion t : CQAssertion (Store Var) (2^(W+M))) σ).1.1
      (workMemState v (Pi.single μ 1)) = ((t * workMass v : ℝ) : ℂ) := by
  simpa [workMass, rmsVecQuad, quadForm] using quadForm_constAssertion_workMemState ht ht' σ v μ

/-- A measured step enters its tail only on the no-click branch. Each segment cost is weighted
by the surviving input norm. Click and exhausted-list readouts also pay their own cost. -/
theorem stoppedChain_scaled {Var I X : Type} [DecidableEq Var] {W M : ℕ}
    (res : Var) (model : CostModel (2^(W+M)))
    (stage : I → QProg Var (2^(W+M))) (finish : QProg Var (2^(W+M)))
    (price : I → ℕ) (readPrice : ℕ) (rep : X → Fin (2^W) → ℂ)
    (keep : I → X → X) (hit : I → X → Fin (2^W) → ℂ) (μ₀ μ₁ : Fin (2^M))
    (hc : ∀ i, CostBound model (stage i) (price i)) (hr : CostBound model finish readPrice)
    (hs : ∀ i x (θ : CQAssertion (Store Var) (2^(W+M))) σ,
      rmsVecQuad ((wp (stage i) θ) σ).1.1 (workMemState (rep x) (Pi.single μ₀ 1)) =
      rmsVecQuad (θ (σ.subst res 0)).1.1 (workMemState (rep (keep i x)) (Pi.single μ₀ 1)) +
      rmsVecQuad (θ (σ.subst res 1)).1.1 (workMemState (hit i x) (Pi.single μ₁ 1)))
    (rows : List I) {B : ℝ} (hB : 0 < B) (hmax : stoppedMax price readPrice rows ≤ B) :
    ∃ θ, ScaledCostRel model B (stoppedChain res stage finish rows) θ
        (stoppedMax price readPrice rows) ∧
      ∀ x σ, rmsVecQuad (θ σ).1.1 (workMemState (rep x) (Pi.single μ₀ 1)) =
        ((stoppedTime rep keep hit price readPrice rows x / B : ℝ) : ℂ) := by
  induction rows with
  | nil =>
    have hrB : (readPrice : ℝ) ≤ B := hmax
    refine ⟨_, ScaledCostRel.of_costBound hB hr (by simpa using hrB), ?_⟩
    intro x σ
    rw [weak_const_quad (div_nonneg (by positivity) hB.le) ((div_le_one hB).mpr (by simpa using hrB))]
    simp [stoppedTime]
    ring
  | cons i rows ih =>
    have hsum : (price i : ℝ) + stoppedMax price readPrice rows ≤ B := by
      simpa [stoppedMax] using hmax
    have hrest : (stoppedMax price readPrice rows : ℝ) ≤ B := by
      linarith [show (0:ℝ) ≤ price i by positivity]
    have hprice : (price i : ℝ) ≤ B := by
      linarith [show (0:ℝ) ≤ stoppedMax price readPrice rows by positivity]
    have hread : (readPrice : ℝ) ≤ stoppedMax price readPrice rows := by
      exact_mod_cast stoppedMax_ge_read price readPrice rows
    obtain ⟨tail, htail, hv⟩ := ih hrest
    have hsr := ScaledCostRel.of_costBound hB (hc i) (by simpa using hprice)
    have hfr := ScaledCostRel.of_costBound hB hr (by simpa using hread.trans hrest)
    have hbranch := ScaledCostRel.qIf hB (fun σ ↦ σ res = 1) hfr htail
    have hm : max ((readPrice : ℝ≥0) : ℝ) (stoppedMax price readPrice rows) =
        stoppedMax price readPrice rows := max_eq_right (by simpa using hread)
    rw [hm] at hbranch
    have hsum' : ((price i : ℝ≥0) : ℝ) + stoppedMax price readPrice rows ≤ B := by simpa using hsum
    have hrel := ScaledCostRel.seq hB hsr hbranch hsum'
    refine ⟨_, (by simpa [stoppedChain,stoppedMax] using hrel), ?_⟩
    intro x σ
    change quadForm _ _ = _
    rw [cqAssertion_add_mat,quadForm_add_mat]
    change rmsVecQuad _ _ + rmsVecQuad _ _ = _
    rw [weak_const_quad (div_nonneg (by positivity) hB.le) ((div_le_one hB).mpr (by simpa using hprice)),
      hs]
    rw [ite_eq_right (show (σ.subst res 0) res ≠ 1 by simp [Store.subst]),
      ite_eq_left (show (σ.subst res 1) res = 1 by simp [Store.subst])]
    rw [hv, weak_const_quad (div_nonneg (by positivity) hB.le)
      ((div_le_one hB).mpr (by simpa using hread.trans hrest))]
    simp [stoppedTime]
    ring

end QuantumComputation.Specs.DickeSol

#print axioms QuantumComputation.Specs.DickeSol.stoppedChain_scaled
