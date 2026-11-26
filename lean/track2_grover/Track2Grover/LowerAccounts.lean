import QuantumComputationSpecs.Algorithms.Grover
import Track2Grover.LowerPotential
import Track2Grover.LowerQueryCost

/-! # Conditional FindAny lower bound

This intermediate route assumes a transcript grouped by query count and derives its
lower bound. The unconditional proof in Track2Grover.UniversalFindAny uses a finite
measurement tree and cofinal loop unrollings. Both use the frozen expected cost of one
common source circuit compiled at each possible hidden input. -/
namespace Track2Grover.Lower
open Real Filter Operator ResourceCounting QuantumComputation.Specs
open scoped Topology BigOperators NNReal NNRat

abbrev Circuit (n m w : ℕ) :=
  OracleDynamicCircuit (Unitary (2^w)) Grover.Var w ((n+1)*m)

open QProg.Notation in
noncomputable def program {n m w : ℕ} (C : Circuit n m w) (S : Finset (Fin (2^n))) :
    QProg Grover.Var (2^w) :=
  qset ;; C.compile QProg.qAssign (groverParallelMarkingOracle m S)

def Correct {n m w : ℕ} (C : Circuit n m w) (k : ℕ) : Prop :=
  ∀ S ∈ groverTargetSets n k, ⦃ ⊤ ⦄ program C S
    ⦃ fun σ ↦ ⌜∃ x ∈ S, σ Grover.Var.res = x.val⌝ ⦄

def AvgBound {n m w : ℕ} (C : Circuit n m w) (k : ℕ) (q : ℝ) : Prop :=
  AvgOracleCostBound k (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
    (program C) q

def witnessStore {n : ℕ} (S : Finset (Fin (2^n))) (σ : Store Grover.Var) : Prop :=
  ∃ x ∈ S, σ Grover.Var.res = x.val

noncomputable instance {n : ℕ} (S : Finset (Fin (2^n))) : DecidablePred (witnessStore S) :=
  Classical.decPred _

/-- Exact Hoare correctness simultaneously gives conservation of total trace and zero
total weight on the classical output stores reporting an incorrect address. -/
theorem correct_output_mass {n m w k : ℕ} {C : Circuit n m w} (hc : Correct C k)
    {S : Finset (Fin (2^n))} (hS : S ∈ groverTargetSets n k)
    (Δ : CQState (Store Grover.Var) (2^w)) :
    let out := (interp (program C S)).toStateFun Δ
    out.trace = Δ.trace ∧ (out.restrict (fun σ => ¬witnessStore S σ)).trace = 0 := by
  classical
  let out := (interp (program C S)).toStateFun Δ
  have h := hc S hS Δ
  change expect Δ ⊤ ≤ expect out (fun σ => ⌜witnessStore S σ⌝) at h
  rw [expect_top, expect_ofProp] at h
  have htotal : out.trace ≤ Δ.trace := (interp (program C S)).trace_toStateFun_le Δ
  have hgood : Δ.trace ≤ (out.restrict (witnessStore S)).trace := by exact_mod_cast h
  have htotal' : out.trace = Δ.trace :=
    le_antisymm htotal (hgood.trans (out.trace_restrict_le _))
  refine ⟨htotal', ?_⟩
  have hp := out.trace_restrict_add_trace_restrict_not (witnessStore S)
  rw [htotal'] at hp
  change (out.restrict (fun σ => ¬witnessStore S σ)).trace = 0
  exact (add_eq_left.mp (le_antisymm (hp.le.trans hgood) (by simp)))

theorem explicit_query_cost {n m w : ℕ} (reg : QRegister ((n+1)*m) w)
    (S : Finset (Fin (2^n))) (Δ : CQState (Store Grover.Var) (2^w)) :
    expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
      ((OracleDynamicCircuit.oracle reg : Circuit n m w).compile QProg.qAssign
        (groverParallelMarkingOracle m S)) Δ = Δ.trace := by
  simp [CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary]

/-- An account of live branches grouped by query count. Hidden-uniform and complementary
mass equal survival times cos²(angle) and survival times (1−cos²(angle)), respectively. -/
structure TranscriptAccount {n m w : ℕ} (C : Circuit n m w) (k : ℕ) where
  initial : CQState (Store Grover.Var) (2^w)
  initial_trace : initial.trace = 1
  survival : ℕ → ℝ
  beforeAngle : ℕ → ℝ
  afterAngle : ℕ → ℝ
  survival_init : survival 0 = 1
  angle_init : beforeAngle 0 = 0
  nonneg : ∀ t, 0 ≤ survival t
  before_range : ∀ t, beforeAngle t ∈ Set.Icc 0 (π/2)
  after_range : ∀ t, afterAngle t ∈ Set.Icc 0 (π/2)
  angle_step : ∀ t, |beforeAngle t-afterAngle t| ≤ 2*arcsin (√((m:ℝ)*k/2^n))
  parallel_drop : ∀ t, survival (t+1)*cos (beforeAngle (t+1))^2 ≤ survival t*cos (afterAngle t)^2
  perp_drop : ∀ t, survival (t+1)*(1-cos (beforeAngle (t+1))^2) ≤
    survival t*(1-cos (afterAngle t)^2)
  stop_budget : ∀ T, ∑ t ∈ Finset.range T,
    (survival t*cos (afterAngle t)^2 - survival (t+1)*cos (beforeAngle (t+1))^2) ≤ k/(2:ℝ)^n
  terminates : Tendsto survival atTop (𝓝 0)
  cost_budget : ∀ T, ((groverTargetSets n k).card:ℝ) * (∑ t ∈ Finset.range T, survival t) ≤
    ∑ S ∈ groverTargetSets n k, (syntacticCost (groverParallelMarkingOracle m S) C
      ((interp .qSet).toStateFun initial)).toReal

/-- The explicit remaining semantic obligation for an arbitrary adaptive circuit. -/
def RealizesTranscript {n m w : ℕ} (C : Circuit n m w) (k : ℕ) : Prop :=
  Correct C k → Nonempty (TranscriptAccount C k)

private theorem profile_range {a : ℝ} (ha : 0 ≤ a) : 0 ≤ profile a ∧ profile a ≤ c := by
  unfold profile
  split_ifs with h
  · unfold c
    constructor <;> linarith
  · refine ⟨sq_nonneg _, ?_⟩
    unfold c
    nlinarith [sin_sq_add_cos_sq a, sq_nonneg (sin a), two_le_pi]

theorem finite_of_account {n m w k : ℕ} {C : Circuit n m w} (A : TranscriptAccount C k)
    {q : ℝ} (hcost : AvgBound C k q) (hm : 0 < m) (hk : 0 < k) (hkN : k ≤ 2^n) :
    finiteBound n m k ≤ q := by
  have hv : 0 < 2*arcsin (√((m:ℝ)*k/2^n)) := by
    apply mul_pos (by norm_num)
    apply arcsin_pos.mpr
    positivity
  let V (t : ℕ) := A.survival t * profile (A.beforeAngle t)
  let D (t : ℕ) := A.survival t * cos (A.afterAngle t)^2 -
    A.survival (t+1) * cos (A.beforeAngle (t+1))^2
  apply limit_accounting V A.survival D _ q _ hv
  · simp [V, A.survival_init, A.angle_init, profile, show (0:ℝ) ≤ π/4 by positivity]
  · intro t
    have hq := query_loss (A.nonneg t) (A.angle_step t)
    have hs := stopping_loss (A.nonneg t) (A.nonneg (t+1))
      (A.after_range t).1 (A.after_range t).2 (A.before_range (t+1)).1 (A.before_range (t+1)).2
      (A.parallel_drop t) (A.perp_drop t)
    dsimp [V,D]
    linarith
  · apply squeeze_zero (fun t => mul_nonneg (A.nonneg t) (profile_range (A.before_range t).1).1)
      (fun t => mul_le_mul_of_nonneg_left (profile_range (A.before_range t).1).2 (A.nonneg t))
    simpa using A.terminates.mul_const c
  · obtain ⟨b, hb, hbmean⟩ := hcost
    have hcard : 0 < (groverTargetSets n k).card := Finset.card_pos.mpr (by
      apply Finset.powersetCard_nonempty_of_le
      simpa using hkN)
    intro T
    apply le_trans _ hbmean
    apply (le_div_iff₀ (by exact_mod_cast hcard)).2
    rw [mul_comm]
    refine (A.cost_budget T).trans (Finset.sum_le_sum fun S hS => ?_)
    have h := hb S hS A.initial
    simp only [A.initial_trace, ENNReal.coe_one, one_mul] at h
    have hh := syntacticCost_le_expected (groverParallelMarkingOracle m S) C
      ((interp .qSet).toStateFun A.initial)
    simp only [program, expectedCost_qSeq, expectedCost_qSet, CostModel.ofEmbeddedOracle,
      Nat.cast_zero, mul_zero, zero_add] at h
    exact ENNReal.toReal_mono ENNReal.coe_ne_top (hh.trans h)
  · exact A.stop_budget

/-- Full target density is an unconditional edge case. A correct circuit can stop without
querying at all, so its first-query survival need not equal one. -/
theorem full_density {n m w : ℕ} {C : Circuit n m w} {q : ℝ}
    (hcost : AvgBound C (2^n) q) : finiteBound n m (2^n) ≤ q := by
  obtain ⟨b, _, hb⟩ := hcost
  have hq : 0 ≤ q := le_trans (by positivity) hb
  simpa [finiteBound] using hq

/-- A matching conditional asymptotic theorem for the frozen notion of an eventual
relative cost bound. Only sparse instances are required by the semantic hypothesis. -/
theorem asymptotic_of_realization {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (w : ℕ → ℕ) (C : ∀ n, Circuit n m (w n)) (R : ℚ≥0)
    (correct : ∀ n, 1 ≤ n → k ≤ 2^n → Correct (C n) k)
    (realize : ∀ n, 1 ≤ n → 2*m*k < 2^n → k ≤ 2^n → RealizesTranscript (C n) k)
    (hupper : ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2^n → AvgBound (C n) k (R * vanillaFindAnyCost n m k)) :
    (1/2 + 1/π : ℝ) ≤ R := by
  obtain ⟨n₀, hupper⟩ := hupper
  apply le_of_tendsto (tendsto_ratio m k hm hk)
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop 1,
    eventually_ge_atTop (2*m*k), eventually_ge_atTop k] with n hn hn1 hnm hnk
  have hp := Nat.lt_two_pow_self (n := n)
  have hkN : k ≤ 2^n := by omega
  obtain ⟨A⟩ := realize n hn1 (by omega) hkN (correct n hn1 hkN)
  have hfin := finite_of_account A (hupper n hn hkN) hm hk hkN
  apply (div_le_iff₀ (by positivity)).2
  exact hfin

#print axioms explicit_query_cost
#print axioms correct_output_mass
#print axioms finite_of_account
#print axioms full_density
#print axioms asymptotic_of_realization
end Track2Grover.Lower
