module

public import Track2Weak.WeakAssembly
public import Track2Weak.WeakCertBudget
public import Track2Grover.Engine.FindAllJohnsonAltStep

/-! Finite size routing and normalization for the 1024-slot, 512-target independent restart
construction. The physical one-attempt contract is an explicit hypothesis. -/

@[expose] public section
namespace Track2Weak

open Operator ResourceCounting QProg.Notation Real QuantumComputation.Specs.DickeSol
open scoped ENNReal NNReal NNRat QHLExpectation

variable {Var : Type} [DecidableEq Var]

def retryGuard (res : Var) (n : ℕ) (σ : Store Var) : Prop :=
  σ res = (2 ^ (512 * n) : ℕ)

instance (res : Var) (n : ℕ) : DecidablePred (retryGuard res n) := fun σ ↦
  inferInstanceAs (Decidable (σ res = ((2 ^ (512 * n) : ℕ) : ℤ)))

abbrev BatchCirc (Var : Type) (q n : ℕ) :=
  OracleDynamicCircuit (Unitary (2 ^ q)) Var q ((n + 1) * 1024)

/-- Use an exact Stage1 circuit below the cutoff. Above it, rerun the measured full
attempt after the sentinel. The maximum number of qubits may depend on the branch. -/
noncomputable def routedBatch (res : Var) (q : ℕ → ℕ) (cutoff : ℕ)
    (A : (n : ℕ) → BatchCirc Var (q n) n) (n : ℕ) : Σ w : ℕ, BatchCirc Var w n :=
  if cutoff ≤ n then ⟨q n, restartCircuit (retryGuard res n) (A n)⟩
  else ⟨Stage1.qubits n 1024 512, Stage1.circuit res n 1024 512⟩

/-- Physical meaning required of the *same* oracle-independent attempt for every target set.
The two scalar inequalities are in unnormalized expected parallel oracle rounds. -/
structure BatchBound (res : Var) (q : ℕ → ℕ) (cutoff : ℕ)
    (A : (n : ℕ) → BatchCirc Var (q n) n) (C : ℝ) : Prop where
  perSet : ∀ n, cutoff ≤ n → ∀ S ∈ groverTargetSets n 512, ∃ p T : ℝ≥0,
    AttemptBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
      ((A n).compile QProg.qAssign (groverParallelMarkingOracle 1024 S))
      (retryGuard res n) (fun σ ↦ decodeTargets n 512 (σ res) = S) p T ∧
    (Cert.success12 : ℝ) / 10^12 ≤ p ∧
    (T : ℝ) ≤ (Cert.weightedCost21 : ℝ) / 10^21 * √((2 : ℝ)^n) + C

variable {res : Var} {q : ℕ → ℕ} {cutoff : ℕ} {A : (n : ℕ) → BatchCirc Var (q n) n}
  {C : ℝ}

theorem routedBatch_correctness (H : BatchBound res q cutoff A C) {n : ℕ}
    (hn : 1 ≤ n) (hk : 512 ≤ 2^n) {S : Finset (Fin (2^n))} (hS : S ∈ groverTargetSets n 512) :
    ⦃ ⊤ ⦄ (qset ;; (routedBatch res q cutoff A n).2.compile QProg.qAssign
      (groverParallelMarkingOracle 1024 S)) ⦃ fun σ ↦ ⌜decodeTargets n 512 (σ res) = S⌝ ⦄ := by
  by_cases h : cutoff ≤ n
  · obtain ⟨p,T,hA,_,_⟩ := H.perSet n h S hS
    rw [show routedBatch res q cutoff A n = ⟨q n, restartCircuit (retryGuard res n) (A n)⟩
      from ite_eq_left h]
    intro Δ
    simpa only [restartCircuit, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_qWhile,
      expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet,
      QMonad.Q.toStateFun_qSet, CQState.trace_qSet] using restart_correct hA Δ.qSet
  · rw [show routedBatch res q cutoff A n =
      ⟨Stage1.qubits n 1024 512, Stage1.circuit res n 1024 512⟩ from ite_eq_right h]
    exact Stage1.correctness (m := 1024) res hn (by decide +kernel) hk hS

/-- Positive slack between the finite-attempt certificate and the public ratio absorbs
any fixed additive number of oracle rounds per attempt. -/
theorem normalized_batch_cost (C : ℝ) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p T : ℝ≥0,
    (Cert.success12 : ℝ) / 10^12 ≤ p →
    (T : ℝ) ≤ (Cert.weightedCost21 : ℝ) / 10^21 * √((2 : ℝ)^n) + C →
    ((T / p : ℝ≥0) : ℝ) ≤ (NNRat.divNat 26768771052 1000000000000 : ℝ) *
      vanillaFindAllCost n 1024 512 := by
  have hnorm := checkAltBound12_sound (by decide : 1 ≤ 1024)
    (show checkAltBound12 1024 512 28787685101031 26768771052 1000000000000 = true by
      decide +kernel)
  have hv : wdScaleR = 10^15 := by norm_num [wdScaleR, wdScale]
  rw [hv] at hnorm
  refine ⟨Nat.ceil ((10^16 * max C 0)^2), ?_⟩
  intro n hn p T hp ht
  have hN : 10^16 * max C 0 ≤ √((2 : ℝ)^n) := by
    apply Real.le_sqrt_of_sq_le
    exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr hn).trans (by exact_mod_cast n.lt_two_pow_self.le))
  have hg := le_max_left C 0
  have hC : C ≤ √((2 : ℝ)^n) / 10^16 := by linarith
  rw [Cert.weightedCost21] at ht
  rw [Cert.success12] at hp
  norm_num1 at ht hp
  have hpos : (0 : ℝ) < p := by linarith
  have hroot : 0 ≤ √((2 : ℝ)^n) := Real.sqrt_nonneg _
  rw [NNReal.coe_div]
  calc (T : ℝ) / p ≤ (28787685101031 / 10^15) * √((2 : ℝ)^n) := by
        apply (div_le_iff₀ hpos).mpr
        have hprod := mul_le_mul_of_nonneg_left hp
          (show 0 ≤ (28787685101031 / 10^15) * √((2 : ℝ)^n) by positivity)
        linarith
    _ ≤ ((NNRat.divNat 26768771052 1000000000000 : ℝ) * (π/4) *
          groverHarmonicSqrtSum 512 / √(1024:ℝ)) * √((2 : ℝ)^n) := by
        exact mul_le_mul_of_nonneg_right hnorm hroot
    _ = _ := by
        unfold vanillaFindAllCost
        rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2^n)]
        ring

theorem routedBatch_rel_cost (H : BatchBound res q cutoff A C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 512 ≤ 2 ^ n →
      AvgOracleCostBound 512
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
        (fun S ↦ qset ;; (routedBatch res q cutoff A n).2.compile QProg.qAssign
          (groverParallelMarkingOracle 1024 S))
        ((NNRat.divNat 26768771052 1000000000000 : ℝ) * vanillaFindAllCost n 1024 512) := by
  obtain ⟨N,hN⟩ := normalized_batch_cost C
  refine ⟨max N cutoff, fun n hn hk ↦ ?_⟩
  have hcut := (le_max_right N cutoff).trans hn
  let cap := (NNRat.divNat 26768771052 1000000000000 : ℝ) * vanillaFindAllCost n 1024 512
  have hnn : 0 ≤ cap := by
    dsimp [cap,vanillaFindAllCost,groverHarmonicSqrtSum]
    positivity
  rw [show routedBatch res q cutoff A n = ⟨q n, restartCircuit (retryGuard res n) (A n)⟩
    from ite_eq_left hcut]
  refine ⟨fun _ ↦ cap.toNNReal, ?_, ?_⟩
  · intro S hS
    obtain ⟨p,T,ha,hp,ht⟩ := H.perSet n hcut S hS
    have hq := hN n ((le_max_left N cutoff).trans hn) p T hp ht
    have hle : T / p ≤ cap.toNNReal := by
      exact_mod_cast hq.trans_eq (Real.coe_toNNReal cap hnn).symm
    have hreset : CostBound (CostModel.ofEmbeddedOracle (n := q n) (groverParallelMarkingOracle 1024 S))
        (QProg.qSet : QProg Var (2^(q n))) 0 := by intro Δ; simp
    simpa [restartCircuit] using hreset.seq ((restart_cost ha).mono hle)
  · have hcard : (0:ℝ) < (groverTargetSets n 512).card := by
      rw [show (groverTargetSets n 512).card = Nat.choose (2^n) 512 by simp [groverTargetSets]]
      exact_mod_cast Nat.choose_pos hk
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard.ne',
      Real.coe_toNNReal cap hnn]

end Track2Weak

#print axioms Track2Weak.routedBatch_correctness
#print axioms Track2Weak.normalized_batch_cost
#print axioms Track2Weak.routedBatch_rel_cost
