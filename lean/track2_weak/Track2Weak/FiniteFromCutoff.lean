module

public import Track2Weak.FindAllWeak
import all Track2Weak.FindAllWeak

@[expose] public section
namespace Track2Weak
open Operator ResourceCounting QProg.Notation Real QuantumComputation.Specs.DickeSol
open scoped ENNReal NNReal NNRat QHLExpectation

/-- The maximal fixed overhead fits in the rounding margin at the physical cutoff. -/
private theorem finite_normalized {n : ℕ} (hn : 80000 ≤ n) {p T : ℝ≥0}
    (hp : (Cert.success12 : ℝ) / 10^12 ≤ p)
    (ht : (T : ℝ) ≤ (Cert.weightedCost21 : ℝ) / 10^21 * √((2:ℝ)^n) + 24673) :
    ((T/p : ℝ≥0):ℝ) ≤ (NNRat.divNat 26768771052 1000000000000 : ℝ) *
      vanillaFindAllCost n 1024 512 := by
  have hnorm := checkAltBound12_sound (by decide : 1 ≤ 1024) Cert.normalized
  change (28787685101031:ℝ) / wdScaleR ≤
    (NNRat.divNat 26768771052 1000000000000 : ℝ) * (π / 4) *
      groverHarmonicSqrtSum 512 / √(1024:ℝ) at hnorm
  rw [show wdScaleR = 10^15 by norm_num [wdScaleR,wdScale]] at hnorm
  have hN : (10^16 * 24673:ℝ) ≤ √((2:ℝ)^n) := by
    apply Real.le_sqrt_of_sq_le
    calc (10^16 * 24673 : ℝ)^2 ≤ (2:ℝ)^140 := by norm_num
         _ ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) (by omega)
  have hC : (24673:ℝ) ≤ √((2:ℝ)^n) / 10^16 := by linarith
  rw [Cert.weightedCost21] at ht
  rw [Cert.success12] at hp
  norm_num1 at ht hp
  have hpos : (0 : ℝ) < p := by linarith
  have hroot : 0 ≤ √((2:ℝ)^n) := Real.sqrt_nonneg _
  rw [NNReal.coe_div]
  calc (T:ℝ) / p ≤ (28787685101031 / 10^15) * √((2:ℝ)^n) := by
         apply (div_le_iff₀ hpos).mpr
         have hprod := mul_le_mul_of_nonneg_left hp
           (show 0 ≤ (28787685101031 / 10^15) * √((2:ℝ)^n) by positivity)
         linarith
       _ ≤ ((NNRat.divNat 26768771052 1000000000000 : ℝ) * (π/4) *
           groverHarmonicSqrtSum 512 / √(1024:ℝ)) * √((2:ℝ)^n) :=
         mul_le_mul_of_nonneg_right hnorm hroot
       _ = _ := by
         unfold vanillaFindAllCost
         rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ 2^n)]
         ring

private theorem finite_routed {Var : Type} [DecidableEq Var]
    {res : Var} {q : ℕ → ℕ} {A : (n : ℕ) → BatchCirc Var (q n) n}
    (H : BatchBound res q 80000 A 24673) {n : ℕ} (hn : 80000 ≤ n) :
    AvgOracleCostBound 512
      (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
      (fun S ↦ qset ;; (routedBatch res q 80000 A n).2.compile
        QProg.qAssign (groverParallelMarkingOracle 1024 S))
      ((NNRat.divNat 26768771052 1000000000000 : ℝ) * vanillaFindAllCost n 1024 512) := by
  let cap := (NNRat.divNat 26768771052 1000000000000 : ℝ) * vanillaFindAllCost n 1024 512
  have hnn : 0 ≤ cap := by
    dsimp [cap,vanillaFindAllCost,groverHarmonicSqrtSum]
    positivity
  rw [show routedBatch res q 80000 A n =
    ⟨q n, restartCircuit (retryGuard res n) (A n)⟩
    from ite_eq_left hn]
  refine ⟨fun _ ↦ cap.toNNReal, ?_, ?_⟩
  · intro S hS
    obtain ⟨p,T,ha,hp,ht⟩ := H.perSet n hn S hS
    have hle : T / p ≤ cap.toNNReal := by
      exact_mod_cast (finite_normalized hn hp ht).trans_eq (Real.coe_toNNReal cap hnn).symm
    have hreset : CostBound (CostModel.ofEmbeddedOracle (n:=q n)
        (groverParallelMarkingOracle 1024 S)) (QProg.qSet : QProg Var (2^(q n))) 0 := by
      intro Δ; simp
    simpa [restartCircuit, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_qWhile] using
      hreset.seq ((restart_cost ha).mono hle)
  · have hk : 512 ≤ 2^n := (show 512 ≤ 2^9 by decide).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    have hcard : (0:ℝ) < (groverTargetSets n 512).card := by
      rw [show (groverTargetSets n 512).card = Nat.choose (2^n) 512 by simp [groverTargetSets]]
      exact_mod_cast Nat.choose_pos hk
    rw [Finset.sum_const,nsmul_eq_mul,mul_div_cancel_left₀ _ hcard.ne',Real.coe_toNNReal cap hnn]

end Track2Weak

namespace QuantumComputation.Specs
open Operator ResourceCounting
open _root_.QuantumComputation.Specs.Grover (Var)
open _root_.QuantumComputation.Specs.Grover.Var (res)

/-- At every dimension in the weak branch, the public program meets its claimed query ratio. -/
theorem groverFindAll_cost_from_80000 {n : ℕ} (hn : 80000 ≤ n) :
    AvgOracleCostBound 512
      (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
      (fun S ↦ groverFindAllProgram n 1024 512 (groverParallelMarkingOracle 1024 S))
      (groverFindAllRelCost 1024 512 * vanillaFindAllCost n 1024 512) := by
  simp only [groverFindAllProgram, circuit_eq]
  exact Track2Weak.finite_routed (Track2Weak.weakBatchBound res) hn

end QuantumComputation.Specs

#print axioms QuantumComputation.Specs.groverFindAll_cost_from_80000
