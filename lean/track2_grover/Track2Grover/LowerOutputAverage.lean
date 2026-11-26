import QuantumComputationSpecs.Algorithms.Grover
import Track2Grover.StopMass
import Mathlib.Tactic

namespace Track2Grover.OutputAverage
open Operator QuantumComputation.Specs Finset Track2Grover.HiddenSet

def good {n : ℕ} (S : Finset (Fin (2^n))) (σ : Store Grover.Var) : Prop :=
  ∃ x ∈ S, σ Grover.Var.res = x.val

noncomputable instance {n : ℕ} (S : Finset (Fin (2^n))) : DecidablePred (good S) :=
  Classical.decPred _

/-- An oracle-independent classical store can succeed on at most a k/N fraction of
inputs, also when the reported integer is negative or exceeds the domain. -/
theorem store_count {n k : ℕ} (hk : 0 < k) (σ : Store Grover.Var) :
    2^n * ((groverTargetSets n k).filter (fun S => good S σ)).card ≤
      (groverTargetSets n k).card * k := by
  classical
  by_cases h : ∃ x : Fin (2^n), σ Grover.Var.res = x.val
  · obtain ⟨x,hx⟩ := h
    have hgood (S : Finset (Fin (2^n))) : good S σ ↔ x ∈ S := by
      refine ⟨fun ⟨y, hy, hxy⟩ => ?_, fun hmem => ⟨x,hmem,hx⟩⟩
      have heq : x = y := Fin.ext (by exact_mod_cast hx.symm.trans hxy)
      rwa [heq]
    simp_rw [hgood]
    exact (incidence x hk).le
  · have hnone (S : Finset (Fin (2^n))) : ¬ good S σ :=
      fun ⟨x,_,hx⟩ => h ⟨x,hx⟩
    simp [hnone]

/-- Average success bound on a common (possibly subnormalized) CQState. -/
theorem shared_output {n k d : ℕ} (hk : 0 < k) (Δ : CQState (Store Grover.Var) d) :
    (2:ℝ)^n * (∑ S ∈ groverTargetSets n k, expect Δ (fun σ => ⌜good S σ⌝)) ≤
      ((groverTargetSets n k).card:ℝ)*k*Δ.trace := by
  classical
  let L := groverTargetSets n k
  let mass (σ : Store Grover.Var) := (Δ σ).1.trace
  let f (S : Finset (Fin (2^n))) (σ : Store Grover.Var) :=
    if good S σ then mass σ else 0
  have hsum (S) : Summable (f S) := by
    exact Δ.summable_trace_val.indicator {σ | good S σ}
  have he (S) : expect Δ (fun σ => ⌜good S σ⌝) = ∑' σ, f S σ := by
    rw [expect_eq_tsum]
    apply tsum_congr
    intro σ
    by_cases h : good S σ <;> simp [f, mass, h]
  have hpt (σ) : (2:ℝ)^n * (∑ S ∈ L, f S σ) ≤ L.card*k*mass σ := by
    have hn : (2:ℝ)^n * ((L.filter (fun S => good S σ)).card:ℝ) ≤ L.card*k := by
      exact_mod_cast store_count hk σ
    simpa [f, ← Finset.sum_filter, nsmul_eq_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hn (Δ σ).trace.coe_nonneg
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (s := L) (fun i _ => hsum i),
    CQState.coe_trace_eq_tsum, ← tsum_mul_left, ← tsum_mul_left]
  exact ((summable_sum (s := L) (fun S _ => hsum S)).mul_left _).tsum_le_tsum hpt
    (Δ.summable_trace_val.mul_left _)

#print axioms store_count
#print axioms shared_output
end Track2Grover.OutputAverage
