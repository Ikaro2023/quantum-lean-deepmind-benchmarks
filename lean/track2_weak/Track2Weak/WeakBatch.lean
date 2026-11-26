module
public import Track2Weak.WeakProbability
public import Track2Weak.WeakWalkTotal
public import Track2Weak.WeakAssemblyTrialCost

@[expose] public section
namespace Track2Weak
open Operator ResourceCounting QuantumComputation.Specs.DickeSol
open scoped NNReal

/-- The probability, expected query budget, return value and retry all concern the same circuit. -/
theorem weakBatchBound {Var : Type} [DecidableEq Var] [Subsingleton Var] (res : Var) :
    BatchBound res weakQubits 80000 (weakTrial res Cert.certRows) 24673 := by
  constructor
  intro n hn S hS
  have hc : S.card = 512 := (Finset.mem_powersetCard.mp hS).2
  have hp := weakProb_pos hn S hc
  have hb := weakProb_bounds hn S hc
  let p : ℝ≥0 := ⟨weakProb n, hp.le⟩
  refine ⟨p, weakTrialBudget n, ?_, hb.1, (weakTrialBudget_eq n).le⟩
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hb.2,
    weakTrial_lossless res Cert.certRows hn S, weakTrial_cost res hn S hc,
    weakTrial_exit res hn S hc, weakTrial_bad res hn S hc⟩

end Track2Weak
#print axioms Track2Weak.weakBatchBound
