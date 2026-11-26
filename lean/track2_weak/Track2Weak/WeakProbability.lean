module
public import Track2Weak.WeakAttempt
public import Track2Weak.WeakWalkOutcomes
public import Track2Weak.WeakCertRun
public import Track2Weak.WeakAssemblyCell

@[expose] public section
namespace Track2Weak
open Operator ResourceCounting Matrix QuantumComputation.Specs.DickeSol
open scoped Matrix NNReal

theorem survivor_eq_cert (n : ℕ) (qs : List Cert.Row) (hok : ∀ q ∈ qs, Cert.RowOK q)
    (x : Cert.V) : weakSurvivor n (qs.map Cert.Row.phys) x = (Cert.runOrbit n qs x).1 := by
  induction qs generalizing x with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons,weakSurvivor,Cert.runOrbit]
    rw [Cert.Row.phys_keep (hok q List.mem_cons_self)]
    exact ih (fun t ht ↦ hok t (List.mem_cons_of_mem _ ht)) _

noncomputable def weakProb (n : ℕ) : ℝ :=
  weakSuccessMass n (Cert.certRows.map Cert.Row.phys) (u0OrbVecGen (2^n) 1024 512)

theorem weakProb_bounds {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512) :
    (Cert.success12 : ℝ)/10^12 ≤ weakProb n ∧ weakProb n ≤ 1 := by
  let x := u0OrbVecGen (2^n) 1024 512
  let y := (Cert.runOrbit n Cert.certRows x).1
  have h : vecSqNorm y ≤ 1 - (Cert.success12 : ℝ)/10^12 := by
    simpa only [y,x,Cert.oneT, Nat.cast_ofNat, show (10:ℝ)^12=1000000000000 by norm_num]
      using (Cert.concreteOrbit hn).1
  have hy : (y weakTop)^2 ≤ vecSqNorm y :=
    Finset.single_le_sum (f := fun i ↦ (y i)^2) (fun i _ ↦ sq_nonneg _) (Finset.mem_univ weakTop)
  have he : weakProb n = 1 - vecSqNorm y + (y weakTop)^2 := by
    unfold weakProb weakSuccessMass
    rw [weakUniformMass hn S hS, survivor_eq_cert n Cert.certRows (fun _ hq ↦ Cert.concreteChain.rowOK hq)]
  rw [he]
  exact ⟨by linarith [sq_nonneg (y weakTop)], by linarith⟩

theorem weakProb_pos {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512) :
    0 < weakProb n := (by norm_num [Cert.success12] : 0 < (Cert.success12 : ℝ)/10^12).trans_le
      (weakProb_bounds hn S hS).1

theorem weakTrial_exit {Var : Type} [DecidableEq Var] [Subsingleton Var] (res : Var)
    {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512) :
    wp ((weakTrial res Cert.certRows n).compile QProg.qAssign (groverParallelMarkingOracle 1024 S))
      (fun τ ↦ ⌜¬ retryGuard res n τ⌝) = .ofProb (weakProb n) := by
  funext σ
  apply Subtype.ext
  apply Subtype.ext
  refine (weakTrial_wp res Cert.certRows hn S hS (fun τ ↦ ⌜¬ retryGuard res n τ⌝) σ).trans ?_
  have hex := weakStages_exit res hn (by omega) (weakRoom n) (Cert.certRows.map Cert.Row.phys) S hS
    (u0OrbVecGen (2^n) 1024 512) 0 (by simp) (fun _ ↦ 0)
  refine (congrArg (fun z : ℂ ↦ z • (1 : Operator _)) hex).trans ?_
  have h := CQAssertion.ofProb_apply_of_bounds (d := 2^(weakQubits n)) (weakProb n)
    (weakProb_pos hn S hS).le (weakProb_bounds hn S hS).2 σ
  exact (congrArg (fun H : HermitianMat (Fin (2^(weakQubits n))) ℂ ↦ H.mat) h).symm

theorem weakTrial_bad {Var : Type} [DecidableEq Var] [Subsingleton Var] (res : Var)
    {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512) :
    wp ((weakTrial res Cert.certRows n).compile QProg.qAssign (groverParallelMarkingOracle 1024 S))
      (fun τ ↦ ⌜¬ retryGuard res n τ ∧ decodeTargets n 512 (τ res) ≠ S⌝) = ⊥ := by
  funext σ
  apply Subtype.ext
  apply Subtype.ext
  refine (weakTrial_wp res Cert.certRows hn S hS
    (fun τ ↦ ⌜¬ retryGuard res n τ ∧ decodeTargets n 512 (τ res) ≠ S⌝) σ).trans ?_
  have hbad := weakStages_bad res hn (by omega) (weakRoom n) (Cert.certRows.map Cert.Row.phys) S hS
    (u0OrbVecGen (2^n) 1024 512) 0 (by simp) (fun _ ↦ 0)
  exact (congrArg (fun z : ℂ ↦ z • (1 : Operator _)) hbad).trans (zero_smul _ _)

end Track2Weak

#print axioms Track2Weak.weakTrial_exit
#print axioms Track2Weak.weakTrial_bad
