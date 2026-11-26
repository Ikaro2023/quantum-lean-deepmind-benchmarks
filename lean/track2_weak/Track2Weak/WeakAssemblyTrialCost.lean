module
public import Track2Weak.WeakAssemblyStages
public import Track2Weak.WeakAttempt
public import Track2Weak.WeakCertRun
import all Track2Grover.Engine.WeakDickeCore

@[expose] public section
namespace Track2Weak
open Operator ResourceCounting Matrix QuantumComputation.Specs.DickeSol
open scoped Matrix NNReal ENNReal QHLExpectation

theorem duration_certificate (n : ℕ) {qs : List Cert.Row}
    (ok : ∀ q ∈ qs, Cert.RowOK q) (x : Cert.V) :
    orbitDuration n (qs.map Cert.Row.phys) x = (Cert.runOrbit n qs x).2 := by
  induction qs generalizing x with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, orbitDuration, Cert.runOrbit]
    change q.time / (10^9:ℝ) * vecSqNorm x + orbitDuration n _ (weakNo n q.phys x) = _
    rw [q.phys_keep (ok q List.mem_cons_self), ih (fun i hi ↦ ok i (List.mem_cons_of_mem _ hi))]
    norm_num [Cert.oneB]

noncomputable def weakTrialBudget (n : ℕ) : ℝ≥0 :=
  Real.toNNReal ((Cert.weightedCost21:ℝ) / 10^21 * Real.sqrt ((2:ℝ)^n) + 24673)

theorem weakTrialBudget_eq (n : ℕ) : (weakTrialBudget n : ℝ) =
    (Cert.weightedCost21:ℝ) / 10^21 * Real.sqrt ((2:ℝ)^n) + 24673 := by
  exact Real.coe_toNNReal _ (by positivity)

/-- The actual oracle-independent finite-n compensated attempt, with a single terminal
oracle charge and at most 1028 additive rounds per stage, including its probe. -/
theorem weakTrial_cost {Var : Type} [DecidableEq Var] [Subsingleton Var] (res : Var) {n : ℕ}
    (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512) :
    CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
      ((weakTrial res Cert.certRows n).compile QProg.qAssign (groverParallelMarkingOracle 1024 S))
      (weakTrialBudget n) := by
  let O := groverParallelMarkingOracle 1024 S
  let model := CostModel.ofEmbeddedOracle (n := weakQubits n) O
  let rows := Cert.certRows.map Cert.Row.phys
  let x := u0OrbVecGen (2^n) 1024 512
  let B : ℝ := stoppedMax (stagePrice n) 1 rows + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hmax : (stoppedMax (stagePrice n) 1 rows:ℝ) ≤ B := by dsimp only [B]; linarith
  have hM : 1 ≤ 512*n := by omega
  have hm : 1024 ≤ 2^n := (by omega : 1024 ≤ 1024+512).trans (weakSize hn)
  let P := (weakInitialize res n 1024 (512*n) hm).compile QProg.qAssign O
  have hread := weakTerminalRead_cost res (M:=512*n) (weakRoom n) S
  obtain ⟨θ, hcost, hv⟩ := weakStages_scaled res hn hM S hS (weakFinish res n) 1
    (by simpa only [weakFinish, Nat.cast_one] using hread) rows hB hmax
  have hpc : CostBound model P 0 := weakInitialize_cost res hm S
  have hfull := ScaledCostRel.seq_zero_left hB hpc hcost
  let L := orbitQueries n 1 rows x
  have hval (σ : Store Var) : ((wp P θ) σ).1.1 = ((L / B : ℝ) : ℂ) • (1 : Operator _) := by
    rw [show ((wp P θ) σ).1.1 = _ from weakInitialize_wp res hm S θ σ]
    have hu := hv x (fun _ ↦ 0)
    change rmsVecQuad _ (workMemState (liftSymVec _ _ (weakOrbitLift S hS x)) _) = _ at hu
    rw [show weakOrbitLift S hS x = _ from weakUniform hn S hS] at hu
    rw [hu]
  have hL : L ≤ (weakTrialBudget n : ℝ) := by
    have hinit : vecSqNorm x = 1 := weakUniformMass hn S hS
    have hQ := orbitQueries_le hn 1 rows x hinit.le
    have hd : orbitDuration n rows x ≤ Cert.weightedCost21 / ((Cert.oneB:ℝ)*Cert.oneT) := by
      rw [show rows = _ from rfl, duration_certificate n (fun _ h ↦ Cert.concreteChain.rowOK h)]
      exact (Cert.concreteOrbit hn).2
    have hlen : rows.length = 24 := rfl
    rw [hinit, hlen] at hQ
    rw [weakTrialBudget_eq]
    have hd' : orbitDuration n rows x ≤ (Cert.weightedCost21:ℝ) / 10^21 := by
      norm_num [Cert.oneB,Cert.oneT] at hd ⊢; exact hd
    have hp := mul_le_mul_of_nonneg_right hd' (Real.sqrt_nonneg ((2:ℝ)^n))
    dsimp only [L]
    norm_num1 at hQ
    linarith only [hQ,hp]
  intro Δ
  have h := hfull.2.2.2 Δ
  have hexp : 𝔼[Δ, wp P θ] = L/B * Δ.trace := by
    rw [expect_eq_mul_of_apply_eq_smul Δ (Ψ:=⊤) (L/B) (fun σ ↦ ?_), expect_top]
    apply HermitianMat.ext
    rw [← HermitianMat.val_eq_coe, HermitianMat.mat_smul]
    convert hval σ using 1 <;> ext i j <;> simp [Complex.real_smul]
  change _ ≤ ENNReal.ofReal (B * 𝔼[Δ, wp P θ]) at h
  rw [hexp] at h
  rw [show B * (L / B * (Δ.trace:ℝ)) = (Δ.trace:ℝ) * L from by field_simp] at h
  simp only [weakTrial, dite_eq_left hn, OracleDynamicCircuit.compile_seq]
  refine h.trans ?_
  calc ENNReal.ofReal ((Δ.trace:ℝ) * L) ≤ ENNReal.ofReal ((Δ.trace:ℝ) * (weakTrialBudget n : ℝ)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hL Δ.trace_nonneg)
    _ = _ := by rw [ENNReal.ofReal_mul Δ.trace_nonneg]; simp

end Track2Weak

#print axioms Track2Weak.weakTrial_cost
