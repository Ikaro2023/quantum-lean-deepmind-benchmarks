module

public import Track2Weak.WeakAssemblyCost
public import Track2Weak.WeakWalkStages

@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting QProg.Notation
open scoped NNReal QHLExpectation

noncomputable def stagePrice (n : ℕ) (row : WeakRow) : ℕ :=
  muxOpsQueryCount (weakCellOps n 512 row) + 2

noncomputable abbrev nextOrbit (n : ℕ) (row : WeakRow) (x : Fin 513 → ℝ) :=
  weakKeep 512 row.2.cVal (weakOrbitStep n 512 row x)

noncomputable abbrev hitOrbit (n : ℕ) (row : WeakRow) (x : Fin 513 → ℝ) :=
  weakClick 512 row.2.sVal (weakOrbitStep n 512 row x)

/-- Finite-dimensional upper query account along actual surviving branches. The terminal
reader is charged on early clicks as well as the exhausted no-click branch. -/
noncomputable def orbitQueries (n readPrice : ℕ) : List WeakRow → (Fin 513 → ℝ) → ℝ
  | [], x => readPrice * vecSqNorm x
  | row :: tail, x => stagePrice n row * vecSqNorm x + readPrice * vecSqNorm (hitOrbit n row x) +
      orbitQueries n readPrice tail (nextOrbit n row x)

noncomputable def orbitDuration (n : ℕ) : List WeakRow → (Fin 513 → ℝ) → ℝ
  | [], _ => 0
  | row :: tail, x => row.1.tau9 / (10^9:ℝ) * vecSqNorm x + orbitDuration n tail (nextOrbit n row x)

theorem weakStage_mass {n : ℕ} (hn : 80000 ≤ n) (row : WeakRow) (x : Fin 513 → ℝ) :
    vecSqNorm (nextOrbit n row x) + vecSqNorm (hitOrbit n row x) = vecSqNorm x := by
  rw [nextOrbit, hitOrbit, weak_branch_mass 512 row.2.cVal_sq_add_sVal_sq, ← sq_vecNorm,
    ← sq_vecNorm x]
  unfold weakOrbitStep
  rw [vecNorm_rkmMaskSignVec]
  have hN : 2^12 ≤ (2:Nat)^n := Nat.pow_le_pow_right (by decide) (by omega)
  have hO := dAltStepOrbMat_orthogonal_two_pow (m:=1024) (r:=512) (n:=n) (by omega)
    (by omega) (by omega)
  generalize altStepCount row.1.tau9 row.1.nSub (2^n) = k
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ (dAltStepOrbMat _ _ _), ← Matrix.mulVec_mulVec, ih,
      vecNorm_mulVec_of_orthogonal hO]

/-- All once-per-stage overhead and the single terminal readout stay additive in n. -/
theorem orbitQueries_le {n : ℕ} (hn : 80000 ≤ n) (readPrice : ℕ)
    (rows : List WeakRow) (x : Fin 513 → ℝ) (hx : vecSqNorm x ≤ 1) :
    orbitQueries n readPrice rows x ≤
      orbitDuration n rows x * Real.sqrt ((2:ℝ)^n) + 1028 * rows.length + readPrice * vecSqNorm x := by
  induction rows generalizing x with
  | nil => simp [orbitQueries,orbitDuration]
  | cons row tail ih =>
    have hm := weakStage_mass hn row x
    have hnext : vecSqNorm (nextOrbit n row x) ≤ 1 := by
      linarith [vecSqNorm_nonneg (hitOrbit n row x)]
    have htail := ih _ hnext
    have hstage : (stagePrice n row : ℝ) ≤
        row.1.tau9 / (10^9:ℝ) * Real.sqrt ((2:ℝ)^n) + 1028 := by
      norm_num [stagePrice] at ⊢
      exact weakStage_charge n row
    have hprice := mul_le_mul_of_nonneg_right hstage (vecSqNorm_nonneg x)
    have hstop := congrArg (fun (a:ℝ) ↦ readPrice * a) hm
    simp only [orbitQueries,orbitDuration,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [htail, hprice, hx, hstop]

private theorem workMass_weakLift {n r : ℕ} (S : Finset (Fin (2^n))) (hS : S.card = r)
    (hmr : 1024 + S.card ≤ 2^n) (x : Fin (orbDim 1024 r) → ℝ) :
    workMass (liftSymVec n 1024 (weakOrbitLift S hS x)) = vecSqNorm x := by
  subst r
  exact workMass_lift_orbit hmr x

theorem weakStages_scaled {Var : Type} [DecidableEq Var] (res : Var) {n : ℕ}
    (hn : 80000 ≤ n) (hM : 1 ≤ 512*n) (S : Finset (Fin (2^n))) (hS : S.card = 512)
    (finish : WeakCellCirc Var n) (readPrice : ℕ)
    (hread : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S))
      (finish.compile QProg.qAssign (groverParallelMarkingOracle 1024 S)) readPrice)
    (rows : List WeakRow) {B : ℝ} (hB : 0 < B) (hmax : stoppedMax (stagePrice n) readPrice rows ≤ B) :
    ∃ θ, ScaledCostRel (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1024 S)) B
        ((weakStages res n hM finish rows).compile QProg.qAssign (groverParallelMarkingOracle 1024 S))
        θ (stoppedMax (stagePrice n) readPrice rows) ∧
      ∀ (x : Fin 513 → ℝ) σ, rmsVecQuad (θ σ).1.1 (weakState S hS x 0) =
        ((orbitQueries n readPrice rows x / B : ℝ) : ℂ) := by
  let rep := fun x : Fin 513 → ℝ ↦ liftSymVec n 1024 (weakOrbitLift S hS x)
  let hit := fun row x ↦ rep (hitOrbit n row x)
  let O := groverParallelMarkingOracle 1024 S
  let stage := fun row ↦ (weakStage res n hM row).compile QProg.qAssign O
  have hzero : (0 : Fin (2^(512*n))).val < 2^(512*n-1) := by simp
  obtain ⟨θ,hθ,hv⟩ := stoppedChain_scaled res (CostModel.ofEmbeddedOracle O) stage
    (finish.compile QProg.qAssign O) (stagePrice n) readPrice rep (nextOrbit n) hit 0
    (memWithTopOne hM 0 hzero) (fun i ↦ by simpa [stage,stagePrice,O] using weakStage_cost res n hM i S)
    hread (fun i x θ σ ↦ weakStage_wp res hn hM i S hS x 0 hzero θ σ) rows hB hmax
  have hchain : ∀ rs, (weakStages res n hM finish rs).compile QProg.qAssign O =
      stoppedChain res stage (finish.compile QProg.qAssign O) rs := by
    intro rs
    induction rs with
    | nil => rfl
    | cons i rs ih => simp [weakStages,stoppedChain,stage,ih]
  have hN : 2^12 ≤ (2:Nat)^n := Nat.pow_le_pow_right (by decide) (by omega)
  have hmr : 1024 + S.card ≤ 2^n := by omega
  have htime : ∀ rs x, stoppedTime rep (nextOrbit n) hit (stagePrice n) readPrice rs x =
      orbitQueries n readPrice rs x := by
    intro rs
    induction rs with
    | nil => intro x; simp [stoppedTime,orbitQueries,rep,workMass_weakLift S hS hmr]
    | cons i rs ih =>
      intro x
      simp [stoppedTime,orbitQueries,hit,rep,ih,workMass_weakLift S hS hmr]
  refine ⟨θ, ?_, ?_⟩
  · change ScaledCostRel (CostModel.ofEmbeddedOracle O) B _ _ _
    rw [hchain]
    exact hθ
  · intro x σ; exact (hv x σ).trans (by rw [htime])

end QuantumComputation.Specs.DickeSol

#print axioms QuantumComputation.Specs.DickeSol.weakStages_scaled
#print axioms QuantumComputation.Specs.DickeSol.orbitQueries_le
