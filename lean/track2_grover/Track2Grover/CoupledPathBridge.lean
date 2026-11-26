import Track2Grover.CoupledActions
import Track2Grover.LowerPath

namespace Track2Grover.CoupledPathBridge
open CoupledHistory CoupledLabels CoupledActions Path Operator QuantumComputation.Specs Finset Real
open scoped BigOperators RealInnerProductSpace

abbrev Labels (n k : ℕ) := ↥(groverTargetSets n k)
abbrev Trees (n m q : ℕ) := Tree Grover.Var q ((n+1)*m)
abbrev Fam (n k q : ℕ) := Family (Labels n k) (Space q)

noncomputable def paid {n m k q : ℕ} (T : Trees n m q) (x : Fam n k q) :=
  ∑ S : Labels n k, score (groverParallelMarkingOracle m S.1) 1 (fun _ ↦ 0) (fun _ _ ↦ 0) T (x S).ofLp
noncomputable def finished {n m k q : ℕ} (T : Trees n m q) (x : Fam n k q) :=
  ∑ S : Labels n k, score (groverParallelMarkingOracle m S.1) 0 (fun _ ↦ 0) (fun _ ↦ energy) T (x S).ofLp
noncomputable def unfinished {n m k q : ℕ} (T : Trees n m q) (x : Fam n k q) :=
  ∑ S : Labels n k, score (groverParallelMarkingOracle m S.1) 0 energy (fun _ _ ↦ 0) T (x S).ofLp
noncomputable def bad {n m k q : ℕ} (T : Trees n m q) (S : Labels n k) (x : Space q) :=
  score (groverParallelMarkingOracle m S.1) 0 (fun _ ↦ 0)
    (fun σ u ↦ if OutputAverage.good S.1 σ then 0 else energy u) T x.ofLp

theorem energy_eq {q : ℕ} (x : Space q) : energy x.ofLp = ‖x‖^2 := by
  simp [energy,EuclideanSpace.norm_sq_eq,Complex.sq_norm]

private theorem bad_nonneg {n m k q : ℕ} (T : Trees n m q) (S : Labels n k) (x : Space q) :
    0 ≤ bad T S x := by
  have h (u : Vec q) : 0 ≤ score (groverParallelMarkingOracle m S.1) 0 (fun _ ↦ 0)
    (fun σ u ↦ if OutputAverage.good S.1 σ then 0 else energy u) T u := by
    induction T generalizing u with
    | timeout => rfl
    | halt σ => simp only [score]; split_ifs <;> first | rfl | exact sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
    | fixed U T ih => exact ih _
    | query r T ih => simpa only [score,zero_mul,zero_add] using ih _
    | measure r children ih => exact sum_nonneg fun o _ ↦ ih o _
  exact h _

theorem run_of_path {n m k q : ℕ} [Nonempty (Labels n k)]
    (hk : 0 < k) (b : ℝ) (hb : b ∈ Set.Icc 0 1)
    (hinv : ∀ (r : QRegister ((n+1)*m) q) (S : Labels n k),
      Function.Involutive (act (r.embedUnitary (groverParallelMarkingOracle m S.1))))
    (comp : ∀ (r : QRegister ((n+1)*m) q) (y : Space q),
      (1-2*b)*(Fintype.card (Labels n k):ℝ)*‖y‖^2 ≤
      ∑ S : Labels n k, ⟪y,act (r.embedUnitary (groverParallelMarkingOracle m S.1)) y⟫)
    (T : Trees n m q) (x : Fam n k q) (good : ∀ S, bad T S (x S)=0) :
    Run (uniform (Labels n k) (Space q)) (k/(2:ℝ)^n) (2*arcsin (√b)) x
      (paid T x) (finished T x) (unfinished T x) := by
  induction T generalizing x with
  | timeout =>
    simpa only [paid,finished,unfinished,score,sum_const_zero,energy_eq,← sum_energy] using
      (Run.cutoff (K := uniform (Labels n k) (Space q)) (p := (k:ℝ)/2^n) (v := 2*arcsin (√b)) x)
  | halt σ =>
    have hs (i : Labels n k) (h : ¬OutputAverage.good i.1 σ) : x i = 0 := by
      have hh := good i
      simp only [bad,score,ite_eq_right h,energy_eq,pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0),norm_eq_zero] at hh
      exact hh
    simpa only [paid,finished,unfinished,score,sum_const_zero,energy_eq,← sum_energy] using
      (Run.done (K := uniform (Labels n k) (Space q)) (v := 2*arcsin (√b)) x (supported hk σ x hs))
  | fixed U T ih =>
    exact fixed_node _ U x (ih _ good)
  | query r T ih =>
    let O := fun S : Labels n k ↦ r.embedUnitary (groverParallelMarkingOracle m S.1)
    let y := joint (Labels n k) O x
    have he (i : Labels n k) :
        ((joint (Labels n k) O x) i).ofLp =
        (r.embedUnitary (groverParallelMarkingOracle m i.1)).1.mulVec (x i).ofLp := rfl
    have hgood (i : Labels n k) : bad T i (y i) = 0 := by
      simpa only [bad,score,zero_mul,zero_add,y,he] using good i
    have h := oracle_node _ O (hinv r) hb (comp r) x (ih _ hgood)
    simpa only [paid,finished,unfinished,score,one_mul,zero_mul,zero_add,energy_eq,
      sum_add_distrib,← sum_energy, he] using h
  | measure r T ih =>
    let y o := lift (Labels n k) (Space q) (read r o) x
    have he (o) (i : Labels n k) : ((y o) i).ofLp = (r.basisOutcomeProjector o).mulVec (x i).ofLp :=
      funext (read_exact r o (x i))
    have hg (o) (i : Labels n k) : bad (T o) i ((y o) i) = 0 := by
      have h := good i
      have h' : ∑ o, bad (T o) i ((y o) i) = 0 := by
        simpa only [bad, score, he] using h
      exact (sum_eq_zero_iff_of_nonneg (fun j _ ↦ bad_nonneg (T j) i _)).mp h' o (mem_univ _)
    have h := measure_node (Labels n k) r x (fun o ↦ ih o (y o) (hg o))
    unfold paid finished unfinished at h ⊢
    simp only [score]
    rw [sum_comm, sum_comm (s := univ) (t := univ) (f := fun i o ↦ score _ 0 _ (fun _ ↦ energy) _ _),
      sum_comm (s := univ) (t := univ) (f := fun i o ↦ score _ 0 energy _ _ _)]
    simp_rw [he] at h
    exact h

#print axioms run_of_path

/-- Starting in a common unit workspace state makes the lower bound homogeneous in
the completed mass. Timeouts carry no negative term in this formulation. -/
theorem completion_le_queries {n m k q : ℕ} [Nonempty (Labels n k)]
    {b : ℝ} (hb : b ∈ Set.Icc 0 1) (T : Trees n m q) (u : Space q) (hu : ‖u‖=1)
    (tree : Run (uniform (Labels n k) (Space q)) (k/(2:ℝ)^n) (2*arcsin (√b))
      (copy (Labels n k) (Space q) u) (paid T (copy (Labels n k) _ u))
      (finished T (copy (Labels n k) _ u)) (unfinished T (copy (Labels n k) _ u))) :
    Lower.c * (1-k/(2:ℝ)^n) * finished T (copy (Labels n k) _ u) ≤
      (2*arcsin (√b)) * paid T (copy (Labels n k) _ u) := by
  let x := copy (Labels n k) (Space q) u
  have hx : x ∈ uniform (Labels n k) (Space q) := by intro i j; rfl
  have hx2 : ‖x‖^2 = Fintype.card (Labels n k) := by
    rw [sum_energy]; change (∑ _ : Labels n k, ‖u‖^2) = _; simp [hu]
  have hx0 : x ≠ 0 := by
    intro h; rw [h,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] at hx2
    have : 0 < (Fintype.card (Labels n k) : ℝ) := by positivity
    linarith
  have ha : QueryAngle.alpha (uniform (Labels n k) (Space q)) x = 0 := by
    simp [QueryAngle.alpha,Submodule.starProjection_eq_self_iff.mpr hx, norm_ne_zero_iff.mpr hx0]
  have hh := tree_accounting _ (v := 2*arcsin (√b))
    ⟨mul_nonneg (by norm_num) (arcsin_nonneg.mpr (sqrt_nonneg b)),
      by linarith [arcsin_le_pi_div_two (√b)]⟩ tree
  change finished T x + unfinished T x = ‖x‖^2 ∧
    potential _ x ≤ _ at hh
  obtain ⟨hs,hp⟩ := hh
  rw [potential,ha,Lower.profile,ite_eq_left (by positivity : (0:ℝ) ≤ π/4), sub_zero] at hp
  change Lower.c * (1-k/(2:ℝ)^n) * finished T x ≤ _
  rw [← hs] at hp
  linarith

#print axioms completion_le_queries
end Track2Grover.CoupledPathBridge
