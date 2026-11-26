import Track2Grover.QueryAngle
import Track2Grover.LowerPotential
import Mathlib.Tactic

/-! Local accounting on finite, unsynchronized quantum history trees.
Measurement branches can run different numbers of queries. A cutoff leaf charges
its entire surviving squared norm. No purity or lower-bound assumption about a
merged classical store is used. -/
namespace Track2Grover.CoupledHistory
open Real Finset Lower
open scoped BigOperators RealInnerProductSpace

private theorem cpos : 0 ≤ c := by unfold c; positivity

private theorem profile_zero : profile 0 = c := by
  simp [profile, show (0:ℝ) ≤ π/4 by positivity]

private lemma angle_zero {a : ℝ} (ha : a ∈ Set.Icc 0 (π/2))
    (h : 1-cos a^2 = 0) : a = 0 := by
  have hp : 0 ≤ cos a := cos_nonneg_of_mem_Icc ⟨by linarith [ha.1,pi_pos],ha.2⟩
  have hc : cos a = 1 := by nlinarith [cos_le_one a]
  exact injOn_cos ⟨ha.1,by linarith [ha.2,pi_pos]⟩ ⟨le_rfl,pi_pos.le⟩ (hc.trans cos_zero.symm)

/-- Measuring a label-independent instrument, retaining all its outcomes, cannot
decrease the sum of path potentials. The two equalities are conservation of total
energy and conservation of uniform-label energy. -/
theorem split_potential {ι : Type*} [Fintype ι] {s a : ℝ} {w b : ι → ℝ}
    (ha : a ∈ Set.Icc 0 (π/2)) (hb : ∀ i, b i ∈ Set.Icc 0 (π/2))
    (hw : ∀ i, 0 ≤ w i) (htot : ∑ i, w i = s)
    (hpar : ∑ i, w i * cos (b i)^2 = s * cos a^2) :
    s * profile a ≤ ∑ i, w i * profile (b i) := by
  rcases ha.1.eq_or_lt with h0 | hpos
  · subst a
    have hnon i : 0 ≤ w i * (1-cos (b i)^2) :=
      mul_nonneg (hw i) (by nlinarith [sin_sq_add_cos_sq (b i), sq_nonneg (sin (b i))])
    have hz : ∑ i, w i * (1-cos (b i)^2) = 0 := by
      simp only [mul_sub,mul_one,sum_sub_distrib,htot,hpar,cos_zero,one_pow,sub_self]
    have each : ∀ i, w i * profile (b i) = w i * profile 0 := by
      intro i
      rcases mul_eq_zero.mp ((sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnon j)).mp hz i (mem_univ i))
        with h | h
      · simp [h]
      · rw [angle_zero (hb i) h]
    rw [show (∑ i, w i * profile (b i)) = s * profile 0 by simp only [each, ← sum_mul, htot]]
  by_cases hsmall : a ≤ π/4
  · obtain ⟨A,B,heq,hline⟩ := profile_supporting_line hpos hsmall
    have h i := mul_le_mul_of_nonneg_left (hline (b i) (hb i).1 (hb i).2) (hw i)
    calc
      s * profile a = ∑ i, w i * (A*cos (b i)^2+B) := by
        rw [heq]
        simp only [mul_add, sum_add_distrib, ← sum_mul, htot]
        simp_rw [show ∀ i, w i*(A*cos (b i)^2) = A*(w i*cos (b i)^2) by intro i; ring]
        rw [← mul_sum, hpar]; ring
      _ ≤ _ := sum_le_sum (fun i _ ↦ h i)
  · rw [profile, ite_eq_right hsmall, ← hpar]
    exact sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (parallel_le_profile _) (hw i)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Submodule ℝ E) [K.HasOrthogonalProjection]

private theorem ratio_le_one (x : E) : ‖K.starProjection x‖ / ‖x‖ ≤ 1 := by
  by_cases h : x=0
  · simp [h]
  exact (div_le_one (norm_pos_iff.mpr h)).mpr (K.norm_starProjection_apply_le x)

theorem angle_range (x : E) : QueryAngle.alpha K x ∈ Set.Icc 0 (π/2) :=
  ⟨arccos_nonneg _, arccos_le_pi_div_two.mpr (div_nonneg (norm_nonneg _) (norm_nonneg _))⟩

theorem projection_energy (x : E) : ‖x‖^2 * cos (QueryAngle.alpha K x)^2 = ‖K.starProjection x‖^2 := by
  rw [QueryAngle.alpha, cos_arccos _ (ratio_le_one K x)]
  · by_cases h : x=0
    · simp [h]
    field_simp [norm_ne_zero_iff.mpr h]
  · linarith [div_nonneg (norm_nonneg (K.starProjection x)) (norm_nonneg x)]

noncomputable def potential (x : E) : ℝ := ‖x‖^2 * profile (QueryAngle.alpha K x)

/-- A finite adaptive tree derivation. Its three real indices are total expected
queries, completed mass, and mass at the fuel cutoff. A measurement uses the same
linear Kraus maps across all labels, expressed by commuting with their projection. -/
inductive Run (p v : ℝ) : E → ℝ → ℝ → ℝ → Prop
  | done (x : E) (support : ‖K.starProjection x‖^2 ≤ p*‖x‖^2) :
      Run p v x 0 (‖x‖^2) 0
  | cutoff (x : E) : Run p v x 0 0 (‖x‖^2)
  | query (x : E) (O : E →ₗᵢ[ℝ] E) (involutive : Function.Involutive O)
      (compressed : ∀ y ∈ K, cos v * ‖y‖^2 ≤ ⟪y, O y⟫)
      {t h f : ℝ} (next : Run p v (O x) t h f) :
      Run p v x (‖x‖^2 + t) h f
  | instrument {l : ℕ} (x : E) (M : Fin l → E →ₗ[ℝ] E)
      (complete : ∀ y, ∑ j, ‖M j y‖^2 = ‖y‖^2)
      (labelIndependent : ∀ j y, K.starProjection (M j y) = M j (K.starProjection y))
      {t h f : Fin l → ℝ} (branches : ∀ j, Run p v (M j x) (t j) (h j) (f j)) :
      Run p v x (∑ j, t j) (∑ j, h j) (∑ j, f j)

theorem tree_accounting {p v t h f : ℝ} (hv : v ∈ Set.Icc 0 π)
    {x : E} (tree : Run K p v x t h f) :
    h+f = ‖x‖^2 ∧ potential K x ≤ v*t + c*p*h + c*f := by
  induction tree with
  | done x support =>
    have hh := angle_range K x
    have hs := Lower.stopping_loss (sq_nonneg ‖x‖) (r := 0) le_rfl hh.1 hh.2
      (b := 0) le_rfl (by positivity) (by simp; positivity)
      (by simp; exact mul_nonneg (sq_nonneg _) (by nlinarith [sin_sq_add_cos_sq (QueryAngle.alpha K x),sq_nonneg (sin (QueryAngle.alpha K x))]))
    rw [projection_energy] at hs
    refine ⟨by ring, ?_⟩
    dsimp [potential]
    nlinarith only [hs, mul_le_mul_of_nonneg_left support cpos]
  | cutoff x =>
    refine ⟨by ring, ?_⟩
    have ap := angle_range K x
    have hprof : profile (QueryAngle.alpha K x) ≤ c := by
      unfold profile
      split_ifs
      · linarith [ap.1]
      · unfold c
        nlinarith [two_le_pi,sin_sq_add_cos_sq (QueryAngle.alpha K x),sq_nonneg (sin (QueryAngle.alpha K x))]
    dsimp [potential]
    nlinarith only [mul_le_mul_of_nonneg_left hprof (sq_nonneg ‖x‖)]
  | query x O hinv hcomp next ih =>
    have hq := query_loss (sq_nonneg ‖x‖)
      (show |QueryAngle.alpha K x-QueryAngle.alpha K (O x)| ≤ v by
        rw [abs_sub_comm]; exact QueryAngle.one_query K O hinv hv.1 hv.2 hcomp x)
    simp only [potential, O.norm_map] at ih ⊢
    exact ⟨ih.1, by linarith [ih.2]⟩
  | instrument x M complete commute branches ih =>
    refine ⟨?_,?_⟩
    · rw [← sum_add_distrib]; simpa only [fun j ↦ (ih j).1] using complete x
    have hpar : ∑ j, ‖M j x‖^2 * cos (QueryAngle.alpha K (M j x))^2 =
        ‖x‖^2 * cos (QueryAngle.alpha K x)^2 := by
      simp_rw [projection_energy,commute]; exact complete _
    have hs := split_potential (angle_range K x) (fun j ↦ angle_range K (M j x))
      (fun j ↦ sq_nonneg ‖M j x‖) (complete x) hpar
    apply hs.trans
    simpa only [potential, sum_add_distrib, ← mul_sum] using sum_le_sum (s := univ) (fun j _ ↦ (ih j).2)

/-- Unconditional on any global query synchronization or pre-supplied angle ledger,
for a finite tree of the stated quantum instruments starting in the label-uniform
subspace. The cutoff error vanishes along any truncation with vanishing unfinished mass. -/
theorem finite_tree_lower_bound {p v t h f : ℝ} (hv : v ∈ Set.Icc 0 π)
    {x : E} (hx : x ∈ K) (hx1 : ‖x‖ = 1) (tree : Run K p v x t h f) :
    c*(1-p)*(1-f) ≤ v*t := by
  have hh := tree_accounting K hv tree
  have hp : K.starProjection x = x := K.starProjection_eq_self_iff.mpr hx
  have hpot : potential K x = c := by simp [potential, QueryAngle.alpha, hp, hx1, profile_zero]
  rw [hpot,hx1] at hh
  obtain ⟨h1,h2⟩ := hh
  simp only [one_pow] at h1
  rw [show h=1-f by linarith] at h2
  linarith

#print axioms split_potential
#print axioms tree_accounting
#print axioms finite_tree_lower_bound
end Track2Grover.CoupledHistory
