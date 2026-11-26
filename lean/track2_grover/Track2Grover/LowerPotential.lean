import Track2Grover.LowerAnalysis
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Angular potential for adaptive stopping. All angles in the stopping inequality are
in the first quadrant. The two masses are the squared norms of complementary projections. -/
namespace Track2Grover.Lower
open Real

noncomputable def profile (t : ℝ) := if t ≤ π/4 then c-t else cos t ^ 2

private lemma at_corner : cos (π/4)^2 = 1/2 := by
  rw [cos_pi_div_four]
  nlinarith [sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]

private lemma cos_sq_lip (x y : ℝ) : |cos x ^ 2 - cos y ^ 2| ≤ |x-y| := by
  have h := abs_cos_sub_cos_le (2*x) (2*y)
  rw [cos_two_mul, cos_two_mul, show 2*cos x^2-1-(2*cos y^2-1) =
    2*(cos x^2-cos y^2) by ring, show 2*x-2*y = 2*(x-y) by ring,
    abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  linarith

private lemma mixed_lip {x y : ℝ} (hx : x ≤ π/4) (hy : π/4 ≤ y) :
    |(c-x)-cos y^2| ≤ |x-y| := by
  have h := cos_sq_lip (π/4) y
  rw [abs_of_nonpos (by linarith : π/4 - y ≤ 0), at_corner, abs_le] at h
  rw [abs_of_nonpos (by linarith : x-y ≤ 0), abs_le]
  unfold c
  constructor <;> linarith [h.1, h.2]

theorem profile_lipschitz (x y : ℝ) : |profile x-profile y| ≤ |x-y| := by
  unfold profile
  split_ifs with hx hy hy
  · rw [show c-x-(c-y) = -(x-y) by ring, abs_neg]
  · exact mixed_lip hx (le_of_not_ge hy)
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact mixed_lip hy (le_of_not_ge hx)
  · exact cos_sq_lip .. 

private lemma cos_sq_le_profile {x : ℝ} : cos x^2 ≤ profile x := by
  unfold profile
  split_ifs with h
  · have hh := cos_sq_lip x (π/4)
    rw [at_corner, abs_of_nonpos (sub_nonpos.mpr h), abs_le] at hh
    unfold c
    linarith [hh.2]
  · rfl

private lemma tangent_cos {x y : ℝ} (hx : x ∈ Set.Icc (-(π/2)) (π/2))
    (hy : y ∈ Set.Icc (-(π/2)) (π/2)) :
    cos y ≤ cos x - sin x * (y-x) := by
  have h := strictConcaveOn_cos_Icc.concaveOn
  rcases lt_trichotomy x y with hlt|heq|hgt
  · have hd := h.slope_le_of_hasDerivAt hx hy hlt (hasDerivAt_cos x)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hlt)] at hd
    linarith
  · subst y; simp
  · have hd := h.le_slope_of_hasDerivAt hy hx hgt (hasDerivAt_cos x)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hgt)] at hd
    linarith

private noncomputable def slopeAt (t : ℝ) := (sin (2*t))⁻¹
private noncomputable def lineAt (t u : ℝ) := c-t + slopeAt t*(u-cos t^2)

private lemma support_small {t b : ℝ} (ht : 0 < t) (ht' : t ≤ π/4)
    (hb : 0 ≤ b) (hb' : b ≤ π/4) : lineAt t (cos b^2) ≤ c-b := by
  have hst : 0 < sin (2*t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hh := tangent_cos (x := 2*t) (y := 2*b) ⟨by linarith [pi_pos], by linarith⟩
    ⟨by linarith [pi_pos], by linarith⟩
  rw [cos_two_mul, cos_two_mul] at hh
  unfold lineAt slopeAt
  rw [inv_mul_eq_div]
  have h : (cos b^2 - cos t^2) / sin (2*t) ≤ t-b := by
    apply (div_le_iff₀ hst).2
    nlinarith
  linarith

private lemma support {t b : ℝ} (ht : 0 < t) (ht' : t ≤ π/4)
    (hb : 0 ≤ b) (hb' : b ≤ π/2) : lineAt t (cos b^2) ≤ profile b := by
  unfold profile
  split_ifs with h
  · exact support_small ht ht' hb h
  have hh := support_small (b := π/4) ht ht' (by linarith [pi_pos]) le_rfl
  rw [at_corner] at hh
  have hst : 0 < sin (2*t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hslope : 1 ≤ slopeAt t := by
    unfold slopeAt
    rw [← one_div, le_div_iff₀ hst]
    simpa using sin_le_one (2*t)
  have hcos := cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos] : 0 ≤ π/4)
    (by linarith [pi_pos] : b ≤ π) (le_of_not_ge h)
  have hsquare : cos b ^ 2 ≤ 1/2 := by
    rw [← at_corner]
    apply pow_le_pow_left₀ _ hcos
    exact cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hb'⟩
  unfold lineAt at *
  dsimp [c] at *
  nlinarith [mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hsquare)]

theorem profile_supporting_line {a : ℝ} (ha : 0 < a) (ha' : a ≤ π/4) :
    ∃ A B : ℝ, profile a = A*cos a^2+B ∧
      ∀ b : ℝ, 0 ≤ b → b ≤ π/2 → A*cos b^2+B ≤ profile b := by
  refine ⟨slopeAt a, c-a-slopeAt a*cos a^2, ?_, ?_⟩
  · simp [profile, ha']
  · intro b hb hb'
    have h := support ha ha' hb hb'
    unfold lineAt at h
    linarith

theorem parallel_le_profile (a : ℝ) : cos a^2 ≤ profile a := cos_sq_le_profile

/-- Discarding a terminated orthogonal component can decrease the potential by at most
`c` times its hidden-uniform projection mass. There is no restriction on the proportion
of discarded complementary mass. -/
theorem stopping_loss {s r a b : ℝ} (_hs : 0 ≤ s) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (ha' : a ≤ π/2) (hb : 0 ≤ b) (hb' : b ≤ π/2)
    (hparallel : r*cos b^2 ≤ s*cos a^2)
    (hperp : r*(1-cos b^2) ≤ s*(1-cos a^2)) :
    s*profile a - r*profile b ≤ c*(s*cos a^2-r*cos b^2) := by
  have hcos_nonneg : 0 ≤ 1-cos b^2 := by nlinarith [sin_sq_add_cos_sq b, sq_nonneg (sin b)]
  rcases eq_or_lt_of_le ha with he|hapos
  · subst a
    simp only [cos_zero, one_pow, mul_one, sub_self, mul_zero] at hparallel hperp ⊢
    have heq := (mul_nonneg hr hcos_nonneg).antisymm' hperp
    rcases mul_eq_zero.mp heq with hzero|hzero
    · rw [hzero]; simp [profile, show (0:ℝ) ≤ π/4 by positivity, mul_comm]
    have hb0 : b = 0 := by
      have hcosb : 0 ≤ cos b := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hb'⟩
      have hcosb1 : cos b = 1 := by nlinarith [cos_le_one b]
      exact (injOn_cos ⟨hb, by linarith [pi_pos]⟩ ⟨le_rfl, pi_pos.le⟩
        (hcosb1.trans cos_zero.symm))
    subst b
    simp [profile, show (0:ℝ) ≤ π/4 by positivity]
    ring_nf
    rfl
  by_cases haa : a ≤ π/4
  · let B := lineAt a 0
    let A := lineAt a 1
    have hA : A ≤ c := by
      have h := support_small (b := 0) hapos haa le_rfl (by positivity)
      simpa [A] using h
    have hB : B ≤ 0 := by
      have hh := support (b := π/2) hapos haa (by positivity) le_rfl
      simpa [profile, show ¬ π/2 ≤ π/4 by linarith [pi_pos], B] using hh
    have hlin (x : ℝ) : A*x + B*(1-x) = lineAt a x := by dsimp [A,B,lineAt]; ring
    have heqa : A*cos a^2 + B*(1-cos a^2) = profile a := by rw [hlin]; simp [lineAt,profile,haa]
    have hleb : A*cos b^2 + B*(1-cos b^2) ≤ profile b := hlin _ ▸ support hapos haa hb hb'
    rw [← heqa]
    nlinarith only [mul_le_mul_of_nonneg_left hleb hr,
      mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hparallel),
      mul_nonpos_of_nonpos_of_nonneg hB (sub_nonneg.mpr hperp)]
  · have hc : 1 ≤ c := by unfold c; linarith [two_le_pi]
    rw [profile, ite_eq_right_iff.mpr (by simp [haa])]
    nlinarith only [mul_le_mul_of_nonneg_left (cos_sq_le_profile (x := b)) hr,
      mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hparallel)]

theorem query_loss {s a b v : ℝ} (hs : 0 ≤ s) (hab : |a-b| ≤ v) :
    s*profile a - s*profile b ≤ s*v := by
  have h := (le_abs_self (profile a-profile b)).trans ((profile_lipschitz a b).trans hab)
  nlinarith [mul_le_mul_of_nonneg_left h hs]

#print axioms profile_lipschitz
#print axioms profile_supporting_line
#print axioms parallel_le_profile
#print axioms stopping_loss
#print axioms query_loss
end Track2Grover.Lower
