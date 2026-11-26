module

public import Track2Grover.Engine.Rk128kEngine
import all Track2Grover.Engine.Rk128kEngine

/-! Finite-dimensional real Johnson-orbit filters and certified conditioned evolution. -/
@[expose] public section

namespace QuantumComputation.Specs.DickeSol
open Matrix Real
open scoped Matrix

/-- No-click branch for a filter that acts on a single intersection-size bin. -/
def weakKeep {d : ℕ} (r : ℕ) (a : ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  if i.val = r then a * x i else x i

/-- Click branch. Its support consists entirely of the chosen intersection-size bin. -/
def weakClick {d : ℕ} (r : ℕ) (s : ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  if i.val = r then s * x i else 0

def weakSubset {N m : ℕ} (R : Finset (Fin N)) (r : ℕ)
    (yes no : ℝ) (x : SymSubset N m → ℝ) (E : SymSubset N m) : ℝ :=
  (if (E.1 ∩ R).card = r then yes else no) * x E

theorem weakSubset_keep_orb {N m : ℕ} (R : Finset (Fin N)) (r : ℕ) (a : ℝ)
    (x : Fin (orbDim m R.card) → ℝ) :
    weakSubset R r a 1 (orbEmbedGen N m R x) = orbEmbedGen N m R (weakKeep r a x) := by
  funext E
  by_cases h : (E.1 ∩ R).card = r <;> simp [weakSubset, weakKeep, orbEmbedGen, h, mul_div_assoc]

theorem weakSubset_click_orb {N m : ℕ} (R : Finset (Fin N)) (r : ℕ) (s : ℝ)
    (x : Fin (orbDim m R.card) → ℝ) :
    weakSubset R r s 0 (orbEmbedGen N m R x) = orbEmbedGen N m R (weakClick r s x) := by
  funext E
  by_cases h : (E.1 ∩ R).card = r <;> simp [weakSubset, weakClick, orbEmbedGen, h, mul_div_assoc]

theorem weak_branch_mass {d : ℕ} (r : ℕ) {a s : ℝ} (h : a ^ 2 + s ^ 2 = 1)
    (x : Fin d → ℝ) :
    vecSqNorm (weakKeep r a x) + vecSqNorm (weakClick r s x) = vecSqNorm x := by
  unfold vecSqNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val = r
  · simp only [weakKeep, weakClick, hi, ite_true, mul_pow]
    rw [← add_mul, h, one_mul]
  · simp [weakKeep, weakClick, hi]

theorem weak_click_mass {d : ℕ} (i : Fin d) (s : ℝ) (x : Fin d → ℝ) :
    vecSqNorm (weakClick i.val s x) = s ^ 2 * x i ^ 2 := by
  unfold vecSqNorm
  rw [Fintype.sum_eq_single i]
  · simp [weakClick, mul_pow]
  · intro j hj
    have hne : j.val ≠ i.val := fun h ↦ hj (Fin.ext h)
    rw [weakClick, ite_eq_right hne]
    norm_num

theorem weak_keep_norm {d : ℕ} (r : ℕ) {a : ℝ} (ha : a ^ 2 ≤ 1) (x : Fin d → ℝ) :
    vecNorm (weakKeep r a x) ≤ vecNorm x := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val = r
  · simpa only [weakKeep, hi, ite_true, mul_pow, one_mul] using
      mul_le_mul_of_nonneg_right ha (sq_nonneg (x i))
  · simp [weakKeep, hi]

theorem weak_keep_nonexpansive {d : ℕ} (r : ℕ) {a : ℝ} (ha : a ^ 2 ≤ 1) (x y : Fin d → ℝ) :
    vecNorm (weakKeep r a x - weakKeep r a y) ≤ vecNorm (x - y) := by
  have h : weakKeep r a x - weakKeep r a y = weakKeep r a (x-y) := by
    funext i
    by_cases hi : i.val = r <;> simp [weakKeep, hi, mul_sub]
  rw [h]
  exact weak_keep_norm r ha _

/-- A certified walk output may be followed by a rounded attenuation. -/
theorem weak_keep_propagates {d : ℕ} (r : ℕ) {a : ℝ} (ha : a ^ 2 ≤ 1)
    {x y rounded : Fin d → ℝ} {walkPad roundingPad : ℝ}
    (hw : vecNorm (x-y) ≤ walkPad)
    (hr : vecNorm (weakKeep r a y - rounded) ≤ roundingPad) :
    vecNorm (weakKeep r a x - rounded) ≤ walkPad + roundingPad := by
  rw [show weakKeep r a x - rounded =
      (weakKeep r a x - weakKeep r a y) + (weakKeep r a y - rounded) by abel]
  exact (vecNorm_add_le _ _).trans (add_le_add ((weak_keep_nonexpansive r ha x y).trans hw) hr)



/-- A caller may start the verified finite-n Johnson step at any subnormalized orbital vector. -/
theorem weak_segment_error {n m lTableMax r lPrev dCur accPad lOut dOut padWalk : ℕ}
    {seg : Rkm128kSeg} {vec next : List ℤ} {x : Fin (orbDim (seg.lS * m) r) → ℝ}
    (hn : 80000 ≤ n) (hr : 2 ≤ r) (hr' : r ≤ 1024)
    (hx : vecNorm x ≤ 1) (hlen : vec.length ≤ min (seg.lS * m) r + 1)
    (hseg : rkm128kRunOneSeg m lTableMax r seg lPrev dCur accPad vec = (lOut,dOut,padWalk,next))
    (hout : lOut ≠ 0) :
    vecNorm (rkmMaskSignVec (min (seg.lS * m) r) seg.mask
      (((dAltStepOrbMat (2 ^ n) (seg.lS * m) r) ^ altStepCount seg.tau9 seg.nSub (2 ^ n)) *ᵥ x) -
      rkmListToOrbVec (min (seg.lS * m) r) next) ≤
      vecNorm (x - rkmListToOrbVec (min (seg.lS * m) r) vec) +
        ((padWalk : ℝ) - (accPad : ℝ) - 1 / 2) / wdScaleR := by
  obtain ⟨_, _, _, _, _, _, _, _, _, mid, _, h⟩ :=
    rkm128kRunOneSeg_sound hn hr hr' hx hlen hseg hout
  refine le_trans ?_ h
  convert vecNorm_add_le (_ - mid) (mid - _) using 1
  congr 1
  abel

/-- The physical sign-mask and walk segment preserve the orbital representation. -/
theorem weak_segment_orbit {n m lS tau9 nSub : ℕ} {mask : List Bool} {R : Finset (Fin (2 ^ n))}
    (hn : 80000 ≤ n) (hm : lS * m ≤ 8192) (hr : R.card ≤ 1024)
    (x : Fin (orbDim (lS * m) R.card) → ℝ) :
    evalMuxSymOps R (rkmSegOps n m R.card lS tau9 nSub mask) (orbEmbedGen (2 ^ n) (lS*m) R x) =
      orbEmbedGen (2 ^ n) (lS*m) R (rkmMaskSignVec (min (lS*m) R.card) mask
      (((dAltStepOrbMat (2 ^ n) (lS*m) R.card) ^ altStepCount tau9 nSub (2 ^ n)) *ᵥ x)) :=
  rkm128k_evalSegOps_orbEmbedGen hn hm hr x
end QuantumComputation.Specs.DickeSol

#print axioms QuantumComputation.Specs.DickeSol.weak_branch_mass
#print axioms QuantumComputation.Specs.DickeSol.weak_keep_propagates
