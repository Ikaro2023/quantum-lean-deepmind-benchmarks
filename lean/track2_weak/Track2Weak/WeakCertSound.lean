module

public import Track2Weak.WeakWalk

@[expose] public section
namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol Matrix Real
open scoped Matrix
set_option maxRecDepth 6000

/-- One fixed-width row for the finite-dimensional conditioned walk. -/
structure Row where
  time : Nat
  substeps : Nat
  degree : Nat
  mask : List Bool
  atten : Nat
  inPad : Nat
  walkPad : Nat
  postPad : Nat
  click12 : Nat
  before : List Int
  after : List Int
  filtered : List Int

def Row.seg (q : Row) : Rkm128kSeg := ⟨1,q.time,q.substeps,q.degree,q.mask⟩

abbrev V := Fin 513 → ℝ
def oneB : Nat := 1000000000
def oneT : Nat := 1000000000000
def topBin : Fin 513 := ⟨512, by decide⟩
noncomputable def Row.factor (q : Row) : ℝ := (q.atten : ℝ) / oneB
def Row.lowerAmp (q : Row) : Nat := (q.after.getD 512 0).natAbs - q.walkPad

structure RowOK (q : Row) : Prop where
  run : rkm128kRunOneSeg 1024 2 512 q.seg 1 512 q.inPad q.before = (1,512,q.walkPad,q.after)
  lens : q.before.length ≤ 513 ∧ 512 < q.after.length
  atten_le : q.atten ≤ oneB
  post : q.filtered = q.after.set 512 (q.filtered.getD 512 0)
  rounded : ((q.atten : Int) * q.after.getD 512 0 - (oneB : Int) * q.filtered.getD 512 0).natAbs +
    oneB * q.walkPad ≤ oneB * q.postPad
  click : q.click12 * (oneB^2 * wdScale^2) ≤
    (oneB^2 - q.atten^2) * q.lowerAmp^2 * oneT

noncomputable def Row.walk (q : Row) (n : Nat) (x : V) : V :=
  rkmMaskSignVec 512 q.mask (((dAltStepOrbMat (2^n) 1024 512) ^
    altStepCount q.time q.substeps (2^n)) *ᵥ x)

theorem Row.norm_walk (q : Row) {n : Nat} (hn : 80000 ≤ n) (x : V) :
    vecNorm (q.walk n x) = vecNorm x := by
  have hN : 2^12 ≤ (2:Nat)^n := Nat.pow_le_pow_right (by decide) (by omega)
  have hO := dAltStepOrbMat_orthogonal_two_pow (m:=1024) (r:=512) (n:=n) (by omega)
    (by omega) (by omega)
  unfold Row.walk
  rw [vecNorm_rkmMaskSignVec]
  generalize altStepCount q.time q.substeps (2^n) = k
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, vecNorm_mulVec_of_orthogonal hO]

theorem RowOK.error {q : Row} (h : RowOK q) {n : Nat} (hn : 80000 ≤ n) {x : V}
    (hx : vecNorm x ≤ 1)
    (herr : vecNorm (x-rkmListToOrbVec 512 q.before) ≤ q.inPad / wdScaleR) :
    vecNorm (q.walk n x - rkmListToOrbVec 512 q.after) ≤ q.walkPad / wdScaleR := by
  have h1 := weak_segment_error (seg:=q.seg) (m:=1024) (r:=512)
    (lTableMax:=2) (lPrev:=1) (dCur:=512) (accPad:=q.inPad) (lOut:=1)
    (dOut:=512) (padWalk:=q.walkPad) (vec:=q.before) (next:=q.after) (x:=x) hn
    (by decide) (by decide) hx h.lens.1 h.run (by decide)
  change vecNorm (q.walk n x - rkmListToOrbVec 512 q.after) ≤
    vecNorm (x-rkmListToOrbVec 512 q.before) + _ at h1
  have hB : (0:ℝ) < wdScaleR := by norm_num [wdScaleR, wdScale]
  linarith [div_pos (by norm_num : (0:ℝ)<1/2) hB,
    show ((q.walkPad:ℝ)-q.inPad-1/2)/wdScaleR =
      q.walkPad/wdScaleR - q.inPad/wdScaleR - (1/2)/wdScaleR by ring]

theorem RowOK.factor_sq {q : Row} (h : RowOK q) : q.factor ^ 2 ≤ 1 := by
  have h0 : 0 ≤ q.factor := by unfold Row.factor; positivity
  have h1 : q.factor ≤ 1 := by
    unfold Row.factor
    rw [div_le_one (by norm_num [oneB])]
    exact_mod_cast h.atten_le
  nlinarith

private theorem cast_abs (z : ℤ) : |(z : ℝ)| = (z.natAbs : ℝ) := by
  cases z <;> simp [Int.negSucc_eq]

theorem RowOK.filtered_error {q : Row} (h : RowOK q) :
    vecNorm (weakKeep 512 q.factor (rkmListToOrbVec 512 q.after) -
      rkmListToOrbVec 512 q.filtered) ≤ (q.postPad : ℝ)/wdScaleR - q.walkPad/wdScaleR := by
  set z := q.after.getD 512 0
  set w := q.filtered.getD 512 0
  set delta := (q.atten : ℤ)*z - (oneB : ℤ)*w
  have hd : (delta.natAbs : ℝ) + (oneB:ℝ)*q.walkPad ≤ (oneB:ℝ)*q.postPad := by
    exact_mod_cast h.rounded
  have hnorm : vecNorm (weakKeep 512 q.factor (rkmListToOrbVec 512 q.after) -
      rkmListToOrbVec 512 q.filtered) = |q.factor * ((z:ℝ)/wdScaleR) - (w:ℝ)/wdScaleR| := by
    unfold vecNorm vecSqNorm
    rw [Fintype.sum_eq_single topBin]
    · simp [weakKeep, topBin, rkmListToOrbVec, z, w, Real.sqrt_sq_eq_abs]
    · intro i hi
      have hne : 512 ≠ i.val := fun e ↦ hi (Fin.ext e.symm)
      have hf : q.filtered.getD i.val 0 = q.after.getD i.val 0 := by
        conv_lhs => rw [h.post]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
      simp only [Pi.sub_apply, weakKeep, if_neg (Ne.symm hne), rkmListToOrbVec, hf, sub_self, zero_pow two_ne_zero]
  have eq : q.factor * ((z:ℝ)/wdScaleR) - (w:ℝ)/wdScaleR =
      (delta:ℝ) / ((oneB:ℝ)*wdScaleR) := by
    simp [delta, Row.factor, oneB, wdScaleR, wdScale]
    ring
  rw [hnorm, eq, abs_div, cast_abs, abs_of_pos (by norm_num [oneB,wdScaleR,wdScale])]
  norm_num [oneB,wdScaleR,wdScale] at hd ⊢
  linarith

theorem RowOK.click_lower {q : Row} (h : RowOK q) {y : V}
    (herr : vecNorm (y-rkmListToOrbVec 512 q.after) ≤ q.walkPad/wdScaleR) :
    q.click12 / (oneT:ℝ) ≤ (1-q.factor^2)*(y topBin)^2 := by
  have hc := (abs_apply_le_vecNorm (y-rkmListToOrbVec 512 q.after) topBin).trans herr
  change |y topBin - ((q.after.getD 512 0 : ℤ) : ℝ)/wdScaleR| ≤ _ at hc
  have hB : (0:ℝ) < wdScaleR := by norm_num [wdScaleR,wdScale]
  have ha : (q.lowerAmp : ℝ)/wdScaleR ≤ |y topBin| := by
    unfold Row.lowerAmp
    by_cases he : (q.after.getD 512 0).natAbs ≤ q.walkPad
    · rw [Nat.sub_eq_zero_of_le he]
      simpa using abs_nonneg (y topBin)
    · rw [Nat.cast_sub (by omega), sub_div, ← cast_abs]
      have habs (v : ℝ) : |v / wdScaleR| = |v| / wdScaleR := by rw [abs_div, abs_of_pos hB]
      rw [← habs]
      have hl := abs_sub_abs_le_abs_sub (((q.after.getD 512 0 : ℤ):ℝ)/wdScaleR) (y topBin)
      rw [abs_sub_comm] at hl
      linarith
  have hs := pow_le_pow_left₀ (by positivity) ha 2
  rw [sq_abs] at hs
  have hAtt : q.atten^2 ≤ oneB^2 := Nat.pow_le_pow_left h.atten_le 2
  have ht := h.click
  have hr : (q.click12:ℝ)*((oneB:ℝ)^2*(wdScale:ℝ)^2) ≤
      (((oneB:ℝ)^2-(q.atten:ℝ)^2)*(q.lowerAmp:ℝ)^2)*(oneT:ℝ) := by
    have hcast : ((q.click12 * (oneB^2 * wdScale^2):Nat):ℝ) ≤
        (((oneB^2 - q.atten^2) * q.lowerAmp^2 * oneT:Nat):ℝ) := by exact_mod_cast ht
    push_cast [Nat.cast_sub hAtt] at hcast
    exact hcast
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr h.factor_sq))
  norm_num [Row.factor, oneB, oneT, wdScaleR, wdScale, div_pow] at hr ⊢
  nlinarith only [hr]

end Track2Weak.Cert
