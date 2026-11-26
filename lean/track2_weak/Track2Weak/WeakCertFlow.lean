module

public import Track2Weak.WeakCertSound

@[expose] public section
namespace Track2Weak.Cert
open QuantumComputation.Specs.DickeSol Real
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

/-- The undecided branch and the survival-weighted duration used in one pass. -/
noncomputable def runOrbit (n : Nat) : List Row → V → V × ℝ
  | [], x => (x,0)
  | q :: qs, x =>
    let (out, tail) := runOrbit n qs (weakKeep 512 q.factor (q.walk n x))
    (out, (q.time:ℝ)/oneB * vecSqNorm x + tail)

/-- Connected input and output vectors and integer upper/lower accounts. -/
inductive Chain : List Row → List Int → Nat → Nat → Nat → Nat → Nat → Prop
  | nil {v p s c} : Chain [] v p s c s c
  | cons {q qs v p s c us uc} (ok : RowOK q) (hv : v = q.before) (hp : p = q.inPad)
      (rest : Chain qs q.filtered q.postPad (s+q.click12) (c+q.time*(oneT-s)) us uc) :
      Chain (q::qs) v p s c us uc

theorem Chain.rowOK {qs v p s c us uc} (h : Chain qs v p s c us uc) {q : Row}
    (hq : q ∈ qs) : RowOK q := by
  induction h with
  | nil => simp at hq
  | cons ok hv hp rest ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ok
    · exact ih hq

theorem Chain.sound {qs v p s c us uc} (h : Chain qs v p s c us uc)
    {n : Nat} (hn : 80000 ≤ n) {x : V}
    (herr : vecNorm (x-rkmListToOrbVec 512 v) ≤ p / wdScaleR)
    (hmass : vecSqNorm x ≤ 1 - s / (oneT:ℝ)) :
    vecSqNorm (runOrbit n qs x).1 ≤ 1 - us / (oneT:ℝ) ∧
      (c:ℝ)/((oneB:ℝ)*oneT) + (runOrbit n qs x).2 ≤ uc/((oneB:ℝ)*oneT) := by
  induction h generalizing x with
  | nil => exact ⟨hmass, by simp [runOrbit]⟩
  | @cons q qs v p s c us uc h hv hp rest ih =>
    subst v; subst p
    let y := q.walk n x
    let z := weakKeep 512 q.factor y
    have hs1 : (s:ℝ)/(oneT:ℝ) ≥ 0 := by positivity
    have hx : vecNorm x ≤ 1 := by nlinarith [sq_vecNorm x]
    have hy := h.error hn hx herr
    have hz : vecNorm (z-rkmListToOrbVec 512 q.filtered) ≤ q.postPad / wdScaleR := by
      have hw := weak_keep_propagates 512 h.factor_sq hy h.filtered_error
      dsimp only [z,y]
      linarith
    have hcl := h.click_lower hy
    have hsqrt : (√(1-q.factor^2))^2 = 1-q.factor^2 := Real.sq_sqrt (sub_nonneg.mpr h.factor_sq)
    have htot := weak_branch_mass 512 (s:=√(1-q.factor^2)) (by linarith : q.factor^2+(√(1-q.factor^2))^2=1) y
    rw [show 512 = topBin.val from rfl, weak_click_mass, hsqrt] at htot
    have hyy : vecSqNorm y = vecSqNorm x := by
      rw [← sq_vecNorm y, ← sq_vecNorm x, q.norm_walk hn]
    have hs' : vecSqNorm z ≤ 1 - ((s+q.click12:Nat):ℝ) / oneT := by
      dsimp only [z]
      rw [Nat.cast_add, add_div]
      change _ ≤ (1-q.factor^2) * (y topBin)^2 at hcl
      change vecSqNorm (weakKeep 512 q.factor y) + _ = _ at htot
      linarith
    obtain ⟨h1,h2⟩ := ih hz hs'
    have hsq := vecSqNorm_nonneg x
    have hsle : s ≤ oneT := by
      have hr : (s:ℝ) / oneT ≤ 1 := by linarith
      have := (div_le_one (show (0:ℝ)<oneT by norm_num [oneT])).mp hr
      exact_mod_cast this
    simp only [runOrbit]
    change vecSqNorm (runOrbit n qs z).1 ≤ _ ∧
      (c:ℝ)/((oneB:ℝ)*oneT) + (q.time/ (oneB:ℝ) * vecSqNorm x + (runOrbit n qs z).2) ≤ _
    refine ⟨h1, le_trans ?_ h2⟩
    push_cast [Nat.cast_sub hsle]
    have ht : (0:ℝ) ≤ q.time / (oneB:ℝ) := by positivity
    have hc := mul_le_mul_of_nonneg_left hmass ht
    norm_num [oneB,oneT] at hc ⊢
    linarith only [hc]

theorem initialError {n : Nat} (hn : 80000 ≤ n) :
    vecNorm (Sub.sub (α:=V) (u0OrbVecGen (2^n) 1024 512) (rkmListToOrbVec 512 [Int.ofNat wdScale])) ≤
      (1:ℝ)/wdScaleR := by
  let e : V := Pi.single (0:Fin 513) 1
  have he : e = rkmListToOrbVec 512 [Int.ofNat wdScale] := by
    funext i
    by_cases h : i=0
    · subst i; norm_num [e,rkmListToOrbVec,wdScaleR,wdScale]
    · have hne : i.val ≠ 0 := fun hi ↦ h (Fin.ext hi)
      obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
      simp [e, Pi.single_eq_of_ne h, rkmListToOrbVec, hj]
  rw [← he]
  have h := vecNorm_u0OrbVecGen_sub_e0_le (m:=1024) (r:=512) hn (by decide) (by decide) (by decide) (by decide)
  apply h.trans
  norm_num [wdScale, wdScaleR]

theorem initialMass {n : Nat} (hn : 80000 ≤ n) :
    vecSqNorm (u0OrbVecGen (2^n) 1024 512) ≤ 1 - ((0:Nat):ℝ)/(oneT:ℝ) := by
  have hN : 2^12 ≤ (2:Nat)^n := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨R, _, hr⟩ := Finset.exists_subset_card_eq (s:=Finset.univ (α:=Fin (2^n))) (n:=512)
    (by simp; omega)
  have hmr : 1024 + R.card ≤ 2^n := by omega
  have hd := dot_orbEmbedGen hmr (u0OrbVecGen (2^n) 1024 R.card) (u0OrbVecGen (2^n) 1024 R.card)
  rw [orbEmbedGen_u0OrbVecGen hmr] at hd
  rw [hr] at hd
  have hm := sum_sq_u0Vec (N:=2^n) (m:=1024) (by omega)
  simp only [vecSqNorm, sq, Nat.cast_zero, zero_div, sub_zero]
  simpa only [sq, hd] using hm.le

end Track2Weak.Cert
