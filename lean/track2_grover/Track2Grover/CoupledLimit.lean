import Track2Grover.CoupledPathBridge
import Track2Grover.LowerAccounts
import Track2Grover.LowerSeed

/-! Passing from finite source-tree lower bounds to arbitrary nested loops via a
single increasing fuel cap, measured on the frozen CQState semantics. -/
namespace Track2Grover.CoupledLimit
open CoupledLabels CoupledActions CoupledPathBridge Track2Grover.Path
open Operator ResourceCounting QuantumComputation.Specs Filter Finset Real Lower QProg
open scoped RealInnerProductSpace Topology NNReal ENNReal

private theorem score_nonneg {V : Type} {q h : ℕ} (O : Unitary (2^h)) (a : ℝ)
    (ha : 0 ≤ a) (P : Vec q → ℝ) (Q : Store V → Vec q → ℝ)
    (hP : ∀ u, 0 ≤ P u) (hQ : ∀ σ u, 0 ≤ Q σ u) (T : Tree V q h) (u) :
    0 ≤ score O a P Q T u := by
  induction T generalizing u with
  | timeout => exact hP _
  | halt σ => exact hQ _ _
  | fixed _ _ ih => exact ih _
  | query _ _ ih => exact add_nonneg (mul_nonneg ha (sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _)) (ih _)
  | measure _ _ ih => exact sum_nonneg fun i _ ↦ ih i _

theorem of_seed_semantics {n m k q : ℕ} {C : Circuit n m q} {bound : ℝ}
    (hk : 0 < k) (hkN : k ≤ 2^n) (σ : Store Grover.Var)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hangle : arcsin (√b) = arcsin (√((m:ℝ)*k/2^n)))
    (cor : Correct C k)
    (cost : ∃ z : Finset (Fin (2^n)) → ℝ≥0,
      (∀ S ∈ groverTargetSets n k, expectedCost (CostModel.ofEmbeddedOracle
        (groverParallelMarkingOracle m S)) (program C S) (seed q σ) ≤ (z S : ℝ≥0∞)) ∧
      (∑ S ∈ groverTargetSets n k, (z S : ℝ)) / (groverTargetSets n k).card ≤ bound)
    (inv : ∀ (r : QRegister ((n+1)*m) q) (S : Labels n k),
      Function.Involutive (act (r.embedUnitary (groverParallelMarkingOracle m S.1))))
    (compression : ∀ (r : QRegister ((n+1)*m) q) (y : Space q),
      (1-2*b)*(Fintype.card (Labels n k):ℝ)*‖y‖^2 ≤
        ∑ S : Labels n k, ⟪y, act (r.embedUnitary (groverParallelMarkingOracle m S.1)) y⟫)
    (prob : ∀ (O : Unitary (2^((n+1)*m))) (F : Finite Grover.Var q ((n+1)*m))
      (σ : Store Grover.Var) (g : Store Grover.Var → Prop) [DecidablePred g],
      ENNReal.ofReal (score O 0 (fun _ ↦ 0) (fun τ ψ ↦ if g τ then energy ψ else 0)
        (build F σ Tree.halt) (basisState 0)) = Fuel.obs (compile O F) (seed q σ) (fun τ ↦ ⌜g τ⌝))
    (price : ∀ (O : Unitary (2^((n+1)*m))) (F : Finite Grover.Var q ((n+1)*m)) (σ : Store Grover.Var),
      ENNReal.ofReal (score O 1 (fun _ ↦ 0) (fun _ _ ↦ 0) (build F σ Tree.halt) (basisState 0))
        ≤ expectedCost (CostModel.ofEmbeddedOracle O) (compile O F) (seed q σ)) :
    finiteBound n m k ≤ bound := by
  classical
  let L := Labels n k
  have hcard : 0 < (groverTargetSets n k).card := Finset.card_pos.mpr (by
    apply Finset.powersetCard_nonempty_of_le
    simpa using hkN)
  letI : Nonempty (Labels n k) := by
    obtain ⟨s,hs⟩ := Finset.card_pos.mp hcard
    exact ⟨⟨s,hs⟩⟩
  have hb : b ∈ Set.Icc 0 1 := ⟨hb0.le,hb1⟩
  let v := 2*arcsin (√b)
  have hv : 0 < v := mul_pos (by norm_num) (arcsin_pos.mpr (sqrt_pos.mpr hb0))
  let O (S : L) := groverParallelMarkingOracle m S.val
  let P (S : L) := C.compile QProg.qAssign (O S)
  let δ := seed q σ
  let T (i : ℕ) := build (cut i C) σ Tree.halt
  let u : Space q := WithLp.toLp 2 (basisState 0)
  have hu : ‖u‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    simp [u,EuclideanSpace.norm_sq_eq,basisState,Pi.single_apply]
  let x := copy (Labels n k) (Space q) u
  let out (S : L) := (interp (P S)).toStateFun δ
  have mout (S : L) : out S = (interp (program C S.val)).toStateFun δ := by
    simp [program,P,O,out,δ,seed_reset]
  have full (S : L) := correct_output_mass cor S.property δ
  have hbad i (S : Labels n k) : bad (T i) S (x S) = 0 := by
    let g (τ : Store Grover.Var) := ¬ OutputAverage.good S.val τ
    have h := prob (O S) (cut i C) σ g
    rw [compile_cut] at h
    have hh := (Fuel.cofinal (P S)).upper i δ (fun τ ↦ ⌜g τ⌝)
    have hz : Fuel.obs (P S) δ (fun τ ↦ ⌜g τ⌝) = 0 := by
      rw [Fuel.obs,FirstQuery.mass_wp]
      change ENNReal.ofReal (expect (out S) (fun τ ↦ ⌜g τ⌝)) = _
      rw [expect_ofProp,mout]
      change ENNReal.ofReal (((((interp (program C S.val)).toStateFun δ).restrict
        (fun τ ↦ ¬ witnessStore S.val τ)).trace : ℝ)) = 0
      simp [full S |>.2]
    have hz' := le_antisymm (h.le.trans (hh.trans hz.le)) bot_le
    have he (τ) (ψ : Vec q) : (if g τ then energy ψ else 0) =
        (if OutputAverage.good S.val τ then 0 else energy ψ) := by by_cases j : OutputAverage.good S.val τ <;> simp [g,j]
    simp_rw [he] at hz'
    apply le_antisymm (ENNReal.ofReal_eq_zero.mp hz') 
    exact score_nonneg _ _ le_rfl _ _ (by simp) (fun τ ψ ↦ by split_ifs <;> first | rfl | exact sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _) _ _
  let one (S : L) (i : ℕ) := score (O S) 0 (fun _ ↦ 0) (fun _ ↦ energy) (T i) (basisState 0)
  have hone (S : L) : Tendsto (one S) atTop (𝓝 1) := by
    let g (_ : Store Grover.Var) := True
    have hfull : Fuel.obs (P S) δ (fun τ ↦ ⌜g τ⌝) = 1 := by
      rw [Fuel.obs,FirstQuery.mass_wp]
      have htop : (fun τ : Store Grover.Var ↦ ⌜g τ⌝ : CQAssertion (Store Grover.Var) (2^q)) = ⊤ := by
        ext τ; simp [g]
      rw [htop,FirstQuery.mass,expect_top]
      change ENNReal.ofReal ((out S).trace:ℝ) = _
      rw [mout,(full S).1]; simp [δ,seed_trace]
    have hlim := (Fuel.cofinal (P S)).limit δ (fun τ ↦ ⌜g τ⌝)
    rw [hfull] at hlim
    have he i : ENNReal.ofReal (one S i) = Fuel.obs (Fuel.cap i (P S)) δ (fun τ ↦ ⌜g τ⌝) := by
      simpa only [one,T,g,ite_true,compile_cut] using prob (O S) (cut i C) σ g
    have hn i : 0 ≤ one S i := score_nonneg _ _ le_rfl _ _ (by simp) (fun _ _ ↦ sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _) _ _
    have hlim' := (ENNReal.tendsto_toReal (by simp : (1:ℝ≥0∞) ≠ ⊤)).comp hlim
    simpa only [Function.comp_def, ← he, ENNReal.toReal_ofReal (hn _),ENNReal.toReal_one] using hlim'
  have fsum : Tendsto (fun i ↦ finished (T i) x) atTop (𝓝 (Fintype.card L:ℝ)) := by
    change Tendsto (fun i ↦ ∑ S : L, one S i) atTop _
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using
      (tendsto_finsetSum univ (fun (S : L) _ ↦ hone S))
  obtain ⟨z, hz, hzmean⟩ := cost
  have hcost i : paid (T i) x ≤ (Fintype.card L:ℝ)*bound := by
    have hsum (S : L) : score (O S) 1 (fun _ ↦ 0) (fun _ _ ↦ 0) (T i) (basisState 0) ≤ (z S.val:ℝ) := by
      have h := price (O S) (cut i C) σ
      rw [compile_cut] at h
      have hc := hz S.val S.property
      simp only [program,expectedCost_qSeq,expectedCost_qSet,CostModel.ofEmbeddedOracle,Nat.cast_zero,mul_zero,
        zero_add,δ,seed_trace,ENNReal.coe_one,one_mul,interp_qSet,QMonad.Q.toStateFun_qSet,seed_reset] at hc
      have hbnd := (h.trans (Fuel.cap_cost _ _ _ _)).trans hc
      change ENNReal.ofReal (score (O S) 1 (fun _ ↦ 0) (fun _ _ ↦ 0)
        (T i) (basisState 0)) ≤ (z S.val : ℝ≥0∞) at hbnd
      have hnon := score_nonneg (O S) 1 (by norm_num) (fun _ ↦ 0) (fun _ _ ↦ 0)
        (by simp) (by simp) (T i) (basisState 0)
      simpa only [ENNReal.toReal_ofReal hnon,ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top hbnd
    apply (sum_le_sum (s := univ) (fun S _ ↦ hsum S)).trans
    rw [Finset.sum_coe_sort (groverTargetSets n k) (fun a ↦ (z a:ℝ)), Fintype.card_coe, mul_comm]
    exact (div_le_iff₀ (by exact_mod_cast hcard)).mp hzmean
  have hfin i := completion_le_queries hb (T i) u hu
    (run_of_path hk b hb (fun r S ↦ inv r S) compression (T i) x (hbad i))
  have hcpos : (0:ℝ) < Fintype.card L := by positivity
  have hl : c*(1-k/(2:ℝ)^n)*(Fintype.card L) ≤ v*((Fintype.card L:ℝ)*bound) := by
    apply le_of_tendsto (fsum.const_mul (c*(1-k/(2:ℝ)^n)))
    exact Eventually.of_forall fun i ↦ (hfin i).trans (mul_le_mul_of_nonneg_left (hcost i) hv.le)
  unfold finiteBound
  rw [← hangle]
  apply (div_le_iff₀ hv).mpr
  exact (le_of_mul_le_mul_right (by nlinarith only [hl]) hcpos)

theorem of_score_semantics {n m k q : ℕ} {C : Circuit n m q} {bound : ℝ}
    (hm : 0 < m) (hk : 0 < k) (hkN : k ≤ 2^n) (sparse : m*k ≤ 2^n)
    (cor : Correct C k) (cost : AvgBound C k bound)
    (inv : ∀ (r : QRegister ((n+1)*m) q) (S : Labels n k),
      Function.Involutive (act (r.embedUnitary (groverParallelMarkingOracle m S.1))))
    (compression : ∀ (r : QRegister ((n+1)*m) q) (y : Space q),
      (1-2*((m:ℝ)*k/2^n))*(Fintype.card (Labels n k):ℝ)*‖y‖^2 ≤
        ∑ S : Labels n k, ⟪y, act (r.embedUnitary (groverParallelMarkingOracle m S.1)) y⟫)
    (prob : ∀ (O : Unitary (2^((n+1)*m))) (F : Finite Grover.Var q ((n+1)*m))
      (σ : Store Grover.Var) (g : Store Grover.Var → Prop) [DecidablePred g],
      ENNReal.ofReal (score O 0 (fun _ ↦ 0) (fun τ ψ ↦ if g τ then energy ψ else 0)
        (build F σ Tree.halt) (basisState 0)) = Fuel.obs (compile O F) (seed q σ) (fun τ ↦ ⌜g τ⌝))
    (price : ∀ (O : Unitary (2^((n+1)*m))) (F : Finite Grover.Var q ((n+1)*m)) (σ : Store Grover.Var),
      ENNReal.ofReal (score O 1 (fun _ ↦ 0) (fun _ _ ↦ 0) (build F σ Tree.halt) (basisState 0))
        ≤ expectedCost (CostModel.ofEmbeddedOracle O) (compile O F) (seed q σ)) :
    finiteBound n m k ≤ bound := by
  let σ : Store Grover.Var := fun _ ↦ 0
  apply of_seed_semantics hk hkN σ ((m:ℝ)*k/2^n) (by positivity)
    ((div_le_one (by positivity : (0:ℝ)<2^n)).mpr (by exact_mod_cast sparse)) rfl cor
    _ inv compression prob price
  obtain ⟨z, hz, hzmean⟩ := cost
  exact ⟨z, fun S hS => by simpa [seed_trace] using hz S hS (seed q σ), hzmean⟩

#print axioms of_seed_semantics
#print axioms of_score_semantics
end Track2Grover.CoupledLimit
