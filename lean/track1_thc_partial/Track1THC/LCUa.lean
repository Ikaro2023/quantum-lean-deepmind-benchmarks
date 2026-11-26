import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum

/-! Unitary with a prescribed real unit first column (via an orthonormal-basis extension). -/

namespace Track1THC.LCU

open Matrix

theorem exists_unitary_first_col {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    ∃ H : Matrix ι ι ℂ, H ∈ Matrix.unitaryGroup ι ℂ ∧ ∀ i, H i i0 = (a i : ℂ) := by
  classical
  let vec : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => (a i : ℂ))
  have hv : Orthonormal ℂ (({i0} : Set ι).domRestrict (fun _ : ι => vec)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = i0 := hi
    have hj' : j = i0 := hj
    subst hi' hj'
    simp only [Set.domRestrict, if_true]
    simp only [vec, PiLp.inner_apply, RCLike.inner_apply, Complex.conj_ofReal]
    rw [← Complex.ofReal_one, ← ha]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) (by simp) hv
  refine ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b, fun i => ?_⟩
  rw [Module.Basis.toMatrix_apply]
  simp [hb i0 rfl, vec]

end Track1THC.LCU
