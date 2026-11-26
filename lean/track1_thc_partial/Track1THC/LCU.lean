import QuantumComputationSpecs.Primitives.THCFactorization
import Track1THC.LCUa

/-!
# Abstract LCU block-encoding lemma (Track 1, Round 2)

For arbitrary `k` (system qubits) and `m` (ancilla qubits), with the system on wires `0 .. k-1`
(`QRegister.block 0 k`) and the ancilla on wires `k .. k+m-1` (`QRegister.block k m`), we show:

*If* `S` is a Hermitian involution on the `k + m` wires (a "SELECT"), `W₀` is any unitary on the
ancilla whose first column is the real amplitude vector `a`, and the top-left ancilla blocks of `S`
satisfy `A = α ∑ₓ ∑ᵧ aₓ aᵧ S_{xy}`, *then* `U = W† S W` (with `W = embed W₀`) is a self-inverse
unitary and `IsQubitizedBlockEncodingUnitary α A U` holds.

We also give a Householder construction of a unitary with prescribed real first column
(`exists_unitary_first_col`), so the existence of `W₀` is not an assumption.

The index-splitting lemmas `blockSplit*` / `*_env_eq_iff_*` are adapted from the read-only
DeepMind `CatalystCleanBridge.lean` (Apache-2.0, Copyright 2026 Google LLC), which is not
imported (it depends on P450-specific modules).
-/

namespace Track1THC.LCU

open QuantumComputation.Specs Operator Matrix
open scoped Matrix

/-! ## Block splitting of `k + m` wires -/

/-- System block (low `k` wires). -/
abbrev sysR (k m : ℕ) : QRegister k (k + m) := QRegister.block 0 k (by omega)
/-- Ancilla block (high `m` wires). -/
abbrev ancR (k m : ℕ) : QRegister m (k + m) := QRegister.block k m le_rfl

/-- Computational-basis bijection `Fin (2^(k+m)) ≃ Fin (2^k) × Fin (2^m)` (system, ancilla). -/
noncomputable def split (k m : ℕ) : Fin (2 ^ (k + m)) ≃ Fin (2 ^ k) × Fin (2 ^ m) where
  toFun g := ((sysR k m).extractIndex g, (ancR k m).extractIndex g)
  invFun p := (basisBits (k + m)).symm (Fin.addCases (basisBits k p.1) (basisBits m p.2))
  left_inv g := by
    apply (basisBits (k + m)).injective
    rw [(basisBits (k + m)).apply_symm_apply]
    funext idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simp only [Fin.addCases_left]
      rw [(sysR k m).basisBits_extractIndex]
      refine congrArg (basisBits (k + m) g) ?_
      ext
      simp [sysR]
    · simp only [Fin.addCases_right]
      rw [(ancR k m).basisBits_extractIndex]
      congr 1
  right_inv := by
    rintro ⟨x, y⟩
    set g := (basisBits (k + m)).symm (Fin.addCases (basisBits k x) (basisBits m y))
    have hg : basisBits (k + m) g = Fin.addCases (basisBits k x) (basisBits m y) :=
      (basisBits (k + m)).apply_symm_apply _
    ext1
    · apply (basisBits k).injective
      funext i
      change basisBits k ((sysR k m).extractIndex g) i = basisBits k x i
      rw [(sysR k m).basisBits_extractIndex]
      have hw : sysR k m i = Fin.castAdd m i := by ext; simp [sysR]
      rw [hw]
      exact (congrFun hg (Fin.castAdd m i)).trans (Fin.addCases_left i)
    · apply (basisBits m).injective
      funext j
      change basisBits m ((ancR k m).extractIndex g) j = basisBits m y j
      rw [(ancR k m).basisBits_extractIndex]
      have hw : ancR k m j = Fin.natAdd k j := by ext; simp [ancR]
      rw [hw]
      exact (congrFun hg (Fin.natAdd k j)).trans (Fin.addCases_right j)

/-- System index of a global basis index. -/
noncomputable abbrev sysIdx (k m : ℕ) (g : Fin (2 ^ (k + m))) : Fin (2 ^ k) :=
  (sysR k m).extractIndex g
/-- Ancilla index of a global basis index. -/
noncomputable abbrev ancIdx (k m : ℕ) (g : Fin (2 ^ (k + m))) : Fin (2 ^ m) :=
  (ancR k m).extractIndex g

@[simp] theorem sysIdx_symm (k m : ℕ) (x : Fin (2 ^ k)) (y : Fin (2 ^ m)) :
    sysIdx k m ((split k m).symm (x, y)) = x :=
  congrArg Prod.fst ((split k m).apply_symm_apply (x, y))

@[simp] theorem ancIdx_symm (k m : ℕ) (x : Fin (2 ^ k)) (y : Fin (2 ^ m)) :
    ancIdx k m ((split k m).symm (x, y)) = y :=
  congrArg Prod.snd ((split k m).apply_symm_apply (x, y))

theorem split_apply (k m : ℕ) (g : Fin (2 ^ (k + m))) :
    split k m g = (sysIdx k m g, ancIdx k m g) := rfl

theorem sum_split (k m : ℕ) (F : Fin (2 ^ (k + m)) → ℂ) :
    ∑ g, F g = ∑ i : Fin (2 ^ k), ∑ x : Fin (2 ^ m), F ((split k m).symm (i, x)) := by
  rw [← Equiv.sum_comp (split k m).symm F, Fintype.sum_prod_type]

private theorem sys_env_eq_iff (k m : ℕ) (i j : Fin (2 ^ (k + m))) :
    ((sysR k m).basisSplitEquiv i).2 = ((sysR k m).basisSplitEquiv j).2 ↔
      ancIdx k m i = ancIdx k m j := by
  rw [(sysR k m).basisSplit_environment_eq_iff, ← (basisBits m).apply_eq_iff_eq, funext_iff]
  simp only [QRegister.AgreeOutside, ancIdx, QRegister.basisBits_extractIndex]
  constructor
  · intro h idx
    apply h (ancR k m idx)
    rintro ⟨l, hl⟩
    have hv := congrArg Fin.val hl
    simp [sysR, ancR, QRegister.block] at hv
    omega
  · intro h w hw
    have hge : k ≤ w.val := by
      by_contra hlt
      exact hw ⟨⟨w.val, by omega⟩, by ext; simp [sysR]⟩
    have hw_eq : w = ancR k m ⟨w.val - k, by omega⟩ := by
      ext
      simp [ancR]
      omega
    rw [hw_eq]
    exact h ⟨w.val - k, by omega⟩

private theorem anc_env_eq_iff (k m : ℕ) (i j : Fin (2 ^ (k + m))) :
    ((ancR k m).basisSplitEquiv i).2 = ((ancR k m).basisSplitEquiv j).2 ↔
      sysIdx k m i = sysIdx k m j := by
  rw [(ancR k m).basisSplit_environment_eq_iff, ← (basisBits k).apply_eq_iff_eq, funext_iff]
  simp only [QRegister.AgreeOutside, sysIdx, QRegister.basisBits_extractIndex]
  constructor
  · intro h idx
    apply h (sysR k m idx)
    rintro ⟨r, hr⟩
    have hv := congrArg Fin.val hr
    simp [sysR, ancR, QRegister.block] at hv
    omega
  · intro h w hw
    have hlt : w.val < k := by
      by_contra hge
      exact hw ⟨⟨w.val - k, by omega⟩, by ext; simp [ancR]; omega⟩
    have hw_eq : w = sysR k m ⟨w.val, hlt⟩ := by
      ext
      simp [sysR]
    rw [hw_eq]
    exact h ⟨w.val, hlt⟩

theorem embedSys_apply (k m : ℕ) (A : Operator (2 ^ k)) (g h : Fin (2 ^ (k + m))) :
    (sysR k m).embedMatrix A g h =
      A (sysIdx k m g) (sysIdx k m h) * if ancIdx k m g = ancIdx k m h then 1 else 0 := by
  rw [QRegister.embedMatrix_apply]
  simp only [sys_env_eq_iff]

theorem embedAnc_apply (k m : ℕ) (B : Operator (2 ^ m)) (g h : Fin (2 ^ (k + m))) :
    (ancR k m).embedMatrix B g h =
      B (ancIdx k m g) (ancIdx k m h) * if sysIdx k m g = sysIdx k m h then 1 else 0 := by
  rw [QRegister.embedMatrix_apply]
  simp only [anc_env_eq_iff]

theorem proj_apply (k m : ℕ) (g h : Fin (2 ^ (k + m))) :
    (ancR k m).basisOutcomeProjector 0 g h =
      if g = h then (if ancIdx k m g = 0 then 1 else 0) else 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_apply]

/-- Entries of the conjugated select `W† S W` in block coordinates. -/
theorem sandwich_apply (k m : ℕ) (W₀ : Operator (2 ^ m)) (S : Operator (2 ^ (k + m)))
    (g h : Fin (2 ^ (k + m))) :
    (((ancR k m).embedMatrix W₀)ᴴ * S * (ancR k m).embedMatrix W₀) g h =
      ∑ x1 : Fin (2 ^ m), ∑ x2 : Fin (2 ^ m),
        star (W₀ x1 (ancIdx k m g)) *
          S ((split k m).symm (sysIdx k m g, x1)) ((split k m).symm (sysIdx k m h, x2)) *
          W₀ x2 (ancIdx k m h) := by
  have inner : ∀ g2 : Fin (2 ^ (k + m)),
      ∑ g1, ((ancR k m).embedMatrix W₀)ᴴ g g1 * S g1 g2 =
        ∑ x1, star (W₀ x1 (ancIdx k m g)) * S ((split k m).symm (sysIdx k m g, x1)) g2 := by
    intro g2
    rw [sum_split k m, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [Finset.sum_eq_single (sysIdx k m g)]
    · rw [Matrix.conjTranspose_apply, embedAnc_apply]
      simp
    · intro i _ hi
      rw [Matrix.conjTranspose_apply, embedAnc_apply]
      simp [hi]
    · simp
  have inner2 : ∀ r : Fin (2 ^ (k + m)),
      ∑ g2, S r g2 * (ancR k m).embedMatrix W₀ g2 h =
        ∑ x2, S r ((split k m).symm (sysIdx k m h, x2)) * W₀ x2 (ancIdx k m h) := by
    intro r
    rw [sum_split k m, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x2 _ => ?_
    rw [Finset.sum_eq_single (sysIdx k m h)]
    · rw [embedAnc_apply]
      simp
    · intro i _ hi
      rw [embedAnc_apply]
      simp [hi]
    · simp
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  have : ∀ g2 : Fin (2 ^ (k + m)),
      (∑ g1, ((ancR k m).embedMatrix W₀)ᴴ g g1 * S g1 g2) * (ancR k m).embedMatrix W₀ g2 h =
      ∑ x1, star (W₀ x1 (ancIdx k m g)) *
        (S ((split k m).symm (sysIdx k m g, x1)) g2 * (ancR k m).embedMatrix W₀ g2 h) := by
    intro g2
    rw [inner, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x1 _ => by ring
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  rw [← Finset.mul_sum, inner2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x2 _ => by ring

/-- **Abstract LCU lemma.** -/
theorem lcu_blockEncoding {k m : ℕ} (S : Operator (2 ^ (k + m))) (hSh : Sᴴ = S)
    (hSS : S * S = 1) (W₀ : Unitary (2 ^ m)) (a : Fin (2 ^ m) → ℝ)
    (hW : ∀ x, W₀.1 x 0 = (a x : ℂ)) (α : ℝ) (hα : 0 < α) (A : Operator (2 ^ k))
    (hA : ∀ i j, A i j = (α : ℂ) * ∑ x, ∑ y, (a x : ℂ) * (a y : ℂ) *
        S ((split k m).symm (i, x)) ((split k m).symm (j, y))) :
    ∃ U : Unitary (2 ^ (k + m)), IsQubitizedBlockEncodingUnitary α A U := by
  set Wm : Operator (2 ^ (k + m)) := (ancR k m).embedMatrix W₀.1 with hWm
  have hW1 : Wm * Wmᴴ = 1 := by
    have := ((ancR k m).embedUnitary W₀).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  have hW2 : Wmᴴ * Wm = 1 := by
    have := ((ancR k m).embedUnitary W₀).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at this
    exact this
  have hUh : (Wmᴴ * S * Wm)ᴴ = Wmᴴ * S * Wm := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  refine ⟨⟨Wmᴴ * S * Wm, ?_⟩, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hUh]
    calc Wmᴴ * S * Wm * (Wmᴴ * S * Wm) = Wmᴴ * (S * (Wm * Wmᴴ) * S) * Wm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hW1, Matrix.mul_one, hSS, Matrix.mul_one, hW2]
  · refine ⟨hα, hUh, ?_⟩
    ext g h
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    by_cases hg : ancIdx k m g = 0
    · by_cases hh : ancIdx k m h = 0
      · have e1 : (QRegister.block 0 k (by omega) : QRegister k (k + m)).embedMatrix A g h =
            A (sysIdx k m g) (sysIdx k m h) := by
          have := embedSys_apply k m A g h
          rw [hg, hh] at this
          simpa using this
        have e2 := sandwich_apply k m W₀.1 S g h
        rw [hWm, e2]
        simp only [ancIdx] at hg hh
        simp only [hg, hh, if_true, mul_one]
        rw [e1, hA]
        have hαne : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
        rw [one_mul, one_mul, ← mul_assoc, inv_mul_cancel₀ hαne, one_mul]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hW x, hW y]
        simp [Complex.conj_ofReal]
        ring
      · simp [hg, hh]
    · simp [hg]

end Track1THC.LCU
