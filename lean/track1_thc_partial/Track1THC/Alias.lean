import Mathlib

/-!
# Walker–Vose alias decomposition (exact, integer weights)

`alias_exists`: any `n` natural-number weights `j i` on an index set `s` of size `n` with total
`n * B` can be split into `n` buckets `(keep i ≤ B, alt i ∈ s)` such that sampling a uniform bucket
and a uniform `r < B` (outputting `i` if `r < keep i`, else `alt i`) hits `α` with weight exactly
`j α`.  This is the combinatorial core of the exact alias-sampling `PREP` for THC.

Pure combinatorics: depends on Mathlib only.
-/

namespace Track1THC

open Finset

theorem alias_exists {ι : Type*} [DecidableEq ι] (B : ℕ) :
    ∀ (n : ℕ) (s : Finset ι) (j : ι → ℕ), s.card = n → ∑ i ∈ s, j i = n * B →
      ∃ (keep : ι → ℕ) (alt : ι → ι),
        (∀ i ∈ s, keep i ≤ B ∧ alt i ∈ s) ∧
        ∀ α ∈ s, j α = keep α + ∑ i ∈ s with alt i = α, (B - keep i) := by
  intro n
  induction n with
  | zero =>
    intro s j hs _
    rw [Finset.card_eq_zero] at hs
    subst hs
    exact ⟨fun _ => 0, id, by simp, by simp⟩
  | succ n ih =>
    intro s j hs hsum
    have hne : s.Nonempty := by rw [← Finset.card_pos]; omega
    -- a bucket `l` with weight at most `B`
    obtain ⟨l, hl, hjl⟩ : ∃ l ∈ s, j l ≤ B := by
      by_contra hcon
      push Not at hcon
      have h1 : ∑ i ∈ s, (B + 1) ≤ ∑ i ∈ s, j i :=
        Finset.sum_le_sum (fun i hi => hcon i hi)
      rw [Finset.sum_const, hs, hsum, smul_eq_mul] at h1
      nlinarith
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- single bucket
      subst hn
      have hcard : s = {l} := by
        rw [Finset.card_eq_one] at hs
        obtain ⟨a, rfl⟩ := hs
        rw [Finset.mem_singleton] at hl
        rw [hl]
      subst hcard
      refine ⟨fun _ => B, id, ?_, ?_⟩
      · intro i hi
        simp at hi
        subst hi
        simp
      · intro α hα
        simp at hα
        subst hα
        simp at hsum
        simp [hsum]
    · -- reduce: remove `l`, donate the deficit `B - j l` from a heavy bucket `g`
      set s' := s.erase l with hs'
      have hs'card : s'.card = n := by rw [hs', Finset.card_erase_of_mem hl]; omega
      have hsum' : ∑ i ∈ s', j i + j l = (n + 1) * B := by
        rw [hs', Finset.sum_erase_add _ _ hl]; exact hsum
      obtain ⟨g, hg, hjg⟩ : ∃ g ∈ s', B ≤ j g := by
        by_contra hcon
        push Not at hcon
        have h1 : ∑ i ∈ s', (j i + 1) ≤ ∑ i ∈ s', B :=
          Finset.sum_le_sum (fun i hi => by have := hcon i hi; omega)
        rw [Finset.sum_add_distrib, Finset.sum_const, hs'card, smul_eq_mul] at h1
        simp only [Finset.sum_const, hs'card, smul_eq_mul, mul_one] at h1
        nlinarith
      have hgl : g ≠ l := Finset.ne_of_mem_erase hg
      have hgs : g ∈ s := Finset.mem_of_mem_erase hg
      let j' : ι → ℕ := Function.update j g (j g + j l - B)
      have hj'sum : ∑ i ∈ s', j' i = n * B := by
        have e1 := Finset.add_sum_erase s' j' hg
        have e2 := Finset.add_sum_erase s' j hg
        have e3 : ∑ i ∈ s'.erase g, j' i = ∑ i ∈ s'.erase g, j i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [j', Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        have e4 : j' g = j g + j l - B := by simp [j']
        rw [e3] at e1
        have : (n + 1) * B = n * B + B := by ring
        omega
      obtain ⟨keep', alt', hprop', hcount'⟩ := ih s' j' hs'card hj'sum
      refine ⟨Function.update keep' l (j l), Function.update alt' l g, ?_, ?_⟩
      · intro i hi
        by_cases hil : i = l
        · subst hil; simp [hjl, hgs]
        · have his' : i ∈ s' := Finset.mem_erase.mpr ⟨hil, hi⟩
          obtain ⟨h1, h2⟩ := hprop' i his'
          simp only [Function.update_of_ne hil]
          exact ⟨h1, Finset.mem_of_mem_erase h2⟩
      · intro α hα
        -- split the sum over `s` into `l` and `s'`
        have hsplit : ∀ F : ι → ℕ, ∑ i ∈ s with
            (Function.update alt' l g) i = α, F i =
            (if g = α then F l else 0) + ∑ i ∈ s' with alt' i = α, F i := by
          intro F
          rw [Finset.sum_filter, ← Finset.add_sum_erase s _ hl]
          rw [Finset.sum_filter]
          congr 1
          · simp
          · apply Finset.sum_congr rfl
            intro i hi
            simp [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        rw [hsplit]
        by_cases hαl : α = l
        · subst hαl
          have hnone : ∑ i ∈ s' with alt' i = α, (B - Function.update keep' α (j α) i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            rw [Finset.mem_filter] at hi
            obtain ⟨hi1, hi2⟩ := hi
            exfalso
            have := (hprop' i hi1).2
            rw [hi2] at this
            exact (Finset.notMem_erase α s) this
          rw [hnone]
          simp [hgl]
        · have hαs' : α ∈ s' := Finset.mem_erase.mpr ⟨hαl, hα⟩
          have hc := hcount' α hαs'
          have hsc : ∑ i ∈ s' with alt' i = α, (B - Function.update keep' l (j l) i) =
              ∑ i ∈ s' with alt' i = α, (B - keep' i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hil : i ≠ l := Finset.ne_of_mem_erase (Finset.mem_filter.mp hi).1
            simp [Function.update_of_ne hil]
          rw [hsc]
          have hk : Function.update keep' l (j l) α = keep' α := Function.update_of_ne hαl _ _
          rw [hk]
          have hkeepg : keep' g ≤ B := (hprop' g hg).1
          by_cases hgα : g = α
          · subst hgα
            have : j' g = j g + j l - B := by simp [j']
            simp only [ite_true, Function.update_self]
            have hc' := hc
            rw [this] at hc'
            omega
          · have : j' α = j α := by simp [j', Function.update_of_ne (Ne.symm hgα)]
            rw [this] at hc
            simp [hgα]
            omega

end Track1THC
