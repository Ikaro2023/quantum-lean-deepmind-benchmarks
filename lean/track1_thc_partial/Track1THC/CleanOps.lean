import QuantumComputation.Circuits.Toffoli
import QuantumComputation.Circuits.ResourceCounting
import QuantumComputation.QuantumHoareLogic.CleanAncilla
import QuantumComputationSpecs.Primitives.THCFactorization

/-!
# Clean `DynamicCircuit` composition algebra (Track 1, Round 3)

Sequential composition theory for `RealizesCleanSubroutine` and `RealizesCatalyticSubroutine`
(same registers), together with the matching `T`/`TOFF` count algebra:

* `triple_seq`: Hoare-triple sequencing for `QProg.qSeq` (derived from `expect_wp`).
* `RealizesCleanSubroutine.skip` / `.seq` / `.of_qAssign` / `.congr`: identity, sequential
  composition `U₂ * U₁`, and any whole-system unitary assignment that is a target-embedded unitary.
* `RealizesCatalyticSubroutine.seq` / `.skip`.
* Cost algebra: `CostBound P t` = (`TOFF = 0` ∧ `T ≤ t`) is closed under `seq` (additive), `qIf`
  (max) and `identity`; `jonesToffoli` has cost `(0, 4)`; sequences of `m` Jones Toffolis
  realize the product of the `m` Toffoli unitaries with `T`-cost `4 m` and `TOFF = 0`.

Everything here is proved from the frozen library `QuantumComputation.*` only.
-/

open Operator QProg Matrix HermitianMat QuantumComputation.Specs

namespace Track1THC.CleanOps

variable {Var : Type} [DecidableEq Var] {n k m : ℕ}

/-! ### Hoare-triple sequencing -/

theorem triple_seq {Θ Φ Ψ : CQAssertion (Store Var) (2 ^ n)} {c₁ c₂ : QProg Var (2 ^ n)}
    (h₁ : ⦃ Θ ⦄ c₁ ⦃ Φ ⦄) (h₂ : ⦃ Φ ⦄ c₂ ⦃ Ψ ⦄) : ⦃ Θ ⦄ QProg.qSeq c₁ c₂ ⦃ Ψ ⦄ := by
  apply Triple.infer
  intro Δ
  rw [wp_qSeq, expect_wp c₁ Δ (wp c₂ Ψ)]
  refine (h₁ Δ).trans ?_
  rw [expect_wp c₂ _ Ψ]
  exact h₂ _

/-! ### Clean subroutines: the commutation lemma -/

/-- An embedded target unitary commutes with the clean-ancilla projector of a disjoint register. -/
theorem proj_mul_embed (rT : QRegister k n) (rA : QRegister m n) (h : rT.DisjointWires rA)
    (U : Unitary (2 ^ k)) :
    rA.basisOutcomeProjector 0 * (rT.embedUnitary U).1 =
      (rT.embedUnitary U).1 * rA.basisOutcomeProjector 0 := by
  have := QRegister.embedMatrix_comm_of_disjoint rA rT (QRegister.disjoint_comm.mp h)
    (compProj 0) U.1
  exact this

theorem embed_adj_mul_proj (rT : QRegister k n) (rA : QRegister m n) (h : rT.DisjointWires rA)
    (U : Unitary (2 ^ k)) :
    (rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0 =
      rA.basisOutcomeProjector 0 * (rT.embedUnitary U).1ᴴ := by
  have h1 := congrArg conjTranspose (proj_mul_embed rT rA h U)
  rw [conjTranspose_mul, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] at h1
  exact h1

/-- Restricting to the clean ancilla subspace is idempotent. -/
theorem restrict_idem {State : Type*} (rA : QRegister m n) (θ : CQAssertion State (2 ^ n)) :
    (θ.restrictToZeroAncilla rA).restrictToZeroAncilla rA = θ.restrictToZeroAncilla rA := by
  funext σ
  apply Subtype.ext
  simp only [CQAssertion.restrictToZeroAncilla_coe, conj_conj]
  rw [QRegister.basisOutcomeProjector_mul_self]

/-- Key lemma: a target-embedded unitary assignment can absorb an inner clean restriction. -/
theorem restrict_qAssign_restrict {State : Type*} (rT : QRegister k n) (rA : QRegister m n)
    (h : rT.DisjointWires rA) (U : Unitary (2 ^ k)) (θ : CQAssertion State (2 ^ n)) :
    ((θ.restrictToZeroAncilla rA).qAssign (rT.embedUnitary U)).restrictToZeroAncilla rA =
      (θ.qAssign (rT.embedUnitary U)).restrictToZeroAncilla rA := by
  funext σ
  apply Subtype.ext
  have hc := embed_adj_mul_proj rT rA h U
  have hP := QRegister.basisOutcomeProjector_mul_self rA 0
  simp only [CQAssertion.restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  have hM : rA.basisOutcomeProjector 0 *
      ((rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0) =
      rA.basisOutcomeProjector 0 * (rT.embedUnitary U).1ᴴ := by
    rw [hc, ← Matrix.mul_assoc, hP]
  rw [hM]

/-! ### Clean subroutines: identity, sequencing, unitary assignments -/

section clean
variable {rT : QRegister k n} {rA : QRegister m n} {h : rT.DisjointWires rA}

theorem realizesClean_skip :
    RealizesCleanSubroutine rT rA h (1 : Unitary (2 ^ k)) (QProg.skip : QProg Var (2 ^ n)) := by
  intro M
  apply Triple.of_le_wp
  simp only [wp_skip, QRegister.embedUnitary_one, CQAssertion.qAssign_one]
  exact (restrict_idem rA _).le

/-- Sequential composition: first `P₁` (realizing `U₁`), then `P₂` (realizing `U₂`), realizes
the product `U₂ * U₁` on the same target and clean ancilla. -/
theorem realizesClean_seq {U₁ U₂ : Unitary (2 ^ k)} {P₁ P₂ : QProg Var (2 ^ n)}
    (h₁ : RealizesCleanSubroutine rT rA h U₁ P₁) (h₂ : RealizesCleanSubroutine rT rA h U₂ P₂) :
    RealizesCleanSubroutine rT rA h (U₂ * U₁) (QProg.qSeq P₁ P₂) := by
  intro M
  -- `P₁` is applied to the observable `M' = U₂† M U₂`
  obtain ⟨M', hM'⟩ : ∃ M' : Observable (Fin (2 ^ n)), (fun _ : Store Var ↦ M') =
      CQAssertion.qAssign (rT.embedUnitary U₂) (fun _ : Store Var ↦ M) :=
    ⟨_, (CQAssertion.qAssign_const _ _).symm⟩
  have hmid :
      ((CQAssertion.restrictToZeroAncilla (fun _ : Store Var ↦ M) rA).qAssign
          (rT.embedUnitary U₂)).restrictToZeroAncilla rA =
        CQAssertion.restrictToZeroAncilla (fun _ : Store Var ↦ M') rA := by
    rw [restrict_qAssign_restrict rT rA h, hM']
  have e₂ := h₂ M
  have e₁ := h₁ M'
  dsimp only at e₁ e₂ ⊢
  have hpre :
      ((CQAssertion.restrictToZeroAncilla (fun _ : Store Var ↦ M) rA).qAssign
          (rT.embedUnitary (U₂ * U₁))).restrictToZeroAncilla rA =
        ((CQAssertion.restrictToZeroAncilla (fun _ : Store Var ↦ M') rA).qAssign
          (rT.embedUnitary U₁)).restrictToZeroAncilla rA := by
    rw [restrict_qAssign_restrict rT rA h (U₂ * U₁), restrict_qAssign_restrict rT rA h U₁,
      QRegister.embedUnitary_mul, hM', CQAssertion.qAssign_qAssign]
  rw [hpre]
  have e₂' : ⦃ CQAssertion.restrictToZeroAncilla (fun _ : Store Var ↦ M') rA ⦄ P₂
      ⦃ CQAssertion.restrictToZeroAncilla (fun _ : Store Var ↦ M) rA ⦄ := by
    rw [← hmid]; exact e₂
  exact triple_seq e₁ e₂'

/-- A single whole-system unitary assignment of a target-embedded unitary realizes it. -/
theorem realizesClean_qAssign (U : Unitary (2 ^ k)) :
    RealizesCleanSubroutine rT rA h U
      (QProg.qAssign (rT.embedUnitary U) : QProg Var (2 ^ n)) := by
  intro M
  apply Triple.of_le_wp
  rw [wp_qAssign]
  refine le_of_eq ?_
  -- `P₀ (θ.qAssign E) P₀ ≤ θ.qAssign E` with `θ = P₀ M P₀`
  funext σ
  apply Subtype.ext
  have hc := embed_adj_mul_proj rT rA h U
  have hP := QRegister.basisOutcomeProjector_mul_self rA 0
  simp only [CQAssertion.restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  have hM : rA.basisOutcomeProjector 0 *
      ((rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0) =
      (rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0 := by
    rw [hc, ← Matrix.mul_assoc, hP]
  rw [hM]

/-- A single whole-system unitary assignment `W` realizes `U` on `rT` with clean ancilla `rA`
as soon as `W` acts on clean-ancilla inputs exactly as the target-embedded `U`:
`W * P₀ = (embed U) * P₀`, where `P₀` projects onto the clean ancilla subspace.  (No relation is
required on dirty inputs: unitarity forces `W` to preserve the dirty subspace.)  This is the
bridge used for catalytic rotations, where `W = V⁻¹ · Add · V` is *not* a target-embedded
unitary but acts as one on the clean subspace. -/
theorem realizesClean_of_clean_action (U : Unitary (2 ^ k)) (W : Unitary (2 ^ n))
    (hW : W.1 * rA.basisOutcomeProjector 0 = (rT.embedUnitary U).1 * rA.basisOutcomeProjector 0) :
    RealizesCleanSubroutine rT rA h U (QProg.qAssign W : QProg Var (2 ^ n)) := by
  intro M
  apply Triple.of_le_wp
  rw [wp_qAssign]
  refine le_of_eq ?_
  funext σ
  apply Subtype.ext
  have hc := embed_adj_mul_proj rT rA h U
  have hcomm := proj_mul_embed rT rA h U
  have hP := QRegister.basisOutcomeProjector_mul_self rA 0
  have hWW : W.1ᴴ * W.1 = 1 := by simpa [Matrix.star_eq_conjTranspose] using W.2.1
  have hEE : (rT.embedUnitary U).1 * (rT.embedUnitary U).1ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (rT.embedUnitary U).2.2
  have h1 : W.1ᴴ * ((rT.embedUnitary U).1 * rA.basisOutcomeProjector 0) =
      rA.basisOutcomeProjector 0 := by
    rw [← hW, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have h2 : W.1ᴴ * rA.basisOutcomeProjector 0 =
      (rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0 := by
    calc W.1ᴴ * rA.basisOutcomeProjector 0
        = W.1ᴴ * (rA.basisOutcomeProjector 0 * ((rT.embedUnitary U).1 *
            (rT.embedUnitary U).1ᴴ)) := by rw [hEE, Matrix.mul_one]
      _ = W.1ᴴ * ((rA.basisOutcomeProjector 0 * (rT.embedUnitary U).1) *
            (rT.embedUnitary U).1ᴴ) := by rw [Matrix.mul_assoc]
      _ = W.1ᴴ * (((rT.embedUnitary U).1 * rA.basisOutcomeProjector 0) *
            (rT.embedUnitary U).1ᴴ) := by rw [hcomm]
      _ = (W.1ᴴ * ((rT.embedUnitary U).1 * rA.basisOutcomeProjector 0)) *
            (rT.embedUnitary U).1ᴴ := by simp only [Matrix.mul_assoc]
      _ = rA.basisOutcomeProjector 0 * (rT.embedUnitary U).1ᴴ := by rw [h1]
      _ = (rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0 := hc.symm
  have hM : rA.basisOutcomeProjector 0 *
      ((rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0) =
      (rT.embedUnitary U).1ᴴ * rA.basisOutcomeProjector 0 := by
    rw [hc, ← Matrix.mul_assoc, hP]
  simp only [CQAssertion.restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [hM, h2]

/-- Equal weakest preconditions give interchangeable realizers. -/
theorem realizesClean_congr {U : Unitary (2 ^ k)} {P Q : QProg Var (2 ^ n)}
    (hPQ : ∀ Θ, wp P Θ = wp Q Θ) (hP : RealizesCleanSubroutine rT rA h U P) :
    RealizesCleanSubroutine rT rA h U Q := by
  intro M
  have e := hP M
  apply Triple.infer
  intro Δ
  rw [← hPQ, expect_wp]
  exact e Δ

end clean

/-! ### Transfer along equal embeddings, and chains -/

/-- `RealizesCleanSubroutine` only sees the target through `rT.embedUnitary U`; any other
target presentation with the same embedded unitary realizes the same subroutine. -/
theorem realizesClean_of_embed_eq {k' : ℕ} {rT : QRegister k n} {rA : QRegister m n}
    {h : rT.DisjointWires rA} {rT' : QRegister k' n} {h' : rT'.DisjointWires rA}
    {U : Unitary (2 ^ k)} {U' : Unitary (2 ^ k')} {P : QProg Var (2 ^ n)}
    (heq : rT'.embedUnitary U' = rT.embedUnitary U)
    (hP : RealizesCleanSubroutine rT rA h U P) :
    RealizesCleanSubroutine rT' rA h' U' P := by
  intro M
  have e := hP M
  dsimp only at e ⊢
  rw [heq]
  exact e

/-- Product of a list of unitaries in execution order (head first). -/
def chainU {d : ℕ} : List (Unitary d) → Unitary d
  | [] => 1
  | U :: Us => chainU Us * U

/-- Sequential composition of a list of programs (head first). -/
def chainP : List (QProg Var (2 ^ n)) → QProg Var (2 ^ n)
  | [] => QProg.skip
  | P :: Ps => QProg.qSeq P (chainP Ps)

theorem realizesClean_chain {rT : QRegister k n} {rA : QRegister m n} {h : rT.DisjointWires rA} :
    ∀ (L : List (Unitary (2 ^ k) × QProg Var (2 ^ n))),
      (∀ x ∈ L, RealizesCleanSubroutine rT rA h x.1 x.2) →
      RealizesCleanSubroutine rT rA h (chainU (L.map Prod.fst)) (chainP (L.map Prod.snd))
  | [], _ => realizesClean_skip
  | x :: L, hL => by
      have h₁ := hL x (by simp)
      have h₂ := realizesClean_chain L (fun y hy ↦ hL y (by simp [hy]))
      -- `chainU (x.1 :: Us) = chainU Us * x.1`, `chainP (x.2 :: Ps) = x.2 ; chainP Ps`
      exact realizesClean_seq h₁ h₂

/-! ### Catalytic subroutines -/

section catalytic
variable {b : ℕ} {rT : QRegister k n} {rS : QRegister m n} {rC : QRegister b n}
  {hsc : rS.DisjointWires rC} {hdisj : rT.DisjointWires (rS.concat rC hsc)}

theorem wp_conj_cancel (V : Unitary (2 ^ n)) (Ξ : CQAssertion (Store Var) (2 ^ n)) :
    wp (QProg.qAssign V⁻¹ : QProg Var (2 ^ n)) (wp (QProg.qAssign V) Ξ) = Ξ := by
  rw [wp_qAssign, wp_qAssign, CQAssertion.qAssign_qAssign, mul_inv_cancel,
    CQAssertion.qAssign_one]

theorem wp_conj_cancel' (V : Unitary (2 ^ n)) (Ξ : CQAssertion (Store Var) (2 ^ n)) :
    wp (QProg.qAssign V : QProg Var (2 ^ n)) (wp (QProg.qAssign V⁻¹) Ξ) = Ξ := by
  rw [wp_qAssign, wp_qAssign, CQAssertion.qAssign_qAssign, inv_mul_cancel,
    CQAssertion.qAssign_one]

theorem realizesCatalytic_skip :
    RealizesCatalyticSubroutine (Var := Var) rT rS rC hsc hdisj (1 : Unitary (2 ^ k))
      (QProg.skip : QProg Var (2 ^ n)) := by
  intro V _
  refine realizesClean_congr (P := (QProg.skip : QProg Var (2 ^ n))) ?_ realizesClean_skip
  intro Θ
  simp only [wp_qSeq, wp_skip, QRegister.embedUnitary_inv]
  rw [wp_conj_cancel']

/-- Sequential composition of catalytic subroutines (same catalyst, same scratch). -/
theorem realizesCatalytic_seq {U₁ U₂ : Unitary (2 ^ k)} {P₁ P₂ : QProg Var (2 ^ n)}
    (h₁ : RealizesCatalyticSubroutine rT rS rC hsc hdisj U₁ P₁)
    (h₂ : RealizesCatalyticSubroutine rT rS rC hsc hdisj U₂ P₂) :
    RealizesCatalyticSubroutine rT rS rC hsc hdisj (U₂ * U₁) (QProg.qSeq P₁ P₂) := by
  intro V hV
  have e := realizesClean_seq (h₁ V hV) (h₂ V hV)
  refine realizesClean_congr ?_ e
  intro Θ
  simp only [wp_qSeq, QRegister.embedUnitary_inv]
  rw [wp_conj_cancel]

/-- A clean subroutine whose program commutes through the catalyst conjugation is catalytic. -/
theorem realizesCatalytic_of_clean {U : Unitary (2 ^ k)} {P : QProg Var (2 ^ n)}
    (hP : ∀ V : Unitary (2 ^ b),
      RealizesCleanSubroutine rT (rS.concat rC hsc) hdisj U
        (.qSeq (.qAssign (rC.embedUnitary V)) (.qSeq P (.qAssign (rC.embedUnitary V⁻¹))))) :
    RealizesCatalyticSubroutine rT rS rC hsc hdisj U P :=
  fun V _ ↦ hP V

end catalytic

/-! ### Sub-register lifting -/

/-- Lifting along a sub-register: a subroutine realizing `U` on the `k`-wire sub-register
`rT.compose sub` of a larger target `rT` realizes `sub.embedUnitary U` on all of `rT`. -/
theorem realizesClean_lift {k' : ℕ} {rA : QRegister m n} (rT : QRegister k' n)
    (sub : QRegister k k') (hbig : rT.DisjointWires rA)
    (hsub : (rT.compose sub).DisjointWires rA)
    {U : Unitary (2 ^ k)} {P : QProg Var (2 ^ n)}
    (hP : RealizesCleanSubroutine (rT.compose sub) rA hsub U P) :
    RealizesCleanSubroutine rT rA hbig (sub.embedUnitary U) P :=
  realizesClean_of_embed_eq (by rw [QRegister.embedUnitary_compose]) hP

/-! ### Cost algebra for dynamic circuits -/

section cost
variable {Var' : Type} {N : ℕ}

/-- `P` uses no `TOFF` gate and at most `t` `T` gates (worst case over `qIf` branches). -/
def CostBound (P : DynamicCircuit Var' N) (t : ℕ) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧ P.count PrimitiveGate.T ≤ t

theorem CostBound.identity : CostBound (DynamicCircuit.identity : DynamicCircuit Var' N) 0 := by
  simp [CostBound, DynamicCircuit.identity]

theorem CostBound.measure (v : Var') (r : QRegister 1 N) :
    CostBound (DynamicCircuit.measure v r) 0 := by
  simp [CostBound]

theorem CostBound.mono {P : DynamicCircuit Var' N} {t t' : ℕ} (h : CostBound P t)
    (htt : t ≤ t') : CostBound P t' :=
  ⟨h.1, h.2.trans htt⟩

theorem CostBound.seq {P Q : DynamicCircuit Var' N} {t u : ℕ} (hP : CostBound P t)
    (hQ : CostBound Q u) : CostBound (DynamicCircuit.seq P Q) (t + u) := by
  refine ⟨?_, ?_⟩
  · simp [hP.1, hQ.1]
  · simp only [DynamicCircuit.count]
    exact Nat.add_le_add hP.2 hQ.2

theorem CostBound.qIf (cond : Store Var' → Prop) [DecidablePred cond]
    {P Q : DynamicCircuit Var' N} {t u : ℕ} (hP : CostBound P t) (hQ : CostBound Q u) :
    CostBound (DynamicCircuit.qIf cond P Q) (max t u) := by
  refine ⟨?_, ?_⟩
  · simp [hP.1, hQ.1]
  · simp only [DynamicCircuit.count]
    exact max_le_max hP.2 hQ.2

theorem CostBound.jonesToffoli (v : Var') (c₁ c₂ tg anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hta : tg ≠ anc) :
    CostBound (DynamicCircuit.jonesToffoli v c₁ c₂ tg anc h₁₂ h₁a h₂a hta) 4 := by
  refine ⟨DynamicCircuit.count_jonesToffoli_toff .., le_of_eq (DynamicCircuit.count_jonesToffoli_t ..)⟩

/-- Sequential composition of a list of dynamic circuits (head first). -/
def dchain : List (DynamicCircuit Var' N) → DynamicCircuit Var' N
  | [] => DynamicCircuit.identity
  | P :: Ps => DynamicCircuit.seq P (dchain Ps)

theorem compile_dchain (L : List (DynamicCircuit Var N)) :
    (dchain L).compile = chainP (L.map DynamicCircuit.compile) := by
  induction L with
  | nil => rfl
  | cons P Ps ih => simp [dchain, chainP, ih]

theorem CostBound.dchain {L : List (DynamicCircuit Var' N)} {ts : List ℕ}
    (hL : List.Forall₂ CostBound L ts) : CostBound (dchain L) ts.sum := by
  induction hL with
  | nil => exact CostBound.identity
  | cons hP _ ih => exact CostBound.seq hP ih

end cost

/-! ### Clean Jones-AND (Toffoli) building block on an arbitrary target -/

/-- Cody Jones' `T = 4`, `TOFF = 0` clean Toffoli, placed on any three wires `sub` of a larger
target register `rT`, with one clean ancilla wire `anc` outside `rT`:
`rT.embed (sub.embed toffoli)` is realized cleanly and the circuit has cost `(0, 4)`. -/
theorem exists_jonesToffoli_on_target {k' : ℕ} (v : Var) (rT : QRegister k' n)
    (sub : QRegister 3 k') (anc : Wire n) (hanc : ∀ i, rT i ≠ anc)
    (hbig : rT.DisjointWires (QRegister.singleton anc)) :
    ∃ P : DynamicCircuit Var n, CostBound P 4 ∧
      RealizesCleanSubroutine rT (QRegister.singleton anc) hbig
        (sub.embedUnitary PrimitiveGate.toffoli.eval) P.compile := by
  have hi : ∀ a b : Fin 3, a ≠ b → rT (sub a) ≠ rT (sub b) := fun a b hab h ↦
    hab (sub.wires.injective (rT.wires.injective h))
  have h₁₂ := hi 0 1 (by decide)
  have h₁t := hi 0 2 (by decide)
  have h₂t := hi 1 2 (by decide)
  have h₁a := hanc (sub 0)
  have h₂a := hanc (sub 1)
  have hta := hanc (sub 2)
  let tri := QRegister.triple (rT (sub 0)) (rT (sub 1)) (rT (sub 2)) h₁₂ h₁t h₂t
  have hreg : rT.compose sub = tri := by
    ext i
    fin_cases i <;> rfl
  have hdtri : tri.DisjointWires (QRegister.singleton anc) := by
    rw [QRegister.disjoint_iff]
    intro i j
    fin_cases i <;> simp [tri, QRegister.triple, hanc]
  have hsub : (rT.compose sub).DisjointWires (QRegister.singleton anc) :=
    hbig.compose_left sub
  refine ⟨DynamicCircuit.jonesToffoli v (rT (sub 0)) (rT (sub 1)) (rT (sub 2)) anc h₁₂ h₁a h₂a hta,
    CostBound.jonesToffoli v _ _ _ _ h₁₂ h₁a h₂a hta, ?_⟩
  have hP := DynamicCircuit.realizesCleanSubroutine_jonesToffoli v (rT (sub 0)) (rT (sub 1)) (rT (sub 2)) anc
    h₁₂ h₁t h₂t h₁a h₂a hta hdtri
  refine realizesClean_lift rT sub hbig hsub ?_
  exact realizesClean_of_embed_eq (by rw [hreg]) hP

end Track1THC.CleanOps
