import Track2Grover.FirstQuery

/-! A common finite cap on all loops of the actual semantics. The cap uses the same natural
number even at nested loops; a single sequence of finite programs recovers every effect. -/
namespace Track2Grover.Fuel
open Filter QProg ResourceCounting
open scoped ENNReal Topology
open FirstQuery (mass mass_wp mass_ite)
variable {V : Type} [DecidableEq V] {d : ℕ} [NeZero d]
abbrev State (V : Type) (d : ℕ) := CQState (Store V) d
abbrev Effect (V : Type) (d : ℕ) := CQAssertion (Store V) d

def unroll (g : Store V → Prop) [DecidablePred g] (p : QProg V d) : ℕ → QProg V d
  | 0 => .abort
  | n+1 => .qIf g (.qSeq p (unroll g p n)) .skip

def cap (t : ℕ) : QProg V d → QProg V d
  | .qSeq p q => .qSeq (cap t p) (cap t q)
  | @QProg.qIf _ _ g _ p q => .qIf g (cap t p) (cap t q)
  | @QProg.qWhile _ _ g _ p => unroll g (cap t p) t
  | p => p

noncomputable def obs (p : QProg V d) (δ : State V d) (θ : Effect V d) := mass δ (wp p θ)
def Below (p q : QProg V d) := ∀ δ θ, obs p δ θ ≤ obs q δ θ

private theorem seq_mono {p q r s : QProg V d} (h : Below p q) (h' : Below r s) :
    Below (.qSeq p r) (.qSeq q s) := by
  intro δ θ
  change mass δ (wp p (wp r θ)) ≤ mass δ (wp q (wp s θ))
  apply (h δ (wp r θ)).trans
  change mass δ (wp q (wp r θ)) ≤ mass δ (wp q (wp s θ))
  rw [mass_wp q, mass_wp q]
  exact h' _ _

private theorem if_mono (g : Store V → Prop) [DecidablePred g] {p q r s : QProg V d}
    (h : Below p q) (h' : Below r s) : Below (.qIf g p r) (.qIf g q s) := by
  intro δ θ
  simpa only [obs, wp_qIf, mass_ite] using
    add_le_add (h (δ.restrict g) θ) (h' (δ.restrict (¬g ·)) θ)

private theorem unroll_mono (g : Store V → Prop) [DecidablePred g] {p q : QProg V d}
    (h : Below p q) {i j : ℕ} (hij : i ≤ j) : Below (unroll g p i) (unroll g q j) := by
  induction i generalizing j with
  | zero => intro δ θ; simp [obs, unroll, mass]
  | succ i ih =>
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact if_mono g (seq_mono h (ih (by omega))) (fun _ _ ↦ le_rfl)

private theorem wp_unroll (g : Store V → Prop) [DecidablePred g] (p : QProg V d)
    (t : ℕ) (θ : Effect V d) : wp (unroll g p t) θ = whileRecWP (wp p) g t θ := by
  induction t with
  | zero => rfl
  | succ t ih => simp [unroll, whileRecWP, ih]

private theorem unroll_below (g : Store V → Prop) [DecidablePred g] (p : QProg V d) (i : ℕ) :
    Below (unroll g p i) (.qWhile g p) := by
  intro δ θ
  simp only [obs, wp_unroll, mass]
  exact ENNReal.ofReal_le_ofReal (expect_mono le_rfl (whileRecWP_le_wp_qWhile g p i θ))

private theorem unroll_limit (g : Store V → Prop) [DecidablePred g] (p : QProg V d)
    (δ : State V d) (θ : Effect V d) :
    Tendsto (fun t ↦ obs (unroll g p t) δ θ) atTop (𝓝 (obs (.qWhile g p) δ θ)) := by
  simp only [obs, wp_unroll, wp_qWhile, mass]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_expect_assertion_ωSup (whileRecWP.chain (wp p) (wp_mono p) g θ) δ)

private theorem diagonal (f : ℕ → ℕ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) (L : ℝ≥0∞)
    (hi : ∀ i j i' j', i ≤ i' → j ≤ j' → f i j ≤ f i' j')
    (hu : ∀ i, f i i ≤ L)
    (row : ∀ j, Tendsto (fun i ↦ f i j) atTop (𝓝 (g j)))
    (col : Tendsto g atTop (𝓝 L)) : Tendsto (fun i ↦ f i i) atTop (𝓝 L) := by
  have hmono : Monotone (fun i ↦ f i i) := fun i j h ↦ hi i i j j h h
  have he : (⨆ i, f i i) = L := by
    refine le_antisymm (iSup_le hu) (le_of_tendsto col (Eventually.of_forall fun j ↦ ?_))
    apply le_of_tendsto (row j) (Eventually.of_forall fun i ↦ ?_)
    exact (hi i j (max i j) (max i j) (le_max_left ..) (le_max_right ..)).trans
      (le_iSup (fun a ↦ f a a) _)
  rw [← he]
  exact tendsto_atTop_iSup hmono

structure Approaches (F : ℕ → QProg V d) (p : QProg V d) : Prop where
  mono : ∀ i j, i ≤ j → Below (F i) (F j)
  upper : ∀ i, Below (F i) p
  limit : ∀ δ θ, Tendsto (fun i ↦ obs (F i) δ θ) atTop (𝓝 (obs p δ θ))

private theorem fixed (p : QProg V d) : Approaches (fun _ ↦ p) p :=
  ⟨fun _ _ _ _ _ ↦ le_rfl, fun _ _ _ ↦ le_rfl, fun _ _ ↦ tendsto_const_nhds⟩

private theorem seq_app {F G : ℕ → QProg V d} {p q} (hf : Approaches F p) (hg : Approaches G q) :
    Approaches (fun i ↦ .qSeq (F i) (G i)) (.qSeq p q) := by
  refine ⟨fun i j h ↦ seq_mono (hf.mono i j h) (hg.mono i j h),
    fun i ↦ seq_mono (hf.upper i) (hg.upper i), fun δ θ ↦ ?_⟩
  apply diagonal (fun i j ↦ obs (.qSeq (F i) (G j)) δ θ) (fun j ↦ obs (.qSeq p (G j)) δ θ)
  · exact fun i j a b h h' ↦ seq_mono (hf.mono i a h) (hg.mono j b h') _ _
  · exact fun i ↦ seq_mono (hf.upper i) (hg.upper i) _ _
  · exact fun j ↦ hf.limit _ (wp (G j) θ)
  · simpa only [obs, wp_qSeq, mass_wp p] using hg.limit ((interp p).toStateFun δ) θ

private theorem if_app (g : Store V → Prop) [DecidablePred g] {F G : ℕ → QProg V d} {p q}
    (hf : Approaches F p) (hg : Approaches G q) :
    Approaches (fun i ↦ .qIf g (F i) (G i)) (.qIf g p q) := by
  refine ⟨fun i j h ↦ if_mono g (hf.mono i j h) (hg.mono i j h),
    fun i ↦ if_mono g (hf.upper i) (hg.upper i), fun δ θ ↦ ?_⟩
  simpa only [obs, wp_qIf, mass_ite] using
    (hf.limit (δ.restrict g) θ).add (hg.limit (δ.restrict (¬g ·)) θ)

private theorem while_app (g : Store V → Prop) [DecidablePred g] {F : ℕ → QProg V d} {p}
    (hf : Approaches F p) : Approaches (fun i ↦ unroll g (F i) i) (.qWhile g p) := by
  have U (i : ℕ) : Below (unroll g (F i) i) (.qWhile g p) := fun δ θ ↦
    (unroll_mono g (hf.upper i) le_rfl δ θ).trans (unroll_below g p i δ θ)
  refine ⟨fun i j h ↦ unroll_mono g (hf.mono i j h) h, U, fun δ θ ↦ ?_⟩
  have fixed_cap (j : ℕ) : Approaches (fun i ↦ unroll g (F i) j) (unroll g p j) := by
    induction j with
    | zero => exact fixed .abort
    | succ j ih => exact if_app g (seq_app hf ih) (fixed .skip)
  exact diagonal (fun i j ↦ obs (unroll g (F i) j) δ θ) (fun j ↦ obs (unroll g p j) δ θ)
    _ (fun i j a b h h' ↦ unroll_mono g (hf.mono i a h) h' _ _)
    (fun i ↦ U i _ _) (fun j ↦ (fixed_cap j).limit _ _) (unroll_limit g p δ θ)

/-- Simultaneously truncating every loop at t recovers the full output distribution
against any frozen effect, on every fixed initial state. -/
theorem cofinal (p : QProg V d) : Approaches (fun t ↦ cap t p) p := by
  induction p with
  | qSeq p q hp hq => exact seq_app hp hq
  | qIf g p q hp hq => exact if_app g hp hq
  | qWhile g p hp => exact while_app g hp
  | _ => exact fixed _

#print axioms cofinal

/-- Operational order detected by all bounded effects. -/
def StateBelow (δ η : State V d) := ∀ θ, mass δ θ ≤ mass η θ

private theorem below_trace {δ η : State V d} (h : StateBelow δ η) :
    (δ.trace : ℝ≥0∞) ≤ η.trace := by simpa [mass, expect_top] using h ⊤

private theorem restrict_below {δ η : State V d} (h : StateBelow δ η)
    (g : Store V → Prop) [DecidablePred g] : StateBelow (δ.restrict g) (η.restrict g) := by
  intro θ
  have z (δ : State V d) : mass δ ⊥ = 0 := by simp [mass]
  simpa only [mass_ite, z, add_zero] using h (fun s ↦ if g s then θ s else (⊥ : Effect V d) s)

private theorem sem_below {δ η : State V d} (h : StateBelow δ η) (p : QProg V d) :
    StateBelow ((interp p).toStateFun δ) ((interp p).toStateFun η) := by
  intro θ
  simpa only [mass_wp] using h (wp p θ)

private theorem sem_below_of_program {p q : QProg V d} (h : Below p q) (δ : State V d) :
    StateBelow ((interp p).toStateFun δ) ((interp q).toStateFun δ) := by
  intro θ
  simpa only [obs, mass_wp] using h δ θ

private theorem priced_loop {p q : QProg V d} {M : CostModel d}
    (h : Below p q) (price : ∀ δ η, StateBelow δ η → expectedCost M p δ ≤ expectedCost M q η)
    (g : Store V → Prop) [DecidablePred g] (t : ℕ) (δ η : State V d) (hstate : StateBelow δ η) :
    whileRecCost (expectedCost M p) (interp p).toStateFun g t δ ≤
    whileRecCost (expectedCost M q) (interp q).toStateFun g t η := by
  induction t generalizing δ η with
  | zero => rfl
  | succ t ih =>
    have hr := restrict_below hstate g
    apply add_le_add (price _ _ hr) (ih _ _ _)
    exact fun θ ↦ (sem_below hr p θ).trans (sem_below_of_program h _ θ)

theorem monotone_cost (M : CostModel d) (p : QProg V d) {δ η : State V d} (h : StateBelow δ η) :
    expectedCost M p δ ≤ expectedCost M p η := by
  induction p generalizing δ η with
  | qSeq p q hp hq => exact add_le_add (hp h) (hq (sem_below h p))
  | qIf g p q hp hq => exact add_le_add (hp (restrict_below h g)) (hq (restrict_below h (¬g ·)))
  | qWhile g p hp =>
    exact iSup_mono fun t ↦ priced_loop (p := p) (q := p) (fun _ _ ↦ le_rfl)
      (fun _ _ hs ↦ hp hs) g t δ η h
  | skip | abort => rfl
  | assign _ _ | qAssign _ | qMeasure _ _ | qSet =>
    exact mul_le_mul_of_nonneg_right (below_trace h) zero_le

private theorem unroll_cost (M : CostModel d) (g : Store V → Prop) [DecidablePred g]
    (p : QProg V d) (t : ℕ) (δ : State V d) :
    expectedCost M (unroll g p t) δ =
    whileRecCost (expectedCost M p) (interp p).toStateFun g t δ := by
  induction t generalizing δ with
  | zero => rfl
  | succ t ih => simp [unroll, ih]

theorem cap_cost (M : CostModel d) (t : ℕ) (p : QProg V d) (δ : State V d) :
    expectedCost M (cap t p) δ ≤ expectedCost M p δ := by
  induction p generalizing δ with
  | qSeq p q hp hq =>
    exact add_le_add (hp _) ((hq _).trans (monotone_cost M q (sem_below_of_program ((cofinal p).upper t) _)))
  | qIf g p q hp hq => exact add_le_add (hp _) (hq _)
  | qWhile g p hp =>
    change expectedCost M (unroll g (cap t p) t) δ ≤ _
    rw [unroll_cost, expectedCost_qWhile]
    apply le_trans _ (le_iSup (fun i : ℕ ↦ whileRecCost (expectedCost M p) (interp p).toStateFun g i δ) t)
    exact priced_loop ((cofinal p).upper t) (fun _ _ h ↦ (hp _).trans (monotone_cost M p h))
      g t δ δ (fun _ ↦ le_rfl)
  | _ => rfl

#print axioms cap_cost
end Track2Grover.Fuel
