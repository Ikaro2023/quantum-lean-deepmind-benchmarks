import Track2Grover.FiniteReduction

/-! Uniform finite source cuts and their per-outcome execution trees. All syntax is
chosen before the oracle is supplied. Unrolling to depth zero produces a timeout. -/
namespace Track2Grover.Path
open Operator ResourceCounting
open scoped ENNReal

inductive Finite (V : Type) (w h : ℕ) where
  | skip | abort
  | step (U : Unitary (2^w))
  | oracle (r : QRegister h w)
  | measure {k : ℕ} (x : V) (r : QRegister k w)
  | branch (g : Store V → Prop) [DecidablePred g] (yes no : Finite V w h)
  | seq (first second : Finite V w h)

variable {V : Type} {w h : ℕ}
noncomputable def compile (O : Unitary (2^h)) : Finite V w h → QProg V (2^w)
  | .skip => .skip
  | .abort => .abort
  | .step U => .qAssign U
  | .oracle r => .qAssign (r.embedUnitary O)
  | .measure x r => QProg.measureRegister x r
  | .seq C D => .qSeq (compile O C) (compile O D)
  | @Finite.branch _ _ _ g _ C D => .qIf g (compile O C) (compile O D)

def cutLoop (g : Store V → Prop) [DecidablePred g] (P : Finite V w h) : ℕ → Finite V w h
  | 0 => .abort
  | i+1 => .branch g (.seq P (cutLoop g P i)) .skip

def cut (t : ℕ) : FirstQuery.Circ V w h → Finite V w h
  | .skip => .skip
  | .step U => .step U
  | .oracle r => .oracle r
  | .measure x r => .measure x r
  | .seq C D => .seq (cut t C) (cut t D)
  | @OracleDynamicCircuit.qIf _ _ _ _ g _ C D => .branch g (cut t C) (cut t D)
  | @OracleDynamicCircuit.qWhile _ _ _ _ g _ C => cutLoop g (cut t C) t

theorem compile_cutLoop (O : Unitary (2^h)) (g : Store V → Prop) [DecidablePred g]
    (P : Finite V w h) (i : ℕ) :
    compile O (cutLoop g P i) = Fuel.unroll g (compile O P) i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [compile, cutLoop, Fuel.unroll, ih]

theorem compile_cut (O : Unitary (2^h)) (t : ℕ) (C : FirstQuery.Circ V w h) :
    compile O (cut t C) = Fuel.cap t (C.compile QProg.qAssign O) := by
  induction C with
  | skip | step | oracle | measure => rfl
  | seq C D ihC ihD => simp [compile, cut, Fuel.cap, ihC, ihD]
  | qIf g C D ihC ihD => simp [compile, cut, Fuel.cap, ihC, ihD]
  | qWhile g C ih => simp [cut, Fuel.cap, compile_cutLoop, ih]

inductive Tree (V : Type) (w h : ℕ) where
  | timeout
  | halt (σ : Store V)
  | fixed (U : Unitary (2^w)) (child : Tree V w h)
  | query (r : QRegister h w) (child : Tree V w h)
  | measure {k : ℕ} (r : QRegister k w) (child : Fin (2^k) → Tree V w h)

/-- Continuation expansion preserves dirty classical stores and retains every
measurement outcome even if distinct paths subsequently reach the same source store. -/
noncomputable def build [DecidableEq V] :
    Finite V w h → Store V → (Store V → Tree V w h) → Tree V w h
  | .skip, σ, K => K σ
  | .abort, _, _ => .timeout
  | .step U, σ, K => .fixed U (K σ)
  | .oracle r, σ, K => .query r (K σ)
  | .measure x r, σ, K => .measure r (fun o => K (σ.subst x (fun _ => o.val)))
  | .seq C D, σ, K => build C σ (fun τ => build D τ K)
  | @Finite.branch _ _ _ g _ C D, σ, K => if g σ then build C σ K else build D σ K

abbrev Vec (w : ℕ) := Fin (2^w) → ℂ
noncomputable def energy (ψ : Vec w) : ℝ := ∑ i, Complex.normSq (ψ i)

/-- Fold all paths with arbitrary terminal payoff and a per-query price. Timeout mass
can be evaluated separately by taking a nonzero timeout payoff. -/
noncomputable def score (O : Unitary (2^h)) (price : ℝ)
    (timeout : Vec w → ℝ) (halt : Store V → Vec w → ℝ) : Tree V w h → Vec w → ℝ
  | .timeout, ψ => timeout ψ
  | .halt σ, ψ => halt σ ψ
  | .fixed U T, ψ => score O price timeout halt T (U.1.mulVec ψ)
  | .query r T, ψ => price*energy ψ + score O price timeout halt T ((r.embedUnitary O).1.mulVec ψ)
  | .measure r T, ψ =>
      ∑ i, score O price timeout halt (T i) ((r.basisOutcomeProjector i).mulVec ψ)

#print axioms compile_cut
end Track2Grover.Path
