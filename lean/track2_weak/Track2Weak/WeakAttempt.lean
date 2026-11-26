module
public import Track2Weak.Initialize
public import Track2Weak.WeakWalkHistory
public import Track2Weak.WeakCertFlow
import all Track2Weak.WeakWalkStages
import all Track2Grover.Engine.FindAllJohnsonRampKickMuxBridge

@[expose] public section
namespace Track2Weak
open Operator ResourceCounting Matrix QuantumComputation.Specs.DickeSol
open scoped Matrix NNReal

noncomputable def Cert.Row.phys (q : Cert.Row) : WeakRow :=
  (q.seg, RealFlagPair.ofAmplitude (min q.factor 1)
    (le_min (by unfold Cert.Row.factor; positivity) zero_le_one) (min_le_right _ _))

theorem Cert.Row.phys_factor {q : Cert.Row} (hq : Cert.RowOK q) : q.phys.2.cVal = q.factor := by
  change min q.factor 1 = q.factor
  exact min_eq_left (by nlinarith [hq.factor_sq, sq_nonneg (q.factor - 1)])

theorem Cert.Row.phys_walk (q : Cert.Row) (n : ℕ) (x : Cert.V) :
    weakOrbitStep n 512 q.phys x = q.walk n x := rfl

theorem Cert.Row.phys_keep {q : Cert.Row} (hq : Cert.RowOK q) (n : ℕ) (x : Cert.V) :
    weakNo n q.phys x = weakKeep 512 q.factor (q.walk n x) := by
  unfold weakNo
  rw [Cert.Row.phys_factor hq, Cert.Row.phys_walk]

def weakQubits (n : ℕ) := 1024*(n+1)+512*n
theorem weakRoom (n : ℕ) : 512*n < 1024*(n+1) := by omega
theorem weakSize {n : ℕ} (hn : 80000 ≤ n) : 1024+512 ≤ 2^n :=
  (by decide : 1024+512 ≤ 2^11).trans (Nat.pow_le_pow_right (by decide) (by omega))

noncomputable def weakFinish {Var : Type} (res : Var) (n : ℕ) : WeakCellCirc Var n :=
  weakTerminalRead res n 1024 512 (512*n) (weakRoom n)

noncomputable def weakTrial {Var : Type} (res : Var) (qs : List Cert.Row) (n : ℕ) : WeakCellCirc Var n :=
  if hn : 80000 ≤ n then
    .seq (weakInitialize res n 1024 (512*n) (by have := weakSize hn; omega))
      (weakStages res n (by omega) (weakFinish res n) (qs.map Cert.Row.phys))
  else .skip

theorem weakUniform {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512) :
    weakOrbitLift S hS (u0OrbVecGen (2^n) 1024 512) = u0Vec (2^n) 1024 := by
  have aux {r : ℕ} (hr : S.card = r) (hm : 1024 + r ≤ 2^n) :
      weakOrbitLift S hr (u0OrbVecGen (2^n) 1024 r) = u0Vec (2^n) 1024 := by
    subst r
    exact orbEmbedGen_u0OrbVecGen hm
  exact aux hS (weakSize hn)

theorem weakUniformMass {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512) :
    vecSqNorm (u0OrbVecGen (2^n) 1024 512) = 1 := by
  have hm := weakSize hn
  have hmr : 1024 + S.card ≤ 2^n := by omega
  have hd := dot_orbEmbedGen hmr (u0OrbVecGen (2^n) 1024 S.card) (u0OrbVecGen (2^n) 1024 S.card)
  rw [orbEmbedGen_u0OrbVecGen hmr, hS] at hd
  simpa only [vecSqNorm, sq, ← hd] using
    (sum_sq_u0Vec (N := 2^n) (m := 1024) (by omega))

theorem weakTrial_wp {Var : Type} [DecidableEq Var] [Subsingleton Var] (res : Var) (qs : List Cert.Row)
    {n : ℕ} (hn : 80000 ≤ n) (S : Finset (Fin (2^n))) (hS : S.card = 512)
    (Θ : CQAssertion (Store Var) (2^(weakQubits n))) (σ : Store Var) :
    ((wp ((weakTrial res qs n).compile QProg.qAssign (groverParallelMarkingOracle 1024 S)) Θ) σ).1.1 =
      rmsVecQuad ((wp ((weakStages res n (by omega) (weakFinish res n) (qs.map Cert.Row.phys)).compile
        QProg.qAssign (groverParallelMarkingOracle 1024 S)) Θ) (fun _ ↦ 0)).1.1
        (weakState S hS (u0OrbVecGen (2^n) 1024 512) 0) • (1 : Operator _) := by
  unfold weakQubits at Θ
  simp only [weakQubits, weakTrial, dite_eq_left hn, OracleDynamicCircuit.compile_seq, wp_qSeq,
    weakInitialize_wp, weakState, weakUniform hn S hS]

end Track2Weak
