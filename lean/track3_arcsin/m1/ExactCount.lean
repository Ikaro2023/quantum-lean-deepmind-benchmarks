module

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.StageProofB

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl.ExactAudit

open Function Operator Step

private theorem exactOp {Var : Type} {n : ℕ} (v : Var)
    (rd ra : QRegister 50 n) (hd : rd.DisjointWires ra)
    (g : Op102) {m m' : Fin 100 → Bool} (h : execOp102 m g = some m') :
    (g.compile v rd ra).count PrimitiveGate.T = g.tCount := by
  have inj := @hw25_inj n rd ra hd
  cases g <;> first | exact Nat.eq_zero_of_le_zero (Op102.count_T_compile v rd ra _) | skip
  case hGadget t pos neg uc ul =>
    have hg : checkHGadgetStatic t pos neg uc ul = true := by
      by_contra bad
      simp [execOp102, bad] at h
    simp [Op102.compile, Op102.tCount, hg, DynamicCircuit.count, count_T_hGadgetCircuit]
  all_goals
    rename_i a b t
    have hv : a < 100 ∧ b < 100 ∧ t < 100 ∧ a ≠ b ∧ a ≠ t ∧ b ≠ t := by
      by_contra bad
      simp [execOp102, bad] at h
    obtain ⟨ha, hb, ht, hab, hat, hbt⟩ := hv
    have hphys : w25 rd ra a ≠ w25 rd ra b ∧ w25 rd ra a ≠ w25 rd ra t ∧
        w25 rd ra b ≠ w25 rd ra t :=
      ⟨fun e => hab (inj ha hb e), fun e => hat (inj ha ht e), fun e => hbt (inj hb ht e)⟩
    simp [Op102.compile, Op102.toStep, Step.compile, hphys, DynamicCircuit.count,
      count_T_AND4T, count_T_RCCX0, count_T_RCCX1, Op102.tCount]

private theorem exactList {Var : Type} {n : ℕ} (v : Var)
    (rd ra : QRegister 50 n) (hd : rd.DisjointWires ra)
    (ops : List Op102) {m m' : Fin 100 → Bool} (h : execList102 ops m = some m') :
    (compileList102 v rd ra ops).count PrimitiveGate.T = (ops.map Op102.tCount).sum := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih =>
    cases hop : execOp102 m op with
    | none => simp [execList102, hop] at h
    | some k =>
      have tail : execList102 ops k = some m' := by simpa only [execList102, hop] using h
      simp only [compileList102, DynamicCircuit.count, List.map_cons, List.sum_cons,
        exactOp v rd ra hd op hop, ih tail]

/-- Exact physical T count for every disjoint placement of the two 50-wire registers. -/
theorem count_T_k25DynCircuit_eq {Var : Type} {n : ℕ} (v : Var)
    (rd ra : QRegister 50 n) (hd : rd.DisjointWires ra) :
    (k25DynCircuit v rd ra).count PrimitiveGate.T = 3662 := by
  let zero : Fin 100 → Bool := fun _ => false
  have hy : ∀ i : Nat, (hi : i < 25) → zero ⟨25 + i, by omega⟩ =
      (sliceVal 25 25 zero).testBit i := by
    intro i hi
    change false = (0 : Nat).testBit i
    simp
  obtain ⟨m, h, _⟩ := exec_fullK25Ops (m0 := zero) hy (fun _ _ => rfl)
  unfold k25DynCircuit
  exact (exactList v rd ra hd fullK25Ops h).trans tCount_fullK25Ops

#print axioms count_T_k25DynCircuit_eq

end QuantumComputation.Specs.ArcsinImpl.ExactAudit
