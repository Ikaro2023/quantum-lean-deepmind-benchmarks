import Track2Grover.OracleCompression

namespace Track2Grover.Physical
open Operator QuantumComputation.Specs
open GroverSolution (flagConj fullReg sDiagM slotAddr slotFlag)
open scoped Matrix
open Finset

def swapWidth {n m q : ℕ} (r : QRegister ((n+1)*m) q) : QRegister (m*(n+1)) q :=
  r.compose (QRegister.block 0 (m*(n+1)) (by simp [Nat.mul_comm]))

theorem swap_back {n m q : ℕ} (r : QRegister ((n+1)*m) q) :
    (swapWidth r).compose (fullReg n m) = r := by
  apply QRegister.ext
  apply Function.Embedding.ext
  intro i
  change r _ = r i
  congr 1
  apply Fin.ext
  simp [fullReg]

noncomputable def B {n m q : ℕ} (r : QRegister ((n+1)*m) q) :=
  (swapWidth r).embedUnitary (flagConj n m)
noncomputable def O {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :=
  r.embedUnitary (groverParallelMarkingOracle m S)
noncomputable def D {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :=
  (swapWidth r).embedMatrix (sDiagM n m S)

theorem conj_eq {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :
    (B r).1 * (O r S).1 * (B r).1 = D r S := by
  unfold O
  rw [show r.embedUnitary (groverParallelMarkingOracle m S) =
        (swapWidth r).embedUnitary ((fullReg n m).embedUnitary (groverParallelMarkingOracle m S)) by
    rw [← QRegister.embedUnitary_compose, swap_back]]
  change (swapWidth r).embedMatrix _ * (swapWidth r).embedMatrix _ * (swapWidth r).embedMatrix _ = _
  rw [← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
  exact congrArg (swapWidth r).embedMatrix (Compression.diagonal_form S)

def eigenSign {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) (z : Fin (2^q)) : ℤ :=
  ∏ j : Fin m, if slotAddr n m ((swapWidth r).extractIndex z) j ∈ S ∧
    slotFlag n m ((swapWidth r).extractIndex z) j = 0 then -1 else 1

theorem diag_eq {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :
    D r S = Matrix.diagonal (fun z ↦ (eigenSign r S z : ℂ)) := by
  unfold D sDiagM
  rw [QRegister.embedMatrix_diagonal]
  congr 1
  funext z
  unfold eigenSign
  push_cast
  apply prod_congr rfl
  intro j _
  unfold GroverSolution.slotDiag
  split <;> simp_all

theorem B_inv {n m q : ℕ} (r : QRegister ((n+1)*m) q) : (B r).1 * (B r).1 = 1 := by
  have h0 : (groverSetMarkingOracle (∅ : Finset (Fin (2^n)))) = 1 := by
    apply Subtype.ext
    ext i j
    rw [groverSetMarkingOracle, GroverSolution.permutationUnitary_apply,
      show GroverSolution.markPerm (∅ : Finset (Fin (2^n))) j = j from
        (splitBasisEquiv n 1).injective (by simp)]
    rfl
  have he : O r ∅ = 1 := by simp [O, groverParallelMarkingOracle, h0]
  simpa [he, diag_eq, eigenSign] using conj_eq r ∅

theorem D_inv {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :
    D r S * D r S = 1 := by
  rw [diag_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext z
  have h : eigenSign r S z = -1 ∨ eigenSign r S z = 1 :=
    GroverSolution.prod_ite_neg_one_or_one univ _
  rcases h with h|h <;> simp [h]

theorem oracle_diag {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :
    (O r S).1 = (B r).1 * D r S * (B r).1 := by
  rw [← conj_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B_inv, Matrix.one_mul,
    Matrix.mul_assoc, B_inv, Matrix.mul_one]

theorem O_inv {n m q : ℕ} (r : QRegister ((n+1)*m) q) (S : Finset (Fin (2^n))) :
    (O r S).1 * (O r S).1 = 1 := by
  rw [oracle_diag]
  calc
    _ = (B r).1 * (D r S * ((B r).1*(B r).1) * D r S) * (B r).1 := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [B_inv, Matrix.mul_one, D_inv, Matrix.mul_one, B_inv]

#print axioms oracle_diag
#print axioms O_inv
end Track2Grover.Physical
