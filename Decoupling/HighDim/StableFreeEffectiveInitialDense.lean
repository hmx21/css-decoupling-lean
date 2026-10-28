import Decoupling.HighDim.StableFreeEffectiveInitialMatrix
import Decoupling.HighDim.StableFreeEffectiveDense

/-! # HD012 counted dense operations used by the initial Schanuel formulas -/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open Matrix ArithmeticCost LaurentArithmetic
variable {K : Type*} [Field K] {D a b c h : ℕ}
set_option backward.isDefEq.respectTransparency false

def zeroMatrix (K : Type*) [Zero K] (D a b h : ℕ) : DenseMatrix K D a b h :=
  Vector.ofFn fun _ => Vector.ofFn fun _ => zeroDense K D h

theorem zeroMatrix_correct : matrixDenote (zeroMatrix K D a b h) = 0 := by
  funext i j
  simp [matrixDenote, zeroMatrix, zeroDense_correct]

def rows (A : DenseMatrix K D a c h) (B : DenseMatrix K D b c h) :
    DenseMatrix K D (a+b) c h :=
  Vector.ofFn fun i => Sum.elim (fun j => A[j]) (fun j => B[j]) (finSumFinEquiv.symm i)

omit [Field K] in
theorem rows_get (A : DenseMatrix K D a c h) (B : DenseMatrix K D b c h)
    (i : Fin (a+b)) :
    (rows A B)[i] = Sum.elim (fun j => A[j]) (fun j => B[j]) (finSumFinEquiv.symm i) := by
  simp only [rows, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

theorem rows_correct (A : DenseMatrix K D a c h) (B : DenseMatrix K D b c h) :
    matrixDenote (rows A B) = joinRows (matrixDenote A) (matrixDenote B) := by
  funext i j
  obtain ⟨k,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b)).surjective i
  change denote ((rows A B)[finSumFinEquiv k][j]) =
    (Matrix.fromRows (matrixDenote A) (matrixDenote B)) (finSumFinEquiv.symm (finSumFinEquiv k)) j
  simp only [rows_get, Equiv.symm_apply_apply]
  cases k <;> rfl

theorem cols_correct (A : DenseMatrix K D a b h) (B : DenseMatrix K D a c h) :
    matrixDenote (joinColumns A B) = joinCols (matrixDenote A) (matrixDenote B) :=
  joinColumns_correct A B

def addSame (A B : DenseMatrix K D a b h) : Work K (DenseMatrix K D a b h) :=
  collect a fun i => collect b fun j => collect (boxSize D h) fun k =>
    ArithmeticCost.add A[i][j][k] B[i][j][k]

@[simp] theorem addSame_cost (A B : DenseMatrix K D a b h) :
    (addSame A B).cost = a*b*boxSize D h := by simp [addSame, Nat.mul_assoc]

theorem addSame_correct (A B : DenseMatrix K D a b h) :
    matrixDenote (addSame A B).value = matrixDenote A + matrixDenote B := by
  funext i j
  change denote ((addSame A B).value[i][j]) = _
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_add (denote_supported A[i][j]) (denote_supported B[i][j])
  · intro k
    simp [addSame, matrixDenote, denote_coeff]

def subSame (A B : DenseMatrix K D a b h) : Work K (DenseMatrix K D a b h) :=
  collect a fun i => collect b fun j => subtractDense A[i][j] B[i][j]

@[simp] theorem subSame_cost (A B : DenseMatrix K D a b h) :
    (subSame A B).cost = a*b*boxSize D h := by simp [subSame, Nat.mul_assoc]

theorem subSame_correct (A B : DenseMatrix K D a b h) :
    matrixDenote (subSame A B).value = matrixDenote A - matrixDenote B := by
  funext i j
  change denote ((subSame A B).value[i][j]) = _
  simp only [subSame, collect_value_get, subtractDense_correct]
  rfl

end Decoupling.HighDim.StableFree.Effective.Initial
