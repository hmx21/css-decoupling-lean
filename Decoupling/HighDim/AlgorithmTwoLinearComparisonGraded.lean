import Decoupling.HighDim.AlgorithmTwoLinearComparisonProgram
import Decoupling.HighDim.AlgorithmTwoFiniteComplexContraction

/-! # Actual graded comparison and contraction input arrays -/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open Matrix ArithmeticCost
variable {K : Type*} [Field K] {D n m k h : ℕ}

/-- Integer label tests require no field arithmetic. -/
def gradedMask (source : Vector ℤ m) (target : Vector ℤ n) (s : ℤ) : Mask n m :=
  Vector.ofFn fun i => Vector.ofFn fun j => decide (target.get i = source.get j + s)

theorem gradedMask_iff (source : Vector ℤ m) (target : Vector ℤ n) (s : ℤ)
    (X : Matrix (Fin n) (Fin m) (Laurent K D)) :
    (∀ i j, maskFunction (gradedMask source target s) i j = false → X i j = 0) ↔
      AlgorithmTwoFiniteComplex.Homogeneous source target s X := by
  simp only [maskFunction, gradedMask, Fin.getElem_fin, Vector.getElem_ofFn, decide_eq_false_iff_not,
    AlgorithmTwoFiniteComplex.Homogeneous]

def zeroMatrix : LaurentArithmetic.DenseMatrix K D n m h :=
  Vector.replicate n (Vector.replicate m zeroDense)

def identityMatrix : LaurentArithmetic.DenseMatrix K D n n h :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i=j then oneDense else zeroDense

@[simp] theorem zeroMatrix_correct : LaurentArithmetic.matrixDenote (zeroMatrix (K := K) (D := D) (n := n) (m := m) (h := h)) = 0 := by
  funext i j
  simp [LaurentArithmetic.matrixDenote, zeroMatrix]

@[simp] theorem identityMatrix_correct : LaurentArithmetic.matrixDenote (identityMatrix (K := K) (D := D) (n := n) (h := h)) = 1 := by
  funext i j
  simp only [LaurentArithmetic.matrixDenote, identityMatrix, Fin.getElem_fin, Vector.getElem_ofFn, Matrix.one_apply]
  split_ifs <;> simp

def comparisonInput (dT : LaurentArithmetic.DenseMatrix K D m m h)
    (dC : LaurentArithmetic.DenseMatrix K D n n h)
    (top : LaurentArithmetic.DenseMatrix K D m k h)
    (cocycles : LaurentArithmetic.DenseMatrix K D n k h)
    (source : Vector ℤ m) (target : Vector ℤ n) : Work K (Input K D n m k h) :=
  Work.bind (LaurentArithmetic.matrixNegProgram dT) fun negT =>
    Work.pure ⟨dC, negT, top, zeroMatrix, cocycles, gradedMask source target 0⟩

theorem comparisonInput_cost (dT : LaurentArithmetic.DenseMatrix K D m m h)
    (dC : LaurentArithmetic.DenseMatrix K D n n h)
    (top : LaurentArithmetic.DenseMatrix K D m k h)
    (cocycles : LaurentArithmetic.DenseMatrix K D n k h)
    (source : Vector ℤ m) (target : Vector ℤ n) :
    (comparisonInput dT dC top cocycles source target).cost = m*m*LaurentArithmetic.boxSize D h := by
  simp [comparisonInput]

theorem comparisonInput_correct (dT : LaurentArithmetic.DenseMatrix K D m m h)
    (dC : LaurentArithmetic.DenseMatrix K D n n h)
    (top : LaurentArithmetic.DenseMatrix K D m k h)
    (cocycles : LaurentArithmetic.DenseMatrix K D n k h)
    (source : Vector ℤ m) (target : Vector ℤ n) (X : Matrix (Fin n) (Fin m) (Laurent K D)) :
    (comparisonInput dT dC top cocycles source target).value.Satisfied X ↔
      LaurentArithmetic.matrixDenote dC * X = X * LaurentArithmetic.matrixDenote dT ∧
      X * LaurentArithmetic.matrixDenote top = LaurentArithmetic.matrixDenote cocycles ∧
      AlgorithmTwoFiniteComplex.Homogeneous source target 0 X := by
  change Satisfies _ _ _ _ _ _ X ↔ _
  simp only [comparisonInput, Work.bind_value, Work.pure_value, Satisfies,
    LaurentArithmetic.matrixNegProgram_correct, zeroMatrix_correct, Matrix.mul_neg,
    ← sub_eq_add_neg, sub_eq_zero, gradedMask_iff]

def contractionInput (d : LaurentArithmetic.DenseMatrix K D n n h)
    (degree : Vector ℤ n) : Input K D n n 0 h :=
  ⟨d, d, zeroMatrix, identityMatrix, zeroMatrix, gradedMask degree degree (-1)⟩

theorem contractionInput_correct (d : LaurentArithmetic.DenseMatrix K D n n h)
    (degree : Vector ℤ n) (H : Matrix (Fin n) (Fin n) (Laurent K D)) :
    (contractionInput d degree).Satisfied H ↔
      LaurentArithmetic.matrixDenote d * H + H * LaurentArithmetic.matrixDenote d = 1 ∧
      AlgorithmTwoFiniteComplex.Homogeneous degree degree (-1) H := by
  simp only [Input.Satisfied, contractionInput, Satisfies, zeroMatrix_correct,
    identityMatrix_correct, Matrix.mul_zero, gradedMask_iff, true_and]

end Decoupling.HighDim.AlgorithmTwoLinearComparison
