import Decoupling.HighDim.AlgorithmTwoLinearComparisonConeArray
import Decoupling.HighDim.AlgorithmTwoFiniteComplexConeBlocks

/-! # Actual inverse and homotopy arrays extracted from the solved H -/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open Matrix ArithmeticCost AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D m n h : ℕ}

def blockArray {a b q r : ℕ} (H : LaurentArithmetic.DenseMatrix K D q r h)
    (rows : Fin a → Fin q) (cols : Fin b → Fin r) : LaurentArithmetic.DenseMatrix K D a b h :=
  Vector.ofFn fun i => Vector.ofFn fun j => H[rows i][cols j]

theorem blockArray_correct {a b q r : ℕ} (H : LaurentArithmetic.DenseMatrix K D q r h)
    (rows : Fin a → Fin q) (cols : Fin b → Fin r) :
    LaurentArithmetic.matrixDenote (blockArray H rows cols) =
      (LaurentArithmetic.matrixDenote H).submatrix rows cols := by
  funext i j
  simp only [blockArray, LaurentArithmetic.matrixDenote, Fin.getElem_fin, Vector.getElem_ofFn,
    Fin.eta, Matrix.submatrix_apply]

structure Extracted (K : Type*) (D m n h : ℕ) where
  inverse : LaurentArithmetic.DenseMatrix K D m n h
  sourceHomotopy : LaurentArithmetic.DenseMatrix K D m m h
  targetHomotopy : LaurentArithmetic.DenseMatrix K D n n h

def extractProgram (H : LaurentArithmetic.DenseMatrix K D (m+n) (m+n) h) :
    Work K (Extracted K D m n h) :=
  let left : Fin m → Fin (m+n) := fun i => finSumFinEquiv (.inl i)
  let right : Fin n → Fin (m+n) := fun i => finSumFinEquiv (.inr i)
  Work.bind (LaurentArithmetic.matrixNegProgram (blockArray H right right)) fun negTarget =>
    Work.pure ⟨blockArray H left right, blockArray H left left, negTarget⟩

theorem extractProgram_cost (H : LaurentArithmetic.DenseMatrix K D (m+n) (m+n) h) :
    (extractProgram H).cost = n*n*LaurentArithmetic.boxSize D h := by
  simp [extractProgram]

theorem extractProgram_inverse (H : LaurentArithmetic.DenseMatrix K D (m+n) (m+n) h) :
    LaurentArithmetic.matrixDenote (extractProgram H).value.inverse =
      inverseBlock (LaurentArithmetic.matrixDenote H) := by
  rw [extractProgram, Work.bind_value, Work.pure_value, blockArray_correct]
  rfl

theorem extractProgram_source (H : LaurentArithmetic.DenseMatrix K D (m+n) (m+n) h) :
    LaurentArithmetic.matrixDenote (extractProgram H).value.sourceHomotopy =
      sourceBlock (LaurentArithmetic.matrixDenote H) := by
  rw [extractProgram, Work.bind_value, Work.pure_value, blockArray_correct]
  rfl

theorem extractProgram_target (H : LaurentArithmetic.DenseMatrix K D (m+n) (m+n) h) :
    LaurentArithmetic.matrixDenote (extractProgram H).value.targetHomotopy =
      targetBlock (LaurentArithmetic.matrixDenote H) := by
  rw [extractProgram, Work.bind_value, Work.pure_value, LaurentArithmetic.matrixNegProgram_correct,
    blockArray_correct]
  rfl

end Decoupling.HighDim.AlgorithmTwoLinearComparison
