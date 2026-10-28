import Decoupling.HighDim.AlgorithmTwoLinearComparisonContraction
import Decoupling.HighDim.AlgorithmTwoFiniteComplexCone

/-! # Actual signed mapping-cone arrays and their arithmetic trace -/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open Matrix ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D m n h : ℕ}

/-- Block assembly is pure copying of materialized coefficients. -/
def coneArray (negativeSource : LaurentArithmetic.DenseMatrix K D m m h)
    (target : LaurentArithmetic.DenseMatrix K D n n h)
    (map : LaurentArithmetic.DenseMatrix K D n m h) :
    LaurentArithmetic.DenseMatrix K D (m+n) (m+n) h :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    match finSumFinEquiv.symm i, finSumFinEquiv.symm j with
    | .inl a, .inl b => negativeSource[a][b]
    | .inl _, .inr _ => zeroDense
    | .inr a, .inl b => map[a][b]
    | .inr a, .inr b => target[a][b]

theorem coneArray_correct (negativeSource : LaurentArithmetic.DenseMatrix K D m m h)
    (target : LaurentArithmetic.DenseMatrix K D n n h)
    (map : LaurentArithmetic.DenseMatrix K D n m h) :
    LaurentArithmetic.matrixDenote (coneArray negativeSource target map) =
      (Matrix.fromBlocks (LaurentArithmetic.matrixDenote negativeSource) 0
        (LaurentArithmetic.matrixDenote map) (LaurentArithmetic.matrixDenote target)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  funext i j
  simp only [LaurentArithmetic.matrixDenote, coneArray, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;>
    rcases finSumFinEquiv.symm j with b | b <;> simp [Matrix.fromBlocks, LaurentArithmetic.matrixDenote]

def coneArrayProgram (source : LaurentArithmetic.DenseMatrix K D m m h)
    (target : LaurentArithmetic.DenseMatrix K D n n h)
    (map : LaurentArithmetic.DenseMatrix K D n m h) :
    Work K (LaurentArithmetic.DenseMatrix K D (m+n) (m+n) h) :=
  Work.bind (LaurentArithmetic.matrixNegProgram source) fun negSource =>
    Work.pure (coneArray negSource target map)

theorem coneArrayProgram_cost (source : LaurentArithmetic.DenseMatrix K D m m h)
    (target : LaurentArithmetic.DenseMatrix K D n n h)
    (map : LaurentArithmetic.DenseMatrix K D n m h) :
    (coneArrayProgram source target map).cost = m*m*LaurentArithmetic.boxSize D h := by
  simp [coneArrayProgram]

theorem coneArrayProgram_correct (source : LaurentArithmetic.DenseMatrix K D m m h)
    (target : LaurentArithmetic.DenseMatrix K D n n h)
    (map : LaurentArithmetic.DenseMatrix K D n m h) :
    LaurentArithmetic.matrixDenote (coneArrayProgram source target map).value =
      (Matrix.fromBlocks (-LaurentArithmetic.matrixDenote source) 0
        (LaurentArithmetic.matrixDenote map) (LaurentArithmetic.matrixDenote target)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
  simp only [coneArrayProgram, Work.bind_value, Work.pure_value, coneArray_correct,
    LaurentArithmetic.matrixNegProgram_correct]

end Decoupling.HighDim.AlgorithmTwoLinearComparison
