import Decoupling.HighDim.LaurentArithmeticMatrix

/-! # HD012 coefficient copying, block assembly and counted augmentation -/
namespace Decoupling.HighDim.LaurentArithmetic
open ArithmeticCost Matrix
variable {K : Type*} [Field K] {D h H m n r : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- Copy into a larger box. This performs no field arithmetic. -/
def pad (v : Dense K D h) (H : ℕ) : Dense K D H :=
  Vector.ofFn fun k => lookup v (exponentAt D H k)

theorem pad_correct (v : Dense K D h) (hH : h ≤ H) : denote (pad v H) = denote v := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_mono (denote_supported v) hH
  · intro k
    simp [pad, denote_coeff]

def matrixPad (A : DenseMatrix K D m n h) (H : ℕ) : DenseMatrix K D m n H :=
  Vector.ofFn fun i => Vector.ofFn fun j => pad A[i][j] H

theorem matrixPad_correct (A : DenseMatrix K D m n h) (hH : h ≤ H) :
    matrixDenote (matrixPad A H) = matrixDenote A := by
  funext i j
  simp only [matrixDenote, matrixPad, Fin.getElem_fin, Vector.getElem_ofFn]
  exact pad_correct A[i][j] hH

def matrixNegProgram (A : DenseMatrix K D m n h) : Work K (DenseMatrix K D m n h) :=
  collect m fun i => collect n fun j => negProgram A[i][j]

@[simp] theorem matrixNegProgram_cost (A : DenseMatrix K D m n h) :
    (matrixNegProgram A).cost = m * n * boxSize D h := by
  simp [matrixNegProgram, mul_assoc]

theorem matrixNegProgram_correct (A : DenseMatrix K D m n h) :
    matrixDenote (matrixNegProgram A).value = -matrixDenote A := by
  funext i j
  change denote ((matrixNegProgram A).value[i][j]) = _
  simp only [matrixNegProgram, collect_value_get, negProgram_correct]
  rfl

/-- Concatenate already materialized column arrays, with no field operations. -/
def joinColumns (A : DenseMatrix K D m n h) (B : DenseMatrix K D m r h) :
    DenseMatrix K D m (n + r) h :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    Sum.elim (fun k => A[i][k]) (fun k => B[i][k]) (finSumFinEquiv.symm j)

theorem joinColumns_correct (A : DenseMatrix K D m n h) (B : DenseMatrix K D m r h) :
    matrixDenote (joinColumns A B) =
      (Matrix.fromCols (matrixDenote A) (matrixDenote B)).submatrix id finSumFinEquiv.symm := by
  funext i j
  simp only [matrixDenote, joinColumns, Fin.getElem_fin, Vector.getElem_ofFn,
    Matrix.submatrix_apply]
  cases finSumFinEquiv.symm j <;> rfl

/-- Evaluation at all translation variables equal to one is an actual sum
of the dense coefficient entries. Its additions are counted. -/
def augmentationProgram (v : Dense K D h) : Work K K :=
  sumValues (boxSize D h) (fun k => v[k])

@[simp] theorem augmentationProgram_cost (v : Dense K D h) :
    (augmentationProgram v).cost = boxSize D h := by simp [augmentationProgram]

theorem augmentationProgram_correct (v : Dense K D h) :
    (augmentationProgram v).value = augmentation (denote v) := by
  simp [augmentationProgram, denote, augmentation]

def matrixAugmentationProgram (A : DenseMatrix K D m n h) :
    Work K (FiniteLinearSolver.DenseMatrix K m n) :=
  collect m fun i => collect n fun j => augmentationProgram A[i][j]

@[simp] theorem matrixAugmentationProgram_cost (A : DenseMatrix K D m n h) :
    (matrixAugmentationProgram A).cost = m * n * boxSize D h := by
  simp [matrixAugmentationProgram, mul_assoc]

theorem matrixAugmentationProgram_correct (A : DenseMatrix K D m n h) :
    FiniteLinearSolver.matrix (matrixAugmentationProgram A).value =
      (matrixDenote A).map augmentation := by
  funext i j
  change (matrixAugmentationProgram A).value[i][j] = _
  simp only [matrixAugmentationProgram, collect_value_get, augmentationProgram_correct]
  rfl

end Decoupling.HighDim.LaurentArithmetic
