import Decoupling.HighDim.LaurentLinearSolverKernel
import Decoupling.HighDim.LaurentArithmeticStructural
import Decoupling.HighDim.CohomologyComputedBasis
import Decoupling.HighDim.CohomologyRelationsIndexed

/-!
# HD012 executable cohomology computation: stored data and actual relations

All intermediate matrices below are materialized arrays. Kernel modules
are computed by the proved complete Laurent routine. Relations are found
from the true matrix `[W | -b]`; augmentation and quotient elimination
execute their own counted programs.
-/
namespace Decoupling.HighDim.AlgorithmTwoCohomology
open ArithmeticCost Matrix
open LaurentArithmetic
variable {K : Type} [Field K] {D q m r h B B' g t : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure Result (K : Type) (D q B : ℕ) where
  dimension : ℕ
  cocycles : DenseMatrix K D q dimension B

/-- Select the actual Gaussian free-column indices from the original
cycle-generator array. This performs no field arithmetic. -/
def selectCocycles (W : DenseMatrix K D q g B)
    (indices : Vector (Fin g) t) : DenseMatrix K D q t B :=
  Vector.ofFn fun i => Vector.ofFn fun j => W[i][indices[j]]

theorem selectCocycles_denote (W : DenseMatrix K D q g B) (indices : Vector (Fin g) t) :
    matrixDenote (selectCocycles W indices) = (matrixDenote W).submatrix id
      (fun j => indices[j]) := by
  funext i j
  simp [matrixDenote, selectCocycles]

def relationInput (b : DenseMatrix K D q m h) (W : DenseMatrix K D q g B) :
    Work K (DenseMatrix K D q (g + m) (max B h)) :=
  Work.bind (matrixNegProgram (matrixPad b (max B h))) fun nb =>
    Work.pure (joinColumns (matrixPad W (max B h)) nb)

theorem relationInput_denote (b : DenseMatrix K D q m h) (W : DenseMatrix K D q g B) :
    matrixDenote (relationInput b W).value =
      CohomologyPresentation.indexedRelationSystem (matrixDenote b) (matrixDenote W) := by
  simp only [relationInput, Work.bind_value, Work.pure_value]
  rw [joinColumns_correct, matrixNegProgram_correct,
    matrixPad_correct _ (le_max_left _ _), matrixPad_correct _ (le_max_right _ _)]
  rfl

@[simp] theorem relationInput_cost (b : DenseMatrix K D q m h) (W : DenseMatrix K D q g B) :
    (relationInput b W).cost = q * m * boxSize D (max B h) := by
  simp [relationInput]

/-- Project genuine relations onto the W-coefficients, copying arrays. -/
def projectRelations (V : DenseMatrix K D (g + m) t B') : DenseMatrix K D g t B' :=
  Vector.ofFn fun i => V[finSumFinEquiv (Sum.inl i)]

theorem projectRelations_denote (V : DenseMatrix K D (g + m) t B') :
    matrixDenote (projectRelations V) =
      CohomologyPresentation.indexedRelationProjection (matrixDenote V) := by
  funext i j
  simp [matrixDenote, projectRelations, CohomologyPresentation.indexedRelationProjection]

variable [DecidableEq K]

def finish (W : DenseMatrix K D q g B) (V : DenseMatrix K D (g + m) t B') :
    Work K (Result K D q B) :=
  Work.bind (matrixAugmentationProgram (projectRelations V)) fun U₀ =>
    Work.bind (FiniteLinearSolver.quotientData U₀) fun data =>
      Work.pure ⟨data.dimension, selectCocycles W data.freeColumns⟩

/-- One full cohomology window: two complete Laurent kernels, actual
augmentation, actual finite quotient basis, and selected actual cocycles. -/
def compute (b : DenseMatrix K D q m h) (d : DenseMatrix K D r q h) :
    Work K (Result K D q (LaurentLinearSolver.outputBox D r h)) :=
  Work.bind (LaurentLinearSolver.kernel d) fun W =>
    Work.bind (relationInput b W.coefficients) fun R =>
      Work.bind (LaurentLinearSolver.kernel R) fun V => finish W.coefficients V.coefficients

end Decoupling.HighDim.AlgorithmTwoCohomology
