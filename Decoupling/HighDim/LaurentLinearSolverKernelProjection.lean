import Decoupling.HighDim.LaurentLinearSolverProjection

/-! # Counted materialization of Laurent generator columns -/
namespace Decoupling.HighDim.LaurentLinearSolver
open ArithmeticCost Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type*} [Field K] {D B q n t : ℕ}

def fieldColumn {s t : ℕ} (W : FiniteLinearSolver.DenseMatrix K s t) (j : Fin t) : Vector K s :=
  Vector.ofFn fun i => W[i][j]

/-- Project each stored Gaussian coefficient column once, then transpose
only the already materialized array layout. -/
def projectColumns
    (W : FiniteLinearSolver.DenseMatrix K (q * PolynomialLinearSolver.boxSize (D + D) B) t)
    (pick : Fin n → Fin q) : Work K (LaurentArithmetic.DenseMatrix K D n t B) :=
  Work.bind (collect t (fun j => projectRows (fieldColumn W j) pick)) fun cols =>
    Work.pure (Vector.ofFn fun i => Vector.ofFn fun j => cols[j][i])

@[simp] theorem projectColumns_cost
    (W : FiniteLinearSolver.DenseMatrix K (q * PolynomialLinearSolver.boxSize (D + D) B) t)
    (pick : Fin n → Fin q) :
    (projectColumns W pick).cost =
      n * t * LaurentArithmetic.boxSize D B * PolynomialLinearSolver.boxSize (D + D) B := by
  simp [projectColumns]
  ring

theorem projectColumns_correct
    (W : FiniteLinearSolver.DenseMatrix K (q * PolynomialLinearSolver.boxSize (D + D) B) t)
    (pick : Fin n → Fin q) (i : Fin n) (j : Fin t) :
    LaurentArithmetic.denote (projectColumns W pick).value[i][j] =
      LaurentPresentation.indexedEvaluation
        (((PolynomialLinearSolver.denseCoordinates (K := K) (D + D) q B).symm
          (FiniteLinearSolver.vector (fieldColumn W j))) (pick i)).val := by
  simp only [projectColumns, Work.bind_value, Work.pure_value, Fin.getElem_fin,
    Vector.getElem_ofFn, collect_value_get_nat]
  exact projectRows_correct (D := D) (B := B) (q := q) (n := n) (fieldColumn W j) pick i

end Decoupling.HighDim.LaurentLinearSolver
