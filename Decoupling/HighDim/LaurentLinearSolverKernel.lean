import Decoupling.HighDim.LaurentLinearSolverProgram
import Decoupling.HighDim.LaurentLinearSolverKernelProjection

/-!
# Executable generators of the entire Laurent kernel

The returned dense columns are the actual Gaussian polynomial generators,
projected with all collision additions counted. The resulting range is the
whole Laurent kernel, not only the bounded vector-space kernel. The number
of columns is a generator count, not an assertion that the kernel is free.
-/

namespace Decoupling.HighDim.LaurentLinearSolver
open Matrix MvPolynomial ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type*} [Field K] [DecidableEq K] {D m n h : ℕ}

structure KernelData (K : Type*) (D n B : ℕ) where
  count : ℕ
  coefficients : LaurentArithmetic.DenseMatrix K D n count B

/-- Execute polynomial kernel computation and every Laurent projection sum. -/
def kernel (A : LaurentArithmetic.DenseMatrix K D m n h) :
    Work K (KernelData K D n (outputBox D m h)) :=
  Work.bind (compileMatrix A) fun A' =>
    Work.bind (PolynomialLinearSolver.kernelComplete (D + D) (inputDegree D h) A') fun s =>
      Work.bind (projectColumns s.kernel (leadingUnknown (D := D) (m := m) (n := n))) fun G =>
        Work.pure ⟨s.dimension, G⟩

/-- The actual native polynomial matrix whose columns are stored by Gaussian elimination. -/
noncomputable def nativePolynomialKernel
    (A : LaurentArithmetic.DenseMatrix K D m n h) :
    Matrix (Fin (n + m * D))
      (Fin (PolynomialLinearSolver.kernelComplete (D + D) (inputDegree D h) (compileMatrix A).value).value.dimension)
      (MvPolynomial (Fin (D + D)) K) :=
  fun i j => PolynomialLinearSolver.polynomialKernelVector (D + D) (inputDegree D h)
    (compileMatrix A).value j i

theorem nativePolynomialKernel_range (A : LaurentArithmetic.DenseMatrix K D m n h) :
    (nativePolynomialKernel A).mulVecLin.range =
      (LaurentPresentation.indexedMatrix (LaurentArithmetic.matrixDenote A)).mulVecLin.ker := by
  rw [Matrix.range_mulVecLin]
  have h := PolynomialLinearSolver.polynomialKernelVector_span (D + D) (inputDegree D h)
    (compileMatrix A).value
  rw [compileMatrix_correct] at h
  exact h

/-- Every projected array entry is the evaluation of the corresponding
actual stored polynomial generator, with original unknowns selected. -/
theorem kernel_denote (A : LaurentArithmetic.DenseMatrix K D m n h) :
    LaurentArithmetic.matrixDenote (kernel A).value.coefficients =
      LaurentPresentation.indexedProjectMatrix (nativePolynomialKernel A) := by
  funext i j
  change LaurentArithmetic.denote
    (projectColumns
      (PolynomialLinearSolver.kernelComplete (D + D) (inputDegree D h) (compileMatrix A).value).value.kernel
      (leadingUnknown (D := D) (m := m) (n := n))).value[i][j] = _
  refine (projectColumns_correct (D := D) (B := outputBox D m h) (q := n + m * D) (n := n)
    (PolynomialLinearSolver.kernelComplete (D + D) (inputDegree D h) (compileMatrix A).value).value.kernel
    (leadingUnknown (D := D) (m := m) (n := n)) i j).trans ?_
  have he : FiniteLinearSolver.vector (fieldColumn
        (PolynomialLinearSolver.kernelComplete (D + D) (inputDegree D h) (compileMatrix A).value).value.kernel j) =
      FiniteLinearSolver.kernelVector
        (PolynomialLinearSolver.assemble (D + D) (inputDegree D h) (outputBox D m h) (compileMatrix A).value) j := by
    funext k
    simp [fieldColumn, FiniteLinearSolver.vector, FiniteLinearSolver.kernelVector,
      PolynomialLinearSolver.kernelComplete, PolynomialLinearSolver.kernelBounded]
  rw [he]
  rfl

/-- Completeness for the full native Laurent-module kernel. -/
theorem kernel_correct (A : LaurentArithmetic.DenseMatrix K D m n h) :
    (LaurentArithmetic.matrixDenote (kernel A).value.coefficients).mulVecLin.range =
      (LaurentArithmetic.matrixDenote A).mulVecLin.ker := by
  rw [kernel_denote]
  exact LaurentPresentation.indexed_projected_kernel _ _ (nativePolynomialKernel_range A)

theorem kernel_number_le (A : LaurentArithmetic.DenseMatrix K D m n h) :
    (kernel A).value.count ≤ (n + m * D) * (outputBox D m h + 1) ^ (D + D) :=
  PolynomialLinearSolver.kernelComplete_number_le (D + D) (inputDegree D h) (compileMatrix A).value

/-- The individual coefficient-box bound survives the actual projection,
without replacing B by the larger total-degree bound (2D)*B. -/
theorem kernel_supported (A : LaurentArithmetic.DenseMatrix K D m n h) :
    LaurentBoxes.MatrixSupported (LaurentArithmetic.matrixDenote (kernel A).value.coefficients)
      (outputBox D m h) := LaurentArithmetic.matrixDenote_supported _

def kernelCost (D m n h : ℕ) : ℕ :=
  1 + 8 * (m * (inputDegree D h + outputBox D m h + 1) ^ (D + D) +
    (n + m * D) * (outputBox D m h + 1) ^ (D + D) + 1) ^ 4 +
      n * ((n + m * D) * PolynomialLinearSolver.boxSize (D + D) (outputBox D m h)) *
        LaurentArithmetic.boxSize D (outputBox D m h) *
          PolynomialLinearSolver.boxSize (D + D) (outputBox D m h)

theorem kernel_cost (A : LaurentArithmetic.DenseMatrix K D m n h) :
    (kernel A).cost ≤ kernelCost D m n h := by
  have hc := PolynomialLinearSolver.kernelComplete_cost (D + D) (inputDegree D h) (compileMatrix A).value
  have hn := PolynomialLinearSolver.kernelComplete_number_le (D + D) (inputDegree D h) (compileMatrix A).value
  have hp := Nat.mul_le_mul_right
    (PolynomialLinearSolver.boxSize (D + D) (outputBox D m h))
    (Nat.mul_le_mul_right (LaurentArithmetic.boxSize D (outputBox D m h))
      (Nat.mul_le_mul_left n hn))
  unfold kernel
  rw [Work.bind_cost, compileMatrix_cost, Work.bind_cost, Work.bind_cost,
    Work.pure_cost, add_zero, projectColumns_cost]
  dsimp only [kernelCost, outputBox, PolynomialLinearSolver.boxSize] at *
  omega

/-- Explicit coefficient-array output-size bound for the generated columns. -/
theorem kernel_output_size (A : LaurentArithmetic.DenseMatrix K D m n h) :
    n * (kernel A).value.count * LaurentArithmetic.boxSize D (outputBox D m h) ≤
      n * ((n + m * D) * (outputBox D m h + 1) ^ (D + D)) *
        LaurentArithmetic.boxSize D (outputBox D m h) :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left n (kernel_number_le A))

end Decoupling.HighDim.LaurentLinearSolver
