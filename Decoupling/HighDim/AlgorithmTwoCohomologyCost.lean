import Decoupling.HighDim.AlgorithmTwoCohomologyCorrectness

/-!
# HD012 actual operation count of the cohomology computation

The bounds use only the ranks and exponent radius of the supplied
differentials. The intermediate generator counts are bounded by the
proved Laurent-kernel algorithm; none is an input cost certificate.
-/
namespace Decoupling.HighDim.AlgorithmTwoCohomology
open ArithmeticCost LaurentArithmetic LaurentLinearSolver
variable {K : Type} [Field K] [DecidableEq K] {D q m r h B B' g t : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem finish_cost (W : DenseMatrix K D q g B) (V : DenseMatrix K D (g + m) t B') :
    (finish W V).cost ≤ g * t * boxSize D B' + 8 * (t + g + 1) ^ 4 := by
  unfold finish
  rw [Work.bind_cost, matrixAugmentationProgram_cost, Work.bind_cost, Work.pure_cost, add_zero]
  exact Nat.add_le_add_left (FiniteLinearSolver.quotientData_cost _) _

def cycleCount (D r q h : ℕ) : ℕ := (q + r * D) * (outputBox D r h + 1) ^ (D + D)
def relationRadius (D r h : ℕ) : ℕ := max (outputBox D r h) h
def relationCount (D q m r h : ℕ) : ℕ :=
  (cycleCount D r q h + m + q * D) *
    (outputBox D q (relationRadius D r h) + 1) ^ (D + D)

def costBound (D q m r h : ℕ) : ℕ :=
  kernelCost D r q h + q * m * boxSize D (relationRadius D r h) +
    kernelCost D q (cycleCount D r q h + m) (relationRadius D r h) +
      cycleCount D r q h * relationCount D q m r h *
        boxSize D (outputBox D q (relationRadius D r h)) +
          8 * (relationCount D q m r h + cycleCount D r q h + 1) ^ 4

theorem kernelCost_mono_columns (D m h : ℕ) {n n' : ℕ} (hn : n ≤ n') :
    kernelCost D m n h ≤ kernelCost D m n' h := by
  unfold kernelCost
  gcongr

theorem compute_cost (b : DenseMatrix K D q m h) (d : DenseMatrix K D r q h) :
    (compute b d).cost ≤ costBound D q m r h := by
  let W := (kernel d).value
  let R := (relationInput b W.coefficients).value
  let V := (kernel R).value
  have hg : W.count ≤ cycleCount D r q h := kernel_number_le d
  have ht : V.count ≤ relationCount D q m r h := by
    exact (kernel_number_le R).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.add_le_add_right hg m) (q * D)))
  have hk₁ : (kernel d).cost ≤ kernelCost D r q h := kernel_cost d
  have hk₂ : (kernel R).cost ≤
      kernelCost D q (cycleCount D r q h + m) (relationRadius D r h) :=
    (kernel_cost R).trans (kernelCost_mono_columns D q _ (Nat.add_le_add_right hg m))
  have hf : (finish W.coefficients V.coefficients).cost ≤
      cycleCount D r q h * relationCount D q m r h *
        boxSize D (outputBox D q (relationRadius D r h)) +
          8 * (relationCount D q m r h + cycleCount D r q h + 1) ^ 4 := by
    apply (finish_cost W.coefficients V.coefficients).trans
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul hg ht))
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left
        (Nat.add_le_add_right (Nat.add_le_add ht hg) 1) 4))
  simp only [compute, Work.bind_cost]
  change (kernel d).cost + ((relationInput b W.coefficients).cost +
    ((kernel R).cost + (finish W.coefficients V.coefficients).cost)) ≤ _
  rw [relationInput_cost]
  unfold costBound relationRadius at *
  omega

theorem compute_output_dimension (b : DenseMatrix K D q m h) (d : DenseMatrix K D r q h) :
    (compute b d).value.dimension ≤ cycleCount D r q h := by
  let W := (kernel d).value
  let V := (kernel (relationInput b W.coefficients).value).value
  let U₀ := (matrixAugmentationProgram (projectRelations V.coefficients)).value
  have hd := (FiniteLinearSolver.homogeneous_correct (FiniteLinearSolver.transposeDense U₀)).dimension_le
  exact hd.trans (kernel_number_le d)

end Decoupling.HighDim.AlgorithmTwoCohomology
