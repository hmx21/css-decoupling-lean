import Decoupling.HighDim.LaurentLinearSolverKernel
import Decoupling.HighDim.ArithmeticGrowth
import Decoupling.HighDim.LaurentArithmeticBounds

/-!
# HD012 a common polynomial growth bound for the actual Laurent routines

Dimension D is a fixed parameter. The bound is explicitly the evaluation
of a polynomial with natural coefficients. Input row count, column count
and exponent radius are bounded by s; all solver bounds below concern
the actual executed programs or their actual returned arrays.
-/
namespace Decoupling.HighDim.LaurentSolverGrowth
open ArithmeticGrowth LaurentLinearSolver

def degreeCap (D s : ℕ) := (2*D+2)*(s+1)
def radiusCap (D s : ℕ) := (4*(s+1)*((D+D)*degreeCap D s))^(2^(D+D))
def rowCap (D s : ℕ) := (s+1)*(degreeCap D s+radiusCap D s+1)^(D+D)
def columnCap (D s : ℕ) := (D+1)*(s+1)*(radiusCap D s+1)^(D+D)
def projectionCap (D s : ℕ) :=
  (s+1)*(columnCap D s+1)*LaurentArithmetic.boxSize D (radiusCap D s)*
    PolynomialLinearSolver.boxSize (D+D) (radiusCap D s)
def bound (D s : ℕ) :=
  (s+1)+degreeCap D s+radiusCap D s+rowCap D s+columnCap D s+1+
    8*(rowCap D s+columnCap D s+1)^4+projectionCap D s

def expression (D : ℕ) : Expression :=
  let s := Expression.add .input (.constant 1)
  let d := Expression.mul (.constant (2*D+2)) s
  let B := Expression.pow (.mul (.mul (.constant 4) s) (.mul (.constant (D+D)) d)) (2^(D+D))
  let row := Expression.mul s (.pow (.add (.add d B) (.constant 1)) (D+D))
  let col := Expression.mul (.mul (.constant (D+1)) s) (.pow (.add B (.constant 1)) (D+D))
  let proj := Expression.mul
    (.mul (.mul s (.add col (.constant 1)))
      (.pow (.add (.mul (.constant 2) B) (.constant 1)) D))
    (.pow (.add B (.constant 1)) (D+D))
  .add
    (.add (.add (.add (.add (.add (.add s d) B) row) col) (.constant 1))
      (.mul (.constant 8) (.pow (.add (.add row col) (.constant 1)) 4)))
    proj

theorem expression_eval (D s : ℕ) : (expression D).eval s = bound D s := rfl

noncomputable def polynomial (D : ℕ) : Polynomial ℕ := (expression D).polynomial

theorem polynomial_eval (D s : ℕ) : (polynomial D).eval s = bound D s :=
  (Expression.polynomial_eval _ _).trans (expression_eval D s)

theorem bound_monotone (D : ℕ) : Monotone (bound D) := by
  intro s t h
  rw [← expression_eval, ← expression_eval]
  exact (expression D).monotone h

theorem input_le_bound (D s : ℕ) : s ≤ bound D s := by unfold bound; omega
theorem radiusCap_le_bound (D s : ℕ) : radiusCap D s ≤ bound D s := by unfold bound; omega
theorem columnCap_le_bound (D s : ℕ) : columnCap D s ≤ bound D s := by unfold bound; omega
theorem projectionCap_le_bound (D s : ℕ) : projectionCap D s ≤ bound D s := by unfold bound; omega

theorem inputDegree_le {D h s : ℕ} (hh : h ≤ s) : inputDegree D h ≤ degreeCap D s := by
  unfold inputDegree degreeCap
  apply max_le <;> nlinarith

theorem outputBox_le {D m h s : ℕ} (hm : m ≤ s) (hh : h ≤ s) :
    outputBox D m h ≤ radiusCap D s := by
  unfold outputBox PolynomialLinearSolver.completeCutoff radiusCap
  apply Nat.pow_le_pow_left
  apply Nat.mul_le_mul
  · omega
  · exact Nat.mul_le_mul_left _ (inputDegree_le hh)

theorem unknowns_le {D m n s : ℕ} (hm : m ≤ s) (hn : n ≤ s) :
    n+m*D ≤ (D+1)*(s+1) := by nlinarith

theorem field_columns_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    (n+m*D)*(outputBox D m h+1)^(D+D) ≤ columnCap D s := by
  exact Nat.mul_le_mul (unknowns_le hm hn)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (outputBox_le hm hh) 1) _)

theorem field_rows_le {D m h s : ℕ} (hm : m ≤ s) (hh : h ≤ s) :
    m*(inputDegree D h+outputBox D m h+1)^(D+D) ≤ rowCap D s := by
  exact Nat.mul_le_mul (by omega)
    (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.add_le_add (inputDegree_le hh) (outputBox_le hm hh)) 1) _)

theorem kernelCost_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    kernelCost D m n h ≤ bound D s := by
  have hb := outputBox_le (D := D) hm hh
  have hc := field_columns_le (D := D) hm hn hh
  have hr := field_rows_le (D := D) hm hh
  have hp : n*((n+m*D)*PolynomialLinearSolver.boxSize (D+D) (outputBox D m h)) *
      LaurentArithmetic.boxSize D (outputBox D m h) *
        PolynomialLinearSolver.boxSize (D+D) (outputBox D m h) ≤ projectionCap D s := by
    unfold projectionCap
    apply Nat.mul_le_mul
    · apply Nat.mul_le_mul
      · exact Nat.mul_le_mul (by omega) (hc.trans (Nat.le_succ _))
      · exact LaurentArithmetic.boxSize_mono hb
    · exact Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) _
  have hg : 8*(m*(inputDegree D h+outputBox D m h+1)^(D+D) +
      (n+m*D)*(outputBox D m h+1)^(D+D)+1)^4 ≤
      8*(rowCap D s+columnCap D s+1)^4 :=
    Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.add_le_add hr hc) 1) 4)
  unfold kernelCost bound
  omega

theorem solveCost_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    solveCost D m n h ≤ bound D s := by
  have hb := outputBox_le (D := D) hm hh
  have hc := field_columns_le (D := D) hm hn hh
  have hr := field_rows_le (D := D) hm hh
  have hp : n*LaurentArithmetic.boxSize D (outputBox D m h) *
      PolynomialLinearSolver.boxSize (D+D) (outputBox D m h) ≤ projectionCap D s := by
    unfold projectionCap
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul (by nlinarith [Nat.zero_le ((s+1)*columnCap D s)])
        (LaurentArithmetic.boxSize_mono hb)
    · exact Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) _
  have hg : 8*(m*(inputDegree D h+outputBox D m h+1)^(D+D) +
      (n+m*D)*(outputBox D m h+1)^(D+D)+1)^4 ≤
      8*(rowCap D s+columnCap D s+1)^4 :=
    Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.add_le_add hr hc) 1) 4)
  unfold solveCost bound
  omega

variable {K : Type*} [Field K] [DecidableEq K] {D m n h s : ℕ}

theorem kernel_cost_polynomial (A : LaurentArithmetic.DenseMatrix K D m n h)
    (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    (kernel A).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (kernel_cost A).trans (kernelCost_le hm hn hh)

theorem solve_cost_polynomial (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m)
    (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    (solve A v).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (solve_cost A v).trans (solveCost_le hm hn hh)

theorem kernel_count_polynomial (A : LaurentArithmetic.DenseMatrix K D m n h)
    (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    (kernel A).value.count ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (kernel_number_le A).trans ((field_columns_le hm hn hh).trans (columnCap_le_bound D s))

end Decoupling.HighDim.LaurentSolverGrowth
