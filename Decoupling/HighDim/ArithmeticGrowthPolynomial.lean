import Decoupling.HighDim.ArithmeticGrowth

/-! # Monotonicity of natural-coefficient resource polynomials -/
namespace Decoupling.HighDim.ArithmeticGrowth

theorem natPolynomial_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  intro s t h
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add]
      exact Nat.add_le_add hp hq
  | monomial n a =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left h n)

end Decoupling.HighDim.ArithmeticGrowth
