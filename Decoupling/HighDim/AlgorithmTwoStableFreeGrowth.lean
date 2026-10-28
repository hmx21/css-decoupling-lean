import Decoupling.HighDim.StableFreeResourceCochainRanks
import Decoupling.HighDim.ArithmeticGrowthPolynomial

/-!
# HD012 a common envelope for the actual C4 cost, ranks, and radius

This sums the independently proved polynomial bounds. It is a
composition interface, not a new hypothesis about any intermediate
projective module or selected basis.
-/
namespace Decoupling.HighDim.AlgorithmTwoStableFreeGrowth
open StableFree.Resource Polynomial

noncomputable def polynomial (D l : ℕ) : Polynomial ℕ :=
  X+1+budgetPolynomial l+uniformCostPolynomial D l+uniformBoxPolynomial D l

noncomputable def bound (D l s : ℕ) := (polynomial D l).eval s

theorem bound_eq (D l s : ℕ) :
    bound D l s = s+1+(budgetPolynomial l).eval s+
      (uniformCostPolynomial D l).eval s+(uniformBoxPolynomial D l).eval s := by
  simp only [bound,polynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]

theorem bound_monotone (D l : ℕ) : Monotone (bound D l) :=
  ArithmeticGrowth.natPolynomial_monotone _

theorem input_le_bound (D l s : ℕ) : s ≤ bound D l s := by rw [bound_eq]; omega
theorem one_le_bound (D l s : ℕ) : 1 ≤ bound D l s := by rw [bound_eq]; omega
theorem budget_le_bound (D l s : ℕ) : (budgetPolynomial l).eval s ≤ bound D l s := by
  rw [bound_eq]; omega
theorem cost_le_bound (D l s : ℕ) : (uniformCostPolynomial D l).eval s ≤ bound D l s := by
  rw [bound_eq]; omega
theorem box_le_bound (D l s : ℕ) : (uniformBoxPolynomial D l).eval s ≤ bound D l s := by
  rw [bound_eq]; omega

end Decoupling.HighDim.AlgorithmTwoStableFreeGrowth
