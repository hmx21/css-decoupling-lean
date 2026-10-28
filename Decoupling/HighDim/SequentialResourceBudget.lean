import Decoupling.HighDim.SequentialContractionGrowth
import Decoupling.HighDim.AlgorithmTwoLayersGrowth
import Decoupling.HighDim.AlgorithmTwoComparisonGrowth
import Decoupling.HighDim.AlgorithmTwoStableFreeGrowth
import Decoupling.HighDim.AlgorithmTwoInvertibleGrowth

/-!
# HD016 common polynomial for the descending-contraction pipeline

The numerical envelopes come from proved stage programs. This module
defines their finite composition, including the comparison solve, all descending cone solves, and
the complete native C4 recursion. Appendix C4 “Inverting Γ” and C5
“The lines of Algorithm 2” use the new contraction radius and trace here. Connecting the full execution trace
to these envelopes is a separate pipeline theorem, not an assumption
in this polynomial definition.
-/
namespace Decoupling.HighDim.SequentialResourceBudget
open Polynomial
noncomputable section

def layerPolynomial (D : ℕ) := AlgorithmTwoLayersGrowth.polynomial D
def comparisonPolynomial (D : ℕ) :=
  (AlgorithmTwoComparisonGrowth.polynomial D).comp (layerPolynomial D)
def conePolynomial (D L : ℕ) :=
  (SequentialContractionGrowth.conePolynomial D (2*(L+1)+1)).comp (comparisonPolynomial D)
def stablePolynomial (D L : ℕ) :=
  (AlgorithmTwoStableFreeGrowth.polynomial D L).comp (conePolynomial D L)
def liftPolynomial (D L : ℕ) :=
  (AlgorithmTwoInvertibleGrowth.polynomial D).comp (stablePolynomial D L)

def layer (D s : ℕ) := (layerPolynomial D).eval s
def comparison (D s : ℕ) := (comparisonPolynomial D).eval s
def cone (D L s : ℕ) := (conePolynomial D L).eval s
def stable (D L s : ℕ) := (stablePolynomial D L).eval s
def lift (D L s : ℕ) := (liftPolynomial D L).eval s

theorem layer_eq (D s : ℕ) : layer D s = AlgorithmTwoLayersGrowth.bound D s :=
  AlgorithmTwoLayersGrowth.polynomial_eval D s
theorem comparison_eq (D s : ℕ) :
    comparison D s = AlgorithmTwoComparisonGrowth.bound D (layer D s) := by
  rw [comparison,comparisonPolynomial,Polynomial.eval_comp,
    AlgorithmTwoComparisonGrowth.polynomial_eval]
  rfl
theorem cone_eq (D L s : ℕ) :
    cone D L s = SequentialContractionGrowth.coneBound D (2*(L+1)+1) (comparison D s) := by
  rw [cone,conePolynomial,Polynomial.eval_comp,SequentialContractionGrowth.conePolynomial_eval]
  rfl
theorem stable_eq (D L s : ℕ) :
    stable D L s = AlgorithmTwoStableFreeGrowth.bound D L (cone D L s) := by
  rw [stable,stablePolynomial,Polynomial.eval_comp]
  rfl
theorem lift_eq (D L s : ℕ) :
    lift D L s = AlgorithmTwoInvertibleGrowth.bound D (stable D L s) := by
  rw [lift,liftPolynomial,Polynomial.eval_comp,AlgorithmTwoInvertibleGrowth.polynomial_eval]
  rfl

theorem input_le_layer (D s : ℕ) : s ≤ layer D s := by
  rw [layer_eq]; exact AlgorithmTwoLayersGrowth.input_le_bound D s
theorem one_le_layer (D s : ℕ) : 1 ≤ layer D s := by
  rw [layer_eq]; exact AlgorithmTwoLayersGrowth.one_le_bound D s
theorem layer_le_comparison (D s : ℕ) : layer D s ≤ comparison D s := by
  rw [comparison_eq]; exact AlgorithmTwoComparisonGrowth.input_le_bound D _
theorem comparison_le_cone (D L s : ℕ) : comparison D s ≤ cone D L s := by
  rw [cone_eq]; exact SequentialContractionGrowth.input_le_coneBound D (2*(L+1)+1) _
theorem cone_le_stable (D L s : ℕ) : cone D L s ≤ stable D L s := by
  rw [stable_eq]; exact AlgorithmTwoStableFreeGrowth.input_le_bound D L _
theorem stable_le_lift (D L s : ℕ) : stable D L s ≤ lift D L s := by
  rw [lift_eq]; exact AlgorithmTwoInvertibleGrowth.input_le_bound D _

/-- One common bound includes the target's one field operation, the
whole execution trace, and (by enlargement) output depth and species.
The final factor two permits treating lift and circuit costs separately. -/
def polynomial (D L : ℕ) : Polynomial ℕ :=
  1+layerPolynomial D+comparisonPolynomial D+conePolynomial D L+
    stablePolynomial D L+2*liftPolynomial D L

def bound (D L s : ℕ) := (polynomial D L).eval s

theorem bound_eq (D L s : ℕ) :
    bound D L s = 1+layer D s+comparison D s+cone D L s+stable D L s+2*lift D L s := by
  simp only [bound,polynomial,Polynomial.eval_add,Polynomial.eval_one,
    Polynomial.eval_mul,Polynomial.eval_ofNat,layer,comparison,cone,stable,lift]

theorem lift_le_bound (D L s : ℕ) : lift D L s ≤ bound D L s := by rw [bound_eq]; omega
theorem bound_monotone (D L : ℕ) : Monotone (bound D L) :=
  ArithmeticGrowth.natPolynomial_monotone _

/-- Exact paper input conversion, with canonical complex bounds ±(D+2).
This polynomial depends on D alone, not on a code, field size,
particular solver output, or independently supplied stage count. -/
def paperPolynomial (D : ℕ) : Polynomial ℕ :=
  (polynomial D (D+2)).comp (C (2*(2*(D+2)+1)+1)*X)

theorem paperPolynomial_eval (D N : ℕ) :
    (paperPolynomial D).eval N = bound D (D+2) ((2*(2*(D+2)+1)+1)*N) := by
  rw [paperPolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  rfl

theorem paper_bound {D s N : ℕ} (hsize : s ≤ (2*(2*(D+2)+1)+1)*N) :
    bound D (D+2) s ≤ (paperPolynomial D).eval N := by
  rw [paperPolynomial_eval]
  exact bound_monotone D (D+2) hsize

end
end Decoupling.HighDim.SequentialResourceBudget
