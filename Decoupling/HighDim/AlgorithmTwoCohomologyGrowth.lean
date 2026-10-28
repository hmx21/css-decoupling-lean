import Decoupling.HighDim.AlgorithmTwoCohomologyCost
import Decoupling.HighDim.LaurentSolverGrowth

/-!
# HD012 polynomial growth of the executed cohomology algorithm

The two kernel computations, augmentation, and field quotient elimination
are bounded using their proved operation counts. The bound also controls
the actual output dimension and exponent radius. It has no solver or
cost-certificate hypothesis.
-/
namespace Decoupling.HighDim.AlgorithmTwoCohomologyGrowth
open ArithmeticGrowth AlgorithmTwoCohomology LaurentArithmetic LaurentLinearSolver

def first (D s : ℕ) := LaurentSolverGrowth.bound D s
def second (D s : ℕ) := LaurentSolverGrowth.bound D (2*first D s)
def bound (D s : ℕ) :=
  s+1+first D s+second D s+s*s*boxSize D (first D s)+
    first D s*second D s*boxSize D (second D s)+
      8*(second D s+first D s+1)^4

def expression (D : ℕ) : Expression :=
  let a := LaurentSolverGrowth.expression D
  let b := (LaurentSolverGrowth.expression D).substitute (.mul (.constant 2) a)
  let box (p : Expression) := Expression.pow (.add (.mul (.constant 2) p) (.constant 1)) D
  .add
    (.add
      (.add (.add (.add (.add .input (.constant 1)) a) b)
        (.mul (.mul .input .input) (box a)))
      (.mul (.mul a b) (box b)))
    (.mul (.constant 8) (.pow (.add (.add b a) (.constant 1)) 4))

theorem expression_eval (D s : ℕ) : (expression D).eval s = bound D s := by
  simp only [expression, Expression.eval, Expression.substitute_eval,
    LaurentSolverGrowth.expression_eval, bound, first, second, boxSize]

noncomputable def polynomial (D : ℕ) : Polynomial ℕ := (expression D).polynomial

theorem polynomial_eval (D s : ℕ) : (polynomial D).eval s = bound D s :=
  (Expression.polynomial_eval _ _).trans (expression_eval D s)

theorem bound_monotone (D : ℕ) : Monotone (bound D) := by
  intro s t h
  rw [← expression_eval, ← expression_eval]
  exact (expression D).monotone h

theorem input_le_first (D s : ℕ) : s ≤ first D s := LaurentSolverGrowth.input_le_bound D s
theorem first_le_second (D s : ℕ) : first D s ≤ second D s :=
  (by omega : first D s ≤ 2*first D s).trans (LaurentSolverGrowth.input_le_bound D _)
theorem input_le_bound (D s : ℕ) : s ≤ bound D s := by unfold bound; omega
theorem first_le_bound (D s : ℕ) : first D s ≤ bound D s := by unfold bound; omega
theorem second_le_bound (D s : ℕ) : second D s ≤ bound D s := by unfold bound; omega

theorem cycleCount_le {D r q h s : ℕ} (hr : r ≤ s) (hq : q ≤ s) (hh : h ≤ s) :
    cycleCount D r q h ≤ first D s :=
  (LaurentSolverGrowth.field_columns_le hr hq hh).trans
    (LaurentSolverGrowth.columnCap_le_bound D s)

theorem outputBox_le {D r h s : ℕ} (hr : r ≤ s) (hh : h ≤ s) :
    outputBox D r h ≤ first D s :=
  (LaurentSolverGrowth.outputBox_le hr hh).trans
    (LaurentSolverGrowth.radiusCap_le_bound D s)

theorem relationRadius_le {D r h s : ℕ} (hr : r ≤ s) (hh : h ≤ s) :
    relationRadius D r h ≤ first D s :=
  max_le (outputBox_le hr hh) (hh.trans (input_le_first D s))

theorem relationCount_le {D q m r h s : ℕ}
    (hq : q ≤ s) (hm : m ≤ s) (hr : r ≤ s) (hh : h ≤ s) :
    relationCount D q m r h ≤ second D s := by
  have hq' : q ≤ 2*first D s := (hq.trans (input_le_first D s)).trans (by omega)
  have hn : cycleCount D r q h+m ≤ 2*first D s := by
    have := cycleCount_le (D := D) hr hq hh
    have := hm.trans (input_le_first D s)
    omega
  have hh' : relationRadius D r h ≤ 2*first D s :=
    (relationRadius_le hr hh).trans (by omega)
  exact (LaurentSolverGrowth.field_columns_le hq' hn hh').trans
    (LaurentSolverGrowth.columnCap_le_bound D _)

theorem secondBox_le {D q r h s : ℕ}
    (hq : q ≤ s) (hr : r ≤ s) (hh : h ≤ s) :
    outputBox D q (relationRadius D r h) ≤ second D s := by
  apply (LaurentSolverGrowth.outputBox_le (s := 2*first D s) _ _).trans
    (LaurentSolverGrowth.radiusCap_le_bound D _)
  · exact (hq.trans (input_le_first D s)).trans (by omega)
  · exact (relationRadius_le hr hh).trans (by omega)

theorem costBound_le {D q m r h s : ℕ}
    (hq : q ≤ s) (hm : m ≤ s) (hr : r ≤ s) (hh : h ≤ s) :
    costBound D q m r h ≤ bound D s := by
  have hg := cycleCount_le (D := D) hr hq hh
  have ht := relationCount_le (D := D) hq hm hr hh
  have hb := relationRadius_le (D := D) hr hh
  have hb' := secondBox_le (D := D) hq hr hh
  have hk : kernelCost D r q h ≤ first D s :=
    LaurentSolverGrowth.kernelCost_le hr hq hh
  have hk' : kernelCost D q (cycleCount D r q h+m) (relationRadius D r h) ≤ second D s := by
    apply LaurentSolverGrowth.kernelCost_le (s := 2*first D s)
    · exact (hq.trans (input_le_first D s)).trans (by omega)
    · have := hm.trans (input_le_first D s)
      omega
    · omega
  have hn : q*m*boxSize D (relationRadius D r h) ≤ s*s*boxSize D (first D s) :=
    Nat.mul_le_mul (Nat.mul_le_mul hq hm) (boxSize_mono hb)
  have ha : cycleCount D r q h*relationCount D q m r h*
      boxSize D (outputBox D q (relationRadius D r h)) ≤
      first D s*second D s*boxSize D (second D s) :=
    Nat.mul_le_mul (Nat.mul_le_mul hg ht) (boxSize_mono hb')
  have hf : 8*(relationCount D q m r h+cycleCount D r q h+1)^4 ≤
      8*(second D s+first D s+1)^4 :=
    Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega) 4)
  unfold costBound bound
  omega

variable {K : Type} [Field K] [DecidableEq K] {D q m r h s : ℕ}

theorem compute_cost_polynomial (b : DenseMatrix K D q m h) (d : DenseMatrix K D r q h)
    (hq : q ≤ s) (hm : m ≤ s) (hr : r ≤ s) (hh : h ≤ s) :
    (compute b d).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (compute_cost b d).trans (costBound_le hq hm hr hh)

theorem compute_dimension_bound (b : DenseMatrix K D q m h) (d : DenseMatrix K D r q h)
    (hq : q ≤ s) (hr : r ≤ s) (hh : h ≤ s) :
    (compute b d).value.dimension ≤ bound D s :=
  (compute_output_dimension b d).trans ((cycleCount_le hr hq hh).trans (first_le_bound D s))

theorem compute_radius_bound (hq : r ≤ s) (hh : h ≤ s) :
    outputBox D r h ≤ bound D s :=
  (outputBox_le hq hh).trans (first_le_bound D s)

end Decoupling.HighDim.AlgorithmTwoCohomologyGrowth
