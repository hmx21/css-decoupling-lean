import Decoupling.HighDim.LaurentSolverGrowth
import Decoupling.HighDim.AlgorithmTwoLinearComparisonConeOutput

/-!
# Polynomial resources for the actual comparison and cone solvers

The spatial dimension is fixed. The scalar equation counts, compiler
arithmetic, Laurent solve, signed cone assembly, and extracted negative
block are all bounded from their actual formulas. No cost certificate
is a hypothesis.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparisonGrowth
open ArithmeticGrowth ArithmeticCost AlgorithmTwoLinearComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def argumentCap (s : ℕ) : ℕ := 2 * (s + 1)
def scalarCap (s : ℕ) : ℕ := 4 * (argumentCap s + 1) ^ 2
def solverCap (D s : ℕ) : ℕ := LaurentSolverGrowth.bound D (scalarCap s)
def compileCap (D s : ℕ) : ℕ := scalarCap s * scalarCap s * LaurentArithmetic.boxSize D (scalarCap s)
def outputCap (D s : ℕ) : ℕ := scalarCap s * scalarCap s * LaurentArithmetic.boxSize D (solverCap D s)
def bound (D s : ℕ) : ℕ :=
  (s + 1) + scalarCap s + solverCap D s + 2 * compileCap D s + 3 * outputCap D s

def scalarExpression : Expression :=
  .mul (.constant 4) (.pow (.add (.mul (.constant 2) (.add .input (.constant 1))) (.constant 1)) 2)

def expression (D : ℕ) : Expression :=
  let E := scalarExpression
  let L := (LaurentSolverGrowth.expression D).substitute E
  let boxE := Expression.pow (.add (.mul (.constant 2) E) (.constant 1)) D
  let boxL := Expression.pow (.add (.mul (.constant 2) L) (.constant 1)) D
  .add
    (.add (.add (.add (.input) (.constant 1)) E) L)
    (.add (.mul (.constant 2) (.mul (.mul E E) boxE))
      (.mul (.constant 3) (.mul (.mul E E) boxL)))

theorem scalarExpression_eval (s : ℕ) : scalarExpression.eval s = scalarCap s := rfl

theorem expression_eval (D s : ℕ) : (expression D).eval s = bound D s := by
  simp only [expression, Expression.eval, Expression.substitute_eval,
    LaurentSolverGrowth.expression_eval, scalarExpression_eval]
  change (s + 1 + scalarCap s + solverCap D s) + (2 * compileCap D s + 3 * outputCap D s) = _
  unfold bound
  omega

noncomputable def polynomial (D : ℕ) : Polynomial ℕ := (expression D).polynomial

theorem polynomial_eval (D s : ℕ) : (polynomial D).eval s = bound D s :=
  (Expression.polynomial_eval _ _).trans (expression_eval D s)

theorem bound_monotone (D : ℕ) : Monotone (bound D) := by
  intro s t h
  rw [← expression_eval, ← expression_eval]
  exact (expression D).monotone h

theorem one_le_bound (D s : ℕ) : 1 ≤ bound D s := by unfold bound; omega
theorem successor_le_bound (D s : ℕ) : s + 1 ≤ bound D s := by unfold bound; omega

theorem input_le_bound (D s : ℕ) : s ≤ bound D s := by unfold bound; omega
theorem scalarCap_le_bound (D s : ℕ) : scalarCap s ≤ bound D s := by unfold bound; omega
theorem solverCap_le_bound (D s : ℕ) : solverCap D s ≤ bound D s := by unfold bound; omega
theorem outputCap_le_bound (D s : ℕ) : outputCap D s ≤ bound D s := by unfold bound; omega

theorem input_le_argumentCap (s : ℕ) : s ≤ argumentCap s := by unfold argumentCap; omega

theorem argumentCap_le_scalarCap (s : ℕ) : argumentCap s ≤ scalarCap s := by
  unfold scalarCap
  nlinarith [Nat.zero_le (argumentCap s)]

theorem input_le_scalarCap (s : ℕ) : s ≤ scalarCap s :=
  (input_le_argumentCap s).trans (argumentCap_le_scalarCap s)

theorem scalarCap_le_solverCap (D s : ℕ) : scalarCap s ≤ solverCap D s :=
  LaurentSolverGrowth.input_le_bound D _

theorem system_dimensions {n m k s : ℕ}
    (hn : n ≤ argumentCap s) (hm : m ≤ argumentCap s) (hk : k ≤ argumentCap s) :
    equationCount n m k ≤ scalarCap s ∧ n * m ≤ scalarCap s := by
  have hnm := Nat.mul_le_mul hn hm
  have hnk := Nat.mul_le_mul hn hk
  unfold equationCount scalarCap
  constructor <;> nlinarith [Nat.zero_le (argumentCap s)]

theorem resultBox_le_solverCap {D n m k h s : ℕ}
    (hn : n ≤ argumentCap s) (hm : m ≤ argumentCap s) (hk : k ≤ argumentCap s)
    (hh : h ≤ argumentCap s) : resultBox D n m k h ≤ solverCap D s :=
  (LaurentSolverGrowth.outputBox_le (system_dimensions hn hm hk).1
    (hh.trans (argumentCap_le_scalarCap s))).trans (LaurentSolverGrowth.radiusCap_le_bound D _)

theorem rawCost_le {D n m k h s : ℕ}
    (hn : n ≤ argumentCap s) (hm : m ≤ argumentCap s) (hk : k ≤ argumentCap s)
    (hh : h ≤ argumentCap s) : costBound D n m k h ≤ compileCap D s + solverCap D s := by
  have hr := (system_dimensions hn hm hk).1
  have hc := (system_dimensions hn hm hk).2
  have hb := hh.trans (argumentCap_le_scalarCap s)
  have hcompile : equationCount n m k * (n*m) * LaurentArithmetic.boxSize D h ≤ compileCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hr hc) (LaurentArithmetic.boxSize_mono hb)
  have hsolve := LaurentSolverGrowth.solveCost_le (D := D) hr hc hb
  exact Nat.add_le_add hcompile hsolve

theorem square_input_cost_le {D n h s : ℕ} (hn : n ≤ argumentCap s) (hh : h ≤ argumentCap s) :
    n*n*LaurentArithmetic.boxSize D h ≤ compileCap D s := by
  have hn' := hn.trans (argumentCap_le_scalarCap s)
  exact Nat.mul_le_mul (Nat.mul_le_mul hn' hn')
    (LaurentArithmetic.boxSize_mono (hh.trans (argumentCap_le_scalarCap s)))

theorem resultBox_le {D n m k h s : ℕ}
    (hn : n ≤ s) (hm : m ≤ s) (hk : k ≤ s) (hh : h ≤ s) :
    resultBox D n m k h ≤ bound D s :=
  (resultBox_le_solverCap (hn.trans (input_le_argumentCap s)) (hm.trans (input_le_argumentCap s))
    (hk.trans (input_le_argumentCap s)) (hh.trans (input_le_argumentCap s))).trans (solverCap_le_bound D s)

theorem comparisonCost_le {D n m k h s : ℕ}
    (hn : n ≤ s) (hm : m ≤ s) (hk : k ≤ s) (hh : h ≤ s) :
    m*m*LaurentArithmetic.boxSize D h + costBound D n m k h ≤ bound D s := by
  have h₁ := square_input_cost_le (D := D) (hm.trans (input_le_argumentCap s))
    (hh.trans (input_le_argumentCap s))
  have h₂ := rawCost_le (D := D) (hn.trans (input_le_argumentCap s)) (hm.trans (input_le_argumentCap s))
    (hk.trans (input_le_argumentCap s)) (hh.trans (input_le_argumentCap s))
  unfold bound
  omega

theorem cone_resultBox_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    resultBox D (m+n) (m+n) 0 h ≤ bound D s := by
  have hmn : m+n ≤ argumentCap s := by unfold argumentCap; omega
  exact (resultBox_le_solverCap (D := D) hmn hmn (Nat.zero_le _) (hh.trans (input_le_argumentCap s))).trans
    (solverCap_le_bound D s)

theorem coneCost_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    m*m*LaurentArithmetic.boxSize D h + costBound D (m+n) (m+n) 0 h +
      n*n*LaurentArithmetic.boxSize D (resultBox D (m+n) (m+n) 0 h) ≤ bound D s := by
  have hmn : m+n ≤ argumentCap s := by unfold argumentCap; omega
  have h₁ := square_input_cost_le (D := D) (hm.trans (input_le_argumentCap s))
    (hh.trans (input_le_argumentCap s))
  have h₂ := rawCost_le (D := D) hmn hmn (Nat.zero_le _) (hh.trans (input_le_argumentCap s))
  have hbox := resultBox_le_solverCap (D := D) hmn hmn (Nat.zero_le _) (hh.trans (input_le_argumentCap s))
  have hn' := hn.trans (input_le_scalarCap s)
  have h₃ : n*n*LaurentArithmetic.boxSize D (resultBox D (m+n) (m+n) 0 h) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hn' hn') (LaurentArithmetic.boxSize_mono hbox)
  unfold bound
  omega

theorem output_size_le {D n m k h s : ℕ}
    (hn : n ≤ argumentCap s) (hm : m ≤ argumentCap s) (hk : k ≤ argumentCap s)
    (hh : h ≤ argumentCap s) :
    n*m*LaurentArithmetic.boxSize D (resultBox D n m k h) ≤ bound D s := by
  have hn' := hn.trans (argumentCap_le_scalarCap s)
  have hm' := hm.trans (argumentCap_le_scalarCap s)
  apply (le_trans _ (outputCap_le_bound D s))
  exact Nat.mul_le_mul (Nat.mul_le_mul hn' hm')
    (LaurentArithmetic.boxSize_mono (resultBox_le_solverCap hn hm hk hh))

theorem coneTermRank_le {D m n s : ℕ} (hm : m ≤ s) (hn : n ≤ s) :
    m+n ≤ bound D s := by
  have hmn : m+n ≤ argumentCap s := by unfold argumentCap; omega
  exact hmn.trans ((argumentCap_le_scalarCap s).trans (scalarCap_le_bound D s))

theorem cone_output_size_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    (m*n+m*m+n*n)*LaurentArithmetic.boxSize D (resultBox D (m+n) (m+n) 0 h) ≤ bound D s := by
  have hmn : m+n ≤ argumentCap s := by unfold argumentCap; omega
  have hb := LaurentArithmetic.boxSize_mono (D := D)
    (resultBox_le_solverCap (D := D) hmn hmn (Nat.zero_le _) (hh.trans (input_le_argumentCap s)))
  have hm' := hm.trans (input_le_scalarCap s)
  have hn' := hn.trans (input_le_scalarCap s)
  have h₁ : m*n*LaurentArithmetic.boxSize D (resultBox D (m+n) (m+n) 0 h) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hm' hn') hb
  have h₂ : m*m*LaurentArithmetic.boxSize D (resultBox D (m+n) (m+n) 0 h) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hm' hm') hb
  have h₃ : n*n*LaurentArithmetic.boxSize D (resultBox D (m+n) (m+n) 0 h) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hn' hn') hb
  simp only [Nat.add_mul]
  unfold bound
  omega

end Decoupling.HighDim.AlgorithmTwoComparisonGrowth
