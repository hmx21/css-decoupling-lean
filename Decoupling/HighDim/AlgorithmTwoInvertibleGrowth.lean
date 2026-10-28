import Decoupling.HighDim.LaurentSolverGrowth
import Decoupling.HighDim.AlgorithmTwoInvertibleFromPresentation
import Decoupling.HighDim.DenseCircuitPermutationTheta

/-!
# Polynomial resources for four lift solves and the actual Theta circuit

The envelope follows the executed right-side products, all four scalar
Laurent solves, signed lift blocks, and compiled SUM/SWAP word. The only
asymptotically fixed parameter is the spatial dimension.
-/
namespace Decoupling.HighDim.AlgorithmTwoInvertibleGrowth
open ArithmeticGrowth ArithmeticCost AlgorithmTwoInvertible
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def scalarCap (s : ℕ) : ℕ := 4 * (s+1)^2
def solverCap (D s : ℕ) : ℕ := LaurentSolverGrowth.bound D (scalarCap s)
def inputCap (D s : ℕ) : ℕ := scalarCap s * scalarCap s * LaurentArithmetic.boxSize D (scalarCap s)
def outputCap (D s : ℕ) : ℕ := scalarCap s * scalarCap s * LaurentArithmetic.boxSize D (solverCap D s)
def rhsCap (D s : ℕ) : ℕ :=
  4 * (scalarCap s * scalarCap s * scalarCap s) * LaurentArithmetic.boxSize D (scalarCap s) *
    (2 * LaurentArithmetic.boxSize D (scalarCap s) + 1) +
  4 * (scalarCap s * scalarCap s) * LaurentArithmetic.boxSize D (scalarCap s)
def bound (D s : ℕ) : ℕ :=
  (s+1) + scalarCap s + solverCap D s + rhsCap D s + 4*solverCap D s +
    2*inputCap D s + 4*outputCap D s + 2*scalarCap s

def scalarExpression : Expression := .mul (.constant 4) (.pow (.add .input (.constant 1)) 2)
def expression (D : ℕ) : Expression :=
  let E := scalarExpression
  let L := (LaurentSolverGrowth.expression D).substitute E
  let square := Expression.mul E E
  let cube := Expression.mul square E
  let boxE := Expression.pow (.add (.mul (.constant 2) E) (.constant 1)) D
  let boxL := Expression.pow (.add (.mul (.constant 2) L) (.constant 1)) D
  let rhs := Expression.add
    (.mul (.mul (.mul (.constant 4) cube) boxE) (.add (.mul (.constant 2) boxE) (.constant 1)))
    (.mul (.mul (.constant 4) square) boxE)
  .add (.add (.add (.add (.add (.add (.add (.add .input (.constant 1)) E) L) rhs)
    (.mul (.constant 4) L)) (.mul (.constant 2) (.mul square boxE)))
    (.mul (.constant 4) (.mul square boxL))) (.mul (.constant 2) E)

theorem scalarExpression_eval (s : ℕ) : scalarExpression.eval s = scalarCap s := rfl

theorem expression_eval (D s : ℕ) : (expression D).eval s = bound D s := by
  simp only [expression, Expression.eval, Expression.substitute_eval,
    LaurentSolverGrowth.expression_eval, scalarExpression_eval]
  rfl

noncomputable def polynomial (D : ℕ) : Polynomial ℕ := (expression D).polynomial

theorem polynomial_eval (D s : ℕ) : (polynomial D).eval s = bound D s :=
  (Expression.polynomial_eval _ _).trans (expression_eval D s)

theorem bound_monotone (D : ℕ) : Monotone (bound D) := by
  intro s t h
  rw [← expression_eval, ← expression_eval]
  exact (expression D).monotone h

theorem successor_le_bound (D s : ℕ) : s+1 ≤ bound D s := by unfold bound; omega
theorem input_le_bound (D s : ℕ) : s ≤ bound D s := by unfold bound; omega
theorem one_le_bound (D s : ℕ) : 1 ≤ bound D s := by unfold bound; omega
theorem scalarCap_le_bound (D s : ℕ) : scalarCap s ≤ bound D s := by unfold bound; omega
theorem solverCap_le_bound (D s : ℕ) : solverCap D s ≤ bound D s := by unfold bound; omega
theorem outputCap_le_bound (D s : ℕ) : outputCap D s ≤ bound D s := by unfold bound; omega

theorem input_le_scalarCap (s : ℕ) : s ≤ scalarCap s := by unfold scalarCap; nlinarith
theorem twice_input_le_scalarCap (s : ℕ) : 2*s ≤ scalarCap s := by unfold scalarCap; nlinarith
theorem four_input_le_scalarCap (s : ℕ) : 4*s ≤ scalarCap s := by unfold scalarCap; nlinarith

theorem product_le_scalarCap {a b s : ℕ} (ha : a ≤ s) (hb : b ≤ s) : a*b ≤ scalarCap s := by
  have h := Nat.mul_le_mul ha hb
  unfold scalarCap
  nlinarith

theorem double_le_scalarCap {h s : ℕ} (hh : h ≤ s) : h+h ≤ scalarCap s := by
  have := twice_input_le_scalarCap s
  omega

theorem scalarCap_le_solverCap (D s : ℕ) : scalarCap s ≤ solverCap D s :=
  LaurentSolverGrowth.input_le_bound D _

theorem outputBox_le_solverCap {D m r h s : ℕ} (hm : m ≤ s) (hr : r ≤ s) (hh : h ≤ s) :
    outputBox D m r (h+h) ≤ solverCap D s :=
  (LaurentSolverGrowth.outputBox_le (product_le_scalarCap hm hr) (double_le_scalarCap hh)).trans
    (LaurentSolverGrowth.radiusCap_le_bound D _)

theorem multiCost_le {D m n r h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hr : r ≤ s) (hh : h ≤ s) :
    LaurentLinearSolver.solveCost D (m*r) (n*r) (h+h) ≤ solverCap D s :=
  LaurentSolverGrowth.solveCost_le (product_le_scalarCap hm hr) (product_le_scalarCap hn hr)
    (double_le_scalarCap hh)

theorem rightSidesCost_le {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    rightSidesCost D c0 c1 t0 t1 h ≤ rhsCap D s := by
  have hc0' := hc0.trans (input_le_scalarCap s)
  have hc1' := hc1.trans (input_le_scalarCap s)
  have ht0' := ht0.trans (input_le_scalarCap s)
  have ht1' := ht1.trans (input_le_scalarCap s)
  have h₁ := Nat.mul_le_mul (Nat.mul_le_mul hc1' ht0') ht1'
  have h₂ := Nat.mul_le_mul (Nat.mul_le_mul ht1' hc0') hc1'
  have h₃ := Nat.mul_le_mul (Nat.mul_le_mul hc1' hc1') ht1'
  have h₄ := Nat.mul_le_mul (Nat.mul_le_mul ht1' ht1') hc1'
  have hsum : c1*t0*t1+t1*c0*c1+c1*c1*t1+t1*t1*c1 ≤ 4*(scalarCap s*scalarCap s*scalarCap s) := by omega
  have hsquare : 2*(c1*c1+t1*t1) ≤ 4*(scalarCap s*scalarCap s) := by
    have := Nat.mul_le_mul hc1' hc1'
    have := Nat.mul_le_mul ht1' ht1'
    omega
  have hb := LaurentArithmetic.boxSize_mono (D := D) (hh.trans (input_le_scalarCap s))
  have hb₂ := LaurentArithmetic.boxSize_mono (D := D) (double_le_scalarCap hh)
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul hsum hb₂) (by omega))
    (Nat.mul_le_mul hsquare hb₂)

theorem fourCost_le {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    fourCost D c0 c1 t0 t1 h ≤ rhsCap D s + 4*solverCap D s := by
  have h₀ := rightSidesCost_le (D := D) hc0 hc1 ht0 ht1 hh
  have h₁ := multiCost_le (D := D) hc1 hc0 ht0 hh
  have h₂ := multiCost_le (D := D) ht1 ht0 hc0 hh
  have h₃ := multiCost_le (D := D) hc1 hc0 hc1 hh
  have h₄ := multiCost_le (D := D) ht1 ht0 ht1 hh
  unfold fourCost
  omega

theorem liftBox_le_solverCap {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    liftBox D c1 t0 t1 c0 h ≤ solverCap D s := by
  unfold liftBox
  exact max_le (hh.trans ((input_le_scalarCap s).trans (scalarCap_le_solverCap D s)))
    (max_le (outputBox_le_solverCap hc1 ht0 hh)
      (max_le (outputBox_le_solverCap ht1 hc0 hh)
        (max_le (outputBox_le_solverCap hc1 hc1 hh) (outputBox_le_solverCap ht1 ht1 hh))))

theorem liftBox_le {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    liftBox D c1 t0 t1 c0 h ≤ bound D s :=
  (liftBox_le_solverCap hc0 hc1 ht0 ht1 hh).trans (solverCap_le_bound D s)

theorem negCost_le {D a b h s : ℕ} (ha : a ≤ s) (hb : b ≤ s) (hh : h ≤ s) :
    a*b*LaurentArithmetic.boxSize D h ≤ inputCap D s :=
  Nat.mul_le_mul (Nat.mul_le_mul (ha.trans (input_le_scalarCap s)) (hb.trans (input_le_scalarCap s)))
    (LaurentArithmetic.boxSize_mono (hh.trans (input_le_scalarCap s)))

theorem liftMatricesCost_le {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    liftMatricesCost D c0 c1 t0 t1 h ≤ rhsCap D s + 4*solverCap D s + 2*inputCap D s := by
  have h₀ := fourCost_le (D := D) hc0 hc1 ht0 ht1 hh
  have h₁ := negCost_le (D := D) hc1 ht1 hh
  have h₂ := negCost_le (D := D) ht1 hc1 hh
  unfold liftMatricesCost
  omega

theorem output_size_le {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    (c0+t1)*(t0+c1)*LaurentArithmetic.boxSize D (liftBox D c1 t0 t1 c0 h) ≤ outputCap D s := by
  have hn : c0+t1 ≤ scalarCap s := by have := twice_input_le_scalarCap s; omega
  have hm : t0+c1 ≤ scalarCap s := by have := twice_input_le_scalarCap s; omega
  exact Nat.mul_le_mul (Nat.mul_le_mul hn hm)
    (LaurentArithmetic.boxSize_mono (liftBox_le_solverCap hc0 hc1 ht0 ht1 hh))

theorem physical_species_le {D c0 c1 t0 t1 s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) :
    (c0+t1)+(t0+c1) ≤ bound D s := by
  have := four_input_le_scalarCap s
  have := scalarCap_le_bound D s
  omega

theorem lift_arrays_size_le {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    ((c0+t1)*(t0+c1)+(t0+c1)*(c0+t1))*
      LaurentArithmetic.boxSize D (liftBox D c1 t0 t1 c0 h) ≤ bound D s := by
  have := output_size_le (D := D) hc0 hc1 ht0 ht1 hh
  rw [Nat.mul_comm (t0+c1) (c0+t1), Nat.add_mul]
  unfold bound
  omega

theorem four_output_size_le {D c0 c1 t0 t1 h s : ℕ}
    (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s) :
    c0*t0*LaurentArithmetic.boxSize D (outputBox D c1 t0 (h+h)) +
      t0*c0*LaurentArithmetic.boxSize D (outputBox D t1 c0 (h+h)) +
      c0*c1*LaurentArithmetic.boxSize D (outputBox D c1 c1 (h+h)) +
      t0*t1*LaurentArithmetic.boxSize D (outputBox D t1 t1 (h+h)) ≤ bound D s := by
  have hc0' := hc0.trans (input_le_scalarCap s)
  have hc1' := hc1.trans (input_le_scalarCap s)
  have ht0' := ht0.trans (input_le_scalarCap s)
  have ht1' := ht1.trans (input_le_scalarCap s)
  have h₁ : c0*t0*LaurentArithmetic.boxSize D (outputBox D c1 t0 (h+h)) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hc0' ht0') (LaurentArithmetic.boxSize_mono (outputBox_le_solverCap hc1 ht0 hh))
  have h₂ : t0*c0*LaurentArithmetic.boxSize D (outputBox D t1 c0 (h+h)) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul ht0' hc0') (LaurentArithmetic.boxSize_mono (outputBox_le_solverCap ht1 hc0 hh))
  have h₃ : c0*c1*LaurentArithmetic.boxSize D (outputBox D c1 c1 (h+h)) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hc0' hc1') (LaurentArithmetic.boxSize_mono (outputBox_le_solverCap hc1 hc1 hh))
  have h₄ : t0*t1*LaurentArithmetic.boxSize D (outputBox D t1 t1 (h+h)) ≤ outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul ht0' ht1') (LaurentArithmetic.boxSize_mono (outputBox_le_solverCap ht1 ht1 hh))
  unfold bound
  omega

end Decoupling.HighDim.AlgorithmTwoInvertibleGrowth
