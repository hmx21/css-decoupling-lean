import Decoupling.HighDim.AlgorithmTwoInvertibleGrowth

/-!
# HD016 explicit resources for descending cone contraction

Appendix C4, “Inverting Γ up to homotopy”, and C5, “The lines of
Algorithm 2”.  A degree step multiplies the previously stored homotopy by
its differential, forms `1 - H*d`, solves a finite Laurent system, and
installs the new degree block by coefficient copying.  The right-side radius uses the *previous
output* radius.  The recurrences include a conservative reserve for assembly, although
the actual overwrite performs no field arithmetic. The program-to-bound
connection is proved separately.
-/
namespace Decoupling.HighDim.SequentialContractionGrowth
open ArithmeticGrowth LaurentArithmetic AlgorithmTwoInvertible
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

/-- Radius after adding one solved degree block to the stored matrix. -/
def nextRadius (D n h a : ℕ) : ℕ := max a (outputBox D n n (a+h))

/-- Multiplication, `1 - H*d`, one multi-right-side Laurent solve, and
a conservative assembly reserve. Grade selection, padding, and component
overwrite only copy coefficients; their actual field-operation cost is zero. -/
def stepCost (D n h a : ℕ) : ℕ :=
  n*n*n*boxSize D (a+h)*(2*boxSize D a+1) +
    2*n*n*boxSize D (a+h) +
    LaurentLinearSolver.solveCost D (n*n) (n*n) (a+h) +
    n*n*boxSize D (nextRadius D n h a)

/-- The radius of the zero initial homotopy is zero. -/
def outputRadius (D n h : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => nextRadius D n h (outputRadius D n h k)

/-- Sum of the conservative degree-step trace upper bounds. -/
def totalCost (D n h : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => totalCost D n h k + stepCost D n h (outputRadius D n h k)

/-- A deliberately conservative common envelope, already proved from the
same Laurent solver and matrix arithmetic formulas. -/
def stepBound (D s : ℕ) : ℕ := AlgorithmTwoInvertibleGrowth.bound D s

noncomputable def stepPolynomial (D : ℕ) : Polynomial ℕ :=
  AlgorithmTwoInvertibleGrowth.polynomial D

theorem stepPolynomial_eval (D s : ℕ) : (stepPolynomial D).eval s = stepBound D s :=
  AlgorithmTwoInvertibleGrowth.polynomial_eval D s

theorem input_le_stepBound (D s : ℕ) : s ≤ stepBound D s :=
  AlgorithmTwoInvertibleGrowth.input_le_bound D s

theorem stepBound_monotone (D : ℕ) : Monotone (stepBound D) :=
  AlgorithmTwoInvertibleGrowth.bound_monotone D

theorem radius_le_stepBound {D n h a s : ℕ} (hn : n ≤ s) (hh : h ≤ s) (ha : a ≤ s) :
    nextRadius D n h a ≤ stepBound D s := by
  have hsum : a+h ≤ AlgorithmTwoInvertibleGrowth.scalarCap s := by
    have := AlgorithmTwoInvertibleGrowth.twice_input_le_scalarCap s
    omega
  have hsolve : outputBox D n n (a+h) ≤ AlgorithmTwoInvertibleGrowth.solverCap D s :=
    (LaurentSolverGrowth.outputBox_le
      (AlgorithmTwoInvertibleGrowth.product_le_scalarCap hn hn) hsum).trans
      (LaurentSolverGrowth.radiusCap_le_bound D _)
  exact max_le (ha.trans (input_le_stepBound D s))
    (hsolve.trans (AlgorithmTwoInvertibleGrowth.solverCap_le_bound D s))

theorem stepCost_le_stepBound {D n h a s : ℕ} (hn : n ≤ s) (hh : h ≤ s) (ha : a ≤ s) :
    stepCost D n h a ≤ stepBound D s := by
  let E := AlgorithmTwoInvertibleGrowth.scalarCap s
  let S := AlgorithmTwoInvertibleGrowth.solverCap D s
  have hnE : n ≤ E := hn.trans (AlgorithmTwoInvertibleGrowth.input_le_scalarCap s)
  have haE : a ≤ E := ha.trans (AlgorithmTwoInvertibleGrowth.input_le_scalarCap s)
  have hsum : a+h ≤ E := by
    have := AlgorithmTwoInvertibleGrowth.twice_input_le_scalarCap s
    dsimp [E]
    omega
  have hsolve : LaurentLinearSolver.solveCost D (n*n) (n*n) (a+h) ≤ S :=
    LaurentSolverGrowth.solveCost_le
      (AlgorithmTwoInvertibleGrowth.product_le_scalarCap hn hn)
      (AlgorithmTwoInvertibleGrowth.product_le_scalarCap hn hn) hsum
  have houtput : outputBox D n n (a+h) ≤ S :=
    (LaurentSolverGrowth.outputBox_le
      (AlgorithmTwoInvertibleGrowth.product_le_scalarCap hn hn) hsum).trans
      (LaurentSolverGrowth.radiusCap_le_bound D _)
  have haS : a ≤ S := haE.trans (AlgorithmTwoInvertibleGrowth.scalarCap_le_solverCap D s)
  have hr : nextRadius D n h a ≤ S := max_le haS houtput
  have hmul : n*n*n*boxSize D (a+h)*(2*boxSize D a+1) ≤
      (E*E*E)*boxSize D E*(2*boxSize D E+1) :=
    Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hnE hnE) hnE) (boxSize_mono hsum))
      (by have := boxSize_mono (D := D) haE; omega)
  have hsub : 2*n*n*boxSize D (a+h) ≤ 2*(E*E)*boxSize D E := by
    have hnn := Nat.mul_le_mul hnE hnE
    have hb := boxSize_mono (D := D) hsum
    nlinarith [Nat.mul_le_mul (Nat.mul_le_mul_left 2 hnn) hb]
  have hadd : n*n*boxSize D (nextRadius D n h a) ≤ AlgorithmTwoInvertibleGrowth.outputCap D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hnE hnE) (boxSize_mono hr)
  have hpre : n*n*n*boxSize D (a+h)*(2*boxSize D a+1) +
      2*n*n*boxSize D (a+h) ≤ AlgorithmTwoInvertibleGrowth.rhsCap D s := by
    unfold AlgorithmTwoInvertibleGrowth.rhsCap
    change _ ≤ 4*(E*E*E)*boxSize D E*(2*boxSize D E+1)+4*(E*E)*boxSize D E
    calc
      _ ≤ (E*E*E)*boxSize D E*(2*boxSize D E+1) + 2*(E*E)*boxSize D E := Nat.add_le_add hmul hsub
      _ = (E*E*E)*boxSize D E*(2*boxSize D E+1) + 2*((E*E)*boxSize D E) := by ring
      _ ≤ 4*((E*E*E)*boxSize D E*(2*boxSize D E+1)) + 4*((E*E)*boxSize D E) := by omega
      _ = _ := by ring
  unfold stepCost stepBound AlgorithmTwoInvertibleGrowth.bound
  dsimp [S] at hsolve
  omega

/-- Forward iteration: each stage budget is evaluated at the complete
previous budget, including its output radius. -/
def iteratedBound (D : ℕ) : ℕ → ℕ → ℕ
  | 0,s => s
  | k+1,s => stepBound D (iteratedBound D k s)

noncomputable def iteratedPolynomial (D : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | k+1 => (stepPolynomial D).comp (iteratedPolynomial D k)

theorem iteratedPolynomial_eval (D k s : ℕ) :
    (iteratedPolynomial D k).eval s = iteratedBound D k s := by
  induction k with
  | zero => simp [iteratedPolynomial,iteratedBound]
  | succ k ih => rw [iteratedPolynomial,Polynomial.eval_comp,ih,stepPolynomial_eval]; rfl

theorem iteratedBound_le_succ (D k s : ℕ) :
    iteratedBound D k s ≤ iteratedBound D (k+1) s :=
  input_le_stepBound D _

theorem input_le_iteratedBound (D k s : ℕ) : s ≤ iteratedBound D k s := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (iteratedBound_le_succ D k s)

theorem iteratedBound_monotone (D k : ℕ) : Monotone (iteratedBound D k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => exact (stepBound_monotone D).comp ih

theorem iteratedBound_monotone_steps (D s : ℕ) : Monotone (fun k => iteratedBound D k s) :=
  monotone_nat_of_le_succ (fun k => iteratedBound_le_succ D k s)

/-- No radius or cost hypothesis: the complete recursion is bounded from
only its fixed rank and initial differential radius. -/
theorem recursion_bounds {D n h s : ℕ} (hn : n ≤ s) (hh : h ≤ s) (k : ℕ) :
    outputRadius D n h k ≤ iteratedBound D k s ∧
      totalCost D n h k ≤ k*iteratedBound D k s := by
  induction k with
  | zero => simp [outputRadius,totalCost,iteratedBound]
  | succ k ih =>
      have hi := input_le_iteratedBound D k s
      have hr := radius_le_stepBound (D := D) (hn.trans hi) (hh.trans hi) ih.1
      have hc := stepCost_le_stepBound (D := D) (hn.trans hi) (hh.trans hi) ih.1
      have hm := iteratedBound_le_succ D k s
      refine ⟨hr, ?_⟩
      change totalCost D n h k + stepCost D n h (outputRadius D n h k) ≤
        (k+1)*stepBound D (iteratedBound D k s)
      change iteratedBound D k s ≤ stepBound D (iteratedBound D k s) at hm
      nlinarith [ih.2]

noncomputable def costPolynomial (D k : ℕ) : Polynomial ℕ :=
  Polynomial.C k * iteratedPolynomial D k

theorem costPolynomial_eval (D k s : ℕ) :
    (costPolynomial D k).eval s = k*iteratedBound D k s := by
  rw [costPolynomial,Polynomial.eval_mul,Polynomial.eval_C,iteratedPolynomial_eval]

theorem outputRadius_polynomial {D n h s : ℕ} (hn : n ≤ s) (hh : h ≤ s) (k : ℕ) :
    outputRadius D n h k ≤ (iteratedPolynomial D k).eval s := by
  rw [iteratedPolynomial_eval]
  exact (recursion_bounds hn hh k).1

theorem totalCost_polynomial {D n h s : ℕ} (hn : n ≤ s) (hh : h ≤ s) (k : ℕ) :
    totalCost D n h k ≤ (costPolynomial D k).eval s := by
  rw [costPolynomial_eval]
  exact (recursion_bounds hn hh k).2

/-- The cone rank is the sum of source and target ranks. -/
def coneBase (s : ℕ) : ℕ := 2*(s+1)

def coneIteration (D k s : ℕ) : ℕ := iteratedBound D k (coneBase s)

/-- Preparation, all descending solves, and extraction of the signed
homotopy block; the radius itself is included for downstream stages. -/
def coneBound (D k s : ℕ) : ℕ :=
  (s+1)+coneIteration D k s+s*s*boxSize D s+
    k*coneIteration D k s+s*s*boxSize D (coneIteration D k s)

noncomputable def conePolynomial (D k : ℕ) : Polynomial ℕ :=
  let B := (iteratedPolynomial D k).comp (2*(Polynomial.X+1))
  (Polynomial.X+1)+B+Polynomial.X*Polynomial.X*(2*Polynomial.X+1)^D+
    Polynomial.C k*B+Polynomial.X*Polynomial.X*(2*B+1)^D

theorem conePolynomial_eval (D k s : ℕ) :
    (conePolynomial D k).eval s = coneBound D k s := by
  simp only [conePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_C,
    Polynomial.eval_comp,iteratedPolynomial_eval]
  rfl

theorem input_le_coneBound (D k s : ℕ) : s ≤ coneBound D k s := by
  unfold coneBound
  omega

theorem coneIteration_le_coneBound (D k s : ℕ) : coneIteration D k s ≤ coneBound D k s := by
  unfold coneBound
  omega

theorem coneRadius_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) (k : ℕ) :
    outputRadius D (m+n) h k ≤ coneBound D k s := by
  have hmn : m+n ≤ coneBase s := by unfold coneBase; omega
  have hhs : h ≤ coneBase s := by unfold coneBase; omega
  exact (recursion_bounds hmn hhs k).1.trans (coneIteration_le_coneBound D k s)

theorem coneCost_le {D m n h s : ℕ} (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) (k : ℕ) :
    m*m*boxSize D h + totalCost D (m+n) h k +
      n*n*boxSize D (outputRadius D (m+n) h k) ≤ coneBound D k s := by
  have hmn : m+n ≤ coneBase s := by unfold coneBase; omega
  have hhs : h ≤ coneBase s := by unfold coneBase; omega
  have hrec := recursion_bounds (D := D) hmn hhs k
  have hp : m*m*boxSize D h ≤ s*s*boxSize D s :=
    Nat.mul_le_mul (Nat.mul_le_mul hm hm) (boxSize_mono hh)
  have he : n*n*boxSize D (outputRadius D (m+n) h k) ≤ s*s*boxSize D (coneIteration D k s) :=
    Nat.mul_le_mul (Nat.mul_le_mul hn hn) (boxSize_mono hrec.1)
  have hc : totalCost D (m+n) h k ≤ k*coneIteration D k s := hrec.2
  unfold coneBound
  omega

end Decoupling.HighDim.SequentialContractionGrowth
