import Decoupling.HighDim.SequentialContraction
import Decoupling.HighDim.SequentialContractionGrowth
import Decoupling.HighDim.AlgorithmTwoInvertibleLinear
import Decoupling.HighDim.AlgorithmTwoInvertibleRightSides

/-!
# Executable one-degree-at-a-time contraction

HD016, Appendix C4 “Inverting Γ up to homotopy”, C5 “The lines of
Algorithm 2”.  Each step executes the existing finite Laurent solver on
`d X = (1-H*d)|degree=k`, then copies its degree -1 component into the
stored homotopy.  Only the actual solver output is used.  Exactness and
freeness prove success; their proofs are erased at runtime.
-/
namespace Decoupling.HighDim.SequentialContraction
open Matrix ArithmeticCost AlgorithmTwoFiniteComplex LaurentArithmetic
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {D n h a b : ℕ}

/-- Copy just one column degree. Integer comparisons cost no field operations. -/
def selectColumns (degree : Vector ℤ n) (k : ℤ) (A : DenseMatrix K D n n a) :
    DenseMatrix K D n n a :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if degree.get j = k then A[i][j] else AlgorithmTwoLinearComparison.zeroDense

theorem selectColumns_correct (degree : Vector ℤ n) (k : ℤ) (A : DenseMatrix K D n n a) :
    matrixDenote (selectColumns degree k A) =
      fun i j => if degree.get j = k then matrixDenote A i j else 0 := by
  funext i j
  simp only [selectColumns, matrixDenote, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs <;> simp

/-- Coefficients in already solved degrees are copied, with no field additions. -/
def installArray (degree : Vector ℤ n) (k : ℤ) (H : DenseMatrix K D n n a)
    (X : DenseMatrix K D n n b) : DenseMatrix K D n n (max a b) :=
  let old := matrixPad H (max a b)
  let fresh := matrixPad X (max a b)
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if degree.get j = k then
      if degree.get i = k-1 then fresh[i][j] else AlgorithmTwoLinearComparison.zeroDense
    else old[i][j]

theorem installArray_correct (degree : Vector ℤ n) (k : ℤ) (H : DenseMatrix K D n n a)
    (X : DenseMatrix K D n n b) :
    matrixDenote (installArray degree k H X) = install degree k (matrixDenote H) (matrixDenote X) := by
  have ho := matrixPad_correct H (le_max_left a b)
  have hx := matrixPad_correct X (le_max_right a b)
  funext i j
  by_cases hj : degree.get j = k
  · by_cases hi : degree.get i = k-1
    · simpa [installArray, matrixDenote, install, component, hj, hi] using congrFun (congrFun hx i) j
    · simp [installArray, matrixDenote, install, component, hj, hi]
  · simpa [installArray, matrixDenote, install, component, hj] using congrFun (congrFun ho i) j

def rhsProgram (degree : Vector ℤ n) (k : ℤ)
    (d : DenseMatrix K D n n h) (H : DenseMatrix K D n n a) :
    Work K (DenseMatrix K D n n (a+h)) :=
  Work.bind (matrixMulProgram H d) fun product =>
    Work.bind (AlgorithmTwoInvertible.oneMinusProgram product) fun difference =>
      Work.pure (selectColumns degree k difference)

theorem rhsProgram_correct (degree : Vector ℤ n) (k : ℤ)
    (d : DenseMatrix K D n n h) (H : DenseMatrix K D n n a) :
    matrixDenote (rhsProgram degree k d H).value = rhs degree k (matrixDenote d) (matrixDenote H) := by
  change _ = fun i j => if degree.get j = k then (1 - matrixDenote H * matrixDenote d) i j else 0
  simp only [rhsProgram, Work.bind_value, Work.pure_value, selectColumns_correct,
    AlgorithmTwoInvertible.oneMinusProgram_correct, matrixMulProgram_correct]

theorem rhsProgram_cost (degree : Vector ℤ n) (k : ℤ)
    (d : DenseMatrix K D n n h) (H : DenseMatrix K D n n a) :
    (rhsProgram degree k d H).cost =
      n*n*n*boxSize D (a+h)*(2*boxSize D a+1)+2*n*n*boxSize D (a+h) := by
  simp only [rhsProgram, Work.bind_cost, Work.pure_cost, matrixMulProgram_cost,
    AlgorithmTwoInvertible.oneMinusProgram_cost, add_zero]

/-- Finite partial output together with the already verified degrees. -/
structure Partial (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ) (steps : ℕ) where
  matrix : DenseMatrix K D n n (SequentialContractionGrowth.outputRadius D n h steps)
  homogeneous : Homogeneous degree degree (-1) (matrixDenote matrix)
  above : Above degree (top-(steps:ℤ)) (matrixDenote d) (matrixDenote matrix)

variable [DecidableEq K]

omit [DecidableEq K] in
theorem step_solvable (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ)
    (steps : ℕ) (H : Partial degree d top steps)
    (hd : Homogeneous degree degree 1 (matrixDenote d))
    (hsq : matrixDenote d * matrixDenote d = 0) (hex : Exact (matrixDenote d)) :
    ∃ X, matrixDenote (matrixPad d (SequentialContractionGrowth.outputRadius D n h steps+h)) * X =
      matrixDenote (rhsProgram degree (top-(steps:ℤ)) d H.matrix).value := by
  rw [matrixPad_correct d (Nat.le_add_left _ _), rhsProgram_correct]
  exact rhs_solvable degree _ _ _ hd hsq hex H.above

/-- One real Laurent solve. The supplied assumptions are real differential
facts, later derived for the actual cone; no solver certificate is supplied. -/
def stepProgram (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ)
    (steps : ℕ) (H : Partial degree d top steps)
    (hd : Homogeneous degree degree 1 (matrixDenote d))
    (hsq : matrixDenote d * matrixDenote d = 0) (hex : Exact (matrixDenote d)) :
    Work K (Partial degree d top (steps+1)) :=
  let prepared := rhsProgram degree (top-(steps:ℤ)) d H.matrix
  let padded := matrixPad d (SequentialContractionGrowth.outputRadius D n h steps+h)
  let solved := AlgorithmTwoInvertible.solveOfExists padded prepared.value
    (step_solvable degree d top steps H hd hsq hex)
  have heq : matrixDenote d * matrixDenote solved.value =
      rhs degree (top-(steps:ℤ)) (matrixDenote d) (matrixDenote H.matrix) := by
    have he := AlgorithmTwoInvertible.solveOfExists_correct padded prepared.value
      (step_solvable degree d top steps H hd hsq hex)
    rw [matrixPad_correct d (Nat.le_add_left _ _), rhsProgram_correct] at he
    exact he
  { value :=
      { matrix := installArray degree (top-(steps:ℤ)) H.matrix solved.value
        homogeneous := by
          rw [installArray_correct]
          exact install_homogeneous degree _ _ _ H.homogeneous
        above := by
          rw [installArray_correct]
          have hh := install_above degree (top-(steps:ℤ)) _ _ _ hd H.homogeneous H.above heq
          have ht : top - ((steps+1:ℕ):ℤ) = (top-(steps:ℤ))-1 := by omega
          rw [ht]
          exact hh }
    trace := prepared.trace ++ solved.trace }

theorem stepProgram_cost (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ)
    (steps : ℕ) (H : Partial degree d top steps)
    (hd : Homogeneous degree degree 1 (matrixDenote d))
    (hsq : matrixDenote d * matrixDenote d = 0) (hex : Exact (matrixDenote d)) :
    (stepProgram degree d top steps H hd hsq hex).cost ≤
      SequentialContractionGrowth.stepCost D n h (SequentialContractionGrowth.outputRadius D n h steps) := by
  have hs := AlgorithmTwoInvertible.solveOfExists_cost
    (matrixPad d (SequentialContractionGrowth.outputRadius D n h steps+h))
    (rhsProgram degree (top-(steps:ℤ)) d H.matrix).value
    (step_solvable degree d top steps H hd hsq hex)
  simp only [stepProgram, Work.cost, List.length_append]
  change (rhsProgram degree (top-(steps:ℤ)) d H.matrix).cost +
    (AlgorithmTwoInvertible.solveOfExists
      (matrixPad d (SequentialContractionGrowth.outputRadius D n h steps+h))
      (rhsProgram degree (top-(steps:ℤ)) d H.matrix).value
      (step_solvable degree d top steps H hd hsq hex)).cost ≤ _
  rw [rhsProgram_cost]
  unfold SequentialContractionGrowth.stepCost
  omega

/-- Descend from top through `top-steps+1`, retaining sharing of all arrays. -/
def run (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ)
    (htop : ∀ j, degree.get j ≤ top)
    (hd : Homogeneous degree degree 1 (matrixDenote d))
    (hsq : matrixDenote d * matrixDenote d = 0) (hex : Exact (matrixDenote d)) :
    (steps : ℕ) → Work K (Partial degree d top steps)
  | 0 => Work.pure
      { matrix := AlgorithmTwoLinearComparison.zeroMatrix
        homogeneous := by rw [AlgorithmTwoLinearComparison.zeroMatrix_correct]; intro i j _; rfl
        above := by
          rw [AlgorithmTwoLinearComparison.zeroMatrix_correct]
          simpa using zero_above degree top (matrixDenote d) htop }
  | steps+1 => Work.bind (run degree d top htop hd hsq hex steps) fun H =>
      stepProgram degree d top steps H hd hsq hex

theorem run_cost (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ)
    (htop : ∀ j, degree.get j ≤ top)
    (hd : Homogeneous degree degree 1 (matrixDenote d))
    (hsq : matrixDenote d * matrixDenote d = 0) (hex : Exact (matrixDenote d)) (steps : ℕ) :
    (run degree d top htop hd hsq hex steps).cost ≤ SequentialContractionGrowth.totalCost D n h steps := by
  induction steps with
  | zero => simp [run, SequentialContractionGrowth.totalCost]
  | succ steps ih =>
      simp only [run, Work.bind_cost, SequentialContractionGrowth.totalCost]
      exact Nat.add_le_add ih (stepProgram_cost degree d top steps _ hd hsq hex)

/-- Complete output, including its actual degree -1 and contraction laws. -/
structure Output (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (steps : ℕ) where
  matrix : DenseMatrix K D n n (SequentialContractionGrowth.outputRadius D n h steps)
  homogeneous : Homogeneous degree degree (-1) (matrixDenote matrix)
  equation : matrixDenote d * matrixDenote matrix + matrixDenote matrix * matrixDenote d = 1

/-- Public finite-data contraction. Bounds and exactness are erased proofs;
its only numerical inputs are degree labels, coefficient arrays and steps. -/
def program (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ) (steps : ℕ)
    (htop : ∀ j, degree.get j ≤ top) (hbottom : ∀ j, top-(steps:ℤ) < degree.get j)
    (hd : Homogeneous degree degree 1 (matrixDenote d))
    (hsq : matrixDenote d * matrixDenote d = 0) (hex : Exact (matrixDenote d)) :
    Work K (Output degree d steps) :=
  Work.bind (run degree d top htop hd hsq hex steps) fun H =>
    Work.pure ⟨H.matrix,H.homogeneous,equation_of_above degree _ _ _ hbottom H.above⟩

theorem program_cost (degree : Vector ℤ n) (d : DenseMatrix K D n n h) (top : ℤ) (steps : ℕ)
    (htop : ∀ j, degree.get j ≤ top) (hbottom : ∀ j, top-(steps:ℤ) < degree.get j)
    (hd : Homogeneous degree degree 1 (matrixDenote d))
    (hsq : matrixDenote d * matrixDenote d = 0) (hex : Exact (matrixDenote d)) :
    (program degree d top steps htop hbottom hd hsq hex).cost ≤
      SequentialContractionGrowth.totalCost D n h steps := by
  simpa only [program, Work.bind_cost, Work.pure_cost, add_zero] using
    run_cost degree d top htop hd hsq hex steps

end Decoupling.HighDim.SequentialContraction
