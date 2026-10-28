import Decoupling.HighDim.LaurentLinearSolverCompile
import Decoupling.HighDim.LaurentLinearSolverProjection
import Decoupling.HighDim.PolynomialLinearSolverGenerators

/-!
# Complete executable Laurent equation solving with counted arithmetic

Input coefficients, Gaussian coefficients, and output Laurent coefficients
are actual dense arrays. The complete polynomial search is invoked only
after the proved exact presentation conversion. Projection executes all
collision sums. Failure is equivalent to actual Laurent nonsolvability.
-/

namespace Decoupling.HighDim.LaurentLinearSolver
open Matrix MvPolynomial ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type*} [Field K] [DecidableEq K] {D m n h : ℕ}

abbrev outputBox (D m h : ℕ) : ℕ :=
  PolynomialLinearSolver.completeCutoff (D + D) m (inputDegree D h)

def leadingUnknown : Fin n → Fin (n + m * D) :=
  fun i => unknownIndex (Sum.inl i)

/-- Execute the complete polynomial search, then materialize the projected
particular solution. The stored particular array is read directly. -/
def solve (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m) :
    Work K (Option (Vector (LaurentArithmetic.Dense K D (outputBox D m h)) n)) :=
  Work.bind (compileMatrix A) fun A' =>
    Work.bind (PolynomialLinearSolver.solveComplete (D + D) (inputDegree D h) A' (compileRhs v)) fun result =>
      match result with
      | none => Work.pure none
      | some s => Work.bind (projectRows s.particular (leadingUnknown (D := D) (m := m) (n := n)))
          (fun y => Work.pure (some y))

omit [DecidableEq K] in
theorem compiled_solvable_iff (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m) :
    (∃ z, PolynomialLinearSolver.denoteMatrix (compileMatrix A).value *ᵥ z =
      fun i => (PolynomialLinearSolver.denoteVector (compileRhs v) i).val) ↔
    ∃ y, LaurentArithmetic.matrixDenote A *ᵥ y = fun i => LaurentArithmetic.denote v[i] := by
  have hv : (fun i => (PolynomialLinearSolver.denoteVector (compileRhs v) i).val) =
      LaurentPresentation.indexedRhs (fun i => LaurentArithmetic.denote v[i]) :=
    funext (compileRhs_correct v)
  rw [compileMatrix_correct, hv]
  exact (LaurentPresentation.indexed_solvable_iff _ _).symm

/-- Failure is exactly unbounded Laurent nonsolvability, not just failure in a window. -/
theorem solve_none_iff (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m) :
    (solve A v).value = none ↔
      ¬ ∃ y, LaurentArithmetic.matrixDenote A *ᵥ y = fun i => LaurentArithmetic.denote v[i] := by
  have he : (solve A v).value = none ↔
      (PolynomialLinearSolver.solveComplete (D + D) (inputDegree D h)
        (compileMatrix A).value (compileRhs v)).value = none := by
    cases hz : (PolynomialLinearSolver.solveComplete (D + D) (inputDegree D h)
      (compileMatrix A).value (compileRhs v)).value <;> simp [solve, hz]
  rw [he, PolynomialLinearSolver.solveComplete_none_iff]
  exact not_congr (compiled_solvable_iff A v)

/-- Every returned materialized Laurent vector solves the original actual equation. -/
theorem solve_sound (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m)
    (y : Vector (LaurentArithmetic.Dense K D (outputBox D m h)) n)
    (hy : (solve A v).value = some y) :
    LaurentArithmetic.matrixDenote A *ᵥ (fun j => LaurentArithmetic.denote y[j]) =
      fun i => LaurentArithmetic.denote v[i] := by
  cases hz : (PolynomialLinearSolver.solveComplete (D + D) (inputDegree D h)
    (compileMatrix A).value (compileRhs v)).value with
  | none => simp [solve, hz] at hy
  | some s =>
    have hproj : (projectRows s.particular (leadingUnknown (D := D) (m := m) (n := n))).value = y := by
      simpa [solve, hz] using hy
    subst y
    let z := fun j => ((PolynomialLinearSolver.denseCoordinates (K := K) (D + D)
      (n + m * D) (outputBox D m h)).symm (FiniteLinearSolver.vector s.particular) j).val
    have hpoly := PolynomialLinearSolver.solveComplete_sound (D + D) (inputDegree D h)
      (compileMatrix A).value (compileRhs v) s hz 0
    simp only [FiniteLinearSolver.Solution.realize, Matrix.mulVec_zero, add_zero] at hpoly
    change PolynomialLinearSolver.denoteMatrix (compileMatrix A).value *ᵥ z = _ at hpoly
    rw [compileMatrix_correct] at hpoly
    have hzsol : LaurentPresentation.indexedMatrix (LaurentArithmetic.matrixDenote A) *ᵥ z =
        LaurentPresentation.indexedRhs (fun i => LaurentArithmetic.denote v[i]) :=
      hpoly.trans (funext (compileRhs_correct v))
    have he : (fun j => LaurentArithmetic.denote
        (projectRows s.particular (leadingUnknown (D := D) (m := m) (n := n))).value[j]) =
        LaurentPresentation.indexedProjection z := by
      funext j
      exact projectRows_correct s.particular leadingUnknown j
    refine (congrArg (fun w => LaurentArithmetic.matrixDenote A *ᵥ w) he).trans ?_
    funext i
    rw [← LaurentPresentation.indexed_evaluate, hzsol, LaurentPresentation.indexedEvaluation_rhs]

/-- Explicit arithmetic bound: compilation, Gaussian execution, and the
actually performed Laurent collision sums are all included. -/
def solveCost (D m n h : ℕ) : ℕ :=
  1 + 8 * (m * (inputDegree D h + outputBox D m h + 1) ^ (D + D) +
    (n + m * D) * (outputBox D m h + 1) ^ (D + D) + 1) ^ 4 +
      n * LaurentArithmetic.boxSize D (outputBox D m h) *
        PolynomialLinearSolver.boxSize (D + D) (outputBox D m h)

theorem solve_cost (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m) : (solve A v).cost ≤ solveCost D m n h := by
  have hc := PolynomialLinearSolver.solveComplete_cost (D + D) (inputDegree D h)
    (compileMatrix A).value (compileRhs v)
  unfold solve
  rw [Work.bind_cost, compileMatrix_cost, Work.bind_cost]
  cases hz : (PolynomialLinearSolver.solveComplete (D + D) (inputDegree D h)
      (compileMatrix A).value (compileRhs v)).value with
  | none =>
    simp only [Work.pure_cost]
    dsimp only [solveCost, outputBox] at *
    omega
  | some s =>
    simp only [Work.bind_cost, Work.pure_cost, add_zero, projectRows_cost]
    dsimp only [solveCost, outputBox] at *
    omega

/-- Known-solvable calls extract the actual program output, with no choice
of a solution and no separate search-window certificate. -/
def solveOfSolvable (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m)
    (hsol : ∃ y, LaurentArithmetic.matrixDenote A *ᵥ y = fun i => LaurentArithmetic.denote v[i]) :
    Work K (Vector (LaurentArithmetic.Dense K D (outputBox D m h)) n) :=
  let result := solve A v
  { value := result.value.get (by
      by_contra hn
      have he : result.value = none := Option.not_isSome_iff_eq_none.mp hn
      exact ((solve_none_iff A v).mp he) hsol)
    trace := result.trace }

theorem solveOfSolvable_correct (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m)
    (hsol : ∃ y, LaurentArithmetic.matrixDenote A *ᵥ y = fun i => LaurentArithmetic.denote v[i]) :
    LaurentArithmetic.matrixDenote A *ᵥ
      (fun j => LaurentArithmetic.denote (solveOfSolvable A v hsol).value[j]) =
        fun i => LaurentArithmetic.denote v[i] := by
  apply solve_sound A v
  exact (Option.some_get _).symm

theorem solveOfSolvable_cost (A : LaurentArithmetic.DenseMatrix K D m n h)
    (v : Vector (LaurentArithmetic.Dense K D h) m)
    (hsol : ∃ y, LaurentArithmetic.matrixDenote A *ᵥ y = fun i => LaurentArithmetic.denote v[i]) :
    (solveOfSolvable A v hsol).cost ≤ solveCost D m n h := solve_cost A v

end Decoupling.HighDim.LaurentLinearSolver
