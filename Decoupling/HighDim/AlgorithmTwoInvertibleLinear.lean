import Decoupling.HighDim.AlgorithmTwoLinearComparisonProgram

/-!
# Actual Laurent solver for rectangular equations with several right sides

Flattening A X = B copies coefficients into the Kronecker system. It
performs no field operations. The complete Laurent solver handles every
right side at once; its true output is reshaped into a materialized X.
-/
namespace Decoupling.HighDim.AlgorithmTwoInvertible
open Matrix ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

section Algebra
variable {R : Type*} [CommRing R] {m n r : ℕ}

def coefficients (A : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m × Fin r) (Fin n × Fin r) R :=
  fun ik jl => if jl.2=ik.2 then A ik.1 jl.1 else 0

theorem coefficients_mulVec (A : Matrix (Fin m) (Fin n) R) (X : Matrix (Fin n) (Fin r) R) :
    coefficients A *ᵥ (fun ij => X ij.1 ij.2) = fun ij => (A*X) ij.1 ij.2 := by
  funext ij
  simp [coefficients, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply]
end Algebra

variable {K : Type*} [Field K] [DecidableEq K] {D m n r h : ℕ}

def compile (A : LaurentArithmetic.DenseMatrix K D m n h) :
    LaurentArithmetic.DenseMatrix K D (m*r) (n*r) h :=
  Vector.ofFn fun row => Vector.ofFn fun col =>
    let ik := finProdFinEquiv.symm row
    let jl := finProdFinEquiv.symm col
    if jl.2=ik.2 then A[ik.1][jl.1] else AlgorithmTwoLinearComparison.zeroDense

def rhs (B : LaurentArithmetic.DenseMatrix K D m r h) :
    Vector (LaurentArithmetic.Dense K D h) (m*r) :=
  Vector.ofFn fun row => B[(finProdFinEquiv.symm row).1][(finProdFinEquiv.symm row).2]

omit [DecidableEq K] in
theorem compile_correct (A : LaurentArithmetic.DenseMatrix K D m n h) :
    LaurentArithmetic.matrixDenote (compile (r := r) A) =
      (coefficients (r := r) (LaurentArithmetic.matrixDenote A)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  funext row col
  simp only [compile, LaurentArithmetic.matrixDenote, Fin.getElem_fin, Vector.getElem_ofFn,
    Fin.eta, Matrix.submatrix_apply, coefficients]
  split_ifs <;> simp_all

omit [DecidableEq K] in
theorem rhs_correct (B : LaurentArithmetic.DenseMatrix K D m r h) (row : Fin (m*r)) :
    LaurentArithmetic.denote (rhs B)[row] = LaurentArithmetic.matrixDenote B
      (finProdFinEquiv.symm row).1 (finProdFinEquiv.symm row).2 := by
  simp only [rhs, LaurentArithmetic.matrixDenote, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

def decode (x : Fin (n*r) → Laurent K D) : Matrix (Fin n) (Fin r) (Laurent K D) :=
  fun i j => x (finProdFinEquiv (i,j))

omit [DecidableEq K] in
theorem indexed_equation_iff (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h) (x : Fin (n*r) → Laurent K D) :
    LaurentArithmetic.matrixDenote (compile A) *ᵥ x = (fun i => LaurentArithmetic.denote (rhs B)[i]) ↔
      LaurentArithmetic.matrixDenote A * decode x = LaurentArithmetic.matrixDenote B := by
  unfold decode
  rw [compile_correct, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  have hm := coefficients_mulVec (LaurentArithmetic.matrixDenote A)
    (fun i j => x (finProdFinEquiv (i,j)))
  change ((coefficients (LaurentArithmetic.matrixDenote A) *ᵥ (fun ij => x (finProdFinEquiv ij))) ∘
    finProdFinEquiv.symm = _) ↔ _
  rw [hm]
  constructor
  · intro he
    funext i j
    have hh := congrFun he (finProdFinEquiv (i,j))
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, rhs_correct] using hh
  · intro he
    funext i
    rw [rhs_correct]
    exact congrFun (congrFun he (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

omit [DecidableEq K] in
theorem indexed_exists_iff (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h) :
    (∃ x, LaurentArithmetic.matrixDenote (compile A) *ᵥ x = fun i => LaurentArithmetic.denote (rhs B)[i]) ↔
      ∃ X, LaurentArithmetic.matrixDenote A * X = LaurentArithmetic.matrixDenote B := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨fun i j => x (finProdFinEquiv (i,j)), (indexed_equation_iff A B x).mp hx⟩
  · rintro ⟨X,hX⟩
    refine ⟨fun i => X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2, ?_⟩
    apply (indexed_equation_iff A B _).mpr
    unfold decode
    simpa only [Equiv.symm_apply_apply] using hX

abbrev outputBox (D m r h : ℕ) := LaurentLinearSolver.outputBox D (m*r) h

def solve (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h) :
    Work K (Option (LaurentArithmetic.DenseMatrix K D n r (outputBox D m r h))) :=
  Work.bind (LaurentLinearSolver.solve (compile A) (rhs B)) fun result =>
    Work.pure (result.map AlgorithmTwoLinearComparison.reshape)

theorem solve_none_iff (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h) :
    (solve A B).value = none ↔ ¬ ∃ X, LaurentArithmetic.matrixDenote A * X = LaurentArithmetic.matrixDenote B := by
  simp only [solve, Work.bind_value, Work.pure_value, Option.map_eq_none_iff,
    LaurentLinearSolver.solve_none_iff]
  exact not_congr (indexed_exists_iff A B)

theorem solve_sound (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h)
    (X : LaurentArithmetic.DenseMatrix K D n r (outputBox D m r h)) (hX : (solve A B).value = some X) :
    LaurentArithmetic.matrixDenote A * LaurentArithmetic.matrixDenote X = LaurentArithmetic.matrixDenote B := by
  cases hx : (LaurentLinearSolver.solve (compile A) (rhs B)).value with
  | none => simp [solve, hx] at hX
  | some x =>
    have he : AlgorithmTwoLinearComparison.reshape x = X := by simpa [solve,hx] using hX
    subst X
    rw [AlgorithmTwoLinearComparison.reshape_correct]
    exact (indexed_equation_iff A B (fun j => LaurentArithmetic.denote x[j])).mp
      (LaurentLinearSolver.solve_sound (compile A) (rhs B) x hx)

theorem solve_cost (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h) :
    (solve A B).cost ≤ LaurentLinearSolver.solveCost D (m*r) (n*r) h := by
  simpa only [solve, Work.bind_cost, Work.pure_cost, add_zero] using LaurentLinearSolver.solve_cost (compile A) (rhs B)

def solveOfExists (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h)
    (hex : ∃ X, LaurentArithmetic.matrixDenote A * X = LaurentArithmetic.matrixDenote B) :
    Work K (LaurentArithmetic.DenseMatrix K D n r (outputBox D m r h)) :=
  let result := solve A B
  { value := result.value.get (by
      by_contra hn
      exact ((solve_none_iff A B).mp (Option.not_isSome_iff_eq_none.mp hn)) hex)
    trace := result.trace }

theorem solveOfExists_correct (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h)
    (hex : ∃ X, LaurentArithmetic.matrixDenote A * X = LaurentArithmetic.matrixDenote B) :
    LaurentArithmetic.matrixDenote A * LaurentArithmetic.matrixDenote (solveOfExists A B hex).value =
      LaurentArithmetic.matrixDenote B := by
  apply solve_sound A B
  exact (Option.some_get _).symm

theorem solveOfExists_cost (A : LaurentArithmetic.DenseMatrix K D m n h)
    (B : LaurentArithmetic.DenseMatrix K D m r h)
    (hex : ∃ X, LaurentArithmetic.matrixDenote A * X = LaurentArithmetic.matrixDenote B) :
    (solveOfExists A B hex).cost ≤ LaurentLinearSolver.solveCost D (m*r) (n*r) h := solve_cost A B

end Decoupling.HighDim.AlgorithmTwoInvertible
