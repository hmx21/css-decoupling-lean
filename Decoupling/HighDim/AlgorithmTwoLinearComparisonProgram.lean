import Decoupling.HighDim.AlgorithmTwoLinearComparisonCompile

/-!
# Actual solver calls for finite comparison and contraction equations

The result is a materialized matrix. Its failure condition concerns the
unbounded native equations; the existence proof used by `solveOfExists`
only rules out the failure branch of this concrete executed program.
-/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open Matrix ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 250000
variable {K : Type*} [Field K] [DecidableEq K] {D n m k h : ℕ}

structure Input (K : Type*) (D n m k h : ℕ) where
  left : LaurentArithmetic.DenseMatrix K D n n h
  right : LaurentArithmetic.DenseMatrix K D m m h
  top : LaurentArithmetic.DenseMatrix K D m k h
  rhs : LaurentArithmetic.DenseMatrix K D n m h
  prescribed : LaurentArithmetic.DenseMatrix K D n k h
  allowed : Mask n m

namespace Input
omit [DecidableEq K] in
noncomputable def Satisfied (v : Input K D n m k h) (X : Matrix (Fin n) (Fin m) (Laurent K D)) : Prop :=
  Satisfies (LaurentArithmetic.matrixDenote v.left) (LaurentArithmetic.matrixDenote v.right)
    (LaurentArithmetic.matrixDenote v.top) (maskFunction v.allowed)
    (LaurentArithmetic.matrixDenote v.rhs) (LaurentArithmetic.matrixDenote v.prescribed) X
end Input

abbrev resultBox (D n m k h : ℕ) := LaurentLinearSolver.outputBox D (equationCount n m k) h

def reshape {B : ℕ} (x : Vector (LaurentArithmetic.Dense K D B) (n*m)) :
    LaurentArithmetic.DenseMatrix K D n m B :=
  Vector.ofFn fun i => Vector.ofFn fun j => x[unknownEquiv n m (i,j)]

omit [DecidableEq K] in
theorem reshape_correct {B : ℕ} (x : Vector (LaurentArithmetic.Dense K D B) (n*m)) :
    LaurentArithmetic.matrixDenote (reshape x) =
      fun i j => LaurentArithmetic.denote x[unknownEquiv n m (i,j)] := by
  funext i j
  simp only [LaurentArithmetic.matrixDenote, reshape, Fin.getElem_fin, Vector.getElem_ofFn]

omit [DecidableEq K] in
theorem indexed_equation_iff (v : Input K D n m k h) (x : Fin (n*m) → Laurent K D) :
    LaurentArithmetic.matrixDenote (compile v.left v.right v.top v.allowed).value *ᵥ x =
      (fun i => LaurentArithmetic.denote (rhsArray v.rhs v.prescribed)[i]) ↔
    v.Satisfied (fun i j => x (unknownEquiv n m (i,j))) := by
  rw [compile_correct, Matrix.submatrix_mulVec_equiv]
  have rhsEq : (fun i => LaurentArithmetic.denote (rhsArray v.rhs v.prescribed)[i]) =
      systemRhs (LaurentArithmetic.matrixDenote v.rhs) (LaurentArithmetic.matrixDenote v.prescribed) ∘
        (equationEquiv n m k).symm := funext (rhsArray_correct _ _)
  rw [rhsEq]
  have hc : Function.Injective (fun f : Equation n m k → Laurent K D => f ∘ (equationEquiv n m k).symm) :=
    fun f g hfg => funext fun i => by
      simpa using congrFun hfg (equationEquiv n m k i)
  rw [hc.eq_iff]
  exact system_equation_iff (R := Laurent K D) (n := n) (m := m) (k := k)
    (LaurentArithmetic.matrixDenote v.left) (LaurentArithmetic.matrixDenote v.right)
    (LaurentArithmetic.matrixDenote v.top) (maskFunction v.allowed)
    (LaurentArithmetic.matrixDenote v.rhs) (LaurentArithmetic.matrixDenote v.prescribed)
    (fun i j => x (unknownEquiv n m (i,j)))

omit [DecidableEq K] in
theorem indexed_exists_iff (v : Input K D n m k h) :
    (∃ x, LaurentArithmetic.matrixDenote (compile v.left v.right v.top v.allowed).value *ᵥ x =
      fun i => LaurentArithmetic.denote (rhsArray v.rhs v.prescribed)[i]) ↔
      ∃ X, v.Satisfied X := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (indexed_equation_iff v x).mp hx⟩
  · rintro ⟨X, hX⟩
    refine ⟨fun j => X ((unknownEquiv n m).symm j).1 ((unknownEquiv n m).symm j).2, ?_⟩
    apply (indexed_equation_iff v _).mpr
    simpa using hX

def solve (v : Input K D n m k h) :
    Work K (Option (LaurentArithmetic.DenseMatrix K D n m (resultBox D n m k h))) :=
  Work.bind (compile v.left v.right v.top v.allowed) fun A =>
    Work.bind (LaurentLinearSolver.solve A (rhsArray v.rhs v.prescribed)) fun result =>
      Work.pure (result.map reshape)

theorem solve_none_iff (v : Input K D n m k h) :
    (solve v).value = none ↔ ¬ ∃ X, v.Satisfied X := by
  simp only [solve, Work.bind_value, Work.pure_value, Option.map_eq_none_iff,
    LaurentLinearSolver.solve_none_iff]
  exact not_congr (indexed_exists_iff v)

theorem solve_sound (v : Input K D n m k h)
    (X : LaurentArithmetic.DenseMatrix K D n m (resultBox D n m k h))
    (hX : (solve v).value = some X) : v.Satisfied (LaurentArithmetic.matrixDenote X) := by
  cases hx : (LaurentLinearSolver.solve (compile v.left v.right v.top v.allowed).value
      (rhsArray v.rhs v.prescribed)).value with
  | none => simp [solve, hx] at hX
  | some x =>
    have he : reshape x = X := by simpa [solve, hx] using hX
    subst X
    have hs := LaurentLinearSolver.solve_sound (compile v.left v.right v.top v.allowed).value
      (rhsArray v.rhs v.prescribed) x hx
    rw [reshape_correct]
    exact (indexed_equation_iff v (fun j => LaurentArithmetic.denote x[j])).mp hs

def costBound (D n m k h : ℕ) : ℕ :=
  equationCount n m k * (n*m) * LaurentArithmetic.boxSize D h +
    LaurentLinearSolver.solveCost D (equationCount n m k) (n*m) h

theorem solve_cost (v : Input K D n m k h) : (solve v).cost ≤ costBound D n m k h := by
  simp only [solve, Work.bind_cost, Work.pure_cost, add_zero]
  exact Nat.add_le_add (compile_cost _ _ _ _) (LaurentLinearSolver.solve_cost _ _)

def solveOfExists (v : Input K D n m k h) (hex : ∃ X, v.Satisfied X) :
    Work K (LaurentArithmetic.DenseMatrix K D n m (resultBox D n m k h)) :=
  let result := solve v
  { value := result.value.get (by
      by_contra hn
      exact ((solve_none_iff v).mp (Option.not_isSome_iff_eq_none.mp hn)) hex)
    trace := result.trace }

theorem solveOfExists_correct (v : Input K D n m k h) (hex : ∃ X, v.Satisfied X) :
    v.Satisfied (LaurentArithmetic.matrixDenote (solveOfExists v hex).value) := by
  apply solve_sound v
  exact (Option.some_get _).symm

theorem solveOfExists_cost (v : Input K D n m k h) (hex : ∃ X, v.Satisfied X) :
    (solveOfExists v hex).cost ≤ costBound D n m k h := solve_cost v

end Decoupling.HighDim.AlgorithmTwoLinearComparison
