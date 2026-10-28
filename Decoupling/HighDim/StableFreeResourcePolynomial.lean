import Decoupling.HighDim.StableFreeResourceStage
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Explicit natural-coefficient polynomials for finite Schanuel iteration

Spatial dimension and the number of recursive stages are fixed parameters.
The numerical envelope is exactly the existing actual-stage envelope.
Polynomial composition follows the same child-input recurrence; no
polynomial bound or iteration-count certificate is supplied by a caller.
-/
namespace Decoupling.HighDim.StableFree.Resource
open Polynomial Effective LaurentArithmetic

noncomputable def updatePolynomial (D : ℕ) (a b p q h : Polynomial ℕ) : Polynomial ℕ :=
  ((b+q)*(a+(b+q))*(a+p)*(2*(h+h)+1)^D*(2*(2*h+1)^D+1) +
    (b+q)*(a+(b+q))*(2*(h+h)+1)^D) +
  ((b+q)*b*(2*h+1)^D +
    ((a+p)*(b+(a+p))*(b+q)*(2*(h+h)+1)^D*(2*(2*h+1)^D+1) +
      (a+p)*(b+(a+p))*(2*(h+h)+1)^D))

theorem updatePolynomial_eval (D : ℕ) (a b p q h : Polynomial ℕ) (s : ℕ) :
    (updatePolynomial D a b p q h).eval s =
      DenseTower.updateCost D (a.eval s) (b.eval s) (p.eval s) (q.eval s) (h.eval s) := by
  simp [updatePolynomial,DenseTower.updateCost,boxSize]

noncomputable def solvePolynomial (D : ℕ) : Polynomial ℕ :=
  (LaurentSolverGrowth.polynomial D).comp (12*(X+1)^2)

theorem solvePolynomial_eval (D s : ℕ) : (solvePolynomial D).eval s = solveCap D s := by
  simp only [solvePolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
    LaurentSolverGrowth.polynomial_eval]
  rfl

noncomputable def stepPolynomial (D : ℕ) : Polynomial ℕ :=
  let s : Polynomial ℕ := X
  let z := solvePolynomial D
  s+1+2*z + (2*s)*(2*s)*(2*s)*(2*(2*s)+1)^D*(2*(2*s+1)^D+1) +
    2*(12*s*s*(2*(2*s)+1)^D+z) + updatePolynomial D s s s s z

theorem stepPolynomial_eval (D s : ℕ) : (stepPolynomial D).eval s = stepBound D s := by
  simp only [stepPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat,solvePolynomial_eval,updatePolynomial_eval]
  rfl

/-- The same recursion order as a child invocation of the actual algorithm. -/
def iteratedBound (D : ℕ) : ℕ → ℕ → ℕ
  | 0,s => s
  | n+1,s => iteratedBound D n (stepBound D s)

noncomputable def iteratedPolynomial (D : ℕ) : ℕ → Polynomial ℕ
  | 0 => X
  | n+1 => (iteratedPolynomial D n).comp (stepPolynomial D)

theorem iteratedPolynomial_eval (D n s : ℕ) :
    (iteratedPolynomial D n).eval s = iteratedBound D n s := by
  induction n generalizing s with
  | zero => simp only [iteratedPolynomial,Polynomial.eval_X,iteratedBound]
  | succ n ih =>
      rw [iteratedPolynomial,Polynomial.eval_comp,stepPolynomial_eval,ih]
      rfl

theorem iteratedBound_monotone (D n : ℕ) : Monotone (iteratedBound D n) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih => exact ih.comp (stepBound_monotone D)

theorem input_le_iteratedBound (D n s : ℕ) : s ≤ iteratedBound D n s := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih => exact (input_le_stepBound D s).trans (ih _)

theorem step_le_iteratedBound_succ (D n s : ℕ) : stepBound D s ≤ iteratedBound D (n+1) s :=
  input_le_iteratedBound D n (stepBound D s)

theorem iteratedBound_le_succ (D n s : ℕ) : iteratedBound D n s ≤ iteratedBound D (n+1) s :=
  iteratedBound_monotone D n (input_le_stepBound D s)

theorem iteratedBound_monotone_steps (D s : ℕ) : Monotone (fun n => iteratedBound D n s) :=
  monotone_nat_of_le_succ (fun n => iteratedBound_le_succ D n s)

/-- Cost is the stage count times the polynomial bounding every stage. -/
noncomputable def costPolynomial (D n : ℕ) : Polynomial ℕ := C n * iteratedPolynomial D n

theorem costPolynomial_eval (D n s : ℕ) :
    (costPolynomial D n).eval s = n*iteratedBound D n s := by
  rw [costPolynomial,Polynomial.eval_mul,Polynomial.eval_C,iteratedPolynomial_eval]

end Decoupling.HighDim.StableFree.Resource
