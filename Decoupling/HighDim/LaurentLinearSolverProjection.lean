import Decoupling.HighDim.LaurentLinearSolverIndex
import Decoupling.HighDim.LaurentArithmeticMatrix

/-!
# Counted projection of polynomial coefficient arrays to Laurent arrays

Different positive/negative exponent pairs can yield the same Laurent
exponent. Every collision is summed by the actual counted `sumValues`
program. A polynomial coefficient box B projects to Laurent radius B,
using the individual exponent bounds, not an incorrect total-degree claim.
-/

namespace Decoupling.HighDim.LaurentLinearSolver
open Matrix MvPolynomial ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D B : ℕ}

theorem joinExponent_mem_box (a : EffectiveLinear.BoxExponent (D + D) B) :
    joinExponent D a.val ∈ LaurentBoxes.box D B := by
  rw [LaurentBoxes.mem_box]
  intro i
  have hp := a.property (finSumFinEquiv (Sum.inl i))
  have hn := a.property (finSumFinEquiv (Sum.inr i))
  change -(B : ℤ) ≤ (a.val (finSumFinEquiv (Sum.inl i)) : ℤ) -
    a.val (finSumFinEquiv (Sum.inr i)) ∧
    (a.val (finSumFinEquiv (Sum.inl i)) : ℤ) - a.val (finSumFinEquiv (Sum.inr i)) ≤ B
  omega

theorem indexedDenote_eq_sum (v : Vector K (PolynomialLinearSolver.boxSize (D + D) B)) :
    LaurentPresentation.indexedEvaluation (PolynomialLinearSolver.denotePolynomial (D + D) B v).val =
      ∑ k, AddMonoidAlgebra.single
        (joinExponent D (PolynomialLinearSolver.exponentAt (D + D) B k).val) v[k] := by
  rw [denotePolynomial_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact indexedEvaluation_monomial _ _

theorem indexedDenote_supported (v : Vector K (PolynomialLinearSolver.boxSize (D + D) B)) :
    LaurentBoxes.Supported
      (LaurentPresentation.indexedEvaluation (PolynomialLinearSolver.denotePolynomial (D + D) B v).val) B := by
  classical
  rw [indexedDenote_eq_sum]
  apply LaurentBoxes.supported_sum
  intro k _ a ha
  change a ∈ (Finsupp.single
    (joinExponent D (PolynomialLinearSolver.exponentAt (D + D) B k).val) v[k]).support at ha
  by_cases he : joinExponent D (PolynomialLinearSolver.exponentAt (D + D) B k).val = a
  · exact he ▸ joinExponent_mem_box (PolynomialLinearSolver.exponentAt (D + D) B k)
  · have hn := Finsupp.mem_support_iff.mp ha
    simp [he] at hn

theorem indexedDenote_coeff (v : Vector K (PolynomialLinearSolver.boxSize (D + D) B))
    (a : Translation D) :
    (LaurentPresentation.indexedEvaluation
      (PolynomialLinearSolver.denotePolynomial (D + D) B v).val).coeff a =
      ∑ k, if joinExponent D (PolynomialLinearSolver.exponentAt (D + D) B k).val = a
        then v[k] else 0 := by
  classical
  rw [indexedDenote_eq_sum]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Execute the actual sums of all coefficient collisions. -/
def projectPolynomial (v : Vector K (PolynomialLinearSolver.boxSize (D + D) B)) :
    Work K (LaurentArithmetic.Dense K D B) :=
  collect (LaurentArithmetic.boxSize D B) fun a =>
    LaurentArithmetic.sumValues (PolynomialLinearSolver.boxSize (D + D) B) (fun k =>
      if joinExponent D (PolynomialLinearSolver.exponentAt (D + D) B k).val =
          LaurentArithmetic.exponentAt D B a then v[k] else 0)

@[simp] theorem projectPolynomial_cost
    (v : Vector K (PolynomialLinearSolver.boxSize (D + D) B)) :
    (projectPolynomial v).cost =
      LaurentArithmetic.boxSize D B * PolynomialLinearSolver.boxSize (D + D) B := by
  simp [projectPolynomial]

theorem projectPolynomial_correct
    (v : Vector K (PolynomialLinearSolver.boxSize (D + D) B)) :
    LaurentArithmetic.denote (projectPolynomial v).value =
      LaurentPresentation.indexedEvaluation (PolynomialLinearSolver.denotePolynomial (D + D) B v).val := by
  apply LaurentArithmetic.denote_eq_of_coeff
  · exact indexedDenote_supported v
  · intro k
    simp only [projectPolynomial, collect_value_get, LaurentArithmetic.sumValues_value,
      indexedDenote_coeff]

/-- Read a specified polynomial coordinate from a flat coefficient vector. -/
def polynomialBlock {N n b : ℕ} (v : Vector K (n * PolynomialLinearSolver.boxSize N b))
    (i : Fin n) : Vector K (PolynomialLinearSolver.boxSize N b) :=
  Vector.ofFn fun k => v[finProdFinEquiv (i, k)]

/-- Materialized polynomial blocks agree with the native coefficient-coordinate inverse. -/
theorem polynomialBlock_denote {N n b : ℕ}
    (v : Vector K (n * PolynomialLinearSolver.boxSize N b)) (i : Fin n) :
    PolynomialLinearSolver.denotePolynomial N b (polynomialBlock v i) =
      (PolynomialLinearSolver.denseCoordinates (K := K) N n b).symm
        (FiniteLinearSolver.vector v) i := by
  apply (EffectiveLinear.boxCoordinates K N b).injective
  funext a
  rw [EffectiveLinear.boxCoordinates_apply, PolynomialLinearSolver.denotePolynomial_coeff]
  have he := congrFun ((PolynomialLinearSolver.denseCoordinates (K := K) N n b).apply_symm_apply
    (FiniteLinearSolver.vector v)) ((PolynomialLinearSolver.systemIndex N n b).symm (i, a))
  change EffectiveLinear.vectorCoordinates K N n b
    ((PolynomialLinearSolver.denseCoordinates (K := K) N n b).symm (FiniteLinearSolver.vector v))
    ((PolynomialLinearSolver.systemIndex N n b) ((PolynomialLinearSolver.systemIndex N n b).symm (i, a))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  change _ = EffectiveLinear.vectorCoordinates K N n b
    ((PolynomialLinearSolver.denseCoordinates (K := K) N n b).symm (FiniteLinearSolver.vector v)) (i, a)
  rw [he]
  simp [polynomialBlock, FiniteLinearSolver.vector, PolynomialLinearSolver.systemIndex]

/-- Project selected polynomial coordinates, returning actual dense Laurent values. -/
def projectRows {q n : ℕ}
    (v : Vector K (q * PolynomialLinearSolver.boxSize (D + D) B)) (pick : Fin n → Fin q) :
    Work K (Vector (LaurentArithmetic.Dense K D B) n) :=
  collect n fun i => projectPolynomial (polynomialBlock v (pick i))

@[simp] theorem projectRows_cost {q n : ℕ}
    (v : Vector K (q * PolynomialLinearSolver.boxSize (D + D) B)) (pick : Fin n → Fin q) :
    (projectRows v pick).cost =
      n * LaurentArithmetic.boxSize D B * PolynomialLinearSolver.boxSize (D + D) B := by
  simp [projectRows]
  ring

theorem projectRows_correct {q n : ℕ}
    (v : Vector K (q * PolynomialLinearSolver.boxSize (D + D) B)) (pick : Fin n → Fin q) (i : Fin n) :
    LaurentArithmetic.denote (projectRows v pick).value[i] =
      LaurentPresentation.indexedEvaluation
        (((PolynomialLinearSolver.denseCoordinates (K := K) (D + D) q B).symm
          (FiniteLinearSolver.vector v)) (pick i)).val := by
  rw [projectRows, collect_value_get, projectPolynomial_correct, polynomialBlock_denote]

end Decoupling.HighDim.LaurentLinearSolver
