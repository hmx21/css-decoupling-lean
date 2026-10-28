import Decoupling.HighDim.LaurentLinearSolverLift
import Decoupling.HighDim.LaurentArithmeticMatrix

/-!
# Executable compilation of dense Laurent systems to polynomial systems

The canonical lift is a coefficient lookup. The inverse-relation columns
are explicit two-monomial arrays; their minus-one coefficient is produced
by one recorded field negation shared by the whole matrix. Thus no field
arithmetic is hidden in the matrix assembly or in an abstract denotation.
-/

namespace Decoupling.HighDim.LaurentLinearSolver
open Matrix MvPolynomial ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D m n h : ℕ}

def inputDegree (D h : ℕ) : ℕ := max (2 * D * h) 2

def unknownIndex : (Fin n ⊕ (Fin m × Fin D)) ≃ Fin (n + m * D) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

/-- The positive-and-negative variable pair for one inverse relation. -/
def relationExponent (D : ℕ) (i : Fin D) : Fin (D + D) →₀ ℕ :=
  PolynomialLinearSolver.exponentOfFunction (fun j =>
    (if j = finSumFinEquiv (Sum.inl i) then 1 else 0) +
      (if j = finSumFinEquiv (Sum.inr i) then 1 else 0))

theorem relationExponent_ne_zero (D : ℕ) (i : Fin D) : relationExponent D i ≠ 0 := by
  intro he
  have hh := congrArg (fun a : Fin (D + D) →₀ ℕ => a (finSumFinEquiv (Sum.inl i))) he
  simp [relationExponent, PolynomialLinearSolver.exponentOfFunction_apply] at hh

theorem variableEquiv_relation (i : Fin D) :
    LaurentPresentation.variableEquiv (LaurentPresentation.relation K D i) =
      MvPolynomial.monomial (relationExponent D i) 1 - 1 := by
  simp only [LaurentPresentation.relation, map_sub, map_mul, map_one,
    LaurentPresentation.variableEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  have he : Finsupp.single (finSumFinEquiv (Sum.inl i)) 1 +
      Finsupp.single (finSumFinEquiv (Sum.inr i)) 1 = relationExponent D i := by
    ext j
    simp [relationExponent, PolynomialLinearSolver.exponentOfFunction_apply, Finsupp.single_apply, eq_comm]
  rw [he]

/-- Explicit coefficients for x_i y_i - 1; negOne is materialized once. -/
def relationDense (d : ℕ) (i : Fin D) (negOne : K) :
    Vector K (PolynomialLinearSolver.boxSize (D + D) d) :=
  Vector.ofFn fun k =>
    let a := (PolynomialLinearSolver.exponentAt (D + D) d k).val
    if a = 0 then negOne else if a = relationExponent D i then 1 else 0

theorem relationDense_correct (d : ℕ) (i : Fin D) (hd : 2 ≤ d) :
    (PolynomialLinearSolver.denotePolynomial (D + D) d (relationDense d i (-1 : K))).val =
      LaurentPresentation.variableEquiv (LaurentPresentation.relation K D i) := by
  apply polynomialDenote_eq_of_coeff
  · apply EffectiveLinear.mem_box_of_totalDegree_le
    rw [LaurentPresentation.variableEquiv_degree]
    exact (LaurentPresentation.relation_degree (K := K) i).trans hd
  · intro k
    rw [variableEquiv_relation]
    simp only [relationDense, Fin.getElem_fin, Vector.getElem_ofFn,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, MvPolynomial.coeff_one]
    by_cases ha : (PolynomialLinearSolver.exponentAt (D + D) d k).val = 0
    · simp [ha, relationExponent_ne_zero D i]
    · by_cases he : (PolynomialLinearSolver.exponentAt (D + D) d k).val = relationExponent D i
      · simp [he, relationExponent_ne_zero D i, Ne.symm (relationExponent_ne_zero D i)]
      · simp [ha, Ne.symm ha, he, Ne.symm he]

theorem zeroDense_correct (N d : ℕ) :
    (PolynomialLinearSolver.denotePolynomial N d (Vector.replicate _ (0 : K))).val = 0 := by
  apply polynomialDenote_eq_of_coeff
  · exact Submodule.zero_mem _
  · intro k
    simp

def expandedDense (negOne : K) (A : LaurentArithmetic.DenseMatrix K D m n h) :
    PolynomialLinearSolver.CoeffMatrix K (D + D) m (n + m * D) (inputDegree D h) :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    match unknownIndex.symm j with
    | Sum.inl k => liftDense (inputDegree D h) A[i][k]
    | Sum.inr z => if i = z.1 then relationDense (inputDegree D h) z.2 negOne
      else Vector.replicate _ 0

/-- Compile the matrix while recording the only field operation in assembly. -/
def compileMatrix (A : LaurentArithmetic.DenseMatrix K D m n h) :
    Work K (PolynomialLinearSolver.CoeffMatrix K (D + D) m (n + m * D) (inputDegree D h)) :=
  Work.bind (ArithmeticCost.neg (1 : K)) fun negOne => Work.pure (expandedDense negOne A)

def compileRhs (v : Vector (LaurentArithmetic.Dense K D h) m) :
    PolynomialLinearSolver.CoeffVector K (D + D) m (inputDegree D h) :=
  v.map (liftDense (inputDegree D h))

@[simp] theorem compileMatrix_cost (A : LaurentArithmetic.DenseMatrix K D m n h) :
    (compileMatrix A).cost = 1 := by simp [compileMatrix]

theorem compileMatrix_correct (A : LaurentArithmetic.DenseMatrix K D m n h) :
    PolynomialLinearSolver.denoteMatrix (compileMatrix A).value =
      LaurentPresentation.indexedMatrix (LaurentArithmetic.matrixDenote A) := by
  funext i j
  change (PolynomialLinearSolver.denotePolynomial (D + D) (inputDegree D h)
    (expandedDense (-1 : K) A)[i][j]).val = _
  simp only [expandedDense, Fin.getElem_fin, Vector.getElem_ofFn]
  generalize hj : (unknownIndex (D := D) (m := m) (n := n)).symm j = z
  have hj' : LaurentPresentation.unknownEquiv.symm j = z := hj
  change _ = (LaurentPresentation.variableEquiv
    (LaurentPresentation.expandedMatrix (LaurentArithmetic.matrixDenote A) i
      (LaurentPresentation.unknownEquiv.symm j)))
  rw [hj']
  cases z with
  | inl k => exact liftDense_correct _ _ (le_max_left _ _)
  | inr z =>
    change (PolynomialLinearSolver.denotePolynomial _ _
      (if i = z.1 then relationDense _ z.2 (-1 : K) else _)).val =
      LaurentPresentation.variableEquiv (if i = z.1 then LaurentPresentation.relation K D z.2 else 0)
    split
    · exact relationDense_correct _ _ (le_max_right _ _)
    · rw [zeroDense_correct, map_zero]

theorem compileRhs_correct (v : Vector (LaurentArithmetic.Dense K D h) m) (i : Fin m) :
    (PolynomialLinearSolver.denoteVector (compileRhs v) i).val =
      LaurentPresentation.indexedRhs (fun i => LaurentArithmetic.denote v[i]) i := by
  change (PolynomialLinearSolver.denotePolynomial _ _ ((v.map (liftDense (inputDegree D h)))[i])).val = _
  simp only [Fin.getElem_fin, Vector.getElem_map]
  exact liftDense_correct _ _ (le_max_left _ _)

end Decoupling.HighDim.LaurentLinearSolver
