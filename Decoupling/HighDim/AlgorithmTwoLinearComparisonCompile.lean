import Decoupling.HighDim.AlgorithmTwoLinearComparisonSystem
import Decoupling.HighDim.LaurentLinearSolverKernel
import Decoupling.HighDim.LaurentArithmeticStructural

/-!
# Executable comparison-system assembly

All inputs are materialized coefficient arrays, including the Boolean
mask. The only field arithmetic in assembly is the recorded addition of
the two Sylvester coefficients. All other entries are copies or 0/1.
-/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open Matrix ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D n m k h : ℕ}

abbrev equationCount (n m k : ℕ) := n * m + (n * k + n * m)

def unknownEquiv (n m : ℕ) : Unknown n m ≃ Fin (n * m) := finProdFinEquiv

def equationEquiv (n m k : ℕ) : Equation n m k ≃ Fin (equationCount n m k) :=
  (Equiv.sumCongr finProdFinEquiv ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
    finSumFinEquiv)).trans finSumFinEquiv

abbrev Mask (n m : ℕ) := Vector (Vector Bool m) n

def maskFunction (allowed : Mask n m) (i : Fin n) (j : Fin m) : Bool := allowed[i][j]

def zeroDense : LaurentArithmetic.Dense K D h := Vector.replicate _ 0

def oneDense : LaurentArithmetic.Dense K D h :=
  Vector.ofFn fun t => if LaurentArithmetic.exponentAt D h t = 0 then 1 else 0

@[simp] theorem zeroDense_correct : LaurentArithmetic.denote (zeroDense (K := K) (D := D) (h := h)) = 0 := by
  simp [zeroDense, LaurentArithmetic.denote]

@[simp] theorem oneDense_correct : LaurentArithmetic.denote (oneDense (K := K) (D := D) (h := h)) = 1 := by
  apply LaurentArithmetic.denote_eq_of_coeff _ _ LaurentBoxes.supported_one
  intro t
  simp [oneDense, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

def addSame (v w : LaurentArithmetic.Dense K D h) : Work K (LaurentArithmetic.Dense K D h) :=
  collect (LaurentArithmetic.boxSize D h) fun t => ArithmeticCost.add v[t] w[t]

@[simp] theorem addSame_cost (v w : LaurentArithmetic.Dense K D h) :
    (addSame v w).cost = LaurentArithmetic.boxSize D h := by simp [addSame]

theorem addSame_correct (v w : LaurentArithmetic.Dense K D h) :
    LaurentArithmetic.denote (addSame v w).value = LaurentArithmetic.denote v + LaurentArithmetic.denote w := by
  apply LaurentArithmetic.denote_eq_of_coeff
  · exact LaurentBoxes.supported_add (LaurentArithmetic.denote_supported v) (LaurentArithmetic.denote_supported w)
  · intro t
    simp [addSame, AddMonoidAlgebra.coeff_add, LaurentArithmetic.denote_coeff]

def coefficientProgram (L : LaurentArithmetic.DenseMatrix K D n n h)
    (A : LaurentArithmetic.DenseMatrix K D m m h) (P : LaurentArithmetic.DenseMatrix K D m k h)
    (allowed : Mask n m) (row : Equation n m k) (col : Unknown n m) :
    Work K (LaurentArithmetic.Dense K D h) :=
  match row with
  | .inl ij => addSame (if col.2 = ij.2 then L[ij.1][col.1] else zeroDense)
      (if col.1 = ij.1 then A[col.2][ij.2] else zeroDense)
  | .inr (.inl ij) => Work.pure (if col.1 = ij.1 then P[col.2][ij.2] else zeroDense)
  | .inr (.inr ij) => Work.pure (if allowed[ij.1][ij.2] then zeroDense else
      if col = ij then oneDense else zeroDense)

theorem coefficientProgram_correct (L : LaurentArithmetic.DenseMatrix K D n n h)
    (A : LaurentArithmetic.DenseMatrix K D m m h) (P : LaurentArithmetic.DenseMatrix K D m k h)
    (allowed : Mask n m) (row : Equation n m k) (col : Unknown n m) :
    LaurentArithmetic.denote (coefficientProgram L A P allowed row col).value =
      systemMatrix (LaurentArithmetic.matrixDenote L) (LaurentArithmetic.matrixDenote A)
        (LaurentArithmetic.matrixDenote P) (maskFunction allowed) row col := by
  rcases row with ij | (ij | ij)
  · simp only [coefficientProgram, addSame_correct, systemMatrix, Sum.elim_inl, sylvesterCoefficient]
    split_ifs <;> simp_all [LaurentArithmetic.matrixDenote]
  · simp only [coefficientProgram, Work.pure_value, systemMatrix, Sum.elim_inr,
      Sum.elim_inl, valuesCoefficient]
    split_ifs <;> simp_all [LaurentArithmetic.matrixDenote]
  · simp only [coefficientProgram, Work.pure_value, systemMatrix, Sum.elim_inr,
      maskCoefficient, maskFunction]
    split_ifs <;> simp_all

theorem coefficientProgram_cost (L : LaurentArithmetic.DenseMatrix K D n n h)
    (A : LaurentArithmetic.DenseMatrix K D m m h) (P : LaurentArithmetic.DenseMatrix K D m k h)
    (allowed : Mask n m) (row : Equation n m k) (col : Unknown n m) :
    (coefficientProgram L A P allowed row col).cost ≤ LaurentArithmetic.boxSize D h := by
  rcases row with ij | (ij | ij) <;> simp [coefficientProgram]

def compile (L : LaurentArithmetic.DenseMatrix K D n n h)
    (A : LaurentArithmetic.DenseMatrix K D m m h) (P : LaurentArithmetic.DenseMatrix K D m k h)
    (allowed : Mask n m) :
    Work K (LaurentArithmetic.DenseMatrix K D (equationCount n m k) (n*m) h) :=
  collect _ fun row => collect _ fun col =>
    coefficientProgram L A P allowed ((equationEquiv n m k).symm row) ((unknownEquiv n m).symm col)

theorem compile_correct (L : LaurentArithmetic.DenseMatrix K D n n h)
    (A : LaurentArithmetic.DenseMatrix K D m m h) (P : LaurentArithmetic.DenseMatrix K D m k h)
    (allowed : Mask n m) :
    LaurentArithmetic.matrixDenote (compile L A P allowed).value =
      (systemMatrix (LaurentArithmetic.matrixDenote L) (LaurentArithmetic.matrixDenote A)
        (LaurentArithmetic.matrixDenote P) (maskFunction allowed)).submatrix
          (equationEquiv n m k).symm (unknownEquiv n m).symm := by
  funext row col
  simp only [LaurentArithmetic.matrixDenote, compile, collect_value_get]
  exact coefficientProgram_correct L A P allowed _ _

theorem compile_cost (L : LaurentArithmetic.DenseMatrix K D n n h)
    (A : LaurentArithmetic.DenseMatrix K D m m h) (P : LaurentArithmetic.DenseMatrix K D m k h)
    (allowed : Mask n m) :
    (compile L A P allowed).cost ≤ equationCount n m k * (n*m) * LaurentArithmetic.boxSize D h := by
  simp only [compile, collect_cost]
  calc
    _ ≤ ∑ _ : Fin (equationCount n m k), ∑ _ : Fin (n*m), LaurentArithmetic.boxSize D h :=
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => coefficientProgram_cost L A P allowed _ _
    _ = _ := by simp [mul_assoc]

def rhsArray (Y : LaurentArithmetic.DenseMatrix K D n m h)
    (Q : LaurentArithmetic.DenseMatrix K D n k h) :
    Vector (LaurentArithmetic.Dense K D h) (equationCount n m k) :=
  Vector.ofFn fun row => match (equationEquiv n m k).symm row with
    | .inl ij => Y[ij.1][ij.2]
    | .inr (.inl ij) => Q[ij.1][ij.2]
    | .inr (.inr _) => zeroDense

theorem rhsArray_correct (Y : LaurentArithmetic.DenseMatrix K D n m h)
    (Q : LaurentArithmetic.DenseMatrix K D n k h) (row : Fin (equationCount n m k)) :
    LaurentArithmetic.denote (rhsArray Y Q)[row] =
      systemRhs (LaurentArithmetic.matrixDenote Y) (LaurentArithmetic.matrixDenote Q)
        ((equationEquiv n m k).symm row) := by
  simp only [rhsArray, Fin.getElem_fin, Vector.getElem_ofFn]
  rcases (equationEquiv n m k).symm row with ij | (ij | ij)
  · rfl
  · rfl
  · exact zeroDense_correct

end Decoupling.HighDim.AlgorithmTwoLinearComparison
