import Decoupling.HighDim.AlgorithmTwoLinearComparisonGraded

/-! # Materialized right-hand sides of the four invertible-lift systems -/
namespace Decoupling.HighDim.AlgorithmTwoInvertible
open Matrix ArithmeticCost
variable {K : Type*} [Field K] {D c0 c1 t0 t1 h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def oneMinusProgram {n : ℕ} (A : LaurentArithmetic.DenseMatrix K D n n h) :
    Work K (LaurentArithmetic.DenseMatrix K D n n h) :=
  Work.bind (LaurentArithmetic.matrixNegProgram A) fun negA =>
    collect n fun i => collect n fun j =>
      AlgorithmTwoLinearComparison.addSame
        (if i=j then AlgorithmTwoLinearComparison.oneDense else AlgorithmTwoLinearComparison.zeroDense) negA[i][j]

theorem oneMinusProgram_correct {n : ℕ} (A : LaurentArithmetic.DenseMatrix K D n n h) :
    LaurentArithmetic.matrixDenote (oneMinusProgram A).value = 1 - LaurentArithmetic.matrixDenote A := by
  funext i j
  change LaurentArithmetic.denote (oneMinusProgram A).value[i][j] = _
  simp only [oneMinusProgram, Work.bind_value, collect_value_get,
    AlgorithmTwoLinearComparison.addSame_correct, Matrix.sub_apply, Matrix.one_apply]
  have hn := congrFun (congrFun (LaurentArithmetic.matrixNegProgram_correct A) i) j
  change LaurentArithmetic.denote (LaurentArithmetic.matrixNegProgram A).value[i][j] = -LaurentArithmetic.matrixDenote A i j at hn
  rw [hn]
  split_ifs <;> simp [sub_eq_add_neg]

theorem oneMinusProgram_cost {n : ℕ} (A : LaurentArithmetic.DenseMatrix K D n n h) :
    (oneMinusProgram A).cost = 2*n*n*LaurentArithmetic.boxSize D h := by
  simp [oneMinusProgram]
  ring

structure RightSides (K : Type*) (D c0 c1 t0 t1 h : ℕ) where
  forward : LaurentArithmetic.DenseMatrix K D c1 t0 (h+h)
  backward : LaurentArithmetic.DenseMatrix K D t1 c0 (h+h)
  errorC : LaurentArithmetic.DenseMatrix K D c1 c1 (h+h)
  errorT : LaurentArithmetic.DenseMatrix K D t1 t1 (h+h)

def rightSidesProgram (dC : LaurentArithmetic.DenseMatrix K D c1 c0 h)
    (dT : LaurentArithmetic.DenseMatrix K D t1 t0 h)
    (F : LaurentArithmetic.DenseMatrix K D c1 t1 h) (G : LaurentArithmetic.DenseMatrix K D t1 c1 h) :
    Work K (RightSides K D c0 c1 t0 t1 h) :=
  Work.bind (LaurentArithmetic.matrixMulProgram F dT) fun fwd =>
    Work.bind (LaurentArithmetic.matrixMulProgram G dC) fun bwd =>
      Work.bind (LaurentArithmetic.matrixMulProgram F G) fun fg =>
        Work.bind (oneMinusProgram fg) fun eC =>
          Work.bind (LaurentArithmetic.matrixMulProgram G F) fun gf =>
            Work.bind (oneMinusProgram gf) fun eT => Work.pure ⟨fwd,bwd,eC,eT⟩

theorem rightSidesProgram_correct (dC : LaurentArithmetic.DenseMatrix K D c1 c0 h)
    (dT : LaurentArithmetic.DenseMatrix K D t1 t0 h)
    (F : LaurentArithmetic.DenseMatrix K D c1 t1 h) (G : LaurentArithmetic.DenseMatrix K D t1 c1 h) :
    let q := (rightSidesProgram dC dT F G).value
    LaurentArithmetic.matrixDenote q.forward = LaurentArithmetic.matrixDenote F * LaurentArithmetic.matrixDenote dT ∧
    LaurentArithmetic.matrixDenote q.backward = LaurentArithmetic.matrixDenote G * LaurentArithmetic.matrixDenote dC ∧
    LaurentArithmetic.matrixDenote q.errorC = 1-LaurentArithmetic.matrixDenote F*LaurentArithmetic.matrixDenote G ∧
    LaurentArithmetic.matrixDenote q.errorT = 1-LaurentArithmetic.matrixDenote G*LaurentArithmetic.matrixDenote F := by
  simp only [rightSidesProgram, Work.bind_value, Work.pure_value,
    LaurentArithmetic.matrixMulProgram_correct, oneMinusProgram_correct, and_self]

def rightSidesCost (D c0 c1 t0 t1 h : ℕ) : ℕ :=
  (c1*t0*t1 + t1*c0*c1 + c1*c1*t1 + t1*t1*c1) * LaurentArithmetic.boxSize D (h+h) *
    (2*LaurentArithmetic.boxSize D h+1) + 2*(c1*c1+t1*t1)*LaurentArithmetic.boxSize D (h+h)

theorem rightSidesProgram_cost (dC : LaurentArithmetic.DenseMatrix K D c1 c0 h)
    (dT : LaurentArithmetic.DenseMatrix K D t1 t0 h)
    (F : LaurentArithmetic.DenseMatrix K D c1 t1 h) (G : LaurentArithmetic.DenseMatrix K D t1 c1 h) :
    (rightSidesProgram dC dT F G).cost = rightSidesCost D c0 c1 t0 t1 h := by
  simp only [rightSidesProgram, Work.bind_cost, Work.pure_cost, LaurentArithmetic.matrixMulProgram_cost,
    oneMinusProgram_cost, rightSidesCost]
  ring

end Decoupling.HighDim.AlgorithmTwoInvertible
