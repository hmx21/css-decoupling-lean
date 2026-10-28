import Decoupling.HighDim.AlgorithmTwoInvertibleProgram

/-! # Actual signed enlarged lift matrices, ready for the physical compiler -/
namespace Decoupling.HighDim.AlgorithmTwoInvertible
open Matrix ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] [DecidableEq K] {D c0 c1 t0 t1 h : ℕ}

def liftBox (D c1 t0 t1 c0 h : ℕ) : ℕ :=
  max h (max (outputBox D c1 t0 (h+h))
    (max (outputBox D t1 c0 (h+h)) (max (outputBox D c1 c1 (h+h)) (outputBox D t1 t1 (h+h)))))

private theorem liftBox_bounds (D c1 t0 t1 c0 h : ℕ) :
    h ≤ liftBox D c1 t0 t1 c0 h ∧ outputBox D c1 t0 (h+h) ≤ liftBox D c1 t0 t1 c0 h ∧
    outputBox D t1 c0 (h+h) ≤ liftBox D c1 t0 t1 c0 h ∧
    outputBox D c1 c1 (h+h) ≤ liftBox D c1 t0 t1 c0 h ∧
    outputBox D t1 t1 (h+h) ≤ liftBox D c1 t0 t1 c0 h := by unfold liftBox; omega

def fromBlocksArray {a b q r : ℕ} (A : LaurentArithmetic.DenseMatrix K D a q h)
    (B : LaurentArithmetic.DenseMatrix K D a r h) (C : LaurentArithmetic.DenseMatrix K D b q h)
    (E : LaurentArithmetic.DenseMatrix K D b r h) : LaurentArithmetic.DenseMatrix K D (a+b) (q+r) h :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    match finSumFinEquiv.symm i, finSumFinEquiv.symm j with
    | .inl i, .inl j => A[i][j]
    | .inl i, .inr j => B[i][j]
    | .inr i, .inl j => C[i][j]
    | .inr i, .inr j => E[i][j]

omit [DecidableEq K] in
theorem fromBlocksArray_correct {a b q r : ℕ} (A : LaurentArithmetic.DenseMatrix K D a q h)
    (B : LaurentArithmetic.DenseMatrix K D a r h) (C : LaurentArithmetic.DenseMatrix K D b q h)
    (E : LaurentArithmetic.DenseMatrix K D b r h) :
    LaurentArithmetic.matrixDenote (fromBlocksArray A B C E) =
      (Matrix.fromBlocks (LaurentArithmetic.matrixDenote A) (LaurentArithmetic.matrixDenote B)
        (LaurentArithmetic.matrixDenote C) (LaurentArithmetic.matrixDenote E)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  funext i j
  simp only [fromBlocksArray, LaurentArithmetic.matrixDenote, Fin.getElem_fin, Vector.getElem_ofFn,
    Fin.eta, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    simp [Matrix.fromBlocks, LaurentArithmetic.matrixDenote]

structure LiftMatrices (K : Type*) (D c0 c1 t0 t1 B : ℕ) where
  phiHat : LaurentArithmetic.DenseMatrix K D (c0+t1) (t0+c1) B
  psiHat : LaurentArithmetic.DenseMatrix K D (t0+c1) (c0+t1) B

variable (dC : LaurentArithmetic.DenseMatrix K D c1 c0 h)
  (dT : LaurentArithmetic.DenseMatrix K D t1 t0 h)
  (F : LaurentArithmetic.DenseMatrix K D c1 t1 h) (G : LaurentArithmetic.DenseMatrix K D t1 c1 h)
  (hs : FourSolvable (LaurentArithmetic.matrixDenote dC) (LaurentArithmetic.matrixDenote dT)
    (LaurentArithmetic.matrixDenote F) (LaurentArithmetic.matrixDenote G))

/-- Actual four solves followed by the two necessary signed blocks.
Padding and block placement copy coefficients without field operations. -/
def liftMatricesProgram : Work K (LiftMatrices K D c0 c1 t0 t1 (liftBox D c1 t0 t1 c0 h)) :=
  let solved := fourProgram dC dT F G hs
  let negF := LaurentArithmetic.matrixNegProgram F
  let negG := LaurentArithmetic.matrixNegProgram G
  let B := liftBox D c1 t0 t1 c0 h
  { value := ⟨fromBlocksArray (LaurentArithmetic.matrixPad solved.value.phi0 B)
      (LaurentArithmetic.matrixPad solved.value.etaC B) (LaurentArithmetic.matrixPad dT B)
      (LaurentArithmetic.matrixPad negG.value B),
      fromBlocksArray (LaurentArithmetic.matrixPad solved.value.psi0 B)
      (LaurentArithmetic.matrixPad solved.value.etaT B) (LaurentArithmetic.matrixPad dC B)
      (LaurentArithmetic.matrixPad negF.value B)⟩
    trace := solved.trace ++ negF.trace ++ negG.trace }

theorem liftMatricesProgram_phiHat :
    LaurentArithmetic.matrixDenote (liftMatricesProgram dC dT F G hs).value.phiHat =
      (comparisonData dC dT F G hs).phiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  have hb := liftBox_bounds D c1 t0 t1 c0 h
  change LaurentArithmetic.matrixDenote (fromBlocksArray _ _ _ _) = _
  rw [fromBlocksArray_correct, LaurentArithmetic.matrixPad_correct _ hb.2.1,
    LaurentArithmetic.matrixPad_correct _ hb.2.2.2.1,
    LaurentArithmetic.matrixPad_correct _ hb.1, LaurentArithmetic.matrixPad_correct _ hb.1,
    LaurentArithmetic.matrixNegProgram_correct]
  rfl

theorem liftMatricesProgram_psiHat :
    LaurentArithmetic.matrixDenote (liftMatricesProgram dC dT F G hs).value.psiHat =
      (comparisonData dC dT F G hs).psiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  have hb := liftBox_bounds D c1 t0 t1 c0 h
  change LaurentArithmetic.matrixDenote (fromBlocksArray _ _ _ _) = _
  rw [fromBlocksArray_correct, LaurentArithmetic.matrixPad_correct _ hb.2.2.1,
    LaurentArithmetic.matrixPad_correct _ hb.2.2.2.2,
    LaurentArithmetic.matrixPad_correct _ hb.1, LaurentArithmetic.matrixPad_correct _ hb.1,
    LaurentArithmetic.matrixNegProgram_correct]
  rfl

def liftMatricesCost (D c0 c1 t0 t1 h : ℕ) : ℕ :=
  fourCost D c0 c1 t0 t1 h + c1*t1*LaurentArithmetic.boxSize D h + t1*c1*LaurentArithmetic.boxSize D h

theorem liftMatricesProgram_cost :
    (liftMatricesProgram dC dT F G hs).cost ≤ liftMatricesCost D c0 c1 t0 t1 h := by
  simp only [liftMatricesProgram, Work.cost, List.length_append, liftMatricesCost]
  exact Nat.add_le_add
    (Nat.add_le_add (fourProgram_cost dC dT F G hs) (LaurentArithmetic.matrixNegProgram_cost F).le)
    (LaurentArithmetic.matrixNegProgram_cost G).le

end Decoupling.HighDim.AlgorithmTwoInvertible
