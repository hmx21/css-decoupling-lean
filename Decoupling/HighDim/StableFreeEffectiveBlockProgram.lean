import Decoupling.HighDim.StableFreeEffectiveStep
import Decoupling.HighDim.StableFreeEffectiveDense

/-!
# Counted execution of the represented Schanuel state update

The next forward/inverse matrices use actual dense products/subtractions.
Canonical row/column concatenation, row selection and padding are pure
coefficient copying. The returned trace counts every executed field operation.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix ArithmeticCost LaurentArithmetic
variable {K : Type*} [Field K] {D h a b p q m n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def zeroMatrixDense (K : Type*) [Zero K] (D h m n : ℕ) : DenseMatrix K D m n h :=
  Vector.ofFn fun _ => Vector.ofFn fun _ => zeroDense K D h

theorem zeroMatrixDense_correct : matrixDenote (zeroMatrixDense K D h m n) = 0 := by
  funext i j
  simp only [matrixDenote,zeroMatrixDense,Fin.getElem_fin,Vector.getElem_ofFn]
  exact zeroDense_correct

def rowBlocksDense (A : DenseMatrix K D a m h) (B : DenseMatrix K D b m h) :
    DenseMatrix K D (a+b) m h :=
  Vector.ofFn fun i => Sum.elim (fun j => A[j]) (fun j => B[j]) (finSumFinEquiv.symm i)

theorem rowBlocksDense_correct (A : DenseMatrix K D a m h) (B : DenseMatrix K D b m h) :
    matrixDenote (rowBlocksDense A B) = rowBlocks (matrixDenote A) (matrixDenote B) := by
  funext i j
  obtain ⟨x,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b)).surjective i
  rcases x with x|x <;>
    simp only [matrixDenote,rowBlocksDense,Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta,
      Equiv.symm_apply_apply,rowBlocks,Matrix.submatrix_apply,Matrix.fromRows,
      Sum.elim_inl,Sum.elim_inr] <;> rfl

theorem columnBlocksDense_correct (A : DenseMatrix K D m a h) (B : DenseMatrix K D m b h) :
    matrixDenote (joinColumns A B) = columnBlocks (matrixDenote A) (matrixDenote B) :=
  joinColumns_correct A B

def firstRowsDense (A : DenseMatrix K D (a+b) m h) : DenseMatrix K D a m h :=
  Vector.ofFn fun i => A[finSumFinEquiv (Sum.inl i)]

theorem firstRowsDense_correct (A : DenseMatrix K D (a+b) m h) :
    matrixDenote (firstRowsDense (a := a) (b := b) A) = firstRows (a := a) (b := b) (matrixDenote A) := by
  funext i j
  simp only [matrixDenote,firstRowsDense,Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta,
    firstRows,Matrix.submatrix_apply]
  rfl

def includeFirstDense (K : Type*) [Zero K] [One K] (D h a b : ℕ) : DenseMatrix K D (a+b) a h :=
  rowBlocksDense (identityDense K D h a) (zeroMatrixDense K D h b a)

theorem includeFirstDense_correct :
    matrixDenote (includeFirstDense K D h a b) = (includeFirst a b : Matrix _ _ (Laurent K D)) := by
  rw [includeFirstDense,rowBlocksDense_correct,identityDense_correct,zeroMatrixDense_correct]
  rfl

def subtractMatrixProgram (A B : DenseMatrix K D m n h) : Work K (DenseMatrix K D m n h) :=
  collect m fun i => collect n fun j => subtractDense A[i][j] B[i][j]

@[simp] theorem subtractMatrixProgram_cost (A B : DenseMatrix K D m n h) :
    (subtractMatrixProgram A B).cost = m*n*boxSize D h := by
  simp [subtractMatrixProgram,Nat.mul_assoc]

theorem subtractMatrixProgram_correct (A B : DenseMatrix K D m n h) :
    matrixDenote (subtractMatrixProgram A B).value = matrixDenote A-matrixDenote B := by
  funext i j
  simp only [matrixDenote,subtractMatrixProgram,collect_value_get,subtractDense_correct]
  rfl

/-- Execute the forward embedded-state update. -/
def stepForwardProgram (U : DenseMatrix K D (a+p) (b+q) h)
    (V : DenseMatrix K D (b+q) (a+p) h) :
    Work K (DenseMatrix K D (b+(a+p)) (a+(b+q)) (h+h)) :=
  let A := joinColumns (includeFirstDense K D h a p) U
  Work.bind (matrixMulProgram V A) fun VA =>
    Work.bind (subtractMatrixProgram VA
      (joinColumns (zeroMatrixDense K D (h+h) (b+q) a) (identityDense K D (h+h) (b+q)))) fun L =>
        Work.pure (rowBlocksDense (firstRowsDense (a := b) (b := q) L) (matrixPad A (h+h)))

@[simp] theorem stepForwardProgram_cost (U : DenseMatrix K D (a+p) (b+q) h)
    (V : DenseMatrix K D (b+q) (a+p) h) :
    (stepForwardProgram U V).cost =
      (b+q)*(a+(b+q))*(a+p)*boxSize D (h+h)*(2*boxSize D h+1) +
        (b+q)*(a+(b+q))*boxSize D (h+h) := by
  simp only [stepForwardProgram,Work.bind_cost,matrixMulProgram_cost,
    subtractMatrixProgram_cost,Work.pure_cost,add_zero]

theorem stepForwardProgram_correct (U : DenseMatrix K D (a+p) (b+q) h)
    (V : DenseMatrix K D (b+q) (a+p) h) :
    matrixDenote (stepForwardProgram U V).value =
      stepForward a b p q (matrixDenote U) (matrixDenote V) := by
  unfold stepForwardProgram
  simp only [Work.bind_value,Work.pure_value]
  rw [rowBlocksDense_correct,firstRowsDense_correct,subtractMatrixProgram_correct,
    matrixMulProgram_correct,matrixPad_correct _ (Nat.le_add_right _ _),
    columnBlocksDense_correct,columnBlocksDense_correct,includeFirstDense_correct,
    zeroMatrixDense_correct,identityDense_correct]
  rfl

/-- Execute the inverse update with its actual negation/subtraction trace. -/
def stepInverseProgram (U : DenseMatrix K D (a+p) (b+q) h)
    (V : DenseMatrix K D (b+q) (a+p) h) :
    Work K (DenseMatrix K D (a+(b+q)) (b+(a+p)) (h+h)) :=
  Work.bind (matrixNegProgram (includeFirstDense K D h b q)) fun negI =>
    let B := joinColumns negI V
    Work.bind (matrixMulProgram U B) fun UB =>
      Work.bind (subtractMatrixProgram
        (joinColumns (zeroMatrixDense K D (h+h) (a+p) b) (identityDense K D (h+h) (a+p))) UB) fun L =>
          Work.pure (rowBlocksDense (firstRowsDense (a := a) (b := p) L) (matrixPad B (h+h)))

@[simp] theorem stepInverseProgram_cost (U : DenseMatrix K D (a+p) (b+q) h)
    (V : DenseMatrix K D (b+q) (a+p) h) :
    (stepInverseProgram U V).cost =
      (b+q)*b*boxSize D h +
      ((a+p)*(b+(a+p))*(b+q)*boxSize D (h+h)*(2*boxSize D h+1) +
        (a+p)*(b+(a+p))*boxSize D (h+h)) := by
  simp only [stepInverseProgram,Work.bind_cost,matrixNegProgram_cost,
    matrixMulProgram_cost,subtractMatrixProgram_cost,Work.pure_cost,add_zero]

theorem stepInverseProgram_correct (U : DenseMatrix K D (a+p) (b+q) h)
    (V : DenseMatrix K D (b+q) (a+p) h) :
    matrixDenote (stepInverseProgram U V).value =
      stepInverse a b p q (matrixDenote U) (matrixDenote V) := by
  unfold stepInverseProgram
  simp only [Work.bind_value,Work.pure_value]
  rw [rowBlocksDense_correct,firstRowsDense_correct,subtractMatrixProgram_correct,
    matrixMulProgram_correct,matrixPad_correct _ (Nat.le_add_right _ _),
    columnBlocksDense_correct,columnBlocksDense_correct,matrixNegProgram_correct,
    includeFirstDense_correct,zeroMatrixDense_correct,identityDense_correct]
  rfl

end Decoupling.HighDim.StableFree.Effective
