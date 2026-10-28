import Decoupling.HighDim.StableFreeEffectiveAbsorb
import Decoupling.HighDim.StableFreeEffectiveFullProgram

/-! Counted dense execution of both actual stable-check-cokernel lift matrices. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
variable {K : Type*} [Field K] {D n m p q A B hL hS hE : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def extendAssociationDense (L : DenseMatrix K D (m+q) (n+p) hL) (b : ℕ) :
    DenseMatrix K D (m+(q+b)) (n+(p+b)) hL :=
  reindexDense (diagonalBlocksDense L (identityDense K D hL b)) (assocOrder m q b) (assocOrder n p b)

theorem extendAssociationDense_correct (L : DenseMatrix K D (m+q) (n+p) hL) (b : ℕ) :
    matrixDenote (extendAssociationDense L b) = extendAssociation (matrixDenote L) b := by
  rw [extendAssociationDense,reindexDense_correct,diagonalBlocksDense_correct,identityDense_correct]
  rfl

structure AbsorbedArrays (K : Type*) (D n m p A B h : ℕ) where
  forward : DenseMatrix K D (m+(p+A)) (n+(p+B)) h
  inverse : DenseMatrix K D (n+(p+B)) (m+(p+A)) h

/-- Three actual dense products implement the two quotient lifts. -/
def absorbProgram (L : DenseMatrix K D (m+q) (n+p) hL)
    (Linv : DenseMatrix K D (n+p) (m+q) hL)
    (S : DenseMatrix K D (q+B) (p+A) hS) (T : DenseMatrix K D (p+A) (q+B) hS)
    (EQ : DenseMatrix K D q q hE) :
    Work K (AbsorbedArrays K D n m p A B (hS+(hE+hL))) :=
  Work.bind (matrixMulProgram
    (diagonalBlocksDense (identityDense K D hE m) (diagonalBlocksDense EQ (identityDense K D hE B)))
    (extendAssociationDense L B)) fun normalized =>
  Work.bind (matrixMulProgram (diagonalBlocksDense (identityDense K D hS m) T) normalized) fun forward =>
  Work.bind (matrixMulProgram (extendAssociationDense Linv B)
    (diagonalBlocksDense (identityDense K D hS m) S)) fun inverse =>
  Work.pure { forward := forward, inverse := matrixPad inverse _ }

theorem absorbProgram_correct (L : DenseMatrix K D (m+q) (n+p) hL)
    (Linv : DenseMatrix K D (n+p) (m+q) hL)
    (S : DenseMatrix K D (q+B) (p+A) hS) (T : DenseMatrix K D (p+A) (q+B) hS)
    (EQ : DenseMatrix K D q q hE) :
    let out := (absorbProgram L Linv S T EQ).value
    matrixDenote out.forward = absorbForwardMatrix (matrixDenote L) (matrixDenote T) (matrixDenote EQ) ∧
    matrixDenote out.inverse = absorbInverseMatrix (matrixDenote Linv) (matrixDenote S) := by
  dsimp [absorbProgram]
  rw [matrixMulProgram_correct,matrixMulProgram_correct,diagonalBlocksDense_correct,
    diagonalBlocksDense_correct,diagonalBlocksDense_correct,identityDense_correct,
    identityDense_correct,identityDense_correct,extendAssociationDense_correct,
    matrixPad_correct _ (by omega),matrixMulProgram_correct,extendAssociationDense_correct,
    diagonalBlocksDense_correct,identityDense_correct]
  exact ⟨rfl,rfl⟩

/-- Exact operation count, including the complement normalization product. -/
def absorbCost (D n m p q A B hL hS hE : ℕ) : ℕ :=
  (m+(q+B))*(n+(p+B))*(m+(q+B))*boxSize D (hE+hL)*(2*boxSize D hE+1) +
  ((m+(p+A))*(n+(p+B))*(m+(q+B))*boxSize D (hS+(hE+hL))*(2*boxSize D hS+1) +
  (n+(p+B))*(m+(p+A))*(m+(q+B))*boxSize D (hL+hS)*(2*boxSize D hL+1))

theorem absorbProgram_cost (L : DenseMatrix K D (m+q) (n+p) hL)
    (Linv : DenseMatrix K D (n+p) (m+q) hL)
    (S : DenseMatrix K D (q+B) (p+A) hS) (T : DenseMatrix K D (p+A) (q+B) hS)
    (EQ : DenseMatrix K D q q hE) :
    (absorbProgram L Linv S T EQ).cost = absorbCost D n m p q A B hL hS hE := by
  simp only [absorbProgram,Work.bind_cost,Work.pure_cost,add_zero,matrixMulProgram_cost,absorbCost]

end Decoupling.HighDim.StableFree.Effective
