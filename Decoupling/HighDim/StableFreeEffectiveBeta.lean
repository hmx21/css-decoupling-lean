import Decoupling.HighDim.StableFreeEffectiveComplement
import Decoupling.HighDim.StableFreeEffectiveAbsorbProgram

/-!
# The calculated stable check-cokernel map with its actual two lifts

The complement equivalence is constructed from the computed inverse-on-image
matrices. The returned beta is a real LinearEquiv, and both materialized lift
matrices commute with the actual stabilized quotient maps. These are the
inputs required for the subsequent four comparison systems.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
universe u
variable {K : Type u} [Field K] {D n m p q A B hL hS hE : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {M N Q : ModuleCat.{u} (Laurent K D)}

/-- Real beta and both actual free-presentation lifts. The partial-inverse
premise is the already proved output of fullStabilizeProgram_correct. -/
theorem absorbProgram_presents
    (πN : Power (Laurent K D) n →ₗ[Laurent K D] N)
    (πM : Power (Laurent K D) m →ₗ[Laurent K D] M)
    (rq : RetractAt Q q) (e : (N × Power (Laurent K D) p) ≃ₗ[Laurent K D] (M × Q))
    (L : DenseMatrix K D (m+q) (n+p) hL) (Linv : DenseMatrix K D (n+p) (m+q) hL)
    (S : DenseMatrix K D (q+B) (p+A) hS) (T : DenseMatrix K D (p+A) (q+B) hS)
    (EQ : DenseMatrix K D q q hE) (hEQ : matrixDenote EQ = rq.model.projector)
    (hs : PartialEquiv (1 : Matrix (Fin (p+A)) (Fin (p+A)) (Laurent K D))
      (diagonalBlocks (matrixDenote EQ) 1) (matrixDenote S) (matrixDenote T))
    (hL : ∀ x, (πM.prodMap rq.project)
      ((powerAdd m q).symm (matrixDenote L *ᵥ x)) = e (stabilizedQuotient πN p x))
    (hLinv : ∀ x, stabilizedQuotient πN p (matrixDenote Linv *ᵥ x) =
      e.symm ((πM.prodMap rq.project) ((powerAdd m q).symm x))) :
    ∃ beta : (N × Power (Laurent K D) (p+B)) ≃ₗ[Laurent K D]
        (M × Power (Laurent K D) (p+A)),
      (∀ x, stabilizedQuotient πM (p+A) (matrixDenote (absorbProgram L Linv S T EQ).value.forward *ᵥ x) =
        beta (stabilizedQuotient πN (p+B) x)) ∧
      (∀ x, stabilizedQuotient πN (p+B) (matrixDenote (absorbProgram L Linv S T EQ).value.inverse *ᵥ x) =
        beta.symm (stabilizedQuotient πM (p+A) x)) := by
  rw [hEQ] at hs
  let s := complementFromMatrices rq (matrixDenote S) (matrixDenote T) hs
  refine ⟨absorbComputed e s,?_,?_⟩
  · intro x
    rw [(absorbProgram_correct L Linv S T EQ).1,hEQ]
    exact absorbForwardMatrix_projects πN πM rq e s _ _ hL
      (complementFromMatrices_inverse rq _ _ hs) x
  · intro x
    rw [(absorbProgram_correct L Linv S T EQ).2]
    exact absorbInverseMatrix_projects πN πM rq e s _ _ hLinv
      (complementFromMatrices_forward rq _ _ hs) x

end Decoupling.HighDim.StableFree.Effective
