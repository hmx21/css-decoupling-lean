import Decoupling.HighDim.AlgorithmTwoInvertibleMatrices
import Decoupling.HighDim.AlgorithmTwoInvertiblePresentations

/-!
# Executable invertible-lift stage from the actual quotient equivalence

The only algebraic hypotheses here describe the actual augmented
presentations and the two already computed representatives of beta and
its inverse. All four lower lifts and both enlarged matrices are outputs
of the executed program. There is no solver or comparison-data oracle.
-/
namespace Decoupling.HighDim.AlgorithmTwoInvertible
open Matrix ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] [DecidableEq K] {D c0 c1 t0 t1 h : ℕ}
variable {NC NT : Type*} [AddCommGroup NC] [Module (Laurent K D) NC]
  [AddCommGroup NT] [Module (Laurent K D) NT]
variable (dC : LaurentArithmetic.DenseMatrix K D c1 c0 h)
  (dT : LaurentArithmetic.DenseMatrix K D t1 t0 h)
  (F : LaurentArithmetic.DenseMatrix K D c1 t1 h) (G : LaurentArithmetic.DenseMatrix K D t1 c1 h)
  (piC : (Fin c1 → Laurent K D) →ₗ[Laurent K D] NC)
  (piT : (Fin t1 → Laurent K D) →ₗ[Laurent K D] NT)
  (exactC : LinearMap.range (LaurentArithmetic.matrixDenote dC).mulVecLin = LinearMap.ker piC)
  (exactT : LinearMap.range (LaurentArithmetic.matrixDenote dT).mulVecLin = LinearMap.ker piT)
  (beta : NT ≃ₗ[Laurent K D] NC)
  (hF : piC.comp (LaurentArithmetic.matrixDenote F).mulVecLin = beta.toLinearMap.comp piT)
  (hG : piT.comp (LaurentArithmetic.matrixDenote G).mulVecLin = beta.symm.toLinearMap.comp piC)

include exactC exactT hF hG in
omit [DecidableEq K] in
theorem solvableOfPresentations :
    FourSolvable (LaurentArithmetic.matrixDenote dC) (LaurentArithmetic.matrixDenote dT)
      (LaurentArithmetic.matrixDenote F) (LaurentArithmetic.matrixDenote G) :=
  fixed_presentations_lifts _ _ piC piT exactC exactT beta _ _ hF hG

/-- This concrete program materializes the two matrices used by the final
SUM/SWAP compiler, with all four solve hypotheses discharged internally. -/
def fromPresentationsProgram : Work K (LiftMatrices K D c0 c1 t0 t1 (liftBox D c1 t0 t1 c0 h)) :=
  liftMatricesProgram dC dT F G (solvableOfPresentations dC dT F G piC piT exactC exactT beta hF hG)

noncomputable def fromPresentationsData :
    Stabilization.ComparisonData (Laurent K D) (Fin c0) (Fin c1) (Fin t0) (Fin t1) :=
  comparisonData dC dT F G (solvableOfPresentations dC dT F G piC piT exactC exactT beta hF hG)

theorem fromPresentationsProgram_phiHat :
    LaurentArithmetic.matrixDenote (fromPresentationsProgram dC dT F G piC piT exactC exactT beta hF hG).value.phiHat =
      (fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG).phiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm :=
  liftMatricesProgram_phiHat _ _ _ _ _

theorem fromPresentationsProgram_psiHat :
    LaurentArithmetic.matrixDenote (fromPresentationsProgram dC dT F G piC piT exactC exactT beta hF hG).value.psiHat =
      (fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG).psiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm :=
  liftMatricesProgram_psiHat _ _ _ _ _

theorem fromPresentationsProgram_cost :
    (fromPresentationsProgram dC dT F G piC piT exactC exactT beta hF hG).cost ≤
      liftMatricesCost D c0 c1 t0 t1 h := liftMatricesProgram_cost _ _ _ _ _

theorem fromPresentationsData_representatives :
    piC.comp (fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG).phi1.mulVecLin =
        beta.toLinearMap.comp piT ∧
    piT.comp (fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG).psi1.mulVecLin =
        beta.symm.toLinearMap.comp piC := ⟨hF,hG⟩

/-- Both actual stabilized inverse identities and the square concern the
same computed comparison data whose enlarged matrices are returned. -/
theorem fromPresentationsData_invertible :
    let c := fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG
    (c.U*c.UInv=1 ∧ c.UInv*c.U=1) ∧ (c.V*c.VInv=1 ∧ c.VInv*c.V=1) ∧
      c.dTHat*c.U=c.V*c.dCHat :=
  ⟨(fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG).U_inverse,
    (fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG).V_inverse,
    (fromPresentationsData dC dT F G piC piT exactC exactT beta hF hG).stabilized_square⟩

end Decoupling.HighDim.AlgorithmTwoInvertible
